"""
IG Leads — أداة شخصية لاستخراج البيانات العامة لحسابات إنستغرام مع الإيميل والهاتف المنشورين.

المصادر:
  • الحسابات التي يتابعها مستخدم (Following) أو متابعوه (Followers)
  • المتفاعلون مع ريل أو منشور: المعلّقون و/أو المعجبون

مصدر البيانات: HikerAPI (https://hikerapi.com) — الدفع لكل طلب.

التشغيل:
    pip install -r requirements.txt
    streamlit run app.py
"""
from __future__ import annotations

import hmac
import io
import math
import os
import re
import threading
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime

import pandas as pd
import requests
import streamlit as st

# ─── الإعدادات ────────────────────────────────────────────────────────────────
BASE_URLS = ["https://api.hikerapi.com", "https://api.instagrapi.com"]  # الثاني عنوان بديل رسمي
LIST_ENDPOINTS = {
    "following": "/v1/user/following/chunk",
    "followers": "/v1/user/followers/chunk",
}
MODE_LABELS = {
    "following": "الحسابات التي يتابعها المستخدم (Following)",
    "followers": "متابعو المستخدم (Followers)",
    "reel": "المتفاعلون مع ريل أو منشور",
    "search": "بحث Reels أو هاشتاغ",
}
AUDIENCE_LABELS = {
    "commenters": "المعلّقون",
    "likers": "المعجبون",
    "both": "الاثنان معاً",
}
SOURCE_LABELS = {  # قيمة عمود Source في نتائج الريل
    frozenset({"comment"}): "commented",
    frozenset({"like"}): "liked",
    frozenset({"comment", "like"}): "commented+liked",
}
EST_PAGE_SIZE = 50          # صفحة المتابعين ترجع 25–100 حساب؛ 50 للتقدير فقط
COMMENTS_PER_PAGE = 15      # حسب توثيق HikerAPI: كل طلب تعليقات يرجع 15 تعليقاً
SEARCH_LABELS = {
    "reels": "Reels بكلمة بحث (مثل: i want sleep)",
    "tag_top": "هاشتاغ: المنشورات الأبرز",
    "tag_recent": "هاشتاغ: المنشورات الأحدث",
    "tag_reels": "هاشتاغ: الريلز فقط",
}
SEARCH_ENDPOINTS = {  # (المسار، اسم باراميتر الكلمة) — من توثيق HikerAPI الرسمي
    "reels": ("/v2/fbsearch/reels", "query"),
    "tag_top": ("/v2/hashtag/medias/top", "name"),
    "tag_recent": ("/v2/hashtag/medias/recent", "name"),
    "tag_reels": ("/v1/hashtag/medias/clips/chunk", "name"),
}
SEARCH_SHORT = {"tag_top": "top", "tag_recent": "recent", "tag_reels": "reels"}
EST_AUTHORS_PER_PAGE = 10   # تقدير متحفظ لعدد الحسابات الجديدة في كل صفحة بحث
FATAL_STATUSES = {401, 402}  # مفتاح خاطئ أو رصيد منتهٍ: نوقف العمل فوراً

COLUMNS = [
    "ID", "Username", "Name", "Email", "Other emails", "Phone", "Category",
    "Business", "Verified", "Private", "Followers", "Following", "Posts",
    "Website", "Bio", "Profile URL",
]
EXTRA_COLUMNS = ["Source", "Comment", "Views", "Post URL", "Email from"]  # تظهر حسب المصدر
NUMERIC_COLUMNS = ["Followers", "Following", "Posts"]

SHORTCODE_RE = re.compile(r"instagram\.com/(?:(?!share/)[A-Za-z0-9._]+/)?(?:p|reels?|tv)/([A-Za-z0-9_-]+)")
FREE_MAIL_DOMAINS = {  # إيميل على مزوّد مجاني = شخصي غالباً، وعلى نطاق خاص = تجاري غالباً
    "gmail.com", "googlemail.com", "yahoo.com", "yahoo.fr", "yahoo.co.uk", "ymail.com",
    "hotmail.com", "hotmail.fr", "hotmail.co.uk", "outlook.com", "outlook.fr", "live.com",
    "live.fr", "msn.com", "icloud.com", "me.com", "mac.com", "proton.me", "protonmail.com",
    "aol.com", "gmx.com", "gmx.de", "mail.ru", "yandex.com", "yandex.ru", "zoho.com", "mail.com",
}
SKIP_LABELS = {"private": "خاصاً", "verified": "موثّقاً", "business": "تجارياً"}

EMAIL_RE = re.compile(r"[A-Za-z0-9._%+\-]+@[A-Za-z0-9.\-]+\.[A-Za-z]{2,}")
OBFUSCATIONS = [  # name [at] gmail [dot] com  →  name@gmail.com
    (re.compile(r"\s*[\[\(\{]\s*at\s*[\]\)\}]\s*", re.I), "@"),
    (re.compile(r"\s*[\[\(\{]\s*dot\s*[\]\)\}]\s*", re.I), "."),
]


# ─── الاتصال بـ HikerAPI ─────────────────────────────────────────────────────
class ApiError(Exception):
    def __init__(self, message: str, status: int | None = None):
        super().__init__(message)
        self.status = status


class HikerClient:
    """عميل بسيط: المفتاح في الترويسة، إعادة المحاولة عند الأخطاء المؤقتة، وعدّاد للطلبات."""

    def __init__(self, api_key: str, base_url: str = BASE_URLS[0], timeout: int = 30, retries: int = 3):
        self.api_key = api_key.strip()
        self.base_url = base_url.rstrip("/")
        self.timeout = timeout
        self.retries = retries
        self.requests_used = 0
        self._switched = False
        self._lock = threading.Lock()
        self._local = threading.local()

    def _session(self) -> requests.Session:
        # جلسة مستقلة لكل خيط (thread) حتى تعمل الطلبات المتوازية بأمان
        session = getattr(self._local, "session", None)
        if session is None:
            session = requests.Session()
            session.headers.update({"x-access-key": self.api_key, "accept": "application/json"})
            self._local.session = session
        return session

    def get(self, path: str, **params):
        params = {k: v for k, v in params.items() if v not in (None, "")}
        last_error = ApiError("فشل الطلب بعد عدة محاولات.")
        for attempt in range(self.retries):
            try:
                resp = self._session().get(self.base_url + path, params=params, timeout=self.timeout)
            except requests.RequestException as exc:
                last_error = ApiError(f"مشكلة في الاتصال: {exc}")
                time.sleep(2 ** attempt)
                continue

            if resp.status_code == 429 or resp.status_code >= 500:  # خطأ مؤقت: ننتظر ونعيد
                last_error = ApiError(f"الخادم مشغول مؤقتاً (HTTP {resp.status_code}).", resp.status_code)
                time.sleep(2 ** attempt)
                continue

            try:
                data = resp.json()
            except ValueError:
                # رد ليس JSON (حجب من جدار حماية مثلاً): نجرّب العنوان البديل مرة واحدة
                alternative = next((b for b in BASE_URLS if b != self.base_url), None)
                if alternative and not self._switched:
                    self.base_url, self._switched = alternative, True
                    continue
                raise ApiError(
                    f"رد غير مفهوم من {self.base_url} (HTTP {resp.status_code}). "
                    "غيّر عنوان الـ API من «إعدادات متقدمة» ثم أعد المحاولة.",
                    resp.status_code,
                )

            with self._lock:
                self.requests_used += 1  # HikerAPI يحتسب ردود 2xx و4xx
            if resp.status_code >= 400:
                detail = (data.get("detail") or data.get("error")) if isinstance(data, dict) else None
                raise ApiError(f"HTTP {resp.status_code}: {detail or data}", resp.status_code)
            return data
        raise last_error


def friendly_error(exc: ApiError, fallback: str) -> str:
    """رسالة واضحة حسب نوع الخطأ، بدل نص عام قد يوهم بأن الرابط أو الحساب هو المشكلة."""
    if exc.status == 402:
        return "رصيدك في HikerAPI انتهى. اشحن حسابك من https://hikerapi.com/billing ثم أعد المحاولة."
    if exc.status == 401:
        return "مفتاح HikerAPI غير صحيح أو منتهٍ. راجعه في الشريط الجانبي."
    return f"{fallback} ({exc})"


# ─── أدوات مشتركة ────────────────────────────────────────────────────────────
def clean_username(text: str) -> str:
    """يقبل: username أو @username أو رابط البروفايل."""
    text = (text or "").strip()
    match = re.search(r"instagram\.com/([A-Za-z0-9._]+)", text)
    if match:
        text = match.group(1)
    return text.lstrip("@").strip("/ ").lower()


def _pk(obj: dict) -> str:
    return str(obj.get("pk") or obj.get("pk_id") or obj.get("id") or "")


def _unwrap(data) -> dict:
    """بعض نقاط الـ API ترجع {"user": {...}} وبعضها ترجع المستخدم مباشرة."""
    if not isinstance(data, dict):
        return {}
    return data["user"] if isinstance(data.get("user"), dict) else data


def skip_reason(user: dict, skip_private=True, skip_verified=False, skip_business=False) -> str | None:
    """أسباب التخطي المجانية: ما يمكن معرفته من بيانات القائمة قبل دفع أي طلب."""
    if skip_private and user.get("is_private"):
        return "private"
    if skip_verified and user.get("is_verified"):
        return "verified"
    if skip_business and (user.get("is_business") or user.get("is_business_account")
                          or user.get("account_type") == 2):
        return "business"
    return None


def is_personal_email(email) -> bool:
    return str(email or "").split("@")[-1].strip().lower() in FREE_MAIL_DOMAINS


def parse_page(data, key: str = "users") -> tuple[list, str | None]:
    """يدعم أشكال الرد: [items, cursor] أو {"response": {key: [...]}, "next_page_id": ...}
    أو {key: [...], "next_max_id": ...} أو قائمة عناصر بلا صفحات."""
    if isinstance(data, list):
        if len(data) == 2 and isinstance(data[0], list):
            return data[0], data[1]
        return [item for item in data if isinstance(item, dict)], None
    if isinstance(data, dict):
        body = data["response"] if isinstance(data.get("response"), dict) else data
        items = body.get(key) or []
        cursor = (data.get("next_page_id") or data.get("next_max_id")
                  or body.get("next_max_id") or data.get("end_cursor"))
        return items, cursor
    return [], None


# ─── المصدر 1: Following / Followers ─────────────────────────────────────────
def lookup_user(client: HikerClient, username: str) -> dict:
    user = _unwrap(client.get("/v1/user/by/username", username=username))
    if not _pk(user):
        raise ApiError(f"لم أجد الحساب @{username}.", 404)
    return user


def collect_accounts(client, user_id, mode, limit, skip_private=True, on_progress=None,
                     skip_verified=False, skip_business=False):
    """يجمع حتى `limit` حساباً من القائمة. المتخطّى يُعدّ فقط ولا يُدفع على تفاصيله."""
    accounts, seen, skips = [], set(), {}
    cursor, pages, max_pages = None, 0, 50 + limit // 10
    while len(accounts) < limit and pages < max_pages:
        page, next_cursor = parse_page(client.get(LIST_ENDPOINTS[mode], user_id=user_id, max_id=cursor))
        pages += 1
        added = 0
        for user in page:
            pk = _pk(user)
            if not pk or pk in seen:
                continue
            seen.add(pk)
            added += 1
            reason = skip_reason(user, skip_private, skip_verified, skip_business)
            if reason:
                skips[reason] = skips.get(reason, 0) + 1
                continue
            accounts.append(user)
            if len(accounts) >= limit:
                break
        if on_progress:
            on_progress(len(accounts))
        if not next_cursor or next_cursor == cursor or added == 0:
            break
        cursor = next_cursor
    return accounts, skips


# ─── المصدر 2: المتفاعلون مع ريل أو منشور ────────────────────────────────────
def shortcode_from(text: str) -> str | None:
    """يستخرج كود المنشور من الرابط (reel / p / tv، مع أو بدون اسم المستخدم)، أو يقبل الكود وحده."""
    text = (text or "").strip()
    match = SHORTCODE_RE.search(text)
    if match:
        return match.group(1)
    if re.fullmatch(r"[A-Za-z0-9_-]{9,14}", text):
        return text
    return None


def _unwrap_media(data) -> dict:
    if isinstance(data, list):
        data = data[0] if data and isinstance(data[0], dict) else {}
    if not isinstance(data, dict):
        return {}
    for key in ("media", "item"):
        if isinstance(data.get(key), dict):
            return data[key]
    if isinstance(data.get("items"), list) and data["items"]:
        return data["items"][0]
    return data


def resolve_media(client: HikerClient, text: str) -> dict:
    """رابط ريل/منشور عادي، أو رابط share للريلز، أو الكود وحده."""
    code = shortcode_from(text)
    if code:
        media = _unwrap_media(client.get("/v1/media/by/code", code=code))
    elif "instagram.com/share/" in (text or ""):
        media = _unwrap_media(client.get("/v1/share/reel/by/url", url=text.strip()))
        if not (media.get("id") or _pk(media)) and media.get("code"):
            media = _unwrap_media(client.get("/v1/media/by/code", code=media["code"]))
    else:
        raise ApiError("الرابط غير مفهوم. انسخه من زر المشاركة ثم «نسخ الرابط» في إنستغرام.")
    if not (media.get("id") or _pk(media)):
        raise ApiError("لم أجد هذا المنشور.", 404)
    return media


def collect_audience(client, media: dict, audience: str, limit: int, skip_private=True, on_progress=None,
                     skip_verified=False, skip_business=False):
    """يجمع المعلّقين و/أو المعجبين بدون تكرار وبدون صاحب الريل.
    الأولوية: من علّق وأعجب معاً، ثم المعلّقون، ثم المعجبون."""
    media_id = str(media.get("id") or _pk(media))
    owner_pk = _pk(media.get("user") or media.get("owner") or {})
    people: dict[str, dict] = {}
    skipped: dict[str, set] = {}

    def add(user: dict, source: str, comment: str = "") -> None:
        pk = _pk(user or {})
        if not pk or pk == owner_pk:
            return
        reason = skip_reason(user, skip_private, skip_verified, skip_business)
        if reason:
            skipped.setdefault(reason, set()).add(pk)
            return
        person = people.get(pk)
        if person is None:
            person = people[pk] = {"user": user, "sources": set(), "comment": "", "order": len(people)}
        person["sources"].add(source)
        if comment and not person["comment"]:
            person["comment"] = comment.strip()[:300]

    if audience in ("commenters", "both"):
        cursor, pages, max_pages = None, 0, 30 + limit // 5
        while pages < max_pages:
            data = client.get("/v2/media/comments", id=media_id, page_id=cursor)
            comments, next_cursor = parse_page(data, "comments")
            pages += 1
            for comment in comments:
                add(comment.get("user") or {}, "comment", comment.get("text") or "")
            if on_progress:
                on_progress(len(people))
            commenters = sum(1 for p in people.values() if "comment" in p["sources"])
            if commenters >= limit or not comments or not next_cursor or next_cursor == cursor:
                break
            cursor = next_cursor

    if audience in ("likers", "both"):
        likers, _ = parse_page(client.get("/v1/media/likers", id=media_id), "users")
        for user in likers:
            add(user, "like")
        if on_progress:
            on_progress(len(people))

    def rank(person: dict):
        sources = person["sources"]
        return (0 if len(sources) == 2 else 1 if "comment" in sources else 2, person["order"])

    chosen = sorted(people.values(), key=rank)[:limit]
    meta = {
        _pk(p["user"]): {"Source": SOURCE_LABELS[frozenset(p["sources"])], "Comment": p["comment"]}
        for p in chosen
    }
    return [p["user"] for p in chosen], meta, {k: len(v) for k, v in skipped.items()}


# ─── المصدر 3: بحث Reels أو هاشتاغ ───────────────────────────────────────────
def clean_search_term(kind: str, text: str) -> str:
    text = (text or "").strip()
    if kind == "reels":
        return text
    return re.sub(r"[\s#]+", "", text).lower()  # الهاشتاغ بدون # وبدون مسافات


def iter_media(obj, found: list | None = None) -> list[dict]:
    """يلتقط كل المنشورات من أي شكل للرد (sections / clips / modules / قوائم)."""
    if found is None:
        found = []
    if isinstance(obj, dict):
        author = obj.get("user") or obj.get("owner")
        if isinstance(author, dict) and (obj.get("code") or obj.get("media_type") is not None):
            found.append(obj)
            return found
        for value in obj.values():
            iter_media(value, found)
    elif isinstance(obj, list):
        for value in obj:
            iter_media(value, found)
    return found


def search_cursor(data, kind: str) -> dict | None:
    """باراميترات الصفحة التالية حسب نوع البحث، أو None إن انتهت النتائج."""
    if isinstance(data, list):  # v1: [items, next_max_id]
        nxt = data[1] if len(data) == 2 and isinstance(data[1], str) else None
        return {"max_id": nxt} if nxt else None
    if not isinstance(data, dict):
        return None
    body = data["response"] if isinstance(data.get("response"), dict) else data
    if kind == "reels":
        max_id = body.get("reels_max_id") or data.get("reels_max_id") or data.get("next_page_id")
        if not max_id or body.get("has_more") is False or data.get("has_more") is False:
            return None
        cursor = {"reels_max_id": max_id}
        rank = body.get("rank_token") or data.get("rank_token")
        if rank:
            cursor["rank_token"] = rank
        return cursor
    nxt = data.get("next_page_id") or body.get("next_max_id")
    if not nxt:
        return None
    return {"max_id": nxt} if kind == "tag_reels" else {"page_id": nxt}


def media_views(media: dict) -> int:
    """المشاهدات للريلز والفيديو، والإعجابات للصور."""
    for key in ("play_count", "ig_play_count", "view_count", "video_view_count"):
        value = media.get(key)
        if isinstance(value, (int, float)) and value > 0:
            return int(value)
    likes = media.get("like_count")
    return int(likes) if isinstance(likes, (int, float)) else 0


def media_caption(media: dict) -> str:
    caption = media.get("caption_text")
    if not caption and isinstance(media.get("caption"), dict):
        caption = media["caption"].get("text")
    return caption or ""


def media_url(media: dict) -> str:
    return f"https://www.instagram.com/p/{media['code']}/" if media.get("code") else ""


def collect_search_authors(client, kind, term, limit, min_views=0, skip_private=True, on_progress=None,
                           skip_verified=False, skip_business=False):
    """أصحاب المنشورات بدون تكرار، مع أعلى مشاهدات لكل واحد، والإيميلات المكتوبة في نص منشوراتهم."""
    path, param = SEARCH_ENDPOINTS[kind]
    authors: dict[str, dict] = {}
    skipped, below, seen_media = {}, set(), set()
    cursor: dict = {}
    pages, max_pages = 0, 20 + limit // 2
    while pages < max_pages:
        data = client.get(path, **{param: term}, **cursor)
        pages += 1
        medias = [m for m in iter_media(data) if _pk(m) not in seen_media]
        seen_media.update(_pk(m) for m in medias)
        for media in medias:
            user = media.get("user") or media.get("owner") or {}
            pk = _pk(user)
            if not pk:
                continue
            reason = skip_reason(user, skip_private, skip_verified, skip_business)
            if reason:
                skipped.setdefault(reason, set()).add(pk)
                continue
            views = media_views(media)
            author = authors.get(pk)
            if author is None:
                if views < min_views:
                    below.add(pk)
                    continue
                if len(authors) >= limit:
                    continue
                author = authors[pk] = {"user": user, "views": views, "url": media_url(media), "emails": []}
            if views > author["views"]:
                author["views"], author["url"] = views, media_url(media)
            for email in extract_emails(media_caption(media)):
                if email not in author["emails"]:
                    author["emails"].append(email)
        if on_progress:
            on_progress(len(authors))
        next_cursor = search_cursor(data, kind)
        if len(authors) >= limit or not medias or not next_cursor or next_cursor == cursor:
            break
        cursor = next_cursor
    found = set(authors)
    stats = {"skips": {k: len(v - found) for k, v in skipped.items() if v - found},
             "below": len(below - found), "pages": pages}
    return list(authors.values()), stats


# ─── تفاصيل البروفايل ────────────────────────────────────────────────────────
def extract_emails(*texts) -> list[str]:
    """الإيميل من حقل التواصل أولاً، ثم أي إيميل مكتوب في البايو (حتى الصيغ المموّهة)."""
    found: list[str] = []
    for text in texts:
        if not text:
            continue
        text = str(text)
        for pattern, replacement in OBFUSCATIONS:
            text = pattern.sub(replacement, text)
        for match in EMAIL_RE.findall(text):
            email = match.strip(".").lower()
            if email not in found:
                found.append(email)
    return found


def build_phone(user: dict) -> str:
    phone = user.get("contact_phone_number") or user.get("business_phone_number")
    if not phone and user.get("public_phone_number"):
        code = user.get("public_phone_country_code")
        phone = f"+{code} {user['public_phone_number']}" if code else user["public_phone_number"]
    return str(phone).strip() if phone else ""


def _count(user: dict, key: str, edge: str):
    value = user.get(key)
    if value is None and isinstance(user.get(edge), dict):
        value = user[edge].get("count")
    return value


def normalize_profile(data) -> dict:
    user = _unwrap(data)
    username = user.get("username") or ""
    emails = extract_emails(user.get("public_email"), user.get("business_email"), user.get("biography"))
    return {
        "ID": _pk(user),
        "Username": username,
        "Name": user.get("full_name") or "",
        "Email": emails[0] if emails else "",
        "Other emails": ", ".join(emails[1:]),
        "Phone": build_phone(user),
        "Category": user.get("business_category_name") or user.get("category_name") or user.get("category") or "",
        "Business": bool(user.get("is_business") or user.get("is_business_account") or user.get("account_type") == 2),
        "Verified": bool(user.get("is_verified")),
        "Private": bool(user.get("is_private")),
        "Followers": _count(user, "follower_count", "edge_followed_by"),
        "Following": _count(user, "following_count", "edge_follow"),
        "Posts": _count(user, "media_count", "edge_owner_to_timeline_media"),
        "Website": user.get("external_url") or "",
        "Bio": user.get("biography") or "",
        "Profile URL": f"https://www.instagram.com/{username}/" if username else "",
    }


def fetch_profile(client: HikerClient, pk: str) -> dict:
    return normalize_profile(client.get("/v1/user/by/id", id=pk))


def estimate_requests(limit: int, mode: str = "following", audience: str = "commenters") -> int:
    if mode == "search":  # صفحات البحث + بروفايل لكل حساب (أقل فعلياً بفضل إيميلات النص)
        return math.ceil(limit / EST_AUTHORS_PER_PAGE) + limit
    if mode != "reel":
        return 1 + math.ceil(limit / EST_PAGE_SIZE) + limit
    total = 1 + limit  # فتح الريل + بروفايل لكل شخص
    if audience in ("commenters", "both"):
        total += math.ceil(limit / COMMENTS_PER_PAGE)
    if audience in ("likers", "both"):
        total += 1
    return total


def make_df(indexed_rows: list[tuple[int, dict]]) -> pd.DataFrame:
    ordered = [row for _, row in sorted(indexed_rows, key=lambda item: item[0])]
    extra = [col for col in EXTRA_COLUMNS if any(col in row for row in ordered)]
    df = pd.DataFrame(ordered, columns=COLUMNS + extra)
    for col in NUMERIC_COLUMNS + (["Views"] if "Views" in df.columns else []):
        df[col] = pd.to_numeric(df[col], errors="coerce").astype("Int64")
    return df


def has_value(series: pd.Series) -> pd.Series:
    return series.fillna("").astype(str).str.strip() != ""


# ─── التصدير ─────────────────────────────────────────────────────────────────
def to_csv_bytes(df: pd.DataFrame) -> bytes:
    return df.to_csv(index=False).encode("utf-8-sig")  # BOM حتى يعرض Excel العربية صحيحاً


def to_excel_bytes(df: pd.DataFrame) -> bytes:
    from openpyxl.cell.cell import ILLEGAL_CHARACTERS_RE
    from openpyxl.utils import get_column_letter

    clean = df.copy()
    for col in clean.columns:
        if pd.api.types.is_object_dtype(clean[col]) or pd.api.types.is_string_dtype(clean[col]):
            clean[col] = clean[col].map(lambda v: ILLEGAL_CHARACTERS_RE.sub("", v) if isinstance(v, str) else v)
    buffer = io.BytesIO()
    with pd.ExcelWriter(buffer, engine="openpyxl") as writer:
        clean.to_excel(writer, index=False, sheet_name="Leads")
        sheet = writer.sheets["Leads"]
        for i, col in enumerate(clean.columns, start=1):
            wide = col in ("Bio", "Comment")
            sheet.column_dimensions[get_column_letter(i)].width = 60 if wide else max(12, len(col) + 4)
        sheet.freeze_panes = "A2"
    return buffer.getvalue()


# ─── الواجهة ─────────────────────────────────────────────────────────────────
RTL_CSS = """
<style>
[data-testid="stMarkdownContainer"], [data-testid="stWidgetLabel"],
[data-testid="stCaptionContainer"], [data-testid="stMetricLabel"],
h1, h2, h3 { direction: rtl; text-align: right; }
</style>
"""


def get_secret(name: str) -> str | None:
    value = os.environ.get(name)
    if value:
        return value
    try:
        return st.secrets.get(name)
    except Exception:  # لا يوجد ملف secrets — طبيعي عند التشغيل المحلي
        return None


def require_password() -> None:
    """إن وُضعت APP_PASSWORD (مهم عند النشر على الإنترنت) لا تُفتح الأداة بدونها."""
    expected = get_secret("APP_PASSWORD")
    if not expected or st.session_state.get("authed"):
        return
    entered = st.text_input("كلمة سر الأداة", type="password", key="app_password")
    if entered and hmac.compare_digest(entered.encode(), str(expected).encode()):
        st.session_state["authed"] = True
        st.rerun()
    if entered:
        st.error("كلمة السر غير صحيحة.")
    st.stop()


def finish_row(row: dict, extra: dict | None) -> dict:
    """يضيف بيانات المصدر للصف. في البحث: إن لم يكن في البروفايل إيميل نستعمل إيميل نص المنشور."""
    if not extra:
        return row
    extra = dict(extra)
    caption_emails = extra.pop("_caption_emails", None)
    row.update(extra)
    if caption_emails is not None:
        found = [row["Email"]] if row["Email"] else []
        found += [e.strip() for e in row["Other emails"].split(",") if e.strip()]
        from_profile = bool(found)
        for email in caption_emails:
            if email not in found:
                found.append(email)
        row["Email"] = found[0] if found else ""
        row["Other emails"] = ", ".join(found[1:])
        row["Email from"] = "profile" if from_profile else ("caption" if found else "")
    return row


def fetch_profiles(client, jobs, meta, workers, rows, progress, preview):
    """يفحص البروفايلات بالتوازي. jobs: [(الترتيب، المستخدم)]. يرجع (الأخطاء، سبب التوقف)."""
    errors, aborted, total = [], None, len(jobs)
    if not total:
        return errors, aborted
    with ThreadPoolExecutor(max_workers=workers) as pool:
        futures = {pool.submit(fetch_profile, client, _pk(user)): (index, user) for index, user in jobs}
        for done, future in enumerate(as_completed(futures), start=1):
            index, user = futures[future]
            name = f"@{user.get('username', _pk(user))}"
            try:
                rows.append((index, finish_row(future.result(), meta.get(_pk(user)))))
            except ApiError as exc:
                errors.append(f"{name}: {exc}")
                if exc.status in FATAL_STATUSES:
                    aborted = friendly_error(exc, str(exc))
                    pool.shutdown(wait=False, cancel_futures=True)
                    break
            except Exception as exc:  # بيانات غير متوقعة لحساب واحد لا توقف العمل كله
                errors.append(f"{name}: {exc}")
            progress.progress(0.2 + 0.8 * done / total, text=f"فحص البروفايلات… {done}/{total}")
            if done % 10 == 0 or done == total:
                preview.dataframe(make_df(rows), hide_index=True)
    return errors, aborted


def run_job(client, target_text, mode, limit, skip_private, workers, audience="commenters",
            search_kind="reels", min_views=0, caption_only=True, personal_only=False):
    st.session_state.pop("job", None)
    progress = st.progress(0.0, text="جاري التحضير…")
    preview = st.empty()
    meta: dict = {}
    rows: list = []
    notes: list[str] = []

    def fail(message: str) -> None:
        progress.empty()
        st.error(message)

    def report(n: int) -> None:
        progress.progress(0.2 * min(n / limit, 1.0), text=f"جلب القائمة… {min(n, limit)}/{limit}")

    if mode == "reel":
        try:
            media = resolve_media(client, target_text)
        except ApiError as exc:
            return fail(friendly_error(exc, "تعذّر فتح الريل. تأكد من الرابط وأن صاحبه حساب عام."))
        code = media.get("code") or _pk(media)
        owner = (media.get("user") or {}).get("username") or ""
        label, slug = f"ريل {code}" + (f" (@{owner})" if owner else ""), f"reel_{code}"
        try:
            accounts, meta, skips = collect_audience(client, media, audience, limit, skip_private, report,
                                                     skip_verified=personal_only, skip_business=personal_only)
        except ApiError as exc:
            return fail(friendly_error(exc, "فشل جلب المتفاعلين."))
        skipped = sum(skips.values())
        jobs, listed = list(enumerate(accounts)), len(accounts) + skipped

    elif mode == "search":
        term = clean_search_term(search_kind, target_text)
        try:
            authors, stats = collect_search_authors(client, search_kind, term, limit, min_views,
                                                    skip_private, report,
                                                    skip_verified=personal_only, skip_business=personal_only)
        except ApiError as exc:
            return fail(friendly_error(exc, "فشل البحث."))
        if not authors:
            hint = "، أو خفّض حد المشاهدات" if min_views else ""
            return fail(f"لم أجد منشورات مناسبة. جرّب كلمة أو هاشتاغاً آخر{hint}.")
        source = f"reels: {term}" if search_kind == "reels" else f"#{term} ({SEARCH_SHORT[search_kind]})"
        label = f"بحث «{term}»" if search_kind == "reels" else f"#{term}"
        slug = "search_" + (re.sub(r"[^A-Za-z0-9_-]+", "_", term).strip("_")[:40] or "results")
        jobs, free = [], 0
        for index, author in enumerate(authors):
            extra = {"Source": source, "Views": author["views"], "Post URL": author["url"]}
            if author["emails"] and caption_only:
                row = normalize_profile(author["user"])  # بيانات مختصرة + إيميل النص، دون أي طلب
                row.update(extra)
                row["Email"], row["Other emails"] = author["emails"][0], ", ".join(author["emails"][1:])
                row["Email from"] = "caption"
                rows.append((index, row))
                free += 1
            else:
                jobs.append((index, author["user"]))
                meta[_pk(author["user"])] = {**extra, "_caption_emails": author["emails"]}
        skips = stats["skips"]
        skipped, listed = sum(skips.values()), len(authors) + sum(skips.values())
        if stats["below"]:
            notes.append(f"تم تجاهل {stats['below']} حساباً لم تبلغ منشوراته {min_views:,} مشاهدة، دون تكلفة.")
        if free:
            notes.append(f"{free} إيميلاً وُجدت في نص المنشورات مباشرة، دون فحص البروفايل (مجاناً).")

    else:
        username = clean_username(target_text)
        try:
            target = lookup_user(client, username)
        except ApiError as exc:
            return fail(friendly_error(exc, f"تعذّر الوصول إلى @{username}. تأكد من الاسم."))
        if target.get("is_private"):
            return fail(f"@{username} حساب خاص، ولا يمكن جلب قائمته. جرّب حساباً عاماً.")
        try:
            accounts, skips = collect_accounts(client, _pk(target), mode, limit, skip_private, report,
                                               skip_verified=personal_only, skip_business=personal_only)
        except ApiError as exc:
            return fail(friendly_error(exc, "فشل جلب القائمة."))
        skipped = sum(skips.values())
        label, slug = f"@{username}", f"{mode}_{username}"
        jobs, listed = list(enumerate(accounts)), len(accounts) + skipped

    if skipped:
        detail = " و".join(f"{count} {SKIP_LABELS.get(reason, reason)}" for reason, count in skips.items())
        notes.insert(0, f"تم تخطي {detail} دون أي تكلفة.")
    errors, aborted = fetch_profiles(client, jobs, meta, workers, rows, progress, preview)

    progress.empty()
    preview.empty()
    st.session_state["job"] = {
        "df": make_df(rows),
        "label": label,
        "slug": slug,
        "listed": listed,
        "skipped": skipped,
        "skips": skips,
        "personal_only": personal_only,
        "notes": notes,
        "errors": errors,
        "aborted": aborted,
        "requests": client.requests_used,
        "time": datetime.now().strftime("%Y%m%d_%H%M"),
    }


def show_results(price: float) -> None:
    job = st.session_state.get("job")
    if not job:
        return
    df = job["df"]
    st.divider()
    st.subheader(f"النتائج: {job['label']}")
    if job["aborted"]:
        st.warning(f"توقف الاستخراج قبل النهاية: {job['aborted']} النتائج الجزئية محفوظة أدناه.")

    with_email = has_value(df["Email"])
    cols = st.columns(5)
    cols[0].metric("في القائمة", job["listed"])
    cols[1].metric("في النتائج", len(df))
    cols[2].metric("لديها إيميل", int(with_email.sum()))
    cols[3].metric("لديها هاتف", int(has_value(df["Phone"]).sum()))
    cols[4].metric("التكلفة التقريبية", f"{job['requests'] * price:.2f}$", help=f"{job['requests']} طلب")
    for note in job.get("notes", []):
        st.caption(note)

    f1, f2, f3 = st.columns(3)
    only_email = f1.checkbox("فقط من لديهم إيميل", key="only_email")
    no_business = f2.checkbox("استبعد الحسابات التجارية", value=job.get("personal_only", False),
                              key="no_business")
    personal_mail = f3.checkbox("إيميلات شخصية فقط (gmail وأمثاله)", key="personal_mail")
    keep = pd.Series(True, index=df.index)
    if only_email or personal_mail:
        keep &= with_email
    if no_business:
        keep &= ~df["Business"].fillna(False).astype(bool)
    if personal_mail:
        keep &= df["Email"].map(is_personal_email)
    view = df[keep]
    if len(view) != len(df):
        st.caption(f"المعروض والمصدَّر: {len(view)} من {len(df)}.")
    st.dataframe(
        view, hide_index=True,
        column_config={
            "Profile URL": st.column_config.LinkColumn("Profile URL"),
            "Website": st.column_config.LinkColumn("Website"),
            "Post URL": st.column_config.LinkColumn("Post URL"),
        },
    )

    name = f"{job['slug']}_{job['time']}"
    left, right = st.columns(2)
    left.download_button("تنزيل CSV", to_csv_bytes(view), f"{name}.csv", "text/csv", key="dl_csv")
    right.download_button(
        "تنزيل Excel", to_excel_bytes(view), f"{name}.xlsx",
        "application/vnd.openxmlformats-officedocument.spreadsheetml.sheet", key="dl_xlsx",
    )
    if job["errors"]:
        with st.expander(f"حسابات تعذّر فحصها ({len(job['errors'])})"):
            st.text("\n".join(job["errors"][:300]))


def main() -> None:
    st.set_page_config(page_title="IG Leads", page_icon="📇", layout="wide")
    st.markdown(RTL_CSS, unsafe_allow_html=True)
    require_password()

    with st.sidebar:
        st.header("الإعدادات")
        api_key = st.text_input("مفتاح HikerAPI", value=get_secret("HIKERAPI_KEY") or "",
                                type="password", key="api_key")
        price = st.number_input("سعر الطلب الواحد بالدولار (حسب خطتك)", min_value=0.0, value=0.001,
                                step=0.0001, format="%.4f", key="price")
        workers = st.slider("عدد الطلبات المتوازية", 1, 10, 4, key="workers",
                            help="رقم أعلى = أسرع. خفّضه إن ظهرت أخطاء 429.")
        with st.expander("إعدادات متقدمة"):
            base_url = st.selectbox("عنوان الـ API", BASE_URLS, key="base_url")
        if st.button("عرض رصيدي", key="balance", disabled=not api_key):
            try:
                st.json(HikerClient(api_key, base_url).get("/sys/balance"))
            except ApiError as exc:
                st.error(friendly_error(exc, "تعذّر جلب الرصيد، راجعه من لوحة HikerAPI."))

    st.title("📇 IG Leads")
    st.caption("استخراج البيانات العامة لحسابات إنستغرام مع الإيميل والهاتف المنشورين.")

    mode = st.selectbox("مصدر البيانات", list(MODE_LABELS), format_func=MODE_LABELS.get, key="mode")
    audience, search_kind, min_views, caption_only = "commenters", "reels", 0, True
    if mode == "reel":
        target = st.text_input("رابط الريل أو المنشور", placeholder="https://www.instagram.com/reel/…",
                               key="target_reel")
        audience = st.radio("من تريد استخراجه؟", list(AUDIENCE_LABELS), format_func=AUDIENCE_LABELS.get,
                            horizontal=True, key="audience")
        if audience != "commenters":
            st.caption("ملاحظة: إنستغرام لا يعطي إلا جزءاً محدوداً من قائمة المعجبين، "
                       "أما التعليقات فتُجلب صفحة بعد صفحة حتى العدد المطلوب.")
    elif mode == "search":
        search_kind = st.radio("نوع البحث", list(SEARCH_LABELS), format_func=SEARCH_LABELS.get, key="search_kind")
        is_tag = search_kind != "reels"
        target = st.text_input("الهاشتاغ" if is_tag else "كلمة البحث",
                               placeholder="#cantsleep" if is_tag else "i want sleep", key="target_search")
        min_views = int(st.number_input(
            "حد أدنى للمشاهدات (للصور: الإعجابات)", min_value=0, value=0, step=10000, key="min_views",
            help="0 = بدون فلتر. الصفحات الكبيرة تضع غالباً إيميلاً للإعلانات والتعاون."))
        caption_only = st.checkbox("لا تفحص بروفايل من وُجد إيميله في نص المنشور (توفير)", value=True,
                                   key="caption_only")
    else:
        target = st.text_input("الحساب المستهدف", placeholder="username أو رابط البروفايل", key="target_user")
    limit = int(st.number_input("عدد الحسابات المطلوب", min_value=1, max_value=20000, value=100,
                                step=50, key="limit"))
    skip_private = st.checkbox("تخطَّ الحسابات الخاصة (لا إيميلات تجارية فيها عادةً، ويوفّر الطلبات)",
                               value=True, key="skip_private")
    personal_only = st.checkbox(
        "الحسابات الشخصية فقط (استبعد التجارية والموثّقة)", value=False, key="personal_only",
        help="الموثّقون والحسابات التي تظهر تجارية في القائمة تُتخطّى مجاناً، "
             "والباقي يُستبعد من النتائج بعد الفحص لأن نوع الحساب لا يُعرف إلا من البروفايل.")

    estimate = estimate_requests(limit, mode, audience)
    st.caption(f"التكلفة القصوى التقريبية: {estimate:,} طلب ≈ {estimate * price:.2f}$")

    if st.button("ابدأ الاستخراج", type="primary", key="start"):
        if mode == "reel":
            target_ok, missing = target.strip(), "الصق رابط الريل أولاً."
        elif mode == "search":
            target_ok, missing = clean_search_term(search_kind, target), "اكتب كلمة البحث أو الهاشتاغ أولاً."
        else:
            target_ok, missing = clean_username(target), "اكتب اسم الحساب المستهدف أو الصق رابطه."
        if not api_key.strip():
            st.error("أدخل مفتاح HikerAPI في الشريط الجانبي أولاً.")
        elif not target_ok:
            st.error(missing)
        else:
            run_job(HikerClient(api_key, base_url), target, mode, limit, skip_private, workers,
                    audience=audience, search_kind=search_kind, min_views=min_views,
                    caption_only=caption_only, personal_only=personal_only)

    show_results(price)


if __name__ == "__main__":
    main()
