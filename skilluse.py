#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Squad CS Bot — FINAL v3
- FIRST-ROUND-STYLE movement (high speed, wall-through, non-stop)
- 4 bots INSIDE each other (0 offset, same position)
- Enemy CHASE → ORBIT (circle around enemy once reached)
- ENEMY-only target (unknown players also treated as enemy)
- Homer skill from homoruse.py (instant cast, 2s cooldown)
"""
import os, re, sys, json, time, uuid, hmac, base64, random, hashlib, secrets
import threading, traceback, collections, argparse
import socket, struct, math, ssl
import asyncio
from datetime import datetime, timedelta, timezone

import requests, aiohttp, urllib3
import httpx
from Crypto.Cipher import AES
from Crypto.Util.Padding import pad, unpad
from protobuf_decoder.protobuf_decoder import Parser

try:
    from google_play_scraper import app as play_scraper
except Exception:
    play_scraper = None

urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)

# ═══════════════════════════════════════════════════════════════════
BOT_NAME = "EREN"
DANGER_JOIN_URL = "https://danger-guild-management-web.vercel.app/join"

DEBUG_ENABLED     = True
DEBUG_CONSOLE     = True
DEBUG_VERBOSE_UDP = False

REPLAY_DELAY_MIN = 10
REPLAY_DELAY_MAX = 20
RUN_TIME_LIMIT   = 8 * 3600

_BASE_DIR = os.path.dirname(os.path.abspath(__file__))
AVAILABLE_ACCOUNTS_FILE = os.path.join(_BASE_DIR, "accounts.json")
RUNNING_ACCOUNTS_FILE   = os.path.join(_BASE_DIR, "running_accounts.json")
USED_ACCOUNTS_FILE      = os.path.join(_BASE_DIR, "used_accounts.json")
DEVICES_FILE            = os.path.join(_BASE_DIR, "devices.json")
UDP_LOG_FILE            = os.path.join(_BASE_DIR, "udp_logs.txt")
DEBUG_LOG_FILE          = os.path.join(_BASE_DIR, "debug.txt")

# ═══════════════════════════════════════════════════════════════════
# DEBUG
# ═══════════════════════════════════════════════════════════════════
_debug_lock = threading.Lock()
_debug_fp   = None

def _ensure_debug_file():
    global _debug_fp
    if _debug_fp is None and DEBUG_ENABLED:
        try:
            _debug_fp = open(DEBUG_LOG_FILE, "w", encoding="utf-8", buffering=1)
            _debug_fp.write(f"=== DEBUG SESSION {datetime.now().isoformat()} ===\n")
            _debug_fp.write(f"CONFIG: speed=9000 formation=INSIDE orbit=ON target=ENEMY_ONLY\n\n")
        except Exception as e:
            print(f"debug init failed: {e}")
    return _debug_fp

def dbg(cat, msg, data=None):
    if not DEBUG_ENABLED: return
    with _debug_lock:
        fp = _ensure_debug_file()
        if fp:
            ts = datetime.now().strftime("%H:%M:%S.%f")[:-3]
            try:
                fp.write(f"[{ts}] [{cat:10s}] {msg}\n")
                if data is not None:
                    if isinstance(data, (bytes, bytearray)):
                        h = data.hex()
                        fp.write(f"  HEX({len(data)}b): {h[:800]}{'...'+h[-800:] if len(h)>1600 else ''}\n")
                    else:
                        fp.write(f"  DATA: {str(data)[:1500]}\n")
            except Exception: pass
    if DEBUG_CONSOLE and cat in ("SKILL", "MATCH", "ERROR", "TARGET", "SUMMARY", "PHASE", "STUCK", "ORBIT"):
        with _print_lock:
            print(f"{GR}{_ts()}{R} {MG}[DBG {cat}]{R} {msg}", flush=True)

def dbg_close():
    global _debug_fp
    with _debug_lock:
        if _debug_fp:
            try:
                _debug_fp.write(f"\n=== ENDED {datetime.now().isoformat()} ===\n")
                _debug_fp.close()
            except Exception: pass
            _debug_fp = None

BAN_KEYWORDS = ("ban", "banned", "kick", "kicked", "suspend", "cheat",
                "violat", "restrict", "block", "abnormal", "invalid", "risk")

def dbg_check_ban(cmd, content, tag):
    if content is None: return False
    try:
        text = content.decode("utf-8", "ignore").lower()
        for kw in BAN_KEYWORDS:
            if kw in text:
                dbg("BAN_ALERT", f"{tag} cmd={cmd} kw='{kw}'", content)
                return True
    except Exception: pass
    return False

# ═══════════════════════════════════════════════════════════════════
R="\033[0m"; B="\033[1m"; GR="\033[90m"
RD="\033[91m"; GN="\033[92m"; YL="\033[93m"; CY="\033[96m"; WH="\033[97m"; MG="\033[95m"
_print_lock = threading.Lock()

def _ts(): return datetime.now().strftime("%H:%M:%S")
def line(m, color=WH, prefix="·"):
    with _print_lock: print(f"{GR}{_ts()}{R} {color}{prefix}{R} {m}", flush=True)
def ok(m):     line(m, GN, "✔")
def warn(m):   line(m, YL, "!")
def err(m):    line(m, RD, "✘")
def info(m):   line(m, GR, "·")
def action(m): line(m, CY, "»")
def squad_line(n, m, color=CY, prefix="»"):
    with _print_lock:
        print(f"{GR}{_ts()}{R} {MG}{B}[Squad {n}]{R} {color}{prefix}{R} {m}", flush=True)
def squad_ok(n, m):   squad_line(n, m, GN, "✔")
def squad_warn(n, m): squad_line(n, m, YL, "!")
def squad_err(n, m):  squad_line(n, m, RD, "✘")

# ═══════════════════════════════════════════════════════════════════
_account_store_lock = threading.Lock()

def _acct_load(path):
    try:
        with open(path, "r", encoding="utf-8") as f: d = json.load(f)
        return d if isinstance(d, list) else []
    except Exception: return []

def _acct_save(path, data):
    tmp = path + ".tmp"
    try:
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(data, f, indent=2, ensure_ascii=False)
        os.replace(tmp, path)
    except Exception as e: err(f"save {path} failed: {e}")

def _acct_key(rec):
    if not isinstance(rec, dict): return ""
    return str(rec.get("uid") or rec.get("user_id") or rec.get("id") or "").strip()

def _acct_region_match(rec, region):
    if not region: return True
    rr = str(rec.get("region", "")).strip().upper()
    return (not rr) or rr == str(region).strip().upper()

def pop_accounts_from_available(count, region=None):
    with _account_store_lock:
        available = _acct_load(AVAILABLE_ACCOUNTS_FILE)
        if not available: return []
        if region:
            matching = [r for r in available if _acct_region_match(r, region)]
            if len(matching) < count:
                ids = {id(r) for r in matching}
                matching.extend([r for r in available if id(r) not in ids])
            taken = matching[:count]
        else:
            taken = available[:count]
        if not taken: return []
        running = _acct_load(RUNNING_ACCOUNTS_FILE)
        taken_keys = {_acct_key(r) for r in taken if _acct_key(r)}
        if taken_keys:
            running = [r for r in running if _acct_key(r) not in taken_keys]
        now_iso = datetime.now().isoformat(timespec="seconds")
        for r in taken:
            if isinstance(r, dict): r["_running_since"] = now_iso
        running.extend(taken)
        _acct_save(RUNNING_ACCOUNTS_FILE, running)
        info(f"took {len(taken)} accounts (available अभी भी {len(available)} हैं)")
        return taken

def return_accounts_to_available(records):
    if not records: return
    with _account_store_lock:
        running = _acct_load(RUNNING_ACCOUNTS_FILE)
        keys = {_acct_key(r) for r in records if _acct_key(r)}
        if keys: running = [r for r in running if _acct_key(r) not in keys]
        _acct_save(RUNNING_ACCOUNTS_FILE, running)

def move_running_to_used(records=None):
    with _account_store_lock:
        running = _acct_load(RUNNING_ACCOUNTS_FILE)
        used = _acct_load(USED_ACCOUNTS_FILE)
        if records is None:
            to_move = list(running); remaining = []
        else:
            keys = {_acct_key(r) for r in records if _acct_key(r)}
            to_move = [r for r in running if _acct_key(r) in keys]
            remaining = [r for r in running if _acct_key(r) not in keys]
        now_iso = datetime.now().isoformat(timespec="seconds")
        for r in to_move:
            if isinstance(r, dict):
                r.pop("_running_since", None); r["_used_at"] = now_iso
        used.extend(to_move)
        _acct_save(RUNNING_ACCOUNTS_FILE, remaining)
        _acct_save(USED_ACCOUNTS_FILE, used)
        return len(to_move)

# ═══════════════════════════════════════════════════════════════════
REGION_LIST = ["IND","ID","TH","ME","EUROPE","VN","BD","PK","TW","RU","NA","SAC","BR","SG","US"]
REGION_LANG = {"ME":"ar","IND":"hi","ID":"id","VN":"vi","TH":"th","BD":"bn","PK":"ur",
               "TW":"zh","EUROPE":"fr","RU":"ru","NA":"na","SAC":"es","BR":"pt","SG":"ms","US":"us"}
REGION_GROUP = {
    "IND":"IND",
    "BR":"AMERICA","US":"AMERICA","NA":"AMERICA","SAC":"AMERICA",
    "ID":"OTHERS","TH":"OTHERS","ME":"OTHERS","EUROPE":"OTHERS",
    "VN":"OTHERS","BD":"OTHERS","PK":"OTHERS","TW":"OTHERS","RU":"OTHERS","SG":"OTHERS",
}
REGION_URLS = {
    "IND":    {"server":"https://loginbp.ggpolarbear.com/","client":"https://client.ind.freefiremobile.com/"},
    "AMERICA":{"server":"https://loginbp.ggpolarbear.com/","client":"https://client.us.freefiremobile.com/"},
    "OTHERS": {"server":"https://loginbp.ggpolarbear.com/","client":"https://clientbp.ggpolarbear.com/"},
}
REGION = "IND"; LANG_CODE = "hi"
SERVER_URL = REGION_URLS["IND"]["server"]
CLIENT_URL = REGION_URLS["IND"]["client"]

APP_ID=100067
SECRET = "2ee44819e9b4598845141067b281621874d0d5d7af9d8f7e00c1e54715b7d1e3"
VER_URL_BASE  = "https://version.ggwhitehawk.com/live/ver.php"
PLAYSTORE_URL = "https://play.google.com/store/apps/details?id=com.dts.freefireth&hl=en&gl=US"
USER_AGENT_WEB = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
                  "(KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36")

KEY = bytes([89,103,38,116,99,37,68,69,117,104,54,37,90,99,94,56])
IV  = bytes([54,111,121,90,68,114,50,50,69,51,121,99,104,106,77,37])
AUTH_AES_KEY = bytes([0x19,0x47,0xB9,0x74,0xD9,0x73,0xF3,0x7F,
                      0x42,0x06,0x01,0x38,0x42,0x00,0x10,0x30])
AUTH_AES_IV  = bytes([0x28,0x7F,0xCA,0x7A,0xF9,0x67,0xF3,0x7A,
                      0x65,0x02,0x01,0x10,0x40,0x40,0x00,0x30])
AUTH_CMD = 0x65
SESSION_HASH = "1ac4b80ecf0478a44203bf8fac6120f5"
Play_Version = "1.132.1"; Ob_VeR = "OB55"; CFG = {}
_LOGIN_LOCK=None
def _get_login_lock():
    global _LOGIN_LOCK
    if _LOGIN_LOCK is None: _LOGIN_LOCK = asyncio.Lock()
    return _LOGIN_LOCK

# ═══════════════════════════════════════════════════════════════════
# HOMER SKILL (homoruse.py style — instant cast)
# ═══════════════════════════════════════════════════════════════════
CMD_USE_ACTIVE_SKILL = 248
SKILL_ID_CANDIDATES = [5506, 706, 5505, 5507, 1250]
SKILL_COOLDOWN_SEC = 2.0        # तुरंत दोबारा cast
SKILL_FIRST_DELAY  = 0.8

def _uleb(n):
    if n < 0: n &= 0xFFFFFFFFFFFFFFFF
    out = bytearray()
    while True:
        b = n & 0x7F; n >>= 7
        if n: out.append(b | 0x80)
        else: out.append(b); break
    return bytes(out)

def _sint16(v):
    v = int(v) & 0xFFFF
    if v > 0x7FFF: v -= 0x10000
    return v.to_bytes(2, "little", signed=True)

def _crc16(data):
    crc = 0xFFFF
    for byte in data:
        crc ^= byte << 8
        for _ in range(8):
            crc = ((crc << 1) ^ 0x1021) if (crc & 0x8000) else (crc << 1)
            crc &= 0xFFFF
    return crc

class HomorSkill:
    def __init__(self, skill_id=None, cooldown=SKILL_COOLDOWN_SEC, first_delay=SKILL_FIRST_DELAY):
        self.skill_id = int(skill_id) if skill_id else SKILL_ID_CANDIDATES[0]
        self.cooldown = float(cooldown)
        self.first_delay = float(first_delay)
        self._last_cast = 0.0
        self._candidate_idx = 0
        self._accepted_skill = None
        self.target_id = 0
        self._aim = {"x": 0, "y": 0, "z": 0}
        self.fire_count = 0
        self.skill_used = {}

    def rotate_skill_id(self):
        if self._accepted_skill:
            self.skill_id = self._accepted_skill
            return
        self._candidate_idx = (self._candidate_idx + 1) % len(SKILL_ID_CANDIDATES)
        self.skill_id = SKILL_ID_CANDIDATES[self._candidate_idx]

    def mark_accepted(self, skill_id=None):
        if skill_id:
            self._accepted_skill = int(skill_id)
            self.skill_id = int(skill_id)
        else:
            self._accepted_skill = int(self.skill_id)

    def set_aim(self, x=None, y=None, z=None):
        if x is not None: self._aim["x"] = int(x)
        if y is not None: self._aim["y"] = int(y)
        if z is not None: self._aim["z"] = int(z)

    def build_packet_body(self, player_id, tick=0, target_id=0):
        body = bytearray()
        body += _uleb(int(player_id))
        body += _uleb(int(self.skill_id))
        body += _uleb(int(self._aim["x"]))
        body += _uleb(int(self._aim["y"]))
        body += _uleb(int(self._aim["z"]))
        body += _sint16(0); body += _sint16(0); body += _sint16(0)
        tid = int(target_id) if target_id else int(self.target_id or 0)
        body += _uleb(tid)
        body += _crc16(bytes(body)).to_bytes(2, "big")
        return bytes(body)

    def should_cast(self, now, joined_at):
        if joined_at is None: return False
        if (now - joined_at) < self.first_delay: return False
        if (now - self._last_cast) < self.cooldown: return False
        return True

    def mark_cast(self, now, sid=None):
        self._last_cast = now
        self.fire_count += 1
        if sid:
            self.skill_used[sid] = self.skill_used.get(sid, 0) + 1
        if not self._accepted_skill:
            self.rotate_skill_id()

# ═══════════════════════════════════════════════════════════════════
# CRYPTO
# ═══════════════════════════════════════════════════════════════════
def enc_aes(data): return AES.new(KEY, AES.MODE_CBC, IV).encrypt(pad(data, 16))

def decode_jwt_payload(token):
    try:
        parts = token.split(".")
        if len(parts) != 3: return {}
        p2 = parts[1] + "=" * (-len(parts[1]) % 4)
        return json.loads(base64.urlsafe_b64decode(p2))
    except Exception: return {}

def _varint(n):
    out = bytearray()
    while True:
        b = n & 0x7F; n >>= 7
        if n: out.append(b | 0x80)
        else: out.append(b); break
    return bytes(out)

def f_str(f, s):
    b = s.encode("utf-8")
    return bytes([(f << 3) | 2]) + _varint(len(b)) + b

def get_play_store_version():
    headers = {"User-Agent": USER_AGENT_WEB, "Accept-Language": "en-US,en;q=0.9"}
    r = requests.get(PLAYSTORE_URL, headers=headers, timeout=15)
    versions = re.findall(r"\b(1\.\d{1,3}\.\d{1,3})\b", r.text)
    if not versions: raise RuntimeError("no version")
    real = [v for v in versions if v != "1.000.000"]
    return (real or versions)[-1]

def fetch_ver_config(initial_version):
    version = initial_version; last = None
    for attempt in range(1, 4):
        url = (f"{VER_URL_BASE}?version={version}&lang={LANG_CODE}&device=android"
               f"&channel=3rd_party&appstore=thirdparty&region={REGION}"
               f"&whitelist_version=1.7.0&whitelist_sp_version=1.0.0")
        try: r = requests.get(url, timeout=15); cfg = r.json()
        except Exception as e:
            last = e; time.sleep(0.5 * attempt); continue
        if cfg.get("code") == 0:
            cfg["region"] = REGION; cfg["lang"] = LANG_CODE
            cfg["country_code"] = REGION
            cfg["server_url"] = SERVER_URL; cfg["client_url"] = CLIENT_URL
            return cfg
        if cfg.get("remote_version"): version = cfg["remote_version"]
        last = cfg; time.sleep(0.5 * attempt)
    raise RuntimeError(f"ver.php failed: {last}")

_AES_AK = b'Yg&tc%DEuh6%Zc^8'
_AES_IV = b'6oyZDr22E3ychjM%'

_login_client = httpx.AsyncClient(verify=False, timeout=25.0,
    limits=httpx.Limits(max_connections=100, max_keepalive_connections=50))

_LOGIN_HEADERS = {
    'User-Agent': 'UnityPlayer/2018.4.12f1 (UnityWebRequest/1.0, libcurl/8.5.0-DEV)',
    'Connection': 'Keep-Alive', 'Accept-Encoding': 'gzip',
    'Content-Type': 'application/x-www-form-urlencoded',
    'Expect': '100-continue', 'X-Unity-Version': '2018.4.12f1',
    'X-GA-SV': '1789535859', 'X-GA': 'v1 1', 'ReleaseVersion': 'OB55',
}

def _pb_read_varint(buf, off):
    shift = 0; val = 0
    while off < len(buf):
        b = buf[off]; off += 1
        val |= (b & 0x7F) << shift
        if not (b & 0x80): return val, off
        shift += 7
    raise ValueError("truncated")

def _pb_parse_simple(buf):
    out = {}; off = 0
    while off < len(buf):
        try: tag, off = _pb_read_varint(buf, off)
        except ValueError: break
        field = tag >> 3; wtype = tag & 0x07; val = None
        if wtype == 0: val, off = _pb_read_varint(buf, off)
        elif wtype == 1:
            if off + 8 > len(buf): break
            val = int.from_bytes(buf[off:off+8], "little"); off += 8
        elif wtype == 2:
            ln, off = _pb_read_varint(buf, off)
            if off + ln > len(buf): break
            val = buf[off:off+ln]; off += ln
        elif wtype == 5:
            if off + 4 > len(buf): break
            val = int.from_bytes(buf[off:off+4], "little"); off += 4
        else: break
        if field in out:
            if isinstance(out[field], list): out[field].append(val)
            else: out[field] = [out[field], val]
        else: out[field] = val
    return out

class MajorLoginRes:
    def __init__(self):
        self.account_id = 0; self.region = ""; self.token = ""
        self.url = ""; self.server_time = 0
        self.aes_ak = b""; self.iv_i = b""
    @classmethod
    def ParseFromString(cls, data):
        obj = cls(); fields = _pb_parse_simple(data)
        v = fields.get(1)
        if isinstance(v, int): obj.account_id = v
        v = fields.get(2)
        if isinstance(v, (bytes, bytearray)): obj.region = v.decode("utf-8", "ignore")
        v = fields.get(8)
        if isinstance(v, (bytes, bytearray)): obj.token = v.decode("utf-8", "ignore")
        v = fields.get(10)
        if isinstance(v, (bytes, bytearray)): obj.url = v.decode("utf-8", "ignore")
        v = fields.get(21)
        if isinstance(v, int): obj.server_time = v
        v = fields.get(22)
        if isinstance(v, (bytes, bytearray)): obj.aes_ak = bytes(v)
        v = fields.get(23)
        if isinstance(v, (bytes, bytearray)): obj.iv_i = bytes(v)
        return obj

class GetLoginDataRes:
    def __init__(self):
        self.nickname = ""; self.functional_addrs = ""; self.informational_addrs = ""
    @classmethod
    def ParseFromString(cls, data):
        obj = cls(); fields = _pb_parse_simple(data)
        v = fields.get(4)
        if isinstance(v, (bytes, bytearray)): obj.nickname = v.decode("utf-8", "ignore")
        v = fields.get(14)
        if isinstance(v, (bytes, bytearray)): obj.functional_addrs = v.decode("utf-8", "ignore")
        v = fields.get(32)
        if isinstance(v, (bytes, bytearray)): obj.informational_addrs = v.decode("utf-8", "ignore")
        return obj

def _get_device_for_account(account_identifier):
    devices = {}
    if os.path.exists(DEVICES_FILE):
        try:
            with open(DEVICES_FILE, "r", encoding="utf-8") as f:
                devices = json.load(f)
        except Exception: pass
    key = str(account_identifier)
    if key in devices: return devices[key]
    pool = [
        ("Samsung", "SM-G998B",  "Adreno (TM) 660", "Android OS 12 / API-31"),
        ("Xiaomi",  "2201122G",  "Adreno (TM) 730", "Android OS 13 / API-33"),
        ("Realme",  "RMX3700",   "Mali-G710",       "Android OS 14 / API-34"),
        ("OnePlus", "CPH2451",   "Adreno (TM) 740", "Android OS 13 / API-33"),
        ("OPPO",    "CPH2491",   "Adreno (TM) 642L","Android OS 13 / API-33"),
        ("Vivo",    "V2230",     "Mali-G77 MC9",    "Android OS 13 / API-33"),
    ]
    brand, model, gpu, os_ver = random.choice(pool)
    dev = {
        "unique_device_id": f"Google|{uuid.uuid4()}",
        "brand": brand, "model": model, "gpu_renderer": gpu,
        "system_software": os_ver,
        "screen_width": random.choice([1080, 1440, 720, 1280]),
        "screen_height": random.choice([2400, 3200, 1600, 2400]),
        "screen_dpi": str(random.randint(300, 420)),
        "memory": random.randint(2800, 6500),
        "processor_details": f"ARM64 FP ASIMD AES VMH | {random.randint(2200,3200)} | {random.randint(6,12)}",
        "client_ip": f"{random.randint(103,223)}.{random.randint(10,250)}.{random.randint(10,250)}.{random.randint(10,250)}",
    }
    devices[key] = dev
    try:
        with open(DEVICES_FILE, "w", encoding="utf-8") as f:
            json.dump(devices, f, indent=4)
    except Exception: pass
    return dev

def _encode_varint_simple(n):
    if n < 0: return b''
    out = bytearray()
    while True:
        b = n & 0x7F; n >>= 7
        if n: b |= 0x80
        out.append(b)
        if not n: return bytes(out)

def _build_proto_simple(fields):
    parts = []
    for k, v in fields.items():
        if isinstance(v, dict):
            nested = _build_proto_simple(v)
            parts.append(_encode_varint_simple((k << 3) | 2) + _encode_varint_simple(len(nested)) + nested)
        elif isinstance(v, int):
            parts.append(_encode_varint_simple((k << 3) | 0) + _encode_varint_simple(v))
        elif isinstance(v, (str, bytes)):
            ev = v.encode() if isinstance(v, str) else v
            parts.append(_encode_varint_simple((k << 3) | 2) + _encode_varint_simple(len(ev)) + ev)
    return b''.join(parts)

def _encrypt_api_bytes(data):
    return AES.new(_AES_AK, AES.MODE_CBC, _AES_IV).encrypt(pad(data, AES.block_size))

async def _get_playstore_version():
    if not play_scraper: return None
    loop = asyncio.get_event_loop()
    res = await loop.run_in_executor(
        None, lambda: play_scraper('com.dts.freefireth', lang='hi', country='id'))
    return res.get("version") if res else None

async def _version_config_async():
    try:
        app_version = await _get_playstore_version()
        if not app_version: return None
        url = (f"https://version.ggwhitehawk.com/live/ver.php?version={app_version}"
               "&lang=hi&device=android&channel=android&appstore=googleplay"
               "&region=ID&whitelist_version=1.3.0&whitelist_sp_version=1.0.0")
        r = await _login_client.get(url); r.raise_for_status()
        d = r.json()
        srv, rv, lrv = d.get("server_url"), d.get("remote_version"), d.get("latest_release_version")
        if not (srv and rv and lrv): return None
        return lrv, rv, srv
    except Exception: return None

async def _get_access_token_async(uid, password):
    url = "https://100067.connect.garena.com/oauth/guest/token/grant"
    hdrs = {
        "Host": "100067.connect.garena.com",
        "User-Agent": "Dalvik/2.1.0 (Linux; U; Android 12; SM-G998B Build/SP1A.210812.016)",
        "Content-Type": "application/x-www-form-urlencoded",
        "Accept-Encoding": "gzip, deflate, br",
        "Connection": "close",
    }
    body = {"uid": uid, "password": password, "response_type": "token",
            "client_type": "2", "client_secret": SECRET, "client_id": "100067"}
    for attempt in range(5):
        try:
            r = await _login_client.post(url, headers=hdrs, data=body)
            if r.status_code == 200:
                j = r.json()
                oi, at = j.get("open_id"), j.get("access_token")
                if oi and at:
                    dbg("LOGIN", f"grant OK uid={uid}")
                    return oi, at, j.get("platform", 4)
            if r.status_code == 429:
                await asyncio.sleep(0.5); continue
        except Exception as e: dbg("ERROR", f"grant: {e}")
        await asyncio.sleep(0.3)
    return None

async def _build_majorlogin_payload_async(open_id, access_token, platform, client_version, device_info):
    d = {3: str(datetime.now())[:-7], 4: "free fire", 5: "1",
         7: str(client_version) if client_version else "1.132.8",
         8: str(device_info.get("system_software", "Android OS 15 / API-35")),
         9: "Handheld", 10: "Telkomsel", 11: "CarrierDataNetwork",
         12: str(device_info.get("screen_width", 1639)),
         13: str(device_info.get("screen_height", 720)),
         14: str(device_info.get("screen_dpi", 320)),
         15: str(device_info.get("processor_details", "ARM64 FP ASIMD AES | 2000 | 8")),
         16: str(device_info.get("memory", 5653)),
         17: str(device_info.get("gpu_renderer", "Mali-G52 MC2")),
         18: "OpenGL ES 3.2 v1.r49p1-03bet0.19498e0ae1d5dac223383c39a2e58f04",
         19: str(device_info.get("unique_device_id", f"Google|{uuid.uuid4()}")),
         20: str(device_info.get("client_ip", "182.5.135.225")),
         21: "en", 22: str(open_id), 23: str(platform), 24: "Handheld",
         25: str(device_info.get("model", "Xiaomi 2409BRN2CY")), 26: "ID",
         29: str(access_token), 30: "1", 41: "Telkomsel", 42: "4G",
         57: SESSION_HASH, 60: "109278", 61: "55402",
         62: "868", 64: "55927", 65: "109278", 66: "55927", 67: "109278",
         73: 2,
         74: "/data/app/~~6Cw028g_ld-8Z0z2qhrOLA==/com.dts.freefireth-i3wiaEmpx8CbiRVhUMx_ag==/lib/arm64",
         76: 1, 77: "b8e0cd5e295eee42f5860d3c86e483dd|base.apk",
         78: 6, 79: 1, 81: "32", 83: "2019121229", 85: 3,
         86: "OpenGLES2", 87: 3071, 88: 4, 89: 14466, 93: "3rd_party",
         94: "KqsHTyb7yHjsAiyNWUUZa0DSOD6U0AhDQ76smAo1WeHHHpSmJ8KMRyRrxb2ttgJqO9YOqO/K6AORAvDMAX/qBS8+JahIkrM7kHfzlfULbgRAoZ9r",
         95: "111207", 96: '{"cur_rate":[60,90,120],"support_etc2":true}', 97: "1",
         98: "1", 99: str(platform), 100: str(platform), 102: "D]C\x15\x05T\x0eU3",
         103: "1", 104: "52837", 105: "1",
         106: "https://dl.gmc.freefiremobile.com/live/ABHotUpdates/|https://core-gmc.freefiremobile.com/live/ABHotUpdates/|211c933168f55902c7dfbfd8c4e2957d",
         107: "1.3fb8adbf45f44ce9"}
    return _encrypt_api_bytes(_build_proto_simple(d))

async def _send_majorlogin_async(data, release_version, server_url, tag="?"):
    try:
        url = f"{server_url}MajorLogin" if server_url.endswith('/') else f"{server_url}/MajorLogin"
        hdrs = _LOGIN_HEADERS.copy(); hdrs["ReleaseVersion"] = str(release_version)
        r = await _login_client.post(url, headers=hdrs, data=data)
        if r.status_code != 200: return None
        content = r.content
        if len(content) < 40: return None
        for offset in range(min(128, len(content))):
            try:
                res = MajorLoginRes.ParseFromString(content[offset:])
                if res.region and res.token and res.account_id > 1000:
                    return res
            except Exception: pass
        return None
    except Exception as e:
        dbg("ERROR", f"{tag} MajorLogin: {e}")
        return None

async def _send_getlogin_async(data, base_url, token, release_version, tag="?"):
    try:
        url = f"{base_url.rstrip('/')}/GetLoginData"
        hdrs = _LOGIN_HEADERS.copy()
        hdrs["ReleaseVersion"] = release_version
        hdrs["Authorization"] = f"Bearer {token}"
        hdrs["Host"] = "clientbp.ppmainecoonghj.com"
        r = await _login_client.post(url, headers=hdrs, data=data)
        if r.status_code != 200: return None
        content = r.content
        res_proto = None
        for offset in range(min(128, len(content))):
            try:
                p = GetLoginDataRes.ParseFromString(content[offset:])
                if p.functional_addrs or p.informational_addrs:
                    res_proto = p; break
            except Exception: pass
        if res_proto is None:
            res_proto = GetLoginDataRes.ParseFromString(content)
        return res_proto
    except Exception as e:
        dbg("ERROR", f"{tag} GetLoginData: {e}")
        return None

async def login_new_account(rec, tag, max_retries=6):
    uid = rec["uid"]
    pw = rec.get("pass") or rec.get("password")
    dbg("LOGIN", f"{tag} START uid={uid}")

    vc = await _version_config_async()
    if not vc: raise RuntimeError(f"{tag} version config failed")
    release_version, client_version, server_url = vc

    tg = await _get_access_token_async(uid, pw)
    if not tg: raise RuntimeError(f"{tag} access_token failed")
    open_id, access_token, platform = tg
    platform = int(platform or 4)

    device = _get_device_for_account(uid)
    payload = await _build_majorlogin_payload_async(open_id, access_token, platform, client_version, device)
    if not payload: raise RuntimeError(f"{tag} build payload failed")

    ml = None; last_err = None
    lock = _get_login_lock()
    async with lock:
        for attempt in range(1, max_retries + 1):
            try:
                ml = await _send_majorlogin_async(payload, release_version, server_url, tag)
                if ml and ml.region and ml.token and ml.account_id > 1000: break
                ml = None
            except Exception as e: last_err = e
            await asyncio.sleep(min(0.5 * attempt, 3.0))
        if ml is None: raise RuntimeError(f"{tag} MajorLogin failed: {last_err}")

    jwt = ml.token
    payload_jwt = decode_jwt_payload(jwt) if jwt else {}
    lock_reg = (payload_jwt.get("lock_region") or "").upper()
    if lock_reg and lock_reg != REGION:
        try:
            body = f_str(1, REGION)
            url = server_url.rstrip("/") + "/ChooseRegion"
            hdrs = _LOGIN_HEADERS.copy()
            hdrs["Authorization"] = f"Bearer {jwt}"
            hdrs["ReleaseVersion"] = release_version
            r = await _login_client.post(url, headers=hdrs, data=enc_aes(body))
            if r.status_code == 200:
                ml = await _send_majorlogin_async(payload, release_version, server_url, tag)
                if ml: jwt = ml.token
        except Exception: pass

    res_proto = await _send_getlogin_async(payload, ml.url, jwt, release_version, tag)
    if not res_proto: raise RuntimeError(f"{tag} GetLoginData failed")

    ts = ml.server_time; kr = ml.aes_ak; ir = ml.iv_i
    if ts is None or kr is None or ir is None:
        raise RuntimeError(f"{tag} missing key/iv/ts")

    dbg("LOGIN", f"{tag} COMPLETE id={ml.account_id} game={res_proto.functional_addrs}")
    return {
        "tag": tag, "uid": uid, "ingame_id": ml.account_id,
        "open_id": open_id, "access_token": access_token,
        "jwt": jwt, "key": kr, "iv": ir, "ts": ts,
        "game_server": res_proto.functional_addrs,
        "chat_server": res_proto.informational_addrs,
        "server_url": ml.url, "name": rec.get("name", "?"),
        "platform": platform,
        "cfg": {
            "remote_version": client_version,
            "latest_release_version": release_version,
            "server_url": server_url, "country_code": REGION,
        },
    }

async def refresh_game_server(acct):
    try:
        device = _get_device_for_account(acct["uid"])
        payload = await _build_majorlogin_payload_async(
            acct["open_id"], acct["access_token"], acct.get("platform", 4),
            acct["cfg"]["remote_version"], device)
        res_proto = await _send_getlogin_async(payload, acct["server_url"],
                                               acct["jwt"], acct["cfg"]["latest_release_version"],
                                               acct["tag"])
        if res_proto and res_proto.functional_addrs:
            acct["game_server"] = res_proto.functional_addrs
            dbg("REFRESH", f"{acct['tag']} game_server → {acct['game_server']}")
            return True
    except Exception as e:
        dbg("ERROR", f"{acct.get('tag')} refresh: {e}")
    return False

# ═══════════════════════════════════════════════════════════════════
# CLAN
# ═══════════════════════════════════════════════════════════════════
async def request_join_clan_via_danger(guild_id, guest_uid, guest_pw):
    params = {"guild_id": str(guild_id), "uid": str(guest_uid), "password": str(guest_pw)}
    try:
        async with aiohttp.ClientSession() as s:
            async with s.get(DANGER_JOIN_URL, params=params, timeout=30) as r:
                return (r.status == 200), r.status, await r.text()
    except Exception as e:
        return False, 0, f"{type(e).__name__}: {e}"

async def join_all_to_clan(accounts, clan_id):
    if not clan_id: return
    action(f"joining clan {clan_id}…")
    ok_n = fail_n = 0
    async def one(a):
        nonlocal ok_n, fail_n
        try:
            uid = a.get("uid"); pw = a.get("password") or a.get("pass")
            if not uid or not pw: fail_n += 1; return
            okk, status, _ = await request_join_clan_via_danger(clan_id, uid, pw)
            if okk: ok_n += 1; ok(f"uid={uid} joined clan {clan_id}")
            else:   fail_n += 1; warn(f"uid={uid} clan join failed · HTTP {status}")
        except Exception as e:
            fail_n += 1; warn(f"{a.get('uid')} error: {e}")
    await asyncio.gather(*[one(a) for a in accounts])
    ok(f"clan join done · {ok_n} ok · {fail_n} failed")

# ═══════════════════════════════════════════════════════════════════
# MOVEMENT — FIRST-ROUND STYLE (high speed, wall-through, non-stop)
# ═══════════════════════════════════════════════════════════════════
SETTLE_AFTER_ALL_JOIN = 1.5
SQUAD_PLAYERS = 4

SEND_HZ = 20.0                         # पहले 15 था → अब 20 (ज्यादा smooth)
MOVE_INTERVAL = 1.0 / SEND_HZ
WALK_SPEED = 9000.0                    # पहले 8000 → अब 9000 (first round जैसा)
STEP_PER_TICK = WALK_SPEED / SEND_HZ
ZONE_RADIUS_SCALE = 1000.0
CHASE_MIN_DIST = 80.0

# ORBIT — enemy के चारों तरफ घूमने का radius
ORBIT_RADIUS = 350.0                   # 0.35m
ORBIT_SPEED = 3.0                      # rad/sec
ORBIT_START_DIST = 500.0               # इससे कम दूरी पर orbit शुरू

# INSIDE — 4 bots बिल्कुल एक-दूसरे के अंदर (0 offset)
FORMATION_INSIDE = 0.0

CMD_PLAYER_JOIN = 101; CMD_MATCH_END = 103; CMD_DEAD = 107
CMD_SAFE_ZONE = 117; CMD_SERVER_TIME = 2000; CMD_MY_STATE = 2001
CMD_OTHER_STATES = 2012; CMD_OTHER_STATES_2014 = 2014
CMD_QUICK_CHAT = 551; CMD_GRI_SYNC = 1901

def _put_varint(out, v):
    v = int(v)
    while v >= 0x80: out.append((v & 0x7F) | 0x80); v >>= 7
    out.append(v & 0x7F)

def _put_zigvarint(out, v):
    z = (int(v) << 1) ^ (int(v) >> 63)
    _put_varint(out, z & 0xFFFFFFFFFFFFFFFF)

def _put_float_bits(out, f):
    _put_varint(out, struct.unpack("<I", struct.pack("<f", float(f)))[0])

def _rd_varint(b, p):
    v = i = 0
    while True:
        c = b[p + i]; v |= (c & 0x7F) << (7 * i); i += 1
        if not c & 0x80: return v, p + i

def _zag(v): return (v >> 1) ^ -(v & 1)

def build_player_state_upload(pid, pos, rot, tdir, vel, aim, st,
                              ps=0, pp=0, plat=0, lg=0, ping=0,
                              jump=0, slide=0, custom=0):
    o = bytearray()
    _put_varint(o, int(pid))
    _put_zigvarint(o, pos[0]); _put_zigvarint(o, pos[1]); _put_zigvarint(o, pos[2])
    _put_zigvarint(o, rot[0]); _put_zigvarint(o, rot[1]); _put_zigvarint(o, rot[2])
    _put_zigvarint(o, tdir[0]); _put_zigvarint(o, tdir[1])
    _put_zigvarint(o, vel[0]); _put_zigvarint(o, vel[1]); _put_zigvarint(o, vel[2])
    o.append(ps & 0xFF); o.append(pp & 0xFF)
    _put_float_bits(o, aim[0]); _put_float_bits(o, aim[1]); _put_float_bits(o, aim[2])
    _put_varint(o, plat); o.append(1 if lg else 0)
    _put_varint(o, ping); o.append(jump & 0xFF)
    _put_varint(o, slide); o.append(custom & 0xFF)
    _put_varint(o, st & 0xFFFFFFFF)
    return bytes(o)

def parse_player_join(body):
    if body is None or len(body) < 4: return None
    try:
        p = 0
        uid, p = _rd_varint(body, p); _s, p = _rd_varint(body, p)
        pid, p = _rd_varint(body, p); rl, p = _rd_varint(body, p)
        n = _zag(rl)
        name = body[p:p+n].decode("utf-8", "replace")
    except (IndexError, ValueError): return None
    return uid, pid, name

def decode_my_state(body):
    if body is None or len(body) < 6: return None
    try:
        p = 0
        _mt, p = _rd_varint(body, p); _c, p = _rd_varint(body, p); p += 1
        x, p = _rd_varint(body, p); y, p = _rd_varint(body, p); z, p = _rd_varint(body, p)
    except (IndexError, ValueError): return None
    return (_zag(x), _zag(y), _zag(z))

def decode_players_v2(body):
    players = {}
    if body is None or len(body) < 4: return players
    p = 2
    while p < len(body) - 1:
        try:
            sid = body[p]; p += 1
            x, p = _rd_varint(body, p); y, p = _rd_varint(body, p); z, p = _rd_varint(body, p)
            vx, p = _rd_varint(body, p); vy, p = _rd_varint(body, p); vz, p = _rd_varint(body, p)
            yr = body[p]; p += 1
            ay = body[p]; p += 1
            axz = body[p]; p += 1
            ps = body[p]; p += 1
            pp = body[p]; p += 1
            _pl, p = _rd_varint(body, p)
            _c = body[p]; p += 1
        except (IndexError, ValueError): break
        pos = (_zag(x), _zag(y), _zag(z))
        if not (1 <= sid <= 64): break
        if any(abs(v) > 4000000 for v in pos): break
        players[sid] = {"pos": pos, "vel": (_zag(vx), _zag(vy), _zag(vz)),
                        "yrot": yr, "aim_y": ay, "aim_xz": axz,
                        "physx_state": ps, "physx_pose": pp}
    return players

def decode_server_time(body):
    if not body: return None
    try:
        tick, p = _rd_varint(body, 0)
        phase = body[p] if p < len(body) else 0
    except (IndexError, ValueError): return None
    return tick, phase

def _read_vec2pos(b, p):
    x, p = _rd_varint(b, p); z, p = _rd_varint(b, p)
    return (_zag(x), _zag(z)), p

def decode_safezone(body):
    if not body: return None
    try:
        p = 0
        stage = body[p]; p += 1
        oc, p = _read_vec2pos(body, p); orad, p = _rd_varint(body, p)
        ic, p = _read_vec2pos(body, p); irad, p = _rd_varint(body, p)
        _t, p = (body[p] if p < len(body) else 0), p + 1
        st, p = _rd_varint(body, p); et, p = _rd_varint(body, p)
    except (IndexError, ValueError): return None
    return {"stage": stage, "outer_center": oc, "outer_radius": orad,
            "inner_center": ic, "inner_radius": irad, "start": st, "end": et}

def parse_gri_block(body):
    if body is None or len(body) < 2: return {}
    try: bl = struct.unpack_from("<H", body, 0)[0]
    except struct.error: return {}
    p = 2; end = min(2 + bl, len(body)); fields = {}
    while p < end:
        fid = body[p]; p += 1
        if p >= end: break
        try: v, p = _rd_varint(body, p)
        except (IndexError, ValueError): break
        fields[fid] = v
    return fields

def get_match_phase(body):
    fields = parse_gri_block(body)
    if 3 not in fields: return None
    v = fields[3]
    if v < 0x10000: return None
    return (v >> 16) & 0xFFFF, fields.get(2), (v >> 32) & 0xFFFFFFFF, v & 0xFFFF

def decode_quick_chat(body):
    if body is None or len(body) < 3: return None
    try:
        p = 0
        cid, p = _rd_varint(body, p); _i, p = _rd_varint(body, p); s, p = _rd_varint(body, p)
    except (IndexError, ValueError): return None
    return cid, s & 0xFF, s


class MovementState:
    """
    - 4 bots INSIDE each other (0 offset)
    - Enemy-only target (unknown players bhi enemy hain)
    - Orbit enemy के चारों तरफ
    - First-round style: fast, wall-through
    """
    def __init__(self, aid, team_uids=None, bot_index=0):
        self.account_id = int(aid)
        self.bot_index = int(bot_index)
        self.team_uids = set(int(x) for x in (team_uids or []) if int(x) != int(aid))
        self.my_id = None
        self.my_short = None
        self.my_pos = None
        self.target_pos = None
        self.target_fid = 0
        self.target_sid = 0
        self.target_uid = 0
        self.target_name = "?"
        self.zone_center = None
        self.zone_radius = 0.0
        self.phase = None
        self.round_no = None
        self.server_tick = None
        self.tick_local = None
        self.tick_rate = 30.0
        self.joined_at = None
        self.homer = HomorSkill()
        self._fallback_pid = (int(aid) & 0xFFFF) | 0x10000000
        self._movement_offset = [0.0, 0.0, 0.0]
        self.players_by_short = {}
        self.enemies_seen = set()
        self.team_skipped = 0
        self.target_changes = 0
        self.stuck_count = 0
        self.orbit_angle = random.uniform(0, 2 * math.pi)
        self.orbit_active = False
        self.last_pos_check = None
        self.last_pos_time = 0.0

    def set_identity(self, fid):
        self.my_id = int(fid); self.my_short = self.my_id & 0xFF
        if self.joined_at is None: self.joined_at = time.time()

    def add_player(self, fid, uid, name):
        self.players_by_short[int(fid) & 0xFF] = {"fid": int(fid), "uid": int(uid), "name": name}

    def is_teammate(self, rec):
        """HARD team filter — सिर्फ clear teammates skip"""
        if rec is None: return False     # ← FIX: unknown player = enemy
        if rec["uid"] in self.team_uids: return True
        if self.my_id is not None:
            if ((rec["fid"] >> 24) & 0xFF) == ((self.my_id >> 24) & 0xFF):
                return True
        return False

    def seed_my_pos(self, pos):
        if self.my_pos is None:
            self.my_pos = pos
        else:
            self.my_pos = (int(pos[0]), int(pos[1]), int(pos[2]))
        self._movement_offset = [0.0, 0.0, 0.0]

    def advance_pos(self, dx, dz):
        if self.my_pos is None: return
        self._movement_offset[0] += dx
        self._movement_offset[2] += dz

    def get_render_pos(self):
        """4 bots INSIDE each other → 0 offset"""
        if self.my_pos is None: return None
        bx, by, bz = self.my_pos
        ox, oy, oz = self._movement_offset
        return (int(bx + ox), int(by + oy), int(bz + oz))

    def sync_clock(self, tick, now):
        if self.server_tick is not None and self.tick_local is not None:
            dt = now - self.tick_local; dtick = tick - self.server_tick
            if dt > 0.5 and 0 < dtick < 10000:
                self.tick_rate = self.tick_rate * 0.7 + (dtick / dt) * 0.3
        self.server_tick = tick; self.tick_local = now

    def server_time(self, now):
        if self.server_tick is None:
            if self.joined_at is None: return 0
            return int((now - self.joined_at) * 1000.0) & 0xFFFFFFFF
        elapsed = now - self.tick_local
        ticks = self.server_tick + elapsed * self.tick_rate
        return int(ticks * 1000.0 / self.tick_rate) & 0xFFFFFFFF

    def effective_pid(self):
        return self.my_id if self.my_id is not None else self._fallback_pid


class MovementPlanner:
    """
    First-round style:
    - High speed (9000)
    - Wall-through (no collision, direct aim)
    - Enemy chase + orbit
    - Anti-stuck jitter
    """
    def __init__(self):
        self.step = float(STEP_PER_TICK)
        self.max_step = float(STEP_PER_TICK * 1.5)
        self._heading = random.uniform(0, 360)
        self._time_offset = random.uniform(0, 1000)
        self._stuck_until = 0.0
        self._stuck_heading = None
        self._last_pos = None
        self._last_pos_time = 0.0

    def next_yaw(self):
        self._heading = (self._heading + 30.0) % 360.0
        return self._heading

    def plan(self, st, now):
        pos = st.get_render_pos()
        if pos is None:
            pos = (128749, 15456, 590657)
            st.my_pos = pos

        # ---- ANTI-STUCK ----
        if self._last_pos is not None and (now - self._last_pos_time) >= 1.0:
            moved = math.hypot(pos[0] - self._last_pos[0], pos[2] - self._last_pos[2])
            if moved < 40.0:
                st.stuck_count += 1
                dbg("STUCK", f"bot{st.bot_index} stuck #{st.stuck_count} moved={moved:.1f}")
                self._stuck_until = now + 1.2
                self._stuck_heading = random.uniform(0, 360)
                st._movement_offset[0] += random.uniform(-800, 800)
                st._movement_offset[2] += random.uniform(-800, 800)
        self._last_pos = pos
        self._last_pos_time = now

        if now < self._stuck_until and self._stuck_heading is not None:
            angle = math.radians(self._stuck_heading)
            step = self.step * 1.2
            ddx = step * math.cos(angle); ddz = step * math.sin(angle)
            self._heading = self._stuck_heading
            return (int(pos[0] + ddx), pos[1], int(pos[2] + ddz)), ddx, ddz, 0.0

        # ---- PRIORITY 1: ENEMY CHASE / ORBIT ----
        if st.target_pos is not None:
            dx = st.target_pos[0] - pos[0]
            dz = st.target_pos[2] - pos[2]
            dist = math.sqrt(dx*dx + dz*dz)

            if dist > ORBIT_START_DIST:
                # दूर है → सीधे चेज़ करो (first-round style, दीवार आर-पार)
                st.orbit_active = False
                step = self.max_step
                move = min(step, dist)
                ux = dx / dist; uz = dz / dist
                ddx = ux * move; ddz = uz * move
                self._heading = math.degrees(math.atan2(dz, dx)) % 360.0
                return (int(pos[0] + ddx), pos[1], int(pos[2] + ddz)), ddx, ddz, dist
            else:
                # पास है → orbit (enemy के चारों तरफ घूमो)
                st.orbit_active = True
                st.orbit_angle += ORBIT_SPEED * (1.0 / SEND_HZ)
                orbit_x = st.target_pos[0] + ORBIT_RADIUS * math.cos(st.orbit_angle)
                orbit_z = st.target_pos[2] + ORBIT_RADIUS * math.sin(st.orbit_angle)
                odx = orbit_x - pos[0]; odz = orbit_z - pos[2]
                odist = math.sqrt(odx*odx + odz*odz)
                if odist > 1.0:
                    step = min(self.max_step, odist)
                    ux = odx / odist; uz = odz / odist
                    ddx = ux * step; ddz = uz * step
                    self._heading = math.degrees(math.atan2(odz, odx)) % 360.0
                    dbg("ORBIT", f"bot{st.bot_index} orbiting enemy d={dist:.0f} ang={math.degrees(st.orbit_angle):.0f}")
                    return (int(pos[0] + ddx), pos[1], int(pos[2] + ddz)), ddx, ddz, dist
                return (int(pos[0]), pos[1], int(pos[2])), 0.0, 0.0, dist

        # ---- PRIORITY 2: SAFE ZONE ----
        aim = None
        if st.zone_center is not None and st.zone_radius > 0:
            dx = pos[0] - st.zone_center[0]
            dz = pos[2] - st.zone_center[2]
            if math.sqrt(dx*dx + dz*dz) > st.zone_radius * 0.85:
                aim = st.zone_center

        # ---- PRIORITY 3: PATROL ----
        if aim is None:
            angle = (now * 60.0 + self._time_offset) % 360.0
            rad = math.radians(angle); radius = 3500.0
            aim = (pos[0] + radius * math.cos(rad), pos[1], pos[2] + radius * math.sin(rad))

        dx = aim[0] - pos[0]; dz = aim[2] - pos[2]
        dist = math.sqrt(dx*dx + dz*dz)
        if dist < 100.0:
            angle = random.uniform(0, 2 * math.pi)
            step = self.step * random.uniform(0.6, 1.0)
            ddx = step * math.cos(angle); ddz = step * math.sin(angle)
            self._heading = math.degrees(angle) % 360
            return (int(pos[0] + ddx), pos[1], int(pos[2] + ddz)), ddx, ddz, dist

        step = self.max_step if dist > 10000.0 else self.step
        move = min(step, dist)
        ux = dx / dist; uz = dz / dist
        ddx = ux * move; ddz = uz * move
        self._heading = math.degrees(math.atan2(dz, dx)) % 360.0
        return (int(pos[0] + ddx), pos[1], int(pos[2] + ddz)), ddx, ddz, dist


def _build_position_body(pid, new_pos, yaw, st, ddx, ddz, jump=0, slide=0):
    rad = math.radians(yaw)
    sx, sz = math.sin(rad), math.cos(rad)
    aim = (sx, 0.0, sz)
    rot = (int(sx * 100), 0, int(sz * 100))
    dist = math.sqrt(ddx*ddx + ddz*ddz)
    if dist >= 0.5:
        ux, uz = ddx/dist, ddz/dist
        vel = (int(ux*900), 0, int(uz*900))
        tdir = (int(ux * 100), int(uz * 100))
        pose = 2
    else:
        vel = (0, 0, 0)
        tdir = (int(sx * 100), int(sz * 100))
        pose = 0
    return build_player_state_upload(pid, new_pos, rot, tdir, vel, aim, st,
                                     ps=0, pp=pose, ping=50, jump=jump, slide=slide, custom=0)


def dispatch_incoming(cmd, body, st, squad_n, tag=""):
    if body is None: return
    if cmd == CMD_PLAYER_JOIN:
        info = parse_player_join(body)
        if info is None: return
        uid, fid, name = info
        if uid == st.account_id:
            st.set_identity(fid)
            squad_ok(squad_n, f"{tag} entered match fid=0x{fid:08X}")
            dbg("MATCH", f"{tag} my fid=0x{fid:08X} uid={uid} name={name}")
        else:
            st.add_player(fid, uid, name)
            is_team = st.is_teammate({"fid": fid, "uid": uid, "name": name})
            dbg("MATCH", f"{tag} {'TEAM' if is_team else 'ENEMY'} join fid=0x{fid:08X} uid={uid} name={name}")
    elif cmd == CMD_MY_STATE:
        pos = decode_my_state(body)
        if pos is not None: st.seed_my_pos(pos)
    elif cmd in (CMD_OTHER_STATES, CMD_OTHER_STATES_2014):
        players = decode_players_v2(body)
        if not players: return
        my = st.get_render_pos() or (0, 0, 0)
        best_sid = None; best_d2 = float("inf"); best_info = None
        for sid, pinfo in players.items():
            if sid == st.my_short: continue
            rec = st.players_by_short.get(sid)
            # HARD TEAM FILTER — rec None मतलब unknown player = ENEMY
            if st.is_teammate(rec):
                st.team_skipped += 1
                continue
            st.enemies_seen.add(sid)
            p = pinfo["pos"]
            dx = p[0] - my[0]; dz = p[2] - my[2]
            d2 = dx*dx + dz*dz
            if d2 < best_d2:
                best_d2 = d2; best_sid = sid; best_info = pinfo
        if best_info is not None and best_sid is not None:
            rec = st.players_by_short.get(best_sid)
            old_fid = st.target_fid
            st.target_pos = best_info["pos"]
            if rec:
                st.target_fid = rec["fid"]
                st.target_uid = rec["uid"]
                st.target_name = rec["name"]
                st.homer.target_id = rec["fid"]
            else:
                # unknown player → fid guess from sid
                st.target_fid = (best_sid & 0xFF) | 0x01000000
                st.target_uid = 0
                st.target_name = f"unknown_{best_sid}"
                st.homer.target_id = st.target_fid
            st.target_sid = int(best_sid)
            if old_fid != st.target_fid:
                st.target_changes += 1
                dist = math.sqrt(best_d2)
                dbg("TARGET", f"{tag} NEW ENEMY sid={best_sid} fid=0x{st.target_fid:X} "
                             f"uid={st.target_uid} name={st.target_name} d={dist:.0f}")
    elif cmd == CMD_SERVER_TIME:
        parsed = decode_server_time(body)
        if parsed is not None: st.sync_clock(parsed[0], time.time())
    elif cmd == CMD_GRI_SYNC:
        parsed = get_match_phase(body)
        if parsed is not None:
            op = st.phase
            st.phase = parsed[0]; st.round_no = parsed[1]
            if op != st.phase:
                dbg("PHASE", f"{tag} {op}→{st.phase}")
    elif cmd == CMD_SAFE_ZONE:
        zone = decode_safezone(body)
        if zone:
            c = zone.get("inner_center") or zone.get("outer_center")
            r = zone.get("inner_radius") or zone.get("outer_radius") or 0
            if c and r > 0:
                st.zone_center = (c[0], 0, c[1])
                st.zone_radius = r * ZONE_RADIUS_SCALE


async def movement_loop(sock, ra, ukb, mc, state, stop_evt, squad_n, tag):
    planner = MovementPlanner()
    nr = (await layouts_from_mask(mc))[1]
    loop = asyncio.get_event_loop()
    next_tick = time.time()
    sent = 0
    logged_started = False
    state.my_pos = (128749, 15456, 590657)
    last_skip_log = 0.0
    last_skill_log = 0.0

    while not stop_evt.is_set():
        now = time.time()
        if now < next_tick:
            try:
                await asyncio.wait_for(stop_evt.wait(), timeout=next_tick - now)
                break
            except asyncio.TimeoutError:
                pass
            continue
        next_tick += MOVE_INTERVAL
        if next_tick < now: next_tick = now + MOVE_INTERVAL

        # ============ SKILL CAST ============
        try:
            cur = state.get_render_pos()
            if state.target_pos is not None and cur is not None:
                dx = state.target_pos[0] - cur[0]
                dz = state.target_pos[2] - cur[2]
                dist = math.sqrt(dx*dx + dz*dz)
                if state.homer.should_cast(now, state.joined_at):
                    st_tick = state.server_time(now)
                    state.homer.set_aim(x=state.target_pos[0],
                                        y=state.target_pos[1],
                                        z=state.target_pos[2])
                    cast_pid = state.effective_pid()
                    body = state.homer.build_packet_body(cast_pid, st_tick,
                                                          target_id=state.target_fid)
                    if state.homer.fire_count < 3:
                        dbg("SKILL", f"{tag} body_hex={body.hex()}")
                    dbg("SKILL", f"{tag} FIRE#{state.homer.fire_count+1} skill={state.homer.skill_id} "
                                 f"ENEMY sid={state.target_sid} fid=0x{state.target_fid:X} "
                                 f"uid={state.target_uid} name={state.target_name} dist={dist:.0f}")
                    for cmd in (1412, 1414, CMD_USE_ACTIVE_SKILL, 250):
                        pkt = await build_packet(0x6B, nr, 0, cmd, None, 1, body, ukb, True)
                        await loop.sock_sendto(sock, pkt, ra)
                    state.homer.mark_cast(now, state.homer.skill_id)
                    if now - last_skill_log > 2.0:
                        last_skill_log = now
                        squad_ok(squad_n,
                            f"{tag} 🎯 SKILL#{state.homer.fire_count} id={state.homer.skill_id} "
                            f"→ ENEMY sid={state.target_sid} fid=0x{state.target_fid:X} "
                            f"d={dist:.0f}")
            else:
                if now - last_skip_log > 15:
                    last_skip_log = now
                    dbg("SKILL", f"{tag} no ENEMY target yet (team skipped={state.team_skipped})")
        except Exception as e:
            dbg("ERROR", f"{tag} skill: {e}")

        # ============ MOVEMENT ============
        try:
            new_pos, ddx, ddz, dist = planner.plan(state, now)
            state.advance_pos(ddx, ddz)
            st = state.server_time(now)
            yaw = planner.next_yaw()
            pid = state.effective_pid()
            render = state.get_render_pos()
            body = _build_position_body(pid, render, yaw, st, ddx, ddz)
            pkt = await build_packet(0x6B, nr, 0, CMD_MY_STATE, None, 1, body, ukb, True)
            await loop.sock_sendto(sock, pkt, ra)
            sent += 1
            if not logged_started:
                logged_started = True
                squad_ok(squad_n, f"{tag} movement started (fast + INSIDE + orbit)")
                dbg("MOVE", f"{tag} movement start pos={render}")
        except Exception as e:
            _udp_log(f"{tag} move err: {e}")

    dbg("SUMMARY", f"{tag} fires={state.homer.fire_count} "
                   f"enemies_seen={len(state.enemies_seen)} "
                   f"team_skipped={state.team_skipped} "
                   f"target_changes={state.target_changes} "
                   f"stuck={state.stuck_count} "
                   f"skills={dict(state.homer.skill_used)} pkts={sent}")

# ═══════════════════════════════════════════════════════════════════
# UDP ENGINE (unchanged)
# ═══════════════════════════════════════════════════════════════════
async def t_enc_packet_hex(h, k, v):
    return AES.new(k, AES.MODE_CBC, v).encrypt(pad(bytes.fromhex(h), 16)).hex()
async def t_enc_vr(n):
    if n < 0: return b""
    out = []
    while True:
        b = n & 0x7F; n >>= 7
        if n: b |= 0x80
        out.append(b)
        if not n: break
    return bytes(out)
async def t_create_varint(f, val): return await t_enc_vr((f << 3) | 0) + await t_enc_vr(val)
async def t_create_length(f, val):
    ev = val.encode() if isinstance(val, str) else val
    return await t_enc_vr((f << 3) | 2) + await t_enc_vr(len(ev)) + ev
async def t_create_proto(fields):
    pkt = bytearray()
    for f, val in fields.items():
        if isinstance(val, list):
            for item in val:
                if isinstance(item, dict): pkt.extend(await t_create_length(f, await t_create_proto(item)))
                elif isinstance(item, int): pkt.extend(await t_create_varint(f, item))
                elif isinstance(item, (str, bytes)): pkt.extend(await t_create_length(f, item))
        elif isinstance(val, dict): pkt.extend(await t_create_length(f, await t_create_proto(val)))
        elif isinstance(val, int): pkt.extend(await t_create_varint(f, val))
        elif isinstance(val, (str, bytes)): pkt.extend(await t_create_length(f, val))
    return pkt
async def t_dec_hex(h):
    s = hex(h)[2:]; return "0" + s if len(s) == 1 else s
async def t_fix_packet(parsed):
    out = {}
    for r in parsed:
        wt = r.wire_type
        if wt == "varint": val = r.data
        elif wt == "string": val = r.data
        elif wt == "bytes":
            v = r.data; val = v.hex() if isinstance(v, (bytes, bytearray)) else v
        elif wt == "length_delimited":
            try: val = await t_fix_packet(r.data.results)
            except Exception: val = str(r.data)
        else: val = r.data
        out[str(r.field)] = val
    return out
async def t_decode_packet(text):
    try: return await t_fix_packet(Parser().parse(text))
    except Exception: return None
async def t_generate_pk(pk_hex, n_prefix, k, v):
    enc = await t_enc_packet_hex(pk_hex, k, v)
    ln = await t_dec_hex(int(len(enc) // 2))
    pad_s = {2: "000000", 3: "00000", 4: "0000", 5: "000"}.get(len(ln), "")
    return bytes.fromhex(n_prefix + pad_s + ln + enc)

def _udp_log(msg):
    try:
        with open(UDP_LOG_FILE, "a", encoding="utf-8") as f:
            f.write(f"[{datetime.now().strftime('%H:%M:%S')}] {msg}\n")
    except Exception: pass

def _auth_region_byte(region):
    reg = str(region or "IND").upper()
    if reg == "IND": return 0x14
    if reg == "BD": return 0x19
    return 0x15

def build_auth_datagram(token, account_id):
    payload = token.encode("utf-8") if isinstance(token, str) else token
    p = 16 - (len(payload) % 16)
    data = AES.new(AUTH_AES_KEY, AES.MODE_CBC, AUTH_AES_IV).encrypt(payload + bytes([p]) * p)
    out = bytearray()
    out.append(AUTH_CMD & 0xFF); out.append(_auth_region_byte(REGION) & 0xFF)
    out += struct.pack(">Q", int(account_id) & 0xFFFFFFFFFFFFFFFF)
    out += struct.pack(">I", int(time.time()) & 0xFFFFFFFF)
    out += struct.pack(">i", len(data)); out += data
    return bytes(out)

def _br_rbyte(region):
    r = str(region or "BD").upper()
    return 0x19 if r == "BD" else (0x14 if r == "IND" else 0x15)

def _vi(n):
    out = bytearray()
    while True:
        b = n & 0x7F; n >>= 7
        if n: out.append(b | 0x80)
        else: out.append(b); break
    return bytes(out)
def _one(field, v):
    if isinstance(v, dict):
        body = _pb(v); return _vi((field << 3) | 2) + _vi(len(body)) + body
    if isinstance(v, int): return _vi(field << 3) + _vi(v)
    if isinstance(v, (str, bytes)):
        b = v.encode() if isinstance(v, str) else v
        return _vi((field << 3) | 2) + _vi(len(b)) + b
    raise TypeError(type(v))
def _pb(fields):
    out = bytearray()
    for f, v in fields.items():
        if isinstance(v, list):
            for it in v: out += _one(f, it)
        else: out += _one(f, v)
    return bytes(out)
def _br_frame(ptype, region, proto, key, iv):
    enc = AES.new(key, AES.MODE_CBC, iv).encrypt(pad(proto, 16))
    return bytes([ptype, _br_rbyte(region)]) + len(enc).to_bytes(4, "big") + enc
def _br_idc(reg, pings=(75, 123)):
    return [{1:"IDC1",2:pings[0],3:reg},{1:"IDC2",2:pings[1],3:reg}]

_C_S1 = "0200044B122D3B02010000000000000000000000000000E3172CED00"
_C_14_1 = b"\x32" + bytes([len(_C_S1)]) + _C_S1.encode() + b"\x30\x30" * 3
_C_14_3 = bytes.fromhex(
    "7e585c521207074f5d030c5c545104570455070f0a555a085201095701025b560601545606010f07100802487d5c4043481e07"
    "1f081a1709034c0757787500566b45627e7a6548407565577a700e7708627a047e7e041005447b5d655070547e437c607f7656"
    "5675704e5877525b5a5b515662410a105f5c5a4c1e637f1c7147430b4f6c557778605b67416b50635850500056575e005a7606"
    "057005067e0c15060045455e56447a665a6672694b5046524b057b79427c715560577b575f0a120e4b470e631b536262186b0f"
    "73406359475343795c481d7918564b47790c13054d1d714b5d75451740515f7e586d414e40595a03000e654e0741507a091b08"
    "4c6668777b1c4c676517505d6e7a4c4e7d7c791f5269057f42440207041005004d7e5c5977037d4a631f560255026b7a647e6b"
    "0007015503746353500e1a0048701a0153626506774f18065e0558610457421856007313771b60010b140745554d7f50477d68"
    "770662600646696876026242541c4a49037f74750a1204074f487402135059457f517b415266604a434506064e79004c5a7b4f"
    "700d14044a58454a5a7c5e5f5b764354425e1267735041537d6041180a6d694305")
_C_14_7 = bytes.fromhex("1d02474b420204030506171d677c716374687d5f557051565753")
_C_14_11 = b"\x03" + (
    "bbSQ69i8H3F5AdV2KyoVlWj2cgPtsEL3Pi8QcWkc/NJiGxtxXsmeZDDwFPKPbvd56sULGeaD3qha9S6hKIkIb3oXVAAFErlI76uU2p2AqNdJyaucxz1ba5ecHPCBohQR6E5Y1UzpsgpxutURpI8pbqY0tCpeL1bOT+F5UaysgFmTeoIalHxxEYPQx7OVJHElCV5el0vpIs98JSA3nB8FWin6ckz5Fd0sG4n2g0B7OUOvcreqilCT737xI24wPxLdidSr1AJ2MK0/m3ugV1iqzPXhttKyvfmMNVY8DoXBBUcYt3vpK7mgbnietrOqJIbJC3O4ygX6IWl/hkp+ngsjfeOZSornpzFnxM/kkqZgZjVOweXe61FRU6JsGSeTeY63kqA/mbCPfdwodSYJE2hXfVJofxRG1644gFPYRkCPUjJazd2l9WAh9kd86kYbjphbxwz55ciWvZ3sDJR11W96ezyxJPhJPD8FQoQVmno6BP4e7QI1xe+h35bkS1epZq6K6xUP5YtHFvqbhARMNQKUYYzXQWRFMNL1JgAeMJNO0+eCPL57+RXzRKtlgM/rVsIWhNw8Oo9SdP+7wsGrMK+HIOJaF1apAXNRQ9mCqxI="
).encode()

def br_create_squad_pkt(region, cv, key, iv):
    reg = str(region or "IND").upper()
    f = {1:1, 2:{
        2: b"\x01", 3:15, 4:SQUAD_PLAYERS - 1, 5:"en",
        8: _br_idc(reg), 9: 1, 10: bytes.fromhex("01090a0b12191a202729"),
        11: 1, 13: 1,
        14: {1:_C_14_1, 2:40, 3:_C_14_3, 4:"w\\Z]", 6:12, 7:_C_14_7,
             8: cv or "1.132.9", 9:6, 10:2, 11:_C_14_11},
        19: 329, 21: bytes.fromhex("374f521955"),
        24: [{1:3,2:360},{1:4,2:391},{1:5,2:156},{1:29,2:204},
             {1:22,2:118},{1:14,2:139},{1:21}],
        30: ("https://dl-ind-production.freefiremobile.com/"
             "2832022628717E276054_7104117490_107_1767713981_0")}}
    return _br_frame(0x05, reg, _pb(f), key, iv)

def br_join_team_pkt(code, region, cv, key, iv):
    reg = str(region or "IND").upper()
    field9 = {1:_C_14_1, 2:40, 3:_C_14_3, 4:"w\\Z]", 6:12, 7:_C_14_7,
              8: cv or "1.132.9", 9:6, 10:2, 11:_C_14_11}
    f = {1:4, 2:{
        4: bytes.fromhex("01090a0b121619201d2729"),
        5: str(code), 6:6, 8:1, 9: field9,
        11: _br_idc(reg, (99, 136)), 13:"en", 16: bytes.fromhex("374f521955"),
        20: [{1:3,2:360},{1:4,2:391},{1:5,2:156},{1:29,2:204},
             {1:22,2:118},{1:14,2:139},{1:21}],
        27: {1:2, 2:4}}}
    return _br_frame(0x05, reg, _pb(f), key, iv)

def br_start_squad_pkt(uid, region, key, iv):
    reg = str(region or "IND").upper()
    return _br_frame(0x05, reg, _pb({1:9, 2:{1:int(uid), 7:_br_idc(reg)}}), key, iv)

async def send_op31(group_id, region, key, iv):
    fields = {1:31, 2:{1:int(group_id)}}
    pkt = f"05{_auth_region_byte(region):02x}"
    proto_hex = (await t_create_proto(fields)).hex()
    return await t_generate_pk(proto_hex, pkt, key, iv)

async def build_auth_packet(account_id, token, server_time, key, iv, region=REGION, typ="OnLine"):
    uid_hex = f"{int(account_id):016x}"; ts_hex = f"{int(server_time):08x}"
    enc = AES.new(key, AES.MODE_CBC, iv).encrypt(pad(token.encode(), 16)).hex()
    enc_len = f"{len(enc) // 2:08x}"
    reg = str(region).upper()
    if reg == "BD": pre_on, pre_chat = "7119", "9219"
    elif reg == "IND": pre_on, pre_chat = "7114", "9214"
    else: pre_on, pre_chat = "7115", "9215"
    if typ == "OnLine":
        return bytes.fromhex(pre_on + uid_hex + ts_hex + "00000000" + enc_len + enc)
    return bytes.fromhex(pre_chat + uid_hex + ts_hex + enc_len + enc)

async def send_keep_alive(region=REGION):
    reg = str(region).upper()
    return bytes.fromhex("0214" if reg == "IND" else ("0219" if reg == "BD" else "0215"))

CRC7_TABLE = bytes([
    0,9,18,27,36,45,54,63,72,65,90,83,108,101,126,119,25,16,11,2,61,52,47,38,
    81,88,67,74,117,124,103,110,50,59,32,41,22,31,4,13,122,115,104,97,94,87,
    76,69,43,34,57,48,15,6,29,20,99,106,113,120,71,78,85,92,100,109,118,127,
    64,73,82,91,44,37,62,55,8,1,26,19,125,116,111,102,89,80,75,66,53,60,39,
    46,17,24,3,10,86,95,68,77,114,123,96,105,30,23,12,5,58,51,40,33,79,70,
    93,84,107,98,121,112,7,14,21,28,35,42,49,56,65,72,83,90,101,108,119,126,
    9,0,27,18,45,36,63,54,88,81,74,67,124,117,110,103,16,25,2,11,52,61,38,
    47,115,122,97,104,87,94,69,76,59,50,41,32,31,22,13,4,106,99,120,113,78,
    71,92,85,34,43,48,57,6,15,20,29,37,44,55,62,1,8,19,26,109,100,127,118,73,
    64,91,82,60,53,46,39,24,17,10,3,116,125,102,111,80,89,66,75,23,30,5,12,
    51,58,33,40,95,86,77,68,123,114,105,96,14,7,28,21,42,35,56,49,70,79,84,
    93,98,107,112,121])

_FIELD_SIZES = {0:1,1:2,2:2,3:1,4:2}
_FIELD_NAMES = {0:"sendOption",1:"cmd",2:"orderId",3:"flags",4:"length"}

def optimize_udp_socket(sock):
    try:
        sock.setsockopt(socket.SOL_SOCKET, socket.SO_RCVBUF, 262144)
        sock.setsockopt(socket.SOL_SOCKET, socket.SO_SNDBUF, 262144)
    except Exception: pass

async def crc7_buff(crc, buf):
    c = crc & 0x7F
    for b in buf: c = CRC7_TABLE[((2 * (c & 0xFF)) ^ (b & 0xFF)) & 0xFF] & 0x7F
    return c & 0x7F

async def tea_enc(v0, v1, k0, k1, k2, k3):
    s = 0; _DELTA = 0x9E3779B9
    for _ in range(16):
        s = (s + _DELTA) & 0xFFFFFFFF
        v0 = (v0 + ((((v1 << 4) & 0xFFFFFFFF) + k0) & 0xFFFFFFFF
                    ^ ((v1 + s) & 0xFFFFFFFF)
                    ^ (((v1 >> 5) + k1) & 0xFFFFFFFF))) & 0xFFFFFFFF
        v1 = (v1 + ((((v0 << 4) & 0xFFFFFFFF) + k2) & 0xFFFFFFFF
                    ^ ((v0 + s) & 0xFFFFFFFF)
                    ^ (((v0 >> 5) + k3) & 0xFFFFFFFF))) & 0xFFFFFFFF
    return v0, v1

async def tea_dec(v0, v1, k0, k1, k2, k3):
    _DELTA = 0x9E3779B9
    s = (_DELTA * 16) & 0xFFFFFFFF
    for _ in range(16):
        v1 = (v1 - ((((v0 << 4) & 0xFFFFFFFF) + k2) & 0xFFFFFFFF
                    ^ ((v0 + s) & 0xFFFFFFFF)
                    ^ (((v0 >> 5) + k3) & 0xFFFFFFFF))) & 0xFFFFFFFF
        v0 = (v0 - ((((v1 << 4) & 0xFFFFFFFF) + k0) & 0xFFFFFFFF
                    ^ ((v1 + s) & 0xFFFFFFFF)
                    ^ (((v1 >> 5) + k1) & 0xFFFFFFFF))) & 0xFFFFFFFF
        s = (s - _DELTA) & 0xFFFFFFFF
    return v0, v1

async def tea_cbc_encrypt(padded, kb):
    k0,k1,k2,k3 = (struct.unpack_from("<I", kb, o)[0] for o in (0,4,8,12))
    out = bytearray(len(padded)); pc = bytearray(8); pi = bytearray(8)
    for i in range(0, len(padded), 8):
        x = bytearray(8)
        for j in range(8): x[j] = padded[i+j] ^ pc[j]
        e0, e1 = await tea_enc(struct.unpack_from("<I", x, 0)[0],
                               struct.unpack_from("<I", x, 4)[0], k0,k1,k2,k3)
        en = bytearray(8)
        struct.pack_into("<I", en, 0, e0); struct.pack_into("<I", en, 4, e1)
        for j in range(8): out[i+j] = en[j] ^ pi[j]
        pc[:] = out[i:i+8]; pi[:] = x
    return bytes(out)

async def tea_cbc_decrypt(body, kb):
    k0,k1,k2,k3 = (struct.unpack_from("<I", kb, o)[0] for o in (0,4,8,12))
    out = bytearray(len(body)); pi = bytearray(8); pc = bytearray(8)
    x = bytearray(8); d = bytearray(8)
    for i in range(0, len(body), 8):
        for j in range(8): x[j] = body[i+j] ^ pi[j]
        d0, d1 = await tea_dec(struct.unpack_from("<I", x, 0)[0],
                               struct.unpack_from("<I", x, 4)[0], k0,k1,k2,k3)
        struct.pack_into("<I", d, 0, d0); struct.pack_into("<I", d, 4, d1)
        for j in range(8): out[i+j] = d[j] ^ pc[j]
        pc[:] = body[i:i+8]; pi[:] = d
    return bytes(out)

async def build_padded(content):
    pl = (8 - (len(content) + 10) % 8) % 8
    return bytes([pl, 0, 0]) + b"\x00" * pl + content + b"\x00" * 7

async def oicq_unpad(padded):
    if not padded or len(padded) < 8: return None
    if not all(padded[-1-i] == 0 for i in range(7)): return None
    pl = padded[0] & 0x07
    s = 3 + pl; e = len(padded) - 7
    return padded[s:e] if s < e else b""

async def layouts_from_mask(mask):
    s = str(mask).strip()
    try: ru = [int(c) for c in s]
    except ValueError: ru = [0,1,2,3,4]
    if sorted(ru) != [0,1,2,3,4]: ru = [0,1,2,3,4]
    return ru, [c for c in ru if c != 2]

async def build_packet(msg_key, layout, so, cmd, oid, flags, content, key, encrypted=True):
    k = key[0]; v80 = ((k << 8) | k) & 0xFFFF
    body = await tea_cbc_encrypt(await build_padded(content), key) if encrypted else content
    hdr = bytearray([msg_key, 0])
    for code in layout:
        value = {0:so,1:cmd,2:oid,3:flags,4:len(body)}[code]
        if _FIELD_SIZES[code] == 1: hdr.append((value & 0xFF) ^ k)
        else:
            v = ((value & 0xFFFF) ^ v80) & 0xFFFF
            hdr.append(v & 0xFF); hdr.append((v >> 8) & 0xFFFF)
    pkt = bytearray(hdr + body)
    pkt[1] = await crc7_buff(0, bytes(pkt[2:])) & 0x7F
    return bytes(pkt)

async def build_hello_packet(text, key, layout):
    data = text.encode("utf-8")[:25]
    content = len(data).to_bytes(4, "little") + data + b"\x00" * 9
    k = key[0]; v80 = ((k << 8) | k) & 0xFFFF
    layout = [int(c) for c in str(layout).strip()]
    eb = await tea_cbc_encrypt(await build_padded(content), key)
    hdr = bytearray([0x63, 0x00])
    for code in layout:
        value = {0:1, 1:1, 2:0, 3:1, 4:len(eb)}[code]
        if _FIELD_SIZES[code] == 1: hdr.append((value & 0xFF) ^ k)
        else:
            v = ((value & 0xFFFF) ^ v80) & 0xFFFF
            hdr.append(v & 0xFF); hdr.append((v >> 8) & 0xFFFF)
    pkt = bytearray(hdr + eb)
    pkt[1] = await crc7_buff(0, bytes(pkt[2:])) & 0x7F
    return bytes(pkt).hex()

def _put_string(out, s):
    raw = s.encode("utf-8") if isinstance(s, str) else s
    _put_zigvarint(out, len(raw)); out += raw

def build_join_info_head(account_id, game_mode=15, match_mode=1, map_id=1,
                         country="IN", client_version="1.132.9",
                         client_version_code="2019121229",
                         client_url=("csoversea.stronghold.freefiremobile.com;"
                                     "0.0.0.0;34.126.76.45;34.87.177.14;"
                                     "34.87.170.230;35.185.183.57"),
                         room_id=0, match_id=0,
                         enable_antihack_tick=1, friend_count=0,
                         client_ip="", session_tag=0, is_emulator=1):
    room = int(match_id or room_id)
    b = bytearray()
    _put_varint(b, int(account_id)); _put_varint(b, room)
    b.append(1); b.append(int(game_mode) & 0xFF); _put_varint(b, room)
    b.append(int(map_id) & 0xFF); b.append(0)
    _put_varint(b, 0); _put_varint(b, 0); b.append(0); b.append(int(is_emulator) & 0xFF)
    b.append(0); b.append(1); b.append(2); b.append(3)
    b.append(int(enable_antihack_tick) & 0xFF); b.append(1)
    _put_string(b, country); _put_varint(b, 0)
    b.append(1); b.append(2); b.append(0); b.append(1); b.append(0); b.append(0); b.append(4)
    _put_string(b, client_version); _put_string(b, client_version_code); _put_string(b, client_url)
    b.append(0); b.append(0)
    _put_varint(b, int(friend_count)); b.append(0)
    _put_varint(b, 0); _put_string(b, "")
    b.append(1); _put_string(b, ""); _put_string(b, ""); b.append(0)
    _put_varint(b, 0); _put_varint(b, 0); b.append(0); b.append(0); b.append(0)
    _put_varint(b, 0); _put_string(b, ""); _put_varint(b, 0)
    b.append(0); b.append(1); b.append(0); b.append(0)
    _put_varint(b, 0); _put_varint(b, 0); b.append(0); b.append(1)
    _put_string(b, ""); _put_varint(b, 0); b.append(0); b.append(0); b.append(0)
    b.append(int(match_mode) & 0xFF); b.append(0)
    _put_varint(b, int(session_tag)); b.append(2); b.append(0)
    _put_string(b, client_ip or ""); _put_string(b, "")
    return bytes(b)

def build_join_post_body(account_id, token_part2, **kw):
    body = bytearray(); body += build_join_info_head(account_id, **kw)
    _put_string(body, token_part2); return bytes(body)

async def build_join_match_startup(jt, uk, mc, aid, bv, server_ip="", region="BD",
                                   cv="1.132.9", cvc="2019121229",
                                   at="", mid=0, cc="IN", map_id=1, gm=15, mm=1):
    jt = jt.strip(); ukb = bytes.fromhex(uk)
    mc = [int(c) for c in str(mc).strip()]
    et = jt.encode("utf-8") if isinstance(jt, str) else jt
    p1, p2 = split_token_bytes(et)
    pb = bytearray(); _put_string(pb, p1)
    prep = (await build_packet(0x5E, mc, 2, 447, 0, 1, bytes(pb), ukb)).hex()
    post_body = build_join_post_body(
        aid, p2, game_mode=gm, match_mode=mm, map_id=map_id,
        country=cc, client_version=cv, client_version_code=cvc,
        match_id=int(mid or bv),
        client_ip=server_ip.split(":")[0] if server_ip else "")
    post = await build_packet(0x5A, mc, 2, 448, 1, 1, post_body, ukb)
    return [prep], post.hex()

HDR_RELIABLE = 10
UDP_HEAD_AND_ENCRY_SIZE = 40
MTU_LIMIT = 1300

def _tea_encrypt_len(n):
    t = 1 + 2 + n + 7; r = t % 8
    return t + (8 - r if r else 0)
def _dg_size(tl, reliable=True):
    zv = bytearray(); _put_zigvarint(zv, tl)
    body = len(zv) + tl
    return (HDR_RELIABLE if reliable else 8) + _tea_encrypt_len(body)
def split_token_bytes(tb):
    n = len(tb); raw = int(n * 0.85); p1 = raw - (raw % 40)
    while UDP_HEAD_AND_ENCRY_SIZE + _dg_size(p1) > MTU_LIMIT and p1 > 40: p1 -= 40
    return tb[:p1], tb[p1:]

async def decode_packet(packet, key, mask=None):
    import itertools
    data = bytes(packet) if isinstance(packet, bytes) else bytes.fromhex(packet)
    if len(data) < 8: return None
    k = key[0]; v80 = ((k << 8) | k) & 0xFFFF
    crc_ok = (data[1] & 0x7F) == await crc7_buff(0, data[2:])
    if mask:
        ru, nr = await layouts_from_mask(mask)
        layouts = [("RUDP", ru), ("nonRUDP", nr)]
    else:
        layouts = [("RUDP", list(p)) for p in itertools.permutations([0,1,2,3,4])]
        layouts += [("nonRUDP", list(p)) for p in itertools.permutations([0,1,3,4])]
    cands = []
    for kind, layout in layouts:
        off = 2; f = {}; ok_ = True
        for code in layout:
            size = _FIELD_SIZES[code]
            if off + size > len(data): ok_ = False; break
            f[_FIELD_NAMES[code]] = (data[off] ^ k) if size == 1 else \
                ((data[off] | (data[off+1] << 8)) ^ v80) & 0xFFFF
            off += size
        if not ok_: continue
        if f["flags"] > 7 or f["sendOption"] > 7: continue
        if f["length"] != len(data) - off: continue
        body = data[off:off+f["length"]]
        content = None
        if f["flags"] & 1:
            if len(body) < 8 or len(body) % 8 != 0: continue
            content = await oicq_unpad(await tea_cbc_decrypt(body, key))
            if content is None: continue
        else: content = body
        score = (1 if crc_ok else 0) + (1 if content is not None else 0)
        cands.append({"kind":kind,"layout":layout,"headerLen":off,"msgKey":data[0],
                      "cmd":f["cmd"],"flags":f["flags"],
                      "orderId":f.get("orderId"),"length":f["length"],
                      "content":content,"crcOk":crc_ok,"score":score})
    if not cands: return None
    cands.sort(key=lambda c: c["score"], reverse=True)
    return cands[0]

def collect_all_ints(obj, out):
    if isinstance(obj, dict):
        if "data" in obj and isinstance(obj["data"], int): out.add(obj["data"])
        for v in obj.values(): collect_all_ints(v, out)
    elif isinstance(obj, list):
        for x in obj: collect_all_ints(x, out)
    elif isinstance(obj, int): out.add(obj)

def _match_info_from_frame(ptype, cmd, decoded):
    if not isinstance(decoded, dict): return None
    if not ((ptype == 0x03 and cmd == 5) or (ptype == 0x11 and cmd == 3)): return None
    r5 = decoded.get("5") or {}
    if not isinstance(r5, dict): return None
    for k in ("2","3","4","42"):
        v = r5.get(k)
        if isinstance(v, dict): r5[k] = v.get("data")
    if (isinstance(r5.get("2"), str) and ":" in r5["2"]
            and isinstance(r5.get("3"), str)
            and isinstance(r5.get("4"), str)
            and r5.get("42")):
        r5["42"] = str(r5["42"]); return r5
    return None

# ═══════════════════════════════════════════════════════════════════
# MASTER / SLAVE
# ═══════════════════════════════════════════════════════════════════
async def master_loop(acct, slave_ids, holder, match_infos, squad_n):
    tag = acct["tag"]
    ip, port = acct["game_server"].split(":")
    key, iv = acct["key"], acct["iv"]
    jwt = acct["jwt"]; aid = int(acct["ingame_id"]); ts = acct["ts"]
    slave_set = {int(x) for x in slave_ids}
    rv = acct["cfg"].get("remote_version", Play_Version)
    auth_online = await build_auth_packet(aid, jwt, ts, key, iv, REGION, "OnLine")
    ka_bytes = await send_keep_alive(REGION)
    reader, writer = await asyncio.open_connection(ip, int(port))
    writer.write(auth_online); await writer.drain()
    writer.write(ka_bytes); await writer.drain()
    await asyncio.sleep(1.5)
    ka_stop = asyncio.Event()
    async def ka_loop():
        while not ka_stop.is_set():
            try:
                await asyncio.sleep(15)
                writer.write(ka_bytes); await writer.drain()
            except Exception: return
    ka_task = asyncio.create_task(ka_loop())
    for attempt in range(3):
        try:
            c = br_create_squad_pkt(REGION, rv, key, iv)
            writer.write(c); await writer.drain()
            squad_line(squad_n, f"master creating squad (attempt {attempt+1})…")
            await asyncio.sleep(1.0)
        except Exception as e:
            squad_err(squad_n, f"create attempt {attempt+1}: {e}")
            await asyncio.sleep(2.0)
    created = False; op31_sent = False; buf = bytearray()

    async def start_watcher():
        try: await asyncio.wait_for(holder["team_code_ready"].wait(), 30)
        except asyncio.TimeoutError:
            squad_err(squad_n, "no team code — retrying")
            try:
                c = br_create_squad_pkt(REGION, rv, key, iv)
                writer.write(c); await writer.drain()
            except Exception: pass
            return
        squad_ok(squad_n, "team code received")
        t0 = time.time()
        while time.time() - t0 < 30:
            if holder["slave_joined"] >= slave_set: break
            await asyncio.sleep(0.4)
        squad_line(squad_n, f"{len(holder['slave_joined'])}/{len(slave_set)} joined")
        await asyncio.sleep(SETTLE_AFTER_ALL_JOIN)
        s = br_start_squad_pkt(aid, REGION, key, iv)
        try:
            writer.write(s); await writer.drain()
            squad_line(squad_n, "starting matchmaking…")
        except Exception as e: squad_err(squad_n, f"start err: {e}")
    start_task = asyncio.create_task(start_watcher())
    loop_deadline = time.time() + 1800
    try:
        while True:
            if time.time() > loop_deadline: break
            try:
                chunk = await asyncio.wait_for(reader.read(65536), timeout=30)
            except asyncio.TimeoutError: continue
            except Exception: break
            if not chunk: break
            buf.extend(chunk)
            while len(buf) >= 5:
                ptype = buf[0]; plen = int.from_bytes(buf[1:5], "big")
                if plen > 100_000: buf.clear(); break
                if len(buf) < 5 + plen: break
                payload = bytes(buf[5:5+plen]); del buf[:5+plen]
                decoded = None
                try: decoded = await t_decode_packet(payload.hex())
                except Exception: pass
                cmd = decoded.get("4") if isinstance(decoded, dict) else None
                if ptype == 0x05 and isinstance(decoded, dict):
                    data = decoded.get("5", {})
                    if cmd == 1 and not created and plen >= 100:
                        gid = None
                        if isinstance(data, dict):
                            g = data.get("1")
                            if isinstance(g, dict): g = g.get("data")
                            if isinstance(g, int): gid = g
                        created = True; holder["group_id"] = gid; holder["master_id"] = aid
                        squad_ok(squad_n, f"squad created (gid={gid})")
                    elif cmd == 32 and not holder["team_code"]:
                        tc_val = None
                        if isinstance(data, dict):
                            t = data.get("1")
                            if isinstance(t, dict): t = t.get("data")
                            if isinstance(t, (str, int)): tc_val = str(t)
                        if tc_val is None:
                            t = decoded.get("1")
                            if isinstance(t, dict): t = t.get("data")
                            if isinstance(t, (str, int)): tc_val = str(t)
                        if tc_val:
                            holder["team_code"] = tc_val; holder["team_code_ready"].set()
                    if created and not op31_sent and holder["group_id"]:
                        op31_sent = True
                        try:
                            p31 = await send_op31(holder["group_id"], REGION, key, iv)
                            writer.write(p31); await writer.drain()
                        except Exception: pass
                    if cmd == 6:
                        found = set(); collect_all_ints(decoded, found)
                        newj = found & slave_set
                        for sid in newj: holder["slave_joined"].add(sid)
                    elif cmd == 10:
                        squad_ok(squad_n, "match accepted — flying in")
                elif ptype == 0x11 and cmd == 5 and not holder["team_code"]:
                    data = decoded.get("5", {}) if isinstance(decoded, dict) else {}
                    tc_val = None
                    if isinstance(data, dict):
                        t = data.get("11")
                        if isinstance(t, dict): t = t.get("data")
                        if isinstance(t, (str, int)) and str(t).isdigit() and len(str(t)) >= 5:
                            tc_val = str(t)
                    if tc_val:
                        holder["team_code"] = tc_val; holder["team_code_ready"].set()
                minfo = _match_info_from_frame(ptype, cmd, decoded)
                if minfo is not None and tag not in match_infos:
                    match_infos[tag] = minfo
                    squad_ok(squad_n, "MATCH FOUND")
                    dbg("MATCH", f"{tag} match_info ip={minfo.get('2')}")
    finally:
        start_task.cancel()
        try: await start_task
        except asyncio.CancelledError: pass
        ka_stop.set(); ka_task.cancel(); writer.close()
        try: await writer.wait_closed()
        except Exception: pass

async def slave_loop(acct, holder, match_infos, stop_evt, squad_n):
    tag = acct["tag"]
    ip, port = acct["game_server"].split(":")
    key, iv = acct["key"], acct["iv"]
    jwt = acct["jwt"]; aid = int(acct["ingame_id"]); ts = acct["ts"]
    auth_online = await build_auth_packet(aid, jwt, ts, key, iv, REGION, "OnLine")
    ka_bytes = await send_keep_alive(REGION)
    rv = acct["cfg"].get("remote_version", Play_Version)
    outer_deadline = time.time() + 1800
    while not stop_evt.is_set():
        try:
            if time.time() > outer_deadline: break
            reader, writer = await asyncio.open_connection(ip, int(port))
            writer.write(auth_online); await writer.drain()
            writer.write(ka_bytes); await writer.drain()
            await asyncio.sleep(1.0)
            ka_stop = asyncio.Event()
            async def ka_loop():
                while not ka_stop.is_set():
                    try:
                        await asyncio.sleep(15)
                        writer.write(ka_bytes); await writer.drain()
                    except Exception: return
            ka_task = asyncio.create_task(ka_loop())
            try: await asyncio.wait_for(holder["team_code_ready"].wait(), 45)
            except asyncio.TimeoutError:
                ka_stop.set(); ka_task.cancel(); writer.close(); continue
            tc = holder["team_code"]
            for attempt in range(3):
                j = br_join_team_pkt(tc, REGION, rv, key, iv)
                writer.write(j); await writer.drain()
                await asyncio.sleep(0.8)
            joined = False; js = time.time(); buf = bytearray()
            inner_deadline = time.time() + 1800
            while not stop_evt.is_set():
                if time.time() > inner_deadline: break
                try:
                    chunk = await asyncio.wait_for(reader.read(65536), timeout=1.0)
                except asyncio.TimeoutError:
                    if not joined and time.time() - js > 8:
                        joined = True; holder["slave_joined"].add(aid)
                        squad_ok(squad_n, f"{tag} joined")
                    continue
                except Exception: break
                if not chunk: break
                buf.extend(chunk)
                while len(buf) >= 5:
                    ptype = buf[0]; plen = int.from_bytes(buf[1:5], "big")
                    if plen > 100_000 or len(buf) < 5 + plen: break
                    payload = bytes(buf[5:5+plen]); del buf[:5+plen]
                    decoded = None
                    try: decoded = await t_decode_packet(payload.hex())
                    except Exception: pass
                    cmd = decoded.get("4") if isinstance(decoded, dict) else None
                    if ptype == 0x05 and plen >= 200 and not joined:
                        joined = True; holder["slave_joined"].add(aid)
                    if ptype == 0x05 and isinstance(decoded, dict) and cmd == 10:
                        squad_ok(squad_n, f"{tag} match accepted")
                    minfo = _match_info_from_frame(ptype, cmd, decoded)
                    if minfo is not None and tag not in match_infos:
                        match_infos[tag] = minfo
            ka_stop.set(); ka_task.cancel(); writer.close()
            try: await writer.wait_closed()
            except Exception: pass
            if stop_evt.is_set(): break
        except Exception: await asyncio.sleep(2.0)

# ═══════════════════════════════════════════════════════════════════
# PLAY GAME
# ═══════════════════════════════════════════════════════════════════
async def play_game(sipp, prep_pkts, post_pkt, uk, mc, aid, tag, squad_n,
                    account_jwt="", sleep_ms=0, team_uids=None, result_box=None,
                    bot_index=0):
    match_start = time.time()
    ping_task = hello_task = movement_task = sock = None
    ping_stop = asyncio.Event()
    movement_stop = asyncio.Event()
    state = MovementState(aid, team_uids=team_uids, bot_index=bot_index)
    try:
        ip, port = sipp.split(":"); port = int(port)
        rip = socket.gethostbyname(ip)
        loop = asyncio.get_event_loop()
        sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        optimize_udp_socket(sock); sock.setblocking(False)
        ukb = bytes.fromhex(uk)
        remote = (rip, port)
        gap = sleep_ms / 1000.0 if sleep_ms else 0.02
        if account_jwt:
            await loop.sock_sendto(sock, build_auth_datagram(account_jwt, aid), remote)
        hello_hex = await build_hello_packet(f"{aid}_2585", ukb, mc)
        hello_bytes = bytes.fromhex(hello_hex)
        await loop.sock_sendto(sock, hello_bytes, remote)
        squad_line(squad_n, f"{tag} connecting… (INSIDE formation)")
        ack_state = "waiting_for_hello_reply"
        startup_sent = False; local_closed = False
        send_lock = asyncio.Lock()
        nr = (await layouts_from_mask(mc))[1]

        async def ka_loop():
            pklist = [0x66,0x6D,0x69,0x6C,0x6B,0x6E,0x6F,0x70]; i = 0
            while not ping_stop.is_set():
                if ack_state != "waiting_for_hello_reply": break
                try: await asyncio.wait_for(ping_stop.wait(), timeout=0.1)
                except asyncio.TimeoutError: pass
            while not ping_stop.is_set():
                pk = pklist[i % len(pklist)]
                cnt = int(time.time()*1000) & 0xFFFFFFFF
                pkt = await build_packet(pk, nr, 0, 3, None, 0,
                                         cnt.to_bytes(4,"little") + b"\x00\x00\x00",
                                         ukb, encrypted=False)
                try: await loop.sock_sendto(sock, pkt, remote)
                except Exception: pass
                i += 1
                try: await asyncio.wait_for(ping_stop.wait(), timeout=3.0)
                except asyncio.TimeoutError: pass

        async def hello_retry_loop():
            for _ in range(8):
                if ping_stop.is_set() or ack_state != "waiting_for_hello_reply": return
                try: await asyncio.wait_for(ping_stop.wait(), timeout=0.8)
                except asyncio.TimeoutError: pass
                if ping_stop.is_set() or ack_state != "waiting_for_hello_reply": return
                try: await loop.sock_sendto(sock, hello_bytes, remote)
                except Exception: pass

        ping_task = asyncio.create_task(ka_loop())
        hello_task = asyncio.create_task(hello_retry_loop())

        movement_task = asyncio.create_task(
            movement_loop(sock, remote, ukb, mc, state, movement_stop, squad_n, tag)
        )
        squad_ok(squad_n, f"{tag} movement active (INSIDE + orbit + skill)")

        async def send_join():
            nonlocal ack_state, startup_sent
            if startup_sent: return
            async with send_lock:
                if startup_sent: return
                for p in prep_pkts:
                    await loop.sock_sendto(sock, bytes.fromhex(p), remote)
                    await asyncio.sleep(gap)
                await asyncio.sleep(gap)
                await loop.sock_sendto(sock, bytes.fromhex(post_pkt), remote)
                startup_sent = True; ack_state = "startup_sent"

        while not local_closed:
            if time.time() - match_start > 1800: break
            try:
                resp, sa = await asyncio.wait_for(loop.sock_recvfrom(sock, 65535), timeout=1.5)
                if resp:
                    frame = await decode_packet(resp, ukb, mc)
                    if frame:
                        cmd = frame.get('cmd'); oid = frame.get('orderId')
                        mk = frame.get('msgKey', 0); content = frame.get('content')

                        if content and cmd in (2001, CMD_USE_ACTIVE_SKILL, CMD_PLAYER_JOIN,
                                              CMD_OTHER_STATES, CMD_OTHER_STATES_2014,
                                              CMD_SERVER_TIME, CMD_GRI_SYNC, CMD_SAFE_ZONE,
                                              CMD_QUICK_CHAT, CMD_DEAD):
                            dbg_check_ban(cmd, content, tag)
                            dispatch_incoming(cmd, content, state, squad_n, tag)

                        if cmd == CMD_USE_ACTIVE_SKILL and content:
                            try:
                                state.homer.mark_accepted()
                            except Exception: pass

                        if mk < 100 and oid is not None:
                            da = await build_packet(0x68, nr, 0, 2, None, 1,
                                                    ((oid + 1) & 0xFFFF).to_bytes(2, "little"), ukb)
                            await loop.sock_sendto(sock, da, sa)
                        if cmd == 1 and ack_state == "waiting_for_hello_reply":
                            ack_state = "ready_to_send_startup"
                        elif cmd == 3:
                            c = content or b""
                            cnt = c[:4] if len(c) >= 4 else c
                            rp = await build_packet(0x6D, nr, 0, 3, None, 0,
                                                    cnt + b"\x00\x00\x00", ukb, False)
                            await loop.sock_sendto(sock, rp, sa)
                        elif cmd == 130:
                            squad_ok(squad_n, f"{tag} in match")
                        elif cmd == 103:
                            squad_line(squad_n, f"{tag} match ended", MG, "★")
                            local_closed = True
            except asyncio.TimeoutError: pass
            except Exception as e:
                _udp_log(f"{tag} udp err: {e}"); await asyncio.sleep(0.5)
            if ack_state == "ready_to_send_startup" and not startup_sent:
                await send_join()
    except Exception as e:
        squad_err(squad_n, f"{tag} fatal: {e}")
        dbg("ERROR", f"{tag} play_game: {e}")
    finally:
        ping_stop.set()
        movement_stop.set()
        if movement_task:
            movement_task.cancel()
            try: await movement_task
            except (asyncio.CancelledError, Exception): pass
        for t in (ping_task, hello_task):
            if t: t.cancel()
        if sock:
            try: sock.close()
            except Exception: pass
        if result_box is not None:
            result_box[tag] = {
                "fires": state.homer.fire_count,
                "enemies_seen": len(state.enemies_seen),
                "team_skipped": state.team_skipped,
                "target_changes": state.target_changes,
                "stuck": state.stuck_count,
                "orbit": state.orbit_active,
                "skills": dict(state.homer.skill_used),
            }

# ═══════════════════════════════════════════════════════════════════
# LOGIN-ONCE + MATCH LOOP
# ═══════════════════════════════════════════════════════════════════
async def login_all_once(accounts, squad_idx=0):
    info("═" * 50)
    info("STEP 1: LOGIN ALL ACCOUNTS (one-time)")
    info("═" * 50)
    login_sem = asyncio.Semaphore(4)
    async def _login(rec, tag):
        async with login_sem:
            try:
                return await login_new_account(rec, tag)
            except Exception as e:
                squad_err(squad_idx, f"{tag} login failed: {e}")
                return None
    tasks = []
    for i, rec in enumerate(accounts):
        tag = f"[{rec.get('uid','?')[:8]}]"
        tasks.append(asyncio.create_task(_login(rec, tag)))
    results = await asyncio.gather(*tasks, return_exceptions=True)
    logged = [r for r in results if isinstance(r, dict) and r is not None]
    if len(logged) < 4:
        err(f"only {len(logged)}/4 logged in")
    else:
        ok(f"✓ {len(logged)} accounts logged in (reusable)")
    return logged

async def run_match_once(logged, match_no):
    squad_n = match_no
    for acct in logged:
        try: await refresh_game_server(acct)
        except Exception as e: dbg("ERROR", f"{acct['tag']} refresh: {e}")

    master = logged[0]; slaves = logged[1:4]
    ids = [int(s["ingame_id"]) for s in slaves]
    team_uids = [int(a["ingame_id"]) for a in logged]
    squad_ok(squad_n, f"master id={master['ingame_id']} · {len(slaves)} slaves")
    squad_line(squad_n, f"TEAM uids = {team_uids}")
    holder = {"group_id": None, "team_code": None,
              "team_code_ready": asyncio.Event(),
              "slave_joined": set(), "master_id": None}
    match_infos = {}
    slave_stop = asyncio.Event()
    slave_tasks = [asyncio.create_task(slave_loop(s, holder, match_infos, slave_stop, squad_n))
                   for s in slaves]
    await asyncio.sleep(2.0)
    master_task = asyncio.create_task(master_loop(master, ids, holder, match_infos, squad_n))
    expected = [a["tag"] for a in logged]
    deadline = time.time() + 180
    while time.time() < deadline:
        if all(t in match_infos for t in expected): break
        await asyncio.sleep(0.5)
    missing = [t for t in expected if t not in match_infos]
    if missing:
        squad_err(squad_n, f"missing match_info for {missing}")
        slave_stop.set()
        for t in slave_tasks + [master_task]: t.cancel()
        try: await asyncio.gather(*slave_tasks, master_task, return_exceptions=True)
        except Exception: pass
        return False
    squad_ok(squad_n, "all got match_info — deploying")
    result_box = {}
    udp_tasks = []
    for bi, a in enumerate(logged):
        r5 = match_infos[a["tag"]]
        def _u(v): return v.get("data") if isinstance(v, dict) else v
        mid  = _u(r5.get("1")) or 0
        map_ = _u(r5.get("6")) or 1
        gm   = _u(r5.get("7")) or 15
        mm   = _u(r5.get("8")) or 1
        sm   = _u(r5.get("5")) or 0
        prep, post = await build_join_match_startup(
            r5["4"], r5["3"], r5["42"], int(a["ingame_id"]), mid,
            server_ip=r5["2"], region=REGION,
            cv=a["cfg"].get("remote_version", Play_Version),
            cvc="2019121229", at=a["access_token"],
            mid=mid, cc="IN", map_id=map_, gm=gm, mm=mm)
        udp_tasks.append(asyncio.create_task(play_game(
            r5["2"], prep, post, r5["3"], r5["42"],
            int(a["ingame_id"]), tag=a["tag"], squad_n=squad_n,
            account_jwt=r5["4"], sleep_ms=sm,
            team_uids=team_uids, result_box=result_box,
            bot_index=bi)))
    tcp_tasks = slave_tasks + [master_task]
    try:
        squad_line(squad_n, "waiting for matches…")
        try:
            await asyncio.wait_for(asyncio.gather(*udp_tasks, return_exceptions=True), timeout=1800)
            squad_line(squad_n, "all matches done")
        except asyncio.TimeoutError:
            squad_warn(squad_n, "matches timed out")
        slave_stop.set()
        for t in tcp_tasks: t.cancel()
        try: await asyncio.gather(*tcp_tasks, return_exceptions=True)
        except Exception: pass
    finally:
        slave_stop.set()
        for t in tcp_tasks: t.cancel()
        try: await asyncio.gather(*tcp_tasks, return_exceptions=True)
        except Exception: pass
        squad_line(squad_n, "═══ MATCH SUMMARY ═══", MG, "★")
        for tag, r in result_box.items():
            squad_line(squad_n,
                f"{tag} fires={r['fires']} enemies={r['enemies_seen']} "
                f"team_skip={r['team_skipped']} target_chg={r['target_changes']} "
                f"stuck={r['stuck']} skills={r['skills']}", WH, "·")
            dbg("SUMMARY", f"{tag} fires={r['fires']} enemies_seen={r['enemies_seen']} "
                           f"team_skipped={r['team_skipped']} target_changes={r['target_changes']} "
                           f"stuck={r['stuck']} skills={r['skills']}")
        squad_ok(squad_n, f"match #{match_no} finished 🏁")
    return True

def _setup_region(region):
    global REGION, LANG_CODE, SERVER_URL, CLIENT_URL
    REGION = region
    LANG_CODE = REGION_LANG.get(region, "en")
    grp = REGION_GROUP.get(region, "OTHERS")
    SERVER_URL = REGION_URLS[grp]["server"]
    CLIENT_URL = REGION_URLS[grp]["client"]

async def main_async(args):
    global CFG, Play_Version, Ob_VeR
    _setup_region(args.region)
    info(f"Region: {REGION}")
    dbg("BOOT", f"region={REGION} args={vars(args)}")
    info("fetching version…")
    try:
        pv = get_play_store_version()
        CFG = fetch_ver_config(pv)
        Play_Version = CFG.get("remote_version", pv)
        Ob_VeR = CFG["latest_release_version"]
        ok(f"game version {Ob_VeR} (client {Play_Version})")
    except Exception as e:
        err(f"version fetch failed: {e}"); return

    if not args.clan:
        try:
            gid = input("\n  » Guild ID to join (blank = skip): ").strip()
            if gid: args.clan = gid
        except (EOFError, KeyboardInterrupt): print()
    if args.clan: info(f"Guild ID: {args.clan}")

    needed = args.squads * 4
    accounts = pop_accounts_from_available(needed, region=args.region)
    if len(accounts) < 4:
        err(f"not enough accounts (got {len(accounts)}/4)")
        if accounts: return_accounts_to_available(accounts)
        return
    squads_this = min(args.squads, len(accounts) // 4)
    leftovers = accounts[squads_this * 4:]
    if leftovers: return_accounts_to_available(leftovers)
    accounts = accounts[:squads_this * 4]
    running_uids = [r.get("uid") for r in accounts if r.get("uid")]
    ok(f"running set: {len(running_uids)} account(s)")

    if args.clan:
        await join_all_to_clan(accounts, args.clan)

    logged = await login_all_once(accounts, squad_idx=0)
    if len(logged) < 4:
        err(f"only {len(logged)}/4 logged in — aborting"); return

    info("═" * 50)
    info("STEP 2: MATCH LOOP (no re-login)")
    info("═" * 50)
    match_no = 0
    loop_start = time.time()
    max_matches = args.matches if args.matches > 0 else 0
    while time.time() - loop_start < RUN_TIME_LIMIT:
        if max_matches > 0 and match_no >= max_matches: break
        match_no += 1
        info(f"═══ MATCH #{match_no} ═══")
        try:
            await run_match_once(logged, match_no)
        except Exception as e:
            err(f"match #{match_no} crashed: {e}")
            dbg("ERROR", f"match #{match_no}: {e}\n{traceback.format_exc()}")
        ok(f"═══ MATCH #{match_no} finished ═══")
        if max_matches > 0 and match_no >= max_matches: break
        w = random.randint(REPLAY_DELAY_MIN, REPLAY_DELAY_MAX)
        action(f"waiting {w}s before match #{match_no+1}…")
        await asyncio.sleep(w)
    ok(f"loop finished · {match_no} match(es)")
    move_running_to_used([{"uid": u} for u in running_uids])

def main():
    p = argparse.ArgumentParser(description="Squad CS Bot — FINAL v3")
    p.add_argument("--region", default="IND", choices=REGION_LIST)
    p.add_argument("--squads", type=int, default=1)
    p.add_argument("--clan", default=None)
    p.add_argument("--matches", type=int, default=0)
    args = p.parse_args()
    print(f"\n{B}{MG}╔══════════════════════════════════════════════════════╗{R}")
    print(f"{B}{MG}║{R}  {WH}{B}SQUAD CS — FINAL v3 (INSIDE + ORBIT + FAST){R}  {B}{MG}║{R}")
    print(f"{B}{MG}╚══════════════════════════════════════════════════════╝{R}\n")
    print(f"  {GR}·{R} Region     : {CY}{args.region}{R}")
    print(f"  {GR}·{R} Squads     : {CY}{args.squads}{R}")
    print(f"  {GR}·{R} Clan ID    : {CY}{args.clan or 'none'}{R}")
    print(f"  {GR}·{R} Max matches: {CY}{args.matches or 'infinite'}{R}")
    print(f"  {GR}·{R} Speed      : {CY}9000 u/s (first-round style){R}")
    print(f"  {GR}·{R} Hz         : {CY}{SEND_HZ:.0f}{R}")
    print(f"  {GR}·{R} Skill CD   : {CY}{SKILL_COOLDOWN_SEC:.0f}s (instant){R}")
    print(f"  {GR}·{R} Target     : {CY}ENEMY-ONLY (unknown = enemy){R}")
    print(f"  {GR}·{R} Formation  : {CY}INSIDE each other (0 offset){R}")
    print(f"  {GR}·{R} Orbit      : {CY}{ORBIT_RADIUS:.0f}u radius around enemy{R}")
    print(f"  {GR}·{R} Debug      : {CY}{DEBUG_LOG_FILE}{R}\n")
    try:
        asyncio.run(main_async(args))
    except KeyboardInterrupt:
        warn("\nstopped")
    finally:
        dbg_close()

if __name__ == "__main__":
    main()