# t.me/RishantAPIs
from flask import Flask, request, jsonify, make_response
import os, sys, time, threading, json, random, requests, re, codecs, base64, hmac, hashlib, string, logging
from datetime import datetime, timezone
from Crypto.Cipher import AES
from Crypto.Util.Padding import pad
import urllib3
import concurrent.futures
import uuid
import ipaddress

urllib3.disable_warnings()

# ========== LOG ==========
logging.basicConfig(level=logging.INFO, format='%(asctime)s [%(levelname)s] %(message)s', stream=sys.stdout)
log = logging.getLogger("ffgen")

# ========== DEBUG SYSTEM ==========
_thread_local = threading.local()

def _safe(v):
    if v is None or isinstance(v, (str, int, float, bool)): return v
    if isinstance(v, (bytes, bytearray)):
        try: return v.decode("utf-8")
        except Exception: return bytes(v).hex()
    if isinstance(v, dict): return {str(k): _safe(x) for k, x in v.items()}
    if isinstance(v, (list, tuple, set)): return [_safe(x) for x in v]
    return str(v)

def _is_debug(): return bool(getattr(_thread_local, "debug_enabled", False))

def dbg(tag, **fields):
    if not _is_debug(): return
    payload = {"ts": datetime.now().isoformat()}
    payload.update({k: _safe(v) for k, v in fields.items()})
    try: line = json.dumps(payload, ensure_ascii=False)
    except Exception: line = str(payload)
    print(f"[DEBUG] {tag} :: {line}", flush=True)

# ========== CONFIG ==========
REGION_LANG = {"ME":"ar","IND":"hi","ID":"id","VN":"vi","TH":"th","BD":"bn","PK":"ur","TW":"zh","CIS":"ru","SAC":"es","BR":"pt"}
HEX_KEY = bytes.fromhex("32656534343831396539623435393838343531343130363762323831363231383734643064356437616639643866376530306331653534373135623764316533")
HEX_KEY_STR = HEX_KEY.decode()

OPT = {'timeout': (3, 5), 'retries': 0}
RARITY_SCORE_THRESHOLD = 8

FIXED_WORKERS      = 50  # Vercel limits ke liye optimize kiya gaya hai
TARGET_ACC_PER_SEC = 50.0
RELEASE_VER        = "OB55"
GAME_VERSION       = "2.132.4"

# ========== IP & DEVICE POOLS ==========
def _build_ip_pool():
    pool = set()
    ranges = [("1.", 100), ("5.", 100), ("14.", 100), ("27.", 100), ("36.", 100)]
    for pfx, cnt in ranges:
        for _ in range(cnt):
            ip_str = f"{pfx}{random.randint(0,255)}.{random.randint(0,255)}.{random.randint(1,254)}"
            pool.add(ip_str)
    pl = list(pool); random.shuffle(pl); return pl

IP_POOL = _build_ip_pool()

def pick_ip():
    if not IP_POOL:
        return f"{random.randint(1,223)}.{random.randint(0,255)}.{random.randint(0,255)}.{random.randint(1,254)}"
    return IP_POOL[random.randint(0, len(IP_POOL) - 1)]

def ip_headers():
    real = pick_ip()
    return {
        "X-Forwarded-For": real,
        "X-Real-IP": real,
        "CF-Connecting-IP": real,
    }

class DevicePool:
    _devices, _index, _lock = [], 0, threading.Lock()
    DEVICE_MODELS = [
        ("SM-A525F", "ARMv8 VFPv4 NEON VMH | 2200 | 8", "Adreno (TM) 618"),
        ("SM-S918B", "ARMv8 VFPv4 NEON VMH | 3200 | 8", "Adreno (TM) 740"),
        ("Redmi Note 10","ARMv8 VFPv4 NEON VMH | 2200 | 8","Adreno (TM) 619"),
    ]
    
    @classmethod
    def _rh(cls, n): return ''.join(random.choices("0123456789abcdef", k=n))
    @classmethod
    def _uuid(cls): return f"{cls._rh(8)}-{cls._rh(4)}-{cls._rh(4)}-{cls._rh(4)}-{cls._rh(12)}"
    @classmethod
    def _mac(cls):  return "02:" + ":".join(cls._rh(2) for _ in range(5))

    @classmethod
    def init_pool(cls, count=100):
        if cls._devices: return
        for _ in range(count):
            model, cpu, gpu = random.choice(cls.DEVICE_MODELS)
            dev = {
                "model": model, "brand": model.split()[0], "cpu": cpu, "gpu": gpu,
                "android_full": "Android OS 13 / API-33", "android_version": "13", "api_level": "33",
                "operator": "Telkomsel", "network": "4G", "sdk": "4.0.39", "mac": cls._mac(),
                "device_id": cls._rh(32), "android_id": cls._rh(16), "uuid": cls._uuid(),
                "imei": cls._rh(15), "fingerprint": cls._rh(40), "gl_renderer": "OpenGL ES 3.2",
            }
            dev["_hdr"] = {
                "X-Device-Id": dev["device_id"], "X-Android-Id": dev["android_id"],
                "X-Device-Model": dev["model"],  "X-Device-Brand": dev["brand"],
            }
            dev["_gpu_full"] = f"{gpu}|OpenGL ES 3.2"
            cls._devices.append(dev)

    @classmethod
    def get(cls):
        with cls._lock:
            if not cls._devices: cls.init_pool(10)
            dev = cls._devices[cls._index % len(cls._devices)]
            cls._index += 1
            return dev

    @classmethod
    def headers(cls, device=None):
        d = device or cls.get()
        return d.get("_hdr") or {}

DevicePool.init_pool(100)

def get_thread_device():
    if not hasattr(_thread_local, "device"):
        _thread_local.device = DevicePool.get()
        _thread_local.dev_headers = _thread_local.device["_hdr"]
    return _thread_local.device

def get_thread_dev_headers():
    if not hasattr(_thread_local, "dev_headers"):
        _thread_local.device = DevicePool.get()
        _thread_local.dev_headers = _thread_local.device["_hdr"]
    return _thread_local.dev_headers

def reset_thread_session():
    s = getattr(_thread_local, "session", None)
    if s is not None: s.cookies.clear()

def get_thread_session():
    s = getattr(_thread_local, "session", None)
    if s is None:
        s = requests.Session()
        adapter = requests.adapters.HTTPAdapter(pool_connections=5, pool_maxsize=5, max_retries=0)
        s.mount("https://", adapter)
        s.mount("http://", adapter)
        s.verify = False
        _thread_local.session = s
    return s

def encode_f14(s):
    ks = [0x30]*32
    return bytes(ord(c) ^ ks[i % len(ks)] for i, c in enumerate(s))

FIELD_22 = bytes.fromhex("4747524501010100620200001052aa0d669c6a36")

USER_AGENTS_POOL = [
    "GarenaMSDK/4.0.39(SM-A325M;Android 13;en;HK;)",
    "GarenaMSDK/4.0.38(Redmi Note 10;Android 12;en;ID;)"
]
def random_ua(): return random.choice(USER_AGENTS_POOL)

def _merge_headers(headers, device=None, rotate_ip=False):
    if headers is None: headers = {}
    merged = dict(headers)
    dev_h = DevicePool.headers(device) if device is not None else get_thread_dev_headers()
    for k, v in dev_h.items():
        merged.setdefault(k, v)
    merged.update(ip_headers())
    return merged

def request_retry(method, url, tag="HTTP", **kwargs):
    sess = get_thread_session()
    try:
        kwargs.setdefault('timeout', OPT['timeout'])
        kwargs['headers'] = _merge_headers(kwargs.get('headers'), rotate_ip=False)
        kwargs['verify'] = False
        resp = sess.request(method, url, **kwargs)
        return resp
    except Exception:
        return None

def encode_varint(n):
    if n < 0: return b''
    result = []
    while True:
        byte = n & 0x7F; n >>= 7
        if n: byte |= 0x80
        result.append(byte)
        if not n: break
    return bytes(result)

def create_proto_field(field_num, value):
    if isinstance(value, dict):
        nested = create_proto_field(field_num, value)
        return encode_varint((field_num << 3) | 2) + encode_varint(len(nested)) + nested
    elif isinstance(value, int):
        return encode_varint((field_num << 3) | 0) + encode_varint(value)
    elif isinstance(value, (str, bytes)):
        ev = value.encode() if isinstance(value, str) else value
        return encode_varint((field_num << 3) | 2) + encode_varint(len(ev)) + ev
    return b''

def build_proto(fields):
    return b''.join(create_proto_field(k, v) for k, v in fields.items())

_AES_KEY = bytes([89,103,38,116,99,37,68,69,117,104,54,37,90,99,94,56])
_AES_IV  = bytes([54,111,121,90,68,114,50,50,69,51,121,99,104,106,77,37])

def aes_encrypt(hex_data):
    data = bytes.fromhex(hex_data)
    return AES.new(_AES_KEY, AES.MODE_CBC, _AES_IV).encrypt(pad(data, AES.block_size))

def encrypt_api(plain_hex):
    plain = bytes.fromhex(plain_hex)
    return AES.new(_AES_KEY, AES.MODE_CBC, _AES_IV).encrypt(pad(plain, AES.block_size)).hex()

def create_account(region, account_name, password_prefix):
    try:
        reset_thread_session()
        rand_part = "".join(random.choices("0123456789ABCDEF", k=16))
        password = f"{password_prefix}_{rand_part}"
        url = "https://100067.connect.garena.com/api/v2/oauth/guest:register"
        payload = {"app_id": 100067, "client_type": 2, "password": password, "source": 2}
        body_json = json.dumps(payload, separators=(",", ":"))
        signature = hmac.new(HEX_KEY, body_json.encode("utf-8"), hashlib.sha256).hexdigest()

        dev = get_thread_device()
        headers = _merge_headers({
            "User-Agent": random_ua(),
            "Authorization": f"Signature {signature}",
            "Content-Type": "application/json; charset=utf-8",
            "Host": "100067.connect.garena.com",
        }, device=dev)

        resp = request_retry('POST', url, tag="Register", headers=headers, data=body_json)
        if resp and resp.status_code == 200:
            res = resp.json()
            if "data" in res and "uid" in res["data"]:
                uid = str(res["data"]["uid"])
                return get_token(uid, password, region, account_name, password_prefix)
        return None
    except Exception:
        return None

def get_token(uid, password, region, account_name, password_prefix):
    try:
        url = "https://100067.connect.garena.com/oauth/guest/token/grant"
        dev = get_thread_device()
        headers = _merge_headers({
            "Content-Type": "application/x-www-form-urlencoded",
            "User-Agent": random_ua(),
        }, device=dev)
        body = {"uid": uid, "password": password, "response_type": "token",
                "client_type": "2", "client_secret": HEX_KEY_STR, "client_id": "100067"}

        resp = request_retry('POST', url, tag="Token", headers=headers, data=body)
        if resp and resp.status_code == 200 and 'open_id' in resp.json():
            j = resp.json()
            open_id = j['open_id']
            access_token = j["access_token"]
            encoded = "".join(chr(ord(open_id[i]) ^ 0x30) for i in range(len(open_id)))
            field = encoded.encode('latin1')
            return major_register(access_token, open_id, field, uid, password, region, account_name, password_prefix)
        return None
    except Exception:
        return None

def major_register(access_token, open_id, field, uid, password, region, account_name, password_prefix):
    try:
        url = ("https://loginbp.ppmainecoonghj.com/MajorRegister"
               if region.upper() not in ["ME","TH"]
               else "https://loginbp.common.ggbluefox.com/MajorRegister")
        name = generate_random_name(account_name)
        dev = get_thread_device()
        headers = _merge_headers({
            'User-Agent': 'UnityPlayer/2018.4.12f1',
            'Authorization': 'Bearer', 'X-GA': 'v1 1',
            'ReleaseVersion': RELEASE_VER,
            'Content-Type': 'application/x-www-form-urlencoded',
        }, device=dev)
        lang = REGION_LANG.get(region.upper(), "en")
        reg_msg = {1: name, 2: access_token, 3: open_id, 5: 102000007, 6: 4, 7: 1, 13: 1,
                    14: encode_f14(open_id), 15: lang, 16: 2, 20: GAME_VERSION, 21: 1, 22: FIELD_22}
        encrypted = aes_encrypt(build_proto(reg_msg).hex())

        request_retry('POST', url, tag="MajorRegister", headers=headers, data=encrypted)
        login_result = major_login(uid, password, access_token, open_id, region)
        account_id = login_result.get("account_id", "N/A")
        jwt_token  = login_result.get("jwt_token", "")
        if account_id != "N/A":
            return {
                "uid": uid, "password": password, "name": name, "region": region,
                "account_id": account_id, "jwt_token": jwt_token,
                "device_model": dev["model"], "device_id": dev["device_id"],
                "created_at": datetime.now().isoformat()
            }
        return None
    except Exception:
        return None

def major_login(uid, password, access_token, open_id, region):
    try:
        lang = REGION_LANG.get(region.upper(), "en")
        dev  = get_thread_device()
        payload_dict = {
            3:  datetime.utcnow().strftime('%Y-%m-%d %H:%M:%S'),
            4:  b'free fire', 5: 1, 7: GAME_VERSION, 8: dev["android_full"], 9: b'Handheld',
            10: dev["operator"], 11: dev["network"], 12: 1280, 13: 720, 14: b'240', 15: dev["cpu"],
            16: 6000, 17: dev["gpu"], 18: dev["_gpu_full"],
            19: f'Google|{dev["uuid"]}', 20: pick_ip(), 21: lang, 22: open_id.encode(),
            23: b'4', 24: b'Handheld', 25: dev["model"], 26: lang, 29: access_token.encode(),
            30: 1, 73: 1, 76: 2, 78: 2, 79: 1, 85: 3, 88: 4, 97: 1, 98: 1
        }
        data = build_proto(payload_dict)
        url = ("https://loginbp.ppmainecoonghj.com/MajorLogin"
               if region.upper() not in ["ME", "TH"]
               else "https://loginbp.common.ggbluefox.com/MajorLogin")

        headers = _merge_headers({
            'User-Agent': 'UnityPlayer/2018.4.12f1',
            'Authorization': 'Bearer', 'X-GA': 'v1 1',
            'ReleaseVersion': RELEASE_VER,
            'Content-Type': 'application/x-www-form-urlencoded',
        }, device=dev)

        enc_hex = encrypt_api(data.hex())
        resp = request_retry('POST', url, tag="MajorLogin", headers=headers, data=bytes.fromhex(enc_hex))

        if resp and resp.status_code == 200 and len(resp.text) > 10:
            jwt_start = resp.text.find("eyJ")
            if jwt_start != -1:
                jwt_token = resp.text[jwt_start:]
                second_dot = jwt_token.find(".", jwt_token.find(".") + 1)
                if second_dot != -1:
                    jwt_token = jwt_token[:second_dot + 44]
                    try:
                        parts = jwt_token.split('.')
                        if len(parts) >= 2:
                            pp = parts[1]
                            padding = 4 - len(pp) % 4
                            if padding != 4: pp += '=' * padding
                            claims = json.loads(base64.urlsafe_b64decode(pp))
                            account_id = claims.get('account_id') or claims.get('external_id')
                            if account_id:
                                return {"account_id": str(account_id), "jwt_token": jwt_token}
                    except Exception:
                        pass
        return {"account_id": "N/A", "jwt_token": ""}
    except Exception:
        return {"account_id": "N/A", "jwt_token": ""}

def generate_random_name(name_prefix):
    return name_prefix + ''.join(random.choices(string.ascii_letters + string.digits, k=6)).upper()

def check_rarity(account_data):
    account_id = account_data.get("account_id", "")
    if not account_id or account_id == "N/A": return False, None, None, 0
    return False, "NORMAL", "", 0

def generate_single_account(region, name_prefix, password_prefix):
    account_result = create_account(region, name_prefix, password_prefix)
    if not account_result or account_result.get("account_id", "N/A") == "N/A":
        return None
    account_result["rarity"] = "NORMAL"
    account_result["rarity_score"] = 0
    account_result["patterns"] = []
    account_result["rarity_reason"] = ""
    return account_result

# ========== FLASK APP ==========
app = Flask(__name__)
app.config['JSONIFY_PRETTYPRINT_REGULAR'] = False

@app.after_request
def after_request(response):
    response.headers.add('Access-Control-Allow-Origin', '*')
    response.headers.add('Access-Control-Allow-Headers', 'Content-Type,Authorization')
    response.headers.add('Access-Control-Allow-Methods', 'GET,OPTIONS')
    return response

@app.route('/', methods=['GET', 'OPTIONS'])
def index():
    if request.method == 'OPTIONS': return make_response('', 200)
    return jsonify({
        "message": "Free Fire Account Generator API — Fixed for Vercel & Local",
        "endpoint": "/v3/generate?count=5&name=User&password=Pass&region=ID",
        "status": "online"
    })

@app.route('/v3/generate', methods=['GET', 'OPTIONS'])
def generate_endpoint():
    if request.method == 'OPTIONS': return make_response('', 200)

    count    = request.args.get('count', default=1, type=int)
    name     = request.args.get('name', default='User', type=str)
    password = request.args.get('password', default='Pass', type=str)
    region   = request.args.get('region', default='ID', type=str).upper()

    if count < 1 or count > 50:  # Vercel timeout protection limit
        return jsonify({"error": "count must be between 1 and 50 for serverless limits"}), 400
    if region not in REGION_LANG:
        return jsonify({"error": f"invalid region, allowed: {list(REGION_LANG.keys())}"}), 400

    accounts = []
    for _ in range(count):
        acc = generate_single_account(region, name, password)
        if acc:
            accounts.append(acc)

    return jsonify({
        "success": True,
        "total_requested": count,
        "total_created": len(accounts),
        "accounts": accounts,
    })

if __name__ == "__main__":
    app.run(debug=False, threaded=True, host="0.0.0.0", port=6000)
