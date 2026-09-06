#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
FnNginxConf - nginx 配置注入引擎（复用 FnMusicEnhance/nginx_setup.py 的密码提取与 ZipCrypto 写 zip）

能力：
  - 从 nginx 二进制提取 ng.conf.zip 密码（ELF 解析，精确法 + 启发式回退）
  - ZipCrypto (PKWARE traditional) 加密写 zip；泛化的 read / write / upsert / remove 条目
  - 根据用户规则生成 conf.d/*.conf（防注入校验）
  - 路径冲突检测：不占用官方已有 location（保留命名空间 / 完全相等 / 子路径提示）
  - 应用编排：写 conf.d -> nginx -t 校验 -> 同步 zip -> 重启 trim_nginx（带回滚）
  - CLI 子命令：ensure / remove / print-conf
"""

import io
import json
import os
import re
import secrets
import shutil
import struct
import subprocess
import sys
import threading
import time
import zipfile
import zlib
from urllib.parse import urlsplit

# ---------------------------------------------------------------------------
# 常量 / 可配置路径（env 可覆盖，便于本地用本机 ng.conf/ 测试）
# ---------------------------------------------------------------------------

NGINX_BIN = os.environ.get("TRIM_NGINX_BIN", "/usr/trim/nginx/sbin/nginx")
NGINX_CONF = os.environ.get("TRIM_NGINX_CONF", "/usr/trim/nginx/conf/nginx.conf")
CONF_DIR = os.environ.get("TRIM_CONF_DIR", "/usr/trim/nginx/conf/conf.d")
RESTORE_ZIP = os.environ.get("TRIM_RESTORE_ZIP", "/usr/trim/share/.restore/ng.conf.zip")

CONF_NAME = "fnnginx_conf.conf"
ZIP_ENTRY = "conf.d/" + CONF_NAME
CONF_PATH = os.path.join(CONF_DIR, CONF_NAME)

# 系统保留命名空间：统一网关 / CGI（trim_http_cgi.conf 的 location /app/ 与 /cgi），
# 由系统动态管理，任何子路径都不允许用户占用
RESERVED_PREFIXES = ["/app", "/cgi"]

# recover 模块出错日志格式串, 用于精确定位 key 缓冲区
PWD_STR = b"archive_read_add_passphrase: %s, key: %s"

# 兜底密码: 在已知 x86-64 飞牛镜像上从 nginx 二进制提取并实测可用的密码。
# 当本机指令集无法抠取(如 arm64 RK3528A/ophub-fnnas)或抠出的密码无法解压时,
# 直接用它对 ng.conf.zip 重试, 实现不依赖抠二进制的注入方式。
FALLBACK_PASSWORD = b"4yXDSVzwVJuMZew2JqmmfMdu"

# location 解析：location [modifier] target
_LOC_RE = re.compile(r"(?m)^\s*location\s+(?:(\^~|=|~\*?)\s+)?([^\s{]+)")

# 正则 location 里终止字面前缀的元字符
_META = set(".^$*+?()[]{}|\\")

# 用户 location 禁止包含的字符（防指令注入）
_BAD_LOC = re.compile(r"[\s;{}#\"'`\\?\x00-\x1f]")

_HTTP_RE = re.compile(r"^(https?://[^\s;{}#\"'`\\]+)$", re.I)

_lock = threading.RLock()
_password_cache = None
_existing_cache = {"t": 0.0, "data": []}
_EXISTING_TTL = 3.0


def log(msg):
    line = "[%s] [nginx_cfg] %s\n" % (time.strftime("%Y-%m-%d %H:%M:%S"), msg)
    lf = os.environ.get("LOG_FILE", "")
    if lf:
        try:
            with open(lf, "a", encoding="utf-8", errors="replace") as f:
                f.write(line)
        except Exception:
            pass
    else:
        print(line, end="")


# ---------------------------------------------------------------------------
# 1) 从 nginx 二进制提取 ng.conf.zip 密码（原样来自 nginx_setup.py）
# ---------------------------------------------------------------------------

_CRC_TABLE = []
for _i in range(256):
    _c = _i
    for _ in range(8):
        _c = (_c >> 1) ^ 0xEDB88320 if _c & 1 else _c >> 1
    _CRC_TABLE.append(_c)


def _crc_update(crc, b):
    return (crc >> 8) ^ _CRC_TABLE[(crc ^ b) & 0xFF]


def _xor_pass(blob):
    return bytes(b ^ 0xAA for b in blob)


def _is_plausible(pw):
    """密码应为 24 字节, XOR 0xAA 后全为字母数字, 且非整段重复(填充区)。"""
    if len(pw) != 24:
        return False
    if not all(
        (c >= 0x41 and c <= 0x5A) or (c >= 0x61 and c <= 0x7A) or (c >= 0x30 and c <= 0x39)
        for c in pw
    ):
        return False
    if len(set(pw)) == 1:
        return False
    return True


def _elf_sections(data):
    """解析 ELF section headers -> {name: (file_offset, vaddr, size)}"""
    out = {}
    if len(data) < 0x40 or data[:4] != b"\x7fELF":
        return out
    e_shoff = struct.unpack_from("<Q", data, 0x28)[0]
    e_shentsize = struct.unpack_from("<H", data, 0x3A)[0]
    e_shnum = struct.unpack_from("<H", data, 0x3C)[0]
    e_shstrndx = struct.unpack_from("<H", data, 0x3E)[0]
    if e_shentsize < 64 or e_shoff + e_shnum * e_shentsize > len(data):
        return out
    str_off = struct.unpack_from("<Q", data, e_shoff + e_shstrndx * e_shentsize + 0x18)[0]
    for i in range(e_shnum):
        s = e_shoff + i * e_shentsize
        name_off = struct.unpack_from("<I", data, s)[0]
        end = data.find(b"\0", str_off + name_off)
        if end < 0:
            continue
        name = data[str_off + name_off:end].decode("utf-8", "replace")
        vaddr, off, size = struct.unpack_from("<QQQ", data, s + 0x10)
        out[name] = (off, vaddr, size)
    return out


def _file_to_vaddr(secs, off):
    for _, (soff, svaddr, ssize) in secs.items():
        if soff <= off < soff + ssize:
            return svaddr + (off - soff)
    return off


def _vaddr_to_off(secs, vaddr):
    for _, (soff, svaddr, ssize) in secs.items():
        if svaddr <= vaddr < svaddr + ssize:
            return soff + (vaddr - svaddr)
    return None


EM_X86_64 = 62
EM_AARCH64 = 183


def _elf_machine(data):
    """读 ELF e_machine: 62=x86-64, 183=AArch64。"""
    if len(data) < 0x14 or data[:4] != b"\x7fELF":
        return None
    return struct.unpack_from("<H", data, 0x12)[0]


def _lea_rip_targets(text, text_vaddr):
    """扫描 .text, 找 64 位 RIP 相对 lea (REX 8D ModRM mod=00 rm=101), 返回 (指令地址, 目标地址)"""
    out = []
    n = len(text)
    i = 0
    while i + 7 <= n:
        j = i
        if 0x40 <= text[j] <= 0x4F:
            j += 1
        if j + 6 > n:
            break
        if text[j] != 0x8D:
            i += 1
            continue
        modrm = text[j + 1]
        if (modrm >> 6) != 0 or (modrm & 7) != 5:
            i += 1
            continue
        disp = struct.unpack_from("<i", text, j + 2)[0]
        ins_addr = text_vaddr + i
        out.append((ins_addr, ins_addr + (j - i + 6) + disp))
        i += 1
    return out


_A64_ADR_MASK = 0x9F000000
_A64_ADR_VAL = 0x10000000
_A64_ADRP_VAL = 0x90000000
_A64_ADD_IMM_MASK = 0xFF000000
_A64_ADD_IMM_VAL = 0x91000000
_A64_LDR_LIT_MASK = 0xFF000000
_A64_LDR_LIT_VAL = 0x58000000


def _a64_sx(v, bits):
    s = 1 << (bits - 1)
    return (v ^ s) - s


def _a64_ref_targets(text, text_vaddr, data, secs):
    """扫描 .text, 提取 AArch64 内存引用 (指令地址, 目标地址)。

    - ADR: PC 相对字节级寻址, 直接给出目标地址
    - ADRP + ADD(imm): 页寻址 + 页内偏移, 合并为精确地址
    - LDR literal: 字面量池加载, 解引用池中 8 字节小端值
    """
    out = []
    pages = {}
    n = len(text)
    for i in range(0, n - 3, 4):
        w = struct.unpack_from("<I", text, i)[0]
        addr = text_vaddr + i
        if (w & _A64_ADR_MASK) == _A64_ADRP_VAL:
            imm = _a64_sx(((w >> 5) & 0x7FFFF) << 2 | ((w >> 29) & 3), 21)
            pages[addr] = ((addr & ~0xFFF) + (imm << 12), w & 0x1F)
        elif (w & _A64_ADR_MASK) == _A64_ADR_VAL:
            imm = _a64_sx(((w >> 5) & 0x7FFFF) << 2 | ((w >> 29) & 3), 21)
            out.append((addr, addr + imm))
        elif (w & _A64_LDR_LIT_MASK) == _A64_LDR_LIT_VAL:
            imm = _a64_sx((w >> 5) & 0x7FFFF, 19)
            lit = addr + (imm << 2)
            target = lit
            off = _vaddr_to_off(secs, lit)
            if off is not None and off + 8 <= len(data):
                target = struct.unpack_from("<Q", data, off)[0]
            out.append((addr, target))
    for addr, (page, rd) in pages.items():
        off = addr - text_vaddr
        for j in range(off + 4, min(off + 24, n - 3), 4):
            w = struct.unpack_from("<I", text, j)[0]
            if (w & _A64_ADD_IMM_MASK) == _A64_ADD_IMM_VAL and ((w >> 5) & 0x1F) == rd:
                imm12 = (w >> 10) & 0xFFF
                shift = 12 if (w >> 22) & 1 else 0
                out.append((addr, page + (imm12 << shift)))
                break
    out.sort(key=lambda x: x[0])
    return out


def _extract_precise(data):
    """精确法: 定位 PWD_STR 的引用, 回溯到 key 缓冲区。
    x86-64 (EM_X86_64=62) 走 lea RIP-relative, arm64 (EM_AARCH64=183) 走 adr/adrp+add,
    其它架构返回 None。"""
    if len(data) < 0x14 or data[:4] != b"\x7fELF":
        return None
    secs = _elf_sections(data)
    t = secs.get(".text")
    if not t:
        return None
    t_off, t_vaddr, t_size = t
    pwd_at = data.find(PWD_STR)
    if pwd_at < 0:
        return None
    pwd_vaddr = _file_to_vaddr(secs, pwd_at)
    text = data[t_off:t_off + t_size]
    machine = _elf_machine(data)
    if machine == EM_X86_64:
        refs = _lea_rip_targets(text, t_vaddr)
    elif machine == EM_AARCH64:
        refs = _a64_ref_targets(text, t_vaddr, data, secs)
    else:
        return None
    site = None
    for ins, target in refs:
        if target == pwd_vaddr:
            site = ins
            break
    if site is None:
        return None
    for ins, target in reversed(refs):
        if ins >= site:
            continue
        if site - ins > 4096:
            break
        off = _vaddr_to_off(secs, target)
        if off is None:
            off = target  # 回退: 旧行为 vaddr 直接当文件偏移
        if off + 24 > len(data):
            continue
        pw = _xor_pass(data[off:off + 24])
        if _is_plausible(pw):
            return pw
    return None


def _extract_heuristic(data):
    """启发式回退: 扫全文件找 XOR 0xAA 后为 24 位字母数字的窗口。"""
    out = []
    for i in range(len(data) - 24):
        pw = _xor_pass(data[i:i + 24])
        if _is_plausible(pw):
            out.append(pw)
    return out


def _extract_candidates(data):
    """按置信度返回候选密码: [精确法] + [启发式全部] (去重)。"""
    cands = []
    pw = _extract_precise(data)
    if pw:
        cands.append(pw)
    for pw in _extract_heuristic(data):
        if pw not in cands:
            cands.append(pw)
    return cands


def get_password():
    """返回能解压 ng.conf.zip 的密码 (带缓存):
    1. 从 nginx 二进制提取候选 (x86-64 lea / arm64 adr-adrp-ldr + 启发式), 逐个实测;
    2. 都不行则尝试兜底密码 FALLBACK_PASSWORD (不依赖抠二进制, 兼容 arm64);
    3. zip 不存在时退回提取出的最佳候选。"""
    global _password_cache
    if _password_cache is not None:
        return _password_cache
    if os.path.exists(NGINX_BIN):
        with open(NGINX_BIN, "rb") as f:
            data = f.read()
        arch = {EM_X86_64: "x86-64", EM_AARCH64: "AArch64"}.get(
            _elf_machine(data), "unknown")
        log("nginx 二进制架构: %s" % arch)
        cands = _extract_candidates(data)
        if cands:
            log("已提取 ng.conf.zip 密码候选 %d 个" % len(cands))
        else:
            log("无法从 %s 提取 zip 密码" % NGINX_BIN)
    else:
        log("nginx 二进制不存在: %s" % NGINX_BIN)
        cands = []

    if os.path.exists(RESTORE_ZIP):
        for pw in cands:
            if _password_valid(RESTORE_ZIP, pw):
                _password_cache = pw
                return pw
            log("二进制提取的密码解压失败, 尝试下一个候选")
        if _password_valid(RESTORE_ZIP, FALLBACK_PASSWORD):
            log("改用兜底密码")
            _password_cache = FALLBACK_PASSWORD
            return FALLBACK_PASSWORD
        log("所有候选(含兜底密码)均无法解压 %s" % RESTORE_ZIP)
        _password_cache = None
        return None

    # zip 不存在: 无法实测, 退回提取出的最佳候选 (或 None)
    pw = cands[0] if cands else None
    _password_cache = pw
    return pw


# ---------------------------------------------------------------------------
# 2) ZipCrypto (PKWARE traditional) 加密写 zip（原样来自 nginx_setup.py）
# ---------------------------------------------------------------------------


class ZipCrypto:
    def __init__(self, password):
        self.k0, self.k1, self.k2 = 0x12345678, 0x23456789, 0x34567890
        for b in password:
            self.update(b)

    def update(self, b):
        self.k0 = _crc_update(self.k0, b) & 0xFFFFFFFF
        self.k1 = (self.k1 + (self.k0 & 0xFF)) & 0xFFFFFFFF
        self.k1 = (self.k1 * 134775813 + 1) & 0xFFFFFFFF
        self.k2 = _crc_update(self.k2, (self.k1 >> 24) & 0xFF) & 0xFFFFFFFF

    def keystream(self):
        t = self.k2 | 2
        return ((t * (t ^ 1)) >> 8) & 0xFF

    def encrypt(self, data, crc):
        out = bytearray()
        for _ in range(11):                      # 11 个随机头字节
            b = secrets.randbelow(256)
            c = b ^ self.keystream()
            out.append(c)
            self.update(b)                       # 用明文更新
        b = (crc >> 24) & 0xFF                   # 第12字节 check byte = CRC 高字节
        out.append(b ^ self.keystream())
        self.update(b)
        for p in data:
            c = p ^ self.keystream()
            out.append(c)
            self.update(p)
        return bytes(out)


def _dos_dt(dt):
    return ((dt[3] << 11) | (dt[4] << 5) | (dt[5] // 2)), \
           (((dt[0] - 1980) << 9) | (dt[1] << 5) | dt[2])


def build_zip(entries, password):
    """entries: [(name, data, date_time, mode), ...] -> ZipCrypto 加密 zip 字节"""
    buf = io.BytesIO()
    central = []
    offset = 0
    for name, data, dt, mode in entries:
        crc = zlib.crc32(data) & 0xFFFFFFFF
        enc = ZipCrypto(password).encrypt(data, crc)
        bname = name.encode("utf-8")
        dtime, ddate = _dos_dt(dt)
        buf.write(struct.pack("<IHHHHHIIIHH", 0x04034B50, 20, 1, 0, dtime, ddate,
                              crc, len(enc), len(data), len(bname), 0))
        buf.write(bname)
        buf.write(enc)
        central.append(struct.pack("<IHHHHHHIIIHHHHHII", 0x02014B50, 0x031E, 20, 1, 0,
                                   dtime, ddate, crc, len(enc), len(data), len(bname),
                                   0, 0, 0, 0, mode, offset) + bname)
        offset += 30 + len(bname) + len(enc)
    cd = b"".join(central)
    buf.write(cd)
    buf.write(struct.pack("<IHHHHIIH", 0x06054B50, 0, 0, len(entries), len(entries),
                          len(cd), offset, 0))
    return buf.getvalue()


# ---------------------------------------------------------------------------
# 3) 泛化 zip 层：read / write / upsert（按名去重）/ remove
# ---------------------------------------------------------------------------


def _read_entry_payload(f, info, password):
    """按 local header 直接读出并解密单个条目。

    厂商 zip 由 libarchive 生成, 设置 data descriptor 标志时会用 DOS 时间
    高字节做校验字节(而非 CRC 高字节), 旧版 Python 的 zipfile 不认识该
    约定, 密码正确也会误报 Bad password。这里两种约定都接受。
    """
    f.seek(info.header_offset)
    hdr = f.read(30)
    if len(hdr) < 30 or hdr[:4] != b"PK\x03\x04":
        raise RuntimeError("%s: 无效的 local header" % info.filename)
    _, flags, method, dtime, _, _, csize, _, nl, el = \
        struct.unpack_from("<HHHHHIIIHH", hdr, 4)
    if csize == 0:
        csize = info.compress_size
    f.seek(info.header_offset + 30 + nl + el)
    if flags & 0x1:
        enc = f.read(csize)
        z = ZipCrypto(password)
        check_crc = (info.CRC >> 24) & 0xFF
        check_time = (dtime >> 8) & 0xFF
        plain = bytearray()
        for i, c in enumerate(enc):
            p = c ^ z.keystream()
            z.update(p)
            if i < 11:
                continue
            if i == 11:
                if p != check_crc and p != check_time:
                    raise RuntimeError("Bad password for file %r" % info.filename)
            else:
                plain.append(p)
        if info.CRC and zlib.crc32(plain) & 0xFFFFFFFF != info.CRC:
            raise RuntimeError("%s: CRC 校验失败" % info.filename)
    else:
        plain = f.read(csize)
    if method == 8:
        return zlib.decompress(plain, -15)
    if method != 0:
        raise RuntimeError("%s: 不支持的压缩方法 %d" % (info.filename, method))
    return bytes(plain)


def read_zip_entries(zip_path, pwd):
    """读回全部条目(含目录), 密码错误时抛异常。

    解密不依赖 zipfile(见 _read_entry_payload), 避免旧版 Python 对
    data descriptor 校验字节约定的兼容问题。
    """
    with zipfile.ZipFile(zip_path) as zf:
        with open(zip_path, "rb") as f:
            entries = []
            for info in zf.infolist():
                if info.is_dir():
                    mode = (info.external_attr >> 16) & 0xFFFF or 0o755
                    entries.append((info.filename, b"", info.date_time, mode))
                    continue
                payload = _read_entry_payload(f, info, pwd)
                mode = (info.external_attr >> 16) & 0xFFFF or 0o644
                entries.append((info.filename, payload, info.date_time, mode))
    return entries


def _password_valid(zip_path, password):
    """验证密码能否完整读回 zip。"""
    try:
        read_zip_entries(zip_path, password)
        return True
    except Exception as e:
        log("zip 密码验证失败: %s" % e)
        return False


def write_zip(zip_path, pwd, entries):
    """ZipCrypto 重写 zip -> tmp + fsync + 自检读回 + .bak + 原子替换。"""
    tmp = zip_path + ".tmp"
    try:
        with open(tmp, "wb") as f:
            f.write(build_zip(entries, pwd))
            f.flush()
            os.fsync(f.fileno())
    except Exception as e:
        log("写临时文件失败: %s" % e)
        try:
            os.remove(tmp)
        except OSError:
            pass
        return False

    # 写回前自检: 能完整读回才算成功
    try:
        with zipfile.ZipFile(tmp) as v:
            v.setpassword(pwd)
            for n in v.namelist():
                if not n.endswith("/"):
                    v.read(n)
    except Exception as e:
        log("重写后的 zip 自检失败, 已放弃: %s" % e)
        try:
            os.remove(tmp)
        except OSError:
            pass
        return False

    try:
        shutil.copy2(zip_path, zip_path + ".bak")   # 保留一份原始备份
        os.replace(tmp, zip_path)
    except Exception as e:
        log("替换 %s 失败: %s" % (zip_path, e))
        return False
    log("已更新 %s (%d 个条目)" % (zip_path, len(entries)))
    return True


def upsert_zip_entry(zip_path, pwd, name, data):
    """加入或替换指定条目（先删同名旧条目，避免重复）。"""
    with _lock:
        try:
            entries = [e for e in read_zip_entries(zip_path, pwd) if e[0] != name]
        except Exception as e:
            log("读取 %s 失败: %s" % (zip_path, e))
            return False
        now = time.localtime()
        entries.append((name, data,
                        (now.tm_year, now.tm_mon, now.tm_mday,
                         now.tm_hour, now.tm_min, now.tm_sec), 0o644))
        return write_zip(zip_path, pwd, entries)


def remove_zip_entry(zip_path, pwd, name):
    """删除指定条目，其余条目原样保留。"""
    with _lock:
        try:
            entries = [e for e in read_zip_entries(zip_path, pwd) if e[0] != name]
        except Exception as e:
            log("读取 %s 失败: %s" % (zip_path, e))
            return False
        return write_zip(zip_path, pwd, entries)


def zip_has_entry(zip_path, name):
    try:
        if os.path.exists(zip_path):
            return name in zipfile.ZipFile(zip_path).namelist()
    except Exception:
        pass
    return False


# ---------------------------------------------------------------------------
# 4) conf 生成与校验
# ---------------------------------------------------------------------------


def validate_location(location):
    if not isinstance(location, str):
        return None, "路径必须是字符串"
    loc = location.strip()
    if not loc.startswith("/"):
        return None, "路径必须以 / 开头"
    if loc == "/":
        return None, "根路径 / 被系统占用，请使用子路径"
    if len(loc) > 255:
        return None, "路径过长（最多 255 字符）"
    if _BAD_LOC.search(loc):
        return None, "路径包含非法字符（不允许空白 / ; { } # \" ' ` \\ ? 等）"
    return loc, None


def validate_http_target(target):
    if not isinstance(target, str):
        return None, "目标必须是字符串"
    t = target.strip()
    if not t:
        return None, "目标地址不能为空"
    if not _HTTP_RE.match(t):
        return None, "目标地址需形如 http://192.168.1.10:8080 或 https://域名"
    try:
        parts = urlsplit(t)
    except ValueError:
        return None, "目标地址格式不正确"
    if not parts.hostname:
        return None, "目标地址缺少主机名"
    return t, None


def validate_socket_target(target):
    if not isinstance(target, str):
        return None, "目标必须是字符串"
    t = target.strip()
    if not t.startswith("/"):
        return None, "socket 路径必须是绝对路径（以 / 开头）"
    if len(t) > 255:
        return None, "socket 路径过长"
    if _BAD_LOC.search(t):
        return None, "socket 路径包含非法字符"
    return t, None


def location_block(rule):
    """生成单条规则的 location 块。rule 为已规范化并通过校验的规则。"""
    loc = rule["location"]
    strip = rule.get("stripPrefix", True)
    if rule["type"] == "socket":
        sock = rule["socket"]
        target = "http://unix:%s:/" % sock if strip else "http://unix:%s" % sock
    else:
        t = rule["target"]
        target = t.rstrip("/") + "/" if strip else t
    return (
        "location %s {\n"
        "    proxy_pass %s;\n"
        "    proxy_set_header Host $host;\n"
        "    proxy_set_header X-Real-IP $remote_addr;\n"
        "    proxy_set_header X-Forwarded-For $proxy_add_x_forwarded_for;\n"
        "}\n" % (loc, target)
    )


def generate_conf(rules):
    """生成整个 conf 文件内容（只含启用规则）。"""
    parts = ["# Generated by FnNginxConf - DO NOT EDIT\n"]
    for r in rules:
        if r.get("enabled", True):
            parts.append(location_block(r))
    return "".join(parts)


# ---------------------------------------------------------------------------
# 5) 路径冲突检测（不占用官方已有路径）
# ---------------------------------------------------------------------------


def normalize_location(p):
    p = (p or "").strip()
    while len(p) > 1 and p.endswith("/"):
        p = p[:-1]
    return p


def _regex_literal_prefix(regex):
    """^/ 后连续字面字符 -> 字面前缀；失败返回 None。"""
    if not regex.startswith("^/"):
        return None
    out = ["/"]
    for ch in regex[2:]:
        if ch in _META:
            break
        out.append(ch)
    lit = "".join(out)
    return lit if len(lit) > 1 else None


def _prefix_targets(loc):
    """返回该 location 用于前缀比较的 (literal_prefix, captures_descendants)。
    captures_descendants=False 表示该 location 只精确匹配（= 或正则），不捕获子路径。"""
    mod, target = loc["modifier"], loc["target"]
    if mod in ("", "^~"):
        return target, True
    if mod == "=":
        return target, False
    lit = _regex_literal_prefix(target)   # ~ / ~* 正则：尽力提取字面前缀
    return (lit, False) if lit else (None, False)


def get_existing_locations(force=False):
    """扫描现有 nginx location。返回 [{modifier, target, source}, ...]。
    排除本应用自己的 conf 文件。带短 TTL 缓存。"""
    with _lock:
        now = time.time()
        if not force and (now - _existing_cache["t"]) < _EXISTING_TTL:
            return _existing_cache["data"]
        out = []
        files = []
        if os.path.exists(NGINX_CONF):
            files.append((NGINX_CONF, os.path.basename(NGINX_CONF)))
        if os.path.isdir(CONF_DIR):
            for fn in sorted(os.listdir(CONF_DIR)):
                if fn.endswith(".conf") and fn != CONF_NAME:
                    files.append((os.path.join(CONF_DIR, fn), fn))
        for path, src in files:
            try:
                with open(path, "r", encoding="utf-8", errors="replace") as f:
                    text = f.read()
            except OSError:
                continue
            for m in _LOC_RE.finditer(text):
                target = (m.group(2) or "").strip().strip("\"'")
                if not target.startswith("/"):
                    continue
                out.append({"modifier": m.group(1) or "", "target": target, "source": src})
        _existing_cache.update(t=now, data=out)
        return out


def check_location_conflict(location):
    """检查用户 location 与系统已有路径是否冲突。
    返回 (status, message, detail)：status in ("ok", "warn", "reject")。"""
    norm = normalize_location(location)
    if not norm:
        return "reject", "路径不能为空", None

    # 1. 保留命名空间（统一网关 / CGI）
    for reserved in RESERVED_PREFIXES:
        if norm == reserved or norm.startswith(reserved + "/"):
            return ("reject",
                    "该路径位于系统保留命名空间 %s（统一网关/CGI），不允许占用。" % reserved,
                    {"reserved": reserved})

    existing = get_existing_locations()

    # 2. 完全相等冲突
    for loc in existing:
        lit, _ = _prefix_targets(loc)
        if lit and normalize_location(lit) == norm:
            return ("reject",
                    "该路径与系统已有路径 %s 冲突（来自 %s）。" % (lit, loc["source"]),
                    {"source": loc["source"], "target": lit})

    # 3. 子路径提示（非阻塞）
    for loc in existing:
        lit, captures = _prefix_targets(loc)
        if lit and captures and norm != lit and norm.startswith(lit):
            return ("warn",
                    "该路径位于系统路径 %s 之下，nginx 按最长前缀匹配，请确认不会抢占系统服务。" % lit,
                    {"source": loc["source"], "parent": lit})

    return "ok", None, None


# ---------------------------------------------------------------------------
# 6) 应用编排（校验先于变更，带回滚）
# ---------------------------------------------------------------------------


def write_conf_atomic(content):
    try:
        os.makedirs(CONF_DIR, exist_ok=True)
    except OSError:
        pass
    tmp = CONF_PATH + ".tmp"
    with open(tmp, "w", encoding="utf-8", newline="\n") as f:
        f.write(content)
        f.flush()
        os.fsync(f.fileno())
    os.chmod(tmp, 0o644)
    os.replace(tmp, CONF_PATH)
    return True


def _current_conf():
    try:
        with open(CONF_PATH, "r", encoding="utf-8") as f:
            return f.read()
    except OSError:
        return None


def validate_nginx():
    """nginx -t 校验。返回 (ok, detail)。"""
    if not os.path.exists(NGINX_BIN):
        return False, "nginx 二进制不存在: %s" % NGINX_BIN
    prefix = os.path.dirname(os.path.dirname(NGINX_BIN))
    try:
        r = subprocess.run([NGINX_BIN, "-t", "-p", prefix],
                           capture_output=True, text=True, timeout=30)
    except Exception as e:
        return False, "nginx -t 执行异常: %s" % e
    if r.returncode == 0:
        return True, ""
    try:
        r2 = subprocess.run([NGINX_BIN, "-t"],
                            capture_output=True, text=True, timeout=30)
    except Exception:
        r2 = None
    if r2 is not None and r2.returncode == 0:
        return True, ""
    detail = ((r2.stderr or r2.stdout) if r2 is not None else "") or (r.stderr or r.stdout or "")
    return False, (detail or "").strip()[-1200:]


def restart_nginx():
    """重启 trim_nginx（recover 模块会重新解压 zip 到 conf.d）。返回 (ok, detail)。"""
    try:
        r = subprocess.run(["systemctl", "restart", "trim_nginx"],
                           capture_output=True, text=True, timeout=60)
    except Exception as e:
        log("重启 trim_nginx 异常: %s" % e)
        return False, "systemctl restart trim_nginx 异常: %s" % e
    if r.returncode != 0:
        log("systemctl restart trim_nginx 失败: %s" % r.stderr.strip())
        return False, ((r.stderr or "").strip()[-1200:] or "systemctl restart trim_nginx 失败")
    log("已重启 trim_nginx")
    return True, ""


def nginx_active():
    """nginx 是否运行（best-effort）。"""
    try:
        r = subprocess.run(["systemctl", "is-active", "trim_nginx"],
                           capture_output=True, text=True, timeout=10)
        return r.returncode == 0 and (r.stdout or "").strip() == "active"
    except Exception:
        return False


def _restore_conf(old_bytes):
    if old_bytes is None:
        try:
            os.remove(CONF_PATH)
        except OSError:
            pass
    else:
        try:
            with open(CONF_PATH, "wb") as f:
                f.write(old_bytes)
        except OSError:
            pass


def _do_apply(rules, restart):
    """应用配置核心逻辑。restart=True 同步重启；False 只准备并返回 changed（供 HTTP 调用方后台重启）。
    返回 (ok, message, detail, changed)。"""
    with _lock:
        enabled = [r for r in rules if r.get("enabled", True)]
        if not enabled:
            return _do_remove(restart)

        content = generate_conf(rules)
        pwd = get_password()
        can_persist = bool(pwd) and os.path.exists(RESTORE_ZIP)

        # 幂等：conf.d 与 zip 都已一致则跳过
        if _current_conf() == content and (zip_has_entry(RESTORE_ZIP, ZIP_ENTRY) or not can_persist):
            return True, "配置已是最新，无需变更。", None, False

        # 0) 预检：系统当前 nginx 配置必须先通过校验，避免与既有异常叠加
        ok, pre_detail = validate_nginx()
        if not ok:
            return False, "系统当前 nginx 配置校验失败，已拒绝应用（请先修复系统配置后重试）。", pre_detail, False

        # 1) 写 conf.d（内存留旧字节以便回滚）
        old_bytes = None
        if os.path.exists(CONF_PATH):
            try:
                with open(CONF_PATH, "rb") as f:
                    old_bytes = f.read()
            except OSError:
                old_bytes = None
        try:
            write_conf_atomic(content)
        except Exception as e:
            log("写入 %s 失败: %s" % (CONF_PATH, e))
            return False, "写入配置文件失败: %s" % e, None, False

        # 2) nginx -t 校验
        ok, detail = validate_nginx()
        if not ok:
            _restore_conf(old_bytes)
            return False, "nginx 配置校验失败，已回滚。", detail, False

        # 3) 同步 zip（无法持久化时降级：仅 conf.d 生效）
        if can_persist:
            if not upsert_zip_entry(RESTORE_ZIP, pwd, ZIP_ENTRY, content.encode("utf-8")):
                _restore_conf(old_bytes)
                return False, "更新 ng.conf.zip 失败，已回滚。", None, False

        if not restart:
            # HTTP 路径：响应先发出，再由调用方后台重启——网关即 nginx，同步重启会切断本请求连接
            if can_persist:
                return True, "配置已应用并持久化到 ng.conf.zip，nginx 正在后台重启。", None, True
            return True, "配置已应用（未持久化：无法提取 zip 密码或找不到 ng.conf.zip）。", None, True

        # 4) 重启
        ok, msg = restart_nginx()
        if not ok:
            _restore_conf(old_bytes)
            if can_persist:
                try:
                    shutil.copy2(RESTORE_ZIP + ".bak", RESTORE_ZIP)
                except OSError:
                    pass
            return False, "重启 nginx 失败，已回滚配置。", msg, False

        if can_persist:
            return True, "配置已应用并持久化到 ng.conf.zip，nginx 已重启。", None, False
        return True, "配置已应用（未持久化：无法提取 zip 密码或找不到 ng.conf.zip）。", None, False


def _do_remove(restart):
    """移除 conf 核心逻辑。restart=True 同步重启；False 只准备并返回 changed。
    返回 (ok, message, detail, changed)。"""
    with _lock:
        changed = False
        old_bytes = None
        if os.path.exists(CONF_PATH):
            try:
                with open(CONF_PATH, "rb") as f:
                    old_bytes = f.read()
            except OSError:
                old_bytes = None
            try:
                os.remove(CONF_PATH)
                changed = True
            except OSError as e:
                log("删除 %s 失败: %s" % (CONF_PATH, e))
                return False, "删除配置文件失败: %s" % e, None, False

        if os.path.exists(RESTORE_ZIP):
            pwd = get_password()
            if not pwd:
                log("无法提取密码，跳过 zip 条目清理")
            elif zip_has_entry(RESTORE_ZIP, ZIP_ENTRY):
                if not remove_zip_entry(RESTORE_ZIP, pwd, ZIP_ENTRY):
                    _restore_conf(old_bytes)   # 还原 conf.d，保持磁盘与 zip 一致
                    return False, "从 ng.conf.zip 移除条目失败，已还原配置。", None, False
                changed = True

        if not restart:
            if changed:
                return True, "已移除配置。", None, True
            return True, "没有需要清理的配置。", None, False

        if changed:
            ok, msg = restart_nginx()
            if not ok:
                return False, "重启 nginx 失败。", msg, False
            return True, "已移除配置并重启 nginx。", None, False
        return True, "没有需要清理的配置。", None, False


def apply_conf(rules):
    """把规则写入 conf.d + 同步 ng.conf.zip + 同步重启 nginx（启动/CLI 路径）。
    返回 (ok, message, detail)。"""
    ok, message, detail, _ = _do_apply(rules, True)
    return ok, message, detail


def prepare(rules):
    """应用配置但不重启（HTTP 路径：响应先发出，再由调用方后台重启避免连接中断）。
    返回 (ok, message, detail, changed)。"""
    return _do_apply(rules, False)


def remove_conf():
    """移除 conf.d 文件 + zip 条目 + 同步重启（卸载 CLI 路径）。
    返回 (ok, message, detail)。"""
    ok, message, detail, _ = _do_remove(True)
    return ok, message, detail


def ensure(rules):
    """启动时幂等对账：规则与 conf.d/zip 保持同步。从不抛异常。"""
    try:
        if not os.path.exists(NGINX_BIN):
            log("nginx 二进制不存在（%s），跳过 ensure" % NGINX_BIN)
            return
        enabled = [r for r in rules if r.get("enabled", True)]
        if enabled:
            content = generate_conf(rules)
            need = _current_conf() != content
            if not need and os.path.exists(RESTORE_ZIP):
                pwd = get_password()
                need = bool(pwd) and not zip_has_entry(RESTORE_ZIP, ZIP_ENTRY)
            if need:
                log("ensure: 应用规则 (%d 条)" % len(enabled))
                apply_conf(rules)
            else:
                log("ensure: 配置已一致，无需变更")
        else:
            stale = os.path.exists(CONF_PATH) or zip_has_entry(RESTORE_ZIP, ZIP_ENTRY)
            if stale:
                log("ensure: 移除残留配置")
                remove_conf()
            else:
                log("ensure: 无需清理")
    except Exception as e:
        log("ensure 异常: %r" % (e,))


# ---------------------------------------------------------------------------
# 7) CLI
# ---------------------------------------------------------------------------


def _load_rules_from_env():
    path = os.environ.get("RULES_FILE", "")
    if not path:
        return []
    try:
        with open(path, "r", encoding="utf-8") as f:
            data = json.load(f)
        return data if isinstance(data, list) else []
    except Exception:
        return []


def main():
    args = sys.argv[1:]
    cmd = args[0] if args else ""
    # 支持可选 --file <rules.json>
    if "--file" in args:
        i = args.index("--file")
        if i + 1 < len(args):
            os.environ["RULES_FILE"] = args[i + 1]
    if cmd == "ensure":
        ensure(_load_rules_from_env())
        return 0
    if cmd == "remove":
        ok, msg, detail = remove_conf()
        log("%s %s" % (msg, detail or ""))
        return 0 if ok else 1
    if cmd == "print-conf":
        sys.stdout.write(generate_conf(_load_rules_from_env()))
        return 0
    print("usage: nginx_cfg.py [ensure|remove|print-conf] [--file rules.json]", file=sys.stderr)
    return 2


if __name__ == "__main__":
    sys.exit(main())
