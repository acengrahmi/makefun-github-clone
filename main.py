#!/usr/bin/env python3
"""github-core-clone-01: a standalone GitHub-compatible git forge.

One process, Python standard library only. It serves, from a single
in-memory store:

  * git smart HTTP (protocol v0 + v2): info/refs, git-upload-pack
    (ls-refs / fetch, shallow + deepen), git-receive-pack (push with
    report-status), real packfile read/write including ofs/ref deltas;
  * the GitHub REST v3 API subset: user, meta, repos CRUD, branches,
    git refs, contents, commits, labels, issues, comments, pull
    requests (list / files / squash merge), search stubs;
  * a GraphQL endpoint: viewer, repository, node, issues and
    pullRequests connections with cursors, the five mutations the
    suite exercises, and __type introspection;
  * an MCP endpoint (JSON-RPC): server/discover, initialize, ping,
    tools/list and tools/call for the six forge tools.

Harness lifecycle (agent/v1): bind an ephemeral port, POST {"port": N}
to $MAKEFUN_ENV_URL/register until accepted, serve until a long-poll of
$MAKEFUN_ENV_URL/done reports {"done": true}, then exit 0.

The suite's bearer token authenticates as the fixed scenario viewer
(the token does not encode an identity): adaiversen, id 1000.
"""

import base64
import difflib
import hashlib
import http.client
import json
import os
import re
import struct
import sys
import threading
import time
import urllib.parse
import uuid
import zlib
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

# --------------------------------------------------------------------------
# Constants: the fixed scenario identity and wire constants.
# --------------------------------------------------------------------------

VIEWER_LOGIN = "adaiversen"
VIEWER_ID = 1000
VIEWER_NAME = "ada iversen"
VIEWER_EMAIL = "adaiversen@example.invalid"
FORGE_VERSION = "1.0.0"
INSTALLED_VERSION = "3.13.0-forge"
ZERO_OID = "0" * 40
GIT_TYPE_NUM = {"commit": 1, "tree": 2, "blob": 3, "tag": 4}
GIT_NUM_TYPE = {v: k for k, v in GIT_TYPE_NUM.items()}

TOKEN = os.environ.get("MAKEFUN_SHOP_TOKEN", "")
ENV_URL = os.environ.get("MAKEFUN_ENV_URL", "")

# --------------------------------------------------------------------------
# Git object store: one content-addressed store shared by every repo.
# Objects are kept as (type_name, raw_bytes); refs live per repository.
# --------------------------------------------------------------------------

OBJECTS = {}
OBJECT_LOCK = threading.RLock()
_COMMIT_CACHE = {}
_TREE_CACHE = {}
_FLAT_CACHE = {}


def hash_object(type_name, data):
    header = ("%s %d" % (type_name, len(data))).encode() + b"\x00"
    return hashlib.sha1(header + data).hexdigest()


def store_object(type_name, data):
    oid = hash_object(type_name, data)
    with OBJECT_LOCK:
        if oid not in OBJECTS:
            OBJECTS[oid] = (type_name, data)
    return oid


def get_object(oid):
    return OBJECTS.get(oid)


def object_type(oid):
    obj = OBJECTS.get(oid)
    return obj[0] if obj else None


def parse_ident(text):
    """'Name <email> 1700000000 +0000' -> dict(name, email, ts)."""
    name, email, ts = text, "", 0
    lt = text.find("<")
    gt = text.find(">", lt + 1)
    if 0 <= lt < gt:
        name = text[:lt].strip()
        email = text[lt + 1:gt]
        rest = text[gt + 1:].split()
        if rest:
            try:
                ts = int(rest[0])
            except ValueError:
                ts = 0
    return {"name": name, "email": email, "ts": ts}


def parse_commit(oid):
    cached = _COMMIT_CACHE.get(oid)
    if cached is not None:
        return cached
    obj = OBJECTS.get(oid)
    if obj is None or obj[0] != "commit":
        return None
    data = obj[1]
    head, _, message = data.partition(b"\n\n")
    info = {"tree": None, "parents": [], "author": "", "committer": "",
            "message": message.decode("utf-8", "replace")}
    for line in head.split(b"\n"):
        if line.startswith(b"tree "):
            info["tree"] = line[5:].decode()
        elif line.startswith(b"parent "):
            info["parents"].append(line[7:].decode())
        elif line.startswith(b"author "):
            info["author"] = line[7:].decode("utf-8", "replace")
        elif line.startswith(b"committer "):
            info["committer"] = line[10:].decode("utf-8", "replace")
    if len(_COMMIT_CACHE) < 500000:
        _COMMIT_CACHE[oid] = info
    return info


def build_commit_bytes(tree_oid, parents, message, ts=None):
    if ts is None:
        ts = int(time.time())
    ident = "%s <%s> %d +0000" % (VIEWER_NAME, VIEWER_EMAIL, ts)
    lines = ["tree %s" % tree_oid]
    for parent in parents:
        lines.append("parent %s" % parent)
    lines.append("author %s" % ident)
    lines.append("committer %s" % ident)
    return ("\n".join(lines) + "\n\n" + message).encode()


def create_commit(tree_oid, parents, message):
    return store_object("commit", build_commit_bytes(tree_oid, parents, message))


def parse_tree(oid):
    cached = _TREE_CACHE.get(oid)
    if cached is not None:
        return cached
    obj = OBJECTS.get(oid)
    if obj is None or obj[0] != "tree":
        return []
    data = obj[1]
    entries = []
    pos = 0
    while pos < len(data):
        sp = data.index(b" ", pos)
        mode = data[pos:sp].decode()
        nul = data.index(b"\x00", sp)
        name = data[sp + 1:nul].decode("utf-8", "surrogateescape")
        child = data[nul + 1:nul + 21].hex()
        entries.append((mode, name, child))
        pos = nul + 21
    if len(_TREE_CACHE) < 500000:
        _TREE_CACHE[oid] = entries
    return entries


def serialize_tree(entries):
    def sort_key(entry):
        mode, name, _ = entry
        return name + ("/" if mode == "40000" else "")

    out = bytearray()
    for mode, name, oid in sorted(entries, key=sort_key):
        out += mode.encode() + b" " + name.encode("utf-8", "surrogateescape")
        out += b"\x00" + bytes.fromhex(oid)
    return bytes(out)


def flatten_tree(tree_oid, prefix=""):
    """tree oid -> {path: (mode, oid)} for every blob below it."""
    if tree_oid is None:
        return {}
    cache_key = (tree_oid, prefix)
    cached = _FLAT_CACHE.get(cache_key)
    if cached is not None:
        return cached
    flat = {}
    for mode, name, child in parse_tree(tree_oid):
        path = prefix + name
        if mode == "40000":
            flat.update(flatten_tree(child, path + "/"))
        else:
            flat[path] = (mode, child)
    if len(_FLAT_CACHE) < 200000:
        _FLAT_CACHE[cache_key] = flat
    return flat


def tree_oid_from_flat(flat):
    """Inverse of flatten_tree: build (and store) nested trees."""
    root = {}
    for path, value in flat.items():
        parts = path.split("/")
        node = root
        for part in parts[:-1]:
            node = node.setdefault(part, {})
        node[parts[-1]] = value

    def build(node):
        entries = []
        for name, value in node.items():
            if isinstance(value, dict):
                entries.append(("40000", name, build(value)))
            else:
                entries.append((value[0], name, value[1]))
        return store_object("tree", serialize_tree(entries))

    return build(root)


def tree_entry_at(tree_oid, path):
    """Resolve a path inside a tree: ('file', oid, size) / ('dir', oid, entries) / None."""
    if tree_oid is None:
        return None
    if path == "":
        return ("dir", tree_oid, parse_tree(tree_oid))
    parts = path.split("/")
    current = tree_oid
    for index, part in enumerate(parts):
        found = None
        for mode, name, child in parse_tree(current):
            if name == part:
                found = (mode, child)
                break
        if found is None:
            return None
        mode, child = found
        if index == len(parts) - 1:
            if mode == "40000":
                return ("dir", child, parse_tree(child))
            obj = OBJECTS.get(child)
            size = len(obj[1]) if obj else 0
            return ("file", child, size)
        if mode != "40000":
            return None
        current = child
    return None


def peel_to_commit(oid):
    """Follow tag objects until a commit; None when the chain breaks."""
    seen = 0
    while oid is not None and seen < 20:
        type_name = object_type(oid)
        if type_name == "commit":
            return oid
        if type_name != "tag":
            return None
        obj = OBJECTS[oid]
        target = None
        for line in obj[1].split(b"\n"):
            if line.startswith(b"object "):
                target = line[7:].decode()
                break
            if line == b"":
                break
        oid = target
        seen += 1
    return None


def peel_target(oid):
    """One peel step for a tag: the object it points at."""
    obj = OBJECTS.get(oid)
    if obj is None or obj[0] != "tag":
        return None
    for line in obj[1].split(b"\n"):
        if line.startswith(b"object "):
            return line[7:].decode()
        if line == b"":
            break
    return None


def commit_ancestors(start):
    """All ancestor commit oids of start (including start), BFS order."""
    order = []
    seen = set()
    queue = [start]
    while queue:
        oid = queue.pop(0)
        if oid in seen or object_type(oid) != "commit":
            continue
        seen.add(oid)
        order.append(oid)
        info = parse_commit(oid)
        if info:
            queue.extend(info["parents"])
    return order


def is_ancestor(ancestor, descendant):
    if ancestor == descendant:
        return True
    seen = set()
    queue = [descendant]
    while queue:
        oid = queue.pop(0)
        if oid in seen:
            continue
        seen.add(oid)
        if oid == ancestor:
            return True
        info = parse_commit(oid)
        if info:
            queue.extend(info["parents"])
    return False


def merge_base(a, b):
    if a is None or b is None:
        return None
    ancestors_a = commit_ancestors(a)
    set_a = set(ancestors_a)
    seen = set()
    queue = [b]
    while queue:
        oid = queue.pop(0)
        if oid in seen:
            continue
        seen.add(oid)
        if oid in set_a:
            return oid
        info = parse_commit(oid)
        if info:
            queue.extend(info["parents"])
    return None


def three_way_merge(base_flat, ours_flat, theirs_flat):
    """Per-path 3-way merge of flattened trees.

    Returns (merged_flat, conflict_paths). A path conflicts when both
    sides changed it to different bytes (or one deleted what the other
    changed).
    """
    merged = {}
    conflicts = []
    paths = set(base_flat) | set(ours_flat) | set(theirs_flat)
    for path in paths:
        base = base_flat.get(path)
        ours = ours_flat.get(path)
        theirs = theirs_flat.get(path)
        if ours == theirs:
            if ours is not None:
                merged[path] = ours
        elif base == ours:
            if theirs is not None:
                merged[path] = theirs
        elif base == theirs:
            if ours is not None:
                merged[path] = ours
        else:
            conflicts.append(path)
    return merged, conflicts


def blob_text_lines(oid):
    obj = OBJECTS.get(oid)
    if obj is None or obj[0] != "blob":
        return None
    data = obj[1]
    if b"\x00" in data[:8000]:
        return None
    return data.decode("utf-8", "replace").split("\n")


def diff_flats(base_flat, head_flat):
    """GitHub-shaped file diff entries between two flattened trees."""
    files = []
    for path in sorted(set(base_flat) | set(head_flat)):
        base = base_flat.get(path)
        head = head_flat.get(path)
        if base == head:
            continue
        if base is None:
            status = "added"
        elif head is None:
            status = "removed"
        else:
            status = "modified"
        additions = 0
        deletions = 0
        base_lines = blob_text_lines(base[1]) if base else []
        head_lines = blob_text_lines(head[1]) if head else []
        if base_lines is not None and head_lines is not None:
            diff = difflib.unified_diff(base_lines, head_lines, lineterm="")
            for line in diff:
                if line.startswith("+") and not line.startswith("+++"):
                    additions += 1
                elif line.startswith("-") and not line.startswith("---"):
                    deletions += 1
        files.append({
            "filename": path,
            "status": status,
            "additions": additions,
            "deletions": deletions,
            "changes": additions + deletions,
        })
    return files


# --------------------------------------------------------------------------
# Packfiles and pkt-lines.
# --------------------------------------------------------------------------


def pkt(payload):
    if isinstance(payload, str):
        payload = payload.encode()
    return ("%04x" % (len(payload) + 4)).encode() + payload


PKT_FLUSH = b"0000"
PKT_DELIM = b"0001"


def read_pkt_line(data, pos):
    """One pkt-line at pos -> (payload or 'flush'/'delim', next_pos)."""
    if pos + 4 > len(data):
        raise ValueError("truncated pkt-line")
    try:
        length = int(data[pos:pos + 4].decode("ascii"), 16)
    except (ValueError, UnicodeDecodeError):
        raise ValueError("invalid pkt-line length")
    if length == 0:
        return ("flush", pos + 4)
    if length == 1:
        return ("delim", pos + 4)
    if length == 2:
        return ("response-end", pos + 4)
    if length < 4 or pos + length > len(data):
        raise ValueError("pkt-line overruns body")
    return (data[pos + 4:pos + length], pos + length)


def pack_entry_header(type_num, size):
    first = (type_num << 4) | (size & 0x0F)
    size >>= 4
    out = bytearray()
    if size:
        first |= 0x80
    out.append(first)
    while size:
        byte = size & 0x7F
        size >>= 7
        if size:
            byte |= 0x80
        out.append(byte)
    return bytes(out)


def write_pack(objects):
    """objects: list of (type_name, data) -> complete pack bytes."""
    out = bytearray()
    out += b"PACK" + struct.pack(">II", 2, len(objects))
    for type_name, data in objects:
        out += pack_entry_header(GIT_TYPE_NUM[type_name], len(data))
        out += zlib.compress(data)
    out += hashlib.sha1(bytes(out)).digest()
    return bytes(out)


def _delta_varint(data, pos):
    value = 0
    shift = 0
    while True:
        byte = data[pos]
        pos += 1
        value |= (byte & 0x7F) << shift
        shift += 7
        if not (byte & 0x80):
            return value, pos


def apply_delta(base, delta):
    src_size, pos = _delta_varint(delta, 0)
    if src_size != len(base):
        raise ValueError("delta base size mismatch")
    tgt_size, pos = _delta_varint(delta, pos)
    out = bytearray()
    while pos < len(delta):
        op = delta[pos]
        pos += 1
        if op & 0x80:
            cp_off = 0
            cp_size = 0
            for bit in range(4):
                if op & (1 << bit):
                    cp_off |= delta[pos] << (8 * bit)
                    pos += 1
            for bit in range(3):
                if op & (0x10 << bit):
                    cp_size |= delta[pos] << (8 * bit)
                    pos += 1
            if cp_size == 0:
                cp_size = 0x10000
            out += base[cp_off:cp_off + cp_size]
        elif op:
            out += delta[pos:pos + op]
            pos += op
        else:
            raise ValueError("delta opcode 0")
    if len(out) != tgt_size:
        raise ValueError("delta target size mismatch")
    return bytes(out)


def parse_pack(data):
    """Parse pack bytes, store every object, return the object count.

    Handles plain entries plus OFS_DELTA and REF_DELTA. Raises
    ValueError on any corruption (the caller reports 'unpack' failure).
    """
    if len(data) < 12 + 20 or data[:4] != b"PACK":
        raise ValueError("not a packfile")
    version, count = struct.unpack(">II", data[4:12])
    if version != 2:
        raise ValueError("unsupported pack version")
    trailer = hashlib.sha1(data[:-20]).digest()
    if trailer != data[-20:]:
        raise ValueError("pack checksum mismatch")
    pos = 12
    entries = []  # (start_pos, type_num, data|None, base_pos|None, base_oid|None)
    decompressor_end = len(data) - 20
    for _ in range(count):
        start = pos
        if pos >= decompressor_end:
            raise ValueError("pack truncated")
        byte = data[pos]
        pos += 1
        type_num = (byte >> 4) & 0x07
        size = byte & 0x0F
        shift = 4
        while byte & 0x80:
            byte = data[pos]
            pos += 1
            size |= (byte & 0x7F) << shift
            shift += 7
        base_pos = None
        base_oid = None
        if type_num == 6:  # OFS_DELTA
            byte = data[pos]
            pos += 1
            offset = byte & 0x7F
            while byte & 0x80:
                byte = data[pos]
                pos += 1
                offset = ((offset + 1) << 7) | (byte & 0x7F)
            base_pos = start - offset
        elif type_num == 7:  # REF_DELTA
            base_oid = data[pos:pos + 20].hex()
            pos += 20
        decomp = zlib.decompressobj()
        try:
            raw = decomp.decompress(data[pos:decompressor_end])
        except zlib.error as exc:
            raise ValueError("bad zlib stream in pack") from exc
        consumed = (decompressor_end - pos) - len(decomp.unused_data)
        if len(raw) != size:
            raise ValueError("pack entry size mismatch")
        pos += consumed
        entries.append((start, type_num, raw, base_pos, base_oid))
    resolved = {}

    def resolve(index):
        if index in resolved:
            return resolved[index]
        start, type_num, raw, base_pos, base_oid = entries[index]
        if type_num in (1, 2, 3, 4):
            result = (GIT_NUM_TYPE[type_num], raw)
        else:
            if base_pos is not None:
                base_index = None
                for i, entry in enumerate(entries):
                    if entry[0] == base_pos:
                        base_index = i
                        break
                if base_index is None:
                    raise ValueError("ofs-delta base not in pack")
                base_type, base_data = resolve(base_index)
            else:
                base = OBJECTS.get(base_oid)
                if base is None:
                    # The base may be an earlier entry of this same pack.
                    base_type = None
                    for i, entry in enumerate(entries):
                        t, d = resolve(i)
                        if hash_object(t, d) == base_oid:
                            base_type, base_data = t, d
                            break
                    if base_type is None:
                        raise ValueError("ref-delta base missing")
                else:
                    base_type, base_data = base
            result = (base_type, apply_delta(base_data, raw))
        resolved[index] = result
        return result

    for i in range(count):
        type_name, raw = resolve(i)
        store_object(type_name, raw)
    return count


# --------------------------------------------------------------------------
# Repository / issue / pull-request store.
# --------------------------------------------------------------------------

STORE_LOCK = threading.RLock()
REPOS = {}          # (owner, name) -> Repo
REPO_BY_DBID = {}   # dbid -> Repo
COMMENT_INDEX = {}  # comment id -> (repo, number)
_NEXT_DBID = [1]
_ITEM_SEQ = [0]


def _next_seq():
    _ITEM_SEQ[0] += 1
    return _ITEM_SEQ[0]


class Repo:
    def __init__(self, owner, name, private=False, description=""):
        self.owner = owner
        self.name = name
        self.dbid = _NEXT_DBID[0]
        _NEXT_DBID[0] += 1
        self.private = bool(private)
        self.description = description or ""
        self.default_branch = "main"
        self.refs = {}        # full ref name -> oid
        self.labels = {}      # name -> {"name":..., "color":...}
        self.items = {}       # number -> item dict (issues and PRs share the counter)
        self.next_number = 1
        self.next_id = 1
        self.created_seq = _next_seq()
        now = int(time.time())
        self.created_at = now
        self.updated_at = now

    def alloc_id(self):
        value = self.next_id
        self.next_id += 1
        return value

    def branch_tip(self, branch):
        return self.refs.get("refs/heads/" + branch)

    def default_tip(self):
        return self.refs.get("refs/heads/" + self.default_branch)


def get_repo(owner, name):
    return REPOS.get((owner, name))


def create_repo(owner, name, private=False, description=""):
    repo = Repo(owner, name, private, description)
    REPOS[(owner, name)] = repo
    REPO_BY_DBID[repo.dbid] = repo
    return repo


def delete_repo(repo):
    REPOS.pop((repo.owner, repo.name), None)
    REPO_BY_DBID.pop(repo.dbid, None)


def iso8601(ts):
    return time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime(ts))


def user_json(login=VIEWER_LOGIN):
    return {
        "login": login,
        "id": VIEWER_ID if login == VIEWER_LOGIN else 0,
        "node_id": base64.b64encode(("User:%d" % VIEWER_ID).encode()).decode(),
        "avatar_url": "",
        "gravatar_id": "",
        "type": "User",
        "site_admin": False,
        "name": VIEWER_NAME if login == VIEWER_LOGIN else login,
        "email": VIEWER_EMAIL if login == VIEWER_LOGIN else None,
        "html_url": "https://forge.invalid/%s" % login,
        "url": "https://forge.invalid/api/v3/users/%s" % login,
    }


def repo_json(repo, host="forge.invalid"):
    open_count = sum(
        1 for item in repo.items.values() if item["state"] == "open")
    return {
        "id": repo.dbid,
        "node_id": global_id("Repository", repo.dbid),
        "name": repo.name,
        "full_name": "%s/%s" % (repo.owner, repo.name),
        "private": repo.private,
        "owner": user_json(repo.owner),
        "description": repo.description,
        "fork": False,
        "default_branch": repo.default_branch,
        "created_at": iso8601(repo.created_at),
        "updated_at": iso8601(repo.updated_at),
        "pushed_at": iso8601(repo.updated_at),
        "html_url": "http://%s/%s/%s" % (host, repo.owner, repo.name),
        "url": "http://%s/api/v3/repos/%s/%s" % (host, repo.owner, repo.name),
        "git_url": "git://%s/%s/%s.git" % (host, repo.owner, repo.name),
        "clone_url": "http://%s/%s/%s.git" % (host, repo.owner, repo.name),
        "size": 0,
        "stargazers_count": 0,
        "watchers_count": 0,
        "forks_count": 0,
        "open_issues_count": open_count,
        "has_issues": True,
        "has_projects": True,
        "has_wiki": True,
        "archived": False,
        "disabled": False,
        "license": None,
        "topics": [],
        "visibility": "private" if repo.private else "public",
        "permissions": {"admin": True, "maintain": True, "push": True,
                        "triage": True, "pull": True},
    }


def label_json(label):
    return {"id": abs(hash(label["name"])) % 1000000, "name": label["name"],
            "color": label["color"], "default": False, "description": None}


def issue_json(repo, item):
    body = {
        "id": item["id"],
        "node_id": global_id("Issue", repo.dbid, item["number"]),
        "number": item["number"],
        "title": item["title"],
        "body": item["body"],
        "state": item["state"],
        "labels": [label_json(repo.labels[name]) for name in item["labels"]
                   if name in repo.labels],
        "user": user_json(),
        "comments": len(item["comments"]),
        "created_at": iso8601(item["created_ts"]),
        "updated_at": iso8601(item["updated_ts"]),
        "closed_at": iso8601(item["updated_ts"]) if item["state"] == "closed" else None,
        "html_url": "https://forge.invalid/%s/%s/issues/%d" % (
            repo.owner, repo.name, item["number"]),
        "url": "https://forge.invalid/api/v3/repos/%s/%s/issues/%d" % (
            repo.owner, repo.name, item["number"]),
    }
    return body


def pull_json(repo, item):
    body = issue_json(repo, item)
    body["node_id"] = global_id("PullRequest", repo.dbid, item["number"])
    head_tip = repo.branch_tip(item["head"]) if item.get("head") else None
    base_tip = repo.branch_tip(item["base"]) if item.get("base") else None
    body["head"] = {"ref": item.get("head"), "sha": head_tip,
                    "label": "%s:%s" % (repo.owner, item.get("head"))}
    body["base"] = {"ref": item.get("base"), "sha": base_tip,
                    "label": "%s:%s" % (repo.owner, item.get("base"))}
    body["merged"] = bool(item.get("merged"))
    body["merged_at"] = item.get("merged_at")
    body["merge_commit_sha"] = item.get("merge_commit_sha")
    body["draft"] = False
    body["html_url"] = "https://forge.invalid/%s/%s/pull/%d" % (
        repo.owner, repo.name, item["number"])
    body["url"] = "https://forge.invalid/api/v3/repos/%s/%s/pulls/%d" % (
        repo.owner, repo.name, item["number"])
    return body


def comment_json(repo, item, comment):
    return {
        "id": comment["id"],
        "node_id": global_id("IssueComment", comment["id"]),
        "body": comment["body"],
        "user": user_json(),
        "created_at": iso8601(comment["ts"]),
        "updated_at": iso8601(comment["ts"]),
        "html_url": "https://forge.invalid/%s/%s/issues/%d#issuecomment-%d" % (
            repo.owner, repo.name, item["number"], comment["id"]),
        "url": "https://forge.invalid/api/v3/repos/%s/%s/issues/comments/%d" % (
            repo.owner, repo.name, comment["id"]),
    }


def new_item(repo, kind, title, body, labels=None):
    number = repo.next_number
    repo.next_number += 1
    now = int(time.time())
    item = {
        "kind": kind,
        "number": number,
        "id": repo.alloc_id(),
        "title": title or "",
        "body": body or "",
        "state": "open",
        "labels": list(labels or []),
        "comments": [],
        "seq": _next_seq(),
        "created_ts": now,
        "updated_ts": now,
        "merged": False,
        "merged_at": None,
        "merge_commit_sha": None,
        "head": None,
        "base": None,
    }
    repo.items[number] = item
    return item


def add_comment(repo, item, body):
    comment = {"id": repo.alloc_id(), "body": body or "", "ts": int(time.time()),
               "seq": _next_seq()}
    item["comments"].append(comment)
    COMMENT_INDEX[comment["id"]] = (repo, item["number"])
    return comment


def repo_tree_flat(repo, commit_oid):
    if commit_oid is None:
        return {}
    info = parse_commit(commit_oid)
    if info is None:
        return {}
    return flatten_tree(info["tree"])


def pull_merge_state(repo, item):
    """(mergeable_bool, merged_flat, base_oid) for a pull request item."""
    base_tip = repo.branch_tip(item["base"])
    head_tip = repo.branch_tip(item["head"])
    if base_tip is None or head_tip is None:
        return False, None, None
    base_commit = peel_to_commit(base_tip)
    head_commit = peel_to_commit(head_tip)
    if base_commit is None or head_commit is None:
        return False, None, None
    ancestor = merge_base(base_commit, head_commit)
    base_flat = repo_tree_flat(repo, ancestor)
    ours_flat = repo_tree_flat(repo, base_commit)
    theirs_flat = repo_tree_flat(repo, head_commit)
    merged_flat, conflicts = three_way_merge(base_flat, ours_flat, theirs_flat)
    return (len(conflicts) == 0), merged_flat, (base_commit, head_commit, ancestor)


def pull_files(repo, item):
    state = pull_merge_state(repo, item)
    if state[2] is None:
        return []
    _, _, (base_commit, head_commit, ancestor) = state
    base_flat = repo_tree_flat(repo, ancestor)
    head_flat = repo_tree_flat(repo, head_commit)
    return diff_flats(base_flat, head_flat)


def perform_merge(repo, item):
    """Squash-merge a PR into its base branch.

    Returns (ok, merge_commit_sha_or_error_message).
    """
    if item.get("merged"):
        return False, "Pull Request is already merged"
    ok, merged_flat, tips = pull_merge_state(repo, item)
    if tips is None:
        return False, "Pull Request is not mergeable"
    if not ok:
        return False, "Pull Request is not mergeable"
    base_commit, _, _ = tips
    tree_oid = tree_oid_from_flat(merged_flat)
    message = "%s (#%d)" % (item["title"], item["number"])
    if item["body"]:
        message += "\n\n" + item["body"]
    commit_oid = create_commit(tree_oid, [base_commit], message)
    repo.refs["refs/heads/" + item["base"]] = commit_oid
    item["merged"] = True
    item["merged_at"] = iso8601(int(time.time()))
    item["merge_commit_sha"] = commit_oid
    item["state"] = "closed"
    item["updated_ts"] = int(time.time())
    return True, commit_oid


# --------------------------------------------------------------------------
# GraphQL global ids: opaque, stable, never the bare database id.
# --------------------------------------------------------------------------


def global_id(kind, *parts):
    raw = ":".join([kind] + [str(p) for p in parts])
    return base64.urlsafe_b64encode(raw.encode()).decode()


def parse_global_id(value):
    try:
        raw = base64.urlsafe_b64decode(value.encode()).decode()
    except Exception:
        return None
    parts = raw.split(":")
    return parts[0], parts[1:]


# --------------------------------------------------------------------------
# REST v3 API. Handlers return (status, body_bytes, content_type, headers).
# --------------------------------------------------------------------------


def J(status, obj, extra=None):
    return (status, json.dumps(obj).encode(), "application/json", extra or {})


def ERR(status, message):
    return J(status, {"message": message})


def parse_body(raw):
    """JSON request body -> (value, error_reply). Empty body reads as {}."""
    if raw is None or raw.strip() == b"":
        return {}, None
    try:
        value = json.loads(raw.decode("utf-8"))
    except Exception:
        return None, ERR(400, "Problems parsing JSON")
    if not isinstance(value, dict):
        return {}, None
    return value, None


def page_of(items, query):
    try:
        per_page = int(query.get("per_page", ["30"])[0])
    except (ValueError, TypeError):
        per_page = 30
    per_page = max(1, min(100, per_page))
    try:
        page = int(query.get("page", ["1"])[0])
    except (ValueError, TypeError):
        page = 1
    page = max(1, page)
    start = (page - 1) * per_page
    return items[start:start + per_page], per_page, page


def link_header(host, path, per_page, page, total):
    last = max(1, (total + per_page - 1) // per_page)
    if page >= last:
        return None
    parts = [
        '<http://%s%s?per_page=%d&page=%d>; rel="next"' % (host, path, per_page, page + 1),
        '<http://%s%s?per_page=%d&page=%d>; rel="last"' % (host, path, per_page, last),
    ]
    return ", ".join(parts)


def commit_json(oid):
    info = parse_commit(oid)
    author = parse_ident(info["author"]) if info else {"name": "", "email": "", "ts": 0}
    committer = parse_ident(info["committer"]) if info else {"name": "", "email": "", "ts": 0}
    return {
        "sha": oid,
        "node_id": global_id("Commit", oid),
        "commit": {
            "message": info["message"] if info else "",
            "author": {"name": author["name"], "email": author["email"],
                       "date": iso8601(author["ts"])},
            "committer": {"name": committer["name"], "email": committer["email"],
                          "date": iso8601(committer["ts"])},
            "tree": {"sha": info["tree"] if info else None},
        },
        "author": user_json(),
        "committer": user_json(),
        "parents": [{"sha": p} for p in (info["parents"] if info else [])],
    }


def walk_commit_list(start_oid, limit=10000):
    ancestors = commit_ancestors(start_oid)
    def ts_of(oid):
        info = parse_commit(oid)
        if not info:
            return 0
        return parse_ident(info["committer"] or info["author"])["ts"]
    return sorted(ancestors[:limit], key=lambda oid: -ts_of(oid))


def resolve_commit_ref(repo, ref):
    """A branch name, 'HEAD', or a full sha -> commit oid or None."""
    if ref is None:
        tip = repo.default_tip()
        return peel_to_commit(tip) if tip else None
    if ref == "HEAD":
        tip = repo.default_tip()
        return peel_to_commit(tip) if tip else None
    tip = repo.branch_tip(ref)
    if tip:
        return peel_to_commit(tip)
    if re.fullmatch(r"[0-9a-f]{40}", ref or "") and object_type(ref) == "commit":
        return ref
    return None


def rest_root():
    return J(200, {
        "current_user_url": "/api/v3/user",
        "current_user_repositories_url": "/api/v3/user/repos",
        "rate_limit_url": "/api/v3/rate_limit",
        "repository_url": "/api/v3/repos/{owner}/{repo}",
        "issue_url": "/api/v3/repos/{owner}/{repo}/issues/{number}",
        "organization_repositories_url": "/api/v3/orgs/{org}/repos",
        "emojis_url": "/api/v3/emojis",
        "feeds_url": "/api/v3/feeds",
        "meta_url": "/api/v3/meta",
    })


def rest_repos(method, segs, query, raw, host, path):
    """segs: everything after /api/v3/repos (or the repo subroutes)."""
    owner, name = segs[0], segs[1]
    rest = segs[2:]
    if owner != VIEWER_LOGIN:
        return ERR(404, "Not Found")
    repo = get_repo(owner, name)

    if not rest:
        if method == "GET":
            if repo is None:
                return ERR(404, "Not Found")
            return J(200, repo_json(repo, host))
        if repo is None:
            return ERR(404, "Not Found")
        if method == "PATCH":
            body, err = parse_body(raw)
            if err:
                return err
            if "description" in body:
                repo.description = body.get("description") or ""
            if "private" in body:
                repo.private = bool(body.get("private"))
            if "default_branch" in body and body.get("default_branch"):
                repo.default_branch = str(body["default_branch"])
            if "name" in body and body.get("name") and body["name"] != repo.name:
                new_name = str(body["name"])
                if get_repo(owner, new_name) is not None:
                    return ERR(422, "Validation Failed")
                del REPOS[(owner, repo.name)]
                repo.name = new_name
                REPOS[(owner, new_name)] = repo
            repo.updated_at = int(time.time())
            return J(200, repo_json(repo, host))
        if method == "DELETE":
            delete_repo(repo)
            return (204, b"", None, {})
        return ERR(404, "Not Found")

    if repo is None:
        return ERR(404, "Not Found")

    head = rest[0]

    if head == "branches":
        if len(rest) == 1 and method == "GET":
            branches = []
            for ref in sorted(repo.refs):
                if ref.startswith("refs/heads/"):
                    branches.append({
                        "name": ref[len("refs/heads/"):],
                        "commit": {"sha": repo.refs[ref]},
                        "protected": False,
                    })
            return J(200, branches)
        if len(rest) >= 2 and method == "GET":
            branch = "/".join(rest[1:])
            tip = repo.branch_tip(branch)
            if tip is None:
                return ERR(404, "Not Found")
            return J(200, {"name": branch, "commit": {"sha": tip},
                           "protected": False})
        return ERR(404, "Not Found")

    if head == "commits":
        if len(rest) == 1 and method == "GET":
            start = resolve_commit_ref(repo, query.get("sha", [None])[0])
            if start is None:
                return J(200, [])
            commits = walk_commit_list(start)
            page_items, _, _ = page_of(commits, query)
            return J(200, [commit_json(oid) for oid in page_items])
        if len(rest) == 2 and method == "GET":
            oid = rest[1]
            if object_type(oid) != "commit":
                return ERR(404, "Not Found")
            return J(200, commit_json(oid))
        return ERR(404, "Not Found")

    if head == "git" and len(rest) >= 2 and rest[1] == "refs":
        if len(rest) == 2 and method == "POST":
            body, err = parse_body(raw)
            if err:
                return err
            ref = body.get("ref")
            sha = body.get("sha")
            if not ref or not isinstance(ref, str) or not ref.startswith("refs/"):
                return ERR(422, "Validation Failed")
            if not sha or object_type(sha) is None:
                return ERR(422, "Validation Failed")
            if ref in repo.refs:
                return ERR(422, "Reference already exists")
            repo.refs[ref] = sha
            return J(201, {"ref": ref, "node_id": "",
                           "object": {"type": object_type(sha), "sha": sha}})
        if len(rest) >= 3 and method == "GET":
            tail = "/".join(rest[2:])
            ref = tail if tail.startswith("refs/") else "refs/" + tail
            oid = repo.refs.get(ref)
            if oid is None:
                return ERR(404, "Not Found")
            return J(200, {"ref": ref, "node_id": "",
                           "object": {"type": object_type(oid), "sha": oid}})
        return ERR(404, "Not Found")

    if head == "contents":
        tail = "/".join(rest[1:])
        return rest_contents(repo, method, tail, query, raw)

    if head == "labels":
        if method == "POST" and len(rest) == 1:
            body, err = parse_body(raw)
            if err:
                return err
            lname = body.get("name")
            if not lname:
                return ERR(422, "Validation Failed")
            if lname in repo.labels:
                return ERR(422, "Validation Failed")
            color = str(body.get("color") or "000000").lstrip("#")
            repo.labels[lname] = {"name": lname, "color": color}
            return J(201, label_json(repo.labels[lname]))
        if method == "GET" and len(rest) == 1:
            return J(200, [label_json(repo.labels[n]) for n in sorted(repo.labels)])
        return ERR(404, "Not Found")

    if head == "issues":
        return rest_issues(repo, method, rest[1:], query, raw)
    if head == "pulls":
        return rest_pulls(repo, method, rest[1:], query, raw)
    return ERR(404, "Not Found")


def rest_contents(repo, method, path, query, raw):
    if method == "GET":
        ref = query.get("ref", [None])[0]
        commit = resolve_commit_ref(repo, ref)
        if commit is None:
            return ERR(404, "Not Found")
        info = parse_commit(commit)
        found = tree_entry_at(info["tree"], path)
        if found is None:
            return ERR(404, "Not Found")
        kind, oid, extra = found
        if kind == "file":
            data = OBJECTS[oid][1]
            return J(200, {
                "type": "file",
                "encoding": "base64",
                "size": len(data),
                "name": path.split("/")[-1],
                "path": path,
                "sha": oid,
                "content": base64.b64encode(data).decode(),
            })
        entries = []
        prefix = (path + "/") if path else ""
        for mode, ename, child in extra:
            entries.append({
                "type": "dir" if mode == "40000" else "file",
                "name": ename,
                "path": prefix + ename,
                "sha": child,
                "size": 0,
            })
        return J(200, entries)

    body, err = parse_body(raw)
    if err:
        return err
    branch = body.get("branch") or repo.default_branch
    tip = repo.branch_tip(branch)
    if tip is None and repo.refs:
        return ERR(422, "Validation Failed")
    if tip is None and branch != repo.default_branch:
        return ERR(422, "Validation Failed")
    flat = repo_tree_flat(repo, peel_to_commit(tip) if tip else None)
    existing = flat.get(path)
    message = body.get("message") or ("Update %s" % path)

    if method == "PUT":
        content = body.get("content")
        if content is None:
            return ERR(422, "Validation Failed")
        sha_given = body.get("sha")
        if existing is not None and sha_given is None:
            return ERR(422, "\"sha\" wasn't supplied")
        if existing is not None and sha_given != existing[1]:
            return ERR(409, "%s does not match %s" % (path, sha_given))
        try:
            data = base64.b64decode(re.sub(r"\s+", "", str(content)))
        except Exception:
            return ERR(422, "Validation Failed")
        blob_oid = store_object("blob", data)
        new_flat = dict(flat)
        new_flat[path] = ("100644", blob_oid)
        tree_oid = tree_oid_from_flat(new_flat)
        parents = [peel_to_commit(tip)] if tip else []
        commit_oid = create_commit(tree_oid, parents, message)
        repo.refs["refs/heads/" + branch] = commit_oid
        status = 200 if existing is not None else 201
        return J(status, {
            "content": {
                "type": "file",
                "encoding": "base64",
                "size": len(data),
                "name": path.split("/")[-1],
                "path": path,
                "sha": blob_oid,
            },
            "commit": {"sha": commit_oid, "message": message},
        })

    if method == "DELETE":
        if existing is None:
            return ERR(404, "Not Found")
        sha_given = body.get("sha")
        if sha_given is None:
            return ERR(422, "\"sha\" wasn't supplied")
        if sha_given != existing[1]:
            return ERR(409, "%s does not match %s" % (path, sha_given))
        new_flat = dict(flat)
        del new_flat[path]
        tree_oid = tree_oid_from_flat(new_flat)
        parents = [peel_to_commit(tip)] if tip else []
        commit_oid = create_commit(tree_oid, parents, message)
        repo.refs["refs/heads/" + branch] = commit_oid
        return J(200, {"content": None,
                       "commit": {"sha": commit_oid, "message": message}})
    return ERR(404, "Not Found")


def _label_names(repo, raw_labels):
    """Validate a labels array -> (names, error_reply)."""
    names = []
    if raw_labels is None:
        return names, None
    if not isinstance(raw_labels, list):
        return None, ERR(422, "Validation Failed")
    for entry in raw_labels:
        lname = entry.get("name") if isinstance(entry, dict) else entry
        if lname not in repo.labels:
            return None, ERR(422, "Validation Failed")
        names.append(lname)
    return names, None


def rest_issues(repo, method, rest, query, raw):
    if not rest:
        if method == "POST":
            body, err = parse_body(raw)
            if err:
                return err
            if not body.get("title"):
                return ERR(422, "Validation Failed")
            names, err = _label_names(repo, body.get("labels"))
            if err:
                return err
            item = new_item(repo, "issue", body.get("title"), body.get("body"), names)
            return J(201, issue_json(repo, item))
        if method == "GET":
            state = query.get("state", ["open"])[0]
            items = [i for i in repo.items.values() if i["kind"] == "issue"]
            if state in ("open", "closed"):
                items = [i for i in items if i["state"] == state]
            direction = query.get("direction", ["desc"])[0]
            items.sort(key=lambda i: i["seq"], reverse=(direction != "asc"))
            page_items, _, _ = page_of(items, query)
            return J(200, [issue_json(repo, i) for i in page_items])
        return ERR(404, "Not Found")

    try:
        number = int(rest[0])
    except ValueError:
        return ERR(404, "Not Found")
    item = repo.items.get(number)
    if item is None or item["kind"] != "issue":
        return ERR(404, "Not Found")

    if len(rest) == 1:
        if method == "GET":
            return J(200, issue_json(repo, item))
        if method == "PATCH":
            body, err = parse_body(raw)
            if err:
                return err
            if "labels" in body:
                names, err = _label_names(repo, body.get("labels"))
                if err:
                    return err
                item["labels"] = names
            if "title" in body:
                item["title"] = body.get("title") or ""
            if "body" in body:
                item["body"] = body.get("body") or ""
            if "state" in body and body["state"] in ("open", "closed"):
                item["state"] = body["state"]
            item["updated_ts"] = int(time.time())
            return J(200, issue_json(repo, item))
        return ERR(404, "Not Found")

    if len(rest) == 2 and rest[1] == "comments":
        if method == "POST":
            body, err = parse_body(raw)
            if err:
                return err
            if body.get("body") is None:
                return ERR(422, "Validation Failed")
            comment = add_comment(repo, item, body.get("body"))
            return J(201, comment_json(repo, item, comment))
        if method == "GET":
            comments = sorted(item["comments"], key=lambda c: c["seq"])
            page_items, _, _ = page_of(comments, query)
            return J(200, [comment_json(repo, item, c) for c in page_items])
    return ERR(404, "Not Found")


def rest_pulls(repo, method, rest, query, raw):
    if not rest:
        if method == "POST":
            body, err = parse_body(raw)
            if err:
                return err
            title = body.get("title")
            head = body.get("head")
            base = body.get("base")
            if not title or not head or not base:
                return ERR(422, "Validation Failed")
            if head == base:
                return ERR(422, "Validation Failed")
            if repo.branch_tip(head) is None or repo.branch_tip(base) is None:
                return ERR(422, "Validation Failed")
            for other in repo.items.values():
                if (other["kind"] == "pr" and other["state"] == "open"
                        and other["head"] == head and other["base"] == base):
                    return ERR(422, "Validation Failed")
            item = new_item(repo, "pr", title, body.get("body"))
            item["head"] = head
            item["base"] = base
            return J(201, pull_json(repo, item))
        if method == "GET":
            state = query.get("state", ["open"])[0]
            items = [i for i in repo.items.values() if i["kind"] == "pr"]
            if state in ("open", "closed"):
                items = [i for i in items if i["state"] == state]
            direction = query.get("direction", ["desc"])[0]
            items.sort(key=lambda i: i["seq"], reverse=(direction != "asc"))
            page_items, _, _ = page_of(items, query)
            return J(200, [pull_json(repo, i) for i in page_items])
        return ERR(404, "Not Found")

    try:
        number = int(rest[0])
    except ValueError:
        return ERR(404, "Not Found")
    item = repo.items.get(number)
    if item is None or item["kind"] != "pr":
        return ERR(404, "Not Found")

    if len(rest) == 1 and method == "GET":
        return J(200, pull_json(repo, item))
    if len(rest) == 2 and rest[1] == "files" and method == "GET":
        files = pull_files(repo, item)
        page_items, _, _ = page_of(files, query)
        return J(200, page_items)
    if len(rest) == 2 and rest[1] == "merge" and method == "PUT":
        _, err = parse_body(raw)
        if err:
            return err
        ok, result = perform_merge(repo, item)
        if not ok:
            return ERR(405, result)
        return J(200, {"sha": result, "merged": True,
                       "message": "Pull Request successfully merged"})
    return ERR(404, "Not Found")


def handle_rest(method, segs, query, raw, host, path):
    """segs: path segments after the host root (api/v3 already stripped)."""
    if not segs:
        if method == "GET":
            return rest_root()
        return ERR(404, "Not Found")
    head = segs[0]
    if head == "meta" and method == "GET":
        return J(200, {"installed_version": INSTALLED_VERSION})
    if head == "rate_limit" and method == "GET":
        rate = {"limit": 5000, "remaining": 4999,
                "reset": int(time.time()) + 3600, "used": 1}
        return J(200, {"resources": {"core": rate}, "rate": rate})
    if head == "user":
        if len(segs) == 1 and method == "GET":
            return J(200, user_json())
        if len(segs) == 2 and segs[1] == "repos":
            if method == "POST":
                body, err = parse_body(raw)
                if err:
                    return err
                name = body.get("name")
                if not name or not isinstance(name, str):
                    return ERR(422, "Validation Failed")
                if get_repo(VIEWER_LOGIN, name) is not None:
                    return ERR(422, "name already exists on this account")
                repo = create_repo(VIEWER_LOGIN, name,
                                   bool(body.get("private")),
                                   body.get("description") or "")
                return J(201, repo_json(repo, host))
            if method == "GET":
                repos = [r for r in REPOS.values() if r.owner == VIEWER_LOGIN]
                repos.sort(key=lambda r: r.created_seq)
                page_items, per_page, page = page_of(repos, query)
                extra = {}
                link = link_header(host, path, per_page, page, len(repos))
                if link:
                    extra["Link"] = link
                return J(200, [repo_json(r, host) for r in page_items], extra)
        return ERR(404, "Not Found")
    if head == "repos" and len(segs) >= 3:
        return rest_repos(method, segs[1:], query, raw, host, path)
    if head == "search" and method == "GET" and len(segs) == 2:
        q = query.get("q", [""])[0].lower()
        if segs[1] == "repositories":
            items = [repo_json(r, host) for r in REPOS.values()
                     if r.owner == VIEWER_LOGIN and q in r.name.lower()]
            return J(200, {"total_count": len(items),
                           "incomplete_results": False, "items": items})
        if segs[1] == "issues":
            items = []
            for r in REPOS.values():
                if r.owner != VIEWER_LOGIN:
                    continue
                for it in r.items.values():
                    if q in it["title"].lower():
                        items.append(issue_json(r, it))
            return J(200, {"total_count": len(items),
                           "incomplete_results": False, "items": items})
        if segs[1] == "users":
            items = [user_json()] if q in VIEWER_LOGIN else []
            return J(200, {"total_count": len(items),
                           "incomplete_results": False, "items": items})
    return ERR(404, "Not Found")


# --------------------------------------------------------------------------
# Git smart HTTP.
# --------------------------------------------------------------------------

UPLOAD_CAPS = ("multi_ack_detailed no-done side-band-64k thin-pack ofs-delta "
               "shallow deepen-since deepen-not agent=forge/1.0")
RECEIVE_CAPS = "report-status delete-refs side-band-64k ofs-delta agent=forge/1.0"
AGENT_CAP = "agent=forge/1.0"


def sorted_refs(repo):
    return sorted(repo.refs.items())


def ref_advertisement_lines(repo, caps):
    lines = []
    head_ref = "refs/heads/" + repo.default_branch
    tip = repo.refs.get(head_ref)
    first = True
    if tip is not None:
        lines.append("%s HEAD\x00%s symref=HEAD:%s\n" % (tip, caps, head_ref))
        first = False
    elif not repo.refs:
        lines.append("%s capabilities^{}\x00%s\n" % (ZERO_OID, caps))
        first = False
    for ref, oid in sorted_refs(repo):
        suffix = "\x00" + caps if first else ""
        lines.append("%s %s%s\n" % (oid, ref, suffix))
        first = False
        if object_type(oid) == "tag":
            target = peel_target(oid)
            if target:
                lines.append("%s %s^{}\n" % (target, ref))
    if first:  # refs exist but HEAD unborn and refs non-empty handled above
        lines.append("%s capabilities^{}\x00%s\n" % (ZERO_OID, caps))
    return lines


def handle_info_refs(repo, service, git_protocol):
    if service == "git-upload-pack":
        ctype = "application/x-git-upload-pack-advertisement"
        if git_protocol and "version=2" in git_protocol:
            body = (pkt("version 2\n") + pkt(AGENT_CAP + "\n")
                    + pkt("ls-refs=unborn\n") + pkt("fetch=shallow\n")
                    + pkt("object-format=sha1\n") + PKT_FLUSH)
            return (200, body, ctype, {})
        body = pkt("# service=git-upload-pack\n") + PKT_FLUSH
        for line in ref_advertisement_lines(repo, UPLOAD_CAPS):
            body += pkt(line)
        body += PKT_FLUSH
        return (200, body, ctype, {})
    if service == "git-receive-pack":
        ctype = "application/x-git-receive-pack-advertisement"
        body = pkt("# service=git-receive-pack\n") + PKT_FLUSH
        lines = []
        first = True
        for ref, oid in sorted_refs(repo):
            suffix = "\x00" + RECEIVE_CAPS if first else ""
            lines.append("%s %s%s\n" % (oid, ref, suffix))
            first = False
            if object_type(oid) == "tag":
                target = peel_target(oid)
                if target:
                    lines.append("%s %s^{}\n" % (target, ref))
        if first:
            lines.append("%s capabilities^{}\x00%s\n" % (ZERO_OID, RECEIVE_CAPS))
        for line in lines:
            body += pkt(line)
        body += PKT_FLUSH
        return (200, body, ctype, {})
    return ERR(404, "Not Found")


def collect_fetch_objects(wants, haves, depth, client_shallow):
    """-> (objects, shallow_oids, unshallow_oids) for an upload-pack reply."""
    from collections import deque

    included = {}
    order = []

    def include(oid):
        if oid not in included:
            obj = OBJECTS.get(oid)
            if obj is not None:
                included[oid] = obj
                order.append(oid)

    def include_tree(tree_oid):
        stack = [tree_oid]
        while stack:
            current = stack.pop()
            if current is None or current in included:
                continue
            include(current)
            for mode, _name, child in parse_tree(current):
                if mode == "40000":
                    stack.append(child)
                else:
                    include(child)

    dist = {}
    queue = deque()
    for want in wants:
        type_name = object_type(want)
        if type_name == "tag":
            current = want
            while object_type(current) == "tag":
                include(current)
                current = peel_target(current)
            if current and object_type(current) == "commit":
                queue.append((current, 1))
        elif type_name == "commit":
            queue.append((want, 1))
        elif type_name == "tree":
            include_tree(want)
        elif type_name == "blob":
            include(want)

    boundary = set()
    while queue:
        oid, distance = queue.popleft()
        if oid in dist and dist[oid] <= distance:
            continue
        dist[oid] = distance
        include(oid)
        info = parse_commit(oid)
        if info is None:
            continue
        include_tree(info["tree"])
        if depth is not None and distance >= depth:
            if info["parents"]:
                boundary.add(oid)
            continue
        for parent in info["parents"]:
            queue.append((parent, distance + 1))

    excluded = set()

    def exclude_tree(tree_oid):
        stack = [tree_oid]
        while stack:
            current = stack.pop()
            if current in excluded:
                continue
            obj = OBJECTS.get(current)
            if obj is None:
                continue
            excluded.add(current)
            if obj[0] == "tree":
                for mode, _name, child in parse_tree(current):
                    stack.append(child)

    seen = set()
    stack = list(haves)
    while stack:
        oid = stack.pop()
        if oid in seen:
            continue
        seen.add(oid)
        type_name = object_type(oid)
        if type_name == "tag":
            excluded.add(oid)
            target = peel_target(oid)
            if target:
                stack.append(target)
            continue
        if type_name != "commit":
            excluded.add(oid)
            continue
        excluded.add(oid)
        info = parse_commit(oid)
        if info is None:
            continue
        exclude_tree(info["tree"])
        if oid in client_shallow:
            continue
        stack.extend(info["parents"])

    send = [oid for oid in order if oid not in excluded]
    send_set = set(send)
    objects = [included[oid] for oid in send]
    shallow = {oid for oid in boundary if oid in send_set}
    unshallow = {oid for oid in client_shallow
                 if oid in dist and (depth is None or dist[oid] < depth)}
    return objects, shallow, unshallow


def sideband_chunks(data):
    out = bytearray()
    for i in range(0, len(data), 32768):
        out += pkt(b"\x01" + data[i:i + 32768])
    return bytes(out)


def ls_refs_reply(repo, args):
    peel = "peel" in args
    symrefs = "symrefs" in args
    unborn = "unborn" in args
    prefixes = [a[len("ref-prefix "):] for a in args if a.startswith("ref-prefix ")]

    def wanted(name):
        if not prefixes:
            return True
        return any(name.startswith(p) for p in prefixes)

    out = bytearray()
    head_ref = "refs/heads/" + repo.default_branch
    tip = repo.refs.get(head_ref)
    if wanted("HEAD"):
        if tip is not None:
            line = "%s HEAD" % tip
            if symrefs:
                line += " symref-target:%s" % head_ref
            out += pkt(line + "\n")
        elif unborn:
            line = "unborn HEAD"
            if symrefs:
                line += " symref-target:%s" % head_ref
            out += pkt(line + "\n")
    for ref, oid in sorted_refs(repo):
        if not wanted(ref):
            continue
        line = "%s %s" % (oid, ref)
        if peel and object_type(oid) == "tag":
            target = peel_target(oid)
            if target:
                line += " peeled:%s" % target
        out += pkt(line + "\n")
    out += PKT_FLUSH
    return bytes(out)


def fetch_reply(repo, wants, haves, depth, client_shallow, shallow_section):
    objects, shallow, unshallow = collect_fetch_objects(
        wants, haves, depth, client_shallow)
    pack = write_pack(objects)
    out = bytearray()
    if shallow_section:
        out += pkt("shallow-info\n")
        for oid in sorted(shallow):
            out += pkt("shallow %s\n" % oid)
        for oid in sorted(unshallow):
            out += pkt("unshallow %s\n" % oid)
        out += PKT_FLUSH
    out += pkt("packfile\n")
    out += sideband_chunks(pack)
    out += PKT_FLUSH
    return bytes(out)


def handle_upload_pack(repo, body, version2):
    try:
        if version2:
            lines = []
            pos = 0
            command = None
            args = []
            seen_delim = False
            while True:
                payload, pos = read_pkt_line(body, pos)
                if payload == "flush":
                    break
                if payload == "delim":
                    seen_delim = True
                    continue
                if payload in ("response-end",):
                    break
                text = payload.decode("utf-8", "replace").rstrip("\n")
                if not seen_delim:
                    if text.startswith("command="):
                        command = text[len("command="):]
                    lines.append(text)
                else:
                    args.append(text)
            if command == "ls-refs":
                return (200, ls_refs_reply(repo, args),
                        "application/x-git-upload-pack-result", {})
            if command == "fetch":
                wants, haves, client_shallow = [], [], set()
                depth = None
                done = False
                shallow_section = False
                for arg in args:
                    if arg.startswith("want "):
                        wants.append(arg[5:].strip())
                    elif arg.startswith("have "):
                        haves.append(arg[5:].strip())
                    elif arg.startswith("shallow "):
                        client_shallow.add(arg[8:].strip())
                        shallow_section = True
                    elif arg.startswith("deepen "):
                        try:
                            depth = int(arg[len("deepen "):].strip())
                        except ValueError:
                            pass
                        shallow_section = True
                    elif arg == "done":
                        done = True
                if not done:
                    return (200, pkt("acknowledgments\n") + pkt("NAK\n") + PKT_FLUSH,
                            "application/x-git-upload-pack-result", {})
                return (200, fetch_reply(repo, wants, haves, depth,
                                         client_shallow, shallow_section),
                        "application/x-git-upload-pack-result", {})
            return ERR(400, "unknown command")
        # Protocol v0 fallback. The request is two pkt-line sections
        # (wants/deepen, flush, haves/done, flush): read through both.
        wants, haves, client_shallow = [], [], set()
        depth = None
        done = False
        caps = ""
        pos = 0
        flushes = 0
        while flushes < 2:
            payload, pos = read_pkt_line(body, pos)
            if payload == "flush":
                flushes += 1
                continue
            if not isinstance(payload, bytes):
                continue
            text = payload.decode("utf-8", "replace").rstrip("\n")
            if "\x00" in text:
                text, caps = text.split("\x00", 1)
            if " " in text and text.startswith("want "):
                # v0 puts the capability list after the oid on the first want line
                text = text.split(" ")[0] + " " + text.split(" ")[1]
            if text.startswith("want "):
                wants.append(text[5:].strip())
            elif text.startswith("have "):
                haves.append(text[5:].strip())
            elif text.startswith("shallow "):
                client_shallow.add(text[8:].strip())
            elif text.startswith("deepen "):
                try:
                    depth = int(text[len("deepen "):].strip())
                except ValueError:
                    pass
            elif text == "done":
                done = True
        objects, shallow_v0, unshallow_v0 = collect_fetch_objects(
            wants, haves, depth, client_shallow)
        pack = write_pack(objects)
        out = bytearray()
        if done:
            for oid in sorted(shallow_v0):
                out += pkt("shallow %s\n" % oid)
            for oid in sorted(unshallow_v0):
                out += pkt("unshallow %s\n" % oid)
        out += pkt("NAK\n")
        if done:
            out += sideband_chunks(pack)
            out += PKT_FLUSH
        return (200, bytes(out), "application/x-git-upload-pack-result", {})
    except (ValueError, IndexError):
        return ERR(400, "malformed upload-pack body")


def apply_ref_update(repo, old, new, ref):
    if not (ref.startswith("refs/heads/") or ref.startswith("refs/tags/")):
        return (ref, False, "invalid ref")
    current = repo.refs.get(ref, ZERO_OID)
    if new == ZERO_OID:
        repo.refs.pop(ref, None)
        return (ref, True, None)
    if object_type(new) is None:
        return (ref, False, "invalid object")
    if old == ZERO_OID:
        if current != ZERO_OID:
            return (ref, False, "reference already exists")
        repo.refs[ref] = new
        return (ref, True, None)
    if current != old:
        return (ref, False, "stale info")
    new_commit = peel_to_commit(new)
    old_commit = peel_to_commit(old)
    if new_commit is None or old_commit is None:
        return (ref, False, "non-fast-forward")
    if not is_ancestor(old_commit, new_commit):
        return (ref, False, "non-fast-forward")
    repo.refs[ref] = new
    return (ref, True, None)


def handle_receive_pack(repo, body):
    commands = []
    caps = ""
    pos = 0
    try:
        while True:
            payload, pos = read_pkt_line(body, pos)
            if payload == "flush":
                break
            if not isinstance(payload, bytes):
                continue
            text = payload.decode("utf-8", "replace").rstrip("\n")
            if not commands and "\x00" in text:
                text, caps = text.split("\x00", 1)
            parts = text.split(" ")
            if len(parts) >= 3:
                commands.append((parts[0], parts[1], parts[2]))
    except (ValueError, IndexError):
        return ERR(400, "malformed receive-pack body")
    pack_data = body[pos:]
    unpack_ok = True
    if pack_data:
        try:
            parse_pack(pack_data)
        except ValueError:
            unpack_ok = False
    results = []
    for old, new, ref in commands:
        if unpack_ok:
            results.append(apply_ref_update(repo, old, new, ref))
        else:
            results.append((ref, False, "unpack failed"))
    repo.updated_at = int(time.time())
    if "report-status" not in caps:
        return (200, b"", "application/x-git-receive-pack-result", {})
    inner = bytearray()
    inner += pkt("unpack ok\n" if unpack_ok else "unpack failed\n")
    for ref, ok, reason in results:
        if ok:
            inner += pkt("ok %s\n" % ref)
        else:
            inner += pkt("ng %s %s\n" % (ref, reason))
    inner += PKT_FLUSH
    if "side-band-64k" in caps:
        out = sideband_chunks(bytes(inner)) + PKT_FLUSH
    else:
        out = bytes(inner)
    return (200, out, "application/x-git-receive-pack-result", {})


def handle_git(method, segs, query, raw, headers):
    """segs: [owner, '<repo>.git', ...rest]."""
    owner = segs[0]
    repo_name = segs[1][:-4]
    rest = segs[2:]
    if owner != VIEWER_LOGIN:
        return ERR(404, "Not Found")
    repo = get_repo(owner, repo_name)
    if repo is None:
        return ERR(404, "Not Found")
    if rest == ["info", "refs"] and method == "GET":
        service = query.get("service", [None])[0]
        if service not in ("git-upload-pack", "git-receive-pack"):
            return ERR(404, "Not Found")
        return handle_info_refs(repo, service, headers.get("git-protocol"))
    if rest == ["git-upload-pack"] and method == "POST":
        git_protocol = headers.get("git-protocol") or ""
        return handle_upload_pack(repo, raw, "version=2" in git_protocol)
    if rest == ["git-receive-pack"] and method == "POST":
        return handle_receive_pack(repo, raw)
    return ERR(404, "Not Found")


# --------------------------------------------------------------------------
# GraphQL: a small parser plus a resolver-based executor.
# --------------------------------------------------------------------------

_GQL_TOKEN_RE = re.compile(
    r"(?P<spread>\.\.\.)"
    r"|(?P<string>\"(?:\\.|[^\"\\])*\")"
    r"|(?P<float>-?\d+\.\d+(?:[eE][+-]?\d+)?)"
    r"|(?P<int>-?\d+)"
    r"|(?P<name>[_A-Za-z][_0-9A-Za-z]*)"
    r"|(?P<punct>[{}()\[\]:$@!=|&])"
)


def _gql_tokens(text):
    tokens = []
    pos = 0
    while pos < len(text):
        ch = text[pos]
        if ch in " \t\r\n,":
            pos += 1
            continue
        if ch == "#":
            while pos < len(text) and text[pos] != "\n":
                pos += 1
            continue
        if text.startswith('"""', pos):
            end = text.index('"""', pos + 3)
            tokens.append(("string", text[pos + 3:end]))
            pos = end + 3
            continue
        match = _GQL_TOKEN_RE.match(text, pos)
        if not match:
            raise ValueError("unexpected character %r" % ch)
        pos = match.end()
        kind = match.lastgroup
        value = match.group()
        if kind == "string":
            value = json.loads(value)
        elif kind == "int":
            value = int(value)
        elif kind == "float":
            value = float(value)
        tokens.append((kind, value))
    tokens.append(("eof", None))
    return tokens


class _GqlParser:
    def __init__(self, text):
        self.tokens = _gql_tokens(text)
        self.pos = 0

    def peek(self):
        return self.tokens[self.pos]

    def next(self):
        token = self.tokens[self.pos]
        self.pos += 1
        return token

    def expect_punct(self, ch):
        kind, value = self.next()
        if kind != "punct" or value != ch:
            raise ValueError("expected %r" % ch)

    def skip_punct(self, ch):
        kind, value = self.peek()
        if kind == "punct" and value == ch:
            self.pos += 1
            return True
        return False

    def expect_name(self):
        kind, value = self.next()
        if kind != "name":
            raise ValueError("expected a name")
        return value

    def parse_document(self):
        operations = []
        fragments = {}
        while self.peek()[0] != "eof":
            kind, value = self.peek()
            if kind == "punct" and value == "{":
                selection = self.parse_selection_set()
                operations.append({"kind": "query", "name": None,
                                   "selection": selection, "var_defaults": {}})
            elif kind == "name" and value in ("query", "mutation", "subscription"):
                self.next()
                op_name = None
                if self.peek()[0] == "name":
                    op_name = self.next()[1]
                var_defaults = {}
                if self.peek() == ("punct", "("):
                    var_defaults = self.parse_variable_definitions()
                # directives are skipped
                while self.peek() == ("punct", "@"):
                    self.next()
                    self.expect_name()
                    if self.peek() == ("punct", "("):
                        self.parse_arguments()
                selection = self.parse_selection_set()
                operations.append({"kind": value, "name": op_name,
                                   "selection": selection,
                                   "var_defaults": var_defaults})
            elif kind == "name" and value == "fragment":
                self.next()
                frag_name = self.expect_name()
                if self.expect_name() != "on":
                    raise ValueError("fragment needs a type condition")
                type_cond = self.expect_name()
                selection = self.parse_selection_set()
                fragments[frag_name] = {"type": type_cond, "selection": selection}
            else:
                raise ValueError("unexpected token in document")
        return operations, fragments

    def parse_variable_definitions(self):
        defaults = {}
        self.expect_punct("(")
        while not self.skip_punct(")"):
            self.expect_punct("$")
            name = self.expect_name()
            self.expect_punct(":")
            self.parse_type()
            if self.skip_punct("="):
                defaults[name] = self.parse_value()
        return defaults

    def parse_type(self):
        if self.skip_punct("["):
            self.parse_type()
            self.expect_punct("]")
        else:
            self.expect_name()
        self.skip_punct("!")

    def parse_selection_set(self):
        self.expect_punct("{")
        selections = []
        while not self.skip_punct("}"):
            selections.append(self.parse_selection())
        return selections

    def parse_selection(self):
        kind, value = self.peek()
        if kind == "spread":
            self.next()
            if self.peek()[0] == "name" and self.peek()[1] == "on":
                self.next()
                type_cond = self.expect_name()
                selection = self.parse_selection_set()
                return {"kind": "inline", "type": type_cond, "selection": selection}
            name = self.expect_name()
            return {"kind": "spread", "name": name}
        name = self.expect_name()
        alias = None
        if self.skip_punct(":"):
            alias = name
            name = self.expect_name()
        args = {}
        if self.peek() == ("punct", "("):
            args = self.parse_arguments()
        while self.peek() == ("punct", "@"):
            self.next()
            self.expect_name()
            if self.peek() == ("punct", "("):
                self.parse_arguments()
        selection = None
        if self.peek() == ("punct", "{"):
            selection = self.parse_selection_set()
        return {"kind": "field", "alias": alias, "name": name,
                "args": args, "selection": selection}

    def parse_arguments(self):
        args = {}
        self.expect_punct("(")
        while not self.skip_punct(")"):
            name = self.expect_name()
            self.expect_punct(":")
            args[name] = self.parse_value()
        return args

    def parse_value(self):
        kind, value = self.next()
        if kind == "punct" and value == "$":
            return ("var", self.expect_name())
        if kind == "string":
            return ("string", value)
        if kind == "int":
            return ("int", value)
        if kind == "float":
            return ("float", value)
        if kind == "name":
            if value == "true":
                return ("bool", True)
            if value == "false":
                return ("bool", False)
            if value == "null":
                return ("null", None)
            return ("enum", value)
        if kind == "punct" and value == "[":
            items = []
            while not self.skip_punct("]"):
                items.append(self.parse_value())
            return ("list", items)
        if kind == "punct" and value == "{":
            obj = {}
            while not self.skip_punct("}"):
                key = self.expect_name()
                self.expect_punct(":")
                obj[key] = self.parse_value()
            return ("object", obj)
        raise ValueError("unexpected value token")


def _eval_value(node, variables):
    kind = node[0]
    if kind == "var":
        return variables.get(node[1])
    if kind in ("string", "int", "float", "bool", "enum"):
        return node[1]
    if kind == "null":
        return None
    if kind == "list":
        return [_eval_value(v, variables) for v in node[1]]
    if kind == "object":
        return {k: _eval_value(v, variables) for k, v in node[1].items()}
    return None


def _encode_cursor(pos):
    return base64.urlsafe_b64encode(("cursor:%d" % pos).encode()).decode()


def _decode_cursor(cursor):
    try:
        raw = base64.urlsafe_b64decode(str(cursor).encode()).decode()
        if raw.startswith("cursor:"):
            return int(raw[len("cursor:"):])
    except Exception:
        pass
    return 0


def _connection(type_name, items, args):
    first = args.get("first")
    after = args.get("after")
    start = _decode_cursor(after) if after else 0
    if first is None:
        sliced = items[start:]
    else:
        sliced = items[start:start + int(first)]
    end_pos = start + len(sliced)
    edges = [{"node": item, "cursor": _encode_cursor(start + i + 1)}
             for i, item in enumerate(sliced)]
    page_info = {
        "hasNextPage": end_pos < len(items),
        "hasPreviousPage": start > 0,
        "startCursor": edges[0]["cursor"] if edges else None,
        "endCursor": edges[-1]["cursor"] if edges else None,
    }
    return (type_name, {"nodes": sliced, "edges": edges,
                        "pageInfo": ("PageInfo", page_info),
                        "totalCount": len(items)})


class _GqlContext:
    def __init__(self, variables, fragments):
        self.variables = variables
        self.fragments = fragments
        self.errors = []


def _repo_from_gid(value):
    parsed = parse_global_id(value or "")
    if not parsed:
        return None
    kind, parts = parsed
    if kind != "Repository" or not parts:
        return None
    try:
        return REPO_BY_DBID.get(int(parts[0]))
    except ValueError:
        return None


def _item_from_gid(value, want_kind=None):
    parsed = parse_global_id(value or "")
    if not parsed:
        return None, None
    kind, parts = parsed
    if len(parts) < 2:
        return None, None
    try:
        repo = REPO_BY_DBID.get(int(parts[0]))
        number = int(parts[1])
    except ValueError:
        return None, None
    if repo is None:
        return None, None
    item = repo.items.get(number)
    if item is None:
        return repo, None
    if want_kind and item["kind"] != want_kind:
        return repo, None
    return repo, item


def _node_from_gid(value):
    parsed = parse_global_id(value or "")
    if not parsed:
        return None
    kind, parts = parsed
    if kind == "Repository":
        repo = _repo_from_gid(value)
        return ("Repository", repo) if repo else None
    if kind in ("Issue", "PullRequest"):
        repo, item = _item_from_gid(value)
        if item is None:
            return None
        type_name = "Issue" if item["kind"] == "issue" else "PullRequest"
        return (type_name, (repo, item))
    if kind == "IssueComment":
        try:
            comment_id = int(parts[0])
        except (ValueError, IndexError):
            return None
        found = COMMENT_INDEX.get(comment_id)
        if not found:
            return None
        repo, number = found
        item = repo.items.get(number)
        if item is None:
            return None
        for comment in item["comments"]:
            if comment["id"] == comment_id:
                return ("IssueComment", (repo, item, comment))
        return None
    if kind == "User":
        return ("User", VIEWER_LOGIN)
    return None


_TYPE_FIELDS = {
    "Query": ["viewer", "repository", "node", "search", "organization",
              "user", "rateLimit"],
    "Mutation": ["createIssue", "closeIssue", "createPullRequest",
                 "mergePullRequest", "addComment"],
    "User": ["id", "login", "name", "email", "url", "avatarUrl",
             "createdAt", "updatedAt"],
    "Repository": ["id", "databaseId", "name", "nameWithOwner", "owner",
                   "description", "isPrivate", "url", "createdAt", "updatedAt",
                   "defaultBranchRef", "viewerPermission", "hasIssuesEnabled",
                   "issue", "issues", "pullRequest", "pullRequests", "labels",
                   "stargazerCount", "forkCount"],
    "Issue": ["id", "number", "title", "state", "body", "url", "createdAt",
              "updatedAt", "closedAt", "author", "repository", "labels",
              "comments"],
    "PullRequest": ["id", "number", "title", "state", "body", "merged",
                    "mergedAt", "closedAt", "headRefName", "baseRefName",
                    "headRef", "baseRef", "mergeable", "url", "createdAt",
                    "updatedAt", "author", "repository", "files", "additions",
                    "deletions", "changedFiles"],
    "IssueComment": ["id", "body", "createdAt", "updatedAt", "author", "url"],
    "Label": ["id", "name", "color", "description"],
    "Ref": ["name", "prefix", "target", "repository"],
    "PageInfo": ["hasNextPage", "hasPreviousPage", "startCursor", "endCursor"],
}

_ENUM_TYPES = {
    "SearchType": ["ISSUE", "REPOSITORY", "USER", "DISCUSSION", "CODE"],
    "IssueState": ["OPEN", "CLOSED"],
    "PullRequestState": ["OPEN", "CLOSED", "MERGED"],
    "MergeableState": ["MERGEABLE", "CONFLICTING", "UNKNOWN"],
    "RepositoryPermission": ["ADMIN", "MAINTAIN", "WRITE", "TRIAGE", "READ"],
    "OrderDirection": ["ASC", "DESC"],
}


def _type_info(name):
    if name in _TYPE_FIELDS:
        return ("__Type", {"name": name, "kind": "OBJECT",
                           "fields": [{"name": f} for f in _TYPE_FIELDS[name]],
                           "enumValues": None})
    if name in _ENUM_TYPES:
        return ("__Type", {"name": name, "kind": "ENUM", "fields": None,
                           "enumValues": [{"name": e} for e in _ENUM_TYPES[name]]})
    return None


def _issue_state(item):
    return "OPEN" if item["state"] == "open" else "CLOSED"


def _pr_state(item):
    if item.get("merged"):
        return "MERGED"
    return "OPEN" if item["state"] == "open" else "CLOSED"


def _filter_states(items, args, default, state_of):
    states = args.get("states")
    if states is None:
        states = default
    if isinstance(states, str):
        states = [states]
    wanted = {str(s).upper() for s in states}
    return [i for i in items if state_of(i) in wanted]


def _resolve_query(field, _payload, args, _ctx):
    if field == "viewer":
        return ("User", VIEWER_LOGIN)
    if field == "repository":
        owner = args.get("owner")
        name = args.get("name")
        if owner != VIEWER_LOGIN:
            return None
        repo = get_repo(owner, name)
        return ("Repository", repo) if repo else None
    if field == "node":
        return _node_from_gid(args.get("id"))
    if field == "__type":
        return _type_info(args.get("name"))
    if field == "user":
        if args.get("login") == VIEWER_LOGIN:
            return ("User", VIEWER_LOGIN)
        return None
    return _MISSING


def _resolve_mutation(field, _payload, args, ctx):
    if field == "createIssue":
        inp = args.get("input") or {}
        repo = _repo_from_gid(inp.get("repositoryId"))
        if repo is None:
            ctx.errors.append("repository not found")
            return ("CreateIssuePayload", {"issue": None})
        item = new_item(repo, "issue", inp.get("title"), inp.get("body"))
        return ("CreateIssuePayload", {
            "issue": ("Issue", (repo, item)),
            "clientMutationId": inp.get("clientMutationId")})
    if field == "closeIssue":
        inp = args.get("input") or {}
        repo, item = _item_from_gid(inp.get("issueId"), "issue")
        if item is None:
            ctx.errors.append("issue not found")
            return ("CloseIssuePayload", {"issue": None})
        item["state"] = "closed"
        item["updated_ts"] = int(time.time())
        return ("CloseIssuePayload", {
            "issue": ("Issue", (repo, item)),
            "clientMutationId": inp.get("clientMutationId")})
    if field == "createPullRequest":
        inp = args.get("input") or {}
        repo = _repo_from_gid(inp.get("repositoryId"))
        if repo is None:
            ctx.errors.append("repository not found")
            return ("CreatePullRequestPayload", {"pullRequest": None})
        item = new_item(repo, "pr", inp.get("title"), inp.get("body"))
        item["head"] = inp.get("headRefName")
        item["base"] = inp.get("baseRefName")
        return ("CreatePullRequestPayload", {
            "pullRequest": ("PullRequest", (repo, item)),
            "clientMutationId": inp.get("clientMutationId")})
    if field == "mergePullRequest":
        inp = args.get("input") or {}
        repo, item = _item_from_gid(inp.get("pullRequestId"), "pr")
        if item is None:
            ctx.errors.append("pull request not found")
            return ("MergePullRequestPayload", {"pullRequest": None})
        ok, result = perform_merge(repo, item)
        if not ok:
            ctx.errors.append(result)
        return ("MergePullRequestPayload", {
            "pullRequest": ("PullRequest", (repo, item)),
            "clientMutationId": inp.get("clientMutationId")})
    if field == "addComment":
        inp = args.get("input") or {}
        subject = _node_from_gid(inp.get("subjectId"))
        if subject is None or subject[0] not in ("Issue", "PullRequest"):
            ctx.errors.append("subject not found")
            return ("AddCommentPayload", {"commentEdge": None})
        repo, item = subject[1]
        comment = add_comment(repo, item, inp.get("body"))
        edge = ("IssueCommentEdge", {
            "node": ("IssueComment", (repo, item, comment)), "cursor": ""})
        return ("AddCommentPayload", {
            "commentEdge": edge,
            "clientMutationId": inp.get("clientMutationId")})
    return _MISSING


def _resolve_repository(field, repo, args, _ctx):
    if field == "id":
        return global_id("Repository", repo.dbid)
    if field == "databaseId":
        return repo.dbid
    if field == "name":
        return repo.name
    if field == "nameWithOwner":
        return "%s/%s" % (repo.owner, repo.name)
    if field == "owner":
        return ("User", repo.owner)
    if field == "description":
        return repo.description
    if field == "isPrivate":
        return repo.private
    if field == "url":
        return "https://forge.invalid/%s/%s" % (repo.owner, repo.name)
    if field == "createdAt":
        return iso8601(repo.created_at)
    if field == "updatedAt":
        return iso8601(repo.updated_at)
    if field == "defaultBranchRef":
        if repo.default_tip() is None:
            return None
        return ("Ref", {"name": repo.default_branch, "repo": repo})
    if field == "viewerPermission":
        return "ADMIN"
    if field == "hasIssuesEnabled":
        return True
    if field == "stargazerCount":
        return 0
    if field == "forkCount":
        return 0
    if field == "issue":
        item = repo.items.get(int(args.get("number") or 0))
        if item is not None and item["kind"] == "issue":
            return ("Issue", (repo, item))
        return None
    if field == "issues":
        items = [i for i in repo.items.values() if i["kind"] == "issue"]
        items = _filter_states(items, args, ["OPEN", "CLOSED"], _issue_state)
        order_by = args.get("orderBy") or {}
        direction = str(order_by.get("direction") or "ASC").upper()
        items.sort(key=lambda i: i["number"])
        if direction == "DESC":
            items.sort(key=lambda i: i["seq"], reverse=True)
        return _connection("IssueConnection",
                           [("Issue", (repo, i)) for i in items], args)
    if field == "pullRequest":
        item = repo.items.get(int(args.get("number") or 0))
        if item is not None and item["kind"] == "pr":
            return ("PullRequest", (repo, item))
        return None
    if field == "pullRequests":
        items = [i for i in repo.items.values() if i["kind"] == "pr"]
        items = _filter_states(items, args, ["OPEN"], _pr_state)
        items.sort(key=lambda i: i["number"])
        return _connection("PullRequestConnection",
                           [("PullRequest", (repo, i)) for i in items], args)
    if field == "labels":
        labels = [("Label", (repo, repo.labels[n])) for n in sorted(repo.labels)]
        return _connection("LabelConnection", labels, args)
    return _MISSING


def _resolve_issue(field, payload, args, _ctx):
    repo, item = payload
    if field == "id":
        return global_id("Issue", repo.dbid, item["number"])
    if field == "number":
        return item["number"]
    if field == "title":
        return item["title"]
    if field == "body":
        return item["body"]
    if field == "state":
        return _issue_state(item)
    if field == "url":
        return "https://forge.invalid/%s/%s/issues/%d" % (
            repo.owner, repo.name, item["number"])
    if field == "createdAt":
        return iso8601(item["created_ts"])
    if field == "updatedAt":
        return iso8601(item["updated_ts"])
    if field == "closedAt":
        return iso8601(item["updated_ts"]) if item["state"] == "closed" else None
    if field == "author":
        return ("User", VIEWER_LOGIN)
    if field == "repository":
        return ("Repository", repo)
    if field == "labels":
        labels = [("Label", (repo, repo.labels[n])) for n in item["labels"]
                  if n in repo.labels]
        return _connection("LabelConnection", labels, args)
    if field == "comments":
        comments = [("IssueComment", (repo, item, c))
                    for c in sorted(item["comments"], key=lambda c: c["seq"])]
        return _connection("IssueCommentConnection", comments, args)
    return _MISSING


def _resolve_pull(field, payload, args, _ctx):
    repo, item = payload
    if field == "id":
        return global_id("PullRequest", repo.dbid, item["number"])
    if field == "number":
        return item["number"]
    if field == "title":
        return item["title"]
    if field == "body":
        return item["body"]
    if field == "state":
        return _pr_state(item)
    if field == "merged":
        return bool(item.get("merged"))
    if field == "mergedAt":
        return item.get("merged_at")
    if field == "closedAt":
        return iso8601(item["updated_ts"]) if item["state"] == "closed" else None
    if field == "headRefName":
        return item.get("head")
    if field == "baseRefName":
        return item.get("base")
    if field == "headRef":
        return ("Ref", {"name": item.get("head"), "repo": repo})
    if field == "baseRef":
        return ("Ref", {"name": item.get("base"), "repo": repo})
    if field == "mergeable":
        if item.get("merged"):
            return "MERGEABLE"
        ok, _, _ = pull_merge_state(repo, item)
        return "MERGEABLE" if ok else "CONFLICTING"
    if field == "url":
        return "https://forge.invalid/%s/%s/pull/%d" % (
            repo.owner, repo.name, item["number"])
    if field == "createdAt":
        return iso8601(item["created_ts"])
    if field == "updatedAt":
        return iso8601(item["updated_ts"])
    if field == "author":
        return ("User", VIEWER_LOGIN)
    if field == "repository":
        return ("Repository", repo)
    if field == "files":
        files = [("PullRequestFile", {"path": f["filename"]})
                 for f in pull_files(repo, item)]
        return _connection("PullRequestFileConnection", files, args)
    if field in ("additions", "deletions", "changedFiles"):
        files = pull_files(repo, item)
        if field == "additions":
            return sum(f["additions"] for f in files)
        if field == "deletions":
            return sum(f["deletions"] for f in files)
        return len(files)
    return _MISSING


def _resolve_user(field, login, _args, _ctx):
    if field == "id":
        return global_id("User", VIEWER_ID)
    if field == "login":
        return login
    if field == "name":
        return VIEWER_NAME if login == VIEWER_LOGIN else login
    if field == "email":
        return VIEWER_EMAIL if login == VIEWER_LOGIN else None
    if field == "url":
        return "https://forge.invalid/%s" % login
    if field == "avatarUrl":
        return ""
    if field in ("createdAt", "updatedAt"):
        return iso8601(1700000000)
    return _MISSING


def _resolve_comment(field, payload, _args, _ctx):
    _repo, _item, comment = payload
    if field == "id":
        return global_id("IssueComment", comment["id"])
    if field == "body":
        return comment["body"]
    if field == "createdAt":
        return iso8601(comment["ts"])
    if field == "updatedAt":
        return iso8601(comment["ts"])
    if field == "author":
        return ("User", VIEWER_LOGIN)
    if field == "url":
        return ""
    return _MISSING


def _resolve_label(field, payload, _args, _ctx):
    repo, label = payload
    if field == "id":
        return global_id("Label", repo.dbid, label["name"])
    if field == "name":
        return label["name"]
    if field == "color":
        return label["color"]
    if field == "description":
        return None
    return _MISSING


def _resolve_ref(field, payload, _args, _ctx):
    if field == "name":
        return payload.get("name")
    if field == "prefix":
        return "refs/heads/"
    if field == "repository":
        repo = payload.get("repo")
        return ("Repository", repo) if repo is not None else None
    if field == "target":
        repo = payload.get("repo")
        name = payload.get("name")
        oid = repo.branch_tip(name) if repo is not None and name else None
        if oid is None:
            return None
        return ("GitObject", {"oid": oid})
    return _MISSING


class _Missing:
    pass


_MISSING = _Missing()

_RESOLVERS = {
    "Query": _resolve_query,
    "Mutation": _resolve_mutation,
    "Repository": _resolve_repository,
    "Issue": _resolve_issue,
    "PullRequest": _resolve_pull,
    "User": _resolve_user,
    "IssueComment": _resolve_comment,
    "Label": _resolve_label,
    "Ref": _resolve_ref,
}


def _type_of(value):
    if isinstance(value, tuple):
        return value[0]
    if isinstance(value, dict):
        return value.get("__type", "Object")
    return None


def _resolve_field(obj, field, args, ctx):
    type_name = _type_of(obj)
    if field == "__typename":
        return type_name
    payload = obj[1] if isinstance(obj, tuple) else obj
    resolver = _RESOLVERS.get(type_name)
    if resolver is not None:
        value = resolver(field, payload, args, ctx)
        if not isinstance(value, _Missing):
            return value
    if isinstance(payload, dict) and field in payload:
        return payload[field]
    ctx.errors.append("Field '%s' doesn't exist on type '%s'" % (field, type_name))
    return None


def _exec_value(value, selection, ctx):
    if value is None:
        return None
    if isinstance(value, list):
        return [_exec_value(v, selection, ctx) for v in value]
    if isinstance(value, (tuple, dict)):
        return _exec_selection(value, selection, ctx)
    return value


def _exec_selection(obj, selections, ctx):
    out = {}
    type_name = _type_of(obj)
    for sel in selections:
        if sel["kind"] == "field":
            args = {k: _eval_value(v, ctx.variables)
                    for k, v in sel["args"].items()}
            value = _resolve_field(obj, sel["name"], args, ctx)
            if sel["selection"] is not None and value is not None:
                value = _exec_value(value, sel["selection"], ctx)
            out[sel["alias"] or sel["name"]] = value
        elif sel["kind"] == "inline":
            if sel["type"] is None or sel["type"] == type_name or sel["type"] == "Node":
                out.update(_exec_selection(obj, sel["selection"], ctx))
        elif sel["kind"] == "spread":
            fragment = ctx.fragments.get(sel["name"])
            if fragment and (fragment["type"] == type_name
                             or fragment["type"] == "Node"):
                out.update(_exec_selection(obj, fragment["selection"], ctx))
    return out


def _execute_graphql_op(op):
    query = op.get("query")
    if not isinstance(query, str):
        return {"errors": [{"message": "no query provided"}], "data": None}
    try:
        operations, fragments = _GqlParser(query).parse_document()
    except Exception as exc:
        return {"errors": [{"message": "parse error: %s" % exc}], "data": None}
    if not operations:
        return {"errors": [{"message": "no operation found"}], "data": None}
    op_name = op.get("operationName")
    chosen = None
    for candidate in operations:
        if op_name is None or candidate["name"] == op_name:
            chosen = candidate
            break
    if chosen is None:
        chosen = operations[0]
    variables = {}
    for key, node in chosen["var_defaults"].items():
        variables[key] = _eval_value(node, {})
    for key, value in (op.get("variables") or {}).items():
        variables[key] = value
    ctx = _GqlContext(variables, fragments)
    root = ("Mutation", None) if chosen["kind"] == "mutation" else ("Query", None)
    data = _exec_selection(root, chosen["selection"], ctx)
    response = {"data": data}
    if ctx.errors:
        response["errors"] = [{"message": m} for m in ctx.errors]
    return response


def handle_graphql(method, raw):
    if method != "POST":
        return ERR(404, "Not Found")
    try:
        body = json.loads(raw.decode("utf-8")) if raw else None
    except Exception:
        return ERR(400, "Problems parsing JSON")
    if isinstance(body, list):
        return J(200, [_execute_graphql_op(op) for op in body])
    if isinstance(body, dict):
        return J(200, _execute_graphql_op(body))
    return ERR(400, "Problems parsing JSON")


# --------------------------------------------------------------------------
# MCP endpoint (JSON-RPC 2.0).
# --------------------------------------------------------------------------


def _mcp_tool(name, description, properties, required):
    return {
        "name": name,
        "description": description,
        "inputSchema": {"type": "object", "properties": properties,
                        "required": required},
    }


_STR = {"type": "string"}
MCP_TOOLS = [
    _mcp_tool("create_repo",
              "Create a new repository owned by the authenticated user.",
              {"name": dict(_STR, description="Repository name"),
               "description": _STR, "private": {"type": "boolean"}},
              ["name"]),
    _mcp_tool("get_repo", "Fetch a repository by owner and name.",
              {"owner": _STR, "repo": _STR}, ["owner", "repo"]),
    _mcp_tool("create_issue", "Open an issue in a repository.",
              {"owner": _STR, "repo": _STR, "title": _STR, "body": _STR},
              ["owner", "repo", "title"]),
    _mcp_tool("list_issues", "List the issues of a repository.",
              {"owner": _STR, "repo": _STR, "state": _STR},
              ["owner", "repo"]),
    _mcp_tool("create_pull_request", "Open a pull request between two branches.",
              {"owner": _STR, "repo": _STR, "title": _STR, "head": _STR,
               "base": _STR, "body": _STR},
              ["owner", "repo", "title", "head", "base"]),
    _mcp_tool("merge_pull_request", "Merge a pull request (squash).",
              {"owner": _STR, "repo": _STR,
               "pull_number": {"type": "integer"}},
              ["owner", "repo", "pull_number"]),
]

MCP_SERVER_INFO = {"name": "forge", "version": FORGE_VERSION}


def _arg(args, *names, default=None):
    for name in names:
        if isinstance(args, dict) and args.get(name) is not None:
            return args[name]
    return default


def _tool_ok(obj):
    return {"content": [{"type": "text", "text": json.dumps(obj)}],
            "structuredContent": obj, "isError": False}


def _tool_err(message):
    return {"content": [{"type": "text", "text": message}], "isError": True}


def mcp_call_tool(name, args, host):
    """-> (result, rpc_error) where exactly one element is not None."""
    if not isinstance(args, dict):
        args = {}
    if name == "create_repo":
        repo_name = _arg(args, "name")
        if not repo_name:
            return None, (-32602, "missing required argument: name")
        existing = get_repo(VIEWER_LOGIN, str(repo_name))
        if existing is not None:
            return _tool_ok(repo_json(existing, host)), None
        repo = create_repo(VIEWER_LOGIN, str(repo_name),
                           bool(_arg(args, "private", "isPrivate", default=False)),
                           _arg(args, "description", default="") or "")
        return _tool_ok(repo_json(repo, host)), None
    if name in ("get_repo", "create_issue", "list_issues",
                "create_pull_request", "merge_pull_request"):
        owner = _arg(args, "owner")
        repo_name = _arg(args, "repo", "name")
        if not owner or not repo_name:
            return None, (-32602, "missing required arguments: owner, repo")
        repo = get_repo(owner, repo_name) if owner == VIEWER_LOGIN else None
        if repo is None:
            return _tool_err("repository not found"), None
        if name == "get_repo":
            return _tool_ok(repo_json(repo, host)), None
        if name == "create_issue":
            title = _arg(args, "title")
            if not title:
                return None, (-32602, "missing required argument: title")
            item = new_item(repo, "issue", title, _arg(args, "body", default=""))
            return _tool_ok(issue_json(repo, item)), None
        if name == "list_issues":
            state = str(_arg(args, "state", default="open")).lower()
            items = [i for i in repo.items.values() if i["kind"] == "issue"]
            if state in ("open", "closed"):
                items = [i for i in items if i["state"] == state]
            items.sort(key=lambda i: i["seq"])
            return _tool_ok([issue_json(repo, i) for i in items]), None
        if name == "create_pull_request":
            title = _arg(args, "title")
            head = _arg(args, "head", "headRefName")
            base = _arg(args, "base", "baseRefName")
            if not title or not head or not base:
                return None, (-32602, "missing required arguments")
            if repo.branch_tip(head) is None or repo.branch_tip(base) is None:
                return _tool_err("head or base branch not found"), None
            item = new_item(repo, "pr", title, _arg(args, "body", default=""))
            item["head"] = head
            item["base"] = base
            return _tool_ok(pull_json(repo, item)), None
        if name == "merge_pull_request":
            number = _arg(args, "pull_number", "number", "pullNumber")
            if number is None:
                return None, (-32602, "missing required argument: pull_number")
            item = repo.items.get(int(number))
            if item is None or item["kind"] != "pr":
                return _tool_err("pull request not found"), None
            ok, result = perform_merge(repo, item)
            if not ok:
                return _tool_err(result), None
            return _tool_ok({"number": item["number"], "merged": True,
                             "sha": result, "state": "closed"}), None
    return None, (-32602, "unknown tool: %s" % name)


def _rpc_result(msg_id, result):
    return {"jsonrpc": "2.0", "id": msg_id, "result": result}


def _rpc_error(msg_id, code, message):
    return {"jsonrpc": "2.0", "id": msg_id,
            "error": {"code": code, "message": message}}


def mcp_process(msg, host):
    """One JSON-RPC message -> response dict, or None for notifications."""
    if not isinstance(msg, dict):
        return _rpc_error(None, -32600, "Invalid Request")
    method = msg.get("method")
    msg_id = msg.get("id")
    is_notification = "id" not in msg
    if isinstance(method, str) and method.startswith("notifications/"):
        return None
    if is_notification:
        return None
    params = msg.get("params") or {}
    if method == "server/discover":
        return _rpc_result(msg_id, {
            "supportedVersions": ["2026-07-28", "2025-11-25", "2025-06-18",
                                  "2025-03-26"],
            "capabilities": {"tools": {}},
            "serverInfo": MCP_SERVER_INFO,
            "_meta": {"io.modelcontextprotocol/serverInfo": MCP_SERVER_INFO},
        })
    if method == "initialize":
        offered = params.get("protocolVersion") if isinstance(params, dict) else None
        return _rpc_result(msg_id, {
            "protocolVersion": offered if isinstance(offered, str) else "2025-11-25",
            "capabilities": {"tools": {}},
            "serverInfo": MCP_SERVER_INFO,
        })
    if method == "ping":
        return _rpc_result(msg_id, {})
    if method == "tools/list":
        return _rpc_result(msg_id, {"tools": MCP_TOOLS})
    if method == "tools/call":
        tool_name = params.get("name") if isinstance(params, dict) else None
        tool_args = params.get("arguments") if isinstance(params, dict) else None
        result, rpc_error = mcp_call_tool(tool_name, tool_args or {}, host)
        if rpc_error is not None:
            return _rpc_error(msg_id, rpc_error[0], rpc_error[1])
        return _rpc_result(msg_id, result)
    return _rpc_error(msg_id, -32601, "Method not found: %s" % method)


def handle_mcp(method, raw, headers, host):
    if method != "POST":
        return ERR(404, "Not Found")
    try:
        body = json.loads(raw.decode("utf-8")) if raw else None
    except Exception:
        return (400, json.dumps(_rpc_error(None, -32700, "Parse error")).encode(),
                "application/json", {})
    if not authorized(headers):
        return ERR(401, "Unauthorized")
    if isinstance(body, list):
        responses = []
        for msg in body:
            response = mcp_process(msg, host)
            if response is not None:
                responses.append(response)
        if not responses:
            return (202, b"", None, {})
        return J(200, responses)
    if isinstance(body, dict):
        response = mcp_process(body, host)
        if response is None:
            return (202, b"", None, {})
        return J(200, response)
    return (400, json.dumps(_rpc_error(None, -32700, "Parse error")).encode(),
            "application/json", {})


# --------------------------------------------------------------------------
# HTTP plumbing: auth, dispatch, handler, harness lifecycle.
# --------------------------------------------------------------------------

import socket  # noqa: E402


def authorized(headers):
    if not TOKEN:
        return True
    auth = headers.get("authorization") or ""
    if auth.startswith("Bearer "):
        return auth[len("Bearer "):] == TOKEN
    if auth.startswith("token "):
        return auth[len("token "):] == TOKEN
    if auth.startswith("Basic "):
        try:
            decoded = base64.b64decode(auth[len("Basic "):]).decode()
        except Exception:
            return False
        return decoded.split(":")[0] == TOKEN or TOKEN in decoded
    return False


_RATE_REMAINING = [4999]


def dispatch(method, target, raw, headers):
    split = urllib.parse.urlsplit(target)
    raw_path = split.path
    query = urllib.parse.parse_qs(split.query)
    segs = [urllib.parse.unquote(s) for s in raw_path.split("/") if s != ""]
    host = headers.get("host", "forge.invalid")

    if method == "GET" and segs == ["healthz"]:
        return J(200, {"ok": True})

    if segs[:2] == ["api", "v3"]:
        if not authorized(headers):
            return ERR(401, "Bad credentials")
        status, body, ctype, extra = handle_rest(
            method, segs[2:], query, raw, host, raw_path)
        extra = dict(extra)
        extra.setdefault("X-OAuth-Scopes", "repo, read:org")
        _RATE_REMAINING[0] = max(0, _RATE_REMAINING[0] - 1)
        extra.setdefault("X-RateLimit-Limit", "5000")
        extra.setdefault("X-RateLimit-Remaining", str(_RATE_REMAINING[0]))
        extra.setdefault("X-RateLimit-Reset", str(int(time.time()) + 3600))
        return (status, body, ctype, extra)

    if segs == ["api", "graphql"]:
        if not authorized(headers):
            return ERR(401, "Bad credentials")
        return handle_graphql(method, raw)

    if segs == ["meta"] and method == "GET":
        if not authorized(headers):
            return ERR(401, "Bad credentials")
        return J(200, {"installed_version": INSTALLED_VERSION})

    if segs == ["mcp"]:
        return handle_mcp(method, raw, headers, host)

    if len(segs) >= 2 and segs[1].endswith(".git"):
        if not authorized(headers):
            return ERR(401, "Bad credentials")
        return handle_git(method, segs, query, raw, headers)

    return ERR(404, "Not Found")


class ForgeHandler(BaseHTTPRequestHandler):
    protocol_version = "HTTP/1.1"
    server_version = "forge/1.0"

    def setup(self):
        super().setup()
        try:
            self.request.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
        except OSError:
            pass

    def log_message(self, *_args):
        pass

    def _read_body(self):
        transfer = (self.headers.get("Transfer-Encoding") or "").lower()
        if "chunked" in transfer:
            chunks = []
            while True:
                size_line = self.rfile.readline(65536).strip()
                try:
                    size = int(size_line.split(b";")[0], 16)
                except ValueError:
                    break
                if size == 0:
                    while True:
                        line = self.rfile.readline(65536)
                        if line in (b"\r\n", b"\n", b""):
                            break
                    break
                chunks.append(self.rfile.read(size))
                self.rfile.read(2)
            return b"".join(chunks)
        length = self.headers.get("Content-Length")
        if length is None:
            return b""
        try:
            count = int(length)
        except ValueError:
            return b""
        return self.rfile.read(count) if count > 0 else b""

    def _handle(self, method):
        try:
            raw = self._read_body() if method in ("POST", "PUT", "PATCH", "DELETE") else b""
            headers = {k.lower(): v for k, v in self.headers.items()}
            with STORE_LOCK:
                status, body, ctype, extra = dispatch(method, self.path, raw, headers)
        except Exception as exc:  # a handler bug must never become an HTML 500
            status = 500
            body = json.dumps({"message": "internal error: %s" % exc}).encode()
            ctype, extra = "application/json", {}
        try:
            self.send_response(status)
            if ctype:
                self.send_header("Content-Type", ctype)
            self.send_header("Content-Length", str(len(body)))
            self.send_header("X-GitHub-Request-Id", uuid.uuid4().hex)
            for key, value in extra.items():
                self.send_header(key, value)
            self.end_headers()
            if body and method != "HEAD":
                self.wfile.write(body)
        except (BrokenPipeError, ConnectionResetError):
            pass

    def do_GET(self):
        self._handle("GET")

    def do_POST(self):
        self._handle("POST")

    def do_PUT(self):
        self._handle("PUT")

    def do_PATCH(self):
        self._handle("PATCH")

    def do_DELETE(self):
        self._handle("DELETE")

    def do_HEAD(self):
        self._handle("HEAD")


class ForgeServer(ThreadingHTTPServer):
    daemon_threads = True
    request_queue_size = 256
    allow_reuse_address = True


def _env_request(method, path, payload=None):
    parts = urllib.parse.urlsplit(ENV_URL)
    if parts.scheme == "https":
        conn = http.client.HTTPSConnection(parts.hostname, parts.port or 443,
                                           timeout=10)
    else:
        conn = http.client.HTTPConnection(parts.hostname, parts.port or 80,
                                          timeout=10)
    body = json.dumps(payload) if payload is not None else None
    headers = {"Content-Type": "application/json"} if body else {}
    prefix = parts.path.rstrip("/")
    conn.request(method, prefix + path, body=body, headers=headers)
    response = conn.getresponse()
    data = response.read()
    status = response.status
    conn.close()
    return status, data


def main():
    if not ENV_URL:
        print("MAKEFUN_ENV_URL is not set; nowhere to register", file=sys.stderr)
        return 1
    server = ForgeServer(("0.0.0.0", 0), ForgeHandler)
    port = server.server_address[1]
    thread = threading.Thread(target=server.serve_forever,
                              kwargs={"poll_interval": 0.1}, daemon=True)
    thread.start()
    print("forge listening on port %d" % port, file=sys.stderr)

    deadline = time.time() + 300
    registered = False
    while time.time() < deadline:
        try:
            status, _ = _env_request("POST", "/register", {"port": port})
            if status in (200, 409):
                registered = True
                break
        except Exception:
            pass
        time.sleep(0.25)
    if not registered:
        print("warning: env did not accept registration", file=sys.stderr)

    end = time.time() + 1500
    while time.time() < end:
        try:
            status, data = _env_request("GET", "/done")
            if status == 200 and json.loads(data).get("done"):
                break
        except Exception:
            pass
        time.sleep(0.5)
    server.shutdown()
    return 0


if __name__ == "__main__":
    sys.exit(main())
