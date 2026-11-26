#!/usr/bin/python3 -I
"""oleanv4.py OLEAN ACTION  (tests only) - craft tampered copies of Lean >= 4.37 (format v4) .olean files to test that
the native exporter declines (fail closed) where the official reader/lookup could behave differently.  Edits in place.
ACTION:
  data-size        set the header's data_size word to a value larger than the file
  closures         set num_closure_offsets (after the data section) to 1
  trie-hash        flip one bit of the cached Name.hash of the key of the first leaf of the constant prefix tree
  trie-unsort      swap the first two children (of different hash) of the first prefix-tree node with >= 2 children
  trie-swapvals    swap the values (ConstantInfo pointers) of the first two leaves of the constant prefix tree
  trie-none        set ModuleData.constTrie? to `none`
Object layout (lean.h): header 8 bytes (rc 4, cs_sz 2, num objs 1, tag 1), then 8-byte fields, then scalars.
Pointers are absolute addresses relative to base_addr (header offset 0x50) of the file start."""
import struct, sys

def main():
    path, action = sys.argv[1], sys.argv[2]
    b = bytearray(open(path, "rb").read())
    assert b[:5] == b"olean" and b[5] == 4, "not a v4 olean"
    base = struct.unpack_from("<Q", b, 0x50)[0]
    dsz = struct.unpack_from("<Q", b, 0x58)[0]
    def off(a): return a - base
    def u64(o): return struct.unpack_from("<Q", b, o)[0]
    def tag(o): return b[o + 7]
    def nobjs(o): return b[o + 6]
    def field(o, i): return u64(o + 8 + 8 * i)
    def is_scalar(r): return r & 1 == 1
    root = off(u64(0x60))
    md = root
    assert tag(md) == 0 and nobjs(md) == 7, "ModuleData shape"
    if action == "data-size":
        struct.pack_into("<Q", b, 0x58, len(b) * 2)
    elif action == "closures":
        struct.pack_into("<I", b, 0x60 + dsz, 1)
    elif action == "trie-none":
        struct.pack_into("<Q", b, md + 8 + 8 * 5, 1)  # box(0) = none
    else:
        opt = off(field(md, 5))
        trie = off(field(opt, 0))
        # DFS for leaves / nodes
        def children(n):
            t = tag(n)
            if t == 0: return None, []
            a = off(field(n, 1 if t == 1 else 2))
            cnt = u64(a + 8)
            return a, [off(u64(a + 24 + 8 * i)) for i in range(cnt)]
        stack, leaves, multi = [trie], [], None
        while stack:
            n = stack.pop()
            a, cs = children(n)
            if tag(n) == 0: leaves.append(n)
            if a is not None and len(cs) >= 2 and multi is None:
                h0 = u64(off(field(cs[0], 0)) + 8 + 16); h1 = u64(off(field(cs[1], 0)) + 8 + 16)
                if h0 != h1: multi = a
            stack.extend(cs)
        if action == "trie-hash":
            k = off(field(leaves[0], 0)); b[k + 8 + 16] ^= 1
        elif action == "trie-unsort":
            assert multi is not None, "no node with 2 children"
            x, y = u64(multi + 24), u64(multi + 32)
            struct.pack_into("<Q", b, multi + 24, y); struct.pack_into("<Q", b, multi + 32, x)
        elif action == "trie-swapvals":
            assert len(leaves) >= 2, "need 2 leaves"
            v0, v1 = field(leaves[0], 1), field(leaves[1], 1)
            struct.pack_into("<Q", b, leaves[0] + 16, v1); struct.pack_into("<Q", b, leaves[1] + 16, v0)
        else:
            sys.exit("unknown action " + action)
    open(path, "wb").write(b)

main()
