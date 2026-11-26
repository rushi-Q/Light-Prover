#!/usr/bin/python3 -I
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
import importlib.util
spec = importlib.util.spec_from_file_location("g1", str(Path(__file__).resolve().parent / "craft_g1.py"))
src = (Path(__file__).resolve().parent / "craft_g1.py").read_text().replace("\nmain()\n", "\n")
ns = {"__file__": str(Path(__file__).resolve().parent / "craft_g1.py")}
exec(compile(src, "craft_g1.py", "exec"), ns)
st, out = sys.argv[1], Path(sys.argv[2])
b = ns["base"](st); n_I, n_mk, n_rec, e_I, e_mk = ns["add_qi"](b, True)
b.items.append({"thm": {"name": n_rec, "levelParams": [], "type": e_I, "value": e_mk, "all": [n_rec]}})
b.write(out / "g1d_dup_rec_thm.export")
b = ns["base"](st); n_I, n_mk, n_rec, e_I, e_mk = ns["add_qi"](b, True)
# theorem first, then the inductive block (move the thm before the block)
blk = b.items.pop()
b.items.append({"thm": {"name": n_rec, "levelParams": [], "type": e_I, "value": e_mk, "all": [n_rec]}})
b.items.append(blk)
b.write(out / "g1e_dup_thm_rec.export")
print("ok")
