#!/usr/bin/env python3
"""Ledger consistency: the binders of `fried_counterexample_of_inputs`
(B1s/fried_counterexample_main.lean) vs the rows of README.md §"The ledger".
Enforces: every row names exactly one binder; the two sets coincide. Exit 1 on drift."""
import re, sys, pathlib
root = pathlib.Path(__file__).resolve().parent.parent
lean = (root / "B1s/fried_counterexample_main.lean").read_text()
sig = lean.split("theorem fried_counterexample_of_inputs")[1].split(":= by")[0]
binders = set(re.findall(r"\((h[\w₀₁₂₃₄'τθ]+)\s*:", sig))
readme = (root / "README.md").read_text()
tbl = readme.split("## The ledger")[1].split("Conclusion:")[0]
rows = [l for l in tbl.splitlines() if l.startswith("| `h")]
row_names, bad = [], []
for l in rows:
    first = l.split("|")[1]
    names = re.findall(r"`(h[\w₀₁₂₃₄'τθ]+)`", first)
    if len(names) != 1: bad.append(l[:60])
    row_names += names
names = set(row_names)
ok = True
print(f"Lean binders: {len(binders)}  README rows: {len(rows)}")
if bad: print("rows not naming exactly one binder:", bad); ok = False
if len(row_names) != len(names): print("duplicate rows:", sorted({n for n in row_names if row_names.count(n) > 1})); ok = False
m, e = sorted(binders - names), sorted(names - binders)
if m: print("in Lean signature, missing from README table:", m); ok = False
if e: print("in README table, not a Lean binder:", e); ok = False
sys.exit(0 if ok else 1)
