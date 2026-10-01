#!/usr/bin/env python3
"""Generate the catalogue and census layer of SemiBase.

Inputs
  research/order6/catalogue.json      GAP Smallsemi 0.7.2, the 15,973 classes of
                                      order six, one-based tables
  provenance/final-census-map.json    the endpoint theorem(s) of every class, as
                                      recorded by the final audit

Outputs (all regenerated from scratch)
  SemiBase/Catalogue/Order6/PartNNN.lean   catalogue data, 150 classes per part
  SemiBase/Catalogue/Order6.lean           the whole catalogue and its basic facts
  SemiBase/Census/ShardNNN.lean            one theorem `Classified` per class
  SemiBase/Classification.lean             the classification theorem

Every per-class proof applies one endpoint theorem of the development and checks,
by `decide`, that the semigroup of the endpoint has the catalogue table (or the
transposed table, for an endpoint stated for the opposite semigroup). Nothing in
the output is trusted: a wrong choice makes the build fail.
"""
import json
import os
import sys

ROOT = sys.argv[1] if len(sys.argv) > 1 else "."
PART = 150
NFB = [3843, 8564, 8878, 13747]

catalogue = json.load(open(os.path.join(ROOT, "research/order6/catalogue.json")))
census = json.load(open(os.path.join(ROOT, "provenance/final-census-map.json")))

classes = []
for entry in catalogue["semigroups"]:
    k = entry["smallsemi_id"][1]
    assert entry["id"] == f"S6_{k}" and entry["smallsemi_id"][0] == 6
    rows = [[x - 1 for x in row] for row in entry["table"]]
    assert len(rows) == 6 and all(len(r) == 6 and all(0 <= x < 6 for x in r) for r in rows)
    classes.append((k, rows))
classes.sort()
assert [k for k, _ in classes] == list(range(1, 15974))

relabelled = census.get("relabelled_classes", {})

# The census map names, for 21 classes, an endpoint module under
# Order6CASExplicitSourceUpstream. Those files are not in this repository: each
# is a strict subset of the Order6FinalL5TransferV3 part with the same number,
# with the same namespace, so the same theorem is imported from that part
# (see provenance/README.md).
CAS_PREFIX = "SemigroupBasis.Generated.Order6CASExplicitSourceUpstream."


def module_in_repository(module):
    if module.startswith(CAS_PREFIX):
        return "Order6FinalL5TransferV3." + module[len(CAS_PREFIX):]
    return module


def write_if_changed(path, text):
    try:
        with open(path) as handle:
            if handle.read() == text:
                return
    except FileNotFoundError:
        pass
    with open(path, "w") as handle:
        handle.write(text)


def inverse(perm):
    inv = [0] * len(perm)
    for i, p in enumerate(perm):
        inv[p] = i
    return inv


def rows_lean(rows):
    return "[" + ", ".join("[" + ", ".join(map(str, r)) + "]" for r in rows) + "]"


def endpoint_of(k):
    c = census["classes"][f"S6_{k}"]
    eps = c["endpoints"]
    if k in NFB:
        nfb = census["non_finitely_based"][f"S6_{k}"]
        return "nonfinite", nfb["name"], module_in_repository(nfb["module"])
    for key in ("plain", "opposite"):
        if key in eps:
            return key, eps[key]["name"], module_in_repository(eps[key]["module"])
    raise SystemExit(f"S6_{k}: no endpoint")


def proof_lines(k):
    kind, name, _ = endpoint_of(k)
    if kind == "nonfinite":
        alts = [
            f"classified_of_nonfinitelyBased (by decide +kernel) {name} (by decide +kernel)",
            f"classified_of_nonfinitelyBased (by decide +kernel) (nonfinitelyBased_opposite {name}) (by decide +kernel)",
        ]
    else:
        fb = f"(SemigroupBasis.BasisFor.finitelyBased {name})"
        alts = [
            f"classified_of_finitelyBased (by decide +kernel) {fb} (by decide +kernel)",
            f"classified_of_finitelyBased (by decide +kernel) (finitelyBased_opposite {fb}) (by decide +kernel)",
        ]
        if f"S6_{k}" in relabelled:
            p = relabelled[f"S6_{k}"]
            q = inverse(p)
            for phi, psi in ((p, q), (q, p)):
                for base in (fb, f"(finitelyBased_opposite {fb})"):
                    alts.append(
                        "classified_of_finitelyBased (by decide +kernel) "
                        f"(finitelyBased_transport (perm6 {phi}) (perm6 {psi}) "
                        f"(by decide +kernel) (by decide +kernel) {base}) (by decide +kernel)"
                    )
    out = [f"theorem S6_{k} : Classified Catalogue.Order6.S6_{k} := by", "  first"]
    out += [f"  | exact {a}" for a in alts]
    return out


parts = [classes[i:i + PART] for i in range(0, len(classes), PART)]
cat_dir = os.path.join(ROOT, "SemiBase/Catalogue/Order6")
census_dir = os.path.join(ROOT, "SemiBase/Census")
os.makedirs(cat_dir, exist_ok=True)
os.makedirs(census_dir, exist_ok=True)

for j, part in enumerate(parts, start=1):
    lo, hi = part[0][0], part[-1][0]
    lines = [
        "import SemiBase.Statement",
        "",
        "/-!",
        f"# Catalogue of order six, part {j:03d}: classes `[6, {lo}]` to `[6, {hi}]`",
        "",
        "Multiplication tables of GAP Smallsemi 0.7.2, rows listed in order, with the",
        "elements `0, …, 5` standing for Smallsemi's `1, …, 6`. Generated by",
        "`scripts/generate_census.py` from `research/order6/catalogue.json`.",
        "-/",
        "",
        "namespace SemiBase.Catalogue.Order6",
        "",
    ]
    for k, rows in part:
        lines.append(f"/-- Smallsemi class `[6, {k}]`. -/")
        lines.append(f"def S6_{k} : Entry := ⟨{k}, {rows_lean(rows)}⟩")
        lines.append("")
    lines.append(f"/-- The classes `[6, {lo}]` to `[6, {hi}]`. -/")
    lines.append(f"def part{j:03d} : List Entry :=")
    names = [f"S6_{k}" for k, _ in part]
    for i in range(0, len(names), 8):
        chunk = ", ".join(names[i:i + 8])
        prefix = "  [" if i == 0 else "   "
        suffix = "]" if i + 8 >= len(names) else ","
        lines.append(prefix + chunk + suffix)
    lines += ["", "end SemiBase.Catalogue.Order6", ""]
    write_if_changed(os.path.join(cat_dir, f"Part{j:03d}.lean"), "\n".join(lines))

    modules = sorted({endpoint_of(k)[2] for k, _ in part})
    lines = ["import SemiBase.Statement", f"import SemiBase.Catalogue.Order6.Part{j:03d}"]
    lines += [f"import {m}" for m in modules]
    lines += [
        "",
        "/-!",
        f"# Census shard {j:03d}: classes `[6, {lo}]` to `[6, {hi}]`",
        "",
        "For each class, the claim `Classified` from one endpoint theorem of the",
        "development. The first alternative that checks is used: the endpoint for the",
        "semigroup with the catalogue table, or for its opposite (the transposed table).",
        "Generated by `scripts/generate_census.py`.",
        "-/",
        "",
        "set_option maxRecDepth 8192",
        "",
        "namespace SemiBase.Census",
        "",
    ]
    for k, _ in part:
        lines += proof_lines(k)
        lines.append("")
    lines.append(f"/-- Every class of part {j:03d} of the catalogue is classified. -/")
    lines.append(f"theorem shard{j:03d} : AllClassified Catalogue.Order6.part{j:03d} :=")
    for k, _ in part:
        lines.append(f"  AllClassified.cons S6_{k} <|")
    lines.append("  AllClassified.nil")
    lines += ["", "end SemiBase.Census", ""]
    write_if_changed(os.path.join(census_dir, f"Shard{j:03d}.lean"), "\n".join(lines))

n = len(parts)
lines = ["import SemiBase.Statement"]
lines += [f"import SemiBase.Catalogue.Order6.Part{j:03d}" for j in range(1, n + 1)]
lines += [
    "",
    "/-!",
    "# The catalogue of semigroups of order six",
    "",
    "The 15,973 classes of semigroups of order six up to isomorphism and",
    "anti-isomorphism, as listed by GAP Smallsemi 0.7.2 (OEIS A001423), in Smallsemi",
    "order. The catalogue is data: this repository does not prove that it lists",
    "every class.",
    "-/",
    "",
    "namespace SemiBase.Catalogue",
    "",
    "/-- The 15,973 classes `[6, 1]`, …, `[6, 15973]` with their tables. -/",
    "def order6 : List Entry :=",
]
terms = [f"Order6.part{j:03d}" for j in range(1, n + 1)]
expr = terms[-1]
for t in reversed(terms[:-1]):
    expr = f"{t} ++ ({expr})"
lines.append("  " + expr)
lines += [
    "",
    "theorem order6_length : order6.length = 15973 := by decide +kernel",
    "",
    "/-- The entries are the classes `[6, 1]`, …, `[6, 15973]`, in this order. -/",
    "theorem order6_ids : order6.map Entry.id = List.range' 1 15973 := by decide +kernel",
    "",
    "end SemiBase.Catalogue",
    "",
]
write_if_changed(os.path.join(ROOT, "SemiBase/Catalogue/Order6.lean"), "\n".join(lines))

lines = ["import SemiBase.Catalogue.Order6"]
lines += [f"import SemiBase.Census.Shard{j:03d}" for j in range(1, n + 1)]
lines += [
    "",
    "/-!",
    "# The classification of the semigroups of order six by finite basability",
    "-/",
    "",
    "set_option maxRecDepth 8192",
    "",
    "namespace SemiBase",
    "",
    "theorem allClassified_order6 : AllClassified Catalogue.order6 :=",
]
for j in range(1, n):
    lines.append(f"  AllClassified.append Census.shard{j:03d} <|")
lines.append(f"  Census.shard{n:03d}")
lines += [
    "",
    "/-- **Classification of the semigroups of order six by finite basability.**",
    "For every class `e` of the catalogue (the 15,973 semigroups of order six of",
    "GAP Smallsemi, up to isomorphism and anti-isomorphism), the table of `e` is the",
    "table of a semigroup, and every semigroup on `Fin 6` with this table is",
    "nonfinitely based if `e` is `[6, 3843]`, `[6, 8564]`, `[6, 8878]` or",
    "`[6, 13747]`, and finitely based otherwise. -/",
    "theorem order6_classification : ∀ e ∈ Catalogue.order6, Classified e :=",
    "  AllClassified.mem allClassified_order6",
    "",
    "/-- Every semigroup with the table of a class of order six other than the four",
    "exceptional classes has a finite identity basis. -/",
    "theorem order6_finitelyBased : ∀ e ∈ Catalogue.order6, e.id ∉ nonfinitelyBasedIds →",
    "    ∀ G : SemigroupBasis.Semigroup (Fin 6), HasTable G e.rows →",
    "      SemigroupBasis.FinitelyBased G :=",
    "  fun e he hid G hG => ((order6_classification e he).2 G hG).2 hid",
    "",
    "/-- The four exceptional classes of order six have no finite identity basis. -/",
    "theorem order6_nonfinitelyBased : ∀ e ∈ Catalogue.order6, e.id ∈ nonfinitelyBasedIds →",
    "    ∀ G : SemigroupBasis.Semigroup (Fin 6), HasTable G e.rows →",
    "      SemigroupBasis.NonfinitelyBased G :=",
    "  fun e he hid G hG => ((order6_classification e he).2 G hG).1 hid",
    "",
    "end SemiBase",
    "",
]
write_if_changed(os.path.join(ROOT, "SemiBase/Classification.lean"), "\n".join(lines))

print(f"{len(classes)} classes, {n} parts and shards")
