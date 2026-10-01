#!/usr/bin/env python3
"""Check that every Lean file is needed, and show what each folder is needed for.

1. Every Lean file of the repository (outside `scripts/`) must be imported,
   directly or indirectly, by `SemiBase.lean`, the root of the classification
   theorem. Otherwise it fails: the repository holds no unused Lean file.
2. With `--table`, it prints for each folder of the repository map in
   README.md: its files and lines, the number of classes whose own proof (the
   endpoint theorem and everything it imports) uses a file of the folder, the
   number of classes whose endpoint theorem lies in the folder, and whether the
   proofs of the four nonfinitely based classes use it.

The endpoint of each class is the one the census layer uses: the theorem named
in `provenance/final-census-map.json`, as in `scripts/generate_census.py`.
"""
import argparse
import json
import os
import re
import sys
from collections import defaultdict

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
IMPORT = re.compile(r"^\s*import\s+(.+)$")
CAS_PREFIX = "SemigroupBasis.Generated.Order6CASExplicitSourceUpstream."
NONFINITE = [3843, 8564, 8878, 13747]

# Folders of the repository map, in the order of README.md. A file belongs to
# the first folder whose prefix matches its path.
FOLDERS = [
    ("SemiBase.lean", "statement layer: root"),
    ("SemiBase/Statement.lean", "statement layer: the claim for one class"),
    ("SemiBase/Classification.lean", "statement layer: the classification theorem"),
    ("SemiBase/Catalogue/", "statement layer: the 15,973 tables"),
    ("SemiBase/Census/", "statement layer: one theorem per class"),
    ("SemigroupBasis/Nonfinite/", "nonfinite-basis arguments"),
    ("SemigroupBasis/Examples/", "named families; three nonfinite-basis proofs"),
    ("SemigroupBasis/CoRoots/S", "family proofs for orders 4 and 5"),
    ("SemigroupBasis/CoRoots/", "family proofs for order 6"),
    ("SemigroupBasis/Generated/Catalogue", "tables of orders 1 to 5"),
    ("SemigroupBasis/Generated/Order6Nilpotent/", "nilpotent certificates, order 6"),
    ("SemigroupBasis/Generated/Order6Final", "transfers that needed heavier proofs, order 6"),
    ("SemigroupBasis/Generated/Order6", "other generated proofs, order 6"),
    ("SemigroupBasis/Generated/", "generated proofs for orders 1 to 5"),
    ("SemigroupBasis/Order6Subdirect/", "subdirect decompositions, order 6"),
    ("SemigroupBasis/Order6ResidualReleaseV3/", "release wrappers, order 6"),
    ("SemigroupBasis/Order6/", "shared order-6 helpers"),
    ("SemigroupBasis/Normalization/", "word normalization"),
    ("SemigroupBasis/Order7/", "a lemma stated for order 7, reused at order 6"),
    ("SemigroupBasis/", "core library"),
    ("Order6FinalL5TransferV3/", "transfers from orders at most 5, final sweep"),
    ("research/formalization/", "transfers from orders at most 5, earlier waves"),
]


def module_files():
    files = {}
    for directory, subdirectories, names in os.walk(ROOT):
        subdirectories[:] = [d for d in subdirectories if d not in (".lake", ".git", "scripts")]
        for name in names:
            if name.endswith(".lean") and name != "lakefile.lean":
                path = os.path.relpath(os.path.join(directory, name), ROOT)
                files[path[:-5].replace(os.sep, ".")] = path
    return files


def imports(path):
    found = []
    in_comment = False
    with open(os.path.join(ROOT, path), encoding="utf-8") as handle:
        for line in handle:
            text = line.strip()
            if in_comment:
                if "-/" in text:
                    in_comment = False
                continue
            if text.startswith("/-"):
                in_comment = "-/" not in text[2:]
                continue
            if not text or text.startswith("--"):
                continue
            match = IMPORT.match(text)
            if not match:
                break
            found += match.group(1).split()
    return found


def folder_of(path):
    for prefix, _ in FOLDERS:
        if path == prefix or path.startswith(prefix):
            return prefix
    return None


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--table", action="store_true", help="print the folder table")
    args = parser.parse_args()

    files = module_files()
    graph = {m: [i for i in imports(p) if i in files] for m, p in files.items()}

    def closure(module):
        stack, seen = [module], set()
        while stack:
            current = stack.pop()
            if current in seen:
                continue
            seen.add(current)
            stack.extend(graph[current])
        return seen

    reachable = closure("SemiBase")
    unused = sorted(files[m] for m in files if m not in reachable)
    print(f"{len(files)} Lean files; {len(reachable)} imported by SemiBase.lean; {len(unused)} unused")
    if unused:
        print("\n".join(unused[:50]))
        sys.exit(1)
    if not args.table:
        return

    census = json.load(open(os.path.join(ROOT, "provenance", "final-census-map.json")))
    endpoint = {}
    for k in range(1, 15974):
        if k in NONFINITE:
            module = census["non_finitely_based"][f"S6_{k}"]["module"]
        else:
            points = census["classes"][f"S6_{k}"]["endpoints"]
            module = (points.get("plain") or points["opposite"])["module"]
        if module.startswith(CAS_PREFIX):
            module = "Order6FinalL5TransferV3." + module[len(CAS_PREFIX):]
        endpoint[k] = module

    folder_files = defaultdict(set)
    for module, path in files.items():
        folder_files[folder_of(path)].add(module)
    lines = defaultdict(int)
    for module, path in files.items():
        with open(os.path.join(ROOT, path), "rb") as handle:
            lines[folder_of(path)] += sum(1 for _ in handle)

    by_endpoint = {}
    needed = defaultdict(int)
    nonfinite_uses = defaultdict(bool)
    hosts = defaultdict(int)
    for k, module in endpoint.items():
        if module not in by_endpoint:
            by_endpoint[module] = {folder_of(files[m]) for m in closure(module)}
        for folder in by_endpoint[module]:
            needed[folder] += 1
            if k in NONFINITE:
                nonfinite_uses[folder] = True
        hosts[folder_of(files[module])] += 1

    print(f"{'folder':44s} {'files':>6s} {'lines':>9s} {'needed by':>9s} {'endpoints':>9s}  4 NFB")
    for prefix, description in FOLDERS:
        if prefix not in folder_files:
            continue
        statement = prefix.startswith("SemiBase")
        needed_by = "all" if statement else str(needed[prefix])
        nonfinite = "yes" if statement or nonfinite_uses[prefix] else "-"
        print(f"{prefix:44s} {len(folder_files[prefix]):6d} {lines[prefix]:9d} "
              f"{needed_by:>9s} {hosts[prefix]:9d}  {nonfinite}"
              f"   {description}")


if __name__ == "__main__":
    main()
