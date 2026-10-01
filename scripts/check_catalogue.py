#!/usr/bin/env python3
"""Check that the Lean catalogue holds GAP Smallsemi's tables of order six.

The statement of the classification is about the tables written in
`SemiBase/Catalogue/Order6/Part*.lean`. This script checks the chain from GAP to
those files:

1. `research/order6/catalogue.json` is the file that `gap/export_order6_catalogue.g`
   exported from Smallsemi 0.7.2 during the campaign; its SHA-256 is pinned below.
2. Every table in the Lean data is the table of the same class in
   `catalogue.json`, with the elements `1, …, 6` renamed `0, …, 5`, and the
   classes are `[6, 1]`, …, `[6, 15973]` in this order.
3. With `--gap FILE ...`, every table is also compared with independent GAP
   exports in the format `[{"index": i, "table": [[...]], ...}, ...]`, for
   example the files `gap/s6_1_10000.json` and `gap/s6_10001_15973.json` of the
   bases-min repository, generated with GAP 4.15.1 and Smallsemi 0.7.2.
"""
import argparse
import glob
import hashlib
import json
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CATALOGUE = os.path.join(ROOT, "research", "order6", "catalogue.json")
CATALOGUE_SHA256 = "944f356c42b8e703988f5684cd81b650f99cc0ccd1ef1d7fc6e900f2c95f287c"
ENTRY = re.compile(r"^def S6_(\d+) : Entry := ⟨(\d+), (\[\[.*\]\])⟩$")


def sha256(path):
    with open(path, "rb") as handle:
        return hashlib.sha256(handle.read()).hexdigest()


def lean_tables():
    tables = {}
    order = []
    for path in sorted(glob.glob(os.path.join(ROOT, "SemiBase/Catalogue/Order6/Part*.lean"))):
        with open(path, encoding="utf-8") as handle:
            for line in handle:
                match = ENTRY.match(line.rstrip("\n"))
                if match:
                    name, ident, rows = int(match.group(1)), int(match.group(2)), match.group(3)
                    if name != ident:
                        sys.exit(f"{path}: S6_{name} carries the number {ident}")
                    if ident in tables:
                        sys.exit(f"{path}: S6_{ident} defined twice")
                    tables[ident] = json.loads(rows)
                    order.append(ident)
    return tables, order


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--gap", nargs="*", default=[], help="independent GAP exports to compare")
    args = parser.parse_args()

    digest = sha256(CATALOGUE)
    if digest != CATALOGUE_SHA256:
        sys.exit(f"research/order6/catalogue.json has SHA-256 {digest}, expected {CATALOGUE_SHA256}")
    catalogue = json.load(open(CATALOGUE))
    reference = {}
    self_dual = 0
    for record in catalogue["semigroups"]:
        order, ident = record["smallsemi_id"]
        if order != 6 or record["id"] != f"S6_{ident}":
            sys.exit(f"unexpected record {record['id']}")
        reference[ident] = [[x - 1 for x in row] for row in record["table"]]
        self_dual += record["self_dual"]

    tables, order = lean_tables()
    if order != list(range(1, 15974)):
        sys.exit("the Lean catalogue does not list [6, 1], ..., [6, 15973] in order")
    mismatched = [k for k in order if tables[k] != reference.get(k)]
    if mismatched or set(reference) != set(tables):
        sys.exit(f"tables differing from catalogue.json: {mismatched[:10]}")
    print(f"catalogue.json: SHA-256 as pinned, {len(reference)} classes, {self_dual} self-dual")
    print(f"Lean catalogue: {len(tables)} tables, all equal to catalogue.json")

    if args.gap:
        independent = {}
        nilpotent = 0
        for path in args.gap:
            for record in json.load(open(path)):
                if record["index"] in independent:
                    sys.exit(f"{path}: class {record['index']} listed twice")
                independent[record["index"]] = [[x - 1 for x in row] for row in record["table"]]
                nilpotent += bool(record.get("nilpotent"))
            print(f"{os.path.basename(path)}: SHA-256 {sha256(path)}")
        if set(independent) != set(tables):
            sys.exit(f"the independent export covers {len(independent)} classes, not the 15,973 of the catalogue")
        mismatched = [k for k in order if tables[k] != independent[k]]
        if mismatched:
            sys.exit(f"tables differing from the independent export: {mismatched[:10]}")
        print(f"independent GAP export: {len(independent)} tables, all equal; {nilpotent} nilpotent")


if __name__ == "__main__":
    main()
