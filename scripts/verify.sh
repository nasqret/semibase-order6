#!/usr/bin/env bash
# Verify the classification from source.
#
#   1. every Lean file of the development is the certified version, apart from
#      the recorded changes (scripts/check_provenance.py);
#   2. the catalogue data in Lean is the Smallsemi export catalogue.json, and
#      its four exceptional classes are those of Lee and Zhang's published
#      classification (scripts/check_catalogue.py);
#   3. every Lean file is needed: it is imported by SemiBase.lean, the root of
#      the classification theorem (scripts/check_closure.py);
#   4. Lake builds everything from source, so the Lean kernel checks every proof;
#   5. the main theorems use no axiom beyond propext, Classical.choice and
#      Quot.sound (no sorry, no native_decide).
set -euo pipefail
cd "$(dirname "$0")/.."

echo "== provenance"
python3 scripts/check_provenance.py

echo "== catalogue"
python3 scripts/check_catalogue.py

echo "== closure"
python3 scripts/check_closure.py

echo "== build"
lake build

echo "== axioms"
lake env lean scripts/Axioms.lean | tee .lake/axioms.txt
python3 - .lake/axioms.txt <<'EOF'
import re, sys
allowed = {"propext", "Classical.choice", "Quot.sound"}
text = open(sys.argv[1]).read()
reports = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text)
reports += [(name, "") for name in re.findall(r"'([^']+)' does not depend on any axioms", text)]
names = {"SemiBase.order6_classification", "SemiBase.order6_finitelyBased",
         "SemiBase.order6_nonfinitelyBased", "SemiBase.Catalogue.order6_length",
         "SemiBase.Catalogue.order6_ids"}
seen = set()
for name, axioms in reports:
    used = {a.strip() for a in axioms.split(",") if a.strip()}
    if not used <= allowed:
        sys.exit(f"{name} uses {sorted(used - allowed)}")
    seen.add(name)
missing = names - seen
if missing:
    sys.exit(f"no axiom report for {sorted(missing)}")
print("OK: the main theorems use only propext, Classical.choice and Quot.sound")
EOF
