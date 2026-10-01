#!/usr/bin/env python3
"""Check the Lean files of the development against the certified commit.

`provenance/certified-blobs.txt` lists every Lean file of the development with
its Git blob id at the certified commit 3ca29f044 (tag
order6-final-20260906-15973) of the campaign repository. A file is
byte-identical to the certified version exactly when its Git blob id is the
same. The only allowed differences are the ones recorded in
`provenance/README.md`:

  * the files in `provenance/modified-files.txt` (one import line changed);
  * the removed directory `SemigroupBasis/Generated/Order6CASExplicitSourceUpstream/`;
  * the new statement layer under `SemiBase/` and the helper `scripts/Axioms.lean`.
"""
import hashlib
import os
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
REMOVED_PREFIX = "SemigroupBasis/Generated/Order6CASExplicitSourceUpstream/"


def blob_id(path):
    with open(path, "rb") as handle:
        data = handle.read()
    return hashlib.sha1(b"blob %d\0" % len(data) + data).hexdigest()


def main():
    certified = {}
    with open(os.path.join(ROOT, "provenance", "certified-blobs.txt")) as handle:
        for line in handle:
            meta, path = line.rstrip("\n").split("\t")
            certified[path] = meta.split()[2]
    with open(os.path.join(ROOT, "provenance", "modified-files.txt")) as handle:
        modified_allowed = {line.strip() for line in handle if line.strip()}

    identical = modified = removed = 0
    problems = []
    for path, blob in sorted(certified.items()):
        full = os.path.join(ROOT, path)
        if not os.path.exists(full):
            if path.startswith(REMOVED_PREFIX):
                removed += 1
            else:
                problems.append(f"missing: {path}")
        elif blob_id(full) == blob:
            identical += 1
        elif path in modified_allowed:
            modified += 1
        else:
            problems.append(f"differs from the certified commit: {path}")

    new = 0
    for directory, subdirectories, files in os.walk(ROOT):
        subdirectories[:] = [d for d in subdirectories if d not in (".lake", ".git")]
        for name in files:
            if not name.endswith(".lean"):
                continue
            path = os.path.relpath(os.path.join(directory, name), ROOT)
            if path in certified:
                continue
            if path.startswith("SemiBase/") or path in ("SemiBase.lean", "scripts/Axioms.lean"):
                new += 1
            else:
                problems.append(f"not in the certified commit: {path}")

    print(f"{identical} Lean files identical to the certified commit, "
          f"{modified} with the recorded import change, "
          f"{removed} recorded removals, {new} files of the statement layer")
    if problems:
        print("\n".join(problems))
        sys.exit(1)


if __name__ == "__main__":
    main()
