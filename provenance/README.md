# Provenance

The Lean development in this repository is taken from the campaign repository
at the certified commit `3ca29f044b09179f7015e349d6ef1640e7aaa7b4` (tag
`order6-final-20260906-15973`). On 6 September 2026 a whole-corpus audit rebuilt
that commit from source on Lean 4.28.0 and certified all 15,973 classes of order
six (run 6, status PASS).

## What was taken

Exactly the import closure of the endpoint theorems of the 15,973 classes, one
`BasisFor` theorem per class (for the four nonfinitely based classes, one
`NonfinitelyBased` theorem): 7,194 Lean files, byte-identical to the certified
commit. Everything else at that commit (earlier attempts, tests, audit modules,
research notes, the files of other orders) is left out.

## What was changed

`scripts/check_provenance.py` checks every Lean file against
`certified-blobs.txt` and allows exactly these differences.

1. **Removed:** the 15 files
   `SemigroupBasis/Generated/Order6CASExplicitSourceUpstream/PartNNN.lean`.
   Each is a strict subset of `Order6FinalL5TransferV3/PartNNN.lean`: the same
   imports, the same namespace, and a subset of its declarations, line for line.
   A Lean environment cannot load both, because the shared declarations would be
   declared twice; this is why the final audit checked the 75 classes that
   depend on them in separate runs.
2. **Changed:** in the 21 files of `modified-files.txt`, the line
   `import SemigroupBasis.Generated.Order6CASExplicitSourceUpstream.PartNNN` is
   replaced by `import Order6FinalL5TransferV3.PartNNN`. Nothing else changes.
   With 1 and 2, every endpoint can be loaded in one environment, which the
   classification theorem needs. For 21 classes the census map names one of the
   removed files as the module of the endpoint; the endpoint theorem, with the
   same name, is imported from the `Order6FinalL5TransferV3` part with the same
   number.
3. **New:** `lakefile.toml` (package name and default target; the same weak Lean
   arguments as the final audit), `lake-manifest.json` (package name), the
   statement layer `SemiBase/` and `SemiBase.lean`, `scripts/`, `provenance/`,
   `README.md`, `NOTICE.md` and `.gitignore`.

The statement layer takes the place of the audit's check modules. The audit
recovered the multiplication table from the type of each endpoint and compared
it with the catalogue in an `example`. Here each class has a named theorem
`SemiBase.Census.S6_k : Classified Catalogue.Order6.S6_k`, and
`SemiBase.order6_classification` collects all of them.

## Files

| File | Content |
|---|---|
| `final-certificate.json` | The audit certificate: status, the 15,973 certified classes, toolchain, allowed axioms, the sha256 of every file added to the earlier head |
| `FINAL-AUDIT.md` | The audit report: what was compiled, what was checked, the 69 version overrides |
| `final-census-map.json` | For every class, the endpoint theorem(s) the audit checked: module, name, statement |
| `version-overrides.json` | The 69 files that the audit took in a later or patched version; the certified commit contains these versions |
| `certified-blobs.txt` | `git ls-tree` of the certified commit for the 7,194 Lean files of the development |
| `modified-files.txt` | The 21 files with the changed import line |

## Independent re-certification

The certified commit was also rebuilt from a fresh clone and checked by the
`bases-min` seal tools of Mikoláš Janota, which read every endpoint back from
Lean: 15,969 finitely based classes with 536 distinct bases and 4 nonfinitely
based classes, no failures, and no axioms beyond `propext`, `Classical.choice`
and `Quot.sound`.
