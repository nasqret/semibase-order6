# SemiBase: finite identity bases of the semigroups of order six

This repository contains Lean 4 proofs that every semigroup of order six is
finitely based, that is, has a finite identity basis, with exactly four
exceptions, which are proved to have no finite basis. The 15,973 semigroups of
order six, counted up to isomorphism and anti-isomorphism, are covered one by
one, and a single theorem states the whole classification. Every proof is
checked from source by the Lean kernel. The underlying logic is a dependent type
theory, a version of the calculus of inductive constructions, and the proofs use
no axioms beyond propositional extensionality, quotient soundness and the axiom
of choice.

The four exceptions are the semigroups `L`, `B₂¹`, `A₂ᵍ` and `A₂¹`, classes
`[6, 3843]`, `[6, 8564]`, `[6, 8878]` and `[6, 13747]` of the GAP library
Smallsemi. That they are the only nonfinitely based semigroups of order six was
shown by Lee, Li and Zhang (2012); Lee and Zhang (2015) treat the semigroups of
order six in detail, and the surveys of Volkov (2001) and Araújo et al. (2023)
describe the finite basis problem for finite semigroups. The proofs here were
written by language-model agents in a three-month campaign; see
[How the proofs were produced](#how-the-proofs-were-produced).

## The theorem

An *identity* is a pair of words `u ≈ v`. It holds in a semigroup `S` when every
substitution of elements of `S` for the variables gives equal values. A finite
list of identities `B` is a *basis* of `S` when the identities of `B` hold in `S`
and every identity of `S` can be derived from `B` by the usual rules of
equational logic. `S` is *finitely based* when it has a finite basis.

In Lean these are the definitions of `SemigroupBasis/Equational.lean` and
`SemigroupBasis/Nonfinite.lean`:

```lean
def SatisfiedBy (e : Identity α) (G : Semigroup S) : Prop :=
  ∀ valuation : α → S, G.eval valuation e.lhs = G.eval valuation e.rhs

def BasisFor (G : Semigroup S) (basis : List (Identity α)) : Prop :=
  Models G basis ∧
    ∀ e : Identity α, e.SatisfiedBy G → Derives basis e.lhs e.rhs

def FinitelyBased (G : Semigroup S) : Prop := FinitelyBasedOver G Nat
-- FinitelyBasedOver G α := ∃ basis : List (Identity α), BasisFor G basis
def NonfinitelyBased (G : Semigroup S) : Prop := NonfinitelyBasedOver G Nat
-- NonfinitelyBasedOver G α := ¬FinitelyBasedOver G α
```

`Derives basis` is the closure of the basis under reflexivity, symmetry,
transitivity, multiplication on either side, and substitution of words for
variables.

The classification is stated in `SemiBase/Classification.lean`:

```lean
theorem SemiBase.order6_classification :
    ∀ e ∈ Catalogue.order6, Classified e
```

`Catalogue.order6` lists the 15,973 classes `[6, 1]`, …, `[6, 15973]` with their
multiplication tables (`Catalogue.order6_length`, `Catalogue.order6_ids`), and
`Classified e` (in `SemiBase/Statement.lean`) says:

```lean
def Classified (e : Entry) : Prop :=
  (∃ G : Semigroup (Fin 6), HasTable G e.rows) ∧
    ∀ G : Semigroup (Fin 6), HasTable G e.rows →
      (e.id ∈ nonfinitelyBasedIds → NonfinitelyBased G) ∧
        (e.id ∉ nonfinitelyBasedIds → FinitelyBased G)
```

that is, the table of the class is the multiplication table of a semigroup, and
every semigroup on `Fin 6` with this table is nonfinitely based if the class is
one of `nonfinitelyBasedIds = [3843, 8564, 8878, 13747]`, and finitely based
otherwise. Two corollaries state the two halves separately:
`SemiBase.order6_finitelyBased` and `SemiBase.order6_nonfinitelyBased`.

Every finitely based class comes with an explicit basis: the endpoint
theorem of the class (listed in `provenance/final-census-map.json`) has the form
`BasisFor T.semigroup B` with a concrete list `B`.

## What a reader has to trust

The statement depends on a small amount of code. To check that the theorem says
what is claimed above, read:

1. `SemigroupBasis/Word.lean`, `SemigroupBasis/Equational.lean` and
   `SemigroupBasis/Nonfinite.lean` (lines 1 to 80): words, semigroups,
   evaluation, identities, derivations, `BasisFor`, `FinitelyBased` and
   `NonfinitelyBased`;
2. `SemiBase/Statement.lean`, lines 1 to 80: `Entry`, `HasTable`, `Classified`;
3. `SemiBase/Catalogue/Order6/Part*.lean`: the tables, as data;
4. `SemiBase/Classification.lean`: the final theorems.

Everything else is proof, checked by the Lean kernel. The tables are those of
Smallsemi 0.7.2 (see [Scope](#scope-and-limitations)).

## Are these the right tables?

The theorem is about the tables written in `SemiBase/Catalogue/Order6/`. Three
links connect them to the semigroups of order six, and each can be checked.

1. **GAP to the catalogue file.** `research/order6/catalogue.json` was exported
   from GAP Smallsemi 0.7.2 by `gap/export_order6_catalogue.g`, which writes
   the multiplication table of `SmallSemigroup(6, k)` for every `k`. With GAP
   and Smallsemi installed, running it again reproduces the file; its SHA-256,
   `944f356c42b8e703988f5684cd81b650f99cc0ccd1ef1d7fc6e900f2c95f287c`, is pinned
   in `scripts/check_catalogue.py`. Independently, the order-six census was
   regenerated from scratch with GAP 4.15.1 and Smallsemi 0.7.2 for the
   `bases-min` re-certification (files `gap/s6_1_10000.json` and
   `gap/s6_10001_15973.json` of that repository); all 15,973 tables agree with
   ours (`scripts/check_catalogue.py --gap <files>`).
2. **The catalogue file to the Lean data.** `scripts/check_catalogue.py` reads
   every table of the Lean data and compares it with `catalogue.json`, with the
   elements `1, …, 6` renamed `0, …, 5`; inside Lean, `Catalogue.order6_ids`
   and `Catalogue.order6_length` show that the entries are the classes
   `[6, 1]`, …, `[6, 15973]` in order.
3. **The Lean data to the proofs.** The statement `Classified` is about the
   catalogue table itself, and each `SemiBase.Census.S6_k` proves, by a kernel
   computation over all 36 products, that the semigroup of the endpoint theorem
   has exactly this table or its transpose. No file name, theorem name or
   generator has to be trusted: a proof about any other table does not
   typecheck.

The four nonfinitely based classes are also tied to the literature. Their
proofs work with the tables in the element order of the published sources and
prove in Lean that these are the catalogue tables, through an explicit
relabelling of the elements where the two orders differ (`B₂¹` and `A₂ᵍ`). And
`research/order6/published_classification.json` records Lee and Zhang's
classification over the same catalogue: `scripts/check_catalogue.py` checks
that its four exceptional classes are exactly `nonfinitelyBasedIds` of the
statement, and that each published table is the catalogue table under the
recorded relabelling.

## Verifying

You need [elan](https://github.com/leanprover/elan); Lean 4.28.0 is pinned in
`lean-toolchain` and installed on first use. There are no other dependencies
(no Mathlib).

```sh
git clone https://github.com/nasqret/semibase-order6.git
cd semibase-order6
./scripts/verify.sh
```

`scripts/verify.sh` does five things:

1. checks every Lean file of the development against the certified commit of
   the campaign (`scripts/check_provenance.py`);
2. checks the catalogue data against `catalogue.json` and the published
   classification (`scripts/check_catalogue.py`);
3. checks that every Lean file is imported by `SemiBase.lean`
   (`scripts/check_closure.py`);
4. builds everything from source with `lake build`;
5. prints the axioms of the main theorems and fails unless they are among
   `propext`, `Classical.choice` and `Quot.sound` (so no `sorry` and no
   `native_decide`).

A full build is a substantial computation: 7,179 files and 5.7 million lines
of Lean, compiled from source. Lake compiles as many files at a time as
`LEAN_NUM_THREADS` allows (by default, the number of cores), and some generated
files need tens of gigabytes each; compiling several of the 315 files of the
proof for class `[6, 12824]` (333,557 lines) at the same time needs more than
200 GB. On a machine with less memory, lower the parallelism, for example

```sh
LEAN_NUM_THREADS=4 ./scripts/verify.sh
```

The independent re-certification rebuilt the same files from a fresh clone in
about two hours with 96 parallel jobs.

## Repository map

Every Lean file in this repository is needed. The repository holds exactly the
files that `SemiBase.lean`, the root of the classification theorem, imports
directly or indirectly; `scripts/check_closure.py` checks this, and
`scripts/check_closure.py --table` recomputes the numbers below.

```text
SemiBase.lean                   root: imports the statement layer
SemiBase/                       the statement and its proof from the endpoints (written for this repository)
├── Statement.lean              what is claimed for one class: Entry, HasTable, Classified
├── Catalogue/Order6/           the 15,973 Smallsemi tables, as Lean data
├── Census/                     one theorem per class, from the endpoint of that class
└── Classification.lean         the classification theorem and its two halves
SemigroupBasis/                 the proof development of the campaign
├── *.lean                      core library: words, identities, derivations, BasisFor,
│                               finite tables, transfer lemmas
├── Examples/                   named families of small order; three nonfinite-basis proofs
├── Nonfinite/                  nonfinite-basis arguments; with Examples/, the four proofs
├── CoRoots/                    family proofs: one basis, proved complete once for a family
│   ├── S4_*, S5_*              families of orders 4 and 5, sources of transfers
│   └── Order6*                 families of order 6
├── Generated/                  machine-generated proofs
│   ├── Catalogue*              the tables of orders 1 to 5
│   ├── S2_* … S5_*, …          bases and proofs for orders 1 to 5, sources of transfers
│   ├── Order6Nilpotent/        certificates for nilpotent semigroups of order 6
│   ├── Order6Final*            the heaviest transfers of order 6
│   └── Order6*                 the other generated proofs of order 6
├── Order6Subdirect/            subdirect decompositions of order-6 semigroups
├── Order6/                     shared order-6 helpers
├── Normalization/              word normal forms
├── Order6ResidualReleaseV3/    thin wrappers that restate endpoints
└── Order7/                     one inflation lemma, used by four order-6 transfer files
Order6FinalL5TransferV3/        transfers from orders at most 5: the final sweep
research/formalization/         transfers from orders at most 5: earlier waves
research/order6/                the catalogue and the published classification (data)
gap/                            the GAP export of the catalogue
scripts/                        the checks and the generator of SemiBase/
provenance/                     the audit certificate and how this tree was derived
```

In the table, *needed by* counts the classes whose own proof (the endpoint
theorem and everything it imports) uses a file of the folder, and *endpoints*
counts the classes whose endpoint theorem lies in the folder; each class has
exactly one endpoint, so that column adds up to 15,973. The statement layer is
needed by every class.

| Folder | Files | Lines | Needed by | Endpoints | Used by the 4 nonfinite proofs |
|---|---:|---:|---:|---:|:---:|
| `SemiBase/` and `SemiBase.lean` | 218 | 152,771 | all | – | yes |
| `SemigroupBasis/*.lean` (core library) | 54 | 14,515 | 15,973 | 0 | yes |
| `SemigroupBasis/Examples/` | 122 | 71,592 | 15,864 | 3 | yes |
| `SemigroupBasis/Nonfinite/` | 19 | 26,328 | 4,840 | 1 | yes |
| `SemigroupBasis/CoRoots/S4_*`, `S5_*` | 419 | 166,820 | 7,017 | 5 | – |
| `SemigroupBasis/CoRoots/Order6*` | 1,891 | 571,514 | 1,203 | 478 | – |
| `SemigroupBasis/Generated/Catalogue*` | 15 | 15,792 | 15,012 | 0 | – |
| `SemigroupBasis/Generated/` (orders 1 to 5) | 138 | 114,565 | 15,564 | 0 | – |
| `SemigroupBasis/Generated/Order6Nilpotent/` | 158 | 396,964 | 129 | 26 | – |
| `SemigroupBasis/Generated/Order6Final*` | 2,988 | 2,410,530 | 63 | 63 | – |
| `SemigroupBasis/Generated/Order6*` (other) | 872 | 793,008 | 5,785 | 5,675 | – |
| `SemigroupBasis/Order6Subdirect/` | 21 | 3,075 | 379 | 0 | – |
| `SemigroupBasis/Order6/` | 13 | 2,923 | 438 | 12 | – |
| `SemigroupBasis/Normalization/` | 7 | 1,380 | 101 | 0 | – |
| `SemigroupBasis/Order6ResidualReleaseV3/` | 28 | 308 | 33 | 25 | – |
| `SemigroupBasis/Order7/` | 1 | 48 | 4 | 0 | – |
| `Order6FinalL5TransferV3/` | 360 | 747,286 | 6,183 | 5,519 | – |
| `research/formalization/` | 73 | 363,880 | 4,178 | 4,166 | – |

Two things stand out. The core library and the lower orders (orders 1 to 5,
tables and bases) are used by almost every class: most classes of order six are
proved by transfer from a smaller semigroup. And the size is concentrated in a
few classes: `SemigroupBasis/Generated/Order6Final*` holds 2.4 million lines,
42% of all Lean code, for the endpoints of 63 classes, among them the largest
proof, that of `[6, 12824]`.

### Reading the names

The names are those of the campaign and record how and when a proof was made,
not what it proves. The ones that occur most often:

| Name | Meaning |
|---|---|
| endpoint | the theorem that settles one class: `BasisFor T.semigroup B`, or its opposite, or `NonfinitelyBased T.semigroup`; `provenance/final-census-map.json` lists them |
| `CoRoots` | family proofs: a basis proved complete once for a family of semigroups that share it |
| `Generated` | proofs written by programs, not by hand: transfers, certificates, adapters |
| `L5` | the campaign's results for orders at most 5 (1,309 classes), used as sources of transfers |
| `Order6FinalL5TransferV3` | order 6, the final sweep of transfers from `L5`, third version of the generated output: a semigroup of order at most 5 with a certified basis embeds in the target, the target satisfies that basis, so the basis carries over |
| `…_l5_extension_v1` to `v3` (in `research/`) | earlier waves of the same transfers |
| `Order6FinalL5Unlocked…` | transfers of the final sweep that needed much heavier generated proofs, among them `[6, 12824]` |
| `EmbeddingTransfers`, `DivisorTransfers`, `DirectPower`, `FactorPair`, `FactorIntersection`, `ExactInflation` | the transfer used: an embedding, a quotient of a subsemigroup, an embedding into a direct power, a subdirect product of two factors, an inflation |
| `Order6Nilpotent/Certificates/CutoffN` | nilpotent semigroups whose products of `N` elements vanish: the basis lists the identities between short words |
| `Order6SporadicSection…` | the sporadic classes treated in the numbered sections of Lee and Zhang (2015); section 19 is `[6, 3842]` |
| `Order6LeeZhang…`, `Order6LeeLi…` | classes covered by sufficient conditions of Lee and Zhang, and of Lee and Li |
| `Order6Day7` … `Order6Day15`, `Order6Sunday` | batches of family proofs, named after the day of the finishing campaign |
| `Order6Astra` | the proof for `[6, 3842]`, named after the agent that wrote it |
| `CAS` | the campaign's search for transfers from lower orders, whose results were replayed in Lean |
| `S4_31`, `S5_207`, … | the Smallsemi class `[4, 31]`, `[5, 207]`, … |

## How the proofs work

**Family proofs.** Many semigroups of order six share a basis. A family proof
fixes a basis, proves once that it derives every identity of every semigroup of
the family, and checks the finitely many identities of the basis on each table
by computation (`decide`). The completeness proofs that succeeded have one
shape: a normal form for words, a few rewriting rules derived from the basis
that bring every word to its normal form, and a proof that the normal form is
determined by features of the word that the table can see, such as the order in
which letters first occur, the order in which they last occur, and the parity of
each letter.

**Generated proofs.** 445 classes have a generated proof of their own, which
builds on semigroups certified earlier. The common step is a transfer: if
a semigroup `S` with basis `B` embeds in a direct power of the target `T`, or is
a quotient of a subsemigroup of `T`, then every identity of `T` holds in `S` and
so follows from `B`; a check on the table that `T` satisfies `B` then makes `B` a
basis of `T` (`SemigroupBasis/TransferPower.lean`). Other generated proofs
combine the bases of the factors of a subdirect product, adapt the basis of a
semigroup that `T` inflates, or, for a nilpotent `T`, enumerate the identities
below the nilpotency degree. These proofs are long and uniform: the median has a
few hundred lines, nine have more than 100,000, and they are meant to be checked
by the kernel, not read.

**The four nonfinitely based semigroups.** Each proof exhibits infinitely many
identities of the semigroup and shows that, for every `k`, one of them does not
follow from identities in at most `k` variables, because a property of words
that separates its two sides survives every derivation step with such an
identity.

| Class | Identities | Argument | Lean |
|---|---|---|---|
| `L`, `[6, 3843]` | `x y₁²⋯yₙ² x ≈ x yₙ²⋯y₁² x` | Zhang and Luo (2011) | `SemigroupBasis/Examples/LeeLNonfinite*.lean`, `SemigroupBasis/Nonfinite/LeeL/` |
| `B₂¹`, `[6, 8564]` | `x y₁⋯yₙ x yₙ⋯y₁ ≈ x yₙ⋯y₁ x y₁⋯yₙ` | Perkins (1969), in the reconstruction of Sapir (1988) | `SemigroupBasis/Examples/B2OneNonfinite.lean`, `SemigroupBasis/Nonfinite/B2One/` |
| `A₂¹`, `[6, 13747]` | `X y X' y X ≈ X y X' y X y X' y X`, `X = x₁⋯xₙ`, `X'` its reverse | Trahtman (1987), Sapir (1988) | `SemigroupBasis/Examples/A2OneNonfinite.lean`, `SemigroupBasis/Nonfinite/A2One/` |
| `A₂ᵍ`, `[6, 8878]` | `(x₁²⋯xₙ²)² ≈ (x₁²⋯xₙ²)³` | a winding-parity argument on cycle words | `SemigroupBasis/Examples/AC2Nonfinite.lean`, `SemigroupBasis/Nonfinite/AC2/` |

**From endpoints to the statement.** Each class has an *endpoint*: one theorem
`BasisFor T.semigroup B` (or `BasisFor T.semigroup.opposite B`, or
`NonfinitelyBased T.semigroup`) about a concrete table `T`. The theorem
`SemiBase.Census.S6_k` checks by kernel computation that the semigroup of the
endpoint has the catalogue table of class `k`, or its transpose, and concludes
`Classified` for the class; a basis read backwards is a basis of the opposite
semigroup. For two classes, `[6, 11165]` and `[6, 11166]`, the endpoint table is
a relabelling of the catalogue table, and the explicit permutation is checked
instead. The files of `SemiBase/` are generated by `scripts/generate_census.py`
from the catalogue and the census map; a wrong choice in the generator could
only make the build fail.

## Provenance

The proofs come from the campaign repository at the commit
`3ca29f044b09179f7015e349d6ef1640e7aaa7b4` (tag `order6-final-20260906-15973`),
which a whole-corpus audit rebuilt from source and certified on 6 September
2026: every endpoint was checked against the catalogue table and for its axioms
(`provenance/final-certificate.json`, `provenance/FINAL-AUDIT.md`). The
certified commit was also rebuilt independently from a fresh clone and checked
by the `bases-min` seal tools.

This repository keeps only the files that the 15,973 endpoint theorems import,
directly or indirectly, byte-identical to the certified commit, with one
exception: 15 duplicate files were removed and 21 import lines changed, so that
all endpoints can be loaded at once. `provenance/README.md` gives the details,
and `scripts/check_provenance.py` checks them.

## Scope and limitations

- The catalogue of the 15,973 classes is taken from GAP Smallsemi 0.7.2
  (OEIS A001423). The repository does not prove in Lean that the catalogue
  contains every semigroup of order six, or that its tables are pairwise
  non-isomorphic and non-anti-isomorphic. What is proved is the statement above
  for each listed table.
- Isomorphic and anti-isomorphic copies are not listed. Finite basability is
  invariant under both: a basis of a semigroup is a basis of every isomorphic
  copy, and a basis read backwards is a basis of the opposite semigroup.
- The semigroups of orders one to five (1,309 classes) were treated by the same
  campaign; they are not part of this repository.
- The development uses Lean 4.28.0 and does not use Lean's module system.

## How the proofs were produced

All Lean code in this repository was written by language-model agents, Codex
agents (GPT-5-family models) as workers and a Claude agent as a referee, in a
campaign from June to September 2026. A scripted pipeline written by the agents
settled 14,989 classes; the remaining 984 classes needed individual work by the
agents, who proposed and refuted candidate bases, wrote the family proofs and
the generators of the individual proofs, and ran the builds. Published bases
were used where they existed. People chose the targets, approved changes to the
repository and restarted stalled agents; they did not write proofs. The
acceptance of a class never rested on an agent's judgement: a class counts only
when the Lean kernel checks its proof, as it does again when this repository is
built.

## Citing

The campaign is described in *Proving at Scale for Universal Algebra*, The 6th
Workshop on Mathematical Reasoning and AI (MATH-AI), NeurIPS 2026. A citable
archive of this repository will receive a DOI.

The repository is created and curated by
[@nasqret](https://github.com/nasqret).

## References

- J. Araújo, J. P. Araújo, P. J. Cameron, E. W. H. Lee and J. Raminhos, A survey
  on varieties generated by small semigroups and a companion website,
  J. Algebra 635 (2023) 698–735.
- A. Distler and J. D. Mitchell, Smallsemi, a library of small semigroups,
  GAP package, version 0.7.2.
- E. W. H. Lee, J. R. Li and W. T. Zhang, Minimal non-finitely based semigroups,
  Semigroup Forum 85 (2012) 577–580.
- E. W. H. Lee and W. T. Zhang, Finite basis problem for semigroups of order
  six, LMS J. Comput. Math. 18 (2015) 1–129.
- P. Perkins, Bases for equational theories of semigroups, J. Algebra 11 (1969)
  298–314.
- M. V. Sapir, Problems of Burnside type and the finite basis property in
  varieties of semigroups, Math. USSR-Izv. 30 (1988) 295–314.
- A. N. Trahtman, Some finite infinitely basable semigroups, Ural. Gos. Univ.
  Mat. Zap. 14 (1987) 128–131.
- M. V. Volkov, The finite basis problem for finite semigroups, Sci. Math. Jpn.
  53 (2001) 171–199.
- W. T. Zhang and Y. F. Luo, A new example of a minimal nonfinitely based
  semigroup, Bull. Aust. Math. Soc. 84 (2011) 484–491.

## Licence

This repository is free software: you can redistribute it and/or modify it
under the terms of the GNU General Public License as published by the Free
Software Foundation, either version 3 of the License, or (at your option) any
later version (SPDX: `GPL-3.0-or-later`). It is distributed in the hope that it
will be useful, but without any warranty; see the full text in `LICENSE`. The
multiplication tables are derived from GAP Smallsemi, which is distributed
under the same licence; see `NOTICE.md`.
