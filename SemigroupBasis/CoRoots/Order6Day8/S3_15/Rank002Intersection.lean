import SemigroupBasis.CoRoots.Order6Day7.S3_15op.SeedS5_841
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCQuotientNormal
import SemigroupBasis.Generated.S3_15
import SemigroupBasis.FiniteCertificate

/-!
# Unrestricted S3_15 × S5_841 completeness for the exact Rank002 sigma

The actual S5_841 anti-automorphism transports right-factor validity under
word reversal.  The independently proved Rank064 seed then derives the
reversed identity.  Every one of its eight reversed displayed laws is
explicitly replayed below into the exact Rank002 basis, with concrete
variable permutations and closed `decide` membership checks.

This module proves the unrestricted factor intersection only.  The finite
class witnesses for S6_13385 and S6_13612 remain owned by codex-S3.
-/

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6Day8.S3_15.Rank002Intersection

open SemigroupBasis

abbrev leftTable : FiniteTable := Generated.S3_15.table
abbrev rightTable : FiniteTable := SemigroupBasis.CoRoots.S5_841.table

def law00 : Identity Nat :=
  ⟨Word.mk 0 [0], Word.mk 0 [0, 0]⟩
def law01 : Identity Nat :=
  ⟨Word.mk 0 [0, 1, 0], Word.mk 0 [1, 0]⟩
def law02 : Identity Nat :=
  ⟨Word.mk 0 [1, 0], Word.mk 0 [1, 0, 0]⟩
def law03 : Identity Nat :=
  ⟨Word.mk 0 [1, 0, 1], Word.mk 0 [1, 1, 0]⟩
def law04 : Identity Nat :=
  ⟨Word.mk 0 [1, 0, 2, 0], Word.mk 0 [1, 2, 0]⟩
def law05 : Identity Nat :=
  ⟨Word.mk 0 [1, 2, 0, 1], Word.mk 0 [1, 2, 1, 0]⟩
def law06 : Identity Nat :=
  ⟨Word.mk 0 [1, 2, 0, 2], Word.mk 0 [1, 2, 2, 0]⟩
def law07 : Identity Nat :=
  ⟨Word.mk 0 [1, 2, 1, 2], Word.mk 0 [2, 1, 1, 2]⟩

/-- The exact ordered eight laws from the frozen S3_15/S5_841 route. -/
def basis : List (Identity Nat) :=
  [law00, law01, law02, law03, law04, law05, law06, law07]

def displayedBasisSHA256 : String :=
  "60501c06483a0a3c358993c36acfe8d2ba0573648994c3d2df389c8fc3376d4d"

private def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

/-- Every exact displayed law holds in the actual S3_15 factor. -/
theorem modelsLeft : Models leftTable.semigroup basis :=
  FiniteCertificate.checkModels_sound leftTable basis toFinThree (by decide)

/-- Every exact displayed law holds in the actual S5_841 factor. -/
theorem modelsRight : Models rightTable.semigroup basis :=
  FiniteCertificate.checkModels_sound rightTable basis toFinThree (by decide)

private def renameThree
    (first second third : Nat) : Nat → Word Nat
  | 0 => Word.singleton first
  | 1 => Word.singleton second
  | 2 => Word.singleton third
  | marker + 3 => Word.singleton (marker + 3)

theorem reversedLaw00 :
    Derives basis (Word.mk 0 [0]) (Word.mk 0 [0, 0]) :=
  Derives.fromBasis (e := law00) (by decide)

theorem reversedLaw01 :
    Derives basis (Word.mk 0 [1, 0, 0]) (Word.mk 0 [1, 0]) :=
  (Derives.fromBasis (e := law02) (by decide)).symm

theorem reversedLaw02 :
    Derives basis (Word.mk 0 [1, 0]) (Word.mk 0 [0, 1, 0]) :=
  (Derives.fromBasis (e := law01) (by decide)).symm

theorem reversedLaw03 :
    Derives basis (Word.mk 1 [0, 1, 0]) (Word.mk 1 [0, 0, 1]) := by
  have primitive :
      Derives basis (Word.mk 0 [1, 0, 1]) (Word.mk 0 [1, 1, 0]) :=
    Derives.fromBasis (e := law03) (by decide)
  simpa [renameThree, Word.bind, Word.singleton, Word.append] using
    Derives.subst primitive (renameThree 1 0 2)

theorem reversedLaw04 :
    Derives basis
      (Word.mk 2 [1, 0, 1, 0]) (Word.mk 2 [0, 1, 1, 0]) := by
  have primitive :
      Derives basis (Word.mk 0 [1, 2, 1, 2]) (Word.mk 0 [2, 1, 1, 2]) :=
    Derives.fromBasis (e := law07) (by decide)
  simpa [renameThree, Word.bind, Word.singleton, Word.append] using
    Derives.subst primitive (renameThree 2 1 0)

theorem reversedLaw05 :
    Derives basis (Word.mk 0 [2, 0, 1, 0]) (Word.mk 0 [2, 1, 0]) := by
  have primitive :
      Derives basis (Word.mk 0 [1, 0, 2, 0]) (Word.mk 0 [1, 2, 0]) :=
    Derives.fromBasis (e := law04) (by decide)
  simpa [renameThree, Word.bind, Word.singleton, Word.append] using
    Derives.subst primitive (renameThree 0 2 1)

theorem reversedLaw06 :
    Derives basis
      (Word.mk 1 [2, 0, 1, 0]) (Word.mk 1 [2, 0, 0, 1]) := by
  have primitive :
      Derives basis (Word.mk 0 [1, 2, 0, 2]) (Word.mk 0 [1, 2, 2, 0]) :=
    Derives.fromBasis (e := law06) (by decide)
  simpa [renameThree, Word.bind, Word.singleton, Word.append] using
    Derives.subst primitive (renameThree 1 2 0)

theorem reversedLaw07 :
    Derives basis
      (Word.mk 1 [0, 2, 1, 0]) (Word.mk 1 [0, 2, 0, 1]) := by
  have primitive :
      Derives basis (Word.mk 0 [1, 2, 0, 1]) (Word.mk 0 [1, 2, 1, 0]) :=
    Derives.fromBasis (e := law05) (by decide)
  simpa [renameThree, Word.bind, Word.singleton, Word.append] using
    Derives.subst primitive (renameThree 1 0 2)

/-- All eight reversed source axioms have actual displayed-basis derivations. -/
theorem reversedSourceAxiomsDeriveDisplayed
    (identity : Identity Nat)
    (member : identity ∈ reversedBasis
      SemigroupBasis.CoRoots.Order6Day7.S3_15op.Rank064.basis) :
    Derives basis identity.lhs identity.rhs := by
  simp only [reversedBasis,
    SemigroupBasis.CoRoots.Order6Day7.S3_15op.Rank064.basis,
    List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact reversedLaw00
  · exact reversedLaw01
  · exact reversedLaw02
  · exact reversedLaw03
  · exact reversedLaw04
  · exact reversedLaw05
  · exact reversedLaw06
  · exact reversedLaw07

/-- Reversal transfers actual S3_15 validity to the source's opposite factor. -/
theorem reversedLeftValidity
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy leftTable.semigroup) :
    identity.reversed.SatisfiedBy
      SemigroupBasis.CoRoots.Order6L3HeavyRank2.s3_15OppositeTable.semigroup := by
  rw [SemigroupBasis.CoRoots.Order6L3HeavyRank2.s3_15OppositeTable_semigroup]
  apply
    (Identity.satisfiedBy_opposite_iff_reversed identity.reversed
      Generated.S3_15.table.semigroup).mpr
  simpa using leftValid

/-- The actual five-element anti-automorphism preserves reversed validity. -/
theorem reversedRightValidity
    (identity : Identity Nat)
    (rightValid : identity.SatisfiedBy rightTable.semigroup) :
    identity.reversed.SatisfiedBy rightTable.semigroup := by
  have oppositeValid :=
    SemigroupBasis.CoRoots.S5_841.selfDuality.pullback_identity
      identity rightValid
  exact
    (Identity.satisfiedBy_opposite_iff_reversed
      identity rightTable.semigroup).mp oppositeValid

/-- Unrestricted exact Rank002 intersection completeness, before any class
witness, quotient normalizer, or endpoint is introduced. -/
theorem derivesOfFactorValid
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy leftTable.semigroup)
    (rightValid : identity.SatisfiedBy rightTable.semigroup) :
    Derives basis identity.lhs identity.rhs := by
  have source :=
    SemigroupBasis.CoRoots.Order6Day7.S3_15op.SeedS5_841.derivesOfFactorValid
      identity.reversed
      (reversedLeftValidity identity leftValid)
      (reversedRightValidity identity rightValid)
  have returned :
      Derives
        (reversedBasis
          SemigroupBasis.CoRoots.Order6Day7.S3_15op.Rank064.basis)
        identity.lhs identity.rhs := by
    simpa [Identity.reversed] using source.reverse
  exact returned.transport reversedSourceAxiomsDeriveDisplayed

/-- The displayed basis defines exactly the arbitrary-word factor intersection. -/
theorem factor_valid_iff_derives (identity : Identity Nat) :
    (identity.SatisfiedBy leftTable.semigroup ∧
      identity.SatisfiedBy rightTable.semigroup) ↔
      Derives basis identity.lhs identity.rhs := by
  constructor
  · rintro ⟨leftValid, rightValid⟩
    exact derivesOfFactorValid identity leftValid rightValid
  · intro derivation
    exact ⟨derivation.sound modelsLeft, derivation.sound modelsRight⟩

def intersectionBasis :
    IntersectionBasis leftTable.semigroup rightTable.semigroup basis where
  leftModels := modelsLeft
  rightModels := modelsRight
  complete := derivesOfFactorValid

/-- Quotient normalization is constructed strictly after unrestricted completeness. -/
noncomputable def intersectionNormalizer :
    IntersectionNormalizer leftTable.semigroup rightTable.semigroup basis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer
    intersectionBasis

end SemigroupBasis.CoRoots.Order6Day8.S3_15.Rank002Intersection
