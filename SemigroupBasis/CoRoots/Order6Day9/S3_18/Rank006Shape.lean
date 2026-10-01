import SemigroupBasis.FiniteCertificate
import SemigroupBasis.Generated.CatalogueOrder3
import SemigroupBasis.Generated.CatalogueOrder4
import SemigroupBasis.Generated.Order6OneLocalFordLord.DisplayedSigma
import SemigroupBasis.Subdirect

/-!
# Rank006: exact twelve-law owner shape and finite-witness interface

The two factors are the DIRECT catalogue representatives S3_18 and S4_69.
The original twelve-law sigma is reused literally, without any of the seven
historical bounded-repair bridges.  S3 supplies the class-specific finite
pairs; S1 separately supplies unrestricted completeness.  The conditional
assembly functions below do not assert that completeness has been proved.
-/

namespace SemigroupBasis.CoRoots.Order6Day9.S3_18.Rank006Shape

open SemigroupBasis

abbrev leftTable : FiniteTable := Generated.Catalogue.S3_18.table
abbrev rightTable : FiniteTable := Generated.Catalogue.S4_69.table

abbrev basis : List (Identity Nat) :=
  Generated.Order6OneLocalFordLord.DisplayedSigma.Sigma_a6866cfa3ad92ae2.basis

abbrev displayedBasisSHA256 : String :=
  Generated.Order6OneLocalFordLord.DisplayedSigma.Sigma_a6866cfa3ad92ae2.sha256

theorem basis_length : basis.length = 12 := by decide

private def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

/-- Exact soundness of every original law in the direct cyclic-three factor. -/
theorem modelsLeft : Models leftTable.semigroup basis :=
  FiniteCertificate.checkModels_sound leftTable basis toFinThree (by decide)

/-- Exact soundness of every original law in the direct unique-separator factor. -/
theorem modelsRight : Models rightTable.semigroup basis :=
  FiniteCertificate.checkModels_sound rightTable basis toFinThree (by decide)

/-- The finite-only contract: actual class table, split maps, joint injection. -/
abbrev FinitePair (target : FiniteTable) :=
  SubdirectPair target.semigroup leftTable.semigroup rightTable.semigroup

/-- Opposite finite witnesses must reverse both factor orientations literally. -/
abbrev FinitePairOpposite (target : FiniteTable) :=
  SubdirectPair target.semigroup.opposite
    leftTable.semigroup.opposite rightTable.semigroup.opposite

/-- S1's outstanding unrestricted obligation; no rank or word-length bound. -/
def Complete : Prop :=
  ∀ identity : Identity Nat,
    identity.SatisfiedBy leftTable.semigroup →
    identity.SatisfiedBy rightTable.semigroup →
    Derives basis identity.lhs identity.rhs

theorem derives_factor_valid {left right : Word Nat}
    (derivation : Derives basis left right) :
    (Identity.mk left right).SatisfiedBy leftTable.semigroup ∧
      (Identity.mk left right).SatisfiedBy rightTable.semigroup :=
  ⟨derivation.sound modelsLeft, derivation.sound modelsRight⟩

theorem factor_valid_iff_of_pair
    (target : FiniteTable) (pair : FinitePair target) (identity : Identity Nat) :
    identity.SatisfiedBy target.semigroup ↔
      (identity.SatisfiedBy leftTable.semigroup ∧
        identity.SatisfiedBy rightTable.semigroup) :=
  pair.satisfiedBy_iff identity

theorem modelsOfPair (target : FiniteTable) (pair : FinitePair target) :
    Models target.semigroup basis := by
  intro identity member
  exact (pair.satisfiedBy_iff identity).mpr
    ⟨modelsLeft identity member, modelsRight identity member⟩

/-- Conditional only: constructing this value still requires the full converse. -/
def intersectionBasisOfComplete (complete : Complete) :
    IntersectionBasis leftTable.semigroup rightTable.semigroup basis where
  leftModels := modelsLeft
  rightModels := modelsRight
  complete := complete

theorem basisForOfComplete (complete : Complete)
    (target : FiniteTable) (pair : FinitePair target) :
    BasisFor target.semigroup basis :=
  (intersectionBasisOfComplete complete).basisFor pair

theorem basisForOppositeOfComplete (complete : Complete)
    (target : FiniteTable) (pair : FinitePairOpposite target) :
    BasisFor target.semigroup.opposite (reversedBasis basis) :=
  (intersectionBasisOfComplete complete).oppositeReversed.basisFor pair

end SemigroupBasis.CoRoots.Order6Day9.S3_18.Rank006Shape
