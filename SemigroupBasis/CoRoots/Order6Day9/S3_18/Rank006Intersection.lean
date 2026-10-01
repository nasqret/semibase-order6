import SemigroupBasis.CoRoots.Order6Day9.S3_18.Rank006TileAlignment
import SemigroupBasis.CoRoots.Order6Day9.S3_18.Rank006FactorBridge

/-!
# Rank006: unrestricted completeness of the approved thirteen-law Sigma+

Every input has a Sigma+-derived canonical-tile realization. The actual
S4_69 factor identifies its separator skeleton; the actual C3 factor
identifies the total residues. Canonical tile alignment supplies the
Sigma+ derivation, completing exactly the positively reviewed obligation.
The lower normalizer is used only for its own semantic uniqueness theorem.
No alphabet, word-length, rank, multiplicity or search bound is present.
-/

namespace SemigroupBasis.CoRoots.Order6Day9.S3_18.Rank006Intersection

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.S5_107
open SemigroupBasis.CoRoots.Order6Day9.S3_18.Rank006SigmaPlus
open SemigroupBasis.CoRoots.Order6Day9.S3_18.Rank006Semantics
open SemigroupBasis.CoRoots.Order6Day9.S3_18.Rank006CanonicalTiles
open SemigroupBasis.CoRoots.Order6Day9.S3_18.Rank006TileAlignment

/-- Sound-direction conversion ONLY: every Sigma+ derivation is valid in
S4_69, whose independent seven-law basis is already complete. -/
theorem sigma_derives_lower {left right : Word Nat}
    (derivation : Derives sigmaPlus left right) :
    Derives uniqueSeparatorFourBasis left right := by
  apply uniqueSeparatorFourBasis_complete.2 (Identity.mk left right)
  have valid : (Identity.mk left right).SatisfiedBy rightTable.semigroup :=
    derivation.sound modelsRight
  rw [rightTable_eq_uniqueSeparatorFour] at valid
  exact valid

theorem sigma_list_derives_lower {left right : List Nat}
    (derivation : ListDerives sigmaPlus left right) :
    UniqueSeparatorListDerives left right := by
  cases derivation with
  | empty => exact UniqueSeparatorListDerives.empty
  | words wordDerivation =>
      exact UniqueSeparatorListDerives.words (sigma_derives_lower wordDerivation)

theorem sigma_list_mod {left right : List Nat}
    (derivation : ListDerives sigmaPlus left right) (letter : Nat) :
    left.count letter % 3 = right.count letter % 3 := by
  cases derivation with
  | empty => rfl
  | @words leftHead rightHead leftTail rightTail wordDerivation =>
      let identity : Identity Nat :=
        ⟨listWordOfCons leftHead leftTail, listWordOfCons rightHead rightTail⟩
      have valid : identity.SatisfiedBy leftTable.semigroup := wordDerivation.sound modelsLeft
      exact (leftValid_iff_mod_eq identity).mp valid letter

/-- Factor-valid arbitrary words have exactly the same canonical tile
skeleton, even though their actual square roots need not agree. -/
theorem canonical_shadows_eq (left right : Word Nat) (leftTiles rightTiles : List Tile)
    (leftCanonical : UniqueSeparatorCanonical (shadows leftTiles))
    (rightCanonical : UniqueSeparatorCanonical (shadows rightTiles))
    (leftDerives : ListDerives sigmaPlus left.toList (tilesRender leftTiles))
    (rightDerives : ListDerives sigmaPlus right.toList (tilesRender rightTiles))
    (valid : (Identity.mk left right).SatisfiedBy rightTable.semigroup) :
    shadows leftTiles = shadows rightTiles := by
  have leftLower := (sigma_list_derives_lower leftDerives).trans (tiles_lower_derives leftTiles)
  have rightLower := (sigma_list_derives_lower rightDerives).trans (tiles_lower_derives rightTiles)
  obtain ⟨leftHead, leftTail, leftRendered, leftWordDerives⟩ := leftLower.from_cons
  obtain ⟨rightHead, rightTail, rightRendered, rightWordDerives⟩ := rightLower.from_cons
  apply uniqueSeparatorCanonical_eq_of_equalEval leftCanonical rightCanonical
    (Word.mk leftHead leftTail) (Word.mk rightHead rightTail)
  · exact leftRendered.symm
  · exact rightRendered.symm
  · intro valuation
    have originalValid : (Identity.mk left right).SatisfiedBy uniqueSeparatorFour.semigroup := by
      rw [rightTable_eq_uniqueSeparatorFour] at valid
      exact valid
    exact (leftWordDerives.sound uniqueSeparatorFourBasis_models valuation).symm.trans
      ((originalValid valuation).trans (rightWordDerives.sound uniqueSeparatorFourBasis_models valuation))

/-- The literal unrestricted statement approved in fable msg-0367. -/
theorem complete : Complete := by
  intro identity leftValid rightValid
  obtain ⟨leftTiles, leftCanonical, leftNonempty, leftDerives⟩ := canonical_tiles_word identity.lhs
  obtain ⟨rightTiles, rightCanonical, rightNonempty, rightDerives⟩ := canonical_tiles_word identity.rhs
  have sameShadows := canonical_shadows_eq identity.lhs identity.rhs leftTiles rightTiles
    leftCanonical rightCanonical leftDerives rightDerives rightValid
  have residues : ∀ letter,
      (tilesRender leftTiles).count letter % 3 = (tilesRender rightTiles).count letter % 3 := by
    intro letter
    exact (sigma_list_mod leftDerives letter).symm.trans
      (((leftValid_iff_mod_eq identity).mp leftValid letter).trans (sigma_list_mod rightDerives letter))
  have comparison := tiles_derives_of_shadow_mod leftTiles rightTiles
    leftCanonical rightCanonical sameShadows residues
  have assembled := leftDerives.trans (comparison.trans rightDerives.symm)
  exact ListDerives.toWord assembled

def intersectionBasis : IntersectionBasis leftTable.semigroup rightTable.semigroup sigmaPlus :=
  intersectionBasisOfComplete complete

theorem derives_of_descriptor_eq (left right : Word Nat)
    (same : descriptor left = descriptor right) : Derives sigmaPlus left right :=
  complete_iff_descriptor_reach.mp complete left right same

theorem basisFor (target : FiniteTable) (pair : FinitePair target) :
    BasisFor target.semigroup sigmaPlus :=
  basisForOfComplete complete target pair

theorem basisForOpposite (target : FiniteTable) (pair : FinitePairOpposite target) :
    BasisFor target.semigroup.opposite (reversedBasis sigmaPlus) :=
  basisForOppositeOfComplete complete target pair

/-- Unconditional shared owner theorem for codex-0's S4_124/S4_69 route.
This is not a finite witness or a class endpoint for S6_14914. -/
def expandedIntersectionBasis :
    IntersectionBasis Rank006FactorBridge.expandedLeft.semigroup rightTable.semigroup sigmaPlus :=
  Rank006FactorBridge.intersectionBasisExpandedOfComplete complete

end SemigroupBasis.CoRoots.Order6Day9.S3_18.Rank006Intersection
