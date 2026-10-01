import SemigroupBasis.CoRoots.S5_1155
import SemigroupBasis.CoRoots.S5_381Invariant
import SemigroupBasis.Generated.CommutativePositiveModThreeTransfersLayer1

namespace SemigroupBasis.CoRoots.S5_1155

open SemigroupBasis
open SemigroupBasis.Examples

private theorem catalogueS3_6_table_eq_finalMarkerThree :
    Generated.Catalogue.S3_6.table = finalMarkerThree := by
  unfold Generated.Catalogue.S3_6.table finalMarkerThree
  rw [FiniteTable.mk.injEq]
  refine ⟨rfl, heq_of_eq ?_⟩
  funext left right
  decide +revert

private theorem simpleInitialMarker_eq_of_initialMarker_valid
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        initialMarkerFactorTable.semigroup.opposite) :
    simpleInitialMarker identity.lhs =
      simpleInitialMarker identity.rhs := by
  have finalMarkerValid :
      identity.SatisfiedBy finalMarkerThree.semigroup.opposite := by
    rw [← catalogueS3_6_table_eq_finalMarkerThree]
    exact valid
  have sameInitial :
      ∀ letter,
        S5_107.SimpleInitial identity.lhs letter ↔
          S5_107.SimpleInitial identity.rhs letter :=
    S5_381Invariant.oppositeFinalMarkerValid_simpleInitial_iff
      identity finalMarkerValid
  by_cases leftSimple :
      identity.lhs.toList.count identity.lhs.head = 1
  · have leftInitial :
        S5_107.SimpleInitial identity.lhs identity.lhs.head :=
      ⟨leftSimple, rfl⟩
    have rightInitial :=
      (sameInitial identity.lhs.head).mp leftInitial
    have rightSimpleAtLeft :
        identity.rhs.toList.count identity.lhs.head = 1 :=
      rightInitial.1
    have headEqual : identity.rhs.head = identity.lhs.head :=
      rightInitial.2
    have rightSimple :
        identity.rhs.toList.count identity.rhs.head = 1 := by
      simpa [headEqual] using rightSimpleAtLeft
    unfold simpleInitialMarker
    rw [if_pos leftSimple, if_pos rightSimple, headEqual]
  · have rightNotSimple :
        identity.rhs.toList.count identity.rhs.head ≠ 1 := by
      intro rightSimple
      have rightInitial :
          S5_107.SimpleInitial identity.rhs identity.rhs.head :=
        ⟨rightSimple, rfl⟩
      have leftInitial :=
        (sameInitial identity.rhs.head).mpr rightInitial
      apply leftSimple
      rw [leftInitial.2]
      exact leftInitial.1
    simp [simpleInitialMarker, leftSimple, rightNotSimple]

/-- Validity in the exact `S5_1155` table preserves support, positive
multiplicity modulo three, and the optional globally simple initial letter. -/
theorem sameSemanticSignature_of_valid
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    SameSemanticSignature identity.lhs identity.rhs := by
  have factors := (valid_iff_factors identity).mp valid
  exact
    ⟨Generated.CommutativePositiveModThreeTransfers.S4_125.valid_support
        identity factors.1,
      Generated.CommutativePositiveModThreeTransfers.S4_125.valid_count_mod_three
        identity factors.1,
      simpleInitialMarker_eq_of_initialMarker_valid identity factors.2⟩

/-- Every derivation from the four-law basis preserves the exact semantic
signature certified by the two factors. -/
theorem derives_sameSemanticSignature
    {left right : Word Nat}
    (derivation : Derives basis left right) :
    SameSemanticSignature left right :=
  sameSemanticSignature_of_valid ⟨left, right⟩
    (fun valuation => derivation.sound models valuation)

end SemigroupBasis.CoRoots.S5_1155
