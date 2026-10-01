import SemigroupBasis.CoRoots.Order6FactorPairS2S5348Prelude
import SemigroupBasis.CoRoots.Order6FactorPairS2S5348Duality
import SemigroupBasis.CoRoots.Order6FactorPairS2S5348ReversalBridge
import SemigroupBasis.CoRoots.Order6FactorPairS2S5381Normal
import SemigroupBasis.Subdirect

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6FactorPairS2S5348

open SemigroupBasis
open SemigroupBasis.CoRoots.Order6FactorPairS2S5348Duality
open SemigroupBasis.CoRoots.Order6FactorPairS2S5348ReversalBridge

private def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

private def finiteBasis : List (Identity (Fin 3)) :=
  basis.map fun identity => identity.map toFinThree

private theorem basisRoundTripChecked :
    basis.all (fun identity =>
      decide ((identity.map toFinThree).map Fin.val = identity)) = true := by
  decide

private theorem modelsOfFiniteChecks
    (table : FiniteTable)
    (checked : finiteBasis.all table.checkIdentity = true) :
    Models table.semigroup basis := by
  intro identity member
  have finiteMember : identity.map toFinThree ∈ finiteBasis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    table.checkIdentityNat_sound (identity.map toFinThree)
      ((List.all_eq_true.mp checked) _ finiteMember)
  have restored : (identity.map toFinThree).map Fin.val = identity :=
    of_decide_eq_true <|
      (List.all_eq_true.mp basisRoundTripChecked) identity member
  rw [restored] at finiteValid
  exact finiteValid

/-- Every displayed axiom is valid in the cyclic factor. -/
theorem modelsS2_2 :
    Models SemigroupBasis.Generated.S2_2.table.semigroup basis :=
  modelsOfFiniteChecks SemigroupBasis.Generated.S2_2.table (by decide)

set_option maxHeartbeats 1000000 in
/-- Every displayed axiom is valid in the direct `S5_348` factor. -/
theorem modelsS5_348 :
    Models
      SemigroupBasis.Generated.Catalogue.S5_348.table.semigroup basis :=
  modelsOfFiniteChecks
    SemigroupBasis.Generated.Catalogue.S5_348.table (by decide)

/-- Unrestricted completeness of the exact thirteen-law system for the
intersection of the `S2_2` and `S5_348` identity theories.

The proof reverses the target identity, applies the already complete
`S2_2 x S5_381` normalizer, reverses that derivation, and transports its
thirteen reversed axioms through the explicit two-step-or-shorter bridge. -/
theorem derivesOfFactorValid
    (identity : Identity Nat)
    (cyclicValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S2_2.table.semigroup)
    (s5Valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_348.table.semigroup) :
    Derives basis identity.lhs identity.rhs := by
  have reversedDerivation :
      Derives
        SemigroupBasis.CoRoots.Order6FactorPairS2S5381.basis
        identity.reversed.lhs identity.reversed.rhs :=
    SemigroupBasis.CoRoots.Order6FactorPairS2S5381.derivesOfFactorValid
      identity.reversed
      (s2_2_reversed_valid identity cyclicValid)
      (s5_381_reversed_valid_of_s5_348_valid identity s5Valid)
  have returned := reversedDerivation.reverse
  have transported :=
    returned.transport reversedS2S5381AxiomDerives
  cases identity
  simpa [Identity.reversed] using transported

/-- The exact finite basis for
`V(S2_2) ∩ V(S5_348)`. -/
def intersectionBasis :
    IntersectionBasis
      SemigroupBasis.Generated.S2_2.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_348.table.semigroup
      basis where
  leftModels := modelsS2_2
  rightModels := modelsS5_348
  complete := derivesOfFactorValid

end SemigroupBasis.CoRoots.Order6FactorPairS2S5348
