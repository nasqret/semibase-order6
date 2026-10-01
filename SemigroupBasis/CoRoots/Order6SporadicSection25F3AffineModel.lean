import SemigroupBasis.CoRoots.Order6SporadicSection25F4Soundness

namespace SemigroupBasis.CoRoots.Order6SporadicSection25
open SemigroupBasis

private def extraLawTwoVariables : Nat → Fin 2
  | 0 => 0
  | _ => 1

theorem law24_affine_valid :
    law24.SatisfiedBy Generated.Catalogue.S4_96.table.semigroup.opposite := by
  have roundTrip : (law24.map extraLawTwoVariables).map Fin.val = law24 := by decide
  have checked := FiniteTable.checkIdentityFusedNat_sound
    (Order6Subdirect.oppositeTable Generated.Catalogue.S4_96.table)
    (law24.map extraLawTwoVariables) (by decide)
  rw [roundTrip] at checked
  exact checked

theorem basis_true_models_affine :
    Models Generated.Catalogue.S4_96.table.semigroup.opposite (basis true) := by
  intro identity member
  change identity ∈ coreBasis ++ [law24] at member
  rcases List.mem_append.mp member with core | extra
  · exact core_models_affine identity core
  · have equal : identity = law24 := List.mem_singleton.mp extra
    subst identity
    exact law24_affine_valid

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.law24_affine_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.basis_true_models_affine

end SemigroupBasis.CoRoots.Order6SporadicSection25
