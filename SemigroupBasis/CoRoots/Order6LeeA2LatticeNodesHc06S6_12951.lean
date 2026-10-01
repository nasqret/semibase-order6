import SemigroupBasis.CoRoots.Order6LeeA2LatticeNodesNormal

/-!
# Lee A2 lattice node `S6_12951`

The `S4_69` quotient supplies the support/exact-cut coordinates, the
right-zero band `(2,4)` supplies the final letter, and the left-zero band
`(0,3)` supplies the head letter.
-/

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6LeeA2LatticeNodesNormal

open SemigroupBasis
open SemigroupBasis.Examples

namespace S6_12951

abbrev table : FiniteTable :=
  Generated.Order6LeeA2LatticeNodes.S6_12951.table

/-- The table-certified quotient `[0,1,2,0,2,3]` onto `S4_69`. -/
def separatorDetector :
    SplitSurjection table.semigroup
      Generated.Catalogue.S4_69.table.semigroup where
  toFun := fun a : Fin 6 =>
    (if a = 0 then 0 else
      if a = 1 then 1 else
        if a = 2 then 2 else
          if a = 3 then 0 else
            if a = 4 then 2 else 3 : Fin 4)
  map_mul := by decide
  preimage := fun b : Fin 4 =>
    (if b = 0 then 0 else
      if b = 1 then 1 else
        if b = 2 then 2 else 5 : Fin 6)
  right_inverse := by decide

theorem representative_basis :
    BasisFor table.semigroup
      Generated.Order6LeeA2LatticeNodes.SystemHc06cb5d53d74.basis := by
  refine ⟨Generated.Order6LeeA2LatticeNodes.S6_12951.models, ?_⟩
  intro identity valid
  apply derivesOfC06DescriptorEq
  apply SameCoalescedChainFinalAndHead.of_s4_69_valid_final_head
  · exact separatorDetector.pushforwardIdentity identity valid
  · exact
      final_eq_of_band_valid (p := (2 : Fin 6)) (q := (4 : Fin 6))
        (by decide) (by decide) (by decide) (by decide) (by decide)
        identity valid
  · exact
      head_eq_of_band_valid (p := (0 : Fin 6)) (q := (3 : Fin 6))
        (by decide) (by decide) (by decide) (by decide) (by decide)
        identity valid

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis
        Generated.Order6LeeA2LatticeNodes.SystemHc06cb5d53d74.basis) :=
  representative_basis.oppositeReversed

end S6_12951

end SemigroupBasis.CoRoots.Order6LeeA2LatticeNodesNormal
