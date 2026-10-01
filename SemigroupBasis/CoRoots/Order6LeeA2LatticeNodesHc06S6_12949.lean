import SemigroupBasis.CoRoots.Order6LeeA2LatticeNodesNormal

/-!
# Lee A2 lattice node `S6_12949`

This endpoint supplies the three coordinates of the
`SameCoalescedChainFinalAndHead` descriptor directly from the generated table:

* the quotient onto `S4_69` supplies support and the exact-cut signature;
* the right-zero band on elements `2` and `4` supplies the final letter;
* the left-zero band on elements `0` and `3` supplies the head letter.

The shared `derivesOfC06DescriptorEq` theorem then supplies derivational
completeness for the displayed seven-law basis.
-/

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6LeeA2LatticeNodesNormal

open SemigroupBasis
open SemigroupBasis.Examples

namespace S6_12949

abbrev table : FiniteTable :=
  Generated.Order6LeeA2LatticeNodes.S6_12949.table

/-- The table-certified quotient `[0,1,2,0,2,3]` from `S6_12949` onto
the exact `S4_69` separator detector. -/
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
  refine ⟨Generated.Order6LeeA2LatticeNodes.S6_12949.models, ?_⟩
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

end S6_12949

end SemigroupBasis.CoRoots.Order6LeeA2LatticeNodesNormal
