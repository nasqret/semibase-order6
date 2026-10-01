import SemigroupBasis.CoRoots.Order6LeeA2LatticeNodesNormal
import SemigroupBasis.CoRoots.S5_806Semantics

/-!
# Lee A2 lattice node `S6_12958`

This is the first endpoint using the `SystemHdefa5ab58c7c` coarsening of the
kernel-verified Lee-A2 trio pilot.  The endpoint follows the frozen pilot
assembly:

* validity is pushed through the recorded quotient onto `S5_806`, whose exact
  semantic theorem supplies the ordered component-base signatures and the
  final letter;
* the left-zero band on elements `0` and `3` supplies equality of word heads;
* `derivesOfDefaDescriptorEq` supplies derivational completeness for the
  displayed six-law basis.
-/

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6LeeA2LatticeNodesNormal

open SemigroupBasis
open SemigroupBasis.Examples

namespace S6_12958

abbrev table : FiniteTable :=
  Generated.Order6LeeA2LatticeNodes.S6_12958.table

/-- The msg-0118 quotient map from `S6_12958` onto the exact `S5_806`
component-signature detector. -/
def detectorSurjection :
    SplitSurjection table.semigroup
      Generated.Catalogue.S5_806.table.semigroup where
  toFun := fun a : Fin 6 =>
    (if a = 0 then 0 else
      if a = 1 then 1 else
        if a = 2 then 2 else
          if a = 3 then 0 else
            if a = 4 then 3 else 4 : Fin 5)
  map_mul := by decide
  preimage := fun b : Fin 5 =>
    (if b = 0 then 0 else
      if b = 1 then 1 else
        if b = 2 then 2 else
          if b = 3 then 4 else 5 : Fin 6)
  right_inverse := by decide

theorem representative_basis :
    BasisFor table.semigroup
      Generated.Order6LeeA2LatticeNodes.SystemHdefa5ab58c7c.basis := by
  refine ⟨Generated.Order6LeeA2LatticeNodes.S6_12958.models, ?_⟩
  intro identity valid
  apply derivesOfDefaDescriptorEq
  constructor
  · exact
      SemigroupBasis.CoRoots.S5_806.valid_sameConnectedCutSignature identity
        (detectorSurjection.pushforwardIdentity identity valid)
  · exact
      head_eq_of_band_valid (p := (0 : Fin 6)) (q := (3 : Fin 6))
        (by decide) (by decide) (by decide) (by decide) (by decide)
        identity valid

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis
        Generated.Order6LeeA2LatticeNodes.SystemHdefa5ab58c7c.basis) :=
  representative_basis.oppositeReversed

end S6_12958

end SemigroupBasis.CoRoots.Order6LeeA2LatticeNodesNormal
