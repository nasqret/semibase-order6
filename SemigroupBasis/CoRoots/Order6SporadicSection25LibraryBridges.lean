import SemigroupBasis.CoRoots.Order6SporadicSection25AnchoredAffine
import SemigroupBasis.Generated.S4_96

/-! Exact actual-affine representation bridges, not a discharge of either
hull's open derivational obligation. The separate frozen-hull bridges retain
the two historical exhaustive model-check imports and are staged separately. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection25
open SemigroupBasis

theorem affineCore_eq_reversed_library_basis :
    affineCore = reversedBasis Examples.affineParityFourBasis := by decide

theorem affineCore_basisFor_actual_catalogue :
    BasisFor Generated.Catalogue.S4_96.table.semigroup.opposite affineCore := by
  rw [affineCore_eq_reversed_library_basis]
  exact Generated.S4_96.opposite_basis

theorem actualAffineValid_derives (identity : Identity Nat)
    (valid : identity.SatisfiedBy Generated.Catalogue.S4_96.table.semigroup.opposite) :
    Derives affineCore identity.lhs identity.rhs :=
  affineCore_basisFor_actual_catalogue.2 identity valid

theorem actualAffineValid_anchored (withB0 : Bool) (identity : Identity Nat)
    (valid : identity.SatisfiedBy Generated.Catalogue.S4_96.table.semigroup.opposite)
    (anchor : Word Nat) (before after : List Nat) :
    ListDerives withB0
      (anchor.toList ++ before ++ identity.lhs.toList ++ after ++ anchor.toList)
      (anchor.toList ++ before ++ identity.rhs.toList ++ after ++ anchor.toList) :=
  affineDerives_anchored withB0 (actualAffineValid_derives identity valid) anchor before after

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.affineCore_eq_reversed_library_basis
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.affineCore_basisFor_actual_catalogue
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.actualAffineValid_derives
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.actualAffineValid_anchored

end SemigroupBasis.CoRoots.Order6SporadicSection25
