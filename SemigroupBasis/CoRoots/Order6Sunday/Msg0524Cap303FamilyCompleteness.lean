import SemigroupBasis.CoRoots.Order6Sunday.Msg0524Cap303FactorCompleteness
import SemigroupBasis.CoRoots.Order6Sunday.IntersectionFinite

/-! Both Cap303 representatives and their opposite orientations, using the
unchanged finite subdirect pairs and the approved three-law intersection. -/

namespace SemigroupBasis.CoRoots.Order6Sunday.Cap303Completion

open SemigroupBasis

theorem s63339_basis : BasisFor IntersectionFinite.SigmaCap303.S6_3339.table.semigroup B3 :=
  basisFor_pair IntersectionFinite.SigmaCap303.S6_3339.pair

theorem s63889_basis : BasisFor IntersectionFinite.SigmaCap303.S6_3889.table.semigroup B3 :=
  basisFor_pair IntersectionFinite.SigmaCap303.S6_3889.pair

theorem s63339_opposite_basis :
    BasisFor IntersectionFinite.SigmaCap303.S6_3339.table.semigroup.opposite
      (reversedBasis B3) := s63339_basis.oppositeReversed

theorem s63889_opposite_basis :
    BasisFor IntersectionFinite.SigmaCap303.S6_3889.table.semigroup.opposite
      (reversedBasis B3) := s63889_basis.oppositeReversed

example : BasisFor IntersectionFinite.SigmaCap303.S6_3339.table.semigroup
    ApprovedB3BridgesFinite.Cap303.approvedBasis := s63339_basis

example : BasisFor IntersectionFinite.SigmaCap303.S6_3889.table.semigroup
    ApprovedB3BridgesFinite.Cap303.approvedBasis := s63889_basis

example : BasisFor IntersectionFinite.SigmaCap303.S6_3339.table.semigroup.opposite
    (reversedBasis ApprovedB3BridgesFinite.Cap303.approvedBasis) := s63339_opposite_basis

example : BasisFor IntersectionFinite.SigmaCap303.S6_3889.table.semigroup.opposite
    (reversedBasis ApprovedB3BridgesFinite.Cap303.approvedBasis) := s63889_opposite_basis

end SemigroupBasis.CoRoots.Order6Sunday.Cap303Completion

#print axioms SemigroupBasis.CoRoots.Order6Sunday.Cap303Completion.s63339_basis
#print axioms SemigroupBasis.CoRoots.Order6Sunday.Cap303Completion.s63889_basis
#print axioms SemigroupBasis.CoRoots.Order6Sunday.Cap303Completion.s63339_opposite_basis
#print axioms SemigroupBasis.CoRoots.Order6Sunday.Cap303Completion.s63889_opposite_basis
