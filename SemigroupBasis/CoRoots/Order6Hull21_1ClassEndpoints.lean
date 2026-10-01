import SemigroupBasis.CoRoots.Order6Hull21_1GapRedistribution
import SemigroupBasis.Order6Subdirect.S6_8222Subdirect
import SemigroupBasis.Order6Subdirect.S6_8223Subdirect
import SemigroupBasis.Order6Subdirect.S6_8227Subdirect
import SemigroupBasis.Order6Subdirect.S6_8228Subdirect
import SemigroupBasis.Order6Subdirect.S6_10983Subdirect
import SemigroupBasis.Order6Subdirect.S6_10984Subdirect

/-!
# Concrete order-six endpoints for Hull 21.1

The six catalogue classes below have the same identity theories as one of the
two Hull 21.1 products.  Their existing subdirect certificates reduce each
class theorem to the corresponding derivational obligation, now discharged
unconditionally by `Order6Hull21_1GapRedistribution`.
-/

namespace SemigroupBasis
namespace CoRoots
namespace Order6Hull21_1ClassEndpoints

open Order6Hull21_1GapRedistribution

theorem s6_8222_basis :
    BasisFor
      SemigroupBasis.Order6Subdirect.S6_8222.table.semigroup
      SemigroupBasis.Order6Subdirect.Hull21_1_S5_831_S3_8.publishedBasis :=
  SemigroupBasis.Order6Subdirect.S6_8222.representative_basis_of_obligation
    h831DerivationalObligation

theorem s6_8227_basis :
    BasisFor
      SemigroupBasis.Order6Subdirect.S6_8227.table.semigroup
      SemigroupBasis.Order6Subdirect.Hull21_1_S5_831_S3_8.publishedBasis :=
  SemigroupBasis.Order6Subdirect.S6_8227.representative_basis_of_obligation
    h831DerivationalObligation

theorem s6_10984_basis :
    BasisFor
      SemigroupBasis.Order6Subdirect.S6_10984.table.semigroup
      SemigroupBasis.Order6Subdirect.Hull21_1_S5_831_S3_8.publishedBasis :=
  SemigroupBasis.Order6Subdirect.S6_10984.representative_basis_of_obligation
    h831DerivationalObligation

theorem s6_8223_basis :
    BasisFor
      SemigroupBasis.Order6Subdirect.S6_8223.table.semigroup
      SemigroupBasis.Order6Subdirect.Hull21_1_S5_832_S3_8.publishedBasis :=
  SemigroupBasis.Order6Subdirect.S6_8223.representative_basis_of_obligation
    h832DerivationalObligation

theorem s6_8228_basis :
    BasisFor
      SemigroupBasis.Order6Subdirect.S6_8228.table.semigroup
      SemigroupBasis.Order6Subdirect.Hull21_1_S5_832_S3_8.publishedBasis :=
  SemigroupBasis.Order6Subdirect.S6_8228.representative_basis_of_obligation
    h832DerivationalObligation

theorem s6_10983_basis :
    BasisFor
      SemigroupBasis.Order6Subdirect.S6_10983.table.semigroup
      SemigroupBasis.Order6Subdirect.Hull21_1_S5_832_S3_8.publishedBasis :=
  SemigroupBasis.Order6Subdirect.S6_10983.representative_basis_of_obligation
    h832DerivationalObligation

#print axioms s6_8222_basis
#print axioms s6_8227_basis
#print axioms s6_10984_basis
#print axioms s6_8223_basis
#print axioms s6_8228_basis
#print axioms s6_10983_basis

end Order6Hull21_1ClassEndpoints
end CoRoots
end SemigroupBasis
