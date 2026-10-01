import SemigroupBasis.CoRoots.Order6LeeZhang23_9B20
import SemigroupBasis.Order6Subdirect.S6_8448Subdirect
import SemigroupBasis.Order6Subdirect.S6_11262Subdirect

/-!
# Lee--Zhang Proposition 23.9 order-six endpoints

The exact B20 product root transfers directly to the two catalogue
representatives through their existing subdirect equivalences.  Applying
`BasisFor.oppositeReversed` then exposes the corresponding opposite
semigroups at the literal reversed B20 list.
-/

namespace SemigroupBasis.CoRoots.Order6LeeZhang23_9Endpoints

open SemigroupBasis
open Order6LeeZhang23_9B20Data
open Order6LeeZhang23_9B20

/-- The accepted B20 list is a basis for the direct representative
`S6_8448`. -/
theorem s6_8448_basis :
    BasisFor
      SemigroupBasis.Order6Subdirect.S6_8448.table.semigroup
      b20Basis :=
  (SemigroupBasis.Order6Subdirect.S6_8448.basisFor_iff
    b20Basis).mpr b20ProductBasisFor

/-- The accepted B20 list is a basis for the direct representative
`S6_11262`. -/
theorem s6_11262_basis :
    BasisFor
      SemigroupBasis.Order6Subdirect.S6_11262.table.semigroup
      b20Basis :=
  (SemigroupBasis.Order6Subdirect.S6_11262.basisFor_iff
    b20Basis).mpr b20ProductBasisFor

/-- The literal reversed B20 list is a basis for the opposite of
`S6_8448`. -/
theorem s6_8448_opposite_basis :
    BasisFor
      SemigroupBasis.Order6Subdirect.S6_8448.table.semigroup.opposite
      (reversedBasis b20Basis) :=
  s6_8448_basis.oppositeReversed

/-- The literal reversed B20 list is a basis for the opposite of
`S6_11262`. -/
theorem s6_11262_opposite_basis :
    BasisFor
      SemigroupBasis.Order6Subdirect.S6_11262.table.semigroup.opposite
      (reversedBasis b20Basis) :=
  s6_11262_basis.oppositeReversed

end SemigroupBasis.CoRoots.Order6LeeZhang23_9Endpoints
