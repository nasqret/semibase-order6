import SemigroupBasis.CoRoots.Order6LeeZhang23_9B20Data
import SemigroupBasis.CoRoots.Order6LeeZhang23_9Completeness

/-!
# Lee--Zhang Proposition 23.9 B20 replacement root

The accepted twenty-law list contains the published four-law basis as its
literal left prefix.  Its remaining sixteen laws are sound in the same
product hull.  `BasisFor.replace` therefore transports the unrestricted B4
product theorem to the exact recorded B20 list.

This module stops at the shared product root.  Representative and opposite
endpoint projections belong to the downstream endpoint module.
-/

namespace SemigroupBasis.CoRoots.Order6LeeZhang23_9B20

open SemigroupBasis
open Order6LeeZhang23_9Moves
open Order6LeeZhang23_9B20Data
open Order6LeeZhang23_9Completeness

/-! ## Literal prefix transport -/

/-- Every published B4 axiom is an axiom of B20 through its literal left
prefix. -/
theorem publishedAxiomsDeriveB20
    (identity : Identity Nat) (member : identity ∈ B4Basis) :
    Derives b20Basis identity.lhs identity.rhs :=
  Derives.fromBasis (List.mem_append.mpr (Or.inl member))

/-- The independently checked B20 laws model the exact product hull. -/
theorem modelsB20 :
    Models
      SemigroupBasis.Order6Subdirect.Hull23_9_S2_4_S5_402op.P
      b20Basis :=
  models_prod

/-- The exact recorded twenty-law list is an unrestricted basis for the
shared product hull. -/
theorem b20ProductBasisFor :
    BasisFor
      SemigroupBasis.Order6Subdirect.Hull23_9_S2_4_S5_402op.P
      b20Basis :=
  publishedProductBasisFor.replace
    modelsB20 publishedAxiomsDeriveB20

end SemigroupBasis.CoRoots.Order6LeeZhang23_9B20
