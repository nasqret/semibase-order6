import SemigroupBasis.CoRoots.Order6L1RRank1.G43fb00e0b3bdd469.EndpointGlobalConnectivity
import SemigroupBasis.Subdirect

/-!
# Unrestricted completeness from G43 endpoint connectivity

The fresh endpoint route connects words with equal complete Layer-A
signatures through the exact contextual closure of the 52 frozen paths.
This file exposes only the compatibility surface required by downstream
factor variants and direct-subdirect endpoints.  It does not import the
retired G43 `Primitives`, `Normalization`, or `Completeness` modules, and it
does not pass through the retired candidate-witness canonicalizer.

Static source draft only: Helios kernel elaboration remains mandatory.
-/

namespace SemigroupBasis.CoRoots.Order6L1RRank1.G43fb00e0b3bdd469

open SemigroupBasis
open SemigroupBasis.CoRoots.Order6L1RRank1

/-- Equality of the selected-factor signature gives an exact derivation via
the common endpoint pivot. -/
theorem derivesOfSameJointSignature
    {left right : Word Nat}
    (same : SameJointSignature left right) :
    Derives basis left right :=
  contextualFrozenRTC_derives
    (contextualFrozenRTC_of_jointSignature_eq
      (jointSignature_eq_of_sameJointSignature same))

/-- The selected factor pair proves every valid identity from the displayed
seven-law basis through the fresh endpoint route. -/
theorem derivesOfFactorValid
    (identity : Identity Nat)
    (s4_116opValid :
      identity.SatisfiedBy FactorTables.s4_116op.semigroup)
    (s4_64Valid :
      identity.SatisfiedBy FactorTables.s4_64.semigroup) :
    Derives basis identity.lhs identity.rhs :=
  derivesOfSameJointSignature
    (sameJointSignature_of_factor_valid
      identity s4_116opValid s4_64Valid)

/-- Unrestricted intersection basis obtained directly from endpoint
connectivity, with no selector or candidate-witness dependency. -/
def intersectionBasis :
    IntersectionBasis
      FactorTables.s4_116op.semigroup
      FactorTables.s4_64.semigroup
      basis where
  leftModels := left_models
  rightModels := right_models
  complete := derivesOfFactorValid

end SemigroupBasis.CoRoots.Order6L1RRank1.G43fb00e0b3bdd469
