import SemigroupBasis.CoRoots.Order6SporadicSection15BetaToScaffold

namespace SemigroupBasis.CoRoots.Order6SporadicSection15

namespace BetaNormalization

/-- Proposition 15.1, beta branch: every beta word derives to the executable
canonical representative determined by its multiplicity and simple-block
data. -/
theorem listDerivesCanonical_of_branch_beta
    (letters : List Nat)
    (branch : CanonicalData.canonicalBranch letters = .beta) :
    ListDerives letters (CanonicalData.betaCanonicalList letters) :=
  (BetaScaffoldMoves.listDerivesToScaffold_of_branch_beta letters branch).trans
    (BetaScaffoldMoves.listDerivesScaffoldToCanonical letters branch)

end BetaNormalization

end SemigroupBasis.CoRoots.Order6SporadicSection15
