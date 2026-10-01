import SemigroupBasis.Generated.S2_4
import SemigroupBasis.CoRoots.S5_196Family
import SemigroupBasis.Order6.FactorPairJoin

namespace SemigroupBasis.CoRoots.Order6FactorPairS2_4S5_196Opposite

open SemigroupBasis

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  Word.mk head tail

/-- The accepted seven-law candidate basis for the
`S2_4 x S5_196^op` identity-theory intersection. -/
def basis : List (Identity Nat) :=
  [ Identity.mk (w 0 [0, 0])       (w 0 [0, 0, 0]),
    Identity.mk (w 0 [0, 0, 1])    (w 0 [0, 1]),
    Identity.mk (w 0 [0, 1])       (w 0 [0, 1, 1]),
    Identity.mk (w 0 [0, 1])       (w 0 [1, 0]),
    Identity.mk (w 0 [1, 1])       (w 0 [1, 1, 1]),
    Identity.mk (w 0 [1, 1, 2])    (w 0 [1, 2]),
    Identity.mk (w 0 [1, 2])       (w 0 [2, 1]) ]

end SemigroupBasis.CoRoots.Order6FactorPairS2_4S5_196Opposite
