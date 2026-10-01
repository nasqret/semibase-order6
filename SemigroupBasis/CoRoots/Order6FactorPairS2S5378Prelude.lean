import SemigroupBasis.Generated.S2_2
import SemigroupBasis.CoRoots.S5_378Family

namespace SemigroupBasis.CoRoots.Order6FactorPairS2S5378

open SemigroupBasis

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  Word.mk head tail

/-- The accepted 14-law candidate basis for the `S2_2 x S5_378`
identity-theory intersection. -/
def basis : List (Identity Nat) :=
  [ Identity.mk (w 0 [0])          (w 0 [0, 0, 0]),
    Identity.mk (w 0 [0, 0, 1, 0]) (w 0 [1, 0]),
    Identity.mk (w 0 [0, 0, 1, 1]) (w 1 [0, 0, 0, 1]),
    Identity.mk (w 0 [0, 1, 0])    (w 0 [1, 0, 0]),
    Identity.mk (w 0 [0, 1, 0, 0]) (w 0 [1, 0]),
    Identity.mk (w 0 [0, 1, 1])    (w 0 [1, 0, 1]),
    Identity.mk (w 0 [0, 1, 1])    (w 0 [1, 1, 0]),
    Identity.mk (w 0 [0, 1, 1])    (w 1 [0, 0, 1]),
    Identity.mk (w 0 [0, 1, 2, 1]) (w 0 [1, 0, 2, 1]),
    Identity.mk (w 0 [0, 1, 2, 1]) (w 0 [1, 1, 2, 0]),
    Identity.mk (w 0 [0, 1, 2, 1]) (w 0 [2, 0, 1, 1]),
    Identity.mk (w 0 [0, 1, 2, 1]) (w 1 [0, 0, 2, 1]),
    Identity.mk (w 0 [1, 0])       (w 0 [1, 0, 0, 0]),
    Identity.mk (w 0 [1, 2, 0])    (w 0 [2, 1, 0]) ]

end SemigroupBasis.CoRoots.Order6FactorPairS2S5378
