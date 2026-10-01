import SemigroupBasis.Generated.S3_18
import SemigroupBasis.Generated.S4_20
import SemigroupBasis.Order6.FactorPairJoin

namespace SemigroupBasis.CoRoots.Order6FactorPairS3_18S4_20

open SemigroupBasis

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  Word.mk head tail

/-- The corrected 14-law candidate basis for the `S3_18 x S4_20`
identity-theory intersection. The final two laws handle the squarefree
interior permutation and contextual period-three expansion that the first
twelve laws cannot initiate. -/
def basis : List (Identity Nat) :=
  [ Identity.mk (w 0 [0])          (w 0 [0, 0, 0, 0]),
    Identity.mk (w 0 [0, 0, 1, 0]) (w 1 [0, 1, 1, 1]),
    Identity.mk (w 0 [0, 0, 1, 1]) (w 1 [0, 0, 0, 1]),
    Identity.mk (w 0 [0, 1, 0])    (w 0 [1, 0, 0]),
    Identity.mk (w 0 [0, 1, 1])    (w 0 [1, 0, 1]),
    Identity.mk (w 0 [0, 1, 1])    (w 0 [1, 1, 0]),
    Identity.mk (w 0 [0, 1, 1])    (w 1 [0, 0, 1]),
    Identity.mk (w 0 [0, 1, 2])    (w 0 [1, 0, 2]),
    Identity.mk (w 0 [0, 1, 2, 1]) (w 0 [1, 1, 2, 0]),
    Identity.mk (w 0 [0, 1, 2, 1]) (w 1 [0, 0, 2, 1]),
    Identity.mk (w 0 [1, 2, 0])    (w 0 [2, 1, 0]),
    Identity.mk (w 0 [1, 2, 1])    (w 0 [2, 1, 1]),
    Identity.mk (w 0 [1, 2, 3])    (w 0 [2, 1, 3]),
    Identity.mk (w 0 [1, 2])       (w 0 [1, 1, 1, 1, 2]) ]

end SemigroupBasis.CoRoots.Order6FactorPairS3_18S4_20
