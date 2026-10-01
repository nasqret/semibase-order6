import SemigroupBasis.Generated.S3_8
import SemigroupBasis.CoRoots.S5_203Family

namespace SemigroupBasis.CoRoots.Order6FactorPairS3_8S5_203

open SemigroupBasis

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  Word.mk head tail

/-- The accepted candidate basis for the `S3_8 x S5_203` intersection rooted
at `S6_2676`. -/
def basis : List (Identity Nat) :=
  [ Identity.mk (w 0 [0, 0])       (w 0 [0, 0, 0]),
    Identity.mk (w 0 [0, 0, 1])    (w 0 [0, 1]),
    Identity.mk (w 0 [0, 1, 0])    (w 0 [1, 0]),
    Identity.mk (w 0 [0, 1, 1, 2]) (w 0 [1, 0, 1, 2]),
    Identity.mk (w 0 [0, 1, 1, 2]) (w 1 [0, 0, 1, 2]),
    Identity.mk (w 0 [0, 1, 2, 1]) (w 0 [1, 0, 2, 1]),
    Identity.mk (w 0 [0, 1, 2, 1]) (w 0 [1, 1, 2, 0]),
    Identity.mk (w 0 [0, 1, 2, 1]) (w 1 [0, 0, 2, 1]),
    Identity.mk (w 0 [1, 0])       (w 0 [1, 0, 0]),
    Identity.mk (w 0 [1, 0])       (w 1 [0, 0, 0]),
    Identity.mk (w 0 [1, 0, 1])    (w 0 [1, 1, 0]),
    Identity.mk (w 0 [1, 2, 0])    (w 0 [2, 1, 0]),
    Identity.mk (w 0 [1, 2, 2])    (w 1 [0, 2, 2]) ]

end SemigroupBasis.CoRoots.Order6FactorPairS3_8S5_203
