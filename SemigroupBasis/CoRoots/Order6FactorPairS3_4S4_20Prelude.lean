import SemigroupBasis.Generated.S3_4
import SemigroupBasis.Generated.S4_20

namespace SemigroupBasis.CoRoots.Order6FactorPairS3_4S4_20

open SemigroupBasis

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

/-- The exact accepted candidate basis for the `S3_4 x S4_20` identity-theory
intersection, whose first order-six realization is `S6_2604`. -/
def basis : List (Identity Nat) :=
  [ Identity.mk (w 0 [0, 0])       (w 0 [0, 0, 0]),
    Identity.mk (w 0 [0, 0, 1])    (w 0 [0, 1]),
    Identity.mk (w 0 [0, 1, 0])    (w 0 [1, 0]),
    Identity.mk (w 0 [0, 1, 1])    (w 0 [1, 0]),
    Identity.mk (w 0 [0, 1, 2, 1]) (w 0 [1, 2, 0]),
    Identity.mk (w 0 [0, 1, 2, 2]) (w 0 [1, 2, 0]),
    Identity.mk (w 0 [1, 0])       (w 1 [0, 1]),
    Identity.mk (w 0 [1, 0, 2, 2]) (w 0 [1, 2, 0]),
    Identity.mk (w 0 [1, 1])       (w 0 [1, 1, 1]),
    Identity.mk (w 0 [1, 1, 2])    (w 0 [1, 2]),
    Identity.mk (w 0 [1, 2, 0])    (w 0 [2, 1, 0]) ]

end SemigroupBasis.CoRoots.Order6FactorPairS3_4S4_20
