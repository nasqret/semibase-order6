import SemigroupBasis.CoRoots.S5_110Family
import SemigroupBasis.Generated.S3_6
import SemigroupBasis.Order6.FactorPairJoin

namespace SemigroupBasis.CoRoots.Order6FactorPairS3_6S5_110

open SemigroupBasis

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  Word.mk head tail

/-- The accepted four-law candidate basis for the `S3_6 x S5_110`
identity-theory intersection. -/
def basis : List (Identity Nat) :=
  [ Identity.mk (w 0 [0])       (w 0 [0, 0]),
    Identity.mk (w 0 [0, 1, 1]) (w 0 [1, 1, 0]),
    Identity.mk (w 0 [0, 1, 2]) (w 0 [1, 0, 2]),
    Identity.mk (w 0 [1, 0])    (w 1 [0, 0]) ]

end SemigroupBasis.CoRoots.Order6FactorPairS3_6S5_110
