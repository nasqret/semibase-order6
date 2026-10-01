import SemigroupBasis.Generated.S3_8
import SemigroupBasis.CoRoots.S5_240Completeness

namespace SemigroupBasis.CoRoots.Order6FactorPairS3_8S5_240

open SemigroupBasis

def w (head : Nat) (tail : List Nat) : Word Nat :=
  Word.mk head tail

/-- The recorded eight-law candidate.  It is retained so the square-free
counterexample can be stated against the exact failed claim. -/
def recordedBasis : List (Identity Nat) :=
  [ Identity.mk (w 0 [0])       (w 0 [0, 0]),
    Identity.mk (w 0 [0, 1, 0]) (w 0 [1, 0]),
    Identity.mk (w 0 [0, 1, 1]) (w 0 [1, 0, 1]),
    Identity.mk (w 0 [0, 1, 1]) (w 0 [1, 1, 0]),
    Identity.mk (w 0 [1, 0, 2]) (w 1 [0, 0, 2]),
    Identity.mk (w 0 [1, 1])    (w 1 [0, 1, 1]),
    Identity.mk (w 0 [1, 2, 0]) (w 1 [0, 2, 0]),
    Identity.mk (w 0 [1, 2, 2]) (w 1 [0, 2, 2]) ]

/-- The missing square-free prefix commutation `xyzt = yxzt`. -/
def prefixSwapLaw : Identity Nat :=
  Identity.mk (w 0 [1, 2, 3]) (w 1 [0, 2, 3])

/-- The corrected candidate for the `S3_8 x S5_240` intersection rooted at
`S6_2980`. -/
def basis : List (Identity Nat) :=
  recordedBasis ++ [prefixSwapLaw]

end SemigroupBasis.CoRoots.Order6FactorPairS3_8S5_240
