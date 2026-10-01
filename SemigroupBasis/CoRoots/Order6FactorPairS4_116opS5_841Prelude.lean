import SemigroupBasis.Generated.BandEmbeddingTransfers
import SemigroupBasis.CoRoots.S5_841Completeness

namespace SemigroupBasis.CoRoots.Order6FactorPairS4_116opS5_841

open SemigroupBasis

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  Word.mk head tail

/-- The accepted candidate basis for the `S4_116^op x S5_841` intersection
rooted at `S6_13421`. -/
def basis : List (Identity Nat) :=
  [ Identity.mk (w 0 [0])          (w 0 [0, 0]),
    Identity.mk (w 0 [0, 1, 0])    (w 0 [1, 0]),
    Identity.mk (w 0 [1, 0])       (w 0 [1, 0, 0]),
    Identity.mk (w 0 [1, 0, 1])    (w 1 [0, 0, 1]),
    Identity.mk (w 0 [1, 0, 2, 0]) (w 0 [1, 2, 0]),
    Identity.mk (w 0 [1, 0, 2, 1]) (w 1 [0, 0, 2, 1]),
    Identity.mk (w 0 [1, 2, 0, 1]) (w 1 [0, 2, 0, 1]) ]

end SemigroupBasis.CoRoots.Order6FactorPairS4_116opS5_841
