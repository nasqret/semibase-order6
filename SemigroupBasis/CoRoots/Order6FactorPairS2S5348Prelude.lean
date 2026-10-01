import SemigroupBasis.Generated.S2_2
import SemigroupBasis.CoRoots.S5_348Family
import SemigroupBasis.Order6.FactorPairJoin

namespace SemigroupBasis.CoRoots.Order6FactorPairS2S5348

open SemigroupBasis

def w (head : Nat) (tail : List Nat) : Word Nat :=
  Word.mk head tail

/-- The accepted 13-law candidate basis for the `S2_2 x S5_348`
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
    Identity.mk (w 0 [0, 1, 2])    (w 0 [1, 0, 2]),
    Identity.mk (w 0 [0, 1, 2, 1]) (w 0 [1, 1, 2, 0]),
    Identity.mk (w 0 [0, 1, 2, 1]) (w 1 [0, 0, 2, 1]),
    Identity.mk (w 0 [0, 1, 2, 2]) (w 0 [1, 2, 2, 0]),
    Identity.mk (w 0 [1, 0])       (w 0 [1, 0, 0, 0]) ]

private def instantiateThreeWords
    (u v z : Word Nat) : Nat -> Word Nat
  | 0 => u
  | 1 => v
  | 2 => z
  | n + 3 => Word.singleton (n + 3)

private theorem basisTriplePrefixPairDeletion :
    Derives basis
      (w 0 [0, 0, 1, 0])
      (w 0 [1, 0]) :=
  Derives.fromBasis
    (e := Identity.mk (w 0 [0, 0, 1, 0]) (w 0 [1, 0])) <| by
      simp [basis]

private theorem basisFirstGapGather :
    Derives basis
      (w 0 [0, 1, 2])
      (w 0 [1, 0, 2]) :=
  Derives.fromBasis
    (e := Identity.mk (w 0 [0, 1, 2]) (w 0 [1, 0, 2])) <| by
      simp [basis]

/-- Delete two leading copies of `u` while retaining the first and final
copies. This is the parity-preserving replacement for the one-copy deletion
used by the `S5_348` normalizer. -/
theorem derivesTriplePrefixPairDeletion (u v : Word Nat) :
    Derives basis
      ((((u ++ u) ++ u) ++ v) ++ u)
      ((u ++ v) ++ u) := by
  have substituted :=
    Derives.subst basisTriplePrefixPairDeletion
      (instantiateThreeWords u v v)
  simpa [w, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- Gather the second copy of `u` beside its first occurrence. -/
theorem derivesFirstGapGather (u v z : Word Nat) :
    Derives basis
      (((u ++ u) ++ v) ++ z)
      (((u ++ v) ++ u) ++ z) := by
  have substituted :=
    Derives.subst basisFirstGapGather
      (instantiateThreeWords u v z)
  simpa [w, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- Delete two interior copies of a repeated word while preserving its first
and final copies:

`u v u z u t u = u v z t u`.

The derivation gathers the two interior copies next to the first one and then
uses `xxxyx = xyx`. It is valid for arbitrary nonempty substituted words, so
it is not a bounded-alphabet or bounded-length computation. -/
theorem derivesInteriorPairDeletion (u v z t : Word Nat) :
    Derives basis
      ((((((u ++ v) ++ u) ++ z) ++ u) ++ t) ++ u)
      ((((u ++ v) ++ z) ++ t) ++ u) := by
  have gatherFirst :
      Derives basis
        ((((((u ++ v) ++ u) ++ z) ++ u) ++ t) ++ u)
        ((((((u ++ u) ++ v) ++ z) ++ u) ++ t) ++ u) := by
    simpa [Word.append_assoc] using
      (derivesFirstGapGather u v (((z ++ u) ++ t) ++ u)).symm
  have gatherSecond :
      Derives basis
        ((((((u ++ u) ++ v) ++ z) ++ u) ++ t) ++ u)
        ((((((u ++ u) ++ u) ++ v) ++ z) ++ t) ++ u) := by
    simpa [Word.append_assoc] using
      (derivesFirstGapGather u ((u ++ v) ++ z) (t ++ u)).symm
  have contract :
      Derives basis
        ((((((u ++ u) ++ u) ++ v) ++ z) ++ t) ++ u)
        ((((u ++ v) ++ z) ++ t) ++ u) := by
    simpa [Word.append_assoc] using
      derivesTriplePrefixPairDeletion u ((v ++ z) ++ t)
  exact gatherFirst.trans (gatherSecond.trans contract)

end SemigroupBasis.CoRoots.Order6FactorPairS2S5348
