import SemigroupBasis.CoRoots.Order6FactorPairS4_69S4_71EventSwaps

namespace SemigroupBasis.CoRoots.Order6FactorPairS4_69S4_71

open SemigroupBasis

/-- The smallest guarded quadratic/simple crossing cycle:

`x y z x y = y z x y x`.

The proof is the explicit four-step chain

`xyzxy -> xzxyy -> xyzyx -> yzyxx -> yzxyx`.

The four steps are reversed law 12, law 13, reversed law 14, and law 10.
The statement uses arbitrary nonempty word substitutions, so later list-level
normalizers may instantiate `x`, `y`, and `z` by whole guarded blocks. -/
theorem derivesQuadraticSimpleCrossingCycle
    (x y z : Word Nat) :
    Derives basis
      ((((x ++ y) ++ z) ++ x) ++ y)
      ((((y ++ z) ++ x) ++ y) ++ x) :=
  (derivesLaw12 x z y).symm.trans <|
    (derivesLaw13 x z y).trans <|
      (derivesLaw14 y z x).symm.trans <|
        derivesLaw10 y z x

/-- Singleton-letter list form of
`derivesQuadraticSimpleCrossingCycle`. -/
theorem listDerivesQuadraticSimpleCrossingCycle
    (x y z : Nat) :
    ListDerives
      [x, y, z, x, y]
      [y, z, x, y, x] := by
  exact S5_107.ListDerives.ofWord <| by
    simpa [Word.singleton, Word.append, List.append_assoc] using
      derivesQuadraticSimpleCrossingCycle
        (Word.singleton x)
        (Word.singleton y)
        (Word.singleton z)

/-- The crossing cycle remains derivable inside arbitrary list context. -/
theorem listDerivesQuadraticSimpleCrossingCycleContext
    (before after : List Nat) (x y z : Nat) :
    ListDerives
      (before ++ [x, y, z, x, y] ++ after)
      (before ++ [y, z, x, y, x] ++ after) :=
  (listDerivesQuadraticSimpleCrossingCycle x y z).context
    before after

end SemigroupBasis.CoRoots.Order6FactorPairS4_69S4_71
