import SemigroupBasis.CoRoots.S5_791EndpointCap

namespace SemigroupBasis.CoRoots.S5_791

open SemigroupBasis

private def cw (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

private def instantiateThreeWords
    (u v z : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => z
  | n + 3 => Word.singleton (n + 3)

private def instantiateFiveWords
    (a b c d e : Word Nat) : Nat → Word Nat
  | 0 => a
  | 1 => b
  | 2 => c
  | 3 => d
  | 4 => e
  | n + 5 => Word.singleton (n + 5)

private theorem basisPowerStep :
    Derives basis powerLaw.lhs powerLaw.rhs :=
  Derives.fromBasis (e := powerLaw) (by simp [basis])

private theorem basisLeftDuplicationStep :
    Derives basis leftDuplicationLaw.lhs leftDuplicationLaw.rhs :=
  Derives.fromBasis (e := leftDuplicationLaw) (by simp [basis])

private theorem basisRightDuplicationStep :
    Derives basis rightDuplicationLaw.lhs rightDuplicationLaw.rhs :=
  Derives.fromBasis (e := rightDuplicationLaw) (by simp [basis])

private theorem basisAlternatingStep :
    Derives basis alternatingLaw.lhs alternatingLaw.rhs :=
  Derives.fromBasis (e := alternatingLaw) (by simp [basis])

private theorem basisRegularStep :
    Derives basis regularBandLaw.lhs regularBandLaw.rhs :=
  Derives.fromBasis (e := regularBandLaw) (by simp [basis])

/-- Put one substituted basis step inside a concrete list context. -/
private theorem derivesConcreteContext
    {source target patternLeft patternRight : Word Nat}
    (patternDerivation :
      Derives basis patternLeft patternRight)
    (u v z : Word Nat) (ctxPrefix ctxSuffix : List Nat)
    (sourceShape :
      source.toList =
        ctxPrefix ++
          (patternLeft.bind (instantiateThreeWords u v z)).toList ++
          ctxSuffix)
    (targetShape :
      target.toList =
        ctxPrefix ++
          (patternRight.bind (instantiateThreeWords u v z)).toList ++
          ctxSuffix) :
    Derives basis source target := by
  have contextual :
      S5_107.ListDerives basis
        (ctxPrefix ++
          (patternLeft.bind (instantiateThreeWords u v z)).toList ++
          ctxSuffix)
        (ctxPrefix ++
          (patternRight.bind (instantiateThreeWords u v z)).toList ++
          ctxSuffix) :=
    (S5_107.ListDerives.ofWord
      (Derives.subst patternDerivation
        (instantiateThreeWords u v z))).context ctxPrefix ctxSuffix
  rw [← sourceShape, ← targetShape] at contextual
  cases source with
  | mk sourceHead sourceTail =>
      cases target with
      | mk targetHead targetTail =>
          exact S5_107.ListDerives.toWord contextual

theorem derivesMiddleDoubling :
    Derives basis (cw 0 [1, 0]) (cw 0 [1, 1, 0]) := by
  have stepOne :
      Derives basis (cw 0 [1, 0]) (cw 0 [1, 0, 0]) :=
    derivesConcreteContext basisRightDuplicationStep
      (cw 0 []) (cw 1 []) (cw 2 [])
      [] [] (by decide) (by decide)
  have stepTwo :
      Derives basis (cw 0 [1, 0, 0]) (cw 0 [1, 0, 1, 0]) :=
    derivesConcreteContext basisAlternatingStep
      (cw 0 []) (cw 1 []) (cw 2 [])
      [] [0] (by decide) (by decide)
  have stepThree :
      Derives basis (cw 0 [1, 0, 1, 0]) (cw 0 [1, 1, 0]) :=
    derivesConcreteContext (Derives.symm basisRegularStep)
      (cw 0 []) (cw 1 []) (cw 1 [])
      [] [] (by decide) (by decide)
  exact stepOne.trans <| stepTwo.trans <| stepThree

theorem derivesShortCrossingAbsorption :
    Derives basis (cw 0 [1, 0, 2, 1]) (cw 0 [1, 2, 0]) := by
  have stepOne :
      Derives basis (cw 0 [1, 0, 2, 1]) (cw 0 [1, 0, 2, 1, 0, 2]) :=
    derivesConcreteContext basisAlternatingStep
      (cw 1 []) (cw 0 [2]) (cw 2 [])
      [0] [] (by decide) (by decide)
  have stepTwo :
      Derives basis (cw 0 [1, 0, 2, 1, 0, 2]) (cw 0 [1, 0, 2, 0, 1, 0, 2]) :=
    derivesConcreteContext basisRegularStep
      (cw 0 []) (cw 1 [0, 2]) (cw 1 [])
      [] [2] (by decide) (by decide)
  have stepThree :
      Derives basis (cw 0 [1, 0, 2, 0, 1, 0, 2]) (cw 0 [1, 0, 2, 0]) :=
    derivesConcreteContext (Derives.symm basisAlternatingStep)
      (cw 0 []) (cw 1 [0, 2]) (cw 2 [])
      [] [] (by decide) (by decide)
  have stepFour :
      Derives basis (cw 0 [1, 0, 2, 0]) (cw 0 [1, 2, 0]) :=
    derivesConcreteContext (Derives.symm basisRegularStep)
      (cw 0 []) (cw 1 []) (cw 2 [])
      [] [] (by decide) (by decide)
  exact stepOne.trans <| stepTwo.trans <| stepThree.trans <| stepFour

theorem derivesCrossingWithoutRightFiller :
    Derives basis (cw 0 [1, 2, 0, 1]) (cw 0 [1, 2, 0]) := by
  have stepOne :
      Derives basis (cw 0 [1, 2, 0, 1]) (cw 0 [1, 2, 0, 1, 2]) :=
    derivesConcreteContext basisAlternatingStep
      (cw 0 [1]) (cw 2 []) (cw 2 [])
      [] [] (by decide) (by decide)
  have stepTwo :
      Derives basis (cw 0 [1, 2, 0, 1, 2]) (cw 0 [1, 2, 0]) :=
    derivesConcreteContext (Derives.symm basisAlternatingStep)
      (cw 0 []) (cw 1 [2]) (cw 2 [])
      [] [] (by decide) (by decide)
  exact stepOne.trans <| stepTwo

theorem derivesAdjacentCrossingAbsorption :
    Derives basis (cw 0 [1, 2, 0, 2]) (cw 0 [1, 2, 0]) := by
  have stepOne :
      Derives basis (cw 0 [1, 2, 0, 2]) (cw 0 [1, 2, 0, 1, 2, 2]) :=
    derivesConcreteContext basisAlternatingStep
      (cw 0 []) (cw 1 [2]) (cw 2 [])
      [] [2] (by decide) (by decide)
  have stepTwo :
      Derives basis (cw 0 [1, 2, 0, 1, 2, 2]) (cw 0 [1, 2, 0, 1, 2]) :=
    derivesConcreteContext (Derives.symm basisRightDuplicationStep)
      (cw 2 []) (cw 0 [1]) (cw 2 [])
      [0, 1] [] (by decide) (by decide)
  have stepThree :
      Derives basis (cw 0 [1, 2, 0, 1, 2]) (cw 0 [1, 2, 0]) :=
    derivesConcreteContext (Derives.symm basisAlternatingStep)
      (cw 0 []) (cw 1 [2]) (cw 2 [])
      [] [] (by decide) (by decide)
  exact stepOne.trans <| stepTwo.trans <| stepThree

theorem derivesNestedRepeatDeletion :
    Derives basis (cw 0 [1, 2, 3, 2, 4, 0]) (cw 0 [1, 2, 3, 4, 0]) := by
  have stepOne :
      Derives basis (cw 0 [1, 2, 3, 2, 4, 0]) (cw 0 [1, 2, 3, 2, 3, 4, 0]) :=
    derivesConcreteContext basisAlternatingStep
      (cw 2 []) (cw 3 []) (cw 2 [])
      [0, 1] [4, 0] (by decide) (by decide)
  have stepTwo :
      Derives basis (cw 0 [1, 2, 3, 2, 3, 4, 0]) (cw 0 [1, 0, 2, 3, 2, 3, 4, 0]) :=
    derivesConcreteContext basisRegularStep
      (cw 0 []) (cw 1 []) (cw 2 [3, 2, 3, 4])
      [] [] (by decide) (by decide)
  have stepThree :
      Derives basis (cw 0 [1, 0, 2, 3, 2, 3, 4, 0]) (cw 0 [1, 0, 2, 3, 0, 2, 3, 4, 0]) :=
    derivesConcreteContext basisRegularStep
      (cw 0 []) (cw 1 [0, 2, 3]) (cw 2 [3, 4])
      [] [] (by decide) (by decide)
  have stepFour :
      Derives basis (cw 0 [1, 0, 2, 3, 0, 2, 3, 4, 0]) (cw 0 [1, 0, 2, 3, 0, 4, 0]) :=
    derivesConcreteContext (Derives.symm basisAlternatingStep)
      (cw 0 []) (cw 2 [3]) (cw 2 [])
      [0, 1] [4, 0] (by decide) (by decide)
  have stepFive :
      Derives basis (cw 0 [1, 0, 2, 3, 0, 4, 0]) (cw 0 [1, 2, 3, 0, 4, 0]) :=
    derivesConcreteContext (Derives.symm basisRegularStep)
      (cw 0 []) (cw 1 []) (cw 2 [3])
      [] [4, 0] (by decide) (by decide)
  have stepSix :
      Derives basis (cw 0 [1, 2, 3, 0, 4, 0]) (cw 0 [1, 2, 3, 4, 0]) :=
    derivesConcreteContext (Derives.symm basisRegularStep)
      (cw 0 []) (cw 1 [2, 3]) (cw 4 [])
      [] [] (by decide) (by decide)
  exact stepOne.trans <| stepTwo.trans <| stepThree.trans <| stepFour.trans <| stepFive.trans <| stepSix

theorem derivesGeneralCrossingAbsorption :
    Derives basis (cw 0 [1, 2, 3, 0, 4, 2]) (cw 0 [1, 2, 3, 4, 0]) := by
  have stepOne :
      Derives basis (cw 0 [1, 2, 3, 0, 4, 2]) (cw 0 [1, 2, 3, 0, 4, 2, 3, 0, 4]) :=
    derivesConcreteContext basisAlternatingStep
      (cw 2 []) (cw 3 [0, 4]) (cw 2 [])
      [0, 1] [] (by decide) (by decide)
  have stepTwo :
      Derives basis (cw 0 [1, 2, 3, 0, 4, 2, 3, 0, 4]) (cw 0 [1, 2, 3, 0, 4, 0, 2, 3, 0, 4]) :=
    derivesConcreteContext basisRegularStep
      (cw 0 []) (cw 1 [2, 3, 0, 4]) (cw 2 [3])
      [] [4] (by decide) (by decide)
  have stepThree :
      Derives basis (cw 0 [1, 2, 3, 0, 4, 0, 2, 3, 0, 4]) (cw 0 [1, 2, 3, 4, 0, 2, 3, 0, 4]) :=
    derivesConcreteContext (Derives.symm basisRegularStep)
      (cw 0 []) (cw 1 [2, 3]) (cw 4 [])
      [] [2, 3, 0, 4] (by decide) (by decide)
  have stepFour :
      Derives basis (cw 0 [1, 2, 3, 4, 0, 2, 3, 0, 4]) (cw 0 [1, 2, 3, 4, 0, 2, 3, 4, 0, 4]) :=
    derivesConcreteContext basisRegularStep
      (cw 4 []) (cw 0 [2, 3]) (cw 0 [])
      [0, 1, 2, 3] [] (by decide) (by decide)
  have stepFive :
      Derives basis (cw 0 [1, 2, 3, 4, 0, 2, 3, 4, 0, 4]) (cw 0 [1, 2, 3, 4, 0, 2, 3, 4]) :=
    derivesConcreteContext (Derives.symm basisAlternatingStep)
      (cw 2 [3]) (cw 4 [0]) (cw 2 [])
      [0, 1] [4] (by decide) (by decide)
  have stepSix :
      Derives basis (cw 0 [1, 2, 3, 4, 0, 2, 3, 4]) (cw 0 [1, 0, 2, 3, 4, 0, 2, 3, 4]) :=
    derivesConcreteContext basisRegularStep
      (cw 0 []) (cw 1 []) (cw 2 [3, 4])
      [] [2, 3, 4] (by decide) (by decide)
  have stepSeven :
      Derives basis (cw 0 [1, 0, 2, 3, 4, 0, 2, 3, 4]) (cw 0 [1, 0, 2, 3, 4, 0]) :=
    derivesConcreteContext (Derives.symm basisAlternatingStep)
      (cw 0 []) (cw 2 [3, 4]) (cw 2 [])
      [0, 1] [] (by decide) (by decide)
  have stepEight :
      Derives basis (cw 0 [1, 0, 2, 3, 4, 0]) (cw 0 [1, 2, 3, 4, 0]) :=
    derivesConcreteContext (Derives.symm basisRegularStep)
      (cw 0 []) (cw 1 []) (cw 2 [3, 4])
      [] [] (by decide) (by decide)
  exact stepOne.trans <| stepTwo.trans <| stepThree.trans <| stepFour.trans <| stepFive.trans <| stepSix.trans <| stepSeven.trans <| stepEight

private theorem derivesNestedLeftEmpty :
    Derives basis (cw 0 [1, 2, 1, 3, 0]) (cw 0 [1, 2, 3, 0]) := by
  have stepOne :
      Derives basis (cw 0 [1, 2, 1, 3, 0]) (cw 0 [1, 2, 0, 1, 3, 0]) :=
    derivesConcreteContext basisRegularStep
      (cw 0 []) (cw 1 [2]) (cw 1 [3])
      [] [] (by decide) (by decide)
  have stepTwo :
      Derives basis (cw 0 [1, 2, 0, 1, 3, 0]) (cw 0 [1, 2, 0, 1, 2, 3, 0]) :=
    derivesConcreteContext basisAlternatingStep
      (cw 0 [1]) (cw 2 []) (cw 2 [])
      [] [3, 0] (by decide) (by decide)
  have stepThree :
      Derives basis (cw 0 [1, 2, 0, 1, 2, 3, 0]) (cw 0 [1, 2, 0, 3, 0]) :=
    derivesConcreteContext (Derives.symm basisAlternatingStep)
      (cw 0 []) (cw 1 [2]) (cw 2 [])
      [] [3, 0] (by decide) (by decide)
  have stepFour :
      Derives basis (cw 0 [1, 2, 0, 3, 0]) (cw 0 [1, 2, 3, 0]) :=
    derivesConcreteContext (Derives.symm basisRegularStep)
      (cw 0 []) (cw 1 [2]) (cw 3 [])
      [] [] (by decide) (by decide)
  exact stepOne.trans <| stepTwo.trans <| stepThree.trans <| stepFour

private theorem derivesNestedMiddleEmpty :
    Derives basis (cw 0 [1, 2, 2, 3, 0]) (cw 0 [1, 2, 3, 0]) := by
  have stepOne :
      Derives basis (cw 0 [1, 2, 2, 3, 0]) (cw 0 [1, 2, 0, 2, 3, 0]) :=
    derivesConcreteContext basisRegularStep
      (cw 0 []) (cw 1 [2]) (cw 2 [3])
      [] [] (by decide) (by decide)
  have stepTwo :
      Derives basis (cw 0 [1, 2, 0, 2, 3, 0]) (cw 0 [1, 0, 2, 0, 2, 3, 0]) :=
    derivesConcreteContext basisRegularStep
      (cw 0 []) (cw 1 []) (cw 2 [])
      [] [2, 3, 0] (by decide) (by decide)
  have stepThree :
      Derives basis (cw 0 [1, 0, 2, 0, 2, 3, 0]) (cw 0 [1, 0, 2, 0, 3, 0]) :=
    derivesConcreteContext (Derives.symm basisAlternatingStep)
      (cw 0 []) (cw 2 []) (cw 2 [])
      [0, 1] [3, 0] (by decide) (by decide)
  have stepFour :
      Derives basis (cw 0 [1, 0, 2, 0, 3, 0]) (cw 0 [1, 0, 2, 3, 0]) :=
    derivesConcreteContext (Derives.symm basisRegularStep)
      (cw 0 []) (cw 1 [0, 2]) (cw 3 [])
      [] [] (by decide) (by decide)
  have stepFive :
      Derives basis (cw 0 [1, 0, 2, 3, 0]) (cw 0 [1, 2, 3, 0]) :=
    derivesConcreteContext (Derives.symm basisRegularStep)
      (cw 0 []) (cw 1 []) (cw 2 [3])
      [] [] (by decide) (by decide)
  exact stepOne.trans <| stepTwo.trans <| stepThree.trans <| stepFour.trans <| stepFive

private theorem derivesNestedRightEmpty :
    Derives basis (cw 0 [1, 2, 3, 2, 0]) (cw 0 [1, 2, 3, 0]) := by
  have stepOne :
      Derives basis (cw 0 [1, 2, 3, 2, 0]) (cw 0 [1, 0, 2, 3, 2, 0]) :=
    derivesConcreteContext basisRegularStep
      (cw 0 []) (cw 1 []) (cw 2 [3, 2])
      [] [] (by decide) (by decide)
  have stepTwo :
      Derives basis (cw 0 [1, 0, 2, 3, 2, 0]) (cw 0 [1, 0, 2, 3, 0, 2, 0]) :=
    derivesConcreteContext basisRegularStep
      (cw 0 []) (cw 1 [0, 2, 3]) (cw 2 [])
      [] [] (by decide) (by decide)
  have stepThree :
      Derives basis (cw 0 [1, 0, 2, 3, 0, 2, 0]) (cw 0 [1, 0, 2, 3, 0, 2, 3, 0]) :=
    derivesConcreteContext basisAlternatingStep
      (cw 0 [2]) (cw 3 []) (cw 2 [])
      [0, 1] [0] (by decide) (by decide)
  have stepFour :
      Derives basis (cw 0 [1, 0, 2, 3, 0, 2, 3, 0]) (cw 0 [1, 0, 2, 3, 0, 0]) :=
    derivesConcreteContext (Derives.symm basisAlternatingStep)
      (cw 0 []) (cw 2 [3]) (cw 2 [])
      [0, 1] [0] (by decide) (by decide)
  have stepFive :
      Derives basis (cw 0 [1, 0, 2, 3, 0, 0]) (cw 0 [1, 0, 2, 3, 0]) :=
    derivesConcreteContext (Derives.symm basisRightDuplicationStep)
      (cw 0 []) (cw 1 [0, 2, 3]) (cw 2 [])
      [] [] (by decide) (by decide)
  have stepSix :
      Derives basis (cw 0 [1, 0, 2, 3, 0]) (cw 0 [1, 2, 3, 0]) :=
    derivesConcreteContext (Derives.symm basisRegularStep)
      (cw 0 []) (cw 1 []) (cw 2 [3])
      [] [] (by decide) (by decide)
  exact stepOne.trans <| stepTwo.trans <| stepThree.trans <| stepFour.trans <| stepFive.trans <| stepSix

private theorem derivesNestedLeftMiddleEmpty :
    Derives basis (cw 0 [1, 1, 2, 0]) (cw 0 [1, 2, 0]) := by
  have stepOne :
      Derives basis (cw 0 [1, 1, 2, 0]) (cw 0 [1, 0, 1, 2, 0]) :=
    derivesConcreteContext basisRegularStep
      (cw 0 []) (cw 1 []) (cw 1 [2])
      [] [] (by decide) (by decide)
  have stepTwo :
      Derives basis (cw 0 [1, 0, 1, 2, 0]) (cw 0 [1, 0, 2, 0]) :=
    derivesConcreteContext (Derives.symm basisAlternatingStep)
      (cw 0 []) (cw 1 []) (cw 2 [])
      [] [2, 0] (by decide) (by decide)
  have stepThree :
      Derives basis (cw 0 [1, 0, 2, 0]) (cw 0 [1, 2, 0]) :=
    derivesConcreteContext (Derives.symm basisRegularStep)
      (cw 0 []) (cw 1 []) (cw 2 [])
      [] [] (by decide) (by decide)
  exact stepOne.trans <| stepTwo.trans <| stepThree

private theorem derivesNestedLeftRightEmpty :
    Derives basis (cw 0 [1, 2, 1, 0]) (cw 0 [1, 2, 0]) := by
  have stepOne :
      Derives basis (cw 0 [1, 2, 1, 0]) (cw 0 [1, 2, 1, 2, 0]) :=
    derivesConcreteContext basisAlternatingStep
      (cw 1 []) (cw 2 []) (cw 2 [])
      [0] [0] (by decide) (by decide)
  have stepTwo :
      Derives basis (cw 0 [1, 2, 1, 2, 0]) (cw 0 [1, 2, 0, 1, 2, 0]) :=
    derivesConcreteContext basisRegularStep
      (cw 0 []) (cw 1 [2]) (cw 1 [2])
      [] [] (by decide) (by decide)
  have stepThree :
      Derives basis (cw 0 [1, 2, 0, 1, 2, 0]) (cw 0 [1, 2, 0, 1, 2]) :=
    derivesConcreteContext (Derives.symm basisAlternatingStep)
      (cw 1 [2]) (cw 0 []) (cw 2 [])
      [0] [] (by decide) (by decide)
  have stepFour :
      Derives basis (cw 0 [1, 2, 0, 1, 2]) (cw 0 [1, 2, 0]) :=
    derivesConcreteContext (Derives.symm basisAlternatingStep)
      (cw 0 []) (cw 1 [2]) (cw 2 [])
      [] [] (by decide) (by decide)
  exact stepOne.trans <| stepTwo.trans <| stepThree.trans <| stepFour

private theorem derivesNestedMiddleRightEmpty :
    Derives basis (cw 0 [1, 2, 2, 0]) (cw 0 [1, 2, 0]) := by
  have stepOne :
      Derives basis (cw 0 [1, 2, 2, 0]) (cw 0 [1, 2, 0, 2, 0]) :=
    derivesConcreteContext basisRegularStep
      (cw 0 []) (cw 1 [2]) (cw 2 [])
      [] [] (by decide) (by decide)
  have stepTwo :
      Derives basis (cw 0 [1, 2, 0, 2, 0]) (cw 0 [1, 0, 2, 0, 2, 0]) :=
    derivesConcreteContext basisRegularStep
      (cw 0 []) (cw 1 []) (cw 2 [])
      [] [2, 0] (by decide) (by decide)
  have stepThree :
      Derives basis (cw 0 [1, 0, 2, 0, 2, 0]) (cw 0 [1, 0, 2, 0, 0]) :=
    derivesConcreteContext (Derives.symm basisAlternatingStep)
      (cw 0 []) (cw 2 []) (cw 2 [])
      [0, 1] [0] (by decide) (by decide)
  have stepFour :
      Derives basis (cw 0 [1, 0, 2, 0, 0]) (cw 0 [1, 2, 0, 0]) :=
    derivesConcreteContext (Derives.symm basisRegularStep)
      (cw 0 []) (cw 1 []) (cw 2 [])
      [] [0] (by decide) (by decide)
  have stepFive :
      Derives basis (cw 0 [1, 2, 0, 0]) (cw 0 [1, 2, 0]) :=
    derivesConcreteContext (Derives.symm basisRightDuplicationStep)
      (cw 0 []) (cw 1 [2]) (cw 2 [])
      [] [] (by decide) (by decide)
  exact stepOne.trans <| stepTwo.trans <| stepThree.trans <| stepFour.trans <| stepFive

private theorem derivesNestedAllEmpty :
    Derives basis (cw 0 [1, 1, 0]) (cw 0 [1, 0]) := by
  have stepOne :
      Derives basis (cw 0 [1, 1, 0]) (cw 0 [1, 0, 1, 0]) :=
    derivesConcreteContext basisRegularStep
      (cw 0 []) (cw 1 []) (cw 1 [])
      [] [] (by decide) (by decide)
  have stepTwo :
      Derives basis (cw 0 [1, 0, 1, 0]) (cw 0 [1, 0, 1]) :=
    derivesConcreteContext (Derives.symm basisAlternatingStep)
      (cw 1 []) (cw 0 []) (cw 2 [])
      [0] [] (by decide) (by decide)
  have stepThree :
      Derives basis (cw 0 [1, 0, 1]) (cw 0 [1, 0]) :=
    derivesConcreteContext (Derives.symm basisAlternatingStep)
      (cw 0 []) (cw 1 []) (cw 2 [])
      [] [] (by decide) (by decide)
  exact stepOne.trans <| stepTwo.trans <| stepThree

private theorem derivesCrossingLeftEmpty :
    Derives basis (cw 0 [1, 2, 0, 3, 1]) (cw 0 [1, 2, 3, 0]) := by
  have stepOne :
      Derives basis (cw 0 [1, 2, 0, 3, 1]) (cw 0 [1, 2, 0, 3, 1, 2, 0, 3]) :=
    derivesConcreteContext basisAlternatingStep
      (cw 1 []) (cw 2 [0, 3]) (cw 2 [])
      [0] [] (by decide) (by decide)
  have stepTwo :
      Derives basis (cw 0 [1, 2, 0, 3, 1, 2, 0, 3]) (cw 0 [1, 2, 0, 3, 1, 2, 0]) :=
    derivesConcreteContext (Derives.symm basisAlternatingStep)
      (cw 1 [2, 0]) (cw 3 []) (cw 2 [])
      [0] [] (by decide) (by decide)
  have stepThree :
      Derives basis (cw 0 [1, 2, 0, 3, 1, 2, 0]) (cw 0 [1, 2, 0, 3, 0, 1, 2, 0]) :=
    derivesConcreteContext basisRegularStep
      (cw 0 []) (cw 1 [2, 0, 3]) (cw 1 [2])
      [] [] (by decide) (by decide)
  have stepFour :
      Derives basis (cw 0 [1, 2, 0, 3, 0, 1, 2, 0]) (cw 0 [1, 2, 3, 0, 1, 2, 0]) :=
    derivesConcreteContext (Derives.symm basisRegularStep)
      (cw 0 []) (cw 1 [2]) (cw 3 [])
      [] [1, 2, 0] (by decide) (by decide)
  have stepFive :
      Derives basis (cw 0 [1, 2, 3, 0, 1, 2, 0]) (cw 0 [1, 2, 3, 0, 1, 2, 3, 0]) :=
    derivesConcreteContext basisAlternatingStep
      (cw 0 [1, 2]) (cw 3 []) (cw 2 [])
      [] [0] (by decide) (by decide)
  have stepSix :
      Derives basis (cw 0 [1, 2, 3, 0, 1, 2, 3, 0]) (cw 0 [1, 2, 3, 0, 1, 2, 3]) :=
    derivesConcreteContext (Derives.symm basisAlternatingStep)
      (cw 1 [2, 3]) (cw 0 []) (cw 2 [])
      [0] [] (by decide) (by decide)
  have stepSeven :
      Derives basis (cw 0 [1, 2, 3, 0, 1, 2, 3]) (cw 0 [1, 2, 3, 0]) :=
    derivesConcreteContext (Derives.symm basisAlternatingStep)
      (cw 0 []) (cw 1 [2, 3]) (cw 2 [])
      [] [] (by decide) (by decide)
  exact stepOne.trans <| stepTwo.trans <| stepThree.trans <| stepFour.trans <| stepFive.trans <| stepSix.trans <| stepSeven

private theorem derivesCrossingMiddleEmpty :
    Derives basis (cw 0 [1, 2, 0, 3, 2]) (cw 0 [1, 2, 3, 0]) := by
  have stepOne :
      Derives basis (cw 0 [1, 2, 0, 3, 2]) (cw 0 [1, 2, 0, 3, 2, 0, 3]) :=
    derivesConcreteContext basisAlternatingStep
      (cw 2 []) (cw 0 [3]) (cw 2 [])
      [0, 1] [] (by decide) (by decide)
  have stepTwo :
      Derives basis (cw 0 [1, 2, 0, 3, 2, 0, 3]) (cw 0 [1, 2, 3, 2, 0, 3]) :=
    derivesConcreteContext (Derives.symm basisRegularStep)
      (cw 0 []) (cw 1 [2]) (cw 3 [2])
      [] [3] (by decide) (by decide)
  have stepThree :
      Derives basis (cw 0 [1, 2, 3, 2, 0, 3]) (cw 0 [1, 2, 3, 2, 3, 0, 3]) :=
    derivesConcreteContext basisAlternatingStep
      (cw 2 []) (cw 3 []) (cw 2 [])
      [0, 1] [0, 3] (by decide) (by decide)
  have stepFour :
      Derives basis (cw 0 [1, 2, 3, 2, 3, 0, 3]) (cw 0 [1, 2, 3, 0, 2, 3, 0, 3]) :=
    derivesConcreteContext basisRegularStep
      (cw 0 []) (cw 1 [2, 3]) (cw 2 [3])
      [] [3] (by decide) (by decide)
  have stepFive :
      Derives basis (cw 0 [1, 2, 3, 0, 2, 3, 0, 3]) (cw 0 [1, 2, 3, 0, 2, 3]) :=
    derivesConcreteContext (Derives.symm basisAlternatingStep)
      (cw 2 []) (cw 3 [0]) (cw 2 [])
      [0, 1] [3] (by decide) (by decide)
  have stepSix :
      Derives basis (cw 0 [1, 2, 3, 0, 2, 3]) (cw 0 [1, 0, 2, 3, 0, 2, 3]) :=
    derivesConcreteContext basisRegularStep
      (cw 0 []) (cw 1 []) (cw 2 [3])
      [] [2, 3] (by decide) (by decide)
  have stepSeven :
      Derives basis (cw 0 [1, 0, 2, 3, 0, 2, 3]) (cw 0 [1, 0, 2, 3, 0]) :=
    derivesConcreteContext (Derives.symm basisAlternatingStep)
      (cw 0 []) (cw 2 [3]) (cw 2 [])
      [0, 1] [] (by decide) (by decide)
  have stepEight :
      Derives basis (cw 0 [1, 0, 2, 3, 0]) (cw 0 [1, 2, 3, 0]) :=
    derivesConcreteContext (Derives.symm basisRegularStep)
      (cw 0 []) (cw 1 []) (cw 2 [3])
      [] [] (by decide) (by decide)
  exact stepOne.trans <| stepTwo.trans <| stepThree.trans <| stepFour.trans <| stepFive.trans <| stepSix.trans <| stepSeven.trans <| stepEight

private theorem derivesCrossingRightEmpty :
    Derives basis (cw 0 [1, 2, 3, 0, 2]) (cw 0 [1, 2, 3, 0]) := by
  have stepOne :
      Derives basis (cw 0 [1, 2, 3, 0, 2]) (cw 0 [1, 2, 3, 0, 1, 2, 3, 2]) :=
    derivesConcreteContext basisAlternatingStep
      (cw 0 []) (cw 1 [2, 3]) (cw 2 [])
      [] [2] (by decide) (by decide)
  have stepTwo :
      Derives basis (cw 0 [1, 2, 3, 0, 1, 2, 3, 2]) (cw 0 [1, 2, 3, 0, 1, 2]) :=
    derivesConcreteContext (Derives.symm basisAlternatingStep)
      (cw 0 [1]) (cw 2 [3]) (cw 2 [])
      [] [2] (by decide) (by decide)
  have stepThree :
      Derives basis (cw 0 [1, 2, 3, 0, 1, 2]) (cw 0 [1, 2, 3, 0, 1, 2, 3]) :=
    derivesConcreteContext basisAlternatingStep
      (cw 0 [1, 2]) (cw 3 []) (cw 2 [])
      [] [] (by decide) (by decide)
  have stepFour :
      Derives basis (cw 0 [1, 2, 3, 0, 1, 2, 3]) (cw 0 [1, 2, 3, 0]) :=
    derivesConcreteContext (Derives.symm basisAlternatingStep)
      (cw 0 []) (cw 1 [2, 3]) (cw 2 [])
      [] [] (by decide) (by decide)
  exact stepOne.trans <| stepTwo.trans <| stepThree.trans <| stepFour

private theorem derivesCrossingLeftMiddleEmpty :
    Derives basis (cw 0 [1, 0, 2, 1]) (cw 0 [1, 2, 0]) := by
  have stepOne :
      Derives basis (cw 0 [1, 0, 2, 1]) (cw 0 [1, 0, 2, 1, 0, 2]) :=
    derivesConcreteContext basisAlternatingStep
      (cw 1 []) (cw 0 [2]) (cw 2 [])
      [0] [] (by decide) (by decide)
  have stepTwo :
      Derives basis (cw 0 [1, 0, 2, 1, 0, 2]) (cw 0 [1, 0, 2, 0, 1, 0, 2]) :=
    derivesConcreteContext basisRegularStep
      (cw 0 []) (cw 1 [0, 2]) (cw 1 [])
      [] [2] (by decide) (by decide)
  have stepThree :
      Derives basis (cw 0 [1, 0, 2, 0, 1, 0, 2]) (cw 0 [1, 0, 2, 0]) :=
    derivesConcreteContext (Derives.symm basisAlternatingStep)
      (cw 0 []) (cw 1 [0, 2]) (cw 2 [])
      [] [] (by decide) (by decide)
  have stepFour :
      Derives basis (cw 0 [1, 0, 2, 0]) (cw 0 [1, 2, 0]) :=
    derivesConcreteContext (Derives.symm basisRegularStep)
      (cw 0 []) (cw 1 []) (cw 2 [])
      [] [] (by decide) (by decide)
  exact stepOne.trans <| stepTwo.trans <| stepThree.trans <| stepFour

private theorem derivesCrossingLeftRightEmpty :
    Derives basis (cw 0 [1, 2, 0, 1]) (cw 0 [1, 2, 0]) := by
  have stepOne :
      Derives basis (cw 0 [1, 2, 0, 1]) (cw 0 [1, 2, 0, 1, 2]) :=
    derivesConcreteContext basisAlternatingStep
      (cw 0 [1]) (cw 2 []) (cw 2 [])
      [] [] (by decide) (by decide)
  have stepTwo :
      Derives basis (cw 0 [1, 2, 0, 1, 2]) (cw 0 [1, 2, 0]) :=
    derivesConcreteContext (Derives.symm basisAlternatingStep)
      (cw 0 []) (cw 1 [2]) (cw 2 [])
      [] [] (by decide) (by decide)
  exact stepOne.trans <| stepTwo

private theorem derivesCrossingMiddleRightEmpty :
    Derives basis (cw 0 [1, 2, 0, 2]) (cw 0 [1, 2, 0]) := by
  have stepOne :
      Derives basis (cw 0 [1, 2, 0, 2]) (cw 0 [1, 2, 0, 1, 2, 2]) :=
    derivesConcreteContext basisAlternatingStep
      (cw 0 []) (cw 1 [2]) (cw 2 [])
      [] [2] (by decide) (by decide)
  have stepTwo :
      Derives basis (cw 0 [1, 2, 0, 1, 2, 2]) (cw 0 [1, 2, 0, 1, 2]) :=
    derivesConcreteContext (Derives.symm basisRightDuplicationStep)
      (cw 2 []) (cw 0 [1]) (cw 2 [])
      [0, 1] [] (by decide) (by decide)
  have stepThree :
      Derives basis (cw 0 [1, 2, 0, 1, 2]) (cw 0 [1, 2, 0]) :=
    derivesConcreteContext (Derives.symm basisAlternatingStep)
      (cw 0 []) (cw 1 [2]) (cw 2 [])
      [] [] (by decide) (by decide)
  exact stepOne.trans <| stepTwo.trans <| stepThree

private theorem derivesCrossingAllEmpty :
    Derives basis (cw 0 [1, 0, 1]) (cw 0 [1, 0]) := by
  have stepOne :
      Derives basis (cw 0 [1, 0, 1]) (cw 0 [1, 0]) :=
    derivesConcreteContext (Derives.symm basisAlternatingStep)
      (cw 0 []) (cw 1 []) (cw 2 [])
      [] [] (by decide) (by decide)
  exact stepOne


/-- Arbitrary-word form of the stored interior-doubling chain. -/
theorem derivesMiddleDuplication (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) (((u ++ v) ++ v) ++ u) := by
  have substituted :=
    Derives.subst derivesMiddleDoubling
      (instantiateThreeWords u v v)
  simpa [cw, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- Delete a nested repeated interval when all three fillers are nonempty. -/
theorem derivesNestedRepeat
    (outer leftGap repeated middleGap rightGap : Word Nat) :
    Derives basis
      ((((((outer ++ leftGap) ++ repeated) ++ middleGap) ++
        repeated) ++ rightGap) ++ outer)
      (((((outer ++ leftGap) ++ repeated) ++ middleGap) ++
        rightGap) ++ outer) := by
  have substituted :=
    Derives.subst derivesNestedRepeatDeletion
      (instantiateFiveWords
        outer leftGap repeated middleGap rightGap)
  simpa [cw, instantiateFiveWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- Absorb a crossing repeated interval when all three fillers are nonempty. -/
theorem derivesCrossingRepeat
    (outer leftGap crossing middleGap rightGap : Word Nat) :
    Derives basis
      ((((((outer ++ leftGap) ++ crossing) ++ middleGap) ++
        outer) ++ rightGap) ++ crossing)
      (((((outer ++ leftGap) ++ crossing) ++ middleGap) ++
        rightGap) ++ outer) := by
  have substituted :=
    Derives.subst derivesGeneralCrossingAbsorption
      (instantiateFiveWords
        outer leftGap crossing middleGap rightGap)
  simpa [cw, instantiateFiveWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

private def substituteTwo
    (a b : Word Nat) : Nat → Word Nat
  | 0 => a
  | 1 => b
  | n + 2 => Word.singleton (n + 2)

private def substituteThree
    (a b c : Word Nat) : Nat → Word Nat
  | 0 => a
  | 1 => b
  | 2 => c
  | n + 3 => Word.singleton (n + 3)

private def substituteFour
    (a b c d : Word Nat) : Nat → Word Nat
  | 0 => a
  | 1 => b
  | 2 => c
  | 3 => d
  | n + 4 => Word.singleton (n + 4)

/-- Delete a nested second occurrence with arbitrary, possibly empty,
filler lists. The eight branches are the nonempty metavariable law and its
seven finite endpoint cases above. -/
theorem listDerivesNestedInterval
    (outer repeated : Nat)
    (left middle right : List Nat) :
    S5_107.ListDerives basis
      ([outer] ++ left ++ [repeated] ++ middle ++
        [repeated] ++ right ++ [outer])
      ([outer] ++ left ++ [repeated] ++ middle ++
        right ++ [outer]) := by
  cases left with
  | nil =>
      cases middle with
      | nil =>
          cases right with
          | nil =>
              have substituted :=
                Derives.subst derivesNestedAllEmpty
                  (substituteTwo
                    (Word.singleton outer)
                    (Word.singleton repeated))
              simpa [cw, substituteTwo, Word.toList_bind,
                Word.singleton, List.append_assoc] using
                S5_107.ListDerives.ofWord substituted
          | cons rightHead rightTail =>
              let rightWord :=
                S5_107.listWordOfCons rightHead rightTail
              have substituted :=
                Derives.subst derivesNestedLeftMiddleEmpty
                  (substituteThree
                    (Word.singleton outer)
                    (Word.singleton repeated) rightWord)
              simpa [cw, rightWord, S5_107.listWordOfCons,
                substituteThree, Word.toList_bind, Word.singleton,
                List.append_assoc] using
                  S5_107.ListDerives.ofWord substituted
      | cons middleHead middleTail =>
          let middleWord :=
            S5_107.listWordOfCons middleHead middleTail
          cases right with
          | nil =>
              have substituted :=
                Derives.subst derivesNestedLeftRightEmpty
                  (substituteThree
                    (Word.singleton outer)
                    (Word.singleton repeated) middleWord)
              simpa [cw, middleWord, S5_107.listWordOfCons,
                substituteThree, Word.toList_bind, Word.singleton,
                List.append_assoc] using
                  S5_107.ListDerives.ofWord substituted
          | cons rightHead rightTail =>
              let rightWord :=
                S5_107.listWordOfCons rightHead rightTail
              have substituted :=
                Derives.subst derivesNestedLeftEmpty
                  (substituteFour
                    (Word.singleton outer)
                    (Word.singleton repeated)
                    middleWord rightWord)
              simpa [cw, middleWord, rightWord,
                S5_107.listWordOfCons, substituteFour,
                Word.toList_bind, Word.singleton,
                List.append_assoc] using
                  S5_107.ListDerives.ofWord substituted
  | cons leftHead leftTail =>
      let leftWord :=
        S5_107.listWordOfCons leftHead leftTail
      cases middle with
      | nil =>
          cases right with
          | nil =>
              have substituted :=
                Derives.subst derivesNestedMiddleRightEmpty
                  (substituteThree
                    (Word.singleton outer) leftWord
                    (Word.singleton repeated))
              simpa [cw, leftWord, S5_107.listWordOfCons,
                substituteThree, Word.toList_bind, Word.singleton,
                List.append_assoc] using
                  S5_107.ListDerives.ofWord substituted
          | cons rightHead rightTail =>
              let rightWord :=
                S5_107.listWordOfCons rightHead rightTail
              have substituted :=
                Derives.subst derivesNestedMiddleEmpty
                  (substituteFour
                    (Word.singleton outer) leftWord
                    (Word.singleton repeated) rightWord)
              simpa [cw, leftWord, rightWord,
                S5_107.listWordOfCons, substituteFour,
                Word.toList_bind, Word.singleton,
                List.append_assoc] using
                  S5_107.ListDerives.ofWord substituted
      | cons middleHead middleTail =>
          let middleWord :=
            S5_107.listWordOfCons middleHead middleTail
          cases right with
          | nil =>
              have substituted :=
                Derives.subst derivesNestedRightEmpty
                  (substituteFour
                    (Word.singleton outer) leftWord
                    (Word.singleton repeated) middleWord)
              simpa [cw, leftWord, middleWord,
                S5_107.listWordOfCons, substituteFour,
                Word.toList_bind, Word.singleton,
                List.append_assoc] using
                  S5_107.ListDerives.ofWord substituted
          | cons rightHead rightTail =>
              let rightWord :=
                S5_107.listWordOfCons rightHead rightTail
              simpa [leftWord, middleWord, rightWord,
                S5_107.listWordOfCons, Word.toList_append,
                Word.singleton, List.append_assoc] using
                  S5_107.ListDerives.ofWord
                    (derivesNestedRepeat
                      (Word.singleton outer) leftWord
                      (Word.singleton repeated)
                      middleWord rightWord)

/-- Absorb a crossing second occurrence with arbitrary, possibly empty,
filler lists. The result keeps the first-occurrence order and moves the
right filler inside the retained outer envelope. -/
theorem listDerivesCrossingInterval
    (outer crossing : Nat)
    (left middle right : List Nat) :
    S5_107.ListDerives basis
      ([outer] ++ left ++ [crossing] ++ middle ++
        [outer] ++ right ++ [crossing])
      ([outer] ++ left ++ [crossing] ++ middle ++
        right ++ [outer]) := by
  cases left with
  | nil =>
      cases middle with
      | nil =>
          cases right with
          | nil =>
              have substituted :=
                Derives.subst derivesCrossingAllEmpty
                  (substituteTwo
                    (Word.singleton outer)
                    (Word.singleton crossing))
              simpa [cw, substituteTwo, Word.toList_bind,
                Word.singleton, List.append_assoc] using
                  S5_107.ListDerives.ofWord substituted
          | cons rightHead rightTail =>
              let rightWord :=
                S5_107.listWordOfCons rightHead rightTail
              have substituted :=
                Derives.subst derivesCrossingLeftMiddleEmpty
                  (substituteThree
                    (Word.singleton outer)
                    (Word.singleton crossing) rightWord)
              simpa [cw, rightWord, S5_107.listWordOfCons,
                substituteThree, Word.toList_bind, Word.singleton,
                List.append_assoc] using
                  S5_107.ListDerives.ofWord substituted
      | cons middleHead middleTail =>
          let middleWord :=
            S5_107.listWordOfCons middleHead middleTail
          cases right with
          | nil =>
              have substituted :=
                Derives.subst derivesCrossingLeftRightEmpty
                  (substituteThree
                    (Word.singleton outer)
                    (Word.singleton crossing) middleWord)
              simpa [cw, middleWord, S5_107.listWordOfCons,
                substituteThree, Word.toList_bind, Word.singleton,
                List.append_assoc] using
                  S5_107.ListDerives.ofWord substituted
          | cons rightHead rightTail =>
              let rightWord :=
                S5_107.listWordOfCons rightHead rightTail
              have substituted :=
                Derives.subst derivesCrossingLeftEmpty
                  (substituteFour
                    (Word.singleton outer)
                    (Word.singleton crossing)
                    middleWord rightWord)
              simpa [cw, middleWord, rightWord,
                S5_107.listWordOfCons, substituteFour,
                Word.toList_bind, Word.singleton,
                List.append_assoc] using
                  S5_107.ListDerives.ofWord substituted
  | cons leftHead leftTail =>
      let leftWord :=
        S5_107.listWordOfCons leftHead leftTail
      cases middle with
      | nil =>
          cases right with
          | nil =>
              have substituted :=
                Derives.subst derivesCrossingMiddleRightEmpty
                  (substituteThree
                    (Word.singleton outer) leftWord
                    (Word.singleton crossing))
              simpa [cw, leftWord, S5_107.listWordOfCons,
                substituteThree, Word.toList_bind, Word.singleton,
                List.append_assoc] using
                  S5_107.ListDerives.ofWord substituted
          | cons rightHead rightTail =>
              let rightWord :=
                S5_107.listWordOfCons rightHead rightTail
              have substituted :=
                Derives.subst derivesCrossingMiddleEmpty
                  (substituteFour
                    (Word.singleton outer) leftWord
                    (Word.singleton crossing) rightWord)
              simpa [cw, leftWord, rightWord,
                S5_107.listWordOfCons, substituteFour,
                Word.toList_bind, Word.singleton,
                List.append_assoc] using
                  S5_107.ListDerives.ofWord substituted
      | cons middleHead middleTail =>
          let middleWord :=
            S5_107.listWordOfCons middleHead middleTail
          cases right with
          | nil =>
              have substituted :=
                Derives.subst derivesCrossingRightEmpty
                  (substituteFour
                    (Word.singleton outer) leftWord
                    (Word.singleton crossing) middleWord)
              simpa [cw, leftWord, middleWord,
                S5_107.listWordOfCons, substituteFour,
                Word.toList_bind, Word.singleton,
                List.append_assoc] using
                  S5_107.ListDerives.ofWord substituted
          | cons rightHead rightTail =>
              let rightWord :=
                S5_107.listWordOfCons rightHead rightTail
              simpa [leftWord, middleWord, rightWord,
                S5_107.listWordOfCons, Word.toList_append,
                Word.singleton, List.append_assoc] using
                  S5_107.ListDerives.ofWord
                    (derivesCrossingRepeat
                      (Word.singleton outer) leftWord
                      (Word.singleton crossing)
                      middleWord rightWord)

end SemigroupBasis.CoRoots.S5_791

