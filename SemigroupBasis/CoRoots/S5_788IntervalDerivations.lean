import SemigroupBasis.CoRoots.S5_788EndpointCap

namespace SemigroupBasis.CoRoots.S5_788

open SemigroupBasis

private def cw (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

private theorem basisPowerStep :
    Derives basis powerLaw.lhs powerLaw.rhs :=
  Derives.fromBasis (e := powerLaw) (by simp [basis])

private theorem basisLeftDuplicationStep :
    Derives basis leftDuplicationLaw.lhs leftDuplicationLaw.rhs :=
  Derives.fromBasis (e := leftDuplicationLaw) (by simp [basis])

private theorem basisSquaresStep :
    Derives basis squaresLaw.lhs squaresLaw.rhs :=
  Derives.fromBasis (e := squaresLaw) (by simp [basis])

private theorem basisRightXExpansionStep :
    Derives basis rightXExpansionLaw.lhs rightXExpansionLaw.rhs :=
  Derives.fromBasis (e := rightXExpansionLaw) (by simp [basis])

private theorem basisRightZExpansionStep :
    Derives basis rightZExpansionLaw.lhs rightZExpansionLaw.rhs :=
  Derives.fromBasis (e := rightZExpansionLaw) (by simp [basis])

private theorem basisAlternatingCrossingStep :
    Derives basis
      alternatingCrossingLaw.lhs alternatingCrossingLaw.rhs :=
  Derives.fromBasis (e := alternatingCrossingLaw) (by simp [basis])

private theorem basisAlternatingCrossingYStep :
    Derives basis
      alternatingCrossingYLaw.lhs alternatingCrossingYLaw.rhs :=
  Derives.fromBasis (e := alternatingCrossingYLaw) (by simp [basis])

private theorem basisThirdOccurrenceStep :
    Derives basis thirdOccurrenceLaw.lhs thirdOccurrenceLaw.rhs :=
  Derives.fromBasis (e := thirdOccurrenceLaw) (by simp [basis])

private theorem basisRepeatedBlockStep :
    Derives basis repeatedBlockLaw.lhs repeatedBlockLaw.rhs :=
  Derives.fromBasis (e := repeatedBlockLaw) (by simp [basis])

/-- Nested deletion with an empty left filler. -/
private theorem derivesNestedLeftEmpty :
    Derives basis (cw 0 [1, 2, 1, 3, 0])
      (cw 0 [1, 2, 3, 0]) := by
  have stepOne :
      Derives basis (cw 0 [1, 2, 1, 3, 0])
        (cw 0 [1, 0, 1, 0, 2, 1, 3, 0]) :=
    derivesConcreteContext basisAlternatingCrossingStep
      (cw 0 []) (cw 1 []) (cw 2 [1, 3]) [] []
      (by decide) (by decide)
  have stepTwo :
      Derives basis (cw 0 [1, 0, 1, 0, 2, 1, 3, 0])
        (cw 0 [1, 2, 0, 3, 0]) :=
    derivesConcreteContext
      (Derives.symm basisAlternatingCrossingYStep)
      (cw 0 []) (cw 1 []) (cw 2 []) [] [3, 0]
      (by decide) (by decide)
  have stepThree :
      Derives basis (cw 0 [1, 2, 0, 3, 0])
        (cw 0 [1, 2, 0, 1, 2, 0, 3, 0]) :=
    derivesConcreteContext basisRepeatedBlockStep
      (cw 0 []) (cw 1 []) (cw 2 []) [] [3, 0]
      (by decide) (by decide)
  have stepFour :
      Derives basis (cw 0 [1, 2, 0, 1, 2, 0, 3, 0])
        (cw 0 [1, 2, 3, 0]) :=
    derivesConcreteContext
      (Derives.symm basisAlternatingCrossingStep)
      (cw 0 []) (cw 1 [2]) (cw 3 []) [] []
      (by decide) (by decide)
  exact stepOne.trans <| stepTwo.trans <| stepThree.trans stepFour

/-- Nested deletion with an empty middle filler. -/
private theorem derivesNestedMiddleEmpty :
    Derives basis (cw 0 [1, 2, 2, 3, 0])
      (cw 0 [1, 2, 3, 0]) := by
  have stepOne :
      Derives basis (cw 0 [1, 2, 2, 3, 0])
        (cw 0 [1, 2, 2, 3, 0, 2, 3]) :=
    derivesConcreteContext basisRightZExpansionStep
      (cw 0 []) (cw 1 [2]) (cw 2 [3]) [] []
      (by decide) (by decide)
  have stepTwo :
      Derives basis (cw 0 [1, 2, 2, 3, 0, 2, 3])
        (cw 0 [1, 2, 3, 0, 2, 3]) :=
    derivesConcreteContext
      (Derives.symm basisLeftDuplicationStep)
      (cw 2 []) (cw 3 [0]) (cw 2 []) [0, 1] [3]
      (by decide) (by decide)
  have stepThree :
      Derives basis (cw 0 [1, 2, 3, 0, 2, 3])
        (cw 0 [1, 2, 3, 0]) :=
    derivesConcreteContext
      (Derives.symm basisRightZExpansionStep)
      (cw 0 []) (cw 1 []) (cw 2 [3]) [] []
      (by decide) (by decide)
  exact stepOne.trans <| stepTwo.trans stepThree

/-- Nested deletion with an empty right filler. -/
private theorem derivesNestedRightEmpty :
    Derives basis (cw 0 [1, 2, 3, 2, 0])
      (cw 0 [1, 2, 3, 0]) := by
  have stepOne :
      Derives basis (cw 0 [1, 2, 3, 2, 0])
        (cw 0 [1, 2, 2, 3, 2, 0]) :=
    derivesConcreteContext basisLeftDuplicationStep
      (cw 2 []) (cw 3 []) (cw 2 []) [0, 1] [0]
      (by decide) (by decide)
  have stepTwo :
      Derives basis (cw 0 [1, 2, 2, 3, 2, 0])
        (cw 0 [1, 2, 2, 3, 2, 3, 0]) :=
    derivesConcreteContext basisRightZExpansionStep
      (cw 2 []) (cw 2 []) (cw 3 []) [0, 1] [0]
      (by decide) (by decide)
  have stepThree :
      Derives basis (cw 0 [1, 2, 2, 3, 2, 3, 0])
        (cw 0 [1, 2, 3, 2, 3, 0]) :=
    derivesConcreteContext
      (Derives.symm basisLeftDuplicationStep)
      (cw 2 []) (cw 3 []) (cw 2 []) [0, 1] [3, 0]
      (by decide) (by decide)
  have stepFour :
      Derives basis (cw 0 [1, 2, 3, 2, 3, 0])
        (cw 0 [1, 2, 3, 2, 3, 0, 0]) :=
    derivesConcreteContext basisRightXExpansionStep
      (cw 0 []) (cw 1 []) (cw 2 [3, 2, 3]) [] []
      (by decide) (by decide)
  have stepFive :
      Derives basis (cw 0 [1, 2, 3, 2, 3, 0, 0])
        (cw 0 [1, 2, 3, 0, 2, 3]) :=
    derivesConcreteContext (Derives.symm basisSquaresStep)
      (cw 2 [3]) (cw 0 []) (cw 2 []) [0, 1] []
      (by decide) (by decide)
  have stepSix :
      Derives basis (cw 0 [1, 2, 3, 0, 2, 3])
        (cw 0 [1, 2, 3, 0]) :=
    derivesConcreteContext
      (Derives.symm basisRightZExpansionStep)
      (cw 0 []) (cw 1 []) (cw 2 [3]) [] []
      (by decide) (by decide)
  exact stepOne.trans <| stepTwo.trans <| stepThree.trans <|
    stepFour.trans <| stepFive.trans stepSix

/-- Nested deletion with empty left and middle fillers. -/
private theorem derivesNestedLeftMiddleEmpty :
    Derives basis (cw 0 [1, 1, 2, 0])
      (cw 0 [1, 2, 0]) := by
  have stepOne :
      Derives basis (cw 0 [1, 1, 2, 0])
        (cw 0 [1, 1, 2, 0, 1, 2]) :=
    derivesConcreteContext basisRightZExpansionStep
      (cw 0 []) (cw 1 []) (cw 1 [2]) [] []
      (by decide) (by decide)
  have stepTwo :
      Derives basis (cw 0 [1, 1, 2, 0, 1, 2])
        (cw 0 [1, 2, 0, 1, 2]) :=
    derivesConcreteContext
      (Derives.symm basisLeftDuplicationStep)
      (cw 1 []) (cw 2 [0]) (cw 2 []) [0] [2]
      (by decide) (by decide)
  have stepThree :
      Derives basis (cw 0 [1, 2, 0, 1, 2])
        (cw 0 [0, 1, 2, 0, 1, 2]) :=
    derivesConcreteContext basisLeftDuplicationStep
      (cw 0 []) (cw 1 [2]) (cw 2 []) [] [1, 2]
      (by decide) (by decide)
  have stepFour :
      Derives basis (cw 0 [0, 1, 2, 0, 1, 2])
        (cw 0 [0, 1, 2, 0]) :=
    derivesConcreteContext
      (Derives.symm basisRightZExpansionStep)
      (cw 0 []) (cw 0 []) (cw 1 [2]) [] []
      (by decide) (by decide)
  have stepFive :
      Derives basis (cw 0 [0, 1, 2, 0])
        (cw 0 [1, 2, 0]) :=
    derivesConcreteContext
      (Derives.symm basisLeftDuplicationStep)
      (cw 0 []) (cw 1 [2]) (cw 2 []) [] []
      (by decide) (by decide)
  exact stepOne.trans <| stepTwo.trans <| stepThree.trans <|
    stepFour.trans stepFive

/-- Nested deletion with empty left and right fillers. -/
private theorem derivesNestedLeftRightEmpty :
    Derives basis (cw 0 [1, 2, 1, 0])
      (cw 0 [1, 2, 0]) := by
  have stepOne :
      Derives basis (cw 0 [1, 2, 1, 0])
        (cw 0 [1, 1, 2, 1, 0]) :=
    derivesConcreteContext basisLeftDuplicationStep
      (cw 1 []) (cw 2 []) (cw 2 []) [0] [0]
      (by decide) (by decide)
  have stepTwo :
      Derives basis (cw 0 [1, 1, 2, 1, 0])
        (cw 0 [1, 1, 2, 1, 2, 0]) :=
    derivesConcreteContext basisRightZExpansionStep
      (cw 1 []) (cw 1 []) (cw 2 []) [0] [0]
      (by decide) (by decide)
  have stepThree :
      Derives basis (cw 0 [1, 1, 2, 1, 2, 0])
        (cw 0 [1, 2, 1, 2, 0]) :=
    derivesConcreteContext
      (Derives.symm basisLeftDuplicationStep)
      (cw 1 []) (cw 2 []) (cw 2 []) [0] [2, 0]
      (by decide) (by decide)
  have stepFour :
      Derives basis (cw 0 [1, 2, 1, 2, 0])
        (cw 0 [0, 1, 2, 1, 2, 0]) :=
    derivesConcreteContext basisLeftDuplicationStep
      (cw 0 []) (cw 1 [2, 1, 2]) (cw 2 []) [] []
      (by decide) (by decide)
  have stepFive :
      Derives basis (cw 0 [0, 1, 2, 1, 2, 0])
        (cw 0 [1, 2, 0, 0]) :=
    derivesConcreteContext (Derives.symm basisSquaresStep)
      (cw 0 []) (cw 1 [2]) (cw 2 []) [] [0]
      (by decide) (by decide)
  have stepSix :
      Derives basis (cw 0 [1, 2, 0, 0])
        (cw 0 [1, 2, 0]) :=
    derivesConcreteContext
      (Derives.symm basisRightXExpansionStep)
      (cw 0 []) (cw 1 []) (cw 2 []) [] []
      (by decide) (by decide)
  exact stepOne.trans <| stepTwo.trans <| stepThree.trans <|
    stepFour.trans <| stepFive.trans stepSix

/-- Nested deletion with empty middle and right fillers. -/
private theorem derivesNestedMiddleRightEmpty :
    Derives basis (cw 0 [1, 2, 2, 0])
      (cw 0 [1, 2, 0]) := by
  have stepOne :
      Derives basis (cw 0 [1, 2, 2, 0])
        (cw 0 [1, 2, 2, 0, 0]) :=
    derivesConcreteContext basisRightXExpansionStep
      (cw 0 []) (cw 1 []) (cw 2 [2]) [] []
      (by decide) (by decide)
  have stepTwo :
      Derives basis (cw 0 [1, 2, 2, 0, 0])
        (cw 0 [1, 2, 0, 2]) :=
    derivesConcreteContext (Derives.symm basisSquaresStep)
      (cw 2 []) (cw 0 []) (cw 2 []) [0, 1] []
      (by decide) (by decide)
  have stepThree :
      Derives basis (cw 0 [1, 2, 0, 2])
        (cw 0 [1, 2, 0]) :=
    derivesConcreteContext
      (Derives.symm basisRightZExpansionStep)
      (cw 0 []) (cw 1 []) (cw 2 []) [] []
      (by decide) (by decide)
  exact stepOne.trans <| stepTwo.trans stepThree

/-- Nested deletion with all three fillers empty. -/
private theorem derivesNestedAllEmpty :
    Derives basis (cw 0 [1, 1, 0])
      (cw 0 [1, 0]) := by
  have stepOne :
      Derives basis (cw 0 [1, 1, 0])
        (cw 0 [0, 1, 1, 1, 1]) :=
    derivesConcreteContext basisSquaresStep
      (cw 0 []) (cw 1 [1]) (cw 2 []) [] []
      (by decide) (by decide)
  have stepTwo :
      Derives basis (cw 0 [0, 1, 1, 1, 1])
        (cw 0 [0, 1, 1, 1]) :=
    derivesConcreteContext (Derives.symm basisPowerStep)
      (cw 1 []) (cw 1 []) (cw 2 []) [0, 0] [1]
      (by decide) (by decide)
  have stepThree :
      Derives basis (cw 0 [0, 1, 1, 1])
        (cw 0 [0, 1, 1]) :=
    derivesConcreteContext (Derives.symm basisPowerStep)
      (cw 1 []) (cw 1 []) (cw 2 []) [0, 0] []
      (by decide) (by decide)
  have stepFour :
      Derives basis (cw 0 [0, 1, 1])
        (cw 0 [1, 0]) :=
    derivesConcreteContext (Derives.symm basisSquaresStep)
      (cw 0 []) (cw 1 []) (cw 2 []) [] []
      (by decide) (by decide)
  exact stepOne.trans <| stepTwo.trans <| stepThree.trans stepFour

/-- Crossing absorption with an empty left filler. -/
private theorem derivesCrossingLeftEmpty :
    Derives basis (cw 0 [1, 2, 0, 3, 1])
      (cw 0 [1, 2, 3, 0]) := by
  have stepOne :
      Derives basis (cw 0 [1, 2, 0, 3, 1])
        (cw 0 [1, 0, 1, 0, 2, 0, 3, 1]) :=
    derivesConcreteContext basisAlternatingCrossingStep
      (cw 0 []) (cw 1 []) (cw 2 []) [] [3, 1]
      (by decide) (by decide)
  have stepTwo :
      Derives basis (cw 0 [1, 0, 1, 0, 2, 0, 3, 1])
        (cw 0 [1, 2, 0, 3, 0]) :=
    derivesConcreteContext
      (Derives.symm basisAlternatingCrossingYStep)
      (cw 0 []) (cw 1 []) (cw 2 [0, 3]) [] []
      (by decide) (by decide)
  have stepThree :
      Derives basis (cw 0 [1, 2, 0, 3, 0])
        (cw 0 [1, 2, 0, 1, 2, 0, 3, 0]) :=
    derivesConcreteContext basisRepeatedBlockStep
      (cw 0 []) (cw 1 []) (cw 2 []) [] [3, 0]
      (by decide) (by decide)
  have stepFour :
      Derives basis (cw 0 [1, 2, 0, 1, 2, 0, 3, 0])
        (cw 0 [1, 2, 3, 0]) :=
    derivesConcreteContext
      (Derives.symm basisAlternatingCrossingStep)
      (cw 0 []) (cw 1 [2]) (cw 3 []) [] []
      (by decide) (by decide)
  exact stepOne.trans <| stepTwo.trans <| stepThree.trans stepFour

/-- Crossing absorption with an empty middle filler. -/
private theorem derivesCrossingMiddleEmpty :
    Derives basis (cw 0 [1, 2, 0, 3, 2])
      (cw 0 [1, 2, 3, 0]) := by
  have stepOne :
      Derives basis (cw 0 [1, 2, 0, 3, 2])
        (cw 0 [1, 2, 0, 2, 3, 0, 2, 3]) :=
    derivesConcreteContext basisThirdOccurrenceStep
      (cw 2 []) (cw 0 []) (cw 3 []) [0, 1] []
      (by decide) (by decide)
  have stepTwo :
      Derives basis (cw 0 [1, 2, 0, 2, 3, 0, 2, 3])
        (cw 0 [1, 2, 0, 2, 3, 0]) :=
    derivesConcreteContext
      (Derives.symm basisRightZExpansionStep)
      (cw 0 []) (cw 1 [2, 0]) (cw 2 [3]) [] []
      (by decide) (by decide)
  have stepThree :
      Derives basis (cw 0 [1, 2, 0, 2, 3, 0])
        (cw 0 [1, 2, 0, 3, 0]) :=
    derivesConcreteContext
      (Derives.symm basisRightZExpansionStep)
      (cw 0 []) (cw 1 []) (cw 2 []) [] [3, 0]
      (by decide) (by decide)
  have stepFour :
      Derives basis (cw 0 [1, 2, 0, 3, 0])
        (cw 0 [1, 2, 0, 1, 2, 0, 3, 0]) :=
    derivesConcreteContext basisRepeatedBlockStep
      (cw 0 []) (cw 1 []) (cw 2 []) [] [3, 0]
      (by decide) (by decide)
  have stepFive :
      Derives basis (cw 0 [1, 2, 0, 1, 2, 0, 3, 0])
        (cw 0 [1, 2, 3, 0]) :=
    derivesConcreteContext
      (Derives.symm basisAlternatingCrossingStep)
      (cw 0 []) (cw 1 [2]) (cw 3 []) [] []
      (by decide) (by decide)
  exact stepOne.trans <| stepTwo.trans <| stepThree.trans <|
    stepFour.trans stepFive

/-- Crossing absorption with an empty right filler. -/
private theorem derivesCrossingRightEmpty :
    Derives basis (cw 0 [1, 2, 3, 0, 2])
      (cw 0 [1, 2, 3, 0]) := by
  have stepOne :
      Derives basis (cw 0 [1, 2, 3, 0, 2])
        (cw 0 [1, 2, 3, 0, 2, 3, 2]) :=
    derivesConcreteContext basisRightZExpansionStep
      (cw 0 []) (cw 1 []) (cw 2 [3]) [] [2]
      (by decide) (by decide)
  have stepTwo :
      Derives basis (cw 0 [1, 2, 3, 0, 2, 3, 2])
        (cw 0 [1, 2, 3, 0, 2, 3]) :=
    derivesConcreteContext
      (Derives.symm basisRightZExpansionStep)
      (cw 3 []) (cw 0 []) (cw 2 []) [0, 1, 2] []
      (by decide) (by decide)
  have stepThree :
      Derives basis (cw 0 [1, 2, 3, 0, 2, 3])
        (cw 0 [1, 2, 3, 0]) :=
    derivesConcreteContext
      (Derives.symm basisRightZExpansionStep)
      (cw 0 []) (cw 1 []) (cw 2 [3]) [] []
      (by decide) (by decide)
  exact stepOne.trans <| stepTwo.trans stepThree

/-- Crossing absorption with empty left and middle fillers. -/
private theorem derivesCrossingLeftMiddleEmpty :
    Derives basis (cw 0 [1, 0, 2, 1])
      (cw 0 [1, 2, 0]) := by
  have stepOne :
      Derives basis (cw 0 [1, 0, 2, 1])
        (cw 0 [0, 1, 1, 2, 1]) :=
    derivesConcreteContext basisSquaresStep
      (cw 0 []) (cw 1 []) (cw 2 []) [] [2, 1]
      (by decide) (by decide)
  have stepTwo :
      Derives basis (cw 0 [0, 1, 1, 2, 1])
        (cw 0 [0, 1, 1, 2, 1, 2]) :=
    derivesConcreteContext basisRightZExpansionStep
      (cw 1 []) (cw 1 []) (cw 2 []) [0, 0] []
      (by decide) (by decide)
  have stepThree :
      Derives basis (cw 0 [0, 1, 1, 2, 1, 2])
        (cw 0 [0, 1, 2, 1, 2]) :=
    derivesConcreteContext
      (Derives.symm basisLeftDuplicationStep)
      (cw 1 []) (cw 2 []) (cw 2 []) [0, 0] [2]
      (by decide) (by decide)
  have stepFour :
      Derives basis (cw 0 [0, 1, 2, 1, 2])
        (cw 0 [1, 2, 0]) :=
    derivesConcreteContext (Derives.symm basisSquaresStep)
      (cw 0 []) (cw 1 [2]) (cw 2 []) [] []
      (by decide) (by decide)
  exact stepOne.trans <| stepTwo.trans <| stepThree.trans stepFour

/-- Crossing absorption with empty left and right fillers. -/
private theorem derivesCrossingLeftRightEmpty :
    Derives basis (cw 0 [1, 2, 0, 1])
      (cw 0 [1, 2, 0]) := by
  have stepOne :
      Derives basis (cw 0 [1, 2, 0, 1])
        (cw 0 [1, 0, 1, 2, 2]) :=
    derivesConcreteContext basisSquaresStep
      (cw 0 [1]) (cw 2 []) (cw 2 []) [] []
      (by decide) (by decide)
  have stepTwo :
      Derives basis (cw 0 [1, 0, 1, 2, 2])
        (cw 0 [0, 1, 1, 1, 2, 2]) :=
    derivesConcreteContext basisSquaresStep
      (cw 0 []) (cw 1 []) (cw 2 []) [] [1, 2, 2]
      (by decide) (by decide)
  have stepThree :
      Derives basis (cw 0 [0, 1, 1, 1, 2, 2])
        (cw 0 [0, 1, 1, 2, 2]) :=
    derivesConcreteContext (Derives.symm basisPowerStep)
      (cw 1 []) (cw 1 []) (cw 2 []) [0, 0] [2, 2]
      (by decide) (by decide)
  have stepFour :
      Derives basis (cw 0 [0, 1, 1, 2, 2])
        (cw 0 [0, 1, 1, 2, 2, 2]) :=
    derivesConcreteContext basisPowerStep
      (cw 2 []) (cw 1 []) (cw 2 []) [0, 0, 1, 1] []
      (by decide) (by decide)
  have stepFive :
      Derives basis (cw 0 [0, 1, 1, 2, 2, 2])
        (cw 0 [0, 1, 2, 1, 2]) :=
    derivesConcreteContext (Derives.symm basisSquaresStep)
      (cw 1 []) (cw 2 []) (cw 2 []) [0, 0] [2]
      (by decide) (by decide)
  have stepSix :
      Derives basis (cw 0 [0, 1, 2, 1, 2])
        (cw 0 [1, 2, 0]) :=
    derivesConcreteContext (Derives.symm basisSquaresStep)
      (cw 0 []) (cw 1 [2]) (cw 2 []) [] []
      (by decide) (by decide)
  exact stepOne.trans <| stepTwo.trans <| stepThree.trans <|
    stepFour.trans <| stepFive.trans stepSix

/-- Crossing absorption with empty middle and right fillers. -/
private theorem derivesCrossingMiddleRightEmpty :
    Derives basis (cw 0 [1, 2, 0, 2])
      (cw 0 [1, 2, 0]) := by
  exact
    derivesConcreteContext
      (Derives.symm basisRightZExpansionStep)
      (cw 0 []) (cw 1 []) (cw 2 []) [] []
      (by decide) (by decide)

/-- Crossing absorption with all three fillers empty. -/
private theorem derivesCrossingAllEmpty :
    Derives basis (cw 0 [1, 0, 1])
      (cw 0 [1, 0]) := by
  have stepOne :
      Derives basis (cw 0 [1, 0, 1])
        (cw 0 [0, 1, 0, 1]) :=
    derivesConcreteContext basisLeftDuplicationStep
      (cw 0 []) (cw 1 []) (cw 2 []) [] [1]
      (by decide) (by decide)
  have stepTwo :
      Derives basis (cw 0 [0, 1, 0, 1])
        (cw 0 [0, 1, 0]) :=
    derivesConcreteContext
      (Derives.symm basisRightZExpansionStep)
      (cw 0 []) (cw 0 []) (cw 1 []) [] []
      (by decide) (by decide)
  have stepThree :
      Derives basis (cw 0 [0, 1, 0])
        (cw 0 [1, 0]) :=
    derivesConcreteContext
      (Derives.symm basisLeftDuplicationStep)
      (cw 0 []) (cw 1 []) (cw 2 []) [] []
      (by decide) (by decide)
  exact stepOne.trans <| stepTwo.trans stepThree

/-- Merge adjacent closed envelopes with nonempty interiors. -/
private theorem derivesAdjacentEnvelopes :
    Derives basis (cw 0 [1, 0, 2, 3, 2])
      (cw 0 [1, 2, 3, 0]) := by
  have stepOne :
      Derives basis (cw 0 [1, 0, 2, 3, 2])
        (cw 0 [1, 0, 2, 2, 3, 2]) :=
    derivesConcreteContext basisLeftDuplicationStep
      (cw 2 []) (cw 3 []) (cw 2 []) [0, 1, 0] []
      (by decide) (by decide)
  have stepTwo :
      Derives basis (cw 0 [1, 0, 2, 2, 3, 2])
        (cw 0 [1, 0, 2, 2, 2, 3, 3]) :=
    derivesConcreteContext basisSquaresStep
      (cw 2 []) (cw 3 []) (cw 2 []) [0, 1, 0, 2] []
      (by decide) (by decide)
  have stepThree :
      Derives basis (cw 0 [1, 0, 2, 2, 2, 3, 3])
        (cw 0 [0, 1, 1, 2, 2, 2, 3, 3]) :=
    derivesConcreteContext basisSquaresStep
      (cw 0 []) (cw 1 []) (cw 2 []) [] [2, 2, 2, 3, 3]
      (by decide) (by decide)
  have stepFour :
      Derives basis (cw 0 [0, 1, 1, 2, 2, 2, 3, 3])
        (cw 0 [0, 1, 2, 1, 2, 3, 3]) :=
    derivesConcreteContext (Derives.symm basisSquaresStep)
      (cw 1 []) (cw 2 []) (cw 2 []) [0, 0] [2, 3, 3]
      (by decide) (by decide)
  have stepFive :
      Derives basis (cw 0 [0, 1, 2, 1, 2, 3, 3])
        (cw 0 [0, 1, 2, 1, 2, 3, 3, 3]) :=
    derivesConcreteContext basisPowerStep
      (cw 3 []) (cw 1 []) (cw 2 []) [0, 0, 1, 2, 1, 2] []
      (by decide) (by decide)
  have stepSix :
      Derives basis (cw 0 [0, 1, 2, 1, 2, 3, 3, 3])
        (cw 0 [0, 1, 2, 3, 1, 2, 3]) :=
    derivesConcreteContext (Derives.symm basisSquaresStep)
      (cw 1 [2]) (cw 3 []) (cw 2 []) [0, 0] [3]
      (by decide) (by decide)
  have stepSeven :
      Derives basis (cw 0 [0, 1, 2, 3, 1, 2, 3])
        (cw 0 [1, 2, 3, 0]) :=
    derivesConcreteContext (Derives.symm basisSquaresStep)
      (cw 0 []) (cw 1 [2, 3]) (cw 2 []) [] []
      (by decide) (by decide)
  exact stepOne.trans <| stepTwo.trans <| stepThree.trans <|
    stepFour.trans <| stepFive.trans <| stepSix.trans stepSeven

/-- Merge adjacent closed envelopes when the first interior is empty. -/
private theorem derivesAdjacentLeftEmpty :
    Derives basis (cw 0 [0, 1, 2, 1])
      (cw 0 [1, 2, 0]) := by
  have stepOne :
      Derives basis (cw 0 [0, 1, 2, 1])
        (cw 0 [0, 1, 1, 2, 1]) :=
    derivesConcreteContext basisLeftDuplicationStep
      (cw 1 []) (cw 2 []) (cw 2 []) [0, 0] []
      (by decide) (by decide)
  have stepTwo :
      Derives basis (cw 0 [0, 1, 1, 2, 1])
        (cw 0 [0, 1, 1, 2, 1, 2]) :=
    derivesConcreteContext basisRightZExpansionStep
      (cw 1 []) (cw 1 []) (cw 2 []) [0, 0] []
      (by decide) (by decide)
  have stepThree :
      Derives basis (cw 0 [0, 1, 1, 2, 1, 2])
        (cw 0 [0, 1, 2, 1, 2]) :=
    derivesConcreteContext
      (Derives.symm basisLeftDuplicationStep)
      (cw 1 []) (cw 2 []) (cw 2 []) [0, 0] [2]
      (by decide) (by decide)
  have stepFour :
      Derives basis (cw 0 [0, 1, 2, 1, 2])
        (cw 0 [1, 2, 0]) :=
    derivesConcreteContext (Derives.symm basisSquaresStep)
      (cw 0 []) (cw 1 [2]) (cw 2 []) [] []
      (by decide) (by decide)
  exact stepOne.trans <| stepTwo.trans <| stepThree.trans stepFour

/-- Merge adjacent closed envelopes when the second interior is empty. -/
private theorem derivesAdjacentRightEmpty :
    Derives basis (cw 0 [1, 0, 2, 2])
      (cw 0 [1, 2, 0]) := by
  have stepOne :
      Derives basis (cw 0 [1, 0, 2, 2])
        (cw 0 [0, 1, 1, 2, 2]) :=
    derivesConcreteContext basisSquaresStep
      (cw 0 []) (cw 1 []) (cw 2 []) [] [2, 2]
      (by decide) (by decide)
  have stepTwo :
      Derives basis (cw 0 [0, 1, 1, 2, 2])
        (cw 0 [0, 1, 1, 2, 2, 2]) :=
    derivesConcreteContext basisPowerStep
      (cw 2 []) (cw 1 []) (cw 2 []) [0, 0, 1, 1] []
      (by decide) (by decide)
  have stepThree :
      Derives basis (cw 0 [0, 1, 1, 2, 2, 2])
        (cw 0 [0, 1, 2, 1, 2]) :=
    derivesConcreteContext (Derives.symm basisSquaresStep)
      (cw 1 []) (cw 2 []) (cw 2 []) [0, 0] [2]
      (by decide) (by decide)
  have stepFour :
      Derives basis (cw 0 [0, 1, 2, 1, 2])
        (cw 0 [1, 2, 0]) :=
    derivesConcreteContext (Derives.symm basisSquaresStep)
      (cw 0 []) (cw 1 [2]) (cw 2 []) [] []
      (by decide) (by decide)
  exact stepOne.trans <| stepTwo.trans <| stepThree.trans stepFour

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

/-- Merge two adjacent closed envelopes without changing their
first-occurrence order. -/
theorem listDerivesAdjacentEnvelopes
    (first second : Nat)
    (firstInterior secondInterior : List Nat) :
    S5_107.ListDerives basis
      ([first] ++ firstInterior ++ [first] ++
        [second] ++ secondInterior ++ [second])
      ([first] ++ firstInterior ++ [second] ++
        secondInterior ++ [first]) := by
  cases firstInterior with
  | nil =>
      cases secondInterior with
      | nil =>
          simpa [Word.toList_append, Word.singleton,
            List.append_assoc] using
              S5_107.ListDerives.ofWord
                (derivesSquares
                  (Word.singleton first)
                  (Word.singleton second)).symm
      | cons secondHead secondTail =>
          let secondWord :=
            S5_107.listWordOfCons secondHead secondTail
          have substituted :=
            Derives.subst derivesAdjacentLeftEmpty
              (substituteThree
                (Word.singleton first)
                (Word.singleton second) secondWord)
          simpa [cw, secondWord, S5_107.listWordOfCons,
            substituteThree, Word.toList_bind, Word.singleton,
            List.append_assoc] using
              S5_107.ListDerives.ofWord substituted
  | cons firstHead firstTail =>
      let firstWord :=
        S5_107.listWordOfCons firstHead firstTail
      cases secondInterior with
      | nil =>
          have substituted :=
            Derives.subst derivesAdjacentRightEmpty
              (substituteThree
                (Word.singleton first) firstWord
                (Word.singleton second))
          simpa [cw, firstWord, S5_107.listWordOfCons,
            substituteThree, Word.toList_bind, Word.singleton,
            List.append_assoc] using
              S5_107.ListDerives.ofWord substituted
      | cons secondHead secondTail =>
          let secondWord :=
            S5_107.listWordOfCons secondHead secondTail
          have substituted :=
            Derives.subst derivesAdjacentEnvelopes
              (substituteFour
                (Word.singleton first) firstWord
                (Word.singleton second) secondWord)
          simpa [cw, firstWord, secondWord,
            S5_107.listWordOfCons, substituteFour,
            Word.toList_bind, Word.singleton,
            List.append_assoc] using
              S5_107.ListDerives.ofWord substituted

end SemigroupBasis.CoRoots.S5_788
