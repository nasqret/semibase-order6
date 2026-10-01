import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.Shards.RepresentativeStateProof
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.Support.Core
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.Support.TransitionMap

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149

open SemigroupBasis

private theorem generatorStateMap :
    ∀ (generator : Fin 6)
      (coordinate : Fin 37),
      stateVector (generatorState generator) coordinate =
        generatorVector generator coordinate := by
  decide

private theorem stateVectorTransitionWord
    (state : Fin 11184)
    (word : List (Fin 6))
    (coordinate : Fin 37) :
    stateVector (word.foldl transition state) coordinate =
      word.foldl
        (fun value generator =>
          oppositeTable.semigroup.mul value
            (generatorVector generator coordinate))
        (stateVector state coordinate) := by
  induction word generalizing state with
  | nil => rfl
  | cons generator word ih =>
      change
        stateVector
            (word.foldl transition
              (transition state generator)) coordinate =
          word.foldl
            (fun value nextGenerator =>
              oppositeTable.semigroup.mul value
                (generatorVector nextGenerator coordinate))
            (oppositeTable.semigroup.mul
              (stateVector state coordinate)
              (generatorVector generator coordinate))
      rw [ih]
      rw [transitionMap]

theorem representativeMap :
    ∀ (state : Fin 11184)
      (coordinate : Fin 37),
      stateVector state coordinate =
        (representativeTail state).foldl
          (fun value generator =>
            oppositeTable.semigroup.mul value
              (generatorVector generator coordinate))
          (generatorVector
            (representativeHead state) coordinate) := by
  intro state coordinate
  calc
    stateVector state coordinate =
        stateVector
          ((representativeTail state).foldl transition
            (generatorState
              (representativeHead state))) coordinate := by
      rw [Shards.representativeState state]
    _ = (representativeTail state).foldl
          (fun value generator =>
            oppositeTable.semigroup.mul value
              (generatorVector generator coordinate))
          (stateVector
            (generatorState
              (representativeHead state)) coordinate) :=
      stateVectorTransitionWord _ _ _
    _ = (representativeTail state).foldl
          (fun value generator =>
            oppositeTable.semigroup.mul value
              (generatorVector generator coordinate))
          (generatorVector
            (representativeHead state) coordinate) := by
      rw [generatorStateMap]

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149
