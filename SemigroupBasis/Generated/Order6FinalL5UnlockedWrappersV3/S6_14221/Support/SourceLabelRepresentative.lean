import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14221.Shards.RepresentativeStateProof
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14221.Support.Core
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14221.Support.SourceLabelTransition

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14221

open SemigroupBasis

private theorem generatorSourceLabelMap :
    ∀ generator : Fin 6,
      sourceLabel (generatorState generator) =
        generatorSourceLabel generator := by
  decide

private theorem sourceLabelTransitionWord
    (state : Fin 11742)
    (word : List (Fin 6)) :
    sourceLabel (word.foldl transition state) =
      word.foldl
        (fun value generator =>
          SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Representative.sourceSemigroup.mul value
            (generatorSourceLabel generator))
        (sourceLabel state) := by
  induction word generalizing state with
  | nil => rfl
  | cons generator word ih =>
      change
        sourceLabel
            (word.foldl transition
              (transition state generator)) =
          word.foldl
            (fun value nextGenerator =>
              SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Representative.sourceSemigroup.mul value
                (generatorSourceLabel nextGenerator))
            (SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Representative.sourceSemigroup.mul
              (sourceLabel state)
              (generatorSourceLabel generator))
      rw [ih]
      rw [sourceLabelTransition]

theorem sourceLabelRepresentative :
    ∀ state : Fin 11742,
      sourceLabel state =
        (representativeTail state).foldl
          (fun value generator =>
            SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Representative.sourceSemigroup.mul value
              (generatorSourceLabel generator))
          (generatorSourceLabel
            (representativeHead state)) := by
  intro state
  calc
    sourceLabel state =
        sourceLabel
          ((representativeTail state).foldl transition
            (generatorState
              (representativeHead state))) := by
      rw [Shards.representativeState state]
    _ = (representativeTail state).foldl
          (fun value generator =>
            SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Representative.sourceSemigroup.mul value
              (generatorSourceLabel generator))
          (sourceLabel
            (generatorState
              (representativeHead state))) :=
      sourceLabelTransitionWord _ _
    _ = (representativeTail state).foldl
          (fun value generator =>
            SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Representative.sourceSemigroup.mul value
              (generatorSourceLabel generator))
          (generatorSourceLabel
            (representativeHead state)) := by
      rw [generatorSourceLabelMap]

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14221
