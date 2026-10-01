import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.Support.Core
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.Shards

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0096 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.transition (⟨6144 + candidate.val, by omega⟩ : Fin 7782) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4022Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel (⟨6144 + candidate.val, by omega⟩ : Fin 7782))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0096
    (state : Fin 7782)
    (lower : 6144 ≤ state.val)
    (upper : state.val < 6208)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4022Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 6144, by omega⟩
  have state_eq :
      (⟨6144 + offset.val, by omega⟩ : Fin 7782) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0096 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0097 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.transition (⟨6208 + candidate.val, by omega⟩ : Fin 7782) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4022Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel (⟨6208 + candidate.val, by omega⟩ : Fin 7782))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0097
    (state : Fin 7782)
    (lower : 6208 ≤ state.val)
    (upper : state.val < 6272)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4022Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 6208, by omega⟩
  have state_eq :
      (⟨6208 + offset.val, by omega⟩ : Fin 7782) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0097 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0098 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.transition (⟨6272 + candidate.val, by omega⟩ : Fin 7782) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4022Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel (⟨6272 + candidate.val, by omega⟩ : Fin 7782))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0098
    (state : Fin 7782)
    (lower : 6272 ≤ state.val)
    (upper : state.val < 6336)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4022Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 6272, by omega⟩
  have state_eq :
      (⟨6272 + offset.val, by omega⟩ : Fin 7782) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0098 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0099 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.transition (⟨6336 + candidate.val, by omega⟩ : Fin 7782) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4022Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel (⟨6336 + candidate.val, by omega⟩ : Fin 7782))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0099
    (state : Fin 7782)
    (lower : 6336 ≤ state.val)
    (upper : state.val < 6400)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4022Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 6336, by omega⟩
  have state_eq :
      (⟨6336 + offset.val, by omega⟩ : Fin 7782) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0099 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0100 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.transition (⟨6400 + candidate.val, by omega⟩ : Fin 7782) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4022Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel (⟨6400 + candidate.val, by omega⟩ : Fin 7782))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0100
    (state : Fin 7782)
    (lower : 6400 ≤ state.val)
    (upper : state.val < 6464)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4022Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 6400, by omega⟩
  have state_eq :
      (⟨6400 + offset.val, by omega⟩ : Fin 7782) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0100 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0101 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.transition (⟨6464 + candidate.val, by omega⟩ : Fin 7782) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4022Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel (⟨6464 + candidate.val, by omega⟩ : Fin 7782))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0101
    (state : Fin 7782)
    (lower : 6464 ≤ state.val)
    (upper : state.val < 6528)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4022Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 6464, by omega⟩
  have state_eq :
      (⟨6464 + offset.val, by omega⟩ : Fin 7782) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0101 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0102 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.transition (⟨6528 + candidate.val, by omega⟩ : Fin 7782) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4022Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel (⟨6528 + candidate.val, by omega⟩ : Fin 7782))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0102
    (state : Fin 7782)
    (lower : 6528 ≤ state.val)
    (upper : state.val < 6592)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4022Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 6528, by omega⟩
  have state_eq :
      (⟨6528 + offset.val, by omega⟩ : Fin 7782) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0102 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0103 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.transition (⟨6592 + candidate.val, by omega⟩ : Fin 7782) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4022Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel (⟨6592 + candidate.val, by omega⟩ : Fin 7782))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0103
    (state : Fin 7782)
    (lower : 6592 ≤ state.val)
    (upper : state.val < 6656)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4022Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 6592, by omega⟩
  have state_eq :
      (⟨6592 + offset.val, by omega⟩ : Fin 7782) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0103 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0104 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.transition (⟨6656 + candidate.val, by omega⟩ : Fin 7782) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4022Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel (⟨6656 + candidate.val, by omega⟩ : Fin 7782))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0104
    (state : Fin 7782)
    (lower : 6656 ≤ state.val)
    (upper : state.val < 6720)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4022Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 6656, by omega⟩
  have state_eq :
      (⟨6656 + offset.val, by omega⟩ : Fin 7782) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0104 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0105 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.transition (⟨6720 + candidate.val, by omega⟩ : Fin 7782) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4022Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel (⟨6720 + candidate.val, by omega⟩ : Fin 7782))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0105
    (state : Fin 7782)
    (lower : 6720 ≤ state.val)
    (upper : state.val < 6784)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4022Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 6720, by omega⟩
  have state_eq :
      (⟨6720 + offset.val, by omega⟩ : Fin 7782) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0105 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0106 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.transition (⟨6784 + candidate.val, by omega⟩ : Fin 7782) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4022Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel (⟨6784 + candidate.val, by omega⟩ : Fin 7782))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0106
    (state : Fin 7782)
    (lower : 6784 ≤ state.val)
    (upper : state.val < 6848)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4022Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 6784, by omega⟩
  have state_eq :
      (⟨6784 + offset.val, by omega⟩ : Fin 7782) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0106 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0107 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.transition (⟨6848 + candidate.val, by omega⟩ : Fin 7782) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4022Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel (⟨6848 + candidate.val, by omega⟩ : Fin 7782))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0107
    (state : Fin 7782)
    (lower : 6848 ≤ state.val)
    (upper : state.val < 6912)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4022Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 6848, by omega⟩
  have state_eq :
      (⟨6848 + offset.val, by omega⟩ : Fin 7782) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0107 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0108 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.transition (⟨6912 + candidate.val, by omega⟩ : Fin 7782) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4022Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel (⟨6912 + candidate.val, by omega⟩ : Fin 7782))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0108
    (state : Fin 7782)
    (lower : 6912 ≤ state.val)
    (upper : state.val < 6976)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4022Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 6912, by omega⟩
  have state_eq :
      (⟨6912 + offset.val, by omega⟩ : Fin 7782) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0108 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0109 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.transition (⟨6976 + candidate.val, by omega⟩ : Fin 7782) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4022Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel (⟨6976 + candidate.val, by omega⟩ : Fin 7782))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0109
    (state : Fin 7782)
    (lower : 6976 ≤ state.val)
    (upper : state.val < 7040)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4022Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 6976, by omega⟩
  have state_eq :
      (⟨6976 + offset.val, by omega⟩ : Fin 7782) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0109 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0110 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.transition (⟨7040 + candidate.val, by omega⟩ : Fin 7782) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4022Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel (⟨7040 + candidate.val, by omega⟩ : Fin 7782))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0110
    (state : Fin 7782)
    (lower : 7040 ≤ state.val)
    (upper : state.val < 7104)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4022Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 7040, by omega⟩
  have state_eq :
      (⟨7040 + offset.val, by omega⟩ : Fin 7782) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0110 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0111 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.transition (⟨7104 + candidate.val, by omega⟩ : Fin 7782) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4022Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel (⟨7104 + candidate.val, by omega⟩ : Fin 7782))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0111
    (state : Fin 7782)
    (lower : 7104 ≤ state.val)
    (upper : state.val < 7168)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4022Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 7104, by omega⟩
  have state_eq :
      (⟨7104 + offset.val, by omega⟩ : Fin 7782) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0111 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0112 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.transition (⟨7168 + candidate.val, by omega⟩ : Fin 7782) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4022Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel (⟨7168 + candidate.val, by omega⟩ : Fin 7782))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0112
    (state : Fin 7782)
    (lower : 7168 ≤ state.val)
    (upper : state.val < 7232)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4022Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 7168, by omega⟩
  have state_eq :
      (⟨7168 + offset.val, by omega⟩ : Fin 7782) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0112 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0113 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.transition (⟨7232 + candidate.val, by omega⟩ : Fin 7782) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4022Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel (⟨7232 + candidate.val, by omega⟩ : Fin 7782))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0113
    (state : Fin 7782)
    (lower : 7232 ≤ state.val)
    (upper : state.val < 7296)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4022Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 7232, by omega⟩
  have state_eq :
      (⟨7232 + offset.val, by omega⟩ : Fin 7782) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0113 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0114 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.transition (⟨7296 + candidate.val, by omega⟩ : Fin 7782) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4022Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel (⟨7296 + candidate.val, by omega⟩ : Fin 7782))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0114
    (state : Fin 7782)
    (lower : 7296 ≤ state.val)
    (upper : state.val < 7360)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4022Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 7296, by omega⟩
  have state_eq :
      (⟨7296 + offset.val, by omega⟩ : Fin 7782) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0114 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0115 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.transition (⟨7360 + candidate.val, by omega⟩ : Fin 7782) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4022Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel (⟨7360 + candidate.val, by omega⟩ : Fin 7782))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0115
    (state : Fin 7782)
    (lower : 7360 ≤ state.val)
    (upper : state.val < 7424)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4022Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 7360, by omega⟩
  have state_eq :
      (⟨7360 + offset.val, by omega⟩ : Fin 7782) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0115 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0116 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.transition (⟨7424 + candidate.val, by omega⟩ : Fin 7782) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4022Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel (⟨7424 + candidate.val, by omega⟩ : Fin 7782))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0116
    (state : Fin 7782)
    (lower : 7424 ≤ state.val)
    (upper : state.val < 7488)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4022Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 7424, by omega⟩
  have state_eq :
      (⟨7424 + offset.val, by omega⟩ : Fin 7782) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0116 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0117 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.transition (⟨7488 + candidate.val, by omega⟩ : Fin 7782) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4022Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel (⟨7488 + candidate.val, by omega⟩ : Fin 7782))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0117
    (state : Fin 7782)
    (lower : 7488 ≤ state.val)
    (upper : state.val < 7552)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4022Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 7488, by omega⟩
  have state_eq :
      (⟨7488 + offset.val, by omega⟩ : Fin 7782) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0117 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0118 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.transition (⟨7552 + candidate.val, by omega⟩ : Fin 7782) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4022Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel (⟨7552 + candidate.val, by omega⟩ : Fin 7782))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0118
    (state : Fin 7782)
    (lower : 7552 ≤ state.val)
    (upper : state.val < 7616)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4022Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 7552, by omega⟩
  have state_eq :
      (⟨7552 + offset.val, by omega⟩ : Fin 7782) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0118 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0119 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.transition (⟨7616 + candidate.val, by omega⟩ : Fin 7782) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4022Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel (⟨7616 + candidate.val, by omega⟩ : Fin 7782))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0119
    (state : Fin 7782)
    (lower : 7616 ≤ state.val)
    (upper : state.val < 7680)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4022Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 7616, by omega⟩
  have state_eq :
      (⟨7616 + offset.val, by omega⟩ : Fin 7782) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0119 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0120 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.transition (⟨7680 + candidate.val, by omega⟩ : Fin 7782) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4022Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel (⟨7680 + candidate.val, by omega⟩ : Fin 7782))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0120
    (state : Fin 7782)
    (lower : 7680 ≤ state.val)
    (upper : state.val < 7744)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4022Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 7680, by omega⟩
  have state_eq :
      (⟨7680 + offset.val, by omega⟩ : Fin 7782) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0120 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0121 :
    ∀ candidate : Fin 38,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.transition (⟨7744 + candidate.val, by omega⟩ : Fin 7782) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4022Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel (⟨7744 + candidate.val, by omega⟩ : Fin 7782))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0121
    (state : Fin 7782)
    (lower : 7744 ≤ state.val)
    (upper : state.val < 7782)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4022Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.generatorSourceLabel generator) := by
  let offset : Fin 38 := ⟨state.val - 7744, by omega⟩
  have state_eq :
      (⟨7744 + offset.val, by omega⟩ : Fin 7782) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0121 offset generator

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.Shards
