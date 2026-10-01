import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.Support.Core
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.Shards

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0032 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition (⟨2048 + candidate.val, by omega⟩ : Fin 17622) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel (⟨2048 + candidate.val, by omega⟩ : Fin 17622))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0032
    (state : Fin 17622)
    (lower : 2048 ≤ state.val)
    (upper : state.val < 2112)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 2048, by omega⟩
  have state_eq :
      (⟨2048 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0032 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0033 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition (⟨2112 + candidate.val, by omega⟩ : Fin 17622) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel (⟨2112 + candidate.val, by omega⟩ : Fin 17622))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0033
    (state : Fin 17622)
    (lower : 2112 ≤ state.val)
    (upper : state.val < 2176)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 2112, by omega⟩
  have state_eq :
      (⟨2112 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0033 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0034 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition (⟨2176 + candidate.val, by omega⟩ : Fin 17622) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel (⟨2176 + candidate.val, by omega⟩ : Fin 17622))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0034
    (state : Fin 17622)
    (lower : 2176 ≤ state.val)
    (upper : state.val < 2240)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 2176, by omega⟩
  have state_eq :
      (⟨2176 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0034 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0035 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition (⟨2240 + candidate.val, by omega⟩ : Fin 17622) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel (⟨2240 + candidate.val, by omega⟩ : Fin 17622))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0035
    (state : Fin 17622)
    (lower : 2240 ≤ state.val)
    (upper : state.val < 2304)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 2240, by omega⟩
  have state_eq :
      (⟨2240 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0035 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0036 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition (⟨2304 + candidate.val, by omega⟩ : Fin 17622) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel (⟨2304 + candidate.val, by omega⟩ : Fin 17622))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0036
    (state : Fin 17622)
    (lower : 2304 ≤ state.val)
    (upper : state.val < 2368)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 2304, by omega⟩
  have state_eq :
      (⟨2304 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0036 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0037 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition (⟨2368 + candidate.val, by omega⟩ : Fin 17622) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel (⟨2368 + candidate.val, by omega⟩ : Fin 17622))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0037
    (state : Fin 17622)
    (lower : 2368 ≤ state.val)
    (upper : state.val < 2432)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 2368, by omega⟩
  have state_eq :
      (⟨2368 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0037 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0038 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition (⟨2432 + candidate.val, by omega⟩ : Fin 17622) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel (⟨2432 + candidate.val, by omega⟩ : Fin 17622))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0038
    (state : Fin 17622)
    (lower : 2432 ≤ state.val)
    (upper : state.val < 2496)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 2432, by omega⟩
  have state_eq :
      (⟨2432 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0038 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0039 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition (⟨2496 + candidate.val, by omega⟩ : Fin 17622) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel (⟨2496 + candidate.val, by omega⟩ : Fin 17622))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0039
    (state : Fin 17622)
    (lower : 2496 ≤ state.val)
    (upper : state.val < 2560)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 2496, by omega⟩
  have state_eq :
      (⟨2496 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0039 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0040 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition (⟨2560 + candidate.val, by omega⟩ : Fin 17622) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel (⟨2560 + candidate.val, by omega⟩ : Fin 17622))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0040
    (state : Fin 17622)
    (lower : 2560 ≤ state.val)
    (upper : state.val < 2624)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 2560, by omega⟩
  have state_eq :
      (⟨2560 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0040 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0041 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition (⟨2624 + candidate.val, by omega⟩ : Fin 17622) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel (⟨2624 + candidate.val, by omega⟩ : Fin 17622))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0041
    (state : Fin 17622)
    (lower : 2624 ≤ state.val)
    (upper : state.val < 2688)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 2624, by omega⟩
  have state_eq :
      (⟨2624 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0041 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0042 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition (⟨2688 + candidate.val, by omega⟩ : Fin 17622) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel (⟨2688 + candidate.val, by omega⟩ : Fin 17622))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0042
    (state : Fin 17622)
    (lower : 2688 ≤ state.val)
    (upper : state.val < 2752)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 2688, by omega⟩
  have state_eq :
      (⟨2688 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0042 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0043 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition (⟨2752 + candidate.val, by omega⟩ : Fin 17622) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel (⟨2752 + candidate.val, by omega⟩ : Fin 17622))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0043
    (state : Fin 17622)
    (lower : 2752 ≤ state.val)
    (upper : state.val < 2816)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 2752, by omega⟩
  have state_eq :
      (⟨2752 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0043 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0044 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition (⟨2816 + candidate.val, by omega⟩ : Fin 17622) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel (⟨2816 + candidate.val, by omega⟩ : Fin 17622))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0044
    (state : Fin 17622)
    (lower : 2816 ≤ state.val)
    (upper : state.val < 2880)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 2816, by omega⟩
  have state_eq :
      (⟨2816 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0044 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0045 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition (⟨2880 + candidate.val, by omega⟩ : Fin 17622) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel (⟨2880 + candidate.val, by omega⟩ : Fin 17622))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0045
    (state : Fin 17622)
    (lower : 2880 ≤ state.val)
    (upper : state.val < 2944)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 2880, by omega⟩
  have state_eq :
      (⟨2880 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0045 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0046 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition (⟨2944 + candidate.val, by omega⟩ : Fin 17622) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel (⟨2944 + candidate.val, by omega⟩ : Fin 17622))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0046
    (state : Fin 17622)
    (lower : 2944 ≤ state.val)
    (upper : state.val < 3008)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 2944, by omega⟩
  have state_eq :
      (⟨2944 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0046 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0047 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition (⟨3008 + candidate.val, by omega⟩ : Fin 17622) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel (⟨3008 + candidate.val, by omega⟩ : Fin 17622))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0047
    (state : Fin 17622)
    (lower : 3008 ≤ state.val)
    (upper : state.val < 3072)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 3008, by omega⟩
  have state_eq :
      (⟨3008 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0047 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0048 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition (⟨3072 + candidate.val, by omega⟩ : Fin 17622) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel (⟨3072 + candidate.val, by omega⟩ : Fin 17622))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0048
    (state : Fin 17622)
    (lower : 3072 ≤ state.val)
    (upper : state.val < 3136)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 3072, by omega⟩
  have state_eq :
      (⟨3072 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0048 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0049 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition (⟨3136 + candidate.val, by omega⟩ : Fin 17622) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel (⟨3136 + candidate.val, by omega⟩ : Fin 17622))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0049
    (state : Fin 17622)
    (lower : 3136 ≤ state.val)
    (upper : state.val < 3200)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 3136, by omega⟩
  have state_eq :
      (⟨3136 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0049 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0050 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition (⟨3200 + candidate.val, by omega⟩ : Fin 17622) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel (⟨3200 + candidate.val, by omega⟩ : Fin 17622))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0050
    (state : Fin 17622)
    (lower : 3200 ≤ state.val)
    (upper : state.val < 3264)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 3200, by omega⟩
  have state_eq :
      (⟨3200 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0050 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0051 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition (⟨3264 + candidate.val, by omega⟩ : Fin 17622) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel (⟨3264 + candidate.val, by omega⟩ : Fin 17622))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0051
    (state : Fin 17622)
    (lower : 3264 ≤ state.val)
    (upper : state.val < 3328)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 3264, by omega⟩
  have state_eq :
      (⟨3264 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0051 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0052 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition (⟨3328 + candidate.val, by omega⟩ : Fin 17622) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel (⟨3328 + candidate.val, by omega⟩ : Fin 17622))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0052
    (state : Fin 17622)
    (lower : 3328 ≤ state.val)
    (upper : state.val < 3392)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 3328, by omega⟩
  have state_eq :
      (⟨3328 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0052 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0053 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition (⟨3392 + candidate.val, by omega⟩ : Fin 17622) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel (⟨3392 + candidate.val, by omega⟩ : Fin 17622))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0053
    (state : Fin 17622)
    (lower : 3392 ≤ state.val)
    (upper : state.val < 3456)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 3392, by omega⟩
  have state_eq :
      (⟨3392 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0053 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0054 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition (⟨3456 + candidate.val, by omega⟩ : Fin 17622) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel (⟨3456 + candidate.val, by omega⟩ : Fin 17622))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0054
    (state : Fin 17622)
    (lower : 3456 ≤ state.val)
    (upper : state.val < 3520)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 3456, by omega⟩
  have state_eq :
      (⟨3456 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0054 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0055 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition (⟨3520 + candidate.val, by omega⟩ : Fin 17622) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel (⟨3520 + candidate.val, by omega⟩ : Fin 17622))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0055
    (state : Fin 17622)
    (lower : 3520 ≤ state.val)
    (upper : state.val < 3584)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 3520, by omega⟩
  have state_eq :
      (⟨3520 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0055 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0056 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition (⟨3584 + candidate.val, by omega⟩ : Fin 17622) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel (⟨3584 + candidate.val, by omega⟩ : Fin 17622))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0056
    (state : Fin 17622)
    (lower : 3584 ≤ state.val)
    (upper : state.val < 3648)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 3584, by omega⟩
  have state_eq :
      (⟨3584 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0056 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0057 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition (⟨3648 + candidate.val, by omega⟩ : Fin 17622) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel (⟨3648 + candidate.val, by omega⟩ : Fin 17622))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0057
    (state : Fin 17622)
    (lower : 3648 ≤ state.val)
    (upper : state.val < 3712)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 3648, by omega⟩
  have state_eq :
      (⟨3648 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0057 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0058 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition (⟨3712 + candidate.val, by omega⟩ : Fin 17622) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel (⟨3712 + candidate.val, by omega⟩ : Fin 17622))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0058
    (state : Fin 17622)
    (lower : 3712 ≤ state.val)
    (upper : state.val < 3776)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 3712, by omega⟩
  have state_eq :
      (⟨3712 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0058 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0059 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition (⟨3776 + candidate.val, by omega⟩ : Fin 17622) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel (⟨3776 + candidate.val, by omega⟩ : Fin 17622))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0059
    (state : Fin 17622)
    (lower : 3776 ≤ state.val)
    (upper : state.val < 3840)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 3776, by omega⟩
  have state_eq :
      (⟨3776 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0059 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0060 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition (⟨3840 + candidate.val, by omega⟩ : Fin 17622) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel (⟨3840 + candidate.val, by omega⟩ : Fin 17622))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0060
    (state : Fin 17622)
    (lower : 3840 ≤ state.val)
    (upper : state.val < 3904)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 3840, by omega⟩
  have state_eq :
      (⟨3840 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0060 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0061 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition (⟨3904 + candidate.val, by omega⟩ : Fin 17622) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel (⟨3904 + candidate.val, by omega⟩ : Fin 17622))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0061
    (state : Fin 17622)
    (lower : 3904 ≤ state.val)
    (upper : state.val < 3968)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 3904, by omega⟩
  have state_eq :
      (⟨3904 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0061 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0062 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition (⟨3968 + candidate.val, by omega⟩ : Fin 17622) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel (⟨3968 + candidate.val, by omega⟩ : Fin 17622))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0062
    (state : Fin 17622)
    (lower : 3968 ≤ state.val)
    (upper : state.val < 4032)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 3968, by omega⟩
  have state_eq :
      (⟨3968 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0062 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0063 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition (⟨4032 + candidate.val, by omega⟩ : Fin 17622) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel (⟨4032 + candidate.val, by omega⟩ : Fin 17622))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0063
    (state : Fin 17622)
    (lower : 4032 ≤ state.val)
    (upper : state.val < 4096)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 4032, by omega⟩
  have state_eq :
      (⟨4032 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0063 offset generator

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.Shards
