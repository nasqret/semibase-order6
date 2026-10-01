import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.Support.Core
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.Shards

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0064 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition (⟨4096 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (⟨4096 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0064
    (state : Fin 18432)
    (lower : 4096 ≤ state.val)
    (upper : state.val < 4160)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 4096, by omega⟩
  have state_eq :
      (⟨4096 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0064 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0065 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition (⟨4160 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (⟨4160 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0065
    (state : Fin 18432)
    (lower : 4160 ≤ state.val)
    (upper : state.val < 4224)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 4160, by omega⟩
  have state_eq :
      (⟨4160 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0065 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0066 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition (⟨4224 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (⟨4224 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0066
    (state : Fin 18432)
    (lower : 4224 ≤ state.val)
    (upper : state.val < 4288)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 4224, by omega⟩
  have state_eq :
      (⟨4224 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0066 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0067 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition (⟨4288 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (⟨4288 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0067
    (state : Fin 18432)
    (lower : 4288 ≤ state.val)
    (upper : state.val < 4352)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 4288, by omega⟩
  have state_eq :
      (⟨4288 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0067 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0068 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition (⟨4352 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (⟨4352 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0068
    (state : Fin 18432)
    (lower : 4352 ≤ state.val)
    (upper : state.val < 4416)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 4352, by omega⟩
  have state_eq :
      (⟨4352 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0068 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0069 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition (⟨4416 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (⟨4416 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0069
    (state : Fin 18432)
    (lower : 4416 ≤ state.val)
    (upper : state.val < 4480)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 4416, by omega⟩
  have state_eq :
      (⟨4416 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0069 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0070 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition (⟨4480 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (⟨4480 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0070
    (state : Fin 18432)
    (lower : 4480 ≤ state.val)
    (upper : state.val < 4544)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 4480, by omega⟩
  have state_eq :
      (⟨4480 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0070 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0071 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition (⟨4544 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (⟨4544 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0071
    (state : Fin 18432)
    (lower : 4544 ≤ state.val)
    (upper : state.val < 4608)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 4544, by omega⟩
  have state_eq :
      (⟨4544 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0071 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0072 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition (⟨4608 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (⟨4608 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0072
    (state : Fin 18432)
    (lower : 4608 ≤ state.val)
    (upper : state.val < 4672)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 4608, by omega⟩
  have state_eq :
      (⟨4608 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0072 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0073 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition (⟨4672 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (⟨4672 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0073
    (state : Fin 18432)
    (lower : 4672 ≤ state.val)
    (upper : state.val < 4736)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 4672, by omega⟩
  have state_eq :
      (⟨4672 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0073 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0074 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition (⟨4736 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (⟨4736 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0074
    (state : Fin 18432)
    (lower : 4736 ≤ state.val)
    (upper : state.val < 4800)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 4736, by omega⟩
  have state_eq :
      (⟨4736 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0074 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0075 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition (⟨4800 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (⟨4800 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0075
    (state : Fin 18432)
    (lower : 4800 ≤ state.val)
    (upper : state.val < 4864)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 4800, by omega⟩
  have state_eq :
      (⟨4800 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0075 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0076 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition (⟨4864 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (⟨4864 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0076
    (state : Fin 18432)
    (lower : 4864 ≤ state.val)
    (upper : state.val < 4928)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 4864, by omega⟩
  have state_eq :
      (⟨4864 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0076 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0077 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition (⟨4928 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (⟨4928 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0077
    (state : Fin 18432)
    (lower : 4928 ≤ state.val)
    (upper : state.val < 4992)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 4928, by omega⟩
  have state_eq :
      (⟨4928 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0077 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0078 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition (⟨4992 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (⟨4992 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0078
    (state : Fin 18432)
    (lower : 4992 ≤ state.val)
    (upper : state.val < 5056)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 4992, by omega⟩
  have state_eq :
      (⟨4992 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0078 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0079 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition (⟨5056 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (⟨5056 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0079
    (state : Fin 18432)
    (lower : 5056 ≤ state.val)
    (upper : state.val < 5120)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 5056, by omega⟩
  have state_eq :
      (⟨5056 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0079 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0080 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition (⟨5120 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (⟨5120 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0080
    (state : Fin 18432)
    (lower : 5120 ≤ state.val)
    (upper : state.val < 5184)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 5120, by omega⟩
  have state_eq :
      (⟨5120 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0080 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0081 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition (⟨5184 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (⟨5184 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0081
    (state : Fin 18432)
    (lower : 5184 ≤ state.val)
    (upper : state.val < 5248)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 5184, by omega⟩
  have state_eq :
      (⟨5184 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0081 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0082 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition (⟨5248 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (⟨5248 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0082
    (state : Fin 18432)
    (lower : 5248 ≤ state.val)
    (upper : state.val < 5312)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 5248, by omega⟩
  have state_eq :
      (⟨5248 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0082 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0083 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition (⟨5312 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (⟨5312 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0083
    (state : Fin 18432)
    (lower : 5312 ≤ state.val)
    (upper : state.val < 5376)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 5312, by omega⟩
  have state_eq :
      (⟨5312 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0083 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0084 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition (⟨5376 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (⟨5376 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0084
    (state : Fin 18432)
    (lower : 5376 ≤ state.val)
    (upper : state.val < 5440)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 5376, by omega⟩
  have state_eq :
      (⟨5376 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0084 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0085 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition (⟨5440 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (⟨5440 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0085
    (state : Fin 18432)
    (lower : 5440 ≤ state.val)
    (upper : state.val < 5504)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 5440, by omega⟩
  have state_eq :
      (⟨5440 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0085 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0086 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition (⟨5504 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (⟨5504 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0086
    (state : Fin 18432)
    (lower : 5504 ≤ state.val)
    (upper : state.val < 5568)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 5504, by omega⟩
  have state_eq :
      (⟨5504 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0086 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0087 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition (⟨5568 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (⟨5568 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0087
    (state : Fin 18432)
    (lower : 5568 ≤ state.val)
    (upper : state.val < 5632)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 5568, by omega⟩
  have state_eq :
      (⟨5568 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0087 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0088 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition (⟨5632 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (⟨5632 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0088
    (state : Fin 18432)
    (lower : 5632 ≤ state.val)
    (upper : state.val < 5696)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 5632, by omega⟩
  have state_eq :
      (⟨5632 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0088 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0089 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition (⟨5696 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (⟨5696 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0089
    (state : Fin 18432)
    (lower : 5696 ≤ state.val)
    (upper : state.val < 5760)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 5696, by omega⟩
  have state_eq :
      (⟨5696 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0089 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0090 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition (⟨5760 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (⟨5760 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0090
    (state : Fin 18432)
    (lower : 5760 ≤ state.val)
    (upper : state.val < 5824)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 5760, by omega⟩
  have state_eq :
      (⟨5760 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0090 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0091 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition (⟨5824 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (⟨5824 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0091
    (state : Fin 18432)
    (lower : 5824 ≤ state.val)
    (upper : state.val < 5888)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 5824, by omega⟩
  have state_eq :
      (⟨5824 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0091 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0092 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition (⟨5888 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (⟨5888 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0092
    (state : Fin 18432)
    (lower : 5888 ≤ state.val)
    (upper : state.val < 5952)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 5888, by omega⟩
  have state_eq :
      (⟨5888 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0092 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0093 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition (⟨5952 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (⟨5952 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0093
    (state : Fin 18432)
    (lower : 5952 ≤ state.val)
    (upper : state.val < 6016)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 5952, by omega⟩
  have state_eq :
      (⟨5952 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0093 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0094 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition (⟨6016 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (⟨6016 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0094
    (state : Fin 18432)
    (lower : 6016 ≤ state.val)
    (upper : state.val < 6080)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 6016, by omega⟩
  have state_eq :
      (⟨6016 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0094 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0095 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition (⟨6080 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (⟨6080 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0095
    (state : Fin 18432)
    (lower : 6080 ≤ state.val)
    (upper : state.val < 6144)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 6080, by omega⟩
  have state_eq :
      (⟨6080 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0095 offset generator

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.Shards
