import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.Support.Core
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.Shards

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0160 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.transition (⟨10240 + candidate.val, by omega⟩ : Fin 11742) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel (⟨10240 + candidate.val, by omega⟩ : Fin 11742))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0160
    (state : Fin 11742)
    (lower : 10240 ≤ state.val)
    (upper : state.val < 10304)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 10240, by omega⟩
  have state_eq :
      (⟨10240 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0160 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0161 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.transition (⟨10304 + candidate.val, by omega⟩ : Fin 11742) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel (⟨10304 + candidate.val, by omega⟩ : Fin 11742))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0161
    (state : Fin 11742)
    (lower : 10304 ≤ state.val)
    (upper : state.val < 10368)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 10304, by omega⟩
  have state_eq :
      (⟨10304 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0161 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0162 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.transition (⟨10368 + candidate.val, by omega⟩ : Fin 11742) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel (⟨10368 + candidate.val, by omega⟩ : Fin 11742))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0162
    (state : Fin 11742)
    (lower : 10368 ≤ state.val)
    (upper : state.val < 10432)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 10368, by omega⟩
  have state_eq :
      (⟨10368 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0162 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0163 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.transition (⟨10432 + candidate.val, by omega⟩ : Fin 11742) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel (⟨10432 + candidate.val, by omega⟩ : Fin 11742))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0163
    (state : Fin 11742)
    (lower : 10432 ≤ state.val)
    (upper : state.val < 10496)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 10432, by omega⟩
  have state_eq :
      (⟨10432 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0163 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0164 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.transition (⟨10496 + candidate.val, by omega⟩ : Fin 11742) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel (⟨10496 + candidate.val, by omega⟩ : Fin 11742))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0164
    (state : Fin 11742)
    (lower : 10496 ≤ state.val)
    (upper : state.val < 10560)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 10496, by omega⟩
  have state_eq :
      (⟨10496 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0164 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0165 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.transition (⟨10560 + candidate.val, by omega⟩ : Fin 11742) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel (⟨10560 + candidate.val, by omega⟩ : Fin 11742))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0165
    (state : Fin 11742)
    (lower : 10560 ≤ state.val)
    (upper : state.val < 10624)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 10560, by omega⟩
  have state_eq :
      (⟨10560 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0165 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0166 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.transition (⟨10624 + candidate.val, by omega⟩ : Fin 11742) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel (⟨10624 + candidate.val, by omega⟩ : Fin 11742))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0166
    (state : Fin 11742)
    (lower : 10624 ≤ state.val)
    (upper : state.val < 10688)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 10624, by omega⟩
  have state_eq :
      (⟨10624 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0166 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0167 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.transition (⟨10688 + candidate.val, by omega⟩ : Fin 11742) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel (⟨10688 + candidate.val, by omega⟩ : Fin 11742))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0167
    (state : Fin 11742)
    (lower : 10688 ≤ state.val)
    (upper : state.val < 10752)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 10688, by omega⟩
  have state_eq :
      (⟨10688 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0167 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0168 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.transition (⟨10752 + candidate.val, by omega⟩ : Fin 11742) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel (⟨10752 + candidate.val, by omega⟩ : Fin 11742))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0168
    (state : Fin 11742)
    (lower : 10752 ≤ state.val)
    (upper : state.val < 10816)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 10752, by omega⟩
  have state_eq :
      (⟨10752 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0168 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0169 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.transition (⟨10816 + candidate.val, by omega⟩ : Fin 11742) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel (⟨10816 + candidate.val, by omega⟩ : Fin 11742))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0169
    (state : Fin 11742)
    (lower : 10816 ≤ state.val)
    (upper : state.val < 10880)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 10816, by omega⟩
  have state_eq :
      (⟨10816 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0169 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0170 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.transition (⟨10880 + candidate.val, by omega⟩ : Fin 11742) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel (⟨10880 + candidate.val, by omega⟩ : Fin 11742))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0170
    (state : Fin 11742)
    (lower : 10880 ≤ state.val)
    (upper : state.val < 10944)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 10880, by omega⟩
  have state_eq :
      (⟨10880 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0170 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0171 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.transition (⟨10944 + candidate.val, by omega⟩ : Fin 11742) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel (⟨10944 + candidate.val, by omega⟩ : Fin 11742))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0171
    (state : Fin 11742)
    (lower : 10944 ≤ state.val)
    (upper : state.val < 11008)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 10944, by omega⟩
  have state_eq :
      (⟨10944 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0171 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0172 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.transition (⟨11008 + candidate.val, by omega⟩ : Fin 11742) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel (⟨11008 + candidate.val, by omega⟩ : Fin 11742))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0172
    (state : Fin 11742)
    (lower : 11008 ≤ state.val)
    (upper : state.val < 11072)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 11008, by omega⟩
  have state_eq :
      (⟨11008 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0172 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0173 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.transition (⟨11072 + candidate.val, by omega⟩ : Fin 11742) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel (⟨11072 + candidate.val, by omega⟩ : Fin 11742))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0173
    (state : Fin 11742)
    (lower : 11072 ≤ state.val)
    (upper : state.val < 11136)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 11072, by omega⟩
  have state_eq :
      (⟨11072 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0173 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0174 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.transition (⟨11136 + candidate.val, by omega⟩ : Fin 11742) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel (⟨11136 + candidate.val, by omega⟩ : Fin 11742))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0174
    (state : Fin 11742)
    (lower : 11136 ≤ state.val)
    (upper : state.val < 11200)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 11136, by omega⟩
  have state_eq :
      (⟨11136 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0174 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0175 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.transition (⟨11200 + candidate.val, by omega⟩ : Fin 11742) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel (⟨11200 + candidate.val, by omega⟩ : Fin 11742))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0175
    (state : Fin 11742)
    (lower : 11200 ≤ state.val)
    (upper : state.val < 11264)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 11200, by omega⟩
  have state_eq :
      (⟨11200 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0175 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0176 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.transition (⟨11264 + candidate.val, by omega⟩ : Fin 11742) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel (⟨11264 + candidate.val, by omega⟩ : Fin 11742))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0176
    (state : Fin 11742)
    (lower : 11264 ≤ state.val)
    (upper : state.val < 11328)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 11264, by omega⟩
  have state_eq :
      (⟨11264 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0176 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0177 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.transition (⟨11328 + candidate.val, by omega⟩ : Fin 11742) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel (⟨11328 + candidate.val, by omega⟩ : Fin 11742))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0177
    (state : Fin 11742)
    (lower : 11328 ≤ state.val)
    (upper : state.val < 11392)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 11328, by omega⟩
  have state_eq :
      (⟨11328 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0177 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0178 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.transition (⟨11392 + candidate.val, by omega⟩ : Fin 11742) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel (⟨11392 + candidate.val, by omega⟩ : Fin 11742))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0178
    (state : Fin 11742)
    (lower : 11392 ≤ state.val)
    (upper : state.val < 11456)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 11392, by omega⟩
  have state_eq :
      (⟨11392 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0178 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0179 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.transition (⟨11456 + candidate.val, by omega⟩ : Fin 11742) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel (⟨11456 + candidate.val, by omega⟩ : Fin 11742))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0179
    (state : Fin 11742)
    (lower : 11456 ≤ state.val)
    (upper : state.val < 11520)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 11456, by omega⟩
  have state_eq :
      (⟨11456 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0179 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0180 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.transition (⟨11520 + candidate.val, by omega⟩ : Fin 11742) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel (⟨11520 + candidate.val, by omega⟩ : Fin 11742))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0180
    (state : Fin 11742)
    (lower : 11520 ≤ state.val)
    (upper : state.val < 11584)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 11520, by omega⟩
  have state_eq :
      (⟨11520 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0180 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0181 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.transition (⟨11584 + candidate.val, by omega⟩ : Fin 11742) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel (⟨11584 + candidate.val, by omega⟩ : Fin 11742))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0181
    (state : Fin 11742)
    (lower : 11584 ≤ state.val)
    (upper : state.val < 11648)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 11584, by omega⟩
  have state_eq :
      (⟨11584 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0181 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0182 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.transition (⟨11648 + candidate.val, by omega⟩ : Fin 11742) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel (⟨11648 + candidate.val, by omega⟩ : Fin 11742))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0182
    (state : Fin 11742)
    (lower : 11648 ≤ state.val)
    (upper : state.val < 11712)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 11648, by omega⟩
  have state_eq :
      (⟨11648 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0182 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0183 :
    ∀ candidate : Fin 30,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.transition (⟨11712 + candidate.val, by omega⟩ : Fin 11742) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel (⟨11712 + candidate.val, by omega⟩ : Fin 11742))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0183
    (state : Fin 11742)
    (lower : 11712 ≤ state.val)
    (upper : state.val < 11742)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.generatorSourceLabel generator) := by
  let offset : Fin 30 := ⟨state.val - 11712, by omega⟩
  have state_eq :
      (⟨11712 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0183 offset generator

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.Shards
