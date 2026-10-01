import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.Support.Core
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.Shards

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0128 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition (⟨8192 + candidate.val, by omega⟩ : Fin 11742) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel (⟨8192 + candidate.val, by omega⟩ : Fin 11742))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0128
    (state : Fin 11742)
    (lower : 8192 ≤ state.val)
    (upper : state.val < 8256)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 8192, by omega⟩
  have state_eq :
      (⟨8192 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0128 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0129 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition (⟨8256 + candidate.val, by omega⟩ : Fin 11742) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel (⟨8256 + candidate.val, by omega⟩ : Fin 11742))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0129
    (state : Fin 11742)
    (lower : 8256 ≤ state.val)
    (upper : state.val < 8320)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 8256, by omega⟩
  have state_eq :
      (⟨8256 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0129 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0130 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition (⟨8320 + candidate.val, by omega⟩ : Fin 11742) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel (⟨8320 + candidate.val, by omega⟩ : Fin 11742))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0130
    (state : Fin 11742)
    (lower : 8320 ≤ state.val)
    (upper : state.val < 8384)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 8320, by omega⟩
  have state_eq :
      (⟨8320 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0130 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0131 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition (⟨8384 + candidate.val, by omega⟩ : Fin 11742) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel (⟨8384 + candidate.val, by omega⟩ : Fin 11742))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0131
    (state : Fin 11742)
    (lower : 8384 ≤ state.val)
    (upper : state.val < 8448)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 8384, by omega⟩
  have state_eq :
      (⟨8384 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0131 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0132 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition (⟨8448 + candidate.val, by omega⟩ : Fin 11742) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel (⟨8448 + candidate.val, by omega⟩ : Fin 11742))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0132
    (state : Fin 11742)
    (lower : 8448 ≤ state.val)
    (upper : state.val < 8512)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 8448, by omega⟩
  have state_eq :
      (⟨8448 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0132 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0133 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition (⟨8512 + candidate.val, by omega⟩ : Fin 11742) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel (⟨8512 + candidate.val, by omega⟩ : Fin 11742))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0133
    (state : Fin 11742)
    (lower : 8512 ≤ state.val)
    (upper : state.val < 8576)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 8512, by omega⟩
  have state_eq :
      (⟨8512 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0133 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0134 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition (⟨8576 + candidate.val, by omega⟩ : Fin 11742) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel (⟨8576 + candidate.val, by omega⟩ : Fin 11742))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0134
    (state : Fin 11742)
    (lower : 8576 ≤ state.val)
    (upper : state.val < 8640)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 8576, by omega⟩
  have state_eq :
      (⟨8576 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0134 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0135 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition (⟨8640 + candidate.val, by omega⟩ : Fin 11742) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel (⟨8640 + candidate.val, by omega⟩ : Fin 11742))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0135
    (state : Fin 11742)
    (lower : 8640 ≤ state.val)
    (upper : state.val < 8704)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 8640, by omega⟩
  have state_eq :
      (⟨8640 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0135 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0136 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition (⟨8704 + candidate.val, by omega⟩ : Fin 11742) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel (⟨8704 + candidate.val, by omega⟩ : Fin 11742))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0136
    (state : Fin 11742)
    (lower : 8704 ≤ state.val)
    (upper : state.val < 8768)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 8704, by omega⟩
  have state_eq :
      (⟨8704 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0136 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0137 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition (⟨8768 + candidate.val, by omega⟩ : Fin 11742) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel (⟨8768 + candidate.val, by omega⟩ : Fin 11742))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0137
    (state : Fin 11742)
    (lower : 8768 ≤ state.val)
    (upper : state.val < 8832)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 8768, by omega⟩
  have state_eq :
      (⟨8768 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0137 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0138 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition (⟨8832 + candidate.val, by omega⟩ : Fin 11742) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel (⟨8832 + candidate.val, by omega⟩ : Fin 11742))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0138
    (state : Fin 11742)
    (lower : 8832 ≤ state.val)
    (upper : state.val < 8896)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 8832, by omega⟩
  have state_eq :
      (⟨8832 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0138 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0139 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition (⟨8896 + candidate.val, by omega⟩ : Fin 11742) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel (⟨8896 + candidate.val, by omega⟩ : Fin 11742))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0139
    (state : Fin 11742)
    (lower : 8896 ≤ state.val)
    (upper : state.val < 8960)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 8896, by omega⟩
  have state_eq :
      (⟨8896 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0139 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0140 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition (⟨8960 + candidate.val, by omega⟩ : Fin 11742) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel (⟨8960 + candidate.val, by omega⟩ : Fin 11742))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0140
    (state : Fin 11742)
    (lower : 8960 ≤ state.val)
    (upper : state.val < 9024)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 8960, by omega⟩
  have state_eq :
      (⟨8960 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0140 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0141 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition (⟨9024 + candidate.val, by omega⟩ : Fin 11742) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel (⟨9024 + candidate.val, by omega⟩ : Fin 11742))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0141
    (state : Fin 11742)
    (lower : 9024 ≤ state.val)
    (upper : state.val < 9088)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 9024, by omega⟩
  have state_eq :
      (⟨9024 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0141 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0142 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition (⟨9088 + candidate.val, by omega⟩ : Fin 11742) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel (⟨9088 + candidate.val, by omega⟩ : Fin 11742))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0142
    (state : Fin 11742)
    (lower : 9088 ≤ state.val)
    (upper : state.val < 9152)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 9088, by omega⟩
  have state_eq :
      (⟨9088 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0142 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0143 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition (⟨9152 + candidate.val, by omega⟩ : Fin 11742) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel (⟨9152 + candidate.val, by omega⟩ : Fin 11742))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0143
    (state : Fin 11742)
    (lower : 9152 ≤ state.val)
    (upper : state.val < 9216)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 9152, by omega⟩
  have state_eq :
      (⟨9152 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0143 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0144 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition (⟨9216 + candidate.val, by omega⟩ : Fin 11742) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel (⟨9216 + candidate.val, by omega⟩ : Fin 11742))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0144
    (state : Fin 11742)
    (lower : 9216 ≤ state.val)
    (upper : state.val < 9280)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 9216, by omega⟩
  have state_eq :
      (⟨9216 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0144 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0145 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition (⟨9280 + candidate.val, by omega⟩ : Fin 11742) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel (⟨9280 + candidate.val, by omega⟩ : Fin 11742))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0145
    (state : Fin 11742)
    (lower : 9280 ≤ state.val)
    (upper : state.val < 9344)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 9280, by omega⟩
  have state_eq :
      (⟨9280 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0145 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0146 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition (⟨9344 + candidate.val, by omega⟩ : Fin 11742) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel (⟨9344 + candidate.val, by omega⟩ : Fin 11742))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0146
    (state : Fin 11742)
    (lower : 9344 ≤ state.val)
    (upper : state.val < 9408)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 9344, by omega⟩
  have state_eq :
      (⟨9344 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0146 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0147 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition (⟨9408 + candidate.val, by omega⟩ : Fin 11742) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel (⟨9408 + candidate.val, by omega⟩ : Fin 11742))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0147
    (state : Fin 11742)
    (lower : 9408 ≤ state.val)
    (upper : state.val < 9472)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 9408, by omega⟩
  have state_eq :
      (⟨9408 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0147 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0148 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition (⟨9472 + candidate.val, by omega⟩ : Fin 11742) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel (⟨9472 + candidate.val, by omega⟩ : Fin 11742))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0148
    (state : Fin 11742)
    (lower : 9472 ≤ state.val)
    (upper : state.val < 9536)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 9472, by omega⟩
  have state_eq :
      (⟨9472 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0148 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0149 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition (⟨9536 + candidate.val, by omega⟩ : Fin 11742) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel (⟨9536 + candidate.val, by omega⟩ : Fin 11742))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0149
    (state : Fin 11742)
    (lower : 9536 ≤ state.val)
    (upper : state.val < 9600)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 9536, by omega⟩
  have state_eq :
      (⟨9536 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0149 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0150 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition (⟨9600 + candidate.val, by omega⟩ : Fin 11742) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel (⟨9600 + candidate.val, by omega⟩ : Fin 11742))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0150
    (state : Fin 11742)
    (lower : 9600 ≤ state.val)
    (upper : state.val < 9664)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 9600, by omega⟩
  have state_eq :
      (⟨9600 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0150 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0151 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition (⟨9664 + candidate.val, by omega⟩ : Fin 11742) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel (⟨9664 + candidate.val, by omega⟩ : Fin 11742))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0151
    (state : Fin 11742)
    (lower : 9664 ≤ state.val)
    (upper : state.val < 9728)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 9664, by omega⟩
  have state_eq :
      (⟨9664 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0151 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0152 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition (⟨9728 + candidate.val, by omega⟩ : Fin 11742) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel (⟨9728 + candidate.val, by omega⟩ : Fin 11742))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0152
    (state : Fin 11742)
    (lower : 9728 ≤ state.val)
    (upper : state.val < 9792)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 9728, by omega⟩
  have state_eq :
      (⟨9728 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0152 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0153 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition (⟨9792 + candidate.val, by omega⟩ : Fin 11742) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel (⟨9792 + candidate.val, by omega⟩ : Fin 11742))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0153
    (state : Fin 11742)
    (lower : 9792 ≤ state.val)
    (upper : state.val < 9856)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 9792, by omega⟩
  have state_eq :
      (⟨9792 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0153 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0154 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition (⟨9856 + candidate.val, by omega⟩ : Fin 11742) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel (⟨9856 + candidate.val, by omega⟩ : Fin 11742))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0154
    (state : Fin 11742)
    (lower : 9856 ≤ state.val)
    (upper : state.val < 9920)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 9856, by omega⟩
  have state_eq :
      (⟨9856 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0154 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0155 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition (⟨9920 + candidate.val, by omega⟩ : Fin 11742) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel (⟨9920 + candidate.val, by omega⟩ : Fin 11742))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0155
    (state : Fin 11742)
    (lower : 9920 ≤ state.val)
    (upper : state.val < 9984)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 9920, by omega⟩
  have state_eq :
      (⟨9920 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0155 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0156 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition (⟨9984 + candidate.val, by omega⟩ : Fin 11742) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel (⟨9984 + candidate.val, by omega⟩ : Fin 11742))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0156
    (state : Fin 11742)
    (lower : 9984 ≤ state.val)
    (upper : state.val < 10048)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 9984, by omega⟩
  have state_eq :
      (⟨9984 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0156 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0157 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition (⟨10048 + candidate.val, by omega⟩ : Fin 11742) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel (⟨10048 + candidate.val, by omega⟩ : Fin 11742))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0157
    (state : Fin 11742)
    (lower : 10048 ≤ state.val)
    (upper : state.val < 10112)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 10048, by omega⟩
  have state_eq :
      (⟨10048 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0157 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0158 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition (⟨10112 + candidate.val, by omega⟩ : Fin 11742) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel (⟨10112 + candidate.val, by omega⟩ : Fin 11742))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0158
    (state : Fin 11742)
    (lower : 10112 ≤ state.val)
    (upper : state.val < 10176)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 10112, by omega⟩
  have state_eq :
      (⟨10112 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0158 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0159 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition (⟨10176 + candidate.val, by omega⟩ : Fin 11742) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel (⟨10176 + candidate.val, by omega⟩ : Fin 11742))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0159
    (state : Fin 11742)
    (lower : 10176 ≤ state.val)
    (upper : state.val < 10240)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 10176, by omega⟩
  have state_eq :
      (⟨10176 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0159 offset generator

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.Shards
