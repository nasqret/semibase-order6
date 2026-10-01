import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.Support.Core
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.Shards

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0256 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.transition (⟨16384 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel (⟨16384 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0256
    (state : Fin 18432)
    (lower : 16384 ≤ state.val)
    (upper : state.val < 16448)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 16384, by omega⟩
  have state_eq :
      (⟨16384 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0256 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0257 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.transition (⟨16448 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel (⟨16448 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0257
    (state : Fin 18432)
    (lower : 16448 ≤ state.val)
    (upper : state.val < 16512)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 16448, by omega⟩
  have state_eq :
      (⟨16448 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0257 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0258 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.transition (⟨16512 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel (⟨16512 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0258
    (state : Fin 18432)
    (lower : 16512 ≤ state.val)
    (upper : state.val < 16576)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 16512, by omega⟩
  have state_eq :
      (⟨16512 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0258 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0259 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.transition (⟨16576 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel (⟨16576 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0259
    (state : Fin 18432)
    (lower : 16576 ≤ state.val)
    (upper : state.val < 16640)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 16576, by omega⟩
  have state_eq :
      (⟨16576 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0259 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0260 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.transition (⟨16640 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel (⟨16640 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0260
    (state : Fin 18432)
    (lower : 16640 ≤ state.val)
    (upper : state.val < 16704)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 16640, by omega⟩
  have state_eq :
      (⟨16640 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0260 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0261 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.transition (⟨16704 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel (⟨16704 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0261
    (state : Fin 18432)
    (lower : 16704 ≤ state.val)
    (upper : state.val < 16768)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 16704, by omega⟩
  have state_eq :
      (⟨16704 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0261 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0262 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.transition (⟨16768 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel (⟨16768 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0262
    (state : Fin 18432)
    (lower : 16768 ≤ state.val)
    (upper : state.val < 16832)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 16768, by omega⟩
  have state_eq :
      (⟨16768 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0262 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0263 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.transition (⟨16832 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel (⟨16832 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0263
    (state : Fin 18432)
    (lower : 16832 ≤ state.val)
    (upper : state.val < 16896)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 16832, by omega⟩
  have state_eq :
      (⟨16832 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0263 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0264 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.transition (⟨16896 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel (⟨16896 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0264
    (state : Fin 18432)
    (lower : 16896 ≤ state.val)
    (upper : state.val < 16960)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 16896, by omega⟩
  have state_eq :
      (⟨16896 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0264 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0265 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.transition (⟨16960 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel (⟨16960 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0265
    (state : Fin 18432)
    (lower : 16960 ≤ state.val)
    (upper : state.val < 17024)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 16960, by omega⟩
  have state_eq :
      (⟨16960 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0265 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0266 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.transition (⟨17024 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel (⟨17024 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0266
    (state : Fin 18432)
    (lower : 17024 ≤ state.val)
    (upper : state.val < 17088)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 17024, by omega⟩
  have state_eq :
      (⟨17024 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0266 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0267 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.transition (⟨17088 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel (⟨17088 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0267
    (state : Fin 18432)
    (lower : 17088 ≤ state.val)
    (upper : state.val < 17152)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 17088, by omega⟩
  have state_eq :
      (⟨17088 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0267 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0268 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.transition (⟨17152 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel (⟨17152 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0268
    (state : Fin 18432)
    (lower : 17152 ≤ state.val)
    (upper : state.val < 17216)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 17152, by omega⟩
  have state_eq :
      (⟨17152 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0268 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0269 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.transition (⟨17216 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel (⟨17216 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0269
    (state : Fin 18432)
    (lower : 17216 ≤ state.val)
    (upper : state.val < 17280)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 17216, by omega⟩
  have state_eq :
      (⟨17216 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0269 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0270 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.transition (⟨17280 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel (⟨17280 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0270
    (state : Fin 18432)
    (lower : 17280 ≤ state.val)
    (upper : state.val < 17344)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 17280, by omega⟩
  have state_eq :
      (⟨17280 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0270 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0271 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.transition (⟨17344 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel (⟨17344 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0271
    (state : Fin 18432)
    (lower : 17344 ≤ state.val)
    (upper : state.val < 17408)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 17344, by omega⟩
  have state_eq :
      (⟨17344 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0271 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0272 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.transition (⟨17408 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel (⟨17408 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0272
    (state : Fin 18432)
    (lower : 17408 ≤ state.val)
    (upper : state.val < 17472)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 17408, by omega⟩
  have state_eq :
      (⟨17408 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0272 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0273 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.transition (⟨17472 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel (⟨17472 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0273
    (state : Fin 18432)
    (lower : 17472 ≤ state.val)
    (upper : state.val < 17536)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 17472, by omega⟩
  have state_eq :
      (⟨17472 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0273 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0274 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.transition (⟨17536 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel (⟨17536 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0274
    (state : Fin 18432)
    (lower : 17536 ≤ state.val)
    (upper : state.val < 17600)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 17536, by omega⟩
  have state_eq :
      (⟨17536 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0274 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0275 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.transition (⟨17600 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel (⟨17600 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0275
    (state : Fin 18432)
    (lower : 17600 ≤ state.val)
    (upper : state.val < 17664)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 17600, by omega⟩
  have state_eq :
      (⟨17600 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0275 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0276 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.transition (⟨17664 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel (⟨17664 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0276
    (state : Fin 18432)
    (lower : 17664 ≤ state.val)
    (upper : state.val < 17728)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 17664, by omega⟩
  have state_eq :
      (⟨17664 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0276 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0277 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.transition (⟨17728 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel (⟨17728 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0277
    (state : Fin 18432)
    (lower : 17728 ≤ state.val)
    (upper : state.val < 17792)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 17728, by omega⟩
  have state_eq :
      (⟨17728 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0277 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0278 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.transition (⟨17792 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel (⟨17792 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0278
    (state : Fin 18432)
    (lower : 17792 ≤ state.val)
    (upper : state.val < 17856)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 17792, by omega⟩
  have state_eq :
      (⟨17792 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0278 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0279 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.transition (⟨17856 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel (⟨17856 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0279
    (state : Fin 18432)
    (lower : 17856 ≤ state.val)
    (upper : state.val < 17920)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 17856, by omega⟩
  have state_eq :
      (⟨17856 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0279 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0280 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.transition (⟨17920 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel (⟨17920 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0280
    (state : Fin 18432)
    (lower : 17920 ≤ state.val)
    (upper : state.val < 17984)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 17920, by omega⟩
  have state_eq :
      (⟨17920 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0280 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0281 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.transition (⟨17984 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel (⟨17984 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0281
    (state : Fin 18432)
    (lower : 17984 ≤ state.val)
    (upper : state.val < 18048)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 17984, by omega⟩
  have state_eq :
      (⟨17984 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0281 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0282 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.transition (⟨18048 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel (⟨18048 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0282
    (state : Fin 18432)
    (lower : 18048 ≤ state.val)
    (upper : state.val < 18112)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 18048, by omega⟩
  have state_eq :
      (⟨18048 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0282 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0283 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.transition (⟨18112 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel (⟨18112 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0283
    (state : Fin 18432)
    (lower : 18112 ≤ state.val)
    (upper : state.val < 18176)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 18112, by omega⟩
  have state_eq :
      (⟨18112 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0283 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0284 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.transition (⟨18176 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel (⟨18176 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0284
    (state : Fin 18432)
    (lower : 18176 ≤ state.val)
    (upper : state.val < 18240)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 18176, by omega⟩
  have state_eq :
      (⟨18176 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0284 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0285 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.transition (⟨18240 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel (⟨18240 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0285
    (state : Fin 18432)
    (lower : 18240 ≤ state.val)
    (upper : state.val < 18304)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 18240, by omega⟩
  have state_eq :
      (⟨18240 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0285 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0286 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.transition (⟨18304 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel (⟨18304 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0286
    (state : Fin 18432)
    (lower : 18304 ≤ state.val)
    (upper : state.val < 18368)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 18304, by omega⟩
  have state_eq :
      (⟨18304 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0286 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0287 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.transition (⟨18368 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel (⟨18368 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0287
    (state : Fin 18432)
    (lower : 18368 ≤ state.val)
    (upper : state.val < 18432)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 18368, by omega⟩
  have state_eq :
      (⟨18368 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0287 offset generator

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.Shards
