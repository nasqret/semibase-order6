import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.Support.Core
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.Shards

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0256 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition (⟨16384 + candidate.val, by omega⟩ : Fin 17622) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.sourceLabel (⟨16384 + candidate.val, by omega⟩ : Fin 17622))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0256
    (state : Fin 17622)
    (lower : 16384 ≤ state.val)
    (upper : state.val < 16448)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 16384, by omega⟩
  have state_eq :
      (⟨16384 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0256 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0257 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition (⟨16448 + candidate.val, by omega⟩ : Fin 17622) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.sourceLabel (⟨16448 + candidate.val, by omega⟩ : Fin 17622))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0257
    (state : Fin 17622)
    (lower : 16448 ≤ state.val)
    (upper : state.val < 16512)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 16448, by omega⟩
  have state_eq :
      (⟨16448 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0257 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0258 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition (⟨16512 + candidate.val, by omega⟩ : Fin 17622) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.sourceLabel (⟨16512 + candidate.val, by omega⟩ : Fin 17622))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0258
    (state : Fin 17622)
    (lower : 16512 ≤ state.val)
    (upper : state.val < 16576)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 16512, by omega⟩
  have state_eq :
      (⟨16512 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0258 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0259 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition (⟨16576 + candidate.val, by omega⟩ : Fin 17622) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.sourceLabel (⟨16576 + candidate.val, by omega⟩ : Fin 17622))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0259
    (state : Fin 17622)
    (lower : 16576 ≤ state.val)
    (upper : state.val < 16640)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 16576, by omega⟩
  have state_eq :
      (⟨16576 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0259 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0260 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition (⟨16640 + candidate.val, by omega⟩ : Fin 17622) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.sourceLabel (⟨16640 + candidate.val, by omega⟩ : Fin 17622))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0260
    (state : Fin 17622)
    (lower : 16640 ≤ state.val)
    (upper : state.val < 16704)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 16640, by omega⟩
  have state_eq :
      (⟨16640 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0260 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0261 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition (⟨16704 + candidate.val, by omega⟩ : Fin 17622) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.sourceLabel (⟨16704 + candidate.val, by omega⟩ : Fin 17622))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0261
    (state : Fin 17622)
    (lower : 16704 ≤ state.val)
    (upper : state.val < 16768)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 16704, by omega⟩
  have state_eq :
      (⟨16704 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0261 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0262 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition (⟨16768 + candidate.val, by omega⟩ : Fin 17622) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.sourceLabel (⟨16768 + candidate.val, by omega⟩ : Fin 17622))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0262
    (state : Fin 17622)
    (lower : 16768 ≤ state.val)
    (upper : state.val < 16832)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 16768, by omega⟩
  have state_eq :
      (⟨16768 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0262 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0263 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition (⟨16832 + candidate.val, by omega⟩ : Fin 17622) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.sourceLabel (⟨16832 + candidate.val, by omega⟩ : Fin 17622))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0263
    (state : Fin 17622)
    (lower : 16832 ≤ state.val)
    (upper : state.val < 16896)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 16832, by omega⟩
  have state_eq :
      (⟨16832 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0263 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0264 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition (⟨16896 + candidate.val, by omega⟩ : Fin 17622) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.sourceLabel (⟨16896 + candidate.val, by omega⟩ : Fin 17622))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0264
    (state : Fin 17622)
    (lower : 16896 ≤ state.val)
    (upper : state.val < 16960)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 16896, by omega⟩
  have state_eq :
      (⟨16896 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0264 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0265 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition (⟨16960 + candidate.val, by omega⟩ : Fin 17622) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.sourceLabel (⟨16960 + candidate.val, by omega⟩ : Fin 17622))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0265
    (state : Fin 17622)
    (lower : 16960 ≤ state.val)
    (upper : state.val < 17024)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 16960, by omega⟩
  have state_eq :
      (⟨16960 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0265 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0266 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition (⟨17024 + candidate.val, by omega⟩ : Fin 17622) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.sourceLabel (⟨17024 + candidate.val, by omega⟩ : Fin 17622))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0266
    (state : Fin 17622)
    (lower : 17024 ≤ state.val)
    (upper : state.val < 17088)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 17024, by omega⟩
  have state_eq :
      (⟨17024 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0266 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0267 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition (⟨17088 + candidate.val, by omega⟩ : Fin 17622) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.sourceLabel (⟨17088 + candidate.val, by omega⟩ : Fin 17622))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0267
    (state : Fin 17622)
    (lower : 17088 ≤ state.val)
    (upper : state.val < 17152)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 17088, by omega⟩
  have state_eq :
      (⟨17088 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0267 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0268 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition (⟨17152 + candidate.val, by omega⟩ : Fin 17622) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.sourceLabel (⟨17152 + candidate.val, by omega⟩ : Fin 17622))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0268
    (state : Fin 17622)
    (lower : 17152 ≤ state.val)
    (upper : state.val < 17216)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 17152, by omega⟩
  have state_eq :
      (⟨17152 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0268 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0269 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition (⟨17216 + candidate.val, by omega⟩ : Fin 17622) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.sourceLabel (⟨17216 + candidate.val, by omega⟩ : Fin 17622))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0269
    (state : Fin 17622)
    (lower : 17216 ≤ state.val)
    (upper : state.val < 17280)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 17216, by omega⟩
  have state_eq :
      (⟨17216 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0269 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0270 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition (⟨17280 + candidate.val, by omega⟩ : Fin 17622) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.sourceLabel (⟨17280 + candidate.val, by omega⟩ : Fin 17622))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0270
    (state : Fin 17622)
    (lower : 17280 ≤ state.val)
    (upper : state.val < 17344)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 17280, by omega⟩
  have state_eq :
      (⟨17280 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0270 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0271 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition (⟨17344 + candidate.val, by omega⟩ : Fin 17622) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.sourceLabel (⟨17344 + candidate.val, by omega⟩ : Fin 17622))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0271
    (state : Fin 17622)
    (lower : 17344 ≤ state.val)
    (upper : state.val < 17408)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 17344, by omega⟩
  have state_eq :
      (⟨17344 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0271 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0272 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition (⟨17408 + candidate.val, by omega⟩ : Fin 17622) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.sourceLabel (⟨17408 + candidate.val, by omega⟩ : Fin 17622))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0272
    (state : Fin 17622)
    (lower : 17408 ≤ state.val)
    (upper : state.val < 17472)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 17408, by omega⟩
  have state_eq :
      (⟨17408 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0272 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0273 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition (⟨17472 + candidate.val, by omega⟩ : Fin 17622) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.sourceLabel (⟨17472 + candidate.val, by omega⟩ : Fin 17622))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0273
    (state : Fin 17622)
    (lower : 17472 ≤ state.val)
    (upper : state.val < 17536)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 17472, by omega⟩
  have state_eq :
      (⟨17472 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0273 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0274 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition (⟨17536 + candidate.val, by omega⟩ : Fin 17622) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.sourceLabel (⟨17536 + candidate.val, by omega⟩ : Fin 17622))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0274
    (state : Fin 17622)
    (lower : 17536 ≤ state.val)
    (upper : state.val < 17600)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 17536, by omega⟩
  have state_eq :
      (⟨17536 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0274 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0275 :
    ∀ candidate : Fin 22,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition (⟨17600 + candidate.val, by omega⟩ : Fin 17622) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.sourceLabel (⟨17600 + candidate.val, by omega⟩ : Fin 17622))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0275
    (state : Fin 17622)
    (lower : 17600 ≤ state.val)
    (upper : state.val < 17622)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorSourceLabel generator) := by
  let offset : Fin 22 := ⟨state.val - 17600, by omega⟩
  have state_eq :
      (⟨17600 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0275 offset generator

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.Shards
