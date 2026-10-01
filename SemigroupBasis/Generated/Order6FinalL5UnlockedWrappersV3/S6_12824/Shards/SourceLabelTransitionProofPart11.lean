import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Support.Core
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0352 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨22528 + candidate.val, by omega⟩ : Fin 48684) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (⟨22528 + candidate.val, by omega⟩ : Fin 48684))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0352
    (state : Fin 48684)
    (lower : 22528 ≤ state.val)
    (upper : state.val < 22592)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 22528, by omega⟩
  have state_eq :
      (⟨22528 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0352 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0353 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨22592 + candidate.val, by omega⟩ : Fin 48684) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (⟨22592 + candidate.val, by omega⟩ : Fin 48684))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0353
    (state : Fin 48684)
    (lower : 22592 ≤ state.val)
    (upper : state.val < 22656)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 22592, by omega⟩
  have state_eq :
      (⟨22592 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0353 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0354 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨22656 + candidate.val, by omega⟩ : Fin 48684) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (⟨22656 + candidate.val, by omega⟩ : Fin 48684))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0354
    (state : Fin 48684)
    (lower : 22656 ≤ state.val)
    (upper : state.val < 22720)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 22656, by omega⟩
  have state_eq :
      (⟨22656 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0354 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0355 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨22720 + candidate.val, by omega⟩ : Fin 48684) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (⟨22720 + candidate.val, by omega⟩ : Fin 48684))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0355
    (state : Fin 48684)
    (lower : 22720 ≤ state.val)
    (upper : state.val < 22784)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 22720, by omega⟩
  have state_eq :
      (⟨22720 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0355 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0356 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨22784 + candidate.val, by omega⟩ : Fin 48684) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (⟨22784 + candidate.val, by omega⟩ : Fin 48684))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0356
    (state : Fin 48684)
    (lower : 22784 ≤ state.val)
    (upper : state.val < 22848)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 22784, by omega⟩
  have state_eq :
      (⟨22784 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0356 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0357 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨22848 + candidate.val, by omega⟩ : Fin 48684) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (⟨22848 + candidate.val, by omega⟩ : Fin 48684))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0357
    (state : Fin 48684)
    (lower : 22848 ≤ state.val)
    (upper : state.val < 22912)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 22848, by omega⟩
  have state_eq :
      (⟨22848 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0357 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0358 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨22912 + candidate.val, by omega⟩ : Fin 48684) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (⟨22912 + candidate.val, by omega⟩ : Fin 48684))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0358
    (state : Fin 48684)
    (lower : 22912 ≤ state.val)
    (upper : state.val < 22976)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 22912, by omega⟩
  have state_eq :
      (⟨22912 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0358 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0359 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨22976 + candidate.val, by omega⟩ : Fin 48684) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (⟨22976 + candidate.val, by omega⟩ : Fin 48684))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0359
    (state : Fin 48684)
    (lower : 22976 ≤ state.val)
    (upper : state.val < 23040)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 22976, by omega⟩
  have state_eq :
      (⟨22976 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0359 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0360 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨23040 + candidate.val, by omega⟩ : Fin 48684) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (⟨23040 + candidate.val, by omega⟩ : Fin 48684))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0360
    (state : Fin 48684)
    (lower : 23040 ≤ state.val)
    (upper : state.val < 23104)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 23040, by omega⟩
  have state_eq :
      (⟨23040 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0360 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0361 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨23104 + candidate.val, by omega⟩ : Fin 48684) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (⟨23104 + candidate.val, by omega⟩ : Fin 48684))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0361
    (state : Fin 48684)
    (lower : 23104 ≤ state.val)
    (upper : state.val < 23168)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 23104, by omega⟩
  have state_eq :
      (⟨23104 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0361 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0362 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨23168 + candidate.val, by omega⟩ : Fin 48684) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (⟨23168 + candidate.val, by omega⟩ : Fin 48684))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0362
    (state : Fin 48684)
    (lower : 23168 ≤ state.val)
    (upper : state.val < 23232)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 23168, by omega⟩
  have state_eq :
      (⟨23168 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0362 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0363 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨23232 + candidate.val, by omega⟩ : Fin 48684) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (⟨23232 + candidate.val, by omega⟩ : Fin 48684))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0363
    (state : Fin 48684)
    (lower : 23232 ≤ state.val)
    (upper : state.val < 23296)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 23232, by omega⟩
  have state_eq :
      (⟨23232 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0363 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0364 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨23296 + candidate.val, by omega⟩ : Fin 48684) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (⟨23296 + candidate.val, by omega⟩ : Fin 48684))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0364
    (state : Fin 48684)
    (lower : 23296 ≤ state.val)
    (upper : state.val < 23360)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 23296, by omega⟩
  have state_eq :
      (⟨23296 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0364 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0365 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨23360 + candidate.val, by omega⟩ : Fin 48684) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (⟨23360 + candidate.val, by omega⟩ : Fin 48684))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0365
    (state : Fin 48684)
    (lower : 23360 ≤ state.val)
    (upper : state.val < 23424)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 23360, by omega⟩
  have state_eq :
      (⟨23360 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0365 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0366 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨23424 + candidate.val, by omega⟩ : Fin 48684) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (⟨23424 + candidate.val, by omega⟩ : Fin 48684))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0366
    (state : Fin 48684)
    (lower : 23424 ≤ state.val)
    (upper : state.val < 23488)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 23424, by omega⟩
  have state_eq :
      (⟨23424 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0366 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0367 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨23488 + candidate.val, by omega⟩ : Fin 48684) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (⟨23488 + candidate.val, by omega⟩ : Fin 48684))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0367
    (state : Fin 48684)
    (lower : 23488 ≤ state.val)
    (upper : state.val < 23552)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 23488, by omega⟩
  have state_eq :
      (⟨23488 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0367 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0368 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨23552 + candidate.val, by omega⟩ : Fin 48684) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (⟨23552 + candidate.val, by omega⟩ : Fin 48684))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0368
    (state : Fin 48684)
    (lower : 23552 ≤ state.val)
    (upper : state.val < 23616)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 23552, by omega⟩
  have state_eq :
      (⟨23552 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0368 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0369 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨23616 + candidate.val, by omega⟩ : Fin 48684) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (⟨23616 + candidate.val, by omega⟩ : Fin 48684))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0369
    (state : Fin 48684)
    (lower : 23616 ≤ state.val)
    (upper : state.val < 23680)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 23616, by omega⟩
  have state_eq :
      (⟨23616 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0369 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0370 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨23680 + candidate.val, by omega⟩ : Fin 48684) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (⟨23680 + candidate.val, by omega⟩ : Fin 48684))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0370
    (state : Fin 48684)
    (lower : 23680 ≤ state.val)
    (upper : state.val < 23744)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 23680, by omega⟩
  have state_eq :
      (⟨23680 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0370 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0371 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨23744 + candidate.val, by omega⟩ : Fin 48684) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (⟨23744 + candidate.val, by omega⟩ : Fin 48684))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0371
    (state : Fin 48684)
    (lower : 23744 ≤ state.val)
    (upper : state.val < 23808)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 23744, by omega⟩
  have state_eq :
      (⟨23744 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0371 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0372 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨23808 + candidate.val, by omega⟩ : Fin 48684) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (⟨23808 + candidate.val, by omega⟩ : Fin 48684))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0372
    (state : Fin 48684)
    (lower : 23808 ≤ state.val)
    (upper : state.val < 23872)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 23808, by omega⟩
  have state_eq :
      (⟨23808 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0372 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0373 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨23872 + candidate.val, by omega⟩ : Fin 48684) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (⟨23872 + candidate.val, by omega⟩ : Fin 48684))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0373
    (state : Fin 48684)
    (lower : 23872 ≤ state.val)
    (upper : state.val < 23936)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 23872, by omega⟩
  have state_eq :
      (⟨23872 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0373 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0374 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨23936 + candidate.val, by omega⟩ : Fin 48684) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (⟨23936 + candidate.val, by omega⟩ : Fin 48684))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0374
    (state : Fin 48684)
    (lower : 23936 ≤ state.val)
    (upper : state.val < 24000)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 23936, by omega⟩
  have state_eq :
      (⟨23936 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0374 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0375 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨24000 + candidate.val, by omega⟩ : Fin 48684) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (⟨24000 + candidate.val, by omega⟩ : Fin 48684))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0375
    (state : Fin 48684)
    (lower : 24000 ≤ state.val)
    (upper : state.val < 24064)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 24000, by omega⟩
  have state_eq :
      (⟨24000 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0375 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0376 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨24064 + candidate.val, by omega⟩ : Fin 48684) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (⟨24064 + candidate.val, by omega⟩ : Fin 48684))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0376
    (state : Fin 48684)
    (lower : 24064 ≤ state.val)
    (upper : state.val < 24128)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 24064, by omega⟩
  have state_eq :
      (⟨24064 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0376 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0377 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨24128 + candidate.val, by omega⟩ : Fin 48684) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (⟨24128 + candidate.val, by omega⟩ : Fin 48684))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0377
    (state : Fin 48684)
    (lower : 24128 ≤ state.val)
    (upper : state.val < 24192)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 24128, by omega⟩
  have state_eq :
      (⟨24128 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0377 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0378 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨24192 + candidate.val, by omega⟩ : Fin 48684) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (⟨24192 + candidate.val, by omega⟩ : Fin 48684))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0378
    (state : Fin 48684)
    (lower : 24192 ≤ state.val)
    (upper : state.val < 24256)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 24192, by omega⟩
  have state_eq :
      (⟨24192 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0378 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0379 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨24256 + candidate.val, by omega⟩ : Fin 48684) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (⟨24256 + candidate.val, by omega⟩ : Fin 48684))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0379
    (state : Fin 48684)
    (lower : 24256 ≤ state.val)
    (upper : state.val < 24320)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 24256, by omega⟩
  have state_eq :
      (⟨24256 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0379 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0380 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨24320 + candidate.val, by omega⟩ : Fin 48684) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (⟨24320 + candidate.val, by omega⟩ : Fin 48684))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0380
    (state : Fin 48684)
    (lower : 24320 ≤ state.val)
    (upper : state.val < 24384)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 24320, by omega⟩
  have state_eq :
      (⟨24320 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0380 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0381 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨24384 + candidate.val, by omega⟩ : Fin 48684) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (⟨24384 + candidate.val, by omega⟩ : Fin 48684))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0381
    (state : Fin 48684)
    (lower : 24384 ≤ state.val)
    (upper : state.val < 24448)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 24384, by omega⟩
  have state_eq :
      (⟨24384 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0381 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0382 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨24448 + candidate.val, by omega⟩ : Fin 48684) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (⟨24448 + candidate.val, by omega⟩ : Fin 48684))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0382
    (state : Fin 48684)
    (lower : 24448 ≤ state.val)
    (upper : state.val < 24512)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 24448, by omega⟩
  have state_eq :
      (⟨24448 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0382 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0383 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨24512 + candidate.val, by omega⟩ : Fin 48684) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (⟨24512 + candidate.val, by omega⟩ : Fin 48684))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0383
    (state : Fin 48684)
    (lower : 24512 ≤ state.val)
    (upper : state.val < 24576)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 24512, by omega⟩
  have state_eq :
      (⟨24512 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0383 offset generator

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards
