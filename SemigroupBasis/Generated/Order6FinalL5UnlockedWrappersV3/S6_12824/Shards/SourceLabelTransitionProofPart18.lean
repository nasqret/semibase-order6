import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Support.Core
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0576 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨36864 + candidate.val, by omega⟩ : Fin 48684) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (⟨36864 + candidate.val, by omega⟩ : Fin 48684))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0576
    (state : Fin 48684)
    (lower : 36864 ≤ state.val)
    (upper : state.val < 36928)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 36864, by omega⟩
  have state_eq :
      (⟨36864 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0576 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0577 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨36928 + candidate.val, by omega⟩ : Fin 48684) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (⟨36928 + candidate.val, by omega⟩ : Fin 48684))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0577
    (state : Fin 48684)
    (lower : 36928 ≤ state.val)
    (upper : state.val < 36992)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 36928, by omega⟩
  have state_eq :
      (⟨36928 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0577 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0578 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨36992 + candidate.val, by omega⟩ : Fin 48684) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (⟨36992 + candidate.val, by omega⟩ : Fin 48684))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0578
    (state : Fin 48684)
    (lower : 36992 ≤ state.val)
    (upper : state.val < 37056)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 36992, by omega⟩
  have state_eq :
      (⟨36992 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0578 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0579 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨37056 + candidate.val, by omega⟩ : Fin 48684) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (⟨37056 + candidate.val, by omega⟩ : Fin 48684))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0579
    (state : Fin 48684)
    (lower : 37056 ≤ state.val)
    (upper : state.val < 37120)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 37056, by omega⟩
  have state_eq :
      (⟨37056 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0579 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0580 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨37120 + candidate.val, by omega⟩ : Fin 48684) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (⟨37120 + candidate.val, by omega⟩ : Fin 48684))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0580
    (state : Fin 48684)
    (lower : 37120 ≤ state.val)
    (upper : state.val < 37184)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 37120, by omega⟩
  have state_eq :
      (⟨37120 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0580 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0581 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨37184 + candidate.val, by omega⟩ : Fin 48684) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (⟨37184 + candidate.val, by omega⟩ : Fin 48684))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0581
    (state : Fin 48684)
    (lower : 37184 ≤ state.val)
    (upper : state.val < 37248)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 37184, by omega⟩
  have state_eq :
      (⟨37184 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0581 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0582 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨37248 + candidate.val, by omega⟩ : Fin 48684) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (⟨37248 + candidate.val, by omega⟩ : Fin 48684))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0582
    (state : Fin 48684)
    (lower : 37248 ≤ state.val)
    (upper : state.val < 37312)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 37248, by omega⟩
  have state_eq :
      (⟨37248 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0582 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0583 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨37312 + candidate.val, by omega⟩ : Fin 48684) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (⟨37312 + candidate.val, by omega⟩ : Fin 48684))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0583
    (state : Fin 48684)
    (lower : 37312 ≤ state.val)
    (upper : state.val < 37376)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 37312, by omega⟩
  have state_eq :
      (⟨37312 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0583 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0584 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨37376 + candidate.val, by omega⟩ : Fin 48684) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (⟨37376 + candidate.val, by omega⟩ : Fin 48684))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0584
    (state : Fin 48684)
    (lower : 37376 ≤ state.val)
    (upper : state.val < 37440)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 37376, by omega⟩
  have state_eq :
      (⟨37376 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0584 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0585 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨37440 + candidate.val, by omega⟩ : Fin 48684) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (⟨37440 + candidate.val, by omega⟩ : Fin 48684))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0585
    (state : Fin 48684)
    (lower : 37440 ≤ state.val)
    (upper : state.val < 37504)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 37440, by omega⟩
  have state_eq :
      (⟨37440 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0585 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0586 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨37504 + candidate.val, by omega⟩ : Fin 48684) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (⟨37504 + candidate.val, by omega⟩ : Fin 48684))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0586
    (state : Fin 48684)
    (lower : 37504 ≤ state.val)
    (upper : state.val < 37568)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 37504, by omega⟩
  have state_eq :
      (⟨37504 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0586 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0587 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨37568 + candidate.val, by omega⟩ : Fin 48684) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (⟨37568 + candidate.val, by omega⟩ : Fin 48684))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0587
    (state : Fin 48684)
    (lower : 37568 ≤ state.val)
    (upper : state.val < 37632)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 37568, by omega⟩
  have state_eq :
      (⟨37568 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0587 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0588 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨37632 + candidate.val, by omega⟩ : Fin 48684) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (⟨37632 + candidate.val, by omega⟩ : Fin 48684))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0588
    (state : Fin 48684)
    (lower : 37632 ≤ state.val)
    (upper : state.val < 37696)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 37632, by omega⟩
  have state_eq :
      (⟨37632 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0588 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0589 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨37696 + candidate.val, by omega⟩ : Fin 48684) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (⟨37696 + candidate.val, by omega⟩ : Fin 48684))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0589
    (state : Fin 48684)
    (lower : 37696 ≤ state.val)
    (upper : state.val < 37760)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 37696, by omega⟩
  have state_eq :
      (⟨37696 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0589 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0590 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨37760 + candidate.val, by omega⟩ : Fin 48684) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (⟨37760 + candidate.val, by omega⟩ : Fin 48684))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0590
    (state : Fin 48684)
    (lower : 37760 ≤ state.val)
    (upper : state.val < 37824)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 37760, by omega⟩
  have state_eq :
      (⟨37760 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0590 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0591 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨37824 + candidate.val, by omega⟩ : Fin 48684) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (⟨37824 + candidate.val, by omega⟩ : Fin 48684))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0591
    (state : Fin 48684)
    (lower : 37824 ≤ state.val)
    (upper : state.val < 37888)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 37824, by omega⟩
  have state_eq :
      (⟨37824 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0591 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0592 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨37888 + candidate.val, by omega⟩ : Fin 48684) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (⟨37888 + candidate.val, by omega⟩ : Fin 48684))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0592
    (state : Fin 48684)
    (lower : 37888 ≤ state.val)
    (upper : state.val < 37952)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 37888, by omega⟩
  have state_eq :
      (⟨37888 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0592 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0593 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨37952 + candidate.val, by omega⟩ : Fin 48684) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (⟨37952 + candidate.val, by omega⟩ : Fin 48684))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0593
    (state : Fin 48684)
    (lower : 37952 ≤ state.val)
    (upper : state.val < 38016)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 37952, by omega⟩
  have state_eq :
      (⟨37952 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0593 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0594 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨38016 + candidate.val, by omega⟩ : Fin 48684) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (⟨38016 + candidate.val, by omega⟩ : Fin 48684))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0594
    (state : Fin 48684)
    (lower : 38016 ≤ state.val)
    (upper : state.val < 38080)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 38016, by omega⟩
  have state_eq :
      (⟨38016 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0594 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0595 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨38080 + candidate.val, by omega⟩ : Fin 48684) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (⟨38080 + candidate.val, by omega⟩ : Fin 48684))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0595
    (state : Fin 48684)
    (lower : 38080 ≤ state.val)
    (upper : state.val < 38144)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 38080, by omega⟩
  have state_eq :
      (⟨38080 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0595 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0596 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨38144 + candidate.val, by omega⟩ : Fin 48684) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (⟨38144 + candidate.val, by omega⟩ : Fin 48684))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0596
    (state : Fin 48684)
    (lower : 38144 ≤ state.val)
    (upper : state.val < 38208)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 38144, by omega⟩
  have state_eq :
      (⟨38144 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0596 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0597 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨38208 + candidate.val, by omega⟩ : Fin 48684) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (⟨38208 + candidate.val, by omega⟩ : Fin 48684))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0597
    (state : Fin 48684)
    (lower : 38208 ≤ state.val)
    (upper : state.val < 38272)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 38208, by omega⟩
  have state_eq :
      (⟨38208 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0597 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0598 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨38272 + candidate.val, by omega⟩ : Fin 48684) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (⟨38272 + candidate.val, by omega⟩ : Fin 48684))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0598
    (state : Fin 48684)
    (lower : 38272 ≤ state.val)
    (upper : state.val < 38336)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 38272, by omega⟩
  have state_eq :
      (⟨38272 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0598 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0599 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨38336 + candidate.val, by omega⟩ : Fin 48684) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (⟨38336 + candidate.val, by omega⟩ : Fin 48684))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0599
    (state : Fin 48684)
    (lower : 38336 ≤ state.val)
    (upper : state.val < 38400)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 38336, by omega⟩
  have state_eq :
      (⟨38336 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0599 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0600 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨38400 + candidate.val, by omega⟩ : Fin 48684) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (⟨38400 + candidate.val, by omega⟩ : Fin 48684))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0600
    (state : Fin 48684)
    (lower : 38400 ≤ state.val)
    (upper : state.val < 38464)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 38400, by omega⟩
  have state_eq :
      (⟨38400 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0600 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0601 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨38464 + candidate.val, by omega⟩ : Fin 48684) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (⟨38464 + candidate.val, by omega⟩ : Fin 48684))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0601
    (state : Fin 48684)
    (lower : 38464 ≤ state.val)
    (upper : state.val < 38528)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 38464, by omega⟩
  have state_eq :
      (⟨38464 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0601 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0602 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨38528 + candidate.val, by omega⟩ : Fin 48684) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (⟨38528 + candidate.val, by omega⟩ : Fin 48684))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0602
    (state : Fin 48684)
    (lower : 38528 ≤ state.val)
    (upper : state.val < 38592)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 38528, by omega⟩
  have state_eq :
      (⟨38528 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0602 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0603 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨38592 + candidate.val, by omega⟩ : Fin 48684) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (⟨38592 + candidate.val, by omega⟩ : Fin 48684))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0603
    (state : Fin 48684)
    (lower : 38592 ≤ state.val)
    (upper : state.val < 38656)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 38592, by omega⟩
  have state_eq :
      (⟨38592 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0603 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0604 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨38656 + candidate.val, by omega⟩ : Fin 48684) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (⟨38656 + candidate.val, by omega⟩ : Fin 48684))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0604
    (state : Fin 48684)
    (lower : 38656 ≤ state.val)
    (upper : state.val < 38720)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 38656, by omega⟩
  have state_eq :
      (⟨38656 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0604 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0605 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨38720 + candidate.val, by omega⟩ : Fin 48684) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (⟨38720 + candidate.val, by omega⟩ : Fin 48684))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0605
    (state : Fin 48684)
    (lower : 38720 ≤ state.val)
    (upper : state.val < 38784)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 38720, by omega⟩
  have state_eq :
      (⟨38720 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0605 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0606 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨38784 + candidate.val, by omega⟩ : Fin 48684) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (⟨38784 + candidate.val, by omega⟩ : Fin 48684))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0606
    (state : Fin 48684)
    (lower : 38784 ≤ state.val)
    (upper : state.val < 38848)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 38784, by omega⟩
  have state_eq :
      (⟨38784 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0606 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0607 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨38848 + candidate.val, by omega⟩ : Fin 48684) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (⟨38848 + candidate.val, by omega⟩ : Fin 48684))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0607
    (state : Fin 48684)
    (lower : 38848 ≤ state.val)
    (upper : state.val < 38912)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7390Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 38848, by omega⟩
  have state_eq :
      (⟨38848 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0607 offset generator

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards
