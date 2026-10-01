import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.Support.Core
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.Shards

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0192 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition (⟨12288 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (⟨12288 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0192
    (state : Fin 18432)
    (lower : 12288 ≤ state.val)
    (upper : state.val < 12352)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 12288, by omega⟩
  have state_eq :
      (⟨12288 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0192 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0193 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition (⟨12352 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (⟨12352 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0193
    (state : Fin 18432)
    (lower : 12352 ≤ state.val)
    (upper : state.val < 12416)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 12352, by omega⟩
  have state_eq :
      (⟨12352 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0193 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0194 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition (⟨12416 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (⟨12416 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0194
    (state : Fin 18432)
    (lower : 12416 ≤ state.val)
    (upper : state.val < 12480)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 12416, by omega⟩
  have state_eq :
      (⟨12416 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0194 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0195 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition (⟨12480 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (⟨12480 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0195
    (state : Fin 18432)
    (lower : 12480 ≤ state.val)
    (upper : state.val < 12544)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 12480, by omega⟩
  have state_eq :
      (⟨12480 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0195 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0196 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition (⟨12544 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (⟨12544 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0196
    (state : Fin 18432)
    (lower : 12544 ≤ state.val)
    (upper : state.val < 12608)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 12544, by omega⟩
  have state_eq :
      (⟨12544 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0196 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0197 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition (⟨12608 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (⟨12608 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0197
    (state : Fin 18432)
    (lower : 12608 ≤ state.val)
    (upper : state.val < 12672)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 12608, by omega⟩
  have state_eq :
      (⟨12608 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0197 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0198 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition (⟨12672 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (⟨12672 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0198
    (state : Fin 18432)
    (lower : 12672 ≤ state.val)
    (upper : state.val < 12736)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 12672, by omega⟩
  have state_eq :
      (⟨12672 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0198 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0199 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition (⟨12736 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (⟨12736 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0199
    (state : Fin 18432)
    (lower : 12736 ≤ state.val)
    (upper : state.val < 12800)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 12736, by omega⟩
  have state_eq :
      (⟨12736 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0199 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0200 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition (⟨12800 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (⟨12800 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0200
    (state : Fin 18432)
    (lower : 12800 ≤ state.val)
    (upper : state.val < 12864)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 12800, by omega⟩
  have state_eq :
      (⟨12800 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0200 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0201 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition (⟨12864 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (⟨12864 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0201
    (state : Fin 18432)
    (lower : 12864 ≤ state.val)
    (upper : state.val < 12928)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 12864, by omega⟩
  have state_eq :
      (⟨12864 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0201 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0202 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition (⟨12928 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (⟨12928 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0202
    (state : Fin 18432)
    (lower : 12928 ≤ state.val)
    (upper : state.val < 12992)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 12928, by omega⟩
  have state_eq :
      (⟨12928 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0202 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0203 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition (⟨12992 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (⟨12992 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0203
    (state : Fin 18432)
    (lower : 12992 ≤ state.val)
    (upper : state.val < 13056)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 12992, by omega⟩
  have state_eq :
      (⟨12992 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0203 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0204 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition (⟨13056 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (⟨13056 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0204
    (state : Fin 18432)
    (lower : 13056 ≤ state.val)
    (upper : state.val < 13120)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 13056, by omega⟩
  have state_eq :
      (⟨13056 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0204 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0205 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition (⟨13120 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (⟨13120 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0205
    (state : Fin 18432)
    (lower : 13120 ≤ state.val)
    (upper : state.val < 13184)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 13120, by omega⟩
  have state_eq :
      (⟨13120 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0205 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0206 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition (⟨13184 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (⟨13184 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0206
    (state : Fin 18432)
    (lower : 13184 ≤ state.val)
    (upper : state.val < 13248)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 13184, by omega⟩
  have state_eq :
      (⟨13184 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0206 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0207 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition (⟨13248 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (⟨13248 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0207
    (state : Fin 18432)
    (lower : 13248 ≤ state.val)
    (upper : state.val < 13312)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 13248, by omega⟩
  have state_eq :
      (⟨13248 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0207 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0208 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition (⟨13312 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (⟨13312 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0208
    (state : Fin 18432)
    (lower : 13312 ≤ state.val)
    (upper : state.val < 13376)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 13312, by omega⟩
  have state_eq :
      (⟨13312 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0208 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0209 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition (⟨13376 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (⟨13376 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0209
    (state : Fin 18432)
    (lower : 13376 ≤ state.val)
    (upper : state.val < 13440)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 13376, by omega⟩
  have state_eq :
      (⟨13376 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0209 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0210 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition (⟨13440 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (⟨13440 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0210
    (state : Fin 18432)
    (lower : 13440 ≤ state.val)
    (upper : state.val < 13504)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 13440, by omega⟩
  have state_eq :
      (⟨13440 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0210 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0211 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition (⟨13504 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (⟨13504 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0211
    (state : Fin 18432)
    (lower : 13504 ≤ state.val)
    (upper : state.val < 13568)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 13504, by omega⟩
  have state_eq :
      (⟨13504 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0211 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0212 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition (⟨13568 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (⟨13568 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0212
    (state : Fin 18432)
    (lower : 13568 ≤ state.val)
    (upper : state.val < 13632)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 13568, by omega⟩
  have state_eq :
      (⟨13568 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0212 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0213 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition (⟨13632 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (⟨13632 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0213
    (state : Fin 18432)
    (lower : 13632 ≤ state.val)
    (upper : state.val < 13696)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 13632, by omega⟩
  have state_eq :
      (⟨13632 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0213 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0214 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition (⟨13696 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (⟨13696 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0214
    (state : Fin 18432)
    (lower : 13696 ≤ state.val)
    (upper : state.val < 13760)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 13696, by omega⟩
  have state_eq :
      (⟨13696 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0214 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0215 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition (⟨13760 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (⟨13760 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0215
    (state : Fin 18432)
    (lower : 13760 ≤ state.val)
    (upper : state.val < 13824)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 13760, by omega⟩
  have state_eq :
      (⟨13760 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0215 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0216 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition (⟨13824 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (⟨13824 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0216
    (state : Fin 18432)
    (lower : 13824 ≤ state.val)
    (upper : state.val < 13888)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 13824, by omega⟩
  have state_eq :
      (⟨13824 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0216 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0217 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition (⟨13888 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (⟨13888 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0217
    (state : Fin 18432)
    (lower : 13888 ≤ state.val)
    (upper : state.val < 13952)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 13888, by omega⟩
  have state_eq :
      (⟨13888 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0217 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0218 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition (⟨13952 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (⟨13952 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0218
    (state : Fin 18432)
    (lower : 13952 ≤ state.val)
    (upper : state.val < 14016)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 13952, by omega⟩
  have state_eq :
      (⟨13952 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0218 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0219 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition (⟨14016 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (⟨14016 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0219
    (state : Fin 18432)
    (lower : 14016 ≤ state.val)
    (upper : state.val < 14080)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 14016, by omega⟩
  have state_eq :
      (⟨14016 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0219 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0220 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition (⟨14080 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (⟨14080 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0220
    (state : Fin 18432)
    (lower : 14080 ≤ state.val)
    (upper : state.val < 14144)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 14080, by omega⟩
  have state_eq :
      (⟨14080 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0220 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0221 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition (⟨14144 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (⟨14144 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0221
    (state : Fin 18432)
    (lower : 14144 ≤ state.val)
    (upper : state.val < 14208)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 14144, by omega⟩
  have state_eq :
      (⟨14144 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0221 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0222 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition (⟨14208 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (⟨14208 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0222
    (state : Fin 18432)
    (lower : 14208 ≤ state.val)
    (upper : state.val < 14272)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 14208, by omega⟩
  have state_eq :
      (⟨14208 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0222 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0223 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition (⟨14272 + candidate.val, by omega⟩ : Fin 18432) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (⟨14272 + candidate.val, by omega⟩ : Fin 18432))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0223
    (state : Fin 18432)
    (lower : 14272 ≤ state.val)
    (upper : state.val < 14336)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 14272, by omega⟩
  have state_eq :
      (⟨14272 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0223 offset generator

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.Shards
