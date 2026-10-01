import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.Support.Core
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.Shards

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0160 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition (⟨10240 + candidate.val, by omega⟩ : Fin 11184) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7644Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.sourceLabel (⟨10240 + candidate.val, by omega⟩ : Fin 11184))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0160
    (state : Fin 11184)
    (lower : 10240 ≤ state.val)
    (upper : state.val < 10304)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7644Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 10240, by omega⟩
  have state_eq :
      (⟨10240 + offset.val, by omega⟩ : Fin 11184) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0160 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0161 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition (⟨10304 + candidate.val, by omega⟩ : Fin 11184) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7644Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.sourceLabel (⟨10304 + candidate.val, by omega⟩ : Fin 11184))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0161
    (state : Fin 11184)
    (lower : 10304 ≤ state.val)
    (upper : state.val < 10368)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7644Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 10304, by omega⟩
  have state_eq :
      (⟨10304 + offset.val, by omega⟩ : Fin 11184) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0161 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0162 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition (⟨10368 + candidate.val, by omega⟩ : Fin 11184) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7644Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.sourceLabel (⟨10368 + candidate.val, by omega⟩ : Fin 11184))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0162
    (state : Fin 11184)
    (lower : 10368 ≤ state.val)
    (upper : state.val < 10432)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7644Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 10368, by omega⟩
  have state_eq :
      (⟨10368 + offset.val, by omega⟩ : Fin 11184) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0162 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0163 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition (⟨10432 + candidate.val, by omega⟩ : Fin 11184) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7644Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.sourceLabel (⟨10432 + candidate.val, by omega⟩ : Fin 11184))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0163
    (state : Fin 11184)
    (lower : 10432 ≤ state.val)
    (upper : state.val < 10496)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7644Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 10432, by omega⟩
  have state_eq :
      (⟨10432 + offset.val, by omega⟩ : Fin 11184) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0163 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0164 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition (⟨10496 + candidate.val, by omega⟩ : Fin 11184) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7644Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.sourceLabel (⟨10496 + candidate.val, by omega⟩ : Fin 11184))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0164
    (state : Fin 11184)
    (lower : 10496 ≤ state.val)
    (upper : state.val < 10560)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7644Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 10496, by omega⟩
  have state_eq :
      (⟨10496 + offset.val, by omega⟩ : Fin 11184) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0164 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0165 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition (⟨10560 + candidate.val, by omega⟩ : Fin 11184) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7644Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.sourceLabel (⟨10560 + candidate.val, by omega⟩ : Fin 11184))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0165
    (state : Fin 11184)
    (lower : 10560 ≤ state.val)
    (upper : state.val < 10624)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7644Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 10560, by omega⟩
  have state_eq :
      (⟨10560 + offset.val, by omega⟩ : Fin 11184) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0165 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0166 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition (⟨10624 + candidate.val, by omega⟩ : Fin 11184) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7644Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.sourceLabel (⟨10624 + candidate.val, by omega⟩ : Fin 11184))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0166
    (state : Fin 11184)
    (lower : 10624 ≤ state.val)
    (upper : state.val < 10688)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7644Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 10624, by omega⟩
  have state_eq :
      (⟨10624 + offset.val, by omega⟩ : Fin 11184) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0166 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0167 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition (⟨10688 + candidate.val, by omega⟩ : Fin 11184) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7644Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.sourceLabel (⟨10688 + candidate.val, by omega⟩ : Fin 11184))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0167
    (state : Fin 11184)
    (lower : 10688 ≤ state.val)
    (upper : state.val < 10752)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7644Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 10688, by omega⟩
  have state_eq :
      (⟨10688 + offset.val, by omega⟩ : Fin 11184) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0167 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0168 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition (⟨10752 + candidate.val, by omega⟩ : Fin 11184) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7644Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.sourceLabel (⟨10752 + candidate.val, by omega⟩ : Fin 11184))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0168
    (state : Fin 11184)
    (lower : 10752 ≤ state.val)
    (upper : state.val < 10816)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7644Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 10752, by omega⟩
  have state_eq :
      (⟨10752 + offset.val, by omega⟩ : Fin 11184) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0168 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0169 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition (⟨10816 + candidate.val, by omega⟩ : Fin 11184) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7644Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.sourceLabel (⟨10816 + candidate.val, by omega⟩ : Fin 11184))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0169
    (state : Fin 11184)
    (lower : 10816 ≤ state.val)
    (upper : state.val < 10880)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7644Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 10816, by omega⟩
  have state_eq :
      (⟨10816 + offset.val, by omega⟩ : Fin 11184) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0169 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0170 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition (⟨10880 + candidate.val, by omega⟩ : Fin 11184) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7644Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.sourceLabel (⟨10880 + candidate.val, by omega⟩ : Fin 11184))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0170
    (state : Fin 11184)
    (lower : 10880 ≤ state.val)
    (upper : state.val < 10944)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7644Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 10880, by omega⟩
  have state_eq :
      (⟨10880 + offset.val, by omega⟩ : Fin 11184) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0170 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0171 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition (⟨10944 + candidate.val, by omega⟩ : Fin 11184) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7644Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.sourceLabel (⟨10944 + candidate.val, by omega⟩ : Fin 11184))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0171
    (state : Fin 11184)
    (lower : 10944 ≤ state.val)
    (upper : state.val < 11008)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7644Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 10944, by omega⟩
  have state_eq :
      (⟨10944 + offset.val, by omega⟩ : Fin 11184) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0171 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0172 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition (⟨11008 + candidate.val, by omega⟩ : Fin 11184) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7644Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.sourceLabel (⟨11008 + candidate.val, by omega⟩ : Fin 11184))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0172
    (state : Fin 11184)
    (lower : 11008 ≤ state.val)
    (upper : state.val < 11072)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7644Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 11008, by omega⟩
  have state_eq :
      (⟨11008 + offset.val, by omega⟩ : Fin 11184) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0172 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0173 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition (⟨11072 + candidate.val, by omega⟩ : Fin 11184) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7644Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.sourceLabel (⟨11072 + candidate.val, by omega⟩ : Fin 11184))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0173
    (state : Fin 11184)
    (lower : 11072 ≤ state.val)
    (upper : state.val < 11136)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7644Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 11072, by omega⟩
  have state_eq :
      (⟨11072 + offset.val, by omega⟩ : Fin 11184) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0173 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0174 :
    ∀ candidate : Fin 48,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition (⟨11136 + candidate.val, by omega⟩ : Fin 11184) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7644Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.sourceLabel (⟨11136 + candidate.val, by omega⟩ : Fin 11184))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0174
    (state : Fin 11184)
    (lower : 11136 ≤ state.val)
    (upper : state.val < 11184)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7644Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorSourceLabel generator) := by
  let offset : Fin 48 := ⟨state.val - 11136, by omega⟩
  have state_eq :
      (⟨11136 + offset.val, by omega⟩ : Fin 11184) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0174 offset generator

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.Shards
