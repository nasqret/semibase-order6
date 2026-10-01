import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6845.Support.Core
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6845.Shards

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0064 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6845.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6845.transition (⟨4096 + candidate.val, by omega⟩ : Fin 4374) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6196Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6845.sourceLabel (⟨4096 + candidate.val, by omega⟩ : Fin 4374))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6845.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0064
    (state : Fin 4374)
    (lower : 4096 ≤ state.val)
    (upper : state.val < 4160)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6845.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6845.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6196Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6845.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6845.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 4096, by omega⟩
  have state_eq :
      (⟨4096 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0064 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0065 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6845.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6845.transition (⟨4160 + candidate.val, by omega⟩ : Fin 4374) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6196Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6845.sourceLabel (⟨4160 + candidate.val, by omega⟩ : Fin 4374))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6845.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0065
    (state : Fin 4374)
    (lower : 4160 ≤ state.val)
    (upper : state.val < 4224)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6845.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6845.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6196Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6845.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6845.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 4160, by omega⟩
  have state_eq :
      (⟨4160 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0065 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0066 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6845.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6845.transition (⟨4224 + candidate.val, by omega⟩ : Fin 4374) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6196Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6845.sourceLabel (⟨4224 + candidate.val, by omega⟩ : Fin 4374))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6845.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0066
    (state : Fin 4374)
    (lower : 4224 ≤ state.val)
    (upper : state.val < 4288)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6845.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6845.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6196Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6845.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6845.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 4224, by omega⟩
  have state_eq :
      (⟨4224 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0066 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0067 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6845.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6845.transition (⟨4288 + candidate.val, by omega⟩ : Fin 4374) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6196Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6845.sourceLabel (⟨4288 + candidate.val, by omega⟩ : Fin 4374))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6845.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0067
    (state : Fin 4374)
    (lower : 4288 ≤ state.val)
    (upper : state.val < 4352)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6845.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6845.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6196Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6845.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6845.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 4288, by omega⟩
  have state_eq :
      (⟨4288 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0067 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0068 :
    ∀ candidate : Fin 22,
    ∀ generator : Fin 6,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6845.sourceLabel
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6845.transition (⟨4352 + candidate.val, by omega⟩ : Fin 4374) generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6196Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6845.sourceLabel (⟨4352 + candidate.val, by omega⟩ : Fin 4374))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6845.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0068
    (state : Fin 4374)
    (lower : 4352 ≤ state.val)
    (upper : state.val < 4374)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6845.sourceLabel (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6845.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6196Representative.sourceSemigroup.mul (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6845.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6845.generatorSourceLabel generator) := by
  let offset : Fin 22 := ⟨state.val - 4352, by omega⟩
  have state_eq :
      (⟨4352 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0068 offset generator

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6845.Shards
