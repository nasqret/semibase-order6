import SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.Support.Core
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.Shards

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0032 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 4,
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.sourceLabel
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.transition (⟨2048 + candidate.val, by omega⟩ : Fin 2712) generator) =
        SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_11390.sourceSemigroup.mul (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.sourceLabel (⟨2048 + candidate.val, by omega⟩ : Fin 2712))
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0032
    (state : Fin 2712)
    (lower : 2048 ≤ state.val)
    (upper : state.val < 2112)
    (generator : Fin 4) :
    SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.sourceLabel (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.transition state generator) =
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_11390.sourceSemigroup.mul (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.sourceLabel state)
        (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 2048, by omega⟩
  have state_eq :
      (⟨2048 + offset.val, by omega⟩ : Fin 2712) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0032 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0033 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 4,
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.sourceLabel
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.transition (⟨2112 + candidate.val, by omega⟩ : Fin 2712) generator) =
        SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_11390.sourceSemigroup.mul (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.sourceLabel (⟨2112 + candidate.val, by omega⟩ : Fin 2712))
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0033
    (state : Fin 2712)
    (lower : 2112 ≤ state.val)
    (upper : state.val < 2176)
    (generator : Fin 4) :
    SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.sourceLabel (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.transition state generator) =
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_11390.sourceSemigroup.mul (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.sourceLabel state)
        (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 2112, by omega⟩
  have state_eq :
      (⟨2112 + offset.val, by omega⟩ : Fin 2712) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0033 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0034 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 4,
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.sourceLabel
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.transition (⟨2176 + candidate.val, by omega⟩ : Fin 2712) generator) =
        SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_11390.sourceSemigroup.mul (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.sourceLabel (⟨2176 + candidate.val, by omega⟩ : Fin 2712))
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0034
    (state : Fin 2712)
    (lower : 2176 ≤ state.val)
    (upper : state.val < 2240)
    (generator : Fin 4) :
    SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.sourceLabel (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.transition state generator) =
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_11390.sourceSemigroup.mul (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.sourceLabel state)
        (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 2176, by omega⟩
  have state_eq :
      (⟨2176 + offset.val, by omega⟩ : Fin 2712) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0034 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0035 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 4,
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.sourceLabel
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.transition (⟨2240 + candidate.val, by omega⟩ : Fin 2712) generator) =
        SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_11390.sourceSemigroup.mul (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.sourceLabel (⟨2240 + candidate.val, by omega⟩ : Fin 2712))
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0035
    (state : Fin 2712)
    (lower : 2240 ≤ state.val)
    (upper : state.val < 2304)
    (generator : Fin 4) :
    SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.sourceLabel (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.transition state generator) =
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_11390.sourceSemigroup.mul (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.sourceLabel state)
        (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 2240, by omega⟩
  have state_eq :
      (⟨2240 + offset.val, by omega⟩ : Fin 2712) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0035 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0036 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 4,
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.sourceLabel
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.transition (⟨2304 + candidate.val, by omega⟩ : Fin 2712) generator) =
        SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_11390.sourceSemigroup.mul (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.sourceLabel (⟨2304 + candidate.val, by omega⟩ : Fin 2712))
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0036
    (state : Fin 2712)
    (lower : 2304 ≤ state.val)
    (upper : state.val < 2368)
    (generator : Fin 4) :
    SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.sourceLabel (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.transition state generator) =
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_11390.sourceSemigroup.mul (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.sourceLabel state)
        (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 2304, by omega⟩
  have state_eq :
      (⟨2304 + offset.val, by omega⟩ : Fin 2712) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0036 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0037 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 4,
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.sourceLabel
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.transition (⟨2368 + candidate.val, by omega⟩ : Fin 2712) generator) =
        SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_11390.sourceSemigroup.mul (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.sourceLabel (⟨2368 + candidate.val, by omega⟩ : Fin 2712))
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0037
    (state : Fin 2712)
    (lower : 2368 ≤ state.val)
    (upper : state.val < 2432)
    (generator : Fin 4) :
    SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.sourceLabel (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.transition state generator) =
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_11390.sourceSemigroup.mul (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.sourceLabel state)
        (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 2368, by omega⟩
  have state_eq :
      (⟨2368 + offset.val, by omega⟩ : Fin 2712) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0037 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0038 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 4,
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.sourceLabel
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.transition (⟨2432 + candidate.val, by omega⟩ : Fin 2712) generator) =
        SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_11390.sourceSemigroup.mul (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.sourceLabel (⟨2432 + candidate.val, by omega⟩ : Fin 2712))
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0038
    (state : Fin 2712)
    (lower : 2432 ≤ state.val)
    (upper : state.val < 2496)
    (generator : Fin 4) :
    SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.sourceLabel (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.transition state generator) =
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_11390.sourceSemigroup.mul (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.sourceLabel state)
        (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 2432, by omega⟩
  have state_eq :
      (⟨2432 + offset.val, by omega⟩ : Fin 2712) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0038 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0039 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 4,
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.sourceLabel
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.transition (⟨2496 + candidate.val, by omega⟩ : Fin 2712) generator) =
        SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_11390.sourceSemigroup.mul (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.sourceLabel (⟨2496 + candidate.val, by omega⟩ : Fin 2712))
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0039
    (state : Fin 2712)
    (lower : 2496 ≤ state.val)
    (upper : state.val < 2560)
    (generator : Fin 4) :
    SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.sourceLabel (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.transition state generator) =
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_11390.sourceSemigroup.mul (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.sourceLabel state)
        (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 2496, by omega⟩
  have state_eq :
      (⟨2496 + offset.val, by omega⟩ : Fin 2712) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0039 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0040 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 4,
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.sourceLabel
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.transition (⟨2560 + candidate.val, by omega⟩ : Fin 2712) generator) =
        SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_11390.sourceSemigroup.mul (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.sourceLabel (⟨2560 + candidate.val, by omega⟩ : Fin 2712))
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0040
    (state : Fin 2712)
    (lower : 2560 ≤ state.val)
    (upper : state.val < 2624)
    (generator : Fin 4) :
    SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.sourceLabel (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.transition state generator) =
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_11390.sourceSemigroup.mul (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.sourceLabel state)
        (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 2560, by omega⟩
  have state_eq :
      (⟨2560 + offset.val, by omega⟩ : Fin 2712) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0040 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0041 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 4,
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.sourceLabel
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.transition (⟨2624 + candidate.val, by omega⟩ : Fin 2712) generator) =
        SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_11390.sourceSemigroup.mul (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.sourceLabel (⟨2624 + candidate.val, by omega⟩ : Fin 2712))
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0041
    (state : Fin 2712)
    (lower : 2624 ≤ state.val)
    (upper : state.val < 2688)
    (generator : Fin 4) :
    SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.sourceLabel (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.transition state generator) =
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_11390.sourceSemigroup.mul (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.sourceLabel state)
        (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 2624, by omega⟩
  have state_eq :
      (⟨2624 + offset.val, by omega⟩ : Fin 2712) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0041 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0042 :
    ∀ candidate : Fin 24,
    ∀ generator : Fin 4,
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.sourceLabel
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.transition (⟨2688 + candidate.val, by omega⟩ : Fin 2712) generator) =
        SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_11390.sourceSemigroup.mul (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.sourceLabel (⟨2688 + candidate.val, by omega⟩ : Fin 2712))
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0042
    (state : Fin 2712)
    (lower : 2688 ≤ state.val)
    (upper : state.val < 2712)
    (generator : Fin 4) :
    SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.sourceLabel (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.transition state generator) =
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_11390.sourceSemigroup.mul (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.sourceLabel state)
        (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.generatorSourceLabel generator) := by
  let offset : Fin 24 := ⟨state.val - 2688, by omega⟩
  have state_eq :
      (⟨2688 + offset.val, by omega⟩ : Fin 2712) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0042 offset generator

end SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.Shards
