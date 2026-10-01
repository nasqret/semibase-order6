import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.Support.Core
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.Shards

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0064 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.representativeTail (⟨4096 + candidate.val, by omega⟩ : Fin 4374)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.representativeHead (⟨4096 + candidate.val, by omega⟩ : Fin 4374))) =
        (⟨4096 + candidate.val, by omega⟩ : Fin 4374)
    := by
  decide

theorem representativeStateProof0064
    (state : Fin 4374)
    (lower : 4096 ≤ state.val)
    (upper : state.val < 4160) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 4096, by omega⟩
  have state_eq :
      (⟨4096 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0064 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0065 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.representativeTail (⟨4160 + candidate.val, by omega⟩ : Fin 4374)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.representativeHead (⟨4160 + candidate.val, by omega⟩ : Fin 4374))) =
        (⟨4160 + candidate.val, by omega⟩ : Fin 4374)
    := by
  decide

theorem representativeStateProof0065
    (state : Fin 4374)
    (lower : 4160 ≤ state.val)
    (upper : state.val < 4224) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 4160, by omega⟩
  have state_eq :
      (⟨4160 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0065 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0066 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.representativeTail (⟨4224 + candidate.val, by omega⟩ : Fin 4374)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.representativeHead (⟨4224 + candidate.val, by omega⟩ : Fin 4374))) =
        (⟨4224 + candidate.val, by omega⟩ : Fin 4374)
    := by
  decide

theorem representativeStateProof0066
    (state : Fin 4374)
    (lower : 4224 ≤ state.val)
    (upper : state.val < 4288) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 4224, by omega⟩
  have state_eq :
      (⟨4224 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0066 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0067 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.representativeTail (⟨4288 + candidate.val, by omega⟩ : Fin 4374)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.representativeHead (⟨4288 + candidate.val, by omega⟩ : Fin 4374))) =
        (⟨4288 + candidate.val, by omega⟩ : Fin 4374)
    := by
  decide

theorem representativeStateProof0067
    (state : Fin 4374)
    (lower : 4288 ≤ state.val)
    (upper : state.val < 4352) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 4288, by omega⟩
  have state_eq :
      (⟨4288 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0067 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0068 :
    ∀ candidate : Fin 22,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.representativeTail (⟨4352 + candidate.val, by omega⟩ : Fin 4374)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.representativeHead (⟨4352 + candidate.val, by omega⟩ : Fin 4374))) =
        (⟨4352 + candidate.val, by omega⟩ : Fin 4374)
    := by
  decide

theorem representativeStateProof0068
    (state : Fin 4374)
    (lower : 4352 ≤ state.val)
    (upper : state.val < 4374) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.representativeHead state)) =
      state
    := by
  let offset : Fin 22 := ⟨state.val - 4352, by omega⟩
  have state_eq :
      (⟨4352 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0068 offset

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.Shards
