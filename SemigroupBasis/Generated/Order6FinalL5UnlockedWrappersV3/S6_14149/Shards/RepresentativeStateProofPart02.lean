import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.Support.Core
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.Shards

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0064 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeTail (⟨4096 + candidate.val, by omega⟩ : Fin 11184)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeHead (⟨4096 + candidate.val, by omega⟩ : Fin 11184))) =
        (⟨4096 + candidate.val, by omega⟩ : Fin 11184)
    := by
  decide

theorem representativeStateProof0064
    (state : Fin 11184)
    (lower : 4096 ≤ state.val)
    (upper : state.val < 4160) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 4096, by omega⟩
  have state_eq :
      (⟨4096 + offset.val, by omega⟩ : Fin 11184) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0064 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0065 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeTail (⟨4160 + candidate.val, by omega⟩ : Fin 11184)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeHead (⟨4160 + candidate.val, by omega⟩ : Fin 11184))) =
        (⟨4160 + candidate.val, by omega⟩ : Fin 11184)
    := by
  decide

theorem representativeStateProof0065
    (state : Fin 11184)
    (lower : 4160 ≤ state.val)
    (upper : state.val < 4224) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 4160, by omega⟩
  have state_eq :
      (⟨4160 + offset.val, by omega⟩ : Fin 11184) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0065 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0066 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeTail (⟨4224 + candidate.val, by omega⟩ : Fin 11184)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeHead (⟨4224 + candidate.val, by omega⟩ : Fin 11184))) =
        (⟨4224 + candidate.val, by omega⟩ : Fin 11184)
    := by
  decide

theorem representativeStateProof0066
    (state : Fin 11184)
    (lower : 4224 ≤ state.val)
    (upper : state.val < 4288) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 4224, by omega⟩
  have state_eq :
      (⟨4224 + offset.val, by omega⟩ : Fin 11184) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0066 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0067 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeTail (⟨4288 + candidate.val, by omega⟩ : Fin 11184)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeHead (⟨4288 + candidate.val, by omega⟩ : Fin 11184))) =
        (⟨4288 + candidate.val, by omega⟩ : Fin 11184)
    := by
  decide

theorem representativeStateProof0067
    (state : Fin 11184)
    (lower : 4288 ≤ state.val)
    (upper : state.val < 4352) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 4288, by omega⟩
  have state_eq :
      (⟨4288 + offset.val, by omega⟩ : Fin 11184) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0067 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0068 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeTail (⟨4352 + candidate.val, by omega⟩ : Fin 11184)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeHead (⟨4352 + candidate.val, by omega⟩ : Fin 11184))) =
        (⟨4352 + candidate.val, by omega⟩ : Fin 11184)
    := by
  decide

theorem representativeStateProof0068
    (state : Fin 11184)
    (lower : 4352 ≤ state.val)
    (upper : state.val < 4416) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 4352, by omega⟩
  have state_eq :
      (⟨4352 + offset.val, by omega⟩ : Fin 11184) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0068 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0069 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeTail (⟨4416 + candidate.val, by omega⟩ : Fin 11184)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeHead (⟨4416 + candidate.val, by omega⟩ : Fin 11184))) =
        (⟨4416 + candidate.val, by omega⟩ : Fin 11184)
    := by
  decide

theorem representativeStateProof0069
    (state : Fin 11184)
    (lower : 4416 ≤ state.val)
    (upper : state.val < 4480) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 4416, by omega⟩
  have state_eq :
      (⟨4416 + offset.val, by omega⟩ : Fin 11184) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0069 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0070 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeTail (⟨4480 + candidate.val, by omega⟩ : Fin 11184)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeHead (⟨4480 + candidate.val, by omega⟩ : Fin 11184))) =
        (⟨4480 + candidate.val, by omega⟩ : Fin 11184)
    := by
  decide

theorem representativeStateProof0070
    (state : Fin 11184)
    (lower : 4480 ≤ state.val)
    (upper : state.val < 4544) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 4480, by omega⟩
  have state_eq :
      (⟨4480 + offset.val, by omega⟩ : Fin 11184) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0070 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0071 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeTail (⟨4544 + candidate.val, by omega⟩ : Fin 11184)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeHead (⟨4544 + candidate.val, by omega⟩ : Fin 11184))) =
        (⟨4544 + candidate.val, by omega⟩ : Fin 11184)
    := by
  decide

theorem representativeStateProof0071
    (state : Fin 11184)
    (lower : 4544 ≤ state.val)
    (upper : state.val < 4608) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 4544, by omega⟩
  have state_eq :
      (⟨4544 + offset.val, by omega⟩ : Fin 11184) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0071 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0072 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeTail (⟨4608 + candidate.val, by omega⟩ : Fin 11184)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeHead (⟨4608 + candidate.val, by omega⟩ : Fin 11184))) =
        (⟨4608 + candidate.val, by omega⟩ : Fin 11184)
    := by
  decide

theorem representativeStateProof0072
    (state : Fin 11184)
    (lower : 4608 ≤ state.val)
    (upper : state.val < 4672) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 4608, by omega⟩
  have state_eq :
      (⟨4608 + offset.val, by omega⟩ : Fin 11184) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0072 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0073 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeTail (⟨4672 + candidate.val, by omega⟩ : Fin 11184)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeHead (⟨4672 + candidate.val, by omega⟩ : Fin 11184))) =
        (⟨4672 + candidate.val, by omega⟩ : Fin 11184)
    := by
  decide

theorem representativeStateProof0073
    (state : Fin 11184)
    (lower : 4672 ≤ state.val)
    (upper : state.val < 4736) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 4672, by omega⟩
  have state_eq :
      (⟨4672 + offset.val, by omega⟩ : Fin 11184) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0073 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0074 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeTail (⟨4736 + candidate.val, by omega⟩ : Fin 11184)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeHead (⟨4736 + candidate.val, by omega⟩ : Fin 11184))) =
        (⟨4736 + candidate.val, by omega⟩ : Fin 11184)
    := by
  decide

theorem representativeStateProof0074
    (state : Fin 11184)
    (lower : 4736 ≤ state.val)
    (upper : state.val < 4800) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 4736, by omega⟩
  have state_eq :
      (⟨4736 + offset.val, by omega⟩ : Fin 11184) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0074 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0075 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeTail (⟨4800 + candidate.val, by omega⟩ : Fin 11184)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeHead (⟨4800 + candidate.val, by omega⟩ : Fin 11184))) =
        (⟨4800 + candidate.val, by omega⟩ : Fin 11184)
    := by
  decide

theorem representativeStateProof0075
    (state : Fin 11184)
    (lower : 4800 ≤ state.val)
    (upper : state.val < 4864) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 4800, by omega⟩
  have state_eq :
      (⟨4800 + offset.val, by omega⟩ : Fin 11184) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0075 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0076 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeTail (⟨4864 + candidate.val, by omega⟩ : Fin 11184)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeHead (⟨4864 + candidate.val, by omega⟩ : Fin 11184))) =
        (⟨4864 + candidate.val, by omega⟩ : Fin 11184)
    := by
  decide

theorem representativeStateProof0076
    (state : Fin 11184)
    (lower : 4864 ≤ state.val)
    (upper : state.val < 4928) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 4864, by omega⟩
  have state_eq :
      (⟨4864 + offset.val, by omega⟩ : Fin 11184) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0076 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0077 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeTail (⟨4928 + candidate.val, by omega⟩ : Fin 11184)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeHead (⟨4928 + candidate.val, by omega⟩ : Fin 11184))) =
        (⟨4928 + candidate.val, by omega⟩ : Fin 11184)
    := by
  decide

theorem representativeStateProof0077
    (state : Fin 11184)
    (lower : 4928 ≤ state.val)
    (upper : state.val < 4992) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 4928, by omega⟩
  have state_eq :
      (⟨4928 + offset.val, by omega⟩ : Fin 11184) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0077 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0078 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeTail (⟨4992 + candidate.val, by omega⟩ : Fin 11184)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeHead (⟨4992 + candidate.val, by omega⟩ : Fin 11184))) =
        (⟨4992 + candidate.val, by omega⟩ : Fin 11184)
    := by
  decide

theorem representativeStateProof0078
    (state : Fin 11184)
    (lower : 4992 ≤ state.val)
    (upper : state.val < 5056) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 4992, by omega⟩
  have state_eq :
      (⟨4992 + offset.val, by omega⟩ : Fin 11184) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0078 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0079 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeTail (⟨5056 + candidate.val, by omega⟩ : Fin 11184)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeHead (⟨5056 + candidate.val, by omega⟩ : Fin 11184))) =
        (⟨5056 + candidate.val, by omega⟩ : Fin 11184)
    := by
  decide

theorem representativeStateProof0079
    (state : Fin 11184)
    (lower : 5056 ≤ state.val)
    (upper : state.val < 5120) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 5056, by omega⟩
  have state_eq :
      (⟨5056 + offset.val, by omega⟩ : Fin 11184) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0079 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0080 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeTail (⟨5120 + candidate.val, by omega⟩ : Fin 11184)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeHead (⟨5120 + candidate.val, by omega⟩ : Fin 11184))) =
        (⟨5120 + candidate.val, by omega⟩ : Fin 11184)
    := by
  decide

theorem representativeStateProof0080
    (state : Fin 11184)
    (lower : 5120 ≤ state.val)
    (upper : state.val < 5184) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 5120, by omega⟩
  have state_eq :
      (⟨5120 + offset.val, by omega⟩ : Fin 11184) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0080 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0081 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeTail (⟨5184 + candidate.val, by omega⟩ : Fin 11184)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeHead (⟨5184 + candidate.val, by omega⟩ : Fin 11184))) =
        (⟨5184 + candidate.val, by omega⟩ : Fin 11184)
    := by
  decide

theorem representativeStateProof0081
    (state : Fin 11184)
    (lower : 5184 ≤ state.val)
    (upper : state.val < 5248) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 5184, by omega⟩
  have state_eq :
      (⟨5184 + offset.val, by omega⟩ : Fin 11184) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0081 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0082 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeTail (⟨5248 + candidate.val, by omega⟩ : Fin 11184)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeHead (⟨5248 + candidate.val, by omega⟩ : Fin 11184))) =
        (⟨5248 + candidate.val, by omega⟩ : Fin 11184)
    := by
  decide

theorem representativeStateProof0082
    (state : Fin 11184)
    (lower : 5248 ≤ state.val)
    (upper : state.val < 5312) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 5248, by omega⟩
  have state_eq :
      (⟨5248 + offset.val, by omega⟩ : Fin 11184) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0082 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0083 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeTail (⟨5312 + candidate.val, by omega⟩ : Fin 11184)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeHead (⟨5312 + candidate.val, by omega⟩ : Fin 11184))) =
        (⟨5312 + candidate.val, by omega⟩ : Fin 11184)
    := by
  decide

theorem representativeStateProof0083
    (state : Fin 11184)
    (lower : 5312 ≤ state.val)
    (upper : state.val < 5376) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 5312, by omega⟩
  have state_eq :
      (⟨5312 + offset.val, by omega⟩ : Fin 11184) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0083 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0084 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeTail (⟨5376 + candidate.val, by omega⟩ : Fin 11184)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeHead (⟨5376 + candidate.val, by omega⟩ : Fin 11184))) =
        (⟨5376 + candidate.val, by omega⟩ : Fin 11184)
    := by
  decide

theorem representativeStateProof0084
    (state : Fin 11184)
    (lower : 5376 ≤ state.val)
    (upper : state.val < 5440) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 5376, by omega⟩
  have state_eq :
      (⟨5376 + offset.val, by omega⟩ : Fin 11184) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0084 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0085 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeTail (⟨5440 + candidate.val, by omega⟩ : Fin 11184)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeHead (⟨5440 + candidate.val, by omega⟩ : Fin 11184))) =
        (⟨5440 + candidate.val, by omega⟩ : Fin 11184)
    := by
  decide

theorem representativeStateProof0085
    (state : Fin 11184)
    (lower : 5440 ≤ state.val)
    (upper : state.val < 5504) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 5440, by omega⟩
  have state_eq :
      (⟨5440 + offset.val, by omega⟩ : Fin 11184) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0085 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0086 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeTail (⟨5504 + candidate.val, by omega⟩ : Fin 11184)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeHead (⟨5504 + candidate.val, by omega⟩ : Fin 11184))) =
        (⟨5504 + candidate.val, by omega⟩ : Fin 11184)
    := by
  decide

theorem representativeStateProof0086
    (state : Fin 11184)
    (lower : 5504 ≤ state.val)
    (upper : state.val < 5568) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 5504, by omega⟩
  have state_eq :
      (⟨5504 + offset.val, by omega⟩ : Fin 11184) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0086 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0087 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeTail (⟨5568 + candidate.val, by omega⟩ : Fin 11184)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeHead (⟨5568 + candidate.val, by omega⟩ : Fin 11184))) =
        (⟨5568 + candidate.val, by omega⟩ : Fin 11184)
    := by
  decide

theorem representativeStateProof0087
    (state : Fin 11184)
    (lower : 5568 ≤ state.val)
    (upper : state.val < 5632) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 5568, by omega⟩
  have state_eq :
      (⟨5568 + offset.val, by omega⟩ : Fin 11184) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0087 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0088 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeTail (⟨5632 + candidate.val, by omega⟩ : Fin 11184)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeHead (⟨5632 + candidate.val, by omega⟩ : Fin 11184))) =
        (⟨5632 + candidate.val, by omega⟩ : Fin 11184)
    := by
  decide

theorem representativeStateProof0088
    (state : Fin 11184)
    (lower : 5632 ≤ state.val)
    (upper : state.val < 5696) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 5632, by omega⟩
  have state_eq :
      (⟨5632 + offset.val, by omega⟩ : Fin 11184) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0088 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0089 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeTail (⟨5696 + candidate.val, by omega⟩ : Fin 11184)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeHead (⟨5696 + candidate.val, by omega⟩ : Fin 11184))) =
        (⟨5696 + candidate.val, by omega⟩ : Fin 11184)
    := by
  decide

theorem representativeStateProof0089
    (state : Fin 11184)
    (lower : 5696 ≤ state.val)
    (upper : state.val < 5760) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 5696, by omega⟩
  have state_eq :
      (⟨5696 + offset.val, by omega⟩ : Fin 11184) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0089 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0090 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeTail (⟨5760 + candidate.val, by omega⟩ : Fin 11184)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeHead (⟨5760 + candidate.val, by omega⟩ : Fin 11184))) =
        (⟨5760 + candidate.val, by omega⟩ : Fin 11184)
    := by
  decide

theorem representativeStateProof0090
    (state : Fin 11184)
    (lower : 5760 ≤ state.val)
    (upper : state.val < 5824) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 5760, by omega⟩
  have state_eq :
      (⟨5760 + offset.val, by omega⟩ : Fin 11184) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0090 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0091 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeTail (⟨5824 + candidate.val, by omega⟩ : Fin 11184)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeHead (⟨5824 + candidate.val, by omega⟩ : Fin 11184))) =
        (⟨5824 + candidate.val, by omega⟩ : Fin 11184)
    := by
  decide

theorem representativeStateProof0091
    (state : Fin 11184)
    (lower : 5824 ≤ state.val)
    (upper : state.val < 5888) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 5824, by omega⟩
  have state_eq :
      (⟨5824 + offset.val, by omega⟩ : Fin 11184) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0091 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0092 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeTail (⟨5888 + candidate.val, by omega⟩ : Fin 11184)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeHead (⟨5888 + candidate.val, by omega⟩ : Fin 11184))) =
        (⟨5888 + candidate.val, by omega⟩ : Fin 11184)
    := by
  decide

theorem representativeStateProof0092
    (state : Fin 11184)
    (lower : 5888 ≤ state.val)
    (upper : state.val < 5952) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 5888, by omega⟩
  have state_eq :
      (⟨5888 + offset.val, by omega⟩ : Fin 11184) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0092 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0093 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeTail (⟨5952 + candidate.val, by omega⟩ : Fin 11184)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeHead (⟨5952 + candidate.val, by omega⟩ : Fin 11184))) =
        (⟨5952 + candidate.val, by omega⟩ : Fin 11184)
    := by
  decide

theorem representativeStateProof0093
    (state : Fin 11184)
    (lower : 5952 ≤ state.val)
    (upper : state.val < 6016) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 5952, by omega⟩
  have state_eq :
      (⟨5952 + offset.val, by omega⟩ : Fin 11184) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0093 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0094 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeTail (⟨6016 + candidate.val, by omega⟩ : Fin 11184)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeHead (⟨6016 + candidate.val, by omega⟩ : Fin 11184))) =
        (⟨6016 + candidate.val, by omega⟩ : Fin 11184)
    := by
  decide

theorem representativeStateProof0094
    (state : Fin 11184)
    (lower : 6016 ≤ state.val)
    (upper : state.val < 6080) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 6016, by omega⟩
  have state_eq :
      (⟨6016 + offset.val, by omega⟩ : Fin 11184) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0094 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0095 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeTail (⟨6080 + candidate.val, by omega⟩ : Fin 11184)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeHead (⟨6080 + candidate.val, by omega⟩ : Fin 11184))) =
        (⟨6080 + candidate.val, by omega⟩ : Fin 11184)
    := by
  decide

theorem representativeStateProof0095
    (state : Fin 11184)
    (lower : 6080 ≤ state.val)
    (upper : state.val < 6144) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 6080, by omega⟩
  have state_eq :
      (⟨6080 + offset.val, by omega⟩ : Fin 11184) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0095 offset

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.Shards
