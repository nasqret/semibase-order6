import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.Support.Core
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.Shards

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0032 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeTail (⟨2048 + candidate.val, by omega⟩ : Fin 4374)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeHead (⟨2048 + candidate.val, by omega⟩ : Fin 4374))) =
        (⟨2048 + candidate.val, by omega⟩ : Fin 4374)
    := by
  decide

theorem representativeStateProof0032
    (state : Fin 4374)
    (lower : 2048 ≤ state.val)
    (upper : state.val < 2112) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 2048, by omega⟩
  have state_eq :
      (⟨2048 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0032 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0033 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeTail (⟨2112 + candidate.val, by omega⟩ : Fin 4374)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeHead (⟨2112 + candidate.val, by omega⟩ : Fin 4374))) =
        (⟨2112 + candidate.val, by omega⟩ : Fin 4374)
    := by
  decide

theorem representativeStateProof0033
    (state : Fin 4374)
    (lower : 2112 ≤ state.val)
    (upper : state.val < 2176) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 2112, by omega⟩
  have state_eq :
      (⟨2112 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0033 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0034 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeTail (⟨2176 + candidate.val, by omega⟩ : Fin 4374)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeHead (⟨2176 + candidate.val, by omega⟩ : Fin 4374))) =
        (⟨2176 + candidate.val, by omega⟩ : Fin 4374)
    := by
  decide

theorem representativeStateProof0034
    (state : Fin 4374)
    (lower : 2176 ≤ state.val)
    (upper : state.val < 2240) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 2176, by omega⟩
  have state_eq :
      (⟨2176 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0034 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0035 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeTail (⟨2240 + candidate.val, by omega⟩ : Fin 4374)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeHead (⟨2240 + candidate.val, by omega⟩ : Fin 4374))) =
        (⟨2240 + candidate.val, by omega⟩ : Fin 4374)
    := by
  decide

theorem representativeStateProof0035
    (state : Fin 4374)
    (lower : 2240 ≤ state.val)
    (upper : state.val < 2304) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 2240, by omega⟩
  have state_eq :
      (⟨2240 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0035 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0036 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeTail (⟨2304 + candidate.val, by omega⟩ : Fin 4374)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeHead (⟨2304 + candidate.val, by omega⟩ : Fin 4374))) =
        (⟨2304 + candidate.val, by omega⟩ : Fin 4374)
    := by
  decide

theorem representativeStateProof0036
    (state : Fin 4374)
    (lower : 2304 ≤ state.val)
    (upper : state.val < 2368) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 2304, by omega⟩
  have state_eq :
      (⟨2304 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0036 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0037 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeTail (⟨2368 + candidate.val, by omega⟩ : Fin 4374)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeHead (⟨2368 + candidate.val, by omega⟩ : Fin 4374))) =
        (⟨2368 + candidate.val, by omega⟩ : Fin 4374)
    := by
  decide

theorem representativeStateProof0037
    (state : Fin 4374)
    (lower : 2368 ≤ state.val)
    (upper : state.val < 2432) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 2368, by omega⟩
  have state_eq :
      (⟨2368 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0037 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0038 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeTail (⟨2432 + candidate.val, by omega⟩ : Fin 4374)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeHead (⟨2432 + candidate.val, by omega⟩ : Fin 4374))) =
        (⟨2432 + candidate.val, by omega⟩ : Fin 4374)
    := by
  decide

theorem representativeStateProof0038
    (state : Fin 4374)
    (lower : 2432 ≤ state.val)
    (upper : state.val < 2496) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 2432, by omega⟩
  have state_eq :
      (⟨2432 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0038 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0039 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeTail (⟨2496 + candidate.val, by omega⟩ : Fin 4374)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeHead (⟨2496 + candidate.val, by omega⟩ : Fin 4374))) =
        (⟨2496 + candidate.val, by omega⟩ : Fin 4374)
    := by
  decide

theorem representativeStateProof0039
    (state : Fin 4374)
    (lower : 2496 ≤ state.val)
    (upper : state.val < 2560) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 2496, by omega⟩
  have state_eq :
      (⟨2496 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0039 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0040 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeTail (⟨2560 + candidate.val, by omega⟩ : Fin 4374)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeHead (⟨2560 + candidate.val, by omega⟩ : Fin 4374))) =
        (⟨2560 + candidate.val, by omega⟩ : Fin 4374)
    := by
  decide

theorem representativeStateProof0040
    (state : Fin 4374)
    (lower : 2560 ≤ state.val)
    (upper : state.val < 2624) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 2560, by omega⟩
  have state_eq :
      (⟨2560 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0040 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0041 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeTail (⟨2624 + candidate.val, by omega⟩ : Fin 4374)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeHead (⟨2624 + candidate.val, by omega⟩ : Fin 4374))) =
        (⟨2624 + candidate.val, by omega⟩ : Fin 4374)
    := by
  decide

theorem representativeStateProof0041
    (state : Fin 4374)
    (lower : 2624 ≤ state.val)
    (upper : state.val < 2688) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 2624, by omega⟩
  have state_eq :
      (⟨2624 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0041 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0042 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeTail (⟨2688 + candidate.val, by omega⟩ : Fin 4374)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeHead (⟨2688 + candidate.val, by omega⟩ : Fin 4374))) =
        (⟨2688 + candidate.val, by omega⟩ : Fin 4374)
    := by
  decide

theorem representativeStateProof0042
    (state : Fin 4374)
    (lower : 2688 ≤ state.val)
    (upper : state.val < 2752) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 2688, by omega⟩
  have state_eq :
      (⟨2688 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0042 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0043 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeTail (⟨2752 + candidate.val, by omega⟩ : Fin 4374)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeHead (⟨2752 + candidate.val, by omega⟩ : Fin 4374))) =
        (⟨2752 + candidate.val, by omega⟩ : Fin 4374)
    := by
  decide

theorem representativeStateProof0043
    (state : Fin 4374)
    (lower : 2752 ≤ state.val)
    (upper : state.val < 2816) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 2752, by omega⟩
  have state_eq :
      (⟨2752 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0043 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0044 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeTail (⟨2816 + candidate.val, by omega⟩ : Fin 4374)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeHead (⟨2816 + candidate.val, by omega⟩ : Fin 4374))) =
        (⟨2816 + candidate.val, by omega⟩ : Fin 4374)
    := by
  decide

theorem representativeStateProof0044
    (state : Fin 4374)
    (lower : 2816 ≤ state.val)
    (upper : state.val < 2880) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 2816, by omega⟩
  have state_eq :
      (⟨2816 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0044 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0045 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeTail (⟨2880 + candidate.val, by omega⟩ : Fin 4374)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeHead (⟨2880 + candidate.val, by omega⟩ : Fin 4374))) =
        (⟨2880 + candidate.val, by omega⟩ : Fin 4374)
    := by
  decide

theorem representativeStateProof0045
    (state : Fin 4374)
    (lower : 2880 ≤ state.val)
    (upper : state.val < 2944) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 2880, by omega⟩
  have state_eq :
      (⟨2880 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0045 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0046 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeTail (⟨2944 + candidate.val, by omega⟩ : Fin 4374)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeHead (⟨2944 + candidate.val, by omega⟩ : Fin 4374))) =
        (⟨2944 + candidate.val, by omega⟩ : Fin 4374)
    := by
  decide

theorem representativeStateProof0046
    (state : Fin 4374)
    (lower : 2944 ≤ state.val)
    (upper : state.val < 3008) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 2944, by omega⟩
  have state_eq :
      (⟨2944 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0046 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0047 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeTail (⟨3008 + candidate.val, by omega⟩ : Fin 4374)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeHead (⟨3008 + candidate.val, by omega⟩ : Fin 4374))) =
        (⟨3008 + candidate.val, by omega⟩ : Fin 4374)
    := by
  decide

theorem representativeStateProof0047
    (state : Fin 4374)
    (lower : 3008 ≤ state.val)
    (upper : state.val < 3072) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 3008, by omega⟩
  have state_eq :
      (⟨3008 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0047 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0048 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeTail (⟨3072 + candidate.val, by omega⟩ : Fin 4374)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeHead (⟨3072 + candidate.val, by omega⟩ : Fin 4374))) =
        (⟨3072 + candidate.val, by omega⟩ : Fin 4374)
    := by
  decide

theorem representativeStateProof0048
    (state : Fin 4374)
    (lower : 3072 ≤ state.val)
    (upper : state.val < 3136) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 3072, by omega⟩
  have state_eq :
      (⟨3072 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0048 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0049 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeTail (⟨3136 + candidate.val, by omega⟩ : Fin 4374)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeHead (⟨3136 + candidate.val, by omega⟩ : Fin 4374))) =
        (⟨3136 + candidate.val, by omega⟩ : Fin 4374)
    := by
  decide

theorem representativeStateProof0049
    (state : Fin 4374)
    (lower : 3136 ≤ state.val)
    (upper : state.val < 3200) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 3136, by omega⟩
  have state_eq :
      (⟨3136 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0049 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0050 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeTail (⟨3200 + candidate.val, by omega⟩ : Fin 4374)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeHead (⟨3200 + candidate.val, by omega⟩ : Fin 4374))) =
        (⟨3200 + candidate.val, by omega⟩ : Fin 4374)
    := by
  decide

theorem representativeStateProof0050
    (state : Fin 4374)
    (lower : 3200 ≤ state.val)
    (upper : state.val < 3264) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 3200, by omega⟩
  have state_eq :
      (⟨3200 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0050 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0051 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeTail (⟨3264 + candidate.val, by omega⟩ : Fin 4374)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeHead (⟨3264 + candidate.val, by omega⟩ : Fin 4374))) =
        (⟨3264 + candidate.val, by omega⟩ : Fin 4374)
    := by
  decide

theorem representativeStateProof0051
    (state : Fin 4374)
    (lower : 3264 ≤ state.val)
    (upper : state.val < 3328) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 3264, by omega⟩
  have state_eq :
      (⟨3264 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0051 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0052 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeTail (⟨3328 + candidate.val, by omega⟩ : Fin 4374)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeHead (⟨3328 + candidate.val, by omega⟩ : Fin 4374))) =
        (⟨3328 + candidate.val, by omega⟩ : Fin 4374)
    := by
  decide

theorem representativeStateProof0052
    (state : Fin 4374)
    (lower : 3328 ≤ state.val)
    (upper : state.val < 3392) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 3328, by omega⟩
  have state_eq :
      (⟨3328 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0052 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0053 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeTail (⟨3392 + candidate.val, by omega⟩ : Fin 4374)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeHead (⟨3392 + candidate.val, by omega⟩ : Fin 4374))) =
        (⟨3392 + candidate.val, by omega⟩ : Fin 4374)
    := by
  decide

theorem representativeStateProof0053
    (state : Fin 4374)
    (lower : 3392 ≤ state.val)
    (upper : state.val < 3456) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 3392, by omega⟩
  have state_eq :
      (⟨3392 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0053 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0054 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeTail (⟨3456 + candidate.val, by omega⟩ : Fin 4374)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeHead (⟨3456 + candidate.val, by omega⟩ : Fin 4374))) =
        (⟨3456 + candidate.val, by omega⟩ : Fin 4374)
    := by
  decide

theorem representativeStateProof0054
    (state : Fin 4374)
    (lower : 3456 ≤ state.val)
    (upper : state.val < 3520) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 3456, by omega⟩
  have state_eq :
      (⟨3456 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0054 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0055 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeTail (⟨3520 + candidate.val, by omega⟩ : Fin 4374)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeHead (⟨3520 + candidate.val, by omega⟩ : Fin 4374))) =
        (⟨3520 + candidate.val, by omega⟩ : Fin 4374)
    := by
  decide

theorem representativeStateProof0055
    (state : Fin 4374)
    (lower : 3520 ≤ state.val)
    (upper : state.val < 3584) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 3520, by omega⟩
  have state_eq :
      (⟨3520 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0055 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0056 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeTail (⟨3584 + candidate.val, by omega⟩ : Fin 4374)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeHead (⟨3584 + candidate.val, by omega⟩ : Fin 4374))) =
        (⟨3584 + candidate.val, by omega⟩ : Fin 4374)
    := by
  decide

theorem representativeStateProof0056
    (state : Fin 4374)
    (lower : 3584 ≤ state.val)
    (upper : state.val < 3648) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 3584, by omega⟩
  have state_eq :
      (⟨3584 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0056 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0057 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeTail (⟨3648 + candidate.val, by omega⟩ : Fin 4374)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeHead (⟨3648 + candidate.val, by omega⟩ : Fin 4374))) =
        (⟨3648 + candidate.val, by omega⟩ : Fin 4374)
    := by
  decide

theorem representativeStateProof0057
    (state : Fin 4374)
    (lower : 3648 ≤ state.val)
    (upper : state.val < 3712) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 3648, by omega⟩
  have state_eq :
      (⟨3648 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0057 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0058 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeTail (⟨3712 + candidate.val, by omega⟩ : Fin 4374)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeHead (⟨3712 + candidate.val, by omega⟩ : Fin 4374))) =
        (⟨3712 + candidate.val, by omega⟩ : Fin 4374)
    := by
  decide

theorem representativeStateProof0058
    (state : Fin 4374)
    (lower : 3712 ≤ state.val)
    (upper : state.val < 3776) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 3712, by omega⟩
  have state_eq :
      (⟨3712 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0058 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0059 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeTail (⟨3776 + candidate.val, by omega⟩ : Fin 4374)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeHead (⟨3776 + candidate.val, by omega⟩ : Fin 4374))) =
        (⟨3776 + candidate.val, by omega⟩ : Fin 4374)
    := by
  decide

theorem representativeStateProof0059
    (state : Fin 4374)
    (lower : 3776 ≤ state.val)
    (upper : state.val < 3840) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 3776, by omega⟩
  have state_eq :
      (⟨3776 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0059 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0060 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeTail (⟨3840 + candidate.val, by omega⟩ : Fin 4374)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeHead (⟨3840 + candidate.val, by omega⟩ : Fin 4374))) =
        (⟨3840 + candidate.val, by omega⟩ : Fin 4374)
    := by
  decide

theorem representativeStateProof0060
    (state : Fin 4374)
    (lower : 3840 ≤ state.val)
    (upper : state.val < 3904) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 3840, by omega⟩
  have state_eq :
      (⟨3840 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0060 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0061 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeTail (⟨3904 + candidate.val, by omega⟩ : Fin 4374)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeHead (⟨3904 + candidate.val, by omega⟩ : Fin 4374))) =
        (⟨3904 + candidate.val, by omega⟩ : Fin 4374)
    := by
  decide

theorem representativeStateProof0061
    (state : Fin 4374)
    (lower : 3904 ≤ state.val)
    (upper : state.val < 3968) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 3904, by omega⟩
  have state_eq :
      (⟨3904 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0061 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0062 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeTail (⟨3968 + candidate.val, by omega⟩ : Fin 4374)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeHead (⟨3968 + candidate.val, by omega⟩ : Fin 4374))) =
        (⟨3968 + candidate.val, by omega⟩ : Fin 4374)
    := by
  decide

theorem representativeStateProof0062
    (state : Fin 4374)
    (lower : 3968 ≤ state.val)
    (upper : state.val < 4032) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 3968, by omega⟩
  have state_eq :
      (⟨3968 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0062 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0063 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeTail (⟨4032 + candidate.val, by omega⟩ : Fin 4374)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeHead (⟨4032 + candidate.val, by omega⟩ : Fin 4374))) =
        (⟨4032 + candidate.val, by omega⟩ : Fin 4374)
    := by
  decide

theorem representativeStateProof0063
    (state : Fin 4374)
    (lower : 4032 ≤ state.val)
    (upper : state.val < 4096) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 4032, by omega⟩
  have state_eq :
      (⟨4032 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0063 offset

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.Shards
