import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Support.Core
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0704 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨45056 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨45056 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨45056 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0704
    (state : Fin 48684)
    (lower : 45056 ≤ state.val)
    (upper : state.val < 45120) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 45056, by omega⟩
  have state_eq :
      (⟨45056 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0704 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0705 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨45120 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨45120 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨45120 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0705
    (state : Fin 48684)
    (lower : 45120 ≤ state.val)
    (upper : state.val < 45184) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 45120, by omega⟩
  have state_eq :
      (⟨45120 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0705 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0706 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨45184 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨45184 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨45184 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0706
    (state : Fin 48684)
    (lower : 45184 ≤ state.val)
    (upper : state.val < 45248) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 45184, by omega⟩
  have state_eq :
      (⟨45184 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0706 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0707 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨45248 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨45248 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨45248 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0707
    (state : Fin 48684)
    (lower : 45248 ≤ state.val)
    (upper : state.val < 45312) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 45248, by omega⟩
  have state_eq :
      (⟨45248 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0707 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0708 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨45312 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨45312 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨45312 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0708
    (state : Fin 48684)
    (lower : 45312 ≤ state.val)
    (upper : state.val < 45376) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 45312, by omega⟩
  have state_eq :
      (⟨45312 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0708 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0709 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨45376 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨45376 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨45376 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0709
    (state : Fin 48684)
    (lower : 45376 ≤ state.val)
    (upper : state.val < 45440) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 45376, by omega⟩
  have state_eq :
      (⟨45376 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0709 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0710 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨45440 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨45440 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨45440 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0710
    (state : Fin 48684)
    (lower : 45440 ≤ state.val)
    (upper : state.val < 45504) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 45440, by omega⟩
  have state_eq :
      (⟨45440 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0710 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0711 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨45504 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨45504 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨45504 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0711
    (state : Fin 48684)
    (lower : 45504 ≤ state.val)
    (upper : state.val < 45568) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 45504, by omega⟩
  have state_eq :
      (⟨45504 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0711 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0712 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨45568 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨45568 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨45568 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0712
    (state : Fin 48684)
    (lower : 45568 ≤ state.val)
    (upper : state.val < 45632) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 45568, by omega⟩
  have state_eq :
      (⟨45568 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0712 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0713 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨45632 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨45632 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨45632 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0713
    (state : Fin 48684)
    (lower : 45632 ≤ state.val)
    (upper : state.val < 45696) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 45632, by omega⟩
  have state_eq :
      (⟨45632 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0713 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0714 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨45696 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨45696 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨45696 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0714
    (state : Fin 48684)
    (lower : 45696 ≤ state.val)
    (upper : state.val < 45760) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 45696, by omega⟩
  have state_eq :
      (⟨45696 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0714 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0715 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨45760 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨45760 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨45760 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0715
    (state : Fin 48684)
    (lower : 45760 ≤ state.val)
    (upper : state.val < 45824) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 45760, by omega⟩
  have state_eq :
      (⟨45760 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0715 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0716 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨45824 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨45824 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨45824 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0716
    (state : Fin 48684)
    (lower : 45824 ≤ state.val)
    (upper : state.val < 45888) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 45824, by omega⟩
  have state_eq :
      (⟨45824 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0716 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0717 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨45888 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨45888 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨45888 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0717
    (state : Fin 48684)
    (lower : 45888 ≤ state.val)
    (upper : state.val < 45952) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 45888, by omega⟩
  have state_eq :
      (⟨45888 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0717 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0718 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨45952 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨45952 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨45952 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0718
    (state : Fin 48684)
    (lower : 45952 ≤ state.val)
    (upper : state.val < 46016) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 45952, by omega⟩
  have state_eq :
      (⟨45952 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0718 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0719 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨46016 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨46016 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨46016 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0719
    (state : Fin 48684)
    (lower : 46016 ≤ state.val)
    (upper : state.val < 46080) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 46016, by omega⟩
  have state_eq :
      (⟨46016 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0719 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0720 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨46080 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨46080 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨46080 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0720
    (state : Fin 48684)
    (lower : 46080 ≤ state.val)
    (upper : state.val < 46144) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 46080, by omega⟩
  have state_eq :
      (⟨46080 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0720 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0721 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨46144 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨46144 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨46144 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0721
    (state : Fin 48684)
    (lower : 46144 ≤ state.val)
    (upper : state.val < 46208) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 46144, by omega⟩
  have state_eq :
      (⟨46144 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0721 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0722 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨46208 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨46208 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨46208 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0722
    (state : Fin 48684)
    (lower : 46208 ≤ state.val)
    (upper : state.val < 46272) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 46208, by omega⟩
  have state_eq :
      (⟨46208 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0722 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0723 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨46272 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨46272 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨46272 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0723
    (state : Fin 48684)
    (lower : 46272 ≤ state.val)
    (upper : state.val < 46336) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 46272, by omega⟩
  have state_eq :
      (⟨46272 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0723 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0724 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨46336 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨46336 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨46336 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0724
    (state : Fin 48684)
    (lower : 46336 ≤ state.val)
    (upper : state.val < 46400) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 46336, by omega⟩
  have state_eq :
      (⟨46336 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0724 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0725 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨46400 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨46400 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨46400 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0725
    (state : Fin 48684)
    (lower : 46400 ≤ state.val)
    (upper : state.val < 46464) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 46400, by omega⟩
  have state_eq :
      (⟨46400 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0725 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0726 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨46464 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨46464 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨46464 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0726
    (state : Fin 48684)
    (lower : 46464 ≤ state.val)
    (upper : state.val < 46528) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 46464, by omega⟩
  have state_eq :
      (⟨46464 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0726 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0727 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨46528 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨46528 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨46528 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0727
    (state : Fin 48684)
    (lower : 46528 ≤ state.val)
    (upper : state.val < 46592) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 46528, by omega⟩
  have state_eq :
      (⟨46528 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0727 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0728 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨46592 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨46592 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨46592 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0728
    (state : Fin 48684)
    (lower : 46592 ≤ state.val)
    (upper : state.val < 46656) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 46592, by omega⟩
  have state_eq :
      (⟨46592 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0728 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0729 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨46656 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨46656 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨46656 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0729
    (state : Fin 48684)
    (lower : 46656 ≤ state.val)
    (upper : state.val < 46720) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 46656, by omega⟩
  have state_eq :
      (⟨46656 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0729 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0730 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨46720 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨46720 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨46720 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0730
    (state : Fin 48684)
    (lower : 46720 ≤ state.val)
    (upper : state.val < 46784) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 46720, by omega⟩
  have state_eq :
      (⟨46720 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0730 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0731 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨46784 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨46784 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨46784 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0731
    (state : Fin 48684)
    (lower : 46784 ≤ state.val)
    (upper : state.val < 46848) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 46784, by omega⟩
  have state_eq :
      (⟨46784 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0731 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0732 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨46848 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨46848 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨46848 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0732
    (state : Fin 48684)
    (lower : 46848 ≤ state.val)
    (upper : state.val < 46912) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 46848, by omega⟩
  have state_eq :
      (⟨46848 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0732 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0733 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨46912 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨46912 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨46912 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0733
    (state : Fin 48684)
    (lower : 46912 ≤ state.val)
    (upper : state.val < 46976) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 46912, by omega⟩
  have state_eq :
      (⟨46912 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0733 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0734 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨46976 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨46976 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨46976 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0734
    (state : Fin 48684)
    (lower : 46976 ≤ state.val)
    (upper : state.val < 47040) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 46976, by omega⟩
  have state_eq :
      (⟨46976 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0734 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0735 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨47040 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨47040 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨47040 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0735
    (state : Fin 48684)
    (lower : 47040 ≤ state.val)
    (upper : state.val < 47104) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 47040, by omega⟩
  have state_eq :
      (⟨47040 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0735 offset

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards
