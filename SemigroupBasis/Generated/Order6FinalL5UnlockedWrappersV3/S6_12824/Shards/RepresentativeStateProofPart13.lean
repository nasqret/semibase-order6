import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Support.Core
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0416 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨26624 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨26624 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨26624 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0416
    (state : Fin 48684)
    (lower : 26624 ≤ state.val)
    (upper : state.val < 26688) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 26624, by omega⟩
  have state_eq :
      (⟨26624 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0416 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0417 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨26688 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨26688 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨26688 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0417
    (state : Fin 48684)
    (lower : 26688 ≤ state.val)
    (upper : state.val < 26752) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 26688, by omega⟩
  have state_eq :
      (⟨26688 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0417 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0418 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨26752 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨26752 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨26752 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0418
    (state : Fin 48684)
    (lower : 26752 ≤ state.val)
    (upper : state.val < 26816) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 26752, by omega⟩
  have state_eq :
      (⟨26752 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0418 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0419 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨26816 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨26816 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨26816 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0419
    (state : Fin 48684)
    (lower : 26816 ≤ state.val)
    (upper : state.val < 26880) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 26816, by omega⟩
  have state_eq :
      (⟨26816 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0419 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0420 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨26880 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨26880 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨26880 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0420
    (state : Fin 48684)
    (lower : 26880 ≤ state.val)
    (upper : state.val < 26944) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 26880, by omega⟩
  have state_eq :
      (⟨26880 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0420 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0421 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨26944 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨26944 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨26944 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0421
    (state : Fin 48684)
    (lower : 26944 ≤ state.val)
    (upper : state.val < 27008) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 26944, by omega⟩
  have state_eq :
      (⟨26944 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0421 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0422 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨27008 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨27008 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨27008 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0422
    (state : Fin 48684)
    (lower : 27008 ≤ state.val)
    (upper : state.val < 27072) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 27008, by omega⟩
  have state_eq :
      (⟨27008 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0422 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0423 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨27072 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨27072 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨27072 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0423
    (state : Fin 48684)
    (lower : 27072 ≤ state.val)
    (upper : state.val < 27136) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 27072, by omega⟩
  have state_eq :
      (⟨27072 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0423 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0424 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨27136 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨27136 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨27136 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0424
    (state : Fin 48684)
    (lower : 27136 ≤ state.val)
    (upper : state.val < 27200) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 27136, by omega⟩
  have state_eq :
      (⟨27136 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0424 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0425 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨27200 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨27200 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨27200 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0425
    (state : Fin 48684)
    (lower : 27200 ≤ state.val)
    (upper : state.val < 27264) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 27200, by omega⟩
  have state_eq :
      (⟨27200 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0425 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0426 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨27264 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨27264 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨27264 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0426
    (state : Fin 48684)
    (lower : 27264 ≤ state.val)
    (upper : state.val < 27328) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 27264, by omega⟩
  have state_eq :
      (⟨27264 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0426 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0427 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨27328 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨27328 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨27328 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0427
    (state : Fin 48684)
    (lower : 27328 ≤ state.val)
    (upper : state.val < 27392) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 27328, by omega⟩
  have state_eq :
      (⟨27328 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0427 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0428 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨27392 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨27392 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨27392 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0428
    (state : Fin 48684)
    (lower : 27392 ≤ state.val)
    (upper : state.val < 27456) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 27392, by omega⟩
  have state_eq :
      (⟨27392 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0428 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0429 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨27456 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨27456 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨27456 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0429
    (state : Fin 48684)
    (lower : 27456 ≤ state.val)
    (upper : state.val < 27520) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 27456, by omega⟩
  have state_eq :
      (⟨27456 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0429 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0430 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨27520 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨27520 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨27520 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0430
    (state : Fin 48684)
    (lower : 27520 ≤ state.val)
    (upper : state.val < 27584) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 27520, by omega⟩
  have state_eq :
      (⟨27520 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0430 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0431 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨27584 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨27584 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨27584 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0431
    (state : Fin 48684)
    (lower : 27584 ≤ state.val)
    (upper : state.val < 27648) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 27584, by omega⟩
  have state_eq :
      (⟨27584 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0431 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0432 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨27648 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨27648 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨27648 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0432
    (state : Fin 48684)
    (lower : 27648 ≤ state.val)
    (upper : state.val < 27712) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 27648, by omega⟩
  have state_eq :
      (⟨27648 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0432 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0433 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨27712 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨27712 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨27712 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0433
    (state : Fin 48684)
    (lower : 27712 ≤ state.val)
    (upper : state.val < 27776) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 27712, by omega⟩
  have state_eq :
      (⟨27712 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0433 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0434 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨27776 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨27776 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨27776 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0434
    (state : Fin 48684)
    (lower : 27776 ≤ state.val)
    (upper : state.val < 27840) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 27776, by omega⟩
  have state_eq :
      (⟨27776 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0434 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0435 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨27840 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨27840 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨27840 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0435
    (state : Fin 48684)
    (lower : 27840 ≤ state.val)
    (upper : state.val < 27904) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 27840, by omega⟩
  have state_eq :
      (⟨27840 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0435 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0436 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨27904 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨27904 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨27904 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0436
    (state : Fin 48684)
    (lower : 27904 ≤ state.val)
    (upper : state.val < 27968) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 27904, by omega⟩
  have state_eq :
      (⟨27904 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0436 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0437 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨27968 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨27968 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨27968 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0437
    (state : Fin 48684)
    (lower : 27968 ≤ state.val)
    (upper : state.val < 28032) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 27968, by omega⟩
  have state_eq :
      (⟨27968 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0437 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0438 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨28032 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨28032 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨28032 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0438
    (state : Fin 48684)
    (lower : 28032 ≤ state.val)
    (upper : state.val < 28096) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 28032, by omega⟩
  have state_eq :
      (⟨28032 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0438 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0439 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨28096 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨28096 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨28096 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0439
    (state : Fin 48684)
    (lower : 28096 ≤ state.val)
    (upper : state.val < 28160) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 28096, by omega⟩
  have state_eq :
      (⟨28096 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0439 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0440 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨28160 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨28160 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨28160 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0440
    (state : Fin 48684)
    (lower : 28160 ≤ state.val)
    (upper : state.val < 28224) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 28160, by omega⟩
  have state_eq :
      (⟨28160 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0440 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0441 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨28224 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨28224 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨28224 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0441
    (state : Fin 48684)
    (lower : 28224 ≤ state.val)
    (upper : state.val < 28288) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 28224, by omega⟩
  have state_eq :
      (⟨28224 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0441 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0442 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨28288 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨28288 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨28288 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0442
    (state : Fin 48684)
    (lower : 28288 ≤ state.val)
    (upper : state.val < 28352) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 28288, by omega⟩
  have state_eq :
      (⟨28288 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0442 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0443 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨28352 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨28352 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨28352 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0443
    (state : Fin 48684)
    (lower : 28352 ≤ state.val)
    (upper : state.val < 28416) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 28352, by omega⟩
  have state_eq :
      (⟨28352 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0443 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0444 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨28416 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨28416 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨28416 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0444
    (state : Fin 48684)
    (lower : 28416 ≤ state.val)
    (upper : state.val < 28480) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 28416, by omega⟩
  have state_eq :
      (⟨28416 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0444 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0445 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨28480 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨28480 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨28480 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0445
    (state : Fin 48684)
    (lower : 28480 ≤ state.val)
    (upper : state.val < 28544) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 28480, by omega⟩
  have state_eq :
      (⟨28480 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0445 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0446 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨28544 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨28544 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨28544 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0446
    (state : Fin 48684)
    (lower : 28544 ≤ state.val)
    (upper : state.val < 28608) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 28544, by omega⟩
  have state_eq :
      (⟨28544 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0446 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0447 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨28608 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨28608 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨28608 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0447
    (state : Fin 48684)
    (lower : 28608 ≤ state.val)
    (upper : state.val < 28672) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 28608, by omega⟩
  have state_eq :
      (⟨28608 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0447 offset

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards
