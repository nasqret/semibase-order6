import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.Support.Core
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.Shards

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0096 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail (⟨6144 + candidate.val, by omega⟩ : Fin 11742)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead (⟨6144 + candidate.val, by omega⟩ : Fin 11742))) =
        (⟨6144 + candidate.val, by omega⟩ : Fin 11742)
    := by
  decide

theorem representativeStateProof0096
    (state : Fin 11742)
    (lower : 6144 ≤ state.val)
    (upper : state.val < 6208) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 6144, by omega⟩
  have state_eq :
      (⟨6144 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0096 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0097 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail (⟨6208 + candidate.val, by omega⟩ : Fin 11742)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead (⟨6208 + candidate.val, by omega⟩ : Fin 11742))) =
        (⟨6208 + candidate.val, by omega⟩ : Fin 11742)
    := by
  decide

theorem representativeStateProof0097
    (state : Fin 11742)
    (lower : 6208 ≤ state.val)
    (upper : state.val < 6272) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 6208, by omega⟩
  have state_eq :
      (⟨6208 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0097 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0098 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail (⟨6272 + candidate.val, by omega⟩ : Fin 11742)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead (⟨6272 + candidate.val, by omega⟩ : Fin 11742))) =
        (⟨6272 + candidate.val, by omega⟩ : Fin 11742)
    := by
  decide

theorem representativeStateProof0098
    (state : Fin 11742)
    (lower : 6272 ≤ state.val)
    (upper : state.val < 6336) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 6272, by omega⟩
  have state_eq :
      (⟨6272 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0098 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0099 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail (⟨6336 + candidate.val, by omega⟩ : Fin 11742)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead (⟨6336 + candidate.val, by omega⟩ : Fin 11742))) =
        (⟨6336 + candidate.val, by omega⟩ : Fin 11742)
    := by
  decide

theorem representativeStateProof0099
    (state : Fin 11742)
    (lower : 6336 ≤ state.val)
    (upper : state.val < 6400) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 6336, by omega⟩
  have state_eq :
      (⟨6336 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0099 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0100 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail (⟨6400 + candidate.val, by omega⟩ : Fin 11742)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead (⟨6400 + candidate.val, by omega⟩ : Fin 11742))) =
        (⟨6400 + candidate.val, by omega⟩ : Fin 11742)
    := by
  decide

theorem representativeStateProof0100
    (state : Fin 11742)
    (lower : 6400 ≤ state.val)
    (upper : state.val < 6464) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 6400, by omega⟩
  have state_eq :
      (⟨6400 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0100 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0101 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail (⟨6464 + candidate.val, by omega⟩ : Fin 11742)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead (⟨6464 + candidate.val, by omega⟩ : Fin 11742))) =
        (⟨6464 + candidate.val, by omega⟩ : Fin 11742)
    := by
  decide

theorem representativeStateProof0101
    (state : Fin 11742)
    (lower : 6464 ≤ state.val)
    (upper : state.val < 6528) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 6464, by omega⟩
  have state_eq :
      (⟨6464 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0101 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0102 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail (⟨6528 + candidate.val, by omega⟩ : Fin 11742)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead (⟨6528 + candidate.val, by omega⟩ : Fin 11742))) =
        (⟨6528 + candidate.val, by omega⟩ : Fin 11742)
    := by
  decide

theorem representativeStateProof0102
    (state : Fin 11742)
    (lower : 6528 ≤ state.val)
    (upper : state.val < 6592) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 6528, by omega⟩
  have state_eq :
      (⟨6528 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0102 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0103 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail (⟨6592 + candidate.val, by omega⟩ : Fin 11742)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead (⟨6592 + candidate.val, by omega⟩ : Fin 11742))) =
        (⟨6592 + candidate.val, by omega⟩ : Fin 11742)
    := by
  decide

theorem representativeStateProof0103
    (state : Fin 11742)
    (lower : 6592 ≤ state.val)
    (upper : state.val < 6656) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 6592, by omega⟩
  have state_eq :
      (⟨6592 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0103 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0104 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail (⟨6656 + candidate.val, by omega⟩ : Fin 11742)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead (⟨6656 + candidate.val, by omega⟩ : Fin 11742))) =
        (⟨6656 + candidate.val, by omega⟩ : Fin 11742)
    := by
  decide

theorem representativeStateProof0104
    (state : Fin 11742)
    (lower : 6656 ≤ state.val)
    (upper : state.val < 6720) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 6656, by omega⟩
  have state_eq :
      (⟨6656 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0104 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0105 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail (⟨6720 + candidate.val, by omega⟩ : Fin 11742)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead (⟨6720 + candidate.val, by omega⟩ : Fin 11742))) =
        (⟨6720 + candidate.val, by omega⟩ : Fin 11742)
    := by
  decide

theorem representativeStateProof0105
    (state : Fin 11742)
    (lower : 6720 ≤ state.val)
    (upper : state.val < 6784) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 6720, by omega⟩
  have state_eq :
      (⟨6720 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0105 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0106 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail (⟨6784 + candidate.val, by omega⟩ : Fin 11742)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead (⟨6784 + candidate.val, by omega⟩ : Fin 11742))) =
        (⟨6784 + candidate.val, by omega⟩ : Fin 11742)
    := by
  decide

theorem representativeStateProof0106
    (state : Fin 11742)
    (lower : 6784 ≤ state.val)
    (upper : state.val < 6848) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 6784, by omega⟩
  have state_eq :
      (⟨6784 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0106 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0107 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail (⟨6848 + candidate.val, by omega⟩ : Fin 11742)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead (⟨6848 + candidate.val, by omega⟩ : Fin 11742))) =
        (⟨6848 + candidate.val, by omega⟩ : Fin 11742)
    := by
  decide

theorem representativeStateProof0107
    (state : Fin 11742)
    (lower : 6848 ≤ state.val)
    (upper : state.val < 6912) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 6848, by omega⟩
  have state_eq :
      (⟨6848 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0107 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0108 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail (⟨6912 + candidate.val, by omega⟩ : Fin 11742)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead (⟨6912 + candidate.val, by omega⟩ : Fin 11742))) =
        (⟨6912 + candidate.val, by omega⟩ : Fin 11742)
    := by
  decide

theorem representativeStateProof0108
    (state : Fin 11742)
    (lower : 6912 ≤ state.val)
    (upper : state.val < 6976) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 6912, by omega⟩
  have state_eq :
      (⟨6912 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0108 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0109 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail (⟨6976 + candidate.val, by omega⟩ : Fin 11742)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead (⟨6976 + candidate.val, by omega⟩ : Fin 11742))) =
        (⟨6976 + candidate.val, by omega⟩ : Fin 11742)
    := by
  decide

theorem representativeStateProof0109
    (state : Fin 11742)
    (lower : 6976 ≤ state.val)
    (upper : state.val < 7040) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 6976, by omega⟩
  have state_eq :
      (⟨6976 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0109 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0110 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail (⟨7040 + candidate.val, by omega⟩ : Fin 11742)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead (⟨7040 + candidate.val, by omega⟩ : Fin 11742))) =
        (⟨7040 + candidate.val, by omega⟩ : Fin 11742)
    := by
  decide

theorem representativeStateProof0110
    (state : Fin 11742)
    (lower : 7040 ≤ state.val)
    (upper : state.val < 7104) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 7040, by omega⟩
  have state_eq :
      (⟨7040 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0110 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0111 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail (⟨7104 + candidate.val, by omega⟩ : Fin 11742)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead (⟨7104 + candidate.val, by omega⟩ : Fin 11742))) =
        (⟨7104 + candidate.val, by omega⟩ : Fin 11742)
    := by
  decide

theorem representativeStateProof0111
    (state : Fin 11742)
    (lower : 7104 ≤ state.val)
    (upper : state.val < 7168) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 7104, by omega⟩
  have state_eq :
      (⟨7104 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0111 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0112 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail (⟨7168 + candidate.val, by omega⟩ : Fin 11742)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead (⟨7168 + candidate.val, by omega⟩ : Fin 11742))) =
        (⟨7168 + candidate.val, by omega⟩ : Fin 11742)
    := by
  decide

theorem representativeStateProof0112
    (state : Fin 11742)
    (lower : 7168 ≤ state.val)
    (upper : state.val < 7232) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 7168, by omega⟩
  have state_eq :
      (⟨7168 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0112 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0113 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail (⟨7232 + candidate.val, by omega⟩ : Fin 11742)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead (⟨7232 + candidate.val, by omega⟩ : Fin 11742))) =
        (⟨7232 + candidate.val, by omega⟩ : Fin 11742)
    := by
  decide

theorem representativeStateProof0113
    (state : Fin 11742)
    (lower : 7232 ≤ state.val)
    (upper : state.val < 7296) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 7232, by omega⟩
  have state_eq :
      (⟨7232 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0113 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0114 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail (⟨7296 + candidate.val, by omega⟩ : Fin 11742)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead (⟨7296 + candidate.val, by omega⟩ : Fin 11742))) =
        (⟨7296 + candidate.val, by omega⟩ : Fin 11742)
    := by
  decide

theorem representativeStateProof0114
    (state : Fin 11742)
    (lower : 7296 ≤ state.val)
    (upper : state.val < 7360) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 7296, by omega⟩
  have state_eq :
      (⟨7296 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0114 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0115 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail (⟨7360 + candidate.val, by omega⟩ : Fin 11742)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead (⟨7360 + candidate.val, by omega⟩ : Fin 11742))) =
        (⟨7360 + candidate.val, by omega⟩ : Fin 11742)
    := by
  decide

theorem representativeStateProof0115
    (state : Fin 11742)
    (lower : 7360 ≤ state.val)
    (upper : state.val < 7424) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 7360, by omega⟩
  have state_eq :
      (⟨7360 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0115 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0116 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail (⟨7424 + candidate.val, by omega⟩ : Fin 11742)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead (⟨7424 + candidate.val, by omega⟩ : Fin 11742))) =
        (⟨7424 + candidate.val, by omega⟩ : Fin 11742)
    := by
  decide

theorem representativeStateProof0116
    (state : Fin 11742)
    (lower : 7424 ≤ state.val)
    (upper : state.val < 7488) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 7424, by omega⟩
  have state_eq :
      (⟨7424 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0116 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0117 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail (⟨7488 + candidate.val, by omega⟩ : Fin 11742)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead (⟨7488 + candidate.val, by omega⟩ : Fin 11742))) =
        (⟨7488 + candidate.val, by omega⟩ : Fin 11742)
    := by
  decide

theorem representativeStateProof0117
    (state : Fin 11742)
    (lower : 7488 ≤ state.val)
    (upper : state.val < 7552) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 7488, by omega⟩
  have state_eq :
      (⟨7488 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0117 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0118 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail (⟨7552 + candidate.val, by omega⟩ : Fin 11742)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead (⟨7552 + candidate.val, by omega⟩ : Fin 11742))) =
        (⟨7552 + candidate.val, by omega⟩ : Fin 11742)
    := by
  decide

theorem representativeStateProof0118
    (state : Fin 11742)
    (lower : 7552 ≤ state.val)
    (upper : state.val < 7616) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 7552, by omega⟩
  have state_eq :
      (⟨7552 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0118 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0119 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail (⟨7616 + candidate.val, by omega⟩ : Fin 11742)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead (⟨7616 + candidate.val, by omega⟩ : Fin 11742))) =
        (⟨7616 + candidate.val, by omega⟩ : Fin 11742)
    := by
  decide

theorem representativeStateProof0119
    (state : Fin 11742)
    (lower : 7616 ≤ state.val)
    (upper : state.val < 7680) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 7616, by omega⟩
  have state_eq :
      (⟨7616 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0119 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0120 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail (⟨7680 + candidate.val, by omega⟩ : Fin 11742)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead (⟨7680 + candidate.val, by omega⟩ : Fin 11742))) =
        (⟨7680 + candidate.val, by omega⟩ : Fin 11742)
    := by
  decide

theorem representativeStateProof0120
    (state : Fin 11742)
    (lower : 7680 ≤ state.val)
    (upper : state.val < 7744) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 7680, by omega⟩
  have state_eq :
      (⟨7680 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0120 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0121 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail (⟨7744 + candidate.val, by omega⟩ : Fin 11742)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead (⟨7744 + candidate.val, by omega⟩ : Fin 11742))) =
        (⟨7744 + candidate.val, by omega⟩ : Fin 11742)
    := by
  decide

theorem representativeStateProof0121
    (state : Fin 11742)
    (lower : 7744 ≤ state.val)
    (upper : state.val < 7808) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 7744, by omega⟩
  have state_eq :
      (⟨7744 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0121 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0122 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail (⟨7808 + candidate.val, by omega⟩ : Fin 11742)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead (⟨7808 + candidate.val, by omega⟩ : Fin 11742))) =
        (⟨7808 + candidate.val, by omega⟩ : Fin 11742)
    := by
  decide

theorem representativeStateProof0122
    (state : Fin 11742)
    (lower : 7808 ≤ state.val)
    (upper : state.val < 7872) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 7808, by omega⟩
  have state_eq :
      (⟨7808 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0122 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0123 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail (⟨7872 + candidate.val, by omega⟩ : Fin 11742)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead (⟨7872 + candidate.val, by omega⟩ : Fin 11742))) =
        (⟨7872 + candidate.val, by omega⟩ : Fin 11742)
    := by
  decide

theorem representativeStateProof0123
    (state : Fin 11742)
    (lower : 7872 ≤ state.val)
    (upper : state.val < 7936) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 7872, by omega⟩
  have state_eq :
      (⟨7872 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0123 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0124 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail (⟨7936 + candidate.val, by omega⟩ : Fin 11742)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead (⟨7936 + candidate.val, by omega⟩ : Fin 11742))) =
        (⟨7936 + candidate.val, by omega⟩ : Fin 11742)
    := by
  decide

theorem representativeStateProof0124
    (state : Fin 11742)
    (lower : 7936 ≤ state.val)
    (upper : state.val < 8000) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 7936, by omega⟩
  have state_eq :
      (⟨7936 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0124 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0125 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail (⟨8000 + candidate.val, by omega⟩ : Fin 11742)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead (⟨8000 + candidate.val, by omega⟩ : Fin 11742))) =
        (⟨8000 + candidate.val, by omega⟩ : Fin 11742)
    := by
  decide

theorem representativeStateProof0125
    (state : Fin 11742)
    (lower : 8000 ≤ state.val)
    (upper : state.val < 8064) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 8000, by omega⟩
  have state_eq :
      (⟨8000 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0125 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0126 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail (⟨8064 + candidate.val, by omega⟩ : Fin 11742)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead (⟨8064 + candidate.val, by omega⟩ : Fin 11742))) =
        (⟨8064 + candidate.val, by omega⟩ : Fin 11742)
    := by
  decide

theorem representativeStateProof0126
    (state : Fin 11742)
    (lower : 8064 ≤ state.val)
    (upper : state.val < 8128) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 8064, by omega⟩
  have state_eq :
      (⟨8064 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0126 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0127 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail (⟨8128 + candidate.val, by omega⟩ : Fin 11742)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead (⟨8128 + candidate.val, by omega⟩ : Fin 11742))) =
        (⟨8128 + candidate.val, by omega⟩ : Fin 11742)
    := by
  decide

theorem representativeStateProof0127
    (state : Fin 11742)
    (lower : 8128 ≤ state.val)
    (upper : state.val < 8192) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 8128, by omega⟩
  have state_eq :
      (⟨8128 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0127 offset

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.Shards
