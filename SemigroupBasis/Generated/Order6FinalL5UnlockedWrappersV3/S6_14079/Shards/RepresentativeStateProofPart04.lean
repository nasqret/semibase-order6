import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.Support.Core
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.Shards

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0128 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail (⟨8192 + candidate.val, by omega⟩ : Fin 11742)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead (⟨8192 + candidate.val, by omega⟩ : Fin 11742))) =
        (⟨8192 + candidate.val, by omega⟩ : Fin 11742)
    := by
  decide

theorem representativeStateProof0128
    (state : Fin 11742)
    (lower : 8192 ≤ state.val)
    (upper : state.val < 8256) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 8192, by omega⟩
  have state_eq :
      (⟨8192 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0128 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0129 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail (⟨8256 + candidate.val, by omega⟩ : Fin 11742)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead (⟨8256 + candidate.val, by omega⟩ : Fin 11742))) =
        (⟨8256 + candidate.val, by omega⟩ : Fin 11742)
    := by
  decide

theorem representativeStateProof0129
    (state : Fin 11742)
    (lower : 8256 ≤ state.val)
    (upper : state.val < 8320) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 8256, by omega⟩
  have state_eq :
      (⟨8256 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0129 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0130 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail (⟨8320 + candidate.val, by omega⟩ : Fin 11742)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead (⟨8320 + candidate.val, by omega⟩ : Fin 11742))) =
        (⟨8320 + candidate.val, by omega⟩ : Fin 11742)
    := by
  decide

theorem representativeStateProof0130
    (state : Fin 11742)
    (lower : 8320 ≤ state.val)
    (upper : state.val < 8384) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 8320, by omega⟩
  have state_eq :
      (⟨8320 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0130 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0131 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail (⟨8384 + candidate.val, by omega⟩ : Fin 11742)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead (⟨8384 + candidate.val, by omega⟩ : Fin 11742))) =
        (⟨8384 + candidate.val, by omega⟩ : Fin 11742)
    := by
  decide

theorem representativeStateProof0131
    (state : Fin 11742)
    (lower : 8384 ≤ state.val)
    (upper : state.val < 8448) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 8384, by omega⟩
  have state_eq :
      (⟨8384 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0131 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0132 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail (⟨8448 + candidate.val, by omega⟩ : Fin 11742)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead (⟨8448 + candidate.val, by omega⟩ : Fin 11742))) =
        (⟨8448 + candidate.val, by omega⟩ : Fin 11742)
    := by
  decide

theorem representativeStateProof0132
    (state : Fin 11742)
    (lower : 8448 ≤ state.val)
    (upper : state.val < 8512) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 8448, by omega⟩
  have state_eq :
      (⟨8448 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0132 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0133 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail (⟨8512 + candidate.val, by omega⟩ : Fin 11742)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead (⟨8512 + candidate.val, by omega⟩ : Fin 11742))) =
        (⟨8512 + candidate.val, by omega⟩ : Fin 11742)
    := by
  decide

theorem representativeStateProof0133
    (state : Fin 11742)
    (lower : 8512 ≤ state.val)
    (upper : state.val < 8576) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 8512, by omega⟩
  have state_eq :
      (⟨8512 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0133 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0134 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail (⟨8576 + candidate.val, by omega⟩ : Fin 11742)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead (⟨8576 + candidate.val, by omega⟩ : Fin 11742))) =
        (⟨8576 + candidate.val, by omega⟩ : Fin 11742)
    := by
  decide

theorem representativeStateProof0134
    (state : Fin 11742)
    (lower : 8576 ≤ state.val)
    (upper : state.val < 8640) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 8576, by omega⟩
  have state_eq :
      (⟨8576 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0134 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0135 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail (⟨8640 + candidate.val, by omega⟩ : Fin 11742)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead (⟨8640 + candidate.val, by omega⟩ : Fin 11742))) =
        (⟨8640 + candidate.val, by omega⟩ : Fin 11742)
    := by
  decide

theorem representativeStateProof0135
    (state : Fin 11742)
    (lower : 8640 ≤ state.val)
    (upper : state.val < 8704) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 8640, by omega⟩
  have state_eq :
      (⟨8640 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0135 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0136 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail (⟨8704 + candidate.val, by omega⟩ : Fin 11742)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead (⟨8704 + candidate.val, by omega⟩ : Fin 11742))) =
        (⟨8704 + candidate.val, by omega⟩ : Fin 11742)
    := by
  decide

theorem representativeStateProof0136
    (state : Fin 11742)
    (lower : 8704 ≤ state.val)
    (upper : state.val < 8768) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 8704, by omega⟩
  have state_eq :
      (⟨8704 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0136 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0137 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail (⟨8768 + candidate.val, by omega⟩ : Fin 11742)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead (⟨8768 + candidate.val, by omega⟩ : Fin 11742))) =
        (⟨8768 + candidate.val, by omega⟩ : Fin 11742)
    := by
  decide

theorem representativeStateProof0137
    (state : Fin 11742)
    (lower : 8768 ≤ state.val)
    (upper : state.val < 8832) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 8768, by omega⟩
  have state_eq :
      (⟨8768 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0137 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0138 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail (⟨8832 + candidate.val, by omega⟩ : Fin 11742)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead (⟨8832 + candidate.val, by omega⟩ : Fin 11742))) =
        (⟨8832 + candidate.val, by omega⟩ : Fin 11742)
    := by
  decide

theorem representativeStateProof0138
    (state : Fin 11742)
    (lower : 8832 ≤ state.val)
    (upper : state.val < 8896) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 8832, by omega⟩
  have state_eq :
      (⟨8832 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0138 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0139 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail (⟨8896 + candidate.val, by omega⟩ : Fin 11742)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead (⟨8896 + candidate.val, by omega⟩ : Fin 11742))) =
        (⟨8896 + candidate.val, by omega⟩ : Fin 11742)
    := by
  decide

theorem representativeStateProof0139
    (state : Fin 11742)
    (lower : 8896 ≤ state.val)
    (upper : state.val < 8960) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 8896, by omega⟩
  have state_eq :
      (⟨8896 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0139 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0140 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail (⟨8960 + candidate.val, by omega⟩ : Fin 11742)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead (⟨8960 + candidate.val, by omega⟩ : Fin 11742))) =
        (⟨8960 + candidate.val, by omega⟩ : Fin 11742)
    := by
  decide

theorem representativeStateProof0140
    (state : Fin 11742)
    (lower : 8960 ≤ state.val)
    (upper : state.val < 9024) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 8960, by omega⟩
  have state_eq :
      (⟨8960 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0140 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0141 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail (⟨9024 + candidate.val, by omega⟩ : Fin 11742)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead (⟨9024 + candidate.val, by omega⟩ : Fin 11742))) =
        (⟨9024 + candidate.val, by omega⟩ : Fin 11742)
    := by
  decide

theorem representativeStateProof0141
    (state : Fin 11742)
    (lower : 9024 ≤ state.val)
    (upper : state.val < 9088) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 9024, by omega⟩
  have state_eq :
      (⟨9024 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0141 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0142 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail (⟨9088 + candidate.val, by omega⟩ : Fin 11742)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead (⟨9088 + candidate.val, by omega⟩ : Fin 11742))) =
        (⟨9088 + candidate.val, by omega⟩ : Fin 11742)
    := by
  decide

theorem representativeStateProof0142
    (state : Fin 11742)
    (lower : 9088 ≤ state.val)
    (upper : state.val < 9152) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 9088, by omega⟩
  have state_eq :
      (⟨9088 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0142 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0143 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail (⟨9152 + candidate.val, by omega⟩ : Fin 11742)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead (⟨9152 + candidate.val, by omega⟩ : Fin 11742))) =
        (⟨9152 + candidate.val, by omega⟩ : Fin 11742)
    := by
  decide

theorem representativeStateProof0143
    (state : Fin 11742)
    (lower : 9152 ≤ state.val)
    (upper : state.val < 9216) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 9152, by omega⟩
  have state_eq :
      (⟨9152 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0143 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0144 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail (⟨9216 + candidate.val, by omega⟩ : Fin 11742)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead (⟨9216 + candidate.val, by omega⟩ : Fin 11742))) =
        (⟨9216 + candidate.val, by omega⟩ : Fin 11742)
    := by
  decide

theorem representativeStateProof0144
    (state : Fin 11742)
    (lower : 9216 ≤ state.val)
    (upper : state.val < 9280) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 9216, by omega⟩
  have state_eq :
      (⟨9216 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0144 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0145 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail (⟨9280 + candidate.val, by omega⟩ : Fin 11742)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead (⟨9280 + candidate.val, by omega⟩ : Fin 11742))) =
        (⟨9280 + candidate.val, by omega⟩ : Fin 11742)
    := by
  decide

theorem representativeStateProof0145
    (state : Fin 11742)
    (lower : 9280 ≤ state.val)
    (upper : state.val < 9344) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 9280, by omega⟩
  have state_eq :
      (⟨9280 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0145 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0146 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail (⟨9344 + candidate.val, by omega⟩ : Fin 11742)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead (⟨9344 + candidate.val, by omega⟩ : Fin 11742))) =
        (⟨9344 + candidate.val, by omega⟩ : Fin 11742)
    := by
  decide

theorem representativeStateProof0146
    (state : Fin 11742)
    (lower : 9344 ≤ state.val)
    (upper : state.val < 9408) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 9344, by omega⟩
  have state_eq :
      (⟨9344 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0146 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0147 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail (⟨9408 + candidate.val, by omega⟩ : Fin 11742)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead (⟨9408 + candidate.val, by omega⟩ : Fin 11742))) =
        (⟨9408 + candidate.val, by omega⟩ : Fin 11742)
    := by
  decide

theorem representativeStateProof0147
    (state : Fin 11742)
    (lower : 9408 ≤ state.val)
    (upper : state.val < 9472) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 9408, by omega⟩
  have state_eq :
      (⟨9408 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0147 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0148 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail (⟨9472 + candidate.val, by omega⟩ : Fin 11742)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead (⟨9472 + candidate.val, by omega⟩ : Fin 11742))) =
        (⟨9472 + candidate.val, by omega⟩ : Fin 11742)
    := by
  decide

theorem representativeStateProof0148
    (state : Fin 11742)
    (lower : 9472 ≤ state.val)
    (upper : state.val < 9536) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 9472, by omega⟩
  have state_eq :
      (⟨9472 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0148 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0149 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail (⟨9536 + candidate.val, by omega⟩ : Fin 11742)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead (⟨9536 + candidate.val, by omega⟩ : Fin 11742))) =
        (⟨9536 + candidate.val, by omega⟩ : Fin 11742)
    := by
  decide

theorem representativeStateProof0149
    (state : Fin 11742)
    (lower : 9536 ≤ state.val)
    (upper : state.val < 9600) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 9536, by omega⟩
  have state_eq :
      (⟨9536 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0149 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0150 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail (⟨9600 + candidate.val, by omega⟩ : Fin 11742)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead (⟨9600 + candidate.val, by omega⟩ : Fin 11742))) =
        (⟨9600 + candidate.val, by omega⟩ : Fin 11742)
    := by
  decide

theorem representativeStateProof0150
    (state : Fin 11742)
    (lower : 9600 ≤ state.val)
    (upper : state.val < 9664) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 9600, by omega⟩
  have state_eq :
      (⟨9600 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0150 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0151 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail (⟨9664 + candidate.val, by omega⟩ : Fin 11742)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead (⟨9664 + candidate.val, by omega⟩ : Fin 11742))) =
        (⟨9664 + candidate.val, by omega⟩ : Fin 11742)
    := by
  decide

theorem representativeStateProof0151
    (state : Fin 11742)
    (lower : 9664 ≤ state.val)
    (upper : state.val < 9728) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 9664, by omega⟩
  have state_eq :
      (⟨9664 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0151 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0152 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail (⟨9728 + candidate.val, by omega⟩ : Fin 11742)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead (⟨9728 + candidate.val, by omega⟩ : Fin 11742))) =
        (⟨9728 + candidate.val, by omega⟩ : Fin 11742)
    := by
  decide

theorem representativeStateProof0152
    (state : Fin 11742)
    (lower : 9728 ≤ state.val)
    (upper : state.val < 9792) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 9728, by omega⟩
  have state_eq :
      (⟨9728 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0152 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0153 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail (⟨9792 + candidate.val, by omega⟩ : Fin 11742)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead (⟨9792 + candidate.val, by omega⟩ : Fin 11742))) =
        (⟨9792 + candidate.val, by omega⟩ : Fin 11742)
    := by
  decide

theorem representativeStateProof0153
    (state : Fin 11742)
    (lower : 9792 ≤ state.val)
    (upper : state.val < 9856) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 9792, by omega⟩
  have state_eq :
      (⟨9792 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0153 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0154 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail (⟨9856 + candidate.val, by omega⟩ : Fin 11742)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead (⟨9856 + candidate.val, by omega⟩ : Fin 11742))) =
        (⟨9856 + candidate.val, by omega⟩ : Fin 11742)
    := by
  decide

theorem representativeStateProof0154
    (state : Fin 11742)
    (lower : 9856 ≤ state.val)
    (upper : state.val < 9920) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 9856, by omega⟩
  have state_eq :
      (⟨9856 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0154 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0155 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail (⟨9920 + candidate.val, by omega⟩ : Fin 11742)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead (⟨9920 + candidate.val, by omega⟩ : Fin 11742))) =
        (⟨9920 + candidate.val, by omega⟩ : Fin 11742)
    := by
  decide

theorem representativeStateProof0155
    (state : Fin 11742)
    (lower : 9920 ≤ state.val)
    (upper : state.val < 9984) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 9920, by omega⟩
  have state_eq :
      (⟨9920 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0155 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0156 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail (⟨9984 + candidate.val, by omega⟩ : Fin 11742)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead (⟨9984 + candidate.val, by omega⟩ : Fin 11742))) =
        (⟨9984 + candidate.val, by omega⟩ : Fin 11742)
    := by
  decide

theorem representativeStateProof0156
    (state : Fin 11742)
    (lower : 9984 ≤ state.val)
    (upper : state.val < 10048) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 9984, by omega⟩
  have state_eq :
      (⟨9984 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0156 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0157 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail (⟨10048 + candidate.val, by omega⟩ : Fin 11742)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead (⟨10048 + candidate.val, by omega⟩ : Fin 11742))) =
        (⟨10048 + candidate.val, by omega⟩ : Fin 11742)
    := by
  decide

theorem representativeStateProof0157
    (state : Fin 11742)
    (lower : 10048 ≤ state.val)
    (upper : state.val < 10112) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 10048, by omega⟩
  have state_eq :
      (⟨10048 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0157 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0158 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail (⟨10112 + candidate.val, by omega⟩ : Fin 11742)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead (⟨10112 + candidate.val, by omega⟩ : Fin 11742))) =
        (⟨10112 + candidate.val, by omega⟩ : Fin 11742)
    := by
  decide

theorem representativeStateProof0158
    (state : Fin 11742)
    (lower : 10112 ≤ state.val)
    (upper : state.val < 10176) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 10112, by omega⟩
  have state_eq :
      (⟨10112 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0158 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0159 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail (⟨10176 + candidate.val, by omega⟩ : Fin 11742)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead (⟨10176 + candidate.val, by omega⟩ : Fin 11742))) =
        (⟨10176 + candidate.val, by omega⟩ : Fin 11742)
    := by
  decide

theorem representativeStateProof0159
    (state : Fin 11742)
    (lower : 10176 ≤ state.val)
    (upper : state.val < 10240) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 10176, by omega⟩
  have state_eq :
      (⟨10176 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0159 offset

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.Shards
