import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.Shards.DecodeState
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.Shards.StateVector
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.Shards

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0128 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨8192 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨8192 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0128
    (state : Fin 11742)
    (lower : 8192 ≤ state.val)
    (upper : state.val < 8256) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 8192, by omega⟩
  have state_eq :
      (⟨8192 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0128 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0129 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨8256 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨8256 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0129
    (state : Fin 11742)
    (lower : 8256 ≤ state.val)
    (upper : state.val < 8320) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 8256, by omega⟩
  have state_eq :
      (⟨8256 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0129 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0130 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨8320 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨8320 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0130
    (state : Fin 11742)
    (lower : 8320 ≤ state.val)
    (upper : state.val < 8384) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 8320, by omega⟩
  have state_eq :
      (⟨8320 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0130 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0131 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨8384 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨8384 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0131
    (state : Fin 11742)
    (lower : 8384 ≤ state.val)
    (upper : state.val < 8448) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 8384, by omega⟩
  have state_eq :
      (⟨8384 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0131 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0132 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨8448 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨8448 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0132
    (state : Fin 11742)
    (lower : 8448 ≤ state.val)
    (upper : state.val < 8512) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 8448, by omega⟩
  have state_eq :
      (⟨8448 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0132 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0133 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨8512 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨8512 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0133
    (state : Fin 11742)
    (lower : 8512 ≤ state.val)
    (upper : state.val < 8576) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 8512, by omega⟩
  have state_eq :
      (⟨8512 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0133 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0134 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨8576 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨8576 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0134
    (state : Fin 11742)
    (lower : 8576 ≤ state.val)
    (upper : state.val < 8640) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 8576, by omega⟩
  have state_eq :
      (⟨8576 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0134 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0135 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨8640 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨8640 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0135
    (state : Fin 11742)
    (lower : 8640 ≤ state.val)
    (upper : state.val < 8704) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 8640, by omega⟩
  have state_eq :
      (⟨8640 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0135 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0136 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨8704 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨8704 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0136
    (state : Fin 11742)
    (lower : 8704 ≤ state.val)
    (upper : state.val < 8768) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 8704, by omega⟩
  have state_eq :
      (⟨8704 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0136 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0137 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨8768 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨8768 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0137
    (state : Fin 11742)
    (lower : 8768 ≤ state.val)
    (upper : state.val < 8832) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 8768, by omega⟩
  have state_eq :
      (⟨8768 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0137 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0138 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨8832 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨8832 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0138
    (state : Fin 11742)
    (lower : 8832 ≤ state.val)
    (upper : state.val < 8896) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 8832, by omega⟩
  have state_eq :
      (⟨8832 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0138 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0139 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨8896 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨8896 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0139
    (state : Fin 11742)
    (lower : 8896 ≤ state.val)
    (upper : state.val < 8960) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 8896, by omega⟩
  have state_eq :
      (⟨8896 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0139 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0140 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨8960 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨8960 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0140
    (state : Fin 11742)
    (lower : 8960 ≤ state.val)
    (upper : state.val < 9024) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 8960, by omega⟩
  have state_eq :
      (⟨8960 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0140 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0141 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨9024 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨9024 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0141
    (state : Fin 11742)
    (lower : 9024 ≤ state.val)
    (upper : state.val < 9088) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 9024, by omega⟩
  have state_eq :
      (⟨9024 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0141 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0142 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨9088 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨9088 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0142
    (state : Fin 11742)
    (lower : 9088 ≤ state.val)
    (upper : state.val < 9152) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 9088, by omega⟩
  have state_eq :
      (⟨9088 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0142 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0143 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨9152 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨9152 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0143
    (state : Fin 11742)
    (lower : 9152 ≤ state.val)
    (upper : state.val < 9216) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 9152, by omega⟩
  have state_eq :
      (⟨9152 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0143 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0144 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨9216 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨9216 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0144
    (state : Fin 11742)
    (lower : 9216 ≤ state.val)
    (upper : state.val < 9280) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 9216, by omega⟩
  have state_eq :
      (⟨9216 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0144 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0145 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨9280 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨9280 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0145
    (state : Fin 11742)
    (lower : 9280 ≤ state.val)
    (upper : state.val < 9344) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 9280, by omega⟩
  have state_eq :
      (⟨9280 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0145 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0146 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨9344 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨9344 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0146
    (state : Fin 11742)
    (lower : 9344 ≤ state.val)
    (upper : state.val < 9408) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 9344, by omega⟩
  have state_eq :
      (⟨9344 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0146 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0147 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨9408 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨9408 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0147
    (state : Fin 11742)
    (lower : 9408 ≤ state.val)
    (upper : state.val < 9472) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 9408, by omega⟩
  have state_eq :
      (⟨9408 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0147 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0148 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨9472 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨9472 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0148
    (state : Fin 11742)
    (lower : 9472 ≤ state.val)
    (upper : state.val < 9536) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 9472, by omega⟩
  have state_eq :
      (⟨9472 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0148 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0149 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨9536 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨9536 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0149
    (state : Fin 11742)
    (lower : 9536 ≤ state.val)
    (upper : state.val < 9600) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 9536, by omega⟩
  have state_eq :
      (⟨9536 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0149 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0150 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨9600 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨9600 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0150
    (state : Fin 11742)
    (lower : 9600 ≤ state.val)
    (upper : state.val < 9664) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 9600, by omega⟩
  have state_eq :
      (⟨9600 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0150 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0151 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨9664 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨9664 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0151
    (state : Fin 11742)
    (lower : 9664 ≤ state.val)
    (upper : state.val < 9728) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 9664, by omega⟩
  have state_eq :
      (⟨9664 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0151 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0152 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨9728 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨9728 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0152
    (state : Fin 11742)
    (lower : 9728 ≤ state.val)
    (upper : state.val < 9792) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 9728, by omega⟩
  have state_eq :
      (⟨9728 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0152 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0153 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨9792 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨9792 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0153
    (state : Fin 11742)
    (lower : 9792 ≤ state.val)
    (upper : state.val < 9856) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 9792, by omega⟩
  have state_eq :
      (⟨9792 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0153 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0154 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨9856 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨9856 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0154
    (state : Fin 11742)
    (lower : 9856 ≤ state.val)
    (upper : state.val < 9920) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 9856, by omega⟩
  have state_eq :
      (⟨9856 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0154 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0155 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨9920 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨9920 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0155
    (state : Fin 11742)
    (lower : 9920 ≤ state.val)
    (upper : state.val < 9984) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 9920, by omega⟩
  have state_eq :
      (⟨9920 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0155 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0156 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨9984 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨9984 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0156
    (state : Fin 11742)
    (lower : 9984 ≤ state.val)
    (upper : state.val < 10048) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 9984, by omega⟩
  have state_eq :
      (⟨9984 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0156 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0157 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨10048 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨10048 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0157
    (state : Fin 11742)
    (lower : 10048 ≤ state.val)
    (upper : state.val < 10112) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 10048, by omega⟩
  have state_eq :
      (⟨10048 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0157 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0158 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨10112 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨10112 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0158
    (state : Fin 11742)
    (lower : 10112 ≤ state.val)
    (upper : state.val < 10176) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 10112, by omega⟩
  have state_eq :
      (⟨10112 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0158 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0159 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨10176 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨10176 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0159
    (state : Fin 11742)
    (lower : 10176 ≤ state.val)
    (upper : state.val < 10240) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 10176, by omega⟩
  have state_eq :
      (⟨10176 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0159 offset

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.Shards
