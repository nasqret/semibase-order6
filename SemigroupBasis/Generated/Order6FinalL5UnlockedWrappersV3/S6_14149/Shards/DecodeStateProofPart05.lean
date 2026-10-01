import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.Shards.DecodeState
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.Shards.StateVector
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.Shards

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0160 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨10240 + candidate.val, by omega⟩ : Fin 11184)) =
        (⟨10240 + candidate.val, by omega⟩ : Fin 11184) := by
  decide

theorem decodeState_stateVectorProof0160
    (state : Fin 11184)
    (lower : 10240 ≤ state.val)
    (upper : state.val < 10304) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 10240, by omega⟩
  have state_eq :
      (⟨10240 + offset.val, by omega⟩ : Fin 11184) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0160 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0161 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨10304 + candidate.val, by omega⟩ : Fin 11184)) =
        (⟨10304 + candidate.val, by omega⟩ : Fin 11184) := by
  decide

theorem decodeState_stateVectorProof0161
    (state : Fin 11184)
    (lower : 10304 ≤ state.val)
    (upper : state.val < 10368) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 10304, by omega⟩
  have state_eq :
      (⟨10304 + offset.val, by omega⟩ : Fin 11184) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0161 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0162 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨10368 + candidate.val, by omega⟩ : Fin 11184)) =
        (⟨10368 + candidate.val, by omega⟩ : Fin 11184) := by
  decide

theorem decodeState_stateVectorProof0162
    (state : Fin 11184)
    (lower : 10368 ≤ state.val)
    (upper : state.val < 10432) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 10368, by omega⟩
  have state_eq :
      (⟨10368 + offset.val, by omega⟩ : Fin 11184) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0162 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0163 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨10432 + candidate.val, by omega⟩ : Fin 11184)) =
        (⟨10432 + candidate.val, by omega⟩ : Fin 11184) := by
  decide

theorem decodeState_stateVectorProof0163
    (state : Fin 11184)
    (lower : 10432 ≤ state.val)
    (upper : state.val < 10496) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 10432, by omega⟩
  have state_eq :
      (⟨10432 + offset.val, by omega⟩ : Fin 11184) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0163 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0164 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨10496 + candidate.val, by omega⟩ : Fin 11184)) =
        (⟨10496 + candidate.val, by omega⟩ : Fin 11184) := by
  decide

theorem decodeState_stateVectorProof0164
    (state : Fin 11184)
    (lower : 10496 ≤ state.val)
    (upper : state.val < 10560) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 10496, by omega⟩
  have state_eq :
      (⟨10496 + offset.val, by omega⟩ : Fin 11184) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0164 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0165 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨10560 + candidate.val, by omega⟩ : Fin 11184)) =
        (⟨10560 + candidate.val, by omega⟩ : Fin 11184) := by
  decide

theorem decodeState_stateVectorProof0165
    (state : Fin 11184)
    (lower : 10560 ≤ state.val)
    (upper : state.val < 10624) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 10560, by omega⟩
  have state_eq :
      (⟨10560 + offset.val, by omega⟩ : Fin 11184) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0165 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0166 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨10624 + candidate.val, by omega⟩ : Fin 11184)) =
        (⟨10624 + candidate.val, by omega⟩ : Fin 11184) := by
  decide

theorem decodeState_stateVectorProof0166
    (state : Fin 11184)
    (lower : 10624 ≤ state.val)
    (upper : state.val < 10688) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 10624, by omega⟩
  have state_eq :
      (⟨10624 + offset.val, by omega⟩ : Fin 11184) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0166 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0167 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨10688 + candidate.val, by omega⟩ : Fin 11184)) =
        (⟨10688 + candidate.val, by omega⟩ : Fin 11184) := by
  decide

theorem decodeState_stateVectorProof0167
    (state : Fin 11184)
    (lower : 10688 ≤ state.val)
    (upper : state.val < 10752) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 10688, by omega⟩
  have state_eq :
      (⟨10688 + offset.val, by omega⟩ : Fin 11184) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0167 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0168 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨10752 + candidate.val, by omega⟩ : Fin 11184)) =
        (⟨10752 + candidate.val, by omega⟩ : Fin 11184) := by
  decide

theorem decodeState_stateVectorProof0168
    (state : Fin 11184)
    (lower : 10752 ≤ state.val)
    (upper : state.val < 10816) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 10752, by omega⟩
  have state_eq :
      (⟨10752 + offset.val, by omega⟩ : Fin 11184) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0168 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0169 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨10816 + candidate.val, by omega⟩ : Fin 11184)) =
        (⟨10816 + candidate.val, by omega⟩ : Fin 11184) := by
  decide

theorem decodeState_stateVectorProof0169
    (state : Fin 11184)
    (lower : 10816 ≤ state.val)
    (upper : state.val < 10880) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 10816, by omega⟩
  have state_eq :
      (⟨10816 + offset.val, by omega⟩ : Fin 11184) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0169 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0170 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨10880 + candidate.val, by omega⟩ : Fin 11184)) =
        (⟨10880 + candidate.val, by omega⟩ : Fin 11184) := by
  decide

theorem decodeState_stateVectorProof0170
    (state : Fin 11184)
    (lower : 10880 ≤ state.val)
    (upper : state.val < 10944) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 10880, by omega⟩
  have state_eq :
      (⟨10880 + offset.val, by omega⟩ : Fin 11184) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0170 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0171 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨10944 + candidate.val, by omega⟩ : Fin 11184)) =
        (⟨10944 + candidate.val, by omega⟩ : Fin 11184) := by
  decide

theorem decodeState_stateVectorProof0171
    (state : Fin 11184)
    (lower : 10944 ≤ state.val)
    (upper : state.val < 11008) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 10944, by omega⟩
  have state_eq :
      (⟨10944 + offset.val, by omega⟩ : Fin 11184) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0171 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0172 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨11008 + candidate.val, by omega⟩ : Fin 11184)) =
        (⟨11008 + candidate.val, by omega⟩ : Fin 11184) := by
  decide

theorem decodeState_stateVectorProof0172
    (state : Fin 11184)
    (lower : 11008 ≤ state.val)
    (upper : state.val < 11072) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 11008, by omega⟩
  have state_eq :
      (⟨11008 + offset.val, by omega⟩ : Fin 11184) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0172 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0173 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨11072 + candidate.val, by omega⟩ : Fin 11184)) =
        (⟨11072 + candidate.val, by omega⟩ : Fin 11184) := by
  decide

theorem decodeState_stateVectorProof0173
    (state : Fin 11184)
    (lower : 11072 ≤ state.val)
    (upper : state.val < 11136) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 11072, by omega⟩
  have state_eq :
      (⟨11072 + offset.val, by omega⟩ : Fin 11184) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0173 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0174 :
    ∀ candidate : Fin 48,
      decodeState (stateVector (⟨11136 + candidate.val, by omega⟩ : Fin 11184)) =
        (⟨11136 + candidate.val, by omega⟩ : Fin 11184) := by
  decide

theorem decodeState_stateVectorProof0174
    (state : Fin 11184)
    (lower : 11136 ≤ state.val)
    (upper : state.val < 11184) :
    decodeState (stateVector state) = state := by
  let offset : Fin 48 := ⟨state.val - 11136, by omega⟩
  have state_eq :
      (⟨11136 + offset.val, by omega⟩ : Fin 11184) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0174 offset

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.Shards
