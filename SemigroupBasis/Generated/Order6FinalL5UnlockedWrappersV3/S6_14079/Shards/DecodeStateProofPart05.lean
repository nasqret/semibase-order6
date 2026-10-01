import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.Shards.DecodeState
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.Shards.StateVector
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.Shards

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0160 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨10240 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨10240 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0160
    (state : Fin 11742)
    (lower : 10240 ≤ state.val)
    (upper : state.val < 10304) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 10240, by omega⟩
  have state_eq :
      (⟨10240 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0160 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0161 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨10304 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨10304 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0161
    (state : Fin 11742)
    (lower : 10304 ≤ state.val)
    (upper : state.val < 10368) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 10304, by omega⟩
  have state_eq :
      (⟨10304 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0161 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0162 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨10368 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨10368 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0162
    (state : Fin 11742)
    (lower : 10368 ≤ state.val)
    (upper : state.val < 10432) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 10368, by omega⟩
  have state_eq :
      (⟨10368 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0162 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0163 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨10432 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨10432 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0163
    (state : Fin 11742)
    (lower : 10432 ≤ state.val)
    (upper : state.val < 10496) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 10432, by omega⟩
  have state_eq :
      (⟨10432 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0163 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0164 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨10496 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨10496 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0164
    (state : Fin 11742)
    (lower : 10496 ≤ state.val)
    (upper : state.val < 10560) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 10496, by omega⟩
  have state_eq :
      (⟨10496 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0164 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0165 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨10560 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨10560 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0165
    (state : Fin 11742)
    (lower : 10560 ≤ state.val)
    (upper : state.val < 10624) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 10560, by omega⟩
  have state_eq :
      (⟨10560 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0165 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0166 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨10624 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨10624 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0166
    (state : Fin 11742)
    (lower : 10624 ≤ state.val)
    (upper : state.val < 10688) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 10624, by omega⟩
  have state_eq :
      (⟨10624 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0166 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0167 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨10688 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨10688 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0167
    (state : Fin 11742)
    (lower : 10688 ≤ state.val)
    (upper : state.val < 10752) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 10688, by omega⟩
  have state_eq :
      (⟨10688 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0167 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0168 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨10752 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨10752 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0168
    (state : Fin 11742)
    (lower : 10752 ≤ state.val)
    (upper : state.val < 10816) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 10752, by omega⟩
  have state_eq :
      (⟨10752 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0168 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0169 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨10816 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨10816 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0169
    (state : Fin 11742)
    (lower : 10816 ≤ state.val)
    (upper : state.val < 10880) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 10816, by omega⟩
  have state_eq :
      (⟨10816 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0169 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0170 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨10880 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨10880 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0170
    (state : Fin 11742)
    (lower : 10880 ≤ state.val)
    (upper : state.val < 10944) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 10880, by omega⟩
  have state_eq :
      (⟨10880 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0170 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0171 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨10944 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨10944 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0171
    (state : Fin 11742)
    (lower : 10944 ≤ state.val)
    (upper : state.val < 11008) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 10944, by omega⟩
  have state_eq :
      (⟨10944 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0171 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0172 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨11008 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨11008 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0172
    (state : Fin 11742)
    (lower : 11008 ≤ state.val)
    (upper : state.val < 11072) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 11008, by omega⟩
  have state_eq :
      (⟨11008 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0172 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0173 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨11072 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨11072 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0173
    (state : Fin 11742)
    (lower : 11072 ≤ state.val)
    (upper : state.val < 11136) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 11072, by omega⟩
  have state_eq :
      (⟨11072 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0173 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0174 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨11136 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨11136 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0174
    (state : Fin 11742)
    (lower : 11136 ≤ state.val)
    (upper : state.val < 11200) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 11136, by omega⟩
  have state_eq :
      (⟨11136 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0174 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0175 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨11200 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨11200 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0175
    (state : Fin 11742)
    (lower : 11200 ≤ state.val)
    (upper : state.val < 11264) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 11200, by omega⟩
  have state_eq :
      (⟨11200 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0175 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0176 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨11264 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨11264 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0176
    (state : Fin 11742)
    (lower : 11264 ≤ state.val)
    (upper : state.val < 11328) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 11264, by omega⟩
  have state_eq :
      (⟨11264 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0176 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0177 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨11328 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨11328 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0177
    (state : Fin 11742)
    (lower : 11328 ≤ state.val)
    (upper : state.val < 11392) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 11328, by omega⟩
  have state_eq :
      (⟨11328 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0177 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0178 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨11392 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨11392 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0178
    (state : Fin 11742)
    (lower : 11392 ≤ state.val)
    (upper : state.val < 11456) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 11392, by omega⟩
  have state_eq :
      (⟨11392 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0178 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0179 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨11456 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨11456 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0179
    (state : Fin 11742)
    (lower : 11456 ≤ state.val)
    (upper : state.val < 11520) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 11456, by omega⟩
  have state_eq :
      (⟨11456 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0179 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0180 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨11520 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨11520 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0180
    (state : Fin 11742)
    (lower : 11520 ≤ state.val)
    (upper : state.val < 11584) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 11520, by omega⟩
  have state_eq :
      (⟨11520 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0180 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0181 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨11584 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨11584 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0181
    (state : Fin 11742)
    (lower : 11584 ≤ state.val)
    (upper : state.val < 11648) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 11584, by omega⟩
  have state_eq :
      (⟨11584 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0181 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0182 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨11648 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨11648 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0182
    (state : Fin 11742)
    (lower : 11648 ≤ state.val)
    (upper : state.val < 11712) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 11648, by omega⟩
  have state_eq :
      (⟨11648 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0182 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0183 :
    ∀ candidate : Fin 30,
      decodeState (stateVector (⟨11712 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨11712 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0183
    (state : Fin 11742)
    (lower : 11712 ≤ state.val)
    (upper : state.val < 11742) :
    decodeState (stateVector state) = state := by
  let offset : Fin 30 := ⟨state.val - 11712, by omega⟩
  have state_eq :
      (⟨11712 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0183 offset

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.Shards
