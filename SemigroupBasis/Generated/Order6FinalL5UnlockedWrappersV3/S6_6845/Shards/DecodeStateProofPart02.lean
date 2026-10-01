import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6845.Shards.DecodeState
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6845.Shards.StateVector
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6845.Shards

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0064 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨4096 + candidate.val, by omega⟩ : Fin 4374)) =
        (⟨4096 + candidate.val, by omega⟩ : Fin 4374) := by
  decide

theorem decodeState_stateVectorProof0064
    (state : Fin 4374)
    (lower : 4096 ≤ state.val)
    (upper : state.val < 4160) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 4096, by omega⟩
  have state_eq :
      (⟨4096 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0064 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0065 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨4160 + candidate.val, by omega⟩ : Fin 4374)) =
        (⟨4160 + candidate.val, by omega⟩ : Fin 4374) := by
  decide

theorem decodeState_stateVectorProof0065
    (state : Fin 4374)
    (lower : 4160 ≤ state.val)
    (upper : state.val < 4224) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 4160, by omega⟩
  have state_eq :
      (⟨4160 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0065 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0066 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨4224 + candidate.val, by omega⟩ : Fin 4374)) =
        (⟨4224 + candidate.val, by omega⟩ : Fin 4374) := by
  decide

theorem decodeState_stateVectorProof0066
    (state : Fin 4374)
    (lower : 4224 ≤ state.val)
    (upper : state.val < 4288) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 4224, by omega⟩
  have state_eq :
      (⟨4224 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0066 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0067 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨4288 + candidate.val, by omega⟩ : Fin 4374)) =
        (⟨4288 + candidate.val, by omega⟩ : Fin 4374) := by
  decide

theorem decodeState_stateVectorProof0067
    (state : Fin 4374)
    (lower : 4288 ≤ state.val)
    (upper : state.val < 4352) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 4288, by omega⟩
  have state_eq :
      (⟨4288 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0067 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0068 :
    ∀ candidate : Fin 22,
      decodeState (stateVector (⟨4352 + candidate.val, by omega⟩ : Fin 4374)) =
        (⟨4352 + candidate.val, by omega⟩ : Fin 4374) := by
  decide

theorem decodeState_stateVectorProof0068
    (state : Fin 4374)
    (lower : 4352 ≤ state.val)
    (upper : state.val < 4374) :
    decodeState (stateVector state) = state := by
  let offset : Fin 22 := ⟨state.val - 4352, by omega⟩
  have state_eq :
      (⟨4352 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0068 offset

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6845.Shards
