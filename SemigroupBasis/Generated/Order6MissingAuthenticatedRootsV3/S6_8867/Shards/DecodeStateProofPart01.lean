import SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.Shards.DecodeState
import SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.Shards.StateVector
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.Shards

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0032 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨2048 + candidate.val, by omega⟩ : Fin 2712)) =
        (⟨2048 + candidate.val, by omega⟩ : Fin 2712) := by
  decide

theorem decodeState_stateVectorProof0032
    (state : Fin 2712)
    (lower : 2048 ≤ state.val)
    (upper : state.val < 2112) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 2048, by omega⟩
  have state_eq :
      (⟨2048 + offset.val, by omega⟩ : Fin 2712) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0032 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0033 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨2112 + candidate.val, by omega⟩ : Fin 2712)) =
        (⟨2112 + candidate.val, by omega⟩ : Fin 2712) := by
  decide

theorem decodeState_stateVectorProof0033
    (state : Fin 2712)
    (lower : 2112 ≤ state.val)
    (upper : state.val < 2176) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 2112, by omega⟩
  have state_eq :
      (⟨2112 + offset.val, by omega⟩ : Fin 2712) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0033 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0034 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨2176 + candidate.val, by omega⟩ : Fin 2712)) =
        (⟨2176 + candidate.val, by omega⟩ : Fin 2712) := by
  decide

theorem decodeState_stateVectorProof0034
    (state : Fin 2712)
    (lower : 2176 ≤ state.val)
    (upper : state.val < 2240) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 2176, by omega⟩
  have state_eq :
      (⟨2176 + offset.val, by omega⟩ : Fin 2712) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0034 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0035 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨2240 + candidate.val, by omega⟩ : Fin 2712)) =
        (⟨2240 + candidate.val, by omega⟩ : Fin 2712) := by
  decide

theorem decodeState_stateVectorProof0035
    (state : Fin 2712)
    (lower : 2240 ≤ state.val)
    (upper : state.val < 2304) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 2240, by omega⟩
  have state_eq :
      (⟨2240 + offset.val, by omega⟩ : Fin 2712) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0035 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0036 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨2304 + candidate.val, by omega⟩ : Fin 2712)) =
        (⟨2304 + candidate.val, by omega⟩ : Fin 2712) := by
  decide

theorem decodeState_stateVectorProof0036
    (state : Fin 2712)
    (lower : 2304 ≤ state.val)
    (upper : state.val < 2368) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 2304, by omega⟩
  have state_eq :
      (⟨2304 + offset.val, by omega⟩ : Fin 2712) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0036 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0037 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨2368 + candidate.val, by omega⟩ : Fin 2712)) =
        (⟨2368 + candidate.val, by omega⟩ : Fin 2712) := by
  decide

theorem decodeState_stateVectorProof0037
    (state : Fin 2712)
    (lower : 2368 ≤ state.val)
    (upper : state.val < 2432) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 2368, by omega⟩
  have state_eq :
      (⟨2368 + offset.val, by omega⟩ : Fin 2712) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0037 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0038 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨2432 + candidate.val, by omega⟩ : Fin 2712)) =
        (⟨2432 + candidate.val, by omega⟩ : Fin 2712) := by
  decide

theorem decodeState_stateVectorProof0038
    (state : Fin 2712)
    (lower : 2432 ≤ state.val)
    (upper : state.val < 2496) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 2432, by omega⟩
  have state_eq :
      (⟨2432 + offset.val, by omega⟩ : Fin 2712) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0038 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0039 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨2496 + candidate.val, by omega⟩ : Fin 2712)) =
        (⟨2496 + candidate.val, by omega⟩ : Fin 2712) := by
  decide

theorem decodeState_stateVectorProof0039
    (state : Fin 2712)
    (lower : 2496 ≤ state.val)
    (upper : state.val < 2560) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 2496, by omega⟩
  have state_eq :
      (⟨2496 + offset.val, by omega⟩ : Fin 2712) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0039 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0040 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨2560 + candidate.val, by omega⟩ : Fin 2712)) =
        (⟨2560 + candidate.val, by omega⟩ : Fin 2712) := by
  decide

theorem decodeState_stateVectorProof0040
    (state : Fin 2712)
    (lower : 2560 ≤ state.val)
    (upper : state.val < 2624) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 2560, by omega⟩
  have state_eq :
      (⟨2560 + offset.val, by omega⟩ : Fin 2712) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0040 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0041 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨2624 + candidate.val, by omega⟩ : Fin 2712)) =
        (⟨2624 + candidate.val, by omega⟩ : Fin 2712) := by
  decide

theorem decodeState_stateVectorProof0041
    (state : Fin 2712)
    (lower : 2624 ≤ state.val)
    (upper : state.val < 2688) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 2624, by omega⟩
  have state_eq :
      (⟨2624 + offset.val, by omega⟩ : Fin 2712) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0041 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0042 :
    ∀ candidate : Fin 24,
      decodeState (stateVector (⟨2688 + candidate.val, by omega⟩ : Fin 2712)) =
        (⟨2688 + candidate.val, by omega⟩ : Fin 2712) := by
  decide

theorem decodeState_stateVectorProof0042
    (state : Fin 2712)
    (lower : 2688 ≤ state.val)
    (upper : state.val < 2712) :
    decodeState (stateVector state) = state := by
  let offset : Fin 24 := ⟨state.val - 2688, by omega⟩
  have state_eq :
      (⟨2688 + offset.val, by omega⟩ : Fin 2712) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0042 offset

end SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.Shards
