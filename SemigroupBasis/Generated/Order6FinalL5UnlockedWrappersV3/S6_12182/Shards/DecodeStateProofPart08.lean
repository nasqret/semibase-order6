import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.Shards.DecodeState
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.Shards.StateVector
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.Shards

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0256 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨16384 + candidate.val, by omega⟩ : Fin 17622)) =
        (⟨16384 + candidate.val, by omega⟩ : Fin 17622) := by
  decide

theorem decodeState_stateVectorProof0256
    (state : Fin 17622)
    (lower : 16384 ≤ state.val)
    (upper : state.val < 16448) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 16384, by omega⟩
  have state_eq :
      (⟨16384 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0256 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0257 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨16448 + candidate.val, by omega⟩ : Fin 17622)) =
        (⟨16448 + candidate.val, by omega⟩ : Fin 17622) := by
  decide

theorem decodeState_stateVectorProof0257
    (state : Fin 17622)
    (lower : 16448 ≤ state.val)
    (upper : state.val < 16512) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 16448, by omega⟩
  have state_eq :
      (⟨16448 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0257 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0258 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨16512 + candidate.val, by omega⟩ : Fin 17622)) =
        (⟨16512 + candidate.val, by omega⟩ : Fin 17622) := by
  decide

theorem decodeState_stateVectorProof0258
    (state : Fin 17622)
    (lower : 16512 ≤ state.val)
    (upper : state.val < 16576) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 16512, by omega⟩
  have state_eq :
      (⟨16512 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0258 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0259 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨16576 + candidate.val, by omega⟩ : Fin 17622)) =
        (⟨16576 + candidate.val, by omega⟩ : Fin 17622) := by
  decide

theorem decodeState_stateVectorProof0259
    (state : Fin 17622)
    (lower : 16576 ≤ state.val)
    (upper : state.val < 16640) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 16576, by omega⟩
  have state_eq :
      (⟨16576 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0259 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0260 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨16640 + candidate.val, by omega⟩ : Fin 17622)) =
        (⟨16640 + candidate.val, by omega⟩ : Fin 17622) := by
  decide

theorem decodeState_stateVectorProof0260
    (state : Fin 17622)
    (lower : 16640 ≤ state.val)
    (upper : state.val < 16704) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 16640, by omega⟩
  have state_eq :
      (⟨16640 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0260 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0261 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨16704 + candidate.val, by omega⟩ : Fin 17622)) =
        (⟨16704 + candidate.val, by omega⟩ : Fin 17622) := by
  decide

theorem decodeState_stateVectorProof0261
    (state : Fin 17622)
    (lower : 16704 ≤ state.val)
    (upper : state.val < 16768) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 16704, by omega⟩
  have state_eq :
      (⟨16704 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0261 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0262 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨16768 + candidate.val, by omega⟩ : Fin 17622)) =
        (⟨16768 + candidate.val, by omega⟩ : Fin 17622) := by
  decide

theorem decodeState_stateVectorProof0262
    (state : Fin 17622)
    (lower : 16768 ≤ state.val)
    (upper : state.val < 16832) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 16768, by omega⟩
  have state_eq :
      (⟨16768 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0262 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0263 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨16832 + candidate.val, by omega⟩ : Fin 17622)) =
        (⟨16832 + candidate.val, by omega⟩ : Fin 17622) := by
  decide

theorem decodeState_stateVectorProof0263
    (state : Fin 17622)
    (lower : 16832 ≤ state.val)
    (upper : state.val < 16896) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 16832, by omega⟩
  have state_eq :
      (⟨16832 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0263 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0264 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨16896 + candidate.val, by omega⟩ : Fin 17622)) =
        (⟨16896 + candidate.val, by omega⟩ : Fin 17622) := by
  decide

theorem decodeState_stateVectorProof0264
    (state : Fin 17622)
    (lower : 16896 ≤ state.val)
    (upper : state.val < 16960) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 16896, by omega⟩
  have state_eq :
      (⟨16896 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0264 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0265 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨16960 + candidate.val, by omega⟩ : Fin 17622)) =
        (⟨16960 + candidate.val, by omega⟩ : Fin 17622) := by
  decide

theorem decodeState_stateVectorProof0265
    (state : Fin 17622)
    (lower : 16960 ≤ state.val)
    (upper : state.val < 17024) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 16960, by omega⟩
  have state_eq :
      (⟨16960 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0265 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0266 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨17024 + candidate.val, by omega⟩ : Fin 17622)) =
        (⟨17024 + candidate.val, by omega⟩ : Fin 17622) := by
  decide

theorem decodeState_stateVectorProof0266
    (state : Fin 17622)
    (lower : 17024 ≤ state.val)
    (upper : state.val < 17088) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 17024, by omega⟩
  have state_eq :
      (⟨17024 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0266 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0267 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨17088 + candidate.val, by omega⟩ : Fin 17622)) =
        (⟨17088 + candidate.val, by omega⟩ : Fin 17622) := by
  decide

theorem decodeState_stateVectorProof0267
    (state : Fin 17622)
    (lower : 17088 ≤ state.val)
    (upper : state.val < 17152) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 17088, by omega⟩
  have state_eq :
      (⟨17088 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0267 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0268 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨17152 + candidate.val, by omega⟩ : Fin 17622)) =
        (⟨17152 + candidate.val, by omega⟩ : Fin 17622) := by
  decide

theorem decodeState_stateVectorProof0268
    (state : Fin 17622)
    (lower : 17152 ≤ state.val)
    (upper : state.val < 17216) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 17152, by omega⟩
  have state_eq :
      (⟨17152 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0268 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0269 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨17216 + candidate.val, by omega⟩ : Fin 17622)) =
        (⟨17216 + candidate.val, by omega⟩ : Fin 17622) := by
  decide

theorem decodeState_stateVectorProof0269
    (state : Fin 17622)
    (lower : 17216 ≤ state.val)
    (upper : state.val < 17280) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 17216, by omega⟩
  have state_eq :
      (⟨17216 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0269 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0270 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨17280 + candidate.val, by omega⟩ : Fin 17622)) =
        (⟨17280 + candidate.val, by omega⟩ : Fin 17622) := by
  decide

theorem decodeState_stateVectorProof0270
    (state : Fin 17622)
    (lower : 17280 ≤ state.val)
    (upper : state.val < 17344) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 17280, by omega⟩
  have state_eq :
      (⟨17280 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0270 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0271 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨17344 + candidate.val, by omega⟩ : Fin 17622)) =
        (⟨17344 + candidate.val, by omega⟩ : Fin 17622) := by
  decide

theorem decodeState_stateVectorProof0271
    (state : Fin 17622)
    (lower : 17344 ≤ state.val)
    (upper : state.val < 17408) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 17344, by omega⟩
  have state_eq :
      (⟨17344 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0271 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0272 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨17408 + candidate.val, by omega⟩ : Fin 17622)) =
        (⟨17408 + candidate.val, by omega⟩ : Fin 17622) := by
  decide

theorem decodeState_stateVectorProof0272
    (state : Fin 17622)
    (lower : 17408 ≤ state.val)
    (upper : state.val < 17472) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 17408, by omega⟩
  have state_eq :
      (⟨17408 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0272 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0273 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨17472 + candidate.val, by omega⟩ : Fin 17622)) =
        (⟨17472 + candidate.val, by omega⟩ : Fin 17622) := by
  decide

theorem decodeState_stateVectorProof0273
    (state : Fin 17622)
    (lower : 17472 ≤ state.val)
    (upper : state.val < 17536) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 17472, by omega⟩
  have state_eq :
      (⟨17472 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0273 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0274 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨17536 + candidate.val, by omega⟩ : Fin 17622)) =
        (⟨17536 + candidate.val, by omega⟩ : Fin 17622) := by
  decide

theorem decodeState_stateVectorProof0274
    (state : Fin 17622)
    (lower : 17536 ≤ state.val)
    (upper : state.val < 17600) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 17536, by omega⟩
  have state_eq :
      (⟨17536 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0274 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0275 :
    ∀ candidate : Fin 22,
      decodeState (stateVector (⟨17600 + candidate.val, by omega⟩ : Fin 17622)) =
        (⟨17600 + candidate.val, by omega⟩ : Fin 17622) := by
  decide

theorem decodeState_stateVectorProof0275
    (state : Fin 17622)
    (lower : 17600 ≤ state.val)
    (upper : state.val < 17622) :
    decodeState (stateVector state) = state := by
  let offset : Fin 22 := ⟨state.val - 17600, by omega⟩
  have state_eq :
      (⟨17600 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0275 offset

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.Shards
