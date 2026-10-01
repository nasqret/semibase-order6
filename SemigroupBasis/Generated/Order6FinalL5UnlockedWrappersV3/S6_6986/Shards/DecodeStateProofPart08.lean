import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.Shards.DecodeState
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.Shards.StateVector
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.Shards

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0256 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨16384 + candidate.val, by omega⟩ : Fin 18432)) =
        (⟨16384 + candidate.val, by omega⟩ : Fin 18432) := by
  decide

theorem decodeState_stateVectorProof0256
    (state : Fin 18432)
    (lower : 16384 ≤ state.val)
    (upper : state.val < 16448) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 16384, by omega⟩
  have state_eq :
      (⟨16384 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0256 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0257 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨16448 + candidate.val, by omega⟩ : Fin 18432)) =
        (⟨16448 + candidate.val, by omega⟩ : Fin 18432) := by
  decide

theorem decodeState_stateVectorProof0257
    (state : Fin 18432)
    (lower : 16448 ≤ state.val)
    (upper : state.val < 16512) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 16448, by omega⟩
  have state_eq :
      (⟨16448 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0257 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0258 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨16512 + candidate.val, by omega⟩ : Fin 18432)) =
        (⟨16512 + candidate.val, by omega⟩ : Fin 18432) := by
  decide

theorem decodeState_stateVectorProof0258
    (state : Fin 18432)
    (lower : 16512 ≤ state.val)
    (upper : state.val < 16576) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 16512, by omega⟩
  have state_eq :
      (⟨16512 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0258 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0259 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨16576 + candidate.val, by omega⟩ : Fin 18432)) =
        (⟨16576 + candidate.val, by omega⟩ : Fin 18432) := by
  decide

theorem decodeState_stateVectorProof0259
    (state : Fin 18432)
    (lower : 16576 ≤ state.val)
    (upper : state.val < 16640) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 16576, by omega⟩
  have state_eq :
      (⟨16576 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0259 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0260 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨16640 + candidate.val, by omega⟩ : Fin 18432)) =
        (⟨16640 + candidate.val, by omega⟩ : Fin 18432) := by
  decide

theorem decodeState_stateVectorProof0260
    (state : Fin 18432)
    (lower : 16640 ≤ state.val)
    (upper : state.val < 16704) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 16640, by omega⟩
  have state_eq :
      (⟨16640 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0260 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0261 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨16704 + candidate.val, by omega⟩ : Fin 18432)) =
        (⟨16704 + candidate.val, by omega⟩ : Fin 18432) := by
  decide

theorem decodeState_stateVectorProof0261
    (state : Fin 18432)
    (lower : 16704 ≤ state.val)
    (upper : state.val < 16768) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 16704, by omega⟩
  have state_eq :
      (⟨16704 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0261 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0262 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨16768 + candidate.val, by omega⟩ : Fin 18432)) =
        (⟨16768 + candidate.val, by omega⟩ : Fin 18432) := by
  decide

theorem decodeState_stateVectorProof0262
    (state : Fin 18432)
    (lower : 16768 ≤ state.val)
    (upper : state.val < 16832) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 16768, by omega⟩
  have state_eq :
      (⟨16768 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0262 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0263 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨16832 + candidate.val, by omega⟩ : Fin 18432)) =
        (⟨16832 + candidate.val, by omega⟩ : Fin 18432) := by
  decide

theorem decodeState_stateVectorProof0263
    (state : Fin 18432)
    (lower : 16832 ≤ state.val)
    (upper : state.val < 16896) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 16832, by omega⟩
  have state_eq :
      (⟨16832 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0263 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0264 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨16896 + candidate.val, by omega⟩ : Fin 18432)) =
        (⟨16896 + candidate.val, by omega⟩ : Fin 18432) := by
  decide

theorem decodeState_stateVectorProof0264
    (state : Fin 18432)
    (lower : 16896 ≤ state.val)
    (upper : state.val < 16960) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 16896, by omega⟩
  have state_eq :
      (⟨16896 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0264 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0265 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨16960 + candidate.val, by omega⟩ : Fin 18432)) =
        (⟨16960 + candidate.val, by omega⟩ : Fin 18432) := by
  decide

theorem decodeState_stateVectorProof0265
    (state : Fin 18432)
    (lower : 16960 ≤ state.val)
    (upper : state.val < 17024) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 16960, by omega⟩
  have state_eq :
      (⟨16960 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0265 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0266 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨17024 + candidate.val, by omega⟩ : Fin 18432)) =
        (⟨17024 + candidate.val, by omega⟩ : Fin 18432) := by
  decide

theorem decodeState_stateVectorProof0266
    (state : Fin 18432)
    (lower : 17024 ≤ state.val)
    (upper : state.val < 17088) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 17024, by omega⟩
  have state_eq :
      (⟨17024 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0266 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0267 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨17088 + candidate.val, by omega⟩ : Fin 18432)) =
        (⟨17088 + candidate.val, by omega⟩ : Fin 18432) := by
  decide

theorem decodeState_stateVectorProof0267
    (state : Fin 18432)
    (lower : 17088 ≤ state.val)
    (upper : state.val < 17152) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 17088, by omega⟩
  have state_eq :
      (⟨17088 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0267 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0268 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨17152 + candidate.val, by omega⟩ : Fin 18432)) =
        (⟨17152 + candidate.val, by omega⟩ : Fin 18432) := by
  decide

theorem decodeState_stateVectorProof0268
    (state : Fin 18432)
    (lower : 17152 ≤ state.val)
    (upper : state.val < 17216) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 17152, by omega⟩
  have state_eq :
      (⟨17152 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0268 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0269 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨17216 + candidate.val, by omega⟩ : Fin 18432)) =
        (⟨17216 + candidate.val, by omega⟩ : Fin 18432) := by
  decide

theorem decodeState_stateVectorProof0269
    (state : Fin 18432)
    (lower : 17216 ≤ state.val)
    (upper : state.val < 17280) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 17216, by omega⟩
  have state_eq :
      (⟨17216 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0269 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0270 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨17280 + candidate.val, by omega⟩ : Fin 18432)) =
        (⟨17280 + candidate.val, by omega⟩ : Fin 18432) := by
  decide

theorem decodeState_stateVectorProof0270
    (state : Fin 18432)
    (lower : 17280 ≤ state.val)
    (upper : state.val < 17344) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 17280, by omega⟩
  have state_eq :
      (⟨17280 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0270 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0271 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨17344 + candidate.val, by omega⟩ : Fin 18432)) =
        (⟨17344 + candidate.val, by omega⟩ : Fin 18432) := by
  decide

theorem decodeState_stateVectorProof0271
    (state : Fin 18432)
    (lower : 17344 ≤ state.val)
    (upper : state.val < 17408) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 17344, by omega⟩
  have state_eq :
      (⟨17344 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0271 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0272 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨17408 + candidate.val, by omega⟩ : Fin 18432)) =
        (⟨17408 + candidate.val, by omega⟩ : Fin 18432) := by
  decide

theorem decodeState_stateVectorProof0272
    (state : Fin 18432)
    (lower : 17408 ≤ state.val)
    (upper : state.val < 17472) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 17408, by omega⟩
  have state_eq :
      (⟨17408 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0272 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0273 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨17472 + candidate.val, by omega⟩ : Fin 18432)) =
        (⟨17472 + candidate.val, by omega⟩ : Fin 18432) := by
  decide

theorem decodeState_stateVectorProof0273
    (state : Fin 18432)
    (lower : 17472 ≤ state.val)
    (upper : state.val < 17536) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 17472, by omega⟩
  have state_eq :
      (⟨17472 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0273 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0274 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨17536 + candidate.val, by omega⟩ : Fin 18432)) =
        (⟨17536 + candidate.val, by omega⟩ : Fin 18432) := by
  decide

theorem decodeState_stateVectorProof0274
    (state : Fin 18432)
    (lower : 17536 ≤ state.val)
    (upper : state.val < 17600) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 17536, by omega⟩
  have state_eq :
      (⟨17536 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0274 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0275 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨17600 + candidate.val, by omega⟩ : Fin 18432)) =
        (⟨17600 + candidate.val, by omega⟩ : Fin 18432) := by
  decide

theorem decodeState_stateVectorProof0275
    (state : Fin 18432)
    (lower : 17600 ≤ state.val)
    (upper : state.val < 17664) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 17600, by omega⟩
  have state_eq :
      (⟨17600 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0275 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0276 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨17664 + candidate.val, by omega⟩ : Fin 18432)) =
        (⟨17664 + candidate.val, by omega⟩ : Fin 18432) := by
  decide

theorem decodeState_stateVectorProof0276
    (state : Fin 18432)
    (lower : 17664 ≤ state.val)
    (upper : state.val < 17728) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 17664, by omega⟩
  have state_eq :
      (⟨17664 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0276 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0277 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨17728 + candidate.val, by omega⟩ : Fin 18432)) =
        (⟨17728 + candidate.val, by omega⟩ : Fin 18432) := by
  decide

theorem decodeState_stateVectorProof0277
    (state : Fin 18432)
    (lower : 17728 ≤ state.val)
    (upper : state.val < 17792) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 17728, by omega⟩
  have state_eq :
      (⟨17728 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0277 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0278 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨17792 + candidate.val, by omega⟩ : Fin 18432)) =
        (⟨17792 + candidate.val, by omega⟩ : Fin 18432) := by
  decide

theorem decodeState_stateVectorProof0278
    (state : Fin 18432)
    (lower : 17792 ≤ state.val)
    (upper : state.val < 17856) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 17792, by omega⟩
  have state_eq :
      (⟨17792 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0278 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0279 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨17856 + candidate.val, by omega⟩ : Fin 18432)) =
        (⟨17856 + candidate.val, by omega⟩ : Fin 18432) := by
  decide

theorem decodeState_stateVectorProof0279
    (state : Fin 18432)
    (lower : 17856 ≤ state.val)
    (upper : state.val < 17920) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 17856, by omega⟩
  have state_eq :
      (⟨17856 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0279 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0280 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨17920 + candidate.val, by omega⟩ : Fin 18432)) =
        (⟨17920 + candidate.val, by omega⟩ : Fin 18432) := by
  decide

theorem decodeState_stateVectorProof0280
    (state : Fin 18432)
    (lower : 17920 ≤ state.val)
    (upper : state.val < 17984) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 17920, by omega⟩
  have state_eq :
      (⟨17920 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0280 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0281 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨17984 + candidate.val, by omega⟩ : Fin 18432)) =
        (⟨17984 + candidate.val, by omega⟩ : Fin 18432) := by
  decide

theorem decodeState_stateVectorProof0281
    (state : Fin 18432)
    (lower : 17984 ≤ state.val)
    (upper : state.val < 18048) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 17984, by omega⟩
  have state_eq :
      (⟨17984 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0281 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0282 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨18048 + candidate.val, by omega⟩ : Fin 18432)) =
        (⟨18048 + candidate.val, by omega⟩ : Fin 18432) := by
  decide

theorem decodeState_stateVectorProof0282
    (state : Fin 18432)
    (lower : 18048 ≤ state.val)
    (upper : state.val < 18112) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 18048, by omega⟩
  have state_eq :
      (⟨18048 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0282 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0283 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨18112 + candidate.val, by omega⟩ : Fin 18432)) =
        (⟨18112 + candidate.val, by omega⟩ : Fin 18432) := by
  decide

theorem decodeState_stateVectorProof0283
    (state : Fin 18432)
    (lower : 18112 ≤ state.val)
    (upper : state.val < 18176) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 18112, by omega⟩
  have state_eq :
      (⟨18112 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0283 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0284 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨18176 + candidate.val, by omega⟩ : Fin 18432)) =
        (⟨18176 + candidate.val, by omega⟩ : Fin 18432) := by
  decide

theorem decodeState_stateVectorProof0284
    (state : Fin 18432)
    (lower : 18176 ≤ state.val)
    (upper : state.val < 18240) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 18176, by omega⟩
  have state_eq :
      (⟨18176 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0284 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0285 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨18240 + candidate.val, by omega⟩ : Fin 18432)) =
        (⟨18240 + candidate.val, by omega⟩ : Fin 18432) := by
  decide

theorem decodeState_stateVectorProof0285
    (state : Fin 18432)
    (lower : 18240 ≤ state.val)
    (upper : state.val < 18304) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 18240, by omega⟩
  have state_eq :
      (⟨18240 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0285 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0286 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨18304 + candidate.val, by omega⟩ : Fin 18432)) =
        (⟨18304 + candidate.val, by omega⟩ : Fin 18432) := by
  decide

theorem decodeState_stateVectorProof0286
    (state : Fin 18432)
    (lower : 18304 ≤ state.val)
    (upper : state.val < 18368) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 18304, by omega⟩
  have state_eq :
      (⟨18304 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0286 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0287 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨18368 + candidate.val, by omega⟩ : Fin 18432)) =
        (⟨18368 + candidate.val, by omega⟩ : Fin 18432) := by
  decide

theorem decodeState_stateVectorProof0287
    (state : Fin 18432)
    (lower : 18368 ≤ state.val)
    (upper : state.val < 18432) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 18368, by omega⟩
  have state_eq :
      (⟨18368 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0287 offset

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.Shards
