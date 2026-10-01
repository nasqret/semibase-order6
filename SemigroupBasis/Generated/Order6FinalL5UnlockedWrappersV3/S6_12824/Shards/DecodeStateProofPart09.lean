import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards.DecodeState
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards.StateVector
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0288 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨18432 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨18432 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0288
    (state : Fin 48684)
    (lower : 18432 ≤ state.val)
    (upper : state.val < 18496) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 18432, by omega⟩
  have state_eq :
      (⟨18432 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0288 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0289 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨18496 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨18496 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0289
    (state : Fin 48684)
    (lower : 18496 ≤ state.val)
    (upper : state.val < 18560) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 18496, by omega⟩
  have state_eq :
      (⟨18496 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0289 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0290 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨18560 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨18560 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0290
    (state : Fin 48684)
    (lower : 18560 ≤ state.val)
    (upper : state.val < 18624) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 18560, by omega⟩
  have state_eq :
      (⟨18560 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0290 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0291 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨18624 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨18624 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0291
    (state : Fin 48684)
    (lower : 18624 ≤ state.val)
    (upper : state.val < 18688) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 18624, by omega⟩
  have state_eq :
      (⟨18624 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0291 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0292 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨18688 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨18688 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0292
    (state : Fin 48684)
    (lower : 18688 ≤ state.val)
    (upper : state.val < 18752) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 18688, by omega⟩
  have state_eq :
      (⟨18688 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0292 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0293 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨18752 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨18752 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0293
    (state : Fin 48684)
    (lower : 18752 ≤ state.val)
    (upper : state.val < 18816) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 18752, by omega⟩
  have state_eq :
      (⟨18752 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0293 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0294 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨18816 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨18816 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0294
    (state : Fin 48684)
    (lower : 18816 ≤ state.val)
    (upper : state.val < 18880) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 18816, by omega⟩
  have state_eq :
      (⟨18816 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0294 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0295 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨18880 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨18880 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0295
    (state : Fin 48684)
    (lower : 18880 ≤ state.val)
    (upper : state.val < 18944) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 18880, by omega⟩
  have state_eq :
      (⟨18880 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0295 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0296 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨18944 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨18944 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0296
    (state : Fin 48684)
    (lower : 18944 ≤ state.val)
    (upper : state.val < 19008) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 18944, by omega⟩
  have state_eq :
      (⟨18944 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0296 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0297 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨19008 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨19008 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0297
    (state : Fin 48684)
    (lower : 19008 ≤ state.val)
    (upper : state.val < 19072) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 19008, by omega⟩
  have state_eq :
      (⟨19008 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0297 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0298 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨19072 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨19072 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0298
    (state : Fin 48684)
    (lower : 19072 ≤ state.val)
    (upper : state.val < 19136) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 19072, by omega⟩
  have state_eq :
      (⟨19072 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0298 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0299 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨19136 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨19136 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0299
    (state : Fin 48684)
    (lower : 19136 ≤ state.val)
    (upper : state.val < 19200) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 19136, by omega⟩
  have state_eq :
      (⟨19136 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0299 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0300 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨19200 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨19200 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0300
    (state : Fin 48684)
    (lower : 19200 ≤ state.val)
    (upper : state.val < 19264) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 19200, by omega⟩
  have state_eq :
      (⟨19200 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0300 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0301 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨19264 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨19264 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0301
    (state : Fin 48684)
    (lower : 19264 ≤ state.val)
    (upper : state.val < 19328) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 19264, by omega⟩
  have state_eq :
      (⟨19264 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0301 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0302 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨19328 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨19328 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0302
    (state : Fin 48684)
    (lower : 19328 ≤ state.val)
    (upper : state.val < 19392) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 19328, by omega⟩
  have state_eq :
      (⟨19328 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0302 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0303 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨19392 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨19392 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0303
    (state : Fin 48684)
    (lower : 19392 ≤ state.val)
    (upper : state.val < 19456) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 19392, by omega⟩
  have state_eq :
      (⟨19392 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0303 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0304 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨19456 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨19456 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0304
    (state : Fin 48684)
    (lower : 19456 ≤ state.val)
    (upper : state.val < 19520) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 19456, by omega⟩
  have state_eq :
      (⟨19456 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0304 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0305 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨19520 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨19520 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0305
    (state : Fin 48684)
    (lower : 19520 ≤ state.val)
    (upper : state.val < 19584) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 19520, by omega⟩
  have state_eq :
      (⟨19520 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0305 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0306 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨19584 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨19584 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0306
    (state : Fin 48684)
    (lower : 19584 ≤ state.val)
    (upper : state.val < 19648) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 19584, by omega⟩
  have state_eq :
      (⟨19584 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0306 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0307 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨19648 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨19648 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0307
    (state : Fin 48684)
    (lower : 19648 ≤ state.val)
    (upper : state.val < 19712) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 19648, by omega⟩
  have state_eq :
      (⟨19648 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0307 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0308 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨19712 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨19712 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0308
    (state : Fin 48684)
    (lower : 19712 ≤ state.val)
    (upper : state.val < 19776) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 19712, by omega⟩
  have state_eq :
      (⟨19712 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0308 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0309 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨19776 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨19776 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0309
    (state : Fin 48684)
    (lower : 19776 ≤ state.val)
    (upper : state.val < 19840) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 19776, by omega⟩
  have state_eq :
      (⟨19776 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0309 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0310 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨19840 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨19840 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0310
    (state : Fin 48684)
    (lower : 19840 ≤ state.val)
    (upper : state.val < 19904) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 19840, by omega⟩
  have state_eq :
      (⟨19840 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0310 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0311 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨19904 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨19904 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0311
    (state : Fin 48684)
    (lower : 19904 ≤ state.val)
    (upper : state.val < 19968) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 19904, by omega⟩
  have state_eq :
      (⟨19904 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0311 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0312 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨19968 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨19968 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0312
    (state : Fin 48684)
    (lower : 19968 ≤ state.val)
    (upper : state.val < 20032) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 19968, by omega⟩
  have state_eq :
      (⟨19968 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0312 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0313 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨20032 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨20032 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0313
    (state : Fin 48684)
    (lower : 20032 ≤ state.val)
    (upper : state.val < 20096) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 20032, by omega⟩
  have state_eq :
      (⟨20032 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0313 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0314 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨20096 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨20096 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0314
    (state : Fin 48684)
    (lower : 20096 ≤ state.val)
    (upper : state.val < 20160) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 20096, by omega⟩
  have state_eq :
      (⟨20096 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0314 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0315 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨20160 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨20160 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0315
    (state : Fin 48684)
    (lower : 20160 ≤ state.val)
    (upper : state.val < 20224) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 20160, by omega⟩
  have state_eq :
      (⟨20160 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0315 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0316 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨20224 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨20224 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0316
    (state : Fin 48684)
    (lower : 20224 ≤ state.val)
    (upper : state.val < 20288) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 20224, by omega⟩
  have state_eq :
      (⟨20224 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0316 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0317 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨20288 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨20288 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0317
    (state : Fin 48684)
    (lower : 20288 ≤ state.val)
    (upper : state.val < 20352) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 20288, by omega⟩
  have state_eq :
      (⟨20288 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0317 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0318 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨20352 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨20352 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0318
    (state : Fin 48684)
    (lower : 20352 ≤ state.val)
    (upper : state.val < 20416) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 20352, by omega⟩
  have state_eq :
      (⟨20352 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0318 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0319 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨20416 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨20416 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0319
    (state : Fin 48684)
    (lower : 20416 ≤ state.val)
    (upper : state.val < 20480) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 20416, by omega⟩
  have state_eq :
      (⟨20416 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0319 offset

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards
