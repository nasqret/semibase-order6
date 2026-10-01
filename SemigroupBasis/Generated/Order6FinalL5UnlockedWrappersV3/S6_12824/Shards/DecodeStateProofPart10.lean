import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards.DecodeState
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards.StateVector
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0320 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨20480 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨20480 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0320
    (state : Fin 48684)
    (lower : 20480 ≤ state.val)
    (upper : state.val < 20544) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 20480, by omega⟩
  have state_eq :
      (⟨20480 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0320 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0321 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨20544 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨20544 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0321
    (state : Fin 48684)
    (lower : 20544 ≤ state.val)
    (upper : state.val < 20608) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 20544, by omega⟩
  have state_eq :
      (⟨20544 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0321 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0322 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨20608 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨20608 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0322
    (state : Fin 48684)
    (lower : 20608 ≤ state.val)
    (upper : state.val < 20672) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 20608, by omega⟩
  have state_eq :
      (⟨20608 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0322 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0323 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨20672 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨20672 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0323
    (state : Fin 48684)
    (lower : 20672 ≤ state.val)
    (upper : state.val < 20736) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 20672, by omega⟩
  have state_eq :
      (⟨20672 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0323 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0324 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨20736 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨20736 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0324
    (state : Fin 48684)
    (lower : 20736 ≤ state.val)
    (upper : state.val < 20800) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 20736, by omega⟩
  have state_eq :
      (⟨20736 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0324 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0325 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨20800 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨20800 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0325
    (state : Fin 48684)
    (lower : 20800 ≤ state.val)
    (upper : state.val < 20864) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 20800, by omega⟩
  have state_eq :
      (⟨20800 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0325 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0326 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨20864 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨20864 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0326
    (state : Fin 48684)
    (lower : 20864 ≤ state.val)
    (upper : state.val < 20928) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 20864, by omega⟩
  have state_eq :
      (⟨20864 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0326 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0327 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨20928 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨20928 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0327
    (state : Fin 48684)
    (lower : 20928 ≤ state.val)
    (upper : state.val < 20992) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 20928, by omega⟩
  have state_eq :
      (⟨20928 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0327 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0328 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨20992 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨20992 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0328
    (state : Fin 48684)
    (lower : 20992 ≤ state.val)
    (upper : state.val < 21056) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 20992, by omega⟩
  have state_eq :
      (⟨20992 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0328 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0329 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨21056 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨21056 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0329
    (state : Fin 48684)
    (lower : 21056 ≤ state.val)
    (upper : state.val < 21120) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 21056, by omega⟩
  have state_eq :
      (⟨21056 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0329 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0330 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨21120 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨21120 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0330
    (state : Fin 48684)
    (lower : 21120 ≤ state.val)
    (upper : state.val < 21184) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 21120, by omega⟩
  have state_eq :
      (⟨21120 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0330 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0331 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨21184 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨21184 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0331
    (state : Fin 48684)
    (lower : 21184 ≤ state.val)
    (upper : state.val < 21248) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 21184, by omega⟩
  have state_eq :
      (⟨21184 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0331 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0332 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨21248 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨21248 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0332
    (state : Fin 48684)
    (lower : 21248 ≤ state.val)
    (upper : state.val < 21312) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 21248, by omega⟩
  have state_eq :
      (⟨21248 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0332 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0333 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨21312 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨21312 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0333
    (state : Fin 48684)
    (lower : 21312 ≤ state.val)
    (upper : state.val < 21376) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 21312, by omega⟩
  have state_eq :
      (⟨21312 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0333 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0334 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨21376 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨21376 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0334
    (state : Fin 48684)
    (lower : 21376 ≤ state.val)
    (upper : state.val < 21440) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 21376, by omega⟩
  have state_eq :
      (⟨21376 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0334 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0335 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨21440 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨21440 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0335
    (state : Fin 48684)
    (lower : 21440 ≤ state.val)
    (upper : state.val < 21504) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 21440, by omega⟩
  have state_eq :
      (⟨21440 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0335 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0336 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨21504 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨21504 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0336
    (state : Fin 48684)
    (lower : 21504 ≤ state.val)
    (upper : state.val < 21568) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 21504, by omega⟩
  have state_eq :
      (⟨21504 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0336 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0337 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨21568 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨21568 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0337
    (state : Fin 48684)
    (lower : 21568 ≤ state.val)
    (upper : state.val < 21632) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 21568, by omega⟩
  have state_eq :
      (⟨21568 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0337 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0338 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨21632 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨21632 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0338
    (state : Fin 48684)
    (lower : 21632 ≤ state.val)
    (upper : state.val < 21696) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 21632, by omega⟩
  have state_eq :
      (⟨21632 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0338 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0339 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨21696 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨21696 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0339
    (state : Fin 48684)
    (lower : 21696 ≤ state.val)
    (upper : state.val < 21760) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 21696, by omega⟩
  have state_eq :
      (⟨21696 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0339 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0340 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨21760 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨21760 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0340
    (state : Fin 48684)
    (lower : 21760 ≤ state.val)
    (upper : state.val < 21824) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 21760, by omega⟩
  have state_eq :
      (⟨21760 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0340 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0341 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨21824 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨21824 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0341
    (state : Fin 48684)
    (lower : 21824 ≤ state.val)
    (upper : state.val < 21888) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 21824, by omega⟩
  have state_eq :
      (⟨21824 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0341 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0342 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨21888 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨21888 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0342
    (state : Fin 48684)
    (lower : 21888 ≤ state.val)
    (upper : state.val < 21952) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 21888, by omega⟩
  have state_eq :
      (⟨21888 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0342 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0343 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨21952 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨21952 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0343
    (state : Fin 48684)
    (lower : 21952 ≤ state.val)
    (upper : state.val < 22016) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 21952, by omega⟩
  have state_eq :
      (⟨21952 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0343 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0344 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨22016 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨22016 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0344
    (state : Fin 48684)
    (lower : 22016 ≤ state.val)
    (upper : state.val < 22080) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 22016, by omega⟩
  have state_eq :
      (⟨22016 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0344 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0345 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨22080 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨22080 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0345
    (state : Fin 48684)
    (lower : 22080 ≤ state.val)
    (upper : state.val < 22144) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 22080, by omega⟩
  have state_eq :
      (⟨22080 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0345 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0346 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨22144 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨22144 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0346
    (state : Fin 48684)
    (lower : 22144 ≤ state.val)
    (upper : state.val < 22208) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 22144, by omega⟩
  have state_eq :
      (⟨22144 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0346 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0347 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨22208 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨22208 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0347
    (state : Fin 48684)
    (lower : 22208 ≤ state.val)
    (upper : state.val < 22272) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 22208, by omega⟩
  have state_eq :
      (⟨22208 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0347 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0348 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨22272 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨22272 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0348
    (state : Fin 48684)
    (lower : 22272 ≤ state.val)
    (upper : state.val < 22336) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 22272, by omega⟩
  have state_eq :
      (⟨22272 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0348 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0349 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨22336 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨22336 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0349
    (state : Fin 48684)
    (lower : 22336 ≤ state.val)
    (upper : state.val < 22400) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 22336, by omega⟩
  have state_eq :
      (⟨22336 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0349 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0350 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨22400 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨22400 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0350
    (state : Fin 48684)
    (lower : 22400 ≤ state.val)
    (upper : state.val < 22464) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 22400, by omega⟩
  have state_eq :
      (⟨22400 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0350 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0351 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨22464 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨22464 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0351
    (state : Fin 48684)
    (lower : 22464 ≤ state.val)
    (upper : state.val < 22528) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 22464, by omega⟩
  have state_eq :
      (⟨22464 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0351 offset

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards
