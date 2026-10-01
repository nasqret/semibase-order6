import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards.DecodeState
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards.StateVector
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0448 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨28672 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨28672 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0448
    (state : Fin 48684)
    (lower : 28672 ≤ state.val)
    (upper : state.val < 28736) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 28672, by omega⟩
  have state_eq :
      (⟨28672 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0448 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0449 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨28736 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨28736 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0449
    (state : Fin 48684)
    (lower : 28736 ≤ state.val)
    (upper : state.val < 28800) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 28736, by omega⟩
  have state_eq :
      (⟨28736 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0449 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0450 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨28800 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨28800 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0450
    (state : Fin 48684)
    (lower : 28800 ≤ state.val)
    (upper : state.val < 28864) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 28800, by omega⟩
  have state_eq :
      (⟨28800 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0450 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0451 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨28864 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨28864 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0451
    (state : Fin 48684)
    (lower : 28864 ≤ state.val)
    (upper : state.val < 28928) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 28864, by omega⟩
  have state_eq :
      (⟨28864 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0451 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0452 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨28928 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨28928 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0452
    (state : Fin 48684)
    (lower : 28928 ≤ state.val)
    (upper : state.val < 28992) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 28928, by omega⟩
  have state_eq :
      (⟨28928 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0452 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0453 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨28992 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨28992 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0453
    (state : Fin 48684)
    (lower : 28992 ≤ state.val)
    (upper : state.val < 29056) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 28992, by omega⟩
  have state_eq :
      (⟨28992 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0453 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0454 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨29056 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨29056 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0454
    (state : Fin 48684)
    (lower : 29056 ≤ state.val)
    (upper : state.val < 29120) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 29056, by omega⟩
  have state_eq :
      (⟨29056 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0454 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0455 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨29120 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨29120 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0455
    (state : Fin 48684)
    (lower : 29120 ≤ state.val)
    (upper : state.val < 29184) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 29120, by omega⟩
  have state_eq :
      (⟨29120 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0455 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0456 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨29184 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨29184 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0456
    (state : Fin 48684)
    (lower : 29184 ≤ state.val)
    (upper : state.val < 29248) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 29184, by omega⟩
  have state_eq :
      (⟨29184 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0456 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0457 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨29248 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨29248 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0457
    (state : Fin 48684)
    (lower : 29248 ≤ state.val)
    (upper : state.val < 29312) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 29248, by omega⟩
  have state_eq :
      (⟨29248 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0457 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0458 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨29312 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨29312 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0458
    (state : Fin 48684)
    (lower : 29312 ≤ state.val)
    (upper : state.val < 29376) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 29312, by omega⟩
  have state_eq :
      (⟨29312 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0458 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0459 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨29376 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨29376 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0459
    (state : Fin 48684)
    (lower : 29376 ≤ state.val)
    (upper : state.val < 29440) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 29376, by omega⟩
  have state_eq :
      (⟨29376 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0459 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0460 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨29440 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨29440 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0460
    (state : Fin 48684)
    (lower : 29440 ≤ state.val)
    (upper : state.val < 29504) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 29440, by omega⟩
  have state_eq :
      (⟨29440 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0460 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0461 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨29504 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨29504 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0461
    (state : Fin 48684)
    (lower : 29504 ≤ state.val)
    (upper : state.val < 29568) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 29504, by omega⟩
  have state_eq :
      (⟨29504 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0461 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0462 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨29568 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨29568 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0462
    (state : Fin 48684)
    (lower : 29568 ≤ state.val)
    (upper : state.val < 29632) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 29568, by omega⟩
  have state_eq :
      (⟨29568 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0462 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0463 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨29632 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨29632 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0463
    (state : Fin 48684)
    (lower : 29632 ≤ state.val)
    (upper : state.val < 29696) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 29632, by omega⟩
  have state_eq :
      (⟨29632 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0463 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0464 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨29696 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨29696 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0464
    (state : Fin 48684)
    (lower : 29696 ≤ state.val)
    (upper : state.val < 29760) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 29696, by omega⟩
  have state_eq :
      (⟨29696 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0464 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0465 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨29760 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨29760 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0465
    (state : Fin 48684)
    (lower : 29760 ≤ state.val)
    (upper : state.val < 29824) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 29760, by omega⟩
  have state_eq :
      (⟨29760 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0465 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0466 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨29824 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨29824 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0466
    (state : Fin 48684)
    (lower : 29824 ≤ state.val)
    (upper : state.val < 29888) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 29824, by omega⟩
  have state_eq :
      (⟨29824 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0466 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0467 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨29888 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨29888 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0467
    (state : Fin 48684)
    (lower : 29888 ≤ state.val)
    (upper : state.val < 29952) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 29888, by omega⟩
  have state_eq :
      (⟨29888 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0467 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0468 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨29952 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨29952 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0468
    (state : Fin 48684)
    (lower : 29952 ≤ state.val)
    (upper : state.val < 30016) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 29952, by omega⟩
  have state_eq :
      (⟨29952 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0468 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0469 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨30016 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨30016 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0469
    (state : Fin 48684)
    (lower : 30016 ≤ state.val)
    (upper : state.val < 30080) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 30016, by omega⟩
  have state_eq :
      (⟨30016 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0469 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0470 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨30080 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨30080 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0470
    (state : Fin 48684)
    (lower : 30080 ≤ state.val)
    (upper : state.val < 30144) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 30080, by omega⟩
  have state_eq :
      (⟨30080 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0470 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0471 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨30144 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨30144 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0471
    (state : Fin 48684)
    (lower : 30144 ≤ state.val)
    (upper : state.val < 30208) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 30144, by omega⟩
  have state_eq :
      (⟨30144 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0471 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0472 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨30208 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨30208 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0472
    (state : Fin 48684)
    (lower : 30208 ≤ state.val)
    (upper : state.val < 30272) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 30208, by omega⟩
  have state_eq :
      (⟨30208 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0472 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0473 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨30272 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨30272 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0473
    (state : Fin 48684)
    (lower : 30272 ≤ state.val)
    (upper : state.val < 30336) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 30272, by omega⟩
  have state_eq :
      (⟨30272 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0473 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0474 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨30336 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨30336 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0474
    (state : Fin 48684)
    (lower : 30336 ≤ state.val)
    (upper : state.val < 30400) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 30336, by omega⟩
  have state_eq :
      (⟨30336 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0474 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0475 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨30400 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨30400 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0475
    (state : Fin 48684)
    (lower : 30400 ≤ state.val)
    (upper : state.val < 30464) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 30400, by omega⟩
  have state_eq :
      (⟨30400 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0475 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0476 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨30464 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨30464 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0476
    (state : Fin 48684)
    (lower : 30464 ≤ state.val)
    (upper : state.val < 30528) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 30464, by omega⟩
  have state_eq :
      (⟨30464 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0476 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0477 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨30528 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨30528 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0477
    (state : Fin 48684)
    (lower : 30528 ≤ state.val)
    (upper : state.val < 30592) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 30528, by omega⟩
  have state_eq :
      (⟨30528 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0477 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0478 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨30592 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨30592 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0478
    (state : Fin 48684)
    (lower : 30592 ≤ state.val)
    (upper : state.val < 30656) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 30592, by omega⟩
  have state_eq :
      (⟨30592 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0478 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0479 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨30656 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨30656 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0479
    (state : Fin 48684)
    (lower : 30656 ≤ state.val)
    (upper : state.val < 30720) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 30656, by omega⟩
  have state_eq :
      (⟨30656 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0479 offset

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards
