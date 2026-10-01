import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards.DecodeState
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards.StateVector
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0512 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨32768 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨32768 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0512
    (state : Fin 48684)
    (lower : 32768 ≤ state.val)
    (upper : state.val < 32832) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 32768, by omega⟩
  have state_eq :
      (⟨32768 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0512 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0513 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨32832 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨32832 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0513
    (state : Fin 48684)
    (lower : 32832 ≤ state.val)
    (upper : state.val < 32896) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 32832, by omega⟩
  have state_eq :
      (⟨32832 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0513 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0514 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨32896 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨32896 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0514
    (state : Fin 48684)
    (lower : 32896 ≤ state.val)
    (upper : state.val < 32960) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 32896, by omega⟩
  have state_eq :
      (⟨32896 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0514 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0515 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨32960 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨32960 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0515
    (state : Fin 48684)
    (lower : 32960 ≤ state.val)
    (upper : state.val < 33024) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 32960, by omega⟩
  have state_eq :
      (⟨32960 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0515 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0516 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨33024 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨33024 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0516
    (state : Fin 48684)
    (lower : 33024 ≤ state.val)
    (upper : state.val < 33088) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 33024, by omega⟩
  have state_eq :
      (⟨33024 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0516 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0517 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨33088 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨33088 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0517
    (state : Fin 48684)
    (lower : 33088 ≤ state.val)
    (upper : state.val < 33152) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 33088, by omega⟩
  have state_eq :
      (⟨33088 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0517 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0518 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨33152 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨33152 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0518
    (state : Fin 48684)
    (lower : 33152 ≤ state.val)
    (upper : state.val < 33216) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 33152, by omega⟩
  have state_eq :
      (⟨33152 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0518 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0519 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨33216 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨33216 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0519
    (state : Fin 48684)
    (lower : 33216 ≤ state.val)
    (upper : state.val < 33280) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 33216, by omega⟩
  have state_eq :
      (⟨33216 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0519 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0520 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨33280 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨33280 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0520
    (state : Fin 48684)
    (lower : 33280 ≤ state.val)
    (upper : state.val < 33344) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 33280, by omega⟩
  have state_eq :
      (⟨33280 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0520 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0521 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨33344 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨33344 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0521
    (state : Fin 48684)
    (lower : 33344 ≤ state.val)
    (upper : state.val < 33408) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 33344, by omega⟩
  have state_eq :
      (⟨33344 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0521 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0522 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨33408 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨33408 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0522
    (state : Fin 48684)
    (lower : 33408 ≤ state.val)
    (upper : state.val < 33472) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 33408, by omega⟩
  have state_eq :
      (⟨33408 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0522 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0523 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨33472 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨33472 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0523
    (state : Fin 48684)
    (lower : 33472 ≤ state.val)
    (upper : state.val < 33536) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 33472, by omega⟩
  have state_eq :
      (⟨33472 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0523 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0524 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨33536 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨33536 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0524
    (state : Fin 48684)
    (lower : 33536 ≤ state.val)
    (upper : state.val < 33600) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 33536, by omega⟩
  have state_eq :
      (⟨33536 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0524 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0525 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨33600 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨33600 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0525
    (state : Fin 48684)
    (lower : 33600 ≤ state.val)
    (upper : state.val < 33664) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 33600, by omega⟩
  have state_eq :
      (⟨33600 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0525 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0526 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨33664 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨33664 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0526
    (state : Fin 48684)
    (lower : 33664 ≤ state.val)
    (upper : state.val < 33728) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 33664, by omega⟩
  have state_eq :
      (⟨33664 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0526 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0527 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨33728 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨33728 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0527
    (state : Fin 48684)
    (lower : 33728 ≤ state.val)
    (upper : state.val < 33792) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 33728, by omega⟩
  have state_eq :
      (⟨33728 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0527 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0528 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨33792 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨33792 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0528
    (state : Fin 48684)
    (lower : 33792 ≤ state.val)
    (upper : state.val < 33856) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 33792, by omega⟩
  have state_eq :
      (⟨33792 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0528 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0529 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨33856 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨33856 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0529
    (state : Fin 48684)
    (lower : 33856 ≤ state.val)
    (upper : state.val < 33920) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 33856, by omega⟩
  have state_eq :
      (⟨33856 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0529 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0530 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨33920 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨33920 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0530
    (state : Fin 48684)
    (lower : 33920 ≤ state.val)
    (upper : state.val < 33984) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 33920, by omega⟩
  have state_eq :
      (⟨33920 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0530 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0531 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨33984 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨33984 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0531
    (state : Fin 48684)
    (lower : 33984 ≤ state.val)
    (upper : state.val < 34048) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 33984, by omega⟩
  have state_eq :
      (⟨33984 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0531 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0532 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨34048 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨34048 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0532
    (state : Fin 48684)
    (lower : 34048 ≤ state.val)
    (upper : state.val < 34112) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 34048, by omega⟩
  have state_eq :
      (⟨34048 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0532 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0533 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨34112 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨34112 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0533
    (state : Fin 48684)
    (lower : 34112 ≤ state.val)
    (upper : state.val < 34176) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 34112, by omega⟩
  have state_eq :
      (⟨34112 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0533 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0534 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨34176 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨34176 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0534
    (state : Fin 48684)
    (lower : 34176 ≤ state.val)
    (upper : state.val < 34240) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 34176, by omega⟩
  have state_eq :
      (⟨34176 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0534 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0535 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨34240 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨34240 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0535
    (state : Fin 48684)
    (lower : 34240 ≤ state.val)
    (upper : state.val < 34304) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 34240, by omega⟩
  have state_eq :
      (⟨34240 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0535 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0536 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨34304 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨34304 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0536
    (state : Fin 48684)
    (lower : 34304 ≤ state.val)
    (upper : state.val < 34368) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 34304, by omega⟩
  have state_eq :
      (⟨34304 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0536 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0537 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨34368 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨34368 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0537
    (state : Fin 48684)
    (lower : 34368 ≤ state.val)
    (upper : state.val < 34432) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 34368, by omega⟩
  have state_eq :
      (⟨34368 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0537 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0538 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨34432 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨34432 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0538
    (state : Fin 48684)
    (lower : 34432 ≤ state.val)
    (upper : state.val < 34496) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 34432, by omega⟩
  have state_eq :
      (⟨34432 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0538 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0539 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨34496 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨34496 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0539
    (state : Fin 48684)
    (lower : 34496 ≤ state.val)
    (upper : state.val < 34560) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 34496, by omega⟩
  have state_eq :
      (⟨34496 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0539 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0540 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨34560 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨34560 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0540
    (state : Fin 48684)
    (lower : 34560 ≤ state.val)
    (upper : state.val < 34624) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 34560, by omega⟩
  have state_eq :
      (⟨34560 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0540 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0541 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨34624 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨34624 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0541
    (state : Fin 48684)
    (lower : 34624 ≤ state.val)
    (upper : state.val < 34688) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 34624, by omega⟩
  have state_eq :
      (⟨34624 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0541 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0542 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨34688 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨34688 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0542
    (state : Fin 48684)
    (lower : 34688 ≤ state.val)
    (upper : state.val < 34752) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 34688, by omega⟩
  have state_eq :
      (⟨34688 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0542 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0543 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨34752 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨34752 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0543
    (state : Fin 48684)
    (lower : 34752 ≤ state.val)
    (upper : state.val < 34816) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 34752, by omega⟩
  have state_eq :
      (⟨34752 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0543 offset

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards
