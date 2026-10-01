import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards.DecodeState
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards.StateVector
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0480 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨30720 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨30720 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0480
    (state : Fin 48684)
    (lower : 30720 ≤ state.val)
    (upper : state.val < 30784) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 30720, by omega⟩
  have state_eq :
      (⟨30720 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0480 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0481 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨30784 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨30784 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0481
    (state : Fin 48684)
    (lower : 30784 ≤ state.val)
    (upper : state.val < 30848) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 30784, by omega⟩
  have state_eq :
      (⟨30784 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0481 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0482 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨30848 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨30848 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0482
    (state : Fin 48684)
    (lower : 30848 ≤ state.val)
    (upper : state.val < 30912) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 30848, by omega⟩
  have state_eq :
      (⟨30848 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0482 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0483 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨30912 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨30912 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0483
    (state : Fin 48684)
    (lower : 30912 ≤ state.val)
    (upper : state.val < 30976) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 30912, by omega⟩
  have state_eq :
      (⟨30912 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0483 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0484 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨30976 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨30976 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0484
    (state : Fin 48684)
    (lower : 30976 ≤ state.val)
    (upper : state.val < 31040) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 30976, by omega⟩
  have state_eq :
      (⟨30976 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0484 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0485 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨31040 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨31040 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0485
    (state : Fin 48684)
    (lower : 31040 ≤ state.val)
    (upper : state.val < 31104) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 31040, by omega⟩
  have state_eq :
      (⟨31040 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0485 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0486 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨31104 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨31104 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0486
    (state : Fin 48684)
    (lower : 31104 ≤ state.val)
    (upper : state.val < 31168) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 31104, by omega⟩
  have state_eq :
      (⟨31104 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0486 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0487 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨31168 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨31168 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0487
    (state : Fin 48684)
    (lower : 31168 ≤ state.val)
    (upper : state.val < 31232) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 31168, by omega⟩
  have state_eq :
      (⟨31168 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0487 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0488 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨31232 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨31232 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0488
    (state : Fin 48684)
    (lower : 31232 ≤ state.val)
    (upper : state.val < 31296) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 31232, by omega⟩
  have state_eq :
      (⟨31232 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0488 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0489 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨31296 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨31296 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0489
    (state : Fin 48684)
    (lower : 31296 ≤ state.val)
    (upper : state.val < 31360) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 31296, by omega⟩
  have state_eq :
      (⟨31296 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0489 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0490 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨31360 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨31360 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0490
    (state : Fin 48684)
    (lower : 31360 ≤ state.val)
    (upper : state.val < 31424) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 31360, by omega⟩
  have state_eq :
      (⟨31360 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0490 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0491 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨31424 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨31424 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0491
    (state : Fin 48684)
    (lower : 31424 ≤ state.val)
    (upper : state.val < 31488) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 31424, by omega⟩
  have state_eq :
      (⟨31424 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0491 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0492 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨31488 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨31488 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0492
    (state : Fin 48684)
    (lower : 31488 ≤ state.val)
    (upper : state.val < 31552) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 31488, by omega⟩
  have state_eq :
      (⟨31488 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0492 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0493 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨31552 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨31552 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0493
    (state : Fin 48684)
    (lower : 31552 ≤ state.val)
    (upper : state.val < 31616) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 31552, by omega⟩
  have state_eq :
      (⟨31552 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0493 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0494 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨31616 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨31616 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0494
    (state : Fin 48684)
    (lower : 31616 ≤ state.val)
    (upper : state.val < 31680) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 31616, by omega⟩
  have state_eq :
      (⟨31616 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0494 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0495 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨31680 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨31680 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0495
    (state : Fin 48684)
    (lower : 31680 ≤ state.val)
    (upper : state.val < 31744) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 31680, by omega⟩
  have state_eq :
      (⟨31680 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0495 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0496 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨31744 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨31744 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0496
    (state : Fin 48684)
    (lower : 31744 ≤ state.val)
    (upper : state.val < 31808) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 31744, by omega⟩
  have state_eq :
      (⟨31744 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0496 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0497 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨31808 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨31808 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0497
    (state : Fin 48684)
    (lower : 31808 ≤ state.val)
    (upper : state.val < 31872) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 31808, by omega⟩
  have state_eq :
      (⟨31808 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0497 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0498 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨31872 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨31872 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0498
    (state : Fin 48684)
    (lower : 31872 ≤ state.val)
    (upper : state.val < 31936) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 31872, by omega⟩
  have state_eq :
      (⟨31872 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0498 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0499 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨31936 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨31936 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0499
    (state : Fin 48684)
    (lower : 31936 ≤ state.val)
    (upper : state.val < 32000) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 31936, by omega⟩
  have state_eq :
      (⟨31936 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0499 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0500 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨32000 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨32000 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0500
    (state : Fin 48684)
    (lower : 32000 ≤ state.val)
    (upper : state.val < 32064) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 32000, by omega⟩
  have state_eq :
      (⟨32000 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0500 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0501 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨32064 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨32064 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0501
    (state : Fin 48684)
    (lower : 32064 ≤ state.val)
    (upper : state.val < 32128) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 32064, by omega⟩
  have state_eq :
      (⟨32064 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0501 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0502 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨32128 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨32128 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0502
    (state : Fin 48684)
    (lower : 32128 ≤ state.val)
    (upper : state.val < 32192) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 32128, by omega⟩
  have state_eq :
      (⟨32128 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0502 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0503 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨32192 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨32192 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0503
    (state : Fin 48684)
    (lower : 32192 ≤ state.val)
    (upper : state.val < 32256) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 32192, by omega⟩
  have state_eq :
      (⟨32192 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0503 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0504 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨32256 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨32256 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0504
    (state : Fin 48684)
    (lower : 32256 ≤ state.val)
    (upper : state.val < 32320) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 32256, by omega⟩
  have state_eq :
      (⟨32256 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0504 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0505 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨32320 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨32320 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0505
    (state : Fin 48684)
    (lower : 32320 ≤ state.val)
    (upper : state.val < 32384) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 32320, by omega⟩
  have state_eq :
      (⟨32320 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0505 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0506 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨32384 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨32384 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0506
    (state : Fin 48684)
    (lower : 32384 ≤ state.val)
    (upper : state.val < 32448) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 32384, by omega⟩
  have state_eq :
      (⟨32384 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0506 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0507 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨32448 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨32448 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0507
    (state : Fin 48684)
    (lower : 32448 ≤ state.val)
    (upper : state.val < 32512) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 32448, by omega⟩
  have state_eq :
      (⟨32448 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0507 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0508 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨32512 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨32512 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0508
    (state : Fin 48684)
    (lower : 32512 ≤ state.val)
    (upper : state.val < 32576) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 32512, by omega⟩
  have state_eq :
      (⟨32512 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0508 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0509 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨32576 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨32576 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0509
    (state : Fin 48684)
    (lower : 32576 ≤ state.val)
    (upper : state.val < 32640) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 32576, by omega⟩
  have state_eq :
      (⟨32576 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0509 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0510 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨32640 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨32640 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0510
    (state : Fin 48684)
    (lower : 32640 ≤ state.val)
    (upper : state.val < 32704) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 32640, by omega⟩
  have state_eq :
      (⟨32640 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0510 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0511 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨32704 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨32704 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0511
    (state : Fin 48684)
    (lower : 32704 ≤ state.val)
    (upper : state.val < 32768) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 32704, by omega⟩
  have state_eq :
      (⟨32704 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0511 offset

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards
