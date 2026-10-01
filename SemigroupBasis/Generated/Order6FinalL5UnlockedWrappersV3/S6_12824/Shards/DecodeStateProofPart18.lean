import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards.DecodeState
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards.StateVector
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0576 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨36864 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨36864 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0576
    (state : Fin 48684)
    (lower : 36864 ≤ state.val)
    (upper : state.val < 36928) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 36864, by omega⟩
  have state_eq :
      (⟨36864 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0576 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0577 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨36928 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨36928 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0577
    (state : Fin 48684)
    (lower : 36928 ≤ state.val)
    (upper : state.val < 36992) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 36928, by omega⟩
  have state_eq :
      (⟨36928 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0577 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0578 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨36992 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨36992 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0578
    (state : Fin 48684)
    (lower : 36992 ≤ state.val)
    (upper : state.val < 37056) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 36992, by omega⟩
  have state_eq :
      (⟨36992 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0578 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0579 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨37056 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨37056 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0579
    (state : Fin 48684)
    (lower : 37056 ≤ state.val)
    (upper : state.val < 37120) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 37056, by omega⟩
  have state_eq :
      (⟨37056 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0579 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0580 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨37120 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨37120 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0580
    (state : Fin 48684)
    (lower : 37120 ≤ state.val)
    (upper : state.val < 37184) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 37120, by omega⟩
  have state_eq :
      (⟨37120 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0580 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0581 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨37184 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨37184 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0581
    (state : Fin 48684)
    (lower : 37184 ≤ state.val)
    (upper : state.val < 37248) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 37184, by omega⟩
  have state_eq :
      (⟨37184 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0581 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0582 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨37248 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨37248 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0582
    (state : Fin 48684)
    (lower : 37248 ≤ state.val)
    (upper : state.val < 37312) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 37248, by omega⟩
  have state_eq :
      (⟨37248 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0582 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0583 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨37312 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨37312 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0583
    (state : Fin 48684)
    (lower : 37312 ≤ state.val)
    (upper : state.val < 37376) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 37312, by omega⟩
  have state_eq :
      (⟨37312 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0583 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0584 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨37376 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨37376 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0584
    (state : Fin 48684)
    (lower : 37376 ≤ state.val)
    (upper : state.val < 37440) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 37376, by omega⟩
  have state_eq :
      (⟨37376 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0584 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0585 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨37440 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨37440 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0585
    (state : Fin 48684)
    (lower : 37440 ≤ state.val)
    (upper : state.val < 37504) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 37440, by omega⟩
  have state_eq :
      (⟨37440 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0585 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0586 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨37504 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨37504 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0586
    (state : Fin 48684)
    (lower : 37504 ≤ state.val)
    (upper : state.val < 37568) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 37504, by omega⟩
  have state_eq :
      (⟨37504 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0586 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0587 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨37568 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨37568 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0587
    (state : Fin 48684)
    (lower : 37568 ≤ state.val)
    (upper : state.val < 37632) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 37568, by omega⟩
  have state_eq :
      (⟨37568 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0587 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0588 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨37632 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨37632 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0588
    (state : Fin 48684)
    (lower : 37632 ≤ state.val)
    (upper : state.val < 37696) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 37632, by omega⟩
  have state_eq :
      (⟨37632 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0588 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0589 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨37696 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨37696 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0589
    (state : Fin 48684)
    (lower : 37696 ≤ state.val)
    (upper : state.val < 37760) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 37696, by omega⟩
  have state_eq :
      (⟨37696 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0589 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0590 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨37760 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨37760 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0590
    (state : Fin 48684)
    (lower : 37760 ≤ state.val)
    (upper : state.val < 37824) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 37760, by omega⟩
  have state_eq :
      (⟨37760 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0590 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0591 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨37824 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨37824 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0591
    (state : Fin 48684)
    (lower : 37824 ≤ state.val)
    (upper : state.val < 37888) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 37824, by omega⟩
  have state_eq :
      (⟨37824 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0591 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0592 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨37888 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨37888 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0592
    (state : Fin 48684)
    (lower : 37888 ≤ state.val)
    (upper : state.val < 37952) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 37888, by omega⟩
  have state_eq :
      (⟨37888 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0592 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0593 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨37952 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨37952 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0593
    (state : Fin 48684)
    (lower : 37952 ≤ state.val)
    (upper : state.val < 38016) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 37952, by omega⟩
  have state_eq :
      (⟨37952 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0593 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0594 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨38016 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨38016 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0594
    (state : Fin 48684)
    (lower : 38016 ≤ state.val)
    (upper : state.val < 38080) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 38016, by omega⟩
  have state_eq :
      (⟨38016 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0594 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0595 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨38080 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨38080 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0595
    (state : Fin 48684)
    (lower : 38080 ≤ state.val)
    (upper : state.val < 38144) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 38080, by omega⟩
  have state_eq :
      (⟨38080 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0595 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0596 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨38144 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨38144 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0596
    (state : Fin 48684)
    (lower : 38144 ≤ state.val)
    (upper : state.val < 38208) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 38144, by omega⟩
  have state_eq :
      (⟨38144 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0596 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0597 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨38208 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨38208 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0597
    (state : Fin 48684)
    (lower : 38208 ≤ state.val)
    (upper : state.val < 38272) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 38208, by omega⟩
  have state_eq :
      (⟨38208 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0597 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0598 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨38272 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨38272 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0598
    (state : Fin 48684)
    (lower : 38272 ≤ state.val)
    (upper : state.val < 38336) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 38272, by omega⟩
  have state_eq :
      (⟨38272 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0598 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0599 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨38336 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨38336 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0599
    (state : Fin 48684)
    (lower : 38336 ≤ state.val)
    (upper : state.val < 38400) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 38336, by omega⟩
  have state_eq :
      (⟨38336 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0599 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0600 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨38400 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨38400 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0600
    (state : Fin 48684)
    (lower : 38400 ≤ state.val)
    (upper : state.val < 38464) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 38400, by omega⟩
  have state_eq :
      (⟨38400 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0600 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0601 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨38464 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨38464 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0601
    (state : Fin 48684)
    (lower : 38464 ≤ state.val)
    (upper : state.val < 38528) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 38464, by omega⟩
  have state_eq :
      (⟨38464 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0601 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0602 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨38528 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨38528 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0602
    (state : Fin 48684)
    (lower : 38528 ≤ state.val)
    (upper : state.val < 38592) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 38528, by omega⟩
  have state_eq :
      (⟨38528 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0602 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0603 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨38592 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨38592 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0603
    (state : Fin 48684)
    (lower : 38592 ≤ state.val)
    (upper : state.val < 38656) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 38592, by omega⟩
  have state_eq :
      (⟨38592 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0603 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0604 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨38656 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨38656 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0604
    (state : Fin 48684)
    (lower : 38656 ≤ state.val)
    (upper : state.val < 38720) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 38656, by omega⟩
  have state_eq :
      (⟨38656 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0604 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0605 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨38720 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨38720 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0605
    (state : Fin 48684)
    (lower : 38720 ≤ state.val)
    (upper : state.val < 38784) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 38720, by omega⟩
  have state_eq :
      (⟨38720 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0605 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0606 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨38784 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨38784 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0606
    (state : Fin 48684)
    (lower : 38784 ≤ state.val)
    (upper : state.val < 38848) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 38784, by omega⟩
  have state_eq :
      (⟨38784 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0606 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0607 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨38848 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨38848 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0607
    (state : Fin 48684)
    (lower : 38848 ≤ state.val)
    (upper : state.val < 38912) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 38848, by omega⟩
  have state_eq :
      (⟨38848 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0607 offset

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards
