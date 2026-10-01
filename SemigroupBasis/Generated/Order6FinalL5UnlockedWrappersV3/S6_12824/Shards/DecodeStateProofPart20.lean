import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards.DecodeState
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards.StateVector
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0640 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨40960 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨40960 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0640
    (state : Fin 48684)
    (lower : 40960 ≤ state.val)
    (upper : state.val < 41024) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 40960, by omega⟩
  have state_eq :
      (⟨40960 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0640 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0641 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨41024 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨41024 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0641
    (state : Fin 48684)
    (lower : 41024 ≤ state.val)
    (upper : state.val < 41088) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 41024, by omega⟩
  have state_eq :
      (⟨41024 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0641 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0642 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨41088 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨41088 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0642
    (state : Fin 48684)
    (lower : 41088 ≤ state.val)
    (upper : state.val < 41152) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 41088, by omega⟩
  have state_eq :
      (⟨41088 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0642 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0643 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨41152 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨41152 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0643
    (state : Fin 48684)
    (lower : 41152 ≤ state.val)
    (upper : state.val < 41216) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 41152, by omega⟩
  have state_eq :
      (⟨41152 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0643 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0644 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨41216 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨41216 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0644
    (state : Fin 48684)
    (lower : 41216 ≤ state.val)
    (upper : state.val < 41280) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 41216, by omega⟩
  have state_eq :
      (⟨41216 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0644 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0645 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨41280 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨41280 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0645
    (state : Fin 48684)
    (lower : 41280 ≤ state.val)
    (upper : state.val < 41344) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 41280, by omega⟩
  have state_eq :
      (⟨41280 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0645 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0646 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨41344 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨41344 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0646
    (state : Fin 48684)
    (lower : 41344 ≤ state.val)
    (upper : state.val < 41408) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 41344, by omega⟩
  have state_eq :
      (⟨41344 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0646 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0647 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨41408 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨41408 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0647
    (state : Fin 48684)
    (lower : 41408 ≤ state.val)
    (upper : state.val < 41472) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 41408, by omega⟩
  have state_eq :
      (⟨41408 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0647 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0648 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨41472 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨41472 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0648
    (state : Fin 48684)
    (lower : 41472 ≤ state.val)
    (upper : state.val < 41536) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 41472, by omega⟩
  have state_eq :
      (⟨41472 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0648 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0649 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨41536 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨41536 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0649
    (state : Fin 48684)
    (lower : 41536 ≤ state.val)
    (upper : state.val < 41600) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 41536, by omega⟩
  have state_eq :
      (⟨41536 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0649 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0650 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨41600 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨41600 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0650
    (state : Fin 48684)
    (lower : 41600 ≤ state.val)
    (upper : state.val < 41664) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 41600, by omega⟩
  have state_eq :
      (⟨41600 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0650 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0651 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨41664 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨41664 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0651
    (state : Fin 48684)
    (lower : 41664 ≤ state.val)
    (upper : state.val < 41728) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 41664, by omega⟩
  have state_eq :
      (⟨41664 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0651 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0652 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨41728 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨41728 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0652
    (state : Fin 48684)
    (lower : 41728 ≤ state.val)
    (upper : state.val < 41792) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 41728, by omega⟩
  have state_eq :
      (⟨41728 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0652 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0653 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨41792 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨41792 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0653
    (state : Fin 48684)
    (lower : 41792 ≤ state.val)
    (upper : state.val < 41856) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 41792, by omega⟩
  have state_eq :
      (⟨41792 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0653 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0654 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨41856 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨41856 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0654
    (state : Fin 48684)
    (lower : 41856 ≤ state.val)
    (upper : state.val < 41920) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 41856, by omega⟩
  have state_eq :
      (⟨41856 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0654 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0655 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨41920 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨41920 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0655
    (state : Fin 48684)
    (lower : 41920 ≤ state.val)
    (upper : state.val < 41984) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 41920, by omega⟩
  have state_eq :
      (⟨41920 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0655 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0656 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨41984 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨41984 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0656
    (state : Fin 48684)
    (lower : 41984 ≤ state.val)
    (upper : state.val < 42048) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 41984, by omega⟩
  have state_eq :
      (⟨41984 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0656 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0657 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨42048 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨42048 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0657
    (state : Fin 48684)
    (lower : 42048 ≤ state.val)
    (upper : state.val < 42112) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 42048, by omega⟩
  have state_eq :
      (⟨42048 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0657 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0658 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨42112 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨42112 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0658
    (state : Fin 48684)
    (lower : 42112 ≤ state.val)
    (upper : state.val < 42176) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 42112, by omega⟩
  have state_eq :
      (⟨42112 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0658 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0659 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨42176 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨42176 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0659
    (state : Fin 48684)
    (lower : 42176 ≤ state.val)
    (upper : state.val < 42240) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 42176, by omega⟩
  have state_eq :
      (⟨42176 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0659 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0660 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨42240 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨42240 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0660
    (state : Fin 48684)
    (lower : 42240 ≤ state.val)
    (upper : state.val < 42304) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 42240, by omega⟩
  have state_eq :
      (⟨42240 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0660 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0661 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨42304 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨42304 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0661
    (state : Fin 48684)
    (lower : 42304 ≤ state.val)
    (upper : state.val < 42368) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 42304, by omega⟩
  have state_eq :
      (⟨42304 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0661 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0662 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨42368 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨42368 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0662
    (state : Fin 48684)
    (lower : 42368 ≤ state.val)
    (upper : state.val < 42432) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 42368, by omega⟩
  have state_eq :
      (⟨42368 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0662 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0663 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨42432 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨42432 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0663
    (state : Fin 48684)
    (lower : 42432 ≤ state.val)
    (upper : state.val < 42496) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 42432, by omega⟩
  have state_eq :
      (⟨42432 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0663 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0664 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨42496 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨42496 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0664
    (state : Fin 48684)
    (lower : 42496 ≤ state.val)
    (upper : state.val < 42560) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 42496, by omega⟩
  have state_eq :
      (⟨42496 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0664 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0665 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨42560 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨42560 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0665
    (state : Fin 48684)
    (lower : 42560 ≤ state.val)
    (upper : state.val < 42624) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 42560, by omega⟩
  have state_eq :
      (⟨42560 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0665 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0666 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨42624 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨42624 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0666
    (state : Fin 48684)
    (lower : 42624 ≤ state.val)
    (upper : state.val < 42688) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 42624, by omega⟩
  have state_eq :
      (⟨42624 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0666 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0667 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨42688 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨42688 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0667
    (state : Fin 48684)
    (lower : 42688 ≤ state.val)
    (upper : state.val < 42752) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 42688, by omega⟩
  have state_eq :
      (⟨42688 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0667 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0668 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨42752 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨42752 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0668
    (state : Fin 48684)
    (lower : 42752 ≤ state.val)
    (upper : state.val < 42816) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 42752, by omega⟩
  have state_eq :
      (⟨42752 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0668 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0669 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨42816 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨42816 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0669
    (state : Fin 48684)
    (lower : 42816 ≤ state.val)
    (upper : state.val < 42880) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 42816, by omega⟩
  have state_eq :
      (⟨42816 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0669 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0670 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨42880 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨42880 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0670
    (state : Fin 48684)
    (lower : 42880 ≤ state.val)
    (upper : state.val < 42944) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 42880, by omega⟩
  have state_eq :
      (⟨42880 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0670 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0671 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨42944 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨42944 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0671
    (state : Fin 48684)
    (lower : 42944 ≤ state.val)
    (upper : state.val < 43008) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 42944, by omega⟩
  have state_eq :
      (⟨42944 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0671 offset

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards
