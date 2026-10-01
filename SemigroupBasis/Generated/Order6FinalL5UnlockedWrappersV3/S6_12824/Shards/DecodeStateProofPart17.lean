import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards.DecodeState
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards.StateVector
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0544 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨34816 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨34816 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0544
    (state : Fin 48684)
    (lower : 34816 ≤ state.val)
    (upper : state.val < 34880) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 34816, by omega⟩
  have state_eq :
      (⟨34816 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0544 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0545 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨34880 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨34880 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0545
    (state : Fin 48684)
    (lower : 34880 ≤ state.val)
    (upper : state.val < 34944) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 34880, by omega⟩
  have state_eq :
      (⟨34880 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0545 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0546 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨34944 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨34944 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0546
    (state : Fin 48684)
    (lower : 34944 ≤ state.val)
    (upper : state.val < 35008) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 34944, by omega⟩
  have state_eq :
      (⟨34944 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0546 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0547 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨35008 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨35008 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0547
    (state : Fin 48684)
    (lower : 35008 ≤ state.val)
    (upper : state.val < 35072) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 35008, by omega⟩
  have state_eq :
      (⟨35008 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0547 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0548 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨35072 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨35072 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0548
    (state : Fin 48684)
    (lower : 35072 ≤ state.val)
    (upper : state.val < 35136) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 35072, by omega⟩
  have state_eq :
      (⟨35072 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0548 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0549 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨35136 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨35136 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0549
    (state : Fin 48684)
    (lower : 35136 ≤ state.val)
    (upper : state.val < 35200) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 35136, by omega⟩
  have state_eq :
      (⟨35136 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0549 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0550 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨35200 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨35200 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0550
    (state : Fin 48684)
    (lower : 35200 ≤ state.val)
    (upper : state.val < 35264) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 35200, by omega⟩
  have state_eq :
      (⟨35200 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0550 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0551 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨35264 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨35264 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0551
    (state : Fin 48684)
    (lower : 35264 ≤ state.val)
    (upper : state.val < 35328) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 35264, by omega⟩
  have state_eq :
      (⟨35264 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0551 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0552 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨35328 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨35328 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0552
    (state : Fin 48684)
    (lower : 35328 ≤ state.val)
    (upper : state.val < 35392) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 35328, by omega⟩
  have state_eq :
      (⟨35328 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0552 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0553 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨35392 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨35392 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0553
    (state : Fin 48684)
    (lower : 35392 ≤ state.val)
    (upper : state.val < 35456) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 35392, by omega⟩
  have state_eq :
      (⟨35392 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0553 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0554 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨35456 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨35456 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0554
    (state : Fin 48684)
    (lower : 35456 ≤ state.val)
    (upper : state.val < 35520) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 35456, by omega⟩
  have state_eq :
      (⟨35456 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0554 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0555 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨35520 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨35520 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0555
    (state : Fin 48684)
    (lower : 35520 ≤ state.val)
    (upper : state.val < 35584) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 35520, by omega⟩
  have state_eq :
      (⟨35520 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0555 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0556 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨35584 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨35584 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0556
    (state : Fin 48684)
    (lower : 35584 ≤ state.val)
    (upper : state.val < 35648) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 35584, by omega⟩
  have state_eq :
      (⟨35584 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0556 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0557 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨35648 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨35648 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0557
    (state : Fin 48684)
    (lower : 35648 ≤ state.val)
    (upper : state.val < 35712) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 35648, by omega⟩
  have state_eq :
      (⟨35648 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0557 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0558 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨35712 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨35712 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0558
    (state : Fin 48684)
    (lower : 35712 ≤ state.val)
    (upper : state.val < 35776) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 35712, by omega⟩
  have state_eq :
      (⟨35712 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0558 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0559 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨35776 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨35776 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0559
    (state : Fin 48684)
    (lower : 35776 ≤ state.val)
    (upper : state.val < 35840) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 35776, by omega⟩
  have state_eq :
      (⟨35776 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0559 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0560 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨35840 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨35840 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0560
    (state : Fin 48684)
    (lower : 35840 ≤ state.val)
    (upper : state.val < 35904) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 35840, by omega⟩
  have state_eq :
      (⟨35840 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0560 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0561 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨35904 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨35904 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0561
    (state : Fin 48684)
    (lower : 35904 ≤ state.val)
    (upper : state.val < 35968) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 35904, by omega⟩
  have state_eq :
      (⟨35904 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0561 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0562 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨35968 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨35968 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0562
    (state : Fin 48684)
    (lower : 35968 ≤ state.val)
    (upper : state.val < 36032) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 35968, by omega⟩
  have state_eq :
      (⟨35968 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0562 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0563 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨36032 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨36032 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0563
    (state : Fin 48684)
    (lower : 36032 ≤ state.val)
    (upper : state.val < 36096) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 36032, by omega⟩
  have state_eq :
      (⟨36032 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0563 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0564 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨36096 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨36096 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0564
    (state : Fin 48684)
    (lower : 36096 ≤ state.val)
    (upper : state.val < 36160) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 36096, by omega⟩
  have state_eq :
      (⟨36096 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0564 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0565 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨36160 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨36160 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0565
    (state : Fin 48684)
    (lower : 36160 ≤ state.val)
    (upper : state.val < 36224) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 36160, by omega⟩
  have state_eq :
      (⟨36160 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0565 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0566 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨36224 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨36224 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0566
    (state : Fin 48684)
    (lower : 36224 ≤ state.val)
    (upper : state.val < 36288) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 36224, by omega⟩
  have state_eq :
      (⟨36224 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0566 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0567 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨36288 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨36288 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0567
    (state : Fin 48684)
    (lower : 36288 ≤ state.val)
    (upper : state.val < 36352) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 36288, by omega⟩
  have state_eq :
      (⟨36288 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0567 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0568 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨36352 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨36352 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0568
    (state : Fin 48684)
    (lower : 36352 ≤ state.val)
    (upper : state.val < 36416) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 36352, by omega⟩
  have state_eq :
      (⟨36352 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0568 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0569 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨36416 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨36416 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0569
    (state : Fin 48684)
    (lower : 36416 ≤ state.val)
    (upper : state.val < 36480) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 36416, by omega⟩
  have state_eq :
      (⟨36416 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0569 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0570 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨36480 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨36480 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0570
    (state : Fin 48684)
    (lower : 36480 ≤ state.val)
    (upper : state.val < 36544) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 36480, by omega⟩
  have state_eq :
      (⟨36480 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0570 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0571 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨36544 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨36544 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0571
    (state : Fin 48684)
    (lower : 36544 ≤ state.val)
    (upper : state.val < 36608) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 36544, by omega⟩
  have state_eq :
      (⟨36544 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0571 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0572 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨36608 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨36608 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0572
    (state : Fin 48684)
    (lower : 36608 ≤ state.val)
    (upper : state.val < 36672) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 36608, by omega⟩
  have state_eq :
      (⟨36608 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0572 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0573 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨36672 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨36672 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0573
    (state : Fin 48684)
    (lower : 36672 ≤ state.val)
    (upper : state.val < 36736) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 36672, by omega⟩
  have state_eq :
      (⟨36672 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0573 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0574 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨36736 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨36736 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0574
    (state : Fin 48684)
    (lower : 36736 ≤ state.val)
    (upper : state.val < 36800) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 36736, by omega⟩
  have state_eq :
      (⟨36736 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0574 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0575 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨36800 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨36800 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0575
    (state : Fin 48684)
    (lower : 36800 ≤ state.val)
    (upper : state.val < 36864) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 36800, by omega⟩
  have state_eq :
      (⟨36800 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0575 offset

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards
