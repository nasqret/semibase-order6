import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards.DecodeState
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards.StateVector
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0672 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨43008 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨43008 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0672
    (state : Fin 48684)
    (lower : 43008 ≤ state.val)
    (upper : state.val < 43072) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 43008, by omega⟩
  have state_eq :
      (⟨43008 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0672 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0673 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨43072 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨43072 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0673
    (state : Fin 48684)
    (lower : 43072 ≤ state.val)
    (upper : state.val < 43136) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 43072, by omega⟩
  have state_eq :
      (⟨43072 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0673 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0674 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨43136 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨43136 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0674
    (state : Fin 48684)
    (lower : 43136 ≤ state.val)
    (upper : state.val < 43200) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 43136, by omega⟩
  have state_eq :
      (⟨43136 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0674 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0675 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨43200 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨43200 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0675
    (state : Fin 48684)
    (lower : 43200 ≤ state.val)
    (upper : state.val < 43264) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 43200, by omega⟩
  have state_eq :
      (⟨43200 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0675 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0676 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨43264 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨43264 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0676
    (state : Fin 48684)
    (lower : 43264 ≤ state.val)
    (upper : state.val < 43328) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 43264, by omega⟩
  have state_eq :
      (⟨43264 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0676 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0677 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨43328 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨43328 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0677
    (state : Fin 48684)
    (lower : 43328 ≤ state.val)
    (upper : state.val < 43392) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 43328, by omega⟩
  have state_eq :
      (⟨43328 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0677 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0678 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨43392 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨43392 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0678
    (state : Fin 48684)
    (lower : 43392 ≤ state.val)
    (upper : state.val < 43456) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 43392, by omega⟩
  have state_eq :
      (⟨43392 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0678 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0679 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨43456 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨43456 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0679
    (state : Fin 48684)
    (lower : 43456 ≤ state.val)
    (upper : state.val < 43520) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 43456, by omega⟩
  have state_eq :
      (⟨43456 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0679 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0680 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨43520 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨43520 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0680
    (state : Fin 48684)
    (lower : 43520 ≤ state.val)
    (upper : state.val < 43584) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 43520, by omega⟩
  have state_eq :
      (⟨43520 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0680 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0681 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨43584 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨43584 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0681
    (state : Fin 48684)
    (lower : 43584 ≤ state.val)
    (upper : state.val < 43648) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 43584, by omega⟩
  have state_eq :
      (⟨43584 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0681 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0682 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨43648 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨43648 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0682
    (state : Fin 48684)
    (lower : 43648 ≤ state.val)
    (upper : state.val < 43712) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 43648, by omega⟩
  have state_eq :
      (⟨43648 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0682 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0683 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨43712 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨43712 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0683
    (state : Fin 48684)
    (lower : 43712 ≤ state.val)
    (upper : state.val < 43776) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 43712, by omega⟩
  have state_eq :
      (⟨43712 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0683 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0684 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨43776 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨43776 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0684
    (state : Fin 48684)
    (lower : 43776 ≤ state.val)
    (upper : state.val < 43840) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 43776, by omega⟩
  have state_eq :
      (⟨43776 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0684 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0685 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨43840 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨43840 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0685
    (state : Fin 48684)
    (lower : 43840 ≤ state.val)
    (upper : state.val < 43904) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 43840, by omega⟩
  have state_eq :
      (⟨43840 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0685 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0686 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨43904 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨43904 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0686
    (state : Fin 48684)
    (lower : 43904 ≤ state.val)
    (upper : state.val < 43968) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 43904, by omega⟩
  have state_eq :
      (⟨43904 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0686 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0687 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨43968 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨43968 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0687
    (state : Fin 48684)
    (lower : 43968 ≤ state.val)
    (upper : state.val < 44032) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 43968, by omega⟩
  have state_eq :
      (⟨43968 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0687 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0688 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨44032 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨44032 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0688
    (state : Fin 48684)
    (lower : 44032 ≤ state.val)
    (upper : state.val < 44096) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 44032, by omega⟩
  have state_eq :
      (⟨44032 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0688 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0689 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨44096 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨44096 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0689
    (state : Fin 48684)
    (lower : 44096 ≤ state.val)
    (upper : state.val < 44160) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 44096, by omega⟩
  have state_eq :
      (⟨44096 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0689 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0690 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨44160 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨44160 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0690
    (state : Fin 48684)
    (lower : 44160 ≤ state.val)
    (upper : state.val < 44224) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 44160, by omega⟩
  have state_eq :
      (⟨44160 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0690 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0691 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨44224 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨44224 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0691
    (state : Fin 48684)
    (lower : 44224 ≤ state.val)
    (upper : state.val < 44288) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 44224, by omega⟩
  have state_eq :
      (⟨44224 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0691 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0692 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨44288 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨44288 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0692
    (state : Fin 48684)
    (lower : 44288 ≤ state.val)
    (upper : state.val < 44352) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 44288, by omega⟩
  have state_eq :
      (⟨44288 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0692 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0693 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨44352 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨44352 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0693
    (state : Fin 48684)
    (lower : 44352 ≤ state.val)
    (upper : state.val < 44416) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 44352, by omega⟩
  have state_eq :
      (⟨44352 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0693 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0694 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨44416 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨44416 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0694
    (state : Fin 48684)
    (lower : 44416 ≤ state.val)
    (upper : state.val < 44480) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 44416, by omega⟩
  have state_eq :
      (⟨44416 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0694 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0695 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨44480 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨44480 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0695
    (state : Fin 48684)
    (lower : 44480 ≤ state.val)
    (upper : state.val < 44544) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 44480, by omega⟩
  have state_eq :
      (⟨44480 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0695 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0696 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨44544 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨44544 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0696
    (state : Fin 48684)
    (lower : 44544 ≤ state.val)
    (upper : state.val < 44608) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 44544, by omega⟩
  have state_eq :
      (⟨44544 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0696 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0697 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨44608 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨44608 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0697
    (state : Fin 48684)
    (lower : 44608 ≤ state.val)
    (upper : state.val < 44672) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 44608, by omega⟩
  have state_eq :
      (⟨44608 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0697 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0698 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨44672 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨44672 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0698
    (state : Fin 48684)
    (lower : 44672 ≤ state.val)
    (upper : state.val < 44736) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 44672, by omega⟩
  have state_eq :
      (⟨44672 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0698 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0699 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨44736 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨44736 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0699
    (state : Fin 48684)
    (lower : 44736 ≤ state.val)
    (upper : state.val < 44800) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 44736, by omega⟩
  have state_eq :
      (⟨44736 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0699 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0700 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨44800 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨44800 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0700
    (state : Fin 48684)
    (lower : 44800 ≤ state.val)
    (upper : state.val < 44864) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 44800, by omega⟩
  have state_eq :
      (⟨44800 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0700 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0701 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨44864 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨44864 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0701
    (state : Fin 48684)
    (lower : 44864 ≤ state.val)
    (upper : state.val < 44928) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 44864, by omega⟩
  have state_eq :
      (⟨44864 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0701 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0702 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨44928 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨44928 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0702
    (state : Fin 48684)
    (lower : 44928 ≤ state.val)
    (upper : state.val < 44992) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 44928, by omega⟩
  have state_eq :
      (⟨44928 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0702 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0703 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨44992 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨44992 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0703
    (state : Fin 48684)
    (lower : 44992 ≤ state.val)
    (upper : state.val < 45056) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 44992, by omega⟩
  have state_eq :
      (⟨44992 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0703 offset

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards
