import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards.DecodeState
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards.StateVector
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0608 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨38912 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨38912 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0608
    (state : Fin 48684)
    (lower : 38912 ≤ state.val)
    (upper : state.val < 38976) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 38912, by omega⟩
  have state_eq :
      (⟨38912 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0608 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0609 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨38976 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨38976 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0609
    (state : Fin 48684)
    (lower : 38976 ≤ state.val)
    (upper : state.val < 39040) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 38976, by omega⟩
  have state_eq :
      (⟨38976 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0609 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0610 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨39040 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨39040 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0610
    (state : Fin 48684)
    (lower : 39040 ≤ state.val)
    (upper : state.val < 39104) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 39040, by omega⟩
  have state_eq :
      (⟨39040 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0610 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0611 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨39104 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨39104 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0611
    (state : Fin 48684)
    (lower : 39104 ≤ state.val)
    (upper : state.val < 39168) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 39104, by omega⟩
  have state_eq :
      (⟨39104 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0611 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0612 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨39168 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨39168 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0612
    (state : Fin 48684)
    (lower : 39168 ≤ state.val)
    (upper : state.val < 39232) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 39168, by omega⟩
  have state_eq :
      (⟨39168 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0612 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0613 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨39232 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨39232 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0613
    (state : Fin 48684)
    (lower : 39232 ≤ state.val)
    (upper : state.val < 39296) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 39232, by omega⟩
  have state_eq :
      (⟨39232 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0613 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0614 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨39296 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨39296 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0614
    (state : Fin 48684)
    (lower : 39296 ≤ state.val)
    (upper : state.val < 39360) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 39296, by omega⟩
  have state_eq :
      (⟨39296 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0614 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0615 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨39360 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨39360 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0615
    (state : Fin 48684)
    (lower : 39360 ≤ state.val)
    (upper : state.val < 39424) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 39360, by omega⟩
  have state_eq :
      (⟨39360 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0615 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0616 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨39424 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨39424 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0616
    (state : Fin 48684)
    (lower : 39424 ≤ state.val)
    (upper : state.val < 39488) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 39424, by omega⟩
  have state_eq :
      (⟨39424 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0616 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0617 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨39488 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨39488 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0617
    (state : Fin 48684)
    (lower : 39488 ≤ state.val)
    (upper : state.val < 39552) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 39488, by omega⟩
  have state_eq :
      (⟨39488 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0617 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0618 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨39552 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨39552 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0618
    (state : Fin 48684)
    (lower : 39552 ≤ state.val)
    (upper : state.val < 39616) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 39552, by omega⟩
  have state_eq :
      (⟨39552 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0618 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0619 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨39616 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨39616 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0619
    (state : Fin 48684)
    (lower : 39616 ≤ state.val)
    (upper : state.val < 39680) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 39616, by omega⟩
  have state_eq :
      (⟨39616 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0619 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0620 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨39680 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨39680 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0620
    (state : Fin 48684)
    (lower : 39680 ≤ state.val)
    (upper : state.val < 39744) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 39680, by omega⟩
  have state_eq :
      (⟨39680 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0620 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0621 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨39744 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨39744 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0621
    (state : Fin 48684)
    (lower : 39744 ≤ state.val)
    (upper : state.val < 39808) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 39744, by omega⟩
  have state_eq :
      (⟨39744 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0621 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0622 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨39808 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨39808 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0622
    (state : Fin 48684)
    (lower : 39808 ≤ state.val)
    (upper : state.val < 39872) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 39808, by omega⟩
  have state_eq :
      (⟨39808 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0622 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0623 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨39872 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨39872 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0623
    (state : Fin 48684)
    (lower : 39872 ≤ state.val)
    (upper : state.val < 39936) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 39872, by omega⟩
  have state_eq :
      (⟨39872 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0623 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0624 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨39936 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨39936 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0624
    (state : Fin 48684)
    (lower : 39936 ≤ state.val)
    (upper : state.val < 40000) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 39936, by omega⟩
  have state_eq :
      (⟨39936 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0624 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0625 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨40000 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨40000 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0625
    (state : Fin 48684)
    (lower : 40000 ≤ state.val)
    (upper : state.val < 40064) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 40000, by omega⟩
  have state_eq :
      (⟨40000 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0625 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0626 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨40064 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨40064 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0626
    (state : Fin 48684)
    (lower : 40064 ≤ state.val)
    (upper : state.val < 40128) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 40064, by omega⟩
  have state_eq :
      (⟨40064 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0626 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0627 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨40128 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨40128 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0627
    (state : Fin 48684)
    (lower : 40128 ≤ state.val)
    (upper : state.val < 40192) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 40128, by omega⟩
  have state_eq :
      (⟨40128 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0627 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0628 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨40192 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨40192 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0628
    (state : Fin 48684)
    (lower : 40192 ≤ state.val)
    (upper : state.val < 40256) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 40192, by omega⟩
  have state_eq :
      (⟨40192 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0628 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0629 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨40256 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨40256 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0629
    (state : Fin 48684)
    (lower : 40256 ≤ state.val)
    (upper : state.val < 40320) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 40256, by omega⟩
  have state_eq :
      (⟨40256 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0629 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0630 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨40320 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨40320 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0630
    (state : Fin 48684)
    (lower : 40320 ≤ state.val)
    (upper : state.val < 40384) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 40320, by omega⟩
  have state_eq :
      (⟨40320 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0630 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0631 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨40384 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨40384 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0631
    (state : Fin 48684)
    (lower : 40384 ≤ state.val)
    (upper : state.val < 40448) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 40384, by omega⟩
  have state_eq :
      (⟨40384 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0631 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0632 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨40448 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨40448 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0632
    (state : Fin 48684)
    (lower : 40448 ≤ state.val)
    (upper : state.val < 40512) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 40448, by omega⟩
  have state_eq :
      (⟨40448 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0632 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0633 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨40512 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨40512 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0633
    (state : Fin 48684)
    (lower : 40512 ≤ state.val)
    (upper : state.val < 40576) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 40512, by omega⟩
  have state_eq :
      (⟨40512 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0633 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0634 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨40576 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨40576 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0634
    (state : Fin 48684)
    (lower : 40576 ≤ state.val)
    (upper : state.val < 40640) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 40576, by omega⟩
  have state_eq :
      (⟨40576 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0634 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0635 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨40640 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨40640 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0635
    (state : Fin 48684)
    (lower : 40640 ≤ state.val)
    (upper : state.val < 40704) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 40640, by omega⟩
  have state_eq :
      (⟨40640 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0635 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0636 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨40704 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨40704 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0636
    (state : Fin 48684)
    (lower : 40704 ≤ state.val)
    (upper : state.val < 40768) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 40704, by omega⟩
  have state_eq :
      (⟨40704 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0636 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0637 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨40768 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨40768 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0637
    (state : Fin 48684)
    (lower : 40768 ≤ state.val)
    (upper : state.val < 40832) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 40768, by omega⟩
  have state_eq :
      (⟨40768 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0637 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0638 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨40832 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨40832 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0638
    (state : Fin 48684)
    (lower : 40832 ≤ state.val)
    (upper : state.val < 40896) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 40832, by omega⟩
  have state_eq :
      (⟨40832 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0638 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0639 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨40896 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨40896 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0639
    (state : Fin 48684)
    (lower : 40896 ≤ state.val)
    (upper : state.val < 40960) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 40896, by omega⟩
  have state_eq :
      (⟨40896 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0639 offset

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards
