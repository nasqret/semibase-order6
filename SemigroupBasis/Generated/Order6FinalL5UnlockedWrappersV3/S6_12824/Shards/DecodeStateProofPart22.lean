import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards.DecodeState
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards.StateVector
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0704 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨45056 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨45056 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0704
    (state : Fin 48684)
    (lower : 45056 ≤ state.val)
    (upper : state.val < 45120) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 45056, by omega⟩
  have state_eq :
      (⟨45056 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0704 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0705 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨45120 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨45120 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0705
    (state : Fin 48684)
    (lower : 45120 ≤ state.val)
    (upper : state.val < 45184) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 45120, by omega⟩
  have state_eq :
      (⟨45120 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0705 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0706 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨45184 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨45184 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0706
    (state : Fin 48684)
    (lower : 45184 ≤ state.val)
    (upper : state.val < 45248) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 45184, by omega⟩
  have state_eq :
      (⟨45184 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0706 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0707 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨45248 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨45248 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0707
    (state : Fin 48684)
    (lower : 45248 ≤ state.val)
    (upper : state.val < 45312) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 45248, by omega⟩
  have state_eq :
      (⟨45248 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0707 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0708 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨45312 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨45312 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0708
    (state : Fin 48684)
    (lower : 45312 ≤ state.val)
    (upper : state.val < 45376) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 45312, by omega⟩
  have state_eq :
      (⟨45312 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0708 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0709 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨45376 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨45376 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0709
    (state : Fin 48684)
    (lower : 45376 ≤ state.val)
    (upper : state.val < 45440) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 45376, by omega⟩
  have state_eq :
      (⟨45376 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0709 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0710 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨45440 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨45440 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0710
    (state : Fin 48684)
    (lower : 45440 ≤ state.val)
    (upper : state.val < 45504) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 45440, by omega⟩
  have state_eq :
      (⟨45440 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0710 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0711 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨45504 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨45504 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0711
    (state : Fin 48684)
    (lower : 45504 ≤ state.val)
    (upper : state.val < 45568) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 45504, by omega⟩
  have state_eq :
      (⟨45504 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0711 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0712 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨45568 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨45568 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0712
    (state : Fin 48684)
    (lower : 45568 ≤ state.val)
    (upper : state.val < 45632) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 45568, by omega⟩
  have state_eq :
      (⟨45568 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0712 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0713 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨45632 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨45632 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0713
    (state : Fin 48684)
    (lower : 45632 ≤ state.val)
    (upper : state.val < 45696) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 45632, by omega⟩
  have state_eq :
      (⟨45632 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0713 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0714 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨45696 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨45696 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0714
    (state : Fin 48684)
    (lower : 45696 ≤ state.val)
    (upper : state.val < 45760) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 45696, by omega⟩
  have state_eq :
      (⟨45696 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0714 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0715 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨45760 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨45760 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0715
    (state : Fin 48684)
    (lower : 45760 ≤ state.val)
    (upper : state.val < 45824) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 45760, by omega⟩
  have state_eq :
      (⟨45760 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0715 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0716 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨45824 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨45824 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0716
    (state : Fin 48684)
    (lower : 45824 ≤ state.val)
    (upper : state.val < 45888) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 45824, by omega⟩
  have state_eq :
      (⟨45824 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0716 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0717 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨45888 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨45888 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0717
    (state : Fin 48684)
    (lower : 45888 ≤ state.val)
    (upper : state.val < 45952) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 45888, by omega⟩
  have state_eq :
      (⟨45888 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0717 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0718 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨45952 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨45952 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0718
    (state : Fin 48684)
    (lower : 45952 ≤ state.val)
    (upper : state.val < 46016) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 45952, by omega⟩
  have state_eq :
      (⟨45952 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0718 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0719 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨46016 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨46016 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0719
    (state : Fin 48684)
    (lower : 46016 ≤ state.val)
    (upper : state.val < 46080) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 46016, by omega⟩
  have state_eq :
      (⟨46016 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0719 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0720 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨46080 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨46080 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0720
    (state : Fin 48684)
    (lower : 46080 ≤ state.val)
    (upper : state.val < 46144) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 46080, by omega⟩
  have state_eq :
      (⟨46080 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0720 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0721 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨46144 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨46144 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0721
    (state : Fin 48684)
    (lower : 46144 ≤ state.val)
    (upper : state.val < 46208) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 46144, by omega⟩
  have state_eq :
      (⟨46144 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0721 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0722 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨46208 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨46208 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0722
    (state : Fin 48684)
    (lower : 46208 ≤ state.val)
    (upper : state.val < 46272) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 46208, by omega⟩
  have state_eq :
      (⟨46208 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0722 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0723 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨46272 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨46272 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0723
    (state : Fin 48684)
    (lower : 46272 ≤ state.val)
    (upper : state.val < 46336) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 46272, by omega⟩
  have state_eq :
      (⟨46272 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0723 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0724 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨46336 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨46336 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0724
    (state : Fin 48684)
    (lower : 46336 ≤ state.val)
    (upper : state.val < 46400) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 46336, by omega⟩
  have state_eq :
      (⟨46336 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0724 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0725 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨46400 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨46400 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0725
    (state : Fin 48684)
    (lower : 46400 ≤ state.val)
    (upper : state.val < 46464) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 46400, by omega⟩
  have state_eq :
      (⟨46400 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0725 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0726 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨46464 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨46464 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0726
    (state : Fin 48684)
    (lower : 46464 ≤ state.val)
    (upper : state.val < 46528) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 46464, by omega⟩
  have state_eq :
      (⟨46464 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0726 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0727 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨46528 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨46528 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0727
    (state : Fin 48684)
    (lower : 46528 ≤ state.val)
    (upper : state.val < 46592) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 46528, by omega⟩
  have state_eq :
      (⟨46528 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0727 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0728 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨46592 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨46592 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0728
    (state : Fin 48684)
    (lower : 46592 ≤ state.val)
    (upper : state.val < 46656) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 46592, by omega⟩
  have state_eq :
      (⟨46592 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0728 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0729 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨46656 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨46656 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0729
    (state : Fin 48684)
    (lower : 46656 ≤ state.val)
    (upper : state.val < 46720) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 46656, by omega⟩
  have state_eq :
      (⟨46656 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0729 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0730 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨46720 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨46720 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0730
    (state : Fin 48684)
    (lower : 46720 ≤ state.val)
    (upper : state.val < 46784) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 46720, by omega⟩
  have state_eq :
      (⟨46720 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0730 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0731 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨46784 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨46784 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0731
    (state : Fin 48684)
    (lower : 46784 ≤ state.val)
    (upper : state.val < 46848) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 46784, by omega⟩
  have state_eq :
      (⟨46784 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0731 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0732 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨46848 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨46848 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0732
    (state : Fin 48684)
    (lower : 46848 ≤ state.val)
    (upper : state.val < 46912) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 46848, by omega⟩
  have state_eq :
      (⟨46848 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0732 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0733 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨46912 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨46912 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0733
    (state : Fin 48684)
    (lower : 46912 ≤ state.val)
    (upper : state.val < 46976) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 46912, by omega⟩
  have state_eq :
      (⟨46912 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0733 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0734 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨46976 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨46976 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0734
    (state : Fin 48684)
    (lower : 46976 ≤ state.val)
    (upper : state.val < 47040) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 46976, by omega⟩
  have state_eq :
      (⟨46976 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0734 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0735 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨47040 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨47040 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0735
    (state : Fin 48684)
    (lower : 47040 ≤ state.val)
    (upper : state.val < 47104) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 47040, by omega⟩
  have state_eq :
      (⟨47040 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0735 offset

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards
