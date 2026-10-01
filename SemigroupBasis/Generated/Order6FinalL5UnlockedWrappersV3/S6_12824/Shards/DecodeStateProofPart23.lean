import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards.DecodeState
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards.StateVector
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0736 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨47104 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨47104 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0736
    (state : Fin 48684)
    (lower : 47104 ≤ state.val)
    (upper : state.val < 47168) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 47104, by omega⟩
  have state_eq :
      (⟨47104 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0736 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0737 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨47168 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨47168 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0737
    (state : Fin 48684)
    (lower : 47168 ≤ state.val)
    (upper : state.val < 47232) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 47168, by omega⟩
  have state_eq :
      (⟨47168 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0737 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0738 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨47232 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨47232 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0738
    (state : Fin 48684)
    (lower : 47232 ≤ state.val)
    (upper : state.val < 47296) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 47232, by omega⟩
  have state_eq :
      (⟨47232 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0738 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0739 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨47296 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨47296 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0739
    (state : Fin 48684)
    (lower : 47296 ≤ state.val)
    (upper : state.val < 47360) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 47296, by omega⟩
  have state_eq :
      (⟨47296 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0739 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0740 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨47360 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨47360 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0740
    (state : Fin 48684)
    (lower : 47360 ≤ state.val)
    (upper : state.val < 47424) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 47360, by omega⟩
  have state_eq :
      (⟨47360 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0740 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0741 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨47424 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨47424 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0741
    (state : Fin 48684)
    (lower : 47424 ≤ state.val)
    (upper : state.val < 47488) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 47424, by omega⟩
  have state_eq :
      (⟨47424 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0741 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0742 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨47488 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨47488 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0742
    (state : Fin 48684)
    (lower : 47488 ≤ state.val)
    (upper : state.val < 47552) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 47488, by omega⟩
  have state_eq :
      (⟨47488 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0742 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0743 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨47552 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨47552 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0743
    (state : Fin 48684)
    (lower : 47552 ≤ state.val)
    (upper : state.val < 47616) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 47552, by omega⟩
  have state_eq :
      (⟨47552 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0743 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0744 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨47616 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨47616 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0744
    (state : Fin 48684)
    (lower : 47616 ≤ state.val)
    (upper : state.val < 47680) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 47616, by omega⟩
  have state_eq :
      (⟨47616 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0744 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0745 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨47680 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨47680 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0745
    (state : Fin 48684)
    (lower : 47680 ≤ state.val)
    (upper : state.val < 47744) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 47680, by omega⟩
  have state_eq :
      (⟨47680 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0745 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0746 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨47744 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨47744 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0746
    (state : Fin 48684)
    (lower : 47744 ≤ state.val)
    (upper : state.val < 47808) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 47744, by omega⟩
  have state_eq :
      (⟨47744 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0746 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0747 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨47808 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨47808 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0747
    (state : Fin 48684)
    (lower : 47808 ≤ state.val)
    (upper : state.val < 47872) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 47808, by omega⟩
  have state_eq :
      (⟨47808 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0747 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0748 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨47872 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨47872 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0748
    (state : Fin 48684)
    (lower : 47872 ≤ state.val)
    (upper : state.val < 47936) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 47872, by omega⟩
  have state_eq :
      (⟨47872 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0748 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0749 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨47936 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨47936 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0749
    (state : Fin 48684)
    (lower : 47936 ≤ state.val)
    (upper : state.val < 48000) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 47936, by omega⟩
  have state_eq :
      (⟨47936 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0749 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0750 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨48000 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨48000 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0750
    (state : Fin 48684)
    (lower : 48000 ≤ state.val)
    (upper : state.val < 48064) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 48000, by omega⟩
  have state_eq :
      (⟨48000 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0750 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0751 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨48064 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨48064 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0751
    (state : Fin 48684)
    (lower : 48064 ≤ state.val)
    (upper : state.val < 48128) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 48064, by omega⟩
  have state_eq :
      (⟨48064 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0751 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0752 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨48128 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨48128 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0752
    (state : Fin 48684)
    (lower : 48128 ≤ state.val)
    (upper : state.val < 48192) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 48128, by omega⟩
  have state_eq :
      (⟨48128 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0752 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0753 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨48192 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨48192 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0753
    (state : Fin 48684)
    (lower : 48192 ≤ state.val)
    (upper : state.val < 48256) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 48192, by omega⟩
  have state_eq :
      (⟨48192 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0753 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0754 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨48256 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨48256 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0754
    (state : Fin 48684)
    (lower : 48256 ≤ state.val)
    (upper : state.val < 48320) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 48256, by omega⟩
  have state_eq :
      (⟨48256 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0754 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0755 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨48320 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨48320 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0755
    (state : Fin 48684)
    (lower : 48320 ≤ state.val)
    (upper : state.val < 48384) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 48320, by omega⟩
  have state_eq :
      (⟨48320 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0755 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0756 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨48384 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨48384 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0756
    (state : Fin 48684)
    (lower : 48384 ≤ state.val)
    (upper : state.val < 48448) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 48384, by omega⟩
  have state_eq :
      (⟨48384 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0756 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0757 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨48448 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨48448 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0757
    (state : Fin 48684)
    (lower : 48448 ≤ state.val)
    (upper : state.val < 48512) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 48448, by omega⟩
  have state_eq :
      (⟨48448 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0757 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0758 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨48512 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨48512 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0758
    (state : Fin 48684)
    (lower : 48512 ≤ state.val)
    (upper : state.val < 48576) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 48512, by omega⟩
  have state_eq :
      (⟨48512 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0758 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0759 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨48576 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨48576 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0759
    (state : Fin 48684)
    (lower : 48576 ≤ state.val)
    (upper : state.val < 48640) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 48576, by omega⟩
  have state_eq :
      (⟨48576 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0759 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0760 :
    ∀ candidate : Fin 44,
      decodeState (stateVector (⟨48640 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨48640 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0760
    (state : Fin 48684)
    (lower : 48640 ≤ state.val)
    (upper : state.val < 48684) :
    decodeState (stateVector state) = state := by
  let offset : Fin 44 := ⟨state.val - 48640, by omega⟩
  have state_eq :
      (⟨48640 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0760 offset

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards
