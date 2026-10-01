import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Support.Core
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0736 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨47104 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨47104 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨47104 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0736
    (state : Fin 48684)
    (lower : 47104 ≤ state.val)
    (upper : state.val < 47168) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 47104, by omega⟩
  have state_eq :
      (⟨47104 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0736 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0737 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨47168 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨47168 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨47168 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0737
    (state : Fin 48684)
    (lower : 47168 ≤ state.val)
    (upper : state.val < 47232) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 47168, by omega⟩
  have state_eq :
      (⟨47168 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0737 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0738 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨47232 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨47232 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨47232 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0738
    (state : Fin 48684)
    (lower : 47232 ≤ state.val)
    (upper : state.val < 47296) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 47232, by omega⟩
  have state_eq :
      (⟨47232 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0738 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0739 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨47296 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨47296 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨47296 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0739
    (state : Fin 48684)
    (lower : 47296 ≤ state.val)
    (upper : state.val < 47360) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 47296, by omega⟩
  have state_eq :
      (⟨47296 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0739 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0740 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨47360 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨47360 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨47360 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0740
    (state : Fin 48684)
    (lower : 47360 ≤ state.val)
    (upper : state.val < 47424) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 47360, by omega⟩
  have state_eq :
      (⟨47360 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0740 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0741 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨47424 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨47424 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨47424 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0741
    (state : Fin 48684)
    (lower : 47424 ≤ state.val)
    (upper : state.val < 47488) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 47424, by omega⟩
  have state_eq :
      (⟨47424 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0741 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0742 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨47488 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨47488 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨47488 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0742
    (state : Fin 48684)
    (lower : 47488 ≤ state.val)
    (upper : state.val < 47552) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 47488, by omega⟩
  have state_eq :
      (⟨47488 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0742 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0743 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨47552 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨47552 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨47552 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0743
    (state : Fin 48684)
    (lower : 47552 ≤ state.val)
    (upper : state.val < 47616) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 47552, by omega⟩
  have state_eq :
      (⟨47552 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0743 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0744 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨47616 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨47616 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨47616 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0744
    (state : Fin 48684)
    (lower : 47616 ≤ state.val)
    (upper : state.val < 47680) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 47616, by omega⟩
  have state_eq :
      (⟨47616 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0744 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0745 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨47680 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨47680 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨47680 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0745
    (state : Fin 48684)
    (lower : 47680 ≤ state.val)
    (upper : state.val < 47744) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 47680, by omega⟩
  have state_eq :
      (⟨47680 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0745 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0746 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨47744 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨47744 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨47744 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0746
    (state : Fin 48684)
    (lower : 47744 ≤ state.val)
    (upper : state.val < 47808) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 47744, by omega⟩
  have state_eq :
      (⟨47744 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0746 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0747 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨47808 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨47808 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨47808 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0747
    (state : Fin 48684)
    (lower : 47808 ≤ state.val)
    (upper : state.val < 47872) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 47808, by omega⟩
  have state_eq :
      (⟨47808 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0747 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0748 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨47872 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨47872 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨47872 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0748
    (state : Fin 48684)
    (lower : 47872 ≤ state.val)
    (upper : state.val < 47936) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 47872, by omega⟩
  have state_eq :
      (⟨47872 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0748 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0749 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨47936 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨47936 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨47936 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0749
    (state : Fin 48684)
    (lower : 47936 ≤ state.val)
    (upper : state.val < 48000) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 47936, by omega⟩
  have state_eq :
      (⟨47936 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0749 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0750 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨48000 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨48000 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨48000 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0750
    (state : Fin 48684)
    (lower : 48000 ≤ state.val)
    (upper : state.val < 48064) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 48000, by omega⟩
  have state_eq :
      (⟨48000 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0750 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0751 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨48064 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨48064 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨48064 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0751
    (state : Fin 48684)
    (lower : 48064 ≤ state.val)
    (upper : state.val < 48128) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 48064, by omega⟩
  have state_eq :
      (⟨48064 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0751 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0752 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨48128 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨48128 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨48128 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0752
    (state : Fin 48684)
    (lower : 48128 ≤ state.val)
    (upper : state.val < 48192) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 48128, by omega⟩
  have state_eq :
      (⟨48128 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0752 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0753 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨48192 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨48192 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨48192 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0753
    (state : Fin 48684)
    (lower : 48192 ≤ state.val)
    (upper : state.val < 48256) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 48192, by omega⟩
  have state_eq :
      (⟨48192 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0753 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0754 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨48256 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨48256 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨48256 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0754
    (state : Fin 48684)
    (lower : 48256 ≤ state.val)
    (upper : state.val < 48320) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 48256, by omega⟩
  have state_eq :
      (⟨48256 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0754 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0755 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨48320 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨48320 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨48320 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0755
    (state : Fin 48684)
    (lower : 48320 ≤ state.val)
    (upper : state.val < 48384) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 48320, by omega⟩
  have state_eq :
      (⟨48320 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0755 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0756 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨48384 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨48384 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨48384 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0756
    (state : Fin 48684)
    (lower : 48384 ≤ state.val)
    (upper : state.val < 48448) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 48384, by omega⟩
  have state_eq :
      (⟨48384 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0756 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0757 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨48448 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨48448 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨48448 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0757
    (state : Fin 48684)
    (lower : 48448 ≤ state.val)
    (upper : state.val < 48512) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 48448, by omega⟩
  have state_eq :
      (⟨48448 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0757 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0758 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨48512 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨48512 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨48512 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0758
    (state : Fin 48684)
    (lower : 48512 ≤ state.val)
    (upper : state.val < 48576) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 48512, by omega⟩
  have state_eq :
      (⟨48512 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0758 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0759 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨48576 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨48576 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨48576 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0759
    (state : Fin 48684)
    (lower : 48576 ≤ state.val)
    (upper : state.val < 48640) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 48576, by omega⟩
  have state_eq :
      (⟨48576 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0759 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0760 :
    ∀ candidate : Fin 44,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨48640 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨48640 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨48640 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0760
    (state : Fin 48684)
    (lower : 48640 ≤ state.val)
    (upper : state.val < 48684) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 44 := ⟨state.val - 48640, by omega⟩
  have state_eq :
      (⟨48640 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0760 offset

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards
