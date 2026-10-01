import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.Support.Core
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.Shards

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0224 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeTail (⟨14336 + candidate.val, by omega⟩ : Fin 17622)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeHead (⟨14336 + candidate.val, by omega⟩ : Fin 17622))) =
        (⟨14336 + candidate.val, by omega⟩ : Fin 17622)
    := by
  decide

theorem representativeStateProof0224
    (state : Fin 17622)
    (lower : 14336 ≤ state.val)
    (upper : state.val < 14400) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 14336, by omega⟩
  have state_eq :
      (⟨14336 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0224 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0225 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeTail (⟨14400 + candidate.val, by omega⟩ : Fin 17622)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeHead (⟨14400 + candidate.val, by omega⟩ : Fin 17622))) =
        (⟨14400 + candidate.val, by omega⟩ : Fin 17622)
    := by
  decide

theorem representativeStateProof0225
    (state : Fin 17622)
    (lower : 14400 ≤ state.val)
    (upper : state.val < 14464) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 14400, by omega⟩
  have state_eq :
      (⟨14400 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0225 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0226 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeTail (⟨14464 + candidate.val, by omega⟩ : Fin 17622)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeHead (⟨14464 + candidate.val, by omega⟩ : Fin 17622))) =
        (⟨14464 + candidate.val, by omega⟩ : Fin 17622)
    := by
  decide

theorem representativeStateProof0226
    (state : Fin 17622)
    (lower : 14464 ≤ state.val)
    (upper : state.val < 14528) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 14464, by omega⟩
  have state_eq :
      (⟨14464 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0226 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0227 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeTail (⟨14528 + candidate.val, by omega⟩ : Fin 17622)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeHead (⟨14528 + candidate.val, by omega⟩ : Fin 17622))) =
        (⟨14528 + candidate.val, by omega⟩ : Fin 17622)
    := by
  decide

theorem representativeStateProof0227
    (state : Fin 17622)
    (lower : 14528 ≤ state.val)
    (upper : state.val < 14592) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 14528, by omega⟩
  have state_eq :
      (⟨14528 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0227 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0228 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeTail (⟨14592 + candidate.val, by omega⟩ : Fin 17622)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeHead (⟨14592 + candidate.val, by omega⟩ : Fin 17622))) =
        (⟨14592 + candidate.val, by omega⟩ : Fin 17622)
    := by
  decide

theorem representativeStateProof0228
    (state : Fin 17622)
    (lower : 14592 ≤ state.val)
    (upper : state.val < 14656) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 14592, by omega⟩
  have state_eq :
      (⟨14592 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0228 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0229 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeTail (⟨14656 + candidate.val, by omega⟩ : Fin 17622)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeHead (⟨14656 + candidate.val, by omega⟩ : Fin 17622))) =
        (⟨14656 + candidate.val, by omega⟩ : Fin 17622)
    := by
  decide

theorem representativeStateProof0229
    (state : Fin 17622)
    (lower : 14656 ≤ state.val)
    (upper : state.val < 14720) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 14656, by omega⟩
  have state_eq :
      (⟨14656 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0229 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0230 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeTail (⟨14720 + candidate.val, by omega⟩ : Fin 17622)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeHead (⟨14720 + candidate.val, by omega⟩ : Fin 17622))) =
        (⟨14720 + candidate.val, by omega⟩ : Fin 17622)
    := by
  decide

theorem representativeStateProof0230
    (state : Fin 17622)
    (lower : 14720 ≤ state.val)
    (upper : state.val < 14784) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 14720, by omega⟩
  have state_eq :
      (⟨14720 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0230 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0231 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeTail (⟨14784 + candidate.val, by omega⟩ : Fin 17622)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeHead (⟨14784 + candidate.val, by omega⟩ : Fin 17622))) =
        (⟨14784 + candidate.val, by omega⟩ : Fin 17622)
    := by
  decide

theorem representativeStateProof0231
    (state : Fin 17622)
    (lower : 14784 ≤ state.val)
    (upper : state.val < 14848) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 14784, by omega⟩
  have state_eq :
      (⟨14784 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0231 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0232 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeTail (⟨14848 + candidate.val, by omega⟩ : Fin 17622)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeHead (⟨14848 + candidate.val, by omega⟩ : Fin 17622))) =
        (⟨14848 + candidate.val, by omega⟩ : Fin 17622)
    := by
  decide

theorem representativeStateProof0232
    (state : Fin 17622)
    (lower : 14848 ≤ state.val)
    (upper : state.val < 14912) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 14848, by omega⟩
  have state_eq :
      (⟨14848 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0232 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0233 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeTail (⟨14912 + candidate.val, by omega⟩ : Fin 17622)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeHead (⟨14912 + candidate.val, by omega⟩ : Fin 17622))) =
        (⟨14912 + candidate.val, by omega⟩ : Fin 17622)
    := by
  decide

theorem representativeStateProof0233
    (state : Fin 17622)
    (lower : 14912 ≤ state.val)
    (upper : state.val < 14976) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 14912, by omega⟩
  have state_eq :
      (⟨14912 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0233 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0234 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeTail (⟨14976 + candidate.val, by omega⟩ : Fin 17622)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeHead (⟨14976 + candidate.val, by omega⟩ : Fin 17622))) =
        (⟨14976 + candidate.val, by omega⟩ : Fin 17622)
    := by
  decide

theorem representativeStateProof0234
    (state : Fin 17622)
    (lower : 14976 ≤ state.val)
    (upper : state.val < 15040) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 14976, by omega⟩
  have state_eq :
      (⟨14976 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0234 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0235 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeTail (⟨15040 + candidate.val, by omega⟩ : Fin 17622)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeHead (⟨15040 + candidate.val, by omega⟩ : Fin 17622))) =
        (⟨15040 + candidate.val, by omega⟩ : Fin 17622)
    := by
  decide

theorem representativeStateProof0235
    (state : Fin 17622)
    (lower : 15040 ≤ state.val)
    (upper : state.val < 15104) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 15040, by omega⟩
  have state_eq :
      (⟨15040 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0235 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0236 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeTail (⟨15104 + candidate.val, by omega⟩ : Fin 17622)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeHead (⟨15104 + candidate.val, by omega⟩ : Fin 17622))) =
        (⟨15104 + candidate.val, by omega⟩ : Fin 17622)
    := by
  decide

theorem representativeStateProof0236
    (state : Fin 17622)
    (lower : 15104 ≤ state.val)
    (upper : state.val < 15168) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 15104, by omega⟩
  have state_eq :
      (⟨15104 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0236 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0237 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeTail (⟨15168 + candidate.val, by omega⟩ : Fin 17622)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeHead (⟨15168 + candidate.val, by omega⟩ : Fin 17622))) =
        (⟨15168 + candidate.val, by omega⟩ : Fin 17622)
    := by
  decide

theorem representativeStateProof0237
    (state : Fin 17622)
    (lower : 15168 ≤ state.val)
    (upper : state.val < 15232) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 15168, by omega⟩
  have state_eq :
      (⟨15168 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0237 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0238 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeTail (⟨15232 + candidate.val, by omega⟩ : Fin 17622)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeHead (⟨15232 + candidate.val, by omega⟩ : Fin 17622))) =
        (⟨15232 + candidate.val, by omega⟩ : Fin 17622)
    := by
  decide

theorem representativeStateProof0238
    (state : Fin 17622)
    (lower : 15232 ≤ state.val)
    (upper : state.val < 15296) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 15232, by omega⟩
  have state_eq :
      (⟨15232 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0238 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0239 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeTail (⟨15296 + candidate.val, by omega⟩ : Fin 17622)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeHead (⟨15296 + candidate.val, by omega⟩ : Fin 17622))) =
        (⟨15296 + candidate.val, by omega⟩ : Fin 17622)
    := by
  decide

theorem representativeStateProof0239
    (state : Fin 17622)
    (lower : 15296 ≤ state.val)
    (upper : state.val < 15360) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 15296, by omega⟩
  have state_eq :
      (⟨15296 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0239 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0240 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeTail (⟨15360 + candidate.val, by omega⟩ : Fin 17622)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeHead (⟨15360 + candidate.val, by omega⟩ : Fin 17622))) =
        (⟨15360 + candidate.val, by omega⟩ : Fin 17622)
    := by
  decide

theorem representativeStateProof0240
    (state : Fin 17622)
    (lower : 15360 ≤ state.val)
    (upper : state.val < 15424) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 15360, by omega⟩
  have state_eq :
      (⟨15360 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0240 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0241 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeTail (⟨15424 + candidate.val, by omega⟩ : Fin 17622)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeHead (⟨15424 + candidate.val, by omega⟩ : Fin 17622))) =
        (⟨15424 + candidate.val, by omega⟩ : Fin 17622)
    := by
  decide

theorem representativeStateProof0241
    (state : Fin 17622)
    (lower : 15424 ≤ state.val)
    (upper : state.val < 15488) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 15424, by omega⟩
  have state_eq :
      (⟨15424 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0241 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0242 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeTail (⟨15488 + candidate.val, by omega⟩ : Fin 17622)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeHead (⟨15488 + candidate.val, by omega⟩ : Fin 17622))) =
        (⟨15488 + candidate.val, by omega⟩ : Fin 17622)
    := by
  decide

theorem representativeStateProof0242
    (state : Fin 17622)
    (lower : 15488 ≤ state.val)
    (upper : state.val < 15552) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 15488, by omega⟩
  have state_eq :
      (⟨15488 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0242 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0243 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeTail (⟨15552 + candidate.val, by omega⟩ : Fin 17622)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeHead (⟨15552 + candidate.val, by omega⟩ : Fin 17622))) =
        (⟨15552 + candidate.val, by omega⟩ : Fin 17622)
    := by
  decide

theorem representativeStateProof0243
    (state : Fin 17622)
    (lower : 15552 ≤ state.val)
    (upper : state.val < 15616) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 15552, by omega⟩
  have state_eq :
      (⟨15552 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0243 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0244 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeTail (⟨15616 + candidate.val, by omega⟩ : Fin 17622)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeHead (⟨15616 + candidate.val, by omega⟩ : Fin 17622))) =
        (⟨15616 + candidate.val, by omega⟩ : Fin 17622)
    := by
  decide

theorem representativeStateProof0244
    (state : Fin 17622)
    (lower : 15616 ≤ state.val)
    (upper : state.val < 15680) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 15616, by omega⟩
  have state_eq :
      (⟨15616 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0244 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0245 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeTail (⟨15680 + candidate.val, by omega⟩ : Fin 17622)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeHead (⟨15680 + candidate.val, by omega⟩ : Fin 17622))) =
        (⟨15680 + candidate.val, by omega⟩ : Fin 17622)
    := by
  decide

theorem representativeStateProof0245
    (state : Fin 17622)
    (lower : 15680 ≤ state.val)
    (upper : state.val < 15744) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 15680, by omega⟩
  have state_eq :
      (⟨15680 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0245 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0246 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeTail (⟨15744 + candidate.val, by omega⟩ : Fin 17622)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeHead (⟨15744 + candidate.val, by omega⟩ : Fin 17622))) =
        (⟨15744 + candidate.val, by omega⟩ : Fin 17622)
    := by
  decide

theorem representativeStateProof0246
    (state : Fin 17622)
    (lower : 15744 ≤ state.val)
    (upper : state.val < 15808) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 15744, by omega⟩
  have state_eq :
      (⟨15744 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0246 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0247 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeTail (⟨15808 + candidate.val, by omega⟩ : Fin 17622)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeHead (⟨15808 + candidate.val, by omega⟩ : Fin 17622))) =
        (⟨15808 + candidate.val, by omega⟩ : Fin 17622)
    := by
  decide

theorem representativeStateProof0247
    (state : Fin 17622)
    (lower : 15808 ≤ state.val)
    (upper : state.val < 15872) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 15808, by omega⟩
  have state_eq :
      (⟨15808 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0247 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0248 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeTail (⟨15872 + candidate.val, by omega⟩ : Fin 17622)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeHead (⟨15872 + candidate.val, by omega⟩ : Fin 17622))) =
        (⟨15872 + candidate.val, by omega⟩ : Fin 17622)
    := by
  decide

theorem representativeStateProof0248
    (state : Fin 17622)
    (lower : 15872 ≤ state.val)
    (upper : state.val < 15936) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 15872, by omega⟩
  have state_eq :
      (⟨15872 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0248 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0249 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeTail (⟨15936 + candidate.val, by omega⟩ : Fin 17622)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeHead (⟨15936 + candidate.val, by omega⟩ : Fin 17622))) =
        (⟨15936 + candidate.val, by omega⟩ : Fin 17622)
    := by
  decide

theorem representativeStateProof0249
    (state : Fin 17622)
    (lower : 15936 ≤ state.val)
    (upper : state.val < 16000) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 15936, by omega⟩
  have state_eq :
      (⟨15936 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0249 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0250 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeTail (⟨16000 + candidate.val, by omega⟩ : Fin 17622)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeHead (⟨16000 + candidate.val, by omega⟩ : Fin 17622))) =
        (⟨16000 + candidate.val, by omega⟩ : Fin 17622)
    := by
  decide

theorem representativeStateProof0250
    (state : Fin 17622)
    (lower : 16000 ≤ state.val)
    (upper : state.val < 16064) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 16000, by omega⟩
  have state_eq :
      (⟨16000 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0250 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0251 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeTail (⟨16064 + candidate.val, by omega⟩ : Fin 17622)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeHead (⟨16064 + candidate.val, by omega⟩ : Fin 17622))) =
        (⟨16064 + candidate.val, by omega⟩ : Fin 17622)
    := by
  decide

theorem representativeStateProof0251
    (state : Fin 17622)
    (lower : 16064 ≤ state.val)
    (upper : state.val < 16128) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 16064, by omega⟩
  have state_eq :
      (⟨16064 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0251 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0252 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeTail (⟨16128 + candidate.val, by omega⟩ : Fin 17622)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeHead (⟨16128 + candidate.val, by omega⟩ : Fin 17622))) =
        (⟨16128 + candidate.val, by omega⟩ : Fin 17622)
    := by
  decide

theorem representativeStateProof0252
    (state : Fin 17622)
    (lower : 16128 ≤ state.val)
    (upper : state.val < 16192) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 16128, by omega⟩
  have state_eq :
      (⟨16128 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0252 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0253 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeTail (⟨16192 + candidate.val, by omega⟩ : Fin 17622)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeHead (⟨16192 + candidate.val, by omega⟩ : Fin 17622))) =
        (⟨16192 + candidate.val, by omega⟩ : Fin 17622)
    := by
  decide

theorem representativeStateProof0253
    (state : Fin 17622)
    (lower : 16192 ≤ state.val)
    (upper : state.val < 16256) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 16192, by omega⟩
  have state_eq :
      (⟨16192 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0253 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0254 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeTail (⟨16256 + candidate.val, by omega⟩ : Fin 17622)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeHead (⟨16256 + candidate.val, by omega⟩ : Fin 17622))) =
        (⟨16256 + candidate.val, by omega⟩ : Fin 17622)
    := by
  decide

theorem representativeStateProof0254
    (state : Fin 17622)
    (lower : 16256 ≤ state.val)
    (upper : state.val < 16320) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 16256, by omega⟩
  have state_eq :
      (⟨16256 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0254 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0255 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeTail (⟨16320 + candidate.val, by omega⟩ : Fin 17622)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeHead (⟨16320 + candidate.val, by omega⟩ : Fin 17622))) =
        (⟨16320 + candidate.val, by omega⟩ : Fin 17622)
    := by
  decide

theorem representativeStateProof0255
    (state : Fin 17622)
    (lower : 16320 ≤ state.val)
    (upper : state.val < 16384) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 16320, by omega⟩
  have state_eq :
      (⟨16320 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0255 offset

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.Shards
