import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Support.Core
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0672 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨43008 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨43008 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨43008 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0672
    (state : Fin 48684)
    (lower : 43008 ≤ state.val)
    (upper : state.val < 43072) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 43008, by omega⟩
  have state_eq :
      (⟨43008 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0672 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0673 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨43072 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨43072 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨43072 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0673
    (state : Fin 48684)
    (lower : 43072 ≤ state.val)
    (upper : state.val < 43136) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 43072, by omega⟩
  have state_eq :
      (⟨43072 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0673 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0674 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨43136 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨43136 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨43136 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0674
    (state : Fin 48684)
    (lower : 43136 ≤ state.val)
    (upper : state.val < 43200) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 43136, by omega⟩
  have state_eq :
      (⟨43136 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0674 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0675 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨43200 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨43200 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨43200 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0675
    (state : Fin 48684)
    (lower : 43200 ≤ state.val)
    (upper : state.val < 43264) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 43200, by omega⟩
  have state_eq :
      (⟨43200 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0675 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0676 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨43264 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨43264 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨43264 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0676
    (state : Fin 48684)
    (lower : 43264 ≤ state.val)
    (upper : state.val < 43328) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 43264, by omega⟩
  have state_eq :
      (⟨43264 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0676 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0677 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨43328 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨43328 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨43328 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0677
    (state : Fin 48684)
    (lower : 43328 ≤ state.val)
    (upper : state.val < 43392) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 43328, by omega⟩
  have state_eq :
      (⟨43328 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0677 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0678 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨43392 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨43392 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨43392 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0678
    (state : Fin 48684)
    (lower : 43392 ≤ state.val)
    (upper : state.val < 43456) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 43392, by omega⟩
  have state_eq :
      (⟨43392 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0678 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0679 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨43456 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨43456 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨43456 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0679
    (state : Fin 48684)
    (lower : 43456 ≤ state.val)
    (upper : state.val < 43520) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 43456, by omega⟩
  have state_eq :
      (⟨43456 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0679 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0680 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨43520 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨43520 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨43520 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0680
    (state : Fin 48684)
    (lower : 43520 ≤ state.val)
    (upper : state.val < 43584) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 43520, by omega⟩
  have state_eq :
      (⟨43520 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0680 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0681 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨43584 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨43584 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨43584 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0681
    (state : Fin 48684)
    (lower : 43584 ≤ state.val)
    (upper : state.val < 43648) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 43584, by omega⟩
  have state_eq :
      (⟨43584 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0681 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0682 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨43648 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨43648 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨43648 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0682
    (state : Fin 48684)
    (lower : 43648 ≤ state.val)
    (upper : state.val < 43712) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 43648, by omega⟩
  have state_eq :
      (⟨43648 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0682 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0683 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨43712 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨43712 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨43712 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0683
    (state : Fin 48684)
    (lower : 43712 ≤ state.val)
    (upper : state.val < 43776) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 43712, by omega⟩
  have state_eq :
      (⟨43712 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0683 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0684 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨43776 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨43776 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨43776 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0684
    (state : Fin 48684)
    (lower : 43776 ≤ state.val)
    (upper : state.val < 43840) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 43776, by omega⟩
  have state_eq :
      (⟨43776 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0684 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0685 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨43840 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨43840 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨43840 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0685
    (state : Fin 48684)
    (lower : 43840 ≤ state.val)
    (upper : state.val < 43904) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 43840, by omega⟩
  have state_eq :
      (⟨43840 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0685 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0686 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨43904 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨43904 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨43904 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0686
    (state : Fin 48684)
    (lower : 43904 ≤ state.val)
    (upper : state.val < 43968) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 43904, by omega⟩
  have state_eq :
      (⟨43904 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0686 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0687 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨43968 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨43968 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨43968 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0687
    (state : Fin 48684)
    (lower : 43968 ≤ state.val)
    (upper : state.val < 44032) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 43968, by omega⟩
  have state_eq :
      (⟨43968 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0687 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0688 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨44032 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨44032 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨44032 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0688
    (state : Fin 48684)
    (lower : 44032 ≤ state.val)
    (upper : state.val < 44096) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 44032, by omega⟩
  have state_eq :
      (⟨44032 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0688 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0689 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨44096 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨44096 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨44096 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0689
    (state : Fin 48684)
    (lower : 44096 ≤ state.val)
    (upper : state.val < 44160) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 44096, by omega⟩
  have state_eq :
      (⟨44096 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0689 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0690 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨44160 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨44160 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨44160 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0690
    (state : Fin 48684)
    (lower : 44160 ≤ state.val)
    (upper : state.val < 44224) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 44160, by omega⟩
  have state_eq :
      (⟨44160 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0690 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0691 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨44224 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨44224 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨44224 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0691
    (state : Fin 48684)
    (lower : 44224 ≤ state.val)
    (upper : state.val < 44288) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 44224, by omega⟩
  have state_eq :
      (⟨44224 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0691 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0692 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨44288 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨44288 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨44288 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0692
    (state : Fin 48684)
    (lower : 44288 ≤ state.val)
    (upper : state.val < 44352) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 44288, by omega⟩
  have state_eq :
      (⟨44288 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0692 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0693 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨44352 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨44352 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨44352 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0693
    (state : Fin 48684)
    (lower : 44352 ≤ state.val)
    (upper : state.val < 44416) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 44352, by omega⟩
  have state_eq :
      (⟨44352 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0693 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0694 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨44416 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨44416 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨44416 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0694
    (state : Fin 48684)
    (lower : 44416 ≤ state.val)
    (upper : state.val < 44480) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 44416, by omega⟩
  have state_eq :
      (⟨44416 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0694 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0695 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨44480 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨44480 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨44480 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0695
    (state : Fin 48684)
    (lower : 44480 ≤ state.val)
    (upper : state.val < 44544) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 44480, by omega⟩
  have state_eq :
      (⟨44480 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0695 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0696 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨44544 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨44544 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨44544 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0696
    (state : Fin 48684)
    (lower : 44544 ≤ state.val)
    (upper : state.val < 44608) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 44544, by omega⟩
  have state_eq :
      (⟨44544 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0696 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0697 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨44608 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨44608 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨44608 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0697
    (state : Fin 48684)
    (lower : 44608 ≤ state.val)
    (upper : state.val < 44672) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 44608, by omega⟩
  have state_eq :
      (⟨44608 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0697 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0698 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨44672 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨44672 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨44672 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0698
    (state : Fin 48684)
    (lower : 44672 ≤ state.val)
    (upper : state.val < 44736) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 44672, by omega⟩
  have state_eq :
      (⟨44672 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0698 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0699 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨44736 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨44736 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨44736 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0699
    (state : Fin 48684)
    (lower : 44736 ≤ state.val)
    (upper : state.val < 44800) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 44736, by omega⟩
  have state_eq :
      (⟨44736 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0699 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0700 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨44800 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨44800 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨44800 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0700
    (state : Fin 48684)
    (lower : 44800 ≤ state.val)
    (upper : state.val < 44864) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 44800, by omega⟩
  have state_eq :
      (⟨44800 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0700 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0701 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨44864 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨44864 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨44864 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0701
    (state : Fin 48684)
    (lower : 44864 ≤ state.val)
    (upper : state.val < 44928) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 44864, by omega⟩
  have state_eq :
      (⟨44864 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0701 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0702 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨44928 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨44928 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨44928 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0702
    (state : Fin 48684)
    (lower : 44928 ≤ state.val)
    (upper : state.val < 44992) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 44928, by omega⟩
  have state_eq :
      (⟨44928 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0702 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0703 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨44992 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨44992 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨44992 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0703
    (state : Fin 48684)
    (lower : 44992 ≤ state.val)
    (upper : state.val < 45056) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 44992, by omega⟩
  have state_eq :
      (⟨44992 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0703 offset

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards
