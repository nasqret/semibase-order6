import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.Support.Core
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.Shards

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0000 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.representativeTail (⟨0 + candidate.val, by omega⟩ : Fin 1158)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.representativeHead (⟨0 + candidate.val, by omega⟩ : Fin 1158))) =
        (⟨0 + candidate.val, by omega⟩ : Fin 1158)
    := by
  decide

theorem representativeStateProof0000
    (state : Fin 1158)
    (lower : 0 ≤ state.val)
    (upper : state.val < 64) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 0, by omega⟩
  have state_eq :
      (⟨0 + offset.val, by omega⟩ : Fin 1158) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0000 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0001 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.representativeTail (⟨64 + candidate.val, by omega⟩ : Fin 1158)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.representativeHead (⟨64 + candidate.val, by omega⟩ : Fin 1158))) =
        (⟨64 + candidate.val, by omega⟩ : Fin 1158)
    := by
  decide

theorem representativeStateProof0001
    (state : Fin 1158)
    (lower : 64 ≤ state.val)
    (upper : state.val < 128) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 64, by omega⟩
  have state_eq :
      (⟨64 + offset.val, by omega⟩ : Fin 1158) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0001 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0002 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.representativeTail (⟨128 + candidate.val, by omega⟩ : Fin 1158)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.representativeHead (⟨128 + candidate.val, by omega⟩ : Fin 1158))) =
        (⟨128 + candidate.val, by omega⟩ : Fin 1158)
    := by
  decide

theorem representativeStateProof0002
    (state : Fin 1158)
    (lower : 128 ≤ state.val)
    (upper : state.val < 192) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 128, by omega⟩
  have state_eq :
      (⟨128 + offset.val, by omega⟩ : Fin 1158) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0002 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0003 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.representativeTail (⟨192 + candidate.val, by omega⟩ : Fin 1158)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.representativeHead (⟨192 + candidate.val, by omega⟩ : Fin 1158))) =
        (⟨192 + candidate.val, by omega⟩ : Fin 1158)
    := by
  decide

theorem representativeStateProof0003
    (state : Fin 1158)
    (lower : 192 ≤ state.val)
    (upper : state.val < 256) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 192, by omega⟩
  have state_eq :
      (⟨192 + offset.val, by omega⟩ : Fin 1158) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0003 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0004 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.representativeTail (⟨256 + candidate.val, by omega⟩ : Fin 1158)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.representativeHead (⟨256 + candidate.val, by omega⟩ : Fin 1158))) =
        (⟨256 + candidate.val, by omega⟩ : Fin 1158)
    := by
  decide

theorem representativeStateProof0004
    (state : Fin 1158)
    (lower : 256 ≤ state.val)
    (upper : state.val < 320) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 256, by omega⟩
  have state_eq :
      (⟨256 + offset.val, by omega⟩ : Fin 1158) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0004 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0005 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.representativeTail (⟨320 + candidate.val, by omega⟩ : Fin 1158)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.representativeHead (⟨320 + candidate.val, by omega⟩ : Fin 1158))) =
        (⟨320 + candidate.val, by omega⟩ : Fin 1158)
    := by
  decide

theorem representativeStateProof0005
    (state : Fin 1158)
    (lower : 320 ≤ state.val)
    (upper : state.val < 384) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 320, by omega⟩
  have state_eq :
      (⟨320 + offset.val, by omega⟩ : Fin 1158) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0005 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0006 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.representativeTail (⟨384 + candidate.val, by omega⟩ : Fin 1158)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.representativeHead (⟨384 + candidate.val, by omega⟩ : Fin 1158))) =
        (⟨384 + candidate.val, by omega⟩ : Fin 1158)
    := by
  decide

theorem representativeStateProof0006
    (state : Fin 1158)
    (lower : 384 ≤ state.val)
    (upper : state.val < 448) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 384, by omega⟩
  have state_eq :
      (⟨384 + offset.val, by omega⟩ : Fin 1158) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0006 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0007 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.representativeTail (⟨448 + candidate.val, by omega⟩ : Fin 1158)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.representativeHead (⟨448 + candidate.val, by omega⟩ : Fin 1158))) =
        (⟨448 + candidate.val, by omega⟩ : Fin 1158)
    := by
  decide

theorem representativeStateProof0007
    (state : Fin 1158)
    (lower : 448 ≤ state.val)
    (upper : state.val < 512) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 448, by omega⟩
  have state_eq :
      (⟨448 + offset.val, by omega⟩ : Fin 1158) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0007 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0008 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.representativeTail (⟨512 + candidate.val, by omega⟩ : Fin 1158)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.representativeHead (⟨512 + candidate.val, by omega⟩ : Fin 1158))) =
        (⟨512 + candidate.val, by omega⟩ : Fin 1158)
    := by
  decide

theorem representativeStateProof0008
    (state : Fin 1158)
    (lower : 512 ≤ state.val)
    (upper : state.val < 576) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 512, by omega⟩
  have state_eq :
      (⟨512 + offset.val, by omega⟩ : Fin 1158) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0008 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0009 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.representativeTail (⟨576 + candidate.val, by omega⟩ : Fin 1158)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.representativeHead (⟨576 + candidate.val, by omega⟩ : Fin 1158))) =
        (⟨576 + candidate.val, by omega⟩ : Fin 1158)
    := by
  decide

theorem representativeStateProof0009
    (state : Fin 1158)
    (lower : 576 ≤ state.val)
    (upper : state.val < 640) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 576, by omega⟩
  have state_eq :
      (⟨576 + offset.val, by omega⟩ : Fin 1158) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0009 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0010 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.representativeTail (⟨640 + candidate.val, by omega⟩ : Fin 1158)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.representativeHead (⟨640 + candidate.val, by omega⟩ : Fin 1158))) =
        (⟨640 + candidate.val, by omega⟩ : Fin 1158)
    := by
  decide

theorem representativeStateProof0010
    (state : Fin 1158)
    (lower : 640 ≤ state.val)
    (upper : state.val < 704) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 640, by omega⟩
  have state_eq :
      (⟨640 + offset.val, by omega⟩ : Fin 1158) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0010 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0011 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.representativeTail (⟨704 + candidate.val, by omega⟩ : Fin 1158)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.representativeHead (⟨704 + candidate.val, by omega⟩ : Fin 1158))) =
        (⟨704 + candidate.val, by omega⟩ : Fin 1158)
    := by
  decide

theorem representativeStateProof0011
    (state : Fin 1158)
    (lower : 704 ≤ state.val)
    (upper : state.val < 768) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 704, by omega⟩
  have state_eq :
      (⟨704 + offset.val, by omega⟩ : Fin 1158) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0011 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0012 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.representativeTail (⟨768 + candidate.val, by omega⟩ : Fin 1158)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.representativeHead (⟨768 + candidate.val, by omega⟩ : Fin 1158))) =
        (⟨768 + candidate.val, by omega⟩ : Fin 1158)
    := by
  decide

theorem representativeStateProof0012
    (state : Fin 1158)
    (lower : 768 ≤ state.val)
    (upper : state.val < 832) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 768, by omega⟩
  have state_eq :
      (⟨768 + offset.val, by omega⟩ : Fin 1158) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0012 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0013 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.representativeTail (⟨832 + candidate.val, by omega⟩ : Fin 1158)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.representativeHead (⟨832 + candidate.val, by omega⟩ : Fin 1158))) =
        (⟨832 + candidate.val, by omega⟩ : Fin 1158)
    := by
  decide

theorem representativeStateProof0013
    (state : Fin 1158)
    (lower : 832 ≤ state.val)
    (upper : state.val < 896) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 832, by omega⟩
  have state_eq :
      (⟨832 + offset.val, by omega⟩ : Fin 1158) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0013 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0014 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.representativeTail (⟨896 + candidate.val, by omega⟩ : Fin 1158)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.representativeHead (⟨896 + candidate.val, by omega⟩ : Fin 1158))) =
        (⟨896 + candidate.val, by omega⟩ : Fin 1158)
    := by
  decide

theorem representativeStateProof0014
    (state : Fin 1158)
    (lower : 896 ≤ state.val)
    (upper : state.val < 960) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 896, by omega⟩
  have state_eq :
      (⟨896 + offset.val, by omega⟩ : Fin 1158) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0014 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0015 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.representativeTail (⟨960 + candidate.val, by omega⟩ : Fin 1158)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.representativeHead (⟨960 + candidate.val, by omega⟩ : Fin 1158))) =
        (⟨960 + candidate.val, by omega⟩ : Fin 1158)
    := by
  decide

theorem representativeStateProof0015
    (state : Fin 1158)
    (lower : 960 ≤ state.val)
    (upper : state.val < 1024) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 960, by omega⟩
  have state_eq :
      (⟨960 + offset.val, by omega⟩ : Fin 1158) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0015 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0016 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.representativeTail (⟨1024 + candidate.val, by omega⟩ : Fin 1158)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.representativeHead (⟨1024 + candidate.val, by omega⟩ : Fin 1158))) =
        (⟨1024 + candidate.val, by omega⟩ : Fin 1158)
    := by
  decide

theorem representativeStateProof0016
    (state : Fin 1158)
    (lower : 1024 ≤ state.val)
    (upper : state.val < 1088) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 1024, by omega⟩
  have state_eq :
      (⟨1024 + offset.val, by omega⟩ : Fin 1158) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0016 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0017 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.representativeTail (⟨1088 + candidate.val, by omega⟩ : Fin 1158)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.representativeHead (⟨1088 + candidate.val, by omega⟩ : Fin 1158))) =
        (⟨1088 + candidate.val, by omega⟩ : Fin 1158)
    := by
  decide

theorem representativeStateProof0017
    (state : Fin 1158)
    (lower : 1088 ≤ state.val)
    (upper : state.val < 1152) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 1088, by omega⟩
  have state_eq :
      (⟨1088 + offset.val, by omega⟩ : Fin 1158) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0017 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0018 :
    ∀ candidate : Fin 6,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.representativeTail (⟨1152 + candidate.val, by omega⟩ : Fin 1158)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.representativeHead (⟨1152 + candidate.val, by omega⟩ : Fin 1158))) =
        (⟨1152 + candidate.val, by omega⟩ : Fin 1158)
    := by
  decide

theorem representativeStateProof0018
    (state : Fin 1158)
    (lower : 1152 ≤ state.val)
    (upper : state.val < 1158) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.representativeHead state)) =
      state
    := by
  let offset : Fin 6 := ⟨state.val - 1152, by omega⟩
  have state_eq :
      (⟨1152 + offset.val, by omega⟩ : Fin 1158) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0018 offset

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.Shards
