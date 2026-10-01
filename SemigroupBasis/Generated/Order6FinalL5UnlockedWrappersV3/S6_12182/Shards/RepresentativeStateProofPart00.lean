import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.Support.Core
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.Shards

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0000 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeTail (⟨0 + candidate.val, by omega⟩ : Fin 17622)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeHead (⟨0 + candidate.val, by omega⟩ : Fin 17622))) =
        (⟨0 + candidate.val, by omega⟩ : Fin 17622)
    := by
  decide

theorem representativeStateProof0000
    (state : Fin 17622)
    (lower : 0 ≤ state.val)
    (upper : state.val < 64) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 0, by omega⟩
  have state_eq :
      (⟨0 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0000 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0001 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeTail (⟨64 + candidate.val, by omega⟩ : Fin 17622)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeHead (⟨64 + candidate.val, by omega⟩ : Fin 17622))) =
        (⟨64 + candidate.val, by omega⟩ : Fin 17622)
    := by
  decide

theorem representativeStateProof0001
    (state : Fin 17622)
    (lower : 64 ≤ state.val)
    (upper : state.val < 128) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 64, by omega⟩
  have state_eq :
      (⟨64 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0001 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0002 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeTail (⟨128 + candidate.val, by omega⟩ : Fin 17622)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeHead (⟨128 + candidate.val, by omega⟩ : Fin 17622))) =
        (⟨128 + candidate.val, by omega⟩ : Fin 17622)
    := by
  decide

theorem representativeStateProof0002
    (state : Fin 17622)
    (lower : 128 ≤ state.val)
    (upper : state.val < 192) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 128, by omega⟩
  have state_eq :
      (⟨128 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0002 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0003 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeTail (⟨192 + candidate.val, by omega⟩ : Fin 17622)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeHead (⟨192 + candidate.val, by omega⟩ : Fin 17622))) =
        (⟨192 + candidate.val, by omega⟩ : Fin 17622)
    := by
  decide

theorem representativeStateProof0003
    (state : Fin 17622)
    (lower : 192 ≤ state.val)
    (upper : state.val < 256) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 192, by omega⟩
  have state_eq :
      (⟨192 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0003 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0004 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeTail (⟨256 + candidate.val, by omega⟩ : Fin 17622)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeHead (⟨256 + candidate.val, by omega⟩ : Fin 17622))) =
        (⟨256 + candidate.val, by omega⟩ : Fin 17622)
    := by
  decide

theorem representativeStateProof0004
    (state : Fin 17622)
    (lower : 256 ≤ state.val)
    (upper : state.val < 320) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 256, by omega⟩
  have state_eq :
      (⟨256 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0004 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0005 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeTail (⟨320 + candidate.val, by omega⟩ : Fin 17622)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeHead (⟨320 + candidate.val, by omega⟩ : Fin 17622))) =
        (⟨320 + candidate.val, by omega⟩ : Fin 17622)
    := by
  decide

theorem representativeStateProof0005
    (state : Fin 17622)
    (lower : 320 ≤ state.val)
    (upper : state.val < 384) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 320, by omega⟩
  have state_eq :
      (⟨320 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0005 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0006 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeTail (⟨384 + candidate.val, by omega⟩ : Fin 17622)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeHead (⟨384 + candidate.val, by omega⟩ : Fin 17622))) =
        (⟨384 + candidate.val, by omega⟩ : Fin 17622)
    := by
  decide

theorem representativeStateProof0006
    (state : Fin 17622)
    (lower : 384 ≤ state.val)
    (upper : state.val < 448) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 384, by omega⟩
  have state_eq :
      (⟨384 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0006 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0007 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeTail (⟨448 + candidate.val, by omega⟩ : Fin 17622)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeHead (⟨448 + candidate.val, by omega⟩ : Fin 17622))) =
        (⟨448 + candidate.val, by omega⟩ : Fin 17622)
    := by
  decide

theorem representativeStateProof0007
    (state : Fin 17622)
    (lower : 448 ≤ state.val)
    (upper : state.val < 512) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 448, by omega⟩
  have state_eq :
      (⟨448 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0007 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0008 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeTail (⟨512 + candidate.val, by omega⟩ : Fin 17622)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeHead (⟨512 + candidate.val, by omega⟩ : Fin 17622))) =
        (⟨512 + candidate.val, by omega⟩ : Fin 17622)
    := by
  decide

theorem representativeStateProof0008
    (state : Fin 17622)
    (lower : 512 ≤ state.val)
    (upper : state.val < 576) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 512, by omega⟩
  have state_eq :
      (⟨512 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0008 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0009 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeTail (⟨576 + candidate.val, by omega⟩ : Fin 17622)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeHead (⟨576 + candidate.val, by omega⟩ : Fin 17622))) =
        (⟨576 + candidate.val, by omega⟩ : Fin 17622)
    := by
  decide

theorem representativeStateProof0009
    (state : Fin 17622)
    (lower : 576 ≤ state.val)
    (upper : state.val < 640) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 576, by omega⟩
  have state_eq :
      (⟨576 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0009 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0010 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeTail (⟨640 + candidate.val, by omega⟩ : Fin 17622)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeHead (⟨640 + candidate.val, by omega⟩ : Fin 17622))) =
        (⟨640 + candidate.val, by omega⟩ : Fin 17622)
    := by
  decide

theorem representativeStateProof0010
    (state : Fin 17622)
    (lower : 640 ≤ state.val)
    (upper : state.val < 704) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 640, by omega⟩
  have state_eq :
      (⟨640 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0010 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0011 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeTail (⟨704 + candidate.val, by omega⟩ : Fin 17622)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeHead (⟨704 + candidate.val, by omega⟩ : Fin 17622))) =
        (⟨704 + candidate.val, by omega⟩ : Fin 17622)
    := by
  decide

theorem representativeStateProof0011
    (state : Fin 17622)
    (lower : 704 ≤ state.val)
    (upper : state.val < 768) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 704, by omega⟩
  have state_eq :
      (⟨704 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0011 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0012 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeTail (⟨768 + candidate.val, by omega⟩ : Fin 17622)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeHead (⟨768 + candidate.val, by omega⟩ : Fin 17622))) =
        (⟨768 + candidate.val, by omega⟩ : Fin 17622)
    := by
  decide

theorem representativeStateProof0012
    (state : Fin 17622)
    (lower : 768 ≤ state.val)
    (upper : state.val < 832) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 768, by omega⟩
  have state_eq :
      (⟨768 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0012 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0013 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeTail (⟨832 + candidate.val, by omega⟩ : Fin 17622)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeHead (⟨832 + candidate.val, by omega⟩ : Fin 17622))) =
        (⟨832 + candidate.val, by omega⟩ : Fin 17622)
    := by
  decide

theorem representativeStateProof0013
    (state : Fin 17622)
    (lower : 832 ≤ state.val)
    (upper : state.val < 896) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 832, by omega⟩
  have state_eq :
      (⟨832 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0013 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0014 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeTail (⟨896 + candidate.val, by omega⟩ : Fin 17622)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeHead (⟨896 + candidate.val, by omega⟩ : Fin 17622))) =
        (⟨896 + candidate.val, by omega⟩ : Fin 17622)
    := by
  decide

theorem representativeStateProof0014
    (state : Fin 17622)
    (lower : 896 ≤ state.val)
    (upper : state.val < 960) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 896, by omega⟩
  have state_eq :
      (⟨896 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0014 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0015 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeTail (⟨960 + candidate.val, by omega⟩ : Fin 17622)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeHead (⟨960 + candidate.val, by omega⟩ : Fin 17622))) =
        (⟨960 + candidate.val, by omega⟩ : Fin 17622)
    := by
  decide

theorem representativeStateProof0015
    (state : Fin 17622)
    (lower : 960 ≤ state.val)
    (upper : state.val < 1024) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 960, by omega⟩
  have state_eq :
      (⟨960 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0015 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0016 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeTail (⟨1024 + candidate.val, by omega⟩ : Fin 17622)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeHead (⟨1024 + candidate.val, by omega⟩ : Fin 17622))) =
        (⟨1024 + candidate.val, by omega⟩ : Fin 17622)
    := by
  decide

theorem representativeStateProof0016
    (state : Fin 17622)
    (lower : 1024 ≤ state.val)
    (upper : state.val < 1088) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 1024, by omega⟩
  have state_eq :
      (⟨1024 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0016 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0017 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeTail (⟨1088 + candidate.val, by omega⟩ : Fin 17622)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeHead (⟨1088 + candidate.val, by omega⟩ : Fin 17622))) =
        (⟨1088 + candidate.val, by omega⟩ : Fin 17622)
    := by
  decide

theorem representativeStateProof0017
    (state : Fin 17622)
    (lower : 1088 ≤ state.val)
    (upper : state.val < 1152) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 1088, by omega⟩
  have state_eq :
      (⟨1088 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0017 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0018 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeTail (⟨1152 + candidate.val, by omega⟩ : Fin 17622)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeHead (⟨1152 + candidate.val, by omega⟩ : Fin 17622))) =
        (⟨1152 + candidate.val, by omega⟩ : Fin 17622)
    := by
  decide

theorem representativeStateProof0018
    (state : Fin 17622)
    (lower : 1152 ≤ state.val)
    (upper : state.val < 1216) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 1152, by omega⟩
  have state_eq :
      (⟨1152 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0018 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0019 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeTail (⟨1216 + candidate.val, by omega⟩ : Fin 17622)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeHead (⟨1216 + candidate.val, by omega⟩ : Fin 17622))) =
        (⟨1216 + candidate.val, by omega⟩ : Fin 17622)
    := by
  decide

theorem representativeStateProof0019
    (state : Fin 17622)
    (lower : 1216 ≤ state.val)
    (upper : state.val < 1280) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 1216, by omega⟩
  have state_eq :
      (⟨1216 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0019 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0020 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeTail (⟨1280 + candidate.val, by omega⟩ : Fin 17622)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeHead (⟨1280 + candidate.val, by omega⟩ : Fin 17622))) =
        (⟨1280 + candidate.val, by omega⟩ : Fin 17622)
    := by
  decide

theorem representativeStateProof0020
    (state : Fin 17622)
    (lower : 1280 ≤ state.val)
    (upper : state.val < 1344) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 1280, by omega⟩
  have state_eq :
      (⟨1280 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0020 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0021 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeTail (⟨1344 + candidate.val, by omega⟩ : Fin 17622)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeHead (⟨1344 + candidate.val, by omega⟩ : Fin 17622))) =
        (⟨1344 + candidate.val, by omega⟩ : Fin 17622)
    := by
  decide

theorem representativeStateProof0021
    (state : Fin 17622)
    (lower : 1344 ≤ state.val)
    (upper : state.val < 1408) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 1344, by omega⟩
  have state_eq :
      (⟨1344 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0021 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0022 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeTail (⟨1408 + candidate.val, by omega⟩ : Fin 17622)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeHead (⟨1408 + candidate.val, by omega⟩ : Fin 17622))) =
        (⟨1408 + candidate.val, by omega⟩ : Fin 17622)
    := by
  decide

theorem representativeStateProof0022
    (state : Fin 17622)
    (lower : 1408 ≤ state.val)
    (upper : state.val < 1472) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 1408, by omega⟩
  have state_eq :
      (⟨1408 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0022 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0023 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeTail (⟨1472 + candidate.val, by omega⟩ : Fin 17622)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeHead (⟨1472 + candidate.val, by omega⟩ : Fin 17622))) =
        (⟨1472 + candidate.val, by omega⟩ : Fin 17622)
    := by
  decide

theorem representativeStateProof0023
    (state : Fin 17622)
    (lower : 1472 ≤ state.val)
    (upper : state.val < 1536) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 1472, by omega⟩
  have state_eq :
      (⟨1472 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0023 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0024 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeTail (⟨1536 + candidate.val, by omega⟩ : Fin 17622)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeHead (⟨1536 + candidate.val, by omega⟩ : Fin 17622))) =
        (⟨1536 + candidate.val, by omega⟩ : Fin 17622)
    := by
  decide

theorem representativeStateProof0024
    (state : Fin 17622)
    (lower : 1536 ≤ state.val)
    (upper : state.val < 1600) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 1536, by omega⟩
  have state_eq :
      (⟨1536 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0024 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0025 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeTail (⟨1600 + candidate.val, by omega⟩ : Fin 17622)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeHead (⟨1600 + candidate.val, by omega⟩ : Fin 17622))) =
        (⟨1600 + candidate.val, by omega⟩ : Fin 17622)
    := by
  decide

theorem representativeStateProof0025
    (state : Fin 17622)
    (lower : 1600 ≤ state.val)
    (upper : state.val < 1664) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 1600, by omega⟩
  have state_eq :
      (⟨1600 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0025 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0026 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeTail (⟨1664 + candidate.val, by omega⟩ : Fin 17622)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeHead (⟨1664 + candidate.val, by omega⟩ : Fin 17622))) =
        (⟨1664 + candidate.val, by omega⟩ : Fin 17622)
    := by
  decide

theorem representativeStateProof0026
    (state : Fin 17622)
    (lower : 1664 ≤ state.val)
    (upper : state.val < 1728) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 1664, by omega⟩
  have state_eq :
      (⟨1664 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0026 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0027 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeTail (⟨1728 + candidate.val, by omega⟩ : Fin 17622)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeHead (⟨1728 + candidate.val, by omega⟩ : Fin 17622))) =
        (⟨1728 + candidate.val, by omega⟩ : Fin 17622)
    := by
  decide

theorem representativeStateProof0027
    (state : Fin 17622)
    (lower : 1728 ≤ state.val)
    (upper : state.val < 1792) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 1728, by omega⟩
  have state_eq :
      (⟨1728 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0027 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0028 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeTail (⟨1792 + candidate.val, by omega⟩ : Fin 17622)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeHead (⟨1792 + candidate.val, by omega⟩ : Fin 17622))) =
        (⟨1792 + candidate.val, by omega⟩ : Fin 17622)
    := by
  decide

theorem representativeStateProof0028
    (state : Fin 17622)
    (lower : 1792 ≤ state.val)
    (upper : state.val < 1856) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 1792, by omega⟩
  have state_eq :
      (⟨1792 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0028 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0029 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeTail (⟨1856 + candidate.val, by omega⟩ : Fin 17622)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeHead (⟨1856 + candidate.val, by omega⟩ : Fin 17622))) =
        (⟨1856 + candidate.val, by omega⟩ : Fin 17622)
    := by
  decide

theorem representativeStateProof0029
    (state : Fin 17622)
    (lower : 1856 ≤ state.val)
    (upper : state.val < 1920) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 1856, by omega⟩
  have state_eq :
      (⟨1856 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0029 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0030 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeTail (⟨1920 + candidate.val, by omega⟩ : Fin 17622)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeHead (⟨1920 + candidate.val, by omega⟩ : Fin 17622))) =
        (⟨1920 + candidate.val, by omega⟩ : Fin 17622)
    := by
  decide

theorem representativeStateProof0030
    (state : Fin 17622)
    (lower : 1920 ≤ state.val)
    (upper : state.val < 1984) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 1920, by omega⟩
  have state_eq :
      (⟨1920 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0030 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0031 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeTail (⟨1984 + candidate.val, by omega⟩ : Fin 17622)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeHead (⟨1984 + candidate.val, by omega⟩ : Fin 17622))) =
        (⟨1984 + candidate.val, by omega⟩ : Fin 17622)
    := by
  decide

theorem representativeStateProof0031
    (state : Fin 17622)
    (lower : 1984 ≤ state.val)
    (upper : state.val < 2048) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 1984, by omega⟩
  have state_eq :
      (⟨1984 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0031 offset

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.Shards
