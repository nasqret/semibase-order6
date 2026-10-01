import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Support.Core
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0256 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨16384 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨16384 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨16384 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0256
    (state : Fin 48684)
    (lower : 16384 ≤ state.val)
    (upper : state.val < 16448) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 16384, by omega⟩
  have state_eq :
      (⟨16384 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0256 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0257 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨16448 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨16448 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨16448 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0257
    (state : Fin 48684)
    (lower : 16448 ≤ state.val)
    (upper : state.val < 16512) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 16448, by omega⟩
  have state_eq :
      (⟨16448 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0257 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0258 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨16512 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨16512 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨16512 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0258
    (state : Fin 48684)
    (lower : 16512 ≤ state.val)
    (upper : state.val < 16576) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 16512, by omega⟩
  have state_eq :
      (⟨16512 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0258 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0259 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨16576 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨16576 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨16576 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0259
    (state : Fin 48684)
    (lower : 16576 ≤ state.val)
    (upper : state.val < 16640) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 16576, by omega⟩
  have state_eq :
      (⟨16576 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0259 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0260 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨16640 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨16640 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨16640 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0260
    (state : Fin 48684)
    (lower : 16640 ≤ state.val)
    (upper : state.val < 16704) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 16640, by omega⟩
  have state_eq :
      (⟨16640 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0260 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0261 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨16704 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨16704 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨16704 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0261
    (state : Fin 48684)
    (lower : 16704 ≤ state.val)
    (upper : state.val < 16768) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 16704, by omega⟩
  have state_eq :
      (⟨16704 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0261 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0262 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨16768 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨16768 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨16768 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0262
    (state : Fin 48684)
    (lower : 16768 ≤ state.val)
    (upper : state.val < 16832) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 16768, by omega⟩
  have state_eq :
      (⟨16768 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0262 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0263 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨16832 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨16832 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨16832 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0263
    (state : Fin 48684)
    (lower : 16832 ≤ state.val)
    (upper : state.val < 16896) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 16832, by omega⟩
  have state_eq :
      (⟨16832 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0263 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0264 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨16896 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨16896 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨16896 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0264
    (state : Fin 48684)
    (lower : 16896 ≤ state.val)
    (upper : state.val < 16960) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 16896, by omega⟩
  have state_eq :
      (⟨16896 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0264 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0265 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨16960 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨16960 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨16960 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0265
    (state : Fin 48684)
    (lower : 16960 ≤ state.val)
    (upper : state.val < 17024) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 16960, by omega⟩
  have state_eq :
      (⟨16960 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0265 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0266 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨17024 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨17024 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨17024 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0266
    (state : Fin 48684)
    (lower : 17024 ≤ state.val)
    (upper : state.val < 17088) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 17024, by omega⟩
  have state_eq :
      (⟨17024 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0266 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0267 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨17088 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨17088 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨17088 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0267
    (state : Fin 48684)
    (lower : 17088 ≤ state.val)
    (upper : state.val < 17152) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 17088, by omega⟩
  have state_eq :
      (⟨17088 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0267 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0268 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨17152 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨17152 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨17152 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0268
    (state : Fin 48684)
    (lower : 17152 ≤ state.val)
    (upper : state.val < 17216) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 17152, by omega⟩
  have state_eq :
      (⟨17152 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0268 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0269 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨17216 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨17216 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨17216 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0269
    (state : Fin 48684)
    (lower : 17216 ≤ state.val)
    (upper : state.val < 17280) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 17216, by omega⟩
  have state_eq :
      (⟨17216 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0269 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0270 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨17280 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨17280 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨17280 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0270
    (state : Fin 48684)
    (lower : 17280 ≤ state.val)
    (upper : state.val < 17344) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 17280, by omega⟩
  have state_eq :
      (⟨17280 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0270 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0271 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨17344 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨17344 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨17344 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0271
    (state : Fin 48684)
    (lower : 17344 ≤ state.val)
    (upper : state.val < 17408) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 17344, by omega⟩
  have state_eq :
      (⟨17344 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0271 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0272 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨17408 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨17408 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨17408 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0272
    (state : Fin 48684)
    (lower : 17408 ≤ state.val)
    (upper : state.val < 17472) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 17408, by omega⟩
  have state_eq :
      (⟨17408 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0272 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0273 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨17472 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨17472 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨17472 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0273
    (state : Fin 48684)
    (lower : 17472 ≤ state.val)
    (upper : state.val < 17536) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 17472, by omega⟩
  have state_eq :
      (⟨17472 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0273 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0274 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨17536 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨17536 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨17536 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0274
    (state : Fin 48684)
    (lower : 17536 ≤ state.val)
    (upper : state.val < 17600) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 17536, by omega⟩
  have state_eq :
      (⟨17536 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0274 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0275 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨17600 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨17600 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨17600 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0275
    (state : Fin 48684)
    (lower : 17600 ≤ state.val)
    (upper : state.val < 17664) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 17600, by omega⟩
  have state_eq :
      (⟨17600 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0275 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0276 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨17664 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨17664 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨17664 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0276
    (state : Fin 48684)
    (lower : 17664 ≤ state.val)
    (upper : state.val < 17728) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 17664, by omega⟩
  have state_eq :
      (⟨17664 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0276 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0277 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨17728 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨17728 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨17728 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0277
    (state : Fin 48684)
    (lower : 17728 ≤ state.val)
    (upper : state.val < 17792) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 17728, by omega⟩
  have state_eq :
      (⟨17728 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0277 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0278 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨17792 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨17792 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨17792 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0278
    (state : Fin 48684)
    (lower : 17792 ≤ state.val)
    (upper : state.val < 17856) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 17792, by omega⟩
  have state_eq :
      (⟨17792 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0278 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0279 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨17856 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨17856 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨17856 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0279
    (state : Fin 48684)
    (lower : 17856 ≤ state.val)
    (upper : state.val < 17920) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 17856, by omega⟩
  have state_eq :
      (⟨17856 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0279 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0280 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨17920 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨17920 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨17920 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0280
    (state : Fin 48684)
    (lower : 17920 ≤ state.val)
    (upper : state.val < 17984) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 17920, by omega⟩
  have state_eq :
      (⟨17920 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0280 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0281 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨17984 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨17984 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨17984 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0281
    (state : Fin 48684)
    (lower : 17984 ≤ state.val)
    (upper : state.val < 18048) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 17984, by omega⟩
  have state_eq :
      (⟨17984 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0281 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0282 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨18048 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨18048 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨18048 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0282
    (state : Fin 48684)
    (lower : 18048 ≤ state.val)
    (upper : state.val < 18112) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 18048, by omega⟩
  have state_eq :
      (⟨18048 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0282 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0283 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨18112 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨18112 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨18112 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0283
    (state : Fin 48684)
    (lower : 18112 ≤ state.val)
    (upper : state.val < 18176) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 18112, by omega⟩
  have state_eq :
      (⟨18112 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0283 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0284 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨18176 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨18176 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨18176 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0284
    (state : Fin 48684)
    (lower : 18176 ≤ state.val)
    (upper : state.val < 18240) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 18176, by omega⟩
  have state_eq :
      (⟨18176 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0284 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0285 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨18240 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨18240 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨18240 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0285
    (state : Fin 48684)
    (lower : 18240 ≤ state.val)
    (upper : state.val < 18304) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 18240, by omega⟩
  have state_eq :
      (⟨18240 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0285 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0286 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨18304 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨18304 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨18304 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0286
    (state : Fin 48684)
    (lower : 18304 ≤ state.val)
    (upper : state.val < 18368) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 18304, by omega⟩
  have state_eq :
      (⟨18304 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0286 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0287 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail (⟨18368 + candidate.val, by omega⟩ : Fin 48684)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead (⟨18368 + candidate.val, by omega⟩ : Fin 48684))) =
        (⟨18368 + candidate.val, by omega⟩ : Fin 48684)
    := by
  decide

theorem representativeStateProof0287
    (state : Fin 48684)
    (lower : 18368 ≤ state.val)
    (upper : state.val < 18432) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 18368, by omega⟩
  have state_eq :
      (⟨18368 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0287 offset

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards
