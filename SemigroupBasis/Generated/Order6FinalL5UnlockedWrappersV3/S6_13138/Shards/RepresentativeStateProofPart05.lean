import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.Support.Core
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.Shards

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0160 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeTail (⟨10240 + candidate.val, by omega⟩ : Fin 11742)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeHead (⟨10240 + candidate.val, by omega⟩ : Fin 11742))) =
        (⟨10240 + candidate.val, by omega⟩ : Fin 11742)
    := by
  decide

theorem representativeStateProof0160
    (state : Fin 11742)
    (lower : 10240 ≤ state.val)
    (upper : state.val < 10304) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 10240, by omega⟩
  have state_eq :
      (⟨10240 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0160 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0161 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeTail (⟨10304 + candidate.val, by omega⟩ : Fin 11742)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeHead (⟨10304 + candidate.val, by omega⟩ : Fin 11742))) =
        (⟨10304 + candidate.val, by omega⟩ : Fin 11742)
    := by
  decide

theorem representativeStateProof0161
    (state : Fin 11742)
    (lower : 10304 ≤ state.val)
    (upper : state.val < 10368) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 10304, by omega⟩
  have state_eq :
      (⟨10304 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0161 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0162 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeTail (⟨10368 + candidate.val, by omega⟩ : Fin 11742)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeHead (⟨10368 + candidate.val, by omega⟩ : Fin 11742))) =
        (⟨10368 + candidate.val, by omega⟩ : Fin 11742)
    := by
  decide

theorem representativeStateProof0162
    (state : Fin 11742)
    (lower : 10368 ≤ state.val)
    (upper : state.val < 10432) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 10368, by omega⟩
  have state_eq :
      (⟨10368 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0162 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0163 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeTail (⟨10432 + candidate.val, by omega⟩ : Fin 11742)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeHead (⟨10432 + candidate.val, by omega⟩ : Fin 11742))) =
        (⟨10432 + candidate.val, by omega⟩ : Fin 11742)
    := by
  decide

theorem representativeStateProof0163
    (state : Fin 11742)
    (lower : 10432 ≤ state.val)
    (upper : state.val < 10496) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 10432, by omega⟩
  have state_eq :
      (⟨10432 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0163 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0164 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeTail (⟨10496 + candidate.val, by omega⟩ : Fin 11742)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeHead (⟨10496 + candidate.val, by omega⟩ : Fin 11742))) =
        (⟨10496 + candidate.val, by omega⟩ : Fin 11742)
    := by
  decide

theorem representativeStateProof0164
    (state : Fin 11742)
    (lower : 10496 ≤ state.val)
    (upper : state.val < 10560) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 10496, by omega⟩
  have state_eq :
      (⟨10496 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0164 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0165 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeTail (⟨10560 + candidate.val, by omega⟩ : Fin 11742)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeHead (⟨10560 + candidate.val, by omega⟩ : Fin 11742))) =
        (⟨10560 + candidate.val, by omega⟩ : Fin 11742)
    := by
  decide

theorem representativeStateProof0165
    (state : Fin 11742)
    (lower : 10560 ≤ state.val)
    (upper : state.val < 10624) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 10560, by omega⟩
  have state_eq :
      (⟨10560 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0165 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0166 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeTail (⟨10624 + candidate.val, by omega⟩ : Fin 11742)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeHead (⟨10624 + candidate.val, by omega⟩ : Fin 11742))) =
        (⟨10624 + candidate.val, by omega⟩ : Fin 11742)
    := by
  decide

theorem representativeStateProof0166
    (state : Fin 11742)
    (lower : 10624 ≤ state.val)
    (upper : state.val < 10688) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 10624, by omega⟩
  have state_eq :
      (⟨10624 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0166 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0167 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeTail (⟨10688 + candidate.val, by omega⟩ : Fin 11742)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeHead (⟨10688 + candidate.val, by omega⟩ : Fin 11742))) =
        (⟨10688 + candidate.val, by omega⟩ : Fin 11742)
    := by
  decide

theorem representativeStateProof0167
    (state : Fin 11742)
    (lower : 10688 ≤ state.val)
    (upper : state.val < 10752) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 10688, by omega⟩
  have state_eq :
      (⟨10688 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0167 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0168 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeTail (⟨10752 + candidate.val, by omega⟩ : Fin 11742)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeHead (⟨10752 + candidate.val, by omega⟩ : Fin 11742))) =
        (⟨10752 + candidate.val, by omega⟩ : Fin 11742)
    := by
  decide

theorem representativeStateProof0168
    (state : Fin 11742)
    (lower : 10752 ≤ state.val)
    (upper : state.val < 10816) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 10752, by omega⟩
  have state_eq :
      (⟨10752 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0168 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0169 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeTail (⟨10816 + candidate.val, by omega⟩ : Fin 11742)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeHead (⟨10816 + candidate.val, by omega⟩ : Fin 11742))) =
        (⟨10816 + candidate.val, by omega⟩ : Fin 11742)
    := by
  decide

theorem representativeStateProof0169
    (state : Fin 11742)
    (lower : 10816 ≤ state.val)
    (upper : state.val < 10880) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 10816, by omega⟩
  have state_eq :
      (⟨10816 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0169 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0170 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeTail (⟨10880 + candidate.val, by omega⟩ : Fin 11742)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeHead (⟨10880 + candidate.val, by omega⟩ : Fin 11742))) =
        (⟨10880 + candidate.val, by omega⟩ : Fin 11742)
    := by
  decide

theorem representativeStateProof0170
    (state : Fin 11742)
    (lower : 10880 ≤ state.val)
    (upper : state.val < 10944) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 10880, by omega⟩
  have state_eq :
      (⟨10880 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0170 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0171 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeTail (⟨10944 + candidate.val, by omega⟩ : Fin 11742)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeHead (⟨10944 + candidate.val, by omega⟩ : Fin 11742))) =
        (⟨10944 + candidate.val, by omega⟩ : Fin 11742)
    := by
  decide

theorem representativeStateProof0171
    (state : Fin 11742)
    (lower : 10944 ≤ state.val)
    (upper : state.val < 11008) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 10944, by omega⟩
  have state_eq :
      (⟨10944 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0171 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0172 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeTail (⟨11008 + candidate.val, by omega⟩ : Fin 11742)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeHead (⟨11008 + candidate.val, by omega⟩ : Fin 11742))) =
        (⟨11008 + candidate.val, by omega⟩ : Fin 11742)
    := by
  decide

theorem representativeStateProof0172
    (state : Fin 11742)
    (lower : 11008 ≤ state.val)
    (upper : state.val < 11072) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 11008, by omega⟩
  have state_eq :
      (⟨11008 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0172 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0173 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeTail (⟨11072 + candidate.val, by omega⟩ : Fin 11742)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeHead (⟨11072 + candidate.val, by omega⟩ : Fin 11742))) =
        (⟨11072 + candidate.val, by omega⟩ : Fin 11742)
    := by
  decide

theorem representativeStateProof0173
    (state : Fin 11742)
    (lower : 11072 ≤ state.val)
    (upper : state.val < 11136) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 11072, by omega⟩
  have state_eq :
      (⟨11072 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0173 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0174 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeTail (⟨11136 + candidate.val, by omega⟩ : Fin 11742)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeHead (⟨11136 + candidate.val, by omega⟩ : Fin 11742))) =
        (⟨11136 + candidate.val, by omega⟩ : Fin 11742)
    := by
  decide

theorem representativeStateProof0174
    (state : Fin 11742)
    (lower : 11136 ≤ state.val)
    (upper : state.val < 11200) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 11136, by omega⟩
  have state_eq :
      (⟨11136 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0174 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0175 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeTail (⟨11200 + candidate.val, by omega⟩ : Fin 11742)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeHead (⟨11200 + candidate.val, by omega⟩ : Fin 11742))) =
        (⟨11200 + candidate.val, by omega⟩ : Fin 11742)
    := by
  decide

theorem representativeStateProof0175
    (state : Fin 11742)
    (lower : 11200 ≤ state.val)
    (upper : state.val < 11264) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 11200, by omega⟩
  have state_eq :
      (⟨11200 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0175 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0176 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeTail (⟨11264 + candidate.val, by omega⟩ : Fin 11742)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeHead (⟨11264 + candidate.val, by omega⟩ : Fin 11742))) =
        (⟨11264 + candidate.val, by omega⟩ : Fin 11742)
    := by
  decide

theorem representativeStateProof0176
    (state : Fin 11742)
    (lower : 11264 ≤ state.val)
    (upper : state.val < 11328) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 11264, by omega⟩
  have state_eq :
      (⟨11264 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0176 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0177 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeTail (⟨11328 + candidate.val, by omega⟩ : Fin 11742)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeHead (⟨11328 + candidate.val, by omega⟩ : Fin 11742))) =
        (⟨11328 + candidate.val, by omega⟩ : Fin 11742)
    := by
  decide

theorem representativeStateProof0177
    (state : Fin 11742)
    (lower : 11328 ≤ state.val)
    (upper : state.val < 11392) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 11328, by omega⟩
  have state_eq :
      (⟨11328 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0177 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0178 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeTail (⟨11392 + candidate.val, by omega⟩ : Fin 11742)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeHead (⟨11392 + candidate.val, by omega⟩ : Fin 11742))) =
        (⟨11392 + candidate.val, by omega⟩ : Fin 11742)
    := by
  decide

theorem representativeStateProof0178
    (state : Fin 11742)
    (lower : 11392 ≤ state.val)
    (upper : state.val < 11456) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 11392, by omega⟩
  have state_eq :
      (⟨11392 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0178 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0179 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeTail (⟨11456 + candidate.val, by omega⟩ : Fin 11742)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeHead (⟨11456 + candidate.val, by omega⟩ : Fin 11742))) =
        (⟨11456 + candidate.val, by omega⟩ : Fin 11742)
    := by
  decide

theorem representativeStateProof0179
    (state : Fin 11742)
    (lower : 11456 ≤ state.val)
    (upper : state.val < 11520) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 11456, by omega⟩
  have state_eq :
      (⟨11456 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0179 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0180 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeTail (⟨11520 + candidate.val, by omega⟩ : Fin 11742)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeHead (⟨11520 + candidate.val, by omega⟩ : Fin 11742))) =
        (⟨11520 + candidate.val, by omega⟩ : Fin 11742)
    := by
  decide

theorem representativeStateProof0180
    (state : Fin 11742)
    (lower : 11520 ≤ state.val)
    (upper : state.val < 11584) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 11520, by omega⟩
  have state_eq :
      (⟨11520 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0180 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0181 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeTail (⟨11584 + candidate.val, by omega⟩ : Fin 11742)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeHead (⟨11584 + candidate.val, by omega⟩ : Fin 11742))) =
        (⟨11584 + candidate.val, by omega⟩ : Fin 11742)
    := by
  decide

theorem representativeStateProof0181
    (state : Fin 11742)
    (lower : 11584 ≤ state.val)
    (upper : state.val < 11648) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 11584, by omega⟩
  have state_eq :
      (⟨11584 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0181 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0182 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeTail (⟨11648 + candidate.val, by omega⟩ : Fin 11742)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeHead (⟨11648 + candidate.val, by omega⟩ : Fin 11742))) =
        (⟨11648 + candidate.val, by omega⟩ : Fin 11742)
    := by
  decide

theorem representativeStateProof0182
    (state : Fin 11742)
    (lower : 11648 ≤ state.val)
    (upper : state.val < 11712) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 11648, by omega⟩
  have state_eq :
      (⟨11648 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0182 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0183 :
    ∀ candidate : Fin 30,
      (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeTail (⟨11712 + candidate.val, by omega⟩ : Fin 11742)).foldl
          SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.transition
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.generatorState
            (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeHead (⟨11712 + candidate.val, by omega⟩ : Fin 11742))) =
        (⟨11712 + candidate.val, by omega⟩ : Fin 11742)
    := by
  decide

theorem representativeStateProof0183
    (state : Fin 11742)
    (lower : 11712 ≤ state.val)
    (upper : state.val < 11742) :
    (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.representativeHead state)) =
      state
    := by
  let offset : Fin 30 := ⟨state.val - 11712, by omega⟩
  have state_eq :
      (⟨11712 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0183 offset

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.Shards
