import SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.Support.Core
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.Shards

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0032 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.representativeTail (⟨2048 + candidate.val, by omega⟩ : Fin 2712)).foldl
          SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.transition
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.generatorState
            (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.representativeHead (⟨2048 + candidate.val, by omega⟩ : Fin 2712))) =
        (⟨2048 + candidate.val, by omega⟩ : Fin 2712)
    := by
  decide

theorem representativeStateProof0032
    (state : Fin 2712)
    (lower : 2048 ≤ state.val)
    (upper : state.val < 2112) :
    (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.representativeTail state).foldl
        SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.transition
        (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.generatorState
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 2048, by omega⟩
  have state_eq :
      (⟨2048 + offset.val, by omega⟩ : Fin 2712) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0032 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0033 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.representativeTail (⟨2112 + candidate.val, by omega⟩ : Fin 2712)).foldl
          SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.transition
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.generatorState
            (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.representativeHead (⟨2112 + candidate.val, by omega⟩ : Fin 2712))) =
        (⟨2112 + candidate.val, by omega⟩ : Fin 2712)
    := by
  decide

theorem representativeStateProof0033
    (state : Fin 2712)
    (lower : 2112 ≤ state.val)
    (upper : state.val < 2176) :
    (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.representativeTail state).foldl
        SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.transition
        (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.generatorState
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 2112, by omega⟩
  have state_eq :
      (⟨2112 + offset.val, by omega⟩ : Fin 2712) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0033 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0034 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.representativeTail (⟨2176 + candidate.val, by omega⟩ : Fin 2712)).foldl
          SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.transition
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.generatorState
            (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.representativeHead (⟨2176 + candidate.val, by omega⟩ : Fin 2712))) =
        (⟨2176 + candidate.val, by omega⟩ : Fin 2712)
    := by
  decide

theorem representativeStateProof0034
    (state : Fin 2712)
    (lower : 2176 ≤ state.val)
    (upper : state.val < 2240) :
    (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.representativeTail state).foldl
        SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.transition
        (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.generatorState
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 2176, by omega⟩
  have state_eq :
      (⟨2176 + offset.val, by omega⟩ : Fin 2712) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0034 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0035 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.representativeTail (⟨2240 + candidate.val, by omega⟩ : Fin 2712)).foldl
          SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.transition
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.generatorState
            (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.representativeHead (⟨2240 + candidate.val, by omega⟩ : Fin 2712))) =
        (⟨2240 + candidate.val, by omega⟩ : Fin 2712)
    := by
  decide

theorem representativeStateProof0035
    (state : Fin 2712)
    (lower : 2240 ≤ state.val)
    (upper : state.val < 2304) :
    (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.representativeTail state).foldl
        SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.transition
        (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.generatorState
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 2240, by omega⟩
  have state_eq :
      (⟨2240 + offset.val, by omega⟩ : Fin 2712) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0035 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0036 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.representativeTail (⟨2304 + candidate.val, by omega⟩ : Fin 2712)).foldl
          SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.transition
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.generatorState
            (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.representativeHead (⟨2304 + candidate.val, by omega⟩ : Fin 2712))) =
        (⟨2304 + candidate.val, by omega⟩ : Fin 2712)
    := by
  decide

theorem representativeStateProof0036
    (state : Fin 2712)
    (lower : 2304 ≤ state.val)
    (upper : state.val < 2368) :
    (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.representativeTail state).foldl
        SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.transition
        (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.generatorState
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 2304, by omega⟩
  have state_eq :
      (⟨2304 + offset.val, by omega⟩ : Fin 2712) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0036 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0037 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.representativeTail (⟨2368 + candidate.val, by omega⟩ : Fin 2712)).foldl
          SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.transition
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.generatorState
            (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.representativeHead (⟨2368 + candidate.val, by omega⟩ : Fin 2712))) =
        (⟨2368 + candidate.val, by omega⟩ : Fin 2712)
    := by
  decide

theorem representativeStateProof0037
    (state : Fin 2712)
    (lower : 2368 ≤ state.val)
    (upper : state.val < 2432) :
    (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.representativeTail state).foldl
        SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.transition
        (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.generatorState
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 2368, by omega⟩
  have state_eq :
      (⟨2368 + offset.val, by omega⟩ : Fin 2712) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0037 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0038 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.representativeTail (⟨2432 + candidate.val, by omega⟩ : Fin 2712)).foldl
          SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.transition
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.generatorState
            (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.representativeHead (⟨2432 + candidate.val, by omega⟩ : Fin 2712))) =
        (⟨2432 + candidate.val, by omega⟩ : Fin 2712)
    := by
  decide

theorem representativeStateProof0038
    (state : Fin 2712)
    (lower : 2432 ≤ state.val)
    (upper : state.val < 2496) :
    (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.representativeTail state).foldl
        SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.transition
        (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.generatorState
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 2432, by omega⟩
  have state_eq :
      (⟨2432 + offset.val, by omega⟩ : Fin 2712) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0038 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0039 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.representativeTail (⟨2496 + candidate.val, by omega⟩ : Fin 2712)).foldl
          SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.transition
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.generatorState
            (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.representativeHead (⟨2496 + candidate.val, by omega⟩ : Fin 2712))) =
        (⟨2496 + candidate.val, by omega⟩ : Fin 2712)
    := by
  decide

theorem representativeStateProof0039
    (state : Fin 2712)
    (lower : 2496 ≤ state.val)
    (upper : state.val < 2560) :
    (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.representativeTail state).foldl
        SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.transition
        (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.generatorState
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 2496, by omega⟩
  have state_eq :
      (⟨2496 + offset.val, by omega⟩ : Fin 2712) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0039 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0040 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.representativeTail (⟨2560 + candidate.val, by omega⟩ : Fin 2712)).foldl
          SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.transition
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.generatorState
            (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.representativeHead (⟨2560 + candidate.val, by omega⟩ : Fin 2712))) =
        (⟨2560 + candidate.val, by omega⟩ : Fin 2712)
    := by
  decide

theorem representativeStateProof0040
    (state : Fin 2712)
    (lower : 2560 ≤ state.val)
    (upper : state.val < 2624) :
    (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.representativeTail state).foldl
        SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.transition
        (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.generatorState
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 2560, by omega⟩
  have state_eq :
      (⟨2560 + offset.val, by omega⟩ : Fin 2712) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0040 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0041 :
    ∀ candidate : Fin 64,
      (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.representativeTail (⟨2624 + candidate.val, by omega⟩ : Fin 2712)).foldl
          SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.transition
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.generatorState
            (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.representativeHead (⟨2624 + candidate.val, by omega⟩ : Fin 2712))) =
        (⟨2624 + candidate.val, by omega⟩ : Fin 2712)
    := by
  decide

theorem representativeStateProof0041
    (state : Fin 2712)
    (lower : 2624 ≤ state.val)
    (upper : state.val < 2688) :
    (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.representativeTail state).foldl
        SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.transition
        (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.generatorState
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.representativeHead state)) =
      state
    := by
  let offset : Fin 64 := ⟨state.val - 2624, by omega⟩
  have state_eq :
      (⟨2624 + offset.val, by omega⟩ : Fin 2712) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0041 offset

set_option maxHeartbeats 2000000 in
theorem representativeStateBounded0042 :
    ∀ candidate : Fin 24,
      (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.representativeTail (⟨2688 + candidate.val, by omega⟩ : Fin 2712)).foldl
          SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.transition
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.generatorState
            (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.representativeHead (⟨2688 + candidate.val, by omega⟩ : Fin 2712))) =
        (⟨2688 + candidate.val, by omega⟩ : Fin 2712)
    := by
  decide

theorem representativeStateProof0042
    (state : Fin 2712)
    (lower : 2688 ≤ state.val)
    (upper : state.val < 2712) :
    (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.representativeTail state).foldl
        SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.transition
        (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.generatorState
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.representativeHead state)) =
      state
    := by
  let offset : Fin 24 := ⟨state.val - 2688, by omega⟩
  have state_eq :
      (⟨2688 + offset.val, by omega⟩ : Fin 2712) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact representativeStateBounded0042 offset

end SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.Shards
