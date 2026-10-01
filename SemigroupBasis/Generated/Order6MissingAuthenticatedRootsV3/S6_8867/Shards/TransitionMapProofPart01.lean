import SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.Support.Core
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.Shards

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0032 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 4,
    ∀ coordinate : Fin 29,
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.stateVector
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.transition (⟨2048 + candidate.val, by omega⟩ : Fin 2712) generator)
          coordinate =
        SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.stateVector (⟨2048 + candidate.val, by omega⟩ : Fin 2712) coordinate)
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0032
    (state : Fin 2712)
    (lower : 2048 ≤ state.val)
    (upper : state.val < 2112)
    (generator : Fin 4)
    (coordinate : Fin 29) :
    SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.stateVector (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 2048, by omega⟩
  have state_eq :
      (⟨2048 + offset.val, by omega⟩ : Fin 2712) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0032 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0033 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 4,
    ∀ coordinate : Fin 29,
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.stateVector
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.transition (⟨2112 + candidate.val, by omega⟩ : Fin 2712) generator)
          coordinate =
        SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.stateVector (⟨2112 + candidate.val, by omega⟩ : Fin 2712) coordinate)
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0033
    (state : Fin 2712)
    (lower : 2112 ≤ state.val)
    (upper : state.val < 2176)
    (generator : Fin 4)
    (coordinate : Fin 29) :
    SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.stateVector (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 2112, by omega⟩
  have state_eq :
      (⟨2112 + offset.val, by omega⟩ : Fin 2712) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0033 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0034 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 4,
    ∀ coordinate : Fin 29,
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.stateVector
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.transition (⟨2176 + candidate.val, by omega⟩ : Fin 2712) generator)
          coordinate =
        SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.stateVector (⟨2176 + candidate.val, by omega⟩ : Fin 2712) coordinate)
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0034
    (state : Fin 2712)
    (lower : 2176 ≤ state.val)
    (upper : state.val < 2240)
    (generator : Fin 4)
    (coordinate : Fin 29) :
    SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.stateVector (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 2176, by omega⟩
  have state_eq :
      (⟨2176 + offset.val, by omega⟩ : Fin 2712) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0034 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0035 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 4,
    ∀ coordinate : Fin 29,
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.stateVector
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.transition (⟨2240 + candidate.val, by omega⟩ : Fin 2712) generator)
          coordinate =
        SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.stateVector (⟨2240 + candidate.val, by omega⟩ : Fin 2712) coordinate)
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0035
    (state : Fin 2712)
    (lower : 2240 ≤ state.val)
    (upper : state.val < 2304)
    (generator : Fin 4)
    (coordinate : Fin 29) :
    SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.stateVector (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 2240, by omega⟩
  have state_eq :
      (⟨2240 + offset.val, by omega⟩ : Fin 2712) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0035 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0036 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 4,
    ∀ coordinate : Fin 29,
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.stateVector
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.transition (⟨2304 + candidate.val, by omega⟩ : Fin 2712) generator)
          coordinate =
        SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.stateVector (⟨2304 + candidate.val, by omega⟩ : Fin 2712) coordinate)
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0036
    (state : Fin 2712)
    (lower : 2304 ≤ state.val)
    (upper : state.val < 2368)
    (generator : Fin 4)
    (coordinate : Fin 29) :
    SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.stateVector (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 2304, by omega⟩
  have state_eq :
      (⟨2304 + offset.val, by omega⟩ : Fin 2712) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0036 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0037 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 4,
    ∀ coordinate : Fin 29,
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.stateVector
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.transition (⟨2368 + candidate.val, by omega⟩ : Fin 2712) generator)
          coordinate =
        SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.stateVector (⟨2368 + candidate.val, by omega⟩ : Fin 2712) coordinate)
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0037
    (state : Fin 2712)
    (lower : 2368 ≤ state.val)
    (upper : state.val < 2432)
    (generator : Fin 4)
    (coordinate : Fin 29) :
    SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.stateVector (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 2368, by omega⟩
  have state_eq :
      (⟨2368 + offset.val, by omega⟩ : Fin 2712) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0037 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0038 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 4,
    ∀ coordinate : Fin 29,
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.stateVector
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.transition (⟨2432 + candidate.val, by omega⟩ : Fin 2712) generator)
          coordinate =
        SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.stateVector (⟨2432 + candidate.val, by omega⟩ : Fin 2712) coordinate)
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0038
    (state : Fin 2712)
    (lower : 2432 ≤ state.val)
    (upper : state.val < 2496)
    (generator : Fin 4)
    (coordinate : Fin 29) :
    SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.stateVector (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 2432, by omega⟩
  have state_eq :
      (⟨2432 + offset.val, by omega⟩ : Fin 2712) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0038 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0039 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 4,
    ∀ coordinate : Fin 29,
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.stateVector
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.transition (⟨2496 + candidate.val, by omega⟩ : Fin 2712) generator)
          coordinate =
        SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.stateVector (⟨2496 + candidate.val, by omega⟩ : Fin 2712) coordinate)
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0039
    (state : Fin 2712)
    (lower : 2496 ≤ state.val)
    (upper : state.val < 2560)
    (generator : Fin 4)
    (coordinate : Fin 29) :
    SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.stateVector (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 2496, by omega⟩
  have state_eq :
      (⟨2496 + offset.val, by omega⟩ : Fin 2712) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0039 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0040 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 4,
    ∀ coordinate : Fin 29,
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.stateVector
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.transition (⟨2560 + candidate.val, by omega⟩ : Fin 2712) generator)
          coordinate =
        SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.stateVector (⟨2560 + candidate.val, by omega⟩ : Fin 2712) coordinate)
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0040
    (state : Fin 2712)
    (lower : 2560 ≤ state.val)
    (upper : state.val < 2624)
    (generator : Fin 4)
    (coordinate : Fin 29) :
    SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.stateVector (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 2560, by omega⟩
  have state_eq :
      (⟨2560 + offset.val, by omega⟩ : Fin 2712) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0040 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0041 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 4,
    ∀ coordinate : Fin 29,
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.stateVector
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.transition (⟨2624 + candidate.val, by omega⟩ : Fin 2712) generator)
          coordinate =
        SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.stateVector (⟨2624 + candidate.val, by omega⟩ : Fin 2712) coordinate)
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0041
    (state : Fin 2712)
    (lower : 2624 ≤ state.val)
    (upper : state.val < 2688)
    (generator : Fin 4)
    (coordinate : Fin 29) :
    SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.stateVector (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 2624, by omega⟩
  have state_eq :
      (⟨2624 + offset.val, by omega⟩ : Fin 2712) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0041 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0042 :
    ∀ candidate : Fin 24,
    ∀ generator : Fin 4,
    ∀ coordinate : Fin 29,
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.stateVector
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.transition (⟨2688 + candidate.val, by omega⟩ : Fin 2712) generator)
          coordinate =
        SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.stateVector (⟨2688 + candidate.val, by omega⟩ : Fin 2712) coordinate)
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0042
    (state : Fin 2712)
    (lower : 2688 ≤ state.val)
    (upper : state.val < 2712)
    (generator : Fin 4)
    (coordinate : Fin 29) :
    SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.stateVector (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.generatorVector generator coordinate)
    := by
  let offset : Fin 24 := ⟨state.val - 2688, by omega⟩
  have state_eq :
      (⟨2688 + offset.val, by omega⟩ : Fin 2712) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0042 offset generator coordinate

end SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.Shards
