import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.Support.Core
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.Shards

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0032 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 39,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition (⟨2048 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector (⟨2048 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0032
    (state : Fin 17622)
    (lower : 2048 ≤ state.val)
    (upper : state.val < 2112)
    (generator : Fin 6)
    (coordinate : Fin 39) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 2048, by omega⟩
  have state_eq :
      (⟨2048 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0032 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0033 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 39,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition (⟨2112 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector (⟨2112 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0033
    (state : Fin 17622)
    (lower : 2112 ≤ state.val)
    (upper : state.val < 2176)
    (generator : Fin 6)
    (coordinate : Fin 39) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 2112, by omega⟩
  have state_eq :
      (⟨2112 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0033 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0034 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 39,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition (⟨2176 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector (⟨2176 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0034
    (state : Fin 17622)
    (lower : 2176 ≤ state.val)
    (upper : state.val < 2240)
    (generator : Fin 6)
    (coordinate : Fin 39) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 2176, by omega⟩
  have state_eq :
      (⟨2176 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0034 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0035 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 39,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition (⟨2240 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector (⟨2240 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0035
    (state : Fin 17622)
    (lower : 2240 ≤ state.val)
    (upper : state.val < 2304)
    (generator : Fin 6)
    (coordinate : Fin 39) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 2240, by omega⟩
  have state_eq :
      (⟨2240 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0035 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0036 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 39,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition (⟨2304 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector (⟨2304 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0036
    (state : Fin 17622)
    (lower : 2304 ≤ state.val)
    (upper : state.val < 2368)
    (generator : Fin 6)
    (coordinate : Fin 39) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 2304, by omega⟩
  have state_eq :
      (⟨2304 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0036 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0037 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 39,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition (⟨2368 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector (⟨2368 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0037
    (state : Fin 17622)
    (lower : 2368 ≤ state.val)
    (upper : state.val < 2432)
    (generator : Fin 6)
    (coordinate : Fin 39) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 2368, by omega⟩
  have state_eq :
      (⟨2368 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0037 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0038 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 39,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition (⟨2432 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector (⟨2432 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0038
    (state : Fin 17622)
    (lower : 2432 ≤ state.val)
    (upper : state.val < 2496)
    (generator : Fin 6)
    (coordinate : Fin 39) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 2432, by omega⟩
  have state_eq :
      (⟨2432 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0038 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0039 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 39,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition (⟨2496 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector (⟨2496 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0039
    (state : Fin 17622)
    (lower : 2496 ≤ state.val)
    (upper : state.val < 2560)
    (generator : Fin 6)
    (coordinate : Fin 39) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 2496, by omega⟩
  have state_eq :
      (⟨2496 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0039 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0040 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 39,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition (⟨2560 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector (⟨2560 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0040
    (state : Fin 17622)
    (lower : 2560 ≤ state.val)
    (upper : state.val < 2624)
    (generator : Fin 6)
    (coordinate : Fin 39) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 2560, by omega⟩
  have state_eq :
      (⟨2560 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0040 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0041 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 39,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition (⟨2624 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector (⟨2624 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0041
    (state : Fin 17622)
    (lower : 2624 ≤ state.val)
    (upper : state.val < 2688)
    (generator : Fin 6)
    (coordinate : Fin 39) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 2624, by omega⟩
  have state_eq :
      (⟨2624 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0041 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0042 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 39,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition (⟨2688 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector (⟨2688 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0042
    (state : Fin 17622)
    (lower : 2688 ≤ state.val)
    (upper : state.val < 2752)
    (generator : Fin 6)
    (coordinate : Fin 39) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 2688, by omega⟩
  have state_eq :
      (⟨2688 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0042 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0043 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 39,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition (⟨2752 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector (⟨2752 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0043
    (state : Fin 17622)
    (lower : 2752 ≤ state.val)
    (upper : state.val < 2816)
    (generator : Fin 6)
    (coordinate : Fin 39) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 2752, by omega⟩
  have state_eq :
      (⟨2752 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0043 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0044 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 39,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition (⟨2816 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector (⟨2816 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0044
    (state : Fin 17622)
    (lower : 2816 ≤ state.val)
    (upper : state.val < 2880)
    (generator : Fin 6)
    (coordinate : Fin 39) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 2816, by omega⟩
  have state_eq :
      (⟨2816 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0044 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0045 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 39,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition (⟨2880 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector (⟨2880 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0045
    (state : Fin 17622)
    (lower : 2880 ≤ state.val)
    (upper : state.val < 2944)
    (generator : Fin 6)
    (coordinate : Fin 39) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 2880, by omega⟩
  have state_eq :
      (⟨2880 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0045 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0046 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 39,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition (⟨2944 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector (⟨2944 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0046
    (state : Fin 17622)
    (lower : 2944 ≤ state.val)
    (upper : state.val < 3008)
    (generator : Fin 6)
    (coordinate : Fin 39) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 2944, by omega⟩
  have state_eq :
      (⟨2944 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0046 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0047 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 39,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition (⟨3008 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector (⟨3008 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0047
    (state : Fin 17622)
    (lower : 3008 ≤ state.val)
    (upper : state.val < 3072)
    (generator : Fin 6)
    (coordinate : Fin 39) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 3008, by omega⟩
  have state_eq :
      (⟨3008 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0047 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0048 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 39,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition (⟨3072 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector (⟨3072 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0048
    (state : Fin 17622)
    (lower : 3072 ≤ state.val)
    (upper : state.val < 3136)
    (generator : Fin 6)
    (coordinate : Fin 39) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 3072, by omega⟩
  have state_eq :
      (⟨3072 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0048 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0049 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 39,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition (⟨3136 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector (⟨3136 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0049
    (state : Fin 17622)
    (lower : 3136 ≤ state.val)
    (upper : state.val < 3200)
    (generator : Fin 6)
    (coordinate : Fin 39) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 3136, by omega⟩
  have state_eq :
      (⟨3136 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0049 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0050 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 39,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition (⟨3200 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector (⟨3200 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0050
    (state : Fin 17622)
    (lower : 3200 ≤ state.val)
    (upper : state.val < 3264)
    (generator : Fin 6)
    (coordinate : Fin 39) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 3200, by omega⟩
  have state_eq :
      (⟨3200 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0050 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0051 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 39,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition (⟨3264 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector (⟨3264 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0051
    (state : Fin 17622)
    (lower : 3264 ≤ state.val)
    (upper : state.val < 3328)
    (generator : Fin 6)
    (coordinate : Fin 39) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 3264, by omega⟩
  have state_eq :
      (⟨3264 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0051 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0052 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 39,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition (⟨3328 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector (⟨3328 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0052
    (state : Fin 17622)
    (lower : 3328 ≤ state.val)
    (upper : state.val < 3392)
    (generator : Fin 6)
    (coordinate : Fin 39) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 3328, by omega⟩
  have state_eq :
      (⟨3328 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0052 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0053 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 39,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition (⟨3392 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector (⟨3392 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0053
    (state : Fin 17622)
    (lower : 3392 ≤ state.val)
    (upper : state.val < 3456)
    (generator : Fin 6)
    (coordinate : Fin 39) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 3392, by omega⟩
  have state_eq :
      (⟨3392 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0053 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0054 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 39,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition (⟨3456 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector (⟨3456 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0054
    (state : Fin 17622)
    (lower : 3456 ≤ state.val)
    (upper : state.val < 3520)
    (generator : Fin 6)
    (coordinate : Fin 39) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 3456, by omega⟩
  have state_eq :
      (⟨3456 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0054 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0055 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 39,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition (⟨3520 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector (⟨3520 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0055
    (state : Fin 17622)
    (lower : 3520 ≤ state.val)
    (upper : state.val < 3584)
    (generator : Fin 6)
    (coordinate : Fin 39) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 3520, by omega⟩
  have state_eq :
      (⟨3520 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0055 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0056 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 39,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition (⟨3584 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector (⟨3584 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0056
    (state : Fin 17622)
    (lower : 3584 ≤ state.val)
    (upper : state.val < 3648)
    (generator : Fin 6)
    (coordinate : Fin 39) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 3584, by omega⟩
  have state_eq :
      (⟨3584 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0056 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0057 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 39,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition (⟨3648 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector (⟨3648 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0057
    (state : Fin 17622)
    (lower : 3648 ≤ state.val)
    (upper : state.val < 3712)
    (generator : Fin 6)
    (coordinate : Fin 39) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 3648, by omega⟩
  have state_eq :
      (⟨3648 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0057 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0058 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 39,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition (⟨3712 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector (⟨3712 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0058
    (state : Fin 17622)
    (lower : 3712 ≤ state.val)
    (upper : state.val < 3776)
    (generator : Fin 6)
    (coordinate : Fin 39) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 3712, by omega⟩
  have state_eq :
      (⟨3712 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0058 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0059 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 39,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition (⟨3776 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector (⟨3776 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0059
    (state : Fin 17622)
    (lower : 3776 ≤ state.val)
    (upper : state.val < 3840)
    (generator : Fin 6)
    (coordinate : Fin 39) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 3776, by omega⟩
  have state_eq :
      (⟨3776 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0059 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0060 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 39,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition (⟨3840 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector (⟨3840 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0060
    (state : Fin 17622)
    (lower : 3840 ≤ state.val)
    (upper : state.val < 3904)
    (generator : Fin 6)
    (coordinate : Fin 39) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 3840, by omega⟩
  have state_eq :
      (⟨3840 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0060 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0061 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 39,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition (⟨3904 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector (⟨3904 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0061
    (state : Fin 17622)
    (lower : 3904 ≤ state.val)
    (upper : state.val < 3968)
    (generator : Fin 6)
    (coordinate : Fin 39) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 3904, by omega⟩
  have state_eq :
      (⟨3904 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0061 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0062 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 39,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition (⟨3968 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector (⟨3968 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0062
    (state : Fin 17622)
    (lower : 3968 ≤ state.val)
    (upper : state.val < 4032)
    (generator : Fin 6)
    (coordinate : Fin 39) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 3968, by omega⟩
  have state_eq :
      (⟨3968 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0062 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0063 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 39,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition (⟨4032 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector (⟨4032 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0063
    (state : Fin 17622)
    (lower : 4032 ≤ state.val)
    (upper : state.val < 4096)
    (generator : Fin 6)
    (coordinate : Fin 39) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 4032, by omega⟩
  have state_eq :
      (⟨4032 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0063 offset generator coordinate

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.Shards
