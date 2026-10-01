import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.Support.Core
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.Shards

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0256 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 46,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition (⟨16384 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.stateVector (⟨16384 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0256
    (state : Fin 17622)
    (lower : 16384 ≤ state.val)
    (upper : state.val < 16448)
    (generator : Fin 6)
    (coordinate : Fin 46) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 16384, by omega⟩
  have state_eq :
      (⟨16384 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0256 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0257 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 46,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition (⟨16448 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.stateVector (⟨16448 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0257
    (state : Fin 17622)
    (lower : 16448 ≤ state.val)
    (upper : state.val < 16512)
    (generator : Fin 6)
    (coordinate : Fin 46) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 16448, by omega⟩
  have state_eq :
      (⟨16448 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0257 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0258 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 46,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition (⟨16512 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.stateVector (⟨16512 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0258
    (state : Fin 17622)
    (lower : 16512 ≤ state.val)
    (upper : state.val < 16576)
    (generator : Fin 6)
    (coordinate : Fin 46) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 16512, by omega⟩
  have state_eq :
      (⟨16512 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0258 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0259 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 46,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition (⟨16576 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.stateVector (⟨16576 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0259
    (state : Fin 17622)
    (lower : 16576 ≤ state.val)
    (upper : state.val < 16640)
    (generator : Fin 6)
    (coordinate : Fin 46) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 16576, by omega⟩
  have state_eq :
      (⟨16576 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0259 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0260 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 46,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition (⟨16640 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.stateVector (⟨16640 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0260
    (state : Fin 17622)
    (lower : 16640 ≤ state.val)
    (upper : state.val < 16704)
    (generator : Fin 6)
    (coordinate : Fin 46) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 16640, by omega⟩
  have state_eq :
      (⟨16640 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0260 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0261 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 46,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition (⟨16704 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.stateVector (⟨16704 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0261
    (state : Fin 17622)
    (lower : 16704 ≤ state.val)
    (upper : state.val < 16768)
    (generator : Fin 6)
    (coordinate : Fin 46) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 16704, by omega⟩
  have state_eq :
      (⟨16704 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0261 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0262 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 46,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition (⟨16768 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.stateVector (⟨16768 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0262
    (state : Fin 17622)
    (lower : 16768 ≤ state.val)
    (upper : state.val < 16832)
    (generator : Fin 6)
    (coordinate : Fin 46) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 16768, by omega⟩
  have state_eq :
      (⟨16768 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0262 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0263 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 46,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition (⟨16832 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.stateVector (⟨16832 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0263
    (state : Fin 17622)
    (lower : 16832 ≤ state.val)
    (upper : state.val < 16896)
    (generator : Fin 6)
    (coordinate : Fin 46) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 16832, by omega⟩
  have state_eq :
      (⟨16832 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0263 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0264 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 46,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition (⟨16896 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.stateVector (⟨16896 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0264
    (state : Fin 17622)
    (lower : 16896 ≤ state.val)
    (upper : state.val < 16960)
    (generator : Fin 6)
    (coordinate : Fin 46) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 16896, by omega⟩
  have state_eq :
      (⟨16896 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0264 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0265 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 46,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition (⟨16960 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.stateVector (⟨16960 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0265
    (state : Fin 17622)
    (lower : 16960 ≤ state.val)
    (upper : state.val < 17024)
    (generator : Fin 6)
    (coordinate : Fin 46) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 16960, by omega⟩
  have state_eq :
      (⟨16960 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0265 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0266 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 46,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition (⟨17024 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.stateVector (⟨17024 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0266
    (state : Fin 17622)
    (lower : 17024 ≤ state.val)
    (upper : state.val < 17088)
    (generator : Fin 6)
    (coordinate : Fin 46) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 17024, by omega⟩
  have state_eq :
      (⟨17024 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0266 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0267 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 46,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition (⟨17088 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.stateVector (⟨17088 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0267
    (state : Fin 17622)
    (lower : 17088 ≤ state.val)
    (upper : state.val < 17152)
    (generator : Fin 6)
    (coordinate : Fin 46) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 17088, by omega⟩
  have state_eq :
      (⟨17088 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0267 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0268 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 46,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition (⟨17152 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.stateVector (⟨17152 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0268
    (state : Fin 17622)
    (lower : 17152 ≤ state.val)
    (upper : state.val < 17216)
    (generator : Fin 6)
    (coordinate : Fin 46) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 17152, by omega⟩
  have state_eq :
      (⟨17152 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0268 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0269 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 46,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition (⟨17216 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.stateVector (⟨17216 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0269
    (state : Fin 17622)
    (lower : 17216 ≤ state.val)
    (upper : state.val < 17280)
    (generator : Fin 6)
    (coordinate : Fin 46) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 17216, by omega⟩
  have state_eq :
      (⟨17216 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0269 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0270 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 46,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition (⟨17280 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.stateVector (⟨17280 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0270
    (state : Fin 17622)
    (lower : 17280 ≤ state.val)
    (upper : state.val < 17344)
    (generator : Fin 6)
    (coordinate : Fin 46) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 17280, by omega⟩
  have state_eq :
      (⟨17280 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0270 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0271 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 46,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition (⟨17344 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.stateVector (⟨17344 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0271
    (state : Fin 17622)
    (lower : 17344 ≤ state.val)
    (upper : state.val < 17408)
    (generator : Fin 6)
    (coordinate : Fin 46) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 17344, by omega⟩
  have state_eq :
      (⟨17344 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0271 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0272 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 46,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition (⟨17408 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.stateVector (⟨17408 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0272
    (state : Fin 17622)
    (lower : 17408 ≤ state.val)
    (upper : state.val < 17472)
    (generator : Fin 6)
    (coordinate : Fin 46) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 17408, by omega⟩
  have state_eq :
      (⟨17408 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0272 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0273 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 46,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition (⟨17472 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.stateVector (⟨17472 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0273
    (state : Fin 17622)
    (lower : 17472 ≤ state.val)
    (upper : state.val < 17536)
    (generator : Fin 6)
    (coordinate : Fin 46) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 17472, by omega⟩
  have state_eq :
      (⟨17472 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0273 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0274 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 46,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition (⟨17536 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.stateVector (⟨17536 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0274
    (state : Fin 17622)
    (lower : 17536 ≤ state.val)
    (upper : state.val < 17600)
    (generator : Fin 6)
    (coordinate : Fin 46) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 17536, by omega⟩
  have state_eq :
      (⟨17536 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0274 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0275 :
    ∀ candidate : Fin 22,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 46,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition (⟨17600 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.stateVector (⟨17600 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0275
    (state : Fin 17622)
    (lower : 17600 ≤ state.val)
    (upper : state.val < 17622)
    (generator : Fin 6)
    (coordinate : Fin 46) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorVector generator coordinate)
    := by
  let offset : Fin 22 := ⟨state.val - 17600, by omega⟩
  have state_eq :
      (⟨17600 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0275 offset generator coordinate

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.Shards
