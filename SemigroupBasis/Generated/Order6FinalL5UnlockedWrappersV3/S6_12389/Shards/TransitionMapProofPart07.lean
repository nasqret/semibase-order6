import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.Support.Core
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.Shards

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0224 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 56,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition (⟨14336 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector (⟨14336 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0224
    (state : Fin 17622)
    (lower : 14336 ≤ state.val)
    (upper : state.val < 14400)
    (generator : Fin 6)
    (coordinate : Fin 56) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 14336, by omega⟩
  have state_eq :
      (⟨14336 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0224 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0225 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 56,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition (⟨14400 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector (⟨14400 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0225
    (state : Fin 17622)
    (lower : 14400 ≤ state.val)
    (upper : state.val < 14464)
    (generator : Fin 6)
    (coordinate : Fin 56) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 14400, by omega⟩
  have state_eq :
      (⟨14400 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0225 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0226 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 56,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition (⟨14464 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector (⟨14464 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0226
    (state : Fin 17622)
    (lower : 14464 ≤ state.val)
    (upper : state.val < 14528)
    (generator : Fin 6)
    (coordinate : Fin 56) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 14464, by omega⟩
  have state_eq :
      (⟨14464 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0226 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0227 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 56,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition (⟨14528 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector (⟨14528 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0227
    (state : Fin 17622)
    (lower : 14528 ≤ state.val)
    (upper : state.val < 14592)
    (generator : Fin 6)
    (coordinate : Fin 56) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 14528, by omega⟩
  have state_eq :
      (⟨14528 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0227 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0228 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 56,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition (⟨14592 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector (⟨14592 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0228
    (state : Fin 17622)
    (lower : 14592 ≤ state.val)
    (upper : state.val < 14656)
    (generator : Fin 6)
    (coordinate : Fin 56) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 14592, by omega⟩
  have state_eq :
      (⟨14592 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0228 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0229 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 56,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition (⟨14656 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector (⟨14656 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0229
    (state : Fin 17622)
    (lower : 14656 ≤ state.val)
    (upper : state.val < 14720)
    (generator : Fin 6)
    (coordinate : Fin 56) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 14656, by omega⟩
  have state_eq :
      (⟨14656 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0229 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0230 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 56,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition (⟨14720 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector (⟨14720 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0230
    (state : Fin 17622)
    (lower : 14720 ≤ state.val)
    (upper : state.val < 14784)
    (generator : Fin 6)
    (coordinate : Fin 56) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 14720, by omega⟩
  have state_eq :
      (⟨14720 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0230 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0231 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 56,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition (⟨14784 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector (⟨14784 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0231
    (state : Fin 17622)
    (lower : 14784 ≤ state.val)
    (upper : state.val < 14848)
    (generator : Fin 6)
    (coordinate : Fin 56) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 14784, by omega⟩
  have state_eq :
      (⟨14784 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0231 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0232 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 56,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition (⟨14848 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector (⟨14848 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0232
    (state : Fin 17622)
    (lower : 14848 ≤ state.val)
    (upper : state.val < 14912)
    (generator : Fin 6)
    (coordinate : Fin 56) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 14848, by omega⟩
  have state_eq :
      (⟨14848 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0232 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0233 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 56,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition (⟨14912 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector (⟨14912 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0233
    (state : Fin 17622)
    (lower : 14912 ≤ state.val)
    (upper : state.val < 14976)
    (generator : Fin 6)
    (coordinate : Fin 56) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 14912, by omega⟩
  have state_eq :
      (⟨14912 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0233 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0234 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 56,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition (⟨14976 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector (⟨14976 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0234
    (state : Fin 17622)
    (lower : 14976 ≤ state.val)
    (upper : state.val < 15040)
    (generator : Fin 6)
    (coordinate : Fin 56) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 14976, by omega⟩
  have state_eq :
      (⟨14976 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0234 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0235 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 56,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition (⟨15040 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector (⟨15040 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0235
    (state : Fin 17622)
    (lower : 15040 ≤ state.val)
    (upper : state.val < 15104)
    (generator : Fin 6)
    (coordinate : Fin 56) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 15040, by omega⟩
  have state_eq :
      (⟨15040 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0235 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0236 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 56,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition (⟨15104 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector (⟨15104 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0236
    (state : Fin 17622)
    (lower : 15104 ≤ state.val)
    (upper : state.val < 15168)
    (generator : Fin 6)
    (coordinate : Fin 56) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 15104, by omega⟩
  have state_eq :
      (⟨15104 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0236 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0237 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 56,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition (⟨15168 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector (⟨15168 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0237
    (state : Fin 17622)
    (lower : 15168 ≤ state.val)
    (upper : state.val < 15232)
    (generator : Fin 6)
    (coordinate : Fin 56) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 15168, by omega⟩
  have state_eq :
      (⟨15168 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0237 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0238 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 56,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition (⟨15232 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector (⟨15232 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0238
    (state : Fin 17622)
    (lower : 15232 ≤ state.val)
    (upper : state.val < 15296)
    (generator : Fin 6)
    (coordinate : Fin 56) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 15232, by omega⟩
  have state_eq :
      (⟨15232 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0238 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0239 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 56,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition (⟨15296 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector (⟨15296 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0239
    (state : Fin 17622)
    (lower : 15296 ≤ state.val)
    (upper : state.val < 15360)
    (generator : Fin 6)
    (coordinate : Fin 56) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 15296, by omega⟩
  have state_eq :
      (⟨15296 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0239 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0240 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 56,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition (⟨15360 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector (⟨15360 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0240
    (state : Fin 17622)
    (lower : 15360 ≤ state.val)
    (upper : state.val < 15424)
    (generator : Fin 6)
    (coordinate : Fin 56) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 15360, by omega⟩
  have state_eq :
      (⟨15360 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0240 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0241 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 56,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition (⟨15424 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector (⟨15424 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0241
    (state : Fin 17622)
    (lower : 15424 ≤ state.val)
    (upper : state.val < 15488)
    (generator : Fin 6)
    (coordinate : Fin 56) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 15424, by omega⟩
  have state_eq :
      (⟨15424 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0241 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0242 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 56,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition (⟨15488 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector (⟨15488 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0242
    (state : Fin 17622)
    (lower : 15488 ≤ state.val)
    (upper : state.val < 15552)
    (generator : Fin 6)
    (coordinate : Fin 56) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 15488, by omega⟩
  have state_eq :
      (⟨15488 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0242 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0243 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 56,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition (⟨15552 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector (⟨15552 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0243
    (state : Fin 17622)
    (lower : 15552 ≤ state.val)
    (upper : state.val < 15616)
    (generator : Fin 6)
    (coordinate : Fin 56) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 15552, by omega⟩
  have state_eq :
      (⟨15552 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0243 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0244 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 56,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition (⟨15616 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector (⟨15616 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0244
    (state : Fin 17622)
    (lower : 15616 ≤ state.val)
    (upper : state.val < 15680)
    (generator : Fin 6)
    (coordinate : Fin 56) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 15616, by omega⟩
  have state_eq :
      (⟨15616 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0244 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0245 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 56,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition (⟨15680 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector (⟨15680 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0245
    (state : Fin 17622)
    (lower : 15680 ≤ state.val)
    (upper : state.val < 15744)
    (generator : Fin 6)
    (coordinate : Fin 56) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 15680, by omega⟩
  have state_eq :
      (⟨15680 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0245 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0246 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 56,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition (⟨15744 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector (⟨15744 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0246
    (state : Fin 17622)
    (lower : 15744 ≤ state.val)
    (upper : state.val < 15808)
    (generator : Fin 6)
    (coordinate : Fin 56) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 15744, by omega⟩
  have state_eq :
      (⟨15744 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0246 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0247 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 56,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition (⟨15808 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector (⟨15808 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0247
    (state : Fin 17622)
    (lower : 15808 ≤ state.val)
    (upper : state.val < 15872)
    (generator : Fin 6)
    (coordinate : Fin 56) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 15808, by omega⟩
  have state_eq :
      (⟨15808 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0247 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0248 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 56,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition (⟨15872 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector (⟨15872 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0248
    (state : Fin 17622)
    (lower : 15872 ≤ state.val)
    (upper : state.val < 15936)
    (generator : Fin 6)
    (coordinate : Fin 56) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 15872, by omega⟩
  have state_eq :
      (⟨15872 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0248 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0249 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 56,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition (⟨15936 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector (⟨15936 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0249
    (state : Fin 17622)
    (lower : 15936 ≤ state.val)
    (upper : state.val < 16000)
    (generator : Fin 6)
    (coordinate : Fin 56) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 15936, by omega⟩
  have state_eq :
      (⟨15936 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0249 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0250 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 56,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition (⟨16000 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector (⟨16000 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0250
    (state : Fin 17622)
    (lower : 16000 ≤ state.val)
    (upper : state.val < 16064)
    (generator : Fin 6)
    (coordinate : Fin 56) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 16000, by omega⟩
  have state_eq :
      (⟨16000 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0250 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0251 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 56,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition (⟨16064 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector (⟨16064 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0251
    (state : Fin 17622)
    (lower : 16064 ≤ state.val)
    (upper : state.val < 16128)
    (generator : Fin 6)
    (coordinate : Fin 56) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 16064, by omega⟩
  have state_eq :
      (⟨16064 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0251 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0252 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 56,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition (⟨16128 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector (⟨16128 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0252
    (state : Fin 17622)
    (lower : 16128 ≤ state.val)
    (upper : state.val < 16192)
    (generator : Fin 6)
    (coordinate : Fin 56) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 16128, by omega⟩
  have state_eq :
      (⟨16128 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0252 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0253 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 56,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition (⟨16192 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector (⟨16192 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0253
    (state : Fin 17622)
    (lower : 16192 ≤ state.val)
    (upper : state.val < 16256)
    (generator : Fin 6)
    (coordinate : Fin 56) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 16192, by omega⟩
  have state_eq :
      (⟨16192 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0253 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0254 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 56,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition (⟨16256 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector (⟨16256 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0254
    (state : Fin 17622)
    (lower : 16256 ≤ state.val)
    (upper : state.val < 16320)
    (generator : Fin 6)
    (coordinate : Fin 56) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 16256, by omega⟩
  have state_eq :
      (⟨16256 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0254 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0255 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 56,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition (⟨16320 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector (⟨16320 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0255
    (state : Fin 17622)
    (lower : 16320 ≤ state.val)
    (upper : state.val < 16384)
    (generator : Fin 6)
    (coordinate : Fin 56) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 16320, by omega⟩
  have state_eq :
      (⟨16320 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0255 offset generator coordinate

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.Shards
