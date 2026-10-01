import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Support.Core
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0352 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨22528 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨22528 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0352
    (state : Fin 48684)
    (lower : 22528 ≤ state.val)
    (upper : state.val < 22592)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 22528, by omega⟩
  have state_eq :
      (⟨22528 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0352 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0353 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨22592 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨22592 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0353
    (state : Fin 48684)
    (lower : 22592 ≤ state.val)
    (upper : state.val < 22656)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 22592, by omega⟩
  have state_eq :
      (⟨22592 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0353 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0354 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨22656 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨22656 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0354
    (state : Fin 48684)
    (lower : 22656 ≤ state.val)
    (upper : state.val < 22720)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 22656, by omega⟩
  have state_eq :
      (⟨22656 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0354 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0355 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨22720 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨22720 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0355
    (state : Fin 48684)
    (lower : 22720 ≤ state.val)
    (upper : state.val < 22784)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 22720, by omega⟩
  have state_eq :
      (⟨22720 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0355 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0356 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨22784 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨22784 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0356
    (state : Fin 48684)
    (lower : 22784 ≤ state.val)
    (upper : state.val < 22848)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 22784, by omega⟩
  have state_eq :
      (⟨22784 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0356 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0357 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨22848 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨22848 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0357
    (state : Fin 48684)
    (lower : 22848 ≤ state.val)
    (upper : state.val < 22912)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 22848, by omega⟩
  have state_eq :
      (⟨22848 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0357 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0358 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨22912 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨22912 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0358
    (state : Fin 48684)
    (lower : 22912 ≤ state.val)
    (upper : state.val < 22976)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 22912, by omega⟩
  have state_eq :
      (⟨22912 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0358 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0359 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨22976 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨22976 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0359
    (state : Fin 48684)
    (lower : 22976 ≤ state.val)
    (upper : state.val < 23040)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 22976, by omega⟩
  have state_eq :
      (⟨22976 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0359 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0360 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨23040 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨23040 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0360
    (state : Fin 48684)
    (lower : 23040 ≤ state.val)
    (upper : state.val < 23104)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 23040, by omega⟩
  have state_eq :
      (⟨23040 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0360 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0361 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨23104 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨23104 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0361
    (state : Fin 48684)
    (lower : 23104 ≤ state.val)
    (upper : state.val < 23168)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 23104, by omega⟩
  have state_eq :
      (⟨23104 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0361 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0362 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨23168 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨23168 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0362
    (state : Fin 48684)
    (lower : 23168 ≤ state.val)
    (upper : state.val < 23232)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 23168, by omega⟩
  have state_eq :
      (⟨23168 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0362 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0363 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨23232 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨23232 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0363
    (state : Fin 48684)
    (lower : 23232 ≤ state.val)
    (upper : state.val < 23296)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 23232, by omega⟩
  have state_eq :
      (⟨23232 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0363 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0364 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨23296 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨23296 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0364
    (state : Fin 48684)
    (lower : 23296 ≤ state.val)
    (upper : state.val < 23360)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 23296, by omega⟩
  have state_eq :
      (⟨23296 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0364 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0365 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨23360 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨23360 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0365
    (state : Fin 48684)
    (lower : 23360 ≤ state.val)
    (upper : state.val < 23424)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 23360, by omega⟩
  have state_eq :
      (⟨23360 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0365 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0366 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨23424 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨23424 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0366
    (state : Fin 48684)
    (lower : 23424 ≤ state.val)
    (upper : state.val < 23488)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 23424, by omega⟩
  have state_eq :
      (⟨23424 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0366 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0367 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨23488 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨23488 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0367
    (state : Fin 48684)
    (lower : 23488 ≤ state.val)
    (upper : state.val < 23552)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 23488, by omega⟩
  have state_eq :
      (⟨23488 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0367 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0368 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨23552 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨23552 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0368
    (state : Fin 48684)
    (lower : 23552 ≤ state.val)
    (upper : state.val < 23616)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 23552, by omega⟩
  have state_eq :
      (⟨23552 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0368 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0369 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨23616 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨23616 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0369
    (state : Fin 48684)
    (lower : 23616 ≤ state.val)
    (upper : state.val < 23680)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 23616, by omega⟩
  have state_eq :
      (⟨23616 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0369 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0370 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨23680 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨23680 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0370
    (state : Fin 48684)
    (lower : 23680 ≤ state.val)
    (upper : state.val < 23744)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 23680, by omega⟩
  have state_eq :
      (⟨23680 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0370 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0371 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨23744 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨23744 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0371
    (state : Fin 48684)
    (lower : 23744 ≤ state.val)
    (upper : state.val < 23808)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 23744, by omega⟩
  have state_eq :
      (⟨23744 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0371 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0372 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨23808 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨23808 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0372
    (state : Fin 48684)
    (lower : 23808 ≤ state.val)
    (upper : state.val < 23872)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 23808, by omega⟩
  have state_eq :
      (⟨23808 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0372 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0373 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨23872 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨23872 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0373
    (state : Fin 48684)
    (lower : 23872 ≤ state.val)
    (upper : state.val < 23936)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 23872, by omega⟩
  have state_eq :
      (⟨23872 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0373 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0374 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨23936 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨23936 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0374
    (state : Fin 48684)
    (lower : 23936 ≤ state.val)
    (upper : state.val < 24000)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 23936, by omega⟩
  have state_eq :
      (⟨23936 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0374 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0375 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨24000 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨24000 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0375
    (state : Fin 48684)
    (lower : 24000 ≤ state.val)
    (upper : state.val < 24064)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 24000, by omega⟩
  have state_eq :
      (⟨24000 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0375 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0376 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨24064 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨24064 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0376
    (state : Fin 48684)
    (lower : 24064 ≤ state.val)
    (upper : state.val < 24128)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 24064, by omega⟩
  have state_eq :
      (⟨24064 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0376 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0377 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨24128 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨24128 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0377
    (state : Fin 48684)
    (lower : 24128 ≤ state.val)
    (upper : state.val < 24192)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 24128, by omega⟩
  have state_eq :
      (⟨24128 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0377 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0378 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨24192 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨24192 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0378
    (state : Fin 48684)
    (lower : 24192 ≤ state.val)
    (upper : state.val < 24256)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 24192, by omega⟩
  have state_eq :
      (⟨24192 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0378 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0379 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨24256 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨24256 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0379
    (state : Fin 48684)
    (lower : 24256 ≤ state.val)
    (upper : state.val < 24320)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 24256, by omega⟩
  have state_eq :
      (⟨24256 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0379 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0380 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨24320 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨24320 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0380
    (state : Fin 48684)
    (lower : 24320 ≤ state.val)
    (upper : state.val < 24384)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 24320, by omega⟩
  have state_eq :
      (⟨24320 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0380 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0381 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨24384 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨24384 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0381
    (state : Fin 48684)
    (lower : 24384 ≤ state.val)
    (upper : state.val < 24448)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 24384, by omega⟩
  have state_eq :
      (⟨24384 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0381 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0382 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨24448 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨24448 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0382
    (state : Fin 48684)
    (lower : 24448 ≤ state.val)
    (upper : state.val < 24512)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 24448, by omega⟩
  have state_eq :
      (⟨24448 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0382 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0383 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨24512 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨24512 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0383
    (state : Fin 48684)
    (lower : 24512 ≤ state.val)
    (upper : state.val < 24576)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 24512, by omega⟩
  have state_eq :
      (⟨24512 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0383 offset generator coordinate

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards
