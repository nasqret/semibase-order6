import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Support.Core
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0512 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨32768 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨32768 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0512
    (state : Fin 48684)
    (lower : 32768 ≤ state.val)
    (upper : state.val < 32832)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 32768, by omega⟩
  have state_eq :
      (⟨32768 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0512 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0513 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨32832 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨32832 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0513
    (state : Fin 48684)
    (lower : 32832 ≤ state.val)
    (upper : state.val < 32896)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 32832, by omega⟩
  have state_eq :
      (⟨32832 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0513 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0514 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨32896 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨32896 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0514
    (state : Fin 48684)
    (lower : 32896 ≤ state.val)
    (upper : state.val < 32960)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 32896, by omega⟩
  have state_eq :
      (⟨32896 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0514 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0515 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨32960 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨32960 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0515
    (state : Fin 48684)
    (lower : 32960 ≤ state.val)
    (upper : state.val < 33024)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 32960, by omega⟩
  have state_eq :
      (⟨32960 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0515 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0516 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨33024 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨33024 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0516
    (state : Fin 48684)
    (lower : 33024 ≤ state.val)
    (upper : state.val < 33088)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 33024, by omega⟩
  have state_eq :
      (⟨33024 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0516 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0517 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨33088 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨33088 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0517
    (state : Fin 48684)
    (lower : 33088 ≤ state.val)
    (upper : state.val < 33152)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 33088, by omega⟩
  have state_eq :
      (⟨33088 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0517 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0518 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨33152 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨33152 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0518
    (state : Fin 48684)
    (lower : 33152 ≤ state.val)
    (upper : state.val < 33216)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 33152, by omega⟩
  have state_eq :
      (⟨33152 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0518 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0519 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨33216 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨33216 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0519
    (state : Fin 48684)
    (lower : 33216 ≤ state.val)
    (upper : state.val < 33280)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 33216, by omega⟩
  have state_eq :
      (⟨33216 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0519 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0520 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨33280 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨33280 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0520
    (state : Fin 48684)
    (lower : 33280 ≤ state.val)
    (upper : state.val < 33344)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 33280, by omega⟩
  have state_eq :
      (⟨33280 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0520 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0521 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨33344 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨33344 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0521
    (state : Fin 48684)
    (lower : 33344 ≤ state.val)
    (upper : state.val < 33408)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 33344, by omega⟩
  have state_eq :
      (⟨33344 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0521 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0522 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨33408 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨33408 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0522
    (state : Fin 48684)
    (lower : 33408 ≤ state.val)
    (upper : state.val < 33472)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 33408, by omega⟩
  have state_eq :
      (⟨33408 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0522 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0523 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨33472 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨33472 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0523
    (state : Fin 48684)
    (lower : 33472 ≤ state.val)
    (upper : state.val < 33536)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 33472, by omega⟩
  have state_eq :
      (⟨33472 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0523 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0524 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨33536 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨33536 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0524
    (state : Fin 48684)
    (lower : 33536 ≤ state.val)
    (upper : state.val < 33600)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 33536, by omega⟩
  have state_eq :
      (⟨33536 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0524 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0525 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨33600 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨33600 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0525
    (state : Fin 48684)
    (lower : 33600 ≤ state.val)
    (upper : state.val < 33664)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 33600, by omega⟩
  have state_eq :
      (⟨33600 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0525 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0526 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨33664 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨33664 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0526
    (state : Fin 48684)
    (lower : 33664 ≤ state.val)
    (upper : state.val < 33728)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 33664, by omega⟩
  have state_eq :
      (⟨33664 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0526 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0527 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨33728 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨33728 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0527
    (state : Fin 48684)
    (lower : 33728 ≤ state.val)
    (upper : state.val < 33792)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 33728, by omega⟩
  have state_eq :
      (⟨33728 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0527 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0528 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨33792 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨33792 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0528
    (state : Fin 48684)
    (lower : 33792 ≤ state.val)
    (upper : state.val < 33856)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 33792, by omega⟩
  have state_eq :
      (⟨33792 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0528 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0529 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨33856 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨33856 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0529
    (state : Fin 48684)
    (lower : 33856 ≤ state.val)
    (upper : state.val < 33920)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 33856, by omega⟩
  have state_eq :
      (⟨33856 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0529 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0530 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨33920 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨33920 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0530
    (state : Fin 48684)
    (lower : 33920 ≤ state.val)
    (upper : state.val < 33984)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 33920, by omega⟩
  have state_eq :
      (⟨33920 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0530 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0531 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨33984 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨33984 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0531
    (state : Fin 48684)
    (lower : 33984 ≤ state.val)
    (upper : state.val < 34048)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 33984, by omega⟩
  have state_eq :
      (⟨33984 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0531 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0532 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨34048 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨34048 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0532
    (state : Fin 48684)
    (lower : 34048 ≤ state.val)
    (upper : state.val < 34112)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 34048, by omega⟩
  have state_eq :
      (⟨34048 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0532 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0533 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨34112 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨34112 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0533
    (state : Fin 48684)
    (lower : 34112 ≤ state.val)
    (upper : state.val < 34176)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 34112, by omega⟩
  have state_eq :
      (⟨34112 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0533 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0534 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨34176 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨34176 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0534
    (state : Fin 48684)
    (lower : 34176 ≤ state.val)
    (upper : state.val < 34240)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 34176, by omega⟩
  have state_eq :
      (⟨34176 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0534 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0535 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨34240 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨34240 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0535
    (state : Fin 48684)
    (lower : 34240 ≤ state.val)
    (upper : state.val < 34304)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 34240, by omega⟩
  have state_eq :
      (⟨34240 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0535 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0536 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨34304 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨34304 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0536
    (state : Fin 48684)
    (lower : 34304 ≤ state.val)
    (upper : state.val < 34368)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 34304, by omega⟩
  have state_eq :
      (⟨34304 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0536 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0537 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨34368 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨34368 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0537
    (state : Fin 48684)
    (lower : 34368 ≤ state.val)
    (upper : state.val < 34432)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 34368, by omega⟩
  have state_eq :
      (⟨34368 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0537 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0538 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨34432 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨34432 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0538
    (state : Fin 48684)
    (lower : 34432 ≤ state.val)
    (upper : state.val < 34496)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 34432, by omega⟩
  have state_eq :
      (⟨34432 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0538 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0539 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨34496 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨34496 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0539
    (state : Fin 48684)
    (lower : 34496 ≤ state.val)
    (upper : state.val < 34560)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 34496, by omega⟩
  have state_eq :
      (⟨34496 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0539 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0540 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨34560 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨34560 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0540
    (state : Fin 48684)
    (lower : 34560 ≤ state.val)
    (upper : state.val < 34624)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 34560, by omega⟩
  have state_eq :
      (⟨34560 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0540 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0541 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨34624 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨34624 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0541
    (state : Fin 48684)
    (lower : 34624 ≤ state.val)
    (upper : state.val < 34688)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 34624, by omega⟩
  have state_eq :
      (⟨34624 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0541 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0542 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨34688 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨34688 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0542
    (state : Fin 48684)
    (lower : 34688 ≤ state.val)
    (upper : state.val < 34752)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 34688, by omega⟩
  have state_eq :
      (⟨34688 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0542 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0543 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨34752 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨34752 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0543
    (state : Fin 48684)
    (lower : 34752 ≤ state.val)
    (upper : state.val < 34816)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 34752, by omega⟩
  have state_eq :
      (⟨34752 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0543 offset generator coordinate

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards
