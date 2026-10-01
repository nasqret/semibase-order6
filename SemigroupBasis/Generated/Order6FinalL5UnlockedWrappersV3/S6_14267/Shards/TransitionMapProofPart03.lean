import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.Support.Core
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.Shards

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0096 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 45,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.transition (⟨6144 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector (⟨6144 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0096
    (state : Fin 11742)
    (lower : 6144 ≤ state.val)
    (upper : state.val < 6208)
    (generator : Fin 6)
    (coordinate : Fin 45) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 6144, by omega⟩
  have state_eq :
      (⟨6144 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0096 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0097 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 45,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.transition (⟨6208 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector (⟨6208 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0097
    (state : Fin 11742)
    (lower : 6208 ≤ state.val)
    (upper : state.val < 6272)
    (generator : Fin 6)
    (coordinate : Fin 45) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 6208, by omega⟩
  have state_eq :
      (⟨6208 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0097 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0098 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 45,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.transition (⟨6272 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector (⟨6272 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0098
    (state : Fin 11742)
    (lower : 6272 ≤ state.val)
    (upper : state.val < 6336)
    (generator : Fin 6)
    (coordinate : Fin 45) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 6272, by omega⟩
  have state_eq :
      (⟨6272 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0098 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0099 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 45,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.transition (⟨6336 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector (⟨6336 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0099
    (state : Fin 11742)
    (lower : 6336 ≤ state.val)
    (upper : state.val < 6400)
    (generator : Fin 6)
    (coordinate : Fin 45) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 6336, by omega⟩
  have state_eq :
      (⟨6336 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0099 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0100 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 45,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.transition (⟨6400 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector (⟨6400 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0100
    (state : Fin 11742)
    (lower : 6400 ≤ state.val)
    (upper : state.val < 6464)
    (generator : Fin 6)
    (coordinate : Fin 45) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 6400, by omega⟩
  have state_eq :
      (⟨6400 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0100 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0101 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 45,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.transition (⟨6464 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector (⟨6464 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0101
    (state : Fin 11742)
    (lower : 6464 ≤ state.val)
    (upper : state.val < 6528)
    (generator : Fin 6)
    (coordinate : Fin 45) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 6464, by omega⟩
  have state_eq :
      (⟨6464 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0101 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0102 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 45,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.transition (⟨6528 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector (⟨6528 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0102
    (state : Fin 11742)
    (lower : 6528 ≤ state.val)
    (upper : state.val < 6592)
    (generator : Fin 6)
    (coordinate : Fin 45) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 6528, by omega⟩
  have state_eq :
      (⟨6528 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0102 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0103 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 45,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.transition (⟨6592 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector (⟨6592 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0103
    (state : Fin 11742)
    (lower : 6592 ≤ state.val)
    (upper : state.val < 6656)
    (generator : Fin 6)
    (coordinate : Fin 45) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 6592, by omega⟩
  have state_eq :
      (⟨6592 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0103 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0104 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 45,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.transition (⟨6656 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector (⟨6656 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0104
    (state : Fin 11742)
    (lower : 6656 ≤ state.val)
    (upper : state.val < 6720)
    (generator : Fin 6)
    (coordinate : Fin 45) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 6656, by omega⟩
  have state_eq :
      (⟨6656 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0104 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0105 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 45,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.transition (⟨6720 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector (⟨6720 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0105
    (state : Fin 11742)
    (lower : 6720 ≤ state.val)
    (upper : state.val < 6784)
    (generator : Fin 6)
    (coordinate : Fin 45) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 6720, by omega⟩
  have state_eq :
      (⟨6720 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0105 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0106 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 45,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.transition (⟨6784 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector (⟨6784 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0106
    (state : Fin 11742)
    (lower : 6784 ≤ state.val)
    (upper : state.val < 6848)
    (generator : Fin 6)
    (coordinate : Fin 45) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 6784, by omega⟩
  have state_eq :
      (⟨6784 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0106 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0107 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 45,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.transition (⟨6848 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector (⟨6848 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0107
    (state : Fin 11742)
    (lower : 6848 ≤ state.val)
    (upper : state.val < 6912)
    (generator : Fin 6)
    (coordinate : Fin 45) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 6848, by omega⟩
  have state_eq :
      (⟨6848 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0107 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0108 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 45,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.transition (⟨6912 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector (⟨6912 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0108
    (state : Fin 11742)
    (lower : 6912 ≤ state.val)
    (upper : state.val < 6976)
    (generator : Fin 6)
    (coordinate : Fin 45) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 6912, by omega⟩
  have state_eq :
      (⟨6912 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0108 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0109 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 45,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.transition (⟨6976 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector (⟨6976 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0109
    (state : Fin 11742)
    (lower : 6976 ≤ state.val)
    (upper : state.val < 7040)
    (generator : Fin 6)
    (coordinate : Fin 45) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 6976, by omega⟩
  have state_eq :
      (⟨6976 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0109 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0110 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 45,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.transition (⟨7040 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector (⟨7040 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0110
    (state : Fin 11742)
    (lower : 7040 ≤ state.val)
    (upper : state.val < 7104)
    (generator : Fin 6)
    (coordinate : Fin 45) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 7040, by omega⟩
  have state_eq :
      (⟨7040 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0110 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0111 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 45,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.transition (⟨7104 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector (⟨7104 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0111
    (state : Fin 11742)
    (lower : 7104 ≤ state.val)
    (upper : state.val < 7168)
    (generator : Fin 6)
    (coordinate : Fin 45) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 7104, by omega⟩
  have state_eq :
      (⟨7104 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0111 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0112 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 45,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.transition (⟨7168 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector (⟨7168 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0112
    (state : Fin 11742)
    (lower : 7168 ≤ state.val)
    (upper : state.val < 7232)
    (generator : Fin 6)
    (coordinate : Fin 45) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 7168, by omega⟩
  have state_eq :
      (⟨7168 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0112 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0113 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 45,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.transition (⟨7232 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector (⟨7232 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0113
    (state : Fin 11742)
    (lower : 7232 ≤ state.val)
    (upper : state.val < 7296)
    (generator : Fin 6)
    (coordinate : Fin 45) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 7232, by omega⟩
  have state_eq :
      (⟨7232 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0113 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0114 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 45,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.transition (⟨7296 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector (⟨7296 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0114
    (state : Fin 11742)
    (lower : 7296 ≤ state.val)
    (upper : state.val < 7360)
    (generator : Fin 6)
    (coordinate : Fin 45) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 7296, by omega⟩
  have state_eq :
      (⟨7296 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0114 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0115 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 45,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.transition (⟨7360 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector (⟨7360 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0115
    (state : Fin 11742)
    (lower : 7360 ≤ state.val)
    (upper : state.val < 7424)
    (generator : Fin 6)
    (coordinate : Fin 45) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 7360, by omega⟩
  have state_eq :
      (⟨7360 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0115 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0116 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 45,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.transition (⟨7424 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector (⟨7424 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0116
    (state : Fin 11742)
    (lower : 7424 ≤ state.val)
    (upper : state.val < 7488)
    (generator : Fin 6)
    (coordinate : Fin 45) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 7424, by omega⟩
  have state_eq :
      (⟨7424 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0116 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0117 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 45,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.transition (⟨7488 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector (⟨7488 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0117
    (state : Fin 11742)
    (lower : 7488 ≤ state.val)
    (upper : state.val < 7552)
    (generator : Fin 6)
    (coordinate : Fin 45) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 7488, by omega⟩
  have state_eq :
      (⟨7488 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0117 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0118 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 45,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.transition (⟨7552 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector (⟨7552 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0118
    (state : Fin 11742)
    (lower : 7552 ≤ state.val)
    (upper : state.val < 7616)
    (generator : Fin 6)
    (coordinate : Fin 45) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 7552, by omega⟩
  have state_eq :
      (⟨7552 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0118 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0119 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 45,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.transition (⟨7616 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector (⟨7616 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0119
    (state : Fin 11742)
    (lower : 7616 ≤ state.val)
    (upper : state.val < 7680)
    (generator : Fin 6)
    (coordinate : Fin 45) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 7616, by omega⟩
  have state_eq :
      (⟨7616 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0119 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0120 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 45,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.transition (⟨7680 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector (⟨7680 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0120
    (state : Fin 11742)
    (lower : 7680 ≤ state.val)
    (upper : state.val < 7744)
    (generator : Fin 6)
    (coordinate : Fin 45) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 7680, by omega⟩
  have state_eq :
      (⟨7680 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0120 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0121 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 45,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.transition (⟨7744 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector (⟨7744 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0121
    (state : Fin 11742)
    (lower : 7744 ≤ state.val)
    (upper : state.val < 7808)
    (generator : Fin 6)
    (coordinate : Fin 45) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 7744, by omega⟩
  have state_eq :
      (⟨7744 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0121 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0122 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 45,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.transition (⟨7808 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector (⟨7808 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0122
    (state : Fin 11742)
    (lower : 7808 ≤ state.val)
    (upper : state.val < 7872)
    (generator : Fin 6)
    (coordinate : Fin 45) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 7808, by omega⟩
  have state_eq :
      (⟨7808 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0122 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0123 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 45,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.transition (⟨7872 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector (⟨7872 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0123
    (state : Fin 11742)
    (lower : 7872 ≤ state.val)
    (upper : state.val < 7936)
    (generator : Fin 6)
    (coordinate : Fin 45) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 7872, by omega⟩
  have state_eq :
      (⟨7872 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0123 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0124 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 45,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.transition (⟨7936 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector (⟨7936 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0124
    (state : Fin 11742)
    (lower : 7936 ≤ state.val)
    (upper : state.val < 8000)
    (generator : Fin 6)
    (coordinate : Fin 45) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 7936, by omega⟩
  have state_eq :
      (⟨7936 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0124 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0125 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 45,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.transition (⟨8000 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector (⟨8000 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0125
    (state : Fin 11742)
    (lower : 8000 ≤ state.val)
    (upper : state.val < 8064)
    (generator : Fin 6)
    (coordinate : Fin 45) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 8000, by omega⟩
  have state_eq :
      (⟨8000 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0125 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0126 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 45,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.transition (⟨8064 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector (⟨8064 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0126
    (state : Fin 11742)
    (lower : 8064 ≤ state.val)
    (upper : state.val < 8128)
    (generator : Fin 6)
    (coordinate : Fin 45) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 8064, by omega⟩
  have state_eq :
      (⟨8064 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0126 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0127 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 45,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.transition (⟨8128 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector (⟨8128 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0127
    (state : Fin 11742)
    (lower : 8128 ≤ state.val)
    (upper : state.val < 8192)
    (generator : Fin 6)
    (coordinate : Fin 45) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 8128, by omega⟩
  have state_eq :
      (⟨8128 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0127 offset generator coordinate

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.Shards
