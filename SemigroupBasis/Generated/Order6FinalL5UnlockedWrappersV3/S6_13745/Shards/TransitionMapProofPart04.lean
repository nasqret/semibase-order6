import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.Support.Core
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.Shards

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0128 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 36,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition (⟨8192 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (⟨8192 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0128
    (state : Fin 11742)
    (lower : 8192 ≤ state.val)
    (upper : state.val < 8256)
    (generator : Fin 6)
    (coordinate : Fin 36) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 8192, by omega⟩
  have state_eq :
      (⟨8192 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0128 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0129 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 36,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition (⟨8256 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (⟨8256 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0129
    (state : Fin 11742)
    (lower : 8256 ≤ state.val)
    (upper : state.val < 8320)
    (generator : Fin 6)
    (coordinate : Fin 36) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 8256, by omega⟩
  have state_eq :
      (⟨8256 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0129 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0130 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 36,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition (⟨8320 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (⟨8320 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0130
    (state : Fin 11742)
    (lower : 8320 ≤ state.val)
    (upper : state.val < 8384)
    (generator : Fin 6)
    (coordinate : Fin 36) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 8320, by omega⟩
  have state_eq :
      (⟨8320 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0130 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0131 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 36,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition (⟨8384 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (⟨8384 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0131
    (state : Fin 11742)
    (lower : 8384 ≤ state.val)
    (upper : state.val < 8448)
    (generator : Fin 6)
    (coordinate : Fin 36) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 8384, by omega⟩
  have state_eq :
      (⟨8384 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0131 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0132 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 36,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition (⟨8448 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (⟨8448 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0132
    (state : Fin 11742)
    (lower : 8448 ≤ state.val)
    (upper : state.val < 8512)
    (generator : Fin 6)
    (coordinate : Fin 36) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 8448, by omega⟩
  have state_eq :
      (⟨8448 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0132 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0133 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 36,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition (⟨8512 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (⟨8512 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0133
    (state : Fin 11742)
    (lower : 8512 ≤ state.val)
    (upper : state.val < 8576)
    (generator : Fin 6)
    (coordinate : Fin 36) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 8512, by omega⟩
  have state_eq :
      (⟨8512 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0133 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0134 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 36,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition (⟨8576 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (⟨8576 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0134
    (state : Fin 11742)
    (lower : 8576 ≤ state.val)
    (upper : state.val < 8640)
    (generator : Fin 6)
    (coordinate : Fin 36) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 8576, by omega⟩
  have state_eq :
      (⟨8576 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0134 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0135 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 36,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition (⟨8640 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (⟨8640 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0135
    (state : Fin 11742)
    (lower : 8640 ≤ state.val)
    (upper : state.val < 8704)
    (generator : Fin 6)
    (coordinate : Fin 36) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 8640, by omega⟩
  have state_eq :
      (⟨8640 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0135 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0136 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 36,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition (⟨8704 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (⟨8704 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0136
    (state : Fin 11742)
    (lower : 8704 ≤ state.val)
    (upper : state.val < 8768)
    (generator : Fin 6)
    (coordinate : Fin 36) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 8704, by omega⟩
  have state_eq :
      (⟨8704 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0136 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0137 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 36,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition (⟨8768 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (⟨8768 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0137
    (state : Fin 11742)
    (lower : 8768 ≤ state.val)
    (upper : state.val < 8832)
    (generator : Fin 6)
    (coordinate : Fin 36) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 8768, by omega⟩
  have state_eq :
      (⟨8768 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0137 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0138 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 36,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition (⟨8832 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (⟨8832 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0138
    (state : Fin 11742)
    (lower : 8832 ≤ state.val)
    (upper : state.val < 8896)
    (generator : Fin 6)
    (coordinate : Fin 36) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 8832, by omega⟩
  have state_eq :
      (⟨8832 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0138 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0139 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 36,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition (⟨8896 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (⟨8896 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0139
    (state : Fin 11742)
    (lower : 8896 ≤ state.val)
    (upper : state.val < 8960)
    (generator : Fin 6)
    (coordinate : Fin 36) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 8896, by omega⟩
  have state_eq :
      (⟨8896 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0139 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0140 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 36,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition (⟨8960 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (⟨8960 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0140
    (state : Fin 11742)
    (lower : 8960 ≤ state.val)
    (upper : state.val < 9024)
    (generator : Fin 6)
    (coordinate : Fin 36) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 8960, by omega⟩
  have state_eq :
      (⟨8960 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0140 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0141 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 36,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition (⟨9024 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (⟨9024 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0141
    (state : Fin 11742)
    (lower : 9024 ≤ state.val)
    (upper : state.val < 9088)
    (generator : Fin 6)
    (coordinate : Fin 36) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 9024, by omega⟩
  have state_eq :
      (⟨9024 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0141 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0142 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 36,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition (⟨9088 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (⟨9088 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0142
    (state : Fin 11742)
    (lower : 9088 ≤ state.val)
    (upper : state.val < 9152)
    (generator : Fin 6)
    (coordinate : Fin 36) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 9088, by omega⟩
  have state_eq :
      (⟨9088 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0142 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0143 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 36,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition (⟨9152 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (⟨9152 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0143
    (state : Fin 11742)
    (lower : 9152 ≤ state.val)
    (upper : state.val < 9216)
    (generator : Fin 6)
    (coordinate : Fin 36) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 9152, by omega⟩
  have state_eq :
      (⟨9152 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0143 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0144 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 36,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition (⟨9216 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (⟨9216 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0144
    (state : Fin 11742)
    (lower : 9216 ≤ state.val)
    (upper : state.val < 9280)
    (generator : Fin 6)
    (coordinate : Fin 36) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 9216, by omega⟩
  have state_eq :
      (⟨9216 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0144 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0145 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 36,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition (⟨9280 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (⟨9280 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0145
    (state : Fin 11742)
    (lower : 9280 ≤ state.val)
    (upper : state.val < 9344)
    (generator : Fin 6)
    (coordinate : Fin 36) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 9280, by omega⟩
  have state_eq :
      (⟨9280 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0145 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0146 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 36,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition (⟨9344 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (⟨9344 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0146
    (state : Fin 11742)
    (lower : 9344 ≤ state.val)
    (upper : state.val < 9408)
    (generator : Fin 6)
    (coordinate : Fin 36) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 9344, by omega⟩
  have state_eq :
      (⟨9344 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0146 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0147 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 36,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition (⟨9408 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (⟨9408 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0147
    (state : Fin 11742)
    (lower : 9408 ≤ state.val)
    (upper : state.val < 9472)
    (generator : Fin 6)
    (coordinate : Fin 36) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 9408, by omega⟩
  have state_eq :
      (⟨9408 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0147 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0148 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 36,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition (⟨9472 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (⟨9472 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0148
    (state : Fin 11742)
    (lower : 9472 ≤ state.val)
    (upper : state.val < 9536)
    (generator : Fin 6)
    (coordinate : Fin 36) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 9472, by omega⟩
  have state_eq :
      (⟨9472 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0148 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0149 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 36,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition (⟨9536 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (⟨9536 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0149
    (state : Fin 11742)
    (lower : 9536 ≤ state.val)
    (upper : state.val < 9600)
    (generator : Fin 6)
    (coordinate : Fin 36) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 9536, by omega⟩
  have state_eq :
      (⟨9536 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0149 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0150 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 36,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition (⟨9600 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (⟨9600 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0150
    (state : Fin 11742)
    (lower : 9600 ≤ state.val)
    (upper : state.val < 9664)
    (generator : Fin 6)
    (coordinate : Fin 36) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 9600, by omega⟩
  have state_eq :
      (⟨9600 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0150 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0151 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 36,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition (⟨9664 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (⟨9664 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0151
    (state : Fin 11742)
    (lower : 9664 ≤ state.val)
    (upper : state.val < 9728)
    (generator : Fin 6)
    (coordinate : Fin 36) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 9664, by omega⟩
  have state_eq :
      (⟨9664 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0151 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0152 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 36,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition (⟨9728 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (⟨9728 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0152
    (state : Fin 11742)
    (lower : 9728 ≤ state.val)
    (upper : state.val < 9792)
    (generator : Fin 6)
    (coordinate : Fin 36) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 9728, by omega⟩
  have state_eq :
      (⟨9728 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0152 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0153 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 36,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition (⟨9792 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (⟨9792 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0153
    (state : Fin 11742)
    (lower : 9792 ≤ state.val)
    (upper : state.val < 9856)
    (generator : Fin 6)
    (coordinate : Fin 36) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 9792, by omega⟩
  have state_eq :
      (⟨9792 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0153 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0154 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 36,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition (⟨9856 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (⟨9856 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0154
    (state : Fin 11742)
    (lower : 9856 ≤ state.val)
    (upper : state.val < 9920)
    (generator : Fin 6)
    (coordinate : Fin 36) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 9856, by omega⟩
  have state_eq :
      (⟨9856 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0154 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0155 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 36,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition (⟨9920 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (⟨9920 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0155
    (state : Fin 11742)
    (lower : 9920 ≤ state.val)
    (upper : state.val < 9984)
    (generator : Fin 6)
    (coordinate : Fin 36) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 9920, by omega⟩
  have state_eq :
      (⟨9920 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0155 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0156 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 36,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition (⟨9984 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (⟨9984 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0156
    (state : Fin 11742)
    (lower : 9984 ≤ state.val)
    (upper : state.val < 10048)
    (generator : Fin 6)
    (coordinate : Fin 36) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 9984, by omega⟩
  have state_eq :
      (⟨9984 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0156 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0157 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 36,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition (⟨10048 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (⟨10048 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0157
    (state : Fin 11742)
    (lower : 10048 ≤ state.val)
    (upper : state.val < 10112)
    (generator : Fin 6)
    (coordinate : Fin 36) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 10048, by omega⟩
  have state_eq :
      (⟨10048 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0157 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0158 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 36,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition (⟨10112 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (⟨10112 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0158
    (state : Fin 11742)
    (lower : 10112 ≤ state.val)
    (upper : state.val < 10176)
    (generator : Fin 6)
    (coordinate : Fin 36) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 10112, by omega⟩
  have state_eq :
      (⟨10112 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0158 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0159 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 36,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition (⟨10176 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (⟨10176 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0159
    (state : Fin 11742)
    (lower : 10176 ≤ state.val)
    (upper : state.val < 10240)
    (generator : Fin 6)
    (coordinate : Fin 36) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 10176, by omega⟩
  have state_eq :
      (⟨10176 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0159 offset generator coordinate

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.Shards
