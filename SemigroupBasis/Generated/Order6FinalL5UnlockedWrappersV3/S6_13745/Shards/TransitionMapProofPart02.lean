import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.Support.Core
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.Shards

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0064 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 36,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition (⟨4096 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (⟨4096 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0064
    (state : Fin 11742)
    (lower : 4096 ≤ state.val)
    (upper : state.val < 4160)
    (generator : Fin 6)
    (coordinate : Fin 36) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 4096, by omega⟩
  have state_eq :
      (⟨4096 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0064 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0065 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 36,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition (⟨4160 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (⟨4160 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0065
    (state : Fin 11742)
    (lower : 4160 ≤ state.val)
    (upper : state.val < 4224)
    (generator : Fin 6)
    (coordinate : Fin 36) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 4160, by omega⟩
  have state_eq :
      (⟨4160 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0065 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0066 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 36,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition (⟨4224 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (⟨4224 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0066
    (state : Fin 11742)
    (lower : 4224 ≤ state.val)
    (upper : state.val < 4288)
    (generator : Fin 6)
    (coordinate : Fin 36) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 4224, by omega⟩
  have state_eq :
      (⟨4224 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0066 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0067 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 36,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition (⟨4288 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (⟨4288 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0067
    (state : Fin 11742)
    (lower : 4288 ≤ state.val)
    (upper : state.val < 4352)
    (generator : Fin 6)
    (coordinate : Fin 36) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 4288, by omega⟩
  have state_eq :
      (⟨4288 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0067 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0068 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 36,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition (⟨4352 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (⟨4352 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0068
    (state : Fin 11742)
    (lower : 4352 ≤ state.val)
    (upper : state.val < 4416)
    (generator : Fin 6)
    (coordinate : Fin 36) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 4352, by omega⟩
  have state_eq :
      (⟨4352 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0068 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0069 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 36,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition (⟨4416 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (⟨4416 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0069
    (state : Fin 11742)
    (lower : 4416 ≤ state.val)
    (upper : state.val < 4480)
    (generator : Fin 6)
    (coordinate : Fin 36) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 4416, by omega⟩
  have state_eq :
      (⟨4416 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0069 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0070 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 36,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition (⟨4480 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (⟨4480 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0070
    (state : Fin 11742)
    (lower : 4480 ≤ state.val)
    (upper : state.val < 4544)
    (generator : Fin 6)
    (coordinate : Fin 36) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 4480, by omega⟩
  have state_eq :
      (⟨4480 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0070 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0071 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 36,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition (⟨4544 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (⟨4544 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0071
    (state : Fin 11742)
    (lower : 4544 ≤ state.val)
    (upper : state.val < 4608)
    (generator : Fin 6)
    (coordinate : Fin 36) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 4544, by omega⟩
  have state_eq :
      (⟨4544 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0071 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0072 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 36,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition (⟨4608 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (⟨4608 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0072
    (state : Fin 11742)
    (lower : 4608 ≤ state.val)
    (upper : state.val < 4672)
    (generator : Fin 6)
    (coordinate : Fin 36) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 4608, by omega⟩
  have state_eq :
      (⟨4608 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0072 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0073 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 36,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition (⟨4672 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (⟨4672 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0073
    (state : Fin 11742)
    (lower : 4672 ≤ state.val)
    (upper : state.val < 4736)
    (generator : Fin 6)
    (coordinate : Fin 36) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 4672, by omega⟩
  have state_eq :
      (⟨4672 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0073 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0074 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 36,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition (⟨4736 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (⟨4736 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0074
    (state : Fin 11742)
    (lower : 4736 ≤ state.val)
    (upper : state.val < 4800)
    (generator : Fin 6)
    (coordinate : Fin 36) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 4736, by omega⟩
  have state_eq :
      (⟨4736 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0074 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0075 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 36,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition (⟨4800 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (⟨4800 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0075
    (state : Fin 11742)
    (lower : 4800 ≤ state.val)
    (upper : state.val < 4864)
    (generator : Fin 6)
    (coordinate : Fin 36) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 4800, by omega⟩
  have state_eq :
      (⟨4800 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0075 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0076 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 36,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition (⟨4864 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (⟨4864 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0076
    (state : Fin 11742)
    (lower : 4864 ≤ state.val)
    (upper : state.val < 4928)
    (generator : Fin 6)
    (coordinate : Fin 36) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 4864, by omega⟩
  have state_eq :
      (⟨4864 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0076 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0077 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 36,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition (⟨4928 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (⟨4928 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0077
    (state : Fin 11742)
    (lower : 4928 ≤ state.val)
    (upper : state.val < 4992)
    (generator : Fin 6)
    (coordinate : Fin 36) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 4928, by omega⟩
  have state_eq :
      (⟨4928 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0077 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0078 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 36,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition (⟨4992 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (⟨4992 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0078
    (state : Fin 11742)
    (lower : 4992 ≤ state.val)
    (upper : state.val < 5056)
    (generator : Fin 6)
    (coordinate : Fin 36) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 4992, by omega⟩
  have state_eq :
      (⟨4992 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0078 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0079 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 36,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition (⟨5056 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (⟨5056 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0079
    (state : Fin 11742)
    (lower : 5056 ≤ state.val)
    (upper : state.val < 5120)
    (generator : Fin 6)
    (coordinate : Fin 36) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 5056, by omega⟩
  have state_eq :
      (⟨5056 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0079 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0080 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 36,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition (⟨5120 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (⟨5120 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0080
    (state : Fin 11742)
    (lower : 5120 ≤ state.val)
    (upper : state.val < 5184)
    (generator : Fin 6)
    (coordinate : Fin 36) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 5120, by omega⟩
  have state_eq :
      (⟨5120 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0080 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0081 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 36,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition (⟨5184 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (⟨5184 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0081
    (state : Fin 11742)
    (lower : 5184 ≤ state.val)
    (upper : state.val < 5248)
    (generator : Fin 6)
    (coordinate : Fin 36) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 5184, by omega⟩
  have state_eq :
      (⟨5184 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0081 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0082 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 36,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition (⟨5248 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (⟨5248 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0082
    (state : Fin 11742)
    (lower : 5248 ≤ state.val)
    (upper : state.val < 5312)
    (generator : Fin 6)
    (coordinate : Fin 36) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 5248, by omega⟩
  have state_eq :
      (⟨5248 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0082 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0083 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 36,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition (⟨5312 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (⟨5312 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0083
    (state : Fin 11742)
    (lower : 5312 ≤ state.val)
    (upper : state.val < 5376)
    (generator : Fin 6)
    (coordinate : Fin 36) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 5312, by omega⟩
  have state_eq :
      (⟨5312 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0083 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0084 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 36,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition (⟨5376 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (⟨5376 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0084
    (state : Fin 11742)
    (lower : 5376 ≤ state.val)
    (upper : state.val < 5440)
    (generator : Fin 6)
    (coordinate : Fin 36) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 5376, by omega⟩
  have state_eq :
      (⟨5376 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0084 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0085 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 36,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition (⟨5440 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (⟨5440 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0085
    (state : Fin 11742)
    (lower : 5440 ≤ state.val)
    (upper : state.val < 5504)
    (generator : Fin 6)
    (coordinate : Fin 36) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 5440, by omega⟩
  have state_eq :
      (⟨5440 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0085 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0086 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 36,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition (⟨5504 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (⟨5504 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0086
    (state : Fin 11742)
    (lower : 5504 ≤ state.val)
    (upper : state.val < 5568)
    (generator : Fin 6)
    (coordinate : Fin 36) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 5504, by omega⟩
  have state_eq :
      (⟨5504 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0086 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0087 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 36,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition (⟨5568 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (⟨5568 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0087
    (state : Fin 11742)
    (lower : 5568 ≤ state.val)
    (upper : state.val < 5632)
    (generator : Fin 6)
    (coordinate : Fin 36) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 5568, by omega⟩
  have state_eq :
      (⟨5568 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0087 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0088 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 36,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition (⟨5632 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (⟨5632 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0088
    (state : Fin 11742)
    (lower : 5632 ≤ state.val)
    (upper : state.val < 5696)
    (generator : Fin 6)
    (coordinate : Fin 36) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 5632, by omega⟩
  have state_eq :
      (⟨5632 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0088 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0089 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 36,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition (⟨5696 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (⟨5696 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0089
    (state : Fin 11742)
    (lower : 5696 ≤ state.val)
    (upper : state.val < 5760)
    (generator : Fin 6)
    (coordinate : Fin 36) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 5696, by omega⟩
  have state_eq :
      (⟨5696 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0089 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0090 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 36,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition (⟨5760 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (⟨5760 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0090
    (state : Fin 11742)
    (lower : 5760 ≤ state.val)
    (upper : state.val < 5824)
    (generator : Fin 6)
    (coordinate : Fin 36) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 5760, by omega⟩
  have state_eq :
      (⟨5760 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0090 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0091 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 36,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition (⟨5824 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (⟨5824 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0091
    (state : Fin 11742)
    (lower : 5824 ≤ state.val)
    (upper : state.val < 5888)
    (generator : Fin 6)
    (coordinate : Fin 36) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 5824, by omega⟩
  have state_eq :
      (⟨5824 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0091 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0092 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 36,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition (⟨5888 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (⟨5888 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0092
    (state : Fin 11742)
    (lower : 5888 ≤ state.val)
    (upper : state.val < 5952)
    (generator : Fin 6)
    (coordinate : Fin 36) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 5888, by omega⟩
  have state_eq :
      (⟨5888 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0092 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0093 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 36,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition (⟨5952 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (⟨5952 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0093
    (state : Fin 11742)
    (lower : 5952 ≤ state.val)
    (upper : state.val < 6016)
    (generator : Fin 6)
    (coordinate : Fin 36) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 5952, by omega⟩
  have state_eq :
      (⟨5952 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0093 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0094 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 36,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition (⟨6016 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (⟨6016 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0094
    (state : Fin 11742)
    (lower : 6016 ≤ state.val)
    (upper : state.val < 6080)
    (generator : Fin 6)
    (coordinate : Fin 36) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 6016, by omega⟩
  have state_eq :
      (⟨6016 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0094 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0095 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 36,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition (⟨6080 + candidate.val, by omega⟩ : Fin 11742) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (⟨6080 + candidate.val, by omega⟩ : Fin 11742) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0095
    (state : Fin 11742)
    (lower : 6080 ≤ state.val)
    (upper : state.val < 6144)
    (generator : Fin 6)
    (coordinate : Fin 36) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 6080, by omega⟩
  have state_eq :
      (⟨6080 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0095 offset generator coordinate

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.Shards
