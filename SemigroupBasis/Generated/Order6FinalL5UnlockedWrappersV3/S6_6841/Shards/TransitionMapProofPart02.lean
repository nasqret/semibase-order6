import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.Support.Core
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.Shards

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0064 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 28,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.transition (⟨4096 + candidate.val, by omega⟩ : Fin 4374) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.stateVector (⟨4096 + candidate.val, by omega⟩ : Fin 4374) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0064
    (state : Fin 4374)
    (lower : 4096 ≤ state.val)
    (upper : state.val < 4160)
    (generator : Fin 6)
    (coordinate : Fin 28) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 4096, by omega⟩
  have state_eq :
      (⟨4096 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0064 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0065 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 28,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.transition (⟨4160 + candidate.val, by omega⟩ : Fin 4374) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.stateVector (⟨4160 + candidate.val, by omega⟩ : Fin 4374) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0065
    (state : Fin 4374)
    (lower : 4160 ≤ state.val)
    (upper : state.val < 4224)
    (generator : Fin 6)
    (coordinate : Fin 28) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 4160, by omega⟩
  have state_eq :
      (⟨4160 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0065 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0066 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 28,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.transition (⟨4224 + candidate.val, by omega⟩ : Fin 4374) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.stateVector (⟨4224 + candidate.val, by omega⟩ : Fin 4374) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0066
    (state : Fin 4374)
    (lower : 4224 ≤ state.val)
    (upper : state.val < 4288)
    (generator : Fin 6)
    (coordinate : Fin 28) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 4224, by omega⟩
  have state_eq :
      (⟨4224 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0066 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0067 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 28,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.transition (⟨4288 + candidate.val, by omega⟩ : Fin 4374) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.stateVector (⟨4288 + candidate.val, by omega⟩ : Fin 4374) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0067
    (state : Fin 4374)
    (lower : 4288 ≤ state.val)
    (upper : state.val < 4352)
    (generator : Fin 6)
    (coordinate : Fin 28) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 4288, by omega⟩
  have state_eq :
      (⟨4288 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0067 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0068 :
    ∀ candidate : Fin 22,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 28,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.transition (⟨4352 + candidate.val, by omega⟩ : Fin 4374) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.stateVector (⟨4352 + candidate.val, by omega⟩ : Fin 4374) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0068
    (state : Fin 4374)
    (lower : 4352 ≤ state.val)
    (upper : state.val < 4374)
    (generator : Fin 6)
    (coordinate : Fin 28) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.generatorVector generator coordinate)
    := by
  let offset : Fin 22 := ⟨state.val - 4352, by omega⟩
  have state_eq :
      (⟨4352 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0068 offset generator coordinate

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.Shards
