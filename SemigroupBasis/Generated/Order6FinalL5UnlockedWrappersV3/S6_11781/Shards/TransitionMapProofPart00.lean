import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.Support.Core
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.Shards

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0000 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 26,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.transition (⟨0 + candidate.val, by omega⟩ : Fin 4374) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector (⟨0 + candidate.val, by omega⟩ : Fin 4374) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0000
    (state : Fin 4374)
    (lower : 0 ≤ state.val)
    (upper : state.val < 64)
    (generator : Fin 6)
    (coordinate : Fin 26) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 0, by omega⟩
  have state_eq :
      (⟨0 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0000 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0001 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 26,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.transition (⟨64 + candidate.val, by omega⟩ : Fin 4374) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector (⟨64 + candidate.val, by omega⟩ : Fin 4374) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0001
    (state : Fin 4374)
    (lower : 64 ≤ state.val)
    (upper : state.val < 128)
    (generator : Fin 6)
    (coordinate : Fin 26) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 64, by omega⟩
  have state_eq :
      (⟨64 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0001 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0002 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 26,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.transition (⟨128 + candidate.val, by omega⟩ : Fin 4374) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector (⟨128 + candidate.val, by omega⟩ : Fin 4374) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0002
    (state : Fin 4374)
    (lower : 128 ≤ state.val)
    (upper : state.val < 192)
    (generator : Fin 6)
    (coordinate : Fin 26) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 128, by omega⟩
  have state_eq :
      (⟨128 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0002 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0003 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 26,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.transition (⟨192 + candidate.val, by omega⟩ : Fin 4374) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector (⟨192 + candidate.val, by omega⟩ : Fin 4374) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0003
    (state : Fin 4374)
    (lower : 192 ≤ state.val)
    (upper : state.val < 256)
    (generator : Fin 6)
    (coordinate : Fin 26) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 192, by omega⟩
  have state_eq :
      (⟨192 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0003 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0004 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 26,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.transition (⟨256 + candidate.val, by omega⟩ : Fin 4374) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector (⟨256 + candidate.val, by omega⟩ : Fin 4374) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0004
    (state : Fin 4374)
    (lower : 256 ≤ state.val)
    (upper : state.val < 320)
    (generator : Fin 6)
    (coordinate : Fin 26) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 256, by omega⟩
  have state_eq :
      (⟨256 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0004 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0005 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 26,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.transition (⟨320 + candidate.val, by omega⟩ : Fin 4374) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector (⟨320 + candidate.val, by omega⟩ : Fin 4374) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0005
    (state : Fin 4374)
    (lower : 320 ≤ state.val)
    (upper : state.val < 384)
    (generator : Fin 6)
    (coordinate : Fin 26) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 320, by omega⟩
  have state_eq :
      (⟨320 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0005 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0006 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 26,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.transition (⟨384 + candidate.val, by omega⟩ : Fin 4374) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector (⟨384 + candidate.val, by omega⟩ : Fin 4374) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0006
    (state : Fin 4374)
    (lower : 384 ≤ state.val)
    (upper : state.val < 448)
    (generator : Fin 6)
    (coordinate : Fin 26) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 384, by omega⟩
  have state_eq :
      (⟨384 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0006 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0007 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 26,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.transition (⟨448 + candidate.val, by omega⟩ : Fin 4374) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector (⟨448 + candidate.val, by omega⟩ : Fin 4374) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0007
    (state : Fin 4374)
    (lower : 448 ≤ state.val)
    (upper : state.val < 512)
    (generator : Fin 6)
    (coordinate : Fin 26) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 448, by omega⟩
  have state_eq :
      (⟨448 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0007 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0008 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 26,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.transition (⟨512 + candidate.val, by omega⟩ : Fin 4374) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector (⟨512 + candidate.val, by omega⟩ : Fin 4374) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0008
    (state : Fin 4374)
    (lower : 512 ≤ state.val)
    (upper : state.val < 576)
    (generator : Fin 6)
    (coordinate : Fin 26) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 512, by omega⟩
  have state_eq :
      (⟨512 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0008 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0009 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 26,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.transition (⟨576 + candidate.val, by omega⟩ : Fin 4374) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector (⟨576 + candidate.val, by omega⟩ : Fin 4374) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0009
    (state : Fin 4374)
    (lower : 576 ≤ state.val)
    (upper : state.val < 640)
    (generator : Fin 6)
    (coordinate : Fin 26) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 576, by omega⟩
  have state_eq :
      (⟨576 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0009 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0010 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 26,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.transition (⟨640 + candidate.val, by omega⟩ : Fin 4374) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector (⟨640 + candidate.val, by omega⟩ : Fin 4374) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0010
    (state : Fin 4374)
    (lower : 640 ≤ state.val)
    (upper : state.val < 704)
    (generator : Fin 6)
    (coordinate : Fin 26) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 640, by omega⟩
  have state_eq :
      (⟨640 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0010 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0011 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 26,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.transition (⟨704 + candidate.val, by omega⟩ : Fin 4374) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector (⟨704 + candidate.val, by omega⟩ : Fin 4374) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0011
    (state : Fin 4374)
    (lower : 704 ≤ state.val)
    (upper : state.val < 768)
    (generator : Fin 6)
    (coordinate : Fin 26) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 704, by omega⟩
  have state_eq :
      (⟨704 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0011 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0012 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 26,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.transition (⟨768 + candidate.val, by omega⟩ : Fin 4374) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector (⟨768 + candidate.val, by omega⟩ : Fin 4374) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0012
    (state : Fin 4374)
    (lower : 768 ≤ state.val)
    (upper : state.val < 832)
    (generator : Fin 6)
    (coordinate : Fin 26) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 768, by omega⟩
  have state_eq :
      (⟨768 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0012 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0013 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 26,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.transition (⟨832 + candidate.val, by omega⟩ : Fin 4374) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector (⟨832 + candidate.val, by omega⟩ : Fin 4374) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0013
    (state : Fin 4374)
    (lower : 832 ≤ state.val)
    (upper : state.val < 896)
    (generator : Fin 6)
    (coordinate : Fin 26) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 832, by omega⟩
  have state_eq :
      (⟨832 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0013 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0014 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 26,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.transition (⟨896 + candidate.val, by omega⟩ : Fin 4374) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector (⟨896 + candidate.val, by omega⟩ : Fin 4374) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0014
    (state : Fin 4374)
    (lower : 896 ≤ state.val)
    (upper : state.val < 960)
    (generator : Fin 6)
    (coordinate : Fin 26) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 896, by omega⟩
  have state_eq :
      (⟨896 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0014 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0015 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 26,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.transition (⟨960 + candidate.val, by omega⟩ : Fin 4374) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector (⟨960 + candidate.val, by omega⟩ : Fin 4374) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0015
    (state : Fin 4374)
    (lower : 960 ≤ state.val)
    (upper : state.val < 1024)
    (generator : Fin 6)
    (coordinate : Fin 26) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 960, by omega⟩
  have state_eq :
      (⟨960 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0015 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0016 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 26,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.transition (⟨1024 + candidate.val, by omega⟩ : Fin 4374) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector (⟨1024 + candidate.val, by omega⟩ : Fin 4374) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0016
    (state : Fin 4374)
    (lower : 1024 ≤ state.val)
    (upper : state.val < 1088)
    (generator : Fin 6)
    (coordinate : Fin 26) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 1024, by omega⟩
  have state_eq :
      (⟨1024 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0016 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0017 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 26,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.transition (⟨1088 + candidate.val, by omega⟩ : Fin 4374) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector (⟨1088 + candidate.val, by omega⟩ : Fin 4374) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0017
    (state : Fin 4374)
    (lower : 1088 ≤ state.val)
    (upper : state.val < 1152)
    (generator : Fin 6)
    (coordinate : Fin 26) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 1088, by omega⟩
  have state_eq :
      (⟨1088 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0017 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0018 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 26,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.transition (⟨1152 + candidate.val, by omega⟩ : Fin 4374) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector (⟨1152 + candidate.val, by omega⟩ : Fin 4374) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0018
    (state : Fin 4374)
    (lower : 1152 ≤ state.val)
    (upper : state.val < 1216)
    (generator : Fin 6)
    (coordinate : Fin 26) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 1152, by omega⟩
  have state_eq :
      (⟨1152 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0018 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0019 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 26,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.transition (⟨1216 + candidate.val, by omega⟩ : Fin 4374) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector (⟨1216 + candidate.val, by omega⟩ : Fin 4374) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0019
    (state : Fin 4374)
    (lower : 1216 ≤ state.val)
    (upper : state.val < 1280)
    (generator : Fin 6)
    (coordinate : Fin 26) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 1216, by omega⟩
  have state_eq :
      (⟨1216 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0019 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0020 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 26,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.transition (⟨1280 + candidate.val, by omega⟩ : Fin 4374) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector (⟨1280 + candidate.val, by omega⟩ : Fin 4374) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0020
    (state : Fin 4374)
    (lower : 1280 ≤ state.val)
    (upper : state.val < 1344)
    (generator : Fin 6)
    (coordinate : Fin 26) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 1280, by omega⟩
  have state_eq :
      (⟨1280 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0020 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0021 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 26,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.transition (⟨1344 + candidate.val, by omega⟩ : Fin 4374) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector (⟨1344 + candidate.val, by omega⟩ : Fin 4374) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0021
    (state : Fin 4374)
    (lower : 1344 ≤ state.val)
    (upper : state.val < 1408)
    (generator : Fin 6)
    (coordinate : Fin 26) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 1344, by omega⟩
  have state_eq :
      (⟨1344 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0021 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0022 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 26,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.transition (⟨1408 + candidate.val, by omega⟩ : Fin 4374) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector (⟨1408 + candidate.val, by omega⟩ : Fin 4374) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0022
    (state : Fin 4374)
    (lower : 1408 ≤ state.val)
    (upper : state.val < 1472)
    (generator : Fin 6)
    (coordinate : Fin 26) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 1408, by omega⟩
  have state_eq :
      (⟨1408 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0022 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0023 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 26,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.transition (⟨1472 + candidate.val, by omega⟩ : Fin 4374) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector (⟨1472 + candidate.val, by omega⟩ : Fin 4374) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0023
    (state : Fin 4374)
    (lower : 1472 ≤ state.val)
    (upper : state.val < 1536)
    (generator : Fin 6)
    (coordinate : Fin 26) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 1472, by omega⟩
  have state_eq :
      (⟨1472 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0023 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0024 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 26,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.transition (⟨1536 + candidate.val, by omega⟩ : Fin 4374) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector (⟨1536 + candidate.val, by omega⟩ : Fin 4374) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0024
    (state : Fin 4374)
    (lower : 1536 ≤ state.val)
    (upper : state.val < 1600)
    (generator : Fin 6)
    (coordinate : Fin 26) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 1536, by omega⟩
  have state_eq :
      (⟨1536 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0024 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0025 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 26,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.transition (⟨1600 + candidate.val, by omega⟩ : Fin 4374) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector (⟨1600 + candidate.val, by omega⟩ : Fin 4374) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0025
    (state : Fin 4374)
    (lower : 1600 ≤ state.val)
    (upper : state.val < 1664)
    (generator : Fin 6)
    (coordinate : Fin 26) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 1600, by omega⟩
  have state_eq :
      (⟨1600 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0025 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0026 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 26,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.transition (⟨1664 + candidate.val, by omega⟩ : Fin 4374) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector (⟨1664 + candidate.val, by omega⟩ : Fin 4374) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0026
    (state : Fin 4374)
    (lower : 1664 ≤ state.val)
    (upper : state.val < 1728)
    (generator : Fin 6)
    (coordinate : Fin 26) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 1664, by omega⟩
  have state_eq :
      (⟨1664 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0026 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0027 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 26,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.transition (⟨1728 + candidate.val, by omega⟩ : Fin 4374) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector (⟨1728 + candidate.val, by omega⟩ : Fin 4374) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0027
    (state : Fin 4374)
    (lower : 1728 ≤ state.val)
    (upper : state.val < 1792)
    (generator : Fin 6)
    (coordinate : Fin 26) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 1728, by omega⟩
  have state_eq :
      (⟨1728 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0027 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0028 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 26,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.transition (⟨1792 + candidate.val, by omega⟩ : Fin 4374) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector (⟨1792 + candidate.val, by omega⟩ : Fin 4374) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0028
    (state : Fin 4374)
    (lower : 1792 ≤ state.val)
    (upper : state.val < 1856)
    (generator : Fin 6)
    (coordinate : Fin 26) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 1792, by omega⟩
  have state_eq :
      (⟨1792 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0028 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0029 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 26,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.transition (⟨1856 + candidate.val, by omega⟩ : Fin 4374) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector (⟨1856 + candidate.val, by omega⟩ : Fin 4374) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0029
    (state : Fin 4374)
    (lower : 1856 ≤ state.val)
    (upper : state.val < 1920)
    (generator : Fin 6)
    (coordinate : Fin 26) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 1856, by omega⟩
  have state_eq :
      (⟨1856 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0029 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0030 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 26,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.transition (⟨1920 + candidate.val, by omega⟩ : Fin 4374) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector (⟨1920 + candidate.val, by omega⟩ : Fin 4374) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0030
    (state : Fin 4374)
    (lower : 1920 ≤ state.val)
    (upper : state.val < 1984)
    (generator : Fin 6)
    (coordinate : Fin 26) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 1920, by omega⟩
  have state_eq :
      (⟨1920 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0030 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0031 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 26,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.transition (⟨1984 + candidate.val, by omega⟩ : Fin 4374) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector (⟨1984 + candidate.val, by omega⟩ : Fin 4374) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0031
    (state : Fin 4374)
    (lower : 1984 ≤ state.val)
    (upper : state.val < 2048)
    (generator : Fin 6)
    (coordinate : Fin 26) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 1984, by omega⟩
  have state_eq :
      (⟨1984 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0031 offset generator coordinate

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.Shards
