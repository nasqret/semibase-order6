import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Support.Core
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0704 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨45056 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨45056 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0704
    (state : Fin 48684)
    (lower : 45056 ≤ state.val)
    (upper : state.val < 45120)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 45056, by omega⟩
  have state_eq :
      (⟨45056 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0704 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0705 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨45120 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨45120 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0705
    (state : Fin 48684)
    (lower : 45120 ≤ state.val)
    (upper : state.val < 45184)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 45120, by omega⟩
  have state_eq :
      (⟨45120 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0705 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0706 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨45184 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨45184 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0706
    (state : Fin 48684)
    (lower : 45184 ≤ state.val)
    (upper : state.val < 45248)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 45184, by omega⟩
  have state_eq :
      (⟨45184 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0706 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0707 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨45248 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨45248 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0707
    (state : Fin 48684)
    (lower : 45248 ≤ state.val)
    (upper : state.val < 45312)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 45248, by omega⟩
  have state_eq :
      (⟨45248 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0707 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0708 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨45312 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨45312 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0708
    (state : Fin 48684)
    (lower : 45312 ≤ state.val)
    (upper : state.val < 45376)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 45312, by omega⟩
  have state_eq :
      (⟨45312 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0708 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0709 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨45376 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨45376 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0709
    (state : Fin 48684)
    (lower : 45376 ≤ state.val)
    (upper : state.val < 45440)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 45376, by omega⟩
  have state_eq :
      (⟨45376 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0709 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0710 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨45440 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨45440 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0710
    (state : Fin 48684)
    (lower : 45440 ≤ state.val)
    (upper : state.val < 45504)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 45440, by omega⟩
  have state_eq :
      (⟨45440 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0710 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0711 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨45504 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨45504 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0711
    (state : Fin 48684)
    (lower : 45504 ≤ state.val)
    (upper : state.val < 45568)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 45504, by omega⟩
  have state_eq :
      (⟨45504 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0711 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0712 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨45568 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨45568 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0712
    (state : Fin 48684)
    (lower : 45568 ≤ state.val)
    (upper : state.val < 45632)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 45568, by omega⟩
  have state_eq :
      (⟨45568 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0712 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0713 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨45632 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨45632 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0713
    (state : Fin 48684)
    (lower : 45632 ≤ state.val)
    (upper : state.val < 45696)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 45632, by omega⟩
  have state_eq :
      (⟨45632 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0713 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0714 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨45696 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨45696 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0714
    (state : Fin 48684)
    (lower : 45696 ≤ state.val)
    (upper : state.val < 45760)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 45696, by omega⟩
  have state_eq :
      (⟨45696 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0714 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0715 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨45760 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨45760 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0715
    (state : Fin 48684)
    (lower : 45760 ≤ state.val)
    (upper : state.val < 45824)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 45760, by omega⟩
  have state_eq :
      (⟨45760 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0715 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0716 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨45824 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨45824 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0716
    (state : Fin 48684)
    (lower : 45824 ≤ state.val)
    (upper : state.val < 45888)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 45824, by omega⟩
  have state_eq :
      (⟨45824 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0716 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0717 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨45888 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨45888 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0717
    (state : Fin 48684)
    (lower : 45888 ≤ state.val)
    (upper : state.val < 45952)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 45888, by omega⟩
  have state_eq :
      (⟨45888 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0717 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0718 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨45952 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨45952 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0718
    (state : Fin 48684)
    (lower : 45952 ≤ state.val)
    (upper : state.val < 46016)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 45952, by omega⟩
  have state_eq :
      (⟨45952 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0718 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0719 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨46016 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨46016 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0719
    (state : Fin 48684)
    (lower : 46016 ≤ state.val)
    (upper : state.val < 46080)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 46016, by omega⟩
  have state_eq :
      (⟨46016 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0719 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0720 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨46080 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨46080 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0720
    (state : Fin 48684)
    (lower : 46080 ≤ state.val)
    (upper : state.val < 46144)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 46080, by omega⟩
  have state_eq :
      (⟨46080 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0720 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0721 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨46144 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨46144 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0721
    (state : Fin 48684)
    (lower : 46144 ≤ state.val)
    (upper : state.val < 46208)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 46144, by omega⟩
  have state_eq :
      (⟨46144 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0721 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0722 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨46208 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨46208 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0722
    (state : Fin 48684)
    (lower : 46208 ≤ state.val)
    (upper : state.val < 46272)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 46208, by omega⟩
  have state_eq :
      (⟨46208 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0722 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0723 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨46272 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨46272 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0723
    (state : Fin 48684)
    (lower : 46272 ≤ state.val)
    (upper : state.val < 46336)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 46272, by omega⟩
  have state_eq :
      (⟨46272 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0723 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0724 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨46336 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨46336 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0724
    (state : Fin 48684)
    (lower : 46336 ≤ state.val)
    (upper : state.val < 46400)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 46336, by omega⟩
  have state_eq :
      (⟨46336 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0724 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0725 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨46400 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨46400 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0725
    (state : Fin 48684)
    (lower : 46400 ≤ state.val)
    (upper : state.val < 46464)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 46400, by omega⟩
  have state_eq :
      (⟨46400 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0725 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0726 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨46464 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨46464 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0726
    (state : Fin 48684)
    (lower : 46464 ≤ state.val)
    (upper : state.val < 46528)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 46464, by omega⟩
  have state_eq :
      (⟨46464 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0726 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0727 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨46528 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨46528 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0727
    (state : Fin 48684)
    (lower : 46528 ≤ state.val)
    (upper : state.val < 46592)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 46528, by omega⟩
  have state_eq :
      (⟨46528 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0727 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0728 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨46592 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨46592 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0728
    (state : Fin 48684)
    (lower : 46592 ≤ state.val)
    (upper : state.val < 46656)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 46592, by omega⟩
  have state_eq :
      (⟨46592 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0728 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0729 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨46656 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨46656 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0729
    (state : Fin 48684)
    (lower : 46656 ≤ state.val)
    (upper : state.val < 46720)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 46656, by omega⟩
  have state_eq :
      (⟨46656 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0729 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0730 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨46720 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨46720 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0730
    (state : Fin 48684)
    (lower : 46720 ≤ state.val)
    (upper : state.val < 46784)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 46720, by omega⟩
  have state_eq :
      (⟨46720 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0730 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0731 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨46784 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨46784 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0731
    (state : Fin 48684)
    (lower : 46784 ≤ state.val)
    (upper : state.val < 46848)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 46784, by omega⟩
  have state_eq :
      (⟨46784 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0731 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0732 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨46848 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨46848 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0732
    (state : Fin 48684)
    (lower : 46848 ≤ state.val)
    (upper : state.val < 46912)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 46848, by omega⟩
  have state_eq :
      (⟨46848 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0732 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0733 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨46912 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨46912 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0733
    (state : Fin 48684)
    (lower : 46912 ≤ state.val)
    (upper : state.val < 46976)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 46912, by omega⟩
  have state_eq :
      (⟨46912 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0733 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0734 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨46976 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨46976 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0734
    (state : Fin 48684)
    (lower : 46976 ≤ state.val)
    (upper : state.val < 47040)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 46976, by omega⟩
  have state_eq :
      (⟨46976 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0734 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0735 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨47040 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨47040 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0735
    (state : Fin 48684)
    (lower : 47040 ≤ state.val)
    (upper : state.val < 47104)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 47040, by omega⟩
  have state_eq :
      (⟨47040 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0735 offset generator coordinate

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards
