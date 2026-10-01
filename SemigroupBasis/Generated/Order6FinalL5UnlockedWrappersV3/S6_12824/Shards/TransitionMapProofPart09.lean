import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Support.Core
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0288 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨18432 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨18432 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0288
    (state : Fin 48684)
    (lower : 18432 ≤ state.val)
    (upper : state.val < 18496)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 18432, by omega⟩
  have state_eq :
      (⟨18432 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0288 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0289 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨18496 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨18496 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0289
    (state : Fin 48684)
    (lower : 18496 ≤ state.val)
    (upper : state.val < 18560)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 18496, by omega⟩
  have state_eq :
      (⟨18496 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0289 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0290 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨18560 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨18560 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0290
    (state : Fin 48684)
    (lower : 18560 ≤ state.val)
    (upper : state.val < 18624)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 18560, by omega⟩
  have state_eq :
      (⟨18560 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0290 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0291 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨18624 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨18624 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0291
    (state : Fin 48684)
    (lower : 18624 ≤ state.val)
    (upper : state.val < 18688)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 18624, by omega⟩
  have state_eq :
      (⟨18624 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0291 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0292 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨18688 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨18688 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0292
    (state : Fin 48684)
    (lower : 18688 ≤ state.val)
    (upper : state.val < 18752)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 18688, by omega⟩
  have state_eq :
      (⟨18688 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0292 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0293 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨18752 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨18752 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0293
    (state : Fin 48684)
    (lower : 18752 ≤ state.val)
    (upper : state.val < 18816)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 18752, by omega⟩
  have state_eq :
      (⟨18752 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0293 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0294 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨18816 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨18816 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0294
    (state : Fin 48684)
    (lower : 18816 ≤ state.val)
    (upper : state.val < 18880)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 18816, by omega⟩
  have state_eq :
      (⟨18816 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0294 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0295 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨18880 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨18880 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0295
    (state : Fin 48684)
    (lower : 18880 ≤ state.val)
    (upper : state.val < 18944)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 18880, by omega⟩
  have state_eq :
      (⟨18880 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0295 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0296 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨18944 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨18944 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0296
    (state : Fin 48684)
    (lower : 18944 ≤ state.val)
    (upper : state.val < 19008)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 18944, by omega⟩
  have state_eq :
      (⟨18944 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0296 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0297 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨19008 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨19008 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0297
    (state : Fin 48684)
    (lower : 19008 ≤ state.val)
    (upper : state.val < 19072)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 19008, by omega⟩
  have state_eq :
      (⟨19008 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0297 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0298 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨19072 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨19072 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0298
    (state : Fin 48684)
    (lower : 19072 ≤ state.val)
    (upper : state.val < 19136)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 19072, by omega⟩
  have state_eq :
      (⟨19072 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0298 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0299 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨19136 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨19136 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0299
    (state : Fin 48684)
    (lower : 19136 ≤ state.val)
    (upper : state.val < 19200)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 19136, by omega⟩
  have state_eq :
      (⟨19136 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0299 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0300 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨19200 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨19200 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0300
    (state : Fin 48684)
    (lower : 19200 ≤ state.val)
    (upper : state.val < 19264)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 19200, by omega⟩
  have state_eq :
      (⟨19200 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0300 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0301 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨19264 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨19264 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0301
    (state : Fin 48684)
    (lower : 19264 ≤ state.val)
    (upper : state.val < 19328)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 19264, by omega⟩
  have state_eq :
      (⟨19264 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0301 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0302 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨19328 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨19328 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0302
    (state : Fin 48684)
    (lower : 19328 ≤ state.val)
    (upper : state.val < 19392)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 19328, by omega⟩
  have state_eq :
      (⟨19328 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0302 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0303 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨19392 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨19392 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0303
    (state : Fin 48684)
    (lower : 19392 ≤ state.val)
    (upper : state.val < 19456)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 19392, by omega⟩
  have state_eq :
      (⟨19392 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0303 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0304 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨19456 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨19456 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0304
    (state : Fin 48684)
    (lower : 19456 ≤ state.val)
    (upper : state.val < 19520)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 19456, by omega⟩
  have state_eq :
      (⟨19456 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0304 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0305 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨19520 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨19520 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0305
    (state : Fin 48684)
    (lower : 19520 ≤ state.val)
    (upper : state.val < 19584)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 19520, by omega⟩
  have state_eq :
      (⟨19520 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0305 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0306 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨19584 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨19584 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0306
    (state : Fin 48684)
    (lower : 19584 ≤ state.val)
    (upper : state.val < 19648)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 19584, by omega⟩
  have state_eq :
      (⟨19584 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0306 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0307 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨19648 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨19648 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0307
    (state : Fin 48684)
    (lower : 19648 ≤ state.val)
    (upper : state.val < 19712)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 19648, by omega⟩
  have state_eq :
      (⟨19648 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0307 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0308 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨19712 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨19712 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0308
    (state : Fin 48684)
    (lower : 19712 ≤ state.val)
    (upper : state.val < 19776)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 19712, by omega⟩
  have state_eq :
      (⟨19712 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0308 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0309 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨19776 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨19776 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0309
    (state : Fin 48684)
    (lower : 19776 ≤ state.val)
    (upper : state.val < 19840)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 19776, by omega⟩
  have state_eq :
      (⟨19776 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0309 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0310 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨19840 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨19840 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0310
    (state : Fin 48684)
    (lower : 19840 ≤ state.val)
    (upper : state.val < 19904)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 19840, by omega⟩
  have state_eq :
      (⟨19840 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0310 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0311 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨19904 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨19904 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0311
    (state : Fin 48684)
    (lower : 19904 ≤ state.val)
    (upper : state.val < 19968)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 19904, by omega⟩
  have state_eq :
      (⟨19904 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0311 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0312 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨19968 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨19968 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0312
    (state : Fin 48684)
    (lower : 19968 ≤ state.val)
    (upper : state.val < 20032)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 19968, by omega⟩
  have state_eq :
      (⟨19968 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0312 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0313 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨20032 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨20032 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0313
    (state : Fin 48684)
    (lower : 20032 ≤ state.val)
    (upper : state.val < 20096)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 20032, by omega⟩
  have state_eq :
      (⟨20032 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0313 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0314 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨20096 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨20096 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0314
    (state : Fin 48684)
    (lower : 20096 ≤ state.val)
    (upper : state.val < 20160)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 20096, by omega⟩
  have state_eq :
      (⟨20096 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0314 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0315 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨20160 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨20160 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0315
    (state : Fin 48684)
    (lower : 20160 ≤ state.val)
    (upper : state.val < 20224)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 20160, by omega⟩
  have state_eq :
      (⟨20160 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0315 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0316 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨20224 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨20224 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0316
    (state : Fin 48684)
    (lower : 20224 ≤ state.val)
    (upper : state.val < 20288)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 20224, by omega⟩
  have state_eq :
      (⟨20224 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0316 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0317 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨20288 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨20288 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0317
    (state : Fin 48684)
    (lower : 20288 ≤ state.val)
    (upper : state.val < 20352)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 20288, by omega⟩
  have state_eq :
      (⟨20288 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0317 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0318 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨20352 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨20352 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0318
    (state : Fin 48684)
    (lower : 20352 ≤ state.val)
    (upper : state.val < 20416)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 20352, by omega⟩
  have state_eq :
      (⟨20352 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0318 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0319 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨20416 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨20416 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0319
    (state : Fin 48684)
    (lower : 20416 ≤ state.val)
    (upper : state.val < 20480)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 20416, by omega⟩
  have state_eq :
      (⟨20416 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0319 offset generator coordinate

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards
