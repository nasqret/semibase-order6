import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.Support.Core
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.Shards

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0160 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 37,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition (⟨10240 + candidate.val, by omega⟩ : Fin 11184) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.stateVector (⟨10240 + candidate.val, by omega⟩ : Fin 11184) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0160
    (state : Fin 11184)
    (lower : 10240 ≤ state.val)
    (upper : state.val < 10304)
    (generator : Fin 6)
    (coordinate : Fin 37) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 10240, by omega⟩
  have state_eq :
      (⟨10240 + offset.val, by omega⟩ : Fin 11184) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0160 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0161 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 37,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition (⟨10304 + candidate.val, by omega⟩ : Fin 11184) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.stateVector (⟨10304 + candidate.val, by omega⟩ : Fin 11184) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0161
    (state : Fin 11184)
    (lower : 10304 ≤ state.val)
    (upper : state.val < 10368)
    (generator : Fin 6)
    (coordinate : Fin 37) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 10304, by omega⟩
  have state_eq :
      (⟨10304 + offset.val, by omega⟩ : Fin 11184) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0161 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0162 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 37,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition (⟨10368 + candidate.val, by omega⟩ : Fin 11184) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.stateVector (⟨10368 + candidate.val, by omega⟩ : Fin 11184) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0162
    (state : Fin 11184)
    (lower : 10368 ≤ state.val)
    (upper : state.val < 10432)
    (generator : Fin 6)
    (coordinate : Fin 37) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 10368, by omega⟩
  have state_eq :
      (⟨10368 + offset.val, by omega⟩ : Fin 11184) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0162 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0163 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 37,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition (⟨10432 + candidate.val, by omega⟩ : Fin 11184) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.stateVector (⟨10432 + candidate.val, by omega⟩ : Fin 11184) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0163
    (state : Fin 11184)
    (lower : 10432 ≤ state.val)
    (upper : state.val < 10496)
    (generator : Fin 6)
    (coordinate : Fin 37) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 10432, by omega⟩
  have state_eq :
      (⟨10432 + offset.val, by omega⟩ : Fin 11184) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0163 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0164 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 37,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition (⟨10496 + candidate.val, by omega⟩ : Fin 11184) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.stateVector (⟨10496 + candidate.val, by omega⟩ : Fin 11184) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0164
    (state : Fin 11184)
    (lower : 10496 ≤ state.val)
    (upper : state.val < 10560)
    (generator : Fin 6)
    (coordinate : Fin 37) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 10496, by omega⟩
  have state_eq :
      (⟨10496 + offset.val, by omega⟩ : Fin 11184) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0164 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0165 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 37,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition (⟨10560 + candidate.val, by omega⟩ : Fin 11184) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.stateVector (⟨10560 + candidate.val, by omega⟩ : Fin 11184) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0165
    (state : Fin 11184)
    (lower : 10560 ≤ state.val)
    (upper : state.val < 10624)
    (generator : Fin 6)
    (coordinate : Fin 37) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 10560, by omega⟩
  have state_eq :
      (⟨10560 + offset.val, by omega⟩ : Fin 11184) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0165 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0166 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 37,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition (⟨10624 + candidate.val, by omega⟩ : Fin 11184) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.stateVector (⟨10624 + candidate.val, by omega⟩ : Fin 11184) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0166
    (state : Fin 11184)
    (lower : 10624 ≤ state.val)
    (upper : state.val < 10688)
    (generator : Fin 6)
    (coordinate : Fin 37) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 10624, by omega⟩
  have state_eq :
      (⟨10624 + offset.val, by omega⟩ : Fin 11184) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0166 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0167 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 37,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition (⟨10688 + candidate.val, by omega⟩ : Fin 11184) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.stateVector (⟨10688 + candidate.val, by omega⟩ : Fin 11184) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0167
    (state : Fin 11184)
    (lower : 10688 ≤ state.val)
    (upper : state.val < 10752)
    (generator : Fin 6)
    (coordinate : Fin 37) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 10688, by omega⟩
  have state_eq :
      (⟨10688 + offset.val, by omega⟩ : Fin 11184) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0167 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0168 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 37,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition (⟨10752 + candidate.val, by omega⟩ : Fin 11184) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.stateVector (⟨10752 + candidate.val, by omega⟩ : Fin 11184) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0168
    (state : Fin 11184)
    (lower : 10752 ≤ state.val)
    (upper : state.val < 10816)
    (generator : Fin 6)
    (coordinate : Fin 37) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 10752, by omega⟩
  have state_eq :
      (⟨10752 + offset.val, by omega⟩ : Fin 11184) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0168 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0169 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 37,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition (⟨10816 + candidate.val, by omega⟩ : Fin 11184) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.stateVector (⟨10816 + candidate.val, by omega⟩ : Fin 11184) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0169
    (state : Fin 11184)
    (lower : 10816 ≤ state.val)
    (upper : state.val < 10880)
    (generator : Fin 6)
    (coordinate : Fin 37) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 10816, by omega⟩
  have state_eq :
      (⟨10816 + offset.val, by omega⟩ : Fin 11184) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0169 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0170 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 37,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition (⟨10880 + candidate.val, by omega⟩ : Fin 11184) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.stateVector (⟨10880 + candidate.val, by omega⟩ : Fin 11184) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0170
    (state : Fin 11184)
    (lower : 10880 ≤ state.val)
    (upper : state.val < 10944)
    (generator : Fin 6)
    (coordinate : Fin 37) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 10880, by omega⟩
  have state_eq :
      (⟨10880 + offset.val, by omega⟩ : Fin 11184) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0170 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0171 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 37,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition (⟨10944 + candidate.val, by omega⟩ : Fin 11184) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.stateVector (⟨10944 + candidate.val, by omega⟩ : Fin 11184) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0171
    (state : Fin 11184)
    (lower : 10944 ≤ state.val)
    (upper : state.val < 11008)
    (generator : Fin 6)
    (coordinate : Fin 37) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 10944, by omega⟩
  have state_eq :
      (⟨10944 + offset.val, by omega⟩ : Fin 11184) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0171 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0172 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 37,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition (⟨11008 + candidate.val, by omega⟩ : Fin 11184) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.stateVector (⟨11008 + candidate.val, by omega⟩ : Fin 11184) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0172
    (state : Fin 11184)
    (lower : 11008 ≤ state.val)
    (upper : state.val < 11072)
    (generator : Fin 6)
    (coordinate : Fin 37) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 11008, by omega⟩
  have state_eq :
      (⟨11008 + offset.val, by omega⟩ : Fin 11184) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0172 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0173 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 37,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition (⟨11072 + candidate.val, by omega⟩ : Fin 11184) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.stateVector (⟨11072 + candidate.val, by omega⟩ : Fin 11184) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0173
    (state : Fin 11184)
    (lower : 11072 ≤ state.val)
    (upper : state.val < 11136)
    (generator : Fin 6)
    (coordinate : Fin 37) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 11072, by omega⟩
  have state_eq :
      (⟨11072 + offset.val, by omega⟩ : Fin 11184) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0173 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0174 :
    ∀ candidate : Fin 48,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 37,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition (⟨11136 + candidate.val, by omega⟩ : Fin 11184) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.stateVector (⟨11136 + candidate.val, by omega⟩ : Fin 11184) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0174
    (state : Fin 11184)
    (lower : 11136 ≤ state.val)
    (upper : state.val < 11184)
    (generator : Fin 6)
    (coordinate : Fin 37) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.generatorVector generator coordinate)
    := by
  let offset : Fin 48 := ⟨state.val - 11136, by omega⟩
  have state_eq :
      (⟨11136 + offset.val, by omega⟩ : Fin 11184) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0174 offset generator coordinate

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.Shards
