import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.Support.Core
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.Shards

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0192 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 59,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.transition (⟨12288 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector (⟨12288 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0192
    (state : Fin 17622)
    (lower : 12288 ≤ state.val)
    (upper : state.val < 12352)
    (generator : Fin 6)
    (coordinate : Fin 59) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 12288, by omega⟩
  have state_eq :
      (⟨12288 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0192 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0193 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 59,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.transition (⟨12352 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector (⟨12352 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0193
    (state : Fin 17622)
    (lower : 12352 ≤ state.val)
    (upper : state.val < 12416)
    (generator : Fin 6)
    (coordinate : Fin 59) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 12352, by omega⟩
  have state_eq :
      (⟨12352 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0193 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0194 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 59,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.transition (⟨12416 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector (⟨12416 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0194
    (state : Fin 17622)
    (lower : 12416 ≤ state.val)
    (upper : state.val < 12480)
    (generator : Fin 6)
    (coordinate : Fin 59) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 12416, by omega⟩
  have state_eq :
      (⟨12416 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0194 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0195 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 59,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.transition (⟨12480 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector (⟨12480 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0195
    (state : Fin 17622)
    (lower : 12480 ≤ state.val)
    (upper : state.val < 12544)
    (generator : Fin 6)
    (coordinate : Fin 59) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 12480, by omega⟩
  have state_eq :
      (⟨12480 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0195 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0196 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 59,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.transition (⟨12544 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector (⟨12544 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0196
    (state : Fin 17622)
    (lower : 12544 ≤ state.val)
    (upper : state.val < 12608)
    (generator : Fin 6)
    (coordinate : Fin 59) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 12544, by omega⟩
  have state_eq :
      (⟨12544 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0196 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0197 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 59,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.transition (⟨12608 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector (⟨12608 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0197
    (state : Fin 17622)
    (lower : 12608 ≤ state.val)
    (upper : state.val < 12672)
    (generator : Fin 6)
    (coordinate : Fin 59) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 12608, by omega⟩
  have state_eq :
      (⟨12608 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0197 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0198 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 59,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.transition (⟨12672 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector (⟨12672 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0198
    (state : Fin 17622)
    (lower : 12672 ≤ state.val)
    (upper : state.val < 12736)
    (generator : Fin 6)
    (coordinate : Fin 59) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 12672, by omega⟩
  have state_eq :
      (⟨12672 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0198 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0199 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 59,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.transition (⟨12736 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector (⟨12736 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0199
    (state : Fin 17622)
    (lower : 12736 ≤ state.val)
    (upper : state.val < 12800)
    (generator : Fin 6)
    (coordinate : Fin 59) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 12736, by omega⟩
  have state_eq :
      (⟨12736 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0199 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0200 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 59,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.transition (⟨12800 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector (⟨12800 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0200
    (state : Fin 17622)
    (lower : 12800 ≤ state.val)
    (upper : state.val < 12864)
    (generator : Fin 6)
    (coordinate : Fin 59) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 12800, by omega⟩
  have state_eq :
      (⟨12800 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0200 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0201 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 59,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.transition (⟨12864 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector (⟨12864 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0201
    (state : Fin 17622)
    (lower : 12864 ≤ state.val)
    (upper : state.val < 12928)
    (generator : Fin 6)
    (coordinate : Fin 59) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 12864, by omega⟩
  have state_eq :
      (⟨12864 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0201 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0202 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 59,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.transition (⟨12928 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector (⟨12928 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0202
    (state : Fin 17622)
    (lower : 12928 ≤ state.val)
    (upper : state.val < 12992)
    (generator : Fin 6)
    (coordinate : Fin 59) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 12928, by omega⟩
  have state_eq :
      (⟨12928 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0202 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0203 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 59,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.transition (⟨12992 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector (⟨12992 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0203
    (state : Fin 17622)
    (lower : 12992 ≤ state.val)
    (upper : state.val < 13056)
    (generator : Fin 6)
    (coordinate : Fin 59) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 12992, by omega⟩
  have state_eq :
      (⟨12992 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0203 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0204 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 59,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.transition (⟨13056 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector (⟨13056 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0204
    (state : Fin 17622)
    (lower : 13056 ≤ state.val)
    (upper : state.val < 13120)
    (generator : Fin 6)
    (coordinate : Fin 59) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 13056, by omega⟩
  have state_eq :
      (⟨13056 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0204 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0205 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 59,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.transition (⟨13120 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector (⟨13120 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0205
    (state : Fin 17622)
    (lower : 13120 ≤ state.val)
    (upper : state.val < 13184)
    (generator : Fin 6)
    (coordinate : Fin 59) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 13120, by omega⟩
  have state_eq :
      (⟨13120 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0205 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0206 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 59,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.transition (⟨13184 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector (⟨13184 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0206
    (state : Fin 17622)
    (lower : 13184 ≤ state.val)
    (upper : state.val < 13248)
    (generator : Fin 6)
    (coordinate : Fin 59) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 13184, by omega⟩
  have state_eq :
      (⟨13184 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0206 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0207 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 59,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.transition (⟨13248 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector (⟨13248 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0207
    (state : Fin 17622)
    (lower : 13248 ≤ state.val)
    (upper : state.val < 13312)
    (generator : Fin 6)
    (coordinate : Fin 59) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 13248, by omega⟩
  have state_eq :
      (⟨13248 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0207 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0208 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 59,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.transition (⟨13312 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector (⟨13312 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0208
    (state : Fin 17622)
    (lower : 13312 ≤ state.val)
    (upper : state.val < 13376)
    (generator : Fin 6)
    (coordinate : Fin 59) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 13312, by omega⟩
  have state_eq :
      (⟨13312 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0208 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0209 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 59,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.transition (⟨13376 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector (⟨13376 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0209
    (state : Fin 17622)
    (lower : 13376 ≤ state.val)
    (upper : state.val < 13440)
    (generator : Fin 6)
    (coordinate : Fin 59) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 13376, by omega⟩
  have state_eq :
      (⟨13376 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0209 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0210 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 59,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.transition (⟨13440 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector (⟨13440 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0210
    (state : Fin 17622)
    (lower : 13440 ≤ state.val)
    (upper : state.val < 13504)
    (generator : Fin 6)
    (coordinate : Fin 59) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 13440, by omega⟩
  have state_eq :
      (⟨13440 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0210 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0211 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 59,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.transition (⟨13504 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector (⟨13504 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0211
    (state : Fin 17622)
    (lower : 13504 ≤ state.val)
    (upper : state.val < 13568)
    (generator : Fin 6)
    (coordinate : Fin 59) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 13504, by omega⟩
  have state_eq :
      (⟨13504 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0211 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0212 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 59,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.transition (⟨13568 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector (⟨13568 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0212
    (state : Fin 17622)
    (lower : 13568 ≤ state.val)
    (upper : state.val < 13632)
    (generator : Fin 6)
    (coordinate : Fin 59) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 13568, by omega⟩
  have state_eq :
      (⟨13568 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0212 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0213 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 59,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.transition (⟨13632 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector (⟨13632 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0213
    (state : Fin 17622)
    (lower : 13632 ≤ state.val)
    (upper : state.val < 13696)
    (generator : Fin 6)
    (coordinate : Fin 59) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 13632, by omega⟩
  have state_eq :
      (⟨13632 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0213 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0214 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 59,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.transition (⟨13696 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector (⟨13696 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0214
    (state : Fin 17622)
    (lower : 13696 ≤ state.val)
    (upper : state.val < 13760)
    (generator : Fin 6)
    (coordinate : Fin 59) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 13696, by omega⟩
  have state_eq :
      (⟨13696 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0214 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0215 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 59,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.transition (⟨13760 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector (⟨13760 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0215
    (state : Fin 17622)
    (lower : 13760 ≤ state.val)
    (upper : state.val < 13824)
    (generator : Fin 6)
    (coordinate : Fin 59) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 13760, by omega⟩
  have state_eq :
      (⟨13760 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0215 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0216 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 59,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.transition (⟨13824 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector (⟨13824 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0216
    (state : Fin 17622)
    (lower : 13824 ≤ state.val)
    (upper : state.val < 13888)
    (generator : Fin 6)
    (coordinate : Fin 59) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 13824, by omega⟩
  have state_eq :
      (⟨13824 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0216 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0217 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 59,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.transition (⟨13888 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector (⟨13888 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0217
    (state : Fin 17622)
    (lower : 13888 ≤ state.val)
    (upper : state.val < 13952)
    (generator : Fin 6)
    (coordinate : Fin 59) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 13888, by omega⟩
  have state_eq :
      (⟨13888 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0217 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0218 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 59,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.transition (⟨13952 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector (⟨13952 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0218
    (state : Fin 17622)
    (lower : 13952 ≤ state.val)
    (upper : state.val < 14016)
    (generator : Fin 6)
    (coordinate : Fin 59) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 13952, by omega⟩
  have state_eq :
      (⟨13952 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0218 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0219 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 59,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.transition (⟨14016 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector (⟨14016 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0219
    (state : Fin 17622)
    (lower : 14016 ≤ state.val)
    (upper : state.val < 14080)
    (generator : Fin 6)
    (coordinate : Fin 59) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 14016, by omega⟩
  have state_eq :
      (⟨14016 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0219 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0220 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 59,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.transition (⟨14080 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector (⟨14080 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0220
    (state : Fin 17622)
    (lower : 14080 ≤ state.val)
    (upper : state.val < 14144)
    (generator : Fin 6)
    (coordinate : Fin 59) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 14080, by omega⟩
  have state_eq :
      (⟨14080 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0220 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0221 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 59,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.transition (⟨14144 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector (⟨14144 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0221
    (state : Fin 17622)
    (lower : 14144 ≤ state.val)
    (upper : state.val < 14208)
    (generator : Fin 6)
    (coordinate : Fin 59) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 14144, by omega⟩
  have state_eq :
      (⟨14144 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0221 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0222 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 59,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.transition (⟨14208 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector (⟨14208 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0222
    (state : Fin 17622)
    (lower : 14208 ≤ state.val)
    (upper : state.val < 14272)
    (generator : Fin 6)
    (coordinate : Fin 59) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 14208, by omega⟩
  have state_eq :
      (⟨14208 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0222 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0223 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 59,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.transition (⟨14272 + candidate.val, by omega⟩ : Fin 17622) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector (⟨14272 + candidate.val, by omega⟩ : Fin 17622) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0223
    (state : Fin 17622)
    (lower : 14272 ≤ state.val)
    (upper : state.val < 14336)
    (generator : Fin 6)
    (coordinate : Fin 59) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 14272, by omega⟩
  have state_eq :
      (⟨14272 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0223 offset generator coordinate

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.Shards
