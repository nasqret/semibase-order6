import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Support.Core
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0672 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨43008 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨43008 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0672
    (state : Fin 48684)
    (lower : 43008 ≤ state.val)
    (upper : state.val < 43072)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 43008, by omega⟩
  have state_eq :
      (⟨43008 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0672 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0673 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨43072 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨43072 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0673
    (state : Fin 48684)
    (lower : 43072 ≤ state.val)
    (upper : state.val < 43136)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 43072, by omega⟩
  have state_eq :
      (⟨43072 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0673 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0674 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨43136 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨43136 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0674
    (state : Fin 48684)
    (lower : 43136 ≤ state.val)
    (upper : state.val < 43200)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 43136, by omega⟩
  have state_eq :
      (⟨43136 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0674 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0675 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨43200 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨43200 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0675
    (state : Fin 48684)
    (lower : 43200 ≤ state.val)
    (upper : state.val < 43264)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 43200, by omega⟩
  have state_eq :
      (⟨43200 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0675 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0676 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨43264 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨43264 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0676
    (state : Fin 48684)
    (lower : 43264 ≤ state.val)
    (upper : state.val < 43328)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 43264, by omega⟩
  have state_eq :
      (⟨43264 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0676 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0677 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨43328 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨43328 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0677
    (state : Fin 48684)
    (lower : 43328 ≤ state.val)
    (upper : state.val < 43392)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 43328, by omega⟩
  have state_eq :
      (⟨43328 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0677 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0678 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨43392 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨43392 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0678
    (state : Fin 48684)
    (lower : 43392 ≤ state.val)
    (upper : state.val < 43456)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 43392, by omega⟩
  have state_eq :
      (⟨43392 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0678 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0679 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨43456 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨43456 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0679
    (state : Fin 48684)
    (lower : 43456 ≤ state.val)
    (upper : state.val < 43520)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 43456, by omega⟩
  have state_eq :
      (⟨43456 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0679 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0680 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨43520 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨43520 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0680
    (state : Fin 48684)
    (lower : 43520 ≤ state.val)
    (upper : state.val < 43584)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 43520, by omega⟩
  have state_eq :
      (⟨43520 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0680 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0681 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨43584 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨43584 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0681
    (state : Fin 48684)
    (lower : 43584 ≤ state.val)
    (upper : state.val < 43648)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 43584, by omega⟩
  have state_eq :
      (⟨43584 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0681 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0682 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨43648 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨43648 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0682
    (state : Fin 48684)
    (lower : 43648 ≤ state.val)
    (upper : state.val < 43712)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 43648, by omega⟩
  have state_eq :
      (⟨43648 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0682 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0683 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨43712 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨43712 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0683
    (state : Fin 48684)
    (lower : 43712 ≤ state.val)
    (upper : state.val < 43776)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 43712, by omega⟩
  have state_eq :
      (⟨43712 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0683 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0684 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨43776 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨43776 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0684
    (state : Fin 48684)
    (lower : 43776 ≤ state.val)
    (upper : state.val < 43840)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 43776, by omega⟩
  have state_eq :
      (⟨43776 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0684 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0685 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨43840 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨43840 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0685
    (state : Fin 48684)
    (lower : 43840 ≤ state.val)
    (upper : state.val < 43904)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 43840, by omega⟩
  have state_eq :
      (⟨43840 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0685 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0686 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨43904 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨43904 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0686
    (state : Fin 48684)
    (lower : 43904 ≤ state.val)
    (upper : state.val < 43968)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 43904, by omega⟩
  have state_eq :
      (⟨43904 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0686 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0687 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨43968 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨43968 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0687
    (state : Fin 48684)
    (lower : 43968 ≤ state.val)
    (upper : state.val < 44032)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 43968, by omega⟩
  have state_eq :
      (⟨43968 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0687 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0688 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨44032 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨44032 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0688
    (state : Fin 48684)
    (lower : 44032 ≤ state.val)
    (upper : state.val < 44096)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 44032, by omega⟩
  have state_eq :
      (⟨44032 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0688 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0689 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨44096 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨44096 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0689
    (state : Fin 48684)
    (lower : 44096 ≤ state.val)
    (upper : state.val < 44160)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 44096, by omega⟩
  have state_eq :
      (⟨44096 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0689 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0690 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨44160 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨44160 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0690
    (state : Fin 48684)
    (lower : 44160 ≤ state.val)
    (upper : state.val < 44224)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 44160, by omega⟩
  have state_eq :
      (⟨44160 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0690 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0691 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨44224 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨44224 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0691
    (state : Fin 48684)
    (lower : 44224 ≤ state.val)
    (upper : state.val < 44288)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 44224, by omega⟩
  have state_eq :
      (⟨44224 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0691 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0692 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨44288 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨44288 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0692
    (state : Fin 48684)
    (lower : 44288 ≤ state.val)
    (upper : state.val < 44352)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 44288, by omega⟩
  have state_eq :
      (⟨44288 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0692 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0693 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨44352 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨44352 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0693
    (state : Fin 48684)
    (lower : 44352 ≤ state.val)
    (upper : state.val < 44416)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 44352, by omega⟩
  have state_eq :
      (⟨44352 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0693 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0694 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨44416 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨44416 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0694
    (state : Fin 48684)
    (lower : 44416 ≤ state.val)
    (upper : state.val < 44480)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 44416, by omega⟩
  have state_eq :
      (⟨44416 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0694 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0695 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨44480 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨44480 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0695
    (state : Fin 48684)
    (lower : 44480 ≤ state.val)
    (upper : state.val < 44544)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 44480, by omega⟩
  have state_eq :
      (⟨44480 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0695 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0696 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨44544 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨44544 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0696
    (state : Fin 48684)
    (lower : 44544 ≤ state.val)
    (upper : state.val < 44608)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 44544, by omega⟩
  have state_eq :
      (⟨44544 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0696 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0697 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨44608 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨44608 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0697
    (state : Fin 48684)
    (lower : 44608 ≤ state.val)
    (upper : state.val < 44672)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 44608, by omega⟩
  have state_eq :
      (⟨44608 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0697 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0698 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨44672 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨44672 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0698
    (state : Fin 48684)
    (lower : 44672 ≤ state.val)
    (upper : state.val < 44736)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 44672, by omega⟩
  have state_eq :
      (⟨44672 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0698 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0699 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨44736 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨44736 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0699
    (state : Fin 48684)
    (lower : 44736 ≤ state.val)
    (upper : state.val < 44800)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 44736, by omega⟩
  have state_eq :
      (⟨44736 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0699 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0700 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨44800 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨44800 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0700
    (state : Fin 48684)
    (lower : 44800 ≤ state.val)
    (upper : state.val < 44864)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 44800, by omega⟩
  have state_eq :
      (⟨44800 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0700 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0701 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨44864 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨44864 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0701
    (state : Fin 48684)
    (lower : 44864 ≤ state.val)
    (upper : state.val < 44928)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 44864, by omega⟩
  have state_eq :
      (⟨44864 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0701 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0702 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨44928 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨44928 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0702
    (state : Fin 48684)
    (lower : 44928 ≤ state.val)
    (upper : state.val < 44992)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 44928, by omega⟩
  have state_eq :
      (⟨44928 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0702 offset generator coordinate

set_option maxHeartbeats 2000000 in
theorem transitionMapBounded0703 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 6,
    ∀ coordinate : Fin 211,
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition (⟨44992 + candidate.val, by omega⟩ : Fin 48684) generator)
          coordinate =
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (⟨44992 + candidate.val, by omega⟩ : Fin 48684) coordinate)
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  decide

theorem transitionMapProof0703
    (state : Fin 48684)
    (lower : 44992 ≤ state.val)
    (upper : state.val < 45056)
    (generator : Fin 6)
    (coordinate : Fin 211) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.generatorVector generator coordinate)
    := by
  let offset : Fin 64 := ⟨state.val - 44992, by omega⟩
  have state_eq :
      (⟨44992 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact transitionMapBounded0703 offset generator coordinate

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards
