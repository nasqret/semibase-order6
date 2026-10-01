import SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.Support.Core
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.Shards

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0000 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 4,
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.transition (⟨0 + candidate.val, by omega⟩ : Fin 1447) generator) =
        SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_3944.sourceSemigroup.mul (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel (⟨0 + candidate.val, by omega⟩ : Fin 1447))
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0000
    (state : Fin 1447)
    (lower : 0 ≤ state.val)
    (upper : state.val < 64)
    (generator : Fin 4) :
    SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.transition state generator) =
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_3944.sourceSemigroup.mul (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel state)
        (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 0, by omega⟩
  have state_eq :
      (⟨0 + offset.val, by omega⟩ : Fin 1447) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0000 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0001 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 4,
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.transition (⟨64 + candidate.val, by omega⟩ : Fin 1447) generator) =
        SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_3944.sourceSemigroup.mul (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel (⟨64 + candidate.val, by omega⟩ : Fin 1447))
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0001
    (state : Fin 1447)
    (lower : 64 ≤ state.val)
    (upper : state.val < 128)
    (generator : Fin 4) :
    SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.transition state generator) =
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_3944.sourceSemigroup.mul (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel state)
        (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 64, by omega⟩
  have state_eq :
      (⟨64 + offset.val, by omega⟩ : Fin 1447) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0001 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0002 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 4,
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.transition (⟨128 + candidate.val, by omega⟩ : Fin 1447) generator) =
        SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_3944.sourceSemigroup.mul (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel (⟨128 + candidate.val, by omega⟩ : Fin 1447))
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0002
    (state : Fin 1447)
    (lower : 128 ≤ state.val)
    (upper : state.val < 192)
    (generator : Fin 4) :
    SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.transition state generator) =
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_3944.sourceSemigroup.mul (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel state)
        (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 128, by omega⟩
  have state_eq :
      (⟨128 + offset.val, by omega⟩ : Fin 1447) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0002 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0003 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 4,
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.transition (⟨192 + candidate.val, by omega⟩ : Fin 1447) generator) =
        SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_3944.sourceSemigroup.mul (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel (⟨192 + candidate.val, by omega⟩ : Fin 1447))
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0003
    (state : Fin 1447)
    (lower : 192 ≤ state.val)
    (upper : state.val < 256)
    (generator : Fin 4) :
    SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.transition state generator) =
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_3944.sourceSemigroup.mul (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel state)
        (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 192, by omega⟩
  have state_eq :
      (⟨192 + offset.val, by omega⟩ : Fin 1447) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0003 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0004 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 4,
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.transition (⟨256 + candidate.val, by omega⟩ : Fin 1447) generator) =
        SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_3944.sourceSemigroup.mul (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel (⟨256 + candidate.val, by omega⟩ : Fin 1447))
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0004
    (state : Fin 1447)
    (lower : 256 ≤ state.val)
    (upper : state.val < 320)
    (generator : Fin 4) :
    SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.transition state generator) =
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_3944.sourceSemigroup.mul (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel state)
        (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 256, by omega⟩
  have state_eq :
      (⟨256 + offset.val, by omega⟩ : Fin 1447) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0004 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0005 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 4,
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.transition (⟨320 + candidate.val, by omega⟩ : Fin 1447) generator) =
        SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_3944.sourceSemigroup.mul (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel (⟨320 + candidate.val, by omega⟩ : Fin 1447))
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0005
    (state : Fin 1447)
    (lower : 320 ≤ state.val)
    (upper : state.val < 384)
    (generator : Fin 4) :
    SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.transition state generator) =
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_3944.sourceSemigroup.mul (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel state)
        (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 320, by omega⟩
  have state_eq :
      (⟨320 + offset.val, by omega⟩ : Fin 1447) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0005 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0006 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 4,
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.transition (⟨384 + candidate.val, by omega⟩ : Fin 1447) generator) =
        SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_3944.sourceSemigroup.mul (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel (⟨384 + candidate.val, by omega⟩ : Fin 1447))
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0006
    (state : Fin 1447)
    (lower : 384 ≤ state.val)
    (upper : state.val < 448)
    (generator : Fin 4) :
    SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.transition state generator) =
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_3944.sourceSemigroup.mul (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel state)
        (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 384, by omega⟩
  have state_eq :
      (⟨384 + offset.val, by omega⟩ : Fin 1447) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0006 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0007 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 4,
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.transition (⟨448 + candidate.val, by omega⟩ : Fin 1447) generator) =
        SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_3944.sourceSemigroup.mul (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel (⟨448 + candidate.val, by omega⟩ : Fin 1447))
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0007
    (state : Fin 1447)
    (lower : 448 ≤ state.val)
    (upper : state.val < 512)
    (generator : Fin 4) :
    SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.transition state generator) =
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_3944.sourceSemigroup.mul (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel state)
        (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 448, by omega⟩
  have state_eq :
      (⟨448 + offset.val, by omega⟩ : Fin 1447) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0007 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0008 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 4,
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.transition (⟨512 + candidate.val, by omega⟩ : Fin 1447) generator) =
        SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_3944.sourceSemigroup.mul (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel (⟨512 + candidate.val, by omega⟩ : Fin 1447))
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0008
    (state : Fin 1447)
    (lower : 512 ≤ state.val)
    (upper : state.val < 576)
    (generator : Fin 4) :
    SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.transition state generator) =
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_3944.sourceSemigroup.mul (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel state)
        (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 512, by omega⟩
  have state_eq :
      (⟨512 + offset.val, by omega⟩ : Fin 1447) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0008 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0009 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 4,
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.transition (⟨576 + candidate.val, by omega⟩ : Fin 1447) generator) =
        SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_3944.sourceSemigroup.mul (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel (⟨576 + candidate.val, by omega⟩ : Fin 1447))
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0009
    (state : Fin 1447)
    (lower : 576 ≤ state.val)
    (upper : state.val < 640)
    (generator : Fin 4) :
    SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.transition state generator) =
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_3944.sourceSemigroup.mul (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel state)
        (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 576, by omega⟩
  have state_eq :
      (⟨576 + offset.val, by omega⟩ : Fin 1447) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0009 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0010 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 4,
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.transition (⟨640 + candidate.val, by omega⟩ : Fin 1447) generator) =
        SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_3944.sourceSemigroup.mul (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel (⟨640 + candidate.val, by omega⟩ : Fin 1447))
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0010
    (state : Fin 1447)
    (lower : 640 ≤ state.val)
    (upper : state.val < 704)
    (generator : Fin 4) :
    SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.transition state generator) =
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_3944.sourceSemigroup.mul (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel state)
        (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 640, by omega⟩
  have state_eq :
      (⟨640 + offset.val, by omega⟩ : Fin 1447) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0010 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0011 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 4,
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.transition (⟨704 + candidate.val, by omega⟩ : Fin 1447) generator) =
        SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_3944.sourceSemigroup.mul (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel (⟨704 + candidate.val, by omega⟩ : Fin 1447))
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0011
    (state : Fin 1447)
    (lower : 704 ≤ state.val)
    (upper : state.val < 768)
    (generator : Fin 4) :
    SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.transition state generator) =
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_3944.sourceSemigroup.mul (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel state)
        (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 704, by omega⟩
  have state_eq :
      (⟨704 + offset.val, by omega⟩ : Fin 1447) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0011 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0012 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 4,
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.transition (⟨768 + candidate.val, by omega⟩ : Fin 1447) generator) =
        SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_3944.sourceSemigroup.mul (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel (⟨768 + candidate.val, by omega⟩ : Fin 1447))
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0012
    (state : Fin 1447)
    (lower : 768 ≤ state.val)
    (upper : state.val < 832)
    (generator : Fin 4) :
    SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.transition state generator) =
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_3944.sourceSemigroup.mul (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel state)
        (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 768, by omega⟩
  have state_eq :
      (⟨768 + offset.val, by omega⟩ : Fin 1447) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0012 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0013 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 4,
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.transition (⟨832 + candidate.val, by omega⟩ : Fin 1447) generator) =
        SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_3944.sourceSemigroup.mul (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel (⟨832 + candidate.val, by omega⟩ : Fin 1447))
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0013
    (state : Fin 1447)
    (lower : 832 ≤ state.val)
    (upper : state.val < 896)
    (generator : Fin 4) :
    SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.transition state generator) =
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_3944.sourceSemigroup.mul (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel state)
        (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 832, by omega⟩
  have state_eq :
      (⟨832 + offset.val, by omega⟩ : Fin 1447) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0013 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0014 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 4,
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.transition (⟨896 + candidate.val, by omega⟩ : Fin 1447) generator) =
        SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_3944.sourceSemigroup.mul (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel (⟨896 + candidate.val, by omega⟩ : Fin 1447))
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0014
    (state : Fin 1447)
    (lower : 896 ≤ state.val)
    (upper : state.val < 960)
    (generator : Fin 4) :
    SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.transition state generator) =
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_3944.sourceSemigroup.mul (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel state)
        (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 896, by omega⟩
  have state_eq :
      (⟨896 + offset.val, by omega⟩ : Fin 1447) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0014 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0015 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 4,
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.transition (⟨960 + candidate.val, by omega⟩ : Fin 1447) generator) =
        SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_3944.sourceSemigroup.mul (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel (⟨960 + candidate.val, by omega⟩ : Fin 1447))
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0015
    (state : Fin 1447)
    (lower : 960 ≤ state.val)
    (upper : state.val < 1024)
    (generator : Fin 4) :
    SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.transition state generator) =
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_3944.sourceSemigroup.mul (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel state)
        (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 960, by omega⟩
  have state_eq :
      (⟨960 + offset.val, by omega⟩ : Fin 1447) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0015 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0016 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 4,
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.transition (⟨1024 + candidate.val, by omega⟩ : Fin 1447) generator) =
        SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_3944.sourceSemigroup.mul (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel (⟨1024 + candidate.val, by omega⟩ : Fin 1447))
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0016
    (state : Fin 1447)
    (lower : 1024 ≤ state.val)
    (upper : state.val < 1088)
    (generator : Fin 4) :
    SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.transition state generator) =
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_3944.sourceSemigroup.mul (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel state)
        (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 1024, by omega⟩
  have state_eq :
      (⟨1024 + offset.val, by omega⟩ : Fin 1447) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0016 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0017 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 4,
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.transition (⟨1088 + candidate.val, by omega⟩ : Fin 1447) generator) =
        SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_3944.sourceSemigroup.mul (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel (⟨1088 + candidate.val, by omega⟩ : Fin 1447))
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0017
    (state : Fin 1447)
    (lower : 1088 ≤ state.val)
    (upper : state.val < 1152)
    (generator : Fin 4) :
    SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.transition state generator) =
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_3944.sourceSemigroup.mul (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel state)
        (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 1088, by omega⟩
  have state_eq :
      (⟨1088 + offset.val, by omega⟩ : Fin 1447) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0017 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0018 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 4,
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.transition (⟨1152 + candidate.val, by omega⟩ : Fin 1447) generator) =
        SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_3944.sourceSemigroup.mul (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel (⟨1152 + candidate.val, by omega⟩ : Fin 1447))
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0018
    (state : Fin 1447)
    (lower : 1152 ≤ state.val)
    (upper : state.val < 1216)
    (generator : Fin 4) :
    SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.transition state generator) =
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_3944.sourceSemigroup.mul (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel state)
        (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 1152, by omega⟩
  have state_eq :
      (⟨1152 + offset.val, by omega⟩ : Fin 1447) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0018 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0019 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 4,
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.transition (⟨1216 + candidate.val, by omega⟩ : Fin 1447) generator) =
        SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_3944.sourceSemigroup.mul (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel (⟨1216 + candidate.val, by omega⟩ : Fin 1447))
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0019
    (state : Fin 1447)
    (lower : 1216 ≤ state.val)
    (upper : state.val < 1280)
    (generator : Fin 4) :
    SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.transition state generator) =
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_3944.sourceSemigroup.mul (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel state)
        (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 1216, by omega⟩
  have state_eq :
      (⟨1216 + offset.val, by omega⟩ : Fin 1447) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0019 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0020 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 4,
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.transition (⟨1280 + candidate.val, by omega⟩ : Fin 1447) generator) =
        SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_3944.sourceSemigroup.mul (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel (⟨1280 + candidate.val, by omega⟩ : Fin 1447))
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0020
    (state : Fin 1447)
    (lower : 1280 ≤ state.val)
    (upper : state.val < 1344)
    (generator : Fin 4) :
    SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.transition state generator) =
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_3944.sourceSemigroup.mul (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel state)
        (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 1280, by omega⟩
  have state_eq :
      (⟨1280 + offset.val, by omega⟩ : Fin 1447) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0020 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0021 :
    ∀ candidate : Fin 64,
    ∀ generator : Fin 4,
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.transition (⟨1344 + candidate.val, by omega⟩ : Fin 1447) generator) =
        SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_3944.sourceSemigroup.mul (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel (⟨1344 + candidate.val, by omega⟩ : Fin 1447))
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0021
    (state : Fin 1447)
    (lower : 1344 ≤ state.val)
    (upper : state.val < 1408)
    (generator : Fin 4) :
    SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.transition state generator) =
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_3944.sourceSemigroup.mul (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel state)
        (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.generatorSourceLabel generator) := by
  let offset : Fin 64 := ⟨state.val - 1344, by omega⟩
  have state_eq :
      (⟨1344 + offset.val, by omega⟩ : Fin 1447) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0021 offset generator

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransitionBounded0022 :
    ∀ candidate : Fin 39,
    ∀ generator : Fin 4,
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.transition (⟨1408 + candidate.val, by omega⟩ : Fin 1447) generator) =
        SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_3944.sourceSemigroup.mul (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel (⟨1408 + candidate.val, by omega⟩ : Fin 1447))
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.generatorSourceLabel generator) := by
  decide

theorem sourceLabelTransitionProof0022
    (state : Fin 1447)
    (lower : 1408 ≤ state.val)
    (upper : state.val < 1447)
    (generator : Fin 4) :
    SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.transition state generator) =
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_3944.sourceSemigroup.mul (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.sourceLabel state)
        (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.generatorSourceLabel generator) := by
  let offset : Fin 39 := ⟨state.val - 1408, by omega⟩
  have state_eq :
      (⟨1408 + offset.val, by omega⟩ : Fin 1447) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact sourceLabelTransitionBounded0022 offset generator

end SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.Shards
