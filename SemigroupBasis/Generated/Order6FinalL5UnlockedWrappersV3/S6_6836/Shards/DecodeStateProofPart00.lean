import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6836.Shards.DecodeState
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6836.Shards.StateVector
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6836.Shards

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0000 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨0 + candidate.val, by omega⟩ : Fin 7782)) =
        (⟨0 + candidate.val, by omega⟩ : Fin 7782) := by
  decide

theorem decodeState_stateVectorProof0000
    (state : Fin 7782)
    (lower : 0 ≤ state.val)
    (upper : state.val < 64) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 0, by omega⟩
  have state_eq :
      (⟨0 + offset.val, by omega⟩ : Fin 7782) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0000 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0001 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨64 + candidate.val, by omega⟩ : Fin 7782)) =
        (⟨64 + candidate.val, by omega⟩ : Fin 7782) := by
  decide

theorem decodeState_stateVectorProof0001
    (state : Fin 7782)
    (lower : 64 ≤ state.val)
    (upper : state.val < 128) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 64, by omega⟩
  have state_eq :
      (⟨64 + offset.val, by omega⟩ : Fin 7782) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0001 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0002 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨128 + candidate.val, by omega⟩ : Fin 7782)) =
        (⟨128 + candidate.val, by omega⟩ : Fin 7782) := by
  decide

theorem decodeState_stateVectorProof0002
    (state : Fin 7782)
    (lower : 128 ≤ state.val)
    (upper : state.val < 192) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 128, by omega⟩
  have state_eq :
      (⟨128 + offset.val, by omega⟩ : Fin 7782) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0002 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0003 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨192 + candidate.val, by omega⟩ : Fin 7782)) =
        (⟨192 + candidate.val, by omega⟩ : Fin 7782) := by
  decide

theorem decodeState_stateVectorProof0003
    (state : Fin 7782)
    (lower : 192 ≤ state.val)
    (upper : state.val < 256) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 192, by omega⟩
  have state_eq :
      (⟨192 + offset.val, by omega⟩ : Fin 7782) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0003 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0004 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨256 + candidate.val, by omega⟩ : Fin 7782)) =
        (⟨256 + candidate.val, by omega⟩ : Fin 7782) := by
  decide

theorem decodeState_stateVectorProof0004
    (state : Fin 7782)
    (lower : 256 ≤ state.val)
    (upper : state.val < 320) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 256, by omega⟩
  have state_eq :
      (⟨256 + offset.val, by omega⟩ : Fin 7782) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0004 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0005 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨320 + candidate.val, by omega⟩ : Fin 7782)) =
        (⟨320 + candidate.val, by omega⟩ : Fin 7782) := by
  decide

theorem decodeState_stateVectorProof0005
    (state : Fin 7782)
    (lower : 320 ≤ state.val)
    (upper : state.val < 384) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 320, by omega⟩
  have state_eq :
      (⟨320 + offset.val, by omega⟩ : Fin 7782) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0005 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0006 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨384 + candidate.val, by omega⟩ : Fin 7782)) =
        (⟨384 + candidate.val, by omega⟩ : Fin 7782) := by
  decide

theorem decodeState_stateVectorProof0006
    (state : Fin 7782)
    (lower : 384 ≤ state.val)
    (upper : state.val < 448) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 384, by omega⟩
  have state_eq :
      (⟨384 + offset.val, by omega⟩ : Fin 7782) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0006 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0007 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨448 + candidate.val, by omega⟩ : Fin 7782)) =
        (⟨448 + candidate.val, by omega⟩ : Fin 7782) := by
  decide

theorem decodeState_stateVectorProof0007
    (state : Fin 7782)
    (lower : 448 ≤ state.val)
    (upper : state.val < 512) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 448, by omega⟩
  have state_eq :
      (⟨448 + offset.val, by omega⟩ : Fin 7782) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0007 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0008 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨512 + candidate.val, by omega⟩ : Fin 7782)) =
        (⟨512 + candidate.val, by omega⟩ : Fin 7782) := by
  decide

theorem decodeState_stateVectorProof0008
    (state : Fin 7782)
    (lower : 512 ≤ state.val)
    (upper : state.val < 576) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 512, by omega⟩
  have state_eq :
      (⟨512 + offset.val, by omega⟩ : Fin 7782) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0008 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0009 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨576 + candidate.val, by omega⟩ : Fin 7782)) =
        (⟨576 + candidate.val, by omega⟩ : Fin 7782) := by
  decide

theorem decodeState_stateVectorProof0009
    (state : Fin 7782)
    (lower : 576 ≤ state.val)
    (upper : state.val < 640) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 576, by omega⟩
  have state_eq :
      (⟨576 + offset.val, by omega⟩ : Fin 7782) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0009 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0010 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨640 + candidate.val, by omega⟩ : Fin 7782)) =
        (⟨640 + candidate.val, by omega⟩ : Fin 7782) := by
  decide

theorem decodeState_stateVectorProof0010
    (state : Fin 7782)
    (lower : 640 ≤ state.val)
    (upper : state.val < 704) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 640, by omega⟩
  have state_eq :
      (⟨640 + offset.val, by omega⟩ : Fin 7782) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0010 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0011 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨704 + candidate.val, by omega⟩ : Fin 7782)) =
        (⟨704 + candidate.val, by omega⟩ : Fin 7782) := by
  decide

theorem decodeState_stateVectorProof0011
    (state : Fin 7782)
    (lower : 704 ≤ state.val)
    (upper : state.val < 768) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 704, by omega⟩
  have state_eq :
      (⟨704 + offset.val, by omega⟩ : Fin 7782) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0011 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0012 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨768 + candidate.val, by omega⟩ : Fin 7782)) =
        (⟨768 + candidate.val, by omega⟩ : Fin 7782) := by
  decide

theorem decodeState_stateVectorProof0012
    (state : Fin 7782)
    (lower : 768 ≤ state.val)
    (upper : state.val < 832) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 768, by omega⟩
  have state_eq :
      (⟨768 + offset.val, by omega⟩ : Fin 7782) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0012 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0013 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨832 + candidate.val, by omega⟩ : Fin 7782)) =
        (⟨832 + candidate.val, by omega⟩ : Fin 7782) := by
  decide

theorem decodeState_stateVectorProof0013
    (state : Fin 7782)
    (lower : 832 ≤ state.val)
    (upper : state.val < 896) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 832, by omega⟩
  have state_eq :
      (⟨832 + offset.val, by omega⟩ : Fin 7782) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0013 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0014 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨896 + candidate.val, by omega⟩ : Fin 7782)) =
        (⟨896 + candidate.val, by omega⟩ : Fin 7782) := by
  decide

theorem decodeState_stateVectorProof0014
    (state : Fin 7782)
    (lower : 896 ≤ state.val)
    (upper : state.val < 960) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 896, by omega⟩
  have state_eq :
      (⟨896 + offset.val, by omega⟩ : Fin 7782) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0014 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0015 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨960 + candidate.val, by omega⟩ : Fin 7782)) =
        (⟨960 + candidate.val, by omega⟩ : Fin 7782) := by
  decide

theorem decodeState_stateVectorProof0015
    (state : Fin 7782)
    (lower : 960 ≤ state.val)
    (upper : state.val < 1024) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 960, by omega⟩
  have state_eq :
      (⟨960 + offset.val, by omega⟩ : Fin 7782) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0015 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0016 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨1024 + candidate.val, by omega⟩ : Fin 7782)) =
        (⟨1024 + candidate.val, by omega⟩ : Fin 7782) := by
  decide

theorem decodeState_stateVectorProof0016
    (state : Fin 7782)
    (lower : 1024 ≤ state.val)
    (upper : state.val < 1088) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 1024, by omega⟩
  have state_eq :
      (⟨1024 + offset.val, by omega⟩ : Fin 7782) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0016 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0017 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨1088 + candidate.val, by omega⟩ : Fin 7782)) =
        (⟨1088 + candidate.val, by omega⟩ : Fin 7782) := by
  decide

theorem decodeState_stateVectorProof0017
    (state : Fin 7782)
    (lower : 1088 ≤ state.val)
    (upper : state.val < 1152) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 1088, by omega⟩
  have state_eq :
      (⟨1088 + offset.val, by omega⟩ : Fin 7782) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0017 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0018 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨1152 + candidate.val, by omega⟩ : Fin 7782)) =
        (⟨1152 + candidate.val, by omega⟩ : Fin 7782) := by
  decide

theorem decodeState_stateVectorProof0018
    (state : Fin 7782)
    (lower : 1152 ≤ state.val)
    (upper : state.val < 1216) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 1152, by omega⟩
  have state_eq :
      (⟨1152 + offset.val, by omega⟩ : Fin 7782) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0018 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0019 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨1216 + candidate.val, by omega⟩ : Fin 7782)) =
        (⟨1216 + candidate.val, by omega⟩ : Fin 7782) := by
  decide

theorem decodeState_stateVectorProof0019
    (state : Fin 7782)
    (lower : 1216 ≤ state.val)
    (upper : state.val < 1280) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 1216, by omega⟩
  have state_eq :
      (⟨1216 + offset.val, by omega⟩ : Fin 7782) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0019 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0020 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨1280 + candidate.val, by omega⟩ : Fin 7782)) =
        (⟨1280 + candidate.val, by omega⟩ : Fin 7782) := by
  decide

theorem decodeState_stateVectorProof0020
    (state : Fin 7782)
    (lower : 1280 ≤ state.val)
    (upper : state.val < 1344) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 1280, by omega⟩
  have state_eq :
      (⟨1280 + offset.val, by omega⟩ : Fin 7782) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0020 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0021 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨1344 + candidate.val, by omega⟩ : Fin 7782)) =
        (⟨1344 + candidate.val, by omega⟩ : Fin 7782) := by
  decide

theorem decodeState_stateVectorProof0021
    (state : Fin 7782)
    (lower : 1344 ≤ state.val)
    (upper : state.val < 1408) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 1344, by omega⟩
  have state_eq :
      (⟨1344 + offset.val, by omega⟩ : Fin 7782) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0021 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0022 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨1408 + candidate.val, by omega⟩ : Fin 7782)) =
        (⟨1408 + candidate.val, by omega⟩ : Fin 7782) := by
  decide

theorem decodeState_stateVectorProof0022
    (state : Fin 7782)
    (lower : 1408 ≤ state.val)
    (upper : state.val < 1472) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 1408, by omega⟩
  have state_eq :
      (⟨1408 + offset.val, by omega⟩ : Fin 7782) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0022 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0023 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨1472 + candidate.val, by omega⟩ : Fin 7782)) =
        (⟨1472 + candidate.val, by omega⟩ : Fin 7782) := by
  decide

theorem decodeState_stateVectorProof0023
    (state : Fin 7782)
    (lower : 1472 ≤ state.val)
    (upper : state.val < 1536) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 1472, by omega⟩
  have state_eq :
      (⟨1472 + offset.val, by omega⟩ : Fin 7782) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0023 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0024 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨1536 + candidate.val, by omega⟩ : Fin 7782)) =
        (⟨1536 + candidate.val, by omega⟩ : Fin 7782) := by
  decide

theorem decodeState_stateVectorProof0024
    (state : Fin 7782)
    (lower : 1536 ≤ state.val)
    (upper : state.val < 1600) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 1536, by omega⟩
  have state_eq :
      (⟨1536 + offset.val, by omega⟩ : Fin 7782) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0024 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0025 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨1600 + candidate.val, by omega⟩ : Fin 7782)) =
        (⟨1600 + candidate.val, by omega⟩ : Fin 7782) := by
  decide

theorem decodeState_stateVectorProof0025
    (state : Fin 7782)
    (lower : 1600 ≤ state.val)
    (upper : state.val < 1664) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 1600, by omega⟩
  have state_eq :
      (⟨1600 + offset.val, by omega⟩ : Fin 7782) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0025 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0026 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨1664 + candidate.val, by omega⟩ : Fin 7782)) =
        (⟨1664 + candidate.val, by omega⟩ : Fin 7782) := by
  decide

theorem decodeState_stateVectorProof0026
    (state : Fin 7782)
    (lower : 1664 ≤ state.val)
    (upper : state.val < 1728) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 1664, by omega⟩
  have state_eq :
      (⟨1664 + offset.val, by omega⟩ : Fin 7782) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0026 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0027 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨1728 + candidate.val, by omega⟩ : Fin 7782)) =
        (⟨1728 + candidate.val, by omega⟩ : Fin 7782) := by
  decide

theorem decodeState_stateVectorProof0027
    (state : Fin 7782)
    (lower : 1728 ≤ state.val)
    (upper : state.val < 1792) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 1728, by omega⟩
  have state_eq :
      (⟨1728 + offset.val, by omega⟩ : Fin 7782) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0027 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0028 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨1792 + candidate.val, by omega⟩ : Fin 7782)) =
        (⟨1792 + candidate.val, by omega⟩ : Fin 7782) := by
  decide

theorem decodeState_stateVectorProof0028
    (state : Fin 7782)
    (lower : 1792 ≤ state.val)
    (upper : state.val < 1856) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 1792, by omega⟩
  have state_eq :
      (⟨1792 + offset.val, by omega⟩ : Fin 7782) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0028 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0029 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨1856 + candidate.val, by omega⟩ : Fin 7782)) =
        (⟨1856 + candidate.val, by omega⟩ : Fin 7782) := by
  decide

theorem decodeState_stateVectorProof0029
    (state : Fin 7782)
    (lower : 1856 ≤ state.val)
    (upper : state.val < 1920) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 1856, by omega⟩
  have state_eq :
      (⟨1856 + offset.val, by omega⟩ : Fin 7782) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0029 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0030 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨1920 + candidate.val, by omega⟩ : Fin 7782)) =
        (⟨1920 + candidate.val, by omega⟩ : Fin 7782) := by
  decide

theorem decodeState_stateVectorProof0030
    (state : Fin 7782)
    (lower : 1920 ≤ state.val)
    (upper : state.val < 1984) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 1920, by omega⟩
  have state_eq :
      (⟨1920 + offset.val, by omega⟩ : Fin 7782) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0030 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0031 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨1984 + candidate.val, by omega⟩ : Fin 7782)) =
        (⟨1984 + candidate.val, by omega⟩ : Fin 7782) := by
  decide

theorem decodeState_stateVectorProof0031
    (state : Fin 7782)
    (lower : 1984 ≤ state.val)
    (upper : state.val < 2048) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 1984, by omega⟩
  have state_eq :
      (⟨1984 + offset.val, by omega⟩ : Fin 7782) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0031 offset

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6836.Shards
