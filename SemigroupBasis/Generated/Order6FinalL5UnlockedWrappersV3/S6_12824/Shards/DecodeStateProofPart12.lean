import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards.DecodeState
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards.StateVector
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0384 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨24576 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨24576 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0384
    (state : Fin 48684)
    (lower : 24576 ≤ state.val)
    (upper : state.val < 24640) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 24576, by omega⟩
  have state_eq :
      (⟨24576 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0384 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0385 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨24640 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨24640 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0385
    (state : Fin 48684)
    (lower : 24640 ≤ state.val)
    (upper : state.val < 24704) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 24640, by omega⟩
  have state_eq :
      (⟨24640 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0385 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0386 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨24704 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨24704 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0386
    (state : Fin 48684)
    (lower : 24704 ≤ state.val)
    (upper : state.val < 24768) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 24704, by omega⟩
  have state_eq :
      (⟨24704 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0386 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0387 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨24768 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨24768 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0387
    (state : Fin 48684)
    (lower : 24768 ≤ state.val)
    (upper : state.val < 24832) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 24768, by omega⟩
  have state_eq :
      (⟨24768 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0387 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0388 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨24832 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨24832 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0388
    (state : Fin 48684)
    (lower : 24832 ≤ state.val)
    (upper : state.val < 24896) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 24832, by omega⟩
  have state_eq :
      (⟨24832 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0388 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0389 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨24896 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨24896 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0389
    (state : Fin 48684)
    (lower : 24896 ≤ state.val)
    (upper : state.val < 24960) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 24896, by omega⟩
  have state_eq :
      (⟨24896 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0389 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0390 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨24960 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨24960 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0390
    (state : Fin 48684)
    (lower : 24960 ≤ state.val)
    (upper : state.val < 25024) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 24960, by omega⟩
  have state_eq :
      (⟨24960 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0390 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0391 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨25024 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨25024 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0391
    (state : Fin 48684)
    (lower : 25024 ≤ state.val)
    (upper : state.val < 25088) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 25024, by omega⟩
  have state_eq :
      (⟨25024 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0391 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0392 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨25088 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨25088 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0392
    (state : Fin 48684)
    (lower : 25088 ≤ state.val)
    (upper : state.val < 25152) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 25088, by omega⟩
  have state_eq :
      (⟨25088 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0392 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0393 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨25152 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨25152 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0393
    (state : Fin 48684)
    (lower : 25152 ≤ state.val)
    (upper : state.val < 25216) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 25152, by omega⟩
  have state_eq :
      (⟨25152 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0393 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0394 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨25216 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨25216 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0394
    (state : Fin 48684)
    (lower : 25216 ≤ state.val)
    (upper : state.val < 25280) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 25216, by omega⟩
  have state_eq :
      (⟨25216 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0394 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0395 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨25280 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨25280 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0395
    (state : Fin 48684)
    (lower : 25280 ≤ state.val)
    (upper : state.val < 25344) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 25280, by omega⟩
  have state_eq :
      (⟨25280 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0395 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0396 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨25344 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨25344 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0396
    (state : Fin 48684)
    (lower : 25344 ≤ state.val)
    (upper : state.val < 25408) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 25344, by omega⟩
  have state_eq :
      (⟨25344 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0396 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0397 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨25408 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨25408 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0397
    (state : Fin 48684)
    (lower : 25408 ≤ state.val)
    (upper : state.val < 25472) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 25408, by omega⟩
  have state_eq :
      (⟨25408 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0397 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0398 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨25472 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨25472 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0398
    (state : Fin 48684)
    (lower : 25472 ≤ state.val)
    (upper : state.val < 25536) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 25472, by omega⟩
  have state_eq :
      (⟨25472 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0398 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0399 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨25536 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨25536 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0399
    (state : Fin 48684)
    (lower : 25536 ≤ state.val)
    (upper : state.val < 25600) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 25536, by omega⟩
  have state_eq :
      (⟨25536 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0399 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0400 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨25600 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨25600 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0400
    (state : Fin 48684)
    (lower : 25600 ≤ state.val)
    (upper : state.val < 25664) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 25600, by omega⟩
  have state_eq :
      (⟨25600 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0400 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0401 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨25664 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨25664 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0401
    (state : Fin 48684)
    (lower : 25664 ≤ state.val)
    (upper : state.val < 25728) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 25664, by omega⟩
  have state_eq :
      (⟨25664 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0401 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0402 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨25728 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨25728 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0402
    (state : Fin 48684)
    (lower : 25728 ≤ state.val)
    (upper : state.val < 25792) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 25728, by omega⟩
  have state_eq :
      (⟨25728 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0402 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0403 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨25792 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨25792 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0403
    (state : Fin 48684)
    (lower : 25792 ≤ state.val)
    (upper : state.val < 25856) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 25792, by omega⟩
  have state_eq :
      (⟨25792 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0403 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0404 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨25856 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨25856 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0404
    (state : Fin 48684)
    (lower : 25856 ≤ state.val)
    (upper : state.val < 25920) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 25856, by omega⟩
  have state_eq :
      (⟨25856 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0404 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0405 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨25920 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨25920 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0405
    (state : Fin 48684)
    (lower : 25920 ≤ state.val)
    (upper : state.val < 25984) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 25920, by omega⟩
  have state_eq :
      (⟨25920 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0405 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0406 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨25984 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨25984 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0406
    (state : Fin 48684)
    (lower : 25984 ≤ state.val)
    (upper : state.val < 26048) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 25984, by omega⟩
  have state_eq :
      (⟨25984 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0406 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0407 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨26048 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨26048 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0407
    (state : Fin 48684)
    (lower : 26048 ≤ state.val)
    (upper : state.val < 26112) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 26048, by omega⟩
  have state_eq :
      (⟨26048 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0407 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0408 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨26112 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨26112 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0408
    (state : Fin 48684)
    (lower : 26112 ≤ state.val)
    (upper : state.val < 26176) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 26112, by omega⟩
  have state_eq :
      (⟨26112 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0408 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0409 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨26176 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨26176 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0409
    (state : Fin 48684)
    (lower : 26176 ≤ state.val)
    (upper : state.val < 26240) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 26176, by omega⟩
  have state_eq :
      (⟨26176 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0409 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0410 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨26240 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨26240 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0410
    (state : Fin 48684)
    (lower : 26240 ≤ state.val)
    (upper : state.val < 26304) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 26240, by omega⟩
  have state_eq :
      (⟨26240 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0410 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0411 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨26304 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨26304 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0411
    (state : Fin 48684)
    (lower : 26304 ≤ state.val)
    (upper : state.val < 26368) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 26304, by omega⟩
  have state_eq :
      (⟨26304 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0411 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0412 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨26368 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨26368 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0412
    (state : Fin 48684)
    (lower : 26368 ≤ state.val)
    (upper : state.val < 26432) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 26368, by omega⟩
  have state_eq :
      (⟨26368 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0412 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0413 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨26432 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨26432 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0413
    (state : Fin 48684)
    (lower : 26432 ≤ state.val)
    (upper : state.val < 26496) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 26432, by omega⟩
  have state_eq :
      (⟨26432 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0413 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0414 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨26496 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨26496 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0414
    (state : Fin 48684)
    (lower : 26496 ≤ state.val)
    (upper : state.val < 26560) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 26496, by omega⟩
  have state_eq :
      (⟨26496 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0414 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0415 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨26560 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨26560 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0415
    (state : Fin 48684)
    (lower : 26560 ≤ state.val)
    (upper : state.val < 26624) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 26560, by omega⟩
  have state_eq :
      (⟨26560 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0415 offset

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards
