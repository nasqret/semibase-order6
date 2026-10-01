import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards.DecodeState
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards.StateVector
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0352 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨22528 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨22528 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0352
    (state : Fin 48684)
    (lower : 22528 ≤ state.val)
    (upper : state.val < 22592) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 22528, by omega⟩
  have state_eq :
      (⟨22528 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0352 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0353 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨22592 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨22592 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0353
    (state : Fin 48684)
    (lower : 22592 ≤ state.val)
    (upper : state.val < 22656) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 22592, by omega⟩
  have state_eq :
      (⟨22592 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0353 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0354 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨22656 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨22656 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0354
    (state : Fin 48684)
    (lower : 22656 ≤ state.val)
    (upper : state.val < 22720) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 22656, by omega⟩
  have state_eq :
      (⟨22656 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0354 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0355 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨22720 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨22720 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0355
    (state : Fin 48684)
    (lower : 22720 ≤ state.val)
    (upper : state.val < 22784) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 22720, by omega⟩
  have state_eq :
      (⟨22720 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0355 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0356 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨22784 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨22784 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0356
    (state : Fin 48684)
    (lower : 22784 ≤ state.val)
    (upper : state.val < 22848) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 22784, by omega⟩
  have state_eq :
      (⟨22784 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0356 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0357 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨22848 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨22848 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0357
    (state : Fin 48684)
    (lower : 22848 ≤ state.val)
    (upper : state.val < 22912) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 22848, by omega⟩
  have state_eq :
      (⟨22848 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0357 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0358 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨22912 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨22912 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0358
    (state : Fin 48684)
    (lower : 22912 ≤ state.val)
    (upper : state.val < 22976) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 22912, by omega⟩
  have state_eq :
      (⟨22912 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0358 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0359 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨22976 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨22976 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0359
    (state : Fin 48684)
    (lower : 22976 ≤ state.val)
    (upper : state.val < 23040) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 22976, by omega⟩
  have state_eq :
      (⟨22976 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0359 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0360 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨23040 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨23040 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0360
    (state : Fin 48684)
    (lower : 23040 ≤ state.val)
    (upper : state.val < 23104) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 23040, by omega⟩
  have state_eq :
      (⟨23040 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0360 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0361 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨23104 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨23104 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0361
    (state : Fin 48684)
    (lower : 23104 ≤ state.val)
    (upper : state.val < 23168) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 23104, by omega⟩
  have state_eq :
      (⟨23104 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0361 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0362 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨23168 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨23168 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0362
    (state : Fin 48684)
    (lower : 23168 ≤ state.val)
    (upper : state.val < 23232) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 23168, by omega⟩
  have state_eq :
      (⟨23168 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0362 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0363 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨23232 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨23232 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0363
    (state : Fin 48684)
    (lower : 23232 ≤ state.val)
    (upper : state.val < 23296) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 23232, by omega⟩
  have state_eq :
      (⟨23232 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0363 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0364 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨23296 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨23296 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0364
    (state : Fin 48684)
    (lower : 23296 ≤ state.val)
    (upper : state.val < 23360) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 23296, by omega⟩
  have state_eq :
      (⟨23296 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0364 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0365 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨23360 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨23360 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0365
    (state : Fin 48684)
    (lower : 23360 ≤ state.val)
    (upper : state.val < 23424) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 23360, by omega⟩
  have state_eq :
      (⟨23360 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0365 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0366 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨23424 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨23424 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0366
    (state : Fin 48684)
    (lower : 23424 ≤ state.val)
    (upper : state.val < 23488) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 23424, by omega⟩
  have state_eq :
      (⟨23424 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0366 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0367 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨23488 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨23488 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0367
    (state : Fin 48684)
    (lower : 23488 ≤ state.val)
    (upper : state.val < 23552) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 23488, by omega⟩
  have state_eq :
      (⟨23488 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0367 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0368 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨23552 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨23552 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0368
    (state : Fin 48684)
    (lower : 23552 ≤ state.val)
    (upper : state.val < 23616) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 23552, by omega⟩
  have state_eq :
      (⟨23552 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0368 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0369 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨23616 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨23616 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0369
    (state : Fin 48684)
    (lower : 23616 ≤ state.val)
    (upper : state.val < 23680) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 23616, by omega⟩
  have state_eq :
      (⟨23616 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0369 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0370 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨23680 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨23680 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0370
    (state : Fin 48684)
    (lower : 23680 ≤ state.val)
    (upper : state.val < 23744) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 23680, by omega⟩
  have state_eq :
      (⟨23680 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0370 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0371 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨23744 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨23744 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0371
    (state : Fin 48684)
    (lower : 23744 ≤ state.val)
    (upper : state.val < 23808) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 23744, by omega⟩
  have state_eq :
      (⟨23744 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0371 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0372 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨23808 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨23808 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0372
    (state : Fin 48684)
    (lower : 23808 ≤ state.val)
    (upper : state.val < 23872) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 23808, by omega⟩
  have state_eq :
      (⟨23808 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0372 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0373 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨23872 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨23872 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0373
    (state : Fin 48684)
    (lower : 23872 ≤ state.val)
    (upper : state.val < 23936) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 23872, by omega⟩
  have state_eq :
      (⟨23872 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0373 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0374 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨23936 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨23936 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0374
    (state : Fin 48684)
    (lower : 23936 ≤ state.val)
    (upper : state.val < 24000) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 23936, by omega⟩
  have state_eq :
      (⟨23936 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0374 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0375 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨24000 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨24000 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0375
    (state : Fin 48684)
    (lower : 24000 ≤ state.val)
    (upper : state.val < 24064) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 24000, by omega⟩
  have state_eq :
      (⟨24000 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0375 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0376 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨24064 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨24064 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0376
    (state : Fin 48684)
    (lower : 24064 ≤ state.val)
    (upper : state.val < 24128) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 24064, by omega⟩
  have state_eq :
      (⟨24064 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0376 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0377 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨24128 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨24128 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0377
    (state : Fin 48684)
    (lower : 24128 ≤ state.val)
    (upper : state.val < 24192) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 24128, by omega⟩
  have state_eq :
      (⟨24128 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0377 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0378 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨24192 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨24192 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0378
    (state : Fin 48684)
    (lower : 24192 ≤ state.val)
    (upper : state.val < 24256) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 24192, by omega⟩
  have state_eq :
      (⟨24192 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0378 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0379 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨24256 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨24256 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0379
    (state : Fin 48684)
    (lower : 24256 ≤ state.val)
    (upper : state.val < 24320) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 24256, by omega⟩
  have state_eq :
      (⟨24256 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0379 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0380 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨24320 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨24320 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0380
    (state : Fin 48684)
    (lower : 24320 ≤ state.val)
    (upper : state.val < 24384) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 24320, by omega⟩
  have state_eq :
      (⟨24320 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0380 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0381 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨24384 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨24384 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0381
    (state : Fin 48684)
    (lower : 24384 ≤ state.val)
    (upper : state.val < 24448) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 24384, by omega⟩
  have state_eq :
      (⟨24384 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0381 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0382 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨24448 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨24448 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0382
    (state : Fin 48684)
    (lower : 24448 ≤ state.val)
    (upper : state.val < 24512) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 24448, by omega⟩
  have state_eq :
      (⟨24448 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0382 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0383 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨24512 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨24512 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0383
    (state : Fin 48684)
    (lower : 24512 ≤ state.val)
    (upper : state.val < 24576) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 24512, by omega⟩
  have state_eq :
      (⟨24512 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0383 offset

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards
