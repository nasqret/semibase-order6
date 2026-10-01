import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards.DecodeState
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards.StateVector
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0416 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨26624 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨26624 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0416
    (state : Fin 48684)
    (lower : 26624 ≤ state.val)
    (upper : state.val < 26688) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 26624, by omega⟩
  have state_eq :
      (⟨26624 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0416 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0417 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨26688 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨26688 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0417
    (state : Fin 48684)
    (lower : 26688 ≤ state.val)
    (upper : state.val < 26752) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 26688, by omega⟩
  have state_eq :
      (⟨26688 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0417 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0418 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨26752 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨26752 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0418
    (state : Fin 48684)
    (lower : 26752 ≤ state.val)
    (upper : state.val < 26816) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 26752, by omega⟩
  have state_eq :
      (⟨26752 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0418 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0419 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨26816 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨26816 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0419
    (state : Fin 48684)
    (lower : 26816 ≤ state.val)
    (upper : state.val < 26880) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 26816, by omega⟩
  have state_eq :
      (⟨26816 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0419 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0420 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨26880 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨26880 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0420
    (state : Fin 48684)
    (lower : 26880 ≤ state.val)
    (upper : state.val < 26944) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 26880, by omega⟩
  have state_eq :
      (⟨26880 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0420 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0421 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨26944 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨26944 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0421
    (state : Fin 48684)
    (lower : 26944 ≤ state.val)
    (upper : state.val < 27008) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 26944, by omega⟩
  have state_eq :
      (⟨26944 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0421 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0422 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨27008 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨27008 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0422
    (state : Fin 48684)
    (lower : 27008 ≤ state.val)
    (upper : state.val < 27072) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 27008, by omega⟩
  have state_eq :
      (⟨27008 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0422 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0423 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨27072 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨27072 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0423
    (state : Fin 48684)
    (lower : 27072 ≤ state.val)
    (upper : state.val < 27136) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 27072, by omega⟩
  have state_eq :
      (⟨27072 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0423 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0424 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨27136 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨27136 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0424
    (state : Fin 48684)
    (lower : 27136 ≤ state.val)
    (upper : state.val < 27200) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 27136, by omega⟩
  have state_eq :
      (⟨27136 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0424 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0425 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨27200 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨27200 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0425
    (state : Fin 48684)
    (lower : 27200 ≤ state.val)
    (upper : state.val < 27264) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 27200, by omega⟩
  have state_eq :
      (⟨27200 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0425 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0426 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨27264 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨27264 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0426
    (state : Fin 48684)
    (lower : 27264 ≤ state.val)
    (upper : state.val < 27328) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 27264, by omega⟩
  have state_eq :
      (⟨27264 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0426 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0427 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨27328 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨27328 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0427
    (state : Fin 48684)
    (lower : 27328 ≤ state.val)
    (upper : state.val < 27392) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 27328, by omega⟩
  have state_eq :
      (⟨27328 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0427 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0428 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨27392 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨27392 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0428
    (state : Fin 48684)
    (lower : 27392 ≤ state.val)
    (upper : state.val < 27456) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 27392, by omega⟩
  have state_eq :
      (⟨27392 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0428 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0429 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨27456 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨27456 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0429
    (state : Fin 48684)
    (lower : 27456 ≤ state.val)
    (upper : state.val < 27520) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 27456, by omega⟩
  have state_eq :
      (⟨27456 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0429 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0430 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨27520 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨27520 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0430
    (state : Fin 48684)
    (lower : 27520 ≤ state.val)
    (upper : state.val < 27584) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 27520, by omega⟩
  have state_eq :
      (⟨27520 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0430 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0431 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨27584 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨27584 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0431
    (state : Fin 48684)
    (lower : 27584 ≤ state.val)
    (upper : state.val < 27648) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 27584, by omega⟩
  have state_eq :
      (⟨27584 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0431 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0432 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨27648 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨27648 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0432
    (state : Fin 48684)
    (lower : 27648 ≤ state.val)
    (upper : state.val < 27712) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 27648, by omega⟩
  have state_eq :
      (⟨27648 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0432 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0433 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨27712 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨27712 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0433
    (state : Fin 48684)
    (lower : 27712 ≤ state.val)
    (upper : state.val < 27776) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 27712, by omega⟩
  have state_eq :
      (⟨27712 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0433 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0434 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨27776 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨27776 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0434
    (state : Fin 48684)
    (lower : 27776 ≤ state.val)
    (upper : state.val < 27840) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 27776, by omega⟩
  have state_eq :
      (⟨27776 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0434 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0435 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨27840 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨27840 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0435
    (state : Fin 48684)
    (lower : 27840 ≤ state.val)
    (upper : state.val < 27904) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 27840, by omega⟩
  have state_eq :
      (⟨27840 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0435 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0436 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨27904 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨27904 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0436
    (state : Fin 48684)
    (lower : 27904 ≤ state.val)
    (upper : state.val < 27968) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 27904, by omega⟩
  have state_eq :
      (⟨27904 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0436 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0437 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨27968 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨27968 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0437
    (state : Fin 48684)
    (lower : 27968 ≤ state.val)
    (upper : state.val < 28032) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 27968, by omega⟩
  have state_eq :
      (⟨27968 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0437 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0438 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨28032 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨28032 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0438
    (state : Fin 48684)
    (lower : 28032 ≤ state.val)
    (upper : state.val < 28096) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 28032, by omega⟩
  have state_eq :
      (⟨28032 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0438 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0439 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨28096 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨28096 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0439
    (state : Fin 48684)
    (lower : 28096 ≤ state.val)
    (upper : state.val < 28160) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 28096, by omega⟩
  have state_eq :
      (⟨28096 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0439 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0440 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨28160 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨28160 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0440
    (state : Fin 48684)
    (lower : 28160 ≤ state.val)
    (upper : state.val < 28224) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 28160, by omega⟩
  have state_eq :
      (⟨28160 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0440 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0441 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨28224 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨28224 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0441
    (state : Fin 48684)
    (lower : 28224 ≤ state.val)
    (upper : state.val < 28288) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 28224, by omega⟩
  have state_eq :
      (⟨28224 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0441 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0442 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨28288 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨28288 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0442
    (state : Fin 48684)
    (lower : 28288 ≤ state.val)
    (upper : state.val < 28352) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 28288, by omega⟩
  have state_eq :
      (⟨28288 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0442 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0443 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨28352 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨28352 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0443
    (state : Fin 48684)
    (lower : 28352 ≤ state.val)
    (upper : state.val < 28416) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 28352, by omega⟩
  have state_eq :
      (⟨28352 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0443 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0444 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨28416 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨28416 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0444
    (state : Fin 48684)
    (lower : 28416 ≤ state.val)
    (upper : state.val < 28480) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 28416, by omega⟩
  have state_eq :
      (⟨28416 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0444 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0445 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨28480 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨28480 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0445
    (state : Fin 48684)
    (lower : 28480 ≤ state.val)
    (upper : state.val < 28544) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 28480, by omega⟩
  have state_eq :
      (⟨28480 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0445 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0446 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨28544 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨28544 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0446
    (state : Fin 48684)
    (lower : 28544 ≤ state.val)
    (upper : state.val < 28608) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 28544, by omega⟩
  have state_eq :
      (⟨28544 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0446 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0447 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨28608 + candidate.val, by omega⟩ : Fin 48684)) =
        (⟨28608 + candidate.val, by omega⟩ : Fin 48684) := by
  decide

theorem decodeState_stateVectorProof0447
    (state : Fin 48684)
    (lower : 28608 ≤ state.val)
    (upper : state.val < 28672) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 28608, by omega⟩
  have state_eq :
      (⟨28608 + offset.val, by omega⟩ : Fin 48684) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0447 offset

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards
