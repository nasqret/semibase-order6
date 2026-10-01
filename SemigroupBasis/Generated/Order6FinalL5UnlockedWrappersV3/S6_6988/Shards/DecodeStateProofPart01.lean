import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6988.Shards.DecodeState
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6988.Shards.StateVector
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6988.Shards

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0032 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨2048 + candidate.val, by omega⟩ : Fin 4374)) =
        (⟨2048 + candidate.val, by omega⟩ : Fin 4374) := by
  decide

theorem decodeState_stateVectorProof0032
    (state : Fin 4374)
    (lower : 2048 ≤ state.val)
    (upper : state.val < 2112) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 2048, by omega⟩
  have state_eq :
      (⟨2048 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0032 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0033 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨2112 + candidate.val, by omega⟩ : Fin 4374)) =
        (⟨2112 + candidate.val, by omega⟩ : Fin 4374) := by
  decide

theorem decodeState_stateVectorProof0033
    (state : Fin 4374)
    (lower : 2112 ≤ state.val)
    (upper : state.val < 2176) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 2112, by omega⟩
  have state_eq :
      (⟨2112 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0033 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0034 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨2176 + candidate.val, by omega⟩ : Fin 4374)) =
        (⟨2176 + candidate.val, by omega⟩ : Fin 4374) := by
  decide

theorem decodeState_stateVectorProof0034
    (state : Fin 4374)
    (lower : 2176 ≤ state.val)
    (upper : state.val < 2240) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 2176, by omega⟩
  have state_eq :
      (⟨2176 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0034 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0035 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨2240 + candidate.val, by omega⟩ : Fin 4374)) =
        (⟨2240 + candidate.val, by omega⟩ : Fin 4374) := by
  decide

theorem decodeState_stateVectorProof0035
    (state : Fin 4374)
    (lower : 2240 ≤ state.val)
    (upper : state.val < 2304) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 2240, by omega⟩
  have state_eq :
      (⟨2240 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0035 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0036 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨2304 + candidate.val, by omega⟩ : Fin 4374)) =
        (⟨2304 + candidate.val, by omega⟩ : Fin 4374) := by
  decide

theorem decodeState_stateVectorProof0036
    (state : Fin 4374)
    (lower : 2304 ≤ state.val)
    (upper : state.val < 2368) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 2304, by omega⟩
  have state_eq :
      (⟨2304 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0036 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0037 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨2368 + candidate.val, by omega⟩ : Fin 4374)) =
        (⟨2368 + candidate.val, by omega⟩ : Fin 4374) := by
  decide

theorem decodeState_stateVectorProof0037
    (state : Fin 4374)
    (lower : 2368 ≤ state.val)
    (upper : state.val < 2432) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 2368, by omega⟩
  have state_eq :
      (⟨2368 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0037 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0038 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨2432 + candidate.val, by omega⟩ : Fin 4374)) =
        (⟨2432 + candidate.val, by omega⟩ : Fin 4374) := by
  decide

theorem decodeState_stateVectorProof0038
    (state : Fin 4374)
    (lower : 2432 ≤ state.val)
    (upper : state.val < 2496) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 2432, by omega⟩
  have state_eq :
      (⟨2432 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0038 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0039 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨2496 + candidate.val, by omega⟩ : Fin 4374)) =
        (⟨2496 + candidate.val, by omega⟩ : Fin 4374) := by
  decide

theorem decodeState_stateVectorProof0039
    (state : Fin 4374)
    (lower : 2496 ≤ state.val)
    (upper : state.val < 2560) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 2496, by omega⟩
  have state_eq :
      (⟨2496 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0039 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0040 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨2560 + candidate.val, by omega⟩ : Fin 4374)) =
        (⟨2560 + candidate.val, by omega⟩ : Fin 4374) := by
  decide

theorem decodeState_stateVectorProof0040
    (state : Fin 4374)
    (lower : 2560 ≤ state.val)
    (upper : state.val < 2624) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 2560, by omega⟩
  have state_eq :
      (⟨2560 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0040 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0041 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨2624 + candidate.val, by omega⟩ : Fin 4374)) =
        (⟨2624 + candidate.val, by omega⟩ : Fin 4374) := by
  decide

theorem decodeState_stateVectorProof0041
    (state : Fin 4374)
    (lower : 2624 ≤ state.val)
    (upper : state.val < 2688) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 2624, by omega⟩
  have state_eq :
      (⟨2624 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0041 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0042 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨2688 + candidate.val, by omega⟩ : Fin 4374)) =
        (⟨2688 + candidate.val, by omega⟩ : Fin 4374) := by
  decide

theorem decodeState_stateVectorProof0042
    (state : Fin 4374)
    (lower : 2688 ≤ state.val)
    (upper : state.val < 2752) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 2688, by omega⟩
  have state_eq :
      (⟨2688 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0042 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0043 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨2752 + candidate.val, by omega⟩ : Fin 4374)) =
        (⟨2752 + candidate.val, by omega⟩ : Fin 4374) := by
  decide

theorem decodeState_stateVectorProof0043
    (state : Fin 4374)
    (lower : 2752 ≤ state.val)
    (upper : state.val < 2816) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 2752, by omega⟩
  have state_eq :
      (⟨2752 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0043 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0044 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨2816 + candidate.val, by omega⟩ : Fin 4374)) =
        (⟨2816 + candidate.val, by omega⟩ : Fin 4374) := by
  decide

theorem decodeState_stateVectorProof0044
    (state : Fin 4374)
    (lower : 2816 ≤ state.val)
    (upper : state.val < 2880) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 2816, by omega⟩
  have state_eq :
      (⟨2816 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0044 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0045 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨2880 + candidate.val, by omega⟩ : Fin 4374)) =
        (⟨2880 + candidate.val, by omega⟩ : Fin 4374) := by
  decide

theorem decodeState_stateVectorProof0045
    (state : Fin 4374)
    (lower : 2880 ≤ state.val)
    (upper : state.val < 2944) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 2880, by omega⟩
  have state_eq :
      (⟨2880 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0045 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0046 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨2944 + candidate.val, by omega⟩ : Fin 4374)) =
        (⟨2944 + candidate.val, by omega⟩ : Fin 4374) := by
  decide

theorem decodeState_stateVectorProof0046
    (state : Fin 4374)
    (lower : 2944 ≤ state.val)
    (upper : state.val < 3008) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 2944, by omega⟩
  have state_eq :
      (⟨2944 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0046 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0047 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨3008 + candidate.val, by omega⟩ : Fin 4374)) =
        (⟨3008 + candidate.val, by omega⟩ : Fin 4374) := by
  decide

theorem decodeState_stateVectorProof0047
    (state : Fin 4374)
    (lower : 3008 ≤ state.val)
    (upper : state.val < 3072) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 3008, by omega⟩
  have state_eq :
      (⟨3008 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0047 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0048 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨3072 + candidate.val, by omega⟩ : Fin 4374)) =
        (⟨3072 + candidate.val, by omega⟩ : Fin 4374) := by
  decide

theorem decodeState_stateVectorProof0048
    (state : Fin 4374)
    (lower : 3072 ≤ state.val)
    (upper : state.val < 3136) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 3072, by omega⟩
  have state_eq :
      (⟨3072 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0048 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0049 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨3136 + candidate.val, by omega⟩ : Fin 4374)) =
        (⟨3136 + candidate.val, by omega⟩ : Fin 4374) := by
  decide

theorem decodeState_stateVectorProof0049
    (state : Fin 4374)
    (lower : 3136 ≤ state.val)
    (upper : state.val < 3200) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 3136, by omega⟩
  have state_eq :
      (⟨3136 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0049 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0050 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨3200 + candidate.val, by omega⟩ : Fin 4374)) =
        (⟨3200 + candidate.val, by omega⟩ : Fin 4374) := by
  decide

theorem decodeState_stateVectorProof0050
    (state : Fin 4374)
    (lower : 3200 ≤ state.val)
    (upper : state.val < 3264) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 3200, by omega⟩
  have state_eq :
      (⟨3200 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0050 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0051 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨3264 + candidate.val, by omega⟩ : Fin 4374)) =
        (⟨3264 + candidate.val, by omega⟩ : Fin 4374) := by
  decide

theorem decodeState_stateVectorProof0051
    (state : Fin 4374)
    (lower : 3264 ≤ state.val)
    (upper : state.val < 3328) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 3264, by omega⟩
  have state_eq :
      (⟨3264 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0051 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0052 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨3328 + candidate.val, by omega⟩ : Fin 4374)) =
        (⟨3328 + candidate.val, by omega⟩ : Fin 4374) := by
  decide

theorem decodeState_stateVectorProof0052
    (state : Fin 4374)
    (lower : 3328 ≤ state.val)
    (upper : state.val < 3392) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 3328, by omega⟩
  have state_eq :
      (⟨3328 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0052 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0053 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨3392 + candidate.val, by omega⟩ : Fin 4374)) =
        (⟨3392 + candidate.val, by omega⟩ : Fin 4374) := by
  decide

theorem decodeState_stateVectorProof0053
    (state : Fin 4374)
    (lower : 3392 ≤ state.val)
    (upper : state.val < 3456) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 3392, by omega⟩
  have state_eq :
      (⟨3392 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0053 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0054 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨3456 + candidate.val, by omega⟩ : Fin 4374)) =
        (⟨3456 + candidate.val, by omega⟩ : Fin 4374) := by
  decide

theorem decodeState_stateVectorProof0054
    (state : Fin 4374)
    (lower : 3456 ≤ state.val)
    (upper : state.val < 3520) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 3456, by omega⟩
  have state_eq :
      (⟨3456 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0054 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0055 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨3520 + candidate.val, by omega⟩ : Fin 4374)) =
        (⟨3520 + candidate.val, by omega⟩ : Fin 4374) := by
  decide

theorem decodeState_stateVectorProof0055
    (state : Fin 4374)
    (lower : 3520 ≤ state.val)
    (upper : state.val < 3584) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 3520, by omega⟩
  have state_eq :
      (⟨3520 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0055 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0056 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨3584 + candidate.val, by omega⟩ : Fin 4374)) =
        (⟨3584 + candidate.val, by omega⟩ : Fin 4374) := by
  decide

theorem decodeState_stateVectorProof0056
    (state : Fin 4374)
    (lower : 3584 ≤ state.val)
    (upper : state.val < 3648) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 3584, by omega⟩
  have state_eq :
      (⟨3584 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0056 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0057 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨3648 + candidate.val, by omega⟩ : Fin 4374)) =
        (⟨3648 + candidate.val, by omega⟩ : Fin 4374) := by
  decide

theorem decodeState_stateVectorProof0057
    (state : Fin 4374)
    (lower : 3648 ≤ state.val)
    (upper : state.val < 3712) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 3648, by omega⟩
  have state_eq :
      (⟨3648 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0057 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0058 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨3712 + candidate.val, by omega⟩ : Fin 4374)) =
        (⟨3712 + candidate.val, by omega⟩ : Fin 4374) := by
  decide

theorem decodeState_stateVectorProof0058
    (state : Fin 4374)
    (lower : 3712 ≤ state.val)
    (upper : state.val < 3776) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 3712, by omega⟩
  have state_eq :
      (⟨3712 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0058 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0059 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨3776 + candidate.val, by omega⟩ : Fin 4374)) =
        (⟨3776 + candidate.val, by omega⟩ : Fin 4374) := by
  decide

theorem decodeState_stateVectorProof0059
    (state : Fin 4374)
    (lower : 3776 ≤ state.val)
    (upper : state.val < 3840) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 3776, by omega⟩
  have state_eq :
      (⟨3776 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0059 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0060 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨3840 + candidate.val, by omega⟩ : Fin 4374)) =
        (⟨3840 + candidate.val, by omega⟩ : Fin 4374) := by
  decide

theorem decodeState_stateVectorProof0060
    (state : Fin 4374)
    (lower : 3840 ≤ state.val)
    (upper : state.val < 3904) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 3840, by omega⟩
  have state_eq :
      (⟨3840 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0060 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0061 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨3904 + candidate.val, by omega⟩ : Fin 4374)) =
        (⟨3904 + candidate.val, by omega⟩ : Fin 4374) := by
  decide

theorem decodeState_stateVectorProof0061
    (state : Fin 4374)
    (lower : 3904 ≤ state.val)
    (upper : state.val < 3968) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 3904, by omega⟩
  have state_eq :
      (⟨3904 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0061 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0062 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨3968 + candidate.val, by omega⟩ : Fin 4374)) =
        (⟨3968 + candidate.val, by omega⟩ : Fin 4374) := by
  decide

theorem decodeState_stateVectorProof0062
    (state : Fin 4374)
    (lower : 3968 ≤ state.val)
    (upper : state.val < 4032) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 3968, by omega⟩
  have state_eq :
      (⟨3968 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0062 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0063 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨4032 + candidate.val, by omega⟩ : Fin 4374)) =
        (⟨4032 + candidate.val, by omega⟩ : Fin 4374) := by
  decide

theorem decodeState_stateVectorProof0063
    (state : Fin 4374)
    (lower : 4032 ≤ state.val)
    (upper : state.val < 4096) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 4032, by omega⟩
  have state_eq :
      (⟨4032 + offset.val, by omega⟩ : Fin 4374) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0063 offset

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6988.Shards
