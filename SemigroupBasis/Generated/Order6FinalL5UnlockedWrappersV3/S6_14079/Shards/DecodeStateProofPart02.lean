import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.Shards.DecodeState
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.Shards.StateVector
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.Shards

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0064 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨4096 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨4096 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0064
    (state : Fin 11742)
    (lower : 4096 ≤ state.val)
    (upper : state.val < 4160) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 4096, by omega⟩
  have state_eq :
      (⟨4096 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0064 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0065 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨4160 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨4160 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0065
    (state : Fin 11742)
    (lower : 4160 ≤ state.val)
    (upper : state.val < 4224) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 4160, by omega⟩
  have state_eq :
      (⟨4160 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0065 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0066 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨4224 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨4224 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0066
    (state : Fin 11742)
    (lower : 4224 ≤ state.val)
    (upper : state.val < 4288) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 4224, by omega⟩
  have state_eq :
      (⟨4224 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0066 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0067 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨4288 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨4288 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0067
    (state : Fin 11742)
    (lower : 4288 ≤ state.val)
    (upper : state.val < 4352) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 4288, by omega⟩
  have state_eq :
      (⟨4288 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0067 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0068 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨4352 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨4352 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0068
    (state : Fin 11742)
    (lower : 4352 ≤ state.val)
    (upper : state.val < 4416) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 4352, by omega⟩
  have state_eq :
      (⟨4352 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0068 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0069 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨4416 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨4416 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0069
    (state : Fin 11742)
    (lower : 4416 ≤ state.val)
    (upper : state.val < 4480) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 4416, by omega⟩
  have state_eq :
      (⟨4416 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0069 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0070 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨4480 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨4480 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0070
    (state : Fin 11742)
    (lower : 4480 ≤ state.val)
    (upper : state.val < 4544) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 4480, by omega⟩
  have state_eq :
      (⟨4480 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0070 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0071 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨4544 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨4544 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0071
    (state : Fin 11742)
    (lower : 4544 ≤ state.val)
    (upper : state.val < 4608) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 4544, by omega⟩
  have state_eq :
      (⟨4544 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0071 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0072 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨4608 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨4608 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0072
    (state : Fin 11742)
    (lower : 4608 ≤ state.val)
    (upper : state.val < 4672) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 4608, by omega⟩
  have state_eq :
      (⟨4608 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0072 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0073 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨4672 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨4672 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0073
    (state : Fin 11742)
    (lower : 4672 ≤ state.val)
    (upper : state.val < 4736) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 4672, by omega⟩
  have state_eq :
      (⟨4672 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0073 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0074 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨4736 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨4736 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0074
    (state : Fin 11742)
    (lower : 4736 ≤ state.val)
    (upper : state.val < 4800) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 4736, by omega⟩
  have state_eq :
      (⟨4736 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0074 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0075 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨4800 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨4800 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0075
    (state : Fin 11742)
    (lower : 4800 ≤ state.val)
    (upper : state.val < 4864) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 4800, by omega⟩
  have state_eq :
      (⟨4800 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0075 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0076 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨4864 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨4864 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0076
    (state : Fin 11742)
    (lower : 4864 ≤ state.val)
    (upper : state.val < 4928) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 4864, by omega⟩
  have state_eq :
      (⟨4864 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0076 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0077 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨4928 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨4928 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0077
    (state : Fin 11742)
    (lower : 4928 ≤ state.val)
    (upper : state.val < 4992) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 4928, by omega⟩
  have state_eq :
      (⟨4928 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0077 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0078 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨4992 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨4992 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0078
    (state : Fin 11742)
    (lower : 4992 ≤ state.val)
    (upper : state.val < 5056) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 4992, by omega⟩
  have state_eq :
      (⟨4992 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0078 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0079 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨5056 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨5056 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0079
    (state : Fin 11742)
    (lower : 5056 ≤ state.val)
    (upper : state.val < 5120) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 5056, by omega⟩
  have state_eq :
      (⟨5056 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0079 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0080 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨5120 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨5120 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0080
    (state : Fin 11742)
    (lower : 5120 ≤ state.val)
    (upper : state.val < 5184) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 5120, by omega⟩
  have state_eq :
      (⟨5120 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0080 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0081 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨5184 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨5184 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0081
    (state : Fin 11742)
    (lower : 5184 ≤ state.val)
    (upper : state.val < 5248) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 5184, by omega⟩
  have state_eq :
      (⟨5184 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0081 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0082 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨5248 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨5248 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0082
    (state : Fin 11742)
    (lower : 5248 ≤ state.val)
    (upper : state.val < 5312) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 5248, by omega⟩
  have state_eq :
      (⟨5248 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0082 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0083 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨5312 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨5312 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0083
    (state : Fin 11742)
    (lower : 5312 ≤ state.val)
    (upper : state.val < 5376) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 5312, by omega⟩
  have state_eq :
      (⟨5312 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0083 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0084 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨5376 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨5376 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0084
    (state : Fin 11742)
    (lower : 5376 ≤ state.val)
    (upper : state.val < 5440) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 5376, by omega⟩
  have state_eq :
      (⟨5376 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0084 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0085 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨5440 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨5440 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0085
    (state : Fin 11742)
    (lower : 5440 ≤ state.val)
    (upper : state.val < 5504) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 5440, by omega⟩
  have state_eq :
      (⟨5440 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0085 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0086 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨5504 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨5504 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0086
    (state : Fin 11742)
    (lower : 5504 ≤ state.val)
    (upper : state.val < 5568) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 5504, by omega⟩
  have state_eq :
      (⟨5504 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0086 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0087 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨5568 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨5568 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0087
    (state : Fin 11742)
    (lower : 5568 ≤ state.val)
    (upper : state.val < 5632) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 5568, by omega⟩
  have state_eq :
      (⟨5568 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0087 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0088 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨5632 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨5632 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0088
    (state : Fin 11742)
    (lower : 5632 ≤ state.val)
    (upper : state.val < 5696) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 5632, by omega⟩
  have state_eq :
      (⟨5632 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0088 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0089 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨5696 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨5696 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0089
    (state : Fin 11742)
    (lower : 5696 ≤ state.val)
    (upper : state.val < 5760) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 5696, by omega⟩
  have state_eq :
      (⟨5696 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0089 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0090 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨5760 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨5760 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0090
    (state : Fin 11742)
    (lower : 5760 ≤ state.val)
    (upper : state.val < 5824) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 5760, by omega⟩
  have state_eq :
      (⟨5760 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0090 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0091 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨5824 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨5824 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0091
    (state : Fin 11742)
    (lower : 5824 ≤ state.val)
    (upper : state.val < 5888) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 5824, by omega⟩
  have state_eq :
      (⟨5824 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0091 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0092 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨5888 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨5888 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0092
    (state : Fin 11742)
    (lower : 5888 ≤ state.val)
    (upper : state.val < 5952) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 5888, by omega⟩
  have state_eq :
      (⟨5888 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0092 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0093 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨5952 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨5952 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0093
    (state : Fin 11742)
    (lower : 5952 ≤ state.val)
    (upper : state.val < 6016) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 5952, by omega⟩
  have state_eq :
      (⟨5952 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0093 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0094 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨6016 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨6016 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0094
    (state : Fin 11742)
    (lower : 6016 ≤ state.val)
    (upper : state.val < 6080) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 6016, by omega⟩
  have state_eq :
      (⟨6016 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0094 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0095 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨6080 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨6080 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0095
    (state : Fin 11742)
    (lower : 6080 ≤ state.val)
    (upper : state.val < 6144) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 6080, by omega⟩
  have state_eq :
      (⟨6080 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0095 offset

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.Shards
