import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.Shards.DecodeState
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.Shards.StateVector
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.Shards

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0096 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨6144 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨6144 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0096
    (state : Fin 11742)
    (lower : 6144 ≤ state.val)
    (upper : state.val < 6208) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 6144, by omega⟩
  have state_eq :
      (⟨6144 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0096 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0097 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨6208 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨6208 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0097
    (state : Fin 11742)
    (lower : 6208 ≤ state.val)
    (upper : state.val < 6272) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 6208, by omega⟩
  have state_eq :
      (⟨6208 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0097 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0098 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨6272 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨6272 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0098
    (state : Fin 11742)
    (lower : 6272 ≤ state.val)
    (upper : state.val < 6336) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 6272, by omega⟩
  have state_eq :
      (⟨6272 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0098 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0099 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨6336 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨6336 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0099
    (state : Fin 11742)
    (lower : 6336 ≤ state.val)
    (upper : state.val < 6400) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 6336, by omega⟩
  have state_eq :
      (⟨6336 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0099 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0100 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨6400 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨6400 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0100
    (state : Fin 11742)
    (lower : 6400 ≤ state.val)
    (upper : state.val < 6464) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 6400, by omega⟩
  have state_eq :
      (⟨6400 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0100 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0101 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨6464 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨6464 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0101
    (state : Fin 11742)
    (lower : 6464 ≤ state.val)
    (upper : state.val < 6528) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 6464, by omega⟩
  have state_eq :
      (⟨6464 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0101 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0102 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨6528 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨6528 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0102
    (state : Fin 11742)
    (lower : 6528 ≤ state.val)
    (upper : state.val < 6592) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 6528, by omega⟩
  have state_eq :
      (⟨6528 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0102 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0103 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨6592 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨6592 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0103
    (state : Fin 11742)
    (lower : 6592 ≤ state.val)
    (upper : state.val < 6656) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 6592, by omega⟩
  have state_eq :
      (⟨6592 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0103 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0104 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨6656 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨6656 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0104
    (state : Fin 11742)
    (lower : 6656 ≤ state.val)
    (upper : state.val < 6720) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 6656, by omega⟩
  have state_eq :
      (⟨6656 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0104 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0105 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨6720 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨6720 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0105
    (state : Fin 11742)
    (lower : 6720 ≤ state.val)
    (upper : state.val < 6784) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 6720, by omega⟩
  have state_eq :
      (⟨6720 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0105 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0106 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨6784 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨6784 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0106
    (state : Fin 11742)
    (lower : 6784 ≤ state.val)
    (upper : state.val < 6848) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 6784, by omega⟩
  have state_eq :
      (⟨6784 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0106 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0107 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨6848 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨6848 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0107
    (state : Fin 11742)
    (lower : 6848 ≤ state.val)
    (upper : state.val < 6912) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 6848, by omega⟩
  have state_eq :
      (⟨6848 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0107 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0108 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨6912 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨6912 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0108
    (state : Fin 11742)
    (lower : 6912 ≤ state.val)
    (upper : state.val < 6976) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 6912, by omega⟩
  have state_eq :
      (⟨6912 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0108 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0109 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨6976 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨6976 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0109
    (state : Fin 11742)
    (lower : 6976 ≤ state.val)
    (upper : state.val < 7040) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 6976, by omega⟩
  have state_eq :
      (⟨6976 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0109 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0110 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨7040 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨7040 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0110
    (state : Fin 11742)
    (lower : 7040 ≤ state.val)
    (upper : state.val < 7104) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 7040, by omega⟩
  have state_eq :
      (⟨7040 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0110 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0111 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨7104 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨7104 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0111
    (state : Fin 11742)
    (lower : 7104 ≤ state.val)
    (upper : state.val < 7168) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 7104, by omega⟩
  have state_eq :
      (⟨7104 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0111 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0112 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨7168 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨7168 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0112
    (state : Fin 11742)
    (lower : 7168 ≤ state.val)
    (upper : state.val < 7232) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 7168, by omega⟩
  have state_eq :
      (⟨7168 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0112 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0113 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨7232 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨7232 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0113
    (state : Fin 11742)
    (lower : 7232 ≤ state.val)
    (upper : state.val < 7296) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 7232, by omega⟩
  have state_eq :
      (⟨7232 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0113 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0114 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨7296 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨7296 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0114
    (state : Fin 11742)
    (lower : 7296 ≤ state.val)
    (upper : state.val < 7360) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 7296, by omega⟩
  have state_eq :
      (⟨7296 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0114 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0115 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨7360 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨7360 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0115
    (state : Fin 11742)
    (lower : 7360 ≤ state.val)
    (upper : state.val < 7424) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 7360, by omega⟩
  have state_eq :
      (⟨7360 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0115 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0116 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨7424 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨7424 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0116
    (state : Fin 11742)
    (lower : 7424 ≤ state.val)
    (upper : state.val < 7488) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 7424, by omega⟩
  have state_eq :
      (⟨7424 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0116 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0117 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨7488 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨7488 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0117
    (state : Fin 11742)
    (lower : 7488 ≤ state.val)
    (upper : state.val < 7552) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 7488, by omega⟩
  have state_eq :
      (⟨7488 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0117 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0118 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨7552 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨7552 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0118
    (state : Fin 11742)
    (lower : 7552 ≤ state.val)
    (upper : state.val < 7616) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 7552, by omega⟩
  have state_eq :
      (⟨7552 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0118 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0119 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨7616 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨7616 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0119
    (state : Fin 11742)
    (lower : 7616 ≤ state.val)
    (upper : state.val < 7680) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 7616, by omega⟩
  have state_eq :
      (⟨7616 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0119 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0120 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨7680 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨7680 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0120
    (state : Fin 11742)
    (lower : 7680 ≤ state.val)
    (upper : state.val < 7744) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 7680, by omega⟩
  have state_eq :
      (⟨7680 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0120 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0121 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨7744 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨7744 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0121
    (state : Fin 11742)
    (lower : 7744 ≤ state.val)
    (upper : state.val < 7808) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 7744, by omega⟩
  have state_eq :
      (⟨7744 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0121 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0122 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨7808 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨7808 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0122
    (state : Fin 11742)
    (lower : 7808 ≤ state.val)
    (upper : state.val < 7872) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 7808, by omega⟩
  have state_eq :
      (⟨7808 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0122 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0123 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨7872 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨7872 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0123
    (state : Fin 11742)
    (lower : 7872 ≤ state.val)
    (upper : state.val < 7936) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 7872, by omega⟩
  have state_eq :
      (⟨7872 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0123 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0124 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨7936 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨7936 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0124
    (state : Fin 11742)
    (lower : 7936 ≤ state.val)
    (upper : state.val < 8000) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 7936, by omega⟩
  have state_eq :
      (⟨7936 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0124 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0125 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨8000 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨8000 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0125
    (state : Fin 11742)
    (lower : 8000 ≤ state.val)
    (upper : state.val < 8064) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 8000, by omega⟩
  have state_eq :
      (⟨8000 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0125 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0126 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨8064 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨8064 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0126
    (state : Fin 11742)
    (lower : 8064 ≤ state.val)
    (upper : state.val < 8128) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 8064, by omega⟩
  have state_eq :
      (⟨8064 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0126 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0127 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨8128 + candidate.val, by omega⟩ : Fin 11742)) =
        (⟨8128 + candidate.val, by omega⟩ : Fin 11742) := by
  decide

theorem decodeState_stateVectorProof0127
    (state : Fin 11742)
    (lower : 8128 ≤ state.val)
    (upper : state.val < 8192) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 8128, by omega⟩
  have state_eq :
      (⟨8128 + offset.val, by omega⟩ : Fin 11742) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0127 offset

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.Shards
