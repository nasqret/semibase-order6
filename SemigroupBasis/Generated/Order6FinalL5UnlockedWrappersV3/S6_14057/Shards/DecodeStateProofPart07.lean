import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.Shards.DecodeState
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.Shards.StateVector
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.Shards

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0224 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨14336 + candidate.val, by omega⟩ : Fin 17622)) =
        (⟨14336 + candidate.val, by omega⟩ : Fin 17622) := by
  decide

theorem decodeState_stateVectorProof0224
    (state : Fin 17622)
    (lower : 14336 ≤ state.val)
    (upper : state.val < 14400) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 14336, by omega⟩
  have state_eq :
      (⟨14336 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0224 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0225 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨14400 + candidate.val, by omega⟩ : Fin 17622)) =
        (⟨14400 + candidate.val, by omega⟩ : Fin 17622) := by
  decide

theorem decodeState_stateVectorProof0225
    (state : Fin 17622)
    (lower : 14400 ≤ state.val)
    (upper : state.val < 14464) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 14400, by omega⟩
  have state_eq :
      (⟨14400 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0225 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0226 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨14464 + candidate.val, by omega⟩ : Fin 17622)) =
        (⟨14464 + candidate.val, by omega⟩ : Fin 17622) := by
  decide

theorem decodeState_stateVectorProof0226
    (state : Fin 17622)
    (lower : 14464 ≤ state.val)
    (upper : state.val < 14528) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 14464, by omega⟩
  have state_eq :
      (⟨14464 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0226 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0227 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨14528 + candidate.val, by omega⟩ : Fin 17622)) =
        (⟨14528 + candidate.val, by omega⟩ : Fin 17622) := by
  decide

theorem decodeState_stateVectorProof0227
    (state : Fin 17622)
    (lower : 14528 ≤ state.val)
    (upper : state.val < 14592) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 14528, by omega⟩
  have state_eq :
      (⟨14528 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0227 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0228 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨14592 + candidate.val, by omega⟩ : Fin 17622)) =
        (⟨14592 + candidate.val, by omega⟩ : Fin 17622) := by
  decide

theorem decodeState_stateVectorProof0228
    (state : Fin 17622)
    (lower : 14592 ≤ state.val)
    (upper : state.val < 14656) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 14592, by omega⟩
  have state_eq :
      (⟨14592 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0228 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0229 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨14656 + candidate.val, by omega⟩ : Fin 17622)) =
        (⟨14656 + candidate.val, by omega⟩ : Fin 17622) := by
  decide

theorem decodeState_stateVectorProof0229
    (state : Fin 17622)
    (lower : 14656 ≤ state.val)
    (upper : state.val < 14720) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 14656, by omega⟩
  have state_eq :
      (⟨14656 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0229 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0230 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨14720 + candidate.val, by omega⟩ : Fin 17622)) =
        (⟨14720 + candidate.val, by omega⟩ : Fin 17622) := by
  decide

theorem decodeState_stateVectorProof0230
    (state : Fin 17622)
    (lower : 14720 ≤ state.val)
    (upper : state.val < 14784) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 14720, by omega⟩
  have state_eq :
      (⟨14720 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0230 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0231 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨14784 + candidate.val, by omega⟩ : Fin 17622)) =
        (⟨14784 + candidate.val, by omega⟩ : Fin 17622) := by
  decide

theorem decodeState_stateVectorProof0231
    (state : Fin 17622)
    (lower : 14784 ≤ state.val)
    (upper : state.val < 14848) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 14784, by omega⟩
  have state_eq :
      (⟨14784 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0231 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0232 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨14848 + candidate.val, by omega⟩ : Fin 17622)) =
        (⟨14848 + candidate.val, by omega⟩ : Fin 17622) := by
  decide

theorem decodeState_stateVectorProof0232
    (state : Fin 17622)
    (lower : 14848 ≤ state.val)
    (upper : state.val < 14912) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 14848, by omega⟩
  have state_eq :
      (⟨14848 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0232 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0233 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨14912 + candidate.val, by omega⟩ : Fin 17622)) =
        (⟨14912 + candidate.val, by omega⟩ : Fin 17622) := by
  decide

theorem decodeState_stateVectorProof0233
    (state : Fin 17622)
    (lower : 14912 ≤ state.val)
    (upper : state.val < 14976) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 14912, by omega⟩
  have state_eq :
      (⟨14912 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0233 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0234 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨14976 + candidate.val, by omega⟩ : Fin 17622)) =
        (⟨14976 + candidate.val, by omega⟩ : Fin 17622) := by
  decide

theorem decodeState_stateVectorProof0234
    (state : Fin 17622)
    (lower : 14976 ≤ state.val)
    (upper : state.val < 15040) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 14976, by omega⟩
  have state_eq :
      (⟨14976 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0234 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0235 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨15040 + candidate.val, by omega⟩ : Fin 17622)) =
        (⟨15040 + candidate.val, by omega⟩ : Fin 17622) := by
  decide

theorem decodeState_stateVectorProof0235
    (state : Fin 17622)
    (lower : 15040 ≤ state.val)
    (upper : state.val < 15104) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 15040, by omega⟩
  have state_eq :
      (⟨15040 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0235 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0236 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨15104 + candidate.val, by omega⟩ : Fin 17622)) =
        (⟨15104 + candidate.val, by omega⟩ : Fin 17622) := by
  decide

theorem decodeState_stateVectorProof0236
    (state : Fin 17622)
    (lower : 15104 ≤ state.val)
    (upper : state.val < 15168) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 15104, by omega⟩
  have state_eq :
      (⟨15104 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0236 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0237 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨15168 + candidate.val, by omega⟩ : Fin 17622)) =
        (⟨15168 + candidate.val, by omega⟩ : Fin 17622) := by
  decide

theorem decodeState_stateVectorProof0237
    (state : Fin 17622)
    (lower : 15168 ≤ state.val)
    (upper : state.val < 15232) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 15168, by omega⟩
  have state_eq :
      (⟨15168 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0237 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0238 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨15232 + candidate.val, by omega⟩ : Fin 17622)) =
        (⟨15232 + candidate.val, by omega⟩ : Fin 17622) := by
  decide

theorem decodeState_stateVectorProof0238
    (state : Fin 17622)
    (lower : 15232 ≤ state.val)
    (upper : state.val < 15296) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 15232, by omega⟩
  have state_eq :
      (⟨15232 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0238 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0239 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨15296 + candidate.val, by omega⟩ : Fin 17622)) =
        (⟨15296 + candidate.val, by omega⟩ : Fin 17622) := by
  decide

theorem decodeState_stateVectorProof0239
    (state : Fin 17622)
    (lower : 15296 ≤ state.val)
    (upper : state.val < 15360) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 15296, by omega⟩
  have state_eq :
      (⟨15296 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0239 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0240 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨15360 + candidate.val, by omega⟩ : Fin 17622)) =
        (⟨15360 + candidate.val, by omega⟩ : Fin 17622) := by
  decide

theorem decodeState_stateVectorProof0240
    (state : Fin 17622)
    (lower : 15360 ≤ state.val)
    (upper : state.val < 15424) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 15360, by omega⟩
  have state_eq :
      (⟨15360 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0240 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0241 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨15424 + candidate.val, by omega⟩ : Fin 17622)) =
        (⟨15424 + candidate.val, by omega⟩ : Fin 17622) := by
  decide

theorem decodeState_stateVectorProof0241
    (state : Fin 17622)
    (lower : 15424 ≤ state.val)
    (upper : state.val < 15488) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 15424, by omega⟩
  have state_eq :
      (⟨15424 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0241 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0242 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨15488 + candidate.val, by omega⟩ : Fin 17622)) =
        (⟨15488 + candidate.val, by omega⟩ : Fin 17622) := by
  decide

theorem decodeState_stateVectorProof0242
    (state : Fin 17622)
    (lower : 15488 ≤ state.val)
    (upper : state.val < 15552) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 15488, by omega⟩
  have state_eq :
      (⟨15488 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0242 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0243 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨15552 + candidate.val, by omega⟩ : Fin 17622)) =
        (⟨15552 + candidate.val, by omega⟩ : Fin 17622) := by
  decide

theorem decodeState_stateVectorProof0243
    (state : Fin 17622)
    (lower : 15552 ≤ state.val)
    (upper : state.val < 15616) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 15552, by omega⟩
  have state_eq :
      (⟨15552 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0243 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0244 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨15616 + candidate.val, by omega⟩ : Fin 17622)) =
        (⟨15616 + candidate.val, by omega⟩ : Fin 17622) := by
  decide

theorem decodeState_stateVectorProof0244
    (state : Fin 17622)
    (lower : 15616 ≤ state.val)
    (upper : state.val < 15680) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 15616, by omega⟩
  have state_eq :
      (⟨15616 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0244 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0245 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨15680 + candidate.val, by omega⟩ : Fin 17622)) =
        (⟨15680 + candidate.val, by omega⟩ : Fin 17622) := by
  decide

theorem decodeState_stateVectorProof0245
    (state : Fin 17622)
    (lower : 15680 ≤ state.val)
    (upper : state.val < 15744) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 15680, by omega⟩
  have state_eq :
      (⟨15680 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0245 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0246 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨15744 + candidate.val, by omega⟩ : Fin 17622)) =
        (⟨15744 + candidate.val, by omega⟩ : Fin 17622) := by
  decide

theorem decodeState_stateVectorProof0246
    (state : Fin 17622)
    (lower : 15744 ≤ state.val)
    (upper : state.val < 15808) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 15744, by omega⟩
  have state_eq :
      (⟨15744 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0246 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0247 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨15808 + candidate.val, by omega⟩ : Fin 17622)) =
        (⟨15808 + candidate.val, by omega⟩ : Fin 17622) := by
  decide

theorem decodeState_stateVectorProof0247
    (state : Fin 17622)
    (lower : 15808 ≤ state.val)
    (upper : state.val < 15872) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 15808, by omega⟩
  have state_eq :
      (⟨15808 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0247 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0248 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨15872 + candidate.val, by omega⟩ : Fin 17622)) =
        (⟨15872 + candidate.val, by omega⟩ : Fin 17622) := by
  decide

theorem decodeState_stateVectorProof0248
    (state : Fin 17622)
    (lower : 15872 ≤ state.val)
    (upper : state.val < 15936) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 15872, by omega⟩
  have state_eq :
      (⟨15872 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0248 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0249 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨15936 + candidate.val, by omega⟩ : Fin 17622)) =
        (⟨15936 + candidate.val, by omega⟩ : Fin 17622) := by
  decide

theorem decodeState_stateVectorProof0249
    (state : Fin 17622)
    (lower : 15936 ≤ state.val)
    (upper : state.val < 16000) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 15936, by omega⟩
  have state_eq :
      (⟨15936 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0249 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0250 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨16000 + candidate.val, by omega⟩ : Fin 17622)) =
        (⟨16000 + candidate.val, by omega⟩ : Fin 17622) := by
  decide

theorem decodeState_stateVectorProof0250
    (state : Fin 17622)
    (lower : 16000 ≤ state.val)
    (upper : state.val < 16064) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 16000, by omega⟩
  have state_eq :
      (⟨16000 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0250 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0251 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨16064 + candidate.val, by omega⟩ : Fin 17622)) =
        (⟨16064 + candidate.val, by omega⟩ : Fin 17622) := by
  decide

theorem decodeState_stateVectorProof0251
    (state : Fin 17622)
    (lower : 16064 ≤ state.val)
    (upper : state.val < 16128) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 16064, by omega⟩
  have state_eq :
      (⟨16064 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0251 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0252 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨16128 + candidate.val, by omega⟩ : Fin 17622)) =
        (⟨16128 + candidate.val, by omega⟩ : Fin 17622) := by
  decide

theorem decodeState_stateVectorProof0252
    (state : Fin 17622)
    (lower : 16128 ≤ state.val)
    (upper : state.val < 16192) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 16128, by omega⟩
  have state_eq :
      (⟨16128 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0252 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0253 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨16192 + candidate.val, by omega⟩ : Fin 17622)) =
        (⟨16192 + candidate.val, by omega⟩ : Fin 17622) := by
  decide

theorem decodeState_stateVectorProof0253
    (state : Fin 17622)
    (lower : 16192 ≤ state.val)
    (upper : state.val < 16256) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 16192, by omega⟩
  have state_eq :
      (⟨16192 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0253 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0254 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨16256 + candidate.val, by omega⟩ : Fin 17622)) =
        (⟨16256 + candidate.val, by omega⟩ : Fin 17622) := by
  decide

theorem decodeState_stateVectorProof0254
    (state : Fin 17622)
    (lower : 16256 ≤ state.val)
    (upper : state.val < 16320) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 16256, by omega⟩
  have state_eq :
      (⟨16256 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0254 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0255 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨16320 + candidate.val, by omega⟩ : Fin 17622)) =
        (⟨16320 + candidate.val, by omega⟩ : Fin 17622) := by
  decide

theorem decodeState_stateVectorProof0255
    (state : Fin 17622)
    (lower : 16320 ≤ state.val)
    (upper : state.val < 16384) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 16320, by omega⟩
  have state_eq :
      (⟨16320 + offset.val, by omega⟩ : Fin 17622) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0255 offset

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.Shards
