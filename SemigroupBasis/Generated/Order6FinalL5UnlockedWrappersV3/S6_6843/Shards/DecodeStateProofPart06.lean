import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.Shards.DecodeState
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.Shards.StateVector
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.Shards

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0192 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨12288 + candidate.val, by omega⟩ : Fin 18432)) =
        (⟨12288 + candidate.val, by omega⟩ : Fin 18432) := by
  decide

theorem decodeState_stateVectorProof0192
    (state : Fin 18432)
    (lower : 12288 ≤ state.val)
    (upper : state.val < 12352) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 12288, by omega⟩
  have state_eq :
      (⟨12288 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0192 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0193 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨12352 + candidate.val, by omega⟩ : Fin 18432)) =
        (⟨12352 + candidate.val, by omega⟩ : Fin 18432) := by
  decide

theorem decodeState_stateVectorProof0193
    (state : Fin 18432)
    (lower : 12352 ≤ state.val)
    (upper : state.val < 12416) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 12352, by omega⟩
  have state_eq :
      (⟨12352 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0193 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0194 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨12416 + candidate.val, by omega⟩ : Fin 18432)) =
        (⟨12416 + candidate.val, by omega⟩ : Fin 18432) := by
  decide

theorem decodeState_stateVectorProof0194
    (state : Fin 18432)
    (lower : 12416 ≤ state.val)
    (upper : state.val < 12480) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 12416, by omega⟩
  have state_eq :
      (⟨12416 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0194 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0195 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨12480 + candidate.val, by omega⟩ : Fin 18432)) =
        (⟨12480 + candidate.val, by omega⟩ : Fin 18432) := by
  decide

theorem decodeState_stateVectorProof0195
    (state : Fin 18432)
    (lower : 12480 ≤ state.val)
    (upper : state.val < 12544) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 12480, by omega⟩
  have state_eq :
      (⟨12480 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0195 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0196 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨12544 + candidate.val, by omega⟩ : Fin 18432)) =
        (⟨12544 + candidate.val, by omega⟩ : Fin 18432) := by
  decide

theorem decodeState_stateVectorProof0196
    (state : Fin 18432)
    (lower : 12544 ≤ state.val)
    (upper : state.val < 12608) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 12544, by omega⟩
  have state_eq :
      (⟨12544 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0196 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0197 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨12608 + candidate.val, by omega⟩ : Fin 18432)) =
        (⟨12608 + candidate.val, by omega⟩ : Fin 18432) := by
  decide

theorem decodeState_stateVectorProof0197
    (state : Fin 18432)
    (lower : 12608 ≤ state.val)
    (upper : state.val < 12672) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 12608, by omega⟩
  have state_eq :
      (⟨12608 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0197 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0198 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨12672 + candidate.val, by omega⟩ : Fin 18432)) =
        (⟨12672 + candidate.val, by omega⟩ : Fin 18432) := by
  decide

theorem decodeState_stateVectorProof0198
    (state : Fin 18432)
    (lower : 12672 ≤ state.val)
    (upper : state.val < 12736) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 12672, by omega⟩
  have state_eq :
      (⟨12672 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0198 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0199 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨12736 + candidate.val, by omega⟩ : Fin 18432)) =
        (⟨12736 + candidate.val, by omega⟩ : Fin 18432) := by
  decide

theorem decodeState_stateVectorProof0199
    (state : Fin 18432)
    (lower : 12736 ≤ state.val)
    (upper : state.val < 12800) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 12736, by omega⟩
  have state_eq :
      (⟨12736 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0199 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0200 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨12800 + candidate.val, by omega⟩ : Fin 18432)) =
        (⟨12800 + candidate.val, by omega⟩ : Fin 18432) := by
  decide

theorem decodeState_stateVectorProof0200
    (state : Fin 18432)
    (lower : 12800 ≤ state.val)
    (upper : state.val < 12864) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 12800, by omega⟩
  have state_eq :
      (⟨12800 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0200 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0201 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨12864 + candidate.val, by omega⟩ : Fin 18432)) =
        (⟨12864 + candidate.val, by omega⟩ : Fin 18432) := by
  decide

theorem decodeState_stateVectorProof0201
    (state : Fin 18432)
    (lower : 12864 ≤ state.val)
    (upper : state.val < 12928) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 12864, by omega⟩
  have state_eq :
      (⟨12864 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0201 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0202 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨12928 + candidate.val, by omega⟩ : Fin 18432)) =
        (⟨12928 + candidate.val, by omega⟩ : Fin 18432) := by
  decide

theorem decodeState_stateVectorProof0202
    (state : Fin 18432)
    (lower : 12928 ≤ state.val)
    (upper : state.val < 12992) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 12928, by omega⟩
  have state_eq :
      (⟨12928 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0202 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0203 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨12992 + candidate.val, by omega⟩ : Fin 18432)) =
        (⟨12992 + candidate.val, by omega⟩ : Fin 18432) := by
  decide

theorem decodeState_stateVectorProof0203
    (state : Fin 18432)
    (lower : 12992 ≤ state.val)
    (upper : state.val < 13056) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 12992, by omega⟩
  have state_eq :
      (⟨12992 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0203 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0204 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨13056 + candidate.val, by omega⟩ : Fin 18432)) =
        (⟨13056 + candidate.val, by omega⟩ : Fin 18432) := by
  decide

theorem decodeState_stateVectorProof0204
    (state : Fin 18432)
    (lower : 13056 ≤ state.val)
    (upper : state.val < 13120) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 13056, by omega⟩
  have state_eq :
      (⟨13056 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0204 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0205 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨13120 + candidate.val, by omega⟩ : Fin 18432)) =
        (⟨13120 + candidate.val, by omega⟩ : Fin 18432) := by
  decide

theorem decodeState_stateVectorProof0205
    (state : Fin 18432)
    (lower : 13120 ≤ state.val)
    (upper : state.val < 13184) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 13120, by omega⟩
  have state_eq :
      (⟨13120 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0205 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0206 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨13184 + candidate.val, by omega⟩ : Fin 18432)) =
        (⟨13184 + candidate.val, by omega⟩ : Fin 18432) := by
  decide

theorem decodeState_stateVectorProof0206
    (state : Fin 18432)
    (lower : 13184 ≤ state.val)
    (upper : state.val < 13248) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 13184, by omega⟩
  have state_eq :
      (⟨13184 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0206 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0207 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨13248 + candidate.val, by omega⟩ : Fin 18432)) =
        (⟨13248 + candidate.val, by omega⟩ : Fin 18432) := by
  decide

theorem decodeState_stateVectorProof0207
    (state : Fin 18432)
    (lower : 13248 ≤ state.val)
    (upper : state.val < 13312) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 13248, by omega⟩
  have state_eq :
      (⟨13248 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0207 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0208 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨13312 + candidate.val, by omega⟩ : Fin 18432)) =
        (⟨13312 + candidate.val, by omega⟩ : Fin 18432) := by
  decide

theorem decodeState_stateVectorProof0208
    (state : Fin 18432)
    (lower : 13312 ≤ state.val)
    (upper : state.val < 13376) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 13312, by omega⟩
  have state_eq :
      (⟨13312 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0208 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0209 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨13376 + candidate.val, by omega⟩ : Fin 18432)) =
        (⟨13376 + candidate.val, by omega⟩ : Fin 18432) := by
  decide

theorem decodeState_stateVectorProof0209
    (state : Fin 18432)
    (lower : 13376 ≤ state.val)
    (upper : state.val < 13440) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 13376, by omega⟩
  have state_eq :
      (⟨13376 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0209 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0210 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨13440 + candidate.val, by omega⟩ : Fin 18432)) =
        (⟨13440 + candidate.val, by omega⟩ : Fin 18432) := by
  decide

theorem decodeState_stateVectorProof0210
    (state : Fin 18432)
    (lower : 13440 ≤ state.val)
    (upper : state.val < 13504) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 13440, by omega⟩
  have state_eq :
      (⟨13440 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0210 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0211 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨13504 + candidate.val, by omega⟩ : Fin 18432)) =
        (⟨13504 + candidate.val, by omega⟩ : Fin 18432) := by
  decide

theorem decodeState_stateVectorProof0211
    (state : Fin 18432)
    (lower : 13504 ≤ state.val)
    (upper : state.val < 13568) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 13504, by omega⟩
  have state_eq :
      (⟨13504 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0211 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0212 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨13568 + candidate.val, by omega⟩ : Fin 18432)) =
        (⟨13568 + candidate.val, by omega⟩ : Fin 18432) := by
  decide

theorem decodeState_stateVectorProof0212
    (state : Fin 18432)
    (lower : 13568 ≤ state.val)
    (upper : state.val < 13632) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 13568, by omega⟩
  have state_eq :
      (⟨13568 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0212 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0213 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨13632 + candidate.val, by omega⟩ : Fin 18432)) =
        (⟨13632 + candidate.val, by omega⟩ : Fin 18432) := by
  decide

theorem decodeState_stateVectorProof0213
    (state : Fin 18432)
    (lower : 13632 ≤ state.val)
    (upper : state.val < 13696) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 13632, by omega⟩
  have state_eq :
      (⟨13632 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0213 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0214 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨13696 + candidate.val, by omega⟩ : Fin 18432)) =
        (⟨13696 + candidate.val, by omega⟩ : Fin 18432) := by
  decide

theorem decodeState_stateVectorProof0214
    (state : Fin 18432)
    (lower : 13696 ≤ state.val)
    (upper : state.val < 13760) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 13696, by omega⟩
  have state_eq :
      (⟨13696 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0214 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0215 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨13760 + candidate.val, by omega⟩ : Fin 18432)) =
        (⟨13760 + candidate.val, by omega⟩ : Fin 18432) := by
  decide

theorem decodeState_stateVectorProof0215
    (state : Fin 18432)
    (lower : 13760 ≤ state.val)
    (upper : state.val < 13824) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 13760, by omega⟩
  have state_eq :
      (⟨13760 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0215 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0216 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨13824 + candidate.val, by omega⟩ : Fin 18432)) =
        (⟨13824 + candidate.val, by omega⟩ : Fin 18432) := by
  decide

theorem decodeState_stateVectorProof0216
    (state : Fin 18432)
    (lower : 13824 ≤ state.val)
    (upper : state.val < 13888) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 13824, by omega⟩
  have state_eq :
      (⟨13824 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0216 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0217 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨13888 + candidate.val, by omega⟩ : Fin 18432)) =
        (⟨13888 + candidate.val, by omega⟩ : Fin 18432) := by
  decide

theorem decodeState_stateVectorProof0217
    (state : Fin 18432)
    (lower : 13888 ≤ state.val)
    (upper : state.val < 13952) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 13888, by omega⟩
  have state_eq :
      (⟨13888 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0217 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0218 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨13952 + candidate.val, by omega⟩ : Fin 18432)) =
        (⟨13952 + candidate.val, by omega⟩ : Fin 18432) := by
  decide

theorem decodeState_stateVectorProof0218
    (state : Fin 18432)
    (lower : 13952 ≤ state.val)
    (upper : state.val < 14016) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 13952, by omega⟩
  have state_eq :
      (⟨13952 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0218 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0219 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨14016 + candidate.val, by omega⟩ : Fin 18432)) =
        (⟨14016 + candidate.val, by omega⟩ : Fin 18432) := by
  decide

theorem decodeState_stateVectorProof0219
    (state : Fin 18432)
    (lower : 14016 ≤ state.val)
    (upper : state.val < 14080) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 14016, by omega⟩
  have state_eq :
      (⟨14016 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0219 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0220 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨14080 + candidate.val, by omega⟩ : Fin 18432)) =
        (⟨14080 + candidate.val, by omega⟩ : Fin 18432) := by
  decide

theorem decodeState_stateVectorProof0220
    (state : Fin 18432)
    (lower : 14080 ≤ state.val)
    (upper : state.val < 14144) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 14080, by omega⟩
  have state_eq :
      (⟨14080 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0220 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0221 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨14144 + candidate.val, by omega⟩ : Fin 18432)) =
        (⟨14144 + candidate.val, by omega⟩ : Fin 18432) := by
  decide

theorem decodeState_stateVectorProof0221
    (state : Fin 18432)
    (lower : 14144 ≤ state.val)
    (upper : state.val < 14208) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 14144, by omega⟩
  have state_eq :
      (⟨14144 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0221 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0222 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨14208 + candidate.val, by omega⟩ : Fin 18432)) =
        (⟨14208 + candidate.val, by omega⟩ : Fin 18432) := by
  decide

theorem decodeState_stateVectorProof0222
    (state : Fin 18432)
    (lower : 14208 ≤ state.val)
    (upper : state.val < 14272) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 14208, by omega⟩
  have state_eq :
      (⟨14208 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0222 offset

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVectorBounded0223 :
    ∀ candidate : Fin 64,
      decodeState (stateVector (⟨14272 + candidate.val, by omega⟩ : Fin 18432)) =
        (⟨14272 + candidate.val, by omega⟩ : Fin 18432) := by
  decide

theorem decodeState_stateVectorProof0223
    (state : Fin 18432)
    (lower : 14272 ≤ state.val)
    (upper : state.val < 14336) :
    decodeState (stateVector state) = state := by
  let offset : Fin 64 := ⟨state.val - 14272, by omega⟩
  have state_eq :
      (⟨14272 + offset.val, by omega⟩ : Fin 18432) = state := by
    apply Fin.ext
    simp only [offset]
    omega
  rw [← state_eq]
  exact decodeState_stateVectorBounded0223 offset

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.Shards
