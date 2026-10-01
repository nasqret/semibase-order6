import SemigroupBasis.CoRoots.Order6SporadicSection27F9G1Canonical
import SemigroupBasis.CoRoots.S5_345Factors

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.Order6SporadicSection27F9G1Targets.S6_13559

open SemigroupBasis
open SemigroupBasis.CoRoots.Order6SporadicSection27
open SemigroupBasis.Examples

private def row6
    (c0 c1 c2 c3 c4 c5 column : Fin 6) : Fin 6 :=
  if column = 0 then c0 else
    if column = 1 then c1 else
      if column = 2 then c2 else
        if column = 3 then c3 else
          if column = 4 then c4 else c5

/-- Exact direct catalogue table for published F9/S6_13559. -/
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 0 0 0 0 right else
    if left = 1 then row6 0 0 0 0 1 2 right else
      if left = 2 then row6 2 2 2 2 2 2 right else
        if left = 3 then row6 0 1 2 3 0 0 right else
          if left = 4 then row6 0 0 0 0 4 5 right else
            row6 5 5 5 5 5 5 right

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "191a9642b042c8b36acf7c8252f234a1817c2ee19dcf2d61703dc9149e4604d8"

def tableRowsOneBased : List (List Nat) :=
  List.ofFn fun left : Fin 6 =>
    List.ofFn fun right : Fin 6 => (mul left right).val + 1

theorem tableRowsOneBased_certificate :
    tableRowsOneBased =
      [[1, 1, 1, 1, 1, 1],
        [1, 1, 1, 1, 2, 3],
        [3, 3, 3, 3, 3, 3],
        [1, 2, 3, 4, 1, 1],
        [1, 1, 1, 1, 5, 6],
        [6, 6, 6, 6, 6, 6]] := by
  decide

set_option maxHeartbeats 0 in
theorem checkA_H_certificate :
    table.checkIdentityFused (lawA_H.map toFinFive) = true := by
  decide

set_option maxHeartbeats 0 in
theorem checkE_HK_certificate :
    table.checkIdentityFused (lawE_HK.map toFinFive) = true := by
  decide

set_option maxHeartbeats 0 in
theorem checkE_H_certificate :
    table.checkIdentityFused (lawE_H.map toFinFive) = true := by
  decide

set_option maxHeartbeats 0 in
theorem checkD_HKT_certificate :
    table.checkIdentityFused (lawD_HKT.map toFinFive) = true := by
  decide

set_option maxHeartbeats 0 in
theorem checkD_HK_certificate :
    table.checkIdentityFused (lawD_HK.map toFinFive) = true := by
  decide

set_option maxHeartbeats 0 in
theorem checkB_HK_certificate :
    table.checkIdentityFused (lawB_HK.map toFinFive) = true := by
  decide

set_option maxHeartbeats 0 in
theorem checkC_HK_certificate :
    table.checkIdentityFused (lawC_HK.map toFinFive) = true := by
  decide

set_option maxHeartbeats 0 in
theorem checkD_HT_certificate :
    table.checkIdentityFused (lawD_HT.map toFinFive) = true := by
  decide

set_option maxHeartbeats 0 in
theorem checkD_H_certificate :
    table.checkIdentityFused (lawD_H.map toFinFive) = true := by
  decide

set_option maxHeartbeats 0 in
theorem checkB_H_certificate :
    table.checkIdentityFused (lawB_H.map toFinFive) = true := by
  decide

set_option maxHeartbeats 0 in
theorem checkC_H_certificate :
    table.checkIdentityFused (lawC_H.map toFinFive) = true := by
  decide

set_option maxHeartbeats 0 in
theorem checkA_empty_certificate :
    table.checkIdentityFused (lawA_empty.map toFinFive) = true := by
  decide

set_option maxHeartbeats 0 in
theorem checkE_K_certificate :
    table.checkIdentityFused (lawE_K.map toFinFive) = true := by
  decide

set_option maxHeartbeats 0 in
theorem checkE_empty_certificate :
    table.checkIdentityFused (lawE_empty.map toFinFive) = true := by
  decide

set_option maxHeartbeats 0 in
theorem checkD_KT_certificate :
    table.checkIdentityFused (lawD_KT.map toFinFive) = true := by
  decide

set_option maxHeartbeats 0 in
theorem checkD_K_certificate :
    table.checkIdentityFused (lawD_K.map toFinFive) = true := by
  decide

set_option maxHeartbeats 0 in
theorem checkB_K_certificate :
    table.checkIdentityFused (lawB_K.map toFinFive) = true := by
  decide

set_option maxHeartbeats 0 in
theorem checkC_K_certificate :
    table.checkIdentityFused (lawC_K.map toFinFive) = true := by
  decide

set_option maxHeartbeats 0 in
theorem checkD_T_certificate :
    table.checkIdentityFused (lawD_T.map toFinFive) = true := by
  decide

set_option maxHeartbeats 0 in
theorem checkD_empty_certificate :
    table.checkIdentityFused (lawD_empty.map toFinFive) = true := by
  decide

set_option maxHeartbeats 0 in
theorem checkB_empty_certificate :
    table.checkIdentityFused (lawB_empty.map toFinFive) = true := by
  decide

set_option maxHeartbeats 0 in
theorem checkC_empty_certificate :
    table.checkIdentityFused (lawC_empty.map toFinFive) = true := by
  decide

theorem models : Models table.semigroup basis :=
  models_of_individual_fused_checks table
    checkA_H_certificate
    checkE_HK_certificate
    checkE_H_certificate
    checkD_HKT_certificate
    checkD_HK_certificate
    checkB_HK_certificate
    checkC_HK_certificate
    checkD_HT_certificate
    checkD_H_certificate
    checkB_H_certificate
    checkC_H_certificate
    checkA_empty_certificate
    checkE_K_certificate
    checkE_empty_certificate
    checkD_KT_certificate
    checkD_K_certificate
    checkB_K_certificate
    checkC_K_certificate
    checkD_T_certificate
    checkD_empty_certificate
    checkB_empty_certificate
    checkC_empty_certificate

theorem oppositeModels :
    Models table.semigroup.opposite oppositeBasis :=
  models.oppositeReversed

/-! ## Shared semantic interfaces -/

/-- The literal subsemigroup `{0,3,2}` is the three-element left regular
band and therefore recovers first-occurrence order. -/
def firstOccurrenceEmbedding :
    Embedding leftRegularBandThree.semigroup table.semigroup where
  toFun := fun value : Fin 3 =>
    if value.val = 0 then (0 : Fin 6)
    else if value.val = 1 then (3 : Fin 6)
    else (2 : Fin 6)
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

theorem valid_firstOccurrenceSequence_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    firstOccurrenceSequence identity.lhs.toList =
      firstOccurrenceSequence identity.rhs.toList :=
  SemigroupBasis.CoRoots.S5_345Factors.leftRegularBandThreeValid_firstOccurrenceSequence_eq
      identity
      (firstOccurrenceEmbedding.pullback_identity identity valid)

/-- The exact zero-based separator values used in the published F9 proof. -/
def betaSeparator : BetaSeparator table.semigroup where
  ordinary := 3
  active := 1
  bridge := 4
  fresh := 5
  hit := 0
  miss := 2
  hit_ne_miss := by decide
  ordinary_active := by decide
  active_active := by decide
  active_ordinary := by decide
  active_bridge := by decide
  active_fresh := by decide
  fresh_absorbs := by
    intro value
    apply Fin.ext
    revert value
    decide
  hit_absorbs := by
    intro value
    apply Fin.ext
    revert value
    decide
  miss_absorbs := by
    intro value
    apply Fin.ext
    revert value
    decide

end SemigroupBasis.Generated.Order6SporadicSection27F9G1Targets.S6_13559

namespace SemigroupBasis.Generated.Order6SporadicSection27F9G1Targets.S6_13561

open SemigroupBasis
open SemigroupBasis.CoRoots.Order6SporadicSection27
open SemigroupBasis.Examples

private def row6
    (c0 c1 c2 c3 c4 c5 column : Fin 6) : Fin 6 :=
  if column = 0 then c0 else
    if column = 1 then c1 else
      if column = 2 then c2 else
        if column = 3 then c3 else
          if column = 4 then c4 else c5

/-- Exact direct catalogue table for published G1/S6_13561. -/
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 0 0 0 0 right else
    if left = 1 then row6 0 0 0 0 1 2 right else
      if left = 2 then row6 2 2 2 2 2 2 right else
        if left = 3 then row6 0 1 2 3 2 2 right else
          if left = 4 then row6 2 2 2 2 4 5 right else
            row6 5 5 5 5 5 5 right

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

/-- SHA-256 of the compact canonical JSON encoding of the one-based table. -/
def tableSHA256 : String :=
  "2ba94299c58dc7728b03cae78e0d67b9689d04966792760065630f2ad1096d04"

def tableRowsOneBased : List (List Nat) :=
  List.ofFn fun left : Fin 6 =>
    List.ofFn fun right : Fin 6 => (mul left right).val + 1

theorem tableRowsOneBased_certificate :
    tableRowsOneBased =
      [[1, 1, 1, 1, 1, 1],
        [1, 1, 1, 1, 2, 3],
        [3, 3, 3, 3, 3, 3],
        [1, 2, 3, 4, 3, 3],
        [3, 3, 3, 3, 5, 6],
        [6, 6, 6, 6, 6, 6]] := by
  decide

set_option maxHeartbeats 0 in
theorem checkA_H_certificate :
    table.checkIdentityFused (lawA_H.map toFinFive) = true := by
  decide

set_option maxHeartbeats 0 in
theorem checkE_HK_certificate :
    table.checkIdentityFused (lawE_HK.map toFinFive) = true := by
  decide

set_option maxHeartbeats 0 in
theorem checkE_H_certificate :
    table.checkIdentityFused (lawE_H.map toFinFive) = true := by
  decide

set_option maxHeartbeats 0 in
theorem checkD_HKT_certificate :
    table.checkIdentityFused (lawD_HKT.map toFinFive) = true := by
  decide

set_option maxHeartbeats 0 in
theorem checkD_HK_certificate :
    table.checkIdentityFused (lawD_HK.map toFinFive) = true := by
  decide

set_option maxHeartbeats 0 in
theorem checkB_HK_certificate :
    table.checkIdentityFused (lawB_HK.map toFinFive) = true := by
  decide

set_option maxHeartbeats 0 in
theorem checkC_HK_certificate :
    table.checkIdentityFused (lawC_HK.map toFinFive) = true := by
  decide

set_option maxHeartbeats 0 in
theorem checkD_HT_certificate :
    table.checkIdentityFused (lawD_HT.map toFinFive) = true := by
  decide

set_option maxHeartbeats 0 in
theorem checkD_H_certificate :
    table.checkIdentityFused (lawD_H.map toFinFive) = true := by
  decide

set_option maxHeartbeats 0 in
theorem checkB_H_certificate :
    table.checkIdentityFused (lawB_H.map toFinFive) = true := by
  decide

set_option maxHeartbeats 0 in
theorem checkC_H_certificate :
    table.checkIdentityFused (lawC_H.map toFinFive) = true := by
  decide

set_option maxHeartbeats 0 in
theorem checkA_empty_certificate :
    table.checkIdentityFused (lawA_empty.map toFinFive) = true := by
  decide

set_option maxHeartbeats 0 in
theorem checkE_K_certificate :
    table.checkIdentityFused (lawE_K.map toFinFive) = true := by
  decide

set_option maxHeartbeats 0 in
theorem checkE_empty_certificate :
    table.checkIdentityFused (lawE_empty.map toFinFive) = true := by
  decide

set_option maxHeartbeats 0 in
theorem checkD_KT_certificate :
    table.checkIdentityFused (lawD_KT.map toFinFive) = true := by
  decide

set_option maxHeartbeats 0 in
theorem checkD_K_certificate :
    table.checkIdentityFused (lawD_K.map toFinFive) = true := by
  decide

set_option maxHeartbeats 0 in
theorem checkB_K_certificate :
    table.checkIdentityFused (lawB_K.map toFinFive) = true := by
  decide

set_option maxHeartbeats 0 in
theorem checkC_K_certificate :
    table.checkIdentityFused (lawC_K.map toFinFive) = true := by
  decide

set_option maxHeartbeats 0 in
theorem checkD_T_certificate :
    table.checkIdentityFused (lawD_T.map toFinFive) = true := by
  decide

set_option maxHeartbeats 0 in
theorem checkD_empty_certificate :
    table.checkIdentityFused (lawD_empty.map toFinFive) = true := by
  decide

set_option maxHeartbeats 0 in
theorem checkB_empty_certificate :
    table.checkIdentityFused (lawB_empty.map toFinFive) = true := by
  decide

set_option maxHeartbeats 0 in
theorem checkC_empty_certificate :
    table.checkIdentityFused (lawC_empty.map toFinFive) = true := by
  decide

theorem models : Models table.semigroup basis :=
  models_of_individual_fused_checks table
    checkA_H_certificate
    checkE_HK_certificate
    checkE_H_certificate
    checkD_HKT_certificate
    checkD_HK_certificate
    checkB_HK_certificate
    checkC_HK_certificate
    checkD_HT_certificate
    checkD_H_certificate
    checkB_H_certificate
    checkC_H_certificate
    checkA_empty_certificate
    checkE_K_certificate
    checkE_empty_certificate
    checkD_KT_certificate
    checkD_K_certificate
    checkB_K_certificate
    checkC_K_certificate
    checkD_T_certificate
    checkD_empty_certificate
    checkB_empty_certificate
    checkC_empty_certificate

theorem oppositeModels :
    Models table.semigroup.opposite oppositeBasis :=
  models.oppositeReversed

/-! ## Shared semantic interfaces -/

/-- The literal subsemigroup `{0,3,2}` is the three-element left regular
band and therefore recovers first-occurrence order. -/
def firstOccurrenceEmbedding :
    Embedding leftRegularBandThree.semigroup table.semigroup where
  toFun := fun value : Fin 3 =>
    if value.val = 0 then (0 : Fin 6)
    else if value.val = 1 then (3 : Fin 6)
    else (2 : Fin 6)
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

theorem valid_firstOccurrenceSequence_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    firstOccurrenceSequence identity.lhs.toList =
      firstOccurrenceSequence identity.rhs.toList :=
  SemigroupBasis.CoRoots.S5_345Factors.leftRegularBandThreeValid_firstOccurrenceSequence_eq
      identity
      (firstOccurrenceEmbedding.pullback_identity identity valid)

/-- The exact zero-based separator values used in the published G1 proof. -/
def betaSeparator : BetaSeparator table.semigroup where
  ordinary := 3
  active := 1
  bridge := 4
  fresh := 5
  hit := 0
  miss := 2
  hit_ne_miss := by decide
  ordinary_active := by decide
  active_active := by decide
  active_ordinary := by decide
  active_bridge := by decide
  active_fresh := by decide
  fresh_absorbs := by
    intro value
    apply Fin.ext
    revert value
    decide
  hit_absorbs := by
    intro value
    apply Fin.ext
    revert value
    decide
  miss_absorbs := by
    intro value
    apply Fin.ext
    revert value
    decide

end SemigroupBasis.Generated.Order6SporadicSection27F9G1Targets.S6_13561
