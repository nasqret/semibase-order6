import SemigroupBasis.FiniteNilpotentCounterexample

namespace SemigroupBasis.Generated.Order6GenericCASRootData

open SemigroupBasis

namespace S6_2802

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,3,1],[1,1,1,1,1,1],[1,1,1,1,1,4],[1,3,1,1,2,1],[1,1,1,4,1,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (2 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (0 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

/-- The exact opposite orientation required by the generic-CAS route. -/
def oppositeTable : FiniteTable where
  order := 6
  mul := fun left right => mul right left
  assoc := by decide

def tableSHA256 : String :=
  "b8d0932f17335c1c4bfb89e334ca5f97c6f40ae7887e7d510df2127307f8b1e7"

def law0 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩
def law1 : Identity Nat :=
  ⟨⟨0, [0, 0, 0]⟩, ⟨0, [0, 0, 0, 0]⟩⟩
def law2 : Identity Nat :=
  ⟨⟨0, [0, 0, 1]⟩, ⟨0, [0, 0, 0, 1]⟩⟩
def law3 : Identity Nat :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨0, [0, 0, 1, 1]⟩⟩
def law4 : Identity Nat :=
  ⟨⟨0, [0, 1, 2]⟩, ⟨0, [0, 0, 1, 2]⟩⟩

/-- The displayed generic-CAS root basis in packet order. -/
def basis : List (Identity Nat) :=
  [law0, law1, law2, law3, law4]

def basisSHA256 : String :=
  "085da82ebd971a5da46be0e2c90a8eb38f23c11c932231109729e83cb28abef0"

private def law0ToFinite : Nat → Fin 2
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨1, by decide⟩
  | _ => ⟨0, by decide⟩

private def law0FromFinite (index : Fin 2) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
private theorem law0Valid :
    law0.SatisfiedBy oppositeTable.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    oppositeTable law0 law0ToFinite law0FromFinite
    (by decide) (by decide)
private def law1ToFinite : Nat → Fin 1
  | 0 => ⟨0, by decide⟩
  | _ => ⟨0, by decide⟩

private def law1FromFinite (index : Fin 1) : Nat :=
  match index.val with
  | 0 => 0
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
private theorem law1Valid :
    law1.SatisfiedBy oppositeTable.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    oppositeTable law1 law1ToFinite law1FromFinite
    (by decide) (by decide)
private def law2ToFinite : Nat → Fin 2
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨1, by decide⟩
  | _ => ⟨0, by decide⟩

private def law2FromFinite (index : Fin 2) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
private theorem law2Valid :
    law2.SatisfiedBy oppositeTable.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    oppositeTable law2 law2ToFinite law2FromFinite
    (by decide) (by decide)
private def law3ToFinite : Nat → Fin 2
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨1, by decide⟩
  | _ => ⟨0, by decide⟩

private def law3FromFinite (index : Fin 2) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
private theorem law3Valid :
    law3.SatisfiedBy oppositeTable.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    oppositeTable law3 law3ToFinite law3FromFinite
    (by decide) (by decide)
private def law4ToFinite : Nat → Fin 3
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨1, by decide⟩
  | 2 => ⟨2, by decide⟩
  | _ => ⟨0, by decide⟩

private def law4FromFinite (index : Fin 3) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
private theorem law4Valid :
    law4.SatisfiedBy oppositeTable.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    oppositeTable law4 law4ToFinite law4FromFinite
    (by decide) (by decide)

theorem models : Models oppositeTable.semigroup basis := by
  unfold basis
  exact
    FiniteNilpotentCounterexample.models_cons law0Valid <|
      FiniteNilpotentCounterexample.models_cons law1Valid <|
        FiniteNilpotentCounterexample.models_cons law2Valid <|
          FiniteNilpotentCounterexample.models_cons law3Valid <|
            FiniteNilpotentCounterexample.models_cons law4Valid <|
              FiniteNilpotentCounterexample.models_nil oppositeTable.semigroup

end S6_2802

end SemigroupBasis.Generated.Order6GenericCASRootData
