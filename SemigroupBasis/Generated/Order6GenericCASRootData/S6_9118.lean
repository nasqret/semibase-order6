import SemigroupBasis.FiniteNilpotentCounterexample

namespace SemigroupBasis.Generated.Order6GenericCASRootData

open SemigroupBasis

namespace S6_9118

/-- Exact one-based order-six catalogue table: `[[1,2,2,1,1,1],[2,1,1,2,2,2],[2,1,1,3,3,3],[1,2,3,4,5,6],[1,2,3,5,6,4],[1,2,3,6,4,5]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (1 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (1 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (5 : Fin 6) else (3 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (3 : Fin 6) else (4 : Fin 6)

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
  "0d8e52ad399a4a699bc0ee7020fe22d5fcdd8e589680124fa0470a3d3ab14c54"

def law0 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩
def law1 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0, 0, 0, 0, 0]⟩⟩

/-- The displayed generic-CAS root basis in packet order. -/
def basis : List (Identity Nat) :=
  [law0, law1]

def basisSHA256 : String :=
  "0f9efa5c27138209a286b345e4b233fb8650b7ccdca84c6665441380959715f1"

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

theorem models : Models oppositeTable.semigroup basis := by
  unfold basis
  exact
    FiniteNilpotentCounterexample.models_cons law0Valid <|
      FiniteNilpotentCounterexample.models_cons law1Valid <|
        FiniteNilpotentCounterexample.models_nil oppositeTable.semigroup

end S6_9118

end SemigroupBasis.Generated.Order6GenericCASRootData
