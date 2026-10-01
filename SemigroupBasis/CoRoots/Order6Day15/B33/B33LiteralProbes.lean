import SemigroupBasis.CoRoots.Order6Day15.B33.B33Tables
import SemigroupBasis.CoRoots.Order6Day15.B33.B33Probes

namespace SemigroupBasis.CoRoots.Order6Day15.B33

def order6225 : Option Bool → Fin 6
  | none => 3
  | some false => 0
  | some true => 5

def parity6225 : Bool → Fin 6
  | false => 3
  | true => 4

def order9878 : Option Bool → Fin 6
  | none => 2
  | some false => 0
  | some true => 4

def parity9878 : Bool → Fin 6
  | false => 2
  | true => 3

private theorem optionBool_cases (a : Option Bool) :
    a = none ∨ a = some false ∨ a = some true := by
  cases a with
  | none => exact Or.inl rfl
  | some b => cases b <;> simp

def probes6225 : Probes table6225.semigroup where
  order := order6225
  order_injective := by
    intro a b
    rcases optionBool_cases a with rfl | rfl | rfl
    all_goals rcases optionBool_cases b with rfl | rfl | rfl
    all_goals decide
  order_mul := by
    intro a b
    rcases optionBool_cases a with rfl | rfl | rfl
    all_goals rcases optionBool_cases b with rfl | rfl | rfl
    all_goals decide
  parity := parity6225
  parity_injective := by intro a b; cases a <;> cases b <;> decide
  parity_mul := by decide
  same_unit := rfl
  head := (2 : Fin 6)
  dead := (0 : Fin 6)
  head_ne_dead := by decide
  head_square := rfl
  dead_head := rfl
  head_unit := rfl
  dead_unit := rfl
  tail := (1 : Fin 6)
  tail_ne_zero := by decide
  unit_tail := rfl
  tail_square := rfl
  zero_tail := rfl

def probes9878 : Probes table9878.semigroup where
  order := order9878
  order_injective := by
    intro a b
    rcases optionBool_cases a with rfl | rfl | rfl
    all_goals rcases optionBool_cases b with rfl | rfl | rfl
    all_goals decide
  order_mul := by
    intro a b
    rcases optionBool_cases a with rfl | rfl | rfl
    all_goals rcases optionBool_cases b with rfl | rfl | rfl
    all_goals decide
  parity := parity9878
  parity_injective := by intro a b; cases a <;> cases b <;> decide
  parity_mul := by decide
  same_unit := rfl
  head := (5 : Fin 6)
  dead := (4 : Fin 6)
  head_ne_dead := by decide
  head_square := rfl
  dead_head := rfl
  head_unit := rfl
  dead_unit := rfl
  tail := (1 : Fin 6)
  tail_ne_zero := by decide
  unit_tail := rfl
  tail_square := rfl
  zero_tail := rfl

end SemigroupBasis.CoRoots.Order6Day15.B33
