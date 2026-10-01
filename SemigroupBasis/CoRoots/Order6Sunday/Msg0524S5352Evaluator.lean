import SemigroupBasis.FiniteTable
import Std.Tactic

/-! Arbitrary-word evaluator for the literal S5352 table. The cost is
additive and saturates at three; the final value selects the marker bit.
Uses S3's recorded terminal-marker shape, not its old finite-key window. -/
namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0524S5352Evaluator

open SemigroupBasis

private def row (v0 v1 v2 v3 v4 v5 : Fin 6) (b : Fin 6) : Fin 6 :=
  if b = 0 then v0 else if b = 1 then v1 else if b = 2 then v2
  else if b = 3 then v3 else if b = 4 then v4 else v5

def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then row 0 0 0 0 0 0 b
  else if a = 1 then row 0 0 0 0 0 1 b
  else if a = 2 then row 0 0 0 0 0 1 b
  else if a = 3 then row 0 0 0 1 2 3 b
  else if a = 4 then row 0 0 0 1 2 3 b
  else row 0 1 2 3 4 5 b

theorem associative : ∀ a b c : Fin 6, mul (mul a b) c = mul a (mul b c) := by decide

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := associative

def weight (value : Fin 6) : Nat := 3 - (value.val + 1) / 2

def marker (value : Fin 6) : Bool := value == 2 || value == 4

def code (amount : Nat) (marked : Bool) : Fin 6 :=
  if amount = 0 then 5
  else if amount = 1 then if marked then 4 else 3
  else if amount = 2 then if marked then 2 else 1
  else 0

def cost (valuation : α → Fin 6) : List α → Nat
  | [] => 0
  | a :: rest => weight (valuation a) + cost valuation rest

def lastWith : List α → α → α
  | [], fallback => fallback
  | a :: rest, _ => lastWith rest a

def last (word : Word α) : α := lastWith word.tail word.head

def lastMarker (valuation : α → Fin 6) : List α → Bool → Bool
  | [], fallback => fallback
  | a :: rest, _ => lastMarker valuation rest (marker (valuation a))

theorem weight_bound : ∀ value : Fin 6, weight value ≤ 3 := by decide

theorem weight_mul : ∀ a b : Fin 6,
    weight (mul a b) = min (weight a + weight b) 3 := by decide

theorem marker_mul : ∀ a b : Fin 6,
    marker (mul a b) = (marker b && decide (weight a + weight b < 3)) := by decide

theorem code_recovery : ∀ value : Fin 6, code (weight value) (marker value) = value := by decide

theorem code_cap (amount : Nat) (marked : Bool) : code (min amount 3) marked = code amount marked := by
  by_cases h0 : amount = 0
  · simp [h0]
  by_cases h1 : amount = 1
  · simp [h1]
  by_cases h2 : amount = 2
  · simp [h2]
  have high : min amount 3 = 3 := by omega
  simp [code, h0, h1, h2, high]

private theorem mul_code_small : ∀ n : Fin 4, ∀ mark : Bool, ∀ value : Fin 6,
    mul (code n.val mark) value = code (n.val + weight value) (marker value) := by decide

theorem mul_code (amount : Nat) (marked : Bool) (value : Fin 6) :
    mul (code amount marked) value = code (amount + weight value) (marker value) := by
  have finite := mul_code_small ⟨min amount 3, by omega⟩ marked value
  change mul (code (min amount 3) marked) value =
    code (min amount 3 + weight value) (marker value) at finite
  rw [code_cap] at finite
  calc
    mul (code amount marked) value = code (min amount 3 + weight value) (marker value) := finite
    _ = code (amount + weight value) (marker value) := by
      rw [← code_cap (min amount 3 + weight value) (marker value),
        ← code_cap (amount + weight value) (marker value)]
      congr 1
      omega

private theorem weight_code_small : ∀ n : Fin 4, ∀ marked : Bool,
    weight (code n.val marked) = n.val := by decide

theorem weight_code (amount : Nat) (marked : Bool) :
    weight (code amount marked) = min amount 3 := by
  have finite := weight_code_small ⟨min amount 3, by omega⟩ marked
  change weight (code (min amount 3) marked) = min amount 3 at finite
  simpa only [code_cap] using finite

theorem code_high (amount : Nat) (marked : Bool) (high : 3 ≤ amount) : code amount marked = 0 := by
  simp [code, show amount ≠ 0 by omega, show amount ≠ 1 by omega, show amount ≠ 2 by omega]

theorem code_tag_injective (amount : Nat) (positive : 0 < amount) (small : amount < 3)
    (a b : Bool) (equal : code amount a = code amount b) : a = b := by
  have cases : amount = 1 ∨ amount = 2 := by omega
  rcases cases with h | h <;> subst amount <;> cases a <;> cases b <;> simp_all [code]

theorem lastWith_mem (letters : List α) (fallback : α) :
    lastWith letters fallback ∈ fallback :: letters := by
  induction letters generalizing fallback with
  | nil => simp [lastWith]
  | cons a rest ih =>
      exact List.mem_cons_of_mem fallback (ih a)

theorem last_mem (word : Word α) : last word ∈ word.toList := lastWith_mem word.tail word.head

theorem lastMarker_eq (valuation : α → Fin 6) (letters : List α) (fallback : α) :
    lastMarker valuation letters (marker (valuation fallback)) =
      marker (valuation (lastWith letters fallback)) := by
  induction letters generalizing fallback with
  | nil => rfl
  | cons a rest ih => exact ih a

theorem fold_code (valuation : α → Fin 6) (letters : List α) (amount : Nat) (marked : Bool) :
    letters.foldl (fun state a => mul state (valuation a)) (code amount marked) =
      code (amount + cost valuation letters) (lastMarker valuation letters marked) := by
  induction letters generalizing amount marked with
  | nil => simp [cost, lastMarker]
  | cons a rest ih =>
      rw [List.foldl_cons, mul_code, ih]
      simp only [cost, lastMarker, Nat.add_assoc]

theorem eval_formula (valuation : α → Fin 6) (word : Word α) :
    table.semigroup.eval valuation word = code (cost valuation word.toList) (marker (valuation (last word))) := by
  have folded := fold_code valuation word.tail (weight (valuation word.head)) (marker (valuation word.head))
  rw [code_recovery, lastMarker_eq] at folded
  exact folded

theorem eval_weight (valuation : α → Fin 6) (word : Word α) :
    weight (table.semigroup.eval valuation word) = min (cost valuation word.toList) 3 := by
  rw [eval_formula, weight_code]

end SemigroupBasis.CoRoots.Order6Sunday.Msg0524S5352Evaluator
