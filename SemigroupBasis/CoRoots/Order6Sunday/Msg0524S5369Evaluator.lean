import SemigroupBasis.FiniteTable
import Std.Tactic

/-! Exact arbitrary-word evaluator for the literal S5369 table.
The nilpotent chain is weighted by 5-value; value5 is a left-zero marker
and annihilates a non-marker prefix on the right. No basis or reach premise. -/
namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0524S5369Evaluator

open SemigroupBasis

private def row (v0 v1 v2 v3 v4 v5 : Fin 6) (b : Fin 6) : Fin 6 :=
  if b = 0 then v0 else if b = 1 then v1 else if b = 2 then v2
  else if b = 3 then v3 else if b = 4 then v4 else v5

def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then row 0 0 0 0 0 0 b
  else if a = 1 then row 0 0 0 0 0 0 b
  else if a = 2 then row 0 0 0 0 1 0 b
  else if a = 3 then row 0 0 0 1 2 0 b
  else if a = 4 then row 0 0 1 2 3 0 b
  else row 5 5 5 5 5 5 b

theorem associative : ∀ a b c : Fin 6, mul (mul a b) c = mul a (mul b c) := by
  decide

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := associative

def weight (value : Fin 6) : Nat := 5 - value.val

def nilValue (amount : Nat) : Fin 6 := ⟨5 - amount, by omega⟩

def cost (valuation : α → Fin 6) : List α → Nat
  | [] => 0
  | a :: rest => weight (valuation a) + cost valuation rest

theorem nilValue_weight (value : Fin 6) : nilValue (weight value) = value := by
  apply Fin.ext
  have bound := value.isLt
  simp only [nilValue, weight]
  omega

theorem mul_five : ∀ b : Fin 6, mul 5 b = 5 := by decide
theorem mul_zero : ∀ b : Fin 6, mul 0 b = 0 := by decide
theorem mul_right_five : ∀ a : Fin 6, a ≠ 5 → mul a 5 = 0 := by decide
theorem mul_not_five : ∀ a b : Fin 6, a ≠ 5 → mul a b ≠ 5 := by decide

theorem mul_low_value : ∀ a b : Fin 6, a ≠ 5 → b ≠ 5 →
    (mul a b).val = 5 - ((5 - a.val) + (5 - b.val)) := by decide

theorem weight_positive (value : Fin 6) (low : value ≠ 5) : 0 < weight value := by
  have bound := value.isLt
  have notValue : value.val ≠ 5 := by
    intro h
    apply low
    exact Fin.ext h
  simp only [weight]
  omega

theorem nilValue_not_five (amount : Nat) (positive : 0 < amount) :
    nilValue amount ≠ 5 := by
  intro h
  have hv := congrArg Fin.val h
  simp only [nilValue] at hv
  omega

theorem mul_nilValue (amount : Nat) (positive : 0 < amount)
    (value : Fin 6) (low : value ≠ 5) :
    mul (nilValue amount) value = nilValue (amount + weight value) := by
  apply Fin.ext
  rw [mul_low_value _ _ (nilValue_not_five amount positive) low]
  simp only [nilValue, weight]
  omega

theorem fold_five (valuation : α → Fin 6) (letters : List α) :
    letters.foldl (fun state a => mul state (valuation a)) 5 = 5 := by
  induction letters with
  | nil => rfl
  | cons a rest ih => simpa only [List.foldl_cons, mul_five] using ih

theorem fold_zero (valuation : α → Fin 6) (letters : List α) :
    letters.foldl (fun state a => mul state (valuation a)) 0 = 0 := by
  induction letters with
  | nil => rfl
  | cons a rest ih => simpa only [List.foldl_cons, mul_zero] using ih

theorem fold_not_five (valuation : α → Fin 6) (letters : List α)
    (initial : Fin 6) (low : initial ≠ 5) :
    letters.foldl (fun state a => mul state (valuation a)) initial ≠ 5 := by
  induction letters generalizing initial with
  | nil => exact low
  | cons a rest ih =>
      exact ih (mul initial (valuation a)) (mul_not_five _ _ low)

theorem fold_zero_of_marker (valuation : α → Fin 6) (letters : List α)
    (initial : Fin 6) (low : initial ≠ 5)
    (marker : ∃ a ∈ letters, valuation a = 5) :
    letters.foldl (fun state a => mul state (valuation a)) initial = 0 := by
  induction letters generalizing initial with
  | nil => simp at marker
  | cons a rest ih =>
      by_cases here : valuation a = 5
      · rw [List.foldl_cons, here, mul_right_five initial low, fold_zero]
      · have later : ∃ b ∈ rest, valuation b = 5 := by
          rcases marker with ⟨b, member, marked⟩
          rcases List.mem_cons.mp member with same | tailMember
          · subst b
            exact False.elim (here marked)
          · exact ⟨b, tailMember, marked⟩
        exact ih (mul initial (valuation a)) (mul_not_five _ _ low) later

theorem fold_low (valuation : α → Fin 6) (letters : List α)
    (amount : Nat) (positive : 0 < amount)
    (low : ∀ a ∈ letters, valuation a ≠ 5) :
    letters.foldl (fun state a => mul state (valuation a)) (nilValue amount) =
      nilValue (amount + cost valuation letters) := by
  induction letters generalizing amount with
  | nil => simp [cost]
  | cons a rest ih =>
      have tailLow : ∀ b ∈ rest, valuation b ≠ 5 :=
        fun b member => low b (List.mem_cons_of_mem a member)
      rw [List.foldl_cons, mul_nilValue amount positive _ (low a (by simp))]
      rw [ih (amount + weight (valuation a)) (by omega) tailLow]
      simp only [cost, Nat.add_assoc]

theorem eval_of_no_marker (valuation : α → Fin 6) (word : Word α)
    (low : ∀ a ∈ word.toList, valuation a ≠ 5) :
    table.semigroup.eval valuation word = nilValue (cost valuation word.toList) := by
  have headLow := low word.head (by simp [Word.toList])
  have tailLow : ∀ a ∈ word.tail, valuation a ≠ 5 :=
    fun a member => low a (by simp [Word.toList, member])
  have folded := fold_low valuation word.tail (weight (valuation word.head))
    (weight_positive _ headLow) tailLow
  rw [nilValue_weight] at folded
  exact folded

theorem eval_five_iff (valuation : α → Fin 6) (word : Word α) :
    table.semigroup.eval valuation word = (5 : Fin 6) ↔ valuation word.head = 5 := by
  change word.tail.foldl (fun state a => mul state (valuation a)) (valuation word.head) = 5 ↔ _
  by_cases head : valuation word.head = 5
  · simp only [head, fold_five]
  · have no := fold_not_five valuation word.tail (valuation word.head) head
    exact ⟨fun h => False.elim (no h), fun h => False.elim (head h)⟩

def formula (valuation : α → Fin 6) (word : Word α) : Fin 6 :=
  if valuation word.head = 5 then 5
  else if word.tail.any (fun a => valuation a == 5) then 0
  else nilValue (cost valuation word.toList)

theorem eval_formula (valuation : α → Fin 6) (word : Word α) :
    table.semigroup.eval valuation word = formula valuation word := by
  by_cases head : valuation word.head = 5
  · simp only [formula, head, if_true]
    exact (eval_five_iff valuation word).mpr head
  · by_cases found : word.tail.any (fun a => valuation a == 5) = true
    · simp only [formula, if_neg head, found, if_true]
      have marker : ∃ a ∈ word.tail, valuation a = 5 := by
        simpa only [beq_iff_eq] using List.any_eq_true.mp found
      exact fold_zero_of_marker valuation word.tail (valuation word.head) head marker
    · simp only [formula, if_neg head, if_neg found]
      apply eval_of_no_marker
      intro a member
      rcases List.mem_cons.mp member with same | tailMember
      · subst a
        exact head
      · intro marked
        apply found
        exact List.any_eq_true.mpr ⟨a, tailMember, by simp [marked]⟩

end SemigroupBasis.CoRoots.Order6Sunday.Msg0524S5369Evaluator
