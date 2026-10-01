import SemigroupBasis.CoRoots.Order6Sunday.Msg0524S5352Observations
import SemigroupBasis.CoRoots.Order6Sunday.Msg0524S5369SemanticKey

/-! Exact S5352 arbitrary-word semantic criterion. Reuses ONLY the generic
capped predicate-count aggregation from S5369, not its semantic theorem.
No reach premise, finite-word bound, external basis, or completeness input. -/
namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0524S5352SemanticKey

open SemigroupBasis
open Msg0524S5352Evaluator Msg0524S5352Observations
open Msg0524S5369SemanticKey (countP_cap_eq)

def extra (valuation : α → Fin 6) (threshold : Nat) (letters : List α) : Nat :=
  letters.countP (fun a => decide ((valuation a).val < threshold))

theorem weight_decomposition : ∀ v : Fin 6,
    weight v = (if v.val < 5 then 1 else 0) +
      (if v.val < 3 then 1 else 0) + (if v.val < 1 then 1 else 0) := by decide

theorem cost_decomposition (valuation : α → Fin 6) (letters : List α) :
    cost valuation letters = extra valuation 5 letters +
      extra valuation 3 letters + extra valuation 1 letters := by
  induction letters with
  | nil => rfl
  | cons a rest ih =>
      rw [cost, ih, weight_decomposition]
      simp only [extra, List.countP_cons, decide_eq_true_eq]
      omega

theorem cost_cap_eq (valuation : Nat → Fin 6) (left right : List Nat)
    (same : ∀ x, min (left.count x) 3 = min (right.count x) 3) :
    min (cost valuation left) 3 = min (cost valuation right) 3 := by
  have h5 := countP_cap_eq 3 left right (fun a => decide ((valuation a).val < 5)) same
  have h3 := countP_cap_eq 3 left right (fun a => decide ((valuation a).val < 3)) same
  have h1 := countP_cap_eq 3 left right (fun a => decide ((valuation a).val < 1)) same
  rw [cost_decomposition valuation left, cost_decomposition valuation right]
  simp only [extra]
  omega

theorem weight_positive : ∀ value : Fin 6, value ≠ 5 → 0 < weight value := by decide

theorem cost_ge_count_of_nonunit (valuation : Nat → Fin 6) (letters : List Nat)
    (x : Nat) (nonunit : valuation x ≠ 5) : letters.count x ≤ cost valuation letters := by
  have positive := weight_positive (valuation x) nonunit
  induction letters with
  | nil => simp [cost]
  | cons a rest ih =>
      by_cases same : a = x
      · subst a
        have total : rest.count x + 1 ≤ weight (valuation x) + cost valuation rest := by omega
        simpa [cost] using total
      · have total : rest.count x ≤ weight (valuation a) + cost valuation rest := by omega
        simpa [cost, same] using total

theorem eval_saturated_terminal (valuation : Nat → Fin 6) (word : Word Nat)
    (saturated : 3 ≤ word.toList.count (last word)) :
    table.semigroup.eval valuation word = code (cost valuation word.toList) false := by
  rw [eval_formula]
  by_cases unit : valuation (last word) = 5
  · simp [unit, marker]
  · have countBound := cost_ge_count_of_nonunit valuation word.toList (last word) unit
    have high : 3 ≤ cost valuation word.toList := by omega
    exact (code_high _ _ high).trans (code_high _ false high).symm

theorem valid_of_key (left right : Word Nat) (key : SameKey left right) :
    (Identity.mk left right).SatisfiedBy table.semigroup := by
  change ∀ valuation : Nat → Fin 6,
    table.semigroup.eval valuation left = table.semigroup.eval valuation right
  rcases key with ⟨counts, tags⟩
  intro valuation
  have amounts := cost_cap_eq valuation left.toList right.toList counts
  by_cases lowLeft : left.toList.count (last left) < 3
  · have lowRight : right.toList.count (last right) < 3 := by
      by_cases low : right.toList.count (last right) < 3
      · exact low
      · simp [terminalTag, lowLeft, low] at tags
    have ends : last left = last right := by
      simpa only [terminalTag, if_pos lowLeft, if_pos lowRight, Option.some.injEq] using tags
    rw [eval_formula, eval_formula, ends,
      ← code_cap (cost valuation left.toList) (marker (valuation (last right))),
      ← code_cap (cost valuation right.toList) (marker (valuation (last right))), amounts]
  · have notLowRight : ¬ right.toList.count (last right) < 3 := by
      intro lowRight
      simp [terminalTag, lowLeft, lowRight] at tags
    rw [eval_saturated_terminal valuation left (by omega),
      eval_saturated_terminal valuation right (by omega),
      ← code_cap (cost valuation left.toList) false,
      ← code_cap (cost valuation right.toList) false, amounts]

theorem semantic_key_iff (left right : Word Nat) :
    (Identity.mk left right).SatisfiedBy table.semigroup ↔ SameKey left right :=
  ⟨key_of_valid left right, valid_of_key left right⟩

end SemigroupBasis.CoRoots.Order6Sunday.Msg0524S5352SemanticKey
