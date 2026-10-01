import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_5595Presentation
import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S4_71SuffixReplay
import SemigroupBasis.Transfer

/-! The actual four-state left action and unrestricted terminal probes.
The auxiliary monoid is a proved retract, not an assumed factor pair. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_5595

open SemigroupBasis
open S4_71Suffix

def quotient (value : Fin 6) : Fin 4 :=
  if value = 5 then 3 else if value = 4 then 2 else if value = 2 ∨ value = 3 then 1 else 0

def embed (value : Fin 4) : Fin 6 :=
  if value = 3 then 5 else if value = 2 then 4 else if value = 1 then 2 else 0

def action (state : Fin 4) (value : Fin 6) : Fin 6 := mul (embed state) value

theorem quotient_embed (value : Fin 4) : quotient (embed value) = value := by decide +revert

theorem quotient_mul (left right : Fin 6) :
    quotient (mul left right) = lowerMul (quotient left) (quotient right) := by decide +revert

theorem embed_mul (left right : Fin 4) :
    embed (lowerMul left right) = mul (embed left) (embed right) := by decide +revert

theorem embed_injective : Function.Injective embed := by
  intro left right equal
  have projected := congrArg quotient equal
  simpa only [quotient_embed] using projected

def lowerEmbedding : Embedding lowerTable.semigroup table.semigroup where
  toFun := embed
  map_mul := embed_mul
  injective := embed_injective

theorem lower_valid_of_valid (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy lowerTable.semigroup :=
  lowerEmbedding.pullback_identity identity valid

theorem mul_eq_action (left right : Fin 6) : mul left right = action (quotient left) right := by decide +revert

theorem action_unit (value : Fin 6) : action 3 value = value := by decide +revert

theorem action_mul (left right : Fin 4) (value : Fin 6) :
    action (lowerMul left right) value = action left (action right value) := by decide +revert

theorem action_five (state : Fin 4) : action state 5 = embed state := by decide +revert

theorem action_five_injective : Function.Injective (fun state => action state 5) := by
  intro left right same
  apply embed_injective
  simpa only [action_five] using same

theorem action_three_nil_injective (left right : Fin 4)
    (leftNil : left = 0 ∨ left = 1) (rightNil : right = 0 ∨ right = 1)
    (same : action left 3 = action right 3) : left = right := by decide +revert

theorem eval_put (valuation : Nat → Fin 6) (front : List Nat) (suffix : Word Nat) :
    table.semigroup.eval valuation (put front suffix) =
      action (listEval (fun letter => quotient (valuation letter)) front)
        (table.semigroup.eval valuation suffix) := by
  induction front with
  | nil => exact (action_unit (table.semigroup.eval valuation suffix)).symm
  | cons first rest ih =>
      simp only [put, Semigroup.eval_append, Semigroup.eval_singleton, listEval]
      rw [ih]
      change mul (valuation first)
        (action (listEval (fun letter => quotient (valuation letter)) rest)
          (table.semigroup.eval valuation suffix)) = _
      rw [mul_eq_action, ← action_mul]

abbrev endWord (front : List Nat) (last : Nat) : Word Nat := put front (Word.singleton last)

theorem eval_endWord (valuation : Nat → Fin 6) (front : List Nat) (last : Nat) :
    table.semigroup.eval valuation (endWord front last) =
      action (listEval (fun letter => quotient (valuation letter)) front) (valuation last) := by
  simpa only [endWord, Semigroup.eval_singleton] using eval_put valuation front (Word.singleton last)

private theorem split_last (first : Nat) (tail : List Nat) :
    ∃ front last, first :: tail = front ++ [last] := by
  induction tail generalizing first with
  | nil => exact ⟨[], first, rfl⟩
  | cons next rest ih =>
      obtain ⟨front, last, shape⟩ := ih next
      exact ⟨first :: front, last, by simp [shape]⟩

theorem existsEndWord (word : Word Nat) : ∃ front last, word = endWord front last := by
  obtain ⟨front, last, shape⟩ := split_last word.head word.tail
  refine ⟨front, last, ?_⟩
  apply Word.toList_injective
  rw [put_toList]
  exact shape

def nilProbe (selected : Nat) (letter : Nat) : Fin 4 := if letter = selected then 1 else 3

theorem listEval_nilProbe (selected : Nat) (word : List Nat) :
    listEval (nilProbe selected) word =
      if word.count selected = 0 then 3 else if word.count selected = 1 then 1 else 0 := by
  induction word with
  | nil => rfl
  | cons first rest ih =>
      by_cases equal : first = selected
      · subst first
        simp only [listEval, nilProbe, List.count_cons_self]
        rw [ih]
        cases countValue : rest.count selected with
        | zero => rfl
        | succ remainder =>
            cases remainder with
            | zero => rfl
            | succ remainder => rfl
      · simp only [listEval, nilProbe, if_neg equal, lower_unit_left, List.count_cons_of_ne equal]
        exact ih

def terminalProbe (selected : Nat) (letter : Nat) : Fin 6 := if letter = selected then 3 else 5

theorem terminalProbe_eval (front : List Nat) (last selected : Nat) :
    table.semigroup.eval (terminalProbe selected) (endWord front last) =
      if last = selected then
        if front.count selected = 0 then (3 : Fin 6) else if front.count selected = 1 then (1 : Fin 6) else (0 : Fin 6)
      else
        if front.count selected = 0 then (5 : Fin 6) else if front.count selected = 1 then (2 : Fin 6) else (0 : Fin 6) := by
  rw [eval_endWord]
  have projection : (fun letter => quotient (terminalProbe selected letter)) = nilProbe selected := by
    funext letter
    by_cases equal : letter = selected <;> simp [terminalProbe, nilProbe, equal, quotient]
  rw [projection, listEval_nilProbe]
  by_cases equal : last = selected
  · subst last
    simp only [terminalProbe]
    cases countValue : front.count selected with
    | zero => rfl
    | succ remainder =>
        cases remainder with
        | zero => rfl
        | succ remainder => rfl
  · simp only [terminalProbe, if_neg equal]
    cases countValue : front.count selected with
    | zero => rfl
    | succ remainder =>
        cases remainder with
        | zero => rfl
        | succ remainder => rfl

theorem terminalProbe_eq_three_iff (front : List Nat) (last selected : Nat) :
    table.semigroup.eval (terminalProbe selected) (endWord front last) = (3 : Fin 6) ↔
      last = selected ∧ front.count selected = 0 := by
  rw [terminalProbe_eval]
  by_cases equal : last = selected <;>
    by_cases zero : front.count selected = 0 <;>
    by_cases one : front.count selected = 1 <;>
    simp_all

theorem terminalProbe_eq_one_iff (front : List Nat) (last selected : Nat) :
    table.semigroup.eval (terminalProbe selected) (endWord front last) = (1 : Fin 6) ↔
      last = selected ∧ front.count selected = 1 := by
  rw [terminalProbe_eval]
  by_cases equal : last = selected <;>
    by_cases zero : front.count selected = 0 <;>
    by_cases one : front.count selected = 1 <;>
    simp_all

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_5595
