import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_2708Sigma12WordNormal
import SemigroupBasis.Examples.CommutativeExponentThree
import SemigroupBasis.Transfer

/-! Actual-table probes separate the terminal normal forms. The capped-count
information is pulled back along the explicit {0,3,5} subsemigroup. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_2708.Sigma12

open SemigroupBasis
open S4_71Suffix (put)

def capEmbed (value : Fin 3) : Fin 6 := if value = 0 then 0 else if value = 1 then 3 else 5

theorem capEmbed_mul (left right : Fin 3) :
    capEmbed (Examples.commutativeExponentThreeMul left right) = mul (capEmbed left) (capEmbed right) := by
  decide +revert

theorem capEmbed_injective : Function.Injective capEmbed := by
  unfold Function.Injective
  decide

def capEmbedding : Embedding Examples.commutativeExponentThree.semigroup table.semigroup where
  toFun := capEmbed
  map_mul := capEmbed_mul
  injective := capEmbed_injective

def Equivalent (left right : Word Nat) : Prop :=
  ∀ valuation, table.semigroup.eval valuation left = table.semigroup.eval valuation right

theorem Equivalent.symm {left right : Word Nat} (same : Equivalent left right) : Equivalent right left :=
  fun valuation => (same valuation).symm

theorem caps_of_equivalent (left right : Word Nat) (same : Equivalent left right) :
    SameCaps left.toList right.toList :=
  Examples.exponentValid_capped_count_eq ⟨left, right⟩ (capEmbedding.pullback_identity ⟨left, right⟩ same)

theorem singleton_of_caps (word : Word Nat) (letter : Nat)
    (same : SameCaps [letter] word.toList) : word = Word.singleton letter := by
  have permutation : word.toList.Perm [letter] := by
    rw [List.perm_iff_count]
    intro tested
    have counts := same tested
    have bound : ([letter] : List Nat).count tested ≤ 1 := List.count_le_length
    omega
  apply Word.toList_injective
  simpa only [List.perm_singleton, Word.toList_singleton] using permutation

def prefixEval (valuation : Nat → Fin 6) : List Nat → Fin 6 → Fin 6
  | [], value => value
  | letter :: rest, value => mul (valuation letter) (prefixEval valuation rest value)

theorem eval_put (valuation : Nat → Fin 6) (front : List Nat) (suffix : Word Nat) :
    table.semigroup.eval valuation (put front suffix) = prefixEval valuation front (table.semigroup.eval valuation suffix) := by
  induction front with
  | nil => rfl
  | cons letter rest ih =>
      simp only [put, Semigroup.eval_append, Semigroup.eval_singleton, prefixEval, ih]
      rfl

theorem prefixEval_zero (valuation : Nat → Fin 6) (front : List Nat) : prefixEval valuation front 0 = 0 := by
  induction front with
  | nil => rfl
  | cons letter rest ih =>
      rw [prefixEval, ih]
      exact (by decide : ∀ value : Fin 6, mul value 0 = 0) (valuation letter)

def falling (count : Nat) : Fin 6 := if count = 0 then 4 else if count = 1 then 1 else 0
def drifting (count : Nat) : Fin 6 := if count = 0 then 5 else if count = 1 then 3 else 0

theorem mul_four_falling (count : Nat) : mul 4 (falling count) = falling (count + 1) := by
  cases count with
  | zero => rfl
  | succ rest => cases rest <;> rfl

theorem mul_two_falling (count : Nat) : mul 2 (falling count) = falling (count + 1) := by
  cases count with
  | zero => rfl
  | succ rest => cases rest <;> rfl

theorem mul_five_falling (count : Nat) : mul 5 (falling count) = falling count := by
  cases count with
  | zero => rfl
  | succ rest => cases rest <;> rfl

theorem mul_four_drifting (count : Nat) : mul 4 (drifting count) = drifting (count + 1) := by
  cases count with
  | zero => rfl
  | succ rest => cases rest <;> rfl

theorem mul_five_drifting (count : Nat) : mul 5 (drifting count) = drifting count := by
  cases count with
  | zero => rfl
  | succ rest => cases rest <;> rfl

theorem falling_eq_four_iff (count : Nat) : falling count = 4 ↔ count = 0 := by
  cases count with
  | zero => decide
  | succ rest => cases rest <;> simp [falling]

theorem falling_eq_one_iff (count : Nat) : falling count = 1 ↔ count = 1 := by
  cases count with
  | zero => decide
  | succ rest => cases rest <;> simp [falling]

theorem drifting_ne_four (count : Nat) : drifting count ≠ 4 := by
  cases count with
  | zero => decide
  | succ rest => cases rest <;> simp [drifting]

theorem drifting_ne_one (count : Nat) : drifting count ≠ 1 := by
  cases count with
  | zero => decide
  | succ rest => cases rest <;> simp [drifting]

def probe4 (selected letter : Nat) : Fin 6 := if letter = selected then 4 else 5

theorem probe4_prefix_four (selected : Nat) (front : List Nat) :
    prefixEval (probe4 selected) front 4 = falling (front.count selected) := by
  induction front with
  | nil => rfl
  | cons letter rest ih =>
      by_cases equal : letter = selected
      · subst letter
        simp only [prefixEval, probe4, List.count_cons_self, ih]
        exact mul_four_falling _
      · simp only [prefixEval, probe4, if_neg equal, List.count_cons_of_ne equal, ih]
        exact mul_five_falling _

theorem probe4_prefix_five (selected : Nat) (front : List Nat) :
    prefixEval (probe4 selected) front 5 = drifting (front.count selected) := by
  induction front with
  | nil => rfl
  | cons letter rest ih =>
      by_cases equal : letter = selected
      · subst letter
        simp only [prefixEval, probe4, List.count_cons_self, ih]
        exact mul_four_drifting _
      · simp only [prefixEval, probe4, if_neg equal, List.count_cons_of_ne equal, ih]
        exact mul_five_drifting _

theorem end_probe4 (front : List Nat) (last selected : Nat) :
    table.semigroup.eval (probe4 selected) (put front (Word.singleton last)) =
      if last = selected then falling (front.count selected) else drifting (front.count selected) := by
  rw [eval_put, Semigroup.eval_singleton]
  by_cases equal : last = selected
  · subst last
    simp only [probe4]
    exact probe4_prefix_four _ _
  · simp only [probe4, if_neg equal]
    exact probe4_prefix_five _ _

theorem end_probe4_eq_four_iff (front : List Nat) (last selected : Nat) :
    table.semigroup.eval (probe4 selected) (put front (Word.singleton last)) = (4 : Fin 6) ↔
      last = selected ∧ (front ++ [last]).count selected = 1 := by
  rw [end_probe4]
  by_cases equal : last = selected
  · subst last
    rw [if_pos rfl, falling_eq_four_iff]
    simp only [true_and, List.count_append, List.count_cons_self, List.count_nil]
    omega
  · rw [if_neg equal]
    constructor
    · intro impossible; exact False.elim (drifting_ne_four _ impossible)
    · intro impossible; exact False.elim (equal impossible.1)

theorem end_probe4_eq_one_iff (front : List Nat) (last selected : Nat) :
    table.semigroup.eval (probe4 selected) (put front (Word.singleton last)) = (1 : Fin 6) ↔
      last = selected ∧ (front ++ [last]).count selected = 2 := by
  rw [end_probe4]
  by_cases equal : last = selected
  · subst last
    rw [if_pos rfl, falling_eq_one_iff]
    simp only [true_and, List.count_append, List.count_cons_self, List.count_nil]
    omega
  · rw [if_neg equal]
    constructor
    · intro impossible; exact False.elim (drifting_ne_one _ impossible)
    · intro impossible; exact False.elim (equal impossible.1)

theorem framed_as_end (front : List Nat) (penultimate last : Nat) :
    framed front penultimate last = put (front ++ [penultimate]) (Word.singleton last) := by
  rw [S4_71Suffix.put_append]
  rfl

theorem frame_probe4_eq_four_iff (front : List Nat) (penultimate last selected : Nat) :
    table.semigroup.eval (probe4 selected) (framed front penultimate last) = (4 : Fin 6) ↔
      last = selected ∧ (front ++ [penultimate, last]).count selected = 1 := by
  rw [framed_as_end]
  simpa only [List.append_assoc, List.cons_append, List.nil_append] using
    end_probe4_eq_four_iff (front ++ [penultimate]) last selected

theorem frame_probe4_eq_one_iff (front : List Nat) (penultimate last selected : Nat) :
    table.semigroup.eval (probe4 selected) (framed front penultimate last) = (1 : Fin 6) ↔
      last = selected ∧ (front ++ [penultimate, last]).count selected = 2 := by
  rw [framed_as_end]
  simpa only [List.append_assoc, List.cons_append, List.nil_append] using
    end_probe4_eq_one_iff (front ++ [penultimate]) last selected

def marked2 (marked : Nat → Bool) (letter : Nat) : Fin 6 := if marked letter then 2 else 5

theorem marked2_prefix_four (marked : Nat → Bool) (front : List Nat) :
    prefixEval (marked2 marked) front 4 = falling (front.countP marked) := by
  induction front with
  | nil => rfl
  | cons letter rest ih =>
      simp only [prefixEval, marked2, List.countP_cons]
      rw [ih]
      cases equation : marked letter with
      | false => simpa only [Bool.false_eq_true, if_false, Nat.add_zero] using mul_five_falling (rest.countP marked)
      | true => simpa only [if_true] using mul_two_falling (rest.countP marked)

theorem countP_single (word : List Nat) (selected : Nat) :
    word.countP (fun letter => decide (letter = selected)) = word.count selected := by
  simp only [← Bool.beq_eq_decide_eq, ← List.count_eq_countP]

theorem countP_pair (word : List Nat) (first second : Nat) (different : first ≠ second) :
    word.countP (fun letter => decide (letter = first ∨ letter = second)) = word.count first + word.count second := by
  induction word with
  | nil => rfl
  | cons letter rest ih =>
      by_cases isFirst : letter = first
      · subst letter
        simp only [List.countP_cons, true_or, decide_true, if_true,
          List.count_cons_self, List.count_cons_of_ne different, ih]
        omega
      · by_cases isSecond : letter = second
        · subst letter
          simp only [List.countP_cons, or_true, decide_true, if_true,
            List.count_cons_self, List.count_cons_of_ne (Ne.symm different), ih]
          omega
        · simp only [List.countP_cons, isFirst, isSecond, false_or, decide_false,
            Bool.false_eq_true, if_false, List.count_cons_of_ne isFirst,
            List.count_cons_of_ne isSecond, ih, Nat.add_zero]

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_2708.Sigma12
