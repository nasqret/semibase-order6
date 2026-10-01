import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_6183Derivations
import SemigroupBasis.Transfer

/-! The literal six-state action, its proved four-state retract, and terminal
observations for arbitrary nonempty words. No factor pair or completeness
assumption is introduced. In particular the four-lift, unlike the two-lift,
separates every lower state. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_6183

open SemigroupBasis
open S4_71Suffix

def quotient (value : Fin 6) : Fin 4 :=
  if value = 5 then 3 else if value = 3 ∨ value = 4 then 2 else if value = 2 then 1 else 0

def embed (value : Fin 4) : Fin 6 :=
  if value = 3 then 5 else if value = 2 then 3 else if value = 1 then 2 else 0

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

theorem action_four_injective : Function.Injective (fun state => action state 4) :=
  (by decide : ∀ left right : Fin 4, action left 4 = action right 4 → left = right)

theorem action_two_nil_constant (state : Fin 4) (nilState : state = 0 ∨ state = 1) :
    action state 2 = 0 := by decide +revert

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

def EndEquivalent (left : List Nat) (leftLast : Nat) (right : List Nat) (rightLast : Nat) : Prop :=
  ∀ valuation, table.semigroup.eval valuation (endWord left leftLast) =
    table.semigroup.eval valuation (endWord right rightLast)

theorem EndEquivalent.symm {left right : List Nat} {leftLast rightLast : Nat}
    (same : EndEquivalent left leftLast right rightLast) : EndEquivalent right rightLast left leftLast :=
  fun valuation => (same valuation).symm

theorem EndEquivalent.lower {left right : List Nat} {leftLast rightLast : Nat}
    (same : EndEquivalent left leftLast right rightLast) (valuation : Nat → Fin 4) :
    listEval valuation (left ++ [leftLast]) = listEval valuation (right ++ [rightLast]) := by
  have valid : (Identity.mk (endWord left leftLast) (endWord right rightLast)).SatisfiedBy
      table.semigroup := same
  have lower := lower_valid_of_valid _ valid valuation
  simpa only [← listEval_toList, put_toList, Word.toList_singleton] using lower

def override (valuation : Nat → Fin 4) (selected : Nat) (value : Fin 4) (letter : Nat) : Fin 4 :=
  if letter = selected then value else valuation letter

theorem override_selected (valuation : Nat → Fin 4) (selected : Nat) (value : Fin 4) :
    override valuation selected value selected = value := by simp [override]

theorem listEval_override_absent (valuation : Nat → Fin 4) (selected : Nat) (value : Fin 4)
    (word : List Nat) (absent : selected ∉ word) :
    listEval (override valuation selected value) word = listEval valuation word := by
  apply listEval_congr_on
  intro letter member
  have different : letter ≠ selected := by
    intro equal
    subst letter
    exact absent member
  simp [override, different]

theorem probe_action_equality (left right : List Nat) (selected : Nat)
    (same : EndEquivalent left selected right selected)
    (valuation : Nat → Fin 4) (value : Fin 6) (projects : quotient value = valuation selected) :
    action (listEval valuation left) value = action (listEval valuation right) value := by
  let lifted : Nat → Fin 6 := fun letter => if letter = selected then value else embed (valuation letter)
  have projection : (fun letter => quotient (lifted letter)) = valuation := by
    funext letter
    by_cases equal : letter = selected
    · subst letter
      simpa only [lifted] using projects
    · simp only [lifted, if_neg equal, quotient_embed]
  have result := same lifted
  rw [eval_endWord, eval_endWord, projection] at result
  simpa only [lifted] using result

theorem simple_prefix_lower_equivalent (left right : List Nat) (selected : Nat)
    (same : EndEquivalent left selected right selected)
    (leftAbsent : selected ∉ left) (rightAbsent : selected ∉ right)
    (valuation : Nat → Fin 4) : listEval valuation left = listEval valuation right := by
  have observation := probe_action_equality left right selected same (override valuation selected 3) 5
    (by simp [override, quotient])
  have equal := action_five_injective observation
  simpa only [listEval_override_absent valuation selected 3 left leftAbsent,
    listEval_override_absent valuation selected 3 right rightAbsent] using equal

def terminalProbe (selected letter : Nat) : Fin 6 := if letter = selected then 1 else 5

private theorem unitZeroProbe (selected : Nat) (word : List Nat) :
    listEval (fun letter => quotient (terminalProbe selected letter)) word =
      if selected ∈ word then 0 else 3 := by
  induction word with
  | nil => rfl
  | cons first rest ih =>
      by_cases equal : first = selected
      · subst first
        simp only [listEval]
        have head : quotient (terminalProbe selected selected) = 0 := by simp [terminalProbe, quotient]
        rw [head]
        rw [lower_zero_left]
        simp
      · simp only [listEval]
        have head : quotient (terminalProbe selected first) = 3 := by simp [terminalProbe, equal, quotient]
        rw [head, lower_unit_left, ih]
        simp [List.mem_cons, Ne.symm equal]

theorem terminalProbe_eval (front : List Nat) (last selected : Nat) :
    table.semigroup.eval (terminalProbe selected) (endWord front last) =
      if selected ∈ front then (0 : Fin 6) else if last = selected then (1 : Fin 6) else (5 : Fin 6) := by
  rw [eval_endWord, unitZeroProbe]
  by_cases member : selected ∈ front
  · simp only [if_pos member]
    simp [action, embed, mul]
  · simp only [if_neg member, action_unit]
    rfl

theorem terminalProbe_eq_one_iff (front : List Nat) (last selected : Nat) :
    table.semigroup.eval (terminalProbe selected) (endWord front last) = (1 : Fin 6) ↔
      last = selected ∧ selected ∉ front := by
  rw [terminalProbe_eval]
  by_cases member : selected ∈ front <;> by_cases equal : last = selected <;> simp_all

theorem simple_terminal_preserved (left right : List Nat) (leftLast rightLast : Nat)
    (same : EndEquivalent left leftLast right rightLast) (simple : leftLast ∉ left) :
    rightLast = leftLast ∧ leftLast ∉ right := by
  have leftOne := (terminalProbe_eq_one_iff left leftLast leftLast).mpr ⟨rfl, simple⟩
  have rightOne := (same (terminalProbe leftLast)).symm.trans leftOne
  exact (terminalProbe_eq_one_iff right rightLast leftLast).mp rightOne

theorem simple_terminal_complete (left right : List Nat) (leftLast rightLast : Nat)
    (same : EndEquivalent left leftLast right rightLast) (simple : leftLast ∉ left) :
    Derives basis (endWord left leftLast) (endWord right rightLast) := by
  obtain ⟨equal, rightSimple⟩ := simple_terminal_preserved left right leftLast rightLast same simple
  subst rightLast
  exact prefix_lower_replay left right (Word.singleton leftLast)
    (simple_prefix_lower_equivalent left right leftLast same simple rightSimple)

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_6183
