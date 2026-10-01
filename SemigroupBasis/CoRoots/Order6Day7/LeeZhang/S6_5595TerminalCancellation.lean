import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_5595ActionSemantics

/-! Cancel an actual simple or double terminal into the proved lower theory.
The double case uses two finite-state observations and arbitrary-list induction. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_5595

open SemigroupBasis
open S4_71Suffix

def EndEquivalent (left : List Nat) (leftLast : Nat) (right : List Nat) (rightLast : Nat) : Prop :=
  ∀ valuation, table.semigroup.eval valuation (endWord left leftLast) =
    table.semigroup.eval valuation (endWord right rightLast)

theorem EndEquivalent.symm {left right : List Nat} {leftLast rightLast : Nat}
    (same : EndEquivalent left leftLast right rightLast) : EndEquivalent right rightLast left leftLast :=
  fun valuation => (same valuation).symm

theorem simple_terminal_preserved (left right : List Nat) (leftLast rightLast : Nat)
    (same : EndEquivalent left leftLast right rightLast) (simple : left.count leftLast = 0) :
    rightLast = leftLast ∧ right.count leftLast = 0 := by
  have leftThree := (terminalProbe_eq_three_iff left leftLast leftLast).mpr ⟨rfl, simple⟩
  have rightThree := (same (terminalProbe leftLast)).symm.trans leftThree
  exact (terminalProbe_eq_three_iff right rightLast leftLast).mp rightThree

theorem double_terminal_preserved (left right : List Nat) (leftLast rightLast : Nat)
    (same : EndEquivalent left leftLast right rightLast) (double : left.count leftLast = 1) :
    rightLast = leftLast ∧ right.count leftLast = 1 := by
  have leftOne := (terminalProbe_eq_one_iff left leftLast leftLast).mpr ⟨rfl, double⟩
  have rightOne := (same (terminalProbe leftLast)).symm.trans leftOne
  exact (terminalProbe_eq_one_iff right rightLast leftLast).mp rightOne

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

/-- A chosen lift of the terminal lets actual validity compare any realizable lower valuation. -/
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
    (leftCount : left.count selected = 0) (rightCount : right.count selected = 0)
    (valuation : Nat → Fin 4) : listEval valuation left = listEval valuation right := by
  have observation := probe_action_equality left right selected same (override valuation selected 3) 5 (by simp [override, quotient])
  have equal := action_five_injective observation
  simpa only [listEval_override_absent valuation selected 3 left (List.not_mem_of_count_eq_zero leftCount),
    listEval_override_absent valuation selected 3 right (List.not_mem_of_count_eq_zero rightCount)] using equal

private theorem lower_nil_ideal (before after : Fin 4) :
    lowerMul before (lowerMul 1 after) = 0 ∨ lowerMul before (lowerMul 1 after) = 1 := by decide +revert

theorem listEval_nil_mem (valuation : Nat → Fin 4) (word : List Nat) (selected : Nat)
    (value : valuation selected = 1) (member : selected ∈ word) :
    listEval valuation word = 0 ∨ listEval valuation word = 1 := by
  obtain ⟨before, after, rfl⟩ := List.append_of_mem member
  rw [listEval_append, listEval, value]
  exact lower_nil_ideal (listEval valuation before) (listEval valuation after)

theorem listEval_zero_mem (valuation : Nat → Fin 4) (word : List Nat) (selected : Nat)
    (value : valuation selected = 0) (member : selected ∈ word) : listEval valuation word = 0 := by
  obtain ⟨before, after, rfl⟩ := List.append_of_mem member
  simp only [listEval_append, listEval, value, lower_zero_left, lower_zero_right]

def flip (value : Fin 4) : Fin 4 :=
  if value = 0 then 0 else if value = 1 then 2 else 3

def WeakFlip (original flipped : Fin 4) : Prop := original = 0 ∨ flipped = flip original

private theorem weakFlip_mul (left right leftFlip rightFlip : Fin 4)
    (leftRelated : WeakFlip left leftFlip) (rightRelated : WeakFlip right rightFlip) :
    WeakFlip (lowerMul left right) (lowerMul leftFlip rightFlip) := by
  unfold WeakFlip at *
  decide +revert

theorem listEval_weakFlip (valuation : Nat → Fin 4) (word : List Nat) :
    WeakFlip (listEval valuation word) (listEval (fun letter => flip (valuation letter)) word) := by
  induction word with
  | nil => exact Or.inr rfl
  | cons first rest ih =>
      exact weakFlip_mul (valuation first) (listEval valuation rest) (flip (valuation first))
        (listEval (fun letter => flip (valuation letter)) rest) (Or.inr rfl) ih

def recoverAtIdempotent (erased flipped : Fin 4) : Fin 4 :=
  if erased = 0 then 0 else if erased = 1 then (if flipped = 0 then 1 else 0) else 2

private theorem recoverAtIdempotent_correct (before after beforeFlip afterFlip : Fin 4)
    (beforeRelated : WeakFlip before beforeFlip) (afterRelated : WeakFlip after afterFlip) :
    lowerMul before (lowerMul 2 after) =
      recoverAtIdempotent (lowerMul before after) (lowerMul beforeFlip (lowerMul 1 afterFlip)) := by
  unfold WeakFlip at *
  decide +revert

/-- Two observations recover a prefix containing exactly one selected idempotent. -/
theorem listEval_recover_idempotent (valuation : Nat → Fin 4) (word : List Nat) (selected : Nat)
    (value : valuation selected = 2) (countOne : word.count selected = 1) :
    listEval valuation word = recoverAtIdempotent
      (listEval (override valuation selected 3) word)
      (listEval (override (fun letter => flip (valuation letter)) selected 1) word) := by
  have member : selected ∈ word := List.count_pos_iff.mp (by omega)
  obtain ⟨before, after, rfl⟩ := List.append_of_mem member
  have counts : before.count selected + (after.count selected + 1) = 1 := by
    simpa only [List.count_append, List.count_cons_self] using countOne
  have beforeAbsent : selected ∉ before := List.not_mem_of_count_eq_zero (by omega)
  have afterAbsent : selected ∉ after := List.not_mem_of_count_eq_zero (by omega)
  simp only [listEval_append, listEval, value, override_selected, lower_unit_left]
  rw [listEval_override_absent valuation selected 3 before beforeAbsent,
    listEval_override_absent valuation selected 3 after afterAbsent,
    listEval_override_absent (fun letter => flip (valuation letter)) selected 1 before beforeAbsent,
    listEval_override_absent (fun letter => flip (valuation letter)) selected 1 after afterAbsent]
  exact recoverAtIdempotent_correct
    (listEval valuation before) (listEval valuation after)
    (listEval (fun letter => flip (valuation letter)) before)
    (listEval (fun letter => flip (valuation letter)) after)
    (listEval_weakFlip valuation before) (listEval_weakFlip valuation after)

theorem double_prefix_lower_equivalent (left right : List Nat) (selected : Nat)
    (same : EndEquivalent left selected right selected)
    (leftCount : left.count selected = 1) (rightCount : right.count selected = 1)
    (valuation : Nat → Fin 4) : listEval valuation left = listEval valuation right := by
  have leftMember : selected ∈ left := List.count_pos_iff.mp (by omega)
  have rightMember : selected ∈ right := List.count_pos_iff.mp (by omega)
  have possibilities : valuation selected = 0 ∨ valuation selected = 1 ∨ valuation selected = 2 ∨ valuation selected = 3 :=
    (by decide : ∀ value : Fin 4, value = 0 ∨ value = 1 ∨ value = 2 ∨ value = 3) (valuation selected)
  rcases possibilities with zero | one | two | three
  · rw [listEval_zero_mem valuation left selected zero leftMember,
      listEval_zero_mem valuation right selected zero rightMember]
  · have observation := probe_action_equality left right selected same valuation 3 (by simpa [quotient] using one.symm)
    exact action_three_nil_injective _ _
      (listEval_nil_mem valuation left selected one leftMember)
      (listEval_nil_mem valuation right selected one rightMember) observation
  · have erasedObservation := probe_action_equality left right selected same (override valuation selected 3) 5 (by simp [override, quotient])
    have erasedEqual := action_five_injective erasedObservation
    let flipped := override (fun letter => flip (valuation letter)) selected 1
    have flippedSelected : flipped selected = 1 := override_selected _ _ _
    have flippedObservation := probe_action_equality left right selected same flipped 3 (by simpa [quotient] using flippedSelected.symm)
    have flippedEqual := action_three_nil_injective _ _
      (listEval_nil_mem flipped left selected flippedSelected leftMember)
      (listEval_nil_mem flipped right selected flippedSelected rightMember) flippedObservation
    rw [listEval_recover_idempotent valuation left selected two leftCount,
      listEval_recover_idempotent valuation right selected two rightCount,
      erasedEqual]
    exact congrArg (recoverAtIdempotent (listEval (override valuation selected 3) right)) flippedEqual
  · have observation := probe_action_equality left right selected same valuation 5 (by simpa [quotient] using three.symm)
    exact action_five_injective observation

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_5595
