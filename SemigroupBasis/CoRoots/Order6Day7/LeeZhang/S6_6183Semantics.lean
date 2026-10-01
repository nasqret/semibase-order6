import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_6183LowerProfiles

/-! Observable terminal cuts and cancellation at an actual adjacent simple
anchor. The difficult nil-state case is recovered by a second six-state
valuation, not assumed from the non-injective two-lift. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_6183

open SemigroupBasis
open S4_71Suffix

theorem listEval_cutProbe_eq_one_iff (word : List Nat) (simple marked : Nat) :
    listEval (cutProbe simple marked) word = (1 : Fin 4) ↔
      ∃ before after, word = before ++ simple :: after ∧
        simple ∉ before ∧ simple ∉ after ∧ marked ∉ after := by
  constructor
  · intro one
    have countOne : word.count simple = 1 := by
      by_cases countOne : word.count simple = 1
      · exact countOne
      · by_cases zero : word.count simple = 0
        · rw [cutProbe_absent simple marked word (List.not_mem_of_count_eq_zero zero),
            listEval_idemProbe] at one
          by_cases member : marked ∈ word
          · rw [if_pos member] at one
            cases one
          · rw [if_neg member] at one
            cases one
        · have repeated : 2 ≤ word.count simple := by omega
          have value : cutProbe simple marked simple = 1 := by simp [cutProbe]
          rw [listEval_nil_repeated _ word simple value repeated] at one
          cases one
    obtain ⟨before, after, shape, beforeAbsent, afterAbsent⟩ := split_simple word simple countOne
    refine ⟨before, after, shape, beforeAbsent, afterAbsent, ?_⟩
    rw [shape, listEval_simple_cut before after simple marked beforeAbsent afterAbsent] at one
    intro member
    rw [if_pos member] at one
    cases one
  · rintro ⟨before, after, rfl, beforeAbsent, afterAbsent, markedAbsent⟩
    rw [listEval_simple_cut before after simple marked beforeAbsent afterAbsent, if_neg markedAbsent]

def activeProbe (marked simple letter : Nat) : Fin 6 :=
  if letter = simple then 2 else if letter = marked then 4 else 5

theorem activeProbe_projection (marked simple letter : Nat) :
    quotient (activeProbe marked simple letter) = cutProbe simple marked letter := by
  unfold activeProbe cutProbe
  by_cases first : letter = simple
  · simp only [if_pos first]
    rfl
  · simp only [if_neg first]
    by_cases second : letter = marked
    · simp only [if_pos second]
      rfl
    · simp only [if_neg second]
      rfl

private theorem activeProbe_action_one (state : Fin 4) (marked simple last : Nat)
    (different : simple ≠ marked) :
    action state (activeProbe marked simple last) = 1 ↔ last = marked ∧ state = 1 := by
  by_cases first : last = simple
  · have probe : activeProbe marked simple last = 2 := by simp only [activeProbe, if_pos first]
    rw [probe]
    have notMarked : last ≠ marked := fun equal => different (first.symm.trans equal)
    have impossible := (by decide : ∀ state : Fin 4, ¬action state 2 = 1) state
    constructor
    · intro one
      exact False.elim (impossible one)
    · rintro ⟨equal, _⟩
      exact False.elim (notMarked equal)
  · by_cases second : last = marked
    · have probe : activeProbe marked simple last = 4 := by simp only [activeProbe, if_neg first, if_pos second]
      rw [probe]
      have observation := (by decide : ∀ state : Fin 4, action state 4 = 1 ↔ state = 1) state
      constructor
      · intro one
        exact ⟨second, observation.mp one⟩
      · intro same
        exact observation.mpr same.2
    · have probe : activeProbe marked simple last = 5 := by simp only [activeProbe, if_neg first, if_neg second]
      rw [probe]
      have impossible := (by decide : ∀ state : Fin 4, ¬action state 5 = 1) state
      constructor
      · intro one
        exact False.elim (impossible one)
      · rintro ⟨equal, _⟩
        exact False.elim (second equal)

def ActiveCut (front : List Nat) (marked simple : Nat) : Prop :=
  simple ≠ marked ∧ ∃ before after, front = before ++ simple :: after ∧
    simple ∉ before ∧ simple ∉ after ∧ marked ∉ after

theorem activeProbe_eq_one_iff (front : List Nat) (last marked simple : Nat)
    (different : simple ≠ marked) :
    table.semigroup.eval (activeProbe marked simple) (endWord front last) = (1 : Fin 6) ↔
      last = marked ∧ ActiveCut front marked simple := by
  rw [eval_endWord]
  have projection : (fun letter => quotient (activeProbe marked simple letter)) = cutProbe simple marked := by
    funext letter
    exact activeProbe_projection marked simple letter
  rw [projection, activeProbe_action_one _ marked simple last different,
    listEval_cutProbe_eq_one_iff]
  constructor
  · intro observed
    exact ⟨observed.1, different, observed.2⟩
  · intro observed
    exact ⟨observed.1, observed.2.2⟩

theorem active_terminal_preserved (left right : List Nat) (leftLast rightLast simple : Nat)
    (same : EndEquivalent left leftLast right rightLast) (active : ActiveCut left leftLast simple) :
    rightLast = leftLast ∧ ActiveCut right leftLast simple := by
  have leftOne := (activeProbe_eq_one_iff left leftLast leftLast simple active.1).mpr ⟨rfl, active⟩
  have rightOne := (same (activeProbe leftLast simple)).symm.trans leftOne
  exact (activeProbe_eq_one_iff right rightLast leftLast simple active.1).mp rightOne

def clip (value : Fin 4) : Fin 4 := if value = 1 then 0 else value

theorem clip_mul (left right : Fin 4) :
    clip (lowerMul left right) = lowerMul (clip left) (clip right) := by decide +revert

theorem listEval_clip (valuation : Nat → Fin 4) (word : List Nat) :
    listEval (fun letter => clip (valuation letter)) word = clip (listEval valuation word) := by
  induction word with
  | nil => rfl
  | cons first rest ih =>
      rw [listEval, listEval, ih, ← clip_mul]

def anchorProbe (valuation : Nat → Fin 4) (marked simple letter : Nat) : Fin 6 :=
  if letter = marked then 4 else if letter = simple then 2 else embed (clip (valuation letter))

theorem listEval_anchor_absent (valuation : Nat → Fin 4) (marked simple : Nat) (word : List Nat)
    (markedAbsent : marked ∉ word) (simpleAbsent : simple ∉ word) :
    listEval (fun letter => quotient (anchorProbe valuation marked simple letter)) word =
      clip (listEval valuation word) := by
  rw [← listEval_clip]
  apply listEval_congr_on
  intro letter member
  have notMarked : letter ≠ marked := by
    intro equal
    subst letter
    exact markedAbsent member
  have notSimple : letter ≠ simple := by
    intro equal
    subst letter
    exact simpleAbsent member
  simp only [anchorProbe, if_neg notMarked, if_neg notSimple, quotient_embed]

def nilRead (value : Fin 4) : Fin 6 := if value = 1 then 1 else 0

private theorem anchor_recovery (before after : Fin 4) :
    action (lowerMul (clip before) (lowerMul 2 (lowerMul 1 (clip after)))) 4 =
      nilRead (lowerMul before (lowerMul 1 after)) := by decide +revert

theorem anchorProbe_eval (valuation : Nat → Fin 4) (marked simple : Nat) (before after : List Nat)
    (different : simple ≠ marked)
    (beforeMarked : marked ∉ before) (afterMarked : marked ∉ after)
    (beforeSimple : simple ∉ before) (afterSimple : simple ∉ after)
    (markedValue : valuation marked = 1) (simpleValue : valuation simple = 3) :
    table.semigroup.eval (anchorProbe valuation marked simple)
        (endWord (before ++ marked :: simple :: after) marked) =
      nilRead (listEval valuation (before ++ marked :: simple :: after)) := by
  rw [eval_endWord, listEval_append, listEval, listEval]
  have markedProjection : quotient (anchorProbe valuation marked simple marked) = 2 := by
    simp [anchorProbe, quotient]
  have simpleProjection : quotient (anchorProbe valuation marked simple simple) = 1 := by
    simp [anchorProbe, different, quotient]
  have finalValue : anchorProbe valuation marked simple marked = 4 := by simp [anchorProbe]
  rw [markedProjection, simpleProjection, finalValue,
    listEval_anchor_absent valuation marked simple before beforeMarked beforeSimple,
    listEval_anchor_absent valuation marked simple after afterMarked afterSimple,
    listEval_append, listEval, listEval, markedValue, simpleValue, lower_unit_left]
  exact anchor_recovery (listEval valuation before) (listEval valuation after)

private theorem nilRead_injective (left right : Fin 4)
    (leftNil : left = 0 ∨ left = 1) (rightNil : right = 0 ∨ right = 1)
    (same : nilRead left = nilRead right) : left = right := by decide +revert

private theorem lower_nil_before_nonunit (before middle after : Fin 4) (nonunit : middle ≠ 3) :
    lowerMul before (lowerMul 1 (lowerMul middle after)) = 0 := by decide +revert

theorem anchored_prefix_lower_equivalent
    (leftBefore leftAfter rightBefore rightAfter : List Nat) (marked simple : Nat)
    (same : EndEquivalent (leftBefore ++ marked :: simple :: leftAfter) marked
      (rightBefore ++ marked :: simple :: rightAfter) marked)
    (different : simple ≠ marked)
    (leftMarked : marked ∉ leftBefore ∧ marked ∉ leftAfter)
    (rightMarked : marked ∉ rightBefore ∧ marked ∉ rightAfter)
    (leftSimple : simple ∉ leftBefore ∧ simple ∉ leftAfter)
    (rightSimple : simple ∉ rightBefore ∧ simple ∉ rightAfter) :
    ListTheory (leftBefore ++ marked :: simple :: leftAfter)
      (rightBefore ++ marked :: simple :: rightAfter) := by
  intro valuation
  have leftMember : marked ∈ leftBefore ++ marked :: simple :: leftAfter := by simp
  have rightMember : marked ∈ rightBefore ++ marked :: simple :: rightAfter := by simp
  have casesValue : valuation marked = 0 ∨ valuation marked = 1 ∨ valuation marked = 2 ∨ valuation marked = 3 :=
    (by decide : ∀ value : Fin 4, value = 0 ∨ value = 1 ∨ value = 2 ∨ value = 3) (valuation marked)
  rcases casesValue with zero | one | two | three
  · rw [listEval_zero_mem valuation _ marked zero leftMember,
      listEval_zero_mem valuation _ marked zero rightMember]
  · by_cases simpleUnit : valuation simple = 3
    · have observation := same (anchorProbe valuation marked simple)
      rw [anchorProbe_eval valuation marked simple leftBefore leftAfter different leftMarked.1 leftMarked.2
        leftSimple.1 leftSimple.2 one simpleUnit,
        anchorProbe_eval valuation marked simple rightBefore rightAfter different rightMarked.1 rightMarked.2
        rightSimple.1 rightSimple.2 one simpleUnit] at observation
      exact nilRead_injective _ _
        (listEval_nil_mem valuation _ marked one leftMember)
        (listEval_nil_mem valuation _ marked one rightMember) observation
    · simp only [listEval_append, listEval, one]
      rw [lower_nil_before_nonunit _ _ _ simpleUnit, lower_nil_before_nonunit _ _ _ simpleUnit]
  · have observation := probe_action_equality _ _ marked same valuation 4 (by simpa [quotient] using two.symm)
    exact action_four_injective observation
  · have observation := probe_action_equality _ _ marked same valuation 5 (by simpa [quotient] using three.symm)
    exact action_five_injective observation

theorem anchored_terminal_complete
    (leftBefore leftAfter rightBefore rightAfter : List Nat) (marked simple : Nat)
    (same : EndEquivalent (leftBefore ++ marked :: simple :: leftAfter) marked
      (rightBefore ++ marked :: simple :: rightAfter) marked)
    (different : simple ≠ marked)
    (leftMarked : marked ∉ leftBefore ∧ marked ∉ leftAfter)
    (rightMarked : marked ∉ rightBefore ∧ marked ∉ rightAfter)
    (leftSimple : simple ∉ leftBefore ∧ simple ∉ leftAfter)
    (rightSimple : simple ∉ rightBefore ∧ simple ∉ rightAfter) :
    Derives basis (endWord (leftBefore ++ marked :: simple :: leftAfter) marked)
      (endWord (rightBefore ++ marked :: simple :: rightAfter) marked) :=
  prefix_lower_replay _ _ (Word.singleton marked)
    (anchored_prefix_lower_equivalent leftBefore leftAfter rightBefore rightAfter marked simple
      same different leftMarked rightMarked leftSimple rightSimple)

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_6183
