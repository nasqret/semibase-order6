import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_6183ActionSemantics

/-! Unrestricted lower-state observations and local saturation of repeated
letters. These are list inductions over the actual four-state retract, not
bounded word searches or an assumed normal-form completeness field. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_6183

open SemigroupBasis
open S4_71Suffix

def ListTheory (left right : List Nat) : Prop :=
  ∀ valuation, listEval valuation left = listEval valuation right

theorem ListTheory.refl (word : List Nat) : ListTheory word word := fun _ => rfl

theorem ListTheory.symm {left right : List Nat} (same : ListTheory left right) : ListTheory right left :=
  fun valuation => (same valuation).symm

theorem ListTheory.trans {left middle right : List Nat}
    (first : ListTheory left middle) (second : ListTheory middle right) : ListTheory left right :=
  fun valuation => (first valuation).trans (second valuation)

theorem listEval_zero_mem (valuation : Nat → Fin 4) (word : List Nat) (selected : Nat)
    (value : valuation selected = 0) (member : selected ∈ word) : listEval valuation word = 0 := by
  obtain ⟨before, after, rfl⟩ := List.append_of_mem member
  simp only [listEval_append, listEval, value, lower_zero_left, lower_zero_right]

private theorem lower_nil_ideal (before after : Fin 4) :
    lowerMul before (lowerMul 1 after) = 0 ∨ lowerMul before (lowerMul 1 after) = 1 := by decide +revert

theorem listEval_nil_mem (valuation : Nat → Fin 4) (word : List Nat) (selected : Nat)
    (value : valuation selected = 1) (member : selected ∈ word) :
    listEval valuation word = 0 ∨ listEval valuation word = 1 := by
  obtain ⟨before, after, rfl⟩ := List.append_of_mem member
  rw [listEval_append, listEval, value]
  exact lower_nil_ideal (listEval valuation before) (listEval valuation after)

theorem listEval_nil_repeated (valuation : Nat → Fin 4) (word : List Nat) (selected : Nat)
    (value : valuation selected = 1) (repeated : 2 ≤ word.count selected) : listEval valuation word = 0 := by
  induction word with
  | nil => simp at repeated
  | cons first rest ih =>
      by_cases equal : first = selected
      · subst first
        have member : selected ∈ rest := List.count_pos_iff.mp (by
          rw [List.count_cons_self] at repeated
          omega)
        have nilRest := listEval_nil_mem valuation rest selected value member
        rw [listEval, value]
        rcases nilRest with zero | one
        · rw [zero]; rfl
        · rw [one]; rfl
      · have restRepeated : 2 ≤ rest.count selected := by
          simpa only [List.count_cons_of_ne equal] using repeated
        rw [listEval, ih restRepeated, lower_zero_right]

def nilProbe (selected letter : Nat) : Fin 4 := if letter = selected then 1 else 3

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

theorem ListTheory.count_zero {left right : List Nat} (same : ListTheory left right) (selected : Nat) :
    left.count selected = 0 ↔ right.count selected = 0 := by
  have observation := same (nilProbe selected)
  rw [listEval_nilProbe, listEval_nilProbe] at observation
  by_cases leftZero : left.count selected = 0 <;> by_cases rightZero : right.count selected = 0 <;>
    by_cases leftOne : left.count selected = 1 <;> by_cases rightOne : right.count selected = 1 <;>
    simp_all

theorem ListTheory.count_one {left right : List Nat} (same : ListTheory left right) (selected : Nat) :
    left.count selected = 1 ↔ right.count selected = 1 := by
  have observation := same (nilProbe selected)
  rw [listEval_nilProbe, listEval_nilProbe] at observation
  by_cases leftZero : left.count selected = 0 <;> by_cases rightZero : right.count selected = 0 <;>
    by_cases leftOne : left.count selected = 1 <;> by_cases rightOne : right.count selected = 1 <;>
    simp_all

theorem ListTheory.mem_iff {left right : List Nat} (same : ListTheory left right) (selected : Nat) :
    selected ∈ left ↔ selected ∈ right := by
  have zeros := same.count_zero selected
  constructor
  · intro member
    by_cases present : selected ∈ right
    · exact present
    · exact False.elim ((List.not_mem_of_count_eq_zero (zeros.mpr (List.count_eq_zero.mpr present))) member)
  · intro member
    by_cases present : selected ∈ left
    · exact present
    · exact False.elim ((List.not_mem_of_count_eq_zero (zeros.mp (List.count_eq_zero.mpr present))) member)

theorem ListTheory.repeated_iff {left right : List Nat} (same : ListTheory left right) (selected : Nat) :
    2 ≤ left.count selected ↔ 2 ≤ right.count selected := by
  have zero := same.count_zero selected
  have one := same.count_one selected
  omega

private theorem lower_duplicate_not_nil (first rest : Fin 4) (notNil : first ≠ 1) :
    lowerMul first rest = lowerMul first (lowerMul first rest) := by decide +revert

theorem listTheory_duplicate (before after : List Nat) (selected : Nat)
    (repeated : 2 ≤ (before ++ selected :: after).count selected) :
    ListTheory (before ++ selected :: after) (before ++ selected :: selected :: after) := by
  intro valuation
  by_cases nilValue : valuation selected = 1
  · have rightRepeated : 2 ≤ (before ++ selected :: selected :: after).count selected := by
      simp only [List.count_append, List.count_cons_self]
      omega
    rw [listEval_nil_repeated valuation _ selected nilValue repeated,
      listEval_nil_repeated valuation _ selected nilValue rightRepeated]
  · simp only [listEval_append, listEval]
    rw [← lower_duplicate_not_nil _ _ nilValue]

def doubleLetters : List Nat → List Nat
  | [] => []
  | first :: rest => first :: first :: doubleLetters rest

theorem count_doubleLetters (word : List Nat) (selected : Nat) :
    (doubleLetters word).count selected = 2 * word.count selected := by
  induction word with
  | nil => rfl
  | cons first rest ih =>
      by_cases equal : first = selected
      · subst first
        simp only [doubleLetters, List.count_cons_self, ih]
        omega
      · simp only [doubleLetters, List.count_cons_of_ne equal, ih]

theorem mem_doubleLetters (word : List Nat) (selected : Nat) :
    selected ∈ doubleLetters word ↔ selected ∈ word := by
  induction word with
  | nil => rfl
  | cons first rest ih => simp [doubleLetters, ih]

theorem doubleLetters_append (left right : List Nat) :
    doubleLetters (left ++ right) = doubleLetters left ++ doubleLetters right := by
  induction left with
  | nil => rfl
  | cons first rest ih => simp only [List.cons_append, doubleLetters, ih]

theorem listTheory_doubleSegment (before middle after : List Nat)
    (repeated : ∀ selected, selected ∈ middle → 2 ≤ (before ++ middle ++ after).count selected) :
    ListTheory (before ++ middle ++ after) (before ++ doubleLetters middle ++ after) := by
  induction middle generalizing before with
  | nil => exact ListTheory.refl _
  | cons first rest ih =>
      have firstRepeated : 2 ≤ (before ++ first :: (rest ++ after)).count first := by
        simpa only [List.append_assoc, List.cons_append] using repeated first (List.Mem.head rest)
      have duplicate := listTheory_duplicate before (rest ++ after) first firstRepeated
      have restRepeated : ∀ selected, selected ∈ rest →
          2 ≤ ((before ++ [first, first]) ++ rest ++ after).count selected := by
        intro selected member
        have original := repeated selected (List.Mem.tail first member)
        by_cases equal : first = selected
        · subst first
          simp only [List.count_append, List.count_cons_self, List.count_nil] at original ⊢
          omega
        · simp only [List.count_append, List.count_cons_of_ne equal, List.count_nil] at original ⊢
          omega
      have remaining := ih (before ++ [first, first]) restRepeated
      have result := duplicate.trans (by
        simpa only [doubleLetters, List.cons_append, List.nil_append, List.append_assoc] using remaining)
      simpa only [doubleLetters, List.append_assoc, List.cons_append] using result

theorem split_simple (word : List Nat) (selected : Nat) (simple : word.count selected = 1) :
    ∃ before after, word = before ++ selected :: after ∧ selected ∉ before ∧ selected ∉ after := by
  have member : selected ∈ word := List.count_pos_iff.mp (by omega)
  obtain ⟨before, after, shape⟩ := List.append_of_mem member
  refine ⟨before, after, shape, ?_, ?_⟩
  all_goals
    rw [shape, List.count_append, List.count_cons_self] at simple
    apply List.not_mem_of_count_eq_zero
    omega

def idemProbe (selected letter : Nat) : Fin 4 := if letter = selected then 2 else 3

theorem listEval_idemProbe (selected : Nat) (word : List Nat) :
    listEval (idemProbe selected) word = if selected ∈ word then 2 else 3 := by
  induction word with
  | nil => rfl
  | cons first rest ih =>
      simp only [listEval]
      by_cases equal : first = selected
      · subst first
        rw [show idemProbe selected selected = 2 from by simp [idemProbe], ih]
        by_cases member : selected ∈ rest <;> simp [member] <;> rfl
      · rw [show idemProbe selected first = 3 from by simp [idemProbe, equal], lower_unit_left, ih]
        simp [List.mem_cons, Ne.symm equal]

def cutProbe (simple marked letter : Nat) : Fin 4 :=
  if letter = simple then 1 else if letter = marked then 2 else 3

theorem cutProbe_absent (simple marked : Nat) (word : List Nat) (absent : simple ∉ word) :
    listEval (cutProbe simple marked) word = listEval (idemProbe marked) word := by
  apply listEval_congr_on
  intro letter member
  have different : letter ≠ simple := by
    intro equal
    subst letter
    exact absent member
  simp [cutProbe, idemProbe, different]

theorem listEval_simple_cut (before after : List Nat) (simple marked : Nat)
    (beforeAbsent : simple ∉ before) (afterAbsent : simple ∉ after) :
    listEval (cutProbe simple marked) (before ++ simple :: after) =
      if marked ∈ after then 0 else 1 := by
  rw [listEval_append, listEval,
    show cutProbe simple marked simple = 1 from by simp [cutProbe],
    cutProbe_absent simple marked before beforeAbsent,
    cutProbe_absent simple marked after afterAbsent,
    listEval_idemProbe, listEval_idemProbe]
  by_cases first : marked ∈ before <;> by_cases second : marked ∈ after <;>
    simp only [first, second, ite_true, ite_false] <;> rfl

theorem ListTheory.simple_suffix_support {before after otherBefore otherAfter : List Nat}
    {selected : Nat} (same : ListTheory (before ++ selected :: after) (otherBefore ++ selected :: otherAfter))
    (beforeAbsent : selected ∉ before) (afterAbsent : selected ∉ after)
    (otherBeforeAbsent : selected ∉ otherBefore) (otherAfterAbsent : selected ∉ otherAfter)
    (marked : Nat) : marked ∈ after ↔ marked ∈ otherAfter := by
  have observation := same (cutProbe selected marked)
  rw [listEval_simple_cut before after selected marked beforeAbsent afterAbsent,
    listEval_simple_cut otherBefore otherAfter selected marked otherBeforeAbsent otherAfterAbsent] at observation
  by_cases leftMember : marked ∈ after <;> by_cases rightMember : marked ∈ otherAfter <;> simp_all

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_6183
