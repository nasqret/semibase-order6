import SemigroupBasis.CoRoots.Order6SporadicSection18ActualEvaluation

/-! The actual C7 table detects adjacent simple letters on arbitrary words.
No length bound, alphabet bound or assumed global identity is used. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection18.Actual
open SemigroupBasis

def pairVal (x y letter : Nat) : Fin 6 :=
  if letter = x then 3 else if letter = y then 2 else 5

theorem pairVal_left (x y : Nat) : pairVal x y x = 3 := by
  unfold pairVal
  exact if_pos rfl

theorem pairVal_right (x y : Nat) (different : x ≠ y) : pairVal x y y = 2 := by
  unfold pairVal
  calc
    (if y = x then (3 : Fin 6) else if y = y then 2 else 5) =
        (if y = y then (2 : Fin 6) else 5) := if_neg (Ne.symm different)
    _ = 2 := if_pos rfl

theorem pairVal_other (x y letter : Nat) (left : letter ≠ x) (right : letter ≠ y) :
    pairVal x y letter = 5 := by
  simp only [pairVal, if_neg left, if_neg right]

private theorem mul13 : tableMul 1 3 = 0 := by decide
private theorem mul12 : tableMul 1 2 = 0 := by decide
private theorem mul15 : tableMul 1 5 = 1 := by decide
private theorem mul33 : tableMul 3 3 = 0 := by decide
private theorem mul32 : tableMul 3 2 = 1 := by decide
private theorem mul35 : tableMul 3 5 = 0 := by decide
private theorem mul53 : tableMul 5 3 = 3 := by decide
private theorem mul52 : tableMul 5 2 = 0 := by decide
private theorem mul55 : tableMul 5 5 = 5 := by decide
private theorem zero_ne_one : (0 : Fin 6) ≠ 1 := by decide
private theorem three_ne_one : (3 : Fin 6) ≠ 1 := by decide
private theorem five_ne_one : (5 : Fin 6) ≠ 1 := by decide

def PairClear (x y : Nat) (letters : List Nat) : Prop := x ∉ letters ∧ y ∉ letters

theorem pairClear_cons (x y letter : Nat) (letters : List Nat) :
    PairClear x y (letter :: letters) ↔ letter ≠ x ∧ letter ≠ y ∧ PairClear x y letters := by
  simp [PairClear, List.mem_cons, not_or, ne_comm, and_assoc, and_left_comm]

def AdjacentOnce (x y : Nat) (letters : List Nat) : Prop :=
  ∃ before after, letters = before ++ x :: y :: after ∧ PairClear x y before ∧ PairClear x y after

theorem not_adjacentOnce_nil (x y : Nat) : ¬ AdjacentOnce x y [] := by
  rintro ⟨before, after, equal, _, _⟩
  have lengths := congrArg List.length equal
  simp only [List.length_nil, List.length_append, List.length_cons] at lengths
  omega

theorem adjacentOnce_cons (x y letter : Nat) (letters : List Nat) :
    AdjacentOnce x y (letter :: letters) ↔
      (letter = x ∧ ∃ after, letters = y :: after ∧ PairClear x y after) ∨
      (letter ≠ x ∧ letter ≠ y ∧ AdjacentOnce x y letters) := by
  constructor
  · rintro ⟨before, after, equal, prefixClear, suffixClear⟩
    cases before with
    | nil =>
        have boundary : letter :: letters = x :: y :: after := equal
        exact Or.inl ⟨(List.cons.inj boundary).1, after, (List.cons.inj boundary).2, suffixClear⟩
    | cons head tail =>
        have boundary : letter :: letters = head :: (tail ++ x :: y :: after) := equal
        rcases List.cons.inj boundary with ⟨heads, tails⟩
        subst head
        have clear := (pairClear_cons x y letter tail).mp prefixClear
        exact Or.inr ⟨clear.1, clear.2.1, tail, after, tails, clear.2.2, suffixClear⟩
  · intro found
    rcases found with ⟨head, after, tail, clear⟩ | ⟨left, right, before, after, tail, prefixClear, suffixClear⟩
    · subst letter
      subst letters
      exact ⟨[], after, rfl, by simp [PairClear], clear⟩
    · refine ⟨letter :: before, after, ?_, (pairClear_cons x y letter before).mpr ⟨left, right, prefixClear⟩, suffixClear⟩
      change letter :: letters = letter :: (before ++ x :: y :: after)
      exact congrArg (List.cons letter) tail

theorem pairVal_run_one_iff (x y : Nat) (letters : List Nat) :
    run (pairVal x y) 1 letters = 1 ↔ PairClear x y letters := by
  induction letters with
  | nil => simp [PairClear, run_nil]
  | cons letter letters ih =>
      by_cases left : letter = x
      · subst letter
        rw [run_cons, pairVal_left, mul13, run_zero]
        constructor
        · intro impossible
          exact False.elim (zero_ne_one impossible)
        · intro clear
          exact False.elim (clear.1 (by simp))
      · by_cases right : letter = y
        · subst letter
          rw [run_cons, pairVal_right x y (Ne.symm left), mul12, run_zero]
          constructor
          · intro impossible
            exact False.elim (zero_ne_one impossible)
          · intro clear
            exact False.elim (clear.2 (by simp))
        · rw [run_cons, pairVal_other x y letter left right, mul15, ih, pairClear_cons]
          simp [left, right]

theorem pairVal_run_three_iff (x y : Nat) (different : x ≠ y) (letters : List Nat) :
    run (pairVal x y) 3 letters = 1 ↔
      ∃ after, letters = y :: after ∧ PairClear x y after := by
  cases letters with
  | nil =>
      rw [run_nil]
      constructor
      · intro impossible
        exact False.elim (three_ne_one impossible)
      · rintro ⟨after, impossible, _⟩
        cases impossible
  | cons letter letters =>
      by_cases right : letter = y
      · subst letter
        rw [run_cons, pairVal_right x y different, mul32, pairVal_run_one_iff]
        constructor
        · intro clear
          exact ⟨letters, rfl, clear⟩
        · rintro ⟨after, equal, clear⟩
          have tails : letters = after := (List.cons.inj equal).2
          subst after
          exact clear
      · have value : run (pairVal x y) 3 (letter :: letters) = 0 := by
          by_cases left : letter = x
          · subst letter
            rw [run_cons, pairVal_left, mul33, run_zero]
          · rw [run_cons, pairVal_other x y letter left right, mul35, run_zero]
        rw [value]
        constructor
        · intro impossible
          exact False.elim (zero_ne_one impossible)
        · rintro ⟨after, equal, _⟩
          exact False.elim (right (List.cons.inj equal).1)

theorem pairVal_run_five_iff (x y : Nat) (different : x ≠ y) (letters : List Nat) :
    run (pairVal x y) 5 letters = 1 ↔ AdjacentOnce x y letters := by
  induction letters with
  | nil =>
      rw [run_nil]
      constructor
      · intro impossible
        exact False.elim (five_ne_one impossible)
      · intro impossible
        exact False.elim (not_adjacentOnce_nil x y impossible)
  | cons letter letters ih =>
      rw [run_cons, adjacentOnce_cons]
      by_cases left : letter = x
      · subst letter
        rw [pairVal_left, mul53, pairVal_run_three_iff x y different]
        simp
      · by_cases right : letter = y
        · subst letter
          rw [pairVal_right x y different, mul52, run_zero]
          constructor
          · intro impossible
            exact False.elim (zero_ne_one impossible)
          · intro alternatives
            rcases alternatives with ⟨equal, _⟩ | ⟨_, impossible, _⟩
            · exact False.elim (left equal)
            · exact False.elim (impossible rfl)
        · rw [pairVal_other x y letter left right, mul55, ih]
          simp [left, right]

def SimpleAdjacent (x y : Nat) (letters : List Nat) : Prop :=
  letters.count x = 1 ∧ letters.count y = 1 ∧ ∃ before after, letters = before ++ x :: y :: after

theorem SimpleAdjacent.distinct {x y : Nat} {letters : List Nat}
    (adjacent : SimpleAdjacent x y letters) : x ≠ y := by
  intro equal
  subst y
  rcases adjacent with ⟨one, _, before, after, decomp⟩
  rw [decomp, List.count_append, List.count_cons_self, List.count_cons_self] at one
  omega

theorem adjacentOnce_iff_simpleAdjacent (x y : Nat) (different : x ≠ y) (letters : List Nat) :
    AdjacentOnce x y letters ↔ SimpleAdjacent x y letters := by
  constructor
  · rintro ⟨before, after, rfl, prefixClear, suffixClear⟩
    have px : before.count x = 0 := List.count_eq_zero.mpr prefixClear.1
    have py : before.count y = 0 := List.count_eq_zero.mpr prefixClear.2
    have sx : after.count x = 0 := List.count_eq_zero.mpr suffixClear.1
    have sy : after.count y = 0 := List.count_eq_zero.mpr suffixClear.2
    refine ⟨?_, ?_, before, after, rfl⟩
    · simp only [List.count_append, List.count_cons_self, List.count_cons_of_ne (Ne.symm different)]
      omega
    · simp only [List.count_append, List.count_cons_of_ne different, List.count_cons_self]
      omega
  · rintro ⟨oneX, oneY, before, after, rfl⟩
    simp only [List.count_append, List.count_cons_self, List.count_cons_of_ne (Ne.symm different)] at oneX
    simp only [List.count_append, List.count_cons_of_ne different, List.count_cons_self] at oneY
    have px : before.count x = 0 := by omega
    have py : before.count y = 0 := by omega
    have sx : after.count x = 0 := by omega
    have sy : after.count y = 0 := by omega
    exact ⟨before, after, rfl, ⟨List.count_eq_zero.mp px, List.count_eq_zero.mp py⟩,
      ⟨List.count_eq_zero.mp sx, List.count_eq_zero.mp sy⟩⟩

theorem SameEval.adjacentOnce {left right : List Nat} (same : SameEval left right)
    (x y : Nat) (different : x ≠ y) : AdjacentOnce x y left ↔ AdjacentOnce x y right := by
  rw [← pairVal_run_five_iff x y different left, ← pairVal_run_five_iff x y different right,
    same (pairVal x y) 5]

theorem SameEval.simpleAdjacent {left right : List Nat} (same : SameEval left right) (x y : Nat) :
    SimpleAdjacent x y left ↔ SimpleAdjacent x y right := by
  constructor
  · intro adjacent
    have different := adjacent.distinct
    exact (adjacentOnce_iff_simpleAdjacent x y different right).mp
      ((same.adjacentOnce x y different).mp ((adjacentOnce_iff_simpleAdjacent x y different left).mpr adjacent))
  · intro adjacent
    have different := adjacent.distinct
    exact (adjacentOnce_iff_simpleAdjacent x y different left).mp
      ((same.symm.adjacentOnce x y different).mp ((adjacentOnce_iff_simpleAdjacent x y different right).mpr adjacent))

theorem identity_simpleAdjacency (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup)
    (x y : Nat) : SimpleAdjacent x y identity.lhs.toList ↔ SimpleAdjacent x y identity.rhs.toList :=
  (sameEval_valid identity valid).simpleAdjacent x y

theorem identity_adjacent_simple (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup)
    (x y : Nat) (simpleX : identity.lhs.toList.count x = 1) (simpleY : identity.lhs.toList.count y = 1) :
    (∃ before after, identity.lhs.toList = before ++ x :: y :: after) ↔
      (∃ before after, identity.rhs.toList = before ++ x :: y :: after) := by
  have same := sameEval_valid identity valid
  constructor
  · intro pair
    exact ((same.simpleAdjacent x y).mp ⟨simpleX, simpleY, pair⟩).2.2
  · intro pair
    exact ((same.simpleAdjacent x y).mpr
      ⟨(same.countOne x).mp simpleX, (same.countOne y).mp simpleY, pair⟩).2.2

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Actual.pairVal_run_one_iff
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Actual.pairVal_run_three_iff
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Actual.pairVal_run_five_iff
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Actual.adjacentOnce_iff_simpleAdjacent
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Actual.SameEval.simpleAdjacent
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Actual.identity_simpleAdjacency
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Actual.identity_adjacent_simple

end SemigroupBasis.CoRoots.Order6SporadicSection18.Actual
