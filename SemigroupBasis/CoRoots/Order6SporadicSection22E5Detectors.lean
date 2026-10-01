import SemigroupBasis.CoRoots.Order6SporadicSection22E5Evaluation

/-! The two positional probes in Lemma22.2. A unique separator is evaluated
at paper element3 for suffix content, and at element2 for immediate
successorship. The latter uses the explicit outer element5 on both sides. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection22.E5
open SemigroupBasis

theorem run_fixed (valuation : Nat → Fin 6) (letters : List Nat) (acc : Fin 6)
    (fixed : ∀ x ∈ letters, tableMul acc (valuation x) = acc) : run valuation acc letters = acc := by
  induction letters with
  | nil => rfl
  | cons x xs ih =>
      rw [run_cons,fixed x (by simp)]
      exact ih (fun y member => fixed y (List.mem_cons_of_mem x member))

def nextVal (separator marker x : Nat) : Fin 6 :=
  if x = separator then 1 else if x = marker then 5 else 4

theorem nextVal_before (separator marker : Nat) (before : List Nat) (absent : separator ∉ before) :
    run (nextVal separator marker) 4 before = 4 := by
  apply run_fixed
  intro x member
  have noSeparator : x ≠ separator := fun equal => absent (by simpa [equal] using member)
  by_cases equal : x = marker
  · rw [nextVal,if_neg noSeparator,if_pos equal]
    decide
  · rw [nextVal,if_neg noSeparator,if_neg equal]
    decide

theorem nextVal_stable (separator marker : Nat) (letters : List Nat) (absent : separator ∉ letters)
    (acc : Fin 6) (stable : acc = 0 ∨ acc = 2) : run (nextVal separator marker) acc letters = acc := by
  apply run_fixed
  intro x member
  have noSeparator : x ≠ separator := fun equal => absent (by simpa [equal] using member)
  rcases stable with rfl | rfl
  · exact zeroRow _
  · by_cases equal : x = marker
    · rw [nextVal,if_neg noSeparator,if_pos equal]
      decide
    · rw [nextVal,if_neg noSeparator,if_neg equal]
      decide

theorem nextVal_after (separator marker : Nat) (after : List Nat) (absent : separator ∉ after) :
    tableMul (run (nextVal separator marker) 1 after) 4 =
      if after.head? = some marker then 2 else 0 := by
  cases after with
  | nil =>
      change tableMul 1 4 = 0
      decide
  | cons x xs =>
      have noSeparator : x ≠ separator := fun equal => absent (by simp [equal])
      have noTail : separator ∉ xs := fun member => absent (List.mem_cons_of_mem x member)
      by_cases equal : x = marker
      · rw [run_cons,nextVal,if_neg noSeparator,if_pos equal,
          show tableMul 1 5 = 2 by decide,nextVal_stable separator marker xs noTail 2 (Or.inr rfl),
          show tableMul 2 4 = 2 by decide]
        simp [equal]
      · rw [run_cons,nextVal,if_neg noSeparator,if_neg equal,
          show tableMul 1 4 = 0 by decide,nextVal_stable separator marker xs noTail 0 (Or.inl rfl),
          show tableMul 0 4 = 0 by decide]
        simp [equal]

theorem nextVal_split (separator marker : Nat) (before after : List Nat)
    (beforeAbsent : separator ∉ before) (afterAbsent : separator ∉ after) :
    tableMul (run (nextVal separator marker) 4 (before ++ separator :: after)) 4 =
      if after.head? = some marker then 2 else 0 := by
  rw [run_append,nextVal_before separator marker before beforeAbsent,run_cons,nextVal,if_pos rfl,
    show tableMul 4 1 = 1 by decide]
  exact nextVal_after separator marker after afterAbsent

def orderVal (separator marker x : Nat) : Fin 6 :=
  if x = separator then 2 else if x = marker then 3 else 4

theorem orderVal_range (separator marker x : Nat) (different : x ≠ separator) :
    orderVal separator marker x = 3 ∨ orderVal separator marker x = 4 := by
  rw [orderVal,if_neg different]
  by_cases same : x = marker
  · rw [if_pos same]
    exact Or.inl rfl
  · rw [if_neg same]
    exact Or.inr rfl

theorem tableMul_closed34 (a b : Fin 6) (left : a = 3 ∨ a = 4) (right : b = 3 ∨ b = 4) :
    tableMul a b = 3 ∨ tableMul a b = 4 := by
  revert a b
  decide

theorem orderVal_before (separator marker : Nat) (before : List Nat) (absent : separator ∉ before)
    (acc : Fin 6) (bounded : acc = 3 ∨ acc = 4) :
    run (orderVal separator marker) acc before = 3 ∨ run (orderVal separator marker) acc before = 4 := by
  induction before generalizing acc with
  | nil => exact bounded
  | cons x xs ih =>
      have noSeparator : x ≠ separator := fun equal => absent (by simp [equal])
      have noTail : separator ∉ xs := fun member => absent (List.mem_cons_of_mem x member)
      rw [run_cons]
      exact ih noTail _ (tableMul_closed34 _ _ bounded (orderVal_range separator marker x noSeparator))

theorem orderVal_after (separator marker : Nat) (after : List Nat) (absent : separator ∉ after) :
    run (orderVal separator marker) 2 after = if marker ∈ after then 0 else 2 := by
  induction after with
  | nil => simp [run_nil]
  | cons x xs ih =>
      have noSeparator : x ≠ separator := fun equal => absent (by simp [equal])
      have noTail : separator ∉ xs := fun member => absent (List.mem_cons_of_mem x member)
      by_cases equal : x = marker
      · rw [run_cons,orderVal,if_neg noSeparator,if_pos equal,
          show tableMul 2 3 = 0 by decide,run_zero]
        simp [equal]
      · rw [run_cons,orderVal,if_neg noSeparator,if_neg equal,
          show tableMul 2 4 = 2 by decide,ih noTail]
        simp [Ne.symm equal]

theorem orderVal_split (separator marker : Nat) (before after : List Nat)
    (beforeAbsent : separator ∉ before) (afterAbsent : separator ∉ after) :
    run (orderVal separator marker) 4 (before ++ separator :: after) =
      if marker ∈ after then 0 else 2 := by
  have bounded := orderVal_before separator marker before beforeAbsent 4 (Or.inr rfl)
  have atSeparator : tableMul (run (orderVal separator marker) 4 before)
      (orderVal separator marker separator) = 2 := by
    rw [orderVal,if_pos rfl]
    rcases bounded with equal | equal
    · rw [equal]
      decide
    · rw [equal]
      decide
  rw [run_append,run_cons,atSeparator]
  exact orderVal_after separator marker after afterAbsent

theorem sameEval_afterMem (separator : Nat) (leftBefore leftAfter rightBefore rightAfter : List Nat)
    (same : SameEval (leftBefore ++ separator :: leftAfter) (rightBefore ++ separator :: rightAfter))
    (leftBeforeAbsent : separator ∉ leftBefore) (leftAfterAbsent : separator ∉ leftAfter)
    (rightBeforeAbsent : separator ∉ rightBefore) (rightAfterAbsent : separator ∉ rightAfter)
    (marker : Nat) : marker ∈ leftAfter ↔ marker ∈ rightAfter := by
  have evaluated := same (orderVal separator marker) 4
  rw [orderVal_split separator marker leftBefore leftAfter leftBeforeAbsent leftAfterAbsent,
    orderVal_split separator marker rightBefore rightAfter rightBeforeAbsent rightAfterAbsent] at evaluated
  by_cases leftMember : marker ∈ leftAfter <;> by_cases rightMember : marker ∈ rightAfter <;>
    simp_all

theorem sameEval_nextAfter (separator : Nat) (leftBefore leftAfter rightBefore rightAfter : List Nat)
    (same : SameEval (leftBefore ++ separator :: leftAfter) (rightBefore ++ separator :: rightAfter))
    (leftBeforeAbsent : separator ∉ leftBefore) (leftAfterAbsent : separator ∉ leftAfter)
    (rightBeforeAbsent : separator ∉ rightBefore) (rightAfterAbsent : separator ∉ rightAfter) :
    leftAfter.head? = rightAfter.head? := by
  have probe (marker : Nat) :
      (if leftAfter.head? = some marker then (2 : Fin 6) else 0) =
      (if rightAfter.head? = some marker then (2 : Fin 6) else 0) := by
    have evaluated : tableMul (run (nextVal separator marker) 4 (leftBefore ++ separator :: leftAfter)) 4 =
        tableMul (run (nextVal separator marker) 4 (rightBefore ++ separator :: rightAfter)) 4 :=
      congrArg (fun value => tableMul value 4) (same (nextVal separator marker) 4)
    rw [nextVal_split separator marker leftBefore leftAfter leftBeforeAbsent leftAfterAbsent,
      nextVal_split separator marker rightBefore rightAfter rightBeforeAbsent rightAfterAbsent] at evaluated
    exact evaluated
  cases leftHead : leftAfter.head? with
  | none =>
      cases rightHead : rightAfter.head? with
      | none => rfl
      | some y =>
          have impossible : (0 : Fin 6) = 2 := by simpa [leftHead,rightHead] using probe y
          exact False.elim ((by decide : (0 : Fin 6) ≠ 2) impossible)
  | some x =>
      cases rightHead : rightAfter.head? with
      | none =>
          have impossible : (2 : Fin 6) = 0 := by simpa [leftHead,rightHead] using probe x
          exact False.elim ((by decide : (2 : Fin 6) ≠ 0) impossible)
      | some y =>
          by_cases equal : x = y
          · simp [equal]
          · have impossible : (2 : Fin 6) = 0 := by
              simpa [leftHead,rightHead,Ne.symm equal] using probe x
            exact False.elim ((by decide : (2 : Fin 6) ≠ 0) impossible)

#print axioms nextVal_split
#print axioms orderVal_split
#print axioms sameEval_afterMem
#print axioms sameEval_nextAfter

end SemigroupBasis.CoRoots.Order6SporadicSection22.E5
