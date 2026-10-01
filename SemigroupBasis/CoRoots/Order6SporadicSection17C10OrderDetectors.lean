import SemigroupBasis.CoRoots.Order6SporadicSection17C10Evaluation

/-! Unbounded probes for last letters and content after a unique simple
letter, simultaneously for the actual C10 and D1 tables. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1.Semantics
open SemigroupBasis

def bandVal (marker x : Nat) : Fin 6 := if x = marker then 3 else 4

theorem bandVal_range (marker x : Nat) : bandVal marker x = 3 ∨ bandVal marker x = 4 := by
  by_cases same : x = marker <;> simp [bandVal,same]

theorem rightBand (which : Bool) (a b : Fin 6)
    (ha : a = 3 ∨ a = 4) (hb : b = 3 ∨ b = 4) : mul which a b = b := by
  revert which a b
  decide

theorem run_band_range (which : Bool) (marker : Nat) (letters : List Nat) (acc : Fin 6)
    (ha : acc = 3 ∨ acc = 4) :
    run which (bandVal marker) acc letters = 3 ∨ run which (bandVal marker) acc letters = 4 := by
  induction letters generalizing acc with
  | nil => exact ha
  | cons x xs ih =>
      rw [run_cons,rightBand which acc (bandVal marker x) ha (bandVal_range marker x)]
      exact ih _ (bandVal_range marker x)

theorem run_band_last (which : Bool) (marker : Nat) (before : List Nat) (last : Nat) (acc : Fin 6)
    (ha : acc = 3 ∨ acc = 4) :
    run which (bandVal marker) acc (before ++ [last]) = bandVal marker last := by
  rw [run_append,run_cons,run_nil]
  exact rightBand which _ _ (run_band_range which marker before acc ha) (bandVal_range marker last)

theorem nil_or_last (letters : List Nat) :
    letters = [] ∨ ∃ before last, letters = before ++ [last] := by
  induction letters with
  | nil => exact Or.inl rfl
  | cons x xs ih =>
      rcases ih with rfl | ⟨before,last,rfl⟩
      · exact Or.inr ⟨[],x,rfl⟩
      · exact Or.inr ⟨x :: before,last,rfl⟩

theorem SameEval.last {which : Bool} {left right : List Nat} (same : SameEval which left right) :
    left.getLast? = right.getLast? := by
  rcases nil_or_last left with rfl | ⟨leftBefore,x,rfl⟩
  · rcases nil_or_last right with rfl | ⟨rightBefore,y,rfl⟩
    · rfl
    · have equal := same (bandVal y) 4
      have impossible : (4 : Fin 6) = 3 := by
        simpa [run_nil,run_band_last which y rightBefore y 4 (Or.inr rfl),bandVal] using equal
      exact False.elim ((by decide : (4 : Fin 6) ≠ 3) impossible)
  · rcases nil_or_last right with rfl | ⟨rightBefore,y,rfl⟩
    · have equal := same (bandVal x) 4
      have impossible : (3 : Fin 6) = 4 := by
        simpa [run_nil,run_band_last which x leftBefore x 4 (Or.inr rfl),bandVal] using equal
      exact False.elim ((by decide : (3 : Fin 6) ≠ 4) impossible)
    · by_cases equal : x = y
      · simp [equal]
      · have observed := same (bandVal x) 4
        have impossible : (3 : Fin 6) = 4 := by
          simpa [run_band_last which x leftBefore x 4 (Or.inr rfl),
            run_band_last which x rightBefore y 4 (Or.inr rfl),bandVal,Ne.symm equal] using observed
        exact False.elim ((by decide : (3 : Fin 6) ≠ 4) impossible)

def orderVal (separator marker x : Nat) : Fin 6 :=
  if x = separator then 2 else if x = marker then 3 else 5

theorem orderVal_range (separator marker x : Nat) (absent : x ≠ separator) :
    orderVal separator marker x = 3 ∨ orderVal separator marker x = 5 := by
  rw [orderVal,if_neg absent]
  by_cases same : x = marker
  · rw [if_pos same]
    exact Or.inl rfl
  · rw [if_neg same]
    exact Or.inr rfl

theorem orderPrefix_closed (which : Bool) (a b : Fin 6)
    (ha : a = 3 ∨ a = 4 ∨ a = 5) (hb : b = 3 ∨ b = 5) :
    mul which a b = 3 ∨ mul which a b = 4 ∨ mul which a b = 5 := by
  revert which a b
  decide

theorem orderPrefix_separator (which : Bool) (a : Fin 6)
    (ha : a = 3 ∨ a = 4 ∨ a = 5) : mul which a 2 = 2 := by
  revert which a
  decide

theorem orderVal_before (which : Bool) (separator marker : Nat) (before : List Nat)
    (absent : separator ∉ before) (acc : Fin 6) (stable : acc = 3 ∨ acc = 4 ∨ acc = 5) :
    run which (orderVal separator marker) acc before = 3 ∨
      run which (orderVal separator marker) acc before = 4 ∨
      run which (orderVal separator marker) acc before = 5 := by
  induction before generalizing acc with
  | nil => exact stable
  | cons x xs ih =>
      have noHead : x ≠ separator := fun equal => absent (by simp [equal])
      have noTail : separator ∉ xs := fun member => absent (List.mem_cons_of_mem x member)
      rw [run_cons]
      exact ih noTail _ (orderPrefix_closed which _ _ stable (orderVal_range separator marker x noHead))

theorem orderVal_after (which : Bool) (separator marker : Nat) (after : List Nat)
    (absent : separator ∉ after) :
    run which (orderVal separator marker) 2 after = if marker ∈ after then 0 else 2 := by
  induction after with
  | nil => simp [run_nil]
  | cons x xs ih =>
      have noHead : x ≠ separator := fun equal => absent (by simp [equal])
      have noTail : separator ∉ xs := fun member => absent (List.mem_cons_of_mem x member)
      by_cases same : x = marker
      · subst x
        have killed : mul which 2 3 = 0 := by cases which <;> decide
        simp [run_cons,orderVal,noHead,killed,run_zero]
      · have kept : mul which 2 5 = 2 := by cases which <;> decide
        simpa [run_cons,orderVal,noHead,same,kept,Ne.symm same] using ih noTail

theorem orderVal_split (which : Bool) (separator marker : Nat) (before after : List Nat)
    (beforeAbsent : separator ∉ before) (afterAbsent : separator ∉ after) :
    run which (orderVal separator marker) 5 (before ++ separator :: after) =
      if marker ∈ after then 0 else 2 := by
  have stable := orderVal_before which separator marker before beforeAbsent 5 (Or.inr (Or.inr rfl))
  rw [run_append,run_cons,show orderVal separator marker separator = 2 by simp [orderVal],
    orderPrefix_separator which _ stable]
  exact orderVal_after which separator marker after afterAbsent

theorem sameEval_afterMem (which : Bool) (separator : Nat)
    (leftBefore leftAfter rightBefore rightAfter : List Nat)
    (same : SameEval which (leftBefore ++ separator :: leftAfter) (rightBefore ++ separator :: rightAfter))
    (leftBeforeAbsent : separator ∉ leftBefore) (leftAfterAbsent : separator ∉ leftAfter)
    (rightBeforeAbsent : separator ∉ rightBefore) (rightAfterAbsent : separator ∉ rightAfter) :
    ∀ marker, marker ∈ leftAfter ↔ marker ∈ rightAfter := by
  intro marker
  have observed := same (orderVal separator marker) 5
  rw [orderVal_split which separator marker leftBefore leftAfter leftBeforeAbsent leftAfterAbsent,
    orderVal_split which separator marker rightBefore rightAfter rightBeforeAbsent rightAfterAbsent] at observed
  by_cases leftFound : marker ∈ leftAfter <;> by_cases rightFound : marker ∈ rightAfter <;>
    simp [leftFound,rightFound] at observed ⊢

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1.Semantics.SameEval.last
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1.Semantics.orderVal_split
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1.Semantics.sameEval_afterMem

end SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1.Semantics
