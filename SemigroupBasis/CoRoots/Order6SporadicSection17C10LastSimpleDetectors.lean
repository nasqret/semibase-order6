import SemigroupBasis.CoRoots.Order6SporadicSection17C10OrderDetectors

/-! The last-to-simple probe of Lemma17.6(v), including an empty-prefix
probe. The C10 and D1 outputs are complementary. Inference never cancels a
semigroup context and never treats a later occurrence as a last one. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1.Semantics
open SemigroupBasis

def markerState (which : Bool) : Fin 6 := if which then 3 else 4
def backgroundState (which : Bool) : Fin 6 := if which then 4 else 3
def hitValue (which : Bool) : Fin 6 := if which then 0 else 2
def missValue (which : Bool) : Fin 6 := if which then 2 else 0

def lastSimpleVal (which : Bool) (separator marker x : Nat) : Fin 6 :=
  if x = separator then 1 else if x = marker then markerState which else 5

def PrefixState (which : Bool) (a : Fin 6) : Prop :=
  a = 5 ∨ a = markerState which ∨ a = backgroundState which

theorem prefix_closed (which : Bool) (a b : Fin 6)
    (ha : PrefixState which a) (hb : b = markerState which ∨ b = 5) :
    PrefixState which (mul which a b) := by
  revert which a b
  unfold PrefixState
  decide

theorem prefix_end_marker (which : Bool) (a : Fin 6) (ha : PrefixState which a) :
    mul which (mul which a (markerState which)) 1 = hitValue which := by
  revert which a
  unfold PrefixState
  decide

theorem prefix_end_background (which : Bool) (a : Fin 6) (ha : PrefixState which a) :
    mul which (mul which a 5) 1 = missValue which := by
  revert which a
  unfold PrefixState
  decide

theorem hit_ne_miss (which : Bool) : hitValue which ≠ missValue which := by
  cases which <;> decide

theorem lastSimpleVal_range (which : Bool) (separator marker x : Nat) (different : x ≠ separator) :
    lastSimpleVal which separator marker x = markerState which ∨
      lastSimpleVal which separator marker x = 5 := by
  rw [lastSimpleVal,if_neg different]
  by_cases same : x = marker
  · rw [if_pos same]
    exact Or.inl rfl
  · rw [if_neg same]
    exact Or.inr rfl

theorem prefix_outcome (which : Bool) (separator marker : Nat) (before : List Nat)
    (absent : separator ∉ before) (acc : Fin 6) (stable : PrefixState which acc) :
    mul which (run which (lastSimpleVal which separator marker) acc before) 1 =
      if before.getLast? = none then mul which acc 1
      else if before.getLast? = some marker then hitValue which else missValue which := by
  induction before generalizing acc with
  | nil => rfl
  | cons x xs ih =>
      have noHead : x ≠ separator := fun same => absent (by simp [same])
      have noTail : separator ∉ xs := fun member => absent (List.mem_cons_of_mem x member)
      have nextStable := prefix_closed which acc (lastSimpleVal which separator marker x) stable
        (lastSimpleVal_range which separator marker x noHead)
      cases xs with
      | nil =>
          by_cases same : x = marker
          · have value : lastSimpleVal which separator marker x = markerState which := by
              rw [lastSimpleVal,if_neg noHead,if_pos same]
            rw [run_cons,run_nil,value]
            simpa [same] using prefix_end_marker which acc stable
          · have value : lastSimpleVal which separator marker x = 5 := by
              rw [lastSimpleVal,if_neg noHead,if_neg same]
            rw [run_cons,run_nil,value]
            simpa [same] using prefix_end_background which acc stable
      | cons y ys =>
          simpa only [run_cons,List.getLast?_cons_cons,List.getLast?_eq_none_iff,
            List.cons_ne_nil,if_false] using ih noTail _ nextStable

theorem lastSimpleVal_after (which : Bool) (separator marker : Nat) (after : List Nat)
    (absent : separator ∉ after) (acc : Fin 6) (stable : acc = 0 ∨ acc = 2) :
    run which (lastSimpleVal which separator marker) acc after = if marker ∈ after then 0 else acc := by
  induction after generalizing acc with
  | nil => simp [run_nil]
  | cons x xs ih =>
      have noHead : x ≠ separator := fun same => absent (by simp [same])
      have noTail : separator ∉ xs := fun member => absent (List.mem_cons_of_mem x member)
      by_cases same : x = marker
      · have killed : mul which acc (markerState which) = 0 := by
          rcases stable with rfl | rfl <;> cases which <;> decide
        have value : lastSimpleVal which separator marker x = markerState which := by
          rw [lastSimpleVal,if_neg noHead,if_pos same]
        rw [run_cons,value,killed,run_zero]
        simp [same]
      · have kept : mul which acc 5 = acc := by
          rcases stable with rfl | rfl <;> cases which <;> decide
        have value : lastSimpleVal which separator marker x = 5 := by
          rw [lastSimpleVal,if_neg noHead,if_neg same]
        simpa [run_cons,value,kept,Ne.symm same] using ih noTail acc stable

theorem previous_probe (which : Bool) (separator marker : Nat) (before after : List Nat)
    (beforeAbsent : separator ∉ before) (afterAbsent : separator ∉ after) :
    run which (lastSimpleVal which separator marker) 5 (before ++ separator :: after) =
      if marker ∈ after then 0
      else if before.getLast? = some marker then hitValue which else missValue which := by
  have initial : mul which 5 1 = missValue which := by cases which <;> decide
  have beforeValue : mul which (run which (lastSimpleVal which separator marker) 5 before) 1 =
      if before.getLast? = some marker then hitValue which else missValue which := by
    rw [prefix_outcome which separator marker before beforeAbsent 5 (Or.inl rfl)]
    by_cases empty : before.getLast? = none
    · simp [empty,initial]
    · simp [empty]
  rw [run_append,run_cons,show lastSimpleVal which separator marker separator = 1 by simp [lastSimpleVal],beforeValue]
  have stable : (if before.getLast? = some marker then hitValue which else missValue which) = 0 ∨
      (if before.getLast? = some marker then hitValue which else missValue which) = 2 := by
    split <;> cases which <;> decide
  exact lastSimpleVal_after which separator marker after afterAbsent _ stable

theorem last_ne_of_absent (marker : Nat) (letters : List Nat) (absent : marker ∉ letters) :
    letters.getLast? ≠ some marker := by
  intro equal
  obtain ⟨before,shape⟩ := List.getLast?_eq_some_iff.mp equal
  exact absent (by simp [shape])

theorem empty_prefix_probe (which : Bool) (separator : Nat) (before after : List Nat)
    (beforeAbsent : separator ∉ before) (afterAbsent : separator ∉ after) :
    run which (lastSimpleVal which separator separator) (markerState which) (before ++ separator :: after) =
      if before = [] then hitValue which else missValue which := by
  have initial : mul which (markerState which) 1 = hitValue which := by cases which <;> decide
  have beforeValue : mul which (run which (lastSimpleVal which separator separator) (markerState which) before) 1 =
      if before = [] then hitValue which else missValue which := by
    rw [prefix_outcome which separator separator before beforeAbsent (markerState which) (Or.inr (Or.inl rfl))]
    simp [initial,last_ne_of_absent separator before beforeAbsent]
  rw [run_append,run_cons,show lastSimpleVal which separator separator separator = 1 by simp [lastSimpleVal],beforeValue]
  have stable : (if before = [] then hitValue which else missValue which) = 0 ∨
      (if before = [] then hitValue which else missValue which) = 2 := by
    split <;> cases which <;> decide
  rw [lastSimpleVal_after which separator separator after afterAbsent _ stable,if_neg afterAbsent]

theorem sameEval_beforeEmpty (which : Bool) (separator : Nat)
    (leftBefore leftAfter rightBefore rightAfter : List Nat)
    (same : SameEval which (leftBefore ++ separator :: leftAfter) (rightBefore ++ separator :: rightAfter))
    (leftBeforeAbsent : separator ∉ leftBefore) (leftAfterAbsent : separator ∉ leftAfter)
    (rightBeforeAbsent : separator ∉ rightBefore) (rightAfterAbsent : separator ∉ rightAfter) :
    leftBefore = [] ↔ rightBefore = [] := by
  have observed := same (lastSimpleVal which separator separator) (markerState which)
  rw [empty_prefix_probe which separator leftBefore leftAfter leftBeforeAbsent leftAfterAbsent,
    empty_prefix_probe which separator rightBefore rightAfter rightBeforeAbsent rightAfterAbsent] at observed
  by_cases leftEmpty : leftBefore = [] <;> by_cases rightEmpty : rightBefore = [] <;>
    simp [leftEmpty,rightEmpty,hit_ne_miss which,Ne.symm (hit_ne_miss which)] at observed ⊢

theorem sameEval_previous (which : Bool) (separator marker : Nat)
    (leftBefore leftAfter rightBefore rightAfter : List Nat)
    (same : SameEval which (leftBefore ++ separator :: leftAfter) (rightBefore ++ separator :: rightAfter))
    (leftBeforeAbsent : separator ∉ leftBefore) (leftAfterAbsent : separator ∉ leftAfter)
    (rightBeforeAbsent : separator ∉ rightBefore) (rightAfterAbsent : separator ∉ rightAfter)
    (markerAfterLeft : marker ∉ leftAfter) (markerAfterRight : marker ∉ rightAfter) :
    leftBefore.getLast? = some marker ↔ rightBefore.getLast? = some marker := by
  have observed := same (lastSimpleVal which separator marker) 5
  rw [previous_probe which separator marker leftBefore leftAfter leftBeforeAbsent leftAfterAbsent,
    previous_probe which separator marker rightBefore rightAfter rightBeforeAbsent rightAfterAbsent] at observed
  simp only [markerAfterLeft,markerAfterRight,if_false] at observed
  by_cases leftLast : leftBefore.getLast? = some marker <;>
    by_cases rightLast : rightBefore.getLast? = some marker <;>
    simp [leftLast,rightLast,hit_ne_miss which,Ne.symm (hit_ne_miss which)] at observed ⊢

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1.Semantics.prefix_outcome
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1.Semantics.previous_probe
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1.Semantics.empty_prefix_probe
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1.Semantics.sameEval_beforeEmpty
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1.Semantics.sameEval_previous

end SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1.Semantics
