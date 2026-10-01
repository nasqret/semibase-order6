import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_1075Endpoints

/-!
# Unrestricted six-state endpoint separators for S6_1075

Map one selected variable to zero-based catalogue element 3, and every
other variable to element 5. On a prepared frame the result records:
0 = interior; 1 = both free endpoints; 2 = free final endpoint;
4 = free initial endpoint; 5 = absent. A singleton instead returns 3.
The proofs below induct over arbitrary lists, not a retained finite window.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_1075

open SemigroupBasis

def probeValuation (selected letter : Nat) : Fin 6 :=
  if letter = selected then 3 else 5

def probeEval (word : Word Nat) (selected : Nat) : Fin 6 :=
  table.semigroup.eval (probeValuation selected) word

def ProbeEquivalent (left right : Word Nat) : Prop :=
  ∀ selected, probeEval left selected = probeEval right selected

private theorem zero_mul (value : Fin 6) : mul 0 value = 0 := by decide +revert

private theorem selected_killed (left right : Fin 6) : mul (mul left 3) right = 0 := by
  decide +revert

private theorem five_stable (left : Fin 6) : mul (mul left 5) 5 = mul left 5 := by
  decide +revert

private theorem fold_zero (selected : Nat) (letters : List Nat) :
    letters.foldl (fun acc letter => mul acc (probeValuation selected letter)) 0 = 0 := by
  induction letters with
  | nil => rfl
  | cons head tail ih => simpa only [List.foldl_cons, zero_mul] using ih

private theorem fold_after_selected (selected last : Nat) (letters : List Nat) (acc : Fin 6) :
    (letters ++ [last]).foldl (fun state letter => mul state (probeValuation selected letter))
      (mul acc 3) = 0 := by
  cases letters with
  | nil => simp only [List.nil_append, List.foldl_cons, List.foldl_nil, selected_killed]
  | cons head tail =>
      simp only [List.cons_append, List.foldl_cons, selected_killed]
      exact fold_zero selected (tail ++ [last])

private theorem fold_final_formula (selected last : Nat) (letters : List Nat) (acc : Fin 6) :
    (letters ++ [last]).foldl (fun state letter => mul state (probeValuation selected letter)) acc =
      if selected ∈ letters then 0
      else if letters = [] then mul acc (probeValuation selected last)
      else mul (mul acc 5) (probeValuation selected last) := by
  induction letters generalizing acc with
  | nil => simp
  | cons head tail ih =>
      simp only [List.cons_append, List.foldl_cons]
      by_cases chosen : head = selected
      · subst head
        have chosenValue : probeValuation selected selected = 3 := by simp [probeValuation]
        rw [chosenValue, fold_after_selected]
        simp
      · have other : probeValuation selected head = 5 := by simp [probeValuation, chosen]
        rw [other, ih]
        by_cases present : selected ∈ tail
        · simp [List.mem_cons, present]
        · by_cases empty : tail = []
          · simp [List.mem_cons, empty, Ne.symm chosen]
          · simp [List.mem_cons, present, empty, Ne.symm chosen, five_stable]

def boundaryValue (first last selected : Nat) : Fin 6 :=
  if first = selected then (if last = selected then 1 else 4)
  else if last = selected then 2 else 5

private theorem boundary_after_five (first last selected : Nat) :
    mul (mul (probeValuation selected first) 5) (probeValuation selected last) =
      boundaryValue first last selected := by
  by_cases initial : first = selected <;> by_cases final : last = selected <;>
    simp [probeValuation, boundaryValue, initial, final, mul]

private theorem boundary_short (first last selected : Nat) (distinct : first ≠ last) :
    mul (probeValuation selected first) (probeValuation selected last) =
      boundaryValue first last selected := by
  by_cases initial : first = selected <;> by_cases final : last = selected
  · exact False.elim (distinct (initial.trans final.symm))
  all_goals simp [probeValuation, boundaryValue, initial, final, mul]

/-- Exact separator formula, including every regular two-letter frame. -/
theorem probe_frame (first last selected : Nat) (interior : List Nat)
    (regular : RegularFrame first interior last) :
    probeEval (framedWord first interior last) selected =
      if selected ∈ interior then 0 else boundaryValue first last selected := by
  change (interior ++ [last]).foldl
      (fun state letter => mul state (probeValuation selected letter))
      (probeValuation selected first) = _
  rw [fold_final_formula]
  by_cases present : selected ∈ interior
  · simp [present]
  · by_cases empty : interior = []
    · have distinct : first ≠ last := by
        rcases regular with nonempty | distinct
        · exact False.elim (nonempty empty)
        · exact distinct
      simp [empty, boundary_short first last selected distinct]
    · simp [present, empty, boundary_after_five]

theorem probe_frame_zero_iff (first last selected : Nat) (interior : List Nat)
    (regular : RegularFrame first interior last) :
    probeEval (framedWord first interior last) selected = 0 ↔ selected ∈ interior := by
  rw [probe_frame first last selected interior regular]
  by_cases present : selected ∈ interior <;>
    by_cases initial : first = selected <;> by_cases final : last = selected <;>
    simp [present, boundaryValue, initial, final]

theorem probe_frame_initial_iff (first last selected : Nat) (interior : List Nat)
    (regular : RegularFrame first interior last) :
    (probeEval (framedWord first interior last) selected = 1 ∨
      probeEval (framedWord first interior last) selected = 4) ↔
        first = selected ∧ selected ∉ interior := by
  rw [probe_frame first last selected interior regular]
  by_cases present : selected ∈ interior <;>
    by_cases initial : first = selected <;> by_cases final : last = selected <;>
    simp [present, boundaryValue, initial, final]

theorem probe_frame_final_iff (first last selected : Nat) (interior : List Nat)
    (regular : RegularFrame first interior last) :
    (probeEval (framedWord first interior last) selected = 1 ∨
      probeEval (framedWord first interior last) selected = 2) ↔
        last = selected ∧ selected ∉ interior := by
  rw [probe_frame first last selected interior regular]
  by_cases present : selected ∈ interior <;>
    by_cases initial : first = selected <;> by_cases final : last = selected <;>
    simp [present, boundaryValue, initial, final]

theorem probe_frame_ne_three (first last selected : Nat) (interior : List Nat)
    (regular : RegularFrame first interior last) :
    probeEval (framedWord first interior last) selected ≠ 3 := by
  rw [probe_frame first last selected interior regular]
  by_cases present : selected ∈ interior <;>
    by_cases initial : first = selected <;> by_cases final : last = selected <;>
    simp [present, boundaryValue, initial, final]

theorem probe_singleton (letter selected : Nat) :
    probeEval (Word.singleton letter) selected = probeValuation selected letter := rfl

/-- The singleton/non-singleton distinction has a concrete separating valuation. -/
theorem singleton_not_probeEquivalent_frame (letter first last : Nat) (interior : List Nat)
    (regular : RegularFrame first interior last) :
    ¬ ProbeEquivalent (Word.singleton letter) (framedWord first interior last) := by
  intro same
  have equal := same letter
  have singletonValue : probeEval (Word.singleton letter) letter = 3 := by
    simp [probe_singleton, probeValuation]
  exact probe_frame_ne_three first last letter interior regular (equal.symm.trans singletonValue)

theorem singleton_eq_of_probeEquivalent (left right : Nat)
    (same : ProbeEquivalent (Word.singleton left) (Word.singleton right)) : left = right := by
  apply Decidable.byContradiction
  intro different
  have equal := same left
  simp [probe_singleton, probeValuation, Ne.symm different] at equal

/-- Equal separator values recover precisely the invariant used by the
unrestricted derivation theorem, with both free endpoints protected. -/
theorem derivesFramesOfProbeEquivalent
    (first last otherFirst otherLast : Nat) (interior otherInterior : List Nat)
    (regular : RegularFrame first interior last)
    (otherRegular : RegularFrame otherFirst otherInterior otherLast)
    (same : ProbeEquivalent (framedWord first interior last)
      (framedWord otherFirst otherInterior otherLast)) :
    Derives basis (framedWord first interior last)
      (framedWord otherFirst otherInterior otherLast) := by
  apply derivesFramedOfEndpointContent first last otherFirst otherLast interior otherInterior
  · intro letter
    rw [← probe_frame_zero_iff first last letter interior regular,
      ← probe_frame_zero_iff otherFirst otherLast letter otherInterior otherRegular,
      same letter]
  · by_cases equal : first = otherFirst
    · exact Or.inl equal
    · apply Or.inr
      constructor
      · apply Decidable.byContradiction
        intro free
        have marked := (probe_frame_initial_iff first last first interior regular).2 ⟨rfl, free⟩
        rw [same first] at marked
        have otherMarked :=
          (probe_frame_initial_iff otherFirst otherLast first otherInterior otherRegular).1 marked
        exact equal otherMarked.1.symm
      · apply Decidable.byContradiction
        intro free
        have marked := (probe_frame_initial_iff otherFirst otherLast otherFirst otherInterior otherRegular).2 ⟨rfl, free⟩
        rw [← same otherFirst] at marked
        exact equal ((probe_frame_initial_iff first last otherFirst interior regular).1 marked).1
  · by_cases equal : last = otherLast
    · exact Or.inl equal
    · apply Or.inr
      constructor
      · apply Decidable.byContradiction
        intro free
        have marked := (probe_frame_final_iff first last last interior regular).2 ⟨rfl, free⟩
        rw [same last] at marked
        have otherMarked :=
          (probe_frame_final_iff otherFirst otherLast last otherInterior otherRegular).1 marked
        exact equal otherMarked.1.symm
      · apply Decidable.byContradiction
        intro free
        have marked := (probe_frame_final_iff otherFirst otherLast otherLast otherInterior otherRegular).2 ⟨rfl, free⟩
        rw [← same otherLast] at marked
        exact equal ((probe_frame_final_iff first last otherLast interior regular).1 marked).1

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_1075
