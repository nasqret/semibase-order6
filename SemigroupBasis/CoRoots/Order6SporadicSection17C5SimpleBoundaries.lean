import SemigroupBasis.CoRoots.Order6SporadicSection17C5Restricted

/-! Arbitrary-word simple-head and simple-tail observations for the literal
C5/C6 tables. Full evaluation is essential for the head test. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6
open SemigroupBasis

theorem countOne_split (marker : Nat) (letters : List Nat) (once : letters.count marker = 1) :
    ∃ before after, letters = before ++ marker :: after ∧ marker ∉ before ∧ marker ∉ after := by
  revert once
  induction letters with
  | nil => intro once; simp at once
  | cons x xs ih =>
      intro once
      by_cases equal : x = marker
      · subst x
        have absent : marker ∉ xs := List.count_eq_zero.mp (by
          have count := once
          simp only [List.count_cons_self] at count
          omega)
        exact ⟨[],xs,rfl,by simp,absent⟩
      · have tailOnce : xs.count marker = 1 := by
          simpa [List.count_cons_of_ne equal] using once
        rcases ih tailOnce with ⟨before,after,shape,absentBefore,absentAfter⟩
        refine ⟨x :: before,after,?_,?_,absentAfter⟩
        · simpa using congrArg (List.cons x) shape
        · simp [equal,Ne.symm equal,absentBefore]

theorem head_split_iff (marker : Nat) (before after : List Nat) (absent : marker ∉ before) :
    (before ++ marker :: after).head? = some marker ↔ before = [] := by
  cases before with
  | nil => simp
  | cons x xs =>
      have different : x ≠ marker := fun equal => absent (by simp [equal])
      simp [different]

theorem reverse_head_split_iff (marker : Nat) (before after : List Nat) (absent : marker ∉ after) :
    (before ++ marker :: after).reverse.head? = some marker ↔ after = [] := by
  have reflected := head_split_iff marker after.reverse before.reverse (by simpa using absent)
  simpa [List.reverse_append,List.reverse_cons,List.append_assoc] using reflected

def SimpleHead (marker : Nat) (letters : List Nat) : Prop :=
  letters.count marker = 1 ∧ letters.head? = some marker

def SimpleTail (marker : Nat) (letters : List Nat) : Prop :=
  letters.count marker = 1 ∧ letters.reverse.head? = some marker

namespace Semantics

def markerVal (marker : Nat) (value : Fin 6) (x : Nat) : Fin 6 :=
  if x = marker then value else 5

def boundaryDrop (which : Bool) : Fin 6 := if which then 1 else 0

theorem five_fixed (which : Bool) : mul which 5 5 = 5 := by
  revert which
  decide

theorem head_fixed (which : Bool) : mul which 2 5 = 2 := by
  revert which
  decide

theorem head_after_prefix (which : Bool) : mul which 5 2 = boundaryDrop which := by
  revert which
  decide

theorem tail_after_prefix (which : Bool) : mul which 5 3 = 3 := by
  revert which
  decide

theorem tail_after_suffix (which : Bool) : mul which 3 5 = boundaryDrop which := by
  revert which
  decide

theorem drop_fixed (which : Bool) : mul which (boundaryDrop which) 5 = boundaryDrop which := by
  revert which
  decide

theorem run_marker_absent (which : Bool) (marker : Nat) (value acc : Fin 6) (letters : List Nat)
    (absent : marker ∉ letters) (fixed : mul which acc 5 = acc) :
    run which (markerVal marker value) acc letters = acc := by
  revert absent
  induction letters with
  | nil => intro _; rfl
  | cons x xs ih =>
      intro absent
      have different : x ≠ marker := fun equal => absent (by simp [equal])
      have tailAbsent : marker ∉ xs := fun member => absent (List.mem_cons.mpr (Or.inr member))
      rw [run_cons,markerVal,if_neg different,fixed]
      exact ih tailAbsent

theorem head_probe (which : Bool) (marker : Nat) (letters : List Nat) (once : letters.count marker = 1) :
    evalList which (markerVal marker 2) letters = some 2 ↔ letters.head? = some marker := by
  rcases countOne_split marker letters once with ⟨before,after,shape,absentBefore,absentAfter⟩
  rw [shape,head_split_iff marker before after absentBefore]
  cases before with
  | nil =>
      have evaluated : evalList which (markerVal marker 2) (marker :: after) = some 2 := by
        change some (run which (markerVal marker 2) (markerVal marker 2 marker) after) = some 2
        rw [markerVal,if_pos rfl,run_marker_absent which marker 2 2 after absentAfter (head_fixed which)]
      simpa using evaluated
  | cons x xs =>
      have different : x ≠ marker := fun equal => absentBefore (by simp [equal])
      have restAbsent : marker ∉ xs := fun member => absentBefore (List.mem_cons.mpr (Or.inr member))
      have evaluated : evalList which (markerVal marker 2) ((x :: xs) ++ marker :: after) =
          some (boundaryDrop which) := by
        change some (run which (markerVal marker 2) (markerVal marker 2 x) (xs ++ marker :: after)) = _
        rw [markerVal,if_neg different,run_append,
          run_marker_absent which marker 2 5 xs restAbsent (five_fixed which)]
        rw [run_cons,markerVal,if_pos rfl,head_after_prefix,
          run_marker_absent which marker 2 (boundaryDrop which) after absentAfter (drop_fixed which)]
      rw [evaluated]
      have differentValue : (some (boundaryDrop which) : Option (Fin 6)) ≠ some 2 := by
        cases which <;> decide
      simp [differentValue]

theorem tail_probe (which : Bool) (marker : Nat) (letters : List Nat) (once : letters.count marker = 1) :
    run which (markerVal marker 3) 5 letters = 3 ↔ letters.reverse.head? = some marker := by
  rcases countOne_split marker letters once with ⟨before,after,shape,absentBefore,absentAfter⟩
  rw [shape,reverse_head_split_iff marker before after absentAfter]
  rw [run_append,run_marker_absent which marker 3 5 before absentBefore (five_fixed which)]
  rw [run_cons,markerVal,if_pos rfl,tail_after_prefix]
  cases after with
  | nil => simp [run_nil]
  | cons x xs =>
      have different : x ≠ marker := fun equal => absentAfter (by simp [equal])
      have restAbsent : marker ∉ xs := fun member => absentAfter (List.mem_cons.mpr (Or.inr member))
      rw [run_cons,markerVal,if_neg different,tail_after_suffix,
        run_marker_absent which marker 3 (boundaryDrop which) xs restAbsent (drop_fixed which)]
      have differentValue : boundaryDrop which ≠ 3 := by cases which <;> decide
      simp [differentValue]

theorem SameEval.headOfSimple {which : Bool} {left right : List Nat}
    (same : SameEval which left right) (marker : Nat) (once : left.count marker = 1) :
    left.head? = some marker ↔ right.head? = some marker := by
  have rightOnce := (same.countOne marker).mp once
  rw [← head_probe which marker left once,← head_probe which marker right rightOnce,same (markerVal marker 2)]

theorem SameEval.tailOfSimple {which : Bool} {left right : List Nat}
    (same : SameEval which left right) (marker : Nat) (once : left.count marker = 1) :
    left.reverse.head? = some marker ↔ right.reverse.head? = some marker := by
  have rightOnce := (same.countOne marker).mp once
  rw [← tail_probe which marker left once,← tail_probe which marker right rightOnce,same.runEq (markerVal marker 3) 5]

theorem SameEval.simpleHead {which : Bool} {left right : List Nat}
    (same : SameEval which left right) (marker : Nat) : SimpleHead marker left ↔ SimpleHead marker right := by
  constructor
  · rintro ⟨once,head⟩
    exact ⟨(same.countOne marker).mp once,(same.headOfSimple marker once).mp head⟩
  · rintro ⟨once,head⟩
    exact ⟨(same.symm.countOne marker).mp once,(same.symm.headOfSimple marker once).mp head⟩

theorem SameEval.simpleTail {which : Bool} {left right : List Nat}
    (same : SameEval which left right) (marker : Nat) : SimpleTail marker left ↔ SimpleTail marker right := by
  constructor
  · rintro ⟨once,tail⟩
    exact ⟨(same.countOne marker).mp once,(same.tailOfSimple marker once).mp tail⟩
  · rintro ⟨once,tail⟩
    exact ⟨(same.symm.countOne marker).mp once,(same.symm.tailOfSimple marker once).mp tail⟩

end Semantics

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.countOne_split
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.head_split_iff
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.reverse_head_split_iff
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.Semantics.run_marker_absent
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.Semantics.head_probe
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.Semantics.tail_probe
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.Semantics.SameEval.headOfSimple
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.Semantics.SameEval.tailOfSimple
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.Semantics.SameEval.simpleHead
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.Semantics.SameEval.simpleTail

end SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6
