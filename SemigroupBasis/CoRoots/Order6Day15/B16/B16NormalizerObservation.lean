import SemigroupBasis.CoRoots.Order6Day15.B16.B16SegmentObservation

namespace SemigroupBasis.CoRoots.Order6Day15.B16.Reach

open Literal
open SemigroupBasis.CoRoots.Order6Sunday.Msg0514RepairedSixteenLawFinite

/-- The already implemented renderer with its global support held fixed. -/
def normalizeWith (ns xs : List Nat) : List Nat :=
  let cut := splitFront ns xs
  match cut.2 with
  | [] => cut.1
  | _ :: tail => cut.1 ++ (squares ns ++ renderSegments ns (splitGaps ns tail).2)

theorem normalizeList_eq_with (xs : List Nat) :
    normalizeList xs = normalizeWith (nonsimpleSupport xs) xs := rfl

theorem normalizeWith_cons_outside (ns : List Nat) (a : Nat) (xs : List Nat) (ha : a ∉ ns) :
    normalizeWith ns (a :: xs) = a :: normalizeWith ns xs := by
  unfold normalizeWith
  rw [splitFront,if_neg ha]
  change (match (splitFront ns xs).2 with
    | [] => a :: (splitFront ns xs).1
    | _ :: tail => (a :: (splitFront ns xs).1) ++
        (squares ns ++ renderSegments ns (splitGaps ns tail).2)) =
    a :: (match (splitFront ns xs).2 with
      | [] => (splitFront ns xs).1
      | _ :: tail => (splitFront ns xs).1 ++
          (squares ns ++ renderSegments ns (splitGaps ns tail).2))
  cases eq : (splitFront ns xs).2 <;> rfl

theorem normalizeWith_cons_inside (ns : List Nat) (a : Nat) (xs : List Nat) (ha : a ∈ ns) :
    normalizeWith ns (a :: xs) = squares ns ++ renderSegments ns (splitGaps ns xs).2 := by
  rw [normalizeWith,splitFront,if_pos ha]
  rfl

theorem marker_head_pin (ns : List Nat) (a : Nat) (xs : List Nat)
    (simple : MarkersSimple ns (a :: xs)) (ha : a ∉ ns) : GapPin a (a :: xs) [] := by
  have one := simple a (List.Mem.head _) ha
  rw [List.count_cons_self] at one
  have zero : xs.count a = 0 := by omega
  have absent : a ∉ xs := List.count_eq_zero.mp zero
  change a = a ∧ a ∉ xs ++ []
  rw [List.append_nil]
  exact ⟨rfl,absent⟩

theorem normalizeWith_eq_of_marked (ns xs ys : List Nat)
    (leftSimple : MarkersSimple ns xs) (rightSimple : MarkersSimple ns ys)
    (obs : MarkedObservation ns xs ys) : normalizeWith ns xs = normalizeWith ns ys := by
  induction xs generalizing ys with
  | nil =>
      have empty : ys = [] := (optional_empty obs.1).mp rfl
      rw [empty]
  | cons a xs ih =>
      cases ys with
      | nil =>
          have bad := (optional_empty obs.1).mpr rfl
          cases bad
      | cons b ys =>
          by_cases ha : a ∈ ns
          · have hb : b ∈ ns := by
              by_cases present : b ∈ ns
              · exact present
              have targetPin := marker_head_pin ns b ys rightSimple present
              have sourcePin := (optional_pins obs.1 b).mpr targetPin
              have heads : a = b := sourcePin.1
              exact False.elim (present (heads ▸ ha))
            have parts := splitGaps_renderSegments_eq ns (a :: xs) (b :: ys) leftSimple rightSimple obs
            rw [splitGaps,if_pos ha,splitGaps,if_pos hb] at parts
            rw [normalizeWith_cons_inside ns a xs ha,normalizeWith_cons_inside ns b ys hb]
            exact congrArg (fun rest => squares ns ++ rest) parts
          · have sourcePin := marker_head_pin ns a xs leftSimple ha
            have targetPin := (optional_pins obs.1 a).mp sourcePin
            have heads : b = a := targetPin.1
            subst b
            have absent : a ∉ xs := by simpa only [List.append_nil] using sourcePin.2
            have cover : ∀ b ∈ ([] : List Nat), b ∈ ns := fun _ h => False.elim (List.not_mem_nil h)
            have tailObs : MarkedObservation ns xs ys :=
              markedObservation_tail ns [] xs [] ys a cover cover ha absent obs
            have ls : MarkersSimple ns xs := markersSimple_suffix ns [a] xs leftSimple
            have rs : MarkersSimple ns ys := markersSimple_suffix ns [a] ys rightSimple
            have tails := ih ys ls rs tailObs
            rw [normalizeWith_cons_outside ns a xs ha,normalizeWith_cons_outside ns a ys ha]
            exact congrArg (List.cons a) tails

theorem sameObservation_normalizeList {u v : Word Nat} (obs : SameObservation u v) :
    normalizeList u.toList = normalizeList v.toList := by
  have ns := sameObservation_nonsimple obs
  have rightSimple : MarkersSimple (nonsimpleSupport u.toList) v.toList := by
    rw [ns]; exact markersSimple_word v
  rw [normalizeList_eq_with,normalizeList_eq_with,← ns]
  exact normalizeWith_eq_of_marked _ _ _ (markersSimple_word u) rightSimple (sameObservation_marked obs)

theorem sameObservation_normalizeWord {u v : Word Nat} (obs : SameObservation u v) :
    normalizeWord u = normalizeWord v := by
  have lists : (normalizeWord u).toList = (normalizeWord v).toList := by
    rw [normalizeWord_toList,normalizeWord_toList]
    exact sameObservation_normalizeList obs
  cases hu : normalizeWord u with
  | mk a xs =>
      cases hv : normalizeWord v with
      | mk b ys =>
          rw [hu,hv] at lists
          have same : a = b ∧ xs = ys := List.cons.inj lists
          rcases same with ⟨rfl,rfl⟩
          rfl

/-- Full observation completeness for the actual B16 Derives relation, on arbitrary words. -/
theorem sameObservation_derives {u v : Word Nat} (obs : SameObservation u v) :
    Derives basis u v :=
  derives_of_normalizeWord_eq u v (sameObservation_normalizeWord obs)

end SemigroupBasis.CoRoots.Order6Day15.B16.Reach
