import SemigroupBasis.CoRoots.Order6Day15.B16.B16FirstSeparator

namespace SemigroupBasis.CoRoots.Order6Day15.B16.Reach

open Literal

def GoodSegments (ns : List Nat) (segs : List (Nat × List Nat)) : Prop :=
  ∀ seg ∈ segs, seg.1 ∉ ns ∧ ∀ a ∈ seg.2, a ∈ ns

theorem splitGaps_good (ns xs : List Nat) : GoodSegments ns (splitGaps ns xs).2 := by
  intro seg hs
  exact ⟨splitGaps_separators ns xs seg hs,splitGaps_later_covered ns xs seg hs⟩

/-- Simultaneously identify every later rendered segment and the current rendered gap. -/
theorem renderParts_eq (ns g : List Nat) (segs : List (Nat × List Nat))
    (g' : List Nat) (segs' : List (Nat × List Nat))
    (leftCovered : ∀ a ∈ g, a ∈ ns) (rightCovered : ∀ a ∈ g', a ∈ ns)
    (leftGood : GoodSegments ns segs) (rightGood : GoodSegments ns segs')
    (leftSimple : MarkersSimple ns (g ++ flattenSegments segs))
    (rightSimple : MarkersSimple ns (g' ++ flattenSegments segs'))
    (obs : MarkedObservation ns (g ++ flattenSegments segs) (g' ++ flattenSegments segs')) :
    renderSegments ns segs = renderSegments ns segs' ∧
      renderedGap ns g (flattenSegments segs) = renderedGap ns g' (flattenSegments segs') := by
  induction segs generalizing g g' segs' with
  | nil =>
      cases segs' with
      | nil =>
          have key : SameOptionalKey g g' := by
            simpa only [flattenSegments,List.append_nil] using obs.1
          exact ⟨rfl,renderedGap_eq_of_observation ns g [] g' [] leftCovered rightCovered (sameGap_final key)⟩
      | cons seg rest =>
          rcases seg with ⟨t,h⟩
          have outside : t ∉ ns := (rightGood (t,h) (List.Mem.head _)).1
          have mem : t ∈ g' ++ flattenSegments ((t,h) :: rest) :=
            List.mem_append.mpr (Or.inr (List.Mem.head _))
          have source : t ∈ g := by
            have old := (optional_support obs.1 t).mpr mem
            simpa only [flattenSegments,List.append_nil] using old
          exact False.elim (outside (leftCovered t source))
  | cons seg rest ih =>
      rcases seg with ⟨s,h⟩
      have sl : s ∉ ns := (leftGood (s,h) (List.Mem.head _)).1
      have hl : ∀ a ∈ h, a ∈ ns := (leftGood (s,h) (List.Mem.head _)).2
      have gl : GoodSegments ns rest := fun seg mem => leftGood seg (List.Mem.tail _ mem)
      cases segs' with
      | nil =>
          have mem : s ∈ g ++ flattenSegments ((s,h) :: rest) :=
            List.mem_append.mpr (Or.inr (List.Mem.head _))
          have target : s ∈ g' := by
            have old := (optional_support obs.1 s).mp mem
            simpa only [flattenSegments,List.append_nil] using old
          exact False.elim (sl (rightCovered s target))
      | cons seg' rest' =>
          rcases seg' with ⟨t,h'⟩
          have tr : t ∉ ns := (rightGood (t,h') (List.Mem.head _)).1
          have hr : ∀ a ∈ h', a ∈ ns := (rightGood (t,h') (List.Mem.head _)).2
          have gr : GoodSegments ns rest' := fun seg mem => rightGood seg (List.Mem.tail _ mem)
          have heads : s = t := first_separator_eq ns g (h ++ flattenSegments rest)
            g' (h' ++ flattenSegments rest') s t leftCovered rightCovered sl tr rightSimple obs
          subst t
          have sourceMem : s ∈ g ++ flattenSegments ((s,h) :: rest) :=
            List.mem_append.mpr (Or.inr (List.Mem.head _))
          have targetMem : s ∈ g' ++ flattenSegments ((s,h') :: rest') :=
            List.mem_append.mpr (Or.inr (List.Mem.head _))
          have absentL : s ∉ h ++ flattenSegments rest :=
            simple_separator_absent g (h ++ flattenSegments rest) s (leftSimple s sourceMem sl)
          have absentR : s ∉ h' ++ flattenSegments rest' :=
            simple_separator_absent g' (h' ++ flattenSegments rest') s (rightSimple s targetMem tr)
          have tailObs : MarkedObservation ns (h ++ flattenSegments rest) (h' ++ flattenSegments rest') :=
            markedObservation_tail ns g (h ++ flattenSegments rest) g' (h' ++ flattenSegments rest') s
              leftCovered rightCovered sl absentL obs
          have simpleL : MarkersSimple ns (h ++ flattenSegments rest) := by
            apply markersSimple_suffix ns (g ++ [s])
            simpa only [flattenSegments,List.append_assoc,List.cons_append,List.nil_append] using leftSimple
          have simpleR : MarkersSimple ns (h' ++ flattenSegments rest') := by
            apply markersSimple_suffix ns (g' ++ [s])
            simpa only [flattenSegments,List.append_assoc,List.cons_append,List.nil_append] using rightSimple
          have later := ih h h' rest' hl hr gl gr simpleL simpleR tailObs
          have segments : renderSegments ns ((s,h) :: rest) = renderSegments ns ((s,h') :: rest') := by
            change s :: (renderedGap ns h (flattenSegments rest) ++ renderSegments ns rest) =
              s :: (renderedGap ns h' (flattenSegments rest') ++ renderSegments ns rest')
            rw [later.1,later.2]
          have currentObs : SameGapObservation g (s :: (h ++ flattenSegments rest))
              g' (s :: (h' ++ flattenSegments rest')) :=
            sameGap_before_separator s g (h ++ flattenSegments rest) g' (h' ++ flattenSegments rest')
              absentL absentR obs.1 (optional_support tailObs.1)
          exact ⟨segments,renderedGap_eq_of_observation ns g _ g' _ leftCovered rightCovered currentObs⟩

theorem splitGaps_renderSegments_eq (ns xs ys : List Nat)
    (leftSimple : MarkersSimple ns xs) (rightSimple : MarkersSimple ns ys)
    (obs : MarkedObservation ns xs ys) :
    renderSegments ns (splitGaps ns xs).2 = renderSegments ns (splitGaps ns ys).2 := by
  have source := splitGaps_join ns xs
  have target := splitGaps_join ns ys
  have left : MarkersSimple ns ((splitGaps ns xs).1 ++ flattenSegments (splitGaps ns xs).2) := by
    rw [source]; exact leftSimple
  have right : MarkersSimple ns ((splitGaps ns ys).1 ++ flattenSegments (splitGaps ns ys).2) := by
    rw [target]; exact rightSimple
  have actual : MarkedObservation ns ((splitGaps ns xs).1 ++ flattenSegments (splitGaps ns xs).2)
      ((splitGaps ns ys).1 ++ flattenSegments (splitGaps ns ys).2) := by
    rw [source,target]; exact obs
  exact (renderParts_eq ns (splitGaps ns xs).1 (splitGaps ns xs).2
    (splitGaps ns ys).1 (splitGaps ns ys).2 (splitGaps_first_covered ns xs)
    (splitGaps_first_covered ns ys) (splitGaps_good ns xs) (splitGaps_good ns ys) left right actual).1

end SemigroupBasis.CoRoots.Order6Day15.B16.Reach
