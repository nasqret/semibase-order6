import SemigroupBasis.CoRoots.Order6SporadicSection18SaturationAnchors
import SemigroupBasis.CoRoots.Order6SporadicSection18RunSegmentation

/-! Positional endpoint anchors force equality of the first and last blocks
of a saturated canonical chain. No global-content-to-position inference occurs. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical

theorem rawRender_append (left right : List Slot) :
    rawRender (left ++ right) = rawRender left ++ rawRender right := by
  induction left with
  | nil => rfl
  | cons head tail ih => simp only [List.cons_append, rawRender, ih, List.append_assoc]

private theorem first_mem_left {first : Nat} {tail left right : List Nat}
    (shape : first :: tail = left ++ right) (leftNonempty : left ≠ []) : first ∈ left := by
  cases left with
  | nil => exact False.elim (leftNonempty rfl)
  | cons head rest =>
      change first :: tail = head :: (rest ++ right) at shape
      cases shape
      exact List.Mem.head _

private theorem last_mem_right {last : Nat} {body left right : List Nat}
    (shape : body ++ [last] = left ++ right) (rightNonempty : right ≠ []) : last ∈ right := by
  have reversed : last :: body.reverse = right.reverse ++ left.reverse := by
    simpa [List.reverse_append] using congrArg List.reverse shape
  have reversedNonempty : right.reverse ≠ [] := by simpa using rightNonempty
  have member := first_mem_left reversed reversedNonempty
  simpa using member

private theorem rawRender_first_letter (first : Slot) (rest : List Slot) (x : Nat) (tail : List Nat)
    (gapEmpty : first.gap = []) (blockNonempty : first.block ≠ [])
    (shape : rawRender (first :: rest) = x :: tail) : x ∈ first.block := by
  obtain ⟨head, more, blockShape⟩ := List.exists_cons_of_ne_nil blockNonempty
  have equation : head :: (more ++ rawRender rest) = x :: tail := by
    simpa [rawRender, gapEmpty, blockShape] using shape
  have equal := (List.cons.inj equation).1
  subst head
  rw [blockShape]
  exact List.Mem.head _

private theorem rawRender_last_letter (before : List Slot) (last : Slot) (x : Nat) (body : List Nat)
    (blockNonempty : last.block ≠ [])
    (shape : rawRender (before ++ [last]) = body ++ [x]) : x ∈ last.block := by
  have lastShape : body ++ [x] = (rawRender before ++ last.gap) ++ last.block := by
    simpa [rawRender_append, rawRender, List.append_assoc] using shape.symm
  exact last_mem_right lastShape blockNonempty

private theorem exists_last_slot (first : Slot) :
    ∀ rest : List Slot, ∃ before last, first :: rest = before ++ [last]
  | [] => ⟨[], first, rfl⟩
  | next :: rest => by
      obtain ⟨before, last, shape⟩ := exists_last_slot next rest
      exact ⟨first :: before, last, congrArg (List.cons first) shape⟩

theorem raw_closed_anchors {nonSimple : Nat → Prop} {first : Slot} {rest : List Slot}
    (runs : RawRuns nonSimple first rest) (gapEmpty : first.gap = [])
    (x : Nat) (interior : List Nat)
    (shape : rawRender (first :: rest) = x :: interior ++ [x]) :
    x ∈ first.block ∧ ∃ before last,
      first :: rest = before ++ [last] ∧ x ∈ last.block := by
  have headMember := rawRender_first_letter first rest x (interior ++ [x])
    gapEmpty runs.1.1 (by simpa only [List.cons_append] using shape)
  obtain ⟨before, last, lastShape⟩ := exists_last_slot first rest
  have lastMember : last ∈ first :: rest := by
    rw [lastShape]
    exact List.mem_append.mpr (Or.inr (List.Mem.head []))
  have lastNonempty := (runs.slotGood last lastMember).1
  have rendered : rawRender (before ++ [last]) = (x :: interior) ++ [x] := by
    rw [← lastShape]
    exact shape
  exact ⟨headMember, before, last, lastShape,
    rawRender_last_letter before last x (x :: interior) lastNonempty rendered⟩

theorem ChainExtends.closed_outer_blocks {nonSimple : Nat → Prop}
    {first next : Slot} {rest tail : List Slot} {alphabet : List Nat}
    (runs : RawRuns nonSimple first rest) (gapEmpty : first.gap = [])
    (x : Nat) (interior : List Nat)
    (shape : rawRender (first :: rest) = x :: interior ++ [x])
    (extended : ChainExtends (first :: rest) (next :: tail))
    (canonical : CanonicalChain alphabet (next :: tail)) (tailNonempty : tail ≠ []) :
    ∃ middle last, tail = middle ++ [last] ∧ next.block = last.block := by
  obtain ⟨headMember, before, last, lastShape, lastMember⟩ :=
    raw_closed_anchors runs gapEmpty x interior shape
  have sourceLast : ChainExtends (before ++ [last]) (next :: tail) := by
    rw [← lastShape]
    exact extended
  obtain ⟨outBefore, outLast, outShape, lastExtended⟩ := sourceLast.last before last
  have inNext : x ∈ next.block := extended.head.2 x headMember
  have inLast : x ∈ outLast.block := lastExtended.2 x lastMember
  cases outBefore with
  | nil =>
      have only : next :: tail = [outLast] := by simpa using outShape
      exact False.elim (tailNonempty (List.cons.inj only).2)
  | cons outHead middle =>
      have tailShape : tail = middle ++ [outLast] := (List.cons.inj outShape).2
      refine ⟨middle, outLast, tailShape, ?_⟩
      apply canonical.2.1 [] middle [] next.gap outLast.gap next.block outLast.block x
      · rw [tailShape]
        rfl
      · exact inNext
      · exact inLast

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.rawRender_append
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.raw_closed_anchors
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.ChainExtends.closed_outer_blocks

end SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical
