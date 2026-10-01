import SemigroupBasis.CoRoots.Order6Day15.B16.B16CanonicalGap

namespace SemigroupBasis.CoRoots.Order6Day15.B16.Reach

open SemigroupBasis.CoRoots.Order6Sunday.Msg0514RepairedSixteenLawFinite

def flattenSegments : List (Nat × List Nat) → List Nat
  | [] => []
  | (s,gap) :: rest => s :: (gap ++ flattenSegments rest)

/-- Each gap reads the original, still-unprocessed future suffix. -/
def renderSegments (ns : List Nat) : List (Nat × List Nat) → List Nat
  | [] => []
  | (s,gap) :: rest => s :: (renderedGap ns gap (flattenSegments rest) ++ renderSegments ns rest)

theorem render_segments_rel (ns pre : List Nat) (segments : List (Nat × List Nat))
    (covered : ∀ seg ∈ segments, ∀ a ∈ seg.2, a ∈ ns) :
    Rel (squares ns ++ (pre ++ flattenSegments segments))
      (squares ns ++ (pre ++ renderSegments ns segments)) := by
  induction segments generalizing pre with
  | nil => exact Rel.refl _
  | cons seg rest ih =>
      rcases seg with ⟨s,gap⟩
      have gapCovered : ∀ a ∈ gap, a ∈ ns := covered (s,gap) (List.Mem.head _)
      have restCovered : ∀ next ∈ rest, ∀ a ∈ next.2, a ∈ ns :=
        fun next hn => covered next (List.Mem.tail _ hn)
      have step := render_gap ns (pre ++ [s]) gap (flattenSegments rest) gapCovered
      have first : Rel (squares ns ++ (pre ++ flattenSegments ((s,gap) :: rest)))
          (squares ns ++ ((pre ++ s :: renderedGap ns gap (flattenSegments rest)) ++ flattenSegments rest)) := by
        simpa only [flattenSegments, List.append_assoc, List.cons_append, List.nil_append] using step
      have second : Rel (squares ns ++ ((pre ++ s :: renderedGap ns gap (flattenSegments rest)) ++ flattenSegments rest))
          (squares ns ++ ((pre ++ s :: renderedGap ns gap (flattenSegments rest)) ++ renderSegments ns rest)) :=
        ih (pre ++ s :: renderedGap ns gap (flattenSegments rest)) restCovered
      have combined := first.trans second
      simpa only [renderSegments, List.append_assoc, List.cons_append] using combined

theorem render_segments_framed (front ns pre : List Nat) (segments : List (Nat × List Nat))
    (covered : ∀ seg ∈ segments, ∀ a ∈ seg.2, a ∈ ns) :
    Rel (front ++ (squares ns ++ (pre ++ flattenSegments segments)))
      (front ++ (squares ns ++ (pre ++ renderSegments ns segments))) :=
  Rel.prependCtx front (render_segments_rel ns pre segments covered)

theorem render_segments_derives (u v : Word Nat) (front ns pre : List Nat)
    (segments : List (Nat × List Nat))
    (source : u.toList = front ++ (squares ns ++ (pre ++ flattenSegments segments)))
    (target : v.toList = front ++ (squares ns ++ (pre ++ renderSegments ns segments)))
    (covered : ∀ seg ∈ segments, ∀ a ∈ seg.2, a ∈ ns) : Derives basis u v := by
  have actual : Rel u.toList v.toList := by
    rw [source,target]
    exact render_segments_framed front ns pre segments covered
  exact Rel.toDerives actual

theorem reservoir_then_segments (front : List Nat) (a : Nat) (gap ns : List Nat)
    (segments : List (Nat × List Nat))
    (avoid : ∀ b ∈ ns, b ∉ front)
    (repeated : ∀ b ∈ ns, 2 ≤ (front ++ a :: (gap ++ flattenSegments segments)).count b)
    (firstCovered : ∀ b ∈ a :: gap, b ∈ ns)
    (laterCovered : ∀ seg ∈ segments, ∀ b ∈ seg.2, b ∈ ns) :
    Rel (front ++ a :: (gap ++ flattenSegments segments))
      (front ++ (squares ns ++ renderSegments ns segments)) := by
  have first : Rel (front ++ a :: (gap ++ flattenSegments segments))
      (front ++ (squares ns ++ flattenSegments segments)) :=
    reservoir_of_global_counts front a gap (flattenSegments segments) ns avoid repeated firstCovered
  have second : Rel (front ++ (squares ns ++ flattenSegments segments))
      (front ++ (squares ns ++ renderSegments ns segments)) :=
    render_segments_framed front ns [] segments laterCovered
  exact first.trans second

theorem reservoir_then_segments_derives (u v : Word Nat) (front : List Nat)
    (a : Nat) (gap ns : List Nat) (segments : List (Nat × List Nat))
    (source : u.toList = front ++ a :: (gap ++ flattenSegments segments))
    (target : v.toList = front ++ (squares ns ++ renderSegments ns segments))
    (avoid : ∀ b ∈ ns, b ∉ front) (repeated : ∀ b ∈ ns, 2 ≤ u.toList.count b)
    (firstCovered : ∀ b ∈ a :: gap, b ∈ ns)
    (laterCovered : ∀ seg ∈ segments, ∀ b ∈ seg.2, b ∈ ns) : Derives basis u v := by
  have counts : ∀ b ∈ ns, 2 ≤ (front ++ a :: (gap ++ flattenSegments segments)).count b := by
    intro b hb
    have actual := repeated b hb
    exact source ▸ actual
  have actual : Rel u.toList v.toList := by
    rw [source,target]
    exact reservoir_then_segments front a gap ns segments avoid counts firstCovered laterCovered
  exact Rel.toDerives actual

end SemigroupBasis.CoRoots.Order6Day15.B16.Reach
