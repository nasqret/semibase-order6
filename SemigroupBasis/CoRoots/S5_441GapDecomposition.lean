import SemigroupBasis.CoRoots.S5_441Invariant
import SemigroupBasis.Examples.UniqueSeparatorFourInvariant

namespace SemigroupBasis.CoRoots.S5_441

open SemigroupBasis.Examples

/-- Executable support-disjointness test used by the exact-cut scanner. -/
def exactCutSupportsDisjointBool
    (left right : List Nat) : Bool :=
  left.all fun letter => decide (letter ∉ right)

theorem exactCutSupportsDisjointBool_eq_true_iff
    {left right : List Nat} :
    exactCutSupportsDisjointBool left right = true ↔
      UniqueSeparatorFourSupportsDisjoint left right := by
  rw [exactCutSupportsDisjointBool, List.all_eq_true]
  constructor
  · intro tested letter member
    exact of_decide_eq_true (tested letter member)
  · intro disjoint letter member
    exact decide_eq_true (disjoint letter member)

/-- A gap followed by an optional exact-cut separator. -/
structure ExactCutSegment where
  gap : List Nat
  separator : Option Nat
deriving DecidableEq, Repr

def ExactCutSegment.render
    (segment : ExactCutSegment) : List Nat :=
  segment.gap ++ segment.separator.toList

def renderExactCutSegments
    (segments : List ExactCutSegment) : List Nat :=
  segments.flatMap ExactCutSegment.render

@[simp]
theorem renderExactCutSegments_nil :
    renderExactCutSegments [] = [] :=
  rfl

@[simp]
theorem renderExactCutSegments_cons
    (segment : ExactCutSegment) (segments : List ExactCutSegment) :
    renderExactCutSegments (segment :: segments) =
      segment.render ++ renderExactCutSegments segments :=
  rfl

/-- Scan left to right while retaining the original word, the already
rendered prefix, the current gap, and the unprocessed suffix. A separator is
emitted exactly when it is globally unique and the full left prefix is
support-disjoint from the remaining suffix. -/
def exactCutScanner
    (whole renderedPrefix gap : List Nat) :
    List Nat → List ExactCutSegment
  | [] => [⟨gap, none⟩]
  | separator :: remaining =>
      if decide (whole.count separator = 1) &&
          exactCutSupportsDisjointBool
            (renderedPrefix ++ gap) remaining then
        ⟨gap, some separator⟩ ::
          exactCutScanner whole
            (renderedPrefix ++ gap ++ [separator]) [] remaining
      else
        exactCutScanner whole renderedPrefix
          (gap ++ [separator]) remaining

/-- Deterministically decompose a list at every exact cut accepted by the
left-to-right scanner. -/
def exactCutDecomposition
    (letters : List Nat) : List ExactCutSegment :=
  exactCutScanner letters [] [] letters

theorem render_exactCutScanner
    (whole renderedPrefix gap remaining : List Nat) :
    renderExactCutSegments
        (exactCutScanner whole renderedPrefix gap remaining) =
      gap ++ remaining := by
  induction remaining generalizing renderedPrefix gap with
  | nil =>
      simp [exactCutScanner, ExactCutSegment.render]
  | cons separator remaining ih =>
      simp only [exactCutScanner]
      split
      · simp only [renderExactCutSegments_cons,
          ExactCutSegment.render, Option.toList_some]
        rw [ih]
        simp [List.append_assoc]
      · rw [ih]
        simp [List.append_assoc]

theorem render_exactCutDecomposition
    (letters : List Nat) :
    renderExactCutSegments (exactCutDecomposition letters) =
      letters := by
  simpa [exactCutDecomposition] using
    render_exactCutScanner letters [] [] letters

/-- Every separator emitted by a scanner call is an exact cut of `whole`.
The displayed left and right factors are exactly the rendered scanner prefix
and suffix around that segment. -/
theorem exactCutScanner_separator_exactCut
    {whole renderedPrefix gap remaining : List Nat}
    (whole_eq : whole = renderedPrefix ++ gap ++ remaining)
    {before after : List ExactCutSegment}
    {segment : ExactCutSegment} {separator : Nat}
    (scan_eq :
      exactCutScanner whole renderedPrefix gap remaining =
        before ++ segment :: after)
    (separator_eq : segment.separator = some separator) :
    UniqueSeparatorFourExactCut whole
      (renderedPrefix ++
        renderExactCutSegments before ++ segment.gap)
      separator
      (renderExactCutSegments after) := by
  induction remaining generalizing
      renderedPrefix gap before after segment separator with
  | nil =>
      have segmentMember :
          segment ∈
            exactCutScanner whole renderedPrefix gap [] := by
        rw [scan_eq]
        simp
      have segmentEq : segment = ⟨gap, none⟩ := by
        simpa [exactCutScanner] using segmentMember
      subst segment
      simp at separator_eq
  | cons candidate remaining ih =>
      simp only [exactCutScanner] at scan_eq
      split at scan_eq <;> rename_i cutCondition
      · cases before with
        | nil =>
            simp only [List.nil_append, List.cons.injEq] at scan_eq
            rcases scan_eq with ⟨segmentEq, afterEq⟩
            subst segment
            subst after
            change some candidate = some separator at separator_eq
            have candidateEq : candidate = separator :=
              Option.some.inj separator_eq
            subst separator
            simp only [Bool.and_eq_true] at cutCondition
            rcases cutCondition with ⟨countTest, disjointTest⟩
            have countOne : whole.count candidate = 1 :=
              of_decide_eq_true countTest
            have disjoint :
                UniqueSeparatorFourSupportsDisjoint
                  (renderedPrefix ++ gap) remaining :=
              exactCutSupportsDisjointBool_eq_true_iff.mp
                disjointTest
            have cut :
                UniqueSeparatorFourExactCut whole
                  (renderedPrefix ++ gap) candidate remaining := by
              refine ⟨?_, countOne, disjoint⟩
              simpa [List.append_assoc] using whole_eq
            have renderedAfter :
                renderExactCutSegments
                    (exactCutScanner whole
                      (renderedPrefix ++ gap ++ [candidate])
                      [] remaining) =
                  remaining := by
              simpa using
                render_exactCutScanner whole
                  (renderedPrefix ++ gap ++ [candidate])
                  [] remaining
            rw [renderedAfter]
            simpa using cut
        | cons beforeHead beforeTail =>
            simp only [List.cons_append, List.cons.injEq] at scan_eq
            rcases scan_eq with ⟨beforeHeadEq, tailEq⟩
            subst beforeHead
            have nextWholeEq :
                whole =
                  (renderedPrefix ++ gap ++ [candidate]) ++
                    [] ++ remaining := by
              simpa [List.append_assoc] using whole_eq
            have recursiveCut :=
              ih
                (renderedPrefix :=
                  renderedPrefix ++ gap ++ [candidate])
                (gap := [])
                (before := beforeTail)
                (after := after)
                (segment := segment)
                (separator := separator)
                nextWholeEq tailEq separator_eq
            simpa [ExactCutSegment.render, List.append_assoc] using
              recursiveCut
      · have nextWholeEq :
            whole =
              renderedPrefix ++ (gap ++ [candidate]) ++
                remaining := by
          simpa [List.append_assoc] using whole_eq
        exact
          ih
            (renderedPrefix := renderedPrefix)
            (gap := gap ++ [candidate])
            (before := before)
            (after := after)
            (segment := segment)
            (separator := separator)
            nextWholeEq scan_eq separator_eq

/-- Every `some separator` segment in the deterministic decomposition gives
the corresponding genuine exact cut of the original list. -/
theorem exactCutDecomposition_separator_exactCut
    {letters : List Nat}
    {before after : List ExactCutSegment}
    {segment : ExactCutSegment} {separator : Nat}
    (decomposition_eq :
      exactCutDecomposition letters =
        before ++ segment :: after)
    (separator_eq : segment.separator = some separator) :
    UniqueSeparatorFourExactCut letters
      (renderExactCutSegments before ++ segment.gap)
      separator
      (renderExactCutSegments after) := by
  have scan_eq :
      exactCutScanner letters [] [] letters =
        before ++ segment :: after := by
    simpa [exactCutDecomposition] using decomposition_eq
  have cut :=
    exactCutScanner_separator_exactCut
      (whole := letters)
      (renderedPrefix := [])
      (gap := [])
      (remaining := letters)
      (before := before)
      (after := after)
      (segment := segment)
      (separator := separator)
      (by simp) scan_eq separator_eq
  simpa using cut

end SemigroupBasis.CoRoots.S5_441
