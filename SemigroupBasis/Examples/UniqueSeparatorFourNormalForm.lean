import SemigroupBasis.Examples.UniqueSeparatorFour

namespace SemigroupBasis.Examples

/-- Scan a word from left to right, deleting exactly those occurrences that
have already appeared and will appear again. Thus the surviving occurrences
of each letter are its first and last occurrences. -/
def uniqueSeparatorEndpointCapAux (seen : List Nat) :
    List Nat → List Nat
  | [] => []
  | x :: xs =>
      if x ∈ seen ∧ x ∈ xs then
        uniqueSeparatorEndpointCapAux (x :: seen) xs
      else
        x :: uniqueSeparatorEndpointCapAux (x :: seen) xs

/-- Retain the first and last occurrence of every letter, retaining one
occurrence when the letter is globally linear. -/
def uniqueSeparatorEndpointCap (xs : List Nat) : List Nat :=
  uniqueSeparatorEndpointCapAux [] xs

@[simp]
theorem uniqueSeparatorEndpointCapAux_nil (seen : List Nat) :
    uniqueSeparatorEndpointCapAux seen [] = [] :=
  rfl

theorem uniqueSeparatorEndpointCapAux_sublist (seen : List Nat) :
    ∀ xs, List.Sublist (uniqueSeparatorEndpointCapAux seen xs) xs
  | [] => List.Sublist.slnil
  | x :: xs => by
      simp only [uniqueSeparatorEndpointCapAux]
      split
      · exact List.Sublist.cons x
          (uniqueSeparatorEndpointCapAux_sublist (x :: seen) xs)
      · exact List.Sublist.cons₂ x
          (uniqueSeparatorEndpointCapAux_sublist (x :: seen) xs)

theorem uniqueSeparatorEndpointCap_sublist (xs : List Nat) :
    List.Sublist (uniqueSeparatorEndpointCap xs) xs :=
  uniqueSeparatorEndpointCapAux_sublist [] xs

theorem uniqueSeparatorEndpointCapAux_mem_iff
    (seen : List Nat) (z : Nat) :
    ∀ xs,
      z ∈ uniqueSeparatorEndpointCapAux seen xs ↔ z ∈ xs
  | [] => by simp
  | x :: xs => by
      by_cases hmiddle : x ∈ seen ∧ x ∈ xs
      · rw [uniqueSeparatorEndpointCapAux]
        simp only [if_pos hmiddle]
        rw [uniqueSeparatorEndpointCapAux_mem_iff (x :: seen) z xs]
        constructor
        · exact List.mem_cons_of_mem x
        · intro hz
          rcases List.mem_cons.mp hz with hzx | hz
          · simpa [hzx] using hmiddle.2
          · exact hz
      · rw [uniqueSeparatorEndpointCapAux]
        simp only [if_neg hmiddle, List.mem_cons]
        rw [uniqueSeparatorEndpointCapAux_mem_iff (x :: seen) z xs]

theorem uniqueSeparatorEndpointCap_mem_iff (z : Nat) (xs : List Nat) :
    z ∈ uniqueSeparatorEndpointCap xs ↔ z ∈ xs :=
  uniqueSeparatorEndpointCapAux_mem_iff [] z xs

/-- The cap has the exact expected multiplicity. A previously seen letter
contributes only its last remaining occurrence; a fresh letter contributes
both endpoints when they are distinct. -/
theorem uniqueSeparatorEndpointCapAux_count
    (seen : List Nat) (z : Nat) :
    ∀ xs,
      (uniqueSeparatorEndpointCapAux seen xs).count z =
        if z ∈ seen then Nat.min 1 (xs.count z)
        else Nat.min 2 (xs.count z)
  | [] => by simp
  | x :: xs => by
      by_cases hxz : x = z
      · subst x
        by_cases hzSeen : z ∈ seen
        · by_cases hzTail : z ∈ xs
          · have hzPositive : 1 ≤ xs.count z :=
              List.one_le_count_iff.mpr hzTail
            rw [uniqueSeparatorEndpointCapAux]
            simp only [hzSeen, hzTail, and_self, if_pos,
              uniqueSeparatorEndpointCapAux_count (z :: seen) z xs]
            simp only [List.mem_cons, true_or, if_true,
              List.count_cons_self]
            have hleft :
                Nat.min 1 (xs.count z) = 1 :=
              Nat.min_eq_left hzPositive
            have hright :
                Nat.min 1 (xs.count z + 1) = 1 :=
              Nat.min_eq_left (by omega)
            rw [hleft, hright]
          · have hzCount : xs.count z = 0 :=
              List.count_eq_zero.mpr hzTail
            rw [uniqueSeparatorEndpointCapAux]
            simp only [hzSeen, hzTail, and_false, if_false,
              List.count_cons_self,
              uniqueSeparatorEndpointCapAux_count (z :: seen) z xs,
              List.mem_cons, true_or, if_true, hzCount]
            decide
        · by_cases hzTail : z ∈ xs
          · have hzPositive : 1 ≤ xs.count z :=
              List.one_le_count_iff.mpr hzTail
            rw [uniqueSeparatorEndpointCapAux]
            simp only [hzSeen, false_and, if_false,
              List.count_cons_self,
              uniqueSeparatorEndpointCapAux_count (z :: seen) z xs,
              List.mem_cons, true_or, if_true]
            have hleft :
                Nat.min 1 (xs.count z) = 1 :=
              Nat.min_eq_left hzPositive
            have hright :
                Nat.min 2 (xs.count z + 1) = 2 :=
              Nat.min_eq_left (by omega)
            rw [hleft, hright]
          · have hzCount : xs.count z = 0 :=
              List.count_eq_zero.mpr hzTail
            rw [uniqueSeparatorEndpointCapAux]
            simp only [hzSeen, false_and, if_false,
              List.count_cons_self,
              uniqueSeparatorEndpointCapAux_count (z :: seen) z xs,
              List.mem_cons, true_or, if_true, hzCount]
            decide
      · by_cases hmiddle : x ∈ seen ∧ x ∈ xs
        · rw [uniqueSeparatorEndpointCapAux]
          simp only [if_pos hmiddle,
            uniqueSeparatorEndpointCapAux_count (x :: seen) z xs]
          simp [hxz, Ne.symm hxz]
        · rw [uniqueSeparatorEndpointCapAux]
          simp only [if_neg hmiddle, List.count_cons_of_ne hxz,
            uniqueSeparatorEndpointCapAux_count (x :: seen) z xs]
          simp [Ne.symm hxz]

theorem uniqueSeparatorEndpointCap_count (z : Nat) (xs : List Nat) :
    (uniqueSeparatorEndpointCap xs).count z =
      Nat.min 2 (xs.count z) := by
  simpa [uniqueSeparatorEndpointCap] using
    uniqueSeparatorEndpointCapAux_count [] z xs

theorem uniqueSeparatorEndpointCap_count_le_two
    (z : Nat) (xs : List Nat) :
    (uniqueSeparatorEndpointCap xs).count z ≤ 2 := by
  rw [uniqueSeparatorEndpointCap_count]
  exact Nat.min_le_left _ _

/-- Every letter occurs at most twice. -/
def UniqueSeparatorTwoLimited (xs : List Nat) : Prop :=
  ∀ z, xs.count z ≤ 2

theorem uniqueSeparatorEndpointCap_twoLimited (xs : List Nat) :
    UniqueSeparatorTwoLimited (uniqueSeparatorEndpointCap xs) :=
  fun z => uniqueSeparatorEndpointCap_count_le_two z xs

theorem uniqueSeparatorEndpointCap_count_eq_zero_iff
    (z : Nat) (xs : List Nat) :
    (uniqueSeparatorEndpointCap xs).count z = 0 ↔ xs.count z = 0 := by
  rw [uniqueSeparatorEndpointCap_count]
  simp only [Nat.min_def]
  split <;> omega

theorem uniqueSeparatorEndpointCap_count_eq_one_iff
    (z : Nat) (xs : List Nat) :
    (uniqueSeparatorEndpointCap xs).count z = 1 ↔ xs.count z = 1 := by
  rw [uniqueSeparatorEndpointCap_count]
  simp only [Nat.min_def]
  split <;> omega

theorem uniqueSeparatorEndpointCap_count_eq_two_iff
    (z : Nat) (xs : List Nat) :
    (uniqueSeparatorEndpointCap xs).count z = 2 ↔ 2 ≤ xs.count z := by
  rw [uniqueSeparatorEndpointCap_count]
  simp only [Nat.min_def]
  split <;> omega

/-- A square-block segment consists of a block of globally quadratic letters,
followed by an optional globally linear separator. -/
structure UniqueSeparatorSquareSegment where
  quadratic : List Nat
  separator : Option Nat
deriving DecidableEq, Repr

def UniqueSeparatorSquareSegment.render
    (segment : UniqueSeparatorSquareSegment) : List Nat :=
  segment.quadratic ++ segment.separator.toList

def uniqueSeparatorRenderSquareSegments
    (segments : List UniqueSeparatorSquareSegment) : List Nat :=
  segments.flatMap UniqueSeparatorSquareSegment.render

private def uniqueSeparatorPrependQuadratic
    (x : Nat) :
    List UniqueSeparatorSquareSegment →
      List UniqueSeparatorSquareSegment
  | [] => [⟨[x], none⟩]
  | segment :: segments =>
      ⟨x :: segment.quadratic, segment.separator⟩ :: segments

/-- Split a list at letters that occur exactly once in `whole`. The first
argument remains fixed while the second argument is structurally consumed. -/
def uniqueSeparatorSplitLinearAux (whole : List Nat) :
    List Nat → List UniqueSeparatorSquareSegment
  | [] => [⟨[], none⟩]
  | x :: xs =>
      if whole.count x = 1 then
        ⟨[], some x⟩ :: uniqueSeparatorSplitLinearAux whole xs
      else
        uniqueSeparatorPrependQuadratic x
          (uniqueSeparatorSplitLinearAux whole xs)

/-- Deterministically split a capped word at its globally linear letters. -/
def uniqueSeparatorSplitLinear
    (xs : List Nat) : List UniqueSeparatorSquareSegment :=
  uniqueSeparatorSplitLinearAux xs xs

private theorem uniqueSeparatorRender_prependQuadratic
    (x : Nat) (segments : List UniqueSeparatorSquareSegment) :
    uniqueSeparatorRenderSquareSegments
        (uniqueSeparatorPrependQuadratic x segments) =
      x :: uniqueSeparatorRenderSquareSegments segments := by
  cases segments with
  | nil =>
      simp [uniqueSeparatorPrependQuadratic,
        uniqueSeparatorRenderSquareSegments,
        UniqueSeparatorSquareSegment.render]
  | cons segment segments =>
      cases segment
      simp [uniqueSeparatorPrependQuadratic,
        uniqueSeparatorRenderSquareSegments,
        UniqueSeparatorSquareSegment.render,
        List.append_assoc]

theorem uniqueSeparatorRender_splitLinearAux
    (whole : List Nat) :
    ∀ xs,
      uniqueSeparatorRenderSquareSegments
          (uniqueSeparatorSplitLinearAux whole xs) = xs
  | [] => by
      simp [uniqueSeparatorSplitLinearAux,
        uniqueSeparatorRenderSquareSegments,
        UniqueSeparatorSquareSegment.render]
  | x :: xs => by
      rw [uniqueSeparatorSplitLinearAux]
      split
      · simp only [uniqueSeparatorRenderSquareSegments,
          List.flatMap_cons, UniqueSeparatorSquareSegment.render,
          Option.toList_some, List.nil_append, List.singleton_append]
        change
          x :: uniqueSeparatorRenderSquareSegments
              (uniqueSeparatorSplitLinearAux whole xs) =
            x :: xs
        rw [uniqueSeparatorRender_splitLinearAux whole xs]
      · rw [uniqueSeparatorRender_prependQuadratic,
          uniqueSeparatorRender_splitLinearAux whole xs]

theorem uniqueSeparatorRender_splitLinear (xs : List Nat) :
    uniqueSeparatorRenderSquareSegments
        (uniqueSeparatorSplitLinear xs) = xs :=
  uniqueSeparatorRender_splitLinearAux xs xs

def UniqueSeparatorSquareSegment.ValidFor
    (whole : List Nat) (segment : UniqueSeparatorSquareSegment) : Prop :=
  (∀ x ∈ segment.quadratic, whole.count x ≠ 1) ∧
    (∀ x, segment.separator = some x → whole.count x = 1)

private theorem uniqueSeparatorPrependQuadratic_valid
    (whole : List Nat) (x : Nat)
    (hx : whole.count x ≠ 1)
    (segments : List UniqueSeparatorSquareSegment)
    (valid :
      ∀ segment ∈ segments,
        UniqueSeparatorSquareSegment.ValidFor whole segment) :
    ∀ segment ∈ uniqueSeparatorPrependQuadratic x segments,
      UniqueSeparatorSquareSegment.ValidFor whole segment := by
  cases segments with
  | nil =>
      intro segment hsegment
      simp only [uniqueSeparatorPrependQuadratic, List.mem_cons,
        List.not_mem_nil, or_false] at hsegment
      subst segment
      exact ⟨by simpa using hx, by simp⟩
  | cons first rest =>
      intro segment hsegment
      simp only [uniqueSeparatorPrependQuadratic, List.mem_cons] at hsegment
      rcases hsegment with rfl | hsegment
      · have firstValid := valid first (List.Mem.head rest)
        exact ⟨by
          intro z hz
          change z ∈ x :: first.quadratic at hz
          rcases List.mem_cons.mp hz with hzx | hz
          · subst z
            exact hx
          · exact firstValid.1 z hz,
          firstValid.2⟩
      · exact valid segment (List.Mem.tail first hsegment)

theorem uniqueSeparatorSplitLinearAux_valid
    (whole : List Nat) :
    ∀ xs segment,
      segment ∈ uniqueSeparatorSplitLinearAux whole xs →
        UniqueSeparatorSquareSegment.ValidFor whole segment
  | [], segment, hsegment => by
      simp only [uniqueSeparatorSplitLinearAux, List.mem_cons,
        List.not_mem_nil, or_false] at hsegment
      subst segment
      exact ⟨by simp, by simp⟩
  | x :: xs, segment, hsegment => by
      by_cases hx : whole.count x = 1
      · rw [uniqueSeparatorSplitLinearAux, if_pos hx] at hsegment
        rcases List.mem_cons.mp hsegment with hfirst | hsegment
        · subst segment
          exact ⟨by simp, by
            intro z hz
            have hxz : x = z := by
              apply Option.some.inj
              simpa using hz
            simpa [hxz] using hx⟩
        · exact uniqueSeparatorSplitLinearAux_valid whole xs segment hsegment
      · rw [uniqueSeparatorSplitLinearAux, if_neg hx] at hsegment
        exact uniqueSeparatorPrependQuadratic_valid whole x hx
          (uniqueSeparatorSplitLinearAux whole xs)
          (fun candidate hcandidate =>
            uniqueSeparatorSplitLinearAux_valid
              whole xs candidate hcandidate)
          segment hsegment

theorem uniqueSeparatorSplitLinear_valid
    (xs : List Nat) (segment : UniqueSeparatorSquareSegment)
    (hsegment : segment ∈ uniqueSeparatorSplitLinear xs) :
    UniqueSeparatorSquareSegment.ValidFor xs segment :=
  uniqueSeparatorSplitLinearAux_valid xs xs segment hsegment

theorem uniqueSeparatorSplitLinear_quadratic_count_two
    (xs : List Nat) (limited : UniqueSeparatorTwoLimited xs)
    (segment : UniqueSeparatorSquareSegment)
    (hsegment : segment ∈ uniqueSeparatorSplitLinear xs)
    (z : Nat) (hz : z ∈ segment.quadratic) :
    xs.count z = 2 := by
  have valid := uniqueSeparatorSplitLinear_valid xs segment hsegment
  have zInSegment : z ∈ segment.render := by
    simp [UniqueSeparatorSquareSegment.render, hz]
  have zInRendered :
      z ∈ uniqueSeparatorRenderSquareSegments
        (uniqueSeparatorSplitLinear xs) := by
    simp only [uniqueSeparatorRenderSquareSegments, List.mem_flatMap]
    exact ⟨segment, hsegment, zInSegment⟩
  have zInXs : z ∈ xs := by
    rw [← uniqueSeparatorRender_splitLinear xs]
    exact zInRendered
  have positive : 1 ≤ xs.count z :=
    List.one_le_count_iff.mpr zInXs
  have notLinear : xs.count z ≠ 1 :=
    valid.1 z hz
  have atMostTwo : xs.count z ≤ 2 :=
    limited z
  exact by omega

theorem uniqueSeparatorSplitLinear_separator_count_one
    (xs : List Nat) (segment : UniqueSeparatorSquareSegment)
    (hsegment : segment ∈ uniqueSeparatorSplitLinear xs)
    (z : Nat) (hz : segment.separator = some z) :
    xs.count z = 1 :=
  (uniqueSeparatorSplitLinear_valid xs segment hsegment).2 z hz

theorem uniqueSeparatorSplitEndpointCap_quadratic_count_two
    (xs : List Nat) (segment : UniqueSeparatorSquareSegment)
    (hsegment :
      segment ∈
        uniqueSeparatorSplitLinear
          (uniqueSeparatorEndpointCap xs))
    (z : Nat) (hz : z ∈ segment.quadratic) :
    (uniqueSeparatorEndpointCap xs).count z = 2 :=
  uniqueSeparatorSplitLinear_quadratic_count_two
    (uniqueSeparatorEndpointCap xs)
    (uniqueSeparatorEndpointCap_twoLimited xs)
    segment hsegment z hz

theorem uniqueSeparatorSplitEndpointCap_separator_count_one
    (xs : List Nat) (segment : UniqueSeparatorSquareSegment)
    (hsegment :
      segment ∈
        uniqueSeparatorSplitLinear
          (uniqueSeparatorEndpointCap xs))
    (z : Nat) (hz : segment.separator = some z) :
    (uniqueSeparatorEndpointCap xs).count z = 1 :=
  uniqueSeparatorSplitLinear_separator_count_one
    (uniqueSeparatorEndpointCap xs) segment hsegment z hz

end SemigroupBasis.Examples
