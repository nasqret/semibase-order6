import SemigroupBasis.Examples.UniqueSeparatorFourListDerives
import SemigroupBasis.Examples.UniqueSeparatorFourNormalForm

namespace SemigroupBasis.Examples

open SemigroupBasis

/-- Whether the supports of two lists intersect. -/
def uniqueSeparatorSupportsIntersect
    (left right : List Nat) : Bool :=
  left.any fun z => decide (z ∈ right)

theorem uniqueSeparatorSupportsIntersect_eq_true_iff
    (left right : List Nat) :
    uniqueSeparatorSupportsIntersect left right = true ↔
      ∃ z, z ∈ left ∧ z ∈ right := by
  induction left with
  | nil =>
      simp [uniqueSeparatorSupportsIntersect]
  | cons x xs ih =>
      simp only [uniqueSeparatorSupportsIntersect, List.any_cons,
        Bool.or_eq_true, decide_eq_true_eq, List.mem_cons]
      have ih' :
          (xs.any fun z => decide (z ∈ right)) = true ↔
            ∃ z, z ∈ xs ∧ z ∈ right := by
        change
          uniqueSeparatorSupportsIntersect xs right = true ↔
            ∃ z, z ∈ xs ∧ z ∈ right
        exact ih
      rw [ih']
      constructor
      · rintro (hx | ⟨z, hzLeft, hzRight⟩)
        · exact ⟨x, Or.inl rfl, hx⟩
        · exact ⟨z, Or.inr hzLeft, hzRight⟩
      · rintro ⟨z, (rfl | hzLeft), hzRight⟩
        · exact Or.inl hzRight
        · exact Or.inr ⟨z, hzLeft, hzRight⟩

theorem uniqueSeparatorSupportsIntersect_eq_false_iff
    (left right : List Nat) :
    uniqueSeparatorSupportsIntersect left right = false ↔
      ∀ z, z ∈ left → z ∈ right → False := by
  constructor
  · intro noIntersection z zLeft zRight
    have intersection :
        uniqueSeparatorSupportsIntersect left right = true :=
      (uniqueSeparatorSupportsIntersect_eq_true_iff
        left right).mpr ⟨z, zLeft, zRight⟩
    rw [noIntersection] at intersection
    contradiction
  · intro disjoint
    cases intersectionShape :
        uniqueSeparatorSupportsIntersect left right with
    | false =>
        rfl
    | true =>
        rcases
            (uniqueSeparatorSupportsIntersect_eq_true_iff
              left right).mp intersectionShape with
          ⟨z, zLeft, zRight⟩
        exact False.elim (disjoint z zLeft zRight)

/-- Scan for the unique occurrence of `x`, remembering the prefix already
passed. At that occurrence, test whether some letter occurs on both sides. -/
def uniqueSeparatorEnclosedAux (x : Nat) (seen : List Nat) :
    List Nat → Bool
  | [] => false
  | y :: ys =>
      if y = x then
        uniqueSeparatorSupportsIntersect seen ys
      else
        uniqueSeparatorEnclosedAux x (seen ++ [y]) ys

/-- A globally linear letter is enclosed when some other letter occurs both
before and after its unique occurrence. -/
def uniqueSeparatorEnclosed (letters : List Nat) (x : Nat) : Bool :=
  uniqueSeparatorEnclosedAux x [] letters

theorem uniqueSeparatorEnclosedAux_split
    (x : Nat) (seen before after : List Nat)
    (notBefore : x ∉ before) :
    uniqueSeparatorEnclosedAux x seen (before ++ x :: after) =
      uniqueSeparatorSupportsIntersect (seen ++ before) after := by
  induction before generalizing seen with
  | nil =>
      simp [uniqueSeparatorEnclosedAux]
  | cons y ys ih =>
      have yNe : y ≠ x := by
        intro equality
        apply notBefore
        simp [equality]
      have xNotYs : x ∉ ys := by
        intro member
        exact notBefore (List.mem_cons_of_mem y member)
      simp only [List.cons_append, uniqueSeparatorEnclosedAux, if_neg yNe]
      rw [ih (seen := seen ++ [y]) xNotYs]
      simp [List.append_assoc]

theorem uniqueSeparatorEnclosed_split
    {letters before after : List Nat} {x : Nat}
    (shape : letters = before ++ x :: after)
    (notBefore : x ∉ before) :
    uniqueSeparatorEnclosed letters x =
      uniqueSeparatorSupportsIntersect before after := by
  subst letters
  simpa [uniqueSeparatorEnclosed] using
    uniqueSeparatorEnclosedAux_split x [] before after notBefore

/-- Edmunds' `L₄` saturation criterion. A letter is duplicated exactly when
it is globally linear and lies strictly inside the two occurrences of some
quadratic letter. -/
def UniqueSeparatorNeedsSaturation
    (whole : List Nat) (x : Nat) : Prop :=
  whole.count x = 1 ∧ uniqueSeparatorEnclosed whole x = true

instance uniqueSeparatorNeedsSaturationDecidable
    (whole : List Nat) (x : Nat) :
    Decidable (UniqueSeparatorNeedsSaturation whole x) := by
  unfold UniqueSeparatorNeedsSaturation
  infer_instance

/-- The local image used by saturation: retain the letter, adding one adjacent
copy precisely when Edmunds' `L₄` criterion applies. -/
def uniqueSeparatorSaturationImage
    (whole : List Nat) (x : Nat) : List Nat :=
  if UniqueSeparatorNeedsSaturation whole x then [x, x] else [x]

/-- Saturate a selected part while testing global multiplicities and
enclosure in the fixed whole list. -/
def uniqueSeparatorSaturatePart
    (whole part : List Nat) : List Nat :=
  part.flatMap (uniqueSeparatorSaturationImage whole)

/-- Deterministically duplicate every globally linear letter enclosed by a
quadratic letter. -/
def uniqueSeparatorSaturate (letters : List Nat) : List Nat :=
  uniqueSeparatorSaturatePart letters letters

theorem uniqueSeparatorSaturationImage_mem_iff
    (whole : List Nat) (x z : Nat) :
    z ∈ uniqueSeparatorSaturationImage whole x ↔ z = x := by
  by_cases needs : UniqueSeparatorNeedsSaturation whole x
  · simp [uniqueSeparatorSaturationImage, needs]
  · simp [uniqueSeparatorSaturationImage, needs]

theorem uniqueSeparatorSaturatePart_mem_iff
    (whole part : List Nat) (z : Nat) :
    z ∈ uniqueSeparatorSaturatePart whole part ↔ z ∈ part := by
  simp only [uniqueSeparatorSaturatePart, List.mem_flatMap]
  constructor
  · rintro ⟨x, xMember, zMember⟩
    exact (uniqueSeparatorSaturationImage_mem_iff whole x z).mp zMember ▸
      xMember
  · intro zMember
    exact ⟨z, zMember,
      (uniqueSeparatorSaturationImage_mem_iff whole z z).mpr rfl⟩

theorem uniqueSeparatorSaturate_mem_iff
    (letters : List Nat) (z : Nat) :
    z ∈ uniqueSeparatorSaturate letters ↔ z ∈ letters :=
  uniqueSeparatorSaturatePart_mem_iff letters letters z

theorem uniqueSeparatorSaturatePart_count
    (whole part : List Nat) (z : Nat) :
    (uniqueSeparatorSaturatePart whole part).count z =
      if UniqueSeparatorNeedsSaturation whole z then
        2 * part.count z
      else
        part.count z := by
  induction part with
  | nil =>
      simp [uniqueSeparatorSaturatePart]
  | cons x xs ih =>
      change
        (uniqueSeparatorSaturationImage whole x ++
            uniqueSeparatorSaturatePart whole xs).count z =
          _
      rw [List.count_append, ih]
      by_cases same : x = z
      · subst x
        by_cases needs : UniqueSeparatorNeedsSaturation whole z
        · simp [uniqueSeparatorSaturationImage, needs]
          omega
        · simp [uniqueSeparatorSaturationImage, needs]
          omega
      · by_cases xNeeds : UniqueSeparatorNeedsSaturation whole x
        · by_cases zNeeds : UniqueSeparatorNeedsSaturation whole z
          · simp [uniqueSeparatorSaturationImage, xNeeds, zNeeds,
              same]
          · simp [uniqueSeparatorSaturationImage, xNeeds, zNeeds,
              same]
        · by_cases zNeeds : UniqueSeparatorNeedsSaturation whole z
          · simp [uniqueSeparatorSaturationImage, xNeeds, zNeeds,
              same]
          · simp [uniqueSeparatorSaturationImage, xNeeds, zNeeds,
              same]

theorem uniqueSeparatorSaturate_count
    (letters : List Nat) (z : Nat) :
    (uniqueSeparatorSaturate letters).count z =
      if UniqueSeparatorNeedsSaturation letters z then
        2
      else
        letters.count z := by
  rw [uniqueSeparatorSaturate,
    uniqueSeparatorSaturatePart_count]
  split
  · rename_i needs
    rw [needs.1]
  · rfl

theorem uniqueSeparatorSaturate_count_eq_one_iff
    (letters : List Nat) (z : Nat) :
    (uniqueSeparatorSaturate letters).count z = 1 ↔
      letters.count z = 1 ∧
        uniqueSeparatorEnclosed letters z = false := by
  constructor
  · intro saturatedCount
    rw [uniqueSeparatorSaturate_count] at saturatedCount
    by_cases needs : UniqueSeparatorNeedsSaturation letters z
    · simp [needs] at saturatedCount
    · have sourceCount : letters.count z = 1 := by
        simpa [needs] using saturatedCount
      have notEnclosed :
          uniqueSeparatorEnclosed letters z = false := by
        cases enclosedShape :
            uniqueSeparatorEnclosed letters z with
        | false =>
            rfl
        | true =>
            exact False.elim <| needs ⟨sourceCount, enclosedShape⟩
      exact ⟨sourceCount, notEnclosed⟩
  · rintro ⟨sourceCount, notEnclosed⟩
    have notNeeds :
        ¬ UniqueSeparatorNeedsSaturation letters z := by
      rintro ⟨_, enclosed⟩
      simp [notEnclosed] at enclosed
    rw [uniqueSeparatorSaturate_count, if_neg notNeeds, sourceCount]

theorem uniqueSeparatorSaturate_count_le_two
    (letters : List Nat) (limited : UniqueSeparatorTwoLimited letters)
    (z : Nat) :
    (uniqueSeparatorSaturate letters).count z ≤ 2 := by
  rw [uniqueSeparatorSaturate_count]
  split
  · omega
  · exact limited z

theorem uniqueSeparatorSaturate_twoLimited
    (letters : List Nat) (limited : UniqueSeparatorTwoLimited letters) :
    UniqueSeparatorTwoLimited (uniqueSeparatorSaturate letters) :=
  uniqueSeparatorSaturate_count_le_two letters limited

theorem uniqueSeparatorSaturate_count_zero_one_or_two
    (letters : List Nat) (limited : UniqueSeparatorTwoLimited letters)
    (z : Nat) :
    (uniqueSeparatorSaturate letters).count z = 0 ∨
      (uniqueSeparatorSaturate letters).count z = 1 ∨
      (uniqueSeparatorSaturate letters).count z = 2 := by
  have bound :=
    uniqueSeparatorSaturate_count_le_two letters limited z
  omega

theorem uniqueSeparatorSaturate_member_count_one_or_two
    (letters : List Nat) (limited : UniqueSeparatorTwoLimited letters)
    (z : Nat) (member : z ∈ uniqueSeparatorSaturate letters) :
    (uniqueSeparatorSaturate letters).count z = 1 ∨
      (uniqueSeparatorSaturate letters).count z = 2 := by
  have positive :
      1 ≤ (uniqueSeparatorSaturate letters).count z :=
    List.one_le_count_iff.mpr member
  have bound :=
    uniqueSeparatorSaturate_count_le_two letters limited z
  omega

/-- A globally linear letter separates two support-disjoint sides. -/
def UniqueSeparatorSupportDisjointSeparator
    (letters : List Nat) (x : Nat) : Prop :=
  ∃ left right,
    letters = left ++ x :: right ∧
      x ∉ left ∧ x ∉ right ∧
      ∀ z, z ∈ left → z ∈ right → False

theorem uniqueSeparatorSaturate_linear_is_supportDisjointSeparator
    (letters : List Nat) (x : Nat)
    (linear : (uniqueSeparatorSaturate letters).count x = 1) :
    UniqueSeparatorSupportDisjointSeparator
      (uniqueSeparatorSaturate letters) x := by
  rcases
      (uniqueSeparatorSaturate_count_eq_one_iff letters x).mp linear with
    ⟨sourceCount, notEnclosed⟩
  have sourceMember : x ∈ letters := by
    apply List.count_pos_iff.mp
    omega
  rcases List.append_of_mem sourceMember with
    ⟨before, after, shape⟩
  have beforeCount : before.count x = 0 := by
    rw [shape] at sourceCount
    simp only [List.count_append, List.count_cons_self] at sourceCount
    omega
  have afterCount : after.count x = 0 := by
    rw [shape] at sourceCount
    simp only [List.count_append, List.count_cons_self] at sourceCount
    omega
  have notBefore : x ∉ before :=
    List.count_eq_zero.mp beforeCount
  have notAfter : x ∉ after :=
    List.count_eq_zero.mp afterCount
  have noIntersection :
      ∀ z, z ∈ before → z ∈ after → False := by
    apply
      (uniqueSeparatorSupportsIntersect_eq_false_iff
        before after).mp
    rw [← uniqueSeparatorEnclosed_split shape notBefore]
    exact notEnclosed
  have notNeeds :
      ¬ UniqueSeparatorNeedsSaturation letters x := by
    rintro ⟨_, enclosed⟩
    simp [notEnclosed] at enclosed
  have notNeedsShape :
      ¬ UniqueSeparatorNeedsSaturation
        (before ++ x :: after) x := by
    simpa [← shape] using notNeeds
  refine
    ⟨uniqueSeparatorSaturatePart letters before,
      uniqueSeparatorSaturatePart letters after, ?_, ?_, ?_, ?_⟩
  · rw [uniqueSeparatorSaturate, shape]
    simp [uniqueSeparatorSaturatePart,
      uniqueSeparatorSaturationImage, notNeedsShape]
  · rwa [uniqueSeparatorSaturatePart_mem_iff]
  · rwa [uniqueSeparatorSaturatePart_mem_iff]
  · intro z zLeft zRight
    exact noIntersection z
      ((uniqueSeparatorSaturatePart_mem_iff
        letters before z).mp zLeft)
      ((uniqueSeparatorSaturatePart_mem_iff
        letters after z).mp zRight)

/-- The exact cut exposed by a surviving globally linear letter. Its two
sides have disjoint support, so in particular no quadratic letter has one
occurrence on each side. -/
theorem uniqueSeparatorSaturate_linear_exactCut
    (letters : List Nat) (x : Nat)
    (linear : (uniqueSeparatorSaturate letters).count x = 1) :
    ∃ left right,
      uniqueSeparatorSaturate letters = left ++ x :: right ∧
        x ∉ left ∧ x ∉ right ∧
        (∀ z, z ∈ left → z ∈ right → False) ∧
        (∀ z,
          (uniqueSeparatorSaturate letters).count z = 2 →
            ¬(z ∈ left ∧ z ∈ right)) := by
  rcases
      uniqueSeparatorSaturate_linear_is_supportDisjointSeparator
        letters x linear with
    ⟨left, right, shape, notLeft, notRight, disjoint⟩
  refine
    ⟨left, right, shape, notLeft, notRight, disjoint, ?_⟩
  intro z _ crossing
  exact disjoint z crossing.1 crossing.2

private theorem uniqueSeparatorUniqueLinearSplit
    {x : Nat} {left right otherLeft otherRight : List Nat}
    (notLeft : x ∉ left) (notOtherLeft : x ∉ otherLeft)
    (same :
      left ++ x :: right =
        otherLeft ++ x :: otherRight) :
    left = otherLeft ∧ right = otherRight := by
  induction left generalizing otherLeft with
  | nil =>
      cases otherLeft with
      | nil =>
          have rightEq : right = otherRight := by
            simpa using congrArg List.tail same
          exact ⟨rfl, rightEq⟩
      | cons y ys =>
          change x :: right = y :: (ys ++ x :: otherRight) at same
          have xy : x = y := (List.cons.inj same).1
          exact False.elim <| notOtherLeft <| by
            simp [← xy]
  | cons y ys ih =>
      cases otherLeft with
      | nil =>
          change y :: (ys ++ x :: right) = x :: otherRight at same
          have yx : y = x := (List.cons.inj same).1
          exact False.elim <| notLeft <| by
            simp [yx]
      | cons z zs =>
          change
            y :: (ys ++ x :: right) =
              z :: (zs ++ x :: otherRight) at same
          have headEq : y = z := (List.cons.inj same).1
          have tailEq :
              ys ++ x :: right =
                zs ++ x :: otherRight :=
            (List.cons.inj same).2
          have notYs : x ∉ ys := by
            intro member
            exact notLeft (List.mem_cons_of_mem y member)
          have notZs : x ∉ zs := by
            intro member
            exact notOtherLeft (List.mem_cons_of_mem z member)
          rcases ih notYs notZs tailEq with
            ⟨ysEq, rightEq⟩
          exact ⟨by simp [headEq, ysEq], rightEq⟩

/-- Transport a support-disjoint-separator witness to any displayed split at
the same unique separator. -/
theorem uniqueSeparatorSupportDisjointSeparator_at_split
    {letters left right : List Nat} {x : Nat}
    (separator :
      UniqueSeparatorSupportDisjointSeparator letters x)
    (shape : letters = left ++ x :: right) :
    ∀ z, z ∈ left → z ∈ right → False := by
  rcases separator with
    ⟨canonicalLeft, canonicalRight, canonicalShape,
      notCanonicalLeft, notCanonicalRight, disjoint⟩
  have countOne : letters.count x = 1 := by
    rw [canonicalShape, List.count_append,
      List.count_cons_self,
      List.count_eq_zero.mpr notCanonicalLeft,
      List.count_eq_zero.mpr notCanonicalRight]
  have notLeft : x ∉ left := by
    rw [shape, List.count_append, List.count_cons_self] at countOne
    have leftCount : left.count x = 0 := by omega
    exact List.count_eq_zero.mp leftCount
  have sameCuts :
      left = canonicalLeft ∧ right = canonicalRight := by
    apply uniqueSeparatorUniqueLinearSplit notLeft notCanonicalLeft
    exact shape.symm.trans canonicalShape
  rintro z zLeft zRight
  rw [sameCuts.1] at zLeft
  rw [sameCuts.2] at zRight
  exact disjoint z zLeft zRight

/-- Cycle-free bridge to `UniqueSeparatorRawSaturated`: after splitting a
saturated list at its count-one letters, the rendered prefix together with
the current quadratic block is support-disjoint from the rendered rest. -/
theorem uniqueSeparatorSplitLinear_saturate_separatorDisjoint
    (letters : List Nat)
    (before : List UniqueSeparatorSquareSegment)
    (segment : UniqueSeparatorSquareSegment)
    (rest : List UniqueSeparatorSquareSegment)
    (separator : Nat)
    (segmentsShape :
      uniqueSeparatorSplitLinear (uniqueSeparatorSaturate letters) =
        before ++ segment :: rest)
    (separatorShape : segment.separator = some separator) :
    ∀ z,
      z ∈
          (uniqueSeparatorRenderSquareSegments before ++
            segment.quadratic) →
        z ∈ uniqueSeparatorRenderSquareSegments rest →
          False := by
  let saturated := uniqueSeparatorSaturate letters
  have segmentMember :
      segment ∈ uniqueSeparatorSplitLinear saturated := by
    rw [segmentsShape]
    simp
  have separatorCount :
      saturated.count separator = 1 :=
    uniqueSeparatorSplitLinear_separator_count_one
      saturated segment segmentMember separator separatorShape
  have exactSeparator :=
    uniqueSeparatorSaturate_linear_is_supportDisjointSeparator
      letters separator separatorCount
  have renderedShape :
      saturated =
        (uniqueSeparatorRenderSquareSegments before ++
            segment.quadratic) ++
          separator ::
            uniqueSeparatorRenderSquareSegments rest := by
    rw [← uniqueSeparatorRender_splitLinear saturated,
      segmentsShape]
    simp [uniqueSeparatorRenderSquareSegments,
      UniqueSeparatorSquareSegment.render, separatorShape,
      List.append_assoc]
  exact
    uniqueSeparatorSupportDisjointSeparator_at_split
      exactSeparator renderedShape

/-- Raw-segment form of the saturation bridge, arranged so that
`UniqueSeparatorRawSaturated` can wrap it directly without an import from
the canonical module back into this one. -/
theorem uniqueSeparatorSplitLinear_saturate_rawDisjoint
    (letters : List Nat) :
    ∀ before segment rest separator,
      uniqueSeparatorSplitLinear (uniqueSeparatorSaturate letters) =
          before ++ segment :: rest →
        segment.separator = some separator →
          ∀ z,
            z ∈
                (uniqueSeparatorRenderSquareSegments before ++
                  segment.quadratic) →
              z ∈ uniqueSeparatorRenderSquareSegments rest →
                False := by
  intro before segment rest separator segmentsShape separatorShape
  exact
    uniqueSeparatorSplitLinear_saturate_separatorDisjoint
      letters before segment rest separator
      segmentsShape separatorShape

/-- A single `L₄` step: duplicate a letter between matching endpoints. The
four cases use the reversals of Edmunds' interior-contraction laws according
to whether the left and right interior blocks are empty. -/
theorem uniqueSeparatorListDerivesEnclosedDuplication
    (before after left right : List Nat) (u x : Nat) :
    UniqueSeparatorListDerives
      (before ++ [u] ++ left ++ [x] ++ right ++ [u] ++ after)
      (before ++ [u] ++ left ++ [x, x] ++ right ++ [u] ++ after) := by
  cases left with
  | nil =>
      cases right with
      | nil =>
          have core :=
            UniqueSeparatorListDerives.ofWord <|
              Derives.symm <|
                uniqueSeparatorDerivesMiddleContraction
                  (Word.singleton u) (Word.singleton x)
          simpa [uniqueSeparatorWordOfCons, Word.singleton,
            Word.append, List.append_assoc] using
            core.context before after
      | cons r rs =>
          have core :=
            UniqueSeparatorListDerives.ofWord <|
              Derives.symm <|
                uniqueSeparatorDerivesLeftInteriorContraction
                  (Word.singleton u) (Word.singleton x)
                  (uniqueSeparatorWordOfCons r rs)
          simpa [uniqueSeparatorWordOfCons, Word.singleton,
            Word.append, List.append_assoc] using
            core.context before after
  | cons l ls =>
      cases right with
      | nil =>
          have core :=
            UniqueSeparatorListDerives.ofWord <|
              Derives.symm <|
                uniqueSeparatorDerivesRightInteriorContraction
                  (Word.singleton u)
                  (uniqueSeparatorWordOfCons l ls)
                  (Word.singleton x)
          simpa [uniqueSeparatorWordOfCons, Word.singleton,
            Word.append, List.append_assoc] using
            core.context before after
      | cons r rs =>
          have core :=
            UniqueSeparatorListDerives.ofWord <|
              Derives.symm <|
                uniqueSeparatorDerivesInteriorContraction
                  (Word.singleton u)
                  (uniqueSeparatorWordOfCons l ls)
                  (Word.singleton x)
                  (uniqueSeparatorWordOfCons r rs)
          simpa [uniqueSeparatorWordOfCons, Word.singleton,
            Word.append, List.append_assoc] using
            core.context before after

private theorem uniqueSeparatorSaturatePart_append_singleton
    (whole pre : List Nat) (x : Nat) :
    uniqueSeparatorSaturatePart whole (pre ++ [x]) =
      uniqueSeparatorSaturatePart whole pre ++
        uniqueSeparatorSaturationImage whole x := by
  simp [uniqueSeparatorSaturatePart]

/-- Processing invariant for the full saturation derivation. The original
prefix has already been saturated; the untouched suffix is processed next. -/
theorem uniqueSeparatorListDerivesSaturateLoop
    (whole : List Nat) :
    ∀ pre rest,
      whole = pre ++ rest →
        UniqueSeparatorListDerives
          (uniqueSeparatorSaturatePart whole pre ++ rest)
          (uniqueSeparatorSaturatePart whole (pre ++ rest))
  | pre, [], _ => by
      simpa using
        UniqueSeparatorListDerives.refl
          (uniqueSeparatorSaturatePart whole pre)
  | pre, x :: xs, shape => by
      by_cases needs : UniqueSeparatorNeedsSaturation whole x
      · have sourceCount : whole.count x = 1 := needs.1
        have preCount : pre.count x = 0 := by
          rw [shape] at sourceCount
          simp only [List.count_append, List.count_cons_self] at sourceCount
          omega
        have notPre : x ∉ pre :=
          List.count_eq_zero.mp preCount
        have enclosedAtSplit :
            uniqueSeparatorSupportsIntersect pre xs = true := by
          rw [← uniqueSeparatorEnclosed_split shape notPre]
          exact needs.2
        rcases
            (uniqueSeparatorSupportsIntersect_eq_true_iff
              pre xs).mp enclosedAtSplit with
          ⟨u, uPre, uRest⟩
        have uSaturatedPrefix :
            u ∈ uniqueSeparatorSaturatePart whole pre :=
          (uniqueSeparatorSaturatePart_mem_iff
            whole pre u).mpr uPre
        rcases List.append_of_mem uSaturatedPrefix with
          ⟨before, left, saturatedPrefixShape⟩
        rcases List.append_of_mem uRest with
          ⟨right, after, restShape⟩
        have duplicateStep :
            UniqueSeparatorListDerives
              (uniqueSeparatorSaturatePart whole pre ++ x :: xs)
              (uniqueSeparatorSaturatePart whole pre ++
                x :: x :: xs) := by
          simpa [saturatedPrefixShape, restShape,
            List.append_assoc] using
            uniqueSeparatorListDerivesEnclosedDuplication
              before after left right u x
        have nextShape :
            whole = (pre ++ [x]) ++ xs := by
          simpa [List.append_assoc] using shape
        have restDerivation :=
          uniqueSeparatorListDerivesSaturateLoop
            whole (pre ++ [x]) xs nextShape
        have imageShape :
            uniqueSeparatorSaturationImage whole x = [x, x] := by
          simp [uniqueSeparatorSaturationImage, needs]
        have alignedRest :
            UniqueSeparatorListDerives
              (uniqueSeparatorSaturatePart whole pre ++
                x :: x :: xs)
              (uniqueSeparatorSaturatePart whole
                (pre ++ x :: xs)) := by
          simpa [uniqueSeparatorSaturatePart_append_singleton,
            imageShape, List.append_assoc] using restDerivation
        exact duplicateStep.trans alignedRest
      · have nextShape :
            whole = (pre ++ [x]) ++ xs := by
          simpa [List.append_assoc] using shape
        have restDerivation :=
          uniqueSeparatorListDerivesSaturateLoop
            whole (pre ++ [x]) xs nextShape
        have imageShape :
            uniqueSeparatorSaturationImage whole x = [x] := by
          simp [uniqueSeparatorSaturationImage, needs]
        simpa [uniqueSeparatorSaturatePart_append_singleton,
          imageShape, List.append_assoc] using restDerivation

/-- The endpoint-capped word derives its fully `L₄`-saturated form. -/
theorem uniqueSeparatorListDerivesSaturate
    (letters : List Nat) :
    UniqueSeparatorListDerives
      letters (uniqueSeparatorSaturate letters) := by
  simpa [uniqueSeparatorSaturate] using
    uniqueSeparatorListDerivesSaturateLoop
      letters [] letters (by simp)

/-- The normalization pipeline's concrete `L₄` phase. -/
theorem uniqueSeparatorListDerivesEndpointCapSaturate
    (letters : List Nat) :
    UniqueSeparatorListDerives
      (uniqueSeparatorEndpointCap letters)
      (uniqueSeparatorSaturate
        (uniqueSeparatorEndpointCap letters)) :=
  uniqueSeparatorListDerivesSaturate
    (uniqueSeparatorEndpointCap letters)

/-- The integration contract for the `L₄` phase. Counts are asserted only for
letters in the output support; absent natural numbers still have count zero. -/
structure UniqueSeparatorSaturationPostcondition
    (source output : List Nat) : Prop where
  supportPreserved :
    ∀ z, z ∈ output ↔ z ∈ source
  memberCountOneOrTwo :
    ∀ z, z ∈ output →
      output.count z = 1 ∨ output.count z = 2
  linearExactCut :
    ∀ x, output.count x = 1 →
      ∃ left right,
        output = left ++ x :: right ∧
          x ∉ left ∧ x ∉ right ∧
          (∀ z, z ∈ left → z ∈ right → False) ∧
          (∀ z, output.count z = 2 →
            ¬(z ∈ left ∧ z ∈ right))
  derives :
    UniqueSeparatorListDerives source output

theorem uniqueSeparatorSaturate_postcondition
    (letters : List Nat) (limited : UniqueSeparatorTwoLimited letters) :
    UniqueSeparatorSaturationPostcondition
      letters (uniqueSeparatorSaturate letters) where
  supportPreserved :=
    fun z => uniqueSeparatorSaturate_mem_iff letters z
  memberCountOneOrTwo :=
    fun z member =>
      uniqueSeparatorSaturate_member_count_one_or_two
        letters limited z member
  linearExactCut :=
    fun x linear =>
      uniqueSeparatorSaturate_linear_exactCut letters x linear
  derives :=
    uniqueSeparatorListDerivesSaturate letters

/-- Strong postcondition specialized to the deterministic endpoint cap used
immediately before saturation in the normalization pipeline. -/
theorem uniqueSeparatorEndpointCapSaturate_postcondition
    (letters : List Nat) :
    UniqueSeparatorSaturationPostcondition
      (uniqueSeparatorEndpointCap letters)
      (uniqueSeparatorSaturate
        (uniqueSeparatorEndpointCap letters)) :=
  uniqueSeparatorSaturate_postcondition
    (uniqueSeparatorEndpointCap letters)
    (uniqueSeparatorEndpointCap_twoLimited letters)

end SemigroupBasis.Examples
