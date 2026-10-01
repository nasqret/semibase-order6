import SemigroupBasis.Examples.UniqueSeparatorFourListDerives

namespace SemigroupBasis.Examples

open SemigroupBasis

@[simp]
theorem uniqueSeparatorWordOfCons_toList (head : Nat) (tail : List Nat) :
    (uniqueSeparatorWordOfCons head tail).toList = head :: tail :=
  rfl

@[simp]
theorem uniqueSeparatorSingleton_eq_wordOfCons (x : Nat) :
    Word.singleton x = uniqueSeparatorWordOfCons x [] :=
  rfl

@[simp]
theorem uniqueSeparatorWordOfCons_append
    (x : Nat) (xs : List Nat) (y : Nat) (ys : List Nat) :
    uniqueSeparatorWordOfCons x xs ++ uniqueSeparatorWordOfCons y ys =
      uniqueSeparatorWordOfCons x (xs ++ y :: ys) :=
  rfl

/-- Edmunds' four `L₆` laws, packaged with possibly empty intervening gaps. -/
theorem uniqueSeparatorListDerivesL6
    (x y : Nat) (middle tail : List Nat) :
    UniqueSeparatorListDerives
      ([x, y] ++ middle ++ [x] ++ tail ++ [y])
      ([y, x] ++ middle ++ [x] ++ tail ++ [y]) := by
  cases middle with
  | nil =>
      cases tail with
      | nil =>
          exact UniqueSeparatorListDerives.words <| by
            simpa [List.append_assoc] using
              uniqueSeparatorDerivesL6Square
                (Word.singleton x) (Word.singleton y)
      | cons t ts =>
          exact UniqueSeparatorListDerives.words <| by
            simpa [List.append_assoc] using
              uniqueSeparatorDerivesL6Short
                (Word.singleton x) (Word.singleton y)
                (uniqueSeparatorWordOfCons t ts)
  | cons m ms =>
      cases tail with
      | nil =>
          exact UniqueSeparatorListDerives.words <| by
            simpa [List.append_assoc] using
              uniqueSeparatorDerivesL6Medium
                (Word.singleton x) (Word.singleton y)
                (uniqueSeparatorWordOfCons m ms)
      | cons t ts =>
          exact UniqueSeparatorListDerives.words <| by
            simpa [List.append_assoc] using
              uniqueSeparatorDerivesL6Long
                (Word.singleton x) (Word.singleton y)
                (uniqueSeparatorWordOfCons m ms)
                (uniqueSeparatorWordOfCons t ts)

/-- Edmunds' four `L₇` laws, packaged with possibly empty intervening gaps. -/
theorem uniqueSeparatorListDerivesL7
    (x y : Nat) (left right : List Nat) :
    UniqueSeparatorListDerives
      ([x] ++ left ++ [y, x] ++ right ++ [y])
      ([x] ++ left ++ [x, y] ++ right ++ [y]) := by
  cases left with
  | nil =>
      cases right with
      | nil =>
          exact UniqueSeparatorListDerives.words <| by
            simpa [List.append_assoc] using
              uniqueSeparatorDerivesL7Square
                (Word.singleton x) (Word.singleton y)
      | cons r rs =>
          exact UniqueSeparatorListDerives.words <| by
            simpa [List.append_assoc] using
              uniqueSeparatorDerivesL7Short
                (Word.singleton x) (Word.singleton y)
                (uniqueSeparatorWordOfCons r rs)
  | cons l ls =>
      cases right with
      | nil =>
          exact UniqueSeparatorListDerives.words <| by
            simpa [List.append_assoc] using
              uniqueSeparatorDerivesL7Medium
                (Word.singleton x) (uniqueSeparatorWordOfCons l ls)
                (Word.singleton y)
      | cons r rs =>
          exact UniqueSeparatorListDerives.words <| by
            simpa [List.append_assoc] using
              uniqueSeparatorDerivesL7Long
                (Word.singleton x) (uniqueSeparatorWordOfCons l ls)
                (Word.singleton y) (uniqueSeparatorWordOfCons r rs)

/-- Edmunds' four `L₈` laws, packaged with possibly empty intervening gaps. -/
theorem uniqueSeparatorListDerivesL8
    (x y : Nat) (left middle : List Nat) :
    UniqueSeparatorListDerives
      ([x] ++ left ++ [y] ++ middle ++ [x, y])
      ([x] ++ left ++ [y] ++ middle ++ [y, x]) := by
  cases left with
  | nil =>
      cases middle with
      | nil =>
          exact UniqueSeparatorListDerives.words <| by
            simpa [List.append_assoc] using
              uniqueSeparatorDerivesL8Square
                (Word.singleton x) (Word.singleton y)
      | cons m ms =>
          exact UniqueSeparatorListDerives.words <| by
            simpa [List.append_assoc] using
              uniqueSeparatorDerivesL8Short
                (Word.singleton x) (Word.singleton y)
                (uniqueSeparatorWordOfCons m ms)
  | cons l ls =>
      cases middle with
      | nil =>
          exact UniqueSeparatorListDerives.words <| by
            simpa [List.append_assoc] using
              uniqueSeparatorDerivesL8Medium
                (Word.singleton x) (uniqueSeparatorWordOfCons l ls)
                (Word.singleton y)
      | cons m ms =>
          exact UniqueSeparatorListDerives.words <| by
            simpa [List.append_assoc] using
              uniqueSeparatorDerivesL8Long
                (Word.singleton x) (uniqueSeparatorWordOfCons l ls)
                (Word.singleton y) (uniqueSeparatorWordOfCons m ms)

/-- Swap adjacent first occurrences when the other `x` occurs before the
other `y`. -/
theorem uniqueSeparatorListDerivesAdjacent_futureXY
    (pre after middle between : List Nat) (x y : Nat) :
    UniqueSeparatorListDerives
      (pre ++ [x, y] ++ middle ++ [x] ++ between ++ [y] ++ after)
      (pre ++ [y, x] ++ middle ++ [x] ++ between ++ [y] ++ after) := by
  simpa [List.append_assoc] using
    (uniqueSeparatorListDerivesL6 x y middle between).context pre after

/-- Swap adjacent first occurrences when the other `y` occurs before the
other `x`. -/
theorem uniqueSeparatorListDerivesAdjacent_futureYX
    (pre after middle between : List Nat) (x y : Nat) :
    UniqueSeparatorListDerives
      (pre ++ [x, y] ++ middle ++ [y] ++ between ++ [x] ++ after)
      (pre ++ [y, x] ++ middle ++ [y] ++ between ++ [x] ++ after) := by
  simpa [List.append_assoc] using
    (uniqueSeparatorListDerivesL6 y x middle between).symm.context pre after

/-- Swap adjacent occurrences when the other `x` is before the pair and the
other `y` is after it. -/
theorem uniqueSeparatorListDerivesAdjacent_straddleXY
    (before after left right : List Nat) (x y : Nat) :
    UniqueSeparatorListDerives
      (before ++ [x] ++ left ++ [x, y] ++ right ++ [y] ++ after)
      (before ++ [x] ++ left ++ [y, x] ++ right ++ [y] ++ after) := by
  simpa [List.append_assoc] using
    (uniqueSeparatorListDerivesL7 x y left right).symm.context before after

/-- Swap adjacent occurrences when the other `y` is before the pair and the
other `x` is after it. -/
theorem uniqueSeparatorListDerivesAdjacent_straddleYX
    (before after left right : List Nat) (x y : Nat) :
    UniqueSeparatorListDerives
      (before ++ [y] ++ left ++ [x, y] ++ right ++ [x] ++ after)
      (before ++ [y] ++ left ++ [y, x] ++ right ++ [x] ++ after) := by
  simpa [List.append_assoc] using
    (uniqueSeparatorListDerivesL7 y x left right).context before after

/-- Swap adjacent second occurrences when the earlier `x` occurs before the
earlier `y`. -/
theorem uniqueSeparatorListDerivesAdjacent_pastXY
    (before post left middle : List Nat) (x y : Nat) :
    UniqueSeparatorListDerives
      (before ++ [x] ++ left ++ [y] ++ middle ++ [x, y] ++ post)
      (before ++ [x] ++ left ++ [y] ++ middle ++ [y, x] ++ post) := by
  simpa [List.append_assoc] using
    (uniqueSeparatorListDerivesL8 x y left middle).context before post

/-- Swap adjacent second occurrences when the earlier `y` occurs before the
earlier `x`. -/
theorem uniqueSeparatorListDerivesAdjacent_pastYX
    (before post left middle : List Nat) (x y : Nat) :
    UniqueSeparatorListDerives
      (before ++ [y] ++ left ++ [x] ++ middle ++ [x, y] ++ post)
      (before ++ [y] ++ left ++ [x] ++ middle ++ [y, x] ++ post) := by
  simpa [List.append_assoc] using
    (uniqueSeparatorListDerivesL8 y x left middle).symm.context before post

/-- Two distinct members of a list occur in one of the two possible orders. -/
theorem uniqueSeparatorDistinctOccurrencesOrdered
    {letters : List Nat} {x y : Nat}
    (different : x ≠ y) (xMember : x ∈ letters) (yMember : y ∈ letters) :
    (∃ before middle after,
        letters = before ++ x :: (middle ++ y :: after)) ∨
      (∃ before middle after,
        letters = before ++ y :: (middle ++ x :: after)) := by
  rcases List.append_of_mem xMember with
    ⟨xBefore, xAfter, xShape⟩
  rw [xShape] at yMember
  simp only [List.mem_append, List.mem_cons] at yMember
  rcases yMember with yBefore | yAtOrAfter
  · rcases List.append_of_mem yBefore with
      ⟨before, middle, beforeShape⟩
    exact Or.inr ⟨before, middle, xAfter, by
      rw [xShape, beforeShape]
      simp [List.append_assoc]⟩
  · rcases yAtOrAfter with equal | yAfter
    · exact (different equal.symm).elim
    · rcases List.append_of_mem yAfter with
        ⟨middle, after, afterShape⟩
      exact Or.inl ⟨xBefore, middle, after, by
        rw [xShape, afterShape]⟩

/-- The six possible positions of the other occurrences of two adjacent
quadratic letters. -/
inductive UniqueSeparatorAdjacentQuadraticPosition
    (x y : Nat) (pre post : List Nat) : Prop
  | futureXY (middle between after : List Nat)
      (postShape : post = middle ++ x :: (between ++ y :: after))
  | futureYX (middle between after : List Nat)
      (postShape : post = middle ++ y :: (between ++ x :: after))
  | straddleXY (before left right after : List Nat)
      (preShape : pre = before ++ x :: left)
      (postShape : post = right ++ y :: after)
  | straddleYX (before left right after : List Nat)
      (preShape : pre = before ++ y :: left)
      (postShape : post = right ++ x :: after)
  | pastXY (before left middle : List Nat)
      (preShape : pre = before ++ x :: (left ++ y :: middle))
  | pastYX (before left middle : List Nat)
      (preShape : pre = before ++ y :: (left ++ x :: middle))

/-- Edmunds' positional lemma: every one of the six possible placements of
the two other occurrences permits the displayed adjacent swap. -/
theorem uniqueSeparatorListDerivesAdjacent_of_position
    {x y : Nat} {pre post : List Nat}
    (position :
      UniqueSeparatorAdjacentQuadraticPosition x y pre post) :
    UniqueSeparatorListDerives
      (pre ++ (x :: y :: post))
      (pre ++ (y :: x :: post)) := by
  cases position with
  | futureXY middle between after postShape =>
      subst post
      simpa [List.append_assoc] using
        uniqueSeparatorListDerivesAdjacent_futureXY
          pre after middle between x y
  | futureYX middle between after postShape =>
      subst post
      simpa [List.append_assoc] using
        uniqueSeparatorListDerivesAdjacent_futureYX
          pre after middle between x y
  | straddleXY before left right after preShape postShape =>
      subst pre
      subst post
      simpa [List.append_assoc] using
        uniqueSeparatorListDerivesAdjacent_straddleXY
          before after left right x y
  | straddleYX before left right after preShape postShape =>
      subst pre
      subst post
      simpa [List.append_assoc] using
        uniqueSeparatorListDerivesAdjacent_straddleYX
          before after left right x y
  | pastXY before left middle preShape =>
      subst pre
      simpa [List.append_assoc] using
        uniqueSeparatorListDerivesAdjacent_pastXY
          before post left middle x y
  | pastYX before left middle preShape =>
      subst pre
      simpa [List.append_assoc] using
        uniqueSeparatorListDerivesAdjacent_pastYX
          before post left middle x y

/-- Exact quadratic multiplicities force one of the six positional cases. -/
theorem uniqueSeparatorAdjacentQuadraticPosition_of_counts
    {x y : Nat} {pre post : List Nat}
    (different : x ≠ y)
    (xQuadratic : (pre ++ (x :: y :: post)).count x = 2)
    (yQuadratic : (pre ++ (x :: y :: post)).count y = 2) :
    UniqueSeparatorAdjacentQuadraticPosition x y pre post := by
  have xSideCounts : pre.count x + post.count x = 1 := by
    have count := xQuadratic
    simp only [List.count_append, List.count_cons_self,
      List.count_cons_of_ne (Ne.symm different)] at count
    omega
  have ySideCounts : pre.count y + post.count y = 1 := by
    have count := yQuadratic
    simp only [List.count_append, List.count_cons_of_ne different,
      List.count_cons_self] at count
    omega
  by_cases xInPre : x ∈ pre
  · by_cases yInPre : y ∈ pre
    · rcases uniqueSeparatorDistinctOccurrencesOrdered
          different xInPre yInPre with
        orderedXY | orderedYX
      · rcases orderedXY with ⟨before, middle, after, shape⟩
        exact
          UniqueSeparatorAdjacentQuadraticPosition.pastXY
            before middle after shape
      · rcases orderedYX with ⟨before, middle, after, shape⟩
        exact
          UniqueSeparatorAdjacentQuadraticPosition.pastYX
            before middle after shape
    · have yPreCount : pre.count y = 0 :=
        List.count_eq_zero.mpr yInPre
      have yInPost : y ∈ post := by
        apply List.count_pos_iff.mp
        omega
      rcases List.append_of_mem xInPre with
        ⟨before, left, preShape⟩
      rcases List.append_of_mem yInPost with
        ⟨right, after, postShape⟩
      exact
        UniqueSeparatorAdjacentQuadraticPosition.straddleXY
          before left right after preShape postShape
  · have xPreCount : pre.count x = 0 :=
      List.count_eq_zero.mpr xInPre
    have xInPost : x ∈ post := by
      apply List.count_pos_iff.mp
      omega
    by_cases yInPre : y ∈ pre
    · rcases List.append_of_mem yInPre with
        ⟨before, left, preShape⟩
      rcases List.append_of_mem xInPost with
        ⟨right, after, postShape⟩
      exact
        UniqueSeparatorAdjacentQuadraticPosition.straddleYX
          before left right after preShape postShape
    · have yPreCount : pre.count y = 0 :=
        List.count_eq_zero.mpr yInPre
      have yInPost : y ∈ post := by
        apply List.count_pos_iff.mp
        omega
      rcases uniqueSeparatorDistinctOccurrencesOrdered
          different xInPost yInPost with
        orderedXY | orderedYX
      · rcases orderedXY with ⟨before, middle, after, shape⟩
        exact
          UniqueSeparatorAdjacentQuadraticPosition.futureXY
            before middle after shape
      · rcases orderedYX with ⟨before, middle, after, shape⟩
        exact
          UniqueSeparatorAdjacentQuadraticPosition.futureYX
            before middle after shape

/-- Adjacent distinct letters that each occur exactly twice can be
interchanged using the seven-law basis. -/
theorem uniqueSeparatorListDerivesAdjacentQuadraticSwap
    {x y : Nat} {pre post : List Nat}
    (different : x ≠ y)
    (xQuadratic : (pre ++ (x :: y :: post)).count x = 2)
    (yQuadratic : (pre ++ (x :: y :: post)).count y = 2) :
    UniqueSeparatorListDerives
      (pre ++ (x :: y :: post))
      (pre ++ (y :: x :: post)) :=
  uniqueSeparatorListDerivesAdjacent_of_position
    (uniqueSeparatorAdjacentQuadraticPosition_of_counts
      different xQuadratic yQuadratic)

end SemigroupBasis.Examples
