import SemigroupBasis.CoRoots.Order6S6_14897RegularOrthogroupListSwaps

namespace SemigroupBasis.CoRoots.Order6S6_14897RegularOrthogroup

open SemigroupBasis

private abbrev ListDerives : List Nat -> List Nat -> Prop :=
  SemigroupBasis.CoRoots.S5_107.ListDerives basis

private theorem orderedOccurrences
    (letters : List Nat) (x y : Nat)
    (different : x ≠ y)
    (xMember : x ∈ letters)
    (yMember : y ∈ letters) :
    Or
      (Exists fun before =>
        Exists fun middle =>
          Exists fun after =>
            letters =
              before ++ [x] ++ middle ++ [y] ++ after)
      (Exists fun before =>
        Exists fun middle =>
          Exists fun after =>
            letters =
              before ++ [y] ++ middle ++ [x] ++ after) := by
  obtain ⟨xBefore, xAfter, xSplit⟩ :=
    List.mem_iff_append.mp xMember
  rw [xSplit] at yMember
  simp only [List.mem_append, List.mem_cons] at yMember
  rcases yMember with yBefore | equal | yAfter
  · obtain ⟨before, middle, beforeSplit⟩ :=
      List.mem_iff_append.mp yBefore
    exact Or.inr <|
      Exists.intro before <|
        Exists.intro middle <|
          Exists.intro xAfter <| by
            simp [xSplit, beforeSplit, List.append_assoc]
  · exact False.elim (different equal.symm)
  · obtain ⟨middle, after, afterSplit⟩ :=
      List.mem_iff_append.mp yAfter
    exact Or.inl <|
      Exists.intro xBefore <|
        Exists.intro middle <|
          Exists.intro after <| by
            simp [xSplit, afterSplit, List.append_assoc]

/-- Adjacent letters commute whenever both occur in the leftContext and in the
suffix. The four possible witness orientations are discharged by the same
and mixed displayed kernels. -/
theorem listDerivesTwoSidedGuardedSwap
    (leftContext suffix : List Nat) (x y : Nat)
    (xInPrefix : x ∈ leftContext)
    (yInPrefix : y ∈ leftContext)
    (xInSuffix : x ∈ suffix)
    (yInSuffix : y ∈ suffix) :
    ListDerives
      (leftContext ++ [x, y] ++ suffix)
      (leftContext ++ [y, x] ++ suffix) := by
  by_cases equal : x = y
  · subst y
    exact SemigroupBasis.CoRoots.S5_107.ListDerives.refl _
  · have prefixOrder :=
      orderedOccurrences leftContext x y equal xInPrefix yInPrefix
    have suffixOrder :=
      orderedOccurrences suffix x y equal xInSuffix yInSuffix
    rcases prefixOrder with
      ⟨leftBefore, leftGap, leftAfter, prefixSplit⟩ |
      ⟨leftBefore, leftGap, leftAfter, prefixSplit⟩
    · rcases suffixOrder with
        ⟨rightBefore, rightGap, rightAfter, suffixSplit⟩ |
        ⟨rightBefore, rightGap, rightAfter, suffixSplit⟩
      · have core :=
          listDerivesDisplayedSwapSame
            x y leftGap leftAfter rightBefore rightGap
        have contextual :=
          SemigroupBasis.CoRoots.S5_107.ListDerives.context
            leftBefore rightAfter core
        simpa [prefixSplit, suffixSplit, List.append_assoc] using contextual
      · have core :=
          listDerivesDisplayedSwapMixed
            x y leftGap leftAfter rightBefore rightGap
        have contextual :=
          SemigroupBasis.CoRoots.S5_107.ListDerives.context
            leftBefore rightAfter core
        simpa [prefixSplit, suffixSplit, List.append_assoc] using contextual
    · rcases suffixOrder with
        ⟨rightBefore, rightGap, rightAfter, suffixSplit⟩ |
        ⟨rightBefore, rightGap, rightAfter, suffixSplit⟩
      · have core :=
          (listDerivesDisplayedSwapMixed
            y x leftGap leftAfter rightBefore rightGap).symm
        have contextual :=
          SemigroupBasis.CoRoots.S5_107.ListDerives.context
            leftBefore rightAfter core
        simpa [prefixSplit, suffixSplit, List.append_assoc] using contextual
      · have core :=
          (listDerivesDisplayedSwapSame
            y x leftGap leftAfter rightBefore rightGap).symm
        have contextual :=
          SemigroupBasis.CoRoots.S5_107.ListDerives.context
            leftBefore rightAfter core
        simpa [prefixSplit, suffixSplit, List.append_assoc] using contextual

/-- Every permutation of a middle block is derivable when each of its
letters occurs in both fixed guards. -/
theorem listDerivesTwoSidedGuardedPermutation
    (leftContext suffix : List Nat)
    {source target : List Nat}
    (leftGuard :
      forall letter, letter ∈ source -> letter ∈ leftContext)
    (rightGuard :
      forall letter, letter ∈ source -> letter ∈ suffix)
    (permutation : source.Perm target) :
    ListDerives
      (leftContext ++ source ++ suffix)
      (leftContext ++ target ++ suffix) := by
  induction permutation generalizing leftContext suffix with
  | nil =>
      exact SemigroupBasis.CoRoots.S5_107.ListDerives.refl _
  | cons head permutation induction =>
      have tailDerivation :=
        induction
          (leftContext ++ [head]) suffix
          (fun letter member =>
            List.mem_append.mpr <|
              Or.inl <| leftGuard letter
                (List.Mem.tail head member))
          (fun letter member =>
            rightGuard letter (List.Mem.tail head member))
      simpa [List.append_assoc] using tailDerivation
  | swap left right rest =>
      have leftInPrefix : left ∈ leftContext :=
        leftGuard left (by simp)
      have rightInPrefix : right ∈ leftContext :=
        leftGuard right (by simp)
      have leftInSuffix : left ∈ rest ++ suffix :=
        List.mem_append.mpr <|
          Or.inr <| rightGuard left (by simp)
      have rightInSuffix : right ∈ rest ++ suffix :=
        List.mem_append.mpr <|
          Or.inr <| rightGuard right (by simp)
      have swapped :=
        (listDerivesTwoSidedGuardedSwap
          leftContext (rest ++ suffix) left right
          leftInPrefix rightInPrefix
          leftInSuffix rightInSuffix).symm
      simpa [List.append_assoc] using swapped
  | trans first second firstInduction secondInduction =>
      have firstDerivation :=
        firstInduction leftContext suffix leftGuard rightGuard
      have secondDerivation :=
        secondInduction leftContext suffix
          (fun letter member =>
            leftGuard letter ((first.mem_iff).mpr member))
          (fun letter member =>
            rightGuard letter ((first.mem_iff).mpr member))
      exact firstDerivation.trans secondDerivation

end SemigroupBasis.CoRoots.Order6S6_14897RegularOrthogroup
