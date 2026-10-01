import SemigroupBasis.CoRoots.Order6SporadicSection13Canonical

namespace SemigroupBasis.CoRoots.Order6SporadicSection13

open SemigroupBasis
open SemigroupBasis.Examples

private def squareWord (letter : Nat) : Word Nat :=
  Word.singleton letter ++ Word.singleton letter

def appendFreshIdentity
    (identity : Identity Nat) (fresh : Nat) : Identity Nat :=
  ⟨identity.lhs ++ Word.singleton fresh,
    identity.rhs ++ Word.singleton fresh⟩

theorem appendFreshIdentity_valid
    {S : Type u} (semigroup : Semigroup S)
    (identity : Identity Nat) (fresh : Nat)
    (valid : identity.SatisfiedBy semigroup) :
    (appendFreshIdentity identity fresh).SatisfiedBy semigroup := by
  intro valuation
  simp only [appendFreshIdentity, Semigroup.eval_append,
    Semigroup.eval_singleton]
  rw [valid valuation]

theorem appendFreshIdentity_left_simple
    (identity : Identity Nat) (fresh : Nat)
    (freshAbsent : fresh ∉ identity.lhs.toList) :
    S5_345.simpleFinalVariable
        (appendFreshIdentity identity fresh).lhs =
      some fresh := by
  apply (S5_345.simpleFinalVariable_eq_some_iff
    (appendFreshIdentity identity fresh).lhs fresh).2
  constructor
  · unfold S5_107.SimpleIn
    simp [appendFreshIdentity, Word.toList_append,
      List.count_eq_zero.mpr freshAbsent]
  · rw [appendFreshIdentity, Word.final_append]
    rfl

private def freshSubstitution
    (fresh : Nat) (replacement : Word Nat) : Nat → Word Nat :=
  fun selected =>
    if selected = fresh then replacement else Word.singleton selected

private theorem flatMap_freshSubstitution_of_not_mem
    (fresh : Nat) (replacement : Word Nat) :
    ∀ (letters : List Nat), fresh ∉ letters →
      letters.flatMap
          (fun selected =>
            (freshSubstitution fresh replacement selected).toList) =
        letters
  | [], _ => rfl
  | selected :: rest, absent => by
      have selectedNe : selected ≠ fresh := by
        intro equal
        apply absent
        simp [equal]
      have restAbsent : fresh ∉ rest := by
        intro member
        exact absent (List.Mem.tail selected member)
      simp only [List.flatMap_cons]
      rw [flatMap_freshSubstitution_of_not_mem
        fresh replacement rest restAbsent]
      simp [freshSubstitution, selectedNe]

private theorem bind_append_fresh
    (word : Word Nat) (fresh : Nat) (replacement : Word Nat)
    (freshAbsent : fresh ∉ word.toList) :
    (word ++ Word.singleton fresh).bind
        (freshSubstitution fresh replacement) =
      word ++ replacement := by
  apply Word.toList_injective
  rw [Word.toList_bind, Word.toList_append,
    Word.toList_singleton, List.flatMap_append,
    flatMap_freshSubstitution_of_not_mem
      fresh replacement word.toList freshAbsent,
    Word.toList_append]
  simp [freshSubstitution]

private theorem derives_append_square_of_append_fresh
    (left right : Word Nat) (fresh replacementLetter : Nat)
    (freshLeft : fresh ∉ left.toList)
    (freshRight : fresh ∉ right.toList)
    (derivation : Derives basis
      (left ++ Word.singleton fresh)
      (right ++ Word.singleton fresh)) :
    Derives basis
      (left ++ squareWord replacementLetter)
      (right ++ squareWord replacementLetter) := by
  have substituted :=
    Derives.subst derivation
      (freshSubstitution fresh (squareWord replacementLetter))
  rw [bind_append_fresh left fresh (squareWord replacementLetter)
      freshLeft,
    bind_append_fresh right fresh (squareWord replacementLetter)
      freshRight] at substituted
  exact substituted

private theorem final_wordOfPrefixFinal
    (stem : List Nat) (final : Nat) :
    (wordOfPrefixFinal stem final).final = final := by
  induction stem with
  | nil => rfl
  | cons letter rest induction =>
      rw [wordOfPrefixFinal_cons, Word.final_append]
      exact induction

private theorem split_final_eq (word : Word Nat) :
    (splitPrefixFinal word).2 = word.final := by
  have reconstructed :=
    congrArg Word.final (wordOfPrefixFinal_split word)
  rw [final_wordOfPrefixFinal] at reconstructed
  exact reconstructed

private theorem split_final_mem_of_nonsimple
    (word : Word Nat)
    (nonsimple : S5_345.simpleFinalVariable word = none) :
    word.final ∈ (splitPrefixFinal word).1 := by
  have finalEq := split_final_eq word
  apply Decidable.byContradiction
  intro absent
  have countOne : word.toList.count word.final = 1 := by
    rw [toList_eq_splitPrefixFinal, finalEq, List.count_append]
    simp [List.count_eq_zero.mpr absent]
  have contradiction : False := by
    simpa [S5_345.simpleFinalVariable, countOne] using nonsimple
  exact contradiction.elim

private theorem pairSquares_perm
    (left right : Nat) :
    [right, right, left, left].Perm
      [left, left, right, right] := by
  have first :
      [right, right, left, left].Perm
        [right, left, right, left] :=
    List.Perm.cons right (List.Perm.swap left right [left])
  have second :
      [right, left, right, left].Perm
        [left, right, right, left] :=
    List.Perm.swap left right [right, left]
  have third :
      [left, right, right, left].Perm
        [left, right, left, right] :=
    List.Perm.cons left <|
      List.Perm.cons right (List.Perm.swap left right [])
  have fourth :
      [left, right, left, right].Perm
        [left, left, right, right] :=
    List.Perm.cons left (List.Perm.swap left right [right])
  exact first.trans <| second.trans <| third.trans fourth

/-- Formal version of Lemma 13.3.  When both original final variables are
nonsimple, a derivation of the identity after appending one fresh variable
can be converted into a derivation of the original identity. -/
theorem derives_of_appendedFresh_of_nonsimpleFinals
    (identity : Identity Nat)
    (oValid :
      identity.SatisfiedBy Generated.S4_96.table.semigroup.opposite)
    (leftNonsimple :
      S5_345.simpleFinalVariable identity.lhs = none)
    (rightNonsimple :
      S5_345.simpleFinalVariable identity.rhs = none)
    (fresh : Nat)
    (freshLeft : fresh ∉ identity.lhs.toList)
    (freshRight : fresh ∉ identity.rhs.toList)
    (appended : Derives basis
      (identity.lhs ++ Word.singleton fresh)
      (identity.rhs ++ Word.singleton fresh)) :
    Derives basis identity.lhs identity.rhs := by
  let leftPrefix := (splitPrefixFinal identity.lhs).1
  let rightPrefix := (splitPrefixFinal identity.rhs).1
  let leftFinal := identity.lhs.final
  let rightFinal := identity.rhs.final
  have leftSplitFinal := split_final_eq identity.lhs
  have rightSplitFinal := split_final_eq identity.rhs
  have leftShape :
      identity.lhs.toList = leftPrefix ++ [leftFinal] := by
    simpa [leftPrefix, leftFinal, leftSplitFinal] using
      toList_eq_splitPrefixFinal identity.lhs
  have rightShape :
      identity.rhs.toList = rightPrefix ++ [rightFinal] := by
    simpa [rightPrefix, rightFinal, rightSplitFinal] using
      toList_eq_splitPrefixFinal identity.rhs
  have leftRepeated : leftFinal ∈ leftPrefix := by
    simpa [leftPrefix, leftFinal] using
      split_final_mem_of_nonsimple identity.lhs leftNonsimple
  have rightRepeated : rightFinal ∈ rightPrefix := by
    simpa [rightPrefix, rightFinal] using
      split_final_mem_of_nonsimple identity.rhs rightNonsimple
  have firstOccurrences :=
    oValid_firstOccurrenceSequence_eq identity oValid
  have rightFinalInRight : rightFinal ∈ identity.rhs.toList := by
    rw [rightShape]
    simp
  have rightFinalInRightFirst :
      rightFinal ∈ firstOccurrenceSequence identity.rhs.toList :=
    (S5_345.mem_firstOccurrenceSequence_iff
      rightFinal identity.rhs.toList).2 rightFinalInRight
  have rightFinalInLeftFirst :
      rightFinal ∈ firstOccurrenceSequence identity.lhs.toList := by
    rw [firstOccurrences]
    exact rightFinalInRightFirst
  have rightFinalInLeft : rightFinal ∈ identity.lhs.toList :=
    (S5_345.mem_firstOccurrenceSequence_iff
      rightFinal identity.lhs.toList).1 rightFinalInLeftFirst
  have leftFinalInLeft : leftFinal ∈ identity.lhs.toList := by
    rw [leftShape]
    exact List.mem_append.mpr (Or.inl leftRepeated)
  have expandLeft : ListDerives
      identity.lhs.toList
      (identity.lhs.toList ++ [leftFinal, leftFinal]) := by
    simpa [leftShape, List.append_assoc] using
      listDerivesAppendFinalSquareOfSeen
        leftPrefix leftFinal leftRepeated
  have insertRight : ListDerives
      (identity.lhs.toList ++ [leftFinal, leftFinal])
      (identity.lhs.toList ++ [rightFinal, rightFinal] ++
        [leftFinal, leftFinal]) := by
    simpa [List.append_assoc] using
      (listDerivesDeleteAdjacentPairAfterPrefix
        identity.lhs.toList [leftFinal, leftFinal]
        rightFinal rightFinalInLeft (by simp)).symm
  have squareLettersSeen :
      ∀ selected,
        selected ∈ [rightFinal, rightFinal, leftFinal, leftFinal] →
          selected ∈ identity.lhs.toList := by
    intro selected member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact rightFinalInLeft
    · exact rightFinalInLeft
    · exact leftFinalInLeft
    · exact leftFinalInLeft
  have commuteSquares : ListDerives
      (identity.lhs.toList ++ [rightFinal, rightFinal] ++
        [leftFinal, leftFinal])
      (identity.lhs.toList ++ [leftFinal, leftFinal] ++
        [rightFinal, rightFinal]) := by
    simpa [List.append_assoc] using
      listDerivesPermuteAfterSeen
        identity.lhs.toList [] squareLettersSeen
          (pairSquares_perm leftFinal rightFinal)
  have deleteLeft : ListDerives
      (identity.lhs.toList ++ [leftFinal, leftFinal] ++
        [rightFinal, rightFinal])
      (identity.lhs.toList ++ [rightFinal, rightFinal]) := by
    simpa [List.append_assoc] using
      listDerivesDeleteAdjacentPairAfterPrefix
        identity.lhs.toList [rightFinal, rightFinal]
        leftFinal leftFinalInLeft (by simp)
  have substitutedWord :=
    derives_append_square_of_append_fresh
      identity.lhs identity.rhs fresh rightFinal
      freshLeft freshRight appended
  have substituted : ListDerives
      (identity.lhs.toList ++ [rightFinal, rightFinal])
      (identity.rhs.toList ++ [rightFinal, rightFinal]) := by
    simpa [squareWord, Word.toList_append] using
      (S5_107.ListDerives.ofWord (basis := basis) substitutedWord)
  have contractRight : ListDerives
      (identity.rhs.toList ++ [rightFinal, rightFinal])
      identity.rhs.toList := by
    simpa [rightShape, List.append_assoc] using
      (listDerivesAppendFinalSquareOfSeen
        rightPrefix rightFinal rightRepeated).symm
  apply derives_of_listDerives_toList
  exact expandLeft.trans <| insertRight.trans <|
    commuteSquares.trans <| deleteLeft.trans <|
      substituted.trans contractRight

/-- The nonsimple-final branch of Proposition 13.1, reduced to the
simple-final branch by appending one fresh variable. -/
theorem derives_of_factors_of_nonsimpleFinal
    (identity : Identity Nat)
    (jValid : identity.SatisfiedBy Generated.S3_6.table.semigroup)
    (oValid :
      identity.SatisfiedBy Generated.S4_96.table.semigroup.opposite)
    (fresh : Nat)
    (freshLeft : fresh ∉ identity.lhs.toList)
    (freshRight : fresh ∉ identity.rhs.toList)
    (leftNonsimple :
      S5_345.simpleFinalVariable identity.lhs = none) :
    Derives basis identity.lhs identity.rhs := by
  have simpleEqual := jValid_simpleFinalVariable_eq identity jValid
  have rightNonsimple :
      S5_345.simpleFinalVariable identity.rhs = none :=
    simpleEqual.symm.trans leftNonsimple
  let extended := appendFreshIdentity identity fresh
  have extendedJValid :
      extended.SatisfiedBy Generated.S3_6.table.semigroup := by
    exact appendFreshIdentity_valid Generated.S3_6.table.semigroup
      identity fresh jValid
  have extendedOValid :
      extended.SatisfiedBy
        Generated.S4_96.table.semigroup.opposite := by
    exact appendFreshIdentity_valid
      Generated.S4_96.table.semigroup.opposite
      identity fresh oValid
  have extendedLeftSimple :
      S5_345.simpleFinalVariable extended.lhs = some fresh := by
    exact appendFreshIdentity_left_simple identity fresh freshLeft
  have appended : Derives basis extended.lhs extended.rhs :=
    derives_of_factors_of_simpleFinal extended
      extendedJValid extendedOValid extendedLeftSimple
  exact derives_of_appendedFresh_of_nonsimpleFinals
    identity oValid leftNonsimple rightNonsimple fresh
    freshLeft freshRight appended

end SemigroupBasis.CoRoots.Order6SporadicSection13
