import SemigroupBasis.CoRoots.S5_730Semantics
import SemigroupBasis.CoRoots.S5_851SupportCompletion

namespace SemigroupBasis.CoRoots.S5_730

open SemigroupBasis
open SemigroupBasis.Examples

private theorem reverse_wordOfPrefixFinal
    (stem : List Nat) (final : Nat) :
    (wordOfPrefixFinal stem final).reverse =
      Word.mk final stem.reverse := by
  apply Word.toList_injective
  rw [Word.toList_reverse, toList_wordOfPrefixFinal]
  simp [Word.toList]

private theorem final_wordOfPrefixFinal
    (stem : List Nat) (final : Nat) :
    (wordOfPrefixFinal stem final).final = final := by
  induction stem with
  | nil => rfl
  | cons letter rest induction =>
      rw [wordOfPrefixFinal_cons, Word.final_append]
      exact induction

private theorem splitPrefixFinal_snd_eq_final (word : Word Nat) :
    (splitPrefixFinal word).2 = word.final := by
  have reconstructed :=
    congrArg Word.final (wordOfPrefixFinal_split word)
  rw [final_wordOfPrefixFinal] at reconstructed
  exact reconstructed

private theorem reverse_head_eq_final (word : Word Nat) :
    word.reverse.head = word.final := by
  calc
    word.reverse.head =
        (wordOfPrefixFinal
          (splitPrefixFinal word).1
          (splitPrefixFinal word).2).reverse.head :=
      congrArg (fun rebuilt : Word Nat => rebuilt.reverse.head)
        (wordOfPrefixFinal_split word).symm
    _ = (splitPrefixFinal word).2 :=
      congrArg Word.head <|
        reverse_wordOfPrefixFinal
          (splitPrefixFinal word).1
          (splitPrefixFinal word).2
    _ = word.final := splitPrefixFinal_snd_eq_final word

private theorem reverse_final_eq_head (word : Word Nat) :
    word.reverse.final = word.head := by
  have reversed := reverse_head_eq_final word.reverse
  simpa using reversed.symm

private theorem repeatedInitial_reverse (word : Word Nat) :
    S5_855.repeatedInitial word.reverse =
      decide (word.final ∈ (splitPrefixFinal word).1) := by
  classical
  have reversedShape :
      word.reverse =
        Word.mk (splitPrefixFinal word).2
          (splitPrefixFinal word).1.reverse :=
    (congrArg Word.reverse
      (wordOfPrefixFinal_split word).symm).trans
        (reverse_wordOfPrefixFinal
          (splitPrefixFinal word).1
          (splitPrefixFinal word).2)
  rw [reversedShape, splitPrefixFinal_snd_eq_final word]
  simp [S5_855.repeatedInitial]

private theorem repeatedInitial_reverse_eq_of_sameSimpleFinal
    {left right : Word Nat}
    (finalEq : left.final = right.final)
    (sameSimple : S5_196.SameSimpleFinal left right) :
    S5_855.repeatedInitial left.reverse =
      S5_855.repeatedInitial right.reverse := by
  have leftSplitFinal := splitPrefixFinal_snd_eq_final left
  have rightSplitFinal := splitPrefixFinal_snd_eq_final right
  have rightSplitCommon :
      (splitPrefixFinal right).2 = left.final :=
    rightSplitFinal.trans finalEq.symm
  have sameAtFinal := sameSimple left.final
  have absence :
      Iff
        (Not (List.Mem left.final (splitPrefixFinal left).1))
        (Not (List.Mem left.final (splitPrefixFinal right).1)) := by
    classical
    simpa [S5_196.SimpleFinal, leftSplitFinal,
      rightSplitCommon] using sameAtFinal
  have membership :
      Iff
        (List.Mem left.final (splitPrefixFinal left).1)
        (List.Mem left.final (splitPrefixFinal right).1) := by
    constructor
    next =>
      intro leftMember
      exact Classical.byContradiction fun rightAbsent =>
        (absence.mpr rightAbsent) leftMember
    next =>
      intro rightMember
      exact Classical.byContradiction fun leftAbsent =>
        (absence.mp leftAbsent) rightMember
  calc
    S5_855.repeatedInitial left.reverse =
        decide (left.final ∈ (splitPrefixFinal left).1) :=
      repeatedInitial_reverse left
    _ = decide (right.final ∈ (splitPrefixFinal right).1) := by
      rw [← finalEq]
      by_cases leftMember :
          left.final ∈ (splitPrefixFinal left).1
      · have rightMember := membership.mp leftMember
        rw [show decide (left.final ∈ (splitPrefixFinal left).1) = true
          from decide_eq_true leftMember]
        rw [show decide (left.final ∈ (splitPrefixFinal right).1) = true
          from decide_eq_true rightMember]
      · have rightAbsent :
            left.final ∉ (splitPrefixFinal right).1 := by
          intro rightMember
          exact leftMember (membership.mpr rightMember)
        rw [show decide (left.final ∈ (splitPrefixFinal left).1) = false
          from decide_eq_false leftMember]
        rw [show decide (left.final ∈ (splitPrefixFinal right).1) = false
          from decide_eq_false rightAbsent]
    _ = S5_855.repeatedInitial right.reverse :=
      (repeatedInitial_reverse right).symm

/-- The exact `S5_730` signature becomes the completed `S5_851`
head/support/final signature after reversing both words. -/
theorem sameSignature_reversed
    {left right : Word Nat}
    (same : S5_730Invariant.SameSignature left right) :
    S5_851.SameHeadSupportFinalSignature
      left.reverse right.reverse := by
  have finalEq : left.final = right.final := same.final
  refine S5_851.SameHeadSupportFinalSignature.mk ?_ ?_ ?_ ?_
  next =>
    rw [reverse_head_eq_final, reverse_head_eq_final]
    exact finalEq
  next =>
    intro letter
    simpa using same.support letter
  next =>
    rw [reverse_final_eq_head, reverse_final_eq_head]
    exact same.head
  next =>
    exact repeatedInitial_reverse_eq_of_sameSimpleFinal
      finalEq same.simpleFinal

/-- Every reversed `S5_851` basis law follows from the exact `S5_730`
basis. -/
theorem reversedS5_851AxiomDerives
    (identity : Identity Nat)
    (member : List.Mem identity (reversedBasis S5_851.basis)) :
    Derives basis identity.lhs identity.rhs := by
  change List.Mem identity S5_851.oppositeBasis at member
  rw [S5_851.oppositeBasis_eq_expected] at member
  change List.Mem identity
    [⟨S5_851.yx, S5_851.yyx⟩, ⟨S5_851.zyx, S5_851.zyzx⟩,
      ⟨S5_851.zyxx, S5_851.zxyx⟩] at member
  rcases List.eq_or_mem_of_mem_cons member with first | member
  · subst identity
    simpa [S5_851.yx, S5_851.yyx, Word.append,
      Word.singleton] using
      derivesLeftDuplication
        (Word.singleton 1) (Word.singleton 0)
  · rcases List.eq_or_mem_of_mem_cons member with second | member
    · subst identity
      simpa [S5_851.zyx, S5_851.zyzx, Word.append,
        Word.singleton] using
        derivesReturnDuplication
          (Word.singleton 2) (Word.singleton 1) (Word.singleton 0)
    · have third := List.eq_of_mem_singleton member
      subst identity
      simpa [S5_851.zyxx, S5_851.zxyx, Word.append,
        Word.singleton] using
        derivesInteriorSwap
          (Word.singleton 2) (Word.singleton 1)
          (Word.singleton 0) (Word.singleton 0)

/-- Transport a derivation from the reversed `S5_851` presentation to
the `S5_730` basis. -/
theorem transportReversedS5_851Derivation
    {left right : Word Nat}
    (derivation :
      Derives (reversedBasis S5_851.basis) left right) :
    Derives basis left right :=
  derivation.transport reversedS5_851AxiomDerives

end SemigroupBasis.CoRoots.S5_730
