import SemigroupBasis.CoRoots.S5_1092
import SemigroupBasis.Examples.LeftRegularBandThree

namespace SemigroupBasis.CoRoots.S5_1092

open SemigroupBasis
open SemigroupBasis.Examples

private abbrev ListDerives : List Nat → List Nat → Prop :=
  SemigroupBasis.CoRoots.S5_107.ListDerives basis

def lastOccurrenceSequence : List Nat → List Nat
  | [] => []
  | letter :: rest =>
      if letter ∈ rest then
        lastOccurrenceSequence rest
      else
        letter :: lastOccurrenceSequence rest

def regularBandNormalList (letters : List Nat) : List Nat :=
  firstOccurrenceSequence letters ++ lastOccurrenceSequence letters

private theorem mem_firstOccurrenceSequence_iff
    (selected : Nat) :
    ∀ letters : List Nat,
      selected ∈ firstOccurrenceSequence letters ↔ selected ∈ letters
  | [] => by simp [firstOccurrenceSequence]
  | letter :: rest => by
      by_cases equal : selected = letter
      · subst letter
        simp [firstOccurrenceSequence]
      · simp [firstOccurrenceSequence, equal,
          mem_firstOccurrenceSequence_iff selected rest]

private theorem firstOccurrenceSequence_append_singleton
    (selected : Nat) :
    ∀ letters : List Nat,
      firstOccurrenceSequence (letters ++ [selected]) =
        if selected ∈ letters then
          firstOccurrenceSequence letters
        else
          firstOccurrenceSequence letters ++ [selected]
  | [] => by simp [firstOccurrenceSequence]
  | letter :: rest => by
      have induction :=
        firstOccurrenceSequence_append_singleton selected rest
      by_cases hEq : letter = selected
      · subst letter
        by_cases hMem : selected ∈ rest <;>
          simp [firstOccurrenceSequence, induction, hMem, List.filter_append]
      · have hReverse : selected ≠ letter := Ne.symm hEq
        by_cases hMem : selected ∈ rest <;>
          simp [firstOccurrenceSequence, induction, hReverse, hMem,
            List.filter_append]

theorem lastOccurrenceSequence_eq_reverse_firstOccurrenceSequence :
    ∀ letters : List Nat,
      lastOccurrenceSequence letters =
        (firstOccurrenceSequence letters.reverse).reverse
  | [] => by simp [lastOccurrenceSequence, firstOccurrenceSequence]
  | letter :: rest => by
      have induction :=
        lastOccurrenceSequence_eq_reverse_firstOccurrenceSequence rest
      rw [lastOccurrenceSequence, List.reverse_cons,
        firstOccurrenceSequence_append_singleton]
      by_cases hMem : letter ∈ rest
      · have hReverse : letter ∈ rest.reverse := by simpa using hMem
        rw [if_pos hMem, if_pos hReverse, induction]
      · have hReverse : letter ∉ rest.reverse := by simpa using hMem
        rw [if_neg hMem, if_neg hReverse, induction]
        simp [List.reverse_append]

theorem listDerivesDeleteBetweenGuards
    (letter : Nat)
    (left right : List Nat) :
    ListDerives
      ([letter] ++ left ++ [letter] ++ right ++ [letter])
      ([letter] ++ left ++ right ++ [letter]) := by
  cases left with
  | nil =>
      have base :
          ListDerives [letter, letter] [letter] :=
        SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
          (derivesIdempotenceContraction (Word.singleton letter))
      simpa [List.append_assoc] using
        (SemigroupBasis.CoRoots.S5_107.ListDerives.context
          ([] : List Nat) (right ++ [letter]) base)
  | cons leftHead leftTail =>
      cases right with
      | nil =>
          have base :
              ListDerives [letter, letter] [letter] :=
            SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
              (derivesIdempotenceContraction (Word.singleton letter))
          simpa [List.append_assoc] using
            (SemigroupBasis.CoRoots.S5_107.ListDerives.context
              ([letter] ++ leftHead :: leftTail) ([] : List Nat) base)
      | cons rightHead rightTail =>
          have core :=
            SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
              (derivesRegularContraction
                (Word.singleton letter)
                (SemigroupBasis.CoRoots.S5_107.listWordOfCons leftHead leftTail)
                (SemigroupBasis.CoRoots.S5_107.listWordOfCons rightHead rightTail))
          simpa [SemigroupBasis.CoRoots.S5_107.listWordOfCons, List.append_assoc] using core

private theorem listDerivesDeleteWithPrefixAndRightGuard
    (letter : Nat)
    (pref suffix guard : List Nat)
    (prefixHas : letter ∈ pref)
    (guardHas : letter ∈ guard) :
    ListDerives
      ((pref ++ letter :: suffix) ++ guard)
      ((pref ++ suffix) ++ guard) := by
  obtain ⟨prefixBefore, prefixAfter, prefixSplit⟩ :=
    List.mem_iff_append.mp prefixHas
  obtain ⟨guardBefore, guardAfter, guardSplit⟩ :=
    List.mem_iff_append.mp guardHas
  have core :=
    listDerivesDeleteBetweenGuards letter prefixAfter (suffix ++ guardBefore)
  have contextual :=
    SemigroupBasis.CoRoots.S5_107.ListDerives.context prefixBefore guardAfter core
  simpa [prefixSplit, guardSplit, List.append_assoc] using contextual

private theorem listDerivesDeleteWithLeftAndRightGuard
    (letter : Nat)
    (leftGuard pref suffix : List Nat)
    (leftHas : letter ∈ leftGuard)
    (rightHas : letter ∈ suffix) :
    ListDerives
      ((leftGuard ++ pref) ++ letter :: suffix)
      ((leftGuard ++ pref) ++ suffix) := by
  obtain ⟨leftBefore, leftAfter, leftSplit⟩ :=
    List.mem_iff_append.mp leftHas
  obtain ⟨rightBefore, rightAfter, rightSplit⟩ :=
    List.mem_iff_append.mp rightHas
  have core :=
    listDerivesDeleteBetweenGuards letter (leftAfter ++ pref) rightBefore
  have contextual :=
    SemigroupBasis.CoRoots.S5_107.ListDerives.context leftBefore rightAfter core
  simpa [leftSplit, rightSplit, List.append_assoc] using contextual

private theorem listDerivesDeleteAllWithGuards
    (letter : Nat)
    (guard : List Nat)
    (guardHas : letter ∈ guard) :
    ∀ (pref middle : List Nat),
      letter ∈ pref →
      ListDerives
        ((pref ++ middle) ++ guard)
        ((pref ++ middle.filter (fun selected => decide (selected ≠ letter))) ++ guard)
  | pref, [], _ => by
      simp only [List.filter_nil]
      exact SemigroupBasis.CoRoots.S5_107.ListDerives.refl _
  | pref, selected :: rest, prefixHas => by
      by_cases hEq : selected = letter
      · subst selected
        have deleteCurrent :=
          listDerivesDeleteWithPrefixAndRightGuard
            letter pref rest guard prefixHas guardHas
        have deleteRest :=
          listDerivesDeleteAllWithGuards letter guard guardHas pref rest prefixHas
        simpa [List.append_assoc] using deleteCurrent.trans deleteRest
      · have extendedHas : letter ∈ pref ++ [selected] :=
          List.mem_append.mpr (Or.inl prefixHas)
        have deleteRest :=
          listDerivesDeleteAllWithGuards
            letter guard guardHas (pref ++ [selected]) rest extendedHas
        simpa [hEq, List.append_assoc] using deleteRest

private theorem listDerivesFirstCopyNormalize :
    ∀ (letters guard : List Nat),
      (∀ letter, letter ∈ letters → letter ∈ guard) →
      ListDerives
        (letters ++ guard)
        (firstOccurrenceSequence letters ++ guard)
  | [], guard, _ => by
      simpa [firstOccurrenceSequence] using
        (SemigroupBasis.CoRoots.S5_107.ListDerives.refl guard)
  | letter :: rest, guard, support => by
      have normalizeRest :=
        listDerivesFirstCopyNormalize rest guard
          (fun selected hSelected => support selected (List.mem_cons_of_mem letter hSelected))
      have prefixed :=
        SemigroupBasis.CoRoots.S5_107.ListDerives.prepend [letter] normalizeRest
      have guardHas : letter ∈ guard :=
        support letter (by simp)
      have deleteDuplicates :=
        listDerivesDeleteAllWithGuards
          letter guard guardHas [letter] (firstOccurrenceSequence rest) (by simp)
      simpa [firstOccurrenceSequence, List.append_assoc] using
        prefixed.trans deleteDuplicates

private theorem listDerivesLastCopyNormalize :
    ∀ (pref letters : List Nat),
      (∀ letter, letter ∈ letters → letter ∈ pref) →
      ListDerives
        (pref ++ letters)
        (pref ++ lastOccurrenceSequence letters)
  | pref, [], _ => by
      simpa [lastOccurrenceSequence] using
        (SemigroupBasis.CoRoots.S5_107.ListDerives.refl pref)
  | pref, letter :: rest, support => by
      by_cases hLater : letter ∈ rest
      · have deleteCurrent :=
          listDerivesDeleteWithLeftAndRightGuard
            letter pref [] rest (support letter (by simp)) hLater
        have normalizeRest :=
          listDerivesLastCopyNormalize pref rest
            (fun selected hSelected => support selected (List.mem_cons_of_mem letter hSelected))
        have deleteCurrent' :
            SemigroupBasis.CoRoots.S5_107.ListDerives basis
              (pref ++ letter :: rest) (pref ++ rest) := by
          simpa using deleteCurrent
        simpa [lastOccurrenceSequence, hLater, List.append_assoc] using
          deleteCurrent'.trans normalizeRest
      · have extendedSupport :
          ∀ selected, selected ∈ rest → selected ∈ pref ++ [letter] :=
        fun selected hSelected =>
          List.mem_append.mpr
            (Or.inl (support selected (List.mem_cons_of_mem letter hSelected)))
        have normalizeRest :=
          listDerivesLastCopyNormalize (pref ++ [letter]) rest extendedSupport
        simpa [lastOccurrenceSequence, hLater, List.append_assoc] using normalizeRest

theorem listDerivesRegularBandNormal (word : Word Nat) :
    ListDerives word.toList (regularBandNormalList word.toList) := by
  have duplicate :
      ListDerives word.toList (word.toList ++ word.toList) := by
    simpa using
      (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
        (derivesIdempotenceExpansion word))
  have normalizeFirst :=
    listDerivesFirstCopyNormalize word.toList word.toList
      (fun _ hLetter => hLetter)
  have normalizeLast :=
    listDerivesLastCopyNormalize
      (firstOccurrenceSequence word.toList) word.toList
      (fun selected hSelected =>
        (mem_firstOccurrenceSequence_iff selected word.toList).mpr hSelected)
  exact duplicate.trans (normalizeFirst.trans normalizeLast)

theorem derives_of_same_occurrence_sequences
    (lhs rhs : Word Nat)
    (firstEq :
      firstOccurrenceSequence lhs.toList =
        firstOccurrenceSequence rhs.toList)
    (lastEq :
      lastOccurrenceSequence lhs.toList =
        lastOccurrenceSequence rhs.toList) :
    Derives basis lhs rhs := by
  have normalEq :
      regularBandNormalList lhs.toList =
        regularBandNormalList rhs.toList := by
    simp only [regularBandNormalList, firstEq, lastEq]
  have lhsNormal := listDerivesRegularBandNormal lhs
  have rhsNormal := listDerivesRegularBandNormal rhs
  rw [normalEq] at lhsNormal
  have listDerivation := lhsNormal.trans rhsNormal.symm
  cases lhs with
  | mk lhsHead lhsTail =>
      cases rhs with
      | mk rhsHead rhsTail =>
          simpa [SemigroupBasis.CoRoots.S5_107.listWordOfCons] using
            SemigroupBasis.CoRoots.S5_107.ListDerives.toWord listDerivation

theorem basis_complete_of_occurrence_separation
    {carrier : Type}
    (semigroup : Semigroup carrier)
    (models : Models semigroup basis)
    (separates :
      ∀ e : Identity Nat,
        e.SatisfiedBy semigroup →
          firstOccurrenceSequence e.lhs.toList =
            firstOccurrenceSequence e.rhs.toList ∧
          lastOccurrenceSequence e.lhs.toList =
            lastOccurrenceSequence e.rhs.toList) :
    BasisFor semigroup basis := by
  refine ⟨models, ?_⟩
  intro e valid
  obtain ⟨firstEq, lastEq⟩ := separates e valid
  exact derives_of_same_occurrence_sequences e.lhs e.rhs firstEq lastEq

end SemigroupBasis.CoRoots.S5_1092
