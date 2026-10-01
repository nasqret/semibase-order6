import SemigroupBasis.CoRoots.S5_1089
import SemigroupBasis.Examples.LeftRegularBandThree

namespace SemigroupBasis.CoRoots.S5_1089

open SemigroupBasis
open SemigroupBasis.Examples

private abbrev ListDerives : List Nat → List Nat → Prop :=
  SemigroupBasis.CoRoots.S5_107.ListDerives basis

private abbrev wordOfCons :=
  SemigroupBasis.CoRoots.S5_107.listWordOfCons

/-- Keep precisely the last occurrence of every variable. -/
def lastOccurrenceSequence : List Nat → List Nat
  | [] => []
  | letter :: rest =>
      if letter ∈ rest then
        lastOccurrenceSequence rest
      else
        letter :: lastOccurrenceSequence rest

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
      by_cases equal : letter = selected
      · subst letter
        by_cases member : selected ∈ rest <;>
          simp [firstOccurrenceSequence, induction, member,
            List.filter_append]
      · have reverseEqual : selected ≠ letter := Ne.symm equal
        by_cases member : selected ∈ rest <;>
          simp [firstOccurrenceSequence, induction, equal, reverseEqual,
            member, List.filter_append]

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
      by_cases member : letter ∈ rest
      · have reverseMember : letter ∈ rest.reverse := by
          simpa using member
        rw [if_pos member, if_pos reverseMember, induction]
      · have reverseAbsent : letter ∉ rest.reverse := by
          simpa using member
        rw [if_neg member, if_neg reverseAbsent, induction]
        simp [List.reverse_append]

/-- Canonical list: the original first variable followed by all variables
in last-occurrence order. -/
def r2s2NormalList (word : Word Nat) : List Nat :=
  word.head :: lastOccurrenceSequence word.toList

def r2s2NormalWord (word : Word Nat) : Word Nat :=
  wordOfCons word.head (lastOccurrenceSequence word.toList)

def SameR2S2Signature (left right : Word Nat) : Prop :=
  left.head = right.head ∧
    lastOccurrenceSequence left.toList =
      lastOccurrenceSequence right.toList

/-- Delete a nonfinal occurrence after a nonempty prefix. -/
theorem listDerivesDeleteEarlier
    (prefixHead letter : Nat)
    (prefixTail middle suffix : List Nat) :
    ListDerives
      ((prefixHead :: prefixTail) ++ [letter] ++
        middle ++ [letter] ++ suffix)
      ((prefixHead :: prefixTail) ++ middle ++ [letter] ++ suffix) := by
  cases middle with
  | nil =>
      have adjacent :=
        SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
          (derivesIdempotenceContraction (Word.singleton letter))
      simpa [List.append_assoc] using
        (SemigroupBasis.CoRoots.S5_107.ListDerives.context
          (prefixHead :: prefixTail) suffix adjacent)
  | cons middleHead middleTail =>
      have core :=
        SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
          (derivesR2S2Contraction
            (wordOfCons prefixHead prefixTail)
            (wordOfCons middleHead middleTail)
            (Word.singleton letter))
      simpa [wordOfCons, Word.append, Word.singleton,
        List.append_assoc] using core.append suffix

private theorem listDerivesDeleteCurrent
    (prefixHead letter : Nat)
    (prefixTail rest : List Nat)
    (later : letter ∈ rest) :
    ListDerives
      ((prefixHead :: prefixTail) ++ letter :: rest)
      ((prefixHead :: prefixTail) ++ rest) := by
  obtain ⟨before, after, split⟩ :=
    List.mem_iff_append.mp later
  have deleted :=
    listDerivesDeleteEarlier
      prefixHead letter prefixTail before after
  simpa [split, List.append_assoc] using deleted

/-- Normalize a suffix while preserving an arbitrary nonempty prefix. -/
private theorem listDerivesLastOccurrenceWithPrefix
    (prefixHead : Nat) :
    ∀ (prefixTail letters : List Nat),
      ListDerives
        ((prefixHead :: prefixTail) ++ letters)
        ((prefixHead :: prefixTail) ++
          lastOccurrenceSequence letters)
  | prefixTail, [] => by
      simpa [lastOccurrenceSequence] using
        (SemigroupBasis.CoRoots.S5_107.ListDerives.refl
          (prefixHead :: prefixTail))
  | prefixTail, letter :: rest => by
      by_cases later : letter ∈ rest
      · have deleteCurrent :=
          listDerivesDeleteCurrent
            prefixHead letter prefixTail rest later
        have normalizeRest :=
          listDerivesLastOccurrenceWithPrefix
            prefixHead prefixTail rest
        simpa [lastOccurrenceSequence, later, List.append_assoc] using
          deleteCurrent.trans normalizeRest
      · have normalizeRest :=
          listDerivesLastOccurrenceWithPrefix
            prefixHead (prefixTail ++ [letter]) rest
        simpa [lastOccurrenceSequence, later, List.append_assoc] using
          normalizeRest

/-- Every word derives to its first-variable/last-occurrence normal list. -/
theorem listDerivesR2S2Normal (word : Word Nat) :
    ListDerives word.toList (r2s2NormalList word) := by
  cases word with
  | mk head tail =>
      have tailNormal :=
        listDerivesLastOccurrenceWithPrefix head [] tail
      by_cases headLater : head ∈ tail
      · simpa [r2s2NormalList, lastOccurrenceSequence, headLater,
          Word.toList] using
          tailNormal
      · have duplicate :=
          (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
            (derivesIdempotenceExpansion
              (Word.singleton head))).append
                (lastOccurrenceSequence tail)
        simpa [r2s2NormalList, lastOccurrenceSequence, headLater,
          Word.toList, List.append_assoc] using tailNormal.trans duplicate

theorem derivesR2S2Normal (word : Word Nat) :
    Derives basis word (r2s2NormalWord word) := by
  have listDerivation := listDerivesR2S2Normal word
  cases word with
  | mk head tail =>
      simpa [r2s2NormalList, r2s2NormalWord, wordOfCons] using
        SemigroupBasis.CoRoots.S5_107.ListDerives.toWord listDerivation

theorem derives_of_same_head_and_last_occurrences
    {left right : Word Nat}
    (headEqual : left.head = right.head)
    (lastEqual :
      lastOccurrenceSequence left.toList =
        lastOccurrenceSequence right.toList) :
    Derives basis left right := by
  have leftNormal := derivesR2S2Normal left
  have rightNormal := derivesR2S2Normal right
  have normalEqual :
      r2s2NormalWord left = r2s2NormalWord right := by
    simp [r2s2NormalWord, headEqual, lastEqual]
  exact leftNormal.trans <| by
    rw [normalEqual]
    exact rightNormal.symm

theorem derives_of_sameR2S2Signature
    {left right : Word Nat}
    (same : SameR2S2Signature left right) :
    Derives basis left right :=
  derives_of_same_head_and_last_occurrences same.1 same.2

theorem basis_complete_of_head_last_separation
    {carrier : Type}
    (semigroup : Semigroup carrier)
    (models : Models semigroup basis)
    (separates :
      ∀ identity : Identity Nat,
        identity.SatisfiedBy semigroup →
          identity.lhs.head = identity.rhs.head ∧
          lastOccurrenceSequence identity.lhs.toList =
            lastOccurrenceSequence identity.rhs.toList) :
    BasisFor semigroup basis := by
  refine ⟨models, ?_⟩
  intro identity valid
  obtain ⟨headEqual, lastEqual⟩ := separates identity valid
  exact derives_of_same_head_and_last_occurrences
    headEqual lastEqual

end SemigroupBasis.CoRoots.S5_1089
