import SemigroupBasis.CoRoots.S5_345Factors
import SemigroupBasis.Examples.FinalMarkerThree

namespace SemigroupBasis.CoRoots.S5_746

open SemigroupBasis
open SemigroupBasis.Examples

def xy : Word Nat := ⟨0, [1]⟩
def xxy : Word Nat := ⟨0, [0, 1]⟩
def xyz : Word Nat := ⟨0, [1, 2]⟩
def xyxz : Word Nat := ⟨0, [1, 0, 2]⟩

def leftDuplicationLaw : Identity Nat := ⟨xy, xxy⟩
def returnDuplicationLaw : Identity Nat := ⟨xyz, xyxz⟩

/-- The exact S5_746 basis `xy = xxy`, `xyz = xyxz`. -/
def basis : List (Identity Nat) :=
  [leftDuplicationLaw, returnDuplicationLaw]

private def instantiateThree
    (u v q : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => q
  | n + 3 => Word.singleton (n + 3)

/-- Delete an adjacent repeated nonempty block when a nonempty suffix remains. -/
theorem derivesLeftContraction (u v : Word Nat) :
    Derives basis ((u ++ u) ++ v) (u ++ v) := by
  have base :
      Derives basis xxy xy :=
    Derives.symm <|
      Derives.fromBasis (e := leftDuplicationLaw) <|
        List.Mem.head _
  have substituted :=
    Derives.subst base (instantiateThree u v v)
  simpa [basis, leftDuplicationLaw, xxy, xy, instantiateThree,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

/-- Delete a later repeated nonempty block across a nonempty middle and
nonempty suffix. -/
theorem derivesReturnContraction (u v q : Word Nat) :
    Derives basis (((u ++ v) ++ u) ++ q) ((u ++ v) ++ q) := by
  have base :
      Derives basis xyxz xyz :=
    Derives.symm <|
      Derives.fromBasis (e := returnDuplicationLaw) <|
        List.Mem.tail _ (List.Mem.head _)
  have substituted :=
    Derives.subst base (instantiateThree u v q)
  simpa [basis, returnDuplicationLaw, xyxz, xyz, instantiateThree,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

private def wordOfCons (x : Nat) (xs : List Nat) : Word Nat :=
  ⟨x, xs⟩

/-- Delete one repeated letter while preserving a designated nonempty final
suffix. -/
private theorem derivesDeleteOne
    (x : Nat) (middle suffix : List Nat) (suffixNonempty : suffix ≠ []) :
    Derives basis
      (wordOfCons x (middle ++ x :: suffix))
      (wordOfCons x (middle ++ suffix)) := by
  cases middle with
  | nil =>
      obtain ⟨suffixHead, suffixTail, rfl⟩ :=
        List.exists_cons_of_ne_nil suffixNonempty
      simpa [wordOfCons, Word.append, Word.singleton,
        Word.append_assoc] using
          derivesLeftContraction
            (Word.singleton x) (wordOfCons suffixHead suffixTail)
  | cons middleHead middleTail =>
      obtain ⟨suffixHead, suffixTail, rfl⟩ :=
        List.exists_cons_of_ne_nil suffixNonempty
      simpa [wordOfCons, Word.append, Word.singleton,
        Word.append_assoc] using
          derivesReturnContraction
            (Word.singleton x)
            (wordOfCons middleHead middleTail)
            (wordOfCons suffixHead suffixTail)

/-- Delete every later occurrence of the initial letter from a prefix while
preserving a fixed nonempty final suffix. -/
private theorem derivesDeleteAfter :
    ∀ (x : Nat) (middle rest suffix : List Nat), suffix ≠ [] →
      Derives basis
        (wordOfCons x (middle ++ rest ++ suffix))
        (wordOfCons x
          (middle ++ rest.filter (fun y => decide (y ≠ x)) ++ suffix))
  | x, middle, [], suffix, _ => by
      simpa using Derives.refl (wordOfCons x (middle ++ suffix))
  | x, middle, y :: ys, suffix, suffixNonempty => by
      by_cases equal : y = x
      · subst y
        have first :=
          derivesDeleteOne x middle (ys ++ suffix) (by
            simp [suffixNonempty])
        have remaining :=
          derivesDeleteAfter x middle ys suffix suffixNonempty
        exact Derives.trans
          (by simpa [List.append_assoc] using first)
          (by simpa using remaining)
      · have remaining :=
          derivesDeleteAfter
            x (middle ++ [y]) ys suffix suffixNonempty
        simpa [equal, List.append_assoc] using remaining

/-- Normalize a nonempty prefix to its duplicate-free first-occurrence
sequence while preserving one final letter. -/
private theorem derivesNormalizePrefix :
    ∀ (x : Nat) (xs : List Nat) (final : Nat),
      match firstOccurrenceSequence (x :: xs) with
      | [] => False
      | y :: ys =>
          Derives basis
            (wordOfCons x (xs ++ [final]))
            (wordOfCons y (ys ++ [final]))
  | x, [], final => by
      exact Derives.refl _
  | x, y :: ys, final => by
      have suffixNormal :=
        derivesNormalizePrefix y ys final
      cases sequenceShape :
          firstOccurrenceSequence (y :: ys) with
      | nil =>
          simp [firstOccurrenceSequence] at sequenceShape
      | cons z zs =>
          rw [sequenceShape] at suffixNormal
          have prefixed :=
            Derives.prepend (Word.singleton x) suffixNormal
          have deleted :=
            derivesDeleteAfter x [] (z :: zs) [final] (by simp)
          have reduced :
              firstOccurrenceSequence (x :: y :: ys) =
                x :: (z :: zs).filter
                  (fun letter => decide (letter ≠ x)) := by
            change
              x :: (firstOccurrenceSequence (y :: ys)).filter
                    (fun letter => decide (letter ≠ x)) =
                x :: (z :: zs).filter
                    (fun letter => decide (letter ≠ x))
            rw [sequenceShape]
          rw [reduced]
          exact Derives.trans
            (by
              simpa [wordOfCons, Word.append, Word.singleton,
                Word.append_assoc, List.append_assoc] using prefixed)
            (by
              simpa [wordOfCons, List.append_assoc] using deleted)
termination_by
  _ xs _ => xs.length

/-- The canonical prefix is the first-occurrence sequence of everything
strictly before the final letter. -/
def normalPrefix (word : Word Nat) : List Nat :=
  firstOccurrenceSequence (splitPrefixFinal word).1

/-- Canonical S5_746 word: duplicate-free prefix, followed by the original
final letter. -/
def normalWord (word : Word Nat) : Word Nat :=
  wordOfPrefixFinal (normalPrefix word) (splitPrefixFinal word).2

theorem toList_eq_splitPrefixFinal (word : Word Nat) :
    word.toList =
      (splitPrefixFinal word).1 ++ [(splitPrefixFinal word).2] := by
  have reconstructed :=
    congrArg Word.toList (wordOfPrefixFinal_split word)
  rw [toList_wordOfPrefixFinal] at reconstructed
  exact reconstructed.symm

private def removeLetter
    (selected : Nat) (letters : List Nat) : List Nat :=
  letters.filter (fun letter => decide (letter ≠ selected))

private theorem firstOccurrenceSequence_cons_eq
    (letter : Nat) (rest : List Nat) :
    firstOccurrenceSequence (letter :: rest) =
      letter :: removeLetter letter
        (firstOccurrenceSequence rest) :=
  rfl

private theorem removeLetter_append
    (selected : Nat) (left right : List Nat) :
    removeLetter selected (left ++ right) =
      removeLetter selected left ++ removeLetter selected right := by
  simp [removeLetter, List.filter_append]

/-- Appending a final letter either leaves the first-occurrence sequence
unchanged or appends that new letter once. -/
theorem firstOccurrenceSequence_append_final
    (final : Nat) :
    ∀ before : List Nat,
      firstOccurrenceSequence (before ++ [final]) =
        if final ∈ before then
          firstOccurrenceSequence before
        else
          firstOccurrenceSequence before ++ [final]
  | [] => by
      simp [firstOccurrenceSequence]
  | letter :: rest => by
      have induction :=
        firstOccurrenceSequence_append_final final rest
      by_cases equal : letter = final
      · subst letter
        rw [List.cons_append, firstOccurrenceSequence_cons_eq,
          induction]
        simp only [List.mem_cons, true_or, if_true]
        by_cases present : final ∈ rest
        · rw [if_pos present]
          exact
            (firstOccurrenceSequence_cons_eq final rest).symm
        · rw [if_neg present, removeLetter_append]
          simpa [removeLetter] using
            (firstOccurrenceSequence_cons_eq final rest).symm
      · have reverse : final ≠ letter := Ne.symm equal
        rw [List.cons_append, firstOccurrenceSequence_cons_eq,
          induction]
        by_cases present : final ∈ rest
        · have fullPresent : final ∈ letter :: rest :=
            List.Mem.tail letter present
          rw [if_pos present, if_pos fullPresent]
          exact
            (firstOccurrenceSequence_cons_eq letter rest).symm
        · have fullAbsent : final ∉ letter :: rest := by
            simp [reverse, present]
          rw [if_neg present, if_neg fullAbsent,
            removeLetter_append]
          have keepFinal :
              removeLetter letter [final] = [final] := by
            simp [removeLetter, reverse]
          rw [keepFinal]
          rfl

/-- Every word derives to its explicit prefix-first-occurrence/final normal
form. -/
theorem derivesNormal (word : Word Nat) :
    Derives basis word (normalWord word) := by
  generalize splitShape : splitPrefixFinal word = split
  rcases split with ⟨stem, final⟩
  rw [normalWord, normalPrefix, splitShape]
  have reconstructed :
      wordOfPrefixFinal stem final = word := by
    have result := wordOfPrefixFinal_split word
    rw [splitShape] at result
    exact result
  cases stem with
  | nil =>
      have reflexive :
          Derives basis
            (wordOfPrefixFinal [] final)
            (wordOfPrefixFinal
              (firstOccurrenceSequence []) final) := by
        exact Derives.refl _
      rw [reconstructed] at reflexive
      exact reflexive
  | cons x xs =>
      have normalized :=
        derivesNormalizePrefix x xs final
      cases sequenceShape :
          firstOccurrenceSequence (x :: xs) with
      | nil =>
          simp [firstOccurrenceSequence] at sequenceShape
      | cons y ys =>
          rw [sequenceShape] at normalized
          have sourceEq :
              wordOfCons x (xs ++ [final]) =
                wordOfPrefixFinal (x :: xs) final := by
            apply Word.toList_injective
            rw [toList_wordOfPrefixFinal]
            rfl
          have targetEq :
              wordOfCons y (ys ++ [final]) =
                wordOfPrefixFinal (y :: ys) final := by
            apply Word.toList_injective
            rw [toList_wordOfPrefixFinal]
            rfl
          have result :
              Derives basis
                (wordOfPrefixFinal (x :: xs) final)
                (wordOfPrefixFinal
                  (firstOccurrenceSequence (x :: xs)) final) := by
            simpa [sourceEq, targetEq, sequenceShape] using normalized
          rw [reconstructed] at result
          simpa [sequenceShape] using result

theorem normalWord_eq_of_invariants
    {left right : Word Nat}
    (stem :
      firstOccurrenceSequence (splitPrefixFinal left).1 =
        firstOccurrenceSequence (splitPrefixFinal right).1)
    (final :
      (splitPrefixFinal left).2 =
        (splitPrefixFinal right).2) :
    normalWord left = normalWord right := by
  unfold normalWord normalPrefix
  rw [stem, final]

/-- Syntactic completeness once the exact prefix-order/final invariants are
known. -/
theorem derivesOfInvariantEq
    {left right : Word Nat}
    (stem :
      firstOccurrenceSequence (splitPrefixFinal left).1 =
        firstOccurrenceSequence (splitPrefixFinal right).1)
    (final :
      (splitPrefixFinal left).2 =
        (splitPrefixFinal right).2) :
    Derives basis left right := by
  have leftNormal := derivesNormal left
  have rightNormal := derivesNormal right
  rw [normalWord_eq_of_invariants stem final] at leftNormal
  exact Derives.trans leftNormal rightNormal.symm

/-- Generic completeness bridge for the S5_746 normal form. -/
theorem basis_complete_of_invariants
    {S : Type}
    (semigroup : Semigroup S)
    (modelsSemigroup : Models semigroup basis)
    (validPrefix :
      ∀ identity : Identity Nat, identity.SatisfiedBy semigroup →
        firstOccurrenceSequence (splitPrefixFinal identity.lhs).1 =
          firstOccurrenceSequence (splitPrefixFinal identity.rhs).1)
    (validFinal :
      ∀ identity : Identity Nat, identity.SatisfiedBy semigroup →
        (splitPrefixFinal identity.lhs).2 =
          (splitPrefixFinal identity.rhs).2) :
    BasisFor semigroup basis := by
  refine ⟨modelsSemigroup, ?_⟩
  intro identity valid
  exact derivesOfInvariantEq
    (validPrefix identity valid)
    (validFinal identity valid)

end SemigroupBasis.CoRoots.S5_746
