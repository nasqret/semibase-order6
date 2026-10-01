import SemigroupBasis.CoRoots.Order6Day8.S3_6.Rank014SemanticBoundary
import SemigroupBasis.CoRoots.S5_107ListDerives

/-!
# Unrestricted repeated-final insertion for the exact Rank014 basis

The complete `S5_636` lower calculus inserts a selected even pair *before*
the unchanged repeated final.  The exact displayed sixth and tenth laws,
together with the already-proved guarded gather law, transport that pair
across the final.  No bounded alphabet, finite witness, or class endpoint is
used.
-/

namespace SemigroupBasis.CoRoots.Order6Day8.S3_6.Rank014RepeatedInsertion

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.Order6Day8.S3_6.Rank014SemanticBoundary

private abbrev ListDerives : List Nat → List Nat → Prop :=
  SemigroupBasis.CoRoots.S5_107.ListDerives basis

private theorem derives_of_listDerives_toList
    (left right : Word Nat)
    (derivation : ListDerives left.toList right.toList) :
    Derives basis left right := by
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail =>
          simpa [SemigroupBasis.CoRoots.S5_107.listWordOfCons] using
            SemigroupBasis.CoRoots.S5_107.ListDerives.toWord derivation

private theorem toList_eq_splitPrefixFinal (word : Word Nat) :
    word.toList =
      (splitPrefixFinal word).1 ++ [(splitPrefixFinal word).2] := by
  have reconstructed :=
    congrArg Word.toList (wordOfPrefixFinal_split word)
  rw [toList_wordOfPrefixFinal] at reconstructed
  exact reconstructed.symm

private def instantiateThree
    (first second third : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | letter + 3 => Word.singleton (letter + 3)

/-- Exact displayed law six transports a square across its enclosing letter. -/
theorem derivesSquareTransport (first selected : Word Nat) :
    Derives basis
      (((first ++ first) ++ selected) ++ selected)
      (((first ++ selected) ++ selected) ++ first) := by
  have primitive :
      Derives basis (Word.mk 0 [0, 1, 1]) (Word.mk 0 [1, 1, 0]) :=
    Derives.fromBasis
      (e :=
        (⟨Word.mk 0 [0, 1, 1], Word.mk 0 [1, 1, 0]⟩ : Identity Nat))
      (by decide)
  have substituted :=
    Derives.subst primitive (instantiateThree first selected selected)
  simpa [instantiateThree, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- Exact displayed law ten transports a square past an arbitrary nonempty gap. -/
theorem derivesSeparatedSquareTransport
    (first gap selected : Word Nat) :
    Derives basis
      ((((first ++ first) ++ gap) ++ selected) ++ selected)
      ((((first ++ gap) ++ selected) ++ selected) ++ first) := by
  have primitive :
      Derives basis
        (Word.mk 0 [0, 1, 2, 2]) (Word.mk 0 [1, 2, 2, 0]) :=
    Derives.fromBasis
      (e :=
        (⟨Word.mk 0 [0, 1, 2, 2],
          Word.mk 0 [1, 2, 2, 0]⟩ : Identity Nat))
      (by decide)
  have substituted :=
    Derives.subst primitive (instantiateThree first gap selected)
  simpa [instantiateThree, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- Exact displayed law eleven adds two copies of a repeated final block. -/
theorem derivesFinalSelfPair (first gap : Word Nat) :
    Derives basis
      ((first ++ gap) ++ first)
      ((((first ++ gap) ++ first) ++ first) ++ first) := by
  have primitive :
      Derives basis (Word.mk 0 [1, 0]) (Word.mk 0 [1, 0, 0, 0]) :=
    Derives.fromBasis
      (e :=
        (⟨Word.mk 0 [1, 0], Word.mk 0 [1, 0, 0, 0]⟩ : Identity Nat))
      (by decide)
  have substituted :=
    Derives.subst primitive (instantiateThree first gap gap)
  simpa [instantiateThree, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- Any already-seen letter can be appended without changing first order. -/
theorem firstOccurrenceSequence_append_seen
    (letters : List Nat) (final : Nat) (seen : final ∈ letters) :
    firstOccurrenceSequence (letters ++ [final]) =
      firstOccurrenceSequence letters := by
  induction letters with
  | nil =>
      simp at seen
  | cons first rest induction =>
      by_cases equal : first = final
      · subst first
        change
          final ::
              (firstOccurrenceSequence (rest ++ [final])).filter
                (fun selected => decide (selected ≠ final)) =
            final ::
              (firstOccurrenceSequence rest).filter
                (fun selected => decide (selected ≠ final))
        congr 1
        let keep : Nat → Bool :=
          fun selected => decide (selected ≠ final)
        change
          (firstOccurrenceSequence (rest ++ [final])).filter keep =
            (firstOccurrenceSequence rest).filter keep
        calc
          (firstOccurrenceSequence (rest ++ [final])).filter keep =
              firstOccurrenceSequence ((rest ++ [final]).filter keep) :=
            (firstOccurrenceSequence_filter keep (rest ++ [final])).symm
          _ = firstOccurrenceSequence (rest.filter keep) := by
            simp [keep]
          _ = (firstOccurrenceSequence rest).filter keep :=
            firstOccurrenceSequence_filter keep rest
      · have tailSeen : final ∈ rest := by
          rcases List.mem_cons.mp seen with same | member
          · exact False.elim (equal same.symm)
          · exact member
        change
          first ::
              (firstOccurrenceSequence (rest ++ [final])).filter
                (fun selected => decide (selected ≠ first)) =
            first ::
              (firstOccurrenceSequence rest).filter
                (fun selected => decide (selected ≠ first))
        rw [induction tailSeen]

/-- Every multiplicity at least two is unchanged by adding an even pair. -/
theorem s5_636Exponent_add_two
    (count : Nat) (repeated : 2 ≤ count) :
    SemigroupBasis.CoRoots.S5_636.s5_636Exponent count =
      SemigroupBasis.CoRoots.S5_636.s5_636Exponent (count + 2) := by
  unfold SemigroupBasis.CoRoots.S5_636.s5_636Exponent
    periodTwoFromTwoExponent
  have current : ¬ count < 2 := by omega
  have next : ¬ count + 2 < 2 := by omega
  simp only [if_neg current, if_neg next]
  omega

/-- The complete exact lower calculus appends a pair of any repeated letter. -/
theorem lowerDerivesAppendSeenPair
    (stem : Word Nat) (selected : Nat)
    (repeated : 2 ≤ stem.toList.count selected) :
    Derives lowerBasis stem
      ((stem ++ Word.singleton selected) ++ Word.singleton selected) := by
  have seen : selected ∈ stem.toList :=
    List.count_pos_iff.mp (by omega)
  apply SemigroupBasis.CoRoots.S5_636.s5_636DerivesOfInvariantEq
    stem ((stem ++ Word.singleton selected) ++ Word.singleton selected)
  · simp only [Word.toList_append, Word.toList_singleton]
    rw [firstOccurrenceSequence_append_seen
      (stem.toList ++ [selected]) selected (by simp),
      firstOccurrenceSequence_append_seen stem.toList selected seen]
  · intro letter
    simp only [Word.toList_append, Word.toList_singleton,
      List.count_append]
    by_cases equal : letter = selected
    · subst letter
      simp only [List.count_singleton_self]
      simpa [Nat.add_assoc] using
        s5_636Exponent_add_two (stem.toList.count selected) repeated
    · have singletonZero : [selected].count letter = 0 :=
        List.count_eq_zero.mpr (by simpa using equal)
      simp [singletonZero]

private theorem listDerivesFinalSelfPair
    (stem : List Nat) (final : Nat) (seen : final ∈ stem) :
    ListDerives (stem ++ [final])
      (stem ++ [final, final, final]) := by
  obtain ⟨before, gap, shape⟩ := List.mem_iff_append.mp seen
  cases gap with
  | nil =>
      have expanded :=
        SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
          (derivesPower (Word.singleton final))
      simpa [shape, Word.toList_append, Word.toList_singleton,
        List.append_assoc] using
        SemigroupBasis.CoRoots.S5_107.ListDerives.prepend before expanded
  | cons gapFirst gapRest =>
      let gapWord :=
        SemigroupBasis.CoRoots.S5_107.listWordOfCons gapFirst gapRest
      have expanded :=
        SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
          (derivesFinalSelfPair (Word.singleton final) gapWord)
      simpa [shape, gapWord,
        SemigroupBasis.CoRoots.S5_107.listWordOfCons,
        Word.toList, Word.toList_append, Word.toList_singleton,
        List.append_assoc] using
        SemigroupBasis.CoRoots.S5_107.ListDerives.prepend before expanded

/-- The repeated final itself can always receive its own final even pair. -/
theorem derivesDuplicateRepeatedFinalPair
    (word : Word Nat)
    (seen : (splitPrefixFinal word).2 ∈ (splitPrefixFinal word).1) :
    Derives basis word
      ((word ++ Word.singleton (splitPrefixFinal word).2) ++
        Word.singleton (splitPrefixFinal word).2) := by
  apply derives_of_listDerives_toList
  rw [Word.toList_append, Word.toList_append,
    Word.toList_singleton, toList_eq_splitPrefixFinal]
  simpa [List.append_assoc] using
    listDerivesFinalSelfPair
      (splitPrefixFinal word).1 (splitPrefixFinal word).2 seen

/-- The sixth/tenth displayed laws move a selected square across a repeated
final, regardless of the nonempty intervening gap. -/
theorem listDerivesMoveSelectedPairAcrossFinal
    (stem : List Nat) (final selected : Nat) (seen : final ∈ stem) :
    ListDerives ((stem ++ [selected, selected]) ++ [final])
      ((stem ++ [final]) ++ [selected, selected]) := by
  obtain ⟨before, gap, shape⟩ := List.mem_iff_append.mp seen
  cases gap with
  | nil =>
      have moved :=
        SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
          (derivesSquareTransport
            (Word.singleton final) (Word.singleton selected)).symm
      simpa [shape, Word.toList_append, Word.toList_singleton,
        List.append_assoc] using
        SemigroupBasis.CoRoots.S5_107.ListDerives.prepend before moved
  | cons gapFirst gapRest =>
      let finalWord := Word.singleton final
      let gapWord :=
        SemigroupBasis.CoRoots.S5_107.listWordOfCons gapFirst gapRest
      let selectedWord := Word.singleton selected
      have gathered :
          Derives basis
            ((((finalWord ++ finalWord) ++ gapWord) ++ selectedWord) ++
              selectedWord)
            ((((finalWord ++ gapWord) ++ finalWord) ++ selectedWord) ++
              selectedWord) := by
        simpa [Word.append_assoc] using
          derivesGuardedGather finalWord gapWord
            (selectedWord ++ selectedWord)
      have moved :=
        (derivesSeparatedSquareTransport
          finalWord gapWord selectedWord).symm.trans gathered
      have listed :=
        SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord moved
      simpa [shape, finalWord, gapWord, selectedWord,
        SemigroupBasis.CoRoots.S5_107.listWordOfCons,
        Word.toList, Word.toList_append, Word.toList_singleton,
        List.append_assoc] using
        SemigroupBasis.CoRoots.S5_107.ListDerives.prepend before listed

/-- Exact unrestricted missing obligation from the previous semantic layer. -/
theorem repeatedFinalPairInsertion : RepeatedFinalPairInsertion := by
  intro word selected finalRepeated selectedRepeated
  let final := (splitPrefixFinal word).2
  by_cases same : selected = final
  · subst selected
    exact derivesDuplicateRepeatedFinalPair word finalRepeated
  · cases stemShape : (splitPrefixFinal word).1 with
    | nil =>
        simp [stemShape] at finalRepeated
    | cons first rest =>
        let stem :=
          SemigroupBasis.CoRoots.S5_107.listWordOfCons first rest
        let selectedWord := Word.singleton selected
        let finalWord := Word.singleton final
        have finalSeen : final ∈ first :: rest := by
          simpa [final, stemShape] using finalRepeated
        have selectedCount : 2 ≤ stem.toList.count selected := by
          have wholeShape := toList_eq_splitPrefixFinal word
          rw [stemShape] at wholeShape
          have countShape := congrArg (List.count selected) wholeShape
          simp only [List.count_append] at countShape
          have finalZero : [final].count selected = 0 := by
            apply List.count_eq_zero.mpr
            intro member
            exact same (by simpa using member)
          have stemList : stem.toList = first :: rest := rfl
          rw [← stemList] at countShape
          change word.toList.count selected =
            stem.toList.count selected + [final].count selected at countShape
          rw [finalZero] at countShape
          omega
        have stemShapeWord : stem ++ finalWord = word := by
          apply Word.toList_injective
          rw [Word.toList_append, Word.toList_singleton]
          change (first :: rest) ++ [final] = word.toList
          rw [toList_eq_splitPrefixFinal word, stemShape]
        have lower := lowerDerivesAppendSeenPair stem selected selectedCount
        have lowerValid :
            (⟨stem, (stem ++ selectedWord) ++ selectedWord⟩ :
              Identity Nat).SatisfiedBy
                SemigroupBasis.CoRoots.S5_636.table.semigroup :=
          lower.sound SemigroupBasis.CoRoots.S5_636.models
        have expanded := derivesSameSuffixOfLowerValid
          stem ((stem ++ selectedWord) ++ selectedWord) finalWord
          lowerValid
        have moved :
            Derives basis
              (((stem ++ selectedWord) ++ selectedWord) ++ finalWord)
              (((stem ++ finalWord) ++ selectedWord) ++ selectedWord) := by
          apply derives_of_listDerives_toList
          simpa [stem, finalWord, selectedWord,
            SemigroupBasis.CoRoots.S5_107.listWordOfCons,
            Word.toList, Word.toList_append, Word.toList_singleton,
            List.append_assoc] using
            listDerivesMoveSelectedPairAcrossFinal
              (first :: rest) final selected finalSeen
        simpa [stemShapeWord, selectedWord] using expanded.trans moved

/-- The whole repeated-final stratum is now unconditional and unrestricted. -/
theorem derivesRepeatedFinal
    (identity : Identity Nat)
    (descriptor : JointDescriptor identity)
    (leftRepeated :
      (splitPrefixFinal identity.lhs).2 ∈
        (splitPrefixFinal identity.lhs).1) :
    Derives basis identity.lhs identity.rhs :=
  derivesRepeatedFinalOfInsertion
    repeatedFinalPairInsertion identity descriptor leftRepeated

end SemigroupBasis.CoRoots.Order6Day8.S3_6.Rank014RepeatedInsertion
