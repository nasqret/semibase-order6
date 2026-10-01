import SemigroupBasis.CoRoots.S5_107ListDerives
import SemigroupBasis.CoRoots.S5_831Invariant
import SemigroupBasis.Nonfinite.GraphParity

namespace SemigroupBasis.CoRoots.S5_831

open SemigroupBasis

private theorem word_toList_eq_prefix_final
    (word : Word Nat) :
    ∃ initial, word.toList = initial ++ [word.final] := by
  cases word with
  | mk head tail =>
      refine ⟨(head :: tail).dropLast, ?_⟩
      have reconstruction :=
        (List.dropLast_concat_getLast
          (l := head :: tail) (by simp)).symm
      rw [List.getLast_eq_getLastD] at reconstruction
      simpa only [Word.toList, Word.final,
        List.getLastD_cons] using reconstruction

/-- Every nonempty word square contracts to one copy followed by its final
letter: `qq -> q last(q)`. -/
theorem derivesSquareToFinal (word : Word Nat) :
    Derives basis (word ++ word)
      (word ++ Word.singleton word.final) := by
  obtain ⟨initial, wordShape⟩ :=
    word_toList_eq_prefix_final word
  cases initial with
  | nil =>
      have wordEq :
          word = Word.singleton word.final := by
        apply Word.toList_injective
        simpa using wordShape
      rw [wordEq]
      exact Derives.refl _
  | cons head tail =>
      let front :=
        SemigroupBasis.CoRoots.S5_107.listWordOfCons head tail
      let last := word.final
      let final := Word.singleton last
      have wordEq :
          word = front ++ final := by
        apply Word.toList_injective
        simpa [front, final, last,
          SemigroupBasis.CoRoots.S5_107.listWordOfCons] using
            wordShape
      rw [wordEq]
      have copied :=
        Derives.appendRight
          (derivesCopy front final) final
      have contracted :=
        Derives.prepend front
          (derivesPowerContraction final)
      have contractedAligned :
          Derives basis
            (((front ++ final) ++ final) ++ final)
            ((front ++ final) ++ final) := by
        simpa [Word.append_assoc] using contracted
      simpa [final, last, Word.append_assoc] using
        copied.trans contractedAligned

private theorem getLastD_append_cons
    (before : List Nat) (head fallback : Nat)
    (tail : List Nat) :
    (before ++ head :: tail).getLastD fallback =
      tail.getLastD head := by
  induction before generalizing fallback with
  | nil =>
      simp only [List.nil_append, List.getLastD_cons]
  | cons letter rest ih =>
      simp only [List.cons_append, List.getLastD_cons]
      exact ih letter

/-- Replace a selected old final letter by the final letter of the preceding
nonempty prefix. This is the list-level form needed when the material before
the selected occurrence may be empty. -/
private theorem listDerivesOldOccurrence
    (before : List Nat) (letter : Nat) :
    ∀ after,
      SemigroupBasis.CoRoots.S5_107.ListDerives basis
        (before ++ letter :: after ++ [letter])
        (before ++ letter :: after ++ [after.getLastD letter])
  | [] => by
      simpa using
        (SemigroupBasis.CoRoots.S5_107.ListDerives.refl
          (basis := basis) (before ++ [letter, letter]))
  | next :: rest => by
      let suffix :=
        SemigroupBasis.CoRoots.S5_107.listWordOfCons next rest
      have copied :=
        SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
          (derivesCopy (Word.singleton letter) suffix)
      have collapsed :=
        (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
          (derivesSquareToFinal suffix)).prepend [letter]
      have core := copied.trans <| by
        simpa [Word.toList_append, List.append_assoc] using
          collapsed
      have lastEq :
          (next :: rest).getLastD letter =
            rest.getLastD next := by
        simp only [List.getLastD_cons]
      rw [lastEq]
      simpa [suffix,
        SemigroupBasis.CoRoots.S5_107.listWordOfCons,
        Word.toList, Word.toList_append, Word.final,
        List.append_assoc] using
          core.prepend before

/-- If `letter` already occurs in a nonempty list, appending it may be
replaced by appending the current final letter. -/
theorem listDerivesAppendOld
    (letters : List Nat) (letter : Nat)
    (member : letter ∈ letters) :
    SemigroupBasis.CoRoots.S5_107.ListDerives basis
      (letters ++ [letter])
      (letters ++ [letters.getLastD letter]) := by
  rcases List.append_of_mem member with
    ⟨before, after, rfl⟩
  have core :=
    listDerivesOldOccurrence before letter after
  have finalEq :
      (before ++ letter :: after).getLastD letter =
        after.getLastD letter :=
    getLastD_append_cons before letter letter after
  rw [finalEq]
  simpa [List.append_assoc] using core

/-- Appending the current phase label either changes a singleton phase to a
double phase or creates a final triple, which contracts back to a double. -/
private theorem listDerivesMarkLastDoubled
    (fallback : Nat) :
    ∀ phases,
      phases ≠ [] →
      SemigroupBasis.CoRoots.S5_107.ListDerives basis
        (renderPhases phases ++
          [(renderPhases phases).getLastD fallback])
        (renderPhases (markLastDoubled phases))
  | [], nonempty => False.elim (nonempty rfl)
  | phase :: rest, _ => by
      cases rest with
      | nil =>
          rcases phase with ⟨label, doubled⟩
          cases doubled with
          | false =>
              simpa [renderPhases, renderPhase,
                markLastDoubled] using
                  (SemigroupBasis.CoRoots.S5_107.ListDerives.refl
                    (basis := basis)
                    [label, label])
          | true =>
              simpa [renderPhases, renderPhase,
                markLastDoubled, Word.toList_append] using
                  (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
                    (derivesPowerContraction
                      (Word.singleton label)))
      | cons next tail =>
          have induction :=
            listDerivesMarkLastDoubled
              ((renderPhase phase).getLastD fallback)
              (next :: tail) (by simp)
          cases phase.doubled <;> cases next.doubled <;>
            simpa [renderPhases, renderPhase,
              markLastDoubled, List.append_assoc] using
                induction.prepend (renderPhase phase)

private theorem listDerivesPhaseStep
    (phases : List Phase) (letter : Nat)
    (nonempty : phases ≠ []) :
    SemigroupBasis.CoRoots.S5_107.ListDerives basis
      (renderPhases phases ++ [letter])
      (renderPhases (phaseStep phases letter)) := by
  unfold phaseStep
  split
  next old =>
    have renderedMember :
        letter ∈ renderPhases phases :=
      (mem_renderPhases_iff letter phases).2 old
    have replace :=
      listDerivesAppendOld
        (renderPhases phases) letter renderedMember
    have mark :=
      listDerivesMarkLastDoubled letter phases nonempty
    exact replace.trans mark
  next fresh =>
    simpa [renderPhases, renderPhase] using
      (SemigroupBasis.CoRoots.S5_107.ListDerives.refl
        (basis := basis) (renderPhases phases ++ [letter]))

/-- Scanner normalization from any nonempty phase state. -/
theorem listDerivesScanPhases
    (phases : List Phase) (nonempty : phases ≠ []) :
    ∀ letters,
      SemigroupBasis.CoRoots.S5_107.ListDerives basis
        (renderPhases phases ++ letters)
        (renderPhases (scanPhases phases letters))
  | [] => by
      simpa [scanPhases] using
        (SemigroupBasis.CoRoots.S5_107.ListDerives.refl
          (basis := basis) (renderPhases phases))
  | letter :: rest => by
      have first :=
        (listDerivesPhaseStep phases letter nonempty).append rest
      have second :=
        listDerivesScanPhases
          (phaseStep phases letter)
          (phaseStep_ne_nil nonempty letter) rest
      simpa [scanPhases, List.append_assoc] using
        first.trans second

/-- Every nonempty list underlying a word derives to the phase rendering. -/
theorem listDerivesCanonical (word : Word Nat) :
    SemigroupBasis.CoRoots.S5_107.ListDerives basis
      word.toList (canonicalList word) := by
  cases word with
  | mk head tail =>
      have normalized :=
        listDerivesScanPhases
          [⟨head, false⟩] (by simp) tail
      simpa [Word.toList, canonicalList, phaseProfile,
        phaseProfileList, renderPhases, renderPhase] using
          normalized

/-- Unrestricted word-level normalization to the positional phase canonical
form. -/
theorem derivesCanonical (word : Word Nat) :
    Derives basis word (canonicalWord word) := by
  cases word with
  | mk head tail =>
      have listDerivation :
          SemigroupBasis.CoRoots.S5_107.ListDerives basis
            (head :: tail)
            (canonicalList (Word.mk head tail)) := by
        simpa [Word.toList] using
          listDerivesCanonical (Word.mk head tail)
      obtain
        ⟨targetHead, targetTail, targetListEq, wordDerivation⟩ :=
          SemigroupBasis.CoRoots.S5_107.ListDerives.from_cons
            listDerivation
      have targetWordEq :
          SemigroupBasis.CoRoots.S5_107.listWordOfCons
              targetHead targetTail =
            canonicalWord (Word.mk head tail) := by
        apply Word.toList_injective
        rw [toList_canonicalWord]
        simpa [SemigroupBasis.CoRoots.S5_107.listWordOfCons] using
          targetListEq.symm
      rw [targetWordEq] at wordDerivation
      simpa [SemigroupBasis.CoRoots.S5_107.listWordOfCons] using
        wordDerivation

end SemigroupBasis.CoRoots.S5_831
