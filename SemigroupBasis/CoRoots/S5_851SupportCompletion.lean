import SemigroupBasis.CoRoots.S5_851
import SemigroupBasis.Examples.SimpleEndpointsFour

namespace SemigroupBasis.CoRoots.S5_851

open SemigroupBasis
open SemigroupBasis.Examples

/-- Membership is unchanged by retaining only first occurrences. -/
theorem mem_firstOccurrenceSequence_iff (selected : Nat) :
    ∀ letters : List Nat,
      selected ∈ firstOccurrenceSequence letters ↔ selected ∈ letters
  | [] => by simp [firstOccurrenceSequence]
  | letter :: rest => by
      by_cases equal : selected = letter
      · subst letter
        simp [firstOccurrenceSequence]
      · simp [firstOccurrenceSequence, equal,
          mem_firstOccurrenceSequence_iff selected rest]

private theorem perm_of_nodup_mem_iff :
    ∀ {left right : List Nat},
      left.Nodup →
      right.Nodup →
      (∀ letter, letter ∈ left ↔ letter ∈ right) →
      left.Perm right
  | [], [], _, _, _ => List.Perm.refl []
  | [], letter :: rest, _, _, same => by
      exact False.elim <| by
        have member := (same letter).2 (List.Mem.head rest)
        exact List.not_mem_nil member
  | letter :: rest, [], _, _, same => by
      exact False.elim <| by
        have member := (same letter).1 (List.Mem.head rest)
        exact List.not_mem_nil member
  | letter :: rest, target :: targets,
      sourceNodup, targetNodup, same => by
      have letterInTarget : letter ∈ target :: targets :=
        (same letter).1 (List.Mem.head rest)
      have expose :
          (target :: targets).Perm
            (letter :: (target :: targets).erase letter) :=
        List.perm_cons_erase letterInTarget
      have restNodup : rest.Nodup :=
        (List.nodup_cons.mp sourceNodup).2
      have erasedNodup : ((target :: targets).erase letter).Nodup :=
        targetNodup.erase _
      have exposedNodup :
          (letter :: (target :: targets).erase letter).Nodup :=
        expose.nodup_iff.mp targetNodup
      have letterNotInErase :
          letter ∉ (target :: targets).erase letter :=
        (List.nodup_cons.mp exposedNodup).1
      have restMembership :
          ∀ current,
            current ∈ rest ↔
              current ∈ (target :: targets).erase letter := by
        intro current
        have letterNotInRest : letter ∉ rest :=
          (List.nodup_cons.mp sourceNodup).1
        by_cases currentLetter : current = letter
        · subst current
          exact iff_of_false letterNotInRest letterNotInErase
        · constructor
          · intro currentInRest
            have targetMember :=
              (expose.mem_iff).mp <|
                (same current).1 (List.Mem.tail letter currentInRest)
            simp only [List.mem_cons] at targetMember
            rcases targetMember with targetHead | targetTail
            · exact False.elim (currentLetter targetHead)
            · exact targetTail
          · intro currentInErase
            have exposedMember :
                current ∈
                  letter :: (target :: targets).erase letter :=
              List.Mem.tail letter currentInErase
            have sourceMember :=
              (same current).2 ((expose.mem_iff).mpr exposedMember)
            simp only [List.mem_cons] at sourceMember
            rcases sourceMember with sourceHead | sourceTail
            · exact False.elim (currentLetter sourceHead)
            · exact sourceTail
      exact
        (List.Perm.cons letter <|
          perm_of_nodup_mem_iff
            restNodup erasedNodup restMembership).trans expose.symm

/-- Equal supports induce a permutation of the two first-occurrence
sequences. -/
theorem firstOccurrenceSequence_perm_of_support
    {left right : Word Nat}
    (sameSupport :
      ∀ letter, letter ∈ left.toList ↔ letter ∈ right.toList) :
    (firstOccurrenceSequence left.toList).Perm
      (firstOccurrenceSequence right.toList) := by
  apply perm_of_nodup_mem_iff
  · exact firstOccurrenceSequence_nodup left.toList
  · exact firstOccurrenceSequence_nodup right.toList
  · intro letter
    rw [mem_firstOccurrenceSequence_iff,
      mem_firstOccurrenceSequence_iff]
    exact sameSupport letter

/-- The first-occurrence sequence of a word starts with its head. -/
theorem firstOccurrenceSequence_eq_head_cons_tail (word : Word Nat) :
    firstOccurrenceSequence word.toList =
      word.head :: (firstOccurrenceSequence word.toList).tail := by
  cases word
  rfl

def firstOccurrenceTail (word : Word Nat) : List Nat :=
  (firstOccurrenceSequence word.toList).tail

private theorem erase_head_firstOccurrenceSequence (word : Word Nat) :
    (firstOccurrenceSequence word.toList).erase word.head =
      firstOccurrenceTail word := by
  rw [firstOccurrenceSequence_eq_head_cons_tail]
  simp [firstOccurrenceTail]

/-- Equal head and support give a permutation of the noninitial parts of
the first-occurrence sequences. -/
theorem firstOccurrenceTail_perm
    {left right : Word Nat}
    (same : SameHeadSupportFinalSignature left right) :
    (firstOccurrenceTail left).Perm
      (firstOccurrenceTail right) := by
  have sequencePermutation :=
    firstOccurrenceSequence_perm_of_support same.support
  have erased := sequencePermutation.erase left.head
  have rightErase :
      (firstOccurrenceSequence right.toList).erase left.head =
        firstOccurrenceTail right := by
    rw [same.head]
    exact erase_head_firstOccurrenceSequence right
  rw [erase_head_firstOccurrenceSequence left, rightErase] at erased
  exact erased

/-- Permute an arbitrary interior while retaining the initial and final
letters. -/
theorem derivesInteriorPermutation
    (initial final : Nat) {left right : List Nat}
    (permutation : left.Perm right) :
    Derives basis
      (wordOfEndpoints initial left final)
      (wordOfEndpoints initial right final) := by
  induction permutation generalizing initial with
  | nil =>
      exact Derives.refl _
  | cons letter _ induction =>
      simpa [wordOfEndpoints_cons] using
        Derives.prepend (Word.singleton initial) (induction letter)
  | swap left right suffix =>
      simpa [wordOfEndpoints_eq, Word.append_assoc] using
        derivesInteriorSwap
          (Word.singleton initial)
          (Word.singleton right)
          (Word.singleton left)
          (wordOfPrefixFinal suffix final)
  | trans _ _ first second =>
      exact Derives.trans (first initial) (second initial)

/-- The extra initial copy retained by the `S5_855` normalizer. -/
def repeatedHeadPrefix (word : Word Nat) : List Nat :=
  if S5_855.repeatedInitial word &&
      decide (word.final ≠ word.head) then
    [word.head]
  else
    []

/-- The padded interior consists of the possible repeated head followed by
the complete noninitial first-occurrence order. -/
def supportMiddle (word : Word Nat) : List Nat :=
  repeatedHeadPrefix word ++ firstOccurrenceTail word

/-- An endpoint-retaining normal form in which the final first occurrence
is also retained in the interior. -/
def supportNormalWord (word : Word Nat) : Word Nat :=
  wordOfEndpoints word.head (supportMiddle word) word.final

@[simp]
theorem toList_supportNormalWord (word : Word Nat) :
    (supportNormalWord word).toList =
      word.head :: supportMiddle word ++ [word.final] := by
  simp [supportNormalWord]

private theorem repeatedHeadPrefix_eq
    {left right : Word Nat}
    (same : SameHeadSupportFinalSignature left right) :
    repeatedHeadPrefix left = repeatedHeadPrefix right := by
  unfold repeatedHeadPrefix
  rw [same.head, same.final, same.repeatedInitial]

/-- The padded interiors attached to equal head/support/final signatures
are permutations. -/
theorem supportMiddle_perm
    {left right : Word Nat}
    (same : SameHeadSupportFinalSignature left right) :
    (supportMiddle left).Perm (supportMiddle right) := by
  unfold supportMiddle
  rw [repeatedHeadPrefix_eq same]
  exact List.Perm.append
    (List.Perm.refl _) (firstOccurrenceTail_perm same)

/-- Duplicate the retained final letter at the end of an endpoint word. -/
theorem derivesDuplicateFinal
    (initial final : Nat) (middle : List Nat) :
    Derives basis
      (wordOfEndpoints initial middle final)
      (wordOfEndpoints initial (middle ++ [final]) final) := by
  have duplicate :=
    Derives.symm <|
      derivesRightContraction
        (SemigroupBasis.CoRoots.S5_107.listWordOfCons initial middle)
        (Word.singleton final)
  change Derives basis
    (SemigroupBasis.CoRoots.S5_107.listWordOfCons initial middle ++
      Word.singleton final)
    ((SemigroupBasis.CoRoots.S5_107.listWordOfCons initial middle ++
      Word.singleton final) ++ Word.singleton final)
  exact duplicate

private theorem dropLast_append_getLastD
    (letters : List Nat) (fallback : Nat)
    (nonempty : letters ≠ []) :
    letters.dropLast ++ [letters.getLastD fallback] = letters := by
  obtain ⟨head, tail, rfl⟩ :=
    List.exists_cons_of_ne_nil nonempty
  have reconstruction :=
    List.dropLast_concat_getLast
      (l := head :: tail) (by simp)
  rw [List.getLast_eq_getLastD] at reconstruction
  simpa only [List.getLastD_cons] using reconstruction

private theorem normalList_eq_core_or_append
    (word : Word Nat)
    (tailNonempty : firstOccurrenceTail word ≠ []) :
    S5_855.normalList word =
      if (firstOccurrenceSequence word.toList).getLastD word.head =
          word.final then
        word.head :: repeatedHeadPrefix word ++
          firstOccurrenceTail word
      else
        (word.head :: repeatedHeadPrefix word ++
          firstOccurrenceTail word) ++ [word.final] := by
  unfold firstOccurrenceTail at tailNonempty
  unfold S5_855.normalList
  rw [firstOccurrenceSequence_eq_head_cons_tail word]
  cases repeated : S5_855.repeatedInitial word <;>
    by_cases finalHead : word.final = word.head <;>
    simp [S5_855.renderInitialFinal, repeatedHeadPrefix,
      firstOccurrenceTail, repeated, finalHead, tailNonempty]

/-- A word with a nontrivial support derives through the `S5_855` normal
form to its padded support normal form. -/
theorem derivesSupportNormal
    (word : Word Nat)
    (tailNonempty : firstOccurrenceTail word ≠ []) :
    Derives basis word (supportNormalWord word) := by
  have normalized :
      Derives basis word (S5_855.normalWord word) :=
    liftS5_855Derivation (S5_855.derivesNormal word)
  refine normalized.trans ?_
  have normalShape :=
    normalList_eq_core_or_append word tailNonempty
  by_cases finalLast :
      (firstOccurrenceSequence word.toList).getLastD word.head =
        word.final
  · have lastInTail :
        (firstOccurrenceTail word).getLastD word.head = word.final := by
      rw [firstOccurrenceSequence_eq_head_cons_tail word] at finalLast
      simpa only [List.getLastD_cons] using finalLast
    have reconstruct :
        (firstOccurrenceTail word).dropLast ++ [word.final] =
          firstOccurrenceTail word := by
      have reconstruction :=
        dropLast_append_getLastD
          (firstOccurrenceTail word) word.head tailNonempty
      rw [lastInTail] at reconstruction
      exact reconstruction
    have sourceShape :
        S5_855.normalWord word =
          wordOfEndpoints word.head
            (repeatedHeadPrefix word ++
              (firstOccurrenceTail word).dropLast)
            word.final := by
      apply Word.toList_injective
      rw [S5_855.toList_normalWord, toList_wordOfEndpoints]
      have finalLastOption :
          (firstOccurrenceSequence word.toList).getLast?.getD
              word.head = word.final := by
        change
          (firstOccurrenceSequence word.toList).getLastD
              word.head = word.final
        exact finalLast
      simp [finalLastOption] at normalShape
      rw [normalShape]
      change
        word.head ::
            (repeatedHeadPrefix word ++ firstOccurrenceTail word) =
          word.head ::
            ((repeatedHeadPrefix word ++
              (firstOccurrenceTail word).dropLast) ++ [word.final])
      apply congrArg (List.cons word.head)
      rw [List.append_assoc, reconstruct]
    have targetShape :
        wordOfEndpoints word.head
            ((repeatedHeadPrefix word ++
              (firstOccurrenceTail word).dropLast) ++ [word.final])
            word.final =
          supportNormalWord word := by
      apply Word.toList_injective
      simp [supportNormalWord, supportMiddle,
        List.append_assoc, reconstruct]
    rw [sourceShape]
    simpa only [targetShape] using
      derivesDuplicateFinal word.head word.final
        (repeatedHeadPrefix word ++
          (firstOccurrenceTail word).dropLast)
  · have wordShape :
        S5_855.normalWord word = supportNormalWord word := by
      apply Word.toList_injective
      rw [S5_855.toList_normalWord, toList_supportNormalWord]
      have finalLastOption :
          ¬(firstOccurrenceSequence word.toList).getLast?.getD
              word.head = word.final := by
        change
          ¬(firstOccurrenceSequence word.toList).getLastD
              word.head = word.final
        exact finalLast
      simp [finalLastOption] at normalShape
      rw [normalShape]
      simp [supportMiddle]
    rw [wordShape]
    exact Derives.refl _

/-- Equal head, support, final letter, and repeated-initial state suffice
for derivability in the exact three-law basis. -/
theorem derivesOfHeadSupportFinalSignature
    {left right : Word Nat}
    (same : SameHeadSupportFinalSignature left right) :
    Derives basis left right := by
  have tailPermutation := firstOccurrenceTail_perm same
  by_cases leftTailEmpty : firstOccurrenceTail left = []
  · have rightTailEmpty : firstOccurrenceTail right = [] := by
      apply List.eq_nil_of_length_eq_zero
      simpa [leftTailEmpty] using tailPermutation.length_eq.symm
    have sequenceEquality :
        firstOccurrenceSequence left.toList =
          firstOccurrenceSequence right.toList := by
      unfold firstOccurrenceTail at leftTailEmpty rightTailEmpty
      rw [firstOccurrenceSequence_eq_head_cons_tail left,
        firstOccurrenceSequence_eq_head_cons_tail right,
        same.head, leftTailEmpty, rightTailEmpty]
    apply derivesOfInitialFinalSignature
    exact ⟨sequenceEquality, same.final, same.repeatedInitial⟩
  · have rightTailNonempty : firstOccurrenceTail right ≠ [] := by
      intro rightTailEmpty
      have leftLengthZero : (firstOccurrenceTail left).length = 0 := by
        simpa [rightTailEmpty] using tailPermutation.length_eq
      exact leftTailEmpty
        (List.eq_nil_of_length_eq_zero leftLengthZero)
    have leftNormal := derivesSupportNormal left leftTailEmpty
    have rightNormal := derivesSupportNormal right rightTailNonempty
    have bridge :
        Derives basis
          (supportNormalWord left) (supportNormalWord right) := by
      simpa [supportNormalWord, same.head, same.final] using
        derivesInteriorPermutation left.head left.final
          (supportMiddle_perm same)
    exact leftNormal.trans <| bridge.trans rightNormal.symm

/-- The requested derivational-completeness witness. -/
theorem headSupportFinalDerivationalCompleteness :
    HeadSupportFinalDerivationalCompleteness := by
  intro left right same
  exact derivesOfHeadSupportFinalSignature same

end SemigroupBasis.CoRoots.S5_851
