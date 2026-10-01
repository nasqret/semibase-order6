import SemigroupBasis.CoRoots.S5_107ListDerives
import SemigroupBasis.CoRoots.S5_579Normalization

namespace SemigroupBasis.CoRoots.S5_579

open SemigroupBasis
open SemigroupBasis.Examples

private abbrev ListDerives :=
  SemigroupBasis.CoRoots.S5_107.ListDerives

private def tripleList (letters : List Nat) : List Nat :=
  (letters ++ letters) ++ letters

/-- Close a parity-block profile at its last block.  A final singleton is
promoted to a terminal triple; a final double is already closed.  On lists
outside `ParityInitialNormal` this is only a total syntax function. -/
def terminalParityList : List Nat → List Nat
  | [] => []
  | [letter] => [letter, letter, letter]
  | letter :: next :: rest =>
      if letter = next then
        match rest with
        | [] => [letter, letter]
        | tailHead :: tail =>
            letter :: letter :: terminalParityList (tailHead :: tail)
      else
        letter :: terminalParityList (next :: rest)
termination_by
  letters => letters.length

private theorem terminalParityList_cons_cons_of_ne
    (letter next : Nat) (tail : List Nat) (different : letter ≠ next) :
    terminalParityList (letter :: next :: tail) =
      letter :: terminalParityList (next :: tail) := by
  rw [terminalParityList.eq_def]
  change
    (if letter = next then
      match tail with
      | [] => [letter, letter]
      | tailHead :: rest =>
          letter :: letter :: terminalParityList (tailHead :: rest)
    else
      letter :: terminalParityList (next :: tail)) =
        letter :: terminalParityList (next :: tail)
  rw [if_neg different]

/-- Peel the first nonempty block from a cubed nonempty word.  The two
contextual gathers collect three copies of the block; the power-tail law then
contracts those copies while the cubed suffix remains as context. -/
theorem derivesCubePeel (block remainder : Word Nat) :
    Derives basis
      (((block ++ remainder) ++ (block ++ remainder)) ++
        (block ++ remainder))
      (block ++ ((remainder ++ remainder) ++ remainder)) := by
  have first :=
    derivesContextualParityGather block remainder
      ((remainder ++ block) ++ remainder)
  have second :=
    Derives.prepend block <|
      derivesContextualParityGather block
        (remainder ++ remainder) remainder
  have contracted :=
    derivesTriplePrefixReduction block
      ((remainder ++ remainder) ++ remainder)
  exact Derives.trans
    (by simpa [Word.append_assoc] using first) <|
      Derives.trans
        (by simpa [Word.append_assoc] using second)
        (by simpa [Word.append_assoc] using contracted)

private theorem listDerivesCubePeel
    (blockHead : Nat) (blockTail : List Nat)
    (remainderHead : Nat) (remainderTail : List Nat) :
    ListDerives basis
      (tripleList
        ((blockHead :: blockTail) ++
          (remainderHead :: remainderTail)))
      ((blockHead :: blockTail) ++
        tripleList (remainderHead :: remainderTail)) := by
  let block :=
    SemigroupBasis.CoRoots.S5_107.listWordOfCons blockHead blockTail
  let remainder :=
    SemigroupBasis.CoRoots.S5_107.listWordOfCons
      remainderHead remainderTail
  have wordDerivation := derivesCubePeel block remainder
  simpa [tripleList, block, remainder,
    SemigroupBasis.CoRoots.S5_107.listWordOfCons,
    Word.toList, Word.toList_append, List.append_assoc] using
      S5_107.ListDerives.ofWord wordDerivation

private theorem listDerivesSixToTwo (letter : Nat) :
    ListDerives basis
      (tripleList [letter, letter]) [letter, letter] := by
  let block := Word.singleton letter
  have sixToFour :=
    Derives.appendRight (derivesTerminalEvenReduction block)
      (block ++ block)
  have sixToTwo :=
    Derives.trans
      (by simpa [Word.append_assoc] using sixToFour)
      (derivesTerminalEvenReduction block)
  simpa [tripleList, block, Word.singleton, Word.toList,
    Word.toList_append, List.append_assoc] using
      S5_107.ListDerives.ofWord sixToTwo

/-- A cubed parity-block profile derives to the profile closed at its last
block.  The recursion is structural on the number of parity blocks. -/
theorem listDerivesCubeToTerminal
    {letters : List Nat} (normal : ParityInitialNormal letters) :
    ListDerives basis (tripleList letters)
      (terminalParityList letters) := by
  induction normal with
  | nil =>
      simpa [tripleList, terminalParityList] using
        (S5_107.ListDerives.refl (basis := basis) [])
  | single letter rest restNormal letterFresh induction =>
      cases rest with
      | nil =>
          simpa [tripleList, terminalParityList] using
            (S5_107.ListDerives.refl (basis := basis)
              [letter, letter, letter])
      | cons next tail =>
          have different : letter ≠ next := by
            intro equal
            subst next
            exact letterFresh (by simp)
          have peeled := listDerivesCubePeel letter [] next tail
          have completed :=
            peeled.trans (induction.prepend [letter])
          rw [terminalParityList_cons_cons_of_ne letter next tail different]
          simpa [tripleList,
            List.append_assoc] using completed
  | double letter rest restNormal letterFresh induction =>
      cases rest with
      | nil =>
          simpa [terminalParityList] using
            listDerivesSixToTwo letter
      | cons next tail =>
          have different : letter ≠ next := by
            intro equal
            subst next
            exact letterFresh (by simp)
          have peeled :=
            listDerivesCubePeel letter [letter] next tail
          have completed :=
            peeled.trans (induction.prepend [letter, letter])
          simpa [tripleList, terminalParityList, different,
            List.append_assoc] using completed

private theorem listDerives_firstOccurrenceParity
    {leftHead rightHead : Nat} {leftTail rightTail : List Nat}
    (derivation :
      ListDerives basis
        (leftHead :: leftTail) (rightHead :: rightTail)) :
    parityInitialNormalList (leftHead :: leftTail) =
      parityInitialNormalList (rightHead :: rightTail) := by
  have wordDerivation := S5_107.ListDerives.toWord derivation
  have valid :
      (Identity.mk
        (SemigroupBasis.CoRoots.S5_107.listWordOfCons
          leftHead leftTail)
        (SemigroupBasis.CoRoots.S5_107.listWordOfCons
          rightHead rightTail)).SatisfiedBy table.semigroup :=
    fun valuation => wordDerivation.sound models valuation
  have same :=
    (valid_signature
      (Identity.mk
        (SemigroupBasis.CoRoots.S5_107.listWordOfCons
          leftHead leftTail)
        (SemigroupBasis.CoRoots.S5_107.listWordOfCons
          rightHead rightTail)) valid).firstOccurrenceParity
  simpa [SameFirstOccurrenceParity, FirstOccurrenceParityProfile,
    SemigroupBasis.CoRoots.S5_107.listWordOfCons, Word.toList] using same

private theorem parityInitialNormalList_tripleList
    {letters : List Nat} (normal : ParityInitialNormal letters)
    (nonempty : letters ≠ []) :
    parityInitialNormalList (tripleList letters) = letters := by
  cases letters with
  | nil => exact False.elim (nonempty rfl)
  | cons head tail =>
      let word :=
        SemigroupBasis.CoRoots.S5_107.listWordOfCons head tail
      have parityDerivation := parityInitialDerivesPowerContraction word
      have canonicalValid :
          (Identity.mk ((word ++ word) ++ word) word).SatisfiedBy
            parityInitialFour.semigroup :=
        fun valuation =>
          parityDerivation.sound parityInitialBasis_models valuation
      have factorValid :
          (Identity.mk ((word ++ word) ++ word) word).SatisfiedBy
            parityFactorTable.semigroup := by
        change
          (Identity.mk ((word ++ word) ++ word) word).SatisfiedBy
            Generated.Catalogue.S4_95.table.semigroup
        rw [← Generated.S4_95.table_eq_canonical_catalogue]
        exact canonicalValid
      have same :=
        sameFirstOccurrenceParity_of_valid_s4_95
          (Identity.mk ((word ++ word) ++ word) word) factorValid
      have fixed :=
        firstOccurrenceParityProfile_eq_toList_of_normal word <| by
          simpa [word,
            SemigroupBasis.CoRoots.S5_107.listWordOfCons,
            Word.toList] using normal
      have profileEqual :
          FirstOccurrenceParityProfile ((word ++ word) ++ word) =
            head :: tail :=
        same.trans <| by
          simpa [word,
            SemigroupBasis.CoRoots.S5_107.listWordOfCons,
            Word.toList] using fixed
      simpa [FirstOccurrenceParityProfile, tripleList, word,
        SemigroupBasis.CoRoots.S5_107.listWordOfCons,
        Word.toList, Word.toList_append, List.append_assoc] using
          profileEqual

/-- Closing a nonempty parity-block profile does not change that profile. -/
theorem parityInitialNormalList_terminalParityList
    {letters : List Nat} (normal : ParityInitialNormal letters)
    (nonempty : letters ≠ []) :
    parityInitialNormalList (terminalParityList letters) = letters := by
  have cube := listDerivesCubeToTerminal normal
  have sourceNonempty : tripleList letters ≠ [] := by
    intro empty
    have appendedEmpty :
        (letters ++ letters) ++ letters = [] := by
      simpa [tripleList] using empty
    exact nonempty (List.append_eq_nil_iff.mp appendedEmpty).2
  have targetNonempty : terminalParityList letters ≠ [] := by
    cases sourceEq : tripleList letters with
    | nil => exact False.elim (sourceNonempty sourceEq)
    | cons sourceHead sourceTail =>
        have aligned :
            ListDerives basis (sourceHead :: sourceTail)
              (terminalParityList letters) := by
          simpa [sourceEq] using cube
        exact S5_107.ListDerives.target_ne_nil aligned
  cases sourceEq : tripleList letters with
  | nil => exact False.elim (sourceNonempty sourceEq)
  | cons sourceHead sourceTail =>
      cases targetEq : terminalParityList letters with
      | nil => exact False.elim (targetNonempty targetEq)
      | cons targetHead targetTail =>
          have aligned :
              ListDerives basis
                (sourceHead :: sourceTail)
                (targetHead :: targetTail) := by
            simpa [sourceEq, targetEq] using cube
          have profiles := listDerives_firstOccurrenceParity aligned
          have sourceProfile :=
            parityInitialNormalList_tripleList normal nonempty
          rw [← sourceEq, sourceProfile] at profiles
          exact profiles.symm
private theorem listDerivesRepeatedFinalEven
    (letter next : Nat) (tail : List Nat) :
    ListDerives basis
      ((letter :: next :: tail) ++ [letter])
      ([letter, letter] ++ tripleList (next :: tail)) := by
  let repeated := Word.singleton letter
  let middle :=
    SemigroupBasis.CoRoots.S5_107.listWordOfCons next tail
  have wordDerivation :=
    derivesRepeatedFinalEvenBridge repeated middle
  simpa [tripleList, repeated, middle,
    SemigroupBasis.CoRoots.S5_107.listWordOfCons,
    Word.singleton, Word.toList, Word.toList_append,
    List.append_assoc] using S5_107.ListDerives.ofWord wordDerivation

private theorem listDerivesRepeatedFinalOdd
    (letter next : Nat) (tail : List Nat) :
    ListDerives basis
      ((letter :: letter :: next :: tail) ++ [letter])
      ([letter] ++ tripleList (next :: tail)) := by
  let repeated := Word.singleton letter
  let middle :=
    SemigroupBasis.CoRoots.S5_107.listWordOfCons next tail
  have wordDerivation :=
    derivesRepeatedFinalOddTerminalTriple repeated middle
  simpa [tripleList, repeated, middle,
    SemigroupBasis.CoRoots.S5_107.listWordOfCons,
    Word.singleton, Word.toList, Word.toList_append,
    List.append_assoc] using S5_107.ListDerives.ofWord wordDerivation

/-- Structural repeated-final iteration.  Appending any variable already in a
normal parity profile toggles exactly that variable's parity block and closes
the last block.  The returned profile has the same support as the input.

The recursion skips leading blocks until it reaches the selected variable.
If a nonempty suffix follows that block, the repeated-final bridge cubes the
suffix and `listDerivesCubeToTerminal` closes it. -/
theorem existsRepeatedFinalCanonicalProfile
    {letters : List Nat} (normal : ParityInitialNormal letters)
    {final : Nat} (member : final ∈ letters) :
    ∃ updated,
      ParityInitialNormal updated ∧
        (∀ letter, letter ∈ updated ↔ letter ∈ letters) ∧
        ListDerives basis (letters ++ [final])
          (terminalParityList updated) := by
  induction normal generalizing final with
  | nil =>
      exact False.elim (by simpa using member)
  | single letter rest restNormal letterFresh induction =>
      by_cases selected : final = letter
      · subst final
        cases rest with
        | nil =>
            refine ⟨[letter, letter], ?_, ?_, ?_⟩
            · exact ParityInitialNormal.double letter []
                ParityInitialNormal.nil (by simp)
            · intro tested
              simp
            · simpa [terminalParityList] using
                (S5_107.ListDerives.refl (basis := basis) [letter, letter])
        | cons next tail =>
            have different : letter ≠ next := by
              intro equal
              subst next
              exact letterFresh (by simp)
            have bridge :=
              listDerivesRepeatedFinalEven letter next tail
            have suffix :=
              listDerivesCubeToTerminal restNormal
            have completed :=
              bridge.trans (suffix.prepend [letter, letter])
            refine ⟨letter :: letter :: next :: tail, ?_, ?_, ?_⟩
            · exact ParityInitialNormal.double letter (next :: tail)
                restNormal letterFresh
            · intro tested
              simp
            · simpa [terminalParityList, different,
                List.append_assoc] using completed
      · have inRest : final ∈ rest := by
          simpa [selected] using member
        obtain ⟨updated, updatedNormal, support, derivation⟩ :=
          induction inRest
        have finalInUpdated : final ∈ updated :=
          (support final).2 inRest
        cases updated with
        | nil =>
            exact False.elim (by simpa using finalInUpdated)
        | cons next tail =>
            have letterFreshUpdated : letter ∉ next :: tail := by
              intro inUpdated
              exact letterFresh ((support letter).1 inUpdated)
            have different : letter ≠ next := by
              intro equal
              subst next
              exact letterFreshUpdated (by simp)
            refine ⟨letter :: next :: tail, ?_, ?_, ?_⟩
            · exact ParityInitialNormal.single letter (next :: tail)
                updatedNormal letterFreshUpdated
            · intro tested
              simpa only [List.mem_cons] using
                or_congr Iff.rfl (support tested)
            · rw [terminalParityList_cons_cons_of_ne
                letter next tail different]
              simpa [List.append_assoc] using
                derivation.prepend [letter]
  | double letter rest restNormal letterFresh induction =>
      by_cases selected : final = letter
      · subst final
        cases rest with
        | nil =>
            refine ⟨[letter], ?_, ?_, ?_⟩
            · exact ParityInitialNormal.single letter []
                ParityInitialNormal.nil (by simp)
            · intro tested
              simp
            · simpa [terminalParityList] using
                (S5_107.ListDerives.refl (basis := basis)
                  [letter, letter, letter])
        | cons next tail =>
            have different : letter ≠ next := by
              intro equal
              subst next
              exact letterFresh (by simp)
            have bridge :=
              listDerivesRepeatedFinalOdd letter next tail
            have suffix :=
              listDerivesCubeToTerminal restNormal
            have completed :=
              bridge.trans (suffix.prepend [letter])
            refine ⟨letter :: next :: tail, ?_, ?_, ?_⟩
            · exact ParityInitialNormal.single letter (next :: tail)
                restNormal letterFresh
            · intro tested
              simp
            · rw [terminalParityList_cons_cons_of_ne
                letter next tail different]
              simpa [List.append_assoc] using completed
      · have inRest : final ∈ rest := by
          simpa [selected] using member
        obtain ⟨updated, updatedNormal, support, derivation⟩ :=
          induction inRest
        have finalInUpdated : final ∈ updated :=
          (support final).2 inRest
        cases updated with
        | nil =>
            exact False.elim (by simpa using finalInUpdated)
        | cons next tail =>
            have letterFreshUpdated : letter ∉ next :: tail := by
              intro inUpdated
              exact letterFresh ((support letter).1 inUpdated)
            have different : letter ≠ next := by
              intro equal
              subst next
              exact letterFreshUpdated (by simp)
            refine ⟨letter :: letter :: next :: tail, ?_, ?_, ?_⟩
            · exact ParityInitialNormal.double letter (next :: tail)
                updatedNormal letterFreshUpdated
            · intro tested
              simpa only [List.mem_cons] using
                or_congr Iff.rfl <|
                  or_congr Iff.rfl (support tested)
            · simpa [terminalParityList, different,
                List.append_assoc] using
                  derivation.prepend [letter, letter]

/-- The structural recursion returns the unique full parity profile after the
selected final occurrence is appended.  Consequently its terminal target is
independent of which repeated final was exposed by the source word. -/
theorem existsRepeatedFinalCanonicalProfile_eq
    {letters : List Nat} (normal : ParityInitialNormal letters)
    {final : Nat} (member : final ∈ letters) :
    ∃ updated,
      ParityInitialNormal updated ∧
        parityInitialNormalList (letters ++ [final]) = updated ∧
        ListDerives basis (letters ++ [final])
          (terminalParityList updated) := by
  obtain ⟨updated, updatedNormal, support, derivation⟩ :=
    existsRepeatedFinalCanonicalProfile normal member
  have lettersNonempty : letters ≠ [] := by
    intro empty
    subst letters
    simpa using member
  have updatedNonempty : updated ≠ [] := by
    intro empty
    subst updated
    have : final ∈ ([] : List Nat) := (support final).2 member
    simpa using this
  have targetProfile :=
    parityInitialNormalList_terminalParityList
      updatedNormal updatedNonempty
  cases letters with
  | nil => exact False.elim (lettersNonempty rfl)
  | cons sourceHead sourceTail =>
      cases updated with
      | nil => exact False.elim (updatedNonempty rfl)
      | cons targetHead targetTail =>
          have targetListNonempty :
              terminalParityList (targetHead :: targetTail) ≠ [] := by
            intro empty
            have normalizedEmpty :
                parityInitialNormalList
                    (terminalParityList (targetHead :: targetTail)) = [] := by
              rw [empty]
              rfl
            have normalizedProfile :=
              parityInitialNormalList_terminalParityList
                updatedNormal (by simp)
            rw [normalizedProfile] at normalizedEmpty
            simp at normalizedEmpty
          cases targetEq :
              terminalParityList (targetHead :: targetTail) with
          | nil => exact False.elim (targetListNonempty targetEq)
          | cons closedHead closedTail =>
              have aligned :
                  ListDerives basis
                    ((sourceHead :: sourceTail) ++ [final])
                    (closedHead :: closedTail) := by
                simpa [targetEq] using derivation
              have profiles :=
                listDerives_firstOccurrenceParity <| by
                  simpa [List.append_assoc] using aligned
              have targetProfileConcrete :
                  parityInitialNormalList (closedHead :: closedTail) =
                    targetHead :: targetTail := by
                rw [← targetEq]
                exact targetProfile
              refine ⟨targetHead :: targetTail, updatedNormal, ?_, ?_⟩
              · exact profiles.trans targetProfileConcrete
              · simpa [targetEq] using derivation

/-- The parity profile of the prefix preceding the original final letter. -/
def prefixParityProfile (word : Word Nat) : List Nat :=
  parityInitialNormalList (splitPrefixFinal word).1

/-- The original final letter already occurs in its prefix. -/
def HasRepeatedFinal (word : Word Nat) : Prop :=
  (splitPrefixFinal word).2 ∈ (splitPrefixFinal word).1

private instance instDecidableHasRepeatedFinal (word : Word Nat) :
    Decidable (HasRepeatedFinal word) := by
  unfold HasRepeatedFinal
  infer_instance

/-- The canonical list selected by the exact `S5_579` signature. -/
def canonicalList (word : Word Nat) : List Nat :=
  if HasRepeatedFinal word then
    terminalParityList (FirstOccurrenceParityProfile word)
  else
    FirstOccurrenceParityProfile word

private def wordOfList (fallback : Nat) : List Nat → Word Nat
  | [] => Word.singleton fallback
  | head :: tail => ⟨head, tail⟩

def canonicalWord (word : Word Nat) : Word Nat :=
  wordOfList word.head (canonicalList word)

private theorem terminalParityList_ne_nil
    {letters : List Nat} (nonempty : letters ≠ []) :
    terminalParityList letters ≠ [] := by
  cases letters with
  | nil => exact False.elim (nonempty rfl)
  | cons letter rest =>
      cases rest with
      | nil => simp [terminalParityList]
      | cons next tail =>
          by_cases equal : letter = next
          · subst next
            cases tail <;> simp [terminalParityList]
          · rw [terminalParityList_cons_cons_of_ne
              letter next tail equal]
            simp

theorem firstOccurrenceParityProfile_ne_nil (word : Word Nat) :
    FirstOccurrenceParityProfile word ≠ [] := by
  intro empty
  apply parityInitialNormalList_cons_ne_nil word.head word.tail
  simpa [FirstOccurrenceParityProfile, Word.toList] using empty

theorem canonicalList_ne_nil (word : Word Nat) :
    canonicalList word ≠ [] := by
  unfold canonicalList
  split
  · exact terminalParityList_ne_nil
      (firstOccurrenceParityProfile_ne_nil word)
  · exact firstOccurrenceParityProfile_ne_nil word

private theorem toList_wordOfList_of_ne_nil
    (fallback : Nat) {letters : List Nat} (nonempty : letters ≠ []) :
    (wordOfList fallback letters).toList = letters := by
  cases letters with
  | nil => exact False.elim (nonempty rfl)
  | cons head tail => rfl

@[simp]
theorem toList_canonicalWord (word : Word Nat) :
    (canonicalWord word).toList = canonicalList word := by
  exact toList_wordOfList_of_ne_nil word.head (canonicalList_ne_nil word)

theorem prefixParityProfile_normal (word : Word Nat) :
    ParityInitialNormal (prefixParityProfile word) :=
  parityInitialNormalList_normal (splitPrefixFinal word).1

/-- The prefix normalizer really returns the normal prefix followed by the
unchanged original final letter. -/
theorem toList_prefixParityNormalWord (word : Word Nat) :
    (prefixParityNormalWord word).toList =
      prefixParityProfile word ++ [(splitPrefixFinal word).2] := by
  let split := splitPrefixFinal word
  cases prefixEq : split.1 with
  | nil =>
      simp [prefixParityNormalWord, prefixParityProfile, split,
        prefixEq, parityInitialNormalList, Word.toList]
  | cons head tail =>
      cases normalEq : parityInitialNormalList (head :: tail) with
      | nil =>
          exact False.elim <|
            parityInitialNormalList_cons_ne_nil head tail normalEq
      | cons normalHead normalTail =>
          simp [prefixParityNormalWord, prefixParityProfile, split,
            prefixEq, normalEq, Word.toList, Word.toList_append]
          constructor <;> rfl

/-- Prefix normalization preserves membership exactly. -/
theorem mem_prefixParityProfile_iff (word : Word Nat) (tested : Nat) :
    tested ∈ prefixParityProfile word ↔
      tested ∈ (splitPrefixFinal word).1 := by
  let split := splitPrefixFinal word
  cases prefixEq : split.1 with
  | nil =>
      simp [prefixParityProfile, split, prefixEq,
        parityInitialNormalList]
  | cons head tail =>
      let prefixWord :=
        SemigroupBasis.CoRoots.S5_107.listWordOfCons head tail
      have support :=
        mem_firstOccurrenceParityProfile_iff prefixWord tested
      simpa [prefixParityProfile, FirstOccurrenceParityProfile,
        split, prefixEq, prefixWord,
        SemigroupBasis.CoRoots.S5_107.listWordOfCons,
        Word.toList] using support

private theorem normal_append_fresh
    {letters : List Nat} (normal : ParityInitialNormal letters) :
    ∀ (final : Nat), final ∉ letters →
      ParityInitialNormal (letters ++ [final]) := by
  induction normal with
  | nil =>
      intro final _
      simpa using
        ParityInitialNormal.single final []
          ParityInitialNormal.nil (by simp)
  | single letter rest restNormal letterFresh induction =>
      intro final finalFresh
      have finalFreshRest : final ∉ rest := by
        exact fun member => finalFresh (by simp [member])
      have letterDifferent : letter ≠ final := by
        intro equal
        subst final
        exact finalFresh (by simp)
      simpa [List.cons_append] using
        ParityInitialNormal.single letter (rest ++ [final])
          (induction final finalFreshRest) (by
            simp [letterFresh, letterDifferent])
  | double letter rest restNormal letterFresh induction =>
      intro final finalFresh
      have finalFreshRest : final ∉ rest := by
        exact fun member => finalFresh (by simp [member])
      have letterDifferent : letter ≠ final := by
        intro equal
        subst final
        exact finalFresh (by simp)
      simpa [List.cons_append] using
        ParityInitialNormal.double letter (rest ++ [final])
          (induction final finalFreshRest) (by
            simp [letterFresh, letterDifferent])

private theorem parityInitialNormalList_eq_self_of_normal
    {letters : List Nat} (normal : ParityInitialNormal letters)
    (nonempty : letters ≠ []) :
    parityInitialNormalList letters = letters := by
  cases letters with
  | nil => exact False.elim (nonempty rfl)
  | cons head tail =>
      let word :=
        SemigroupBasis.CoRoots.S5_107.listWordOfCons head tail
      have fixed :=
        firstOccurrenceParityProfile_eq_toList_of_normal word <| by
          simpa [word,
            SemigroupBasis.CoRoots.S5_107.listWordOfCons,
            Word.toList] using normal
      simpa [FirstOccurrenceParityProfile, word,
        SemigroupBasis.CoRoots.S5_107.listWordOfCons,
        Word.toList] using fixed

private theorem listDerivesPrefixParityNormal (word : Word Nat) :
    ListDerives basis word.toList
      (prefixParityProfile word ++ [(splitPrefixFinal word).2]) := by
  have derivation :=
    S5_107.ListDerives.ofWord (derivesPrefixParityNormal word)
  rw [toList_prefixParityNormalWord] at derivation
  exact derivation

private theorem fullProfile_eq_prefixProfile_append_final (word : Word Nat) :
    FirstOccurrenceParityProfile word =
      parityInitialNormalList
        (prefixParityProfile word ++ [(splitPrefixFinal word).2]) := by
  have derivation := derivesPrefixParityNormal word
  have valid :
      (Identity.mk word (prefixParityNormalWord word)).SatisfiedBy
        table.semigroup :=
    fun valuation => derivation.sound models valuation
  have same :=
    (valid_signature
      (Identity.mk word (prefixParityNormalWord word)) valid).firstOccurrenceParity
  simpa [SameFirstOccurrenceParity, FirstOccurrenceParityProfile,
    toList_prefixParityNormalWord] using same

private theorem derives_to_wordOfList
    (word : Word Nat) {target : List Nat}
    (derivation : ListDerives basis word.toList target)
    (targetNonempty : target ≠ []) :
    Derives basis word (wordOfList word.head target) := by
  cases word with
  | mk sourceHead sourceTail =>
      cases target with
      | nil => exact False.elim (targetNonempty rfl)
      | cons targetHead targetTail =>
          have aligned :
              ListDerives basis
                (sourceHead :: sourceTail)
                (targetHead :: targetTail) := by
            simpa [Word.toList] using derivation
          have wordDerivation := S5_107.ListDerives.toWord aligned
          simpa [wordOfList,
            SemigroupBasis.CoRoots.S5_107.listWordOfCons] using
              wordDerivation

/-- Every word derives to the canonical word selected by its exact parity and
globally-simple-final signature. -/
theorem derivesCanonical (word : Word Nat) :
    Derives basis word (canonicalWord word) := by
  let final := (splitPrefixFinal word).2
  let stem := prefixParityProfile word
  have prefixNormal : ParityInitialNormal stem := by
    simpa [stem] using prefixParityProfile_normal word
  have prefixDerivation :
      ListDerives basis word.toList (stem ++ [final]) := by
    simpa [stem, final] using listDerivesPrefixParityNormal word
  have fullProfile :
      FirstOccurrenceParityProfile word =
        parityInitialNormalList (stem ++ [final]) := by
    simpa [stem, final] using
      fullProfile_eq_prefixProfile_append_final word
  by_cases repeated : HasRepeatedFinal word
  · have finalInPrefix : final ∈ stem := by
      have originalMember :
          (splitPrefixFinal word).2 ∈ (splitPrefixFinal word).1 :=
        repeated
      exact (mem_prefixParityProfile_iff word final).2 <| by
        simpa [final] using originalMember
    obtain ⟨updated, updatedNormal, updatedProfile, closed⟩ :=
      existsRepeatedFinalCanonicalProfile_eq prefixNormal finalInPrefix
    have updatedEq : updated = FirstOccurrenceParityProfile word :=
      (fullProfile.trans updatedProfile).symm
    have closedCanonical :
        ListDerives basis (stem ++ [final]) (canonicalList word) := by
      simpa [canonicalList, repeated, updatedEq] using closed
    have complete := prefixDerivation.trans closedCanonical
    exact derives_to_wordOfList word complete (canonicalList_ne_nil word)
  · have finalFreshPrefix : final ∉ stem := by
      intro member
      apply repeated
      exact (mem_prefixParityProfile_iff word final).1 <| by
        simpa [stem, final] using member
    have appendedNormal :
        ParityInitialNormal (stem ++ [final]) :=
      normal_append_fresh prefixNormal final finalFreshPrefix
    have appendedFixed :
        parityInitialNormalList (stem ++ [final]) =
          stem ++ [final] :=
      parityInitialNormalList_eq_self_of_normal appendedNormal (by simp)
    have canonicalEq : canonicalList word = stem ++ [final] := by
      simp [canonicalList, repeated, fullProfile, appendedFixed]
    have complete :
        ListDerives basis word.toList (canonicalList word) := by
      rw [canonicalEq]
      exact prefixDerivation
    exact derives_to_wordOfList word complete (canonicalList_ne_nil word)

private theorem sameHasRepeatedFinal
    {left right : Word Nat}
    (same : SameGloballySimpleFinal left right) :
    HasRepeatedFinal left ↔ HasRepeatedFinal right := by
  constructor
  · intro leftRepeated
    apply Decidable.byContradiction
    intro rightRepeated
    let rightFinal := (splitPrefixFinal right).2
    have rightSimple : GloballySimpleFinal right rightFinal := by
      refine ⟨rfl, ?_⟩
      simpa [HasRepeatedFinal, rightFinal] using rightRepeated
    have leftSimple := (same rightFinal).2 rightSimple
    have leftFresh :
        (splitPrefixFinal left).2 ∉ (splitPrefixFinal left).1 := by
      rw [leftSimple.1]
      exact leftSimple.2
    exact leftFresh leftRepeated
  · intro rightRepeated
    apply Decidable.byContradiction
    intro leftRepeated
    let leftFinal := (splitPrefixFinal left).2
    have leftSimple : GloballySimpleFinal left leftFinal := by
      refine ⟨rfl, ?_⟩
      simpa [HasRepeatedFinal, leftFinal] using leftRepeated
    have rightSimple := (same leftFinal).1 leftSimple
    have rightFresh :
        (splitPrefixFinal right).2 ∉ (splitPrefixFinal right).1 := by
      rw [rightSimple.1]
      exact rightSimple.2
    exact rightFresh rightRepeated

theorem canonicalList_eq_of_sameSignature
    {left right : Word Nat}
    (same : SameS5_579Signature left right) :
    canonicalList left = canonicalList right := by
  have profileEqual := same.firstOccurrenceParity
  have repeatedEqual := sameHasRepeatedFinal same.globallySimpleFinal
  by_cases leftRepeated : HasRepeatedFinal left
  · have rightRepeated := repeatedEqual.1 leftRepeated
    simp only [canonicalList, if_pos leftRepeated, if_pos rightRepeated]
    exact congrArg terminalParityList profileEqual
  · have rightRepeated : ¬ HasRepeatedFinal right := by
      exact fun repeated => leftRepeated (repeatedEqual.2 repeated)
    simp only [canonicalList, if_neg leftRepeated, if_neg rightRepeated]
    exact profileEqual

theorem canonicalWord_eq_of_sameSignature
    {left right : Word Nat}
    (same : SameS5_579Signature left right) :
    canonicalWord left = canonicalWord right := by
  apply Word.toList_injective
  rw [toList_canonicalWord, toList_canonicalWord]
  exact canonicalList_eq_of_sameSignature same

end SemigroupBasis.CoRoots.S5_579
