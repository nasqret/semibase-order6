import SemigroupBasis.CoRoots.Order6FactorPairS4_69S4_71Prelude
import SemigroupBasis.CoRoots.S5_788EndpointCap
import SemigroupBasis.CoRoots.S5_1089Normalization

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6FactorPairS4_69S4_71

open SemigroupBasis
open SemigroupBasis.Examples

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  Word.mk head tail

def xx : Word Nat := w 0 [0]
def xxx : Word Nat := w 0 [0, 0]
def xyx : Word Nat := w 0 [1, 0]
def xxyx : Word Nat := w 0 [0, 1, 0]
def xyxx : Word Nat := w 0 [1, 0, 0]
def xyzx : Word Nat := w 0 [1, 2, 0]
def xyxzx : Word Nat := w 0 [1, 0, 2, 0]

private def instantiateThreeWords
    (u v z : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => z
  | n + 3 => Word.singleton (n + 3)

/-- The displayed power law `xx = xxx` is the first member of the exact
14-law basis. -/
theorem basisPowerLaw :
    Derives basis xx xxx :=
  Derives.fromBasis (e := Identity.mk xx xxx) (by decide)

/-- The displayed left-endpoint law `xxyx = xyx` is the second member of
the exact 14-law basis. -/
theorem basisLeftEndpointDuplicationLaw :
    Derives basis xxyx xyx :=
  Derives.fromBasis (e := Identity.mk xxyx xyx) (by decide)

/-- The displayed right-endpoint law `xyx = xyxx` is the eighth member of
the exact 14-law basis. -/
theorem basisRightEndpointDuplicationLaw :
    Derives basis xyx xyxx :=
  Derives.fromBasis (e := Identity.mk xyx xyxx) (by decide)

/-- Direct access to the ninth displayed basis law
`xyxzx = xyzx`. This is the nonempty-gap third-occurrence deletion law. -/
theorem basisThirdOccurrenceDeletionLaw :
    Derives basis xyxzx xyzx :=
  Derives.fromBasis (e := Identity.mk xyxzx xyzx) (by decide)

/-- Substitute an arbitrary nonempty word for `x` in `xx = xxx`. -/
theorem derivesPowerExpansion (u : Word Nat) :
    Derives basis (u ++ u) ((u ++ u) ++ u) := by
  have substituted :=
    Derives.subst basisPowerLaw
      (instantiateThreeWords u u u)
  simpa [xx, xxx, w, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- Duplicate the left endpoint in an arbitrary envelope:
`u v u = u u v u`. -/
theorem derivesLeftEndpointExpansion (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) (((u ++ u) ++ v) ++ u) := by
  have substituted :=
    Derives.subst basisLeftEndpointDuplicationLaw
      (instantiateThreeWords u v v)
  exact Derives.symm <| by
    simpa [xyx, xxyx, w, instantiateThreeWords, Word.bind,
      Word.append, Word.singleton, Word.append_assoc] using substituted

/-- Duplicate the right endpoint in an arbitrary envelope:
`u v u = u v u u`. -/
theorem derivesRightEndpointExpansion (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) (((u ++ v) ++ u) ++ u) := by
  have substituted :=
    Derives.subst basisRightEndpointDuplicationLaw
      (instantiateThreeWords u v v)
  simpa [xyx, xyxx, w, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- Delete the middle copy in three separated occurrences:
`u v u z u = u v z u`. Unlike normalizers that synthesize this rule from
several laws, this theorem is a direct substitution instance of
`xyxzx = xyzx`. -/
theorem derivesThirdOccurrenceDeletion
    (u v z : Word Nat) :
    Derives basis
      ((((u ++ v) ++ u) ++ z) ++ u)
      (((u ++ v) ++ z) ++ u) := by
  have substituted :=
    Derives.subst basisThirdOccurrenceDeletionLaw
      (instantiateThreeWords u v z)
  simpa [xyxzx, xyzx, w, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-! ## List-level endpoint-cap reduction -/

/-- List-level derivability for the exact 14-law basis. -/
abbrev ListDerives : List Nat → List Nat → Prop :=
  S5_107.ListDerives basis

private abbrev listWordOfCons :=
  S5_107.listWordOfCons

/-- Delete the middle of three displayed occurrences. The four branches
make the empty/nonempty status of the two intervening gaps explicit. -/
theorem listDerivesDeleteMiddleCore
    (letter : Nat) (left right : List Nat) :
    ListDerives
      ([letter] ++ left ++ [letter] ++ right ++ [letter])
      ([letter] ++ left ++ right ++ [letter]) := by
  cases left with
  | nil =>
      cases right with
      | nil =>
          exact S5_107.ListDerives.words <| by
            simpa [listWordOfCons, Word.singleton, Word.append,
              Word.append_assoc, List.append_assoc] using
                (derivesPowerExpansion (Word.singleton letter)).symm
      | cons rightHead rightTail =>
          exact S5_107.ListDerives.words <| by
            simpa [listWordOfCons, Word.singleton, Word.append,
              Word.append_assoc, List.append_assoc] using
                (derivesLeftEndpointExpansion
                  (Word.singleton letter)
                  (listWordOfCons rightHead rightTail)).symm
  | cons leftHead leftTail =>
      cases right with
      | nil =>
          exact S5_107.ListDerives.words <| by
            simpa [listWordOfCons, Word.singleton, Word.append,
              Word.append_assoc, List.append_assoc] using
                (derivesRightEndpointExpansion
                  (Word.singleton letter)
                  (listWordOfCons leftHead leftTail)).symm
      | cons rightHead rightTail =>
          exact S5_107.ListDerives.words <| by
            simpa [listWordOfCons, Word.singleton, Word.append,
              Word.append_assoc, List.append_assoc] using
                derivesThirdOccurrenceDeletion
                  (Word.singleton letter)
                  (listWordOfCons leftHead leftTail)
                  (listWordOfCons rightHead rightTail)

/-- Delete a current occurrence when the processed prefix and unprocessed
suffix each contain another occurrence. -/
theorem listDerivesDeleteCurrent
    (pre suffix : List Nat) (letter : Nat)
    (past : letter ∈ pre) (future : letter ∈ suffix) :
    ListDerives
      (pre ++ letter :: suffix)
      (pre ++ suffix) := by
  rcases List.append_of_mem past with
    ⟨before, firstGap, preShape⟩
  rcases List.append_of_mem future with
    ⟨secondGap, after, suffixShape⟩
  rw [preShape, suffixShape]
  simpa [List.append_assoc] using
    (listDerivesDeleteMiddleCore
      letter firstGap secondGap).context before after

/-- Derive the endpoint cap while preserving an arbitrary processed
prefix. The invariant says that every letter remembered by `seen` already
occurs in that prefix. -/
private theorem listDerivesEndpointCapAux
    (pre seen : List Nat)
    (seenInPre : ∀ tested ∈ seen, tested ∈ pre) :
    ∀ suffix : List Nat,
      ListDerives
        (pre ++ suffix)
        (pre ++ uniqueSeparatorEndpointCapAux seen suffix)
  | [] => by
      simpa using
        S5_107.ListDerives.refl (basis := basis) pre
  | letter :: rest => by
      by_cases middle : letter ∈ seen ∧ letter ∈ rest
      · have letterInPre : letter ∈ pre :=
          seenInPre letter middle.1
        have deleteCurrent :
            ListDerives
              (pre ++ letter :: rest)
              (pre ++ rest) :=
          listDerivesDeleteCurrent
            pre rest letter letterInPre middle.2
        have nextSeenInPre :
            ∀ tested ∈ letter :: seen, tested ∈ pre := by
          intro tested member
          rcases List.mem_cons.mp member with rfl | member
          · exact letterInPre
          · exact seenInPre tested member
        have recurse :=
          listDerivesEndpointCapAux
            pre (letter :: seen) nextSeenInPre rest
        rw [uniqueSeparatorEndpointCapAux, if_pos middle]
        exact deleteCurrent.trans recurse
      · have nextSeenInPre :
            ∀ tested ∈ letter :: seen,
              tested ∈ pre ++ [letter] := by
          intro tested member
          rcases List.mem_cons.mp member with rfl | member
          · exact List.mem_append_right pre (List.Mem.head [])
          · exact List.mem_append_left [letter]
              (seenInPre tested member)
        have recurse :=
          listDerivesEndpointCapAux
            (pre ++ [letter]) (letter :: seen)
            nextSeenInPre rest
        rw [uniqueSeparatorEndpointCapAux, if_neg middle]
        simpa [List.append_assoc] using recurse

/-- Retain exactly the first and last occurrence of every multiple letter,
and the sole occurrence of every simple letter. -/
abbrev endpointCap : List Nat → List Nat :=
  uniqueSeparatorEndpointCap

/-- Every list derives to its deterministic first/last endpoint cap. -/
theorem listDerivesEndpointCap (letters : List Nat) :
    ListDerives letters (endpointCap letters) := by
  simpa [uniqueSeparatorEndpointCap] using
    listDerivesEndpointCapAux [] [] (by simp) letters

/-- The endpoint cap has the exact capped multiplicity. -/
theorem endpointCap_count (tested : Nat) (letters : List Nat) :
    (endpointCap letters).count tested =
      Nat.min 2 (letters.count tested) :=
  uniqueSeparatorEndpointCap_count tested letters

/-- Every output letter occurs at most twice. -/
theorem endpointCap_count_le_two
    (tested : Nat) (letters : List Nat) :
    (endpointCap letters).count tested ≤ 2 :=
  uniqueSeparatorEndpointCap_count_le_two tested letters

/-- Endpoint capping preserves support exactly. -/
theorem mem_endpointCap_iff
    (tested : Nat) (letters : List Nat) :
    tested ∈ endpointCap letters ↔ tested ∈ letters :=
  uniqueSeparatorEndpointCap_mem_iff tested letters

/-- Endpoint capping preserves the sequence of first occurrences. The
underlying statement is the basis-independent endpoint-cap theorem already
used by the `S5_788` normalizer. -/
theorem endpointCap_firstOccurrenceSequence
    (letters : List Nat) :
    firstOccurrenceSequence (endpointCap letters) =
      firstOccurrenceSequence letters :=
  S5_788.firstOccurrenceSequence_endpointCap letters

private theorem lastOccurrenceSequence_endpointCapAux :
    ∀ (seen letters : List Nat),
      S5_1089.lastOccurrenceSequence
          (uniqueSeparatorEndpointCapAux seen letters) =
        S5_1089.lastOccurrenceSequence letters
  | _, [] => rfl
  | seen, letter :: rest => by
      have recurse :=
        lastOccurrenceSequence_endpointCapAux
          (letter :: seen) rest
      by_cases middle : letter ∈ seen ∧ letter ∈ rest
      · rw [uniqueSeparatorEndpointCapAux, if_pos middle]
        rw [S5_1089.lastOccurrenceSequence, if_pos middle.2]
        exact recurse
      · rw [uniqueSeparatorEndpointCapAux, if_neg middle]
        by_cases later : letter ∈ rest
        · have cappedLater :
              letter ∈
                uniqueSeparatorEndpointCapAux
                  (letter :: seen) rest :=
            (uniqueSeparatorEndpointCapAux_mem_iff
              (letter :: seen) letter rest).2 later
          rw [S5_1089.lastOccurrenceSequence, if_pos cappedLater]
          rw [S5_1089.lastOccurrenceSequence, if_pos later]
          exact recurse
        · have cappedAbsent :
              letter ∉
                uniqueSeparatorEndpointCapAux
                  (letter :: seen) rest := by
            intro member
            exact later <|
              (uniqueSeparatorEndpointCapAux_mem_iff
                (letter :: seen) letter rest).1 member
          rw [S5_1089.lastOccurrenceSequence, if_neg cappedAbsent]
          rw [S5_1089.lastOccurrenceSequence, if_neg later]
          exact congrArg (List.cons letter) recurse

/-- Endpoint capping preserves the sequence of last occurrences. -/
theorem endpointCap_lastOccurrenceSequence
    (letters : List Nat) :
    S5_1089.lastOccurrenceSequence (endpointCap letters) =
      S5_1089.lastOccurrenceSequence letters := by
  exact lastOccurrenceSequence_endpointCapAux [] letters

/-! ## Word-level reduction package -/

private theorem word_toList_ne_nil (word : Word Nat) :
    word.toList ≠ [] := by
  cases word with
  | mk head tail =>
      simp [Word.toList]

private def wordOfNonemptyList :
    (letters : List Nat) → letters ≠ [] → Word Nat
  | [], nonempty => False.elim (nonempty rfl)
  | head :: tail, _ => listWordOfCons head tail

private theorem toList_wordOfNonemptyList
    (letters : List Nat) (nonempty : letters ≠ []) :
    (wordOfNonemptyList letters nonempty).toList = letters := by
  cases letters with
  | nil =>
      exact False.elim (nonempty rfl)
  | cons head tail =>
      rfl

theorem endpointCap_ne_nil {letters : List Nat}
    (nonempty : letters ≠ []) :
    endpointCap letters ≠ [] := by
  cases letters with
  | nil =>
      exact False.elim (nonempty rfl)
  | cons head tail =>
      exact List.ne_nil_of_mem <|
        (mem_endpointCap_iff head (head :: tail)).2 (by simp)

private theorem listDerives_toWordOfNonemptyList
    {left right : List Nat}
    (derivation : ListDerives left right)
    (leftNonempty : left ≠ []) (rightNonempty : right ≠ []) :
    Derives basis
      (wordOfNonemptyList left leftNonempty)
      (wordOfNonemptyList right rightNonempty) := by
  cases derivation with
  | empty =>
      exact False.elim (leftNonempty rfl)
  | words wordDerivation =>
      simpa [wordOfNonemptyList] using wordDerivation

/-- The nonempty word represented by the deterministic endpoint cap. -/
def countReducedWord (word : Word Nat) : Word Nat :=
  wordOfNonemptyList (endpointCap word.toList)
    (endpointCap_ne_nil (word_toList_ne_nil word))

@[simp]
theorem countReducedWord_toList (word : Word Nat) :
    (countReducedWord word).toList =
      endpointCap word.toList := by
  exact toList_wordOfNonemptyList _ _

/-- Every semigroup word derives to its deterministic count-reduced word. -/
theorem derivesCountReducedWord (word : Word Nat) :
    Derives basis word (countReducedWord word) := by
  have sourceNonempty := word_toList_ne_nil word
  have targetNonempty := endpointCap_ne_nil sourceNonempty
  have listDerivation := listDerivesEndpointCap word.toList
  have wordDerivation :=
    listDerives_toWordOfNonemptyList
      listDerivation sourceNonempty targetNonempty
  have sourceEq :
      wordOfNonemptyList word.toList sourceNonempty = word := by
    apply Word.toList_injective
    exact toList_wordOfNonemptyList _ _
  have targetEq :
      wordOfNonemptyList
          (endpointCap word.toList) targetNonempty =
        countReducedWord word := by
    apply Word.toList_injective
    rw [toList_wordOfNonemptyList, countReducedWord_toList]
  rw [sourceEq, targetEq] at wordDerivation
  exact wordDerivation

/-- The complete reusable contract supplied by count reduction. -/
structure CountReductionResult
    (source target : Word Nat) : Prop where
  derives : Derives basis source target
  twoLimited :
    ∀ tested, target.toList.count tested ≤ 2
  firstOccurrenceOrder :
    firstOccurrenceSequence target.toList =
      firstOccurrenceSequence source.toList
  lastOccurrenceOrder :
    S5_1089.lastOccurrenceSequence target.toList =
      S5_1089.lastOccurrenceSequence source.toList
  support :
    ∀ tested, tested ∈ target.toList ↔ tested ∈ source.toList
  exactCappedCount :
    ∀ tested,
      target.toList.count tested =
        Nat.min 2 (source.toList.count tested)
  cappedMultiplicity :
    ∀ tested,
      Nat.min 2 (target.toList.count tested) =
        Nat.min 2 (source.toList.count tested)

/-- Every nonempty semigroup word has a derivable representative in which
each letter occurs at most twice, with the same first-occurrence order,
last-occurrence order, support, and multiplicities capped at two. -/
theorem countReductionResult (word : Word Nat) :
    CountReductionResult word (countReducedWord word) := by
  refine
    ⟨derivesCountReducedWord word, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro tested
    rw [countReducedWord_toList]
    exact endpointCap_count_le_two tested word.toList
  · rw [countReducedWord_toList]
    exact endpointCap_firstOccurrenceSequence word.toList
  · rw [countReducedWord_toList]
    exact endpointCap_lastOccurrenceSequence word.toList
  · intro tested
    rw [countReducedWord_toList]
    exact mem_endpointCap_iff tested word.toList
  · intro tested
    rw [countReducedWord_toList]
    exact endpointCap_count tested word.toList
  · intro tested
    rw [countReducedWord_toList, endpointCap_count]
    simp [Nat.min_assoc]

/-- Existential form used by downstream canonicalization stages. -/
theorem existsCountReducedWord (word : Word Nat) :
    ∃ reduced,
      CountReductionResult word reduced :=
  ⟨countReducedWord word, countReductionResult word⟩

end SemigroupBasis.CoRoots.Order6FactorPairS4_69S4_71
