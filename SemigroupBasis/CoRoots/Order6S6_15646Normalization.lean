import SemigroupBasis.CoRoots.Order6FennemoreR3InvariantPrelude
import SemigroupBasis.CoRoots.S5_1089Normalization
import SemigroupBasis.CoRoots.S5_1099Normalization

namespace SemigroupBasis.CoRoots.Order6FennemoreR3Band

open SemigroupBasis

private abbrev ListDerives : List Nat → List Nat → Prop :=
  SemigroupBasis.CoRoots.S5_107.ListDerives basis

private abbrev wordOfCons :=
  SemigroupBasis.CoRoots.S5_107.listWordOfCons

private theorem r3ListDerivesSquareExpansion (letters : List Nat) :
    ListDerives letters (letters ++ letters) := by
  cases letters with
  | nil =>
      exact SemigroupBasis.CoRoots.S5_107.ListDerives.empty
  | cons head tail =>
      simpa [wordOfCons, Word.toList] using
        SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
          (r3DerivesSquareExpansion (wordOfCons head tail))

private theorem r3ListDerivesSquareContraction (letters : List Nat) :
    ListDerives (letters ++ letters) letters :=
  (r3ListDerivesSquareExpansion letters).symm

private theorem r3ListDerivesEraseSupported
    (anchor : List Nat) (letter : Nat) (member : letter ∈ anchor) :
    ∃ extension,
      ListDerives (anchor ++ [letter] ++ extension) anchor := by
  obtain ⟨before, after, split⟩ := List.mem_iff_append.mp member
  refine ⟨after, ?_⟩
  have contraction :=
    (r3ListDerivesSquareContraction (letter :: after)).prepend before
  simpa [split, List.append_assoc] using contraction

private theorem r3ListDerivesCompletion
    (anchor : List Nat) :
    ∀ suffix : List Nat,
      (∀ letter, letter ∈ suffix → letter ∈ anchor) →
      ∃ extension,
        ListDerives (anchor ++ suffix ++ extension) anchor
  | [], _ => by
      refine ⟨[], ?_⟩
      simpa using
        (SemigroupBasis.CoRoots.S5_107.ListDerives.refl
          (basis := basis) anchor)
  | letter :: rest, subset => by
      have letterMember : letter ∈ anchor :=
        subset letter (List.Mem.head rest)
      have restSubset :
          ∀ tested, tested ∈ rest → tested ∈ anchor ++ [letter] := by
        intro tested testedMember
        exact List.mem_append_left [letter]
          (subset tested (List.Mem.tail letter testedMember))
      obtain ⟨restExtension, restDerivation⟩ :=
        r3ListDerivesCompletion (anchor ++ [letter]) rest restSubset
      obtain ⟨letterExtension, letterDerivation⟩ :=
        r3ListDerivesEraseSupported anchor letter letterMember
      refine ⟨restExtension ++ letterExtension, ?_⟩
      have first := restDerivation.append letterExtension
      have firstStep :
          ListDerives
            (anchor ++ (letter :: rest) ++
              (restExtension ++ letterExtension))
            (anchor ++ [letter] ++ letterExtension) := by
        simpa [List.append_assoc] using first
      exact firstStep.trans letterDerivation

/-- Band swallowing, derived only from the displayed idempotence law. -/
theorem r3ListDerivesSwallow
    (anchor suffix : List Nat)
    (subset : ∀ letter, letter ∈ suffix → letter ∈ anchor) :
    ListDerives (anchor ++ suffix ++ anchor) anchor := by
  obtain ⟨extension, completion⟩ :=
    r3ListDerivesCompletion anchor suffix subset
  let full := anchor ++ suffix
  have insertCompletion := completion.symm.prepend full
  have contractSquare :=
    (r3ListDerivesSquareContraction full).append extension
  have insertStep :
      ListDerives (anchor ++ suffix ++ anchor)
        ((full ++ full) ++ extension) := by
    simpa [full, List.append_assoc] using insertCompletion
  have completionStep : ListDerives (full ++ extension) anchor := by
    simpa [full, List.append_assoc] using completion
  exact insertStep.trans (contractSquare.trans completionStep)

/-- The standard band deletion law: equal-support outer blocks absorb a
supported middle block. -/
theorem r3ListDerivesBandDeletion
    (left middle right : List Nat)
    (middleSubset : ∀ letter, letter ∈ middle → letter ∈ left)
    (rightSubset : ∀ letter, letter ∈ right → letter ∈ left)
    (leftSubset : ∀ letter, letter ∈ left → letter ∈ right) :
    ListDerives (left ++ middle ++ right) (left ++ right) := by
  have insertLeft :=
    (r3ListDerivesSwallow right left leftSubset).symm.prepend
      (left ++ middle)
  have supported :
      ∀ letter, letter ∈ middle ++ right → letter ∈ left := by
    intro letter member
    rcases List.mem_append.mp member with member | member
    · exact middleSubset letter member
    · exact rightSubset letter member
  have eraseMiddle :=
    (r3ListDerivesSwallow left (middle ++ right) supported).append right
  have insertStep :
      ListDerives (left ++ middle ++ right)
        (left ++ middle ++ right ++ left ++ right) := by
    simpa [List.append_assoc] using insertLeft
  have eraseStep :
      ListDerives (left ++ middle ++ right ++ left ++ right)
        (left ++ right) := by
    simpa [List.append_assoc] using eraseMiddle
  exact insertStep.trans eraseStep

/-- Delete an earlier occurrence whose intervening letters already occur in
the nonempty anchor. This is the local R3 reduction. -/
theorem r3ListDerivesDeleteEarlier
    (anchorHead letter : Nat) (anchorTail middle suffix : List Nat)
    (letterMember : letter ∈ anchorHead :: anchorTail)
    (middleSubset :
      ∀ tested, tested ∈ middle → tested ∈ anchorHead :: anchorTail) :
    ListDerives
      ((anchorHead :: anchorTail) ++ [letter] ++ middle ++ [letter] ++ suffix)
      ((anchorHead :: anchorTail) ++ middle ++ [letter] ++ suffix) := by
  let anchor := anchorHead :: anchorTail
  cases middle with
  | nil =>
      have contraction :=
        SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
          ((r3DerivesSquareExpansion (Word.singleton letter)).symm)
      simpa [anchor, Word.singleton, List.append_assoc] using
        (SemigroupBasis.CoRoots.S5_107.ListDerives.context
          anchor suffix contraction)
  | cons middleHead middleTail =>
      let middle := middleHead :: middleTail
      let source := anchor ++ [letter] ++ middle ++ [letter]
      let target := anchor ++ middle ++ [letter]
      have expansion : ListDerives target (target ++ source) := by
        have wordExpansion :=
          SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
            (r3DerivesExpansion
              (wordOfCons anchorHead anchorTail)
              (wordOfCons middleHead middleTail)
              (Word.singleton letter))
        simpa [anchor, middle, source, target, wordOfCons,
          Word.append, Word.singleton, List.append_assoc] using wordExpansion
      have sourceSubset :
          ∀ tested, tested ∈ source → tested ∈ anchor := by
        intro tested testedMember
        rw [show source = ((anchor ++ [letter]) ++ middle) ++ [letter]
          by simp [source, List.append_assoc]] at testedMember
        rcases List.mem_append.mp testedMember with beforeFinal | finalMember
        · rcases List.mem_append.mp beforeFinal with
            beforeMiddle | middleMember
          · rcases List.mem_append.mp beforeMiddle with
              anchorMember | singletonMember
            · exact anchorMember
            · have testedLetter : tested = letter := by
                simpa using singletonMember
              simpa [anchor, testedLetter] using letterMember
          · exact middleSubset tested (by simpa [middle] using middleMember)
        · have testedLetter : tested = letter := by simpa using finalMember
          simpa [anchor, testedLetter] using letterMember
      have targetTailSubset :
          ∀ tested, tested ∈ middle ++ [letter] → tested ∈ anchor := by
        intro tested testedMember
        rcases List.mem_append.mp testedMember with middleMember | finalMember
        · exact middleSubset tested (by simpa [middle] using middleMember)
        · have testedLetter : tested = letter := by simpa using finalMember
          simpa [anchor, testedLetter] using letterMember
      have deleteExpansion :
          ListDerives (target ++ source) (anchor ++ source) := by
        simpa [target, List.append_assoc] using
          r3ListDerivesBandDeletion
            anchor (middle ++ [letter]) source
            targetTailSubset sourceSubset
            (fun tested testedMember => by
              simp [source, testedMember])
      have contractAnchor : ListDerives (anchor ++ source) source := by
        have contraction :=
          (r3ListDerivesSquareContraction anchor).append
            ([letter] ++ middle ++ [letter])
        simpa [source, List.append_assoc] using contraction
      have core : ListDerives source target :=
        (expansion.trans (deleteExpansion.trans contractAnchor)).symm
      simpa [anchor, middle, source, target, List.append_assoc] using
        core.append suffix

private theorem r3LastOccurrenceSequence_eq_s5
    (letters : List Nat) :
    r3LastOccurrenceSequence letters =
      SemigroupBasis.CoRoots.S5_1089.lastOccurrenceSequence letters := by
  rw [SemigroupBasis.CoRoots.S5_1089.lastOccurrenceSequence_eq_reverse_firstOccurrenceSequence]
  rfl

theorem r3MemLastOccurrenceSequence_iff
    (selected : Nat) (letters : List Nat) :
    selected ∈ r3LastOccurrenceSequence letters ↔ selected ∈ letters := by
  simp [r3LastOccurrenceSequence,
    SemigroupBasis.CoRoots.S5_1099.mem_firstOccurrenceSequence_iff]

private theorem r3ListDerivesLastOccurrenceWithPrefix
    (prefixHead : Nat) :
    ∀ (prefixTail letters : List Nat),
      (∀ tested, tested ∈ letters → tested ∈ prefixHead :: prefixTail) →
      ListDerives
        ((prefixHead :: prefixTail) ++ letters)
        ((prefixHead :: prefixTail) ++
          SemigroupBasis.CoRoots.S5_1089.lastOccurrenceSequence letters)
  | prefixTail, [], _ => by
      simpa [SemigroupBasis.CoRoots.S5_1089.lastOccurrenceSequence] using
        (SemigroupBasis.CoRoots.S5_107.ListDerives.refl
          (basis := basis) (prefixHead :: prefixTail))
  | prefixTail, letter :: rest, subset => by
      by_cases later : letter ∈ rest
      · obtain ⟨before, after, split⟩ :=
          List.mem_iff_append.mp later
        have beforeSubset :
            ∀ tested, tested ∈ before → tested ∈ prefixHead :: prefixTail := by
          intro tested testedMember
          exact subset tested (by
            simp [split, testedMember])
        have deleteCurrent :=
          r3ListDerivesDeleteEarlier
            prefixHead letter prefixTail before after
            (subset letter (List.Mem.head rest)) beforeSubset
        have restSubset :
            ∀ tested, tested ∈ rest → tested ∈ prefixHead :: prefixTail := by
          intro tested testedMember
          exact subset tested (List.Mem.tail letter testedMember)
        have normalizeRest :=
          r3ListDerivesLastOccurrenceWithPrefix
            prefixHead prefixTail rest restSubset
        have deleteCurrent' :
            ListDerives
              ((prefixHead :: prefixTail) ++ letter :: rest)
              ((prefixHead :: prefixTail) ++ rest) := by
          simpa [split, List.append_assoc] using deleteCurrent
        simpa [SemigroupBasis.CoRoots.S5_1089.lastOccurrenceSequence,
          later, List.append_assoc] using
            deleteCurrent'.trans normalizeRest
      · have restSubset :
            ∀ tested, tested ∈ rest →
              tested ∈ prefixHead :: (prefixTail ++ [letter]) := by
          intro tested testedMember
          exact List.mem_append_left [letter]
            (subset tested (List.Mem.tail letter testedMember))
        have normalizeRest :=
          r3ListDerivesLastOccurrenceWithPrefix
            prefixHead (prefixTail ++ [letter]) rest restSubset
        simpa [SemigroupBasis.CoRoots.S5_1089.lastOccurrenceSequence,
          later, List.append_assoc] using normalizeRest

private theorem r3ListDerivesAppendLastOccurrence
    (head : Nat) (tail : List Nat) :
    ListDerives (head :: tail)
      ((head :: tail) ++ r3LastOccurrenceSequence (head :: tail)) := by
  have square := r3ListDerivesSquareExpansion (head :: tail)
  have normalizeSecond :=
    r3ListDerivesLastOccurrenceWithPrefix head tail (head :: tail)
      (fun tested testedMember => testedMember)
  simpa [r3LastOccurrenceSequence_eq_s5, List.append_assoc] using
    square.trans normalizeSecond

private theorem r3WordOfList_toList
    {letters : List Nat} (nonempty : letters ≠ []) :
    (r3WordOfList letters).toList = letters := by
  cases letters with
  | nil => contradiction
  | cons head tail => rfl

/-- Once the last new letter has appeared, the remaining repetitions reduce
to the last-occurrence tail. -/
theorem r3DerivesLastOccurrenceTail
    (pref : Word Nat) (pivot : Nat) (tail : List Nat)
    (hcontent : ∀ letter, letter ∈ tail →
      letter ∈ pref.toList ∨ letter = pivot) :
    Derives basis
      (pref ++ Word.mk pivot tail)
      (r3WordOfList
        (pref.toList ++ pivot ::
          r3LastOccurrenceSequence
            (pref.toList ++ pivot :: tail))) := by
  let anchor := pref.toList ++ [pivot]
  let full := anchor ++ tail
  have tailSubset :
      ∀ letter, letter ∈ tail → letter ∈ anchor := by
    intro letter member
    rcases hcontent letter member with prefixMember | pivotEqual
    · exact List.mem_append_left [pivot] prefixMember
    · simp [anchor, pivotEqual]
  have lastSubset :
      ∀ letter, letter ∈ r3LastOccurrenceSequence full →
        letter ∈ anchor := by
    intro letter member
    have fullMember :=
      (r3MemLastOccurrenceSequence_iff letter full).mp member
    rcases List.mem_append.mp fullMember with anchorMember | tailMember
    · exact anchorMember
    · exact tailSubset letter tailMember
  have anchorSubset :
      ∀ letter, letter ∈ anchor →
        letter ∈ r3LastOccurrenceSequence full := by
    intro letter member
    exact (r3MemLastOccurrenceSequence_iff letter full).mpr
      (List.mem_append_left tail member)
  cases pref with
  | mk prefHead prefTail =>
      have appendLast :=
        r3ListDerivesAppendLastOccurrence prefHead
          (prefTail ++ pivot :: tail)
      have deleteTail :=
        r3ListDerivesBandDeletion anchor tail
          (r3LastOccurrenceSequence full)
          tailSubset lastSubset anchorSubset
      have listDerivation :
          ListDerives full
            (anchor ++ r3LastOccurrenceSequence full) := by
        have appendLast' :
            ListDerives full
              (full ++ r3LastOccurrenceSequence full) := by
          simpa [anchor, full, List.append_assoc] using appendLast
        have deleteTail' :
            ListDerives (full ++ r3LastOccurrenceSequence full)
              (anchor ++ r3LastOccurrenceSequence full) := by
          simpa [full, List.append_assoc] using deleteTail
        exact appendLast'.trans deleteTail'
      have targetNonempty :
          anchor ++ r3LastOccurrenceSequence full ≠ [] := by
        simp [anchor, Word.toList]
      cases targetEq : anchor ++ r3LastOccurrenceSequence full with
      | nil => contradiction
      | cons targetHead targetTail =>
          have wordDerivation :=
            SemigroupBasis.CoRoots.S5_107.ListDerives.toWord <| by
              simpa [full, Word.toList, List.append_assoc, targetEq] using
                listDerivation
          have sourceWordEq :
              Word.mk prefHead prefTail ++ Word.mk pivot tail =
                wordOfCons prefHead (prefTail ++ pivot :: tail) := rfl
          have targetWordEq :
              r3WordOfList
                  ((prefHead :: prefTail) ++ pivot ::
                    r3LastOccurrenceSequence
                      ((prefHead :: prefTail) ++ pivot :: tail)) =
                wordOfCons targetHead targetTail := by
            apply Word.toList_injective
            rw [r3WordOfList_toList]
            · simpa [anchor, full, wordOfCons, Word.toList,
                List.append_assoc] using targetEq
            · simpa [anchor, full, List.append_assoc] using targetNonempty
          change Derives basis
            (Word.mk prefHead prefTail ++ Word.mk pivot tail)
            (r3WordOfList
              ((prefHead :: prefTail) ++ pivot ::
                r3LastOccurrenceSequence
                  ((prefHead :: prefTail) ++ pivot :: tail)))
          rw [sourceWordEq, targetWordEq]
          have sourceTailEq :
              (prefTail ++ [pivot]) ++ tail =
                prefTail ++ pivot :: tail := by
            simp [List.append_assoc]
          rw [← sourceTailEq]
          exact wordDerivation

private theorem r3LastOccurrenceConstant
    (pivot : Nat) :
    ∀ tail : List Nat,
      (∀ letter, letter ∈ tail → letter = pivot) →
      r3LastOccurrenceSequence (pivot :: tail) = [pivot]
  | [], _ => by
      simp [r3LastOccurrenceSequence_eq_s5,
        SemigroupBasis.CoRoots.S5_1089.lastOccurrenceSequence]
  | letter :: rest, constant => by
      have letterEq := constant letter (List.Mem.head rest)
      subst letter
      have restConstant : ∀ letter, letter ∈ rest → letter = pivot := by
        intro letter member
        exact constant letter (List.Mem.tail pivot member)
      have induction := r3LastOccurrenceConstant pivot rest restConstant
      simpa [r3LastOccurrenceSequence_eq_s5,
        SemigroupBasis.CoRoots.S5_1089.lastOccurrenceSequence] using induction

private theorem r3ListDerivesConstantContraction
    (pivot : Nat) :
    ∀ tail : List Nat,
      (∀ letter, letter ∈ tail → letter = pivot) →
      ListDerives (pivot :: tail) [pivot]
  | [], _ =>
      SemigroupBasis.CoRoots.S5_107.ListDerives.refl [pivot]
  | letter :: rest, constant => by
      have letterEq := constant letter (List.Mem.head rest)
      subst letter
      have restConstant : ∀ letter, letter ∈ rest → letter = pivot := by
        intro letter member
        exact constant letter (List.Mem.tail pivot member)
      have first :=
        (r3ListDerivesSquareContraction [pivot]).append rest
      have remaining :=
        r3ListDerivesConstantContraction pivot rest restConstant
      simpa using first.trans remaining

/-- Every word derives to its recursive Fennemore `i3` invariant. -/
theorem r3ListDerivesInvariant :
    ∀ letters : List Nat, letters ≠ [] →
      ListDerives letters (r3Invariant letters)
  | letters, nonempty => by
      cases split : r3Split letters with
      | none =>
          exact False.elim
            (nonempty ((r3Split_none_iff letters).mp split))
      | some result =>
          rcases result with ⟨stem, pivot, tail⟩
          have spec := r3Split_some_spec split
          rw [r3Invariant_eq_of_split split]
          by_cases prefixEmpty : stem = []
          · subst stem
            have shape : letters = pivot :: tail := by
              simpa using spec.shape
            have constant : ∀ letter, letter ∈ tail → letter = pivot := by
              intro letter member
              rcases spec.tailContent letter member with
                impossible | impossible | equal
              · simp at impossible
              · simp at impossible
              · exact equal
            have contraction :=
              r3ListDerivesConstantContraction pivot tail constant
            have expansion := r3ListDerivesSquareExpansion [pivot]
            have invariantNil : r3Invariant [] = [] := by
              rw [r3Invariant]
              rfl
            simpa [shape, invariantNil,
              r3LastOccurrenceConstant pivot tail constant] using
                contraction.trans expansion
          · obtain ⟨prefixHead, prefixTail, prefixShape⟩ :=
              List.exists_cons_of_ne_nil prefixEmpty
            have tailDerivation :=
              r3DerivesLastOccurrenceTail
                (wordOfCons prefixHead prefixTail) pivot tail <| by
                  intro letter member
                  rcases spec.tailContent letter member with
                    impossible | prefixMember | equal
                  · simp at impossible
                  · exact Or.inl (by
                      simpa [prefixShape, wordOfCons, Word.toList] using
                        prefixMember)
                  · exact Or.inr equal
            have tailListDerivation :=
              SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord tailDerivation
            have prefixDerivation :=
              r3ListDerivesInvariant stem prefixEmpty
            have normalizePrefix :=
              prefixDerivation.append
                (pivot :: r3LastOccurrenceSequence letters)
            have tailStep :
                ListDerives letters
                  (stem ++ pivot :: r3LastOccurrenceSequence letters) := by
              simpa [spec.shape, prefixShape, wordOfCons, Word.toList,
                Word.append, r3WordOfList, List.append_assoc] using
                  tailListDerivation
            have prefixStep :
                ListDerives
                  (stem ++ pivot :: r3LastOccurrenceSequence letters)
                  (r3Invariant stem ++ pivot ::
                    r3LastOccurrenceSequence letters) := by
              simpa [List.append_assoc] using normalizePrefix
            exact tailStep.trans prefixStep
termination_by
  letters => letters.length
decreasing_by
  exact r3Split_prefix_length_lt split

theorem r3_derives_invariant (word : Word Nat) :
    Derives basis word (r3WordOfList (r3Invariant word.toList)) := by
  have nonempty : word.toList ≠ [] := by
    cases word
    simp [Word.toList]
  have listDerivation := r3ListDerivesInvariant word.toList nonempty
  cases word with
  | mk wordHead wordTail =>
      cases invariantEq : r3Invariant (wordHead :: wordTail) with
      | nil =>
          exact False.elim
            (r3Invariant_ne_nil (Word.mk wordHead wordTail) <| by
              simpa [Word.toList] using invariantEq)
      | cons normalHead normalTail =>
          have wordDerivation :=
            SemigroupBasis.CoRoots.S5_107.ListDerives.toWord <| by
              simpa [Word.toList, invariantEq] using listDerivation
          simpa [r3WordOfList, invariantEq, wordOfCons, Word.toList] using
            wordDerivation

theorem r3_derives_of_invariant_eq
    (left right : Word Nat)
    (equalInvariant :
      r3Invariant left.toList = r3Invariant right.toList) :
    Derives basis left right := by
  exact (r3_derives_invariant left).trans <| by
    rw [equalInvariant]
    exact (r3_derives_invariant right).symm

end SemigroupBasis.CoRoots.Order6FennemoreR3Band
