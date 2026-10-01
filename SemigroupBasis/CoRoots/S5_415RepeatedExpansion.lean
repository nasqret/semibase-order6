import SemigroupBasis.CoRoots.S5_415
import SemigroupBasis.CoRoots.S5_415RepeatedWords

namespace SemigroupBasis.CoRoots.S5_415

open SemigroupBasis

/-- The supported letters which occur exactly once, in their occurrence order. -/
def singletonLetters (word : Word Nat) : List Nat :=
  word.toList.filter fun letter => decide (word.toList.count letter = 1)

/-- The number of supported letters which occur exactly once. -/
def singletonMeasure (word : Word Nat) : Nat :=
  (singletonLetters word).length

/-- Two words use the same set of letters. -/
def SameLetterSupport (left right : Word Nat) : Prop :=
  ∀ letter, letter ∈ left.toList ↔ letter ∈ right.toList

/-- No supported letter occurs exactly once. -/
def NoSingletonLetters (word : Word Nat) : Prop :=
  ∀ letter, letter ∈ word.toList → word.toList.count letter ≠ 1

theorem SameLetterSupport.refl (word : Word Nat) :
    SameLetterSupport word word := by
  intro letter
  rfl

theorem SameLetterSupport.trans
    {left middle right : Word Nat}
    (first : SameLetterSupport left middle)
    (second : SameLetterSupport middle right) :
    SameLetterSupport left right := by
  intro letter
  exact (first letter).trans (second letter)

@[simp]
theorem mem_singletonLetters_iff (word : Word Nat) (letter : Nat) :
    letter ∈ singletonLetters word ↔ word.toList.count letter = 1 := by
  simp only [singletonLetters, List.mem_filter, decide_eq_true_eq]
  constructor
  · exact And.right
  · intro countOne
    exact ⟨List.count_pos_iff.mp (by omega), countOne⟩

/-- Filtering by global multiplicity one produces no duplicate letters. -/
theorem singletonLetters_nodup (word : Word Nat) :
    (singletonLetters word).Nodup := by
  rw [List.nodup_iff_count]
  intro tested
  have countBound :=
    (List.filter_sublist
      (l := word.toList)
      (p := fun letter => decide (word.toList.count letter = 1))).count_le
        tested
  by_cases singleton : word.toList.count tested = 1
  · simpa [singletonLetters, singleton] using countBound
  · have absent : tested ∉ singletonLetters word := by
      simpa using singleton
    rw [List.count_eq_zero.mpr absent]
    omega

private theorem nodup_length_le_of_subset
    {source target : List Nat}
    (nodup : source.Nodup)
    (subset : ∀ value, value ∈ source → value ∈ target) :
    source.length ≤ target.length := by
  induction source generalizing target with
  | nil => simp
  | cons head tail induction =>
      have nodupParts := List.pairwise_cons.mp nodup
      have headNotTail : head ∉ tail := by
        intro member
        exact (nodupParts.1 head member) rfl
      have headTarget : head ∈ target :=
        subset head (List.Mem.head tail)
      have tailSubset :
          ∀ value, value ∈ tail → value ∈ target.erase head := by
        intro value member
        have different : value ≠ head := by
          intro equality
          subst value
          exact headNotTail member
        exact (List.mem_erase_of_ne different).mpr
          (subset value (List.Mem.tail head member))
      have lengthBound := induction nodupParts.2 tailSubset
      rw [List.length_erase_of_mem headTarget] at lengthBound
      have targetPositive : 1 ≤ target.length := by
        apply List.length_pos_iff.mpr
        intro empty
        subst target
        simp at headTarget
      simp only [List.length_cons]
      omega

/-- The displayed letters of the source cell `y p y`. -/
def CellContains.cellLetters
    {word : Word Nat} {tested : Nat}
    (cell : CellContains word tested) : List Nat :=
  cell.y :: (cell.p ++ [cell.y])

/-- The suffix `p y` inserted by the expansion `y p y -> y p y p y`. -/
def CellContains.expansionCopy
    {word : Word Nat} {tested : Nat}
    (cell : CellContains word tested) : List Nat :=
  cell.p ++ [cell.y]

theorem CellContains.toList_eq_context
    {word : Word Nat} {tested : Nat}
    (cell : CellContains word tested) :
    word.toList =
      cell.leadingContext ++ cell.cellLetters ++ cell.suffix := by
  simpa [CellContains.cellLetters, List.append_assoc] using
    cell.factorization

theorem CellContains.mem_expansionCopy_of_mem_cellLetters
    {word : Word Nat} {tested letter : Nat}
    (cell : CellContains word tested)
    (member : letter ∈ cell.cellLetters) :
    letter ∈ cell.expansionCopy := by
  change letter ∈ cell.y :: (cell.p ++ [cell.y]) at member
  change letter ∈ cell.p ++ [cell.y]
  rcases List.mem_cons.mp member with equal | inCopy
  · subst letter
    simp
  · exact inCopy

theorem CellContains.mem_cellLetters_of_mem_expansionCopy
    {word : Word Nat} {tested letter : Nat}
    (cell : CellContains word tested)
    (member : letter ∈ cell.expansionCopy) :
    letter ∈ cell.cellLetters := by
  change letter ∈ cell.p ++ [cell.y] at member
  change letter ∈ cell.y :: (cell.p ++ [cell.y])
  exact List.Mem.tail cell.y member

/-- A concrete nonempty word with list `prefix ++ y p y p y ++ suffix`. -/
def CellContains.expansionWord
    {word : Word Nat} {tested : Nat}
    (cell : CellContains word tested) : Word Nat :=
  match cell.leadingContext with
  | [] =>
      ⟨cell.y,
        cell.p ++ cell.y :: (cell.p ++ cell.y :: cell.suffix)⟩
  | first :: rest =>
      ⟨first,
        rest ++ cell.y ::
          (cell.p ++ cell.y :: (cell.p ++ cell.y :: cell.suffix))⟩

theorem CellContains.expansionWord_toList
    {word : Word Nat} {tested : Nat}
    (cell : CellContains word tested) :
    cell.expansionWord.toList =
      cell.leadingContext ++ cell.cellLetters ++
        cell.expansionCopy ++ cell.suffix := by
  cases leadingShape : cell.leadingContext <;>
    simp [CellContains.expansionWord, CellContains.cellLetters,
      CellContains.expansionCopy, leadingShape, Word.toList,
      List.append_assoc]

/-- Proof-relevant data for one contextual `y p y -> y p y p y` step. -/
structure ContextualCellExpansion
    {word : Word Nat} {tested : Nat}
    (cell : CellContains word tested) (expanded : Word Nat) : Prop where
  derives : Derives basis word expanded
  expanded_toList :
    expanded.toList =
      cell.leadingContext ++ cell.cellLetters ++
        cell.expansionCopy ++ cell.suffix

private theorem derives_in_list_context
    {source target localSource localTarget : Word Nat}
    (derivation : Derives basis localSource localTarget)
    (leftContext suffix : List Nat)
    (sourceShape :
      source.toList = leftContext ++ localSource.toList ++ suffix)
    (targetShape :
      target.toList = leftContext ++ localTarget.toList ++ suffix) :
    Derives basis source target := by
  cases leftContext with
  | nil =>
      cases suffix with
      | nil =>
          have sourceEq : source = localSource :=
            Word.toList_injective (by simpa using sourceShape)
          have targetEq : target = localTarget :=
            Word.toList_injective (by simpa using targetShape)
          subst source
          subst target
          exact derivation
      | cons suffixHead suffixTail =>
          let suffixWord : Word Nat := ⟨suffixHead, suffixTail⟩
          have sourceEq : source = localSource ++ suffixWord :=
            Word.toList_injective (by
              rw [Word.toList_append]
              simpa [suffixWord] using sourceShape)
          have targetEq : target = localTarget ++ suffixWord :=
            Word.toList_injective (by
              rw [Word.toList_append]
              simpa [suffixWord] using targetShape)
          subst source
          subst target
          exact Derives.appendRight derivation suffixWord
  | cons prefixHead prefixTail =>
      let prefixWord : Word Nat := ⟨prefixHead, prefixTail⟩
      cases suffix with
      | nil =>
          have sourceEq : source = prefixWord ++ localSource :=
            Word.toList_injective (by
              rw [Word.toList_append]
              simpa [prefixWord] using sourceShape)
          have targetEq : target = prefixWord ++ localTarget :=
            Word.toList_injective (by
              rw [Word.toList_append]
              simpa [prefixWord] using targetShape)
          subst source
          subst target
          exact Derives.prepend prefixWord derivation
      | cons suffixHead suffixTail =>
          let suffixWord : Word Nat := ⟨suffixHead, suffixTail⟩
          have sourceEq :
              source = (prefixWord ++ localSource) ++ suffixWord :=
            Word.toList_injective (by
              simp only [Word.toList_append]
              simpa [prefixWord, suffixWord, List.append_assoc] using
                sourceShape)
          have targetEq :
              target = (prefixWord ++ localTarget) ++ suffixWord :=
            Word.toList_injective (by
              simp only [Word.toList_append]
              simpa [prefixWord, suffixWord, List.append_assoc] using
                targetShape)
          subst source
          subst target
          exact Derives.appendRight
            (Derives.prepend prefixWord derivation) suffixWord

/-- Every displayed cell admits the contextual expansion. The empty interior
uses `x^2 = x^3`; a nonempty interior uses `xyx = xyxyx`. -/
theorem CellContains.exists_contextualCellExpansion
    {word : Word Nat} {tested : Nat}
    (cell : CellContains word tested) :
    ∃ expanded, ContextualCellExpansion cell expanded := by
  let expanded := cell.expansionWord
  refine ⟨expanded, ?_, cell.expansionWord_toList⟩
  cases interiorShape : cell.p with
  | nil =>
      let yWord := Word.singleton cell.y
      apply derives_in_list_context
        (derivesPowerExpansion yWord) cell.leadingContext cell.suffix
      · simpa [CellContains.cellLetters, yWord, interiorShape,
          Word.toList_append, List.append_assoc] using
          cell.toList_eq_context
      · simpa [expanded, CellContains.cellLetters,
          CellContains.expansionCopy, yWord, interiorShape,
          Word.toList_append, List.append_assoc] using
          cell.expansionWord_toList
  | cons interiorHead interiorTail =>
      let yWord := Word.singleton cell.y
      let interiorWord : Word Nat := ⟨interiorHead, interiorTail⟩
      apply derives_in_list_context
        (derivesSandwichExpansion yWord interiorWord)
        cell.leadingContext cell.suffix
      · simpa [CellContains.cellLetters, yWord, interiorWord,
          interiorShape, Word.toList_append, List.append_assoc] using
          cell.toList_eq_context
      · simpa [expanded, CellContains.cellLetters,
          CellContains.expansionCopy, yWord, interiorWord,
          interiorShape, Word.toList_append, List.append_assoc] using
          cell.expansionWord_toList

/-- The exact multiplicity change: the inserted suffix contributes one copy
of each of its letters and changes no other count. -/
theorem ContextualCellExpansion.count_eq
    {word expanded : Word Nat} {tested : Nat}
    {cell : CellContains word tested}
    (step : ContextualCellExpansion cell expanded)
    (letter : Nat) :
    expanded.toList.count letter =
      word.toList.count letter + cell.expansionCopy.count letter := by
  rw [step.expanded_toList, cell.toList_eq_context]
  simp only [List.count_append]
  omega

/-- Contextual cell expansion preserves the set of supported letters. -/
theorem ContextualCellExpansion.sameLetterSupport
    {word expanded : Word Nat} {tested : Nat}
    {cell : CellContains word tested}
    (step : ContextualCellExpansion cell expanded) :
    SameLetterSupport word expanded := by
  intro letter
  rw [cell.toList_eq_context, step.expanded_toList]
  simp only [List.mem_append]
  constructor
  · intro member
    rcases member with (inPrefix | inCell) | inSuffix
    · exact Or.inl (Or.inl (Or.inl inPrefix))
    · exact Or.inl (Or.inl (Or.inr inCell))
    · exact Or.inr inSuffix
  · intro member
    rcases member with ((inPrefix | inCell) | inCopy) | inSuffix
    · exact Or.inl (Or.inl inPrefix)
    · exact Or.inl (Or.inr inCell)
    · exact Or.inl (Or.inr
        (cell.mem_cellLetters_of_mem_expansionCopy inCopy))
    · exact Or.inr inSuffix

/-- Every letter in the selected cell occurs at least twice after expansion. -/
theorem ContextualCellExpansion.duplicatesCellLetter
    {word expanded : Word Nat} {tested letter : Nat}
    {cell : CellContains word tested}
    (step : ContextualCellExpansion cell expanded)
    (inside : letter ∈ cell.cellLetters) :
    2 ≤ expanded.toList.count letter := by
  have sourceMember : letter ∈ word.toList := by
    rw [cell.toList_eq_context]
    simp only [List.mem_append]
    exact Or.inl (Or.inr inside)
  have sourcePositive : 1 ≤ word.toList.count letter :=
    List.one_le_count_iff.mpr sourceMember
  have copyPositive : 1 ≤ cell.expansionCopy.count letter :=
    List.one_le_count_iff.mpr
      (cell.mem_expansionCopy_of_mem_cellLetters inside)
  rw [step.count_eq letter]
  omega

/-- No letter becomes a new singleton under contextual cell expansion. -/
theorem ContextualCellExpansion.noNewSingleton
    {word expanded : Word Nat} {tested : Nat}
    {cell : CellContains word tested}
    (step : ContextualCellExpansion cell expanded)
    (letter : Nat)
    (targetSingleton : expanded.toList.count letter = 1) :
    word.toList.count letter = 1 := by
  have targetMember : letter ∈ expanded.toList :=
    List.count_pos_iff.mp (by omega)
  have sourceMember : letter ∈ word.toList :=
    (step.sameLetterSupport letter).mpr targetMember
  have sourcePositive : 1 ≤ word.toList.count letter :=
    List.one_le_count_iff.mpr sourceMember
  have countChange := step.count_eq letter
  omega

/-- Expanding a cell containing a chosen singleton strictly lowers the
singleton-support measure. -/
theorem ContextualCellExpansion.singletonMeasure_lt
    {word expanded : Word Nat} {tested : Nat}
    {cell : CellContains word tested}
    (step : ContextualCellExpansion cell expanded)
    (testedSingleton : word.toList.count tested = 1) :
    singletonMeasure expanded < singletonMeasure word := by
  have testedDuplicated : 2 ≤ expanded.toList.count tested :=
    step.duplicatesCellLetter cell.tested_mem
  have testedSource : tested ∈ singletonLetters word :=
    (mem_singletonLetters_iff word tested).mpr testedSingleton
  have testedTarget : tested ∉ singletonLetters expanded := by
    intro member
    have countOne :=
      (mem_singletonLetters_iff expanded tested).mp member
    omega
  have augmentedNodup :
      (tested :: singletonLetters expanded).Nodup := by
    simp only [List.nodup_cons]
    exact ⟨testedTarget, singletonLetters_nodup expanded⟩
  have augmentedSubset :
      ∀ letter,
        letter ∈ tested :: singletonLetters expanded →
          letter ∈ singletonLetters word := by
    intro letter member
    simp only [List.mem_cons] at member
    rcases member with equal | targetMember
    · subst letter
      exact testedSource
    · have targetCount :=
        (mem_singletonLetters_iff expanded letter).mp targetMember
      exact (mem_singletonLetters_iff word letter).mpr
        (step.noNewSingleton letter targetCount)
  have lengthBound :=
    nodup_length_le_of_subset augmentedNodup augmentedSubset
  simp only [List.length_cons] at lengthBound
  simpa [singletonMeasure] using (show
    (singletonLetters expanded).length <
      (singletonLetters word).length by omega)

private theorem cellContains_of_mem_sides
    {word : Word Nat} {tested boundary : Nat}
    {before after : List Nat}
    (shape : word.toList = before ++ tested :: after)
    (boundaryBefore : boundary ∈ before)
    (boundaryAfter : boundary ∈ after) :
    Nonempty (CellContains word tested) := by
  obtain ⟨leadingContext, leftMiddle, beforeShape⟩ :=
    List.mem_iff_append.mp boundaryBefore
  obtain ⟨rightMiddle, suffix, afterShape⟩ :=
    List.mem_iff_append.mp boundaryAfter
  refine
    ⟨{ y := boundary
       leadingContext := leadingContext
       p := leftMiddle ++ tested :: rightMiddle
       suffix := suffix
       factorization := ?_
       tested_mem := ?_ }⟩
  · rw [shape, beforeShape, afterShape]
    simp [List.append_assoc]
  · simp [List.append_assoc]

private theorem cellContains_of_two_le_count
    {word : Word Nat} {tested : Nat}
    (two : 2 ≤ word.toList.count tested) :
    Nonempty (CellContains word tested) := by
  have member : tested ∈ word.toList :=
    List.count_pos_iff.mp (by omega)
  obtain ⟨beforeTested, suffix, shape⟩ :=
    List.mem_iff_append.mp member
  have countShape := two
  rw [shape] at countShape
  simp only [List.count_append, List.count_cons_self] at countShape
  by_cases prefixZero : beforeTested.count tested = 0
  · have suffixMember : tested ∈ suffix :=
      List.count_pos_iff.mp (by omega)
    obtain ⟨middle, after, suffixShape⟩ :=
      List.mem_iff_append.mp suffixMember
    refine
      ⟨{ y := tested
         leadingContext := beforeTested
         p := middle
         suffix := after
         factorization := ?_
         tested_mem := by simp }⟩
    rw [shape, suffixShape]
  · have prefixMember : tested ∈ beforeTested :=
      List.count_pos_iff.mp (by omega)
    obtain ⟨before, middle, prefixShape⟩ :=
      List.mem_iff_append.mp prefixMember
    refine
      ⟨{ y := tested
         leadingContext := before
         p := middle
         suffix := suffix
         factorization := ?_
         tested_mem := by simp }⟩
    rw [shape, prefixShape]
    simp [List.append_assoc]

private theorem mem_insert_middle
    {letter : Nat} {left inserted right : List Nat}
    (member : letter ∈ left ++ right) :
    letter ∈ left ++ inserted ++ right := by
  simp only [List.mem_append] at member ⊢
  rcases member with inLeft | inRight
  · exact Or.inl (Or.inl inLeft)
  · exact Or.inr inRight

/-- Inserting letters anywhere in a word preserves every pre-existing cell. -/
private theorem CellContains.mono_insert
    {source target : Word Nat} {tested : Nat}
    (cell : CellContains source tested)
    (left inserted right : List Nat)
    (sourceShape : source.toList = left ++ right)
    (targetShape : target.toList = left ++ inserted ++ right) :
    Nonempty (CellContains target tested) := by
  by_cases atBoundary : tested = cell.y
  · apply cellContains_of_two_le_count
    have sourceTwoAtBoundary : 2 ≤ source.toList.count cell.y := by
      rw [cell.factorization]
      simp only [List.count_append, List.count_cons_self]
      omega
    have sourceTwo : 2 ≤ source.toList.count tested := by
      simpa only [atBoundary] using sourceTwoAtBoundary
    have countChange :
        target.toList.count tested =
          source.toList.count tested + inserted.count tested := by
      rw [sourceShape, targetShape]
      simp only [List.count_append]
      omega
    omega
  · have testedInP : tested ∈ cell.p := by
      rcases List.mem_cons.mp cell.tested_mem with boundary | inside
      · exact False.elim (atBoundary boundary)
      · rcases List.mem_append.mp inside with inP | boundary
        · exact inP
        · exact False.elim
            (atBoundary (List.mem_singleton.mp boundary))
    obtain ⟨beforeP, afterP, pShape⟩ :=
      List.mem_iff_append.mp testedInP
    let beforeTested := cell.leadingContext ++ cell.y :: beforeP
    let afterTested := afterP ++ cell.y :: cell.suffix
    have testedShape :
        source.toList = beforeTested ++ tested :: afterTested := by
      rw [cell.factorization, pShape]
      simp [beforeTested, afterTested, List.append_assoc]
    have boundaryBefore : cell.y ∈ beforeTested := by
      simp [beforeTested]
    have boundaryAfter : cell.y ∈ afterTested := by
      simp [afterTested]
    have splitEquality :
        left ++ right = beforeTested ++ tested :: afterTested :=
      sourceShape.symm.trans testedShape
    rcases List.append_eq_append_iff.mp splitEquality with
        ⟨extra, beforeShape, rightShape⟩ |
        ⟨extra, leftShape, tailShape⟩
    · have targetSplit :
          target.toList =
            (left ++ inserted ++ extra) ++ tested :: afterTested := by
        rw [targetShape, rightShape]
        simp [List.append_assoc]
      have boundaryBefore' :
          cell.y ∈ left ++ inserted ++ extra := by
        apply mem_insert_middle
        rw [← beforeShape]
        exact boundaryBefore
      exact cellContains_of_mem_sides
        targetSplit boundaryBefore' boundaryAfter
    · cases extra with
      | nil =>
          simp only [List.append_nil, List.nil_append] at leftShape tailShape
          have targetSplit :
              target.toList =
                (beforeTested ++ inserted) ++ tested :: afterTested := by
            rw [targetShape, leftShape, ← tailShape]
          have boundaryBefore' :
              cell.y ∈ beforeTested ++ inserted :=
            List.mem_append_left inserted boundaryBefore
          exact cellContains_of_mem_sides
            targetSplit boundaryBefore' boundaryAfter
      | cons extraHead extraTail =>
          simp only [List.cons_append] at tailShape
          injection tailShape with headEquality afterShape
          subst extraHead
          have targetSplit :
              target.toList =
                beforeTested ++ tested ::
                  (extraTail ++ inserted ++ right) := by
            rw [targetShape, leftShape]
            simp [List.append_assoc]
          have boundaryAfter' :
              cell.y ∈ extraTail ++ inserted ++ right := by
            apply mem_insert_middle
            rw [← afterShape]
            exact boundaryAfter
          exact cellContains_of_mem_sides
            targetSplit boundaryBefore boundaryAfter'

private theorem repeatedWord_insert
    {source target : Word Nat}
    (repeated : RepeatedWord source)
    (left inserted right : List Nat)
    (sourceShape : source.toList = left ++ right)
    (targetShape : target.toList = left ++ inserted ++ right)
    (insertedSupported :
      ∀ letter, letter ∈ inserted → letter ∈ source.toList) :
    RepeatedWord target := by
  refine ⟨?_⟩
  intro tested targetMember
  have sourceMember : tested ∈ source.toList := by
    rw [targetShape] at targetMember
    simp only [List.mem_append] at targetMember
    rw [sourceShape]
    simp only [List.mem_append]
    rcases targetMember with (inLeft | inInserted) | inRight
    · exact Or.inl inLeft
    · have supported := insertedSupported tested inInserted
      rw [sourceShape] at supported
      simpa only [List.mem_append] using supported
    · exact Or.inr inRight
  exact Classical.choice <|
    (repeated tested sourceMember).mono_insert
      left inserted right sourceShape targetShape

/-- Contextual cell expansion preserves Volkov's repeated-word condition. -/
theorem ContextualCellExpansion.repeatedWord
    {word expanded : Word Nat} {tested : Nat}
    {cell : CellContains word tested}
    (step : ContextualCellExpansion cell expanded)
    (repeated : RepeatedWord word) :
    RepeatedWord expanded := by
  apply repeatedWord_insert repeated
    (cell.leadingContext ++ cell.cellLetters)
    cell.expansionCopy cell.suffix
  · exact cell.toList_eq_context
  · simpa [List.append_assoc] using step.expanded_toList
  · intro letter member
    rw [cell.toList_eq_context]
    simp only [List.mem_append]
    exact Or.inl (Or.inr
      (cell.mem_cellLetters_of_mem_expansionCopy member))

/-- Volkov's first repeated-class regularity step: a repeated word derives,
through one selected singleton-containing cell, to a repeated word with the
same support and a strictly smaller singleton-support measure. -/
theorem exists_repeated_contextualExpansion
    {word : Word Nat} (repeated : RepeatedWord word)
    {tested : Nat} (testedSingleton : word.toList.count tested = 1) :
    ∃ expanded,
      Derives basis word expanded ∧
        SameLetterSupport word expanded ∧
        RepeatedWord expanded ∧
        singletonMeasure expanded < singletonMeasure word := by
  have testedMember : tested ∈ word.toList :=
    List.count_pos_iff.mp (by omega)
  let cell := repeated tested testedMember
  obtain ⟨expanded, step⟩ := cell.exists_contextualCellExpansion
  exact ⟨expanded, step.derives, step.sameLetterSupport,
    step.repeatedWord repeated,
    step.singletonMeasure_lt testedSingleton⟩

/-- Every repeated word derives to an explicit same-support word in which no
letter occurs exactly once. -/
theorem repeatedWord_derives_noSingletonLetters
    {word : Word Nat} (repeated : RepeatedWord word) :
    ∃ q,
      Derives basis word q ∧
        SameLetterSupport word q ∧
        NoSingletonLetters q := by
  have closeAtMeasure :
      ∀ bound current,
        singletonMeasure current = bound →
          RepeatedWord current →
            ∃ q,
              Derives basis current q ∧
                SameLetterSupport current q ∧
                NoSingletonLetters q := by
    intro bound
    exact Nat.strongRecOn
      (motive := fun currentBound =>
        ∀ current,
          singletonMeasure current = currentBound →
            RepeatedWord current →
              ∃ q,
                Derives basis current q ∧
                  SameLetterSupport current q ∧
                  NoSingletonLetters q)
      bound (by
        intro currentBound induction current measureEq currentRepeated
        cases singletonShape : singletonLetters current with
        | nil =>
            refine ⟨current, Derives.refl current,
              SameLetterSupport.refl current, ?_⟩
            intro letter _ countOne
            have member : letter ∈ singletonLetters current :=
              (mem_singletonLetters_iff current letter).mpr countOne
            rw [singletonShape] at member
            simp at member
        | cons tested rest =>
            have testedInSingletons :
                tested ∈ singletonLetters current := by
              rw [singletonShape]
              simp
            have testedSingleton : current.toList.count tested = 1 :=
              (mem_singletonLetters_iff current tested).mp testedInSingletons
            obtain ⟨expanded, expansion, sameSupport,
                expandedRepeated, smaller⟩ :=
              exists_repeated_contextualExpansion
                currentRepeated testedSingleton
            have smallerBound :
                singletonMeasure expanded < currentBound := by
              simpa [measureEq] using smaller
            obtain ⟨q, remainder, finalSupport, noSingletons⟩ :=
              induction (singletonMeasure expanded) smallerBound
                expanded rfl expandedRepeated
            exact ⟨q, expansion.trans remainder,
              sameSupport.trans finalSupport, noSingletons⟩)
  exact closeAtMeasure
    (singletonMeasure word) word rfl repeated

end SemigroupBasis.CoRoots.S5_415
