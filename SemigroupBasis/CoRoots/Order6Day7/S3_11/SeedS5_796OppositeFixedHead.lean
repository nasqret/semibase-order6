import SemigroupBasis.CoRoots.Order6Day7.S3_11.SeedS5_796OppositeGuardedLift

/-!
# Unrestricted parity / exact-separator / fixed-first completeness

A globally unique first letter is removed from both words, with every exact
cut transported across the protected prefix.  A repeated first letter is
expanded by exactly two copies, preserving parity, before the complete
twenty-five-law separator normalizer is replayed behind the protected pair.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.S3_11.SeedS5_796Opposite

open SemigroupBasis
open SemigroupBasis.Examples

private abbrev targetBasis : List (Identity Nat) :=
  reversedBasis Rank001.basis

/-- The exact invariant of the reversed rank-001 factor intersection. -/
structure SameFixedHeadParitySeparatorSignature
    (left right : Word Nat) : Prop where
  paritySeparator :
    SemigroupBasis.CoRoots.S5_441Invariant.SameParitySeparatorSignature
      left right
  first : left.head = right.head

namespace SameFixedHeadParitySeparatorSignature

theorem symm {left right : Word Nat}
    (same : SameFixedHeadParitySeparatorSignature left right) :
    SameFixedHeadParitySeparatorSignature right left :=
  ⟨same.paritySeparator.symm, same.first.symm⟩

end SameFixedHeadParitySeparatorSignature

private theorem headCountOneTransport
    {left right : Word Nat}
    (same : SameFixedHeadParitySeparatorSignature left right)
    (countOne : left.toList.count left.head = 1) :
    right.toList.count right.head = 1 := by
  have concreteCut :
      UniqueSeparatorFourExactCut
        left.toList [] left.head left.tail := by
    refine ⟨?_, countOne, ?_⟩
    · cases left
      rfl
    · intro tested member
      simp at member
  have sourceSignature :
      SemigroupBasis.CoRoots.S5_441Invariant.ExactCutSignature
        left left.head [] left.tail :=
    ⟨[], left.tail, concreteCut,
      fun _ => Iff.rfl, fun _ => Iff.rfl⟩
  have targetSignature :=
    (same.paritySeparator.exactCuts
      left.head [] left.tail).mp sourceSignature
  rcases targetSignature with ⟨_, _, targetCut, _, _⟩
  simpa [same.first] using targetCut.2.1

private theorem headCountOne_iff
    {left right : Word Nat}
    (same : SameFixedHeadParitySeparatorSignature left right) :
    left.toList.count left.head = 1 ↔
      right.toList.count right.head = 1 :=
  ⟨headCountOneTransport same,
    headCountOneTransport same.symm⟩

private theorem exactCut_left_mem
    {letters left right : List Nat} {separator tested : Nat}
    (cut : UniqueSeparatorFourExactCut letters left separator right)
    (member : tested ∈ left) : tested ∈ letters := by
  rw [cut.1]
  exact List.mem_append_left _ member

private theorem exactCut_right_mem
    {letters left right : List Nat} {separator tested : Nat}
    (cut : UniqueSeparatorFourExactCut letters left separator right)
    (member : tested ∈ right) : tested ∈ letters := by
  rw [cut.1]
  exact List.mem_append_right _ (List.Mem.tail separator member)

private theorem exactCut_separator_mem
    {letters left right : List Nat} {separator : Nat}
    (cut : UniqueSeparatorFourExactCut letters left separator right) :
    separator ∈ letters := by
  rw [cut.1]
  exact List.mem_append_right _ (List.Mem.head _)

private theorem exactCut_addFreshHead
    {letters left right : List Nat} {head separator : Nat}
    (headAbsent : head ∉ letters)
    (cut : UniqueSeparatorFourExactCut letters left separator right) :
    UniqueSeparatorFourExactCut
      (head :: letters) (head :: left) separator right := by
  have headNeSeparator : head ≠ separator := by
    intro equal
    subst separator
    exact headAbsent (exactCut_separator_mem cut)
  refine ⟨?_, ?_, ?_⟩
  · simp [cut.1]
  · simpa [List.count_cons_of_ne headNeSeparator] using cut.2.1
  · intro tested leftMember rightMember
    rcases List.mem_cons.mp leftMember with equal | member
    · subst tested
      exact headAbsent (exactCut_right_mem cut rightMember)
    · exact cut.2.2 tested member rightMember

private theorem exactCut_dropFreshHead
    {letters wholeLeft right : List Nat} {head separator : Nat}
    (headNeSeparator : head ≠ separator)
    (cut :
      UniqueSeparatorFourExactCut
        (head :: letters) wholeLeft separator right) :
    ∃ left,
      wholeLeft = head :: left ∧
        UniqueSeparatorFourExactCut letters left separator right := by
  cases wholeLeft with
  | nil =>
      have heads : head = separator := by
        simpa using congrArg List.head? cut.1
      exact False.elim (headNeSeparator heads)
  | cons leftHead leftTail =>
      have split := cut.1
      simp only [List.cons_append, List.cons.injEq] at split
      have headEq : head = leftHead := split.1
      subst leftHead
      refine ⟨leftTail, rfl, split.2, ?_, ?_⟩
      · simpa [List.count_cons_of_ne headNeSeparator] using cut.2.1
      · intro tested leftMember rightMember
        exact cut.2.2 tested
          (List.Mem.tail head leftMember) rightMember

private theorem tailSupportIffOfCons
    {head : Nat} {left right : List Nat}
    (headAbsentLeft : head ∉ left)
    (headAbsentRight : head ∉ right)
    (same : ∀ tested,
      tested ∈ head :: left ↔ tested ∈ head :: right) :
    ∀ tested, tested ∈ left ↔ tested ∈ right := by
  intro tested
  by_cases equal : tested = head
  · subst tested
    simp [headAbsentLeft, headAbsentRight]
  · simpa [equal] using same tested

private theorem exactCutSignature_addFreshHead
    {source : Word Nat} {head separator : Nat}
    {leftSupport rightSupport : List Nat}
    (headAbsent : head ∉ source.toList)
    (signature :
      SemigroupBasis.CoRoots.S5_441Invariant.ExactCutSignature
        source separator leftSupport rightSupport) :
    SemigroupBasis.CoRoots.S5_441Invariant.ExactCutSignature
      (Word.singleton head ++ source) separator
      (head :: leftSupport) rightSupport := by
  rcases signature with
    ⟨left, right, cut, leftSupportIff, rightSupportIff⟩
  refine ⟨head :: left, right, ?_, ?_, rightSupportIff⟩
  · simpa [uniqueSeparatorWordOfCons, Word.toList,
      Word.append, Word.singleton] using
        exactCut_addFreshHead headAbsent cut
  · intro tested
    simp only [List.mem_cons]
    constructor
    · rintro (rfl | member)
      · exact Or.inl rfl
      · exact Or.inr ((leftSupportIff tested).1 member)
    · rintro (rfl | member)
      · exact Or.inl rfl
      · exact Or.inr ((leftSupportIff tested).2 member)

private theorem exactCutSignature_separator_ne_head
    {source : Word Nat} {head separator : Nat}
    {leftSupport rightSupport : List Nat}
    (headAbsent : head ∉ source.toList)
    (signature :
      SemigroupBasis.CoRoots.S5_441Invariant.ExactCutSignature
        source separator leftSupport rightSupport) :
    head ≠ separator := by
  rintro rfl
  rcases signature with ⟨left, right, cut, _, _⟩
  exact headAbsent (exactCut_separator_mem cut)

private theorem exactCutSignature_head_absent_leftSupport
    {source : Word Nat} {head separator : Nat}
    {leftSupport rightSupport : List Nat}
    (headAbsent : head ∉ source.toList)
    (signature :
      SemigroupBasis.CoRoots.S5_441Invariant.ExactCutSignature
        source separator leftSupport rightSupport) :
    head ∉ leftSupport := by
  rcases signature with
    ⟨left, right, cut, leftSupportIff, _⟩
  intro member
  exact headAbsent <|
    exactCut_left_mem cut ((leftSupportIff head).2 member)

private theorem exactCutSignature_dropFreshHead
    {source : Word Nat} {head separator : Nat}
    {leftSupport rightSupport : List Nat}
    (headAbsent : head ∉ source.toList)
    (headNeSeparator : head ≠ separator)
    (headAbsentLeftSupport : head ∉ leftSupport)
    (signature :
      SemigroupBasis.CoRoots.S5_441Invariant.ExactCutSignature
        (Word.singleton head ++ source) separator
        (head :: leftSupport) rightSupport) :
    SemigroupBasis.CoRoots.S5_441Invariant.ExactCutSignature
      source separator leftSupport rightSupport := by
  rcases signature with
    ⟨wholeLeft, right, wholeCut,
      wholeLeftSupportIff, rightSupportIff⟩
  have listCut :
      UniqueSeparatorFourExactCut
        (head :: source.toList) wholeLeft separator right := by
    simpa [uniqueSeparatorWordOfCons, Word.toList,
      Word.append, Word.singleton] using wholeCut
  obtain ⟨left, wholeLeftEq, cut⟩ :=
    exactCut_dropFreshHead headNeSeparator listCut
  have headAbsentLeft : head ∉ left := by
    intro member
    exact headAbsent (exactCut_left_mem cut member)
  have consSupport : ∀ tested,
      tested ∈ head :: left ↔
        tested ∈ head :: leftSupport := by
    intro tested
    simpa [wholeLeftEq] using wholeLeftSupportIff tested
  refine ⟨left, right, cut, ?_, rightSupportIff⟩
  exact tailSupportIffOfCons
    headAbsentLeft headAbsentLeftSupport consSupport

private theorem suffixSameParitySeparator
    (head : Nat) (left right : Word Nat)
    (headAbsentLeft : head ∉ left.toList)
    (headAbsentRight : head ∉ right.toList)
    (whole :
      SameFixedHeadParitySeparatorSignature
        (Word.singleton head ++ left)
        (Word.singleton head ++ right)) :
    SemigroupBasis.CoRoots.S5_441Invariant.SameParitySeparatorSignature
      left right := by
  refine ⟨?_, ?_, ?_⟩
  · intro letter
    by_cases equal : letter = head
    · subst letter
      simp [headAbsentLeft, headAbsentRight]
    · simpa [uniqueSeparatorWordOfCons, Word.toList,
        Word.append, Word.singleton, equal, Ne.symm equal] using
          whole.paritySeparator.support letter
  · intro separator leftSupport rightSupport
    constructor
    · intro sourceSignature
      have headNeSeparator :=
        exactCutSignature_separator_ne_head
          headAbsentLeft sourceSignature
      have headAbsentSupport :=
        exactCutSignature_head_absent_leftSupport
          headAbsentLeft sourceSignature
      have prefixedSource :=
        exactCutSignature_addFreshHead
          headAbsentLeft sourceSignature
      have prefixedTarget :=
        (whole.paritySeparator.exactCuts
          separator (head :: leftSupport) rightSupport).1
            prefixedSource
      exact exactCutSignature_dropFreshHead
        headAbsentRight headNeSeparator headAbsentSupport
          prefixedTarget
    · intro targetSignature
      have headNeSeparator :=
        exactCutSignature_separator_ne_head
          headAbsentRight targetSignature
      have headAbsentSupport :=
        exactCutSignature_head_absent_leftSupport
          headAbsentRight targetSignature
      have prefixedTarget :=
        exactCutSignature_addFreshHead
          headAbsentRight targetSignature
      have prefixedSource :=
        (whole.paritySeparator.exactCuts
          separator (head :: leftSupport) rightSupport).2
            prefixedTarget
      exact exactCutSignature_dropFreshHead
        headAbsentLeft headNeSeparator headAbsentSupport
          prefixedSource
  · intro letter
    by_cases equal : letter = head
    · subst letter
      have leftZero : left.toList.count head = 0 :=
        List.count_eq_zero.mpr headAbsentLeft
      have rightZero : right.toList.count head = 0 :=
        List.count_eq_zero.mpr headAbsentRight
      simp [leftZero, rightZero]
    · simpa [uniqueSeparatorWordOfCons, Word.toList, Word.append,
        Word.singleton, equal, Ne.symm equal] using
          whole.paritySeparator.parity letter

private theorem headNotMemTailOfCountOne
    (source : Word Nat)
    (countOne : source.toList.count source.head = 1) :
    source.head ∉ source.tail := by
  intro member
  have positive : 0 < source.tail.count source.head :=
    List.count_pos_iff.mpr member
  simp only [Word.toList, List.count_cons_self] at countOne
  omega

private theorem headMemTailOfCountNeOne
    (source : Word Nat)
    (countNotOne : source.toList.count source.head ≠ 1) :
    source.head ∈ source.tail := by
  apply Decidable.byContradiction
  intro absent
  apply countNotOne
  cases source with
  | mk head tail =>
      simp [Word.toList, List.count_eq_zero.mpr absent]

private theorem tailNilOfSameSignature
    {left right : Word Nat}
    (same : SameFixedHeadParitySeparatorSignature left right)
    (rightHeadSimple : right.toList.count right.head = 1)
    (leftTailEmpty : left.tail = []) :
    right.tail = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro letter member
  have rightMember : letter ∈ right.toList := by
    cases right
    simp [Word.toList, member]
  have leftMember : letter ∈ left.toList :=
    (same.paritySeparator.support letter).2 rightMember
  have letterIsLeftHead : letter = left.head := by
    have headOrTail :
        letter = left.head ∨ letter ∈ left.tail := by
      simpa [Word.toList] using leftMember
    rcases headOrTail with equal | inTail
    · exact equal
    · simp [leftTailEmpty] at inTail
  have letterIsRightHead : letter = right.head :=
    letterIsLeftHead.trans same.first
  have rightHeadInTail : right.head ∈ right.tail := by
    simpa [letterIsRightHead] using member
  exact
    (headNotMemTailOfCountOne right rightHeadSimple)
      rightHeadInTail

private abbrev ListDerives :=
  SemigroupBasis.CoRoots.S5_107.ListDerives targetBasis

private theorem listDerivesAddInitialPair
    (head : Nat) (tail : List Nat)
    (headInTail : head ∈ tail) :
    ListDerives
      (head :: tail)
      ([head, head] ++ head :: tail) := by
  rcases List.append_of_mem headInTail with
    ⟨before, after, rfl⟩
  cases before with
  | nil =>
      have expanded :=
        SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
          (derivesPowerExpansion (Word.singleton head))
      simpa [Word.toList_append, List.append_assoc] using
        expanded.append after
  | cons middleHead middleTail =>
      let middle :=
        SemigroupBasis.CoRoots.S5_107.listWordOfCons middleHead middleTail
      have expanded :=
        SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
          (derivesTripleInitialExpansion
            (Word.singleton head) middle)
      simpa [middle, SemigroupBasis.CoRoots.S5_107.listWordOfCons,
        Word.toList_append, List.append_assoc] using
        expanded.append after

private theorem derivesAddInitialPair
    (source : Word Nat)
    (headInTail : source.head ∈ source.tail) :
    Derives targetBasis source
      ((Word.singleton source.head ++ Word.singleton source.head) ++ source) := by
  cases source with
  | mk head tail =>
      have listDerivation :=
        listDerivesAddInitialPair head tail headInTail
      simpa [SemigroupBasis.CoRoots.S5_107.listWordOfCons,
        Word.singleton, Word.append, List.append_assoc] using
          SemigroupBasis.CoRoots.S5_107.ListDerives.toWord listDerivation

private theorem bind_singleton (source : Word Nat) :
    source.bind Word.singleton = source := by
  apply Word.toList_injective
  simp [Word.toList_bind]

/-- Exact unrestricted completeness for parity, all unique-separator cuts,
and a common protected first variable. -/
theorem derivesOfSameFixedHeadParitySeparatorSignature
    {left right : Word Nat}
    (same : SameFixedHeadParitySeparatorSignature left right) :
    Derives targetBasis left right := by
  have countIff := headCountOne_iff same
  by_cases leftHeadSimple : left.toList.count left.head = 1
  · have rightHeadSimple :
        right.toList.count right.head = 1 :=
      countIff.mp leftHeadSimple
    have tailsEmpty : left.tail = [] ↔ right.tail = [] := by
      constructor
      · exact tailNilOfSameSignature same rightHeadSimple
      · exact tailNilOfSameSignature same.symm leftHeadSimple
    cases left with
    | mk leftHead leftTail =>
        cases right with
        | mk rightHead rightTail =>
            simp only at same leftHeadSimple rightHeadSimple tailsEmpty
            have heads : leftHead = rightHead := same.first
            subst rightHead
            cases leftTail with
            | nil =>
                have rightEmpty : rightTail = [] := tailsEmpty.mp rfl
                subst rightTail
                exact Derives.refl _
            | cons leftSecond leftRest =>
                cases rightTail with
                | nil =>
                    have impossible : leftSecond :: leftRest = [] :=
                      tailsEmpty.mpr rfl
                    contradiction
                | cons rightSecond rightRest =>
                    let leftSuffix : Word Nat :=
                      Word.mk leftSecond leftRest
                    let rightSuffix : Word Nat :=
                      Word.mk rightSecond rightRest
                    have leftHeadAbsent :
                        leftHead ∉ leftSuffix.toList := by
                      change leftHead ∉ leftSecond :: leftRest
                      exact headNotMemTailOfCountOne
                        (Word.mk leftHead (leftSecond :: leftRest))
                        leftHeadSimple
                    have rightHeadAbsent :
                        leftHead ∉ rightSuffix.toList := by
                      change leftHead ∉ rightSecond :: rightRest
                      exact headNotMemTailOfCountOne
                        (Word.mk leftHead (rightSecond :: rightRest))
                        rightHeadSimple
                    have whole :
                        SameFixedHeadParitySeparatorSignature
                          (Word.singleton leftHead ++ leftSuffix)
                          (Word.singleton leftHead ++ rightSuffix) := by
                      simpa [leftSuffix, rightSuffix, Word.singleton,
                        Word.append] using same
                    have suffixSame :=
                      suffixSameParitySeparator
                        leftHead leftSuffix rightSuffix
                        leftHeadAbsent rightHeadAbsent whole
                    have suffixDerivation :=
                      SemigroupBasis.CoRoots.S5_441.derives_of_sameParitySeparatorSignature
                        suffixSame
                    have lifted :=
                      liftS5_441UnderPrefix suffixDerivation
                        (Word.singleton leftHead) Word.singleton
                    rw [bind_singleton, bind_singleton] at lifted
                    simpa [leftSuffix, rightSuffix, Word.singleton,
                      Word.append] using lifted
  · have rightHeadNotSimple :
        right.toList.count right.head ≠ 1 := by
      intro rightSimple
      exact leftHeadSimple (countIff.mpr rightSimple)
    have leftHeadInTail : left.head ∈ left.tail :=
      headMemTailOfCountNeOne left leftHeadSimple
    have rightHeadInTail : right.head ∈ right.tail :=
      headMemTailOfCountNeOne right rightHeadNotSimple
    have leftExpanded :=
      derivesAddInitialPair left leftHeadInTail
    have rightExpanded :=
      derivesAddInitialPair right rightHeadInTail
    have commonDerivation :=
      SemigroupBasis.CoRoots.S5_441.derives_of_sameParitySeparatorSignature
        same.paritySeparator
    let guardPrefix :=
      Word.singleton left.head ++ Word.singleton left.head
    have lifted :=
      liftS5_441UnderPrefix
        commonDerivation guardPrefix Word.singleton
    rw [bind_singleton, bind_singleton] at lifted
    have guarded :
        Derives targetBasis
          (guardPrefix ++ left) (guardPrefix ++ right) := by
      simpa [guardPrefix, same.first] using lifted
    have rightContracted :
        Derives targetBasis (guardPrefix ++ right) right := by
      simpa [guardPrefix, same.first] using rightExpanded.symm
    exact leftExpanded.trans (guarded.trans rightContracted)

end SemigroupBasis.CoRoots.Order6Day7.S3_11.SeedS5_796Opposite
