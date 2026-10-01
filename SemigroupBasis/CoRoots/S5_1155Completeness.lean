import SemigroupBasis.CoRoots.S5_1155NormalizationWitness

namespace SemigroupBasis.CoRoots.S5_1155

open SemigroupBasis
open SemigroupBasis.Examples

/-- Positive-mod-three reduction assigns the same canonical multiplicity to
each letter when support and multiplicity residues agree. -/
theorem positiveModThreeReduce_count_eq_of_support_and_residue
    (left right : List Nat)
    (support : ∀ letter, letter ∈ left ↔ letter ∈ right)
    (residue :
      ∀ letter, left.count letter % 3 = right.count letter % 3)
    (letter : Nat) :
    (positiveModThreeReduce left).count letter =
      (positiveModThreeReduce right).count letter :=
  (List.perm_iff_count.mp
    (positiveModThreeReduce_perm support residue)) letter

/-- Equal support and modulo-three multiplicity profiles make two tails
derivable behind a fixed head. Both tails are fully reduced before the
resulting canonical multisets are permuted. -/
theorem derivesWordOfCons_of_tail_profile
    (head : Nat) (left right : List Nat)
    (support : ∀ letter, letter ∈ left ↔ letter ∈ right)
    (residue :
      ∀ letter, left.count letter % 3 = right.count letter % 3) :
    Derives basis (wordOfCons head left) (wordOfCons head right) := by
  have reducedPermutation :
      (positiveModThreeReduce left).Perm
        (positiveModThreeReduce right) := by
    apply List.perm_iff_count.mpr
    intro letter
    exact positiveModThreeReduce_count_eq_of_support_and_residue
      left right support residue letter
  have leftReduction :=
    derivesPositiveModThreeTail (Word.singleton head) left
  have rightReduction :=
    derivesPositiveModThreeTail (Word.singleton head) right
  have middle :=
    derivesTailPermutation (Word.singleton head) reducedPermutation
  have leftReduction' :
      Derives basis (wordOfCons head left)
        (wordOfCons head (positiveModThreeReduce left)) := by
    simpa using leftReduction
  have middle' :
      Derives basis
        (wordOfCons head (positiveModThreeReduce left))
        (wordOfCons head (positiveModThreeReduce right)) := by
    simpa using middle
  have rightReduction' :
      Derives basis (wordOfCons head right)
        (wordOfCons head (positiveModThreeReduce right)) := by
    simpa using rightReduction
  exact leftReduction'.trans <|
    middle'.trans rightReduction'.symm

/-- Symmetry of the exact semantic signature. -/
theorem sameSemanticSignature_symm
    {left right : Word Nat}
    (same : SameSemanticSignature left right) :
    SameSemanticSignature right left :=
  ⟨fun letter => (same.support letter).symm,
    fun letter =>
      (same.positiveMultiplicityModuloThree letter).symm,
    same.simpleInitial.symm⟩

/-- Transitivity of the exact semantic signature. -/
theorem sameSemanticSignature_trans
    {first second third : Word Nat}
    (firstSecond : SameSemanticSignature first second)
    (secondThird : SameSemanticSignature second third) :
    SameSemanticSignature first third :=
  ⟨fun letter =>
      (firstSecond.support letter).trans
        (secondThird.support letter),
    fun letter =>
      (firstSecond.positiveMultiplicityModuloThree letter).trans
        (secondThird.positiveMultiplicityModuloThree letter),
    firstSecond.simpleInitial.trans secondThird.simpleInitial⟩

private theorem head_mem_toList (word : Word Nat) :
    word.head ∈ word.toList := by
  cases word
  simp [Word.toList]

private theorem head_not_mem_tail_of_count_one
    (word : Word Nat)
    (countOne : word.toList.count word.head = 1) :
    word.head ∉ word.tail := by
  have countZero : word.tail.count word.head = 0 := by
    cases word with
    | mk head tail =>
        simpa [Word.toList] using countOne
  exact List.count_eq_zero.mp countZero

private theorem head_mem_tail_of_count_ge_two
    (word : Word Nat)
    (countAtLeastTwo : 2 ≤ word.toList.count word.head) :
    word.head ∈ word.tail := by
  cases word with
  | mk head tail =>
      simp only [Word.toList, List.count_cons_self] at countAtLeastTwo
      apply Decidable.byContradiction
      intro headAbsent
      have countZero : tail.count head = 0 :=
        List.count_eq_zero.mpr headAbsent
      simp [countZero] at countAtLeastTwo

private theorem tail_support_of_sameSemanticSignature
    {left right : Word Nat}
    (same : SameSemanticSignature left right)
    (heads : left.head = right.head)
    (headInTail :
      left.head ∈ left.tail ↔ right.head ∈ right.tail) :
    ∀ letter, letter ∈ left.tail ↔ letter ∈ right.tail := by
  intro letter
  by_cases isHead : letter = left.head
  · subst letter
    simpa only [heads] using headInTail
  · have isNotRightHead : letter ≠ right.head := by
      intro equal
      exact isHead (equal.trans heads.symm)
    have wholeSupport := same.support letter
    simpa [Word.toList, isHead, isNotRightHead] using wholeSupport

private theorem tail_residue_of_sameSemanticSignature
    {left right : Word Nat}
    (same : SameSemanticSignature left right)
    (heads : left.head = right.head) :
    ∀ letter,
      left.tail.count letter % 3 = right.tail.count letter % 3 := by
  intro letter
  have wholeResidue :=
    same.positiveMultiplicityModuloThree letter
  simp only [Word.toList] at wholeResidue
  by_cases isHead : letter = left.head
  · subst letter
    rw [heads] at wholeResidue ⊢
    simp only [List.count_cons_self] at wholeResidue
    omega
  · have isNotRightHead : letter ≠ right.head := by
      intro equal
      exact isHead (equal.trans heads.symm)
    rw [List.count_cons_of_ne (Ne.symm isHead),
      List.count_cons_of_ne (Ne.symm isNotRightHead)] at wholeResidue
    exact wholeResidue

/-- Once both words have the same head and agree on whether that head occurs
again, their semantic signature determines the complete tail profile and
hence a derivation. -/
theorem derives_of_sameSemanticSignature_sameHead
    {left right : Word Nat}
    (same : SameSemanticSignature left right)
    (heads : left.head = right.head)
    (headInTail :
      left.head ∈ left.tail ↔ right.head ∈ right.tail) :
    Derives basis left right := by
  have tailSupport :=
    tail_support_of_sameSemanticSignature same heads headInTail
  have tailResidue :=
    tail_residue_of_sameSemanticSignature same heads
  have tailDerivation :=
    derivesWordOfCons_of_tail_profile
      left.head left.tail right.tail tailSupport tailResidue
  have leftRebuild : wordOfCons left.head left.tail = left :=
    wordOfCons_head_tail left
  have rightRebuild : wordOfCons left.head right.tail = right := by
    rw [heads]
    exact wordOfCons_head_tail right
  simpa only [leftRebuild, rightRebuild] using tailDerivation

private theorem simple_heads_of_sameSemanticSignature
    {left right : Word Nat}
    (same : SameSemanticSignature left right)
    (leftSimple : left.toList.count left.head = 1) :
    right.toList.count right.head = 1 ∧
      left.head = right.head := by
  have leftMarker :
      simpleInitialMarker left = some left.head := by
    simp [simpleInitialMarker, leftSimple]
  have rightMarker :
      simpleInitialMarker right = some left.head :=
    same.simpleInitial.symm.trans leftMarker
  by_cases rightSimple : right.toList.count right.head = 1
  · have rightHeadEq : right.head = left.head := by
      apply Option.some.inj
      simpa [simpleInitialMarker, rightSimple] using rightMarker
    exact ⟨rightSimple, rightHeadEq.symm⟩
  · have impossible : False := by
      simpa [simpleInitialMarker, rightSimple] using rightMarker
    exact impossible.elim

private theorem right_head_not_simple_of_sameSemanticSignature
    {left right : Word Nat}
    (same : SameSemanticSignature left right)
    (leftNotSimple : left.toList.count left.head ≠ 1) :
    right.toList.count right.head ≠ 1 := by
  have leftMarker : simpleInitialMarker left = none := by
    simp [simpleInitialMarker, leftNotSimple]
  have rightMarker : simpleInitialMarker right = none :=
    same.simpleInitial.symm.trans leftMarker
  intro rightSimple
  simpa [simpleInitialMarker, rightSimple] using rightMarker

/-- The four-law system derives every pair with the same exact semantic
signature. The simple-head branch fixes the shared simple initial letter;
the repeated-head branch retargets both words to the same supported letter
before applying the canonical tail theorem. -/
theorem canonicalCompleteness :
    CanonicalCompletenessObligation repeatedHeadNormalization where
  derive left right same := by
    by_cases leftSimple : left.toList.count left.head = 1
    · obtain ⟨rightSimple, heads⟩ :=
        simple_heads_of_sameSemanticSignature same leftSimple
      have leftHeadAbsent :=
        head_not_mem_tail_of_count_one left leftSimple
      have rightHeadAbsent :=
        head_not_mem_tail_of_count_one right rightSimple
      apply derives_of_sameSemanticSignature_sameHead same heads
      exact
        ⟨fun member => (leftHeadAbsent member).elim,
          fun member => (rightHeadAbsent member).elim⟩
    · have rightNotSimple :=
        right_head_not_simple_of_sameSemanticSignature
          same leftSimple
      have leftHeadSupported : left.head ∈ left.toList :=
        head_mem_toList left
      have rightSelectedSupported : left.head ∈ right.toList :=
        (same.support left.head).mp leftHeadSupported
      have leftHeadRepeated :
          2 ≤ left.toList.count left.head := by
        have positive : 0 < left.toList.count left.head :=
          List.count_pos_iff.mpr leftHeadSupported
        omega
      have rightHeadRepeated :
          2 ≤ right.toList.count right.head := by
        have positive : 0 < right.toList.count right.head :=
          List.count_pos_iff.mpr (head_mem_toList right)
        omega
      obtain
          ⟨leftNormal, leftNormalHead, leftNormalRepeated,
            leftSameNormal, leftDerivation⟩ :=
        repeatedHeadNormalization.retarget
          left left.head leftHeadRepeated leftHeadSupported
      obtain
          ⟨rightNormal, rightNormalHead, rightNormalRepeated,
            rightSameNormal, rightDerivation⟩ :=
        repeatedHeadNormalization.retarget
          right left.head rightHeadRepeated rightSelectedSupported
      have normalSignature :
          SameSemanticSignature leftNormal rightNormal :=
        sameSemanticSignature_trans
          (sameSemanticSignature_trans
            (sameSemanticSignature_symm leftSameNormal) same)
          rightSameNormal
      have normalHeads : leftNormal.head = rightNormal.head :=
        leftNormalHead.trans rightNormalHead.symm
      have leftNormalHeadRepeated :
          2 ≤ leftNormal.toList.count leftNormal.head := by
        simpa only [leftNormalHead] using leftNormalRepeated
      have rightNormalHeadRepeated :
          2 ≤ rightNormal.toList.count rightNormal.head := by
        simpa only [rightNormalHead] using rightNormalRepeated
      have leftNormalHeadInTail :
          leftNormal.head ∈ leftNormal.tail :=
        head_mem_tail_of_count_ge_two
          leftNormal leftNormalHeadRepeated
      have rightNormalHeadInTail :
          rightNormal.head ∈ rightNormal.tail :=
        head_mem_tail_of_count_ge_two
          rightNormal rightNormalHeadRepeated
      have middle :=
        derives_of_sameSemanticSignature_sameHead
          normalSignature normalHeads
          ⟨fun _ => rightNormalHeadInTail,
            fun _ => leftNormalHeadInTail⟩
      exact leftDerivation.trans <|
        middle.trans rightDerivation.symm

end SemigroupBasis.CoRoots.S5_1155
