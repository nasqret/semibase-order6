import SemigroupBasis.CoRoots.Order6Level2TierBHash8a296208Direct
import SemigroupBasis.CoRoots.S5_378Family
import SemigroupBasis.CoRoots.S5_787Factors

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6Hash8aSiblingFixedHead

open SemigroupBasis
open SemigroupBasis.Examples

/-!
Shared completeness theorem for the six order-six classes in the
`hash8a` sibling family.  The displayed system extends the seven-law
`8a296208...` system by `xxyy = xyxy`.

The proof replays the complete `S5_378` normalizer behind a protected first
letter.  When that letter is globally simple, the separator/simple signature
is restricted to the suffix.  When it is repeated, one extra initial copy is
introduced and removed with the displayed contraction laws.
-/

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  Word.mk head tail

def xx : Word Nat := w 0 [0]
def xxx : Word Nat := w 0 [0, 0]
def xxyx : Word Nat := w 0 [0, 1, 0]
def xyx : Word Nat := w 0 [1, 0]
def xyxx : Word Nat := w 0 [1, 0, 0]
def xxyy : Word Nat := w 0 [0, 1, 1]
def xyxy : Word Nat := w 0 [1, 0, 1]
def xyyx : Word Nat := w 0 [1, 1, 0]
def xyxzy : Word Nat := w 0 [1, 0, 2, 1]
def xyyzx : Word Nat := w 0 [1, 1, 2, 0]
def xyzx : Word Nat := w 0 [1, 2, 0]
def xzyx : Word Nat := w 0 [2, 1, 0]
def xyzyz : Word Nat := w 0 [1, 2, 1, 2]
def xzyyz : Word Nat := w 0 [2, 1, 1, 2]

def powerLaw : Identity Nat := ⟨xx, xxx⟩
def leftContractionLaw : Identity Nat := ⟨xxyx, xyx⟩
def rightDuplicationLaw : Identity Nat := ⟨xyx, xyxx⟩
def crossingFinalLaw : Identity Nat := ⟨xyxy, xyyx⟩
def attachmentLaw : Identity Nat := ⟨xyxzy, xyyzx⟩
def closedInteriorSwapLaw : Identity Nat := ⟨xyzx, xzyx⟩
def guardedCrossingInitialLaw : Identity Nat := ⟨xyzyz, xzyyz⟩
def squareInterleaveLaw : Identity Nat := ⟨xxyy, xyxy⟩

/-- The exact eight-law displayed sibling basis. -/
def basis : List (Identity Nat) :=
  [powerLaw, leftContractionLaw, rightDuplicationLaw,
    crossingFinalLaw, attachmentLaw, closedInteriorSwapLaw,
    guardedCrossingInitialLaw, squareInterleaveLaw]

theorem basis_length : basis.length = 8 := by
  decide

private def instantiateThreeWords
    (first second third : Word Nat) : Nat -> Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | n + 3 => Word.singleton (n + 3)

private theorem derivesBasisSubstitution
    (identity : Identity Nat) (member : identity ∈ basis)
    (substitution : Nat -> Word Nat) :
    Derives basis
      (identity.lhs.bind substitution)
      (identity.rhs.bind substitution) :=
  Derives.subst (Derives.fromBasis member) substitution

private theorem derivesPowerExpansion (word : Word Nat) :
    Derives basis (word ++ word) ((word ++ word) ++ word) := by
  have substituted :=
    derivesBasisSubstitution powerLaw (by simp [basis])
      (instantiateThreeWords word word word)
  simpa [powerLaw, xx, xxx, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

private theorem derivesLeftContraction
    (left middle : Word Nat) :
    Derives basis
      (((left ++ left) ++ middle) ++ left)
      ((left ++ middle) ++ left) := by
  have substituted :=
    derivesBasisSubstitution leftContractionLaw (by simp [basis])
      (instantiateThreeWords left middle middle)
  simpa [leftContractionLaw, xxyx, xyx, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

private theorem derivesSquareFinalSwitch
    (left right : Word Nat) :
    Derives basis
      (((left ++ left) ++ right) ++ right)
      (((left ++ right) ++ right) ++ left) := by
  have interleave :=
    derivesBasisSubstitution squareInterleaveLaw (by simp [basis])
      (instantiateThreeWords left right right)
  have crossing :=
    derivesBasisSubstitution crossingFinalLaw (by simp [basis])
      (instantiateThreeWords left right right)
  exact (by
    simpa [squareInterleaveLaw, crossingFinalLaw, xxyy, xyxy, xyyx,
      w, instantiateThreeWords, Word.bind, Word.append, Word.singleton,
      Word.append_assoc] using interleave.trans crossing)

private theorem derivesGuardedCrossingInitial
    (guard left right : Word Nat) :
    Derives basis
      (guard ++ (((left ++ right) ++ left) ++ right))
      (guard ++ (((right ++ left) ++ left) ++ right)) := by
  have substituted :=
    derivesBasisSubstitution guardedCrossingInitialLaw
      (by simp [basis])
      (instantiateThreeWords guard left right)
  simpa [guardedCrossingInitialLaw, xyzyz, xzyyz, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

private theorem derivesGuardedSquareInitialSwitch
    (guard left right : Word Nat) :
    Derives basis
      (guard ++ (((left ++ left) ++ right) ++ right))
      (guard ++ (((right ++ left) ++ left) ++ right)) := by
  have interleave :=
    derivesBasisSubstitution squareInterleaveLaw (by simp [basis])
      (instantiateThreeWords left right right)
  have prefixed := Derives.prepend guard interleave
  have crossing := derivesGuardedCrossingInitial guard left right
  exact (by
    simpa [squareInterleaveLaw, xxyy, xyxy, w,
      instantiateThreeWords, Word.bind, Word.append, Word.singleton,
      Word.append_assoc] using prefixed.trans crossing)

private theorem bind_append
    (left right : Word Nat) (substitution : Nat -> Word Nat) :
    (left ++ right).bind substitution =
      left.bind substitution ++ right.bind substitution := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem bind_bind
    (word : Word Nat)
    (first second : Nat -> Word Nat) :
    (word.bind first).bind second =
      word.bind (fun letter => (first letter).bind second) := by
  apply Word.toList_injective
  simp [Word.toList_bind, List.flatMap_assoc]

private theorem bind_singleton (word : Word Nat) :
    word.bind Word.singleton = word := by
  apply Word.toList_injective
  simp [Word.toList_bind]

/-- Replay the complete `S5_378` normalizer behind a protected nonempty
prefix. -/
theorem liftS5_378UnderPrefix
    {left right : Word Nat}
    (derivation :
      Derives SemigroupBasis.CoRoots.S5_378.basis left right)
    (guard : Word Nat) (substitution : Nat -> Word Nat) :
    Derives basis
      (guard ++ left.bind substitution)
      (guard ++ right.bind substitution) := by
  induction derivation generalizing guard substitution with
  | fromBasis member =>
      simp only [SemigroupBasis.CoRoots.S5_378.basis,
        List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact Derives.prepend guard <|
          derivesBasisSubstitution powerLaw (by simp [basis]) substitution
      · exact Derives.prepend guard <|
          (derivesBasisSubstitution leftContractionLaw
            (by simp [basis]) substitution).symm
      · exact Derives.prepend guard <|
          derivesBasisSubstitution rightDuplicationLaw
            (by simp [basis]) substitution
      · have xxyyShape : SemigroupBasis.CoRoots.S5_378.xxyy =
            (⟨0, [0, 1, 1]⟩ : Word Nat) := by decide
        have xyxyShape : SemigroupBasis.CoRoots.S5_378.xyxy =
            (⟨0, [1, 0, 1]⟩ : Word Nat) := by decide
        simpa [SemigroupBasis.CoRoots.S5_378.squareInterleaveLaw,
          xxyyShape, xyxyShape, squareInterleaveLaw, xxyy, xyxy, w]
          using Derives.prepend guard <|
            derivesBasisSubstitution squareInterleaveLaw
              (by simp [basis]) substitution
      · have xxyyShape : SemigroupBasis.CoRoots.S5_378.xxyy =
            (⟨0, [0, 1, 1]⟩ : Word Nat) := by decide
        have xyyxShape : SemigroupBasis.CoRoots.S5_378.xyyx =
            (⟨0, [1, 1, 0]⟩ : Word Nat) := by decide
        simpa [SemigroupBasis.CoRoots.S5_378.squareFinalSwitchLaw,
          xxyyShape, xyyxShape, Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
            Derives.prepend guard
              (derivesSquareFinalSwitch
                (substitution 0) (substitution 1))
      · have xxyyShape : SemigroupBasis.CoRoots.S5_378.xxyy =
            (⟨0, [0, 1, 1]⟩ : Word Nat) := by decide
        have yxxyShape : SemigroupBasis.CoRoots.S5_378.yxxy =
            (⟨1, [0, 0, 1]⟩ : Word Nat) := by decide
        simpa [SemigroupBasis.CoRoots.S5_378.squareInitialSwitchLaw,
          xxyyShape, yxxyShape, Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
            derivesGuardedSquareInitialSwitch guard
              (substitution 0) (substitution 1)
      · exact Derives.prepend guard <|
          derivesBasisSubstitution closedInteriorSwapLaw
            (by simp [basis]) substitution
  | refl =>
      exact Derives.refl _
  | symm _ inductionHypothesis =>
      exact (inductionHypothesis guard substitution).symm
  | trans _ _ firstHypothesis secondHypothesis =>
      exact
        (firstHypothesis guard substitution).trans
          (secondHypothesis guard substitution)
  | prepend front _ inductionHypothesis =>
      simpa [bind_append, Word.append_assoc] using
        inductionHypothesis
          (guard ++ front.bind substitution) substitution
  | appendRight _ suffix inductionHypothesis =>
      simpa [bind_append, Word.append_assoc] using
        Derives.appendRight
          (inductionHypothesis guard substitution)
          (suffix.bind substitution)
  | subst _ first inductionHypothesis =>
      simpa [bind_bind] using
        inductionHypothesis guard
          (fun letter => (first letter).bind substitution)

/-! ## Fixed-head separator/simple signature -/

structure SameFixedHeadSeparatorSimpleSignature
    (left right : Word Nat) : Prop where
  separatorSimple :
    SemigroupBasis.CoRoots.S5_378.SameSeparatorSimpleSignature
      left right
  first : left.head = right.head

namespace SameFixedHeadSeparatorSimpleSignature

theorem symm {left right : Word Nat}
    (same : SameFixedHeadSeparatorSimpleSignature left right) :
    SameFixedHeadSeparatorSimpleSignature right left := by
  refine ⟨⟨?_, ?_, ?_⟩, same.first.symm⟩
  · intro letter
    exact (same.separatorSimple.support letter).symm
  · intro separator leftSupport rightSupport
    exact (same.separatorSimple.exactCuts
      separator leftSupport rightSupport).symm
  · intro letter
    exact (same.separatorSimple.globallySimple letter).symm

end SameFixedHeadSeparatorSimpleSignature

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
    {word : Word Nat} {head separator : Nat}
    {leftSupport rightSupport : List Nat}
    (headAbsent : head ∉ word.toList)
    (signature :
      SemigroupBasis.CoRoots.S5_378.ExactCutSignature
        word separator leftSupport rightSupport) :
    SemigroupBasis.CoRoots.S5_378.ExactCutSignature
      (Word.singleton head ++ word) separator
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
    {word : Word Nat} {head separator : Nat}
    {leftSupport rightSupport : List Nat}
    (headAbsent : head ∉ word.toList)
    (signature :
      SemigroupBasis.CoRoots.S5_378.ExactCutSignature
        word separator leftSupport rightSupport) :
    head ≠ separator := by
  rintro rfl
  rcases signature with ⟨left, right, cut, _, _⟩
  exact headAbsent (exactCut_separator_mem cut)

private theorem exactCutSignature_head_absent_leftSupport
    {word : Word Nat} {head separator : Nat}
    {leftSupport rightSupport : List Nat}
    (headAbsent : head ∉ word.toList)
    (signature :
      SemigroupBasis.CoRoots.S5_378.ExactCutSignature
        word separator leftSupport rightSupport) :
    head ∉ leftSupport := by
  rcases signature with
    ⟨left, right, cut, leftSupportIff, _⟩
  intro member
  exact headAbsent <|
    exactCut_left_mem cut ((leftSupportIff head).2 member)

private theorem exactCutSignature_dropFreshHead
    {word : Word Nat} {head separator : Nat}
    {leftSupport rightSupport : List Nat}
    (headAbsent : head ∉ word.toList)
    (headNeSeparator : head ≠ separator)
    (headAbsentLeftSupport : head ∉ leftSupport)
    (signature :
      SemigroupBasis.CoRoots.S5_378.ExactCutSignature
        (Word.singleton head ++ word) separator
        (head :: leftSupport) rightSupport) :
    SemigroupBasis.CoRoots.S5_378.ExactCutSignature
      word separator leftSupport rightSupport := by
  rcases signature with
    ⟨wholeLeft, right, wholeCut,
      wholeLeftSupportIff, rightSupportIff⟩
  have listCut :
      UniqueSeparatorFourExactCut
        (head :: word.toList) wholeLeft separator right := by
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

private theorem suffixSameSeparatorSimple
    (head : Nat) (left right : Word Nat)
    (headAbsentLeft : head ∉ left.toList)
    (headAbsentRight : head ∉ right.toList)
    (whole :
      SameFixedHeadSeparatorSimpleSignature
        (Word.singleton head ++ left)
        (Word.singleton head ++ right)) :
    SemigroupBasis.CoRoots.S5_378.SameSeparatorSimpleSignature
      left right := by
  refine ⟨?_, ?_, ?_⟩
  · intro letter
    by_cases equal : letter = head
    · subst letter
      simp [headAbsentLeft, headAbsentRight]
    · simpa [uniqueSeparatorWordOfCons, Word.toList,
        Word.append, Word.singleton, equal, Ne.symm equal] using
          whole.separatorSimple.support letter
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
        (whole.separatorSimple.exactCuts
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
        (whole.separatorSimple.exactCuts
          separator (head :: leftSupport) rightSupport).2
            prefixedTarget
      exact exactCutSignature_dropFreshHead
        headAbsentLeft headNeSeparator headAbsentSupport
          prefixedSource
  · intro letter
    by_cases equal : letter = head
    · subst letter
      simp only [SemigroupBasis.CoRoots.S5_378.GloballySimple]
      have leftZero : left.toList.count head = 0 :=
        List.count_eq_zero.mpr headAbsentLeft
      have rightZero : right.toList.count head = 0 :=
        List.count_eq_zero.mpr headAbsentRight
      simp [leftZero, rightZero]
    · simpa [SemigroupBasis.CoRoots.S5_378.GloballySimple,
        uniqueSeparatorWordOfCons, Word.toList, Word.append,
        Word.singleton, equal, Ne.symm equal] using
          whole.separatorSimple.globallySimple letter

private theorem headSimple_iff
    {left right : Word Nat}
    (same : SameFixedHeadSeparatorSimpleSignature left right) :
    SemigroupBasis.CoRoots.S5_378.GloballySimple left left.head ↔
      SemigroupBasis.CoRoots.S5_378.GloballySimple right right.head := by
  simpa [same.first] using
    same.separatorSimple.globallySimple left.head

private theorem headNotMemTailOfSimple
    (word : Word Nat)
    (simple :
      SemigroupBasis.CoRoots.S5_378.GloballySimple word word.head) :
    word.head ∉ word.tail := by
  intro member
  have positive : 0 < word.tail.count word.head :=
    List.count_pos_iff.mpr member
  simp only [SemigroupBasis.CoRoots.S5_378.GloballySimple,
    Word.toList, List.count_cons_self] at simple
  omega

private theorem headMemTailOfNotSimple
    (word : Word Nat)
    (notSimple :
      ¬ SemigroupBasis.CoRoots.S5_378.GloballySimple word word.head) :
    word.head ∈ word.tail := by
  apply Decidable.byContradiction
  intro absent
  apply notSimple
  cases word with
  | mk head tail =>
      simp [SemigroupBasis.CoRoots.S5_378.GloballySimple,
        Word.toList, List.count_eq_zero.mpr absent]

private theorem tailNilOfSameSignature
    {left right : Word Nat}
    (same : SameFixedHeadSeparatorSimpleSignature left right)
    (rightHeadSimple :
      SemigroupBasis.CoRoots.S5_378.GloballySimple right right.head)
    (leftTailEmpty : left.tail = []) :
    right.tail = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro letter member
  have rightMember : letter ∈ right.toList := by
    cases right
    simp [Word.toList, member]
  have leftMember : letter ∈ left.toList :=
    (same.separatorSimple.support letter).2 rightMember
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
    (headNotMemTailOfSimple right rightHeadSimple)
      rightHeadInTail

private abbrev ListDerives := S5_107.ListDerives basis

private theorem listDerivesAddInitialHead
    (head : Nat) (tail : List Nat)
    (headInTail : head ∈ tail) :
    ListDerives (head :: tail) (head :: head :: tail) := by
  rcases List.append_of_mem headInTail with
    ⟨before, after, rfl⟩
  cases before with
  | nil =>
      have expanded :=
        S5_107.ListDerives.ofWord
          (derivesPowerExpansion (Word.singleton head))
      simpa [Word.toList_append, List.append_assoc] using
        expanded.append after
  | cons middleHead middleTail =>
      let middle := S5_107.listWordOfCons middleHead middleTail
      have expanded :=
        S5_107.ListDerives.ofWord
          (derivesLeftContraction
            (Word.singleton head) middle).symm
      simpa [middle, S5_107.listWordOfCons,
        Word.toList_append, List.append_assoc] using
        expanded.append after

private theorem derivesAddInitialHead
    (word : Word Nat)
    (headInTail : word.head ∈ word.tail) :
    Derives basis word (Word.singleton word.head ++ word) := by
  cases word with
  | mk head tail =>
      have listDerivation :=
        listDerivesAddInitialHead head tail headInTail
      simpa [S5_107.listWordOfCons, Word.singleton,
        Word.append, List.append_assoc] using
        S5_107.ListDerives.toWord listDerivation

/-- Equal `S5_378` separator/simple signatures with a common first letter
are sufficient for the eight-law sibling system. -/
theorem derivesOfSameFixedHeadSeparatorSimpleSignature
    {left right : Word Nat}
    (same : SameFixedHeadSeparatorSimpleSignature left right) :
    Derives basis left right := by
  have simpleIff := headSimple_iff same
  by_cases leftHeadSimple :
      SemigroupBasis.CoRoots.S5_378.GloballySimple left left.head
  · have rightHeadSimple :
        SemigroupBasis.CoRoots.S5_378.GloballySimple right right.head :=
      simpleIff.mp leftHeadSimple
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
                      exact headNotMemTailOfSimple
                        (Word.mk leftHead (leftSecond :: leftRest))
                        leftHeadSimple
                    have rightHeadAbsent :
                        leftHead ∉ rightSuffix.toList := by
                      change leftHead ∉ rightSecond :: rightRest
                      exact headNotMemTailOfSimple
                        (Word.mk leftHead (rightSecond :: rightRest))
                        rightHeadSimple
                    have whole :
                        SameFixedHeadSeparatorSimpleSignature
                          (Word.singleton leftHead ++ leftSuffix)
                          (Word.singleton leftHead ++ rightSuffix) := by
                      simpa [leftSuffix, rightSuffix, Word.singleton,
                        Word.append] using same
                    have suffixSame :=
                      suffixSameSeparatorSimple
                        leftHead leftSuffix rightSuffix
                        leftHeadAbsent rightHeadAbsent whole
                    have suffixDerivation :=
                      SemigroupBasis.CoRoots.S5_378.derivesOfSameSignature
                        suffixSame
                    have lifted :=
                      liftS5_378UnderPrefix suffixDerivation
                        (Word.singleton leftHead) Word.singleton
                    rw [bind_singleton, bind_singleton] at lifted
                    simpa [leftSuffix, rightSuffix, Word.singleton,
                      Word.append] using lifted
  · have rightHeadNotSimple :
        ¬ SemigroupBasis.CoRoots.S5_378.GloballySimple
          right right.head := by
      intro rightSimple
      exact leftHeadSimple (simpleIff.mpr rightSimple)
    have leftHeadInTail : left.head ∈ left.tail :=
      headMemTailOfNotSimple left leftHeadSimple
    have rightHeadInTail : right.head ∈ right.tail :=
      headMemTailOfNotSimple right rightHeadNotSimple
    have leftExpanded :=
      derivesAddInitialHead left leftHeadInTail
    have rightExpanded :=
      derivesAddInitialHead right rightHeadInTail
    have commonDerivation :=
      SemigroupBasis.CoRoots.S5_378.derivesOfSameSignature
        same.separatorSimple
    have lifted :=
      liftS5_378UnderPrefix commonDerivation
        (Word.singleton left.head) Word.singleton
    rw [bind_singleton, bind_singleton] at lifted
    have guarded :
        Derives basis
          (Word.singleton left.head ++ left)
          (Word.singleton right.head ++ right) := by
      simpa [same.first] using lifted
    exact leftExpanded.trans <| guarded.trans rightExpanded.symm

/-- A target carrying semantic `S5_378` and left-zero detectors has the
eight-law sibling basis.  Target-specific subdirect maps are supplied by the
generated endpoint modules. -/
theorem basisForOfS5_378AndHeadDetectors
    {S : Type u} (target : Semigroup S)
    (targetModels : Models target basis)
    (s5_378Detector : ∀ identity : Identity Nat,
      identity.SatisfiedBy target →
        identity.SatisfiedBy
          SemigroupBasis.CoRoots.S5_378.table.semigroup)
    (headDetector : ∀ identity : Identity Nat,
      identity.SatisfiedBy target →
        identity.SatisfiedBy leftZeroTwo.semigroup) :
    BasisFor target basis := by
  refine ⟨targetModels, ?_⟩
  intro identity valid
  exact derivesOfSameFixedHeadSeparatorSimpleSignature
    ⟨SemigroupBasis.CoRoots.S5_378.valid_sameSignature
        identity (s5_378Detector identity valid),
      S5_790Invariant.leftZeroValid_head_eq
        identity (headDetector identity valid)⟩

/-! ## Direct factor intersections -/

private def toFinThree : Nat -> Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

private theorem modelsS2_4 :
    Models SemigroupBasis.Generated.S2_4.table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.S2_4.table basis toFinThree (by decide)

private theorem modelsS3_15 :
    Models SemigroupBasis.Generated.S3_15.table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.S3_15.table basis toFinThree (by decide)

private theorem modelsS5_378 :
    Models SemigroupBasis.CoRoots.S5_378.table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.CoRoots.S5_378.table basis toFinThree (by decide)

private theorem modelsS3_8 :
    Models SemigroupBasis.Generated.S3_8.table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.S3_8.table basis toFinThree (by decide)

private theorem modelsS5_787 :
    Models
      SemigroupBasis.Generated.Catalogue.S5_787.table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.Catalogue.S5_787.table
    basis toFinThree (by decide)

private theorem modelsS5_789 :
    Models
      SemigroupBasis.Generated.Catalogue.S5_789.table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.Catalogue.S5_789.table
    basis toFinThree (by decide)

private theorem modelsS5_796 :
    Models
      SemigroupBasis.Generated.Catalogue.S5_796.table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.Catalogue.S5_796.table
    basis toFinThree (by decide)

private theorem head_eq_of_s2_4_valid
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S2_4.table.semigroup) :
    identity.lhs.head = identity.rhs.head := by
  have markerValid :
      identity.SatisfiedBy leftZeroTwo.semigroup := by
    simpa [SemigroupBasis.Generated.S2_4.table_eq_catalogue_model] using
      valid
  exact S5_790Invariant.leftZeroValid_head_eq identity markerValid

private theorem head_eq_of_s3_15_valid
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S3_15.table.semigroup) :
    identity.lhs.head = identity.rhs.head := by
  change identity.SatisfiedBy leftNormalBandFifteen.semigroup at valid
  exact leftNormalBandFifteenValid_head_eq identity valid

theorem derivesOfS2_4S5_378Valid
    (identity : Identity Nat)
    (headValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S2_4.table.semigroup)
    (signatureValid :
      identity.SatisfiedBy
        SemigroupBasis.CoRoots.S5_378.table.semigroup) :
    Derives basis identity.lhs identity.rhs :=
  derivesOfSameFixedHeadSeparatorSimpleSignature
    ⟨SemigroupBasis.CoRoots.S5_378.valid_sameSignature
        identity signatureValid,
      head_eq_of_s2_4_valid identity headValid⟩

theorem derivesOfS3_15S5_378Valid
    (identity : Identity Nat)
    (headValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S3_15.table.semigroup)
    (signatureValid :
      identity.SatisfiedBy
        SemigroupBasis.CoRoots.S5_378.table.semigroup) :
    Derives basis identity.lhs identity.rhs :=
  derivesOfSameFixedHeadSeparatorSimpleSignature
    ⟨SemigroupBasis.CoRoots.S5_378.valid_sameSignature
        identity signatureValid,
      head_eq_of_s3_15_valid identity headValid⟩

private theorem direct_s4_69_valid_of_catalogue
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S4_69.table.semigroup) :
    identity.SatisfiedBy
      SemigroupBasis.Generated.S4_69.table.semigroup := by
  rw [SemigroupBasis.Generated.S4_69.table_eq_canonical_catalogue]
  exact valid

private theorem direct_s2_4_table_eq_catalogue :
    SemigroupBasis.Generated.S2_4.table =
      SemigroupBasis.Generated.Catalogue.S2_4.table := by
  unfold SemigroupBasis.Generated.S2_4.table
    SemigroupBasis.Generated.Catalogue.S2_4.table
    SemigroupBasis.Generated.Catalogue.S2_4.mul
  rw [FiniteTable.mk.injEq]
  refine ⟨rfl, heq_of_eq ?_⟩
  funext a b
  decide +revert

private theorem direct_s2_4_valid_of_catalogue
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S2_4.table.semigroup) :
    identity.SatisfiedBy
      SemigroupBasis.Generated.S2_4.table.semigroup := by
  rw [direct_s2_4_table_eq_catalogue]
  exact valid

private theorem direct_s3_15_valid_of_catalogue
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S3_15.table.semigroup) :
    identity.SatisfiedBy
      SemigroupBasis.Generated.S3_15.table.semigroup := by
  rw [SemigroupBasis.Generated.S3_15.table_eq_canonical_catalogue]
  exact valid

theorem derivesOfS3_8S5_787Valid
    (identity : Identity Nat)
    (multiplicityValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S3_8.table.semigroup)
    (rightValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_787.table.semigroup) :
    Derives basis identity.lhs identity.rhs := by
  have separatorValid :=
    direct_s4_69_valid_of_catalogue identity <|
      S5_787Factors.S5_787.valid_s4_69 identity rightValid
  have headValid :=
    direct_s2_4_valid_of_catalogue identity <|
      S5_787Factors.S5_787.valid_s2_4 identity rightValid
  exact derivesOfSameFixedHeadSeparatorSimpleSignature
    ⟨SemigroupBasis.CoRoots.S5_378.sameSignature_of_factors
        identity separatorValid multiplicityValid,
      head_eq_of_s2_4_valid identity headValid⟩

theorem derivesOfS3_8S5_789Valid
    (identity : Identity Nat)
    (multiplicityValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S3_8.table.semigroup)
    (rightValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_789.table.semigroup) :
    Derives basis identity.lhs identity.rhs := by
  have separatorValid :=
    direct_s4_69_valid_of_catalogue identity <|
      S5_787Factors.S5_789.valid_s4_69 identity rightValid
  have headValid :=
    direct_s2_4_valid_of_catalogue identity <|
      S5_787Factors.S5_789.valid_s2_4 identity rightValid
  exact derivesOfSameFixedHeadSeparatorSimpleSignature
    ⟨SemigroupBasis.CoRoots.S5_378.sameSignature_of_factors
        identity separatorValid multiplicityValid,
      head_eq_of_s2_4_valid identity headValid⟩

theorem derivesOfS3_8S5_796Valid
    (identity : Identity Nat)
    (multiplicityValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S3_8.table.semigroup)
    (rightValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_796.table.semigroup) :
    Derives basis identity.lhs identity.rhs := by
  have separatorValid :=
    direct_s4_69_valid_of_catalogue identity <|
      S5_787Factors.S5_796.valid_s4_69 identity rightValid
  have headValid :=
    direct_s3_15_valid_of_catalogue identity <|
      S5_787Factors.S5_796.valid_s3_15 identity rightValid
  exact derivesOfSameFixedHeadSeparatorSimpleSignature
    ⟨SemigroupBasis.CoRoots.S5_378.sameSignature_of_factors
        identity separatorValid multiplicityValid,
      head_eq_of_s3_15_valid identity headValid⟩

def intersectionBasisS2_4S5_378 :
    IntersectionBasis
      SemigroupBasis.Generated.S2_4.table.semigroup
      SemigroupBasis.CoRoots.S5_378.table.semigroup
      basis where
  leftModels := modelsS2_4
  rightModels := modelsS5_378
  complete := derivesOfS2_4S5_378Valid

def intersectionBasisS3_15S5_378 :
    IntersectionBasis
      SemigroupBasis.Generated.S3_15.table.semigroup
      SemigroupBasis.CoRoots.S5_378.table.semigroup
      basis where
  leftModels := modelsS3_15
  rightModels := modelsS5_378
  complete := derivesOfS3_15S5_378Valid

def intersectionBasisS3_8S5_787 :
    IntersectionBasis
      SemigroupBasis.Generated.S3_8.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_787.table.semigroup
      basis where
  leftModels := modelsS3_8
  rightModels := modelsS5_787
  complete := derivesOfS3_8S5_787Valid

def intersectionBasisS3_8S5_789 :
    IntersectionBasis
      SemigroupBasis.Generated.S3_8.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_789.table.semigroup
      basis where
  leftModels := modelsS3_8
  rightModels := modelsS5_789
  complete := derivesOfS3_8S5_789Valid

def intersectionBasisS3_8S5_796 :
    IntersectionBasis
      SemigroupBasis.Generated.S3_8.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_796.table.semigroup
      basis where
  leftModels := modelsS3_8
  rightModels := modelsS5_796
  complete := derivesOfS3_8S5_796Valid

end SemigroupBasis.CoRoots.Order6Hash8aSiblingFixedHead
