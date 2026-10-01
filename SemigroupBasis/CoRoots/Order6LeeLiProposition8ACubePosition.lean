import SemigroupBasis.CoRoots.Order6LeeLiProposition8ACanonicalization

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6LeeLiProposition8A

open SemigroupBasis

namespace CubePosition

private abbrev ListDerives : List Nat → List Nat → Prop :=
  S5_107.ListDerives basis

private abbrev listWordOfCons :=
  S5_107.listWordOfCons

private theorem existsFirstOccurrenceSplit
    (letter : Nat) :
    ∀ {letters : List Nat},
      letter ∈ letters →
      ∃ before after,
        letters = before ++ letter :: after ∧ letter ∉ before
  | [], member => by simp at member
  | first :: rest, member => by
      by_cases equality : first = letter
      · subst first
        exact ⟨[], rest, by simp⟩
      · have restMember : letter ∈ rest := by
          simpa [equality, Ne.symm equality] using member
        obtain ⟨before, after, shape, absent⟩ :=
          existsFirstOccurrenceSplit letter restMember
        exact ⟨first :: before, after, by simp [shape], by
          simp [equality, Ne.symm equality, absent]⟩

private theorem firstOccurrenceSplit_unique
    (letter : Nat) :
    ∀ (firstBefore firstAfter secondBefore secondAfter : List Nat),
      letter ∉ firstBefore →
      letter ∉ secondBefore →
      firstBefore ++ letter :: firstAfter =
        secondBefore ++ letter :: secondAfter →
      firstBefore = secondBefore ∧ firstAfter = secondAfter
  | [], firstAfter, [], secondAfter, _, _, shape => by
      simp only [List.nil_append] at shape
      exact ⟨rfl, (List.cons.inj shape).2⟩
  | [], _, second :: secondRest, _, _, secondAbsent, shape => by
      simp only [List.nil_append, List.cons_append] at shape
      injection shape with headEq tailEq
      subst second
      exact False.elim (secondAbsent (List.Mem.head secondRest))
  | first :: firstRest, _, [], _, firstAbsent, _, shape => by
      simp only [List.nil_append, List.cons_append] at shape
      injection shape with headEq tailEq
      subst first
      exact False.elim (firstAbsent (List.Mem.head firstRest))
  | first :: firstRest, firstAfter,
      second :: secondRest, secondAfter,
      firstAbsent, secondAbsent, shape => by
      simp only [List.cons_append] at shape
      injection shape with headEq tailEq
      subst second
      have firstRestAbsent : letter ∉ firstRest :=
        fun member => firstAbsent (List.Mem.tail first member)
      have secondRestAbsent : letter ∉ secondRest :=
        fun member => secondAbsent (List.Mem.tail first member)
      obtain ⟨prefixEq, suffixEq⟩ :=
        firstOccurrenceSplit_unique letter firstRest firstAfter
          secondRest secondAfter firstRestAbsent secondRestAbsent tailEq
      exact ⟨by simp [prefixEq], suffixEq⟩

/-- Condition V, named independently of the eventual canonical structure so
the positioning pass can state its own terminating driver. -/
def CubesTerminalOrBeforeFirst (letters : List Nat) : Prop :=
  ∀ letter before after,
    letters = before ++ [letter, letter, letter] ++ after →
      after = [] ∨
        ∃ next rest,
          after = next :: rest ∧
          next ∉ before ++ [letter, letter, letter]

/-- Condition VI for literal adjacent cube blocks. -/
def AdjacentCubesOrdered (letters : List Nat) : Prop :=
  ∀ left right before after,
    left ≠ right →
    letters = before ++ [left, left, left] ++
      [right, right, right] ++ after →
    left < right

/-- Assemble the existing public canonical structure from the four
independently normalized conditions. -/
theorem proposition8ACanonical_of_components
    {letters : List Nat}
    (capThree : ∀ tested, letters.count tested ≤ 3)
    (cubes : TripleCubesContiguous letters)
    (positioned : CubesTerminalOrBeforeFirst letters)
    (ordered : AdjacentCubesOrdered letters) :
    Proposition8ACanonical letters where
  capThree := capThree
  cubeContiguous := cubes
  cubeTerminalOrBeforeFirst := positioned
  adjacentCubesOrdered := ordered

/-!
# Positioning and ordering contiguous cubes

This module isolates the literal Proposition 8 moves used after the
cap-three/condition-IV pass.  Laws 4 and 9 move a repeated letter from just
after a cube to just before it.  Law 8 interchanges two adjacent cubes.

The `cubicSuffixDebt` certificate below is relative to a fixed reference
list.  Every occurrence of a reference letter of multiplicity three is
charged by the length of its remaining suffix.  Moving one such cube one
place to the right across a noncubic letter lowers the debt by exactly three.
-/

private def instantiateFourWords
    (x h y t : Word Nat) : Nat → Word Nat
  | 0 => x
  | 1 => h
  | 2 => y
  | 3 => t
  | n + 4 => Word.singleton (n + 4)

private theorem basisCubeMoveGeneral :
    Derives basis xhxyyy xhyyyx :=
  Derives.fromBasis (e := cubeMoveGeneralLaw) (by simp [basis])

private theorem basisCubeMoveFinalGapEmpty :
    Derives basis xxyyy xyyyx :=
  Derives.fromBasis (e := cubeMoveFinalGapEmptyLaw) (by simp [basis])

private theorem basisCubeInterchange :
    Derives basis xxxyyy yyyxxx :=
  Derives.fromBasis (e := cubeInterchangeLaw) (by simp [basis])

private theorem derivesMoveRepeatedFollowerGeneral
    (repeated gap cube : Word Nat) :
    Derives basis
      (((((repeated ++ gap) ++ cube) ++ cube) ++ cube) ++ repeated)
      (((((repeated ++ gap) ++ repeated) ++ cube) ++ cube) ++ cube) := by
  have substituted :=
    Derives.subst basisCubeMoveGeneral
      (instantiateFourWords repeated gap cube cube)
  simpa [xhxyyy, xhyyyx, w, instantiateFourWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted.symm

private theorem derivesMoveRepeatedFollowerFinalGapEmpty
    (repeated cube : Word Nat) :
    Derives basis
      ((((repeated ++ cube) ++ cube) ++ cube) ++ repeated)
      ((((repeated ++ repeated) ++ cube) ++ cube) ++ cube) := by
  have substituted :=
    Derives.subst basisCubeMoveFinalGapEmpty
      (instantiateFourWords repeated repeated cube cube)
  simpa [xxyyy, xyyyx, w, instantiateFourWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted.symm

private theorem derivesInterchangeCubes
    (left right : Word Nat) :
    Derives basis
      (((((left ++ left) ++ left) ++ right) ++ right) ++ right)
      (((((right ++ right) ++ right) ++ left) ++ left) ++ left) := by
  have substituted :=
    Derives.subst basisCubeInterchange
      (instantiateFourWords left left right right)
  simpa [xxxyyy, yyyxxx, w, instantiateFourWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-! ## Extracting a literal condition-V obstruction -/

/-- The condition-V obstruction can be chosen at the first earlier
occurrence of the letter following the displayed cube.  The absent-front
certificate is what makes condition-IV preservation local. -/
theorem existsConditionVBadConfigurationFirst
    {letters : List Nat}
    (bounded : ∀ tested, letters.count tested ≤ 3)
    (notPositioned : ¬ CubesTerminalOrBeforeFirst letters) :
    ∃ cube repeated before middle after,
      cube ≠ repeated ∧
      repeated ∉ before ∧
      letters.count cube = 3 ∧
      letters = before ++ [repeated] ++ middle ++
        [cube, cube, cube, repeated] ++ after := by
  classical
  apply Classical.byContradiction
  intro noConfiguration
  apply notPositioned
  intro cube cubeBefore cubeAfter shape
  cases cubeAfter with
  | nil =>
      exact Or.inl rfl
  | cons repeated rest =>
      apply Or.inr
      refine ⟨repeated, rest, rfl, ?_⟩
      intro seen
      have different : cube ≠ repeated := by
        intro equality
        subst repeated
        have countBound := bounded cube
        rw [shape] at countBound
        simp only [List.count_append, List.count_cons_self,
          List.count_nil] at countBound
        omega
      have repeatedBefore : repeated ∈ cubeBefore := by
        simpa [different, Ne.symm different] using seen
      obtain ⟨before, middle, beforeShape, repeatedAbsent⟩ :=
        existsFirstOccurrenceSplit repeated repeatedBefore
      have cubeThree : letters.count cube = 3 := by
        have countLower : 3 ≤ letters.count cube := by
          rw [shape]
          simp only [List.count_append, List.count_cons_self,
            List.count_nil]
          omega
        exact Nat.le_antisymm (bounded cube) countLower
      apply noConfiguration
      refine ⟨cube, repeated, before, middle, rest,
        different, repeatedAbsent, cubeThree, ?_⟩
      rw [shape, beforeShape]
      simp [List.append_assoc]

/-- Failure of condition V in a cap-three list exposes exactly the pattern
consumed by laws 4 and 9: an earlier copy of the letter immediately following
the displayed cube. -/
theorem existsConditionVBadConfiguration
    {letters : List Nat}
    (bounded : ∀ tested, letters.count tested ≤ 3)
    (notPositioned : ¬ CubesTerminalOrBeforeFirst letters) :
    ∃ cube repeated before middle after,
      cube ≠ repeated ∧
      letters.count cube = 3 ∧
      letters = before ++ [repeated] ++ middle ++
        [cube, cube, cube, repeated] ++ after := by
  obtain ⟨cube, repeated, before, middle, after, different,
      _repeatedAbsent, cubeThree, shape⟩ :=
    existsConditionVBadConfigurationFirst bounded notPositioned
  exact ⟨cube, repeated, before, middle, after, different,
    cubeThree, shape⟩

private theorem cubeTail_ne_separatedFollower
    (cube repeated : Nat) (middle cubeAfter after : List Nat)
    (different : cube ≠ repeated)
    (cubeAfterAbsent : repeated ∉ cubeAfter) :
    repeated :: repeated :: cubeAfter ≠
      middle ++ [cube, cube, cube, repeated] ++ after := by
  intro impossible
  cases middle with
  | nil =>
      simp only [List.nil_append] at impossible
      injection impossible with equality
      exact different equality.symm
  | cons first rest =>
      simp only [List.cons_append] at impossible
      injection impossible with firstEq tailEq
      subst first
      cases rest with
      | nil =>
          simp only [List.nil_append] at tailEq
          injection tailEq with equality
          exact different equality.symm
      | cons second tail =>
          simp only [List.cons_append] at tailEq
          injection tailEq with secondEq remainingEq
          subst second
          apply cubeAfterAbsent
          rw [remainingEq]
          simp

/-- In a condition-IV obstruction chosen at the first earlier occurrence,
the crossed letter cannot itself have multiplicity three. -/
theorem repeatedCount_ne_three_of_conditionVBadConfiguration
    {letters : List Nat}
    (cubes : TripleCubesContiguous letters)
    (cube repeated : Nat) (before middle after : List Nat)
    (different : cube ≠ repeated)
    (repeatedAbsent : repeated ∉ before)
    (shape :
      letters = before ++ [repeated] ++ middle ++
        [cube, cube, cube, repeated] ++ after) :
    letters.count repeated ≠ 3 := by
  intro repeatedThree
  obtain ⟨cubeBefore, cubeAfter, cubeShape⟩ :=
    cubes repeated repeatedThree
  have countEquation := repeatedThree
  rw [cubeShape] at countEquation
  simp only [List.count_append, List.count_cons_self,
    List.count_nil] at countEquation
  have cubeBeforeZero : cubeBefore.count repeated = 0 := by omega
  have cubeAfterZero : cubeAfter.count repeated = 0 := by omega
  have cubeBeforeAbsent : repeated ∉ cubeBefore :=
    List.count_eq_zero.mp cubeBeforeZero
  have cubeAfterAbsent : repeated ∉ cubeAfter :=
    List.count_eq_zero.mp cubeAfterZero
  have firstShape :
      letters = before ++ repeated ::
        (middle ++ [cube, cube, cube, repeated] ++ after) := by
    simpa [List.append_assoc] using shape
  have cubeFirstShape :
      letters = cubeBefore ++ repeated ::
        (repeated :: repeated :: cubeAfter) := by
    simpa [List.append_assoc] using cubeShape
  obtain ⟨_prefixEq, suffixEq⟩ :=
    firstOccurrenceSplit_unique repeated before
      (middle ++ [cube, cube, cube, repeated] ++ after)
      cubeBefore (repeated :: repeated :: cubeAfter)
      repeatedAbsent cubeBeforeAbsent
      (firstShape.symm.trans cubeFirstShape)
  exact cubeTail_ne_separatedFollower cube repeated middle cubeAfter after
    different cubeAfterAbsent suffixEq.symm

private theorem tripleCubePersistsAcrossFollowerMove
    (cube repeated tested : Nat) (front after : List Nat)
    (testedNeCube : tested ≠ cube)
    (testedNeRepeated : tested ≠ repeated)
    (cubes :
      TripleCubesContiguous
        (front ++ [cube, cube, cube, repeated] ++ after))
    (testedThree :
      (front ++ [cube, cube, cube, repeated] ++ after).count tested =
        3) :
    ∃ cubeBefore cubeAfter,
      front ++ [repeated, cube, cube, cube] ++ after =
        cubeBefore ++ [tested, tested, tested] ++ cubeAfter := by
  classical
  obtain ⟨displayedBefore, displayedAfter, displayedShape⟩ :=
    cubes tested testedThree
  have countEquation := testedThree
  rw [displayedShape] at countEquation
  simp only [List.count_append, List.count_cons_self,
    List.count_nil] at countEquation
  have displayedBeforeZero : displayedBefore.count tested = 0 := by
    omega
  have displayedAfterZero : displayedAfter.count tested = 0 := by
    omega
  have displayedBeforeAbsent : tested ∉ displayedBefore :=
    List.count_eq_zero.mp displayedBeforeZero
  by_cases testedInPrefix : tested ∈ front
  · obtain ⟨firstBefore, firstAfter, prefixShape, firstAbsent⟩ :=
      existsFirstOccurrenceSplit tested testedInPrefix
    have sourceFirstShape :
        front ++ [cube, cube, cube, repeated] ++ after =
          firstBefore ++ tested ::
            (firstAfter ++ [cube, cube, cube, repeated] ++ after) := by
      rw [prefixShape]
      simp [List.append_assoc]
    have displayedFirstShape :
        front ++ [cube, cube, cube, repeated] ++ after =
          displayedBefore ++ tested ::
            (tested :: tested :: displayedAfter) := by
      simpa [List.append_assoc] using displayedShape
    obtain ⟨_prefixEq, suffixEq⟩ :=
      firstOccurrenceSplit_unique tested firstBefore
        (firstAfter ++ [cube, cube, cube, repeated] ++ after)
        displayedBefore (tested :: tested :: displayedAfter)
        firstAbsent displayedBeforeAbsent
        (sourceFirstShape.symm.trans displayedFirstShape)
    cases firstAfter with
    | nil =>
        simp only [List.nil_append] at suffixEq
        injection suffixEq with equality
        exact False.elim (testedNeCube equality.symm)
    | cons first rest =>
        simp only [List.cons_append] at suffixEq
        injection suffixEq with firstEq tailEq
        subst first
        cases rest with
        | nil =>
            simp only [List.nil_append] at tailEq
            injection tailEq with equality
            exact False.elim (testedNeCube equality.symm)
        | cons second tail =>
            simp only [List.cons_append] at tailEq
            injection tailEq with secondEq remainingEq
            subst second
            refine ⟨firstBefore,
              tail ++ [repeated, cube, cube, cube] ++ after, ?_⟩
            rw [prefixShape]
            simp [List.append_assoc]
  · have prefixZero : front.count tested = 0 :=
      List.count_eq_zero.mpr testedInPrefix
    have afterThree : after.count tested = 3 := by
      simpa [List.count_append, prefixZero, testedNeCube,
        Ne.symm testedNeCube, testedNeRepeated,
        Ne.symm testedNeRepeated] using testedThree
    have afterMember : tested ∈ after :=
      List.count_pos_iff.mp (by omega : 0 < after.count tested)
    obtain ⟨afterBefore, afterRest, afterShape, afterBeforeAbsent⟩ :=
      existsFirstOccurrenceSplit tested afterMember
    have sourceBeforeAbsent :
        tested ∉ front ++ [cube, cube, cube, repeated] ++
          afterBefore := by
      simp [testedInPrefix, testedNeCube, Ne.symm testedNeCube,
        testedNeRepeated, Ne.symm testedNeRepeated,
        afterBeforeAbsent]
    have sourceAfterFirstShape :
        front ++ [cube, cube, cube, repeated] ++ after =
          (front ++ [cube, cube, cube, repeated] ++ afterBefore) ++
            tested :: afterRest := by
      rw [afterShape]
      simp [List.append_assoc]
    have displayedFirstShape :
        front ++ [cube, cube, cube, repeated] ++ after =
          displayedBefore ++ tested ::
            (tested :: tested :: displayedAfter) := by
      simpa [List.append_assoc] using displayedShape
    obtain ⟨_prefixEq, suffixEq⟩ :=
      firstOccurrenceSplit_unique tested displayedBefore
        (tested :: tested :: displayedAfter)
        (front ++ [cube, cube, cube, repeated] ++ afterBefore)
        afterRest displayedBeforeAbsent sourceBeforeAbsent
        (displayedFirstShape.symm.trans sourceAfterFirstShape)
    refine ⟨front ++ [repeated, cube, cube, cube] ++ afterBefore,
      displayedAfter, ?_⟩
    rw [afterShape, ← suffixEq]
    simp [List.append_assoc]

private theorem tripleCubeLocatedOutsideAvoidingBlock
    (tested barrier : Nat) (front sourceTail after : List Nat)
    (testedNeBarrier : tested ≠ barrier)
    (sourceTailAbsent : tested ∉ sourceTail)
    (cubes :
      TripleCubesContiguous
        (front ++ barrier :: sourceTail ++ after))
    (testedThree :
      (front ++ barrier :: sourceTail ++ after).count tested = 3) :
    (∃ cubeBefore cubeAfter,
      front = cubeBefore ++ [tested, tested, tested] ++ cubeAfter) ∨
    ∃ cubeBefore cubeAfter,
      after = cubeBefore ++ [tested, tested, tested] ++ cubeAfter := by
  classical
  obtain ⟨displayedBefore, displayedAfter, displayedShape⟩ :=
    cubes tested testedThree
  have countEquation := testedThree
  rw [displayedShape] at countEquation
  simp only [List.count_append, List.count_cons_self,
    List.count_nil] at countEquation
  have displayedBeforeZero : displayedBefore.count tested = 0 := by
    omega
  have displayedBeforeAbsent : tested ∉ displayedBefore :=
    List.count_eq_zero.mp displayedBeforeZero
  by_cases testedInPrefix : tested ∈ front
  · obtain ⟨firstBefore, firstAfter, prefixShape, firstAbsent⟩ :=
      existsFirstOccurrenceSplit tested testedInPrefix
    have sourceFirstShape :
        front ++ barrier :: sourceTail ++ after =
          firstBefore ++ tested ::
            (firstAfter ++ barrier :: sourceTail ++ after) := by
      rw [prefixShape]
      simp [List.append_assoc]
    have displayedFirstShape :
        front ++ barrier :: sourceTail ++ after =
          displayedBefore ++ tested ::
            (tested :: tested :: displayedAfter) := by
      simpa [List.append_assoc] using displayedShape
    obtain ⟨_prefixEq, suffixEq⟩ :=
      firstOccurrenceSplit_unique tested firstBefore
        (firstAfter ++ barrier :: sourceTail ++ after)
        displayedBefore (tested :: tested :: displayedAfter)
        firstAbsent displayedBeforeAbsent
        (sourceFirstShape.symm.trans displayedFirstShape)
    cases firstAfter with
    | nil =>
        simp only [List.nil_append] at suffixEq
        injection suffixEq with equality
        exact False.elim (testedNeBarrier equality.symm)
    | cons first rest =>
        simp only [List.cons_append] at suffixEq
        injection suffixEq with firstEq tailEq
        subst first
        cases rest with
        | nil =>
            simp only [List.nil_append] at tailEq
            injection tailEq with equality
            exact False.elim (testedNeBarrier equality.symm)
        | cons second tail =>
            simp only [List.cons_append] at tailEq
            injection tailEq with secondEq remainingEq
            subst second
            exact Or.inl ⟨firstBefore, tail, by
              simpa [List.append_assoc] using prefixShape⟩
  · have prefixZero : front.count tested = 0 :=
      List.count_eq_zero.mpr testedInPrefix
    have sourceTailZero : sourceTail.count tested = 0 :=
      List.count_eq_zero.mpr sourceTailAbsent
    have afterThree : after.count tested = 3 := by
      simpa [List.count_append, prefixZero, sourceTailZero,
        testedNeBarrier, Ne.symm testedNeBarrier] using testedThree
    have afterMember : tested ∈ after :=
      List.count_pos_iff.mp (by omega : 0 < after.count tested)
    obtain ⟨afterBefore, afterRest, afterShape, afterBeforeAbsent⟩ :=
      existsFirstOccurrenceSplit tested afterMember
    have sourceBeforeAbsent :
        tested ∉ front ++ barrier :: sourceTail ++ afterBefore := by
      simp [testedInPrefix, testedNeBarrier, Ne.symm testedNeBarrier,
        sourceTailAbsent, afterBeforeAbsent]
    have sourceAfterFirstShape :
        front ++ barrier :: sourceTail ++ after =
          (front ++ barrier :: sourceTail ++ afterBefore) ++
            tested :: afterRest := by
      rw [afterShape]
      simp [List.append_assoc]
    have displayedFirstShape :
        front ++ barrier :: sourceTail ++ after =
          displayedBefore ++ tested ::
            (tested :: tested :: displayedAfter) := by
      simpa [List.append_assoc] using displayedShape
    obtain ⟨_prefixEq, suffixEq⟩ :=
      firstOccurrenceSplit_unique tested displayedBefore
        (tested :: tested :: displayedAfter)
        (front ++ barrier :: sourceTail ++ afterBefore)
        afterRest displayedBeforeAbsent sourceBeforeAbsent
        (displayedFirstShape.symm.trans sourceAfterFirstShape)
    exact Or.inr ⟨afterBefore, displayedAfter, by
      rw [afterShape, ← suffixEq]
      simp [List.append_assoc]⟩

/-! ## Literal list-level moves -/

/-- Laws 4 and 9, in the direction used by condition V.  The displayed
`repeated` before the cube witnesses that its copy immediately following the
cube is not a first occurrence. -/
theorem listDerivesMoveRepeatedFollowerBeforeCube
    (cube repeated : Nat)
    (before middle after : List Nat) :
    ListDerives
      (before ++ [repeated] ++ middle ++
        [cube, cube, cube, repeated] ++ after)
      (before ++ [repeated] ++ middle ++
        [repeated, cube, cube, cube] ++ after) := by
  cases middle with
  | nil =>
      have moved := S5_107.ListDerives.ofWord
        (derivesMoveRepeatedFollowerFinalGapEmpty
          (Word.singleton repeated) (Word.singleton cube))
      simpa [listWordOfCons, Word.singleton, Word.append,
        Word.append_assoc, List.append_assoc] using
          S5_107.ListDerives.context before after moved
  | cons middleHead middleTail =>
      let middleWord := listWordOfCons middleHead middleTail
      have moved := S5_107.ListDerives.ofWord
        (derivesMoveRepeatedFollowerGeneral
          (Word.singleton repeated) middleWord (Word.singleton cube))
      simpa [middleWord, listWordOfCons, Word.singleton, Word.append,
        Word.append_assoc, List.append_assoc] using
          S5_107.ListDerives.context before after moved

/-- Law 8 interchanges two literal adjacent cubes in arbitrary context. -/
theorem listDerivesInterchangeAdjacentCubes
    (left right : Nat) (before after : List Nat) :
    ListDerives
      (before ++ [left, left, left, right, right, right] ++ after)
      (before ++ [right, right, right, left, left, left] ++ after) := by
  have interchanged := S5_107.ListDerives.ofWord
    (derivesInterchangeCubes
      (Word.singleton left) (Word.singleton right))
  simpa [listWordOfCons, Word.singleton, Word.append,
    Word.append_assoc, List.append_assoc] using
      S5_107.ListDerives.context before after interchanged

/-! ## Exact multiplicity certificates -/

/-- The condition-V move is a literal permutation. -/
theorem moveRepeatedFollowerBeforeCube_perm
    (cube repeated : Nat)
    (before middle after : List Nat) :
    (before ++ [repeated] ++ middle ++
        [cube, cube, cube, repeated] ++ after).Perm
      (before ++ [repeated] ++ middle ++
        [repeated, cube, cube, cube] ++ after) := by
  have exchanged :
      ([cube, cube, cube] ++ [repeated]).Perm
        ([repeated] ++ [cube, cube, cube]) :=
    List.perm_append_comm
  simpa [List.append_assoc] using
    (exchanged.append_left (before ++ [repeated] ++ middle)).append_right after

private theorem cubeSplit_unique_of_count_three
    {letters : List Nat} (tested : Nat)
    (testedThree : letters.count tested = 3)
    (firstBefore firstAfter secondBefore secondAfter : List Nat)
    (firstShape :
      letters = firstBefore ++ [tested, tested, tested] ++ firstAfter)
    (secondShape :
      letters = secondBefore ++ [tested, tested, tested] ++ secondAfter) :
    firstBefore = secondBefore ∧ firstAfter = secondAfter := by
  have firstCountEquation := testedThree
  rw [firstShape] at firstCountEquation
  simp only [List.count_append, List.count_cons_self,
    List.count_nil] at firstCountEquation
  have firstBeforeZero : firstBefore.count tested = 0 := by omega
  have secondCountEquation := testedThree
  rw [secondShape] at secondCountEquation
  simp only [List.count_append, List.count_cons_self,
    List.count_nil] at secondCountEquation
  have secondBeforeZero : secondBefore.count tested = 0 := by omega
  have firstBeforeAbsent : tested ∉ firstBefore :=
    List.count_eq_zero.mp firstBeforeZero
  have secondBeforeAbsent : tested ∉ secondBefore :=
    List.count_eq_zero.mp secondBeforeZero
  have firstConsShape :
      letters = firstBefore ++ tested ::
        (tested :: tested :: firstAfter) := by
    simpa [List.append_assoc] using firstShape
  have secondConsShape :
      letters = secondBefore ++ tested ::
        (tested :: tested :: secondAfter) := by
    simpa [List.append_assoc] using secondShape
  obtain ⟨prefixEq, suffixEq⟩ :=
    firstOccurrenceSplit_unique tested firstBefore
      (tested :: tested :: firstAfter) secondBefore
      (tested :: tested :: secondAfter) firstBeforeAbsent
      secondBeforeAbsent (firstConsShape.symm.trans secondConsShape)
  exact ⟨prefixEq, by simpa using suffixEq⟩

/-- The condition-V move preserves condition IV when the earlier displayed
copy of the crossed letter is its first occurrence. -/
theorem tripleCubesContiguous_moveRepeatedFollowerBeforeCube
    (cube repeated : Nat) (before middle after : List Nat)
    (different : cube ≠ repeated)
    (repeatedAbsent : repeated ∉ before)
    (cubes :
      TripleCubesContiguous
        (before ++ [repeated] ++ middle ++
          [cube, cube, cube, repeated] ++ after)) :
    TripleCubesContiguous
      (before ++ [repeated] ++ middle ++
        [repeated, cube, cube, cube] ++ after) := by
  classical
  intro tested targetThree
  have sourceThree :
      (before ++ [repeated] ++ middle ++
        [cube, cube, cube, repeated] ++ after).count tested = 3 :=
    ((moveRepeatedFollowerBeforeCube_perm
      cube repeated before middle after).count tested).trans targetThree
  by_cases testedEqCube : tested = cube
  · subst tested
    exact ⟨before ++ [repeated] ++ middle ++ [repeated], after, by
      simp [List.append_assoc]⟩
  by_cases testedEqRepeated : tested = repeated
  · subst tested
    have repeatedNotThree :=
      repeatedCount_ne_three_of_conditionVBadConfiguration cubes
        cube repeated before middle after different repeatedAbsent rfl
    exact False.elim (repeatedNotThree sourceThree)
  · let front := before ++ [repeated] ++ middle
    have prefixCubes :
        TripleCubesContiguous
          (front ++ [cube, cube, cube, repeated] ++ after) := by
      simpa [front, List.append_assoc] using cubes
    have prefixThree :
        (front ++ [cube, cube, cube, repeated] ++ after).count tested =
          3 := by
      simpa [front, List.append_assoc] using sourceThree
    obtain ⟨cubeBefore, cubeAfter, persistent⟩ :=
      tripleCubePersistsAcrossFollowerMove cube repeated tested
        front after testedEqCube testedEqRepeated prefixCubes prefixThree
    exact ⟨cubeBefore, cubeAfter, by
      simpa [front, List.append_assoc] using persistent⟩

/-- Adjacent cube interchange is a literal permutation. -/
theorem interchangeAdjacentCubes_perm
    (left right : Nat) (before after : List Nat) :
    (before ++ [left, left, left, right, right, right] ++ after).Perm
      (before ++ [right, right, right, left, left, left] ++ after) := by
  have exchanged :
      ([left, left, left] ++ [right, right, right]).Perm
        ([right, right, right] ++ [left, left, left]) :=
    List.perm_append_comm
  simpa [List.append_assoc] using
    (exchanged.append_left before).append_right after

/-- Interchanging two distinct adjacent cubes preserves condition IV. -/
theorem tripleCubesContiguous_interchangeAdjacentCubes
    (left right : Nat) (before after : List Nat)
    (different : left ≠ right)
    (cubes :
      TripleCubesContiguous
        (before ++ [left, left, left, right, right, right] ++ after)) :
    TripleCubesContiguous
      (before ++ [right, right, right, left, left, left] ++ after) := by
  classical
  intro tested targetThree
  have sourceThree :
      (before ++ [left, left, left, right, right, right] ++
        after).count tested = 3 :=
    ((interchangeAdjacentCubes_perm left right before after).count
      tested).trans targetThree
  by_cases testedEqLeft : tested = left
  · subst tested
    exact ⟨before ++ [right, right, right], after, by
      simp [List.append_assoc]⟩
  by_cases testedEqRight : tested = right
  · subst tested
    exact ⟨before, [left, left, left] ++ after, by
      simp [List.append_assoc]⟩
  · have tailAbsent :
        tested ∉ [left, left, right, right, right] := by
      simp [testedEqLeft, testedEqRight]
    have sourceCubes :
        TripleCubesContiguous
          (before ++ left :: [left, left, right, right, right] ++
            after) := by
      simpa [List.append_assoc] using cubes
    have sourceThree' :
        (before ++ left :: [left, left, right, right, right] ++
          after).count tested = 3 := by
      simpa [List.append_assoc] using sourceThree
    rcases tripleCubeLocatedOutsideAvoidingBlock tested left before
        [left, left, right, right, right] after testedEqLeft
        tailAbsent sourceCubes sourceThree' with
      ⟨cubeBefore, cubeAfter, beforeShape⟩ |
        ⟨cubeBefore, cubeAfter, afterShape⟩
    · exact ⟨cubeBefore,
        cubeAfter ++ [right, right, right, left, left, left] ++ after,
        by rw [beforeShape]; simp [List.append_assoc]⟩
    · exact ⟨before ++
          [right, right, right, left, left, left] ++ cubeBefore,
        cubeAfter, by rw [afterShape]; simp [List.append_assoc]⟩

private theorem mem_interchangedCubeContext_iff
    (tested left right : Nat) (before after : List Nat) :
    tested ∈
        before ++ [left, left, left, right, right, right] ++ after ↔
      tested ∈
        before ++ [right, right, right, left, left, left] ++ after := by
  simp [List.mem_append, or_comm, or_left_comm, or_assoc]

/-- Interchanging two adjacent cubes preserves condition V.  A third cube
lies wholly outside the swapped block; at a left boundary the new successor
is fresh, and elsewhere only the order of the same two cubic labels changes
inside the already-seen front. -/
theorem cubesTerminalOrBeforeFirst_interchangeAdjacentCubes
    (left right : Nat) (before after : List Nat)
    (different : left ≠ right)
    (bounded :
      ∀ tested,
        (before ++ [left, left, left, right, right, right] ++
          after).count tested ≤ 3)
    (cubes :
      TripleCubesContiguous
        (before ++ [left, left, left, right, right, right] ++ after))
    (positioned :
      CubesTerminalOrBeforeFirst
        (before ++ [left, left, left, right, right, right] ++ after)) :
    CubesTerminalOrBeforeFirst
      (before ++ [right, right, right, left, left, left] ++ after) := by
  classical
  let source :=
    before ++ [left, left, left, right, right, right] ++ after
  let target :=
    before ++ [right, right, right, left, left, left] ++ after
  have targetBounded : ∀ tested, target.count tested ≤ 3 := by
    intro tested
    have countEquality :=
      (interchangeAdjacentCubes_perm left right before after).count tested
    change
      (before ++ [right, right, right, left, left, left] ++
        after).count tested ≤ 3
    rw [← countEquality]
    exact bounded tested
  have targetCubes : TripleCubesContiguous target := by
    simpa [target] using
      tripleCubesContiguous_interchangeAdjacentCubes
        left right before after different cubes
  have leftBeforeAbsent : left ∉ before := by
    apply List.count_eq_zero.mp
    have countBound := bounded left
    simp [List.count_append, different, Ne.symm different] at countBound
    omega
  have rightBeforeAbsent : right ∉ before := by
    apply List.count_eq_zero.mp
    have countBound := bounded right
    simp [List.count_append, different, Ne.symm different] at countBound
    omega
  intro tested cubeBefore cubeAfter targetShape
  have targetLower : 3 ≤ target.count tested := by
    dsimp only [target]
    rw [targetShape]
    simp only [List.count_append, List.count_cons_self,
      List.count_nil]
    omega
  have targetThree : target.count tested = 3 :=
    Nat.le_antisymm (targetBounded tested) targetLower
  have sourceThree : source.count tested = 3 := by
    exact ((interchangeAdjacentCubes_perm
      left right before after).count tested).trans targetThree
  by_cases testedEqRight : tested = right
  · subst tested
    have displayedShape :
        target = before ++ [right, right, right] ++
          ([left, left, left] ++ after) := by
      simp [target, List.append_assoc]
    obtain ⟨beforeEq, afterEq⟩ :=
      cubeSplit_unique_of_count_three right targetThree
        cubeBefore cubeAfter before ([left, left, left] ++ after)
        targetShape displayedShape
    subst cubeBefore
    subst cubeAfter
    exact Or.inr ⟨left, [left, left] ++ after, by simp, by
      simp [leftBeforeAbsent, different]⟩
  by_cases testedEqLeft : tested = left
  · subst tested
    have displayedShape :
        target = (before ++ [right, right, right]) ++
          [left, left, left] ++ after := by
      simp [target, List.append_assoc]
    obtain ⟨beforeEq, afterEq⟩ :=
      cubeSplit_unique_of_count_three left targetThree
        cubeBefore cubeAfter (before ++ [right, right, right]) after
        targetShape displayedShape
    subst cubeBefore
    subst cubeAfter
    have sourceRightShape :
        source = (before ++ [left, left, left]) ++
          [right, right, right] ++ after := by
      simp [source, List.append_assoc]
    rcases positioned right (before ++ [left, left, left]) after
        (by simpa [source] using sourceRightShape) with
      terminal | ⟨next, rest, afterShape, nextFresh⟩
    · exact Or.inl terminal
    · exact Or.inr ⟨next, rest, afterShape, by
        intro seen
        apply nextFresh
        have transferred :=
          (mem_interchangedCubeContext_iff next left right before []).mpr
            (by simpa [List.append_assoc] using seen)
        simpa [List.append_assoc] using transferred⟩
  · have testedNeRight : tested ≠ right := testedEqRight
    have testedNeLeft : tested ≠ left := testedEqLeft
    have tailAbsent :
        tested ∉ [left, left, right, right, right] := by
      simp [testedNeLeft, testedNeRight]
    have sourceCubes :
        TripleCubesContiguous
          (before ++ left :: [left, left, right, right, right] ++
            after) := by
      simpa [source, List.append_assoc] using cubes
    have sourceThree' :
        (before ++ left :: [left, left, right, right, right] ++
          after).count tested = 3 := by
      simpa [source, List.append_assoc] using sourceThree
    rcases tripleCubeLocatedOutsideAvoidingBlock tested left before
        [left, left, right, right, right] after testedNeLeft
        tailAbsent sourceCubes sourceThree' with
      ⟨localBefore, localAfter, beforeShape⟩ |
        ⟨localBefore, localAfter, afterShape⟩
    · have locatedTargetShape :
          target = localBefore ++ [tested, tested, tested] ++
            (localAfter ++
              [right, right, right, left, left, left] ++ after) := by
        rw [show target =
          before ++ [right, right, right, left, left, left] ++ after by
            rfl, beforeShape]
        simp [List.append_assoc]
      obtain ⟨cubeBeforeEq, cubeAfterEq⟩ :=
        cubeSplit_unique_of_count_three tested targetThree
          cubeBefore cubeAfter localBefore
          (localAfter ++
            [right, right, right, left, left, left] ++ after)
          targetShape locatedTargetShape
      subst cubeBefore
      subst cubeAfter
      cases localAfter with
      | nil =>
          exact Or.inr ⟨right,
            [right, right, left, left, left] ++ after, by simp, by
              intro seen
              apply rightBeforeAbsent
              rw [beforeShape]
              simpa using seen⟩
      | cons next rest =>
          have sourceLocatedShape :
              source = localBefore ++ [tested, tested, tested] ++
                (next ::
                  (rest ++ [left, left, left, right, right, right] ++
                    after)) := by
            rw [show source =
              before ++ [left, left, left, right, right, right] ++ after by
                rfl, beforeShape]
            simp [List.append_assoc]
          have nextFresh :
              next ∉ localBefore ++ [tested, tested, tested] := by
            rcases positioned tested localBefore
                (next ::
                  (rest ++ [left, left, left, right, right, right] ++
                    after))
                (by simpa [source] using sourceLocatedShape) with
              terminal | ⟨found, foundRest, foundShape, foundFresh⟩
            · simp at terminal
            · injection foundShape with headEq tailEq
              subst found
              exact foundFresh
          exact Or.inr ⟨next,
            rest ++ [right, right, right, left, left, left] ++ after,
            by simp, nextFresh⟩
    · have locatedTargetShape :
          target =
            (before ++ [right, right, right, left, left, left] ++
              localBefore) ++
              [tested, tested, tested] ++ localAfter := by
        rw [show target =
          before ++ [right, right, right, left, left, left] ++ after by
            rfl, afterShape]
        simp [List.append_assoc]
      obtain ⟨cubeBeforeEq, cubeAfterEq⟩ :=
        cubeSplit_unique_of_count_three tested targetThree
          cubeBefore cubeAfter
          (before ++ [right, right, right, left, left, left] ++
            localBefore)
          localAfter targetShape locatedTargetShape
      subst cubeBefore
      subst cubeAfter
      have sourceLocatedShape :
          source =
            (before ++ [left, left, left, right, right, right] ++
              localBefore) ++
              [tested, tested, tested] ++ localAfter := by
        rw [show source =
          before ++ [left, left, left, right, right, right] ++ after by
            rfl, afterShape]
        simp [List.append_assoc]
      rcases positioned tested
          (before ++ [left, left, left, right, right, right] ++
            localBefore)
          localAfter (by simpa [source] using sourceLocatedShape) with
        terminal | ⟨next, rest, localAfterShape, nextFresh⟩
      · exact Or.inl terminal
      · exact Or.inr ⟨next, rest, localAfterShape, by
          intro seen
          apply nextFresh
          have transferred :=
            (mem_interchangedCubeContext_iff next left right before
              (localBefore ++ [tested, tested, tested])).mpr
              (by simpa [List.append_assoc] using seen)
          simpa [List.append_assoc] using transferred⟩

/-- Any cap-three bound is preserved by the condition-V move. -/
theorem capThree_moveRepeatedFollowerBeforeCube
    (cube repeated : Nat)
    (before middle after : List Nat)
    (bounded :
      ∀ tested,
        (before ++ [repeated] ++ middle ++
          [cube, cube, cube, repeated] ++ after).count tested ≤ 3) :
    ∀ tested,
      (before ++ [repeated] ++ middle ++
        [repeated, cube, cube, cube] ++ after).count tested ≤ 3 := by
  intro tested
  rw [← (moveRepeatedFollowerBeforeCube_perm cube repeated before middle
    after).count tested]
  exact bounded tested

/-- Any cap-three bound is preserved by adjacent cube interchange. -/
theorem capThree_interchangeAdjacentCubes
    (left right : Nat) (before after : List Nat)
    (bounded :
      ∀ tested,
        (before ++ [left, left, left, right, right, right] ++
          after).count tested ≤ 3) :
    ∀ tested,
      (before ++ [right, right, right, left, left, left] ++
        after).count tested ≤ 3 := by
  intro tested
  rw [← (interchangeAdjacentCubes_perm left right before after).count
    tested]
  exact bounded tested

/-! ## A fixed cubic weighted suffix debt -/

/-- Weighted suffix debt of `letters`, using `reference` only to decide
which letters are cubic.  An occurrence of a cubic reference letter is
charged by the number of positions following it. -/
def cubicSuffixDebt (reference : List Nat) : List Nat → Nat
  | [] => 0
  | letter :: rest =>
      (if reference.count letter = 3 then rest.length else 0) +
        cubicSuffixDebt reference rest

/-- The invariant maintained by the condition-V positioning pass.  Counts
are tied to one fixed reference so `cubicSuffixDebt` classifies the same
letters as cubic throughout the recursion. -/
def CubePositionInvariant
    (reference current : List Nat) : Prop :=
  (∀ tested, current.count tested = reference.count tested) ∧
  (∀ tested, current.count tested ≤ 3) ∧
  TripleCubesContiguous current

/-- Generic well-founded normalization driver.  Supplying one strict repair
for every non-normal invariant state yields a derived normal state, with all
steps composed in `ListDerives`.  The condition-V phase uses
`measure := cubicSuffixDebt reference`. -/
theorem existsListNormalOfStrictRepair
    (measure : List Nat → Nat)
    (Invariant Normal : List Nat → Prop)
    (repair :
      ∀ current,
        Invariant current → ¬ Normal current →
          ∃ next,
            Invariant next ∧
            ListDerives current next ∧
            measure next < measure current) :
    ∀ source,
      Invariant source →
        ∃ normalized,
          Invariant normalized ∧
          Normal normalized ∧
          ListDerives source normalized
  | source, sourceInvariant => by
      by_cases normal : Normal source
      · exact ⟨source, sourceInvariant, normal,
          S5_107.ListDerives.refl (basis := basis) source⟩
      · obtain ⟨next, nextInvariant, step, decrease⟩ :=
          repair source sourceInvariant normal
        obtain ⟨normalized, normalizedInvariant, normalizedNormal,
            tail⟩ :=
          existsListNormalOfStrictRepair measure Invariant Normal repair
            next nextInvariant
        exact ⟨normalized, normalizedInvariant, normalizedNormal,
          step.trans tail⟩
termination_by
  source _ => measure source
decreasing_by
  exact decrease

/-- Condition-V specialization of the generic driver.  A caller only needs
to prove that the literal repair step preserves its chosen invariant and
strictly lowers `cubicSuffixDebt`. -/
theorem existsCubesTerminalOrBeforeFirstOfStrictRepairs
    (reference : List Nat)
    (Invariant : List Nat → Prop)
    (repair :
      ∀ current,
        Invariant current → ¬ CubesTerminalOrBeforeFirst current →
          ∃ next,
            Invariant next ∧
            ListDerives current next ∧
            cubicSuffixDebt reference next <
              cubicSuffixDebt reference current)
    (source : List Nat)
    (sourceInvariant : Invariant source) :
    ∃ normalized,
      Invariant normalized ∧
      CubesTerminalOrBeforeFirst normalized ∧
      ListDerives source normalized :=
  existsListNormalOfStrictRepair
    (cubicSuffixDebt reference) Invariant CubesTerminalOrBeforeFirst
      repair source sourceInvariant

private theorem cubicSuffixDebt_prepend
    (reference : List Nat) {left right : List Nat} {difference : Nat}
    (sameLength : left.length = right.length)
    (debtEquation :
      cubicSuffixDebt reference left =
        cubicSuffixDebt reference right + difference) :
    ∀ before,
      cubicSuffixDebt reference (before ++ left) =
        cubicSuffixDebt reference (before ++ right) + difference
  | [] => debtEquation
  | letter :: rest => by
      by_cases cubic : reference.count letter = 3
      · simp only [List.cons_append, cubicSuffixDebt, if_pos cubic,
          List.length_append]
        rw [sameLength,
          cubicSuffixDebt_prepend reference sameLength debtEquation rest]
        omega
      · simp only [List.cons_append, cubicSuffixDebt, if_neg cubic,
          Nat.zero_add]
        exact cubicSuffixDebt_prepend reference sameLength debtEquation rest

private theorem cubicSuffixDebt_cubeFollower
    (reference after : List Nat) (cube repeated : Nat)
    (cubeThree : reference.count cube = 3)
    (repeatedNotThree : reference.count repeated ≠ 3) :
    cubicSuffixDebt reference
        ([cube, cube, cube, repeated] ++ after) =
      cubicSuffixDebt reference
          ([repeated, cube, cube, cube] ++ after) + 3 := by
  simp [cubicSuffixDebt, cubeThree, repeatedNotThree]
  omega

/-- The condition-V repair lowers the fixed cubic suffix debt by exactly
three.  The `repeatedNotThree` premise is precisely what condition IV and the
two separated displayed occurrences establish for the crossed letter. -/
theorem cubicSuffixDebt_moveRepeatedFollowerBeforeCube
    (reference : List Nat) (cube repeated : Nat)
    (before middle after : List Nat)
    (cubeThree : reference.count cube = 3)
    (repeatedNotThree : reference.count repeated ≠ 3) :
    cubicSuffixDebt reference
        (before ++ [repeated] ++ middle ++
          [cube, cube, cube, repeated] ++ after) =
      cubicSuffixDebt reference
          (before ++ [repeated] ++ middle ++
            [repeated, cube, cube, cube] ++ after) + 3 := by
  let front := before ++ [repeated] ++ middle
  have localDebt := cubicSuffixDebt_cubeFollower reference after
    cube repeated cubeThree repeatedNotThree
  have sameLength :
      ([cube, cube, cube, repeated] ++ after).length =
        ([repeated, cube, cube, cube] ++ after).length := by
    simp
  have prefixed := cubicSuffixDebt_prepend reference sameLength localDebt
    front
  simpa [front, List.append_assoc] using prefixed

/-- Adjacent interchange of two cubic letters leaves the cubic suffix debt
unchanged.  This separates the terminating condition-V phase from the later
condition-VI cube-run sorting phase. -/
theorem cubicSuffixDebt_interchangeAdjacentCubes
    (reference : List Nat) (left right : Nat)
    (before after : List Nat)
    (leftThree : reference.count left = 3)
    (rightThree : reference.count right = 3) :
    cubicSuffixDebt reference
        (before ++ [left, left, left, right, right, right] ++ after) =
      cubicSuffixDebt reference
        (before ++ [right, right, right, left, left, left] ++ after) := by
  let leftBlock := [left, left, left, right, right, right] ++ after
  let rightBlock := [right, right, right, left, left, left] ++ after
  have sameLength : leftBlock.length = rightBlock.length := by
    simp [leftBlock, rightBlock]
  have localDebt :
      cubicSuffixDebt reference leftBlock =
        cubicSuffixDebt reference rightBlock := by
    simp [leftBlock, rightBlock, cubicSuffixDebt, leftThree, rightThree]
  have prefixed := cubicSuffixDebt_prepend reference
    sameLength (difference := 0) (by simpa using localDebt) before
  simpa [leftBlock, rightBlock] using prefixed

/-! ## Bundled rewrite steps for the normalization driver -/

/-- The exact derivation, multiplicity preservation, and strict measure
decrease supplied by one condition-V repair. -/
theorem conditionVRepairStep
    (reference : List Nat) (cube repeated : Nat)
    (before middle after : List Nat)
    (cubeThree : reference.count cube = 3)
    (repeatedNotThree : reference.count repeated ≠ 3) :
    let source :=
      before ++ [repeated] ++ middle ++
        [cube, cube, cube, repeated] ++ after
    let target :=
      before ++ [repeated] ++ middle ++
        [repeated, cube, cube, cube] ++ after
    ListDerives source target ∧
      (∀ tested, target.count tested = source.count tested) ∧
      cubicSuffixDebt reference source =
        cubicSuffixDebt reference target + 3 := by
  dsimp
  refine ⟨listDerivesMoveRepeatedFollowerBeforeCube
      cube repeated before middle after, ?_,
    cubicSuffixDebt_moveRepeatedFollowerBeforeCube
      reference cube repeated before middle after cubeThree
        repeatedNotThree⟩
  intro tested
  exact ((moveRepeatedFollowerBeforeCube_perm
    cube repeated before middle after).count tested).symm

/-- Every failure of condition V inside the fixed-reference invariant has
one derived repair which preserves counts, the cap-three bound, and condition
IV while strictly lowering the cubic suffix debt. -/
theorem existsConditionVStrictRepair
    (reference current : List Nat)
    (invariant : CubePositionInvariant reference current)
    (notPositioned : ¬ CubesTerminalOrBeforeFirst current) :
    ∃ next,
      CubePositionInvariant reference next ∧
      ListDerives current next ∧
      cubicSuffixDebt reference next <
        cubicSuffixDebt reference current := by
  classical
  obtain ⟨counts, bounded, cubes⟩ := invariant
  obtain ⟨cube, repeated, before, middle, after, different,
      repeatedAbsent, cubeThree, shape⟩ :=
    existsConditionVBadConfigurationFirst bounded notPositioned
  have repeatedNotThreeCurrent : current.count repeated ≠ 3 :=
    repeatedCount_ne_three_of_conditionVBadConfiguration cubes
      cube repeated before middle after different repeatedAbsent shape
  have cubeThreeReference : reference.count cube = 3 := by
    rw [← counts cube]
    exact cubeThree
  have repeatedNotThreeReference : reference.count repeated ≠ 3 := by
    intro repeatedThree
    apply repeatedNotThreeCurrent
    exact (counts repeated).trans repeatedThree
  subst current
  let target :=
    before ++ [repeated] ++ middle ++
      [repeated, cube, cube, cube] ++ after
  have targetCounts :
      ∀ tested,
        target.count tested =
          (before ++ [repeated] ++ middle ++
            [cube, cube, cube, repeated] ++ after).count tested := by
    intro tested
    exact ((moveRepeatedFollowerBeforeCube_perm
      cube repeated before middle after).count tested).symm
  have targetBounded : ∀ tested, target.count tested ≤ 3 := by
    simpa [target] using capThree_moveRepeatedFollowerBeforeCube
      cube repeated before middle after bounded
  have targetCubes : TripleCubesContiguous target := by
    simpa [target] using
      tripleCubesContiguous_moveRepeatedFollowerBeforeCube
        cube repeated before middle after different repeatedAbsent cubes
  have targetDerivation :
      ListDerives
        (before ++ [repeated] ++ middle ++
          [cube, cube, cube, repeated] ++ after) target := by
    simpa [target] using listDerivesMoveRepeatedFollowerBeforeCube
      cube repeated before middle after
  have debtEquation :=
    cubicSuffixDebt_moveRepeatedFollowerBeforeCube reference
      cube repeated before middle after cubeThreeReference
      repeatedNotThreeReference
  refine ⟨target, ?_, targetDerivation, ?_⟩
  · refine ⟨?_, targetBounded, targetCubes⟩
    intro tested
    exact (targetCounts tested).trans (counts tested)
  · dsimp [target] at debtEquation ⊢
    omega

/-- A cap-three condition-IV list derives, with exactly the same counts, to
a list additionally satisfying condition V. -/
theorem existsCubePositionReduction
    (letters : List Nat)
    (bounded : ∀ tested, letters.count tested ≤ 3)
    (cubes : TripleCubesContiguous letters) :
    ∃ positioned,
      (∀ tested, positioned.count tested = letters.count tested) ∧
      (∀ tested, positioned.count tested ≤ 3) ∧
      TripleCubesContiguous positioned ∧
      CubesTerminalOrBeforeFirst positioned ∧
      ListDerives letters positioned := by
  have sourceInvariant : CubePositionInvariant letters letters :=
    ⟨fun tested => rfl, bounded, cubes⟩
  obtain ⟨positioned, positionedInvariant, positionedNormal,
      derivation⟩ :=
    existsCubesTerminalOrBeforeFirstOfStrictRepairs letters
      (CubePositionInvariant letters)
      (fun current currentInvariant notPositioned =>
        existsConditionVStrictRepair letters current currentInvariant
          notPositioned)
      letters sourceInvariant
  exact ⟨positioned, positionedInvariant.1,
    positionedInvariant.2.1, positionedInvariant.2.2,
    positionedNormal, derivation⟩

/-! ## Sorting adjacent cube runs -/

private def cubicSmallerCount
    (reference : List Nat) (pivot : Nat) (letters : List Nat) : Nat :=
  (letters.filter fun tested =>
    decide (reference.count tested = 3 ∧ tested < pivot)).length

/-- Fixed-reference inversion count of cubic occurrences.  Using occurrences
rather than compressed cube tokens makes an inverted adjacent cube swap drop
the measure by exactly nine. -/
def cubicInversionCount (reference : List Nat) : List Nat → Nat
  | [] => 0
  | first :: rest =>
      (if reference.count first = 3 then
        cubicSmallerCount reference first rest
      else 0) + cubicInversionCount reference rest

private theorem cubicSmallerCount_append
    (reference : List Nat) (pivot : Nat) (left right : List Nat) :
    cubicSmallerCount reference pivot (left ++ right) =
      cubicSmallerCount reference pivot left +
        cubicSmallerCount reference pivot right := by
  simp [cubicSmallerCount, List.filter_append]

private theorem cubicInversionCount_prepend
    (reference : List Nat) {left right : List Nat} {difference : Nat}
    (smallerEquation :
      ∀ pivot,
        cubicSmallerCount reference pivot left =
          cubicSmallerCount reference pivot right)
    (inversionEquation :
      cubicInversionCount reference left =
        cubicInversionCount reference right + difference) :
    ∀ before,
      cubicInversionCount reference (before ++ left) =
        cubicInversionCount reference (before ++ right) + difference
  | [] => inversionEquation
  | first :: rest => by
      simp only [List.cons_append, cubicInversionCount]
      rw [cubicSmallerCount_append, cubicSmallerCount_append,
        smallerEquation first,
        cubicInversionCount_prepend reference smallerEquation
          inversionEquation rest]
      omega

private theorem cubicSmallerCount_cubeInterchange
    (reference : List Nat) (pivot left right : Nat)
    (after : List Nat) :
    cubicSmallerCount reference pivot
        ([left, left, left, right, right, right] ++ after) =
    cubicSmallerCount reference pivot
        ([right, right, right, left, left, left] ++ after) := by
  by_cases leftSmall :
      reference.count left = 3 ∧ left < pivot <;>
    by_cases rightSmall :
      reference.count right = 3 ∧ right < pivot <;>
    simp [cubicSmallerCount, leftSmall, rightSmall, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm]

private theorem cubicInversionCount_cubeInterchange
    (reference : List Nat) (left right : Nat) (after : List Nat)
    (leftThree : reference.count left = 3)
    (rightThree : reference.count right = 3)
    (inverted : right < left) :
    cubicInversionCount reference
        ([left, left, left, right, right, right] ++ after) =
      cubicInversionCount reference
          ([right, right, right, left, left, left] ++ after) + 9 := by
  have notLeftLtRight : ¬ left < right := by omega
  have different : left ≠ right := by omega
  simp [cubicInversionCount, cubicSmallerCount, leftThree, rightThree,
    inverted, notLeftLtRight, different, Ne.symm different] <;> omega

/-- Swapping an inverted adjacent cube pair lowers the fixed-reference cubic
inversion count by exactly nine. -/
theorem cubicInversionCount_interchangeAdjacentCubes
    (reference : List Nat) (left right : Nat)
    (before after : List Nat)
    (leftThree : reference.count left = 3)
    (rightThree : reference.count right = 3)
    (inverted : right < left) :
    cubicInversionCount reference
        (before ++ [left, left, left, right, right, right] ++ after) =
      cubicInversionCount reference
          (before ++ [right, right, right, left, left, left] ++ after) +
        9 := by
  have localEquation := cubicInversionCount_cubeInterchange reference
    left right after leftThree rightThree inverted
  have smallerEquation := fun pivot =>
    cubicSmallerCount_cubeInterchange reference pivot left right after
  have prefixed := cubicInversionCount_prepend reference
    smallerEquation localEquation before
  simpa [List.append_assoc] using prefixed

/-- Invariant maintained while adjacent cube runs are sorted. -/
def CubeOrderInvariant
    (reference current : List Nat) : Prop :=
  CubePositionInvariant reference current ∧
  CubesTerminalOrBeforeFirst current

/-- The exact derivation and invariant certificates supplied by swapping one
inverted adjacent cube pair. -/
theorem conditionVIRepairStep
    (reference : List Nat) (left right : Nat)
    (before after : List Nat)
    (leftThree : reference.count left = 3)
    (rightThree : reference.count right = 3)
    (_inverted : right < left) :
    let source :=
      before ++ [left, left, left, right, right, right] ++ after
    let target :=
      before ++ [right, right, right, left, left, left] ++ after
    ListDerives source target ∧
      (∀ tested, target.count tested = source.count tested) ∧
      cubicSuffixDebt reference source =
        cubicSuffixDebt reference target := by
  dsimp
  refine ⟨listDerivesInterchangeAdjacentCubes
      left right before after, ?_,
    cubicSuffixDebt_interchangeAdjacentCubes
      reference left right before after leftThree rightThree⟩
  intro tested
  exact ((interchangeAdjacentCubes_perm left right before after).count
    tested).symm

/-- Every failure of condition VI has an inverted adjacent cube pair.  Law 8
repairs it while preserving counts and conditions III--V, and the cubic
inversion count drops strictly. -/
theorem existsConditionVIStrictRepair
    (reference current : List Nat)
    (invariant : CubeOrderInvariant reference current)
    (notOrdered : ¬ AdjacentCubesOrdered current) :
    ∃ next,
      CubeOrderInvariant reference next ∧
      ListDerives current next ∧
      cubicInversionCount reference next <
        cubicInversionCount reference current := by
  classical
  obtain ⟨⟨counts, bounded, cubes⟩, positioned⟩ := invariant
  unfold AdjacentCubesOrdered at notOrdered
  obtain ⟨left, notOrdered⟩ := Classical.not_forall.mp notOrdered
  obtain ⟨right, notOrdered⟩ := Classical.not_forall.mp notOrdered
  obtain ⟨before, notOrdered⟩ := Classical.not_forall.mp notOrdered
  obtain ⟨after, notOrdered⟩ := Classical.not_forall.mp notOrdered
  have different : left ≠ right := by
    apply Classical.byContradiction
    intro same
    apply notOrdered
    intro different
    exact (same different).elim
  have shape :
      current = before ++ [left, left, left] ++
        [right, right, right] ++ after := by
    apply Classical.byContradiction
    intro notShape
    apply notOrdered
    intro _ candidateShape
    exact (notShape candidateShape).elim
  have notIncreasing : ¬ left < right := by
    intro increasing
    apply notOrdered
    intro _ _
    exact increasing
  have inverted : right < left := by omega
  have leftLower : 3 ≤ current.count left := by
    rw [shape]
    simp [List.count_append, different, Ne.symm different] <;> omega
  have rightLower : 3 ≤ current.count right := by
    rw [shape]
    simp [List.count_append, different, Ne.symm different] <;> omega
  have leftThreeCurrent : current.count left = 3 :=
    Nat.le_antisymm (bounded left) leftLower
  have rightThreeCurrent : current.count right = 3 :=
    Nat.le_antisymm (bounded right) rightLower
  have leftThreeReference : reference.count left = 3 := by
    rw [← counts left]
    exact leftThreeCurrent
  have rightThreeReference : reference.count right = 3 := by
    rw [← counts right]
    exact rightThreeCurrent
  have flattenedShape :
      current = before ++ [left, left, left, right, right, right] ++ after := by
    simpa [List.append_assoc] using shape
  rw [flattenedShape] at counts bounded cubes positioned ⊢
  let target :=
    before ++ [right, right, right, left, left, left] ++ after
  have targetCounts :
      ∀ tested,
        target.count tested =
          (before ++ [left, left, left, right, right, right] ++
            after).count tested := by
    intro tested
    exact ((interchangeAdjacentCubes_perm left right before after).count
      tested).symm
  have targetBounded : ∀ tested, target.count tested ≤ 3 := by
    simpa [target] using capThree_interchangeAdjacentCubes
      left right before after bounded
  have targetCubes : TripleCubesContiguous target := by
    simpa [target] using
      tripleCubesContiguous_interchangeAdjacentCubes
        left right before after different cubes
  have targetPositioned : CubesTerminalOrBeforeFirst target := by
    simpa [target] using
      cubesTerminalOrBeforeFirst_interchangeAdjacentCubes
        left right before after different bounded cubes positioned
  have targetDerivation :
      ListDerives
        (before ++ [left, left, left, right, right, right] ++ after)
        target := by
    simpa [target] using listDerivesInterchangeAdjacentCubes
      left right before after
  have inversionEquation :=
    cubicInversionCount_interchangeAdjacentCubes reference
      left right before after leftThreeReference rightThreeReference
      inverted
  refine ⟨target, ?_, targetDerivation, ?_⟩
  · exact ⟨⟨fun tested =>
        (targetCounts tested).trans (counts tested),
      targetBounded, targetCubes⟩, targetPositioned⟩
  · dsimp [target] at inversionEquation ⊢
    omega

/-- A cap-three list satisfying conditions IV--V derives, with exactly the
same counts, to a list satisfying conditions IV--VI. -/
theorem existsCubeOrderReduction
    (letters : List Nat)
    (bounded : ∀ tested, letters.count tested ≤ 3)
    (cubes : TripleCubesContiguous letters)
    (positioned : CubesTerminalOrBeforeFirst letters) :
    ∃ ordered,
      (∀ tested, ordered.count tested = letters.count tested) ∧
      (∀ tested, ordered.count tested ≤ 3) ∧
      TripleCubesContiguous ordered ∧
      CubesTerminalOrBeforeFirst ordered ∧
      AdjacentCubesOrdered ordered ∧
      ListDerives letters ordered := by
  have sourceInvariant : CubeOrderInvariant letters letters :=
    ⟨⟨fun tested => rfl, bounded, cubes⟩, positioned⟩
  obtain ⟨ordered, orderedInvariant, orderedNormal, derivation⟩ :=
    existsListNormalOfStrictRepair
      (cubicInversionCount letters) (CubeOrderInvariant letters)
      AdjacentCubesOrdered
      (fun current currentInvariant notOrdered =>
        existsConditionVIStrictRepair letters current currentInvariant
          notOrdered)
      letters sourceInvariant
  exact ⟨ordered, orderedInvariant.1.1,
    orderedInvariant.1.2.1, orderedInvariant.1.2.2,
    orderedInvariant.2, orderedNormal, derivation⟩

/-- Full Proposition 8.1 canonicalization: cap multiplicities, gather every
cube, position cube followers, and sort each adjacent cube run. -/
theorem existsProposition8ACanonicalReductionInner
    (letters : List Nat) :
    ∃ normal,
      Proposition8ACanonical normal ∧
      (∀ tested,
        normal.count tested = min (letters.count tested) 3) ∧
      ListDerives letters normal := by
  obtain ⟨gathered, gatheredBounded, gatheredCounts, gatheredCubes,
      gatheredDerivation⟩ :=
    existsCapThreeContiguousCubeReduction letters
  obtain ⟨positioned, positionedCounts, positionedBounded,
      positionedCubes, positionedNormal, positionDerivation⟩ :=
    existsCubePositionReduction gathered gatheredBounded gatheredCubes
  obtain ⟨ordered, orderedCounts, orderedBounded, orderedCubes,
      orderedPositioned, orderedNormal, orderDerivation⟩ :=
    existsCubeOrderReduction positioned positionedBounded positionedCubes
      positionedNormal
  refine ⟨ordered,
    proposition8ACanonical_of_components orderedBounded orderedCubes
      orderedPositioned orderedNormal,
    ?_, gatheredDerivation.trans
      (positionDerivation.trans orderDerivation)⟩
  intro tested
  exact (orderedCounts tested).trans
    ((positionedCounts tested).trans (gatheredCounts tested))

end CubePosition

/-- Public assembly theorem consumed by the Proposition 8.1 completeness
module. -/
theorem existsProposition8ACanonicalReduction
    (letters : List Nat) :
    ∃ normal,
      Proposition8ACanonical normal ∧
      (∀ tested,
        normal.count tested = min (letters.count tested) 3) ∧
      S5_107.ListDerives basis letters normal :=
  CubePosition.existsProposition8ACanonicalReductionInner letters

end SemigroupBasis.CoRoots.Order6LeeLiProposition8A
