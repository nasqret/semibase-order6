import SemigroupBasis.CoRoots.Order6LeeLiProposition8ACapThree
import SemigroupBasis.CoRoots.Order6LeeLiCompletePrecedencePermutation

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6LeeLiProposition8A

open SemigroupBasis

private abbrev ListDerives : List Nat → List Nat → Prop :=
  S5_107.ListDerives basis

/-! The complete-precedence scanner has a private step function in
`S5_841`.  The following definition is the same transparent five-state
automaton; the reflexive bridge lets the structural cube lemmas below remain
independent of the finite semantic classifier. -/

private def precedenceStep
    (x y : Nat) (state : S5_841.PrecedenceState) (letter : Nat) :
    S5_841.PrecedenceState :=
  if letter = x then
    match state with
    | .neither => .onlyX
    | .onlyX => .onlyX
    | .onlyY | .ordered | .violated => .violated
  else if letter = y then
    match state with
    | .neither => .onlyY
    | .onlyX => .ordered
    | .onlyY => .onlyY
    | .ordered => .ordered
    | .violated => .violated
  else state

private theorem precedenceScanList_eq_fold
    (letters : List Nat) (x y : Nat) :
    S5_841.precedenceScanList letters x y =
      letters.foldl (precedenceStep x y) .neither := by
  rfl

private theorem precedenceFold_pairFree
    (x y : Nat) :
    ∀ (letters : List Nat) (state : S5_841.PrecedenceState),
      x ∉ letters → y ∉ letters →
      letters.foldl (precedenceStep x y) state = state
  | [], _, _, _ => rfl
  | letter :: rest, state, xAbsent, yAbsent => by
      have letterNeX : letter ≠ x := by
        intro equal
        subst letter
        exact xAbsent (List.Mem.head rest)
      have letterNeY : letter ≠ y := by
        intro equal
        subst letter
        exact yAbsent (List.Mem.head rest)
      have restXAbsent : x ∉ rest :=
        fun member => xAbsent (List.Mem.tail letter member)
      have restYAbsent : y ∉ rest :=
        fun member => yAbsent (List.Mem.tail letter member)
      simp only [List.foldl_cons]
      rw [show precedenceStep x y state letter = state by
        simp [precedenceStep, letterNeX, letterNeY]]
      exact precedenceFold_pairFree x y rest state
        restXAbsent restYAbsent

private theorem precedenceFold_onlyX_of_y_absent
    (x y : Nat) :
    ∀ letters : List Nat,
      y ∉ letters →
      letters.foldl (precedenceStep x y) .onlyX = .onlyX
  | [], _ => rfl
  | letter :: rest, absent => by
      have letterNeY : letter ≠ y := by
        intro equal
        subst letter
        exact absent (List.Mem.head rest)
      have restAbsent : y ∉ rest :=
        fun member => absent (List.Mem.tail letter member)
      simp only [List.foldl_cons]
      rw [show precedenceStep x y .onlyX letter = .onlyX by
        by_cases isX : letter = x
        · simp [precedenceStep, isX]
        · simp [precedenceStep, isX, letterNeY]]
      exact precedenceFold_onlyX_of_y_absent x y rest restAbsent

private theorem precedenceFold_onlyY_of_x_absent
    (x y : Nat) :
    ∀ letters : List Nat,
      x ∉ letters →
      letters.foldl (precedenceStep x y) .onlyY = .onlyY
  | [], _ => rfl
  | letter :: rest, absent => by
      have letterNeX : letter ≠ x := by
        intro equal
        subst letter
        exact absent (List.Mem.head rest)
      have restAbsent : x ∉ rest :=
        fun member => absent (List.Mem.tail letter member)
      simp only [List.foldl_cons]
      rw [show precedenceStep x y .onlyY letter = .onlyY by
        simp [precedenceStep, letterNeX]]
      exact precedenceFold_onlyY_of_x_absent x y rest restAbsent

private theorem precedenceFold_ordered_of_x_absent
    (x y : Nat) :
    ∀ letters : List Nat,
      x ∉ letters →
      letters.foldl (precedenceStep x y) .ordered = .ordered
  | [], _ => rfl
  | letter :: rest, absent => by
      have letterNeX : letter ≠ x := by
        intro equal
        subst letter
        exact absent (List.Mem.head rest)
      have restAbsent : x ∉ rest :=
        fun member => absent (List.Mem.tail letter member)
      simp only [List.foldl_cons]
      rw [show precedenceStep x y .ordered letter = .ordered by
        simp [precedenceStep, letterNeX]]
      exact precedenceFold_ordered_of_x_absent x y rest restAbsent

private theorem precedenceFold_violated
    (x y : Nat) :
    ∀ letters : List Nat,
      letters.foldl (precedenceStep x y) .violated = .violated
  | [] => rfl
  | letter :: rest => by
      simp only [List.foldl_cons]
      rw [show precedenceStep x y .violated letter = .violated by
        simp [precedenceStep]]
      exact precedenceFold_violated x y rest

private theorem precedenceFold_onlyX_of_x_mem_y_absent
    (x y : Nat) :
    ∀ letters : List Nat,
      x ∈ letters → y ∉ letters →
      letters.foldl (precedenceStep x y) .neither = .onlyX
  | [], member, _ => by simp at member
  | letter :: rest, xMember, yAbsent => by
      have letterNeY : letter ≠ y := by
        intro equal
        subst letter
        exact yAbsent (List.Mem.head rest)
      have restYAbsent : y ∉ rest :=
        fun member => yAbsent (List.Mem.tail letter member)
      simp only [List.foldl_cons]
      by_cases isX : letter = x
      · rw [show precedenceStep x y .neither letter = .onlyX by
          simp [precedenceStep, isX]]
        exact precedenceFold_onlyX_of_y_absent x y rest restYAbsent
      · have restXMember : x ∈ rest :=
          (List.mem_cons.mp xMember).resolve_left (Ne.symm isX)
        rw [show precedenceStep x y .neither letter = .neither by
          simp [precedenceStep, isX, letterNeY]]
        exact precedenceFold_onlyX_of_x_mem_y_absent
          x y rest restXMember restYAbsent

private theorem precedenceFold_ordered_of_x_absent_y_mem
    (x y : Nat) :
    ∀ letters : List Nat,
      x ∉ letters → y ∈ letters →
      letters.foldl (precedenceStep x y) .onlyX = .ordered
  | [], _, member => by simp at member
  | letter :: rest, xAbsent, yMember => by
      have letterNeX : letter ≠ x := by
        intro equal
        subst letter
        exact xAbsent (List.Mem.head rest)
      have restXAbsent : x ∉ rest :=
        fun member => xAbsent (List.Mem.tail letter member)
      simp only [List.foldl_cons]
      by_cases isY : letter = y
      · rw [show precedenceStep x y .onlyX letter = .ordered by
          have yNeX : y ≠ x := fun equal => letterNeX (isY.trans equal)
          simp [precedenceStep, isY, yNeX]]
        exact precedenceFold_ordered_of_x_absent x y rest restXAbsent
      · have restYMember : y ∈ rest :=
          (List.mem_cons.mp yMember).resolve_left (Ne.symm isY)
        rw [show precedenceStep x y .onlyX letter = .onlyX by
          simp [precedenceStep, letterNeX, isY]]
        exact precedenceFold_ordered_of_x_absent_y_mem
          x y rest restXAbsent restYMember

private theorem precedenceFold_violated_of_x_mem_from_onlyY
    (x y : Nat) :
    ∀ letters : List Nat,
      x ∈ letters →
      letters.foldl (precedenceStep x y) .onlyY = .violated
  | [], member => by simp at member
  | letter :: rest, member => by
      simp only [List.foldl_cons]
      by_cases isX : letter = x
      · rw [show precedenceStep x y .onlyY letter = .violated by
          simp [precedenceStep, isX]]
        exact precedenceFold_violated x y rest
      · have restMember : x ∈ rest :=
          (List.mem_cons.mp member).resolve_left (Ne.symm isX)
        rw [show precedenceStep x y .onlyY letter = .onlyY by
          simp [precedenceStep, isX]]
        exact precedenceFold_violated_of_x_mem_from_onlyY
          x y rest restMember

private theorem precedenceFold_violated_of_x_mem_from_ordered
    (x y : Nat) :
    ∀ letters : List Nat,
      x ∈ letters →
      letters.foldl (precedenceStep x y) .ordered = .violated
  | [], member => by simp at member
  | letter :: rest, member => by
      simp only [List.foldl_cons]
      by_cases isX : letter = x
      · rw [show precedenceStep x y .ordered letter = .violated by
          simp [precedenceStep, isX]]
        exact precedenceFold_violated x y rest
      · have restMember : x ∈ rest :=
          (List.mem_cons.mp member).resolve_left (Ne.symm isX)
        rw [show precedenceStep x y .ordered letter = .ordered by
          simp [precedenceStep, isX]]
        exact precedenceFold_violated_of_x_mem_from_ordered
          x y rest restMember

private theorem precedenceScan_ordered_of_blocks
    {x y : Nat} (different : x ≠ y)
    (before after : List Nat)
    (xInBefore : x ∈ before)
    (yAbsentBefore : y ∉ before)
    (xAbsentAfter : x ∉ after)
    (yInAfter : y ∈ after) :
    S5_841.precedenceScanList (before ++ after) x y = .ordered := by
  rw [precedenceScanList_eq_fold, List.foldl_append]
  rw [precedenceFold_onlyX_of_x_mem_y_absent
    x y before xInBefore yAbsentBefore]
  exact precedenceFold_ordered_of_x_absent_y_mem
    x y after xAbsentAfter yInAfter

private theorem precedenceScan_violated_of_inversion
    {x y : Nat} (different : x ≠ y)
    (before after : List Nat)
    (yAbsentBefore : y ∉ before)
    (xInAfter : x ∈ after) :
    S5_841.precedenceScanList (before ++ y :: after) x y = .violated := by
  rw [precedenceScanList_eq_fold, List.foldl_append]
  by_cases xInBefore : x ∈ before
  · rw [precedenceFold_onlyX_of_x_mem_y_absent
      x y before xInBefore yAbsentBefore]
    simp only [List.foldl_cons]
    rw [show precedenceStep x y .onlyX y = .ordered by
      simp [precedenceStep, Ne.symm different]]
    exact precedenceFold_violated_of_x_mem_from_ordered
      x y after xInAfter
  · rw [precedenceFold_pairFree x y before .neither
      xInBefore yAbsentBefore]
    simp only [List.foldl_cons]
    rw [show precedenceStep x y .neither y = .onlyY by
      simp [precedenceStep, Ne.symm different]]
    exact precedenceFold_violated_of_x_mem_from_onlyY
      x y after xInAfter

private theorem precedenceState_violated_ne_ordered :
    (S5_841.PrecedenceState.violated : S5_841.PrecedenceState) ≠
      .ordered := by
  decide

/-- Every letter of multiplicity three occurs as one literal contiguous
cube.  This is Lee--Li condition IV, separated out because the post-cap
gathering pass establishes it before conditions V and VI are imposed. -/
def TripleCubesContiguous (letters : List Nat) : Prop :=
  ∀ tested, letters.count tested = 3 →
    ∃ before after,
      letters = before ++ [tested, tested, tested] ++ after

/-!
## Lee--Li conditions III--VI

The fields below are deliberately stated on literal list decompositions.
Thus condition IV exposes the whole cube, condition V talks about the letter
immediately following that cube, and condition VI applies exactly to two
adjacent cubes.
-/

/-- A cap-three word satisfying Lee--Li Proposition 8.1 conditions III--VI.

* `capThree` is condition III;
* `cubeContiguous` is condition IV;
* `cubeTerminalOrBeforeFirst` is condition V;
* `adjacentCubesOrdered` is condition VI, with the fixed natural-number order
  used only to choose one representative among freely interchangeable cubes.
-/
structure Proposition8ACanonical (letters : List Nat) : Prop where
  capThree : ∀ letter, letters.count letter ≤ 3
  cubeContiguous : TripleCubesContiguous letters
  cubeTerminalOrBeforeFirst :
    ∀ letter before after,
      letters = before ++ [letter, letter, letter] ++ after →
      after = [] ∨
        ∃ next rest,
          after = next :: rest ∧
          next ∉ before ++ [letter, letter, letter]
  adjacentCubesOrdered :
    ∀ left right before after,
      left ≠ right →
      letters = before ++ [left, left, left] ++
        [right, right, right] ++ after →
      left < right

namespace Proposition8ACanonical

/-- In a canonical cube decomposition, no copy of the cube letter occurs
before the displayed cube. -/
theorem cubePrefixAbsent
    {letters : List Nat} (canonical : Proposition8ACanonical letters)
    {letter : Nat} {before after : List Nat}
    (shape : letters = before ++ [letter, letter, letter] ++ after) :
    letter ∉ before := by
  have countBound := canonical.capThree letter
  rw [shape] at countBound
  simp only [List.count_append, List.count_cons_self,
    List.count_nil] at countBound
  have zero : before.count letter = 0 := by omega
  exact List.count_eq_zero.mp zero

/-- In a canonical cube decomposition, no copy of the cube letter occurs
after the displayed cube. -/
theorem cubeSuffixAbsent
    {letters : List Nat} (canonical : Proposition8ACanonical letters)
    {letter : Nat} {before after : List Nat}
    (shape : letters = before ++ [letter, letter, letter] ++ after) :
    letter ∉ after := by
  have countBound := canonical.capThree letter
  rw [shape] at countBound
  simp only [List.count_append, List.count_cons_self,
    List.count_nil] at countBound
  have zero : after.count letter = 0 := by omega
  exact List.count_eq_zero.mp zero

/-- Condition IV also supplies the first adjacent pair required by the
segmented complete-precedence permutation argument. -/
theorem firstPairOfCountThree
    {letters : List Nat} (canonical : Proposition8ACanonical letters)
    (tested : Nat) (count : letters.count tested = 3) :
    ∃ before after,
      letters = before ++ tested :: tested :: after ∧
      tested ∉ before := by
  obtain ⟨before, after, shape⟩ :=
    canonical.cubeContiguous tested count
  refine ⟨before, tested :: after, ?_, ?_⟩
  · simpa [List.append_assoc] using shape
  · exact canonical.cubePrefixAbsent shape

private theorem prefixCount_ne_one_of_firstPairAux
    (tested separator : Nat) (pairAfter suffix : List Nat)
    (different : tested ≠ separator) :
    ∀ (pairBefore preWords : List Nat),
      tested ∉ pairBefore →
      pairBefore ++ tested :: tested :: pairAfter =
        preWords ++ separator :: suffix →
      preWords.count tested ≠ 1
  | [], [], _, _ => by simp
  | [], first :: rest, _, shape => by
      simp only [List.nil_append, List.cons_append] at shape
      injection shape with firstEq tailEq
      subst first
      intro countOne
      cases rest with
      | nil =>
          simp only [List.nil_append] at tailEq
          injection tailEq with equality
          exact different equality
      | cons next more =>
          simp only [List.cons_append] at tailEq
          injection tailEq with equality
          subst next
          simp only [List.count_cons_self] at countOne
          omega
  | first :: rest, [], _, _ => by simp
  | first :: rest, next :: preWords, absent, shape => by
      have firstDifferent : first ≠ tested := by
        intro equality
        subst first
        exact absent (List.Mem.head rest)
      have restAbsent : tested ∉ rest :=
        fun member => absent (List.Mem.tail first member)
      simp only [List.cons_append] at shape
      injection shape with headEq tailEq
      subst next
      have recurse :=
        prefixCount_ne_one_of_firstPairAux tested separator
          pairAfter suffix different rest preWords restAbsent tailEq
      simpa [firstDifferent] using recurse

/-- Condition IV implies the exact public separator condition consumed by
`Order6LeeLiCompletePrecedencePermutation.listDerivesCanonicalPair`. -/
theorem simpleSplitCanonical
    {letters : List Nat} (canonical : Proposition8ACanonical letters) :
    Order6LeeLiCompletePrecedencePermutation.SimpleSplitCanonical letters := by
  intro tested separator before after split testedThree
    _separatorSimple different
  obtain ⟨pairBefore, pairAfter, pairShape, pairBeforeAbsent⟩ :=
    canonical.firstPairOfCountThree tested testedThree
  exact prefixCount_ne_one_of_firstPairAux tested separator
    pairAfter after different pairBefore before pairBeforeAbsent
    (pairShape.symm.trans split)

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

/-- Starting after a cube which is straddled by another letter, conditions
III--V eventually encounter a first occurrence of a letter of multiplicity
at most two.  Intervening count-three letters are skipped a whole cube at a
time, so the suffix length is the termination measure. -/
private theorem existsSmallFirstAfterCubeBeforeRepeated
    {letters : List Nat} (canonical : Proposition8ACanonical letters) :
    ∀ (suffix : List Nat) (current : Nat) (before : List Nat)
      (target : Nat),
      letters = before ++ [current, current, current] ++ suffix →
      target ∈ before →
      target ∈ suffix →
      current ≠ target →
      ∃ next middle right,
        suffix = middle ++ next :: right ∧
        next ∉ before ++ [current, current, current] ++ middle ∧
        letters.count next ≤ 2 ∧
        target ∈ right
  | suffix, current, before, target, shape,
      targetBefore, targetSuffix, currentNeTarget => by
      rcases canonical.cubeTerminalOrBeforeFirst
          current before suffix shape with
        terminal | ⟨next, rest, suffixShape, nextFresh⟩
      · subst suffix
        simp at targetSuffix
      · subst suffix
        have nextNeTarget : next ≠ target := by
          intro equality
          subst next
          exact nextFresh
            (List.mem_append_left [current, current, current]
              targetBefore)
        have targetRest : target ∈ rest := by
          simpa [nextNeTarget, Ne.symm nextNeTarget] using targetSuffix
        by_cases nextThree : letters.count next = 3
        · obtain ⟨nextBefore, nextAfter, nextCubeShape⟩ :=
            canonical.cubeContiguous next nextThree
          have nextBeforeAbsent : next ∉ nextBefore :=
            canonical.cubePrefixAbsent nextCubeShape
          let currentPrefix :=
            before ++ [current, current, current]
          have currentShape :
              letters = currentPrefix ++ next :: rest := by
            simpa [currentPrefix, List.append_assoc] using shape
          have displayedNextShape :
              letters =
                nextBefore ++ next :: next :: next :: nextAfter := by
            simpa [List.append_assoc] using nextCubeShape
          obtain ⟨prefixEq, restEq⟩ :=
            firstOccurrenceSplit_unique next currentPrefix rest
              nextBefore (next :: next :: nextAfter) nextFresh
              nextBeforeAbsent
              (currentShape.symm.trans displayedNextShape)
          have recursiveShape :
              letters =
                currentPrefix ++ [next, next, next] ++ nextAfter := by
            calc
              letters =
                  nextBefore ++ [next, next, next] ++ nextAfter :=
                nextCubeShape
              _ = currentPrefix ++ [next, next, next] ++ nextAfter := by
                rw [← prefixEq]
          have targetNextAfter : target ∈ nextAfter := by
            rw [restEq] at targetRest
            simpa [nextNeTarget, Ne.symm nextNeTarget] using targetRest
          have targetCurrentPrefix : target ∈ currentPrefix := by
            exact List.mem_append_left [current, current, current]
              targetBefore
          obtain ⟨witness, middle, right, afterShape,
              witnessFresh, witnessSmall, targetRight⟩ :=
            existsSmallFirstAfterCubeBeforeRepeated canonical
              nextAfter next currentPrefix target recursiveShape
              targetCurrentPrefix targetNextAfter nextNeTarget
          refine ⟨witness, [next, next, next] ++ middle, right,
            ?_, ?_, witnessSmall, targetRight⟩
          · rw [restEq, afterShape]
            simp [List.append_assoc]
          · simpa [currentPrefix, List.append_assoc] using witnessFresh
        · have nextSmall : letters.count next ≤ 2 := by
            have nextBound := canonical.capThree next
            omega
          exact ⟨next, [], rest, by simp, by simpa using nextFresh,
            nextSmall, targetRest⟩
termination_by suffix => suffix.length
/- PROOF-SHAPE-FRAGMENT-BEGIN canonicalization_first_termination_chain -/
decreasing_by
  have restLength :
      rest.length = (next :: next :: nextAfter).length :=
    congrArg List.length restEq
  have suffixLength : suffix.length = (next :: rest).length :=
    congrArg List.length suffixShape
  calc
    nextAfter.length < (next :: next :: nextAfter).length := by
      simp only [List.length_cons]
      omega
    _ = rest.length := restLength.symm
    _ < (next :: rest).length := by simp
    _ = suffix.length := suffixLength.symm
/- PROOF-SHAPE-FRAGMENT-END canonicalization_first_termination_chain -/

/-- Starting from a canonical cube with a later count-three target, skip
adjacent cube successors.  A low-multiplicity first occurrence is found
before the target, unless condition VI makes the whole cube chain strictly
increasing from the starting letter to the target. -/
private theorem existsSmallBeforeTripleOrLt
    {letters : List Nat} (canonical : Proposition8ACanonical letters) :
    ∀ (suffix : List Nat) (current : Nat) (before : List Nat)
      (target : Nat),
      letters = before ++ [current, current, current] ++ suffix →
      target ∈ suffix →
      letters.count target = 3 →
      current ≠ target →
      (∃ next middle right,
        suffix = middle ++ next :: right ∧
        next ∉ before ++ [current, current, current] ++ middle ∧
        letters.count next ≤ 2 ∧
        target ∈ right) ∨
      current < target
  | suffix, current, before, target, shape,
      targetSuffix, targetThree, currentNeTarget => by
      rcases canonical.cubeTerminalOrBeforeFirst
          current before suffix shape with
        terminal | ⟨next, rest, suffixShape, nextFresh⟩
      · subst suffix
        simp at targetSuffix
      · subst suffix
        have nextNeCurrent : next ≠ current := by
          intro equality
          subst next
          exact nextFresh (by simp)
        by_cases nextThree : letters.count next = 3
        · obtain ⟨nextBefore, nextAfter, nextCubeShape⟩ :=
            canonical.cubeContiguous next nextThree
          have nextBeforeAbsent : next ∉ nextBefore :=
            canonical.cubePrefixAbsent nextCubeShape
          let currentPrefix :=
            before ++ [current, current, current]
          have currentShape :
              letters = currentPrefix ++ next :: rest := by
            simpa [currentPrefix, List.append_assoc] using shape
          have displayedNextShape :
              letters =
                nextBefore ++ next :: next :: next :: nextAfter := by
            simpa [List.append_assoc] using nextCubeShape
          obtain ⟨prefixEq, restEq⟩ :=
            firstOccurrenceSplit_unique next currentPrefix rest
              nextBefore (next :: next :: nextAfter) nextFresh
              nextBeforeAbsent
              (currentShape.symm.trans displayedNextShape)
          have recursiveShape :
              letters =
                currentPrefix ++ [next, next, next] ++ nextAfter := by
            calc
              letters =
                  nextBefore ++ [next, next, next] ++ nextAfter :=
                nextCubeShape
              _ = currentPrefix ++ [next, next, next] ++ nextAfter := by
                rw [← prefixEq]
          have adjacentShape :
              letters = before ++ [current, current, current] ++
                [next, next, next] ++ nextAfter := by
            simpa [currentPrefix, List.append_assoc] using recursiveShape
          have currentLtNext : current < next :=
            canonical.adjacentCubesOrdered current next before nextAfter
              (Ne.symm nextNeCurrent) adjacentShape
          by_cases nextEqTarget : next = target
          · subst next
            exact Or.inr currentLtNext
          · have targetRest : target ∈ rest := by
              simpa [nextEqTarget, Ne.symm nextEqTarget] using targetSuffix
            have targetNextAfter : target ∈ nextAfter := by
              rw [restEq] at targetRest
              simpa [nextEqTarget, Ne.symm nextEqTarget] using targetRest
            rcases existsSmallBeforeTripleOrLt canonical
                nextAfter next currentPrefix target recursiveShape
                targetNextAfter targetThree nextEqTarget with
              witness | nextLtTarget
            · obtain ⟨witness, middle, right, afterShape,
                  witnessFresh, witnessSmall, targetRight⟩ := witness
              refine Or.inl ⟨witness,
                [next, next, next] ++ middle, right,
                ?_, ?_, witnessSmall, targetRight⟩
              · rw [restEq, afterShape]
                simp [List.append_assoc]
              · simpa [currentPrefix, List.append_assoc] using
                  witnessFresh
            · exact Or.inr (Nat.lt_trans currentLtNext nextLtTarget)
        · have nextSmall : letters.count next ≤ 2 := by
            have nextBound := canonical.capThree next
            omega
          have nextNeTarget : next ≠ target := by
            intro equality
            subst next
            exact nextThree targetThree
          have targetRest : target ∈ rest := by
            simpa [nextNeTarget, Ne.symm nextNeTarget] using targetSuffix
          exact Or.inl ⟨next, [], rest, by simp,
            by simpa using nextFresh, nextSmall, targetRest⟩
termination_by suffix => suffix.length
/- PROOF-SHAPE-FRAGMENT-BEGIN canonicalization_second_termination_chain -/
decreasing_by
  have restLength :
      rest.length = (next :: next :: nextAfter).length :=
    congrArg List.length restEq
  have suffixLength : suffix.length = (next :: rest).length :=
    congrArg List.length suffixShape
  calc
    nextAfter.length < (next :: next :: nextAfter).length := by
      simp only [List.length_cons]
      omega
    _ = rest.length := restLength.symm
    _ < (next :: rest).length := by simp
    _ = suffix.length := suffixLength.symm
/- PROOF-SHAPE-FRAGMENT-END canonicalization_second_termination_chain -/

/-- If a twice-occurring letter straddles a canonical cube, conditions III--V
produce a low-multiplicity first occurrence separating the two.  The result
is phrased only with the public `S5_841` complete-precedence relation, which
is the interface used by the semantic exceptional-pair argument. -/
theorem straddledCubeWitness
    {letters : List Nat} (canonical : Proposition8ACanonical letters)
    {x y : Nat} (different : x ≠ y)
    (xTwo : letters.count x = 2)
    (yThree : letters.count y = 3)
    (notXY : ¬ S5_841.CompletePrecedenceList letters x y)
    (notYX : ¬ S5_841.CompletePrecedenceList letters y x) :
    ∃ z,
      x ≠ z ∧ y ≠ z ∧ letters.count z ≤ 2 ∧
      S5_841.CompletePrecedenceList letters y z ∧
      ¬ S5_841.CompletePrecedenceList letters x z := by
  obtain ⟨before, after, cubeShape⟩ :=
    canonical.cubeContiguous y yThree
  have yBeforeAbsent : y ∉ before :=
    canonical.cubePrefixAbsent cubeShape
  have yAfterAbsent : y ∉ after :=
    canonical.cubeSuffixAbsent cubeShape
  have xMember : x ∈ letters :=
    List.count_pos_iff.mp (by omega)
  have xBeforeOrAfter : x ∈ before ∨ x ∈ after := by
    rw [cubeShape] at xMember
    simpa [different, Ne.symm different] using xMember
  have xBefore : x ∈ before := by
    apply Decidable.byContradiction
    intro xBeforeAbsent
    have xAfter : x ∈ after :=
      xBeforeOrAfter.resolve_left xBeforeAbsent
    have xAbsentPrefix :
        x ∉ before ++ [y, y, y] := by
      simp [xBeforeAbsent, different, Ne.symm different]
    apply notYX
    refine ⟨Ne.symm different, ?_⟩
    rw [cubeShape]
    simpa [List.append_assoc] using
      precedenceScan_ordered_of_blocks (Ne.symm different)
        (before ++ [y, y, y]) after (by simp)
        xAbsentPrefix yAfterAbsent xAfter
  have xAfter : x ∈ after := by
    apply Decidable.byContradiction
    intro xAfterAbsent
    have xAbsentSuffix : x ∉ [y, y, y] ++ after := by
      simp [xAfterAbsent, different, Ne.symm different]
    apply notXY
    refine ⟨different, ?_⟩
    rw [cubeShape]
    simpa [List.append_assoc] using
      precedenceScan_ordered_of_blocks different before
        ([y, y, y] ++ after) xBefore yBeforeAbsent
        xAbsentSuffix (by simp)
  obtain ⟨z, middle, right, afterShape, zFresh, zSmall, xRight⟩ :=
    existsSmallFirstAfterCubeBeforeRepeated canonical
      after y before x cubeShape xBefore xAfter (Ne.symm different)
  have xNeZ : x ≠ z := by
    intro equality
    subst z
    exact zFresh
      (List.mem_append_left middle
        (List.mem_append_left [y, y, y] xBefore))
  have yNeZ : y ≠ z := by
    intro equality
    subst z
    exact zFresh (by simp)
  have yAbsentRight : y ∉ z :: right := by
    intro member
    exact yAfterAbsent <| by
      rw [afterShape]
      exact List.mem_append_right middle member
  have yz : S5_841.CompletePrecedenceList letters y z := by
    refine ⟨yNeZ, ?_⟩
    rw [cubeShape, afterShape]
    simpa [List.append_assoc] using
      precedenceScan_ordered_of_blocks yNeZ
        (before ++ [y, y, y] ++ middle) (z :: right)
        (by simp) zFresh yAbsentRight (by simp)
  have notXZ : ¬ S5_841.CompletePrecedenceList letters x z := by
    intro xz
    have violated :
        S5_841.precedenceScanList letters x z = .violated := by
      rw [cubeShape, afterShape]
      simpa [List.append_assoc] using
        precedenceScan_violated_of_inversion xNeZ
          (before ++ [y, y, y] ++ middle) right zFresh xRight
    exact precedenceState_violated_ne_ordered
      (violated.symm.trans xz.2)
  exact ⟨z, xNeZ, yNeZ, zSmall, yz, notXZ⟩

/-- For two count-three letters in complete-precedence order, conditions
III--VI either expose a low-multiplicity first occurrence before the second
cube, or force the two cube labels into the fixed natural-number order. -/
theorem orderedCubePairWitnessOrLt
    {letters : List Nat} (canonical : Proposition8ACanonical letters)
    {x y : Nat} (different : x ≠ y)
    (xThree : letters.count x = 3)
    (yThree : letters.count y = 3)
    (xy : S5_841.CompletePrecedenceList letters x y) :
    (∃ z,
      x ≠ z ∧ y ≠ z ∧ letters.count z ≤ 2 ∧
      S5_841.CompletePrecedenceList letters x z ∧
      ¬ S5_841.CompletePrecedenceList letters y z) ∨
    x < y := by
  obtain ⟨before, after, cubeShape⟩ :=
    canonical.cubeContiguous x xThree
  have xBeforeAbsent : x ∉ before :=
    canonical.cubePrefixAbsent cubeShape
  have xAfterAbsent : x ∉ after :=
    canonical.cubeSuffixAbsent cubeShape
  have yMember : y ∈ letters :=
    List.count_pos_iff.mp (by omega)
  have yBeforeOrAfter : y ∈ before ∨ y ∈ after := by
    rw [cubeShape] at yMember
    simpa [different, Ne.symm different] using yMember
  have yAfter : y ∈ after := by
    apply Decidable.byContradiction
    intro yAfterAbsent
    have yBefore : y ∈ before :=
      yBeforeOrAfter.resolve_right yAfterAbsent
    obtain ⟨firstBefore, firstAfter, beforeShape,
        yFirstBeforeAbsent⟩ :=
      existsFirstOccurrenceSplit y yBefore
    have violated :
        S5_841.precedenceScanList letters x y = .violated := by
      rw [cubeShape, beforeShape]
      simpa [List.append_assoc] using
        precedenceScan_violated_of_inversion different firstBefore
          (firstAfter ++ [x, x, x] ++ after)
          yFirstBeforeAbsent (by simp)
    exact precedenceState_violated_ne_ordered
      (violated.symm.trans xy.2)
  rcases existsSmallBeforeTripleOrLt canonical
      after x before y cubeShape yAfter yThree different with
    witness | ordered
  · obtain ⟨z, middle, right, afterShape,
        zFresh, zSmall, yRight⟩ := witness
    have xNeZ : x ≠ z := by
      intro equality
      subst z
      exact zFresh (by simp)
    have yNeZ : y ≠ z := by
      intro equality
      subst z
      omega
    have xAbsentRight : x ∉ z :: right := by
      intro member
      exact xAfterAbsent <| by
        rw [afterShape]
        exact List.mem_append_right middle member
    have xz : S5_841.CompletePrecedenceList letters x z := by
      refine ⟨xNeZ, ?_⟩
      rw [cubeShape, afterShape]
      simpa [List.append_assoc] using
        precedenceScan_ordered_of_blocks xNeZ
          (before ++ [x, x, x] ++ middle) (z :: right)
          (by simp) zFresh xAbsentRight (by simp)
    have notYZ : ¬ S5_841.CompletePrecedenceList letters y z := by
      intro yz
      have violated :
          S5_841.precedenceScanList letters y z = .violated := by
        rw [cubeShape, afterShape]
        simpa [List.append_assoc] using
          precedenceScan_violated_of_inversion yNeZ
            (before ++ [x, x, x] ++ middle) right zFresh yRight
      exact precedenceState_violated_ne_ordered
        (violated.symm.trans yz.2)
    exact Or.inl ⟨z, xNeZ, yNeZ, zSmall, xz, notYZ⟩
  · exact Or.inr ordered

end Proposition8ACanonical

/-!
## Post-cap gathering of all cubes

The recursion works from the right.  When the final letter occurs three
times, its two earlier copies are gathered to that final occurrence and the
new terminal cube is protected while the shorter prefix is normalized.
Otherwise the final singleton is protected.  This avoids any global claim
that an arbitrary later gathering preserves a previously displayed cube.
-/

private theorem existsAppendSingletonOfNeNil
    {alpha : Type u} :
    ∀ (items : List alpha), items ≠ [] →
      ∃ front last, items = front ++ [last]
  | [], nonempty => False.elim (nonempty rfl)
  | item :: rest, _ => by
      cases rest with
      | nil =>
          exact ⟨[], item, by simp⟩
      | cons next tail =>
          obtain ⟨front, last, shape⟩ :=
            existsAppendSingletonOfNeNil (next :: tail) (by simp)
          exact ⟨item :: front, last, by simp [shape]⟩

private theorem existsTwoOccurrenceSplit
    (letter : Nat) :
    ∀ {letters : List Nat},
      2 ≤ letters.count letter →
        ∃ before middle after,
          letters = before ++ letter :: middle ++ letter :: after
  | [], count => by
      simp at count
  | first :: rest, count => by
      by_cases equality : first = letter
      · subst first
        have restPositive : 0 < rest.count letter := by
          simp only [List.count_cons_self] at count
          omega
        have restMember : letter ∈ rest :=
          List.count_pos_iff.mp restPositive
        obtain ⟨middle, after, split⟩ :=
          List.mem_iff_append.mp restMember
        exact ⟨[], middle, after,
          by simp [split, List.append_assoc]⟩
      · have restCount : 2 ≤ rest.count letter := by
          simpa [equality] using count
        obtain ⟨before, middle, after, split⟩ :=
          existsTwoOccurrenceSplit letter restCount
        exact ⟨first :: before, middle, after,
          by simp [split, List.append_assoc]⟩

private theorem existsContiguousCubeReductionFuel :
    ∀ (fuel : Nat) (letters : List Nat),
      letters.length ≤ fuel →
      (∀ tested, letters.count tested ≤ 3) →
      ∃ normalized : List Nat,
        (∀ tested,
          normalized.count tested = letters.count tested) ∧
        TripleCubesContiguous normalized ∧
        ListDerives letters normalized
  | 0, letters, lengthBound, _bounded => by
      have lengthZero : letters.length = 0 := by omega
      have empty : letters = [] :=
        List.eq_nil_of_length_eq_zero lengthZero
      subst letters
      refine ⟨[], by simp, ?_, S5_107.ListDerives.refl (basis := basis) []⟩
      intro tested count
      simp at count
  | fuel + 1, letters, lengthBound, bounded => by
      by_cases empty : letters = []
      · subst letters
        refine ⟨[], by simp, ?_, S5_107.ListDerives.refl (basis := basis) []⟩
        intro tested count
        simp at count
      · obtain ⟨initial, final, shape⟩ :=
          existsAppendSingletonOfNeNil letters empty
        subst letters
        by_cases finalThree :
            (initial ++ [final]).count final = 3
        · have initialTwo : initial.count final = 2 := by
            have count := finalThree
            simp only [List.count_append, List.count_cons_self,
              List.count_nil] at count
            omega
          obtain ⟨before, middle, after, initialShape⟩ :=
            existsTwoOccurrenceSplit final (by omega :
              2 ≤ initial.count final)
          let remainder := before ++ middle ++ after
          let cube := [final, final, final]
          have exposedPermutation :
              (initial ++ [final]).Perm (remainder ++ cube) := by
            rw [List.perm_iff_count]
            intro tested
            rw [initialShape]
            by_cases equality : tested = final
            · subst tested
              simp [remainder, cube, List.count_append,
                Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
            · simp [remainder, cube, List.count_append, equality,
                Ne.symm equality, Nat.add_assoc, Nat.add_comm,
                Nat.add_left_comm]
          have remainderBound :
              ∀ tested, remainder.count tested ≤ 3 := by
            intro tested
            have targetBound :
                (remainder ++ cube).count tested ≤ 3 := by
              rw [← exposedPermutation.count tested]
              exact bounded tested
            simp only [List.count_append] at targetBound
            omega
          have remainderLength : remainder.length ≤ fuel := by
            rw [initialShape] at lengthBound
            simp only [List.length_append, List.length_cons,
              List.length_nil] at lengthBound
            simp only [remainder, List.length_append]
            omega
          obtain ⟨normalizedRemainder, recursiveCounts,
              recursiveCubes, recursiveDerivation⟩ :=
            existsContiguousCubeReductionFuel fuel remainder
              remainderLength remainderBound
          have normalizedCounts :
              ∀ tested,
                (normalizedRemainder ++ cube).count tested =
                  (initial ++ [final]).count tested := by
            intro tested
            calc
              (normalizedRemainder ++ cube).count tested =
                  (remainder ++ cube).count tested := by
                simp only [List.count_append]
                rw [recursiveCounts tested]
              _ = (initial ++ [final]).count tested :=
                (exposedPermutation.count tested).symm
          have normalizedCubes :
              TripleCubesContiguous (normalizedRemainder ++ cube) := by
            intro tested testedThree
            by_cases equality : tested = final
            · subst tested
              exact ⟨normalizedRemainder, [], by simp [cube]⟩
            · have remainderThree :
                  normalizedRemainder.count tested = 3 := by
                simpa [cube, List.count_append, equality,
                  Ne.symm equality] using testedThree
              obtain ⟨cubeBefore, cubeAfter, cubeShape⟩ :=
                recursiveCubes tested remainderThree
              refine ⟨cubeBefore, cubeAfter ++ cube, ?_⟩
              rw [cubeShape]
              simp [List.append_assoc]
          have gathered :
              ListDerives (initial ++ [final])
                (remainder ++ cube) := by
            rw [initialShape]
            simpa [remainder, cube, List.append_assoc] using
              listDerivesGatherThreeToLast final before middle after []
          have normalizedRemainderDerivation :
              ListDerives (remainder ++ cube)
                (normalizedRemainder ++ cube) :=
            recursiveDerivation.append cube
          exact ⟨normalizedRemainder ++ cube, normalizedCounts,
            normalizedCubes,
            gathered.trans normalizedRemainderDerivation⟩
        · have initialBound :
              ∀ tested, initial.count tested ≤ 3 := by
            intro tested
            have wholeBound := bounded tested
            simp only [List.count_append] at wholeBound
            omega
          have initialLength : initial.length ≤ fuel := by
            simp only [List.length_append, List.length_cons,
              List.length_nil] at lengthBound
            omega
          obtain ⟨normalizedInitial, recursiveCounts,
              recursiveCubes, recursiveDerivation⟩ :=
            existsContiguousCubeReductionFuel fuel initial
              initialLength initialBound
          have normalizedCounts :
              ∀ tested,
                (normalizedInitial ++ [final]).count tested =
                  (initial ++ [final]).count tested := by
            intro tested
            simp only [List.count_append]
            rw [recursiveCounts tested]
          have normalizedCubes :
              TripleCubesContiguous (normalizedInitial ++ [final]) := by
            intro tested testedThree
            by_cases equality : tested = final
            · subst tested
              have sourceThree :
                  (initial ++ [final]).count final = 3 :=
                (normalizedCounts final).symm.trans testedThree
              exact False.elim (finalThree sourceThree)
            · have initialThree :
                  normalizedInitial.count tested = 3 := by
                simpa [List.count_append, equality,
                  Ne.symm equality] using testedThree
              obtain ⟨cubeBefore, cubeAfter, cubeShape⟩ :=
                recursiveCubes tested initialThree
              refine ⟨cubeBefore, cubeAfter ++ [final], ?_⟩
              rw [cubeShape]
              simp [List.append_assoc]
          exact ⟨normalizedInitial ++ [final], normalizedCounts,
            normalizedCubes, recursiveDerivation.append [final]⟩

/-- A cap-three list derives, without changing any multiplicity, to a list
satisfying condition IV. -/
theorem existsContiguousCubeReduction
    (letters : List Nat)
    (bounded : ∀ tested, letters.count tested ≤ 3) :
    ∃ normalized : List Nat,
      (∀ tested, normalized.count tested ≤ 3) ∧
      (∀ tested,
        normalized.count tested = letters.count tested) ∧
      TripleCubesContiguous normalized ∧
      S5_107.ListDerives basis letters normalized := by
  obtain ⟨normalized, counts, cubes, derivation⟩ :=
    existsContiguousCubeReductionFuel letters.length letters
      (by simp) bounded
  refine ⟨normalized, ?_, counts, cubes, derivation⟩
  intro tested
  rw [counts tested]
  exact bounded tested

/-- Unrestricted conditions III--IV normalization, composed with the exact
cap-three pass. -/
theorem existsCapThreeContiguousCubeReduction
    (letters : List Nat) :
    ∃ normalized : List Nat,
      (∀ tested, normalized.count tested ≤ 3) ∧
      (∀ tested,
        normalized.count tested = min (letters.count tested) 3) ∧
      TripleCubesContiguous normalized ∧
      S5_107.ListDerives basis letters normalized := by
  obtain ⟨capped, cappedBound, cappedCounts, capDerivation⟩ :=
    existsCapThreeReduction letters
  obtain ⟨normalized, normalizedBound, gatheredCounts,
      cubes, gatherDerivation⟩ :=
    existsContiguousCubeReduction capped cappedBound
  refine ⟨normalized, normalizedBound, ?_, cubes,
    capDerivation.trans gatherDerivation⟩
  intro tested
  exact (gatheredCounts tested).trans (cappedCounts tested)

end SemigroupBasis.CoRoots.Order6LeeLiProposition8A
