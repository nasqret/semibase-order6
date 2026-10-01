import SemigroupBasis.CoRoots.Order6LeeZhangCondition4Derivations

/-!
# Lee--Zhang Condition 4: residual normalization

After the first repeated letter has been exposed as a square, the Condition-4
laws make the remaining tail commutative.  The power law deletes every
additional copy of the marker and caps every other multiplicity at two.  This
module implements that reduction and its deterministic sorted representative.
-/

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6LeeZhangCondition4

open SemigroupBasis

private abbrev ListDerives : List Nat → List Nat → Prop :=
  SemigroupBasis.CoRoots.S5_107.ListDerives basis

/-- No marker copies remain after the displayed marker square; every other
letter retains at most two copies. -/
def residualLimit (marker letter : Nat) : Nat :=
  if letter = marker then 0 else 2

/-- Right-to-left multiplicity reduction for the post-marker tail. -/
def residualReduce (marker : Nat) : List Nat → List Nat
  | [] => []
  | letter :: rest =>
      let reduced := residualReduce marker rest
      if reduced.count letter < residualLimit marker letter then
        letter :: reduced
      else
        reduced

theorem count_residualReduce
    (marker tested : Nat) (letters : List Nat) :
    (residualReduce marker letters).count tested =
      min (letters.count tested) (residualLimit marker tested) := by
  induction letters with
  | nil =>
      simp [residualReduce, residualLimit]
  | cons letter rest inductionHypothesis =>
      simp only [residualReduce]
      split <;> rename_i countBound
      · by_cases equal : tested = letter
        · subst tested
          rw [List.count_cons_self, List.count_cons_self,
            inductionHypothesis]
          rw [inductionHypothesis] at countBound
          by_cases markerEqual : letter = marker <;>
            simp [residualLimit, markerEqual] at countBound ⊢ <;> omega
        · rw [List.count_cons_of_ne (Ne.symm equal),
            List.count_cons_of_ne (Ne.symm equal), inductionHypothesis]
      · by_cases equal : tested = letter
        · subst tested
          rw [List.count_cons_self, inductionHypothesis]
          rw [inductionHypothesis] at countBound
          by_cases markerEqual : letter = marker <;>
            simp [residualLimit, markerEqual] at countBound ⊢ <;> omega
        · rw [List.count_cons_of_ne (Ne.symm equal),
            inductionHypothesis]

private theorem listDerivesTailTripleContraction
    (marker letter : Nat) (suffix : List Nat) :
    ListDerives
      ([marker, marker, letter, letter, letter] ++ suffix)
      ([marker, marker, letter, letter] ++ suffix) := by
  have contracted :=
    SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
      (derivesTripleContraction (Word.singleton letter))
  simpa [Word.singleton, Word.toList_append, List.append_assoc] using
    (contracted.prepend [marker, marker]).append suffix

/-- Delete one residual copy of the pivot, whose two retained copies are the
displayed marker square. -/
private theorem listDerivesDeleteResidualMarker
    (marker : Nat) (pre rest : List Nat) :
    ListDerives
      ([marker, marker] ++ pre ++ marker :: rest)
      ([marker, marker] ++ pre ++ rest) := by
  have exposePermutation :
      (pre ++ marker :: rest).Perm
        (marker :: rest ++ pre) := by
    simpa [List.append_assoc] using
      (List.perm_append_comm (l₁ := pre) (l₂ := marker :: rest))
  have expose :=
    listDerivesSquareTailPermutation marker exposePermutation [] []
  have contract :=
    (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
      (derivesTripleContraction (Word.singleton marker))).append
        (rest ++ pre)
  have restorePermutation :
      (rest ++ pre).Perm (pre ++ rest) :=
    List.perm_append_comm (l₁ := rest) (l₂ := pre)
  have restore :=
    listDerivesSquareTailPermutation marker restorePermutation [] []
  simp [List.append_assoc] at expose
  simp [Word.singleton, Word.toList_append, List.append_assoc] at contract
  simp [List.append_assoc] at restore
  simpa using expose.trans (contract.trans restore)

/-- Delete the third post-marker copy of a non-marker letter. -/
private theorem listDerivesDeleteThirdResidualCopy
    (marker letter : Nat) (pre rest : List Nat)
    (count : rest.count letter = 2) :
    ListDerives
      ([marker, marker] ++ pre ++ letter :: rest)
      ([marker, marker] ++ pre ++ rest) := by
  let remainder := (rest.erase letter).erase letter
  have sourcePermutation :
      (pre ++ letter :: rest).Perm
        (letter :: letter :: letter :: pre ++ remainder) := by
    rw [List.perm_iff_count]
    intro tested
    simp only [List.count_append]
    by_cases equal : tested = letter
    · subst tested
      simp only [List.count_cons_self]
      have firstErase : (rest.erase letter).count letter = 1 := by
        rw [List.count_erase_self, count]
      have secondErase :
          ((rest.erase letter).erase letter).count letter = 0 := by
        rw [List.count_erase_self, firstErase]
      simp only [remainder, secondErase, count]
    · simp only [List.count_cons_of_ne (Ne.symm equal),
        List.count_erase_of_ne equal, remainder]
  have targetPermutation :
      (letter :: letter :: pre ++ remainder).Perm
        (pre ++ rest) := by
    rw [List.perm_iff_count]
    intro tested
    simp only [List.count_append]
    by_cases equal : tested = letter
    · subst tested
      simp only [List.count_cons_self]
      have firstErase : (rest.erase letter).count letter = 1 := by
        rw [List.count_erase_self, count]
      have secondErase :
          ((rest.erase letter).erase letter).count letter = 0 := by
        rw [List.count_erase_self, firstErase]
      simp only [remainder, secondErase, count]
    · simp only [List.count_cons_of_ne (Ne.symm equal),
        List.count_erase_of_ne equal, remainder]
  have expose :=
    listDerivesSquareTailPermutation marker sourcePermutation [] []
  have contract :=
    listDerivesTailTripleContraction marker letter (pre ++ remainder)
  have restore :=
    listDerivesSquareTailPermutation marker targetPermutation [] []
  simp [List.append_assoc] at expose
  simp [List.append_assoc] at contract
  simp [List.append_assoc] at restore
  simpa using expose.trans (contract.trans restore)

/-- Reduce a selected suffix while retaining an already-normalized prefix
after the marker square. -/
theorem listDerivesResidualReduce :
    ∀ (marker : Nat) (pre letters : List Nat),
      ListDerives
        ([marker, marker] ++ pre ++ letters)
        ([marker, marker] ++ pre ++ residualReduce marker letters)
  | marker, pre, [] => by
      exact SemigroupBasis.CoRoots.S5_107.ListDerives.refl _
  | marker, pre, letter :: rest => by
      have normalizeRest :=
        listDerivesResidualReduce marker (pre ++ [letter]) rest
      let reduced := residualReduce marker rest
      have firstStep :
          ListDerives
            ([marker, marker] ++ pre ++ letter :: rest)
            ([marker, marker] ++ pre ++ letter :: reduced) := by
        simpa [reduced, List.append_assoc] using normalizeRest
      by_cases countBound :
          reduced.count letter < residualLimit marker letter
      · have reductionEquation :
            residualReduce marker (letter :: rest) =
              letter :: reduced := by
          simp [residualReduce, reduced, countBound]
        rw [reductionEquation]
        exact firstStep
      · have countLe :
            reduced.count letter ≤ residualLimit marker letter := by
          rw [show reduced = residualReduce marker rest by rfl,
            count_residualReduce]
          exact Nat.min_le_right _ _
        have countEq :
            reduced.count letter = residualLimit marker letter := by
          omega
        have reductionEquation :
            residualReduce marker (letter :: rest) = reduced := by
          simp [residualReduce, reduced, countBound]
        rw [reductionEquation]
        by_cases isMarker : letter = marker
        · subst letter
          exact firstStep.trans
            (listDerivesDeleteResidualMarker marker pre reduced)
        · have twoCopies : reduced.count letter = 2 := by
            simpa [residualLimit, isMarker] using countEq
          exact firstStep.trans
            (listDerivesDeleteThirdResidualCopy
              marker letter pre reduced twoCopies)
termination_by
  _ pre letters => letters.length

/-- Deterministic ascending representative of the reduced residual tail. -/
def residualNormal (marker : Nat) (letters : List Nat) : List Nat :=
  (residualReduce marker letters).mergeSort
    (fun left right : Nat => decide (left ≤ right))

theorem residualNormal_perm (marker : Nat) (letters : List Nat) :
    (residualNormal marker letters).Perm
      (residualReduce marker letters) := by
  exact List.mergeSort_perm _ _

/-- Normalize and sort the complete tail following a displayed marker square. -/
theorem listDerivesResidualNormal
    (marker : Nat) (letters : List Nat) :
    ListDerives
      ([marker, marker] ++ letters)
      ([marker, marker] ++ residualNormal marker letters) := by
  have reduced := listDerivesResidualReduce marker [] letters
  have sorted :=
    listDerivesSquareTailPermutation marker
      (residualNormal_perm marker letters).symm [] []
  simp [List.append_assoc] at reduced
  simp [residualNormal, List.append_assoc] at sorted
  simpa using reduced.trans sorted

/-! ## Simple-head branch -/

/-- After a protected simple head and second letter, retain one further copy
of the second letter and at most two copies of every other tail letter.  The
head itself is absent from the tail at the only call site. -/
def simpleResidualLimit (second letter : Nat) : Nat :=
  if letter = second then 1 else 2

def simpleResidualReduce (second : Nat) : List Nat → List Nat
  | [] => []
  | letter :: rest =>
      let reduced := simpleResidualReduce second rest
      if reduced.count letter < simpleResidualLimit second letter then
        letter :: reduced
      else
        reduced

theorem count_simpleResidualReduce
    (second tested : Nat) (letters : List Nat) :
    (simpleResidualReduce second letters).count tested =
      min (letters.count tested) (simpleResidualLimit second tested) := by
  induction letters with
  | nil =>
      simp [simpleResidualReduce, simpleResidualLimit]
  | cons letter rest inductionHypothesis =>
      simp only [simpleResidualReduce]
      split <;> rename_i countBound
      · by_cases equal : tested = letter
        · subst tested
          rw [List.count_cons_self, List.count_cons_self,
            inductionHypothesis]
          rw [inductionHypothesis] at countBound
          by_cases secondEqual : letter = second <;>
            simp [simpleResidualLimit, secondEqual] at countBound ⊢ <;>
            omega
        · rw [List.count_cons_of_ne (Ne.symm equal),
            List.count_cons_of_ne (Ne.symm equal), inductionHypothesis]
      · by_cases equal : tested = letter
        · subst tested
          rw [List.count_cons_self, inductionHypothesis]
          rw [inductionHypothesis] at countBound
          by_cases secondEqual : letter = second <;>
            simp [simpleResidualLimit, secondEqual] at countBound ⊢ <;>
            omega
        · rw [List.count_cons_of_ne (Ne.symm equal),
            inductionHypothesis]

private theorem listDerivesTripleContractionAfterTwo
    (first second letter : Nat) (suffix : List Nat) :
    ListDerives
      ([first, second, letter, letter, letter] ++ suffix)
      ([first, second, letter, letter] ++ suffix) := by
  have contracted :=
    SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
      (derivesTripleContraction (Word.singleton letter))
  simpa [Word.singleton, Word.toList_append, List.append_assoc] using
    (contracted.prepend [first, second]).append suffix

/-- Contract three copies of the protected second letter.  Here the displayed
second position is one of the three copies, so only the first letter remains
outside the contracted block. -/
private theorem listDerivesProtectedSecondContraction
    (first second : Nat) (suffix : List Nat) :
    ListDerives
      ([first, second, second, second] ++ suffix)
      ([first, second, second] ++ suffix) := by
  have contracted :=
    SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
      (derivesTripleContraction (Word.singleton second))
  simpa [Word.singleton, Word.toList_append, List.append_assoc] using
    (contracted.prepend [first]).append suffix

/-- Delete a second residual occurrence of the protected second letter.  Its
displayed occurrence supplies the third copy needed by the power law. -/
private theorem listDerivesDeleteSecondResidualExcess
    (first second : Nat) (pre rest : List Nat)
    (count : rest.count second = 1) :
    ListDerives
      ([first, second] ++ pre ++ second :: rest)
      ([first, second] ++ pre ++ rest) := by
  let remainder := rest.erase second
  have sourcePermutation :
      (pre ++ second :: rest).Perm
        (second :: second :: pre ++ remainder) := by
    rw [List.perm_iff_count]
    intro tested
    simp only [List.count_append]
    by_cases equal : tested = second
    · subst tested
      simp only [List.count_cons_self]
      have erasedCount : (rest.erase second).count second = 0 := by
        rw [List.count_erase_self, count]
      simp only [remainder, erasedCount, count]
    · simp only [List.count_cons_of_ne (Ne.symm equal),
        List.count_erase_of_ne equal, remainder]
  have targetPermutation :
      (second :: pre ++ remainder).Perm
        (pre ++ rest) := by
    rw [List.perm_iff_count]
    intro tested
    simp only [List.count_append]
    by_cases equal : tested = second
    · subst tested
      simp only [List.count_cons_self]
      have erasedCount : (rest.erase second).count second = 0 := by
        rw [List.count_erase_self, count]
      simp only [remainder, erasedCount, count]
    · simp only [List.count_cons_of_ne (Ne.symm equal),
        List.count_erase_of_ne equal, remainder]
  have expose :=
    listDerivesTailPermutationAfterTwo
      first second sourcePermutation [] []
  have contract :=
    listDerivesProtectedSecondContraction
      first second (pre ++ remainder)
  have restore :=
    listDerivesTailPermutationAfterTwo
      first second targetPermutation [] []
  simp [List.append_assoc] at expose
  simp [List.append_assoc] at contract
  simp [List.append_assoc] at restore
  simpa using expose.trans (contract.trans restore)

/-- Delete the third retained copy of any unprotected tail letter. -/
private theorem listDerivesDeleteThirdAfterTwo
    (first second letter : Nat) (pre rest : List Nat)
    (count : rest.count letter = 2) :
    ListDerives
      ([first, second] ++ pre ++ letter :: rest)
      ([first, second] ++ pre ++ rest) := by
  let remainder := (rest.erase letter).erase letter
  have sourcePermutation :
      (pre ++ letter :: rest).Perm
        (letter :: letter :: letter :: pre ++ remainder) := by
    rw [List.perm_iff_count]
    intro tested
    simp only [List.count_append]
    by_cases equal : tested = letter
    · subst tested
      simp only [List.count_cons_self]
      have firstErase : (rest.erase letter).count letter = 1 := by
        rw [List.count_erase_self, count]
      have secondErase :
          ((rest.erase letter).erase letter).count letter = 0 := by
        rw [List.count_erase_self, firstErase]
      simp only [remainder, secondErase, count]
    · simp only [List.count_cons_of_ne (Ne.symm equal),
        List.count_erase_of_ne equal, remainder]
  have targetPermutation :
      (letter :: letter :: pre ++ remainder).Perm
        (pre ++ rest) := by
    rw [List.perm_iff_count]
    intro tested
    simp only [List.count_append]
    by_cases equal : tested = letter
    · subst tested
      simp only [List.count_cons_self]
      have firstErase : (rest.erase letter).count letter = 1 := by
        rw [List.count_erase_self, count]
      have secondErase :
          ((rest.erase letter).erase letter).count letter = 0 := by
        rw [List.count_erase_self, firstErase]
      simp only [remainder, secondErase, count]
    · simp only [List.count_cons_of_ne (Ne.symm equal),
        List.count_erase_of_ne equal, remainder]
  have expose :=
    listDerivesTailPermutationAfterTwo
      first second sourcePermutation [] []
  have contract :=
    listDerivesTripleContractionAfterTwo
      first second letter (pre ++ remainder)
  have restore :=
    listDerivesTailPermutationAfterTwo
      first second targetPermutation [] []
  simp [List.append_assoc] at expose
  simp [List.append_assoc] at contract
  simp [List.append_assoc] at restore
  simpa using expose.trans (contract.trans restore)

/-- Reduce the tail after two protected initial letters. -/
theorem listDerivesSimpleResidualReduce :
    ∀ (first second : Nat) (pre letters : List Nat),
      ListDerives
        ([first, second] ++ pre ++ letters)
        ([first, second] ++ pre ++
          simpleResidualReduce second letters)
  | first, second, pre, [] => by
      exact SemigroupBasis.CoRoots.S5_107.ListDerives.refl _
  | first, second, pre, letter :: rest => by
      have normalizeRest :=
        listDerivesSimpleResidualReduce
          first second (pre ++ [letter]) rest
      let reduced := simpleResidualReduce second rest
      have firstStep :
          ListDerives
            ([first, second] ++ pre ++ letter :: rest)
            ([first, second] ++ pre ++ letter :: reduced) := by
        simpa [reduced, List.append_assoc] using normalizeRest
      by_cases countBound :
          reduced.count letter < simpleResidualLimit second letter
      · have reductionEquation :
            simpleResidualReduce second (letter :: rest) =
              letter :: reduced := by
          simp [simpleResidualReduce, reduced, countBound]
        rw [reductionEquation]
        exact firstStep
      · have countLe :
            reduced.count letter ≤
              simpleResidualLimit second letter := by
          rw [show reduced = simpleResidualReduce second rest by rfl,
            count_simpleResidualReduce]
          exact Nat.min_le_right _ _
        have countEq :
            reduced.count letter =
              simpleResidualLimit second letter := by
          omega
        have reductionEquation :
            simpleResidualReduce second (letter :: rest) = reduced := by
          simp [simpleResidualReduce, reduced, countBound]
        rw [reductionEquation]
        by_cases isSecond : letter = second
        · subst letter
          have oneCopy : reduced.count second = 1 := by
            simpa [simpleResidualLimit] using countEq
          exact firstStep.trans
            (listDerivesDeleteSecondResidualExcess
              first second pre reduced oneCopy)
        · have twoCopies : reduced.count letter = 2 := by
            simpa [simpleResidualLimit, isSecond] using countEq
          exact firstStep.trans
            (listDerivesDeleteThirdAfterTwo
              first second letter pre reduced twoCopies)
termination_by
  _ _ pre letters => letters.length

def simpleResidualNormal (second : Nat) (letters : List Nat) : List Nat :=
  (simpleResidualReduce second letters).mergeSort
    (fun left right : Nat => decide (left ≤ right))

theorem simpleResidualNormal_perm (second : Nat) (letters : List Nat) :
    (simpleResidualNormal second letters).Perm
      (simpleResidualReduce second letters) := by
  exact List.mergeSort_perm _ _

theorem listDerivesSimpleResidualNormal
    (first second : Nat) (letters : List Nat) :
    ListDerives
      ([first, second] ++ letters)
      ([first, second] ++ simpleResidualNormal second letters) := by
  have reduced :=
    listDerivesSimpleResidualReduce first second [] letters
  have sorted :=
    listDerivesTailPermutationAfterTwo first second
      (simpleResidualNormal_perm second letters).symm [] []
  simp [List.append_assoc] at reduced
  simp [simpleResidualNormal, List.append_assoc] at sorted
  simpa using reduced.trans sorted

/-! ## Uniqueness of the sorted representatives -/

private theorem natMergeSort_pairwise (letters : List Nat) :
    (letters.mergeSort
      (fun left right : Nat => decide (left ≤ right))).Pairwise
        (fun left right => left ≤ right) := by
  have transitive :
      ∀ left middle right : Nat,
        decide (left ≤ middle) = true →
        decide (middle ≤ right) = true →
        decide (left ≤ right) = true := by
    intro left middle right first second
    exact decide_eq_true
      (Nat.le_trans (of_decide_eq_true first)
        (of_decide_eq_true second))
  have total :
      ∀ left right : Nat,
        (decide (left ≤ right) || decide (right ≤ left)) = true := by
    intro left right
    rcases Nat.le_total left right with first | second
    · simp [first]
    · simp [second]
  exact
    (List.pairwise_mergeSort transitive total letters).imp
      (fun relation => of_decide_eq_true relation)

theorem residualNormal_eq_of_cappedCounts
    (marker : Nat) (left right : List Nat)
    (counts : ∀ letter,
      min (left.count letter) (residualLimit marker letter) =
        min (right.count letter) (residualLimit marker letter)) :
    residualNormal marker left = residualNormal marker right := by
  have permutation :
      (residualNormal marker left).Perm
        (residualNormal marker right) := by
    rw [List.perm_iff_count]
    intro letter
    rw [(List.perm_iff_count.mp
          (residualNormal_perm marker left)) letter,
      (List.perm_iff_count.mp
          (residualNormal_perm marker right)) letter,
      count_residualReduce, count_residualReduce]
    exact counts letter
  exact List.Perm.eq_of_pairwise
    (fun _ _ _ _ leftLe rightLe =>
      Nat.le_antisymm leftLe rightLe)
    (by simpa [residualNormal] using
      natMergeSort_pairwise (residualReduce marker left))
    (by simpa [residualNormal] using
      natMergeSort_pairwise (residualReduce marker right))
    permutation

theorem simpleResidualNormal_eq_of_cappedCounts
    (second : Nat) (left right : List Nat)
    (counts : ∀ letter,
      min (left.count letter) (simpleResidualLimit second letter) =
        min (right.count letter) (simpleResidualLimit second letter)) :
    simpleResidualNormal second left =
      simpleResidualNormal second right := by
  have permutation :
      (simpleResidualNormal second left).Perm
        (simpleResidualNormal second right) := by
    rw [List.perm_iff_count]
    intro letter
    rw [(List.perm_iff_count.mp
          (simpleResidualNormal_perm second left)) letter,
      (List.perm_iff_count.mp
          (simpleResidualNormal_perm second right)) letter,
      count_simpleResidualReduce, count_simpleResidualReduce]
    exact counts letter
  exact List.Perm.eq_of_pairwise
    (fun _ _ _ _ leftLe rightLe =>
      Nat.le_antisymm leftLe rightLe)
    (by simpa [simpleResidualNormal] using
      natMergeSort_pairwise (simpleResidualReduce second left))
    (by simpa [simpleResidualNormal] using
      natMergeSort_pairwise (simpleResidualReduce second right))
    permutation

end SemigroupBasis.CoRoots.Order6LeeZhangCondition4
