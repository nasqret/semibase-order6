import SemigroupBasis.CoRoots.Order6S6_15646Normalization
import SemigroupBasis.CoRoots.S5_1099Semantics
import SemigroupBasis.Opposite
import SemigroupBasis.Transfer

namespace SemigroupBasis.CoRoots.Order6FennemoreR3Band

open SemigroupBasis
open SemigroupBasis.Examples

/-- The nonidentity ideal is exactly the compiled `S5_1099` separator. -/
def s5_1099Embedding :
    Embedding
      SemigroupBasis.CoRoots.S5_1099.table.semigroup
      table.semigroup where
  toFun := fun value =>
    if value.val = 3 then (4 : Fin 6)
    else if value.val = 4 then (5 : Fin 6)
    else ⟨value.val, Nat.lt_trans value.isLt (by decide)⟩
  injective := by
    intro left right
    revert left right
    decide
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide

def one : Fin 6 := 3

@[simp]
theorem one_mul (value : Fin 6) : mul one value = value := by
  revert value
  decide

@[simp]
theorem mul_one (value : Fin 6) : mul value one = value := by
  revert value
  decide

/-- Zero-based opposite-`S3_16` embedding `[1, 3, 4]`. This separator
detects the last-occurrence sequence without asserting that the full
six-element table is self-dual. -/
def lastOccurrenceEmbedding :
    Embedding
      leftRegularBandThree.semigroup.opposite table.semigroup where
  toFun := fun value =>
    if value.val = 0 then (1 : Fin 6)
    else if value.val = 1 then (3 : Fin 6)
    else (4 : Fin 6)
  injective := by
    intro left right
    revert left right
    decide
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide

theorem valid_firstOccurrenceSequence_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    firstOccurrenceSequence identity.lhs.toList =
      firstOccurrenceSequence identity.rhs.toList :=
  SemigroupBasis.CoRoots.S5_1099.valid_firstOccurrenceSequence_eq
    identity (s5_1099Embedding.pullback_identity identity valid)

theorem valid_lastOccurrenceSequence_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    r3LastOccurrenceSequence identity.lhs.toList =
      r3LastOccurrenceSequence identity.rhs.toList := by
  have validRight :=
    lastOccurrenceEmbedding.pullback_identity identity valid
  have validReversed :
      identity.reversed.SatisfiedBy leftRegularBandThree.semigroup :=
    (Identity.satisfiedBy_opposite_iff_reversed
      identity leftRegularBandThree.semigroup).mp validRight
  have firstReversed :=
    SemigroupBasis.CoRoots.S5_345Factors.leftRegularBandThreeValid_firstOccurrenceSequence_eq
      identity.reversed validReversed
  have reversedEqual := congrArg List.reverse firstReversed
  simpa [Identity.reversed, r3LastOccurrenceSequence] using reversedEqual

private theorem firstOccurrenceSequence_append_singleton
    (selected : Nat) :
    ∀ letters : List Nat,
      firstOccurrenceSequence (letters ++ [selected]) =
        if selected ∈ letters then
          firstOccurrenceSequence letters
        else
          firstOccurrenceSequence letters ++ [selected]
  | [] => by simp [firstOccurrenceSequence]
  | letter :: rest => by
      have induction :=
        firstOccurrenceSequence_append_singleton selected rest
      by_cases equal : letter = selected
      · subst letter
        by_cases member : selected ∈ rest <;>
          simp [firstOccurrenceSequence, induction, member,
            List.filter_append]
      · have reverseEqual : selected ≠ letter := Ne.symm equal
        by_cases member : selected ∈ rest <;>
          simp [firstOccurrenceSequence, induction, equal, reverseEqual,
            member, List.filter_append]

private theorem firstOccurrenceSequence_append_of_subset :
    ∀ (right left : List Nat),
      (∀ letter, letter ∈ right → letter ∈ left) →
      firstOccurrenceSequence (left ++ right) =
        firstOccurrenceSequence left
  | [], left, _ => by simp
  | letter :: rest, left, subset => by
      have letterMember : letter ∈ left :=
        subset letter (List.Mem.head rest)
      have restSubset :
          ∀ tested, tested ∈ rest → tested ∈ left ++ [letter] := by
        intro tested member
        exact List.mem_append_left [letter]
          (subset tested (List.Mem.tail letter member))
      calc
        firstOccurrenceSequence (left ++ letter :: rest) =
            firstOccurrenceSequence ((left ++ [letter]) ++ rest) := by
          simp [List.append_assoc]
        _ = firstOccurrenceSequence (left ++ [letter]) :=
          firstOccurrenceSequence_append_of_subset rest
            (left ++ [letter]) restSubset
        _ = firstOccurrenceSequence left := by
          rw [firstOccurrenceSequence_append_singleton,
            if_pos letterMember]

theorem firstOccurrenceSequence_eq_of_r3Split
    {letters stem : List Nat} {pivot : Nat} {tail : List Nat}
    (split : r3Split letters = some (stem, pivot, tail)) :
    firstOccurrenceSequence letters =
      firstOccurrenceSequence stem ++ [pivot] := by
  have spec := r3Split_some_spec split
  have tailSubset :
      ∀ letter, letter ∈ tail → letter ∈ stem ++ [pivot] := by
    intro letter member
    rcases spec.tailContent letter member with
      impossible | prefixMember | pivotEqual
    · simp at impossible
    · exact List.mem_append_left [pivot] prefixMember
    · simp [pivotEqual]
  calc
    firstOccurrenceSequence letters =
        firstOccurrenceSequence ((stem ++ [pivot]) ++ tail) := by
      rw [spec.shape]
      simp [List.append_assoc]
    _ = firstOccurrenceSequence (stem ++ [pivot]) :=
      firstOccurrenceSequence_append_of_subset tail
        (stem ++ [pivot]) tailSubset
    _ = firstOccurrenceSequence stem ++ [pivot] := by
      rw [firstOccurrenceSequence_append_singleton,
        if_neg spec.pivotFreshPrefix]

def evalList (valuation : Nat → Fin 6) (letters : List Nat) : Fin 6 :=
  letters.foldl
    (fun current letter => mul current (valuation letter)) one

private theorem evalList_toList
    (valuation : Nat → Fin 6) (word : Word Nat) :
    evalList valuation word.toList =
      table.semigroup.eval valuation word := by
  cases word with
  | mk head tail =>
      simp only [evalList, Word.toList, List.foldl_cons, Semigroup.eval]
      rw [one_mul]
      rfl

def pivotValuation
    (pivot : Nat) (marker : Fin 6) (valuation : Nat → Fin 6) :
    Nat → Fin 6 :=
  fun letter => if letter = pivot then marker else valuation letter

private theorem fold_pivotValuation_of_not_mem
    (pivot : Nat) (marker : Fin 6) (valuation : Nat → Fin 6) :
    ∀ (letters : List Nat) (initial : Fin 6),
      pivot ∉ letters →
      letters.foldl
          (fun current letter =>
            mul current (pivotValuation pivot marker valuation letter))
          initial =
        letters.foldl
          (fun current letter => mul current (valuation letter)) initial
  | [], initial, _ => rfl
  | letter :: rest, initial, absent => by
      have letterDifferent : letter ≠ pivot := by
        intro equal
        exact absent (by simp [equal])
      have restAbsent : pivot ∉ rest := by
        intro member
        exact absent (List.Mem.tail letter member)
      simp only [List.foldl_cons]
      rw [fold_pivotValuation_of_not_mem
        pivot marker valuation rest _ restAbsent]
      simp [pivotValuation, letterDifferent]

private def IsLeftZero (value : Fin 6) : Prop :=
  ∀ right, mul value right = value

private theorem markerProduct_leftZero
    (state marker : Fin 6)
    (markerChoice : marker = 0 ∨ marker = 2 ∨ marker = 5) :
    IsLeftZero (mul state marker) := by
  rcases markerChoice with rfl | rfl | rfl
  all_goals
    intro right
    revert state right
    decide

private theorem fold_leftZero
    (valuation : Nat → Fin 6) (state : Fin 6)
    (leftZero : IsLeftZero state) :
    ∀ letters : List Nat,
      letters.foldl
          (fun current letter => mul current (valuation letter)) state = state
  | [] => rfl
  | letter :: rest => by
      simp only [List.foldl_cons]
      rw [leftZero]
      exact fold_leftZero valuation state leftZero rest

private theorem evalList_pivot_marker
    (stem : List Nat) (pivot : Nat) (tail : List Nat)
    (marker : Fin 6) (valuation : Nat → Fin 6)
    (pivotFresh : pivot ∉ stem)
    (markerChoice : marker = 0 ∨ marker = 2 ∨ marker = 5) :
    evalList (pivotValuation pivot marker valuation)
        (stem ++ pivot :: tail) =
      mul (evalList valuation stem) marker := by
  simp only [evalList, List.foldl_append, List.foldl_cons]
  rw [fold_pivotValuation_of_not_mem
    pivot marker valuation stem one pivotFresh]
  simp only [pivotValuation, if_pos]
  exact fold_leftZero
    (pivotValuation pivot marker valuation)
    (mul (List.foldl
      (fun current letter => mul current (valuation letter)) one stem)
      marker)
    (markerProduct_leftZero _ _ markerChoice) tail

theorem markerProfile_injective
    (left right : Fin 6)
    (atZero : mul left 0 = mul right 0)
    (atTwo : mul left 2 = mul right 2)
    (atFive : mul left 5 = mul right 5) :
    left = right := by
  revert left right
  decide

private theorem prefix_eval_eq_of_valid
    (left right : Word Nat)
    (valid : ∀ valuation : Nat → Fin 6,
      table.semigroup.eval valuation left =
        table.semigroup.eval valuation right)
    {leftPrefix rightPrefix : List Nat}
    {leftPivot rightPivot : Nat}
    {leftTail rightTail : List Nat}
    (leftSplit :
      r3Split left.toList =
        some (leftPrefix, leftPivot, leftTail))
    (rightSplit :
      r3Split right.toList =
        some (rightPrefix, rightPivot, rightTail))
    (pivotEqual : leftPivot = rightPivot) :
    ∀ valuation,
      evalList valuation leftPrefix = evalList valuation rightPrefix := by
  subst rightPivot
  have leftSpec := r3Split_some_spec leftSplit
  have rightSpec := r3Split_some_spec rightSplit
  intro valuation
  apply markerProfile_injective
  · have evaluated :=
      valid (pivotValuation leftPivot 0 valuation)
    rw [← evalList_toList, ← evalList_toList,
      leftSpec.shape, rightSpec.shape,
      evalList_pivot_marker leftPrefix leftPivot leftTail 0 valuation
        leftSpec.pivotFreshPrefix (Or.inl rfl),
      evalList_pivot_marker rightPrefix leftPivot rightTail 0 valuation
        rightSpec.pivotFreshPrefix (Or.inl rfl)] at evaluated
    exact evaluated
  · have evaluated :=
      valid (pivotValuation leftPivot 2 valuation)
    rw [← evalList_toList, ← evalList_toList,
      leftSpec.shape, rightSpec.shape,
      evalList_pivot_marker leftPrefix leftPivot leftTail 2 valuation
        leftSpec.pivotFreshPrefix (Or.inr (Or.inl rfl)),
      evalList_pivot_marker rightPrefix leftPivot rightTail 2 valuation
        rightSpec.pivotFreshPrefix (Or.inr (Or.inl rfl))] at evaluated
    exact evaluated
  · have evaluated :=
      valid (pivotValuation leftPivot 5 valuation)
    rw [← evalList_toList, ← evalList_toList,
      leftSpec.shape, rightSpec.shape,
      evalList_pivot_marker leftPrefix leftPivot leftTail 5 valuation
        leftSpec.pivotFreshPrefix (Or.inr (Or.inr rfl)),
      evalList_pivot_marker rightPrefix leftPivot rightTail 5 valuation
        rightSpec.pivotFreshPrefix (Or.inr (Or.inr rfl))] at evaluated
    exact evaluated

/-- The exact six-element table separates distinct recursive `i3`
invariants. -/
theorem r3_invariant_eq_of_valid
    (left right : Word Nat)
    (valid : ∀ valuation : Nat → Fin 6,
      table.semigroup.eval valuation left =
        table.semigroup.eval valuation right) :
    r3Invariant left.toList = r3Invariant right.toList := by
  have leftNonempty : left.toList ≠ [] := by
    cases left
    simp [Word.toList]
  have rightNonempty : right.toList ≠ [] := by
    cases right
    simp [Word.toList]
  obtain ⟨leftPrefix, leftPivot, leftTail, leftSplit⟩ :
      ∃ stem pivot tail,
        r3Split left.toList = some (stem, pivot, tail) := by
    cases splitEq : r3Split left.toList with
    | none =>
        exact False.elim
          (leftNonempty ((r3Split_none_iff left.toList).mp splitEq))
    | some result =>
        rcases result with ⟨stem, pivot, tail⟩
        exact ⟨stem, pivot, tail, rfl⟩
  obtain ⟨rightPrefix, rightPivot, rightTail, rightSplit⟩ :
      ∃ stem pivot tail,
        r3Split right.toList = some (stem, pivot, tail) := by
    cases splitEq : r3Split right.toList with
    | none =>
        exact False.elim
          (rightNonempty ((r3Split_none_iff right.toList).mp splitEq))
    | some result =>
        rcases result with ⟨stem, pivot, tail⟩
        exact ⟨stem, pivot, tail, rfl⟩
  let identity : Identity Nat := ⟨left, right⟩
  have firstEqual := valid_firstOccurrenceSequence_eq identity valid
  have leftFirst := firstOccurrenceSequence_eq_of_r3Split leftSplit
  have rightFirst := firstOccurrenceSequence_eq_of_r3Split rightSplit
  have splitFirstEqual :
      firstOccurrenceSequence leftPrefix ++ [leftPivot] =
        firstOccurrenceSequence rightPrefix ++ [rightPivot] := by
    exact leftFirst.symm.trans (firstEqual.trans rightFirst)
  have pivotEqual : leftPivot = rightPivot := by
    have lastEqual :=
      congrArg (fun letters : List Nat => letters.getLastD 0)
        splitFirstEqual
    simpa using lastEqual
  subst rightPivot
  have prefixFirstEqual :
      firstOccurrenceSequence leftPrefix =
        firstOccurrenceSequence rightPrefix :=
    List.append_cancel_right splitFirstEqual
  have lastEqual := valid_lastOccurrenceSequence_eq identity valid
  have prefixInvariantEqual :
      r3Invariant leftPrefix = r3Invariant rightPrefix := by
    by_cases leftPrefixEmpty : leftPrefix = []
    · subst leftPrefix
      have rightPrefixEmpty : rightPrefix = [] := by
        cases rightPrefix with
        | nil => rfl
        | cons head tail =>
            have member :
                head ∈ firstOccurrenceSequence (head :: tail) :=
              (SemigroupBasis.CoRoots.S5_1099.mem_firstOccurrenceSequence_iff
                head (head :: tail)).mpr (by simp)
            rw [← prefixFirstEqual] at member
            simpa [firstOccurrenceSequence] using member
      subst rightPrefix
      rfl
    · have rightPrefixNonempty : rightPrefix ≠ [] := by
        intro rightEmpty
        subst rightPrefix
        obtain ⟨head, tail, leftShape⟩ :=
          List.exists_cons_of_ne_nil leftPrefixEmpty
        have member :
            head ∈ firstOccurrenceSequence leftPrefix :=
          (SemigroupBasis.CoRoots.S5_1099.mem_firstOccurrenceSequence_iff
            head leftPrefix).mpr (by simp [leftShape])
        rw [prefixFirstEqual] at member
        simpa [firstOccurrenceSequence] using member
      obtain ⟨leftHead, leftRest, leftShape⟩ :=
        List.exists_cons_of_ne_nil leftPrefixEmpty
      obtain ⟨rightHead, rightRest, rightShape⟩ :=
        List.exists_cons_of_ne_nil rightPrefixNonempty
      let leftWord :=
        SemigroupBasis.CoRoots.S5_107.listWordOfCons leftHead leftRest
      let rightWord :=
        SemigroupBasis.CoRoots.S5_107.listWordOfCons rightHead rightRest
      have prefixEvalEqual :=
        prefix_eval_eq_of_valid left right valid
          leftSplit rightSplit rfl
      have prefixValid :
          ∀ valuation : Nat → Fin 6,
            table.semigroup.eval valuation leftWord =
              table.semigroup.eval valuation rightWord := by
        intro valuation
        rw [← evalList_toList, ← evalList_toList]
        simpa [leftWord, rightWord, leftShape, rightShape,
          SemigroupBasis.CoRoots.S5_107.listWordOfCons] using
            prefixEvalEqual valuation
      have recursive :=
        r3_invariant_eq_of_valid leftWord rightWord prefixValid
      simpa [leftWord, rightWord, leftShape, rightShape,
        SemigroupBasis.CoRoots.S5_107.listWordOfCons, Word.toList] using
          recursive
  rw [r3Invariant_eq_of_split leftSplit,
    r3Invariant_eq_of_split rightSplit,
    prefixInvariantEqual, lastEqual]
termination_by
  left.toList.length
decreasing_by
  have leftDecrease := r3Split_prefix_length_lt leftSplit
  simpa [leftWord,
    SemigroupBasis.CoRoots.S5_107.listWordOfCons, Word.toList,
    leftShape] using leftDecrease

end SemigroupBasis.CoRoots.Order6FennemoreR3Band
