import SemigroupBasis.CoRoots.S5_1099Normalization
import SemigroupBasis.CoRoots.S5_345Factors
import SemigroupBasis.Generated.CatalogueOrder5Part09
import SemigroupBasis.Transfer

namespace SemigroupBasis.CoRoots.S5_1099

open SemigroupBasis
open SemigroupBasis.Examples

abbrev table : FiniteTable :=
  SemigroupBasis.Generated.Catalogue.S5_1099.table

theorem table_eq_canonical_catalogue :
    table = SemigroupBasis.Generated.Catalogue.S5_1099.table := rfl

set_option maxRecDepth 100000 in
theorem models : Models table.semigroup basis :=
  models_of_finite_checks table (by decide)

theorem leftRegularBandThree_models_basis :
    Models leftRegularBandThree.semigroup basis :=
  models_of_finite_checks leftRegularBandThree (by decide)

/-- Zero-based embedding `0 -> 0`, `1 -> 1`, `2 -> 4`. -/
def firstOccurrenceEmbedding :
    Embedding leftRegularBandThree.semigroup table.semigroup where
  toFun := fun value =>
    if value.val = 0 then (0 : Fin 5)
    else if value.val = 1 then (1 : Fin 5)
    else (4 : Fin 5)
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
      firstOccurrenceSequence identity.rhs.toList := by
  exact
    SemigroupBasis.CoRoots.S5_345Factors.leftRegularBandThreeValid_firstOccurrenceSequence_eq
      identity
      (firstOccurrenceEmbedding.pullback_identity identity valid)

private def finalSeparator (tested : Nat) : Nat → Fin 5 :=
  fun letter => if letter = tested then 3 else 1

private theorem finalSeparator_mul
    (tested left right : Nat) :
    table.mul
        (finalSeparator tested left)
        (finalSeparator tested right) =
      finalSeparator tested right := by
  by_cases leftHit : left = tested <;>
    by_cases rightHit : right = tested <;>
      simp [finalSeparator, leftHit, rightHit,
        SemigroupBasis.Generated.Catalogue.S5_1099.table,
        SemigroupBasis.Generated.Catalogue.S5_1099.mul]

private theorem fold_finalSeparator
    (tested : Nat) (letters : List Nat) (previous : Nat) :
    letters.foldl
        (fun current letter =>
          table.mul current (finalSeparator tested letter))
        (finalSeparator tested previous) =
      finalSeparator tested (letters.getLastD previous) := by
  induction letters generalizing previous with
  | nil => rfl
  | cons next rest ih =>
      simp only [List.foldl_cons, List.getLastD_cons]
      rw [finalSeparator_mul]
      exact ih next

private theorem eval_finalSeparator
    (tested : Nat) (word : Word Nat) :
    table.semigroup.eval (finalSeparator tested) word =
      finalSeparator tested word.final := by
  cases word with
  | mk head tail =>
      exact fold_finalSeparator tested tail head

theorem valid_final_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.lhs.final = identity.rhs.final := by
  apply Decidable.byContradiction
  intro different
  have evaluated := valid (finalSeparator identity.lhs.final)
  rw [eval_finalSeparator, eval_finalSeparator] at evaluated
  have leftValue :
      finalSeparator identity.lhs.final identity.lhs.final =
        (3 : Fin 5) := by
    simp [finalSeparator]
  have rightValue :
      finalSeparator identity.lhs.final identity.rhs.final =
        (1 : Fin 5) := by
    simp [finalSeparator, Ne.symm different]
  rw [leftValue, rightValue] at evaluated
  exact (by decide : (3 : Fin 5) ≠ 1) evaluated

private def predecessorSeparator
    (source target : Nat) : Nat → Fin 5 :=
  fun letter =>
    if letter = target then 2
    else if letter = source then 3
    else 1

private def predecessorOutput (source : Nat) (previous : Nat) : Fin 5 :=
  if previous = source then 4 else 0

private theorem pass_mul
    (source target previous next : Nat)
    (previousNotTarget : previous ≠ target)
    (nextNotTarget : next ≠ target) :
    table.mul
        (predecessorSeparator source target previous)
        (predecessorSeparator source target next) =
      predecessorSeparator source target next := by
  by_cases previousSource : previous = source <;>
    by_cases nextSource : next = source <;>
      simp_all [predecessorSeparator,
        SemigroupBasis.Generated.Catalogue.S5_1099.table,
        SemigroupBasis.Generated.Catalogue.S5_1099.mul]

private theorem hit_mul
    (source target previous : Nat)
    (different : source ≠ target)
    (previousNotTarget : previous ≠ target) :
    table.mul
        (predecessorSeparator source target previous)
        (predecessorSeparator source target target) =
      predecessorOutput source previous := by
  by_cases previousSource : previous = source <;>
    simp [predecessorSeparator, predecessorOutput, different,
      previousNotTarget, previousSource,
      SemigroupBasis.Generated.Catalogue.S5_1099.table,
      SemigroupBasis.Generated.Catalogue.S5_1099.mul]

private theorem absorbing_mul
    (state : Fin 5) (absorbing : state = 0 ∨ state = 2 ∨ state = 4)
    (value : Fin 5) :
    table.mul state value = state := by
  rcases absorbing with rfl | rfl | rfl <;>
    simp [SemigroupBasis.Generated.Catalogue.S5_1099.table,
      SemigroupBasis.Generated.Catalogue.S5_1099.mul]

private theorem fold_after_hit
    (valuation : Nat → Fin 5)
    (state : Fin 5) (absorbing : state = 0 ∨ state = 2 ∨ state = 4) :
    ∀ letters : List Nat,
      letters.foldl
          (fun current letter => table.mul current (valuation letter))
          state = state
  | [] => rfl
  | next :: rest => by
      simp only [List.foldl_cons]
      rw [absorbing_mul state absorbing]
      exact fold_after_hit valuation state absorbing rest

private theorem predecessorOutput_absorbing
    (source previous : Nat) :
    predecessorOutput source previous = 0 ∨
      predecessorOutput source previous = 2 ∨
      predecessorOutput source previous = 4 := by
  by_cases same : previous = source
  · exact Or.inr (Or.inr (by
      simp [predecessorOutput, same]))
  · exact Or.inl (by
      simp [predecessorOutput, same])

private theorem fold_predecessorSeparator_of_some
    (source target result previous : Nat)
    (different : source ≠ target)
    (previousNotTarget : previous ≠ target) :
    ∀ letters : List Nat,
      firstPredecessorFrom previous target letters = some result →
      letters.foldl
          (fun current letter =>
            table.mul current
              (predecessorSeparator source target letter))
          (predecessorSeparator source target previous) =
        predecessorOutput source result
  | [], found => by
      simp [firstPredecessorFrom] at found
  | next :: rest, found => by
      by_cases nextTarget : next = target
      · subst next
        have previousResult : previous = result := by
          simpa [firstPredecessorFrom] using found
        subst result
        simp only [List.foldl_cons]
        rw [hit_mul source target previous different previousNotTarget]
        exact fold_after_hit _ _
          (predecessorOutput_absorbing source previous) rest
      · have later :
            firstPredecessorFrom next target rest = some result := by
          simpa [firstPredecessorFrom, nextTarget] using found
        simp only [List.foldl_cons]
        rw [pass_mul source target previous next
          previousNotTarget nextTarget]
        exact fold_predecessorSeparator_of_some
          source target result next different nextTarget rest later

private theorem eval_predecessorSeparator_of_some
    (source target result : Nat)
    (different : source ≠ target)
    (word : Word Nat)
    (found : firstPredecessor word.toList target = some result) :
    table.semigroup.eval
        (predecessorSeparator source target) word =
      predecessorOutput source result := by
  have headNotTarget : word.head ≠ target := by
    intro headTarget
    simpa [Word.toList, firstPredecessor, headTarget] using found
  have fromFound :
      firstPredecessorFrom word.head target word.tail = some result := by
    simpa [Word.toList, firstPredecessor, headNotTarget] using found
  change
    word.tail.foldl
        (fun current letter =>
          table.mul current
            (predecessorSeparator source target letter))
        (predecessorSeparator source target word.head) =
      predecessorOutput source result
  exact fold_predecessorSeparator_of_some
    source target result word.head different headNotTarget
    word.tail fromFound

private theorem firstPredecessorFrom_eq_none_iff
    (target previous : Nat) :
    ∀ letters : List Nat,
      firstPredecessorFrom previous target letters = none ↔
        target ∉ letters
  | [] => by
      simp [firstPredecessorFrom]
  | next :: rest => by
      by_cases nextTarget : next = target
      · subst next
        simp [firstPredecessorFrom]
      · simp [firstPredecessorFrom, nextTarget, Ne.symm nextTarget,
          firstPredecessorFrom_eq_none_iff target next rest]

private theorem firstPredecessor_eq_none_iff
    (word : Word Nat) (target : Nat)
    (headNotTarget : word.head ≠ target) :
    firstPredecessor word.toList target = none ↔
      target ∉ word.toList := by
  simp [Word.toList, firstPredecessor, headNotTarget,
    Ne.symm headNotTarget, firstPredecessorFrom_eq_none_iff]

private theorem firstPredecessorFrom_ne_target_of_some
    (target result previous : Nat)
    (previousNotTarget : previous ≠ target) :
    ∀ letters : List Nat,
      firstPredecessorFrom previous target letters = some result →
        result ≠ target
  | [], found => by
      simp [firstPredecessorFrom] at found
  | next :: rest, found => by
      by_cases nextTarget : next = target
      · subst next
        have previousResult : previous = result := by
          simpa [firstPredecessorFrom] using found
        intro resultTarget
        exact previousNotTarget (previousResult.trans resultTarget)
      · have later :
            firstPredecessorFrom next target rest = some result := by
          simpa [firstPredecessorFrom, nextTarget] using found
        exact firstPredecessorFrom_ne_target_of_some
          target result next nextTarget rest later

private theorem firstPredecessor_ne_target_of_some
    (word : Word Nat) (target result : Nat)
    (found : firstPredecessor word.toList target = some result) :
    result ≠ target := by
  have headNotTarget : word.head ≠ target := by
    intro headTarget
    simpa [Word.toList, firstPredecessor, headTarget] using found
  have fromFound :
      firstPredecessorFrom word.head target word.tail = some result := by
    simpa [Word.toList, firstPredecessor, headNotTarget] using found
  exact firstPredecessorFrom_ne_target_of_some
    target result word.head headNotTarget word.tail fromFound

private theorem head_eq_of_firstOccurrenceSequence_eq
    {left right : Word Nat}
    (equal :
      firstOccurrenceSequence left.toList =
        firstOccurrenceSequence right.toList) :
    left.head = right.head := by
  have heads := congrArg List.head? equal
  simpa [Word.toList, firstOccurrenceSequence] using heads

private theorem mem_iff_of_firstOccurrenceSequence_eq
    {left right : Word Nat}
    (equal :
      firstOccurrenceSequence left.toList =
        firstOccurrenceSequence right.toList)
    (target : Nat) :
    target ∈ left.toList ↔ target ∈ right.toList := by
  constructor
  · intro member
    have firstMember :
        target ∈ firstOccurrenceSequence left.toList :=
      (mem_firstOccurrenceSequence_iff target left.toList).2 member
    rw [equal] at firstMember
    exact (mem_firstOccurrenceSequence_iff target right.toList).1
      firstMember
  · intro member
    have firstMember :
        target ∈ firstOccurrenceSequence right.toList :=
      (mem_firstOccurrenceSequence_iff target right.toList).2 member
    rw [← equal] at firstMember
    exact (mem_firstOccurrenceSequence_iff target left.toList).1
      firstMember

theorem valid_firstPredecessor_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    ∀ target,
      firstPredecessor identity.lhs.toList target =
        firstPredecessor identity.rhs.toList target := by
  intro target
  have firstEqual := valid_firstOccurrenceSequence_eq identity valid
  have headsEqual := head_eq_of_firstOccurrenceSequence_eq firstEqual
  have supportEqual :=
    mem_iff_of_firstOccurrenceSequence_eq firstEqual target
  by_cases leftInitial : identity.lhs.head = target
  · have rightInitial : identity.rhs.head = target :=
      headsEqual.symm.trans leftInitial
    simp [Word.toList, firstPredecessor, leftInitial, rightInitial]
  · have rightNotInitial : identity.rhs.head ≠ target := by
      intro rightInitial
      exact leftInitial (headsEqual.trans rightInitial)
    cases leftEq :
      firstPredecessor identity.lhs.toList target with
    | none =>
        have leftAbsent :
            target ∉ identity.lhs.toList := by
          exact (firstPredecessor_eq_none_iff
            identity.lhs target leftInitial).1 leftEq
        have rightAbsent :
            target ∉ identity.rhs.toList := by
          intro rightMember
          exact leftAbsent (supportEqual.2 rightMember)
        have rightNone :
            firstPredecessor identity.rhs.toList target = none :=
          (firstPredecessor_eq_none_iff
            identity.rhs target rightNotInitial).2 rightAbsent
        exact rightNone.symm
    | some leftPrevious =>
        cases rightEq :
          firstPredecessor identity.rhs.toList target with
        | none =>
            have rightAbsent :
                target ∉ identity.rhs.toList :=
              (firstPredecessor_eq_none_iff
                identity.rhs target rightNotInitial).1 rightEq
            have leftPresent : target ∈ identity.lhs.toList := by
              apply Decidable.byContradiction
              intro leftAbsent
              have leftNone :
                  firstPredecessor identity.lhs.toList target = none :=
                (firstPredecessor_eq_none_iff
                  identity.lhs target leftInitial).2 leftAbsent
              rw [leftEq] at leftNone
              contradiction
            exact False.elim
              (rightAbsent (supportEqual.1 leftPresent))
        | some rightPrevious =>
            have previousEqual : leftPrevious = rightPrevious := by
              apply Decidable.byContradiction
              intro previousDifferent
              have leftDifferent : leftPrevious ≠ target :=
                firstPredecessor_ne_target_of_some
                  identity.lhs target leftPrevious leftEq
              have evaluated :=
                valid (predecessorSeparator leftPrevious target)
              have leftValue :
                  table.semigroup.eval
                      (predecessorSeparator leftPrevious target)
                      identity.lhs = (4 : Fin 5) := by
                simpa [predecessorOutput] using
                  eval_predecessorSeparator_of_some
                    leftPrevious target leftPrevious leftDifferent
                    identity.lhs leftEq
              have rightValue :
                  table.semigroup.eval
                      (predecessorSeparator leftPrevious target)
                      identity.rhs = (0 : Fin 5) := by
                simpa [predecessorOutput,
                    Ne.symm previousDifferent] using
                  eval_predecessorSeparator_of_some
                    leftPrevious target rightPrevious leftDifferent
                    identity.rhs rightEq
              rw [leftValue, rightValue] at evaluated
              exact (by decide : (4 : Fin 5) ≠ 0) evaluated
            exact congrArg Option.some previousEqual

theorem valid_sameTraceSignature
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    SameTraceSignature identity.lhs identity.rhs :=
  ⟨valid_firstOccurrenceSequence_eq identity valid,
    valid_firstPredecessor_eq identity valid,
    valid_final_eq identity valid⟩

end SemigroupBasis.CoRoots.S5_1099
