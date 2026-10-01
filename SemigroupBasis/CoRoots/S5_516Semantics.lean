import SemigroupBasis.CoRoots.S5_516Invariant
import SemigroupBasis.Generated.CatalogueOrder5Part05
import SemigroupBasis.Transfer

namespace SemigroupBasis.CoRoots.S5_516

open SemigroupBasis
open SemigroupBasis.Examples

abbrev table : FiniteTable :=
  Generated.Catalogue.S5_516.table

set_option maxRecDepth 100000 in
theorem models :
    Models table.semigroup basis :=
  models_of_finite_checks table (by decide)

/-- The three-state initial marker embeds as one-based states
`[4,5,1]`: otherwise present, uniquely initial, and absent. -/
def initialMarkerEmbedding :
    Embedding finalMarkerThree.semigroup.opposite
      table.semigroup where
  toFun := fun value =>
    if value.val = 0 then ⟨3, by decide⟩
    else if value.val = 1 then ⟨4, by decide⟩
    else ⟨0, by decide⟩
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

def initialMarkerValuation (tested : Nat) : Nat → Fin 3 :=
  fun letter => if letter = tested then 1 else 2

private theorem initialMarkerFold (tested : Nat) :
    ∀ (letters : List Nat) (initial : Fin 3),
      letters.foldl
          (fun value letter =>
            finalMarkerThree.semigroup.opposite.mul value
              (initialMarkerValuation tested letter))
          initial =
        if tested ∈ letters then 0 else initial
  | [], initial => by
      simp
  | letter :: rest, initial => by
      simp only [List.foldl_cons]
      rw [initialMarkerFold tested rest]
      by_cases letterEq : letter = tested
      · subst letter
        simp [initialMarkerValuation, finalMarkerThree,
          FiniteTable.semigroup, Semigroup.opposite,
          finalMarkerThreeMul]
      · by_cases restMem : tested ∈ rest
        · simp [initialMarkerValuation, letterEq, restMem,
            finalMarkerThree, FiniteTable.semigroup,
            Semigroup.opposite, finalMarkerThreeMul]
        · have testedNeLetter : tested ≠ letter :=
            fun equality => letterEq equality.symm
          simp only [List.mem_cons, restMem, or_false, testedNeLetter,
            if_false]
          simp [initialMarkerValuation, letterEq,
            finalMarkerThree, FiniteTable.semigroup,
            Semigroup.opposite, finalMarkerThreeMul]

theorem initialMarkerEval (word : Word Nat) (tested : Nat) :
    finalMarkerThree.semigroup.opposite.eval
        (initialMarkerValuation tested) word =
      if tested ∈ word.tail then (0 : Fin 3)
      else if word.head = tested then (1 : Fin 3) else (2 : Fin 3) := by
  cases word with
  | mk head tail =>
      simp only [Semigroup.eval]
      rw [initialMarkerFold tested tail]
      by_cases tailMem : tested ∈ tail
      · simp [tailMem]
      · by_cases headEq : head = tested
        · subst head
          simp [tailMem, initialMarkerValuation]
        · simp [tailMem, headEq, initialMarkerValuation]

/-- The embedded marker valuation: the tested variable is one-based element
`5` and every other variable is element `1`. -/
def supportInitialSeparator (tested : Nat) : Nat → Fin 5 :=
  fun letter =>
    initialMarkerEmbedding.toFun
      (initialMarkerValuation tested letter)

/-- On an arbitrary word, the support/initial separator returns one-based
`1` when the tested variable is absent, `5` when it occurs uniquely first,
and `4` otherwise. -/
theorem evalSupportInitialSeparator
    (word : Word Nat) (tested : Nat) :
    (show Fin 5 from
      table.semigroup.eval (supportInitialSeparator tested) word) =
      if tested ∈ word.tail then 3
      else if word.head = tested then 4 else 0 := by
  change
    table.semigroup.eval
        (fun letter =>
          initialMarkerEmbedding.toFun
            (initialMarkerValuation tested letter))
        word =
      _
  rw [← initialMarkerEmbedding.toHom.map_eval,
    initialMarkerEval]
  by_cases tailMem : tested ∈ word.tail
  · simp [tailMem, initialMarkerEmbedding]
    apply Fin.ext
    rfl
  · by_cases headEq : word.head = tested
    · simp [tailMem, headEq, initialMarkerEmbedding]
      apply Fin.ext
      rfl
    · simp [tailMem, headEq, initialMarkerEmbedding]

theorem valid_initialMarker
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy finalMarkerThree.semigroup.opposite :=
  initialMarkerEmbedding.pullback_identity identity valid

def lengthState (marker : Fin 5) (length : Nat) : Fin 5 :=
  if length = 1 then marker
  else if length = 2 then 1 else 0

private theorem lengthFold
    (mul : Fin 5 → Fin 5 → Fin 5)
    (marker : Fin 5)
    (step :
      ∀ length, 0 < length →
        mul (lengthState marker length) marker =
          lengthState marker (length + 1))
    (letters : List Nat) (acc : Nat) (accPositive : 0 < acc) :
    letters.foldl (fun current _ => mul current marker)
        (lengthState marker acc) =
      lengthState marker (acc + letters.length) := by
  induction letters generalizing acc with
  | nil =>
      simp
  | cons letter rest ih =>
      simp only [List.foldl_cons, List.length_cons]
      rw [step acc accPositive, ih (acc + 1) (by omega)]
      congr 1
      omega

private theorem lengthState_capped_injective
    (marker : Fin 5)
    (markerNeZero : marker ≠ 0)
    (markerNeOne : marker ≠ 1)
    {leftLength rightLength : Nat}
    (leftPositive : 0 < leftLength)
    (rightPositive : 0 < rightLength)
    (equal :
      lengthState marker leftLength =
        lengthState marker rightLength) :
    min leftLength 3 = min rightLength 3 := by
  by_cases leftOne : leftLength = 1
  · subst leftLength
    by_cases rightOne : rightLength = 1
    · subst rightLength
      rfl
    · by_cases rightTwo : rightLength = 2
      · subst rightLength
        have markerEq : marker = 1 := by
          simpa [lengthState] using equal
        exact (markerNeOne markerEq).elim
      · have rightLong : 3 ≤ rightLength := by omega
        have markerEq : marker = 0 := by
          simpa [lengthState, rightOne, rightTwo] using equal
        exact (markerNeZero markerEq).elim
  · by_cases leftTwo : leftLength = 2
    · subst leftLength
      by_cases rightOne : rightLength = 1
      · subst rightLength
        have markerEq : marker = 1 := by
          simpa [lengthState] using equal.symm
        exact (markerNeOne markerEq).elim
      · by_cases rightTwo : rightLength = 2
        · subst rightLength
          rfl
        · have rightLong : 3 ≤ rightLength := by omega
          have values := congrArg Fin.val equal
          simp [lengthState, rightOne, rightTwo] at values
    · have leftLong : 3 ≤ leftLength := by omega
      by_cases rightOne : rightLength = 1
      · subst rightLength
        have markerEq : marker = 0 := by
          simpa [lengthState, leftOne, leftTwo] using equal.symm
        exact (markerNeZero markerEq).elim
      · by_cases rightTwo : rightLength = 2
        · subst rightLength
          have values := congrArg Fin.val equal
          simp [lengthState, leftOne, leftTwo] at values
        · have rightLong : 3 ≤ rightLength := by omega
          simp [Nat.min_eq_right leftLong,
            Nat.min_eq_right rightLong]

private theorem lengthStep (length : Nat) (positive : 0 < length) :
    Generated.Catalogue.S5_516.mul
        (lengthState 2 length) 2 =
      lengthState 2 (length + 1) := by
  by_cases lengthOne : length = 1
  · subst length
    rfl
  · by_cases lengthTwo : length = 2
    · subst length
      rfl
    · have lengthLong : 3 ≤ length := by omega
      simp [lengthState, lengthOne, lengthTwo,
        show length ≠ 0 by omega,
        show length + 1 ≠ 2 by omega,
        Generated.Catalogue.S5_516.mul]

/-- Assigning every variable to one-based element `3` returns elements
`3`, `2`, and `1` at lengths one, two, and at least three. -/
theorem evalLengthSeparator (word : Word Nat) :
    table.semigroup.eval (fun _ => (2 : Fin 5)) word =
      lengthState 2 word.toList.length := by
  cases word with
  | mk head tail =>
      change
        tail.foldl
            (fun current _ =>
              Generated.Catalogue.S5_516.mul current 2)
            2 =
          lengthState 2 (head :: tail).length
      simpa [lengthState, Nat.add_comm] using
        lengthFold Generated.Catalogue.S5_516.mul 2
          lengthStep tail 1 (by omega)

theorem valid_cappedLength
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    min identity.lhs.toList.length 3 =
      min identity.rhs.toList.length 3 := by
  have evaluated := valid (fun _ => (2 : Fin 5))
  rw [evalLengthSeparator, evalLengthSeparator] at evaluated
  exact lengthState_capped_injective 2
    (by decide) (by decide)
    (by simp [Word.toList]) (by simp [Word.toList]) evaluated

/-- The exact `S5_516` table separates precisely the support plus
initial-uniqueness classes, including literal words of lengths one and
two. -/
theorem valid_exactBasisClass
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    ExactBasisClass identity.lhs identity.rhs := by
  have markerValid := valid_initialMarker identity valid
  have reversedMarkerValid :
      identity.reversed.SatisfiedBy finalMarkerThree.semigroup :=
    (Identity.satisfiedBy_opposite_iff_reversed
      identity finalMarkerThree.semigroup).mp markerValid
  have dualSupport :=
    SemigroupBasis.CoRoots.S5_196.finalMarkerValid_support
      identity.reversed reversedMarkerValid
  have dualSimple :=
    SemigroupBasis.CoRoots.S5_196.finalMarkerValid_simpleFinal
      identity.reversed reversedMarkerValid
  have capped := valid_cappedLength identity valid
  have dualCapped :
      min identity.reversed.lhs.toList.length 3 =
        min identity.reversed.rhs.toList.length 3 := by
    simpa [Identity.reversed] using capped
  have dualExact :=
    SemigroupBasis.CoRoots.S5_196.exactBasisClass_of_separates
      identity.reversed dualSupport dualSimple dualCapped
  apply (exactBasisClass_iff_dual identity.lhs identity.rhs).2
  simpa [Identity.reversed] using dualExact

end SemigroupBasis.CoRoots.S5_516
