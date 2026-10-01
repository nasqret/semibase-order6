import SemigroupBasis.CoRoots.S5_526Normalization
import SemigroupBasis.Examples.LeftZeroTwo
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Generated.CatalogueOrder5Part05
import SemigroupBasis.Transfer

namespace SemigroupBasis.CoRoots.S5_526

open SemigroupBasis
open SemigroupBasis.Examples

abbrev table : FiniteTable :=
  Generated.Catalogue.S5_526.table

def finiteFirstRepeatLaw : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [0, 1]⟩⟩

def finiteSecondRepeatLaw : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1]⟩⟩

def finiteFirstPairLaw : Identity (Fin 3) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 2]⟩⟩

theorem finiteFirstRepeatLaw_map :
    finiteFirstRepeatLaw.map Fin.val = firstRepeatLaw := rfl

theorem finiteSecondRepeatLaw_map :
    finiteSecondRepeatLaw.map Fin.val = secondRepeatLaw := rfl

theorem finiteFirstPairLaw_map :
    finiteFirstPairLaw.map Fin.val = firstPairLaw := rfl

/-- The exact catalogue table satisfies the ordered three-law basis. -/
theorem models : Models table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · rw [← finiteFirstRepeatLaw_map]
    exact table.checkIdentityNat_sound finiteFirstRepeatLaw (by decide)
  · rw [← finiteSecondRepeatLaw_map]
    exact table.checkIdentityNat_sound finiteSecondRepeatLaw (by decide)
  · rw [← finiteFirstPairLaw_map]
    exact table.checkIdentityNat_sound finiteFirstPairLaw (by decide)

/-- The one-based states `4` and `5` form an embedded two-element
left-zero semigroup and therefore recover the first variable. -/
def headEmbedding :
    Embedding leftZeroTwo.semigroup table.semigroup where
  toFun := fun value =>
    if value.val = 0 then ⟨3, by decide⟩ else ⟨4, by decide⟩
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

theorem valid_head_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.lhs.head = identity.rhs.head := by
  have pulled := headEmbedding.pullback_identity identity valid
  apply Decidable.byContradiction
  intro different
  let valuation : Nat → Fin 2 :=
    fun letter => if letter = identity.lhs.head then 0 else 1
  have evaluated := pulled valuation
  rw [leftZeroTwo_eval, leftZeroTwo_eval] at evaluated
  simp [valuation, Ne.symm different] at evaluated

inductive LengthClass where
  | singleton
  | pair
  | long
deriving DecidableEq, Repr

def lengthClass : Word Nat → LengthClass
  | ⟨_, []⟩ => .singleton
  | ⟨_, _ :: []⟩ => .pair
  | ⟨_, _ :: _ :: _⟩ => .long

private def lengthCode : LengthClass → Fin 5
  | .singleton => 2
  | .pair => 1
  | .long => 0

private theorem lengthCode_injective :
    Function.Injective lengthCode := by
  intro left right equal
  cases left <;> cases right <;>
    simp [lengthCode] at equal ⊢

private theorem mul_zero_left (value : Fin 5) :
    Generated.Catalogue.S5_526.mul 0 value = 0 := by
  revert value
  decide

private theorem mul_one_left (value : Fin 5) :
    Generated.Catalogue.S5_526.mul 1 value = 0 := by
  revert value
  decide

private theorem mul_three_left (value : Fin 5) :
    Generated.Catalogue.S5_526.mul 3 value = 3 := by
  revert value
  decide

private theorem fold_zero
    (valuation : Nat → Fin 5) (letters : List Nat) :
    letters.foldl
        (fun current letter =>
          Generated.Catalogue.S5_526.mul current (valuation letter))
        0 = 0 := by
  induction letters with
  | nil =>
      rfl
  | cons letter rest induction =>
      simp only [List.foldl_cons]
      rw [mul_zero_left]
      exact induction

private theorem fold_three
    (valuation : Nat → Fin 5) (letters : List Nat) :
    letters.foldl
        (fun current letter =>
          Generated.Catalogue.S5_526.mul current (valuation letter))
        3 = 3 := by
  induction letters with
  | nil =>
      rfl
  | cons letter rest induction =>
      simp only [List.foldl_cons]
      rw [mul_three_left]
      exact induction

/-- Constant one-based state `3` evaluates singleton, pair, and long words
to one-based states `3`, `2`, and `1`, respectively. -/
theorem eval_constant_length (word : Word Nat) :
    table.semigroup.eval (fun _ => (2 : Fin 5)) word =
      lengthCode (lengthClass word) := by
  cases word with
  | mk first tail =>
      cases tail with
      | nil =>
          rfl
      | cons second rest =>
          cases rest with
          | nil =>
              rfl
          | cons third more =>
              change
                more.foldl
                    (fun current _ =>
                      Generated.Catalogue.S5_526.mul current 2)
                    (Generated.Catalogue.S5_526.mul
                      (Generated.Catalogue.S5_526.mul 2 2) 2) =
                  0
              rw [show
                Generated.Catalogue.S5_526.mul 2 2 = (1 : Fin 5) by
                  decide]
              rw [show
                Generated.Catalogue.S5_526.mul 1 2 = (0 : Fin 5) by
                  decide]
              exact fold_zero (fun _ => (2 : Fin 5)) more

theorem valid_lengthClass_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    lengthClass identity.lhs = lengthClass identity.rhs := by
  have evaluated := valid (fun _ => (2 : Fin 5))
  rw [eval_constant_length, eval_constant_length] at evaluated
  exact lengthCode_injective evaluated

/-- The valuation used to recover a noninitial second variable. The first
variable receives one-based state `3`, the selected second variable receives
state `5`, and every other variable receives state `4`. -/
def secondSeparator
    (first selected : Nat) : Nat → Fin 5 :=
  fun letter =>
    if letter = first then 2 else
      if letter = selected then 4 else 3

/-- Exact evaluation formula for a word with a fixed first two letters
under a second-coordinate separator. -/
theorem secondSeparator_eval
    (first selected second : Nat) (rest : List Nat)
    (selectedNeFirst : selected ≠ first) :
    table.semigroup.eval (secondSeparator first selected)
        (wordOfTwo first second rest) =
      if second = first then
        if rest = [] then (1 : Fin 5) else 0
      else if second = selected then 3 else 0 := by
  cases rest with
  | nil =>
      change
        Generated.Catalogue.S5_526.mul
            (secondSeparator first selected first)
            (secondSeparator first selected second) =
          if second = first then (1 : Fin 5)
          else if second = selected then 3 else 0
      by_cases secondFirst : second = first
      · subst second
        simp [secondSeparator, selectedNeFirst,
          Generated.Catalogue.S5_526.mul]
      · by_cases secondSelected : second = selected
        · subst second
          simp [secondSeparator, selectedNeFirst,
            Generated.Catalogue.S5_526.mul]
        · simp [secondSeparator, secondFirst, secondSelected,
            Generated.Catalogue.S5_526.mul]
  | cons third more =>
      change
        more.foldl
            (fun current letter =>
              Generated.Catalogue.S5_526.mul current
                (secondSeparator first selected letter))
            (Generated.Catalogue.S5_526.mul
              (Generated.Catalogue.S5_526.mul
                (secondSeparator first selected first)
                (secondSeparator first selected second))
              (secondSeparator first selected third)) =
          if second = first then (0 : Fin 5)
          else if second = selected then 3 else 0
      by_cases secondFirst : second = first
      · subst second
        simp only [if_pos, List.cons_ne_nil, if_false]
        rw [show secondSeparator first selected first = (2 : Fin 5) by
          simp [secondSeparator]]
        rw [show
          Generated.Catalogue.S5_526.mul 2 2 = (1 : Fin 5) by
            decide]
        rw [mul_one_left]
        exact fold_zero (secondSeparator first selected) more
      · by_cases secondSelected : second = selected
        · subst second
          simp only [selectedNeFirst, if_false, if_pos,
            List.cons_ne_nil]
          rw [show secondSeparator first selected first = (2 : Fin 5) by
            simp [secondSeparator]]
          rw [show
            secondSeparator first selected selected = (4 : Fin 5) by
              simp [secondSeparator, selectedNeFirst]]
          rw [show
            Generated.Catalogue.S5_526.mul 2 4 = (3 : Fin 5) by
              decide]
          rw [mul_three_left]
          exact fold_three (secondSeparator first selected) more
        · simp only [secondFirst, secondSelected, if_false,
            List.cons_ne_nil]
          rw [show secondSeparator first selected first = (2 : Fin 5) by
            simp [secondSeparator]]
          rw [show
            secondSeparator first selected second = (3 : Fin 5) by
              simp [secondSeparator, secondFirst, secondSelected]]
          rw [show
            Generated.Catalogue.S5_526.mul 2 3 = (0 : Fin 5) by
              decide]
          rw [mul_zero_left]
          exact fold_zero (secondSeparator first selected) more

private theorem second_eq_of_valid
    (first lhsSecond rhsSecond : Nat)
    (lhsRest rhsRest : List Nat)
    (sameClass :
      lengthClass (wordOfTwo first lhsSecond lhsRest) =
        lengthClass (wordOfTwo first rhsSecond rhsRest))
    (valid :
      (Identity.mk
        (wordOfTwo first lhsSecond lhsRest)
        (wordOfTwo first rhsSecond rhsRest)).SatisfiedBy
          table.semigroup) :
    lhsSecond = rhsSecond := by
  apply Decidable.byContradiction
  intro secondsNe
  cases lhsRest with
  | nil =>
      cases rhsRest with
      | nil =>
          by_cases lhsFirst : lhsSecond = first
          · have rhsFirst : rhsSecond ≠ first := by
              intro equal
              exact secondsNe (lhsFirst.trans equal.symm)
            let valuation :=
              secondSeparator first rhsSecond
            have evaluated := valid valuation
            rw [secondSeparator_eval first rhsSecond lhsSecond []
                rhsFirst,
              secondSeparator_eval first rhsSecond rhsSecond []
                rhsFirst] at evaluated
            simp [lhsFirst, rhsFirst] at evaluated
          · let valuation :=
              secondSeparator first lhsSecond
            have rhsSelected : rhsSecond ≠ lhsSecond :=
              Ne.symm secondsNe
            have evaluated := valid valuation
            rw [secondSeparator_eval first lhsSecond lhsSecond []
                lhsFirst,
              secondSeparator_eval first lhsSecond rhsSecond []
                lhsFirst] at evaluated
            by_cases rhsFirst : rhsSecond = first
            · simp [lhsFirst, rhsFirst, rhsSelected] at evaluated
            · simp [lhsFirst, rhsFirst, rhsSelected] at evaluated
      | cons rhsThird rhsMore =>
          simp [lengthClass, wordOfTwo] at sameClass
  | cons lhsThird lhsMore =>
      cases rhsRest with
      | nil =>
          simp [lengthClass, wordOfTwo] at sameClass
      | cons rhsThird rhsMore =>
          by_cases lhsFirst : lhsSecond = first
          · have rhsFirst : rhsSecond ≠ first := by
              intro equal
              exact secondsNe (lhsFirst.trans equal.symm)
            let valuation :=
              secondSeparator first rhsSecond
            have evaluated := valid valuation
            rw [secondSeparator_eval first rhsSecond lhsSecond
                (lhsThird :: lhsMore) rhsFirst,
              secondSeparator_eval first rhsSecond rhsSecond
                (rhsThird :: rhsMore) rhsFirst] at evaluated
            simp [lhsFirst, rhsFirst] at evaluated
          · let valuation :=
              secondSeparator first lhsSecond
            have rhsSelected : rhsSecond ≠ lhsSecond :=
              Ne.symm secondsNe
            have evaluated := valid valuation
            rw [secondSeparator_eval first lhsSecond lhsSecond
                (lhsThird :: lhsMore) lhsFirst,
              secondSeparator_eval first lhsSecond rhsSecond
                (rhsThird :: rhsMore) lhsFirst] at evaluated
            simp [lhsFirst, rhsSelected] at evaluated

/-- Every valid identity on the exact table has the same unrestricted
first-pair signature on both sides. -/
theorem valid_signature_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    signature identity.lhs = signature identity.rhs := by
  rcases identity with
    ⟨⟨lhsHead, lhsTail⟩, ⟨rhsHead, rhsTail⟩⟩
  have heads :
      lhsHead = rhsHead :=
    valid_head_eq
      ⟨⟨lhsHead, lhsTail⟩, ⟨rhsHead, rhsTail⟩⟩ valid
  have classes :
      lengthClass ⟨lhsHead, lhsTail⟩ =
        lengthClass ⟨rhsHead, rhsTail⟩ :=
    valid_lengthClass_eq
      ⟨⟨lhsHead, lhsTail⟩, ⟨rhsHead, rhsTail⟩⟩ valid
  cases lhsTail with
  | nil =>
      cases rhsTail with
      | nil =>
          subst rhsHead
          rfl
      | cons rhsSecond rhsRest =>
          cases rhsRest <;>
            simp [lengthClass] at classes
  | cons lhsSecond lhsRest =>
      cases rhsTail with
      | nil =>
          cases lhsRest <;>
            simp [lengthClass] at classes
      | cons rhsSecond rhsRest =>
          subst rhsHead
          have specialized :
              (Identity.mk
                (wordOfTwo lhsHead lhsSecond lhsRest)
                (wordOfTwo lhsHead rhsSecond rhsRest)).SatisfiedBy
                  table.semigroup := by
            simpa [wordOfTwo] using valid
          have seconds :=
            second_eq_of_valid lhsHead lhsSecond rhsSecond
              lhsRest rhsRest (by
                simpa [wordOfTwo] using classes) specialized
          subst rhsSecond
          cases lhsRest with
          | nil =>
              cases rhsRest with
              | nil =>
                  rfl
              | cons rhsThird rhsMore =>
                  simp [lengthClass, wordOfTwo] at classes
          | cons lhsThird lhsMore =>
              cases rhsRest with
              | nil =>
                  simp [lengthClass, wordOfTwo] at classes
              | cons rhsThird rhsMore =>
                  rfl

def headEmbeddingOneBased : List Nat :=
  List.ofFn fun value : Fin 2 =>
    (headEmbedding.toFun value).val + 1

theorem headEmbedding_certificate :
    headEmbeddingOneBased = [4, 5] := by
  decide

theorem lengthMarker_certificate :
    Generated.Catalogue.S5_526.mul 2 2 = 1 ∧
      Generated.Catalogue.S5_526.mul 1 2 = 0 ∧
      Generated.Catalogue.S5_526.mul 0 2 = 0 := by
  decide

theorem secondSeparator_certificate :
    Generated.Catalogue.S5_526.mul 2 2 = 1 ∧
      Generated.Catalogue.S5_526.mul 2 4 = 3 ∧
      Generated.Catalogue.S5_526.mul 2 3 = 0 := by
  decide

theorem absorbingStates_certificate (value : Fin 5) :
    Generated.Catalogue.S5_526.mul 0 value = 0 ∧
      Generated.Catalogue.S5_526.mul 3 value = 3 ∧
      Generated.Catalogue.S5_526.mul 4 value = 4 := by
  revert value
  decide

end SemigroupBasis.CoRoots.S5_526
