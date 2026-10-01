import SemigroupBasis.CoRoots.S5_860Completeness
import SemigroupBasis.Examples.CommutativeExponentThree
import SemigroupBasis.Examples.LeftZeroTwo
import SemigroupBasis.Transfer

namespace SemigroupBasis.CoRoots.S5_860

open SemigroupBasis
open SemigroupBasis.Examples

/-- The exact five-element catalogue table for `S5_860`. -/
abbrev table : FiniteTable :=
  Generated.Catalogue.S5_860.table

/-- Zero-based left-zero embedding `[0, 2]`, which exposes the literal
initial variable of every word. -/
def initialEmbedding :
    Embedding leftZeroTwo.semigroup table.semigroup where
  toFun := fun value =>
    if value.val = 0 then (0 : Fin 5) else (2 : Fin 5)
  injective := by
    intro left right
    revert left right
    decide
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide

theorem initialEmbedding_outputs :
    initialEmbedding.toFun (0 : Fin 2) = (0 : Fin 5) ∧
      initialEmbedding.toFun (1 : Fin 2) = (2 : Fin 5) := by
  decide

/-- Zero-based commutative exponent-three embedding `[0, 1, 3]`. -/
def cappedMultiplicityEmbedding :
    Embedding commutativeExponentThree.semigroup table.semigroup where
  toFun := fun value =>
    if value.val = 0 then (0 : Fin 5)
    else if value.val = 1 then (1 : Fin 5)
    else (3 : Fin 5)
  injective := by
    intro left right
    revert left right
    decide
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide

theorem cappedMultiplicityEmbedding_outputs :
    cappedMultiplicityEmbedding.toFun (0 : Fin 3) = (0 : Fin 5) ∧
      cappedMultiplicityEmbedding.toFun (1 : Fin 3) = (1 : Fin 5) ∧
        cappedMultiplicityEmbedding.toFun (2 : Fin 3) = (3 : Fin 5) := by
  decide

/-- Valid target identities have the same literal initial variable. -/
theorem valid_initial_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.lhs.head = identity.rhs.head := by
  have pulled := initialEmbedding.pullback_identity identity valid
  apply Decidable.byContradiction
  intro different
  let valuation : Nat → Fin 2 :=
    fun letter => if letter = identity.lhs.head then 0 else 1
  have evaluated := pulled valuation
  rw [leftZeroTwo_eval, leftZeroTwo_eval] at evaluated
  simp [valuation, Ne.symm different] at evaluated

/-- Valid target identities have equal multiplicities capped at two. -/
theorem valid_capped_count_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    ∀ letter,
      Nat.min (identity.lhs.toList.count letter) 2 =
        Nat.min (identity.rhs.toList.count letter) 2 :=
  exponentValid_capped_count_eq identity
    (cappedMultiplicityEmbedding.pullback_identity identity valid)

private theorem min_two_pos_iff (count : Nat) :
    0 < Nat.min count 2 ↔ 0 < count := by
  simp only [Nat.min_def]
  split <;> omega

private theorem min_two_eq_one_iff (count : Nat) :
    Nat.min count 2 = 1 ↔ count = 1 := by
  simp only [Nat.min_def]
  split <;> omega

/-- Capped multiplicity detects exactly the support of a word. -/
theorem valid_support
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup)
    (letter : Nat) :
    letter ∈ identity.lhs.toList ↔
      letter ∈ identity.rhs.toList := by
  have capped := valid_capped_count_eq identity valid letter
  constructor
  · intro leftMember
    apply List.count_pos_iff.mp
    apply (min_two_pos_iff _).1
    rw [← capped]
    exact (min_two_pos_iff _).2 <|
      List.count_pos_iff.mpr leftMember
  · intro rightMember
    apply List.count_pos_iff.mp
    apply (min_two_pos_iff _).1
    rw [capped]
    exact (min_two_pos_iff _).2 <|
      List.count_pos_iff.mpr rightMember

/-- Capped multiplicity detects exactly the globally simple variables. -/
theorem valid_simple
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup)
    (letter : Nat) :
    identity.lhs.toList.count letter = 1 ↔
      identity.rhs.toList.count letter = 1 := by
  have capped := valid_capped_count_eq identity valid letter
  rw [← min_two_eq_one_iff (identity.lhs.toList.count letter),
    ← min_two_eq_one_iff (identity.rhs.toList.count letter), capped]

/-- The right-zero pair `[3, 4]` tests the literal final variable. -/
def finalMarker (tested : Nat) : Nat → Fin 5 :=
  fun letter => if letter = tested then 4 else 3

theorem finalMarker_outputs
    (tested other : Nat) (different : other ≠ tested) :
    finalMarker tested tested = (4 : Fin 5) ∧
      finalMarker tested other = (3 : Fin 5) := by
  simp [finalMarker, different]

private theorem finalMarker_mul
    (tested left right : Nat) :
    table.mul
        (finalMarker tested left)
        (finalMarker tested right) =
      finalMarker tested right := by
  by_cases leftHit : left = tested <;>
    by_cases rightHit : right = tested <;>
      simp [table, finalMarker, leftHit, rightHit,
        Generated.Catalogue.S5_860.mul] <;>
      decide

/-- Evaluation under a final-marker valuation returns the marker assigned
to the literal final variable. -/
theorem finalMarker_eval
    (tested : Nat) :
    ∀ word : Word Nat,
      table.semigroup.eval (finalMarker tested) word =
        finalMarker tested word.final
  | ⟨head, []⟩ => rfl
  | ⟨head, next :: rest⟩ => by
      simp only [Semigroup.eval, Word.final, List.foldl_cons]
      change
        rest.foldl
            (fun current letter =>
              table.mul current (finalMarker tested letter))
            (table.mul
              (finalMarker tested head)
              (finalMarker tested next)) =
          finalMarker tested ((next :: rest).getLastD head)
      rw [finalMarker_mul]
      rw [List.getLastD_cons]
      change
        table.semigroup.eval
            (finalMarker tested) (Word.mk next rest) =
          finalMarker tested (Word.mk next rest).final
      exact finalMarker_eval tested (Word.mk next rest)

/-- Valid target identities have the same literal final variable. -/
theorem valid_final_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.lhs.final = identity.rhs.final := by
  apply Decidable.byContradiction
  intro different
  have evaluated := valid (finalMarker identity.lhs.final)
  rw [finalMarker_eval, finalMarker_eval] at evaluated
  have leftValue :
      finalMarker identity.lhs.final identity.lhs.final =
        (4 : Fin 5) := by
    simp [finalMarker]
  have rightValue :
      finalMarker identity.lhs.final identity.rhs.final =
        (3 : Fin 5) := by
    simp [finalMarker, Ne.symm different]
  rw [leftValue, rightValue] at evaluated
  exact (by decide : (4 : Fin 5) ≠ 3) evaluated

/-- Every identity valid in the exact catalogue table has the recorded
support/simple-variable/exact-endpoint signature. -/
theorem valid_sameSignature
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    SameSupportSimpleEndpointsSignature
      identity.lhs identity.rhs :=
  ⟨fun letter => valid_support identity valid letter,
    fun letter => valid_simple identity valid letter,
    valid_initial_eq identity valid,
    valid_final_eq identity valid⟩

/-- The exact table models all eight recorded basis laws. -/
theorem table_models_basis : Models table.semigroup basis :=
  catalogueModels

set_option maxRecDepth 100000 in
/-- Every derivation from the eight-law basis preserves the exact
`S5_860` signature, including through contexts and substitutions. -/
theorem derives_sameSignature
    {left right : Word Nat}
    (derivation : Derives basis left right) :
    SameSupportSimpleEndpointsSignature left right :=
  valid_sameSignature ⟨left, right⟩
    (fun valuation => derivation.sound table_models_basis valuation)

/-- Every displayed basis law preserves the exact signature after an
arbitrary simultaneous nonempty-word substitution. -/
theorem basisLaw_bind_sameSignature
    (identity : Identity Nat) (member : identity ∈ basis)
    (substitution : Nat → Word Nat) :
    SameSupportSimpleEndpointsSignature
      (identity.lhs.bind substitution)
      (identity.rhs.bind substitution) :=
  derives_sameSignature <|
    Derives.subst
      (Derives.fromBasis (basis := basis) member) substitution

end SemigroupBasis.CoRoots.S5_860
