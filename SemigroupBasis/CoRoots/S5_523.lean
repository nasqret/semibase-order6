import SemigroupBasis.CoRoots.S5_523Normalization
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Generated.CatalogueOrder5Part05
import SemigroupBasis.Transfer

namespace SemigroupBasis.CoRoots.S5_523

open SemigroupBasis
open SemigroupBasis.Examples

private def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

def finiteBasis : List (Identity (Fin 3)) :=
  basis.map fun identity => identity.map toFinThree

private theorem basisRoundTripChecked :
    basis.all (fun identity =>
      decide ((identity.map toFinThree).map Fin.val = identity)) = true := by
  decide

private theorem basisRoundTrip
    (identity : Identity Nat) (member : identity ∈ basis) :
    (identity.map toFinThree).map Fin.val = identity := by
  exact of_decide_eq_true <|
    (List.all_eq_true.mp basisRoundTripChecked) identity member

theorem modelsOfFiniteChecks
    (table : FiniteTable)
    (checks : finiteBasis.all table.checkIdentity = true) :
    Models table.semigroup basis := by
  intro identity member
  have finiteMember : identity.map toFinThree ∈ finiteBasis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    table.checkIdentityNat_sound (identity.map toFinThree)
      ((List.all_eq_true.mp checks) _ finiteMember)
  rw [basisRoundTrip identity member] at finiteValid
  exact finiteValid

abbrev table : FiniteTable :=
  Generated.Catalogue.S5_523.table

abbrev siblingTable : FiniteTable :=
  Generated.Catalogue.S5_539.table

theorem models : Models table.semigroup basis :=
  modelsOfFiniteChecks table (by decide)

theorem siblingModels : Models siblingTable.semigroup basis :=
  modelsOfFiniteChecks siblingTable (by decide)

def tableRowsOneBased : List (List Nat) :=
  List.ofFn fun left : Fin 5 =>
    List.ofFn fun right : Fin 5 =>
      (table.mul left right).val + 1

def siblingTableRowsOneBased : List (List Nat) :=
  List.ofFn fun left : Fin 5 =>
    List.ofFn fun right : Fin 5 =>
      (siblingTable.mul left right).val + 1

theorem tableRowsOneBased_certificate :
    tableRowsOneBased =
      [[1, 1, 1, 1, 1],
        [1, 1, 1, 1, 1],
        [1, 1, 2, 1, 1],
        [1, 1, 1, 4, 5],
        [5, 5, 5, 5, 5]] := by
  decide

theorem siblingTableRowsOneBased_certificate :
    siblingTableRowsOneBased =
      [[1, 1, 1, 4, 5],
        [1, 1, 1, 4, 5],
        [1, 1, 2, 4, 5],
        [4, 4, 4, 4, 4],
        [5, 5, 5, 5, 5]] := by
  decide

def oppositeTableRowsOneBased : List (List Nat) :=
  List.ofFn fun left : Fin 5 =>
    List.ofFn fun right : Fin 5 =>
      (table.semigroup.opposite.mul left right).val + 1

def siblingOppositeTableRowsOneBased : List (List Nat) :=
  List.ofFn fun left : Fin 5 =>
    List.ofFn fun right : Fin 5 =>
      (siblingTable.semigroup.opposite.mul left right).val + 1

theorem oppositeTableRowsOneBased_certificate :
    oppositeTableRowsOneBased =
      [[1, 1, 1, 1, 5],
        [1, 1, 1, 1, 5],
        [1, 1, 2, 1, 5],
        [1, 1, 1, 4, 5],
        [1, 1, 1, 5, 5]] := by
  decide

theorem siblingOppositeTableRowsOneBased_certificate :
    siblingOppositeTableRowsOneBased =
      [[1, 1, 1, 4, 5],
        [1, 1, 1, 4, 5],
        [1, 1, 2, 4, 5],
        [4, 4, 4, 4, 5],
        [5, 5, 5, 4, 5]] := by
  decide

/-- Semantic separation statement corresponding exactly to the published
normal forms. The guarded WMI replay checks both finite tables against the
recorded finite-state witness domains; an unrestricted Lean proof remains
separate from the derivational normalization obligation. -/
def SeparatesLongFirstOccurrenceSignatures
    (model : Semigroup S) : Prop :=
  ∀ left right : Word Nat,
    (∀ valuation : Nat → S,
      model.eval valuation left = model.eval valuation right) →
    SameLongFirstOccurrenceSignature left right

def S5_523SemanticSeparation : Prop :=
  SeparatesLongFirstOccurrenceSignatures table.semigroup

def S5_539SemanticSeparation : Prop :=
  SeparatesLongFirstOccurrenceSignatures siblingTable.semigroup

/-- The subsemigroup on one-based elements `1,4,5` is the standard
three-element left regular band. -/
def representativeLrbEmbedding :
    Embedding leftRegularBandThree.semigroup table.semigroup where
  toFun := fun value => by
    change Fin 3 at value
    change Fin 5
    exact if value = 0 then 0 else if value = 1 then 3 else 4
  map_mul := by decide +revert
  injective := by
    intro left right equal
    change Fin 3 at left right
    by_cases leftZero : left = 0 <;>
      by_cases leftOne : left = 1 <;>
        by_cases rightZero : right = 0 <;>
          by_cases rightOne : right = 1 <;>
            simp [leftZero, leftOne, rightZero, rightOne] at equal ⊢ <;>
              apply Fin.ext <;> omega

/-- The subsemigroup on one-based elements `4,1,5` is the same left regular
band inside `S5_539`. -/
def siblingLrbEmbedding :
    Embedding leftRegularBandThree.semigroup siblingTable.semigroup where
  toFun := fun value => by
    change Fin 3 at value
    change Fin 5
    exact if value = 0 then 3 else if value = 1 then 0 else 4
  map_mul := by decide +revert
  injective := by
    intro left right equal
    change Fin 3 at left right
    by_cases leftZero : left = 0 <;>
      by_cases leftOne : left = 1 <;>
        by_cases rightZero : right = 0 <;>
          by_cases rightOne : right = 1 <;>
            simp [leftZero, leftOne, rightZero, rightOne] at equal ⊢ <;>
              apply Fin.ext <;> omega

private theorem firstOccurrences_of_valid
    (target : Semigroup (Fin 5))
    (embedding : Embedding leftRegularBandThree.semigroup target)
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy target) :
    firstOccurrenceSequence identity.lhs.toList =
      firstOccurrenceSequence identity.rhs.toList := by
  exact
    SemigroupBasis.CoRoots.S5_345Factors.leftRegularBandThreeValid_firstOccurrenceSequence_eq
      identity
        (embedding.pullback_identity identity valid)

private def lengthState (length : Nat) : Fin 5 :=
  if length = 1 then 2 else if length = 2 then 1 else 0

private theorem lengthFold
    (mul : Fin 5 → Fin 5 → Fin 5)
    (step :
      ∀ length, 0 < length →
        mul (lengthState length) 2 = lengthState (length + 1))
    (letters : List Nat) (initial : Nat) (positive : 0 < initial) :
    letters.foldl (fun current _ => mul current 2)
        (lengthState initial) =
      lengthState (initial + letters.length) := by
  induction letters generalizing initial with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons, List.length_cons]
      rw [step initial positive, ih (initial + 1) (by omega)]
      congr 1
      omega

private theorem representativeLengthStep
    (length : Nat) (positive : 0 < length) :
    table.mul (lengthState length) (2 : Fin 5) =
      lengthState (length + 1) := by
  by_cases one : length = 1
  · subst length
    rfl
  · by_cases two : length = 2
    · subst length
      rfl
    · have three : 3 ≤ length := by omega
      have zero : length ≠ 0 := by omega
      change
        Generated.Catalogue.S5_523.mul (lengthState length) (2 : Fin 5) =
          lengthState (length + 1)
      simp [lengthState, zero, one, two,
        show length + 1 ≠ 1 by omega,
        show length + 1 ≠ 2 by omega,
        Generated.Catalogue.S5_523.mul]

private theorem siblingLengthStep
    (length : Nat) (positive : 0 < length) :
    siblingTable.mul (lengthState length) (2 : Fin 5) =
      lengthState (length + 1) := by
  by_cases one : length = 1
  · subst length
    rfl
  · by_cases two : length = 2
    · subst length
      rfl
    · have three : 3 ≤ length := by omega
      have zero : length ≠ 0 := by omega
      change
        Generated.Catalogue.S5_539.mul (lengthState length) (2 : Fin 5) =
          lengthState (length + 1)
      simp [lengthState, zero, one, two,
        show length + 1 ≠ 1 by omega,
        show length + 1 ≠ 2 by omega,
        Generated.Catalogue.S5_539.mul]

private theorem representativeEvalLength (word : Word Nat) :
    table.semigroup.eval (fun _ => (2 : Fin 5)) word =
      lengthState word.toList.length := by
  cases word with
  | mk head tail =>
      change
        tail.foldl
            (fun current _ => table.mul current (2 : Fin 5)) (2 : Fin 5) =
          lengthState (head :: tail).length
      simpa [lengthState, Nat.add_comm] using
        lengthFold table.mul representativeLengthStep tail 1 (by omega)

private theorem siblingEvalLength (word : Word Nat) :
    siblingTable.semigroup.eval (fun _ => (2 : Fin 5)) word =
      lengthState word.toList.length := by
  cases word with
  | mk head tail =>
      change
        tail.foldl
            (fun current _ => siblingTable.mul current (2 : Fin 5))
            (2 : Fin 5) =
          lengthState (head :: tail).length
      simpa [lengthState, Nat.add_comm] using
        lengthFold siblingTable.mul siblingLengthStep tail 1 (by omega)

private theorem lengthState_capped_injective
    {left right : Nat}
    (leftPositive : 0 < left) (rightPositive : 0 < right)
    (equal : lengthState left = lengthState right) :
    min left 3 = min right 3 := by
  by_cases leftOne : left = 1
  · subst left
    by_cases rightOne : right = 1
    · subst right
      rfl
    · by_cases rightTwo : right = 2
      · subst right
        have values := congrArg Fin.val equal
        simp [lengthState] at values
      · have rightThree : 3 ≤ right := by omega
        have values := congrArg Fin.val equal
        simp [lengthState, rightOne, rightTwo] at values
  · by_cases leftTwo : left = 2
    · subst left
      by_cases rightOne : right = 1
      · subst right
        have values := congrArg Fin.val equal
        simp [lengthState] at values
      · by_cases rightTwo : right = 2
        · subst right
          rfl
        · have rightThree : 3 ≤ right := by omega
          have values := congrArg Fin.val equal
          simp [lengthState, rightOne, rightTwo] at values
    · have leftThree : 3 ≤ left := by omega
      by_cases rightOne : right = 1
      · subst right
        have values := congrArg Fin.val equal
        simp [lengthState, leftOne, leftTwo] at values
      · by_cases rightTwo : right = 2
        · subst right
          have values := congrArg Fin.val equal
          simp [lengthState, leftOne, leftTwo] at values
        · have rightThree : 3 ≤ right := by omega
          simp [Nat.min_eq_right leftThree,
            Nat.min_eq_right rightThree]

private theorem cappedLength_of_valid
    (target : Semigroup (Fin 5))
    (evalLength :
      ∀ word : Word Nat,
        target.eval (fun _ => (2 : Fin 5)) word =
          lengthState word.toList.length)
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy target) :
    min identity.lhs.toList.length 3 =
      min identity.rhs.toList.length 3 := by
  have evaluated := valid (fun _ => (2 : Fin 5))
  rw [evalLength, evalLength] at evaluated
  exact lengthState_capped_injective
    (by simp [Word.toList]) (by simp [Word.toList]) evaluated

private theorem lengthTwo_eq_of_firstOccurrences
    (leftHead leftTail rightHead rightTail : Nat)
    (equal :
      firstOccurrenceSequence [leftHead, leftTail] =
        firstOccurrenceSequence [rightHead, rightTail]) :
    [leftHead, leftTail] = [rightHead, rightTail] := by
  by_cases leftRepeated : leftTail = leftHead <;>
    by_cases rightRepeated : rightTail = rightHead
  · subst leftTail
    subst rightTail
    simp [firstOccurrenceSequence] at equal
    simpa [equal]
  · subst leftTail
    simp [firstOccurrenceSequence, rightRepeated] at equal
  · subst rightTail
    simp [firstOccurrenceSequence, leftRepeated] at equal
  · simpa [firstOccurrenceSequence, leftRepeated, rightRepeated] using equal

private theorem signature_eq_of_invariants
    (left right : Word Nat)
    (order :
      firstOccurrenceSequence left.toList =
        firstOccurrenceSequence right.toList)
    (length :
      min left.toList.length 3 = min right.toList.length 3) :
    SameLongFirstOccurrenceSignature left right := by
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail =>
          cases leftTail with
          | nil =>
              cases rightTail with
              | nil =>
                  simp [SameLongFirstOccurrenceSignature,
                    longFirstOccurrenceSignature,
                    longFirstOccurrenceNormalList, Word.toList,
                    firstOccurrenceSequence] at order ⊢
                  exact order
              | cons rightSecond rightRest =>
                  simp [Word.toList] at length <;> omega
          | cons leftSecond leftRest =>
              cases leftRest with
              | nil =>
                  cases rightTail with
                  | nil => simp [Word.toList] at length <;> omega
                  | cons rightSecond rightRest =>
                      cases rightRest with
                      | nil =>
                          have words :=
                            lengthTwo_eq_of_firstOccurrences
                              leftHead leftSecond rightHead rightSecond <| by
                                simpa [Word.toList] using order
                          simpa [SameLongFirstOccurrenceSignature,
                            longFirstOccurrenceSignature,
                            longFirstOccurrenceNormalList, Word.toList] using
                              words
                      | cons rightThird rightMore =>
                          simp [Word.toList] at length <;> omega
              | cons leftThird leftMore =>
                  cases rightTail with
                  | nil => simp [Word.toList] at length <;> omega
                  | cons rightSecond rightRest =>
                      cases rightRest with
                      | nil => simp [Word.toList] at length <;> omega
                      | cons rightThird rightMore =>
                          unfold SameLongFirstOccurrenceSignature
                          unfold longFirstOccurrenceSignature
                          simp only [Word.toList,
                            longFirstOccurrenceNormalList]
                          exact congrArg
                            (fun occurrenceOrder =>
                              match occurrenceOrder with
                              | [a] => [a, a, a]
                              | [a, b] => [a, a, b]
                              | sequence => sequence) order

theorem s5_523SemanticSeparation : S5_523SemanticSeparation := by
  intro left right valid
  exact signature_eq_of_invariants left right
    (firstOccurrences_of_valid table.semigroup
      representativeLrbEmbedding ⟨left, right⟩ valid)
    (cappedLength_of_valid table.semigroup representativeEvalLength
      ⟨left, right⟩ valid)

theorem s5_539SemanticSeparation : S5_539SemanticSeparation := by
  intro left right valid
  exact signature_eq_of_invariants left right
    (firstOccurrences_of_valid siblingTable.semigroup
      siblingLrbEmbedding ⟨left, right⟩ valid)
    (cappedLength_of_valid siblingTable.semigroup siblingEvalLength
      ⟨left, right⟩ valid)

theorem representative_basis_of_certificates
    (normalization : LongFirstOccurrenceDerivationalCompleteness)
    (separation : S5_523SemanticSeparation) :
    BasisFor table.semigroup basis := by
  refine ⟨models, ?_⟩
  intro identity valid
  exact normalization identity.lhs identity.rhs <|
    separation identity.lhs identity.rhs valid

theorem sibling_basis_of_certificates
    (normalization : LongFirstOccurrenceDerivationalCompleteness)
    (separation : S5_539SemanticSeparation) :
    BasisFor siblingTable.semigroup basis := by
  refine ⟨siblingModels, ?_⟩
  intro identity valid
  exact normalization identity.lhs identity.rhs <|
    separation identity.lhs identity.rhs valid

theorem representative_opposite_basis_of_certificates
    (normalization : LongFirstOccurrenceDerivationalCompleteness)
    (separation : S5_523SemanticSeparation) :
    BasisFor table.semigroup.opposite expectedOppositeBasis := by
  rw [← oppositeBasis_eq_expected]
  exact
    (representative_basis_of_certificates normalization separation).oppositeReversed

theorem sibling_opposite_basis_of_certificates
    (normalization : LongFirstOccurrenceDerivationalCompleteness)
    (separation : S5_539SemanticSeparation) :
    BasisFor siblingTable.semigroup.opposite expectedOppositeBasis := by
  rw [← oppositeBasis_eq_expected]
  exact
    (sibling_basis_of_certificates normalization separation).oppositeReversed

/-- Unconditional direct endpoint for `S5_523`. -/
theorem representative_basis : BasisFor table.semigroup basis :=
  representative_basis_of_certificates
    longFirstOccurrenceDerivationalCompleteness
    s5_523SemanticSeparation

/-- Unconditional direct endpoint for `S5_539`. -/
theorem sibling_basis : BasisFor siblingTable.semigroup basis :=
  sibling_basis_of_certificates
    longFirstOccurrenceDerivationalCompleteness
    s5_539SemanticSeparation

/-- Unconditional opposite endpoint for `S5_523`. -/
theorem representative_opposite_basis :
    BasisFor table.semigroup.opposite expectedOppositeBasis :=
  representative_opposite_basis_of_certificates
    longFirstOccurrenceDerivationalCompleteness
    s5_523SemanticSeparation

/-- Unconditional opposite endpoint for `S5_539`. -/
theorem sibling_opposite_basis :
    BasisFor siblingTable.semigroup.opposite expectedOppositeBasis :=
  sibling_opposite_basis_of_certificates
    longFirstOccurrenceDerivationalCompleteness
    s5_539SemanticSeparation

end SemigroupBasis.CoRoots.S5_523
