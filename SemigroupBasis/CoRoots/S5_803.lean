import SemigroupBasis.CoRoots.S5_787Normalization
import SemigroupBasis.Examples.FinalMarkerThree
import SemigroupBasis.Generated.CatalogueOrder5Part07
import SemigroupBasis.Generated.S4_69
import SemigroupBasis.Opposite
import SemigroupBasis.TransferPower

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.S5_803

open SemigroupBasis
open SemigroupBasis.Examples

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def xx : Word Nat := w 0 [0]
def xxx : Word Nat := w 0 [0, 0]
def xyx : Word Nat := w 0 [1, 0]
def xyxx : Word Nat := w 0 [1, 0, 0]
def yyxx : Word Nat := w 1 [1, 0, 0]
def xyzx : Word Nat := w 0 [1, 2, 0]
def xzyx : Word Nat := w 0 [2, 1, 0]
def xyxz : Word Nat := w 0 [1, 0, 2]
def yxyz : Word Nat := w 1 [0, 1, 2]

def xxyx : Word Nat := w 0 [0, 1, 0]
def xxyy : Word Nat := w 0 [0, 1, 1]
def yzyx : Word Nat := w 1 [2, 1, 0]
def zyzx : Word Nat := w 2 [1, 2, 0]
def zxyx : Word Nat := w 2 [0, 1, 0]
def zyxy : Word Nat := w 2 [1, 0, 1]

def powerLaw : Identity Nat := ⟨xx, xxx⟩
def rightDuplicationLaw : Identity Nat := ⟨xyx, xyxx⟩
def squaresLaw : Identity Nat := ⟨xyx, yyxx⟩
def closedInteriorSwapLaw : Identity Nat := ⟨xyzx, xzyx⟩
def finalRotationLaw : Identity Nat := ⟨xyxz, yxyz⟩

/-- The exact five-law basis recorded at the lower-order frontier:
`xx = xxx`, `xyx = xyxx`, `xyx = yyxx`, `xyzx = xzyx`, and
`xyxz = yxyz`. -/
def basis : List (Identity Nat) :=
  [powerLaw, rightDuplicationLaw, squaresLaw,
    closedInteriorSwapLaw, finalRotationLaw]

/-- The literal reverse-word basis for the non-self-dual opposite. -/
def oppositeBasis : List (Identity Nat) :=
  reversedBasis basis

def expectedOppositeBasis : List (Identity Nat) :=
  [⟨xx, xxx⟩, ⟨xyx, xxyx⟩, ⟨xyx, xxyy⟩,
    ⟨xzyx, xyzx⟩, ⟨zxyx, zyxy⟩]

theorem oppositeBasis_eq_expected :
    oppositeBasis = expectedOppositeBasis := by
  decide

/-- The literal reversal of the already formalized `S5_787` basis. -/
def literalReversedSourceBasis : List (Identity Nat) :=
  [powerLaw, rightDuplicationLaw, squaresLaw,
    ⟨xzyx, xyzx⟩, ⟨yzyx, zyzx⟩]

theorem reversedSourceBasis_eq_literal :
    reversedBasis SemigroupBasis.CoRoots.S5_787.basis =
      literalReversedSourceBasis := by
  decide

private def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

def finiteBasis : List (Identity (Fin 3)) :=
  basis.map fun identity => identity.map toFinThree

private theorem basis_roundTrip_checked :
    basis.all (fun identity =>
      decide ((identity.map toFinThree).map Fin.val = identity)) = true := by
  decide

private theorem basis_roundTrip
    (identity : Identity Nat) (member : identity ∈ basis) :
    (identity.map toFinThree).map Fin.val = identity := by
  exact of_decide_eq_true <|
    (List.all_eq_true.mp basis_roundTrip_checked) identity member

/-- Exhaustive checks on the three displayed variables imply a `Models`
theorem over the standard infinite variable type. -/
theorem models_of_finite_checks
    (model : FiniteTable)
    (checks : finiteBasis.all model.checkIdentity = true) :
    Models model.semigroup basis := by
  intro identity member
  have finiteMember : identity.map toFinThree ∈ finiteBasis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    model.checkIdentityNat_sound (identity.map toFinThree)
      ((List.all_eq_true.mp checks) _ finiteMember)
  rw [basis_roundTrip identity member] at finiteValid
  exact finiteValid

abbrev table : FiniteTable :=
  Generated.Catalogue.S5_803.table

abbrev separatorTable : FiniteTable :=
  Generated.Catalogue.S4_69.table

theorem table_eq_canonical_catalogue :
    table = Generated.Catalogue.S5_803.table := rfl

theorem models : Models table.semigroup basis :=
  models_of_finite_checks table (by decide)

def tableRowsOneBased : List (List Nat) :=
  List.ofFn fun left : Fin 5 =>
    List.ofFn fun right : Fin 5 =>
      (table.mul left right).val + 1

theorem tableRowsOneBased_certificate :
    tableRowsOneBased =
      [[1, 1, 1, 1, 1],
        [1, 1, 1, 1, 2],
        [1, 2, 3, 4, 1],
        [1, 2, 3, 4, 1],
        [1, 1, 1, 1, 5]] := by
  decide

def oppositeTableRowsOneBased : List (List Nat) :=
  List.ofFn fun left : Fin 5 =>
    List.ofFn fun right : Fin 5 =>
      (table.semigroup.opposite.mul left right).val + 1

theorem oppositeTableRowsOneBased_certificate :
    oppositeTableRowsOneBased =
      [[1, 1, 1, 1, 1],
        [1, 1, 2, 2, 1],
        [1, 1, 3, 3, 1],
        [1, 1, 4, 4, 1],
        [1, 2, 1, 1, 5]] := by
  decide

/-- The first recorded copy `[1,2,3,5]` of `S4_69`. -/
def separatorEmbeddingFirst :
    Embedding separatorTable.semigroup table.semigroup where
  toFun := fun value =>
    if value.val = 0 then ⟨0, by decide⟩ else
      if value.val = 1 then ⟨1, by decide⟩ else
        if value.val = 2 then ⟨2, by decide⟩ else
          ⟨4, by decide⟩
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

/-- The second recorded copy `[1,2,4,5]` of `S4_69`. -/
def separatorEmbeddingSecond :
    Embedding separatorTable.semigroup table.semigroup where
  toFun := fun value =>
    if value.val = 0 then ⟨0, by decide⟩ else
      if value.val = 1 then ⟨1, by decide⟩ else
        if value.val = 2 then ⟨3, by decide⟩ else
          ⟨4, by decide⟩
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

/-- The right-zero-inflation quotient `[1,2,3,3,4]`. -/
def separatorQuotient :
    SplitSurjection table.semigroup separatorTable.semigroup where
  toFun := fun value =>
    if value.val = 0 then ⟨0, by decide⟩ else
      if value.val = 1 then ⟨1, by decide⟩ else
        if value.val = 2 then ⟨2, by decide⟩ else
          if value.val = 3 then ⟨2, by decide⟩ else
            ⟨3, by decide⟩
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  preimage := separatorEmbeddingFirst.toFun
  right_inverse := by
    intro value
    apply Fin.ext
    revert value
    decide

def separatorQuotientOneBased : List Nat :=
  List.ofFn fun value : Fin 5 =>
    (separatorQuotient.toFun value).val + 1

def separatorEmbeddingsOneBased : List (List Nat) :=
  [List.ofFn fun value : Fin 4 =>
      (separatorEmbeddingFirst.toFun value).val + 1,
    List.ofFn fun value : Fin 4 =>
      (separatorEmbeddingSecond.toFun value).val + 1]

theorem separatorQuotientOneBased_certificate :
    separatorQuotientOneBased = [1, 2, 3, 3, 4] := by
  decide

theorem separatorEmbeddingsOneBased_certificate :
    separatorEmbeddingsOneBased =
      [[1, 2, 3, 5], [1, 2, 4, 5]] := by
  decide

/-- The permutation `[1,2,4,3]` is the concrete self-duality of `S4_69`. -/
def separatorSelfDualValue (value : Fin 4) : Fin 4 :=
  if value.val = 2 then ⟨3, by decide⟩ else
    if value.val = 3 then ⟨2, by decide⟩ else
      value

def separatorSelfDualOneBased : List Nat :=
  List.ofFn fun value : Fin 4 =>
    (separatorSelfDualValue value).val + 1

theorem separatorSelfDualOneBased_certificate :
    separatorSelfDualOneBased = [1, 2, 4, 3] := by
  decide

@[simp]
theorem separatorSelfDualValue_involutive (value : Fin 4) :
    separatorSelfDualValue (separatorSelfDualValue value) = value := by
  revert value
  decide

/-- The anti-automorphism of `S4_69`, presented as an embedding from its
opposite back into the stored orientation. -/
def separatorSelfDualEmbedding :
    Embedding separatorTable.semigroup.opposite
      separatorTable.semigroup where
  toFun := separatorSelfDualValue
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right equality
    have inverseEquality :=
      congrArg separatorSelfDualValue equality
    simpa using inverseEquality

/-- Zero-based states `2` and `3` form the split right-zero fiber. -/
def rightZeroFiberValue (value : Fin 2) : Fin 5 :=
  if value = 0 then 2 else 3

def rightZeroFiberOneBased : List Nat :=
  List.ofFn fun value : Fin 2 =>
    (rightZeroFiberValue value).val + 1

theorem rightZeroFiberOneBased_certificate :
    rightZeroFiberOneBased = [3, 4] := by
  decide

theorem rightZeroFiber_mul (left right : Fin 2) :
    table.mul (rightZeroFiberValue left)
        (rightZeroFiberValue right) =
      rightZeroFiberValue right := by
  revert left right
  decide

def leftTranslation (value : Fin 5) : Fin 5 → Fin 5 :=
  fun right => table.mul value right

def rightTranslation (value : Fin 5) : Fin 5 → Fin 5 :=
  fun left => table.mul left value

def rightTranslationCode (value : Fin 5) : Fin 5 × Fin 5 :=
  (table.mul ⟨1, by decide⟩ value,
    table.mul ⟨2, by decide⟩ value)

theorem splitFiber_leftTranslation_eq :
    leftTranslation 2 = leftTranslation 3 := by
  funext right
  revert right
  decide

theorem rightTranslationCode_injective :
    Function.Injective rightTranslationCode := by
  intro left right
  revert left right
  decide

theorem rightTranslation_injective :
    Function.Injective rightTranslation := by
  intro left right equality
  apply rightTranslationCode_injective
  apply Prod.ext
  · simpa [rightTranslationCode, rightTranslation] using
      congrFun equality (⟨1, by decide⟩ : Fin 5)
  · simpa [rightTranslationCode, rightTranslation] using
      congrFun equality (⟨2, by decide⟩ : Fin 5)

/-- There is no bijective anti-homomorphism from the stored `S5_803`
table to itself. Equal left translations of the split fiber would be
carried to equal right translations, but all right translations are
distinct. -/
theorem noAntiAutomorphism
    (f : Fin 5 → Fin 5)
    (injective : Function.Injective f)
    (surjective : Function.Surjective f)
    (anti :
      ∀ left right,
        f (table.mul left right) =
          table.mul (f right) (f left)) :
    False := by
  have rightEqual :
      rightTranslation (f 2) = rightTranslation (f 3) := by
    funext image
    obtain ⟨source, rfl⟩ := surjective image
    change
      table.mul (f source) (f 2) =
        table.mul (f source) (f 3)
    calc
      table.mul (f source) (f 2) =
          f (table.mul ⟨2, by decide⟩ source) :=
        (anti (⟨2, by decide⟩ : Fin 5) source).symm
      _ = f (table.mul ⟨3, by decide⟩ source) := by
          apply congrArg f
          simpa [leftTranslation] using
            congrFun splitFiber_leftTranslation_eq source
      _ = table.mul (f source) (f 3) :=
        anti (⟨3, by decide⟩ : Fin 5) source
  have imageEquality : f 2 = f 3 :=
    rightTranslation_injective rightEqual
  have sourceEquality : (2 : Fin 5) = 3 :=
    injective imageEquality
  exact (by decide : (2 : Fin 5) ≠ 3) sourceEquality

theorem not_self_dual :
    ¬ ∃ f : Fin 5 → Fin 5,
      (Function.Injective f ∧ Function.Surjective f) ∧
        ∀ left right,
          f (table.mul left right) =
            table.mul (f right) (f left) := by
  rintro ⟨f, bijective, anti⟩
  exact noAntiAutomorphism f bijective.1 bijective.2 anti

/-- A valuation into the right-zero fiber which marks one tested
variable. -/
def finalSeparator (tested : Nat) : Nat → Fin 5 :=
  fun letter => if letter = tested then 2 else 3

private theorem finalSeparator_mul
    (tested leftLetter rightLetter : Nat) :
    Generated.Catalogue.S5_803.mul
        (finalSeparator tested leftLetter)
        (finalSeparator tested rightLetter) =
      finalSeparator tested rightLetter := by
  by_cases leftEqual : leftLetter = tested <;>
    by_cases rightEqual : rightLetter = tested <;>
      simp [finalSeparator, leftEqual, rightEqual, eq_comm,
        Generated.Catalogue.S5_803.mul]

theorem finalSeparator_eval
    (tested : Nat) (stem : List Nat) (final : Nat) :
    table.semigroup.eval (finalSeparator tested)
        (wordOfPrefixFinal stem final) =
      finalSeparator tested final := by
  induction stem with
  | nil => rfl
  | cons letter rest induction =>
      rw [wordOfPrefixFinal_cons, Semigroup.eval_append,
        Semigroup.eval_singleton, induction]
      exact finalSeparator_mul tested letter final

theorem valid_final_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    (splitPrefixFinal identity.lhs).2 =
      (splitPrefixFinal identity.rhs).2 := by
  let tested := (splitPrefixFinal identity.lhs).2
  have evaluated := valid (finalSeparator tested)
  rw [← wordOfPrefixFinal_split identity.lhs,
    ← wordOfPrefixFinal_split identity.rhs,
    finalSeparator_eval, finalSeparator_eval] at evaluated
  apply Decidable.byContradiction
  intro different
  have reverseDifferent :
      (splitPrefixFinal identity.rhs).2 ≠
        (splitPrefixFinal identity.lhs).2 :=
    Ne.symm different
  simp [tested, finalSeparator, reverseDifferent] at evaluated

private theorem reverse_wordOfPrefixFinal_head
    (stem : List Nat) (final : Nat) :
    (wordOfPrefixFinal stem final).reverse.head = final := by
  induction stem with
  | nil => rfl
  | cons letter rest induction =>
      rw [wordOfPrefixFinal_cons, Word.reverse_append]
      simpa using induction

theorem reverseHead_eq_splitFinal (word : Word Nat) :
    word.reverse.head = (splitPrefixFinal word).2 := by
  have reconstructed :=
    congrArg (fun rebuilt : Word Nat => rebuilt.reverse.head)
      (wordOfPrefixFinal_split word)
  exact reconstructed.symm.trans <|
    reverse_wordOfPrefixFinal_head
      (splitPrefixFinal word).1
      (splitPrefixFinal word).2

theorem valid_reversed_head_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.lhs.reverse.head =
      identity.rhs.reverse.head := by
  exact
    (reverseHead_eq_splitFinal identity.lhs).trans <|
      (valid_final_eq identity valid).trans <|
        (reverseHead_eq_splitFinal identity.rhs).symm

/-- Reversal of every `S5_803` identity is valid in `S4_69`: first pass
to the quotient, then pull back across the concrete self-duality. -/
theorem valid_reversed_separator
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.reversed.SatisfiedBy separatorTable.semigroup := by
  have separatorValid :
      identity.SatisfiedBy separatorTable.semigroup :=
    separatorQuotient.pushforwardIdentity identity valid
  have oppositeValid :
      identity.SatisfiedBy separatorTable.semigroup.opposite :=
    separatorSelfDualEmbedding.pullback_identity
      identity separatorValid
  exact
    (Identity.satisfiedBy_opposite_iff_reversed
      identity separatorTable.semigroup).mp oppositeValid

/-- The exact semantic input expected by the completed `S5_787`
separator-first normalizer, applied after word reversal. -/
theorem valid_reversed_signature
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    S5_787Invariant.SameSeparatorFirstSignature
      identity.lhs.reverse identity.rhs.reverse := by
  have separatorValid :=
    valid_reversed_separator identity valid
  exact
    ⟨S5_441Invariant.sameSupport_of_s4_69_valid
        identity.reversed separatorValid,
      S5_441Invariant.sameExactCutSignature_of_s4_69_valid
        identity.reversed separatorValid,
      valid_reversed_head_eq identity valid⟩

private theorem targetPowerDerives :
    Derives basis xx xxx :=
  Derives.fromBasis (e := powerLaw) (by simp [basis])

private theorem targetRightDuplicationDerives :
    Derives basis xyx xyxx :=
  Derives.fromBasis (e := rightDuplicationLaw) (by simp [basis])

private theorem targetSquaresDerives :
    Derives basis xyx yyxx :=
  Derives.fromBasis (e := squaresLaw) (by simp [basis])

private theorem targetClosedInteriorDerives :
    Derives basis xyzx xzyx :=
  Derives.fromBasis (e := closedInteriorSwapLaw) (by simp [basis])

private theorem targetFinalRotationDerives :
    Derives basis xyxz yxyz :=
  Derives.fromBasis (e := finalRotationLaw) (by simp [basis])

private theorem reversedSourcePowerDerives :
    Derives (reversedBasis SemigroupBasis.CoRoots.S5_787.basis)
      xx xxx := by
  apply Derives.fromBasis (e := powerLaw)
  rw [reversedSourceBasis_eq_literal]
  simp [literalReversedSourceBasis, powerLaw]

private theorem reversedSourceRightDuplicationDerives :
    Derives (reversedBasis SemigroupBasis.CoRoots.S5_787.basis)
      xyx xyxx := by
  apply Derives.fromBasis (e := rightDuplicationLaw)
  rw [reversedSourceBasis_eq_literal]
  simp [literalReversedSourceBasis, rightDuplicationLaw]

private theorem reversedSourceSquaresDerives :
    Derives (reversedBasis SemigroupBasis.CoRoots.S5_787.basis)
      xyx yyxx := by
  apply Derives.fromBasis (e := squaresLaw)
  rw [reversedSourceBasis_eq_literal]
  simp [literalReversedSourceBasis, squaresLaw]

private theorem reversedSourceClosedInteriorDerives :
    Derives (reversedBasis SemigroupBasis.CoRoots.S5_787.basis)
      xzyx xyzx := by
  apply Derives.fromBasis (e := ⟨xzyx, xyzx⟩)
  rw [reversedSourceBasis_eq_literal]
  simp [literalReversedSourceBasis]

private theorem reversedSourceFinalRotationDerives :
    Derives (reversedBasis SemigroupBasis.CoRoots.S5_787.basis)
      yzyx zyzx := by
  apply Derives.fromBasis (e := ⟨yzyx, zyzx⟩)
  rw [reversedSourceBasis_eq_literal]
  simp [literalReversedSourceBasis]

private def sourceToTargetRename : Nat → Word Nat
  | 0 => Word.singleton 2
  | 1 => Word.singleton 0
  | 2 => Word.singleton 1
  | n + 3 => Word.singleton (n + 3)

private def targetToSourceRename : Nat → Word Nat
  | 0 => Word.singleton 1
  | 1 => Word.singleton 2
  | 2 => Word.singleton 0
  | n + 3 => Word.singleton (n + 3)

theorem sourceFinalRotationDerivesTarget :
    Derives (reversedBasis SemigroupBasis.CoRoots.S5_787.basis)
      xyxz yxyz := by
  have renamed :=
    Derives.subst reversedSourceFinalRotationDerives
      sourceToTargetRename
  simpa [xyxz, yxyz, yzyx, zyzx, w, sourceToTargetRename,
    Word.bind, Word.singleton, Word.append] using renamed

theorem targetFinalRotationDerivesSource :
    Derives basis yzyx zyzx := by
  have renamed :=
    Derives.subst targetFinalRotationDerives
      targetToSourceRename
  simpa [xyxz, yxyz, yzyx, zyzx, w, targetToSourceRename,
    Word.bind, Word.singleton, Word.append] using renamed

/-- Every literal reversed `S5_787` axiom follows from the exact
frontier basis. The fourth law uses symmetry and the fifth uses the
inverse cyclic renaming `x -> y -> z -> x`. -/
theorem reversedSourceAxiomsDeriveTarget
    (identity : Identity Nat)
    (member :
      identity ∈
        reversedBasis SemigroupBasis.CoRoots.S5_787.basis) :
    Derives basis identity.lhs identity.rhs := by
  rw [reversedSourceBasis_eq_literal] at member
  simp only [literalReversedSourceBasis, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact targetPowerDerives
  · exact targetRightDuplicationDerives
  · exact targetSquaresDerives
  · exact targetClosedInteriorDerives.symm
  · exact targetFinalRotationDerivesSource

/-- Conversely, every exact frontier axiom follows from the literal
reversed `S5_787` basis. The final law uses the cyclic renaming
`x -> z`, `y -> x`, `z -> y`. -/
theorem targetAxiomsDeriveReversedSource
    (identity : Identity Nat)
    (member : identity ∈ basis) :
    Derives (reversedBasis SemigroupBasis.CoRoots.S5_787.basis)
      identity.lhs identity.rhs := by
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact reversedSourcePowerDerives
  · exact reversedSourceRightDuplicationDerives
  · exact reversedSourceSquaresDerives
  · exact reversedSourceClosedInteriorDerives.symm
  · exact sourceFinalRotationDerivesTarget

theorem reversedSourceModels :
    Models table.semigroup
      (reversedBasis SemigroupBasis.CoRoots.S5_787.basis) := by
  intro identity member valuation
  exact
    (reversedSourceAxiomsDeriveTarget identity member).sound
      models valuation

/-- Completeness of the literal reversed `S5_787` source basis for the
stored `S5_803` table. This is the reversal-transfer step: semantic
validity gives the reversed separator-first signature, the complete
`S5_787` normalizer derives the reversed words, and `Derives.reverse`
returns to the original orientation. -/
theorem reversed_source_basis_complete :
    BasisFor table.semigroup
      (reversedBasis SemigroupBasis.CoRoots.S5_787.basis) := by
  refine ⟨reversedSourceModels, ?_⟩
  intro identity valid
  have normalized :=
    SemigroupBasis.CoRoots.S5_787.derives_of_sameSeparatorFirstSignature
      (valid_reversed_signature identity valid)
  have reversed := Derives.reverse normalized
  simpa using reversed

/-- Unconditional exact-basis endpoint in the stored catalogue
orientation. -/
theorem representative_basis :
    BasisFor table.semigroup basis :=
  reversed_source_basis_complete.replace
    models reversedSourceAxiomsDeriveTarget

/-- Unconditional exact-basis endpoint for the non-self-dual opposite
orientation. -/
theorem opposite_basis :
    BasisFor table.semigroup.opposite oppositeBasis := by
  simpa [oppositeBasis] using
    representative_basis.oppositeReversed

end SemigroupBasis.CoRoots.S5_803
