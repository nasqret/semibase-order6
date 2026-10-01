import SemigroupBasis.CoRoots.S5_863
import SemigroupBasis.CoRoots.S5_345Factors

namespace SemigroupBasis.CoRoots.S5_863

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.S5_107

/-- The exact invariant recorded for `S5_863`: first-occurrence order,
multiplicity capped at two, and the literal final variable. -/
structure SameInitialSimpleFinalSignature
    (left right : Word Nat) : Prop where
  firstOccurrences :
    firstOccurrenceSequence left.toList =
      firstOccurrenceSequence right.toList
  capped :
    forall letter,
      cappedMultiplicity left letter =
        cappedMultiplicity right letter
  finalLetter : left.final = right.final

namespace SameInitialSimpleFinalSignature

theorem refl (word : Word Nat) :
    SameInitialSimpleFinalSignature word word :=
  ⟨rfl, fun _ => rfl, rfl⟩

theorem symm {left right : Word Nat}
    (same : SameInitialSimpleFinalSignature left right) :
    SameInitialSimpleFinalSignature right left :=
  ⟨same.firstOccurrences.symm,
    fun letter => (same.capped letter).symm,
    same.finalLetter.symm⟩

theorem trans {left middle right : Word Nat}
    (first : SameInitialSimpleFinalSignature left middle)
    (second : SameInitialSimpleFinalSignature middle right) :
    SameInitialSimpleFinalSignature left right :=
  ⟨first.firstOccurrences.trans second.firstOccurrences,
    fun letter =>
      (first.capped letter).trans (second.capped letter),
    first.finalLetter.trans second.finalLetter⟩

/-- Equal signatures preserve absence of every variable. -/
theorem absent {left right : Word Nat}
    (same : SameInitialSimpleFinalSignature left right)
    (letter : Nat) :
    letter ∉ left.toList ↔ letter ∉ right.toList := by
  rw [← List.count_eq_zero, ← List.count_eq_zero,
    ← cappedMultiplicity_eq_zero_iff,
    ← cappedMultiplicity_eq_zero_iff, same.capped letter]

/-- Equal signatures preserve word support. -/
theorem support {left right : Word Nat}
    (same : SameInitialSimpleFinalSignature left right)
    (letter : Nat) :
    letter ∈ left.toList ↔ letter ∈ right.toList := by
  simpa using not_congr (same.absent letter)

/-- Equal signatures preserve globally simple variables. -/
theorem simple {left right : Word Nat}
    (same : SameInitialSimpleFinalSignature left right)
    (letter : Nat) :
    SimpleIn left letter ↔ SimpleIn right letter := by
  unfold SimpleIn
  rw [← cappedMultiplicity_eq_one_iff,
    ← cappedMultiplicity_eq_one_iff, same.capped letter]

/-- Equal signatures preserve variables occurring at least twice. -/
theorem multiple {left right : Word Nat}
    (same : SameInitialSimpleFinalSignature left right)
    (letter : Nat) :
    2 ≤ left.toList.count letter ↔
      2 ≤ right.toList.count letter := by
  rw [← S5_345.cappedMultiplicity_eq_two_iff,
    ← S5_345.cappedMultiplicity_eq_two_iff, same.capped letter]

theorem cappedFunction_eq {left right : Word Nat}
    (same : SameInitialSimpleFinalSignature left right) :
    cappedMultiplicity left = cappedMultiplicity right :=
  funext same.capped

end SameInitialSimpleFinalSignature

/-- The exact five-element catalogue table for `S5_863`. -/
abbrev catalogueTable : FiniteTable :=
  Generated.Catalogue.S5_863.table

/-- Quotient with zero-based fibers `[0, 0, 2, 1, 1]`.  It records the
complete sequence of first occurrences. -/
def firstOccurrenceQuotient :
    SplitSurjection catalogueTable.semigroup
      leftRegularBandThree.semigroup where
  toFun := fun value =>
    if value.val = 0 then ⟨0, by decide⟩ else
      if value.val = 1 then ⟨0, by decide⟩ else
        if value.val = 2 then ⟨2, by decide⟩ else
          ⟨1, by decide⟩
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  preimage := fun value =>
    if value.val = 0 then ⟨0, by decide⟩ else
      if value.val = 1 then ⟨3, by decide⟩ else
        ⟨2, by decide⟩
  right_inverse := by
    intro value
    apply Fin.ext
    revert value
    decide

/-- Quotient with zero-based fibers `[0, 1, 0, 2, 2]`.  Its states mean
multiple, simple, and absent, respectively. -/
def cappedMultiplicityQuotient :
    SplitSurjection catalogueTable.semigroup
      commutativeExponentThree.semigroup where
  toFun := fun value =>
    if value.val = 0 then ⟨0, by decide⟩ else
      if value.val = 1 then ⟨1, by decide⟩ else
        if value.val = 2 then ⟨0, by decide⟩ else
          ⟨2, by decide⟩
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  preimage := fun value =>
    if value.val = 0 then ⟨0, by decide⟩ else
      if value.val = 1 then ⟨1, by decide⟩ else
        ⟨3, by decide⟩
  right_inverse := by
    intro value
    apply Fin.ext
    revert value
    decide

/-- One-based outputs from the finite certificate: no selected variable gives
state `4`, selected first gives `1`, and comparator first gives `3`. -/
theorem firstOccurrenceMarkerOutputs :
    firstOccurrenceQuotient.preimage (1 : Fin 3) = (3 : Fin 5) ∧
      firstOccurrenceQuotient.preimage (0 : Fin 3) = (0 : Fin 5) ∧
        firstOccurrenceQuotient.preimage (2 : Fin 3) = (2 : Fin 5) := by
  decide

/-- One-based outputs from the finite certificate: absent, simple, and
multiple selected variables give states `4`, `2`, and `1`. -/
theorem cappedMultiplicityMarkerOutputs :
    cappedMultiplicityQuotient.preimage (2 : Fin 3) = (3 : Fin 5) ∧
      cappedMultiplicityQuotient.preimage (1 : Fin 3) = (1 : Fin 5) ∧
        cappedMultiplicityQuotient.preimage (0 : Fin 3) = (0 : Fin 5) := by
  decide

theorem valid_firstOccurrenceSequence_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy catalogueTable.semigroup) :
    firstOccurrenceSequence identity.lhs.toList =
      firstOccurrenceSequence identity.rhs.toList :=
  S5_345Factors.leftRegularBandThreeValid_firstOccurrenceSequence_eq
    identity
    (firstOccurrenceQuotient.pushforwardIdentity identity valid)

theorem valid_cappedMultiplicity_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy catalogueTable.semigroup) :
    forall letter,
      cappedMultiplicity identity.lhs letter =
        cappedMultiplicity identity.rhs letter := by
  intro letter
  simpa [cappedMultiplicity, Nat.min_comm] using
    exponentValid_capped_count_eq identity
      (cappedMultiplicityQuotient.pushforwardIdentity identity valid)
      letter

/-- The source-table final marker from the finite certificate: tested
variables receive one-based state `5`, and all others state `4`. -/
def finalMarker (tested : Nat) : Nat → Fin 5 :=
  fun letter => if letter = tested then 4 else 3

theorem finalMarkerOutputs
    (tested other : Nat) (different : other ≠ tested) :
    finalMarker tested tested = (4 : Fin 5) ∧
      finalMarker tested other = (3 : Fin 5) := by
  simp [finalMarker, different]

private theorem finalMarker_mul
    (tested leftLetter rightLetter : Nat) :
    Generated.Catalogue.S5_863.mul
        (finalMarker tested leftLetter)
        (finalMarker tested rightLetter) =
      finalMarker tested rightLetter := by
  by_cases leftEqual : leftLetter = tested
  · subst leftLetter
    by_cases rightEqual : rightLetter = tested
    · subst rightLetter
      simp [finalMarker, Generated.Catalogue.S5_863.mul]
    · simp [finalMarker, rightEqual, eq_comm,
        Generated.Catalogue.S5_863.mul]
  · by_cases rightEqual : rightLetter = tested
    · subst rightLetter
      simp [finalMarker, leftEqual, eq_comm,
        Generated.Catalogue.S5_863.mul]
    · simp [finalMarker, leftEqual, rightEqual, eq_comm,
        Generated.Catalogue.S5_863.mul]

theorem finalMarker_eval
    (tested : Nat) (stem : List Nat) (final : Nat) :
    catalogueTable.semigroup.eval (finalMarker tested)
        (wordOfPrefixFinal stem final) =
      finalMarker tested final := by
  induction stem with
  | nil => rfl
  | cons letter rest induction =>
      rw [wordOfPrefixFinal_cons, Semigroup.eval_append,
        Semigroup.eval_singleton, induction]
      exact finalMarker_mul tested letter final

private theorem final_wordOfPrefixFinal
    (stem : List Nat) (final : Nat) :
    (wordOfPrefixFinal stem final).final = final := by
  induction stem with
  | nil => rfl
  | cons letter rest induction =>
      rw [wordOfPrefixFinal_cons, Word.final_append]
      exact induction

theorem valid_final_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy catalogueTable.semigroup) :
    identity.lhs.final = identity.rhs.final := by
  have splitFinalEq :
      (splitPrefixFinal identity.lhs).2 =
        (splitPrefixFinal identity.rhs).2 := by
    let tested := (splitPrefixFinal identity.lhs).2
    have evaluated := valid (finalMarker tested)
    rw [← wordOfPrefixFinal_split identity.lhs,
      ← wordOfPrefixFinal_split identity.rhs,
      finalMarker_eval, finalMarker_eval] at evaluated
    apply Decidable.byContradiction
    intro different
    have reversed :
        (splitPrefixFinal identity.rhs).2 =
          (splitPrefixFinal identity.lhs).2 := by
      simpa [tested, finalMarker, different] using evaluated
    exact different reversed.symm
  have leftFinal :
      (splitPrefixFinal identity.lhs).2 =
        identity.lhs.final := by
    have reconstructed :=
      congrArg Word.final (wordOfPrefixFinal_split identity.lhs)
    rw [final_wordOfPrefixFinal] at reconstructed
    exact reconstructed
  have rightFinal :
      (splitPrefixFinal identity.rhs).2 =
        identity.rhs.final := by
    have reconstructed :=
      congrArg Word.final (wordOfPrefixFinal_split identity.rhs)
    rw [final_wordOfPrefixFinal] at reconstructed
    exact reconstructed
  exact leftFinal.symm.trans (splitFinalEq.trans rightFinal)

/-- Every valid identity of the exact catalogue table has the recorded
initial/simple/final signature. -/
theorem valid_sameSignature
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy catalogueTable.semigroup) :
    SameInitialSimpleFinalSignature identity.lhs identity.rhs :=
  ⟨valid_firstOccurrenceSequence_eq identity valid,
    valid_cappedMultiplicity_eq identity valid,
    valid_final_eq identity valid⟩

/-- The five displayed basis laws hold in the exact catalogue table. -/
theorem table_models_basis :
    Models catalogueTable.semigroup basis :=
  catalogueModels

set_option maxRecDepth 100000 in
/-- Preservation lifts through every equational derivation from the five-law
basis.  In particular, this covers contexts and further substitutions. -/
theorem derives_sameSignature
    {left right : Word Nat}
    (derivation : Derives basis left right) :
    SameInitialSimpleFinalSignature left right := by
  exact valid_sameSignature ⟨left, right⟩
    (fun valuation => derivation.sound table_models_basis valuation)

/-- Every one of the five basis laws preserves the exact signature after an
arbitrary simultaneous nonempty-word substitution.  Nonemptiness is enforced
by the codomain `Word Nat`. -/
theorem basisLaw_bind_sameSignature
    (identity : Identity Nat) (member : identity ∈ basis)
    (substitution : Nat → Word Nat) :
    SameInitialSimpleFinalSignature
      (identity.lhs.bind substitution)
      (identity.rhs.bind substitution) :=
  derives_sameSignature <|
    Derives.subst (Derives.fromBasis member) substitution

theorem powerLaw_bind_sameSignature
    (substitution : Nat → Word Nat) :
    SameInitialSimpleFinalSignature
      (powerLaw.lhs.bind substitution)
      (powerLaw.rhs.bind substitution) :=
  basisLaw_bind_sameSignature powerLaw (by simp [basis]) substitution

theorem leftEndpointDuplicationLaw_bind_sameSignature
    (substitution : Nat → Word Nat) :
    SameInitialSimpleFinalSignature
      (leftEndpointDuplicationLaw.lhs.bind substitution)
      (leftEndpointDuplicationLaw.rhs.bind substitution) :=
  basisLaw_bind_sameSignature leftEndpointDuplicationLaw
    (by simp [basis]) substitution

theorem rightEndpointDuplicationLaw_bind_sameSignature
    (substitution : Nat → Word Nat) :
    SameInitialSimpleFinalSignature
      (rightEndpointDuplicationLaw.lhs.bind substitution)
      (rightEndpointDuplicationLaw.rhs.bind substitution) :=
  basisLaw_bind_sameSignature rightEndpointDuplicationLaw
    (by simp [basis]) substitution

theorem squareInterleaveLaw_bind_sameSignature
    (substitution : Nat → Word Nat) :
    SameInitialSimpleFinalSignature
      (squareInterleaveLaw.lhs.bind substitution)
      (squareInterleaveLaw.rhs.bind substitution) :=
  basisLaw_bind_sameSignature squareInterleaveLaw
    (by simp [basis]) substitution

theorem doubledInitialMoveLaw_bind_sameSignature
    (substitution : Nat → Word Nat) :
    SameInitialSimpleFinalSignature
      (doubledInitialMoveLaw.lhs.bind substitution)
      (doubledInitialMoveLaw.rhs.bind substitution) :=
  basisLaw_bind_sameSignature doubledInitialMoveLaw
    (by simp [basis]) substitution

end SemigroupBasis.CoRoots.S5_863
