import SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank082
import SemigroupBasis.CoRoots.Order6Day7.S3_16.SeedS5_353Opposite
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCTransportNormalizer
import SemigroupBasis.CoRoots.S5_203Family
import SemigroupBasis.CoRoots.S5_523

/-!
# The exact first-occurrence/initial-state bridge for rank 082

Four checked finite product embeddings identify the unrestricted theory of
`S3_16 × S5_203ᵒᵖ` with that of `S5_523 × S5_203ᵒᵖ`.  Behind two arbitrary
nonempty INITIAL guards the exact frozen presentation replays both complete
left-regular-band axioms and all five complete `S5_523` axioms.  Both lifts
handle arbitrary contexts and substitutions.  Thus equal full
first-occurrence order suffices for every doubly initially guarded identity.

The opposite factor's independently complete direct theory supplies the
reversed terminal signature, including the initial-doubleton state.  Global
initial double-guard cancellation is formally false.  The sole unproved
unrestricted obligation is exposed as cancellation conditioned on BOTH
complete owner signatures; no unconditional class theorem is asserted.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank082.InitialGuard

open SemigroupBasis
open SemigroupBasis.Examples

universe u

abbrev ownerLeft : FiniteTable :=
  SemigroupBasis.Generated.Catalogue.S5_523.table

abbrev ownerRight : FiniteTable := rightTable

abbrev targetProduct : Semigroup (Fin 3 × Fin 5) :=
  leftTable.semigroup.prod rightTable.semigroup

abbrev ownerProduct : Semigroup (Fin 5 × Fin 5) :=
  ownerLeft.semigroup.prod ownerRight.semigroup

/-- Exact one-based target coordinates `[1,1,1,2,3] × [1,2,4,1,1]`. -/
def ownerLeftIntoTargetProduct :
    Embedding ownerLeft.semigroup targetProduct where
  toFun := fun value =>
    (if value.val = 3 then 1 else if value.val = 4 then 2 else 0,
      if value.val = 1 then 1 else if value.val = 2 then 3 else 0)
  map_mul := by
    intro first second
    apply Prod.ext <;> apply Fin.ext <;> revert first second <;> decide
  injective := by
    intro first second equal
    revert first second
    decide

/-- Exact one-based target coordinates `[1,1,1,1,1] × [1,2,3,4,5]`. -/
def ownerRightIntoTargetProduct :
    Embedding ownerRight.semigroup targetProduct where
  toFun := fun value => (0, value)
  map_mul := by
    intro first second
    apply Prod.ext <;> apply Fin.ext <;> revert first second <;> decide
  injective := by
    intro first second equal
    exact congrArg Prod.snd equal

/-- Exact one-based owner coordinates `[1,4,5] × [1,1,1]`. -/
def targetLeftIntoOwnerProduct :
    Embedding leftTable.semigroup ownerProduct where
  toFun := fun value =>
    (if value.val = 1 then 3 else if value.val = 2 then 4 else 0, 0)
  map_mul := by
    intro first second
    apply Prod.ext <;> apply Fin.ext <;> revert first second <;> decide
  injective := by
    intro first second equal
    revert first second
    decide

/-- Exact one-based owner coordinates `[1,1,1,1,1] × [1,2,3,4,5]`. -/
def targetRightIntoOwnerProduct :
    Embedding rightTable.semigroup ownerProduct where
  toFun := fun value => (0, value)
  map_mul := by
    intro first second
    apply Prod.ext <;> apply Fin.ext <;> revert first second <;> decide
  injective := by
    intro first second equal
    exact congrArg Prod.snd equal

/-- Exact factor-theory equality on EVERY alphabet, not a bounded profile. -/
theorem ownerPairTheory_iff_targetPairTheory
    {α : Type u} (identity : Identity α) :
    (identity.SatisfiedBy leftTable.semigroup ∧
      identity.SatisfiedBy rightTable.semigroup) ↔
      (identity.SatisfiedBy ownerLeft.semigroup ∧
        identity.SatisfiedBy ownerRight.semigroup) := by
  constructor
  · rintro ⟨leftValid, rightValid⟩
    have product := Identity.satisfiedBy_prod leftValid rightValid
    exact ⟨ownerLeftIntoTargetProduct.pullback_identity identity product,
      ownerRightIntoTargetProduct.pullback_identity identity product⟩
  · rintro ⟨leftValid, rightValid⟩
    have product := Identity.satisfiedBy_prod leftValid rightValid
    exact ⟨targetLeftIntoOwnerProduct.pullback_identity identity product,
      targetRightIntoOwnerProduct.pullback_identity identity product⟩

/-- Kernel-green rank 046's initial-double swap changes first-occurrence order. -/
theorem legacyInitialDoubleSwap_not_leftValid :
    ¬ (Identity.mk (Word.mk 0 [0, 1, 2])
        (Word.mk 0 [0, 2, 1])).SatisfiedBy leftTable.semigroup := by
  intro valid
  have witness := valid
    (fun letter =>
      if letter = 0 then (1 : Fin 3) else
        if letter = 1 then (0 : Fin 3) else (2 : Fin 3))
  change (0 : Fin 3) = 2 at witness
  omega

/-- Its repeated-marker switch likewise changes full first-occurrence order. -/
theorem legacyMarkerSwitch_not_leftValid :
    ¬ (Identity.mk (Word.mk 0 [1, 1, 2])
        (Word.mk 0 [2, 1, 2])).SatisfiedBy leftTable.semigroup := by
  intro valid
  have witness := valid
    (fun letter =>
      if letter = 0 then (1 : Fin 3) else
        if letter = 1 then (0 : Fin 3) else (2 : Fin 3))
  change (0 : Fin 3) = 2 at witness
  omega

/-- Unguarded LRB idempotence destroys an actual initial-factor state. -/
theorem lrbIdempotence_not_rightValid :
    ¬ lrbIdempotenceLaw.SatisfiedBy rightTable.semigroup := by
  intro valid
  have witness := valid (fun _ => (1 : Fin 5))
  change (1 : Fin 5) = 0 at witness
  omega

/-- Unguarded LRB regularity also destroys an actual initial-factor state. -/
theorem lrbRegular_not_rightValid :
    ¬ lrbRegularLaw.SatisfiedBy rightTable.semigroup := by
  intro valid
  have witness := valid
    (fun letter => if letter = 0 then (1 : Fin 5) else (4 : Fin 5))
  change (1 : Fin 5) = 0 at witness
  omega

/-- One initial guard does not suffice for the LRB regularity replay. -/
theorem oneInitialGuardLrbRegular_not_rightValid :
    ¬ (Identity.mk (Word.mk 2 [0, 1])
        (Word.mk 2 [0, 1, 0])).SatisfiedBy rightTable.semigroup := by
  intro valid
  have witness := valid
    (fun letter =>
      if letter = 0 then (2 : Fin 5) else
        if letter = 1 then (4 : Fin 5) else (3 : Fin 5))
  change (1 : Fin 5) = 0 at witness
  omega

/-- One initial guard also fails for the complete owner's transfer axiom. -/
theorem oneInitialGuardOwnerTransfer_not_rightValid :
    ¬ (Identity.mk (Word.mk 2 [0, 0, 1])
        (Word.mk 2 [0, 1, 1])).SatisfiedBy rightTable.semigroup := by
  intro valid
  have witness := valid
    (fun letter =>
      if letter = 0 then (2 : Fin 5) else
        if letter = 1 then (4 : Fin 5) else (3 : Fin 5))
  change (0 : Fin 5) = 1 at witness
  omega

/-- An initial doubleton is not an initial triple in the opposite factor. -/
theorem initialDoubletonSquareCube_not_rightValid :
    ¬ (Identity.mk (Word.mk 0 [0])
        (Word.mk 0 [0, 0])).SatisfiedBy rightTable.semigroup := by
  intro valid
  have witness := valid (fun _ => (3 : Fin 5))
  change (1 : Fin 5) = 0 at witness
  omega

private def instantiateThree
    (first second third : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | letter + 3 => Word.singleton (letter + 3)

/-- Frozen law 00 is the complete first-occurrence owner's power law. -/
theorem derivesLongPowerExpansion (first : Word Nat) :
    Derives basis
      ((first ++ first) ++ first)
      (((first ++ first) ++ first) ++ first) := by
  have primitive :
      Derives basis (Word.mk 0 [0, 0]) (Word.mk 0 [0, 0, 0]) :=
    Derives.fromBasis (e := law00) (by simp [basis])
  have substituted :=
    Derives.subst primitive (instantiateThree first first first)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Frozen law 01 exchanges a triple prefix for a returning initial block. -/
theorem derivesTripleReturn (first second : Word Nat) :
    Derives basis
      (((first ++ first) ++ first) ++ second)
      ((first ++ second) ++ first) := by
  have primitive :
      Derives basis (Word.mk 0 [0, 0, 1]) (Word.mk 0 [1, 0]) :=
    Derives.fromBasis (e := law01) (by simp [basis])
  have substituted :=
    Derives.subst primitive (instantiateThree first second second)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Frozen law 02 duplicates the second block after a repeated initial block. -/
theorem derivesInitialPairFinalDuplication
    (first second : Word Nat) :
    Derives basis
      ((first ++ first) ++ second)
      (((first ++ first) ++ second) ++ second) := by
  have primitive :
      Derives basis (Word.mk 0 [0, 1]) (Word.mk 0 [0, 1, 1]) :=
    Derives.fromBasis (e := law02) (by simp [basis])
  have substituted :=
    Derives.subst primitive (instantiateThree first second second)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Frozen law 18 expands a repeated second block to three copies. -/
theorem derivesSecondCube (first second : Word Nat) :
    Derives basis
      ((first ++ second) ++ second)
      (((first ++ second) ++ second) ++ second) := by
  have primitive :
      Derives basis (Word.mk 0 [1, 1]) (Word.mk 0 [1, 1, 1]) :=
    Derives.fromBasis (e := law18) (by simp [basis])
  have substituted :=
    Derives.subst primitive (instantiateThree first second second)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Frozen law 21 duplicates any nonempty block behind two initial guards. -/
theorem derivesSuffixDuplication
    (guard₁ guard₂ block : Word Nat) :
    Derives basis
      ((guard₁ ++ guard₂) ++ block)
      (((guard₁ ++ guard₂) ++ block) ++ block) := by
  have primitive :
      Derives basis (Word.mk 0 [1, 2]) (Word.mk 0 [1, 2, 2]) :=
    Derives.fromBasis (e := law21) (by simp [basis])
  have substituted :=
    Derives.subst primitive (instantiateThree guard₁ guard₂ block)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- LRB regularity has the exact three-step guarded replay
`zwxy → zwxxy → zwxxxy → zwxyx`. -/
theorem derivesLrbRegularUnderInitialPair
    (guard₁ guard₂ first second : Word Nat) :
    Derives basis
      (((guard₁ ++ guard₂) ++ first) ++ second)
      ((((guard₁ ++ guard₂) ++ first) ++ second) ++ first) := by
  have firstStep :
      Derives basis
        (((guard₁ ++ guard₂) ++ first) ++ second)
        ((((guard₁ ++ guard₂) ++ first) ++ first) ++ second) := by
    simpa [Word.append_assoc] using
      Derives.appendRight
        (derivesSuffixDuplication guard₁ guard₂ first) second
  have secondStep :
      Derives basis
        ((((guard₁ ++ guard₂) ++ first) ++ first) ++ second)
        (((((guard₁ ++ guard₂) ++ first) ++ first) ++ first) ++ second) := by
    simpa [Word.append_assoc] using
      Derives.prepend guard₁ <|
        Derives.appendRight (derivesSecondCube guard₂ first) second
  have thirdStep :
      Derives basis
        (((((guard₁ ++ guard₂) ++ first) ++ first) ++ first) ++ second)
        ((((guard₁ ++ guard₂) ++ first) ++ second) ++ first) := by
    simpa [Word.append_assoc] using
      Derives.prepend (guard₁ ++ guard₂)
        (derivesTripleReturn first second)
  exact firstStep.trans (secondStep.trans thirdStep)

/-- The complete owner's gather has the exact protected two-step replay
`zwxxy → zwxxxy → zwxyx`. -/
theorem derivesOwnerGatherUnderInitialPair
    (guard₁ guard₂ first second : Word Nat) :
    Derives basis
      ((((guard₁ ++ guard₂) ++ first) ++ first) ++ second)
      ((((guard₁ ++ guard₂) ++ first) ++ second) ++ first) := by
  have firstStep :
      Derives basis
        ((((guard₁ ++ guard₂) ++ first) ++ first) ++ second)
        (((((guard₁ ++ guard₂) ++ first) ++ first) ++ first) ++ second) := by
    simpa [Word.append_assoc] using
      Derives.prepend guard₁ <|
        Derives.appendRight (derivesSecondCube guard₂ first) second
  have secondStep :
      Derives basis
        (((((guard₁ ++ guard₂) ++ first) ++ first) ++ first) ++ second)
        ((((guard₁ ++ guard₂) ++ first) ++ second) ++ first) := by
    simpa [Word.append_assoc] using
      Derives.prepend (guard₁ ++ guard₂)
        (derivesTripleReturn first second)
  exact firstStep.trans secondStep

/-- The complete owner's transfer has the exact protected two-step replay
`zwxxy → zwxxyy → zwxyy`. -/
theorem derivesOwnerTransferUnderInitialPair
    (guard₁ guard₂ first second : Word Nat) :
    Derives basis
      ((((guard₁ ++ guard₂) ++ first) ++ first) ++ second)
      ((((guard₁ ++ guard₂) ++ first) ++ second) ++ second) := by
  have firstStep :
      Derives basis
        ((((guard₁ ++ guard₂) ++ first) ++ first) ++ second)
        (((((guard₁ ++ guard₂) ++ first) ++ first) ++ second) ++ second) := by
    simpa [Word.append_assoc] using
      Derives.prepend (guard₁ ++ guard₂)
        (derivesInitialPairFinalDuplication first second)
  have secondStep :
      Derives basis
        (((((guard₁ ++ guard₂) ++ first) ++ first) ++ second) ++ second)
        ((((guard₁ ++ guard₂) ++ first) ++ second) ++ second) := by
    simpa [Word.append_assoc] using
      Derives.appendRight
        (derivesSuffixDuplication guard₁ guard₂ first).symm
        (second ++ second)
  exact firstStep.trans secondStep

private theorem bind_append
    (left right : Word Nat) (substitution : Nat → Word Nat) :
    (left ++ right).bind substitution =
      left.bind substitution ++ right.bind substitution := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem bind_bind
    (word : Word Nat) (first second : Nat → Word Nat) :
    (word.bind first).bind second =
      word.bind (fun letter => (first letter).bind second) := by
  apply Word.toList_injective
  simp [Word.toList_bind, List.flatMap_assoc]

private theorem bind_singleton (word : Word Nat) :
    word.bind Word.singleton = word := by
  apply Word.toList_injective
  simp

/-- Replay the COMPLETE two-law LRB calculus behind any two initial guards.
The prepend branch absorbs its context into the second guard. -/
theorem liftLeftRegularBandUnderInitialPair
    {left right : Word Nat}
    (derivation : Derives leftRegularBandThreeBasis left right)
    (guard₁ guard₂ : Word Nat) (substitution : Nat → Word Nat) :
    Derives basis
      ((guard₁ ++ guard₂) ++ left.bind substitution)
      ((guard₁ ++ guard₂) ++ right.bind substitution) := by
  induction derivation generalizing guard₁ guard₂ substitution with
  | fromBasis member =>
      simp only [leftRegularBandThreeBasis, List.mem_cons,
        List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · change Derives basis
          ((guard₁ ++ guard₂) ++ (Word.singleton 0).bind substitution)
          ((guard₁ ++ guard₂) ++ (Word.mk 0 [0]).bind substitution)
        simpa [Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          derivesSuffixDuplication guard₁ guard₂ (substitution 0)
      · change Derives basis
          ((guard₁ ++ guard₂) ++ (Word.mk 0 [1]).bind substitution)
          ((guard₁ ++ guard₂) ++ (Word.mk 0 [1, 0]).bind substitution)
        simpa [Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          derivesLrbRegularUnderInitialPair guard₁ guard₂
            (substitution 0) (substitution 1)
  | refl => exact Derives.refl _
  | symm _ hypothesis =>
      exact (hypothesis guard₁ guard₂ substitution).symm
  | trans _ _ first second =>
      exact (first guard₁ guard₂ substitution).trans
        (second guard₁ guard₂ substitution)
  | prepend front _ hypothesis =>
      simpa [bind_append, Word.append_assoc] using
        hypothesis guard₁ (guard₂ ++ front.bind substitution)
          substitution
  | appendRight _ suffix hypothesis =>
      simpa [bind_append, Word.append_assoc] using
        Derives.appendRight
          (hypothesis guard₁ guard₂ substitution)
          (suffix.bind substitution)
  | subst _ first hypothesis =>
      simpa [bind_bind] using
        hypothesis guard₁ guard₂
          (fun letter => (first letter).bind substitution)

/-- The independently complete five-law first-occurrence owner also replays
under arbitrary simultaneous substitutions and every guarded context. -/
theorem liftS5_523UnderInitialPair
    {left right : Word Nat}
    (derivation :
      Derives SemigroupBasis.CoRoots.S5_523.basis left right)
    (guard₁ guard₂ : Word Nat) (substitution : Nat → Word Nat) :
    Derives basis
      ((guard₁ ++ guard₂) ++ left.bind substitution)
      ((guard₁ ++ guard₂) ++ right.bind substitution) := by
  induction derivation generalizing guard₁ guard₂ substitution with
  | fromBasis member =>
      simp only [SemigroupBasis.CoRoots.S5_523.basis,
        List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl
      · change Derives basis
          ((guard₁ ++ guard₂) ++ (Word.mk 0 [0, 0]).bind substitution)
          ((guard₁ ++ guard₂) ++ (Word.mk 0 [0, 0, 0]).bind substitution)
        simpa [Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          Derives.prepend (guard₁ ++ guard₂)
            (derivesLongPowerExpansion (substitution 0))
      · change Derives basis
          ((guard₁ ++ guard₂) ++ (Word.mk 0 [0, 1]).bind substitution)
          ((guard₁ ++ guard₂) ++ (Word.mk 0 [1, 0]).bind substitution)
        simpa [Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          derivesOwnerGatherUnderInitialPair guard₁ guard₂
            (substitution 0) (substitution 1)
      · change Derives basis
          ((guard₁ ++ guard₂) ++ (Word.mk 0 [0, 1]).bind substitution)
          ((guard₁ ++ guard₂) ++ (Word.mk 0 [1, 1]).bind substitution)
        simpa [Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          derivesOwnerTransferUnderInitialPair guard₁ guard₂
            (substitution 0) (substitution 1)
      · change Derives basis
          ((guard₁ ++ guard₂) ++ (Word.mk 0 [0, 1]).bind substitution)
          ((guard₁ ++ guard₂) ++ (Word.mk 0 [0, 0, 1]).bind substitution)
        simpa [Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          Derives.prepend guard₁ <|
            Derives.appendRight
              (derivesSecondCube guard₂ (substitution 0))
              (substitution 1)
      · change Derives basis
          ((guard₁ ++ guard₂) ++ (Word.mk 0 [1, 2]).bind substitution)
          ((guard₁ ++ guard₂) ++ (Word.mk 0 [0, 1, 2]).bind substitution)
        simpa [Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          Derives.appendRight
            (derivesSuffixDuplication guard₁ guard₂ (substitution 0))
            (substitution 1 ++ substitution 2)
  | refl => exact Derives.refl _
  | symm _ hypothesis =>
      exact (hypothesis guard₁ guard₂ substitution).symm
  | trans _ _ first second =>
      exact (first guard₁ guard₂ substitution).trans
        (second guard₁ guard₂ substitution)
  | prepend front _ hypothesis =>
      simpa [bind_append, Word.append_assoc] using
        hypothesis guard₁ (guard₂ ++ front.bind substitution)
          substitution
  | appendRight _ suffix hypothesis =>
      simpa [bind_append, Word.append_assoc] using
        Derives.appendRight
          (hypothesis guard₁ guard₂ substitution)
          (suffix.bind substitution)
  | subst _ first hypothesis =>
      simpa [bind_bind] using
        hypothesis guard₁ guard₂
          (fun letter => (first letter).bind substitution)

/-- Equal COMPLETE first-occurrence sequences give an unguarded derivation
in the independently complete two-law left-regular-band theory. -/
theorem lrbDerives_of_sameFirstOccurrences
    (left right : Word Nat)
    (order :
      firstOccurrenceSequence left.toList =
        firstOccurrenceSequence right.toList) :
    Derives leftRegularBandThreeBasis left right := by
  have leftNormal := lrbDerivesNormal left
  have rightNormal := lrbDerivesNormal right
  cases normal : firstOccurrenceSequence left.toList with
  | nil =>
      rw [normal] at leftNormal
      exact False.elim leftNormal
  | cons head tail =>
      have rightSequence :
          firstOccurrenceSequence right.toList = head :: tail := by
        simpa [normal] using order.symm
      rw [normal] at leftNormal
      rw [rightSequence] at rightNormal
      exact leftNormal.trans rightNormal.symm

/-- STRONGER than target validity: every pair of nonempty words with equal
full first-occurrence order derives behind any two initial guards. -/
theorem derivesSameFirstOrderUnderInitialPair
    (left right guard₁ guard₂ : Word Nat)
    (order :
      firstOccurrenceSequence left.toList =
        firstOccurrenceSequence right.toList) :
    Derives basis
      ((guard₁ ++ guard₂) ++ left)
      ((guard₁ ++ guard₂) ++ right) := by
  simpa only [bind_singleton] using
    liftLeftRegularBandUnderInitialPair
      (lrbDerives_of_sameFirstOccurrences left right order)
      guard₁ guard₂ Word.singleton

/-- Every complete-owner identity derives behind two arbitrary initial guards. -/
theorem derivesInitialPair_of_ownerLeftValid
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy ownerLeft.semigroup)
    (guard₁ guard₂ : Word Nat) :
    Derives basis
      ((guard₁ ++ guard₂) ++ identity.lhs)
      ((guard₁ ++ guard₂) ++ identity.rhs) := by
  have owner :=
    SemigroupBasis.CoRoots.S5_523.representative_basis.2
      identity valid
  simpa only [bind_singleton] using
    liftS5_523UnderInitialPair owner guard₁ guard₂ Word.singleton

/-- Every ACTUAL target-pair identity has an unrestricted guarded replay. -/
theorem derivesInitialPair_of_targetPairValid
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy leftTable.semigroup)
    (rightValid : identity.SatisfiedBy rightTable.semigroup)
    (guard₁ guard₂ : Word Nat) :
    Derives basis
      ((guard₁ ++ guard₂) ++ identity.lhs)
      ((guard₁ ++ guard₂) ++ identity.rhs) :=
  derivesInitialPair_of_ownerLeftValid identity
    ((ownerPairTheory_iff_targetPairTheory identity).mp
      ⟨leftValid, rightValid⟩).1 guard₁ guard₂

/-- The independently kernel-green rank-018 detector fixes FULL first order. -/
theorem firstOccurrences_of_targetLeftValid
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy leftTable.semigroup) :
    firstOccurrenceSequence identity.lhs.toList =
      firstOccurrenceSequence identity.rhs.toList :=
  SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank018.Seed.firstOccurrences_of_leftValid
    identity valid

/-- Opposite-factor validity is independently valid direct-factor semantics
for the reversed words. -/
theorem targetRightValid_reversed
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy rightTable.semigroup) :
    identity.reversed.SatisfiedBy
      SemigroupBasis.CoRoots.S5_203.table.semigroup := by
  change
    identity.SatisfiedBy
      SemigroupBasis.CoRoots.S5_203.table.semigroup.opposite at valid
  exact
    (Identity.satisfiedBy_opposite_iff_reversed identity
      SemigroupBasis.CoRoots.S5_203.table.semigroup).mp valid

/-- The reversed independent direct signature preserves singleton words,
unique INITIALS, initial doubletons, and the conditional unique initial pair. -/
theorem initialSignature_of_targetRightValid
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy rightTable.semigroup) :
    SemigroupBasis.CoRoots.S5_203.DirectCompletenessArchitecture.SameSupportTerminalStateSignature
      identity.lhs.reverse identity.rhs.reverse := by
  exact SemigroupBasis.CoRoots.S5_203.valid_sameSupportTerminalStateSignature
    identity.reversed (targetRightValid_reversed identity valid)

/-- Unguarded initial cancellation, without both complete owner signatures. -/
def GlobalInitialDoubleGuardCancellation : Prop :=
  ∀ left right : Word Nat,
    (∀ guard₁ guard₂ : Word Nat,
      Derives basis
        ((guard₁ ++ guard₂) ++ left)
        ((guard₁ ++ guard₂) ++ right)) →
      Derives basis left right

/-- Global initial cancellation is formally FALSE: all protected square/cube
instances derive, while the actual opposite factor distinguishes them. -/
theorem not_globalInitialDoubleGuardCancellation :
    ¬ GlobalInitialDoubleGuardCancellation := by
  intro cancellation
  have guarded (guard₁ guard₂ : Word Nat) :
      Derives basis
        ((guard₁ ++ guard₂) ++ Word.mk 0 [0])
        ((guard₁ ++ guard₂) ++ Word.mk 0 [0, 0]) := by
    simpa [Word.singleton, Word.append, Word.append_assoc] using
      Derives.appendRight
        (derivesSuffixDuplication guard₁ guard₂ (Word.singleton 0))
        (Word.singleton 0)
  have derivation :=
    cancellation (Word.mk 0 [0]) (Word.mk 0 [0, 0]) guarded
  apply initialDoubletonSquareCube_not_rightValid
  intro valuation
  exact Derives.sound rightModels derivation valuation

/-- Exact missing unrestricted first-order plus reversed-initial-state proof. -/
def FirstOccurrenceInitialTerminalSignatureLift : Prop :=
  ∀ identity : Identity Nat,
    identity.SatisfiedBy ownerLeft.semigroup →
      identity.SatisfiedBy ownerRight.semigroup →
        Derives basis identity.lhs identity.rhs

/-- Initial cancellation is allowed ONLY for identities validated by BOTH
the complete first-occurrence owner and the opposite initial-state owner. -/
def PairValidInitialDoubleGuardCancellation : Prop :=
  ∀ identity : Identity Nat,
    identity.SatisfiedBy ownerLeft.semigroup →
      identity.SatisfiedBy ownerRight.semigroup →
        (∀ guard₁ guard₂ : Word Nat,
          Derives basis
            ((guard₁ ++ guard₂) ++ identity.lhs)
            ((guard₁ ++ guard₂) ++ identity.rhs)) →
        Derives basis identity.lhs identity.rhs

/-- The owner obligation is EXACTLY cancellation restricted to actual
first-occurrence-valid and reversed-initial-signature-valid identities. -/
theorem ownerLift_iff_pairValidInitialDoubleGuardCancellation :
    FirstOccurrenceInitialTerminalSignatureLift ↔
      PairValidInitialDoubleGuardCancellation := by
  constructor
  · intro owner identity leftValid rightValid _
    exact owner identity leftValid rightValid
  · intro cancellation identity leftValid rightValid
    exact cancellation identity leftValid rightValid
      (fun guard₁ guard₂ =>
        derivesInitialPair_of_ownerLeftValid identity leftValid
          guard₁ guard₂)

/-- An independent exact owner proof suffices; its premise remains visible. -/
def intersectionBasis_of_ownerLift
    (owner : FirstOccurrenceInitialTerminalSignatureLift) :
    IntersectionBasis leftTable.semigroup rightTable.semigroup basis where
  leftModels := leftModels
  rightModels := rightModels
  complete := by
    intro identity leftValid rightValid
    have factors :=
      (ownerPairTheory_iff_targetPairTheory identity).mp
        ⟨leftValid, rightValid⟩
    exact owner identity factors.1 factors.2

/-- Exact equivalence between target completeness and the isolated obligation. -/
theorem targetIntersection_iff_ownerLift :
    IntersectionBasis leftTable.semigroup rightTable.semigroup basis ↔
      FirstOccurrenceInitialTerminalSignatureLift := by
  constructor
  · intro intersection identity leftValid rightValid
    have factors :=
      (ownerPairTheory_iff_targetPairTheory identity).mpr
        ⟨leftValid, rightValid⟩
    exact intersection.complete identity factors.1 factors.2
  · exact intersectionBasis_of_ownerLift

/-- Transport remains strictly conditional on the exact missing owner proof. -/
noncomputable def normalizer_of_ownerLift
    (owner : FirstOccurrenceInitialTerminalSignatureLift) :
    IntersectionNormalizer leftTable.semigroup rightTable.semigroup basis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer
    (intersectionBasis_of_ownerLift owner)

/-- Rank 082's only representative class remains strictly conditional. -/
theorem s6_5636_representative_basis_of_ownerLift
    (owner : FirstOccurrenceInitialTerminalSignatureLift) :
    BasisFor S6_5636.table.semigroup basis :=
  S6_5636.representative_basis_of_normalizer
    (normalizer_of_ownerLift owner)

/-- Its opposite orientation has the identical visible missing premise. -/
theorem s6_5636_opposite_basis_of_ownerLift
    (owner : FirstOccurrenceInitialTerminalSignatureLift) :
    BasisFor S6_5636.table.semigroup.opposite (reversedBasis basis) :=
  S6_5636.opposite_basis_of_normalizer
    (normalizer_of_ownerLift owner)

end SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank082.InitialGuard
