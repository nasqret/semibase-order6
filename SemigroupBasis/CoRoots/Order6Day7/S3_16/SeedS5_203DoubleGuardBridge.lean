import SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank081
import SemigroupBasis.CoRoots.Order6Day7.S3_16.SeedS5_353Opposite
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCTransportNormalizer
import SemigroupBasis.CoRoots.S5_203Family
import SemigroupBasis.CoRoots.S5_523

/-!
# The exact first-occurrence/two-terminal bridge for rank 081

Four finite product embeddings identify the actual `S3_16 × S5_203` pair
with `S5_523 × S5_203` on every alphabet.  The independently complete
five-law first-occurrence owner can be replayed behind any two nonempty
terminal blocks.  In particular, its gather axiom requires four displayed
rank-081 steps, and its transfer axiom requires two displayed steps.

The structural lift handles arbitrary contexts and simultaneous
substitutions.  Any remaining unrestricted conclusion is exposed as the
precise terminal-signature-aware double-guard cancellation obligation; no
unguarded cancellation or completeness premise is silently manufactured.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank081.DoubleGuard

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

/-- Exact unrestricted factor-theory equality, not a bounded profile. -/
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

/-- Rank 044's returning middle swap destroys first-occurrence order. -/
theorem legacyReturningSwap_not_leftValid :
    ¬ (Identity.mk (Word.mk 0 [1, 2, 0])
        (Word.mk 0 [2, 1, 0])).SatisfiedBy leftTable.semigroup := by
  intro valid
  have witness := valid
    (fun letter =>
      if letter = 0 then (1 : Fin 3) else
        if letter = 1 then (0 : Fin 3) else (2 : Fin 3))
  change (0 : Fin 3) = 2 at witness
  omega

/-- The complete terminal owner's alternating switch is invalid in `S3_16`. -/
theorem lowerAlternatingSwitch_not_leftValid :
    ¬ SemigroupBasis.CoRoots.S5_203.alternatingSwitchLaw.SatisfiedBy
      leftTable.semigroup := by
  intro valid
  have witness := valid
    (fun letter => if letter = 0 then (0 : Fin 3) else (2 : Fin 3))
  change (0 : Fin 3) = 2 at witness
  omega

/-- The complete first-occurrence owner's gather is false without guards. -/
theorem ownerGather_not_rightValid :
    ¬ SemigroupBasis.CoRoots.S5_523.gatherLaw.SatisfiedBy
      rightTable.semigroup := by
  intro valid
  have witness := valid
    (fun letter => if letter = 0 then (4 : Fin 5) else (1 : Fin 5))
  change (1 : Fin 5) = 0 at witness
  omega

/-- The complete owner's transfer also changes the terminal state. -/
theorem ownerTransfer_not_rightValid :
    ¬ SemigroupBasis.CoRoots.S5_523.transferLaw.SatisfiedBy
      rightTable.semigroup := by
  intro valid
  have witness := valid
    (fun letter => if letter = 0 then (4 : Fin 5) else (1 : Fin 5))
  change (1 : Fin 5) = 0 at witness
  omega

/-- A single final block does not protect the owner's gathering law. -/
theorem oneGuardedOwnerGather_not_rightValid :
    ¬ (Identity.mk (Word.mk 0 [0, 1, 2])
        (Word.mk 0 [1, 0, 2])).SatisfiedBy rightTable.semigroup := by
  intro valid
  have witness := valid
    (fun letter =>
      if letter = 0 then (4 : Fin 5) else
        if letter = 1 then (2 : Fin 5) else (3 : Fin 5))
  change (1 : Fin 5) = 0 at witness
  omega

/-- An unguarded square/cube cancellation destroys the terminal doubleton. -/
theorem terminalDoubletonSquareCube_not_rightValid :
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

/-- Frozen law 00 is exactly the complete owner's power law. -/
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

/-- Frozen law 01 contracts three initial copies before a nonempty suffix. -/
theorem derivesTriplePrefixContraction
    (first second : Word Nat) :
    Derives basis
      (((first ++ first) ++ first) ++ second)
      ((first ++ first) ++ second) := by
  have primitive :
      Derives basis (Word.mk 0 [0, 0, 1]) (Word.mk 0 [0, 1]) :=
    Derives.fromBasis (e := law01) (by simp [basis])
  have substituted :=
    Derives.subst primitive (instantiateThree first second second)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Frozen law 03 contracts the first block before a repeated second block. -/
theorem derivesPairedPrefixContraction
    (first second : Word Nat) :
    Derives basis
      (((first ++ first) ++ second) ++ second)
      ((first ++ second) ++ second) := by
  have primitive :
      Derives basis (Word.mk 0 [0, 1, 1]) (Word.mk 0 [1, 1]) :=
    Derives.fromBasis (e := law03) (by simp [basis])
  have substituted :=
    Derives.subst primitive (instantiateThree first second second)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Frozen law 04 contracts an initial duplicate with two later blocks. -/
theorem derivesHeadContraction
    (first second third : Word Nat) :
    Derives basis
      (((first ++ first) ++ second) ++ third)
      ((first ++ second) ++ third) := by
  have primitive :
      Derives basis (Word.mk 0 [0, 1, 2]) (Word.mk 0 [1, 2]) :=
    Derives.fromBasis (e := law04) (by simp [basis])
  have substituted :=
    Derives.subst primitive (instantiateThree first second third)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Frozen law 08 exchanges a return for three copies of the second block. -/
theorem derivesTerminalCube
    (first second : Word Nat) :
    Derives basis
      ((first ++ second) ++ first)
      (((first ++ second) ++ second) ++ second) := by
  have primitive :
      Derives basis (Word.mk 0 [1, 0]) (Word.mk 0 [1, 1, 1]) :=
    Derives.fromBasis (e := law08) (by simp [basis])
  have substituted :=
    Derives.subst primitive (instantiateThree first second second)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- The owner's `xxy = xyx` is false without guards.  Behind two arbitrary
nonempty terminal blocks it has the exact four-step displayed replay
`xxyzw → xyzw → xyyzw → xyyyzw → xyxzw`. -/
theorem derivesOwnerGatherUnderDoubleGuard
    (first second guard₁ guard₂ : Word Nat) :
    Derives basis
      ((((first ++ first) ++ second) ++ guard₁) ++ guard₂)
      ((((first ++ second) ++ first) ++ guard₁) ++ guard₂) := by
  have firstStep :
      Derives basis
        ((((first ++ first) ++ second) ++ guard₁) ++ guard₂)
        (((first ++ second) ++ guard₁) ++ guard₂) := by
    simpa [Word.append_assoc] using
      Derives.appendRight
        (derivesHeadContraction first second guard₁) guard₂
  have secondStep :
      Derives basis
        (((first ++ second) ++ guard₁) ++ guard₂)
        ((((first ++ second) ++ second) ++ guard₁) ++ guard₂) := by
    simpa [Word.append_assoc] using
      Derives.prepend first
        (derivesHeadContraction second guard₁ guard₂).symm
  have thirdStep :
      Derives basis
        ((((first ++ second) ++ second) ++ guard₁) ++ guard₂)
        (((((first ++ second) ++ second) ++ second) ++ guard₁) ++ guard₂) := by
    simpa [Word.append_assoc] using
      Derives.prepend first <|
        Derives.appendRight
          (derivesTriplePrefixContraction second guard₁).symm guard₂
  have fourthStep :
      Derives basis
        (((((first ++ second) ++ second) ++ second) ++ guard₁) ++ guard₂)
        ((((first ++ second) ++ first) ++ guard₁) ++ guard₂) := by
    simpa [Word.append_assoc] using
      Derives.appendRight
        (derivesTerminalCube first second).symm (guard₁ ++ guard₂)
  exact firstStep.trans (secondStep.trans (thirdStep.trans fourthStep))

/-- The owner's `xxy = xyy` also needs both terminal guards:
`xxyzw → xxyyzw → xyyzw`. -/
theorem derivesOwnerTransferUnderDoubleGuard
    (first second guard₁ guard₂ : Word Nat) :
    Derives basis
      ((((first ++ first) ++ second) ++ guard₁) ++ guard₂)
      ((((first ++ second) ++ second) ++ guard₁) ++ guard₂) := by
  have firstStep :
      Derives basis
        ((((first ++ first) ++ second) ++ guard₁) ++ guard₂)
        (((((first ++ first) ++ second) ++ second) ++ guard₁) ++ guard₂) := by
    simpa [Word.append_assoc] using
      Derives.prepend (first ++ first)
        (derivesHeadContraction second guard₁ guard₂).symm
  have secondStep :
      Derives basis
        (((((first ++ first) ++ second) ++ second) ++ guard₁) ++ guard₂)
        ((((first ++ second) ++ second) ++ guard₁) ++ guard₂) := by
    simpa [Word.append_assoc] using
      Derives.appendRight
        (derivesPairedPrefixContraction first second)
        (guard₁ ++ guard₂)
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

/-- Replay the independently COMPLETE first-occurrence owner calculus behind
any two nonempty terminal blocks.  The append-right induction case absorbs
its nonempty context as the first guard instead of assuming cancellation. -/
theorem liftS5_523UnderDoubleGuard
    {left right : Word Nat}
    (derivation :
      Derives SemigroupBasis.CoRoots.S5_523.basis left right)
    (guard₁ guard₂ : Word Nat) (substitution : Nat → Word Nat) :
    Derives basis
      ((left.bind substitution ++ guard₁) ++ guard₂)
      ((right.bind substitution ++ guard₁) ++ guard₂) := by
  induction derivation generalizing guard₁ guard₂ substitution with
  | fromBasis member =>
      simp only [SemigroupBasis.CoRoots.S5_523.basis,
        List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl
      · change Derives basis
          (((Word.mk 0 [0, 0]).bind substitution ++ guard₁) ++ guard₂)
          (((Word.mk 0 [0, 0, 0]).bind substitution ++ guard₁) ++ guard₂)
        simpa [Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          Derives.appendRight
            (derivesLongPowerExpansion (substitution 0))
            (guard₁ ++ guard₂)
      · change Derives basis
          (((Word.mk 0 [0, 1]).bind substitution ++ guard₁) ++ guard₂)
          (((Word.mk 0 [1, 0]).bind substitution ++ guard₁) ++ guard₂)
        simpa [Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          derivesOwnerGatherUnderDoubleGuard
            (substitution 0) (substitution 1) guard₁ guard₂
      · change Derives basis
          (((Word.mk 0 [0, 1]).bind substitution ++ guard₁) ++ guard₂)
          (((Word.mk 0 [1, 1]).bind substitution ++ guard₁) ++ guard₂)
        simpa [Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          derivesOwnerTransferUnderDoubleGuard
            (substitution 0) (substitution 1) guard₁ guard₂
      · change Derives basis
          (((Word.mk 0 [0, 1]).bind substitution ++ guard₁) ++ guard₂)
          (((Word.mk 0 [0, 0, 1]).bind substitution ++ guard₁) ++ guard₂)
        simpa [Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          Derives.appendRight
            (derivesTriplePrefixContraction
              (substitution 0) (substitution 1)).symm
            (guard₁ ++ guard₂)
      · change Derives basis
          (((Word.mk 0 [1, 2]).bind substitution ++ guard₁) ++ guard₂)
          (((Word.mk 0 [0, 1, 2]).bind substitution ++ guard₁) ++ guard₂)
        simpa [Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          Derives.appendRight
            (derivesHeadContraction
              (substitution 0) (substitution 1)
              (substitution 2)).symm
            (guard₁ ++ guard₂)
  | refl => exact Derives.refl _
  | symm _ hypothesis =>
      exact (hypothesis guard₁ guard₂ substitution).symm
  | trans _ _ first second =>
      exact (first guard₁ guard₂ substitution).trans
        (second guard₁ guard₂ substitution)
  | prepend front _ hypothesis =>
      simpa [bind_append, Word.append_assoc] using
        Derives.prepend (front.bind substitution)
          (hypothesis guard₁ guard₂ substitution)
  | appendRight _ suffix hypothesis =>
      simpa [bind_append, Word.append_assoc] using
        hypothesis (suffix.bind substitution) (guard₁ ++ guard₂)
          substitution
  | subst _ first hypothesis =>
      simpa [bind_bind] using
        hypothesis guard₁ guard₂
          (fun letter => (first letter).bind substitution)

/-- Every identity valid in the actual complete first-occurrence owner has
a rank-081 derivation after ANY two nonempty final contexts. -/
theorem derivesDoubleGuard_of_ownerLeftValid
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy ownerLeft.semigroup)
    (guard₁ guard₂ : Word Nat) :
    Derives basis
      ((identity.lhs ++ guard₁) ++ guard₂)
      ((identity.rhs ++ guard₁) ++ guard₂) := by
  have owner :=
    SemigroupBasis.CoRoots.S5_523.representative_basis.2
      identity valid
  simpa only [bind_singleton] using
    liftS5_523UnderDoubleGuard owner guard₁ guard₂ Word.singleton

/-- The double-guard theorem holds for every unrestricted ACTUAL target-pair
identity; neither catalogue truncation nor a factor-only assumption is used. -/
theorem derivesDoubleGuard_of_targetPairValid
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy leftTable.semigroup)
    (rightValid : identity.SatisfiedBy rightTable.semigroup)
    (guard₁ guard₂ : Word Nat) :
    Derives basis
      ((identity.lhs ++ guard₁) ++ guard₂)
      ((identity.rhs ++ guard₁) ++ guard₂) :=
  derivesDoubleGuard_of_ownerLeftValid identity
    ((ownerPairTheory_iff_targetPairTheory identity).mp
      ⟨leftValid, rightValid⟩).1 guard₁ guard₂

/-- Two additional initial copies force a nonempty owner word into the
length-at-least-three first-occurrence stratum. -/
def paddedInitial (word : Word Nat) : Word Nat :=
  (Word.singleton word.head ++ Word.singleton word.head) ++ word

/-- Adding copies of the already initial letter never changes first order. -/
theorem firstOccurrences_paddedInitial (word : Word Nat) :
    firstOccurrenceSequence (paddedInitial word).toList =
      firstOccurrenceSequence word.toList := by
  cases word with
  | mk head tail =>
      simp [paddedInitial, Word.singleton, Word.toList,
        firstOccurrenceSequence, List.filter_filter]

/-- Equal first-occurrence orders give identical COMPLETE owner signatures
after the common initial-padding construction. -/
theorem paddedInitial_sameOwnerSignature
    (left right : Word Nat)
    (order :
      firstOccurrenceSequence left.toList =
        firstOccurrenceSequence right.toList) :
    SemigroupBasis.CoRoots.S5_523.SameLongFirstOccurrenceSignature
      (paddedInitial left) (paddedInitial right) := by
  have paddedOrder :
      firstOccurrenceSequence (paddedInitial left).toList =
        firstOccurrenceSequence (paddedInitial right).toList := by
    rw [firstOccurrences_paddedInitial,
      firstOccurrences_paddedInitial, order]
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail =>
          change
            firstOccurrenceSequence
                (leftHead :: leftHead :: leftHead :: leftTail) =
              firstOccurrenceSequence
                (rightHead :: rightHead :: rightHead :: rightTail)
            at paddedOrder
          change
            SemigroupBasis.CoRoots.S5_523.longFirstOccurrenceNormalList
              (leftHead :: leftHead :: leftHead :: leftTail) =
            SemigroupBasis.CoRoots.S5_523.longFirstOccurrenceNormalList
              (rightHead :: rightHead :: rightHead :: rightTail)
          simp only [SemigroupBasis.CoRoots.S5_523.longFirstOccurrenceNormalList]
          rw [paddedOrder]

/-- Two final guards permit insertion of two initial copies regardless of
whether the original initial block has a nonempty proper tail. -/
theorem derivesPaddedInitialUnderDoubleGuard
    (word guard₁ guard₂ : Word Nat) :
    Derives basis
      ((word ++ guard₁) ++ guard₂)
      ((paddedInitial word ++ guard₁) ++ guard₂) := by
  cases word with
  | mk head tail =>
      cases tail with
      | nil =>
          have first :=
            (derivesHeadContraction
              (Word.singleton head) guard₁ guard₂).symm
          have second :=
            Derives.appendRight
              (derivesTriplePrefixContraction
                (Word.singleton head) guard₁).symm guard₂
          simpa [paddedInitial, Word.singleton, Word.append,
            Word.append_assoc] using first.trans second
      | cons next rest =>
          let remaining : Word Nat := Word.mk next rest
          have first :
              Derives basis
                (((Word.singleton head ++ remaining) ++ guard₁) ++ guard₂)
                ((((Word.singleton head ++ Word.singleton head) ++ remaining) ++
                  guard₁) ++ guard₂) := by
            simpa [Word.append_assoc] using
              (derivesHeadContraction (Word.singleton head)
                remaining (guard₁ ++ guard₂)).symm
          have second :
              Derives basis
                ((((Word.singleton head ++ Word.singleton head) ++ remaining) ++
                  guard₁) ++ guard₂)
                (((((Word.singleton head ++ Word.singleton head) ++
                  Word.singleton head) ++ remaining) ++ guard₁) ++ guard₂) := by
            simpa [Word.append_assoc] using
              (derivesTriplePrefixContraction
                (Word.singleton head)
                (remaining ++ (guard₁ ++ guard₂))).symm
          simpa [paddedInitial, remaining, Word.singleton,
            Word.append, Word.append_assoc] using first.trans second

/-- STRONG fixed-terminal theorem: any two nonempty initial words with the
same unrestricted first-occurrence sequence derive behind the same two
terminal blocks, without any finite-length or equal-length hypothesis. -/
theorem derivesSameFirstOrderUnderDoubleGuard
    (left right guard₁ guard₂ : Word Nat)
    (order :
      firstOccurrenceSequence left.toList =
        firstOccurrenceSequence right.toList) :
    Derives basis
      ((left ++ guard₁) ++ guard₂)
      ((right ++ guard₁) ++ guard₂) := by
  have owner :=
    SemigroupBasis.CoRoots.S5_523.longFirstOccurrenceDerivationalCompleteness
      (paddedInitial left) (paddedInitial right)
      (paddedInitial_sameOwnerSignature left right order)
  have middle :=
    liftS5_523UnderDoubleGuard owner guard₁ guard₂ Word.singleton
  rw [bind_singleton, bind_singleton] at middle
  exact (derivesPaddedInitialUnderDoubleGuard left guard₁ guard₂).trans <|
    middle.trans
      (derivesPaddedInitialUnderDoubleGuard right guard₁ guard₂).symm

/-- The already kernel-green rank-018 detector controls the FULL initial
occurrence order, not merely the common initial letter. -/
theorem firstOccurrences_of_targetLeftValid
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy leftTable.semigroup) :
    firstOccurrenceSequence identity.lhs.toList =
      firstOccurrenceSequence identity.rhs.toList :=
  SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank018.Seed.firstOccurrences_of_leftValid
    identity valid

/-- The exact right factor fixes singleton words, unique finals, terminal
doubletons, and the conditional globally unique terminal pair. -/
theorem terminalSignature_of_targetRightValid
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy rightTable.semigroup) :
    SemigroupBasis.CoRoots.S5_203.DirectCompletenessArchitecture.SameSupportTerminalStateSignature
      identity.lhs identity.rhs := by
  apply SemigroupBasis.CoRoots.S5_203.valid_sameSupportTerminalStateSignature
    identity
  simpa [rightTable, SemigroupBasis.CoRoots.S5_203.table] using valid

/-- Cancelling two guards without the independent terminal-signature
hypothesis would incorrectly identify a terminal doubleton with a cube. -/
def GlobalDoubleGuardCancellation : Prop :=
  ∀ left right : Word Nat,
    (∀ guard₁ guard₂ : Word Nat,
      Derives basis ((left ++ guard₁) ++ guard₂)
        ((right ++ guard₁) ++ guard₂)) →
      Derives basis left right

/-- Global double-guard cancellation is formally FALSE for the actual frozen
presentation, even though every doubly guarded instance is derivable. -/
theorem not_globalDoubleGuardCancellation :
    ¬ GlobalDoubleGuardCancellation := by
  intro cancellation
  have guarded (guard₁ guard₂ : Word Nat) :
      Derives basis
        (((Word.mk 0 [0]) ++ guard₁) ++ guard₂)
        (((Word.mk 0 [0, 0]) ++ guard₁) ++ guard₂) := by
    simpa [Word.singleton, Word.append, Word.append_assoc] using
      Derives.appendRight
        (derivesTriplePrefixContraction
          (Word.singleton 0) guard₁).symm guard₂
  have derivation :=
    cancellation (Word.mk 0 [0]) (Word.mk 0 [0, 0]) guarded
  apply terminalDoubletonSquareCube_not_rightValid
  intro valuation
  exact Derives.sound rightModels derivation valuation

/-- Exact unrestricted missing proof, with both independent owner factors. -/
def FirstOccurrenceTerminalSignatureLift : Prop :=
  ∀ identity : Identity Nat,
    identity.SatisfiedBy ownerLeft.semigroup →
      identity.SatisfiedBy ownerRight.semigroup →
        Derives basis identity.lhs identity.rhs

/-- Cancellation is demanded ONLY on actual first-occurrence-valid and
terminal-signature-valid identities; global cancellation would be false. -/
def PairValidDoubleGuardCancellation : Prop :=
  ∀ identity : Identity Nat,
    identity.SatisfiedBy ownerLeft.semigroup →
      identity.SatisfiedBy ownerRight.semigroup →
        (∀ guard₁ guard₂ : Word Nat,
          Derives basis
            ((identity.lhs ++ guard₁) ++ guard₂)
            ((identity.rhs ++ guard₁) ++ guard₂)) →
        Derives basis identity.lhs identity.rhs

/-- The exact owner obligation is equivalent to cancellation only under its
complete first-occurrence AND terminal-state hypotheses. -/
theorem ownerLift_iff_pairValidDoubleGuardCancellation :
    FirstOccurrenceTerminalSignatureLift ↔
      PairValidDoubleGuardCancellation := by
  constructor
  · intro owner identity leftValid rightValid _
    exact owner identity leftValid rightValid
  · intro cancellation identity leftValid rightValid
    exact cancellation identity leftValid rightValid
      (fun guard₁ guard₂ =>
        derivesDoubleGuard_of_ownerLeftValid identity leftValid
          guard₁ guard₂)

/-- An actual owner proof suffices for the exact frozen intersection; its
premise remains visible and cannot be filled by finite reflection. -/
def intersectionBasis_of_ownerLift
    (owner : FirstOccurrenceTerminalSignatureLift) :
    IntersectionBasis leftTable.semigroup rightTable.semigroup basis where
  leftModels := leftModels
  rightModels := rightModels
  complete := by
    intro identity leftValid rightValid
    have factors :=
      (ownerPairTheory_iff_targetPairTheory identity).mp
        ⟨leftValid, rightValid⟩
    exact owner identity factors.1 factors.2

/-- Exact equivalence between the target intersection and the isolated
first-occurrence/terminal-signature owner proof. -/
theorem targetIntersection_iff_ownerLift :
    IntersectionBasis leftTable.semigroup rightTable.semigroup basis ↔
      FirstOccurrenceTerminalSignatureLift := by
  constructor
  · intro intersection identity leftValid rightValid
    have factors :=
      (ownerPairTheory_iff_targetPairTheory identity).mpr
        ⟨leftValid, rightValid⟩
    exact intersection.complete identity factors.1 factors.2
  · exact intersectionBasis_of_ownerLift

/-- Transport remains conditional on the exact owner proof. -/
noncomputable def normalizer_of_ownerLift
    (owner : FirstOccurrenceTerminalSignatureLift) :
    IntersectionNormalizer leftTable.semigroup rightTable.semigroup basis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer
    (intersectionBasis_of_ownerLift owner)

/-- The single representative class remains conditional on the owner lift. -/
theorem s6_5581_representative_basis_of_ownerLift
    (owner : FirstOccurrenceTerminalSignatureLift) :
    BasisFor S6_5581.table.semigroup basis :=
  S6_5581.representative_basis_of_normalizer
    (normalizer_of_ownerLift owner)

/-- Its opposite orientation retains the identical exact missing premise. -/
theorem s6_5581_opposite_basis_of_ownerLift
    (owner : FirstOccurrenceTerminalSignatureLift) :
    BasisFor S6_5581.table.semigroup.opposite (reversedBasis basis) :=
  S6_5581.opposite_basis_of_normalizer
    (normalizer_of_ownerLift owner)

end SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank081.DoubleGuard
