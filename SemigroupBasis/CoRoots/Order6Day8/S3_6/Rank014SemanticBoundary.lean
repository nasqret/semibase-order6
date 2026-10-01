import SemigroupBasis.CoRoots.S5_636
import SemigroupBasis.FiniteCertificate
import SemigroupBasis.Generated.Order6OneLocalFordLast.DisplayedSigma
import SemigroupBasis.Generated.S3_6

namespace SemigroupBasis.CoRoots.Order6Day8.S3_6.Rank014SemanticBoundary

open SemigroupBasis
open SemigroupBasis.Examples

abbrev basis : List (Identity Nat) :=
  Generated.Order6OneLocalFordLast.DisplayedSigma.Sigma_fa3011392afb2dee.basis

abbrev lowerBasis : List (Identity Nat) :=
  SemigroupBasis.CoRoots.S5_636.basis

private def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

/-- The exact frozen eleven-law system is sound for the final-marker factor. -/
theorem markerModels :
    Models Generated.S3_6.table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    Generated.S3_6.table basis toFinThree (by decide)

/-- The same exact system is sound for the independently normalized factor. -/
theorem lowerModels :
    Models SemigroupBasis.CoRoots.S5_636.table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.CoRoots.S5_636.table basis toFinThree (by decide)

/-- First-occurrence equality implies equality of unrestricted variable support. -/
theorem support_of_firstOccurrence_eq
    {left right : Word Nat}
    (equalOrder :
      firstOccurrenceSequence left.toList =
        firstOccurrenceSequence right.toList)
    (letter : Nat) :
    letter ∈ left.toList ↔ letter ∈ right.toList := by
  constructor
  · intro member
    have first : letter ∈ firstOccurrenceSequence left.toList :=
      (mem_firstOccurrenceSequence_iff letter left.toList).mpr member
    rw [equalOrder] at first
    exact (mem_firstOccurrenceSequence_iff letter right.toList).mp first
  · intro member
    have first : letter ∈ firstOccurrenceSequence right.toList :=
      (mem_firstOccurrenceSequence_iff letter right.toList).mpr member
    rw [← equalOrder] at first
    exact (mem_firstOccurrenceSequence_iff letter left.toList).mp first

/-- Exact evaluation under an arbitrary valuation, not just finite separators. -/
theorem marker_eval_prefix
    (valuation : Nat → Fin 3) (letters : List Nat) (final : Nat) :
    finalMarkerThree.semigroup.eval valuation
        (wordOfPrefixFinal letters final) =
      if ∀ letter, letter ∈ letters → valuation letter = (2 : Fin 3)
      then valuation final else 0 := by
  classical
  induction letters with
  | nil =>
      simp [wordOfPrefixFinal]
  | cons head tail induction =>
      rw [wordOfPrefixFinal_cons, Semigroup.eval_append,
        Semigroup.eval_singleton, induction]
      change
        finalMarkerThreeMul (valuation head)
            (if ∀ letter, letter ∈ tail → valuation letter = (2 : Fin 3)
              then valuation final else 0) =
          if ∀ letter, letter ∈ head :: tail →
              valuation letter = (2 : Fin 3)
            then valuation final else 0
      by_cases headIdentity : valuation head = (2 : Fin 3)
      · simp [finalMarkerThreeMul, headIdentity]
      · simp [finalMarkerThreeMul, headIdentity]

/-- Whole-word support and the exact simple-final flag determine prefix support. -/
theorem prefix_support_of_support_and_simple
    (identity : Identity Nat)
    (support : ∀ letter,
      letter ∈ identity.lhs.toList ↔ letter ∈ identity.rhs.toList)
    (simple : ∀ letter,
      ((splitPrefixFinal identity.lhs).2 = letter ∧
        letter ∉ (splitPrefixFinal identity.lhs).1) ↔
        ((splitPrefixFinal identity.rhs).2 = letter ∧
          letter ∉ (splitPrefixFinal identity.rhs).1))
    (letter : Nat) :
    letter ∈ (splitPrefixFinal identity.lhs).1 ↔
      letter ∈ (splitPrefixFinal identity.rhs).1 := by
  let left := splitPrefixFinal identity.lhs
  let right := splitPrefixFinal identity.rhs
  have leftMembership (selected : Nat) :
      selected ∈ identity.lhs.toList ↔
        selected ∈ left.1 ∨ selected = left.2 := by
    rw [← wordOfPrefixFinal_split identity.lhs,
      toList_wordOfPrefixFinal]
    simp [left]
  have rightMembership (selected : Nat) :
      selected ∈ identity.rhs.toList ↔
        selected ∈ right.1 ∨ selected = right.2 := by
    rw [← wordOfPrefixFinal_split identity.rhs,
      toList_wordOfPrefixFinal]
    simp [right]
  change letter ∈ left.1 ↔ letter ∈ right.1
  constructor
  · intro member
    have whole :=
      (support letter).mp ((leftMembership letter).mpr (.inl member))
    rcases (rightMembership letter).mp whole with rightMember | rightFinal
    · exact rightMember
    · apply Decidable.byContradiction
      intro missing
      have rightSimple : right.2 = letter ∧ letter ∉ right.1 :=
        ⟨rightFinal.symm, missing⟩
      have leftSimple := (simple letter).mpr rightSimple
      exact leftSimple.2 member
  · intro member
    have whole :=
      (support letter).mpr ((rightMembership letter).mpr (.inl member))
    rcases (leftMembership letter).mp whole with leftMember | leftFinal
    · exact leftMember
    · apply Decidable.byContradiction
      intro missing
      have leftSimple : left.2 = letter ∧ letter ∉ left.1 :=
        ⟨leftFinal.symm, missing⟩
      have rightSimple := (simple letter).mp leftSimple
      exact rightSimple.2 member

/-- The exact final-marker identity theory requires no stronger final invariant. -/
theorem marker_valid_of_support_and_simple
    (identity : Identity Nat)
    (support : ∀ letter,
      letter ∈ identity.lhs.toList ↔ letter ∈ identity.rhs.toList)
    (simple : ∀ letter,
      ((splitPrefixFinal identity.lhs).2 = letter ∧
        letter ∉ (splitPrefixFinal identity.lhs).1) ↔
        ((splitPrefixFinal identity.rhs).2 = letter ∧
          letter ∉ (splitPrefixFinal identity.rhs).1)) :
    identity.SatisfiedBy Generated.S3_6.table.semigroup := by
  classical
  intro valuation
  change
    finalMarkerThree.semigroup.eval valuation identity.lhs =
      finalMarkerThree.semigroup.eval valuation identity.rhs
  let left := splitPrefixFinal identity.lhs
  let right := splitPrefixFinal identity.rhs
  have leftReconstruct :
      wordOfPrefixFinal left.1 left.2 = identity.lhs :=
    wordOfPrefixFinal_split identity.lhs
  have rightReconstruct :
      wordOfPrefixFinal right.1 right.2 = identity.rhs :=
    wordOfPrefixFinal_split identity.rhs
  rw [← leftReconstruct, ← rightReconstruct,
    marker_eval_prefix, marker_eval_prefix]
  have prefixSupport (letter : Nat) :
      letter ∈ left.1 ↔ letter ∈ right.1 :=
    prefix_support_of_support_and_simple identity support simple letter
  have sameCondition :
      (∀ letter, letter ∈ left.1 → valuation letter = (2 : Fin 3)) ↔
        (∀ letter, letter ∈ right.1 → valuation letter = (2 : Fin 3)) := by
    constructor
    · intro all letter member
      exact all letter ((prefixSupport letter).mpr member)
    · intro all letter member
      exact all letter ((prefixSupport letter).mp member)
  by_cases allRight :
      ∀ letter, letter ∈ right.1 → valuation letter = (2 : Fin 3)
  · have allLeft := sameCondition.mpr allRight
    simp only [if_pos allLeft, if_pos allRight]
    by_cases leftRepeated : left.2 ∈ left.1
    · have rightRepeated : right.2 ∈ right.1 := by
        apply Decidable.byContradiction
        intro notRepeated
        have leftSimple :=
          (simple right.2).mpr ⟨rfl, notRepeated⟩
        have rightInLeft : right.2 ∈ left.1 := by
          rw [← leftSimple.1]
          exact leftRepeated
        exact leftSimple.2 rightInLeft
      have leftIdentity :=
        allRight left.2 ((prefixSupport left.2).mp leftRepeated)
      have rightIdentity := allRight right.2 rightRepeated
      exact leftIdentity.trans rightIdentity.symm
    · have rightSimple := (simple left.2).mp ⟨rfl, leftRepeated⟩
      exact congrArg valuation rightSimple.1.symm
  · have notLeft :
        ¬ ∀ letter, letter ∈ left.1 →
          valuation letter = (2 : Fin 3) := by
      intro allLeft
      exact allRight (sameCondition.mp allLeft)
    simp [notLeft, allRight]

/-- Under the independently necessary first-occurrence order, marker validity
is equivalent to preservation of the globally simple final letter. -/
theorem marker_valid_iff_simple_of_firstOccurrence
    (identity : Identity Nat)
    (equalOrder :
      firstOccurrenceSequence identity.lhs.toList =
        firstOccurrenceSequence identity.rhs.toList) :
    identity.SatisfiedBy Generated.S3_6.table.semigroup ↔
      ∀ letter,
        ((splitPrefixFinal identity.lhs).2 = letter ∧
          letter ∉ (splitPrefixFinal identity.lhs).1) ↔
          ((splitPrefixFinal identity.rhs).2 = letter ∧
            letter ∉ (splitPrefixFinal identity.rhs).1) := by
  constructor
  · intro valid letter
    exact finalMarkerValid_splitSimpleFinal_iff identity valid letter
  · intro simple
    exact marker_valid_of_support_and_simple identity
      (support_of_firstOccurrence_eq equalOrder) simple

/-- The completed lower factor has precisely the published order/period key. -/
theorem lower_valid_iff_order_and_period
    (identity : Identity Nat) :
    identity.SatisfiedBy SemigroupBasis.CoRoots.S5_636.table.semigroup ↔
      firstOccurrenceSequence identity.lhs.toList =
          firstOccurrenceSequence identity.rhs.toList ∧
        ∀ letter,
          SemigroupBasis.CoRoots.S5_636.s5_636Exponent
              (identity.lhs.toList.count letter) =
            SemigroupBasis.CoRoots.S5_636.s5_636Exponent
              (identity.rhs.toList.count letter) := by
  constructor
  · intro valid
    exact ⟨SemigroupBasis.CoRoots.S5_636.valid_firstOccurrenceSequence_eq
        identity valid,
      SemigroupBasis.CoRoots.S5_636.valid_exponent_eq identity valid⟩
  · intro invariant
    exact (SemigroupBasis.CoRoots.S5_636.s5_636DerivesOfInvariantEq
      identity.lhs identity.rhs invariant.1 invariant.2).sound
      SemigroupBasis.CoRoots.S5_636.models

/-- The full, unrestricted joint key; the raw final letter is intentionally
absent in the repeated-final stratum. -/
structure JointDescriptor (identity : Identity Nat) : Prop where
  firstOccurrenceOrder :
    firstOccurrenceSequence identity.lhs.toList =
      firstOccurrenceSequence identity.rhs.toList
  periodTwoMultiplicity : ∀ letter,
    SemigroupBasis.CoRoots.S5_636.s5_636Exponent
        (identity.lhs.toList.count letter) =
      SemigroupBasis.CoRoots.S5_636.s5_636Exponent
        (identity.rhs.toList.count letter)
  simpleFinal : ∀ letter,
    ((splitPrefixFinal identity.lhs).2 = letter ∧
      letter ∉ (splitPrefixFinal identity.lhs).1) ↔
      ((splitPrefixFinal identity.rhs).2 = letter ∧
        letter ∉ (splitPrefixFinal identity.rhs).1)

/-- Exact, bidirectional unrestricted semantics for the first live owner pair. -/
theorem factor_valid_iff_joint_descriptor
    (identity : Identity Nat) :
    (identity.SatisfiedBy Generated.S3_6.table.semigroup ∧
      identity.SatisfiedBy SemigroupBasis.CoRoots.S5_636.table.semigroup) ↔
      JointDescriptor identity := by
  constructor
  · rintro ⟨markerValid, lowerValid⟩
    have lower := (lower_valid_iff_order_and_period identity).mp lowerValid
    exact ⟨lower.1, lower.2,
      (marker_valid_iff_simple_of_firstOccurrence identity lower.1).mp
        markerValid⟩
  · intro descriptor
    exact ⟨(marker_valid_iff_simple_of_firstOccurrence
        identity descriptor.firstOccurrenceOrder).mpr descriptor.simpleFinal,
      (lower_valid_iff_order_and_period identity).mpr
        ⟨descriptor.firstOccurrenceOrder,
          descriptor.periodTwoMultiplicity⟩⟩

private def instantiateThree
    (first second third : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | letter + 3 => Word.singleton (letter + 3)

/-- The exact displayed power law adds two copies of any nonempty block. -/
theorem derivesPower (block : Word Nat) :
    Derives basis
      (block ++ block)
      (((block ++ block) ++ block) ++ block) := by
  have primitive :
      Derives basis
        (Word.mk 0 [0]) (Word.mk 0 [0, 0, 0]) :=
    Derives.fromBasis
      (e := (⟨Word.mk 0 [0], Word.mk 0 [0, 0, 0]⟩ : Identity Nat))
      (by decide)
  have substituted :=
    Derives.subst primitive (instantiateThree block block block)
  simpa [instantiateThree, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- The lower gather axiom is sound only before a genuine nonempty guard. -/
theorem derivesGuardedGather
    (block middle guard : Word Nat) :
    Derives basis
      (((block ++ block) ++ middle) ++ guard)
      (((block ++ middle) ++ block) ++ guard) := by
  have primitive :
      Derives basis
        (Word.mk 0 [0, 1, 2]) (Word.mk 0 [1, 0, 2]) :=
    Derives.fromBasis
      (e :=
        (⟨Word.mk 0 [0, 1, 2], Word.mk 0 [1, 0, 2]⟩ : Identity Nat))
      (by decide)
  have substituted :=
    Derives.subst primitive (instantiateThree block middle guard)
  simpa [instantiateThree, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

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
  simp [Word.toList_bind]

/-- Replay EVERY complete lower-factor derivation under arbitrary nonempty
substitution and an unchanged arbitrary nonempty right guard. -/
theorem liftLowerWithSuffix
    {left right : Word Nat}
    (derivation : Derives lowerBasis left right)
    (suffix : Word Nat) (substitution : Nat → Word Nat) :
    Derives basis
      (left.bind substitution ++ suffix)
      (right.bind substitution ++ suffix) := by
  induction derivation generalizing suffix substitution with
  | fromBasis member =>
      simp only [lowerBasis, SemigroupBasis.CoRoots.S5_636.basis,
        SemigroupBasis.CoRoots.S5_636.s5_636Basis,
        List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · change
          Derives basis
            ((Word.mk 0 [0]).bind substitution ++ suffix)
            ((Word.mk 0 [0, 0, 0]).bind substitution ++ suffix)
        simpa [Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
            Derives.appendRight (derivesPower (substitution 0)) suffix
      · change
          Derives basis
            ((Word.mk 0 [0, 1]).bind substitution ++ suffix)
            ((Word.mk 0 [1, 0]).bind substitution ++ suffix)
        simpa [Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
            derivesGuardedGather
              (substitution 0) (substitution 1) suffix
  | refl =>
      exact Derives.refl _
  | symm _ induction =>
      exact (induction suffix substitution).symm
  | trans _ _ first second =>
      exact (first suffix substitution).trans
        (second suffix substitution)
  | prepend stem _ induction =>
      simpa [bind_append, Word.append_assoc] using
        Derives.prepend (stem.bind substitution)
          (induction suffix substitution)
  | appendRight _ final induction =>
      simpa [bind_append, Word.append_assoc] using
        induction (final.bind substitution ++ suffix) substitution
  | subst _ next induction =>
      simpa [bind_bind] using
        induction suffix
          (fun letter => (next letter).bind substitution)

/-- Unrestricted lower validity is enough once both sides have the same
nonempty protected suffix. -/
theorem derivesSameSuffixOfLowerValid
    (left right suffix : Word Nat)
    (valid :
      (⟨left, right⟩ : Identity Nat).SatisfiedBy
        SemigroupBasis.CoRoots.S5_636.table.semigroup) :
    Derives basis (left ++ suffix) (right ++ suffix) := by
  have lower := SemigroupBasis.CoRoots.S5_636.representative_basis.2
    (⟨left, right⟩ : Identity Nat) valid
  simpa [bind_singleton] using
    liftLowerWithSuffix lower suffix Word.singleton

/-- Positive even/odd-at-least-three states cannot disguise a simple letter. -/
theorem count_ge_two_of_period_eq
    {leftCount rightCount : Nat}
    (equalState :
      SemigroupBasis.CoRoots.S5_636.s5_636Exponent leftCount =
        SemigroupBasis.CoRoots.S5_636.s5_636Exponent rightCount)
    (rightRepeated : 2 ≤ rightCount) :
    2 ≤ leftCount := by
  unfold SemigroupBasis.CoRoots.S5_636.s5_636Exponent
    periodTwoFromTwoExponent at equalState
  split at equalState <;> split at equalState <;> omega

/-- The only missing unrestricted repeated-final obligation.  It is stated
for the exact eleven-law basis and arbitrary alphabet, never a finite bound. -/
def RepeatedFinalPairInsertion : Prop :=
  ∀ (word : Word Nat) (selected : Nat),
    (splitPrefixFinal word).2 ∈ (splitPrefixFinal word).1 →
    2 ≤ word.toList.count selected →
      Derives basis word
        ((word ++ Word.singleton selected) ++ Word.singleton selected)

/-- A single genuine repeated-final insertion theorem closes the entire
repeated-final stratum via the already-unrestricted guarded lower replay. -/
theorem derivesRepeatedFinalOfInsertion
    (insertion : RepeatedFinalPairInsertion)
    (identity : Identity Nat)
    (descriptor : JointDescriptor identity)
    (leftRepeated :
      (splitPrefixFinal identity.lhs).2 ∈
        (splitPrefixFinal identity.lhs).1) :
    Derives basis identity.lhs identity.rhs := by
  let left := splitPrefixFinal identity.lhs
  let right := splitPrefixFinal identity.rhs
  have rightRepeated : right.2 ∈ right.1 := by
    apply Decidable.byContradiction
    intro rightSimple
    have leftSimple :=
      (descriptor.simpleFinal right.2).mpr ⟨rfl, rightSimple⟩
    exact leftSimple.2 (by simpa [leftSimple.1] using leftRepeated)
  have rightReconstruct :
      wordOfPrefixFinal right.1 right.2 = identity.rhs :=
    wordOfPrefixFinal_split identity.rhs
  have rightCount : 2 ≤ identity.rhs.toList.count right.2 := by
    rw [← rightReconstruct, toList_wordOfPrefixFinal,
      List.count_append]
    have positive := List.count_pos_iff.mpr rightRepeated
    simp
    omega
  have leftCount : 2 ≤ identity.lhs.toList.count right.2 :=
    count_ge_two_of_period_eq
      (descriptor.periodTwoMultiplicity right.2) rightCount
  let guard := Word.singleton right.2 ++ Word.singleton right.2
  have lowerValid :=
    (lower_valid_iff_order_and_period identity).mpr
      ⟨descriptor.firstOccurrenceOrder,
        descriptor.periodTwoMultiplicity⟩
  have lowerDerivation :=
    SemigroupBasis.CoRoots.S5_636.representative_basis.2 identity lowerValid
  have lifted :
      Derives basis (identity.lhs ++ guard) (identity.rhs ++ guard) := by
    simpa [bind_singleton] using
      liftLowerWithSuffix lowerDerivation guard Word.singleton
  have leftInsertion :
      Derives basis identity.lhs (identity.lhs ++ guard) := by
    simpa [guard, Word.append_assoc] using
      insertion identity.lhs right.2 leftRepeated leftCount
  have rightInsertion :
      Derives basis identity.rhs (identity.rhs ++ guard) := by
    simpa [guard, Word.append_assoc] using
      insertion identity.rhs right.2 rightRepeated rightCount
  exact leftInsertion.trans (lifted.trans rightInsertion.symm)

end SemigroupBasis.CoRoots.Order6Day8.S3_6.Rank014SemanticBoundary
