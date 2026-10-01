import SemigroupBasis.CoRoots.Order6Day8.S3_6.Rank014RepeatedInsertion

/-!
# Full unrestricted intersection completeness for the exact Rank014 pair

The globally simple final is stripped using the actual `S5_636` right
identity, and its complete lower derivation is replayed under the common
terminal guard.  The repeated-final stratum is closed by the separately
proved unrestricted displayed-law pair insertion.
-/

namespace SemigroupBasis.CoRoots.Order6Day8.S3_6.Rank014IntersectionCompleteness

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.Order6Day8.S3_6.Rank014SemanticBoundary
open SemigroupBasis.CoRoots.Order6Day8.S3_6.Rank014RepeatedInsertion

private theorem foldl_eval_congr {S : Type}
    (semigroup : Semigroup S)
    (leftValuation rightValuation : Nat → S) :
    ∀ (letters : List Nat) (initial : S),
      (∀ letter, letter ∈ letters →
        leftValuation letter = rightValuation letter) →
      letters.foldl
          (fun value letter =>
            semigroup.mul value (leftValuation letter)) initial =
        letters.foldl
          (fun value letter =>
            semigroup.mul value (rightValuation letter)) initial
  | [], _, _ => rfl
  | letter :: rest, initial, agree => by
      simp only [List.foldl_cons]
      rw [agree letter (List.Mem.head rest)]
      apply foldl_eval_congr semigroup
      intro tested member
      exact agree tested (List.Mem.tail letter member)

private theorem eval_congr_on_support {S : Type}
    (semigroup : Semigroup S)
    (leftValuation rightValuation : Nat → S)
    (word : Word Nat)
    (agree : ∀ letter, letter ∈ word.toList →
      leftValuation letter = rightValuation letter) :
    semigroup.eval leftValuation word =
      semigroup.eval rightValuation word := by
  cases word with
  | mk first rest =>
      simp only [Semigroup.eval]
      rw [agree first (by simp [Word.toList])]
      apply foldl_eval_congr semigroup
      intro letter member
      exact agree letter (List.Mem.tail first member)

/-- Zero-based catalogue state 2 is the actual lower-factor right identity. -/
theorem s5_636_right_identity (value : Fin 5) :
    SemigroupBasis.CoRoots.S5_636.table.semigroup.mul
      value SemigroupBasis.CoRoots.S5_636.identityElement = value :=
  (SemigroupBasis.CoRoots.S5_636.identityElement_certificate value).2

/-- A globally fresh terminal variable can be stripped over the actual factor. -/
theorem simpleFinal_stem_valid
    (final : Nat) (left right : Word Nat)
    (finalNotLeft : final ∉ left.toList)
    (finalNotRight : final ∉ right.toList)
    (wholeValid :
      (⟨left ++ Word.singleton final,
        right ++ Word.singleton final⟩ : Identity Nat).SatisfiedBy
        SemigroupBasis.CoRoots.S5_636.table.semigroup) :
    (⟨left, right⟩ : Identity Nat).SatisfiedBy
      SemigroupBasis.CoRoots.S5_636.table.semigroup := by
  intro valuation
  let lifted : Nat → Fin 5 :=
    fun letter =>
      if letter = final then
        SemigroupBasis.CoRoots.S5_636.identityElement
      else valuation letter
  have leftAgree :
      SemigroupBasis.CoRoots.S5_636.table.semigroup.eval valuation left =
        SemigroupBasis.CoRoots.S5_636.table.semigroup.eval lifted left := by
    apply eval_congr_on_support
    intro letter member
    have different : letter ≠ final := by
      intro equal
      subst letter
      exact finalNotLeft member
    simp [lifted, different]
  have rightAgree :
      SemigroupBasis.CoRoots.S5_636.table.semigroup.eval valuation right =
        SemigroupBasis.CoRoots.S5_636.table.semigroup.eval lifted right := by
    apply eval_congr_on_support
    intro letter member
    have different : letter ≠ final := by
      intro equal
      subst letter
      exact finalNotRight member
    simp [lifted, different]
  have evaluated := wholeValid lifted
  simp only [Semigroup.eval_append, Semigroup.eval_singleton] at evaluated
  have liftedFinal :
      lifted final = SemigroupBasis.CoRoots.S5_636.identityElement := by
    simp [lifted]
  rw [liftedFinal, s5_636_right_identity,
    s5_636_right_identity] at evaluated
  exact leftAgree.trans <| evaluated.trans rightAgree.symm

/-- The exact joint descriptor preserves whether the terminal stem is empty. -/
theorem splitStem_nil_iff
    (identity : Identity Nat) (descriptor : JointDescriptor identity) :
    (splitPrefixFinal identity.lhs).1 = [] ↔
      (splitPrefixFinal identity.rhs).1 = [] := by
  have support :=
    support_of_firstOccurrence_eq descriptor.firstOccurrenceOrder
  have prefixSupport :=
    prefix_support_of_support_and_simple
      identity support descriptor.simpleFinal
  constructor
  · intro leftEmpty
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro letter rightMember
    have leftMember := (prefixSupport letter).mpr rightMember
    rw [leftEmpty] at leftMember
    simpa using leftMember
  · intro rightEmpty
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro letter leftMember
    have rightMember := (prefixSupport letter).mp leftMember
    rw [rightEmpty] at rightMember
    simpa using rightMember

/-- Complete unrestricted derivability throughout the globally simple-final
stratum, with no finite-alphabet or bounded-length hypothesis. -/
theorem derivesSimpleFinal
    (identity : Identity Nat)
    (descriptor : JointDescriptor identity)
    (leftSimple :
      (splitPrefixFinal identity.lhs).2 ∉
        (splitPrefixFinal identity.lhs).1) :
    Derives basis identity.lhs identity.rhs := by
  let final := (splitPrefixFinal identity.lhs).2
  have rightSimple :=
    (descriptor.simpleFinal final).mp ⟨rfl, leftSimple⟩
  have finalEq : (splitPrefixFinal identity.rhs).2 = final :=
    rightSimple.1
  have rightAbsent : final ∉ (splitPrefixFinal identity.rhs).1 :=
    rightSimple.2
  have stemsEmpty := splitStem_nil_iff identity descriptor
  cases leftStem : (splitPrefixFinal identity.lhs).1 with
  | nil =>
      have rightStem := stemsEmpty.mp leftStem
      have leftReconstructed := wordOfPrefixFinal_split identity.lhs
      have rightReconstructed := wordOfPrefixFinal_split identity.rhs
      rw [leftStem] at leftReconstructed
      rw [rightStem] at rightReconstructed
      simp only [wordOfPrefixFinal_nil] at leftReconstructed
      simp only [wordOfPrefixFinal_nil] at rightReconstructed
      rw [← leftReconstructed, ← rightReconstructed, finalEq]
      exact Derives.refl _
  | cons leftFirst leftRest =>
      cases rightStem : (splitPrefixFinal identity.rhs).1 with
      | nil =>
          have impossible := stemsEmpty.mpr rightStem
          rw [leftStem] at impossible
          contradiction
      | cons rightFirst rightRest =>
          let leftWord :=
            SemigroupBasis.CoRoots.S5_107.listWordOfCons
              leftFirst leftRest
          let rightWord :=
            SemigroupBasis.CoRoots.S5_107.listWordOfCons
              rightFirst rightRest
          have leftFinalAbsent : final ∉ leftWord.toList := by
            simpa [final, leftWord,
              SemigroupBasis.CoRoots.S5_107.listWordOfCons,
              Word.toList, leftStem] using leftSimple
          have rightFinalAbsent : final ∉ rightWord.toList := by
            simpa [rightWord,
              SemigroupBasis.CoRoots.S5_107.listWordOfCons,
              Word.toList, rightStem] using rightAbsent
          have leftShape :
              leftWord ++ Word.singleton final = identity.lhs := by
            apply Word.toList_injective
            rw [Word.toList_append, Word.toList_singleton,
              ← wordOfPrefixFinal_split identity.lhs,
              toList_wordOfPrefixFinal, leftStem]
            rfl
          have rightShape :
              rightWord ++ Word.singleton final = identity.rhs := by
            apply Word.toList_injective
            rw [Word.toList_append, Word.toList_singleton,
              ← wordOfPrefixFinal_split identity.rhs,
              toList_wordOfPrefixFinal, rightStem, finalEq]
            rfl
          have lowerValid :=
            (lower_valid_iff_order_and_period identity).mpr
              ⟨descriptor.firstOccurrenceOrder,
                descriptor.periodTwoMultiplicity⟩
          have wholeValid :
              (⟨leftWord ++ Word.singleton final,
                rightWord ++ Word.singleton final⟩ :
                Identity Nat).SatisfiedBy
                  SemigroupBasis.CoRoots.S5_636.table.semigroup := by
            simpa only [leftShape, rightShape] using lowerValid
          have stemValid :=
            simpleFinal_stem_valid final leftWord rightWord
              leftFinalAbsent rightFinalAbsent wholeValid
          have lifted :=
            derivesSameSuffixOfLowerValid
              leftWord rightWord (Word.singleton final) stemValid
          simpa only [leftShape, rightShape] using lifted

/-- Full unrestricted completeness for the exact joint descriptor. -/
theorem derivesOfJointDescriptor
    (identity : Identity Nat) (descriptor : JointDescriptor identity) :
    Derives basis identity.lhs identity.rhs := by
  by_cases repeated :
      (splitPrefixFinal identity.lhs).2 ∈
        (splitPrefixFinal identity.lhs).1
  · exact derivesRepeatedFinal identity descriptor repeated
  · exact derivesSimpleFinal identity descriptor repeated

/-- Full unrestricted factor-intersection completeness for the exact frozen
eleven-law Rank014 displayed basis. -/
theorem derivesOfFactorValid
    (identity : Identity Nat)
    (markerValid :
      identity.SatisfiedBy Generated.S3_6.table.semigroup)
    (lowerValid :
      identity.SatisfiedBy SemigroupBasis.CoRoots.S5_636.table.semigroup) :
    Derives basis identity.lhs identity.rhs :=
  derivesOfJointDescriptor identity
    ((factor_valid_iff_joint_descriptor identity).mp
      ⟨markerValid, lowerValid⟩)

/-- Exact bidirectional unrestricted identity theory of the frozen pair. -/
theorem factor_valid_iff_derives
    (identity : Identity Nat) :
    (identity.SatisfiedBy Generated.S3_6.table.semigroup ∧
      identity.SatisfiedBy SemigroupBasis.CoRoots.S5_636.table.semigroup) ↔
      Derives basis identity.lhs identity.rhs := by
  constructor
  · rintro ⟨markerValid, lowerValid⟩
    exact derivesOfFactorValid identity markerValid lowerValid
  · intro derivation
    exact ⟨derivation.sound markerModels,
      derivation.sound lowerModels⟩

end SemigroupBasis.CoRoots.Order6Day8.S3_6.Rank014IntersectionCompleteness
