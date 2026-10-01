import SemigroupBasis.CoRoots.Order6Day7.S2_2.SeedS5_415RetargetCoverage
import SemigroupBasis.CoRoots.S5_415MinimalCounterexample

/-!
# Rank040: exact parity-preserving isolated-letter reduction

The existing Brandt split theorem supplies actual corresponding isolated
markers, disjoint side supports, and recursive Brandt signatures. This
module proves that global occurrence parity also restricts to EACH side.
Recursive rank040 derivations then compose through the real marker, with
empty contexts handled explicitly and no dummy semigroup identity word.

A support-minimal nonderivable join identity therefore has repeated words
on BOTH sides. The full BrandtParityLift, and hence the already-reduced
FixedHeadParityLift, is equivalent to the repeated-pair obligation below.
The repeated-pair obligation remains a named OPEN cut, not a proved field.
No lower-factor derivation that changes parity is transported.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank040.IsolatedParitySplit

open SemigroupBasis
open SemigroupBasis.CoRoots.S5_415
open BrandtParityBridge

def ListSameParity (left right : List Nat) : Prop :=
  ∀ letter, left.count letter % 2 = right.count letter % 2

theorem sameFactorSignature_symm {left right : Word Nat}
    (same : SameFactorSignature left right) : SameFactorSignature right left :=
  ⟨same.brandt.symm, fun letter => (same.parity letter).symm⟩

/-- A letter on the prefix side contributes nothing on either suffix side;
letters outside the prefix support have zero prefix count on both sides. -/
theorem CorrespondingIsolatedSplit.prefixParity
    {left right : Word Nat} {leftPrefix leftSuffix : List Nat} {marker : Nat}
    (split : CorrespondingIsolatedSplit leftPrefix marker leftSuffix right)
    (parity : SameOccurrenceParity left right)
    (leftFactorization : left.toList = leftPrefix ++ [marker] ++ leftSuffix)
    (leftDisjoint : ∀ letter, letter ∈ leftPrefix → letter ∉ leftSuffix) :
    ListSameParity leftPrefix split.rightPrefix := by
  intro letter
  by_cases member : letter ∈ leftPrefix
  · have rightMember := (split.prefix_support letter).mp member
    have leftZero := List.count_eq_zero.mpr (leftDisjoint letter member)
    have rightZero := List.count_eq_zero.mpr (split.supports_disjoint letter rightMember)
    have whole := parity letter
    rw [leftFactorization, split.factorization] at whole
    simp only [List.count_append, leftZero, rightZero, Nat.add_zero] at whole
    omega
  · have rightAbsent : letter ∉ split.rightPrefix :=
      fun found => member ((split.prefix_support letter).mpr found)
    rw [List.count_eq_zero.mpr member, List.count_eq_zero.mpr rightAbsent]

/-- The symmetric restriction to the suffix, including all empty-side cases. -/
theorem CorrespondingIsolatedSplit.suffixParity
    {left right : Word Nat} {leftPrefix leftSuffix : List Nat} {marker : Nat}
    (split : CorrespondingIsolatedSplit leftPrefix marker leftSuffix right)
    (parity : SameOccurrenceParity left right)
    (leftFactorization : left.toList = leftPrefix ++ [marker] ++ leftSuffix)
    (leftDisjoint : ∀ letter, letter ∈ leftPrefix → letter ∉ leftSuffix) :
    ListSameParity leftSuffix split.rightSuffix := by
  intro letter
  by_cases member : letter ∈ leftSuffix
  · have rightMember := (split.suffix_support letter).mp member
    have leftAbsent : letter ∉ leftPrefix := fun found => leftDisjoint letter found member
    have rightAbsent : letter ∉ split.rightPrefix :=
      fun found => split.supports_disjoint letter found rightMember
    have whole := parity letter
    rw [leftFactorization, split.factorization] at whole
    simp only [List.count_append, List.count_eq_zero.mpr leftAbsent,
      List.count_eq_zero.mpr rightAbsent, Nat.zero_add] at whole
    omega
  · have rightAbsent : letter ∉ split.rightSuffix :=
      fun found => member ((split.suffix_support letter).mpr found)
    rw [List.count_eq_zero.mpr member, List.count_eq_zero.mpr rightAbsent]

inductive OptionalFactorSignature : Option (Word Nat) → Option (Word Nat) → Prop
  | none : OptionalFactorSignature none none
  | some {left right : Word Nat} : SameFactorSignature left right →
      OptionalFactorSignature (some left) (some right)

theorem optionalFactorSignature_of_brandt_and_parity
    {left right : List Nat}
    (brandt : OptionalSameBrandtSignature (optionalWordOfList left) (optionalWordOfList right))
    (parity : ListSameParity left right) :
    OptionalFactorSignature (optionalWordOfList left) (optionalWordOfList right) := by
  cases left with
  | nil =>
      cases right with
      | nil => exact .none
      | cons head tail => cases brandt
  | cons leftHead leftTail =>
      cases right with
      | nil => cases brandt
      | cons rightHead rightTail =>
          cases brandt with
          | some same => exact .some ⟨same, parity⟩

/-- Reuse the already-proved unrestricted Brandt split, adding the exact
parity needed by the join. No positional excursion matching is assumed. -/
theorem CorrespondingIsolatedSplit.recursiveFactorSignatures
    {left right : Word Nat} {leftPrefix leftSuffix : List Nat} {marker : Nat}
    (split : CorrespondingIsolatedSplit leftPrefix marker leftSuffix right)
    (same : SameFactorSignature left right)
    (leftFactorization : left.toList = leftPrefix ++ [marker] ++ leftSuffix)
    (markerNotPrefix : marker ∉ leftPrefix) (markerNotSuffix : marker ∉ leftSuffix)
    (leftDisjoint : ∀ letter, letter ∈ leftPrefix → letter ∉ leftSuffix) :
    OptionalFactorSignature (optionalWordOfList leftPrefix) (optionalWordOfList split.rightPrefix) ∧
      OptionalFactorSignature (optionalWordOfList leftSuffix) (optionalWordOfList split.rightSuffix) := by
  have recursive := split.recursiveSignatures same.brandt leftFactorization
    markerNotPrefix markerNotSuffix leftDisjoint
  exact ⟨optionalFactorSignature_of_brandt_and_parity recursive.1
      (CorrespondingIsolatedSplit.prefixParity split same.parity leftFactorization leftDisjoint),
    optionalFactorSignature_of_brandt_and_parity recursive.2
      (CorrespondingIsolatedSplit.suffixParity split same.parity leftFactorization leftDisjoint)⟩

inductive OptionalRank040Derives : Option (Word Nat) → Option (Word Nat) → Prop
  | none : OptionalRank040Derives none none
  | some {left right : Word Nat} : Derives Rank040.basis left right →
      OptionalRank040Derives (some left) (some right)

def isolatedRebuild (marker : Nat) (leading trailing : Option (Word Nat)) : Word Nat :=
  match leading, trailing with
  | none, none => Word.singleton marker
  | none, some suffix => Word.singleton marker ++ suffix
  | some before, none => before ++ Word.singleton marker
  | some before, some suffix => (before ++ Word.singleton marker) ++ suffix

theorem isolatedRebuild_toList (marker : Nat) (leading trailing : Option (Word Nat)) :
    (isolatedRebuild marker leading trailing).toList =
      optionalWordLetters leading ++ [marker] ++ optionalWordLetters trailing := by
  cases leading <;> cases trailing <;>
    simp only [isolatedRebuild, optionalWordLetters, Word.toList_append,
      Word.toList_singleton, List.nil_append, List.append_nil]

/-- Genuine recursive derivations compose around the same isolated marker. -/
theorem derivesIsolatedRebuild (marker : Nat)
    {leftPrefix rightPrefix leftSuffix rightSuffix : Option (Word Nat)}
    (leading : OptionalRank040Derives leftPrefix rightPrefix)
    (trailing : OptionalRank040Derives leftSuffix rightSuffix) :
    Derives Rank040.basis (isolatedRebuild marker leftPrefix leftSuffix)
      (isolatedRebuild marker rightPrefix rightSuffix) := by
  cases leading with
  | none =>
      cases trailing with
      | none => exact Derives.refl _
      | some derived => exact Derives.prepend (Word.singleton marker) derived
  | @some leftPrefix rightPrefix prefixDerived =>
      cases trailing with
      | none => exact Derives.appendRight prefixDerived (Word.singleton marker)
      | @some leftSuffix rightSuffix suffixDerived =>
          exact (Derives.appendRight
            (Derives.appendRight prefixDerived (Word.singleton marker)) leftSuffix).trans
            (Derives.prepend (rightPrefix ++ Word.singleton marker) suffixDerived)

theorem optionalDerives_of_smaller_signature
    {larger : Word Nat} {left right : Option (Word Nat)}
    (same : OptionalFactorSignature left right)
    (smaller : ∀ word, left = some word → brandtSupportCard word < brandtSupportCard larger)
    (induction : ∀ {source target : Word Nat}, SameFactorSignature source target →
      brandtSupportCard source < brandtSupportCard larger → Derives Rank040.basis source target) :
    OptionalRank040Derives left right := by
  cases same with
  | none => exact .none
  | some signature => exact .some (induction signature (smaller _ rfl))

/-- Any non-repeated left word is completely handled by smaller-support
join derivations. Both recursive premises retain occurrence parity. -/
theorem derives_of_nonRepeated_and_smaller
    {left right : Word Nat} (same : SameFactorSignature left right)
    (notRepeated : ¬ RepeatedWord left)
    (induction : ∀ {source target : Word Nat}, SameFactorSignature source target →
      brandtSupportCard source < brandtSupportCard left → Derives Rank040.basis source target) :
    Derives Rank040.basis left right := by
  obtain ⟨marker, leftPrefix, leftSuffix, factorization,
    markerNotPrefix, markerNotSuffix, disjoint⟩ := exists_isolated_split_of_not_repeated notRepeated
  let split := correspondingIsolatedSplit_of_sameBrandtSignature same.brandt
    factorization markerNotPrefix markerNotSuffix disjoint
  have recursive := CorrespondingIsolatedSplit.recursiveFactorSignatures split same factorization
    markerNotPrefix markerNotSuffix disjoint
  have markerMember : marker ∈ left.toList := by rw [factorization]; simp
  have prefixSmaller : ∀ word, optionalWordOfList leftPrefix = some word →
      brandtSupportCard word < brandtSupportCard left := by
    intro word shape
    apply brandtSupportCard_lt_of_optionalWordOfList_of_missing
      (larger := left) (missing := marker) shape
    · intro letter member
      rw [factorization]
      exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl member)))
    · exact markerMember
    · exact markerNotPrefix
  have suffixSmaller : ∀ word, optionalWordOfList leftSuffix = some word →
      brandtSupportCard word < brandtSupportCard left := by
    intro word shape
    apply brandtSupportCard_lt_of_optionalWordOfList_of_missing
      (larger := left) (missing := marker) shape
    · intro letter member
      rw [factorization]
      exact List.mem_append.mpr (Or.inr member)
    · exact markerMember
    · exact markerNotSuffix
  have prefixDerived := optionalDerives_of_smaller_signature recursive.1 prefixSmaller induction
  have suffixDerived := optionalDerives_of_smaller_signature recursive.2 suffixSmaller induction
  have leftShape : left = isolatedRebuild marker
      (optionalWordOfList leftPrefix) (optionalWordOfList leftSuffix) := by
    apply Word.toList_injective
    rw [isolatedRebuild_toList, optionalWordLetters_optionalWordOfList,
      optionalWordLetters_optionalWordOfList]
    exact factorization
  have rightShape : right = isolatedRebuild marker
      (optionalWordOfList split.rightPrefix) (optionalWordOfList split.rightSuffix) := by
    apply Word.toList_injective
    rw [isolatedRebuild_toList, optionalWordLetters_optionalWordOfList,
      optionalWordLetters_optionalWordOfList]
    exact split.factorization
  rw [leftShape, rightShape]
  exact derivesIsolatedRebuild marker prefixDerived suffixDerived

/-- Exact minimal-counterexample reduction for the JOIN, not just Brandt:
any smaller same-signature-and-parity pair is derivable, so both sides here
must be repeated. -/
theorem minimalJoinCounterexample_repeated
    {left right : Word Nat} (same : SameFactorSignature left right)
    (notDerived : ¬ Derives Rank040.basis left right)
    (induction : ∀ {source target : Word Nat}, SameFactorSignature source target →
      brandtSupportCard source < brandtSupportCard left → Derives Rank040.basis source target) :
    RepeatedWord left ∧ RepeatedWord right := by
  have leftRepeated : RepeatedWord left := by
    apply Classical.byContradiction
    intro notRepeated
    exact notDerived (derives_of_nonRepeated_and_smaller same notRepeated induction)
  have supportEqual := brandtSupportCard_eq_of_sameBrandtSignature same.brandt
  have rightRepeated : RepeatedWord right := by
    apply Classical.byContradiction
    intro notRepeated
    have reverse := derives_of_nonRepeated_and_smaller (sameFactorSignature_symm same)
      notRepeated (fun signature smaller => induction signature (by
        rw [supportEqual]
        exact smaller))
    exact notDerived reverse.symm
  exact ⟨leftRepeated, rightRepeated⟩

/-- OPEN remaining cut: actual derivability on pairs of repeated words. -/
def RepeatedPairParityLift : Prop :=
  ∀ left right : Word Nat, RepeatedWord left → RepeatedWord right →
    SameFactorSignature left right → Derives Rank040.basis left right

/-- Strong support induction removes all isolated-marker cases. -/
theorem brandtParityLift_of_repeatedPairParityLift
    (owner : RepeatedPairParityLift) : BrandtParityLift := by
  have close : ∀ bound, ∀ left right : Word Nat,
      brandtSupportCard left = bound → SameFactorSignature left right →
        Derives Rank040.basis left right := by
    intro bound
    refine Nat.strongRecOn bound ?_
    intro currentBound smaller left right measure same
    apply Classical.byContradiction
    intro notDerived
    have smallerDerived : ∀ {source target : Word Nat}, SameFactorSignature source target →
        brandtSupportCard source < brandtSupportCard left → Derives Rank040.basis source target := by
      intro source target signature decrease
      exact smaller (brandtSupportCard source) (by simpa only [measure] using decrease)
        source target rfl signature
    have repeated := minimalJoinCounterexample_repeated same notDerived smallerDerived
    exact notDerived (owner left right repeated.1 repeated.2 same)
  intro identity same parity
  exact close (brandtSupportCard identity.lhs) identity.lhs identity.rhs rfl ⟨same, parity⟩

/-- An exact reduction; the repeated-pair field is not asserted here. -/
theorem brandtParityLift_iff_repeatedPairParityLift :
    BrandtParityLift ↔ RepeatedPairParityLift :=
  ⟨fun owner left right _ _ same => owner (Identity.mk left right) same.brandt same.parity,
    brandtParityLift_of_repeatedPairParityLift⟩

theorem fixedHeadParityLift_iff_repeatedPairParityLift :
    RetargetCoverage.FixedHeadParityLift ↔ RepeatedPairParityLift :=
  RetargetCoverage.brandtParityLift_iff_fixedHeadParityLift.symm.trans
    brandtParityLift_iff_repeatedPairParityLift

end SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank040.IsolatedParitySplit
