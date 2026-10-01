import SemigroupBasis.CoRoots.Order6Day7.S2_2.SeedS5_415TaggedExposure

/-!
# Rank040: chosen-loop retarget coverage from enclosing literal returns

The FIRST occurrence of an eligible head must lie in a repeated-letter
interval. Otherwise the letters before and after its cut are separated;
a compatible two-coordinate assignment makes that occurrence a one-way
edge, contradicting its return walk. Rotate the enclosing literal return
to the chosen occurrence, then relocate its square to the original head.

This proves the weaker, sufficient head-stage obligation in msg-0361:
ONE genuinely absorbed loop per eligible head. It does NOT assert that
all closed walks are products of literal generators, or prove the stronger
ClosedReturnDerivation statement. Fixed-anchor parity normalization is
still required for the full BrandtParityLift.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank040.RetargetCoverage

open SemigroupBasis
open SemigroupBasis.CoRoots.S5_415
open HeadRetargetBoundary ClosedReturnReplay ExposureReplay CutConnectivity

/-- A compatible coordinate assignment that is nondecreasing on each letter
is nondecreasing along EVERY actual class walk, without a walk-length bound. -/
theorem classWalkCoordinateMonotone
    {word : Word Nat} {source target : BrandtEndpoint} (walk : ClassWalk word source target)
    (assignment : EndpointAssignment) (compatible : Compatible assignment word)
    (monotone : ∀ letter, letter ∈ word.toList → (assignment letter).1 ≤ (assignment letter).2) :
    brandtEndpointValue assignment source ≤ brandtEndpointValue assignment target := by
  induction walk with
  | stationary connected =>
      rw [brandtEndpointValue_eq_of_connected assignment compatible connected]
      exact Nat.le_refl _
  | step letter member entry _ ih =>
      rw [brandtEndpointValue_eq_of_connected assignment compatible entry]
      exact Nat.le_trans (monotone letter member) ih

def separatingCutAssignment (before : List Nat) (pivot : Nat) : EndpointAssignment :=
  fun letter => if letter ∈ before then (0, 0) else if letter = pivot then (0, 1) else (1, 1)

theorem separatingCutAssignmentMonotone (before : List Nat) (pivot letter : Nat) :
    (separatingCutAssignment before pivot letter).1 ≤
      (separatingCutAssignment before pivot letter).2 := by
  unfold separatingCutAssignment
  by_cases earlier : letter ∈ before
  · rw [if_pos earlier]
    decide
  · rw [if_neg earlier]
    by_cases same : letter = pivot
    · rw [if_pos same]
      decide
    · rw [if_neg same]
      decide

private theorem cutAssignmentBefore (before : List Nat) (pivot letter : Nat)
    (member : letter ∈ before) : separatingCutAssignment before pivot letter = (0, 0) := by
  unfold separatingCutAssignment
  rw [if_pos member]

private theorem cutAssignmentPivot (before : List Nat) (pivot : Nat)
    (first : pivot ∉ before) : separatingCutAssignment before pivot pivot = (0, 1) := by
  unfold separatingCutAssignment
  rw [if_neg first, if_pos rfl]

private theorem cutAssignmentAfter (before after : List Nat) (pivot letter : Nat)
    (disjoint : ∀ candidate, candidate ∈ before → candidate ∉ after)
    (last : pivot ∉ after) (member : letter ∈ after) :
    separatingCutAssignment before pivot letter = (1, 1) := by
  have absent : letter ∉ before := fun earlier => disjoint letter earlier member
  have different : letter ≠ pivot := fun same => last (same ▸ member)
  unfold separatingCutAssignment
  rw [if_neg absent, if_neg different]

private theorem final_mem (word : Word Nat) : word.final ∈ word.toList := by
  cases word with
  | mk head tail =>
      simpa only [Word.final, Word.toList] using (List.getLastD_mem_cons (l := tail) (a := head))

private theorem constantCompatible
    (assignment : EndpointAssignment) (word : Word Nat) (value : Fin 2)
    (constant : ∀ letter, letter ∈ word.toList → assignment letter = (value, value)) :
    Compatible assignment word := by
  apply (compatible_iff_adjacent_endpoint_eq assignment word).mpr
  intro source target edge
  obtain ⟨before, after, partition⟩ := adjacentPairSplit word edge
  have sourceMember : source ∈ word.toList := by rw [partition]; simp
  have targetMember : target ∈ word.toList := by rw [partition]; simp
  rw [constant source sourceMember, constant target targetMember]

private theorem singletonCompatible (assignment : EndpointAssignment) (letter : Nat) :
    Compatible assignment (Word.singleton letter) := by
  apply (compatible_iff_adjacent_endpoint_eq assignment _).mpr
  intro source target edge
  simp only [Word.singleton, Word.adjacentPairs, Word.adjacentPairsFrom, List.not_mem_nil] at edge

/-- With no repeated letter spanning the chosen first occurrence, this is a
genuine compatible assignment on the entire source word, not a graph guess. -/
theorem separatingCutAssignmentCompatible
    (word : Word Nat) (pivot : Nat) (before after : List Nat)
    (partition : word.toList = before ++ pivot :: after)
    (first : pivot ∉ before) (last : pivot ∉ after)
    (disjoint : ∀ letter, letter ∈ before → letter ∉ after) :
    Compatible (separatingCutAssignment before pivot) word := by
  let assignment := separatingCutAssignment before pivot
  have pivotValue : assignment pivot = (0, 1) := cutAssignmentPivot before pivot first
  have laterValue : ∀ letter, letter ∈ after → assignment letter = (1, 1) :=
    fun letter member => cutAssignmentAfter before after pivot letter disjoint last member
  have suffixCompatible : Compatible assignment (Word.mk pivot after) := by
    cases after with
    | nil => exact singletonCompatible assignment pivot
    | cons next rest =>
        change Compatible assignment (Word.singleton pivot ++ Word.mk next rest)
        apply (compatibleAppendIff assignment _ _).mpr
        refine ⟨singletonCompatible assignment pivot, ?_,
          constantCompatible assignment (Word.mk next rest) 1 laterValue⟩
        change (assignment pivot).2 = (assignment next).1
        rw [pivotValue, laterValue next (List.mem_cons_self)]
  cases before with
  | nil =>
      have same : word = Word.mk pivot after := Word.toList_injective partition
      simpa only [same] using suffixCompatible
  | cons head tail =>
      let preceding := Word.mk head tail
      have same : word = preceding ++ Word.mk pivot after := Word.toList_injective partition
      rw [same]
      apply (compatibleAppendIff assignment preceding (Word.mk pivot after)).mpr
      refine ⟨constantCompatible assignment preceding 0
        (fun letter member => cutAssignmentBefore (head :: tail) pivot letter member), ?_, suffixCompatible⟩
      change (assignment preceding.final).2 = (assignment pivot).1
      rw [show assignment preceding.final = (0, 0) from
        cutAssignmentBefore (head :: tail) pivot preceding.final (final_mem preceding), pivotValue]

/-- The source's first pivot occurrence cannot return if no repeated-letter
interval encloses it. The coordinates would require 1 ≤ 0. -/
theorem noEligibleHeadAtSeparatedFirstOccurrence
    (word : Word Nat) (pivot : Nat) (before after : List Nat)
    (partition : word.toList = before ++ pivot :: after)
    (first : pivot ∉ before) (last : pivot ∉ after)
    (disjoint : ∀ letter, letter ∈ before → letter ∉ after) :
    ¬ EligibleHead word pivot := by
  intro eligible
  let assignment := separatingCutAssignment before pivot
  have compatible := separatingCutAssignmentCompatible word pivot before after partition first last disjoint
  have bound := classWalkCoordinateMonotone eligible.2.2 assignment compatible
    (fun letter _ => separatingCutAssignmentMonotone before pivot letter)
  have initial := brandtEndpointValue_eq_of_connected assignment compatible eligible.2.1
  have pivotValue : assignment pivot = (0, 1) := cutAssignmentPivot before pivot first
  have outgoing : brandtEndpointValue assignment (BrandtEndpoint.outgoing pivot) = (1 : Fin 2) := by
    change (assignment pivot).2 = 1
    rw [pivotValue]
  have incoming : brandtEndpointValue assignment (BrandtEndpoint.incoming pivot) = (0 : Fin 2) := by
    change (assignment pivot).1 = 0
    rw [pivotValue]
  rw [outgoing, ← initial, incoming] at bound
  exact (by decide : ¬ ((1 : Fin 2) ≤ 0)) bound

private theorem firstOccurrenceSplit (pivot : Nat) :
    ∀ letters : List Nat, pivot ∈ letters →
      ∃ before after, letters = before ++ pivot :: after ∧ pivot ∉ before
  | [], member => by simp only [List.not_mem_nil] at member
  | head :: tail, member => by
      by_cases same : head = pivot
      · subst head
        exact ⟨[], tail, rfl, by simp⟩
      · have later : pivot ∈ tail := by
          rcases List.mem_cons.mp member with first | later
          · exact False.elim (same first.symm)
          · exact later
        obtain ⟨before, after, partition, absent⟩ := firstOccurrenceSplit pivot tail later
        refine ⟨head :: before, after, ?_, ?_⟩
        · rw [partition]
          rfl
        · intro found
          rcases List.mem_cons.mp found with first | later
          · exact same first.symm
          · exact absent later

/-- A purely combinatorial coverage statement: an eligible first occurrence
is enclosed by two occurrences of SOME letter, possibly the pivot itself. -/
theorem eligibleFirstOccurrenceHasSpan
    (word : Word Nat) (pivot : Nat) (before after : List Nat)
    (partition : word.toList = before ++ pivot :: after) (first : pivot ∉ before)
    (eligible : EligibleHead word pivot) :
    ∃ letter, letter ∈ before ++ [pivot] ∧ letter ∈ after := by
  classical
  apply Classical.byContradiction
  intro missing
  have last : pivot ∉ after := fun member => missing ⟨pivot, by simp, member⟩
  have disjoint : ∀ letter, letter ∈ before → letter ∉ after :=
    fun letter earlier later => missing ⟨letter, List.mem_append.mpr (Or.inl earlier), later⟩
  exact noEligibleHeadAtSeparatedFirstOccurrence word pivot before after partition first last disjoint eligible

/-- Rotate ONE actual literal return, then move its insertion to the head.
The enclosing anchor need not be in the initial endpoint component. -/
theorem enclosingReturnRotationAbsorbs
    (word first second : Word Nat) (before after : List Nat)
    (partition : word.toList = before ++ first.toList ++ second.toList ++ [first.head] ++ after)
    (connected : BrandtEndpointConnected word
      (BrandtEndpoint.incoming second.head) (BrandtEndpoint.incoming word.head)) :
    SquareAbsorbs word (second ++ first) := by
  have coreShape : Word.mk first.head ((first.tail ++ second.toList) ++ [first.head]) =
      (first ++ second) ++ Word.singleton first.head := rfl
  have loopShape : Word.mk first.head (first.tail ++ second.toList) = first ++ second := rfl
  have coreAbsorbs := literalReturnAbsorbs first.head (first.tail ++ second.toList)
  rw [coreShape, loopShape] at coreAbsorbs
  have corePartition : word.toList =
      before ++ ((first ++ second) ++ Word.singleton first.head).toList ++ after := by
    simpa only [Word.toList_append, Word.toList_singleton, List.append_assoc] using partition
  have atAnchor := contextualEndpointAbsorbs before after corePartition coreAbsorbs
  have rotationPartition : word.toList =
      before ++ first.toList ++ (second ++ Word.singleton first.head).toList ++ after := by
    simpa only [Word.toList_append, Word.toList_singleton, List.append_assoc] using partition
  have rotated := endpointAbsorbs_rotation word first second
    (second ++ Word.singleton first.head) before after rotationPartition atAnchor
  exact (endpointAbsorbs_head_iff word (second ++ first)).mp
    (endpointAbsorbs_transport connected rotated)

/-- The chosen-loop owner cut requested in msg-0361. Its witness is genuinely
derived, not supplied by factor semantics or by a stamped unrestricted field. -/
def RetargetCoverage : Prop :=
  ∀ word : Word Nat, ∀ letter : Nat, EligibleHead word letter →
    ∃ loop : Word Nat, loop.head = letter ∧ SquareAbsorbs word loop

theorem eligibleHeadHasDerivedReturn
    (word : Word Nat) (pivot : Nat) (eligible : EligibleHead word pivot) :
    ∃ loop : Word Nat, loop.head = pivot ∧ SquareAbsorbs word loop := by
  obtain ⟨before, after, partition, first⟩ := firstOccurrenceSplit pivot word.toList eligible.1
  obtain ⟨anchor, earlier, later⟩ := eligibleFirstOccurrenceHasSpan word pivot before after
    partition first eligible
  obtain ⟨gap, rest, afterSplit⟩ := List.mem_iff_append.mp later
  rcases List.mem_append.mp earlier with inBefore | isPivot
  · obtain ⟨outer, middle, beforeSplit⟩ := List.mem_iff_append.mp inBefore
    let left := Word.mk anchor middle
    let right := Word.mk pivot gap
    have enclosed : word.toList = outer ++ left.toList ++ right.toList ++ [left.head] ++ rest := by
      rw [partition, beforeSplit, afterSplit]
      simp only [left, right, Word.toList, List.append_assoc, List.cons_append, List.nil_append]
    exact ⟨right ++ left, rfl,
      enclosingReturnRotationAbsorbs word left right outer rest enclosed eligible.2.1⟩
  · have same : anchor = pivot := List.mem_singleton.mp isPivot
    subst anchor
    have enclosed : word.toList = before ++ pivot :: (gap ++ pivot :: rest) := by
      rw [partition, afterSplit]
    exact ⟨Word.mk pivot gap, rfl,
      enclosedReturnAbsorbsAtHead word pivot gap before rest enclosed eligible.2.1⟩

theorem retargetCoverage : RetargetCoverage := eligibleHeadHasDerivedReturn

/-- The actual canonical-head consumer is now unconditional. It does not
require the stronger still-open arbitrary-loop ClosedReturnDerivation. -/
theorem existsDerivesCanonicalHead (word : Word Nat) :
    ∃ target : Word Nat, Derives Rank040.basis word target ∧
      target.head = canonicalHead word := by
  rcases canonicalHead_spec word with ⟨eligible, _⟩ | ⟨_, unchanged⟩
  · obtain ⟨loop, headEq, derived⟩ := eligibleHeadHasDerivedReturn word (canonicalHead word) eligible
    exact ⟨(loop ++ loop) ++ word, derived, headEq⟩
  · exact ⟨word, Derives.refl word, unchanged.symm⟩

/-- Exactly the semantic eligible-head criterion is realized by actual
frozen-basis derivations, with the unchanged-head branch retained. -/
theorem derivableHead_iff (word : Word Nat) (letter : Nat) :
    (∃ target : Word Nat, Derives Rank040.basis word target ∧ target.head = letter) ↔
      letter = word.head ∨ EligibleHead word letter := by
  constructor
  · rintro ⟨target, derived, headEq⟩
    exact (realizableHead_iff word letter).mp
      ⟨target, headEq, derived.sound Rank040.leftModels, derived.sound Rank040.rightModels⟩
  · rintro (unchanged | eligible)
    · exact ⟨word, Derives.refl word, unchanged.symm⟩
    · obtain ⟨loop, headEq, derived⟩ := eligibleHeadHasDerivedReturn word letter eligible
      exact ⟨(loop ++ loop) ++ word, derived, headEq⟩

/-- The exact remaining owner obligation after the proved retarget step.
No implementation or semantic-to-derivational proof is asserted here. -/
def FixedHeadParityLift : Prop :=
  ∀ identity : Identity Nat, identity.lhs.head = identity.rhs.head →
    SameBrandtSignature identity.lhs identity.rhs →
    BrandtParityBridge.SameOccurrenceParity identity.lhs identity.rhs →
      Derives Rank040.basis identity.lhs identity.rhs

/-- Retarget both sides to their common canonical head, invoke ONLY the
fixed-head obligation, and compose the actual frozen-basis derivations. -/
theorem brandtParityLift_of_fixedHeadParityLift
    (owner : FixedHeadParityLift) : BrandtParityBridge.BrandtParityLift := by
  intro identity same parity
  obtain ⟨left, leftDerived, leftHead⟩ := existsDerivesCanonicalHead identity.lhs
  obtain ⟨right, rightDerived, rightHead⟩ := existsDerivesCanonicalHead identity.rhs
  have heads : left.head = right.head :=
    leftHead.trans ((canonicalHead_eq_of_sameBrandtSignature same).trans rightHead.symm)
  have originalLeft := BrandtParityBridge.leftValid_of_sameOccurrenceParity identity parity
  have originalRight := BrandtParityBridge.rightValid_of_sameBrandtSignature identity same
  have leftValid : (Identity.mk left right).SatisfiedBy leftTable.semigroup := by
    intro valuation
    exact (leftDerived.sound Rank040.leftModels valuation).symm.trans
      ((originalLeft valuation).trans (rightDerived.sound Rank040.leftModels valuation))
  have rightValid : (Identity.mk left right).SatisfiedBy rightTable.semigroup := by
    intro valuation
    exact (leftDerived.sound Rank040.rightModels valuation).symm.trans
      ((originalRight valuation).trans (rightDerived.sound Rank040.rightModels valuation))
  have signature := BrandtParityBridge.sameFactorSignature_of_factorValid
    (Identity.mk left right) leftValid rightValid
  exact leftDerived.trans
    ((owner (Identity.mk left right) heads signature.brandt signature.parity).trans rightDerived.symm)

/-- An exact reduction, NOT a claim that the remaining fixed-head lift is proved. -/
theorem brandtParityLift_iff_fixedHeadParityLift :
    BrandtParityBridge.BrandtParityLift ↔ FixedHeadParityLift :=
  ⟨fun owner identity _ same parity => owner identity same parity,
    brandtParityLift_of_fixedHeadParityLift⟩

end SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank040.RetargetCoverage
