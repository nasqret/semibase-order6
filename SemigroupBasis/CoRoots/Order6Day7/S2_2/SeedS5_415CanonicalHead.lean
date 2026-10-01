import SemigroupBasis.CoRoots.Order6Day7.S2_2.SeedS5_415HeadRetargetBoundary

/-!
# Rank040: the corrected head dichotomy and invariant canonical head

This module proves the correction in msg-0351 without a finite-word bound.
If any return-capable head exists, the original head is return-capable.
Otherwise the literal head is forced by the actual Brandt signature.
Consequently the least return-capable head, with the original head as the
empty-set fallback, is total and invariant under both actual factor theories.

This is the head-selection layer only. It does not derive a selected return
word from the frozen rank040 basis and does not claim BrandtParityLift.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank040.HeadRetargetBoundary

open SemigroupBasis
open SemigroupBasis.CoRoots.S5_415

theorem ClassWalk.precompose
    {word : Word Nat} {source middle target : BrandtEndpoint}
    (walk : ClassWalk word middle target)
    (connection : BrandtEndpointConnected word source middle) :
    ClassWalk word source target := by
  cases walk with
  | stationary last => exact .stationary (.trans connection last)
  | step letter member entry rest =>
      exact .step letter member (.trans connection entry) rest

theorem ClassWalk.trans
    {word : Word Nat} {source middle target : BrandtEndpoint}
    (first : ClassWalk word source middle)
    (second : ClassWalk word middle target) : ClassWalk word source target := by
  revert second
  induction first with
  | stationary connection =>
      intro second
      exact second.precompose connection
  | step letter member entry _ ih =>
      intro second
      exact .step letter member entry (ih second)

theorem ClassWalk.postcompose
    {word : Word Nat} {source middle target : BrandtEndpoint}
    (walk : ClassWalk word source middle)
    (connection : BrandtEndpointConnected word middle target) :
    ClassWalk word source target :=
  walk.trans (.stationary connection)

theorem ClassWalk.transportSameSignature
    {left right : Word Nat} (same : SameBrandtSignature left right)
    {source target : BrandtEndpoint} (walk : ClassWalk left source target) :
    ClassWalk right source target := by
  induction walk with
  | stationary connection =>
      exact .stationary
        ((brandtEndpointConnected_iff_of_sameBrandtSignature same _ _).mp connection)
  | step letter member entry _ ih =>
      exact .step letter ((same.1 letter).mp member)
        ((brandtEndpointConnected_iff_of_sameBrandtSignature same _ _).mp entry) ih

private theorem walkToTailLetter (word : Word Nat) (target : Nat)
    (previous : Nat) (letters : List Nat)
    (support : ∀ letter, letter ∈ letters → letter ∈ word.toList)
    (edges : ∀ first second, (first, second) ∈ Word.adjacentPairsFrom previous letters →
      (first, second) ∈ word.adjacentPairs)
    (member : target ∈ letters) :
    ClassWalk word (BrandtEndpoint.outgoing previous) (BrandtEndpoint.incoming target) := by
  induction letters generalizing previous with
  | nil => simp at member
  | cons next rest ih =>
      have entry : BrandtEndpointConnected word (BrandtEndpoint.outgoing previous)
          (BrandtEndpoint.incoming next) :=
        .adjacency (edges previous next (by simp [Word.adjacentPairsFrom]))
      rcases List.mem_cons.mp member with targetEq | later
      · simpa only [targetEq] using ClassWalk.stationary entry
      · exact .step next (support next (by simp)) entry
          (ih next (fun letter present => support letter (List.mem_cons_of_mem _ present))
            (fun first second edge => edges first second
              (List.mem_cons_of_mem _ edge)) later)

/-- Following the actual word gives a class-graph path to each later letter. -/
theorem headPathToTailMember
    {word : Word Nat} {letter : Nat} (member : letter ∈ word.tail) :
    ClassWalk word (BrandtEndpoint.outgoing word.head) (BrandtEndpoint.incoming letter) :=
  walkToTailLetter word letter word.head word.tail
    (fun _ present => List.mem_cons_of_mem _ present)
    (fun _ _ edge => edge) member

theorem repeatedHeadEligible
    {word : Word Nat} (repeated : word.head ∈ word.tail) :
    EligibleHead word word.head :=
  ⟨by simp [Word.toList], .refl _, headPathToTailMember repeated⟩

/-- Any eligible letter forces a return path for the word's original head. -/
theorem originalHeadEligibleOfAny
    {word : Word Nat} {letter : Nat} (eligible : EligibleHead word letter) :
    EligibleHead word word.head := by
  by_cases sameHead : letter = word.head
  · simpa only [sameHead] using eligible
  · have later : letter ∈ word.tail :=
      (List.mem_cons.mp eligible.1).resolve_left sameHead
    refine ⟨by simp [Word.toList], .refl _, ?_⟩
    exact (headPathToTailMember later).trans
      (.step letter eligible.1 (.refl _) eligible.2.2)

/-- The corrected dichotomy of msg-0351 is unrestricted. -/
theorem headDichotomy (word : Word Nat) :
    EligibleHead word word.head ∨ ∀ letter, ¬ EligibleHead word letter := by
  classical
  by_cases eligible : EligibleHead word word.head
  · exact Or.inl eligible
  · exact Or.inr (fun _ witness => eligible (originalHeadEligibleOfAny witness))

private theorem sameSignatureSymm
    {left right : Word Nat} (same : SameBrandtSignature left right) :
    SameBrandtSignature right left := by
  refine ⟨fun letter => (same.1 letter).symm, ?_⟩
  intro assignment
  refine ⟨(same.2 assignment).1.symm, ?_⟩
  intro compatible
  have coordinates := (same.2 assignment).2 ((same.2 assignment).1.mpr compatible)
  exact ⟨coordinates.1.symm, coordinates.2.symm⟩

private theorem transportEligibleHead
    {left right : Word Nat} (same : SameBrandtSignature left right)
    {letter : Nat} (eligible : EligibleHead left letter) :
    EligibleHead right letter := by
  have headAlignment :=
    (brandtEndpointConnected_iff_of_sameBrandtSignature same _ _).mp
      (incomingHeads_connected_of_sameBrandtSignature same)
  refine ⟨(same.1 letter).mp eligible.1, ?_, ?_⟩
  · exact .trans
      ((brandtEndpointConnected_iff_of_sameBrandtSignature same _ _).mp eligible.2.1)
      headAlignment
  · exact (eligible.2.2.transportSameSignature same).postcompose headAlignment

theorem eligibleHead_iff_of_sameBrandtSignature
    {left right : Word Nat} (same : SameBrandtSignature left right) (letter : Nat) :
    EligibleHead left letter ↔ EligibleHead right letter :=
  ⟨transportEligibleHead same, transportEligibleHead (sameSignatureSymm same)⟩

private theorem adjacentTargetMemTail
    {word : Word Nat} {source target : Nat}
    (edge : (source, target) ∈ word.adjacentPairs) : target ∈ word.tail := by
  cases word with
  | mk head tail =>
      change (source, target) ∈ Word.adjacentPairsFrom head tail at edge
      change target ∈ tail
      induction tail generalizing head with
      | nil => simp [Word.adjacentPairsFrom] at edge
      | cons next rest ih =>
          simp only [Word.adjacentPairsFrom, List.mem_cons] at edge
          rcases edge with first | later
          · have targetEq : target = next := congrArg Prod.snd first
            simp [targetEq]
          · exact List.mem_cons_of_mem next (ih next later)

/-- A nonrepeated head has an isolated incoming endpoint, so equivalent
Brandt words must have exactly that literal head. -/
theorem headsEqualOfNonrepeated
    {left right : Word Nat} (same : SameBrandtSignature left right)
    (notRepeated : left.head ∉ left.tail) : left.head = right.head := by
  classical
  let assignment : EndpointAssignment := fun letter =>
    (if letter = left.head then 0 else 1, 1)
  have compatible : Compatible assignment left := by
    apply (compatible_iff_adjacent_endpoint_eq assignment left).mpr
    intro source target edge
    have targetDifferent : target ≠ left.head := by
      intro equality
      exact notRepeated (equality ▸ adjacentTargetMemTail edge)
    simp [assignment, targetDifferent]
  apply Decidable.byContradiction
  intro different
  have equality := ((same.2 assignment).2 compatible).1
  simp [assignment, Ne.symm different] at equality

theorem headsEqualOfEmptyEligible
    {left right : Word Nat} (same : SameBrandtSignature left right)
    (empty : ∀ letter, ¬ EligibleHead left letter) : left.head = right.head :=
  headsEqualOfNonrepeated same
    (fun repeated => empty left.head (repeatedHeadEligible repeated))

/-- Specification of min E, with the exact empty-set fallback. -/
def IsCanonicalHead (word : Word Nat) (head : Nat) : Prop :=
  (EligibleHead word head ∧ ∀ letter, EligibleHead word letter → head ≤ letter) ∨
  ((∀ letter, ¬ EligibleHead word letter) ∧ head = word.head)

private theorem existsLeastNat (predicate : Nat → Prop)
    (nonempty : ∃ n, predicate n) :
    ∃ n, predicate n ∧ ∀ m, predicate m → n ≤ m := by
  classical
  have bounded : ∀ bound, predicate bound →
      ∃ n, predicate n ∧ ∀ m, predicate m → n ≤ m := by
    intro bound
    induction bound using Nat.strongRecOn with
    | ind bound ih =>
        intro atBound
        by_cases smaller : ∃ m, m < bound ∧ predicate m
        · obtain ⟨m, below, atM⟩ := smaller
          exact ih m below atM
        · refine ⟨bound, atBound, ?_⟩
          intro m atM
          apply Decidable.byContradiction
          intro notBelow
          exact smaller ⟨m, by omega, atM⟩
  obtain ⟨bound, atBound⟩ := nonempty
  exact bounded bound atBound

theorem existsCanonicalHead (word : Word Nat) : ∃ head, IsCanonicalHead word head := by
  classical
  by_cases nonempty : ∃ letter, EligibleHead word letter
  · obtain ⟨head, eligible, least⟩ := existsLeastNat (EligibleHead word) nonempty
    exact ⟨head, Or.inl ⟨eligible, least⟩⟩
  · exact ⟨word.head, Or.inr ⟨fun letter eligible => nonempty ⟨letter, eligible⟩, rfl⟩⟩

noncomputable def canonicalHead (word : Word Nat) : Nat :=
  Classical.choose (existsCanonicalHead word)

theorem canonicalHead_spec (word : Word Nat) : IsCanonicalHead word (canonicalHead word) :=
  Classical.choose_spec (existsCanonicalHead word)

theorem canonicalHead_mem (word : Word Nat) : canonicalHead word ∈ word.toList := by
  rcases canonicalHead_spec word with ⟨eligible, _⟩ | ⟨_, unchanged⟩
  · exact eligible.1
  · rw [unchanged]
    simp [Word.toList]

/-- The corrected selector is invariant under the ACTUAL Brandt signature. -/
theorem canonicalHead_eq_of_sameBrandtSignature
    {left right : Word Nat} (same : SameBrandtSignature left right) :
    canonicalHead left = canonicalHead right := by
  have equivalent := eligibleHead_iff_of_sameBrandtSignature same
  rcases canonicalHead_spec left with ⟨leftEligible, leftLeast⟩ | ⟨leftEmpty, leftHead⟩
  · rcases canonicalHead_spec right with ⟨rightEligible, rightLeast⟩ | ⟨rightEmpty, _⟩
    · exact Nat.le_antisymm
        (leftLeast _ ((equivalent _).mpr rightEligible))
        (rightLeast _ ((equivalent _).mp leftEligible))
    · exact False.elim (rightEmpty _ ((equivalent _).mp leftEligible))
  · rcases canonicalHead_spec right with ⟨rightEligible, _⟩ | ⟨_, rightHead⟩
    · exact False.elim (leftEmpty _ ((equivalent _).mpr rightEligible))
    · exact leftHead.trans ((headsEqualOfEmptyEligible same leftEmpty).trans rightHead.symm)

theorem canonicalHead_eq_of_factorValid
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy leftTable.semigroup)
    (rightValid : identity.SatisfiedBy rightTable.semigroup) :
    canonicalHead identity.lhs = canonicalHead identity.rhs :=
  canonicalHead_eq_of_sameBrandtSignature
    (BrandtParityBridge.sameFactorSignature_of_factorValid identity leftValid rightValid).brandt

theorem singletonCanonicalHead (letter : Nat) :
    canonicalHead (Word.singleton letter) = letter := by
  rcases canonicalHead_spec (Word.singleton letter) with ⟨eligible, _⟩ | ⟨_, unchanged⟩
  · exact False.elim (singletonEligibleHeadEmpty letter _ eligible)
  · exact unchanged

theorem law03CanonicalHeadsAgree : canonicalHead law03.lhs = canonicalHead law03.rhs :=
  canonicalHead_eq_of_factorValid law03 left_law03_valid right_law03_valid

/-- A class-graph walk materializes as a finite return tail, with all support,
internal connectivity and final connectivity evidence retained. -/
theorem ClassWalk.existsReturnTail
    {word : Word Nat} {source target : BrandtEndpoint}
    (walk : ClassWalk word source target) :
    ∀ previous, source = BrandtEndpoint.outgoing previous →
      ∃ tail : List Nat,
        (∀ letter, letter ∈ tail → letter ∈ word.toList) ∧
        (∀ first second, (first, second) ∈ Word.adjacentPairsFrom previous tail →
          BrandtEndpointConnected word (BrandtEndpoint.outgoing first)
            (BrandtEndpoint.incoming second)) ∧
        BrandtEndpointConnected word
          (BrandtEndpoint.outgoing (tail.getLastD previous)) target := by
  induction walk with
  | stationary connection =>
      intro previous sourceEq
      refine ⟨[], by simp, by simp [Word.adjacentPairsFrom], ?_⟩
      exact sourceEq ▸ connection
  | step letter present entry _ ih =>
      intro previous sourceEq
      obtain ⟨tail, support, edges, finalConnection⟩ := ih letter rfl
      refine ⟨letter :: tail, ?_, ?_, ?_⟩
      · intro next member
        rcases List.mem_cons.mp member with sameLetter | later
        · simpa only [sameLetter] using present
        · exact support next later
      · intro first second edge
        simp only [Word.adjacentPairsFrom, List.mem_cons] at edge
        rcases edge with firstEdge | later
        · cases firstEdge
          exact sourceEq ▸ entry
        · exact edges first second later
      · simpa only [List.getLastD_cons] using finalConnection

/-- Every member of E has an actual closed return word with that literal head. -/
theorem eligibleHeadHasClosedReturnWord
    {word : Word Nat} {letter : Nat} (eligible : EligibleHead word letter) :
    ∃ loop : Word Nat, loop.head = letter ∧ ClosedReturnWord word loop := by
  obtain ⟨tail, support, edges, finalConnection⟩ :=
    eligible.2.2.existsReturnTail letter rfl
  refine ⟨Word.mk letter tail, rfl, ?_⟩
  refine ⟨?_, eligible.2.1, edges, finalConnection⟩
  intro next member
  rcases List.mem_cons.mp member with sameLetter | later
  · simpa only [sameLetter] using eligible.1
  · exact support next later

theorem eligibleHeadRealizable
    {word : Word Nat} {letter : Nat} (eligible : EligibleHead word letter) :
    RealizableHead word letter := by
  obtain ⟨loop, headEq, closed⟩ := eligibleHeadHasClosedReturnWord eligible
  simpa only [headEq] using closed.realizableHead

/-- The exact repaired characterization: a head is either unchanged or
genuinely return-capable. The empty-return restriction is never dropped. -/
theorem realizableHead_iff
    (word : Word Nat) (letter : Nat) :
    RealizableHead word letter ↔ letter = word.head ∨ EligibleHead word letter := by
  constructor
  · rintro ⟨target, headEq, leftValid, rightValid⟩
    by_cases sameHead : letter = word.head
    · exact Or.inl sameHead
    · apply Or.inr
      have same :=
        (BrandtParityBridge.sameFactorSignature_of_factorValid
          (Identity.mk word target) leftValid rightValid).brandt
      have targetEligible : EligibleHead target target.head := by
        rcases headDichotomy target with eligible | empty
        · exact eligible
        · have sameHeads := headsEqualOfEmptyEligible (sameSignatureSymm same) empty
          exact False.elim (sameHead (headEq.symm.trans sameHeads))
      have eligible := (eligibleHead_iff_of_sameBrandtSignature same target.head).mpr
        targetEligible
      simpa only [headEq] using eligible
  · rintro (unchanged | eligible)
    · rw [unchanged]
      exact originalHeadRealizable word
    · exact eligibleHeadRealizable eligible

theorem canonicalHeadRealizable (word : Word Nat) :
    RealizableHead word (canonicalHead word) := by
  rcases canonicalHead_spec word with ⟨eligible, _⟩ | ⟨_, unchanged⟩
  · exact eligibleHeadRealizable eligible
  · rw [unchanged]
    exact originalHeadRealizable word

/-- The remaining head-stage OWNER obligation. Semantic validity above does
not fill this field; an actual frozen-basis derivation is still required. -/
def ClosedReturnDerivation : Prop :=
  ∀ word loop : Word Nat, ClosedReturnWord word loop →
    Derives Rank040.basis word ((loop ++ loop) ++ word)

theorem existsDerivesCanonicalHead (owner : ClosedReturnDerivation) (word : Word Nat) :
    ∃ target : Word Nat, Derives Rank040.basis word target ∧
      target.head = canonicalHead word := by
  rcases canonicalHead_spec word with ⟨eligible, _⟩ | ⟨_, unchanged⟩
  · obtain ⟨loop, headEq, closed⟩ := eligibleHeadHasClosedReturnWord eligible
    exact ⟨(loop ++ loop) ++ word, owner word loop closed, headEq⟩
  · exact ⟨word, Derives.refl word, unchanged.symm⟩

/-- Full BrandtParityLift would discharge this cut, not conversely. -/
theorem closedReturnDerivation_of_brandtParityLift
    (owner : BrandtParityBridge.BrandtParityLift) : ClosedReturnDerivation := by
  intro word loop closed
  exact owner (Identity.mk word ((loop ++ loop) ++ word))
    closed.sameBrandtSignature (squarePrefixSameOccurrenceParity word loop)

end SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank040.HeadRetargetBoundary
