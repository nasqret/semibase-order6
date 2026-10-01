import SemigroupBasis.CoRoots.Order6Day7.S2_2.SeedS5_415DoubledReplayBoundary
import SemigroupBasis.CoRoots.S5_415EndpointConnectivity

/-!
# Rank040: exact eligible-head boundary and qualified return-word semantics

The class-graph definition in msg-0350 excludes the original head of every
singleton word. Thus its proposed necessity and total min-E selector fail.
Adding that head while dropping the return condition is not a valid repair:
the actual Brandt matrix unit 1 separates a from aaa.

The qualified square-prefix statement itself is sound. Below it is proved
for arbitrary words from the ACTUAL endpoint-connectivity and parity
invariants, with every content, adjacency and boundary premise explicit.
This is semantic validity, not derivability from the frozen fifteen laws.
The final total witness type distinguishes an unchanged head from a closed
return word. No common canonical choice or BrandtParityLift is asserted.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank040.HeadRetargetBoundary

open SemigroupBasis
open SemigroupBasis.CoRoots.S5_415

/-- A directed walk in the graph of endpoint-equivalence classes. The
stationary constructor allows a zero-length walk inside one class. -/
inductive ClassWalk (word : Word Nat) : BrandtEndpoint → BrandtEndpoint → Prop
  | stationary {source target : BrandtEndpoint} :
      BrandtEndpointConnected word source target → ClassWalk word source target
  | step {source target : BrandtEndpoint} (letter : Nat)
      (member : letter ∈ word.toList)
      (entry : BrandtEndpointConnected word source (BrandtEndpoint.incoming letter))
      (rest : ClassWalk word (BrandtEndpoint.outgoing letter) target) :
      ClassWalk word source target

/-- Literally E(w) from msg-0350, including its return-path condition. -/
def EligibleHead (word : Word Nat) (letter : Nat) : Prop :=
  letter ∈ word.toList ∧
    BrandtEndpointConnected word (BrandtEndpoint.incoming letter)
      (BrandtEndpoint.incoming word.head) ∧
    ClassWalk word (BrandtEndpoint.outgoing letter)
      (BrandtEndpoint.incoming word.head)

private theorem singletonConnected_eq
    {letter : Nat} {source target : BrandtEndpoint}
    (connected : BrandtEndpointConnected (Word.singleton letter) source target) :
    source = target := by
  induction connected with
  | refl endpoint => rfl
  | adjacency member =>
      simp [Word.singleton, Word.adjacentPairs, Word.adjacentPairsFrom] at member
  | symm _ ih => exact ih.symm
  | trans _ _ firstIH secondIH => exact firstIH.trans secondIH

private theorem singletonWalk_outgoing
    {anchor : Nat} {source target : BrandtEndpoint}
    (walk : ClassWalk (Word.singleton anchor) source target)
    (sourceIsOutgoing : source = BrandtEndpoint.outgoing anchor) :
    target = BrandtEndpoint.outgoing anchor := by
  induction walk with
  | stationary connected =>
      exact (singletonConnected_eq connected).symm.trans sourceIsOutgoing
  | step letter member connected _ _ =>
      have letterEq : letter = anchor := by simpa using member
      have mismatch := singletonConnected_eq connected
      rw [sourceIsOutgoing, letterEq] at mismatch
      have sideMismatch := congrArg BrandtEndpoint.side mismatch
      cases sideMismatch

/-- The original definition has NO eligible head for ANY singleton. -/
theorem singletonEligibleHeadEmpty (anchor candidate : Nat) :
    ¬ EligibleHead (Word.singleton anchor) candidate := by
  rintro ⟨member, _, walk⟩
  have candidateEq : candidate = anchor := by simpa using member
  subst candidate
  have mismatch := singletonWalk_outgoing walk rfl
  have sideMismatch := congrArg BrandtEndpoint.side mismatch
  cases sideMismatch

/-- Realizability refers to both actual factors, not an assumed renderer. -/
def RealizableHead (word : Word Nat) (letter : Nat) : Prop :=
  ∃ target : Word Nat, target.head = letter ∧
    (Identity.mk word target).SatisfiedBy leftTable.semigroup ∧
    (Identity.mk word target).SatisfiedBy rightTable.semigroup

theorem originalHeadRealizable (word : Word Nat) :
    RealizableHead word word.head := by
  exact ⟨word, rfl, fun _ => rfl, fun _ => rfl⟩

/-- Section 2's claimed necessity fails even for equality with oneself. -/
theorem eligibleHeadNecessityRefuted :
    ¬ (∀ word letter, RealizableHead word letter → EligibleHead word letter) := by
  intro necessity
  exact singletonEligibleHeadEmpty 0 0
    (necessity (Word.singleton 0) 0 (originalHeadRealizable _))

/-- Consequently min E cannot be a total selector with membership in E. -/
theorem eligibleHeadTotalityRefuted :
    ¬ (∀ word : Word Nat, ∃ letter, EligibleHead word letter) := by
  intro total
  obtain ⟨letter, member⟩ := total (Word.singleton 0)
  exact singletonEligibleHeadEmpty 0 letter member

theorem noEligibleHeadSelector (select : Word Nat → Nat) :
    ¬ (∀ word, EligibleHead word (select word)) := by
  intro selects
  exact singletonEligibleHeadEmpty 0 (select (Word.singleton 0)) (selects _)

def singletonCubeLaw : Identity Nat :=
  ⟨Word.singleton 0, Word.mk 0 [0, 0]⟩

/-- The actual nonloop Brandt unit witnesses the missing return condition. -/
theorem singletonCubeCountervaluation :
    rightTable.semigroup.eval (fun _ => (1 : Fin 5)) singletonCubeLaw.lhs = (1 : Fin 5) ∧
    rightTable.semigroup.eval (fun _ => (1 : Fin 5)) singletonCubeLaw.rhs = (0 : Fin 5) := by
  decide

theorem singletonCubeNotRightValid :
    ¬ singletonCubeLaw.SatisfiedBy rightTable.semigroup := by
  intro valid
  have equality := valid (fun _ => (1 : Fin 5))
  change (1 : Fin 5) = 0 at equality
  exact (by decide : (1 : Fin 5) ≠ 0) equality

private theorem cyclicCubeValue (value : Fin 2) :
    leftTable.mul (leftTable.mul value value) value = value := by
  decide +revert

/-- The counterexample is parity-safe; failure comes from the Brandt factor. -/
theorem singletonCubeLeftValid :
    singletonCubeLaw.SatisfiedBy leftTable.semigroup := by
  intro valuation
  exact (cyclicCubeValue (valuation 0)).symm

theorem singletonCubeNotDerivable :
    ¬ Derives Rank040.basis singletonCubeLaw.lhs singletonCubeLaw.rhs := by
  intro derived
  exact singletonCubeNotRightValid (derived.sound rightModels)

/-- A concrete closed return word, exactly the hypotheses needed for
prefixing by its square. No unproved graph-to-derivation bridge is hidden. -/
structure ClosedReturnWord (word loop : Word Nat) : Prop where
  support : ∀ letter, letter ∈ loop.toList → letter ∈ word.toList
  initial : BrandtEndpointConnected word (BrandtEndpoint.incoming loop.head)
    (BrandtEndpoint.incoming word.head)
  internal : ∀ source target, (source, target) ∈ loop.adjacentPairs →
    BrandtEndpointConnected word (BrandtEndpoint.outgoing source)
      (BrandtEndpoint.incoming target)
  returns : BrandtEndpointConnected word (BrandtEndpoint.outgoing loop.final)
    (BrandtEndpoint.incoming word.head)

/-- The public local append interface exposes the boundary equation. -/
theorem compatibleAppendIff
    (assignment : EndpointAssignment) (left right : Word Nat) :
    Compatible assignment (left ++ right) ↔
      Compatible assignment left ∧
        (assignment left.final).2 = (assignment right.head).1 ∧
          Compatible assignment right := by
  constructor
  · intro fullCompatible
    have fullEdges :=
      (compatible_iff_adjacent_endpoint_eq assignment (left ++ right)).mp fullCompatible
    refine ⟨?_, ?_, ?_⟩
    · apply (compatible_iff_adjacent_endpoint_eq assignment left).mpr
      intro source target edge
      exact fullEdges source target (by
        rw [Word.adjacentPairs_append]
        exact List.mem_append.mpr (Or.inl edge))
    · exact fullEdges left.final right.head (by
        rw [Word.adjacentPairs_append]
        exact List.mem_append.mpr (Or.inr (by simp)))
    · apply (compatible_iff_adjacent_endpoint_eq assignment right).mpr
      intro source target edge
      exact fullEdges source target (by
        rw [Word.adjacentPairs_append]
        exact List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ edge)))
  · rintro ⟨leftCompatible, boundary, rightCompatible⟩
    have leftEdges :=
      (compatible_iff_adjacent_endpoint_eq assignment left).mp leftCompatible
    have rightEdges :=
      (compatible_iff_adjacent_endpoint_eq assignment right).mp rightCompatible
    apply (compatible_iff_adjacent_endpoint_eq assignment (left ++ right)).mpr
    intro source target edge
    rw [Word.adjacentPairs_append] at edge
    rcases List.mem_append.mp edge with edge | edge
    · exact leftEdges source target edge
    · simp only [List.mem_cons] at edge
      rcases edge with edge | edge
      · cases edge
        exact boundary
      · exact rightEdges source target edge

/-- All internal return-word edges are already forced by the source word. -/
theorem ClosedReturnWord.compatible
    {word loop : Word Nat} (closed : ClosedReturnWord word loop)
    (assignment : EndpointAssignment) (compatible : Compatible assignment word) :
    Compatible assignment loop := by
  apply (compatible_iff_adjacent_endpoint_eq assignment loop).mpr
  intro source target member
  exact brandtEndpointValue_eq_of_connected assignment compatible
    (closed.internal source target member)

/-- Unrestricted semantic Brandt preservation of the qualified square prefix. -/
theorem ClosedReturnWord.sameBrandtSignature
    {word loop : Word Nat} (closed : ClosedReturnWord word loop) :
    SameBrandtSignature word ((loop ++ loop) ++ word) := by
  constructor
  · intro letter
    simp only [Word.toList_append, List.mem_append]
    constructor
    · intro member
      exact Or.inr member
    · rintro ((member | member) | member)
      · exact closed.support letter member
      · exact closed.support letter member
      · exact member
  · intro assignment
    have endpoints (compatible : Compatible assignment word) :
        (assignment loop.head).1 = (assignment word.head).1 ∧
        (assignment loop.final).2 = (assignment word.head).1 :=
      ⟨brandtEndpointValue_eq_of_connected assignment compatible closed.initial,
        brandtEndpointValue_eq_of_connected assignment compatible closed.returns⟩
    constructor
    · constructor
      · intro compatible
        have loopCompatible := closed.compatible assignment compatible
        have coordinates := endpoints compatible
        have squareCompatible : Compatible assignment (loop ++ loop) :=
          (compatibleAppendIff assignment loop loop).mpr
            ⟨loopCompatible, coordinates.2.trans coordinates.1.symm, loopCompatible⟩
        apply (compatibleAppendIff assignment (loop ++ loop) word).mpr
        exact ⟨squareCompatible, by simpa only [Word.final_append] using coordinates.2,
          compatible⟩
      · intro compatible
        exact ((compatibleAppendIff assignment (loop ++ loop) word).mp compatible).2.2
    · intro compatible
      constructor
      · exact (endpoints compatible).1.symm
      · simp only [Word.final_append]

/-- Two added copies preserve every occurrence parity, without a graph premise. -/
theorem squarePrefixSameOccurrenceParity (word loop : Word Nat) :
    BrandtParityBridge.SameOccurrenceParity word ((loop ++ loop) ++ word) := by
  intro letter
  simp only [Word.toList_append, List.count_append]
  omega

theorem ClosedReturnWord.sameFactorSignature
    {word loop : Word Nat} (closed : ClosedReturnWord word loop) :
    BrandtParityBridge.SameFactorSignature word ((loop ++ loop) ++ word) :=
  ⟨closed.sameBrandtSignature, squarePrefixSameOccurrenceParity word loop⟩

/-- This proves validity in BOTH ACTUAL factors, not frozen-basis derivability. -/
theorem ClosedReturnWord.factorValid
    {word loop : Word Nat} (closed : ClosedReturnWord word loop) :
    (Identity.mk word ((loop ++ loop) ++ word)).SatisfiedBy leftTable.semigroup ∧
    (Identity.mk word ((loop ++ loop) ++ word)).SatisfiedBy rightTable.semigroup :=
  (BrandtParityBridge.factorValid_iff_sameFactorSignature _).mpr closed.sameFactorSignature

theorem ClosedReturnWord.realizableHead
    {word loop : Word Nat} (closed : ClosedReturnWord word loop) :
    RealizableHead word loop.head :=
  ⟨(loop ++ loop) ++ word, rfl, closed.factorValid⟩

/-- A total repair of the WITNESS interface, not a claimed canonical selector.
The original head is left unchanged; every other supplied case has a real loop. -/
inductive HeadRetargetWitness (word : Word Nat) (letter : Nat) : Prop
  | unchanged : word.head = letter → HeadRetargetWitness word letter
  | closed (loop : Word Nat) : loop.head = letter → ClosedReturnWord word loop →
      HeadRetargetWitness word letter

theorem headRetargetWitnessTotal (word : Word Nat) :
    ∃ letter, HeadRetargetWitness word letter :=
  ⟨word.head, HeadRetargetWitness.unchanged rfl⟩

theorem HeadRetargetWitness.realizable
    {word : Word Nat} {letter : Nat} (witness : HeadRetargetWitness word letter) :
    RealizableHead word letter := by
  cases witness with
  | unchanged headEq =>
      rw [← headEq]
      exact originalHeadRealizable word
  | closed loop headEq closed =>
      rw [← headEq]
      exact closed.realizableHead

end SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank040.HeadRetargetBoundary
