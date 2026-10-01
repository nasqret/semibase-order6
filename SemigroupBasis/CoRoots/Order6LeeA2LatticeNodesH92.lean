import SemigroupBasis.CoRoots.Order6LeeA2LatticeNodesSingletonNormal

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6LeeA2LatticeNodesH92

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.Order6LeeA2LatticeNodesBarrierFinal
open SemigroupBasis.CoRoots.Order6LeeA2LatticeNodesSingletonNormal
open SemigroupBasis.CoRoots.S5_868
  (maximalFactorWord)

/-!
# The H92 singleton residual

This module isolates the remaining derivational work for
`SystemH92e6c7c087f0`.  Its first result closes the semantic bridge which is
specific to this residual: equality of the ordered `S4_70` component
signatures already transports every `S4_69` exact cut.  Thus the
`SamePredecessorFinals` field really does pair the literal final of each
nonempty predecessor of a bare successor in the two component chains.

The final section records three candidate local interfaces for a future
square-guarded chain induction.  Two related moves already follow from the
frozen pilot normalizer.  The genuinely new pieces are deliberately stated
as named obligations, rather than hidden behind an endpoint theorem:

* switching the first component without a left guard;
* exposing a square at the start of every non-bare successor;
* changing an interior component's final across that exposed square.

This module does not yet prove that the three candidates imply chain
assembly.  Its final conditional wrapper therefore remains
completeness-equivalent, rather than a completed reduction.
-/

/-! ## Ordered components transport all exact cuts -/

/-- Every law of the `S4_70` component basis is valid in the `S4_69`
separator detector.  The latter has the same six laws and one additional
square law. -/
private theorem uniqueSeparatorFour_models_connectedComponentFourBasis :
    Models uniqueSeparatorFour.semigroup connectedComponentFourBasis := by
  intro identity member
  apply uniqueSeparatorFourBasis_models identity
  simp only [connectedComponentFourBasis, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · change connectedComponentPowerLaw ∈ uniqueSeparatorFourBasis
    simpa only [
      show connectedComponentPowerLaw = uniqueSeparatorPowerLaw by rfl]
      using
        (show uniqueSeparatorPowerLaw ∈ uniqueSeparatorFourBasis by
          simp [uniqueSeparatorFourBasis])
  · change connectedComponentLeftDuplicationLaw ∈
      uniqueSeparatorFourBasis
    simpa only [
      show connectedComponentLeftDuplicationLaw =
        uniqueSeparatorLeftDuplicationLaw by rfl]
      using
        (show uniqueSeparatorLeftDuplicationLaw ∈
            uniqueSeparatorFourBasis by
          simp [uniqueSeparatorFourBasis])
  · change connectedComponentMiddleDuplicationLaw ∈
      uniqueSeparatorFourBasis
    simpa only [
      show connectedComponentMiddleDuplicationLaw =
        uniqueSeparatorMiddleDuplicationLaw by rfl]
      using
        (show uniqueSeparatorMiddleDuplicationLaw ∈
            uniqueSeparatorFourBasis by
          simp [uniqueSeparatorFourBasis])
  · change connectedComponentRightDuplicationLaw ∈
      uniqueSeparatorFourBasis
    simpa only [
      show connectedComponentRightDuplicationLaw =
        uniqueSeparatorRightDuplicationLaw by rfl]
      using
        (show uniqueSeparatorRightDuplicationLaw ∈
            uniqueSeparatorFourBasis by
          simp [uniqueSeparatorFourBasis])
  · change connectedComponentAlternatingLaw ∈ uniqueSeparatorFourBasis
    simpa only [
      show connectedComponentAlternatingLaw =
        uniqueSeparatorAlternatingLaw by rfl]
      using
        (show uniqueSeparatorAlternatingLaw ∈
            uniqueSeparatorFourBasis by
          simp [uniqueSeparatorFourBasis])
  · change connectedComponentRotationLaw ∈ uniqueSeparatorFourBasis
    simpa only [
      show connectedComponentRotationLaw =
        uniqueSeparatorRotationLaw by rfl]
      using
        (show uniqueSeparatorRotationLaw ∈ uniqueSeparatorFourBasis by
          simp [uniqueSeparatorFourBasis])

/-- Equal ordered component signatures give equal term functions in the
weaker `S4_69` detector.  This is the key direction: normalize with the
six-law `S4_70` basis, then interpret that derivation in `S4_69`. -/
theorem uniqueSeparatorFour_equalEval_of_sameComponents
    {left right : Word Nat}
    (components :
      connectedComponentSignaturesWord left =
        connectedComponentSignaturesWord right) :
    ∀ valuation : Nat → Fin 4,
      uniqueSeparatorFour.semigroup.eval valuation left =
        uniqueSeparatorFour.semigroup.eval valuation right := by
  have leftNormal :=
    connectedComponentFour_derivesCanonical left
  have rightNormal :=
    connectedComponentFour_derivesCanonical right
  have normalEq :
      connectedComponentCanonicalRender left =
        connectedComponentCanonicalRender right :=
    connectedComponentCanonicalRender_eq_of_signature_eq components
  have derivation :
      Derives connectedComponentFourBasis left right := by
    exact leftNormal.trans <| by
      rw [normalEq]
      exact rightNormal.symm
  intro valuation
  exact derivation.sound
    uniqueSeparatorFour_models_connectedComponentFourBasis valuation

/-- Equal ordered `S4_70` components imply equal global support. -/
theorem sameSupport_of_sameComponents
    {left right : Word Nat}
    (components :
      connectedComponentSignaturesWord left =
        connectedComponentSignaturesWord right) :
    SemigroupBasis.CoRoots.S5_441Invariant.SameSupport left right :=
  SemigroupBasis.CoRoots.S5_441Invariant.sameSupport_of_uniqueSeparatorFour_equalEval
    left right
    (uniqueSeparatorFour_equalEval_of_sameComponents components)

/-- Equal ordered `S4_70` components imply the complete `S4_69` exact-cut
signature, including the support on both sides of every unique separator. -/
theorem sameExactCutSignature_of_sameComponents
    {left right : Word Nat}
    (components :
      connectedComponentSignaturesWord left =
        connectedComponentSignaturesWord right) :
    SemigroupBasis.CoRoots.S5_441Invariant.SameExactCutSignature
      left right :=
  SemigroupBasis.CoRoots.S5_441Invariant.sameExactCutSignature_of_uniqueSeparatorFour_equalEval
    left right
    (uniqueSeparatorFour_equalEval_of_sameComponents components)

/-- The semantic data actually consumed at a bare successor: the component
chain fixes and pairs the exact cut, while the H92 barrier detector fixes the
literal final of its nonempty predecessor. -/
structure SameBareSuccessorData
    (left right : Word Nat) : Prop where
  support :
    SemigroupBasis.CoRoots.S5_441Invariant.SameSupport left right
  exactCuts :
    SemigroupBasis.CoRoots.S5_441Invariant.SameExactCutSignature
      left right
  predecessorFinals : SamePredecessorFinals left right

/-- Extract the paired bare-successor data from the H92 descriptor. -/
theorem sameBareSuccessorData_of_descriptor
    {left right : Word Nat}
    (same : SameH92PlainConditionalFinals left right) :
    SameBareSuccessorData left right :=
  ⟨sameSupport_of_sameComponents same.components,
    sameExactCutSignature_of_sameComponents same.components,
    same.predecessorFinals⟩

/-- Concrete form of the bridge used by the chain induction.  A nonempty
predecessor ending at a bare successor in `source` has a paired exact cut in
`target`, with equal side supports and equal literal predecessor final. -/
theorem exists_pairedBareSuccessorExactCut
    {source target : Word Nat}
    (same : SameH92PlainConditionalFinals source target)
    {sourceBefore sourceAfter : List Nat} {separator : Nat}
    (sourceCut :
      UniqueSeparatorFourExactCut
        source.toList sourceBefore separator sourceAfter)
    (sourceBeforeNonempty : sourceBefore ≠ []) :
    ∃ targetBefore targetAfter,
      UniqueSeparatorFourExactCut
          target.toList targetBefore separator targetAfter ∧
        (∀ letter,
          letter ∈ sourceBefore ↔ letter ∈ targetBefore) ∧
        (∀ letter,
          letter ∈ sourceAfter ↔ letter ∈ targetAfter) ∧
        targetBefore ≠ [] ∧
        SemigroupBasis.CoRoots.S5_804.componentFinal sourceBefore =
          SemigroupBasis.CoRoots.S5_804.componentFinal targetBefore := by
  exact exists_matchingPredecessorFinalCut
    (sameExactCutSignature_of_sameComponents same.components)
    same.predecessorFinals sourceCut sourceBeforeNonempty

/-! ## Bare and square-capable component signatures -/

/-- The component signature singled out as bare by the candidate
square-exposure interface. -/
def BareComponentSignature
    (signature : connectedComponentSignature) : Prop :=
  ∃ letter, signature = ⟨[letter], false⟩

/-- A nonempty component has a bare signature exactly when it is literally
one letter. -/
theorem bareComponentSignature_iff
    {component : List Nat} (componentNonempty : component ≠ []) :
    BareComponentSignature
        (connectedComponentSignatureOfList component) ↔
      ∃ letter, component = [letter] := by
  constructor
  · rintro ⟨letter, signatureEq⟩
    have supportEq :
        connectedComponentSortedSupport component = [letter] := by
      have projected :=
        congrArg connectedComponentSignature.support signatureEq
      simpa only [connectedComponentSignatureOfList_support] using
        projected
    have repeatedFalse :
        (connectedComponentSignatureOfList component).repeatedUnary =
          false :=
      congrArg connectedComponentSignature.repeatedUnary signatureEq
    have lengthOne : component.length = 1 := by
      unfold connectedComponentSignatureOfList at repeatedFalse
      rw [supportEq] at repeatedFalse
      simp only at repeatedFalse
      by_cases equal : component.length = 1
      · exact equal
      · exact False.elim
          ((of_decide_eq_false repeatedFalse) equal)
    rcases component with _ | ⟨head, tail⟩
    · exact False.elim (componentNonempty rfl)
    · rcases tail with _ | ⟨next, rest⟩
      · exact ⟨head, rfl⟩
      · simp at lengthOne
  · rintro ⟨letter, rfl⟩
    refine ⟨letter, ?_⟩
    simp [connectedComponentSignatureOfList,
      connectedComponentSortedSupport,
      connectedComponentDistinctSupport]

/-! ## Frozen local moves and the exact residual obligations -/

private abbrev h92Environment :=
  Order6LeeA2LatticeNodesSingletonNormal.S6_7982.squareFinalEraseEnvironment

private theorem h92PilotLawDerives :
    ∀ identity ∈
        Generated.Order6LeeA2LatticeNodes.SystemHebf52dbf4ddc.basis,
      Derives
        Order6LeeA2LatticeNodesSingletonNormal.S6_7982.laws
        identity.lhs identity.rhs :=
  pilotLawDerives h92Environment.toInitialSwitchLawEnvironment

/-- Exact component data can already be changed behind a nonempty guard.
This is the frozen pilot component switch, transported into the H92 laws. -/
theorem derivesExactComponentBehindGuard
    (guard suffix : Word Nat)
    {chead dhead : Nat} {ctail dtail : List Nat}
    (cConnected :
      ConnectedComponentSupportConnected (chead :: ctail))
    (dConnected :
      ConnectedComponentSupportConnected (dhead :: dtail))
    (signature :
      SemigroupBasis.CoRoots.S5_804.connectedCutComponentSignatureOfList
          (chead :: ctail) =
        SemigroupBasis.CoRoots.S5_804.connectedCutComponentSignatureOfList
          (dhead :: dtail)) :
    Derives
      Order6LeeA2LatticeNodesSingletonNormal.S6_7982.laws
      ((guard ++ maximalFactorWord (chead :: ctail)) ++ suffix)
      ((guard ++ maximalFactorWord (dhead :: dtail)) ++ suffix) := by
  have pilot :=
    Order6LeeA2LatticeNodesNormal.derivesComponentSwitchWords
      Order6LeeA2LatticeNodesNormal.trioEnvironment guard
      cConnected dConnected signature
  have transported := pilot.transport h92PilotLawDerives
  exact Derives.appendRight transported suffix

/-- Without a guard, exact component data can already be changed when the
literal component heads agree. -/
theorem derivesExactFirstComponentOfSameHead
    (suffix : Word Nat)
    {chead dhead : Nat} {ctail dtail : List Nat}
    (cConnected :
      ConnectedComponentSupportConnected (chead :: ctail))
    (dConnected :
      ConnectedComponentSupportConnected (dhead :: dtail))
    (signature :
      SemigroupBasis.CoRoots.S5_804.connectedCutComponentSignatureOfList
          (chead :: ctail) =
        SemigroupBasis.CoRoots.S5_804.connectedCutComponentSignatureOfList
          (dhead :: dtail))
    (heads : chead = dhead) :
    Derives
      Order6LeeA2LatticeNodesSingletonNormal.S6_7982.laws
      (maximalFactorWord (chead :: ctail) ++ suffix)
      (maximalFactorWord (dhead :: dtail) ++ suffix) := by
  have pilot :=
    Order6LeeA2LatticeNodesNormal.derivesComponentWords
      Order6LeeA2LatticeNodesNormal.trioEnvironment
      cConnected dConnected signature heads
  exact Derives.appendRight
    (pilot.transport h92PilotLawDerives) suffix

/-- The literal H92 square-final move, restated at the component-induction
boundary. -/
theorem derivesSquareFinalEraseAtBoundary
    (leftContext X Y H suffix : Word Nat) :
    Derives
      Order6LeeA2LatticeNodesSingletonNormal.S6_7982.laws
      (leftContext ++ X ++ X ++ Y ++ Y ++ X ++ X ++ Y ++ Y ++
        H ++ H ++ suffix)
      (leftContext ++ X ++ X ++ Y ++ Y ++ X ++ X ++
        H ++ H ++ suffix) :=
  derivesSquareFinalEraseInContext
    h92Environment leftContext X Y H suffix

/-- First new local obligation.  The unguarded switch must connect a first
component with fixed exact component data even when its literal head changes.
Unary components are already covered by
`derivesExactFirstComponentOfSameHead`; the residual case has support size at
least two. -/
def FirstComponentSwitchObligation : Prop :=
  ∀ {chead dhead : Nat} {ctail dtail : List Nat},
    ConnectedComponentSupportConnected (chead :: ctail) →
      ConnectedComponentSupportConnected (dhead :: dtail) →
      SemigroupBasis.CoRoots.S5_804.connectedCutComponentSignatureOfList
          (chead :: ctail) =
        SemigroupBasis.CoRoots.S5_804.connectedCutComponentSignatureOfList
          (dhead :: dtail) →
      Derives
        Order6LeeA2LatticeNodesSingletonNormal.S6_7982.laws
        (maximalFactorWord (chead :: ctail))
        (maximalFactorWord (dhead :: dtail))

/-- Second new local obligation.  Every non-bare component must derive to a
word beginning with a square.  The derivation is reversible, so the chain
induction can expose the guard, change the preceding component, and restore
the successor. -/
def SquarePrefixExposureObligation : Prop :=
  ∀ {head : Nat} {tail : List Nat},
    ConnectedComponentSupportConnected (head :: tail) →
      ¬BareComponentSignature
        (connectedComponentSignatureOfList (head :: tail)) →
      ∃ H rest : Word Nat,
        Derives
          Order6LeeA2LatticeNodesSingletonNormal.S6_7982.laws
          (maximalFactorWord (head :: tail))
          (H ++ H ++ rest)

/-- Third candidate local obligation.  Once the following component has
exposed a square, two current components with the same base signature may
differ in both head and final.  The intended construction combines the
initial-switch, guarded pilot-switch, and square-final moves; that
construction is not supplied here. -/
structure SquareInteriorComponentObligation : Prop where
  first :
    ∀ (H rest : Word Nat)
      {chead dhead : Nat} {ctail dtail : List Nat},
      ConnectedComponentSupportConnected (chead :: ctail) →
        ConnectedComponentSupportConnected (dhead :: dtail) →
        connectedComponentSignatureOfList (chead :: ctail) =
          connectedComponentSignatureOfList (dhead :: dtail) →
        Derives
          Order6LeeA2LatticeNodesSingletonNormal.S6_7982.laws
          (maximalFactorWord (chead :: ctail) ++ H ++ H ++ rest)
          (maximalFactorWord (dhead :: dtail) ++ H ++ H ++ rest)
  guarded :
    ∀ (guard H rest : Word Nat)
      {chead dhead : Nat} {ctail dtail : List Nat},
      ConnectedComponentSupportConnected (chead :: ctail) →
        ConnectedComponentSupportConnected (dhead :: dtail) →
        connectedComponentSignatureOfList (chead :: ctail) =
          connectedComponentSignatureOfList (dhead :: dtail) →
        Derives
          Order6LeeA2LatticeNodesSingletonNormal.S6_7982.laws
          ((guard ++ maximalFactorWord (chead :: ctail)) ++
            H ++ H ++ rest)
          ((guard ++ maximalFactorWord (dhead :: dtail)) ++
            H ++ H ++ rest)

/-! ## Completeness-equivalent assembly boundary -/

/-- A chain-assembly interface carrying the exact-cut coordinate extracted by
the semantic bridge.  The coordinate is convenient for a future recursive
proof, but no theorem below constructs this interface from the three
candidate local obligations.  As currently stated it is equivalent in
strength to the original H92 derivational-completeness obligation. -/
def SquareGuardedChainAssembly : Prop :=
  ∀ {left right : Word Nat},
    connectedComponentSignaturesWord left =
        connectedComponentSignaturesWord right →
      SameBareSuccessorData left right →
      SemigroupBasis.CoRoots.S5_806.componentFinal left.toList =
        SemigroupBasis.CoRoots.S5_806.componentFinal right.toList →
      Derives
        Order6LeeA2LatticeNodesSingletonNormal.S6_7982.laws
        left right

/-- The completeness-equivalent assembly interface implies the named H92
derivational obligation.  This is a fail-closed conditional wrapper, not a
proof that the three candidate local moves suffice. -/
theorem derivationalCompleteness_of_squareGuardedChainAssembly
    (assembly : SquareGuardedChainAssembly) :
    Order6LeeA2LatticeNodesSingletonNormal.S6_7982.DerivationalCompleteness := by
  intro left right same
  exact assembly same.components
    (sameBareSuccessorData_of_descriptor same) same.final

end SemigroupBasis.CoRoots.Order6LeeA2LatticeNodesH92
