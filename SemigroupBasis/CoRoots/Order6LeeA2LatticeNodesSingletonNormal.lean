import SemigroupBasis.CoRoots.Order6LeeA2LatticeNodesNormal
import SemigroupBasis.CoRoots.Order6LeeA2LatticeNodesBarrierFinal

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6LeeA2LatticeNodesSingletonNormal

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.Order6LeeA2LatticeNodesBarrierFinal

/-!
# Shared source boundary for the two singleton Lee-A2 systems

`SystemH9c7bd9460597` and `SystemH92e6c7c087f0` share the four-law
Lee-A2 scaffold and the unguarded initial switch

`X²Y²X²Y² = Y²X²Y²`.

The first system adds unguarded collapse and retains the final letter of
every coalesced block.  The second keeps the plain connected-component
chain, erasing an interior final only before a square successor.  This file
provides their shared primitive derivations, necessary semantic descriptors,
and the conditional endpoint boundary. The two descriptor-completeness
inductions remain separate named obligations.
-/

/-! ## Shared initial-switch derivations -/

/-- The unguarded switch shared by the two singleton systems:
`x²y²x²y² = y²x²y²`. -/
def initialSwitchLaw : Identity Nat :=
  ⟨⟨0, [0, 1, 1, 0, 0, 1, 1]⟩,
    ⟨1, [1, 0, 0, 1, 1]⟩⟩

/-- The four frozen Lee-A2 scaffold laws together with the unguarded
initial switch. -/
structure InitialSwitchLawEnvironment
    (laws : List (Identity Nat)) : Prop where
  power :
    Order6LeeA2LatticeScaffold.powerContractionLaw ∈ laws
  sandwich :
    Order6LeeA2LatticeScaffold.sandwichContractionLaw ∈ laws
  graph :
    Order6LeeA2LatticeScaffold.graphSwitchLaw ∈ laws
  middle :
    Order6LeeA2LatticeScaffold.middleContractionLaw ∈ laws
  initialSwitch : initialSwitchLaw ∈ laws

private def instantiateInitialSwitch
    (X Y : Word Nat) : Nat → Word Nat
  | 0 => X
  | 1 => Y
  | n + 2 => Word.singleton (n + 2)

/-- Substitute arbitrary nonempty words into the initial switch. -/
theorem derivesInitialSwitch
    {laws : List (Identity Nat)}
    (env : InitialSwitchLawEnvironment laws)
    (X Y : Word Nat) :
    Derives laws
      (X ++ X ++ Y ++ Y ++ X ++ X ++ Y ++ Y)
      (Y ++ Y ++ X ++ X ++ Y ++ Y) := by
  have base :
      Derives laws initialSwitchLaw.lhs initialSwitchLaw.rhs :=
    Derives.fromBasis env.initialSwitch
  have substituted :=
    Derives.subst base (instantiateInitialSwitch X Y)
  simpa [initialSwitchLaw, instantiateInitialSwitch, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- The initial switch under an arbitrary nonempty left context. -/
theorem derivesGuardedInitialSwitch
    {laws : List (Identity Nat)}
    (env : InitialSwitchLawEnvironment laws)
    (leftContext X Y : Word Nat) :
    Derives laws
      (leftContext ++ X ++ X ++ Y ++ Y ++ X ++ X ++ Y ++ Y)
      (leftContext ++ Y ++ Y ++ X ++ X ++ Y ++ Y) := by
  have prefixed :=
    Derives.prepend leftContext (derivesInitialSwitch env X Y)
  simpa [Word.append_assoc] using prefixed

/-- Every law in the frozen pilot basis derives from an initial-switch
environment.  The pilot's guarded switch is obtained by prefixing the
unguarded switch. -/
theorem pilotLawDerives
    {laws : List (Identity Nat)}
    (env : InitialSwitchLawEnvironment laws) :
    ∀ identity ∈
        Generated.Order6LeeA2LatticeNodes.SystemHebf52dbf4ddc.basis,
      Derives laws identity.lhs identity.rhs := by
  intro identity member
  simp only [
    Generated.Order6LeeA2LatticeNodes.SystemHebf52dbf4ddc.basis,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact Derives.fromBasis env.power
  · exact Derives.fromBasis env.sandwich
  · exact Derives.fromBasis env.graph
  · exact Derives.fromBasis env.middle
  · have switched :=
      derivesGuardedInitialSwitch env
        (Word.singleton 0) (Word.singleton 1) (Word.singleton 2)
    simpa [
      Generated.Order6LeeA2LatticeNodes.SystemHebf52dbf4ddc.law4,
      Order6LeeA2LatticeNodesNormal.guardedSwitchLaw,
      initialSwitchLaw, Word.singleton, Word.append,
      Word.append_assoc] using switched

/-- Reuse the frozen pilot normalizer whenever the direct connected-cut
signature and literal head already agree. -/
theorem derivesOfDirectSignatureAndHead
    {laws : List (Identity Nat)}
    (env : InitialSwitchLawEnvironment laws)
    {left right : Word Nat}
    (same :
      Order6LeeA2LatticeNodesNormal.SameDirectSignatureAndHead
        left right) :
    Derives laws left right :=
  (Order6LeeA2LatticeNodesNormal.derivesOfDescriptorEq same).transport
    (pilotLawDerives env)

/-! ## System-specific primitive laws -/

/-- An initial-switch environment with the unguarded collapse carried by
`SystemH9c7bd9460597`. -/
structure InitialCollapseLawEnvironment
    (laws : List (Identity Nat))
    extends InitialSwitchLawEnvironment laws : Prop where
  collapse : Order6LeeA2LatticeNodesNormal.collapseLaw ∈ laws

private def instantiateCollapse
    (X Y : Word Nat) : Nat → Word Nat
  | 0 => X
  | 1 => Y
  | n + 2 => Word.singleton (n + 2)

/-- Word-substituted singleton-system collapse:
`X²Y²X²Y² = X²Y²`. -/
theorem derivesCollapse
    {laws : List (Identity Nat)}
    (env : InitialCollapseLawEnvironment laws)
    (X Y : Word Nat) :
    Derives laws
      (X ++ X ++ Y ++ Y ++ X ++ X ++ Y ++ Y)
      (X ++ X ++ Y ++ Y) := by
  have base :
      Derives laws
        Order6LeeA2LatticeNodesNormal.collapseLaw.lhs
        Order6LeeA2LatticeNodesNormal.collapseLaw.rhs :=
    Derives.fromBasis env.collapse
  have substituted :=
    Derives.subst base (instantiateCollapse X Y)
  simpa [Order6LeeA2LatticeNodesNormal.collapseLaw,
    instantiateCollapse, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Collapse inside an arbitrary two-sided nonempty context. -/
theorem derivesCollapseInContext
    {laws : List (Identity Nat)}
    (env : InitialCollapseLawEnvironment laws)
    (leftContext X Y suffix : Word Nat) :
    Derives laws
      (leftContext ++ X ++ X ++ Y ++ Y ++ X ++ X ++ Y ++ Y ++ suffix)
      (leftContext ++ X ++ X ++ Y ++ Y ++ suffix) := by
  have prefixed :=
    Derives.prepend leftContext (derivesCollapse env X Y)
  have contextual := Derives.appendRight prefixed suffix
  simpa [Word.append_assoc] using contextual

/-- The square-guarded interior-final erasure carried by
`SystemH92e6c7c087f0`:
`x²y²x²y²h² = x²y²x²h²`. -/
def squareFinalEraseLaw : Identity Nat :=
  ⟨⟨0, [0, 1, 1, 0, 0, 1, 1, 2, 2]⟩,
    ⟨0, [0, 1, 1, 0, 0, 2, 2]⟩⟩

/-- An initial-switch environment with square-guarded final erasure. -/
structure SquareFinalEraseLawEnvironment
    (laws : List (Identity Nat))
    extends InitialSwitchLawEnvironment laws : Prop where
  erase : squareFinalEraseLaw ∈ laws

private def instantiateSquareFinalErase
    (X Y H : Word Nat) : Nat → Word Nat
  | 0 => X
  | 1 => Y
  | 2 => H
  | n + 3 => Word.singleton (n + 3)

/-- Substitute arbitrary nonempty words into square-guarded final
erasure. -/
theorem derivesSquareFinalErase
    {laws : List (Identity Nat)}
    (env : SquareFinalEraseLawEnvironment laws)
    (X Y H : Word Nat) :
    Derives laws
      (X ++ X ++ Y ++ Y ++ X ++ X ++ Y ++ Y ++ H ++ H)
      (X ++ X ++ Y ++ Y ++ X ++ X ++ H ++ H) := by
  have base :
      Derives laws squareFinalEraseLaw.lhs squareFinalEraseLaw.rhs :=
    Derives.fromBasis env.erase
  have substituted :=
    Derives.subst base (instantiateSquareFinalErase X Y H)
  simpa [squareFinalEraseLaw, instantiateSquareFinalErase, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- Square-guarded final erasure inside an arbitrary two-sided context. -/
theorem derivesSquareFinalEraseInContext
    {laws : List (Identity Nat)}
    (env : SquareFinalEraseLawEnvironment laws)
    (leftContext X Y H suffix : Word Nat) :
    Derives laws
      (leftContext ++ X ++ X ++ Y ++ Y ++ X ++ X ++ Y ++ Y ++
        H ++ H ++ suffix)
      (leftContext ++ X ++ X ++ Y ++ Y ++ X ++ X ++
        H ++ H ++ suffix) := by
  have prefixed :=
    Derives.prepend leftContext (derivesSquareFinalErase env X Y H)
  have contextual := Derives.appendRight prefixed suffix
  simpa [Word.append_assoc] using contextual

/-! ## Necessary semantic descriptors -/

/-- Candidate system-H9 descriptor: the exact-cut support skeleton gives the
coalesced chain; predecessor finals retain the final of every non-last block,
and the whole-word final retains the last one. An initial bare block is already
identified by its exact cut, while a collapsible initial block has no head
coordinate. -/
structure SameH9CoalescedAllFinals
    (left right : Word Nat) : Prop where
  support :
    SemigroupBasis.CoRoots.S5_441Invariant.SameSupport left right
  exactCuts :
    SemigroupBasis.CoRoots.S5_441Invariant.SameExactCutSignature
      left right
  predecessorFinals : SamePredecessorFinals left right
  final :
    SemigroupBasis.CoRoots.S5_806.componentFinal left.toList =
      SemigroupBasis.CoRoots.S5_806.componentFinal right.toList

/-- Candidate system-H92 descriptor: the ordered S4_70 component data gives
the plain component chain. Predecessor finals retain interior finals before
matching exact cuts, and the whole-word final is retained. Sufficiency still
requires the named derivational obligation below. -/
structure SameH92PlainConditionalFinals
    (left right : Word Nat) : Prop where
  components :
    connectedComponentSignaturesWord left =
      connectedComponentSignaturesWord right
  predecessorFinals : SamePredecessorFinals left right
  final :
    SemigroupBasis.CoRoots.S5_806.componentFinal left.toList =
      SemigroupBasis.CoRoots.S5_806.componentFinal right.toList

/-- Transport an exact cut together with the final letter immediately before
its separator.  This is the exact assembly consumed by the H9 coalesced-chain
induction; the H92 induction uses the same conclusion after locating its bare
successor in the plain component chain. -/
theorem exists_matchingPredecessorFinalCut
    {source target : Word Nat}
    (sameCuts :
      SemigroupBasis.CoRoots.S5_441Invariant.SameExactCutSignature
        source target)
    (sameFinals : SamePredecessorFinals source target)
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
  obtain
    ⟨targetBefore, targetAfter, targetCut,
      targetBeforeSupport, targetAfterSupport⟩ :=
    SemigroupBasis.CoRoots.S5_441Invariant.SameExactCutSignature.transport
      sameCuts sourceCut
  have beforeSupport :
      ∀ letter,
        letter ∈ sourceBefore ↔ letter ∈ targetBefore :=
    fun letter => (targetBeforeSupport letter).symm
  have afterSupport :
      ∀ letter,
        letter ∈ sourceAfter ↔ letter ∈ targetAfter :=
    fun letter => (targetAfterSupport letter).symm
  have targetBeforeNonempty : targetBefore ≠ [] := by
    intro targetEmpty
    obtain ⟨head, tail, sourceShape⟩ :=
      List.exists_cons_of_ne_nil sourceBeforeNonempty
    have sourceMember : head ∈ sourceBefore := by
      rw [sourceShape]
      exact List.Mem.head tail
    have targetMember : head ∈ targetBefore :=
      (beforeSupport head).mp sourceMember
    rw [targetEmpty] at targetMember
    exact List.not_mem_nil targetMember
  have finals :
      SemigroupBasis.CoRoots.S5_804.componentFinal sourceBefore =
        SemigroupBasis.CoRoots.S5_804.componentFinal targetBefore :=
    sameFinals sourceCut targetCut beforeSupport afterSupport
      sourceBeforeNonempty targetBeforeNonempty
  exact
    ⟨targetBefore, targetAfter, targetCut,
      beforeSupport, afterSupport, targetBeforeNonempty, finals⟩

/-- Semantic extraction of the ordered S4_70 component signatures from
validity in the four-element detector. -/
theorem sameBaseComponentSignatures_of_s4_70_valid
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy connectedComponentFour.semigroup) :
    connectedComponentSignaturesWord identity.lhs =
      connectedComponentSignaturesWord identity.rhs := by
  have lhsDerivation :=
    connectedComponentFour_derivesCanonical identity.lhs
  have rhsDerivation :=
    connectedComponentFour_derivesCanonical identity.rhs
  have normalizedEval :
      ∀ valuation : Nat → Fin 4,
        connectedComponentFour.semigroup.eval valuation
            (connectedComponentCanonicalRender identity.lhs) =
          connectedComponentFour.semigroup.eval valuation
            (connectedComponentCanonicalRender identity.rhs) := by
    intro valuation
    have lhsSound :=
      lhsDerivation.sound connectedComponentFourBasis_models valuation
    have rhsSound :=
      rhsDerivation.sound connectedComponentFourBasis_models valuation
    exact lhsSound.symm.trans <| (valid valuation).trans rhsSound
  exact
    connectedComponentCanonical_eq_of_equalEval
      (connectedComponentFourSignaturesWord_canonical identity.lhs)
      (connectedComponentFourSignaturesWord_canonical identity.rhs)
      (connectedComponentCanonicalRender identity.lhs)
      (connectedComponentCanonicalRender identity.rhs)
      (connectedComponentCanonicalRender_toList identity.lhs)
      (connectedComponentCanonicalRender_toList identity.rhs)
      normalizedEval

/-! ## H9 semantic assembly and endpoint boundary -/

namespace S6_7976

abbrev table : FiniteTable :=
  Generated.Order6LeeA2LatticeNodes.S6_7976.table

abbrev laws : List (Identity Nat) :=
  Generated.Order6LeeA2LatticeNodes.SystemH9c7bd9460597.basis

/-- The exact S4_69 separator detector inside S6_7976. -/
def separatorEmbedding :
    Embedding uniqueSeparatorFour.semigroup table.semigroup where
  toFun := fun value =>
    if value.val = 0 then ⟨0, by decide⟩ else
      if value.val = 1 then ⟨2, by decide⟩ else
        if value.val = 2 then ⟨4, by decide⟩ else ⟨5, by decide⟩
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

theorem initialCollapseEnvironment :
    InitialCollapseLawEnvironment laws where
  toInitialSwitchLawEnvironment := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide
  collapse := by decide

/-- Every identity valid in S6_7976 has the necessary H9 singleton
descriptor. -/
theorem sameDescriptor_of_valid
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    SameH9CoalescedAllFinals identity.lhs identity.rhs := by
  have separatorValid :
      identity.SatisfiedBy uniqueSeparatorFour.semigroup :=
    separatorEmbedding.pullback_identity identity valid
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact
      SemigroupBasis.CoRoots.S5_441Invariant.sameSupport_of_uniqueSeparatorFour_valid
        identity separatorValid
  · exact
      SemigroupBasis.CoRoots.S5_441Invariant.sameExactCutSignature_of_uniqueSeparatorFour_valid
        identity separatorValid
  · exact
      samePredecessorFinals_of_valid
        Order6LeeA2LatticeNodesBarrierFinal.S6_7976.marker
        identity valid
  · exact
      Order6LeeA2LatticeNodesNormal.final_eq_of_band_valid
        (G := table.semigroup) (p := (3 : Fin 6)) (q := (4 : Fin 6))
        (by decide) (by decide) (by decide) (by decide) (by decide)
        identity valid

/-- The remaining H9 proof obligation, isolated from the semantic and
endpoint layers. -/
def DerivationalCompleteness : Prop :=
  ∀ {left right : Word Nat},
    SameH9CoalescedAllFinals left right →
      Derives laws left right

/-- Closing the named H9 derivational obligation immediately yields the
representative endpoint. -/
theorem representative_basis_of_derivationalCompleteness
    (complete : DerivationalCompleteness) :
    BasisFor table.semigroup laws := by
  refine
    ⟨Generated.Order6LeeA2LatticeNodes.S6_7976.models, ?_⟩
  intro identity valid
  exact complete (sameDescriptor_of_valid identity valid)

/-- The opposite endpoint follows by the standard reversed-basis transfer. -/
theorem opposite_basis_of_derivationalCompleteness
    (complete : DerivationalCompleteness) :
    BasisFor table.semigroup.opposite (reversedBasis laws) :=
  (representative_basis_of_derivationalCompleteness complete).oppositeReversed

end S6_7976

/-! ## H92 semantic assembly and endpoint boundary -/

namespace S6_7982

abbrev table : FiniteTable :=
  Generated.Order6LeeA2LatticeNodes.S6_7982.table

abbrev laws : List (Identity Nat) :=
  Generated.Order6LeeA2LatticeNodes.SystemH92e6c7c087f0.basis

/-- The exact S4_70 component detector inside S6_7982. -/
def componentEmbedding :
    Embedding connectedComponentFour.semigroup table.semigroup where
  toFun := fun value =>
    if value.val = 0 then ⟨0, by decide⟩ else
      if value.val = 1 then ⟨2, by decide⟩ else
        if value.val = 2 then ⟨4, by decide⟩ else ⟨5, by decide⟩
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

theorem squareFinalEraseEnvironment :
    SquareFinalEraseLawEnvironment laws where
  toInitialSwitchLawEnvironment := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide
  erase := by decide

/-- Every identity valid in S6_7982 has the necessary H92 singleton
descriptor. -/
theorem sameDescriptor_of_valid
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    SameH92PlainConditionalFinals identity.lhs identity.rhs := by
  have componentValid :
      identity.SatisfiedBy connectedComponentFour.semigroup :=
    componentEmbedding.pullback_identity identity valid
  refine ⟨?_, ?_, ?_⟩
  · exact
      sameBaseComponentSignatures_of_s4_70_valid
        identity componentValid
  · exact
      samePredecessorFinals_of_valid
        Order6LeeA2LatticeNodesBarrierFinal.S6_7982.marker
        identity valid
  · exact
      Order6LeeA2LatticeNodesNormal.final_eq_of_band_valid
        (G := table.semigroup) (p := (3 : Fin 6)) (q := (4 : Fin 6))
        (by decide) (by decide) (by decide) (by decide) (by decide)
        identity valid

/-- The remaining H92 proof obligation, isolated from the semantic and
endpoint layers. -/
def DerivationalCompleteness : Prop :=
  ∀ {left right : Word Nat},
    SameH92PlainConditionalFinals left right →
      Derives laws left right

/-- Closing the named H92 derivational obligation immediately yields the
representative endpoint. -/
theorem representative_basis_of_derivationalCompleteness
    (complete : DerivationalCompleteness) :
    BasisFor table.semigroup laws := by
  refine
    ⟨Generated.Order6LeeA2LatticeNodes.S6_7982.models, ?_⟩
  intro identity valid
  exact complete (sameDescriptor_of_valid identity valid)

/-- The opposite endpoint follows by the standard reversed-basis transfer. -/
theorem opposite_basis_of_derivationalCompleteness
    (complete : DerivationalCompleteness) :
    BasisFor table.semigroup.opposite (reversedBasis laws) :=
  (representative_basis_of_derivationalCompleteness complete).oppositeReversed

end S6_7982

end SemigroupBasis.CoRoots.Order6LeeA2LatticeNodesSingletonNormal
