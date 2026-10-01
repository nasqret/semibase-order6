import SemigroupBasis.CoRoots.Order6FactorPairS2S5348Prelude
import SemigroupBasis.CoRoots.Order6FactorPairS2S5381Normal

namespace SemigroupBasis.CoRoots.Order6FactorPairS2S5348ReversalBridge

open SemigroupBasis

private abbrev w := Order6FactorPairS2S5348.w

private def instantiateThreeWords
    (u v z : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => z
  | n + 3 => Word.singleton (n + 3)

/-! ## Source-law substitution instances -/

private theorem derivesPowerExpansion (u : Word Nat) :
    Derives Order6FactorPairS2S5348.basis
      (u ++ u)
      (((u ++ u) ++ u) ++ u) := by
  have source :
      Derives Order6FactorPairS2S5348.basis
        (w 0 [0])
        (w 0 [0, 0, 0]) :=
    Derives.fromBasis
      (e := Identity.mk (w 0 [0]) (w 0 [0, 0, 0])) <| by
        simp [w, Order6FactorPairS2S5348.w,
          Order6FactorPairS2S5348.basis]
  have substituted :=
    Derives.subst source (instantiateThreeWords u u u)
  simpa [w, Order6FactorPairS2S5348.w, instantiateThreeWords,
    Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

private theorem derivesEndpointTransfer (u v : Word Nat) :
    Derives Order6FactorPairS2S5348.basis
      (((u ++ u) ++ v) ++ u)
      ((u ++ v) ++ (u ++ u)) := by
  have source :
      Derives Order6FactorPairS2S5348.basis
        (w 0 [0, 1, 0])
        (w 0 [1, 0, 0]) :=
    Derives.fromBasis
      (e := Identity.mk (w 0 [0, 1, 0]) (w 0 [1, 0, 0])) <| by
        simp [w, Order6FactorPairS2S5348.w,
          Order6FactorPairS2S5348.basis]
  have substituted :=
    Derives.subst source (instantiateThreeWords u v v)
  simpa [w, Order6FactorPairS2S5348.w, instantiateThreeWords,
    Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

private theorem derivesSplitEndpointContraction (u v : Word Nat) :
    Derives Order6FactorPairS2S5348.basis
      ((((u ++ u) ++ v) ++ u) ++ u)
      ((u ++ v) ++ u) := by
  have source :
      Derives Order6FactorPairS2S5348.basis
        (w 0 [0, 1, 0, 0])
        (w 0 [1, 0]) :=
    Derives.fromBasis
      (e := Identity.mk (w 0 [0, 1, 0, 0]) (w 0 [1, 0])) <| by
        simp [w, Order6FactorPairS2S5348.w,
          Order6FactorPairS2S5348.basis]
  have substituted :=
    Derives.subst source (instantiateThreeWords u v v)
  simpa [w, Order6FactorPairS2S5348.w, instantiateThreeWords,
    Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

private theorem derivesSquareInterleave (u v : Word Nat) :
    Derives Order6FactorPairS2S5348.basis
      ((u ++ u) ++ (v ++ v))
      ((u ++ v) ++ (u ++ v)) := by
  have source :
      Derives Order6FactorPairS2S5348.basis
        (w 0 [0, 1, 1])
        (w 0 [1, 0, 1]) :=
    Derives.fromBasis
      (e := Identity.mk (w 0 [0, 1, 1]) (w 0 [1, 0, 1])) <| by
        simp [w, Order6FactorPairS2S5348.w,
          Order6FactorPairS2S5348.basis]
  have substituted :=
    Derives.subst source (instantiateThreeWords u v v)
  simpa [w, Order6FactorPairS2S5348.w, instantiateThreeWords,
    Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

private theorem derivesSquareFinalSwitch (u v : Word Nat) :
    Derives Order6FactorPairS2S5348.basis
      ((u ++ u) ++ (v ++ v))
      (((u ++ v) ++ v) ++ u) := by
  have source :
      Derives Order6FactorPairS2S5348.basis
        (w 0 [0, 1, 1])
        (w 0 [1, 1, 0]) :=
    Derives.fromBasis
      (e := Identity.mk (w 0 [0, 1, 1]) (w 0 [1, 1, 0])) <| by
        simp [w, Order6FactorPairS2S5348.w,
          Order6FactorPairS2S5348.basis]
  have substituted :=
    Derives.subst source (instantiateThreeWords u v v)
  simpa [w, Order6FactorPairS2S5348.w, instantiateThreeWords,
    Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

private theorem derivesSquareInitialSwitch (u v : Word Nat) :
    Derives Order6FactorPairS2S5348.basis
      ((u ++ u) ++ (v ++ v))
      (((v ++ u) ++ u) ++ v) := by
  have source :
      Derives Order6FactorPairS2S5348.basis
        (w 0 [0, 1, 1])
        (w 1 [0, 0, 1]) :=
    Derives.fromBasis
      (e := Identity.mk (w 0 [0, 1, 1]) (w 1 [0, 0, 1])) <| by
        simp [w, Order6FactorPairS2S5348.w,
          Order6FactorPairS2S5348.basis]
  have substituted :=
    Derives.subst source (instantiateThreeWords u v v)
  simpa [w, Order6FactorPairS2S5348.w, instantiateThreeWords,
    Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

private theorem derivesAttachmentFinalSwitch
    (u v z : Word Nat) :
    Derives Order6FactorPairS2S5348.basis
      ((((u ++ u) ++ v) ++ z) ++ v)
      ((((u ++ v) ++ v) ++ z) ++ u) := by
  have source :
      Derives Order6FactorPairS2S5348.basis
        (w 0 [0, 1, 2, 1])
        (w 0 [1, 1, 2, 0]) :=
    Derives.fromBasis
      (e := Identity.mk
        (w 0 [0, 1, 2, 1])
        (w 0 [1, 1, 2, 0])) <| by
          simp [w, Order6FactorPairS2S5348.w,
            Order6FactorPairS2S5348.basis]
  have substituted :=
    Derives.subst source (instantiateThreeWords u v z)
  simpa [w, Order6FactorPairS2S5348.w, instantiateThreeWords,
    Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

private theorem derivesAttachmentInitialSwitch
    (u v z : Word Nat) :
    Derives Order6FactorPairS2S5348.basis
      ((((u ++ u) ++ v) ++ z) ++ v)
      ((((v ++ u) ++ u) ++ z) ++ v) := by
  have source :
      Derives Order6FactorPairS2S5348.basis
        (w 0 [0, 1, 2, 1])
        (w 1 [0, 0, 2, 1]) :=
    Derives.fromBasis
      (e := Identity.mk
        (w 0 [0, 1, 2, 1])
        (w 1 [0, 0, 2, 1])) <| by
          simp [w, Order6FactorPairS2S5348.w,
            Order6FactorPairS2S5348.basis]
  have substituted :=
    Derives.subst source (instantiateThreeWords u v z)
  simpa [w, Order6FactorPairS2S5348.w, instantiateThreeWords,
    Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

private theorem derivesHeadSquareRotation
    (head middle square : Word Nat) :
    Derives Order6FactorPairS2S5348.basis
      ((((head ++ head) ++ middle) ++ square) ++ square)
      ((((head ++ middle) ++ square) ++ square) ++ head) := by
  have source :
      Derives Order6FactorPairS2S5348.basis
        (w 0 [0, 1, 2, 2])
        (w 0 [1, 2, 2, 0]) :=
    Derives.fromBasis
      (e := Identity.mk
        (w 0 [0, 1, 2, 2])
        (w 0 [1, 2, 2, 0])) <| by
          simp [w, Order6FactorPairS2S5348.w,
            Order6FactorPairS2S5348.basis]
  have substituted :=
    Derives.subst source
      (instantiateThreeWords head middle square)
  simpa [w, Order6FactorPairS2S5348.w, instantiateThreeWords,
    Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

private theorem derivesRightTripleExpansion (u v : Word Nat) :
    Derives Order6FactorPairS2S5348.basis
      ((u ++ v) ++ u)
      ((((u ++ v) ++ u) ++ u) ++ u) := by
  have source :
      Derives Order6FactorPairS2S5348.basis
        (w 0 [1, 0])
        (w 0 [1, 0, 0, 0]) :=
    Derives.fromBasis
      (e := Identity.mk (w 0 [1, 0]) (w 0 [1, 0, 0, 0])) <| by
        simp [w, Order6FactorPairS2S5348.w,
          Order6FactorPairS2S5348.basis]
  have substituted :=
    Derives.subst source (instantiateThreeWords u v v)
  simpa [w, Order6FactorPairS2S5348.w, instantiateThreeWords,
    Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-! ## Literal reversal of the `S2_2 x S5_381` basis -/

def reversedPowerLaw : Identity Nat :=
  Identity.mk (w 0 [0]) (w 0 [0, 0, 0])

def reversedTripleLeftContractionLaw : Identity Nat :=
  Identity.mk (w 0 [1, 0, 0, 0]) (w 0 [1, 0])

def reversedTripleHeadSwitchLaw : Identity Nat :=
  Identity.mk (w 1 [1, 0, 0, 0]) (w 1 [0, 0, 0, 1])

def reversedEndpointTransferLaw : Identity Nat :=
  Identity.mk (w 0 [1, 0, 0]) (w 0 [0, 1, 0])

def reversedSplitEndpointContractionLaw : Identity Nat :=
  Identity.mk (w 0 [0, 1, 0, 0]) (w 0 [1, 0])

def reversedSquareInterleaveLaw : Identity Nat :=
  Identity.mk (w 1 [1, 0, 0]) (w 1 [0, 1, 0])

def reversedSquareFinalSwitchLaw : Identity Nat :=
  Identity.mk (w 1 [1, 0, 0]) (w 0 [1, 1, 0])

def reversedSquareInitialSwitchLaw : Identity Nat :=
  Identity.mk (w 1 [1, 0, 0]) (w 1 [0, 0, 1])

def reversedAttachmentYXXZYLaw : Identity Nat :=
  Identity.mk (w 1 [2, 1, 0, 0]) (w 1 [2, 0, 0, 1])

def reversedRightTripleExpansionLaw : Identity Nat :=
  Identity.mk (w 0 [1, 0]) (w 0 [0, 0, 1, 0])

def reversedHeadSquareRotationLaw : Identity Nat :=
  Identity.mk (w 2 [2, 0, 1, 0]) (w 0 [2, 2, 1, 0])

def reversedHeadSquareTransferLaw : Identity Nat :=
  Identity.mk (w 2 [2, 0, 1, 0]) (w 2 [0, 1, 0, 2])

def reversedPrefixedGatherLaw : Identity Nat :=
  Identity.mk (w 1 [2, 1, 0]) (w 1 [1, 2, 0])

def bridgeBasis : List (Identity Nat) :=
  [ reversedPowerLaw,
    reversedTripleLeftContractionLaw,
    reversedTripleHeadSwitchLaw,
    reversedEndpointTransferLaw,
    reversedSplitEndpointContractionLaw,
    reversedSquareInterleaveLaw,
    reversedSquareFinalSwitchLaw,
    reversedSquareInitialSwitchLaw,
    reversedAttachmentYXXZYLaw,
    reversedRightTripleExpansionLaw,
    reversedHeadSquareRotationLaw,
    reversedHeadSquareTransferLaw,
    reversedPrefixedGatherLaw ]

theorem reversedS2S5381Basis_eq_bridge :
    reversedBasis Order6FactorPairS2S5381.basis = bridgeBasis := by
  decide

/-! ## The thirteen source derivations -/

private theorem derivesReversedPowerLaw :
    Derives Order6FactorPairS2S5348.basis
      reversedPowerLaw.lhs reversedPowerLaw.rhs := by
  simpa [reversedPowerLaw, w, Word.singleton, Word.append] using
    derivesPowerExpansion (Word.singleton 0)

private theorem derivesReversedTripleLeftContractionLaw :
    Derives Order6FactorPairS2S5348.basis
      reversedTripleLeftContractionLaw.lhs
      reversedTripleLeftContractionLaw.rhs := by
  simpa [reversedTripleLeftContractionLaw, w,
    Word.singleton, Word.append] using
      (derivesRightTripleExpansion
        (Word.singleton 0) (Word.singleton 1)).symm

private theorem derivesReversedTripleHeadSwitchLaw :
    Derives Order6FactorPairS2S5348.basis
      reversedTripleHeadSwitchLaw.lhs
      reversedTripleHeadSwitchLaw.rhs := by
  simpa [reversedTripleHeadSwitchLaw, w,
    Word.singleton, Word.append] using
      derivesAttachmentFinalSwitch
        (Word.singleton 1) (Word.singleton 0) (Word.singleton 0)

private theorem derivesReversedEndpointTransferLaw :
    Derives Order6FactorPairS2S5348.basis
      reversedEndpointTransferLaw.lhs
      reversedEndpointTransferLaw.rhs := by
  simpa [reversedEndpointTransferLaw, w,
    Word.singleton, Word.append] using
      (derivesEndpointTransfer
        (Word.singleton 0) (Word.singleton 1)).symm

private theorem derivesReversedSplitEndpointContractionLaw :
    Derives Order6FactorPairS2S5348.basis
      reversedSplitEndpointContractionLaw.lhs
      reversedSplitEndpointContractionLaw.rhs := by
  simpa [reversedSplitEndpointContractionLaw, w,
    Word.singleton, Word.append] using
      derivesSplitEndpointContraction
        (Word.singleton 0) (Word.singleton 1)

private theorem derivesReversedSquareInterleaveLaw :
    Derives Order6FactorPairS2S5348.basis
      reversedSquareInterleaveLaw.lhs
      reversedSquareInterleaveLaw.rhs := by
  simpa [reversedSquareInterleaveLaw, w,
    Word.singleton, Word.append] using
      derivesSquareInterleave
        (Word.singleton 1) (Word.singleton 0)

private theorem derivesReversedSquareFinalSwitchLaw :
    Derives Order6FactorPairS2S5348.basis
      reversedSquareFinalSwitchLaw.lhs
      reversedSquareFinalSwitchLaw.rhs := by
  simpa [reversedSquareFinalSwitchLaw, w,
    Word.singleton, Word.append] using
      derivesSquareInitialSwitch
        (Word.singleton 1) (Word.singleton 0)

private theorem derivesReversedSquareInitialSwitchLaw :
    Derives Order6FactorPairS2S5348.basis
      reversedSquareInitialSwitchLaw.lhs
      reversedSquareInitialSwitchLaw.rhs := by
  simpa [reversedSquareInitialSwitchLaw, w,
    Word.singleton, Word.append] using
      derivesSquareFinalSwitch
        (Word.singleton 1) (Word.singleton 0)

private theorem derivesReversedAttachmentYXXZYLaw :
    Derives Order6FactorPairS2S5348.basis
      reversedAttachmentYXXZYLaw.lhs
      reversedAttachmentYXXZYLaw.rhs := by
  have gatherBackward :
      Derives Order6FactorPairS2S5348.basis
        (w 1 [2, 1, 0, 0])
        (w 1 [1, 2, 0, 0]) := by
    have gathered :=
      Derives.appendRight
        (Order6FactorPairS2S5348.derivesFirstGapGather
          (Word.singleton 1)
          (Word.singleton 2)
          (Word.singleton 0)).symm
        (Word.singleton 0)
    simpa [w, Order6FactorPairS2S5348.w, Word.singleton,
      Word.append] using gathered
  have rotate :
      Derives Order6FactorPairS2S5348.basis
        (w 1 [1, 2, 0, 0])
        (w 1 [2, 0, 0, 1]) := by
    simpa [w, Order6FactorPairS2S5348.w, Word.singleton,
      Word.append] using
      derivesHeadSquareRotation
        (Word.singleton 1)
        (Word.singleton 2)
        (Word.singleton 0)
  simpa [reversedAttachmentYXXZYLaw] using
    gatherBackward.trans rotate

private theorem derivesReversedRightTripleExpansionLaw :
    Derives Order6FactorPairS2S5348.basis
      reversedRightTripleExpansionLaw.lhs
      reversedRightTripleExpansionLaw.rhs := by
  simpa [reversedRightTripleExpansionLaw, w,
    Word.singleton, Word.append] using
      (Order6FactorPairS2S5348.derivesTriplePrefixPairDeletion
        (Word.singleton 0) (Word.singleton 1)).symm

private theorem derivesReversedHeadSquareRotationLaw :
    Derives Order6FactorPairS2S5348.basis
      reversedHeadSquareRotationLaw.lhs
      reversedHeadSquareRotationLaw.rhs := by
  simpa [reversedHeadSquareRotationLaw, w,
    Word.singleton, Word.append] using
      derivesAttachmentInitialSwitch
        (Word.singleton 2)
        (Word.singleton 0)
        (Word.singleton 1)

private theorem derivesReversedHeadSquareTransferLaw :
    Derives Order6FactorPairS2S5348.basis
      reversedHeadSquareTransferLaw.lhs
      reversedHeadSquareTransferLaw.rhs := by
  have switch :
      Derives Order6FactorPairS2S5348.basis
        (w 2 [2, 0, 1, 0])
        (w 2 [0, 0, 1, 2]) := by
    simpa [w, Order6FactorPairS2S5348.w, Word.singleton,
      Word.append] using
      derivesAttachmentFinalSwitch
        (Word.singleton 2)
        (Word.singleton 0)
        (Word.singleton 1)
  have gather :
      Derives Order6FactorPairS2S5348.basis
        (w 2 [0, 0, 1, 2])
        (w 2 [0, 1, 0, 2]) := by
    have prefixed :=
      Derives.prepend (Word.singleton 2)
        (Order6FactorPairS2S5348.derivesFirstGapGather
          (Word.singleton 0)
          (Word.singleton 1)
          (Word.singleton 2))
    simpa [w, Order6FactorPairS2S5348.w, Word.singleton,
      Word.append] using prefixed
  simpa [reversedHeadSquareTransferLaw] using
    switch.trans gather

private theorem derivesReversedPrefixedGatherLaw :
    Derives Order6FactorPairS2S5348.basis
      reversedPrefixedGatherLaw.lhs
      reversedPrefixedGatherLaw.rhs := by
  simpa [reversedPrefixedGatherLaw, w,
    Word.singleton, Word.append] using
      (Order6FactorPairS2S5348.derivesFirstGapGather
        (Word.singleton 1)
        (Word.singleton 2)
        (Word.singleton 0)).symm

/-- Every axiom in the literal reversal of the complete
`S2_2 x S5_381` basis is derivable from the candidate
`S2_2 x S5_348` basis. -/
theorem reversedS2S5381AxiomDerives :
    (identity : Identity Nat) →
      identity ∈ reversedBasis Order6FactorPairS2S5381.basis →
        Derives Order6FactorPairS2S5348.basis
          identity.lhs identity.rhs := by
  intro identity member
  rw [reversedS2S5381Basis_eq_bridge] at member
  simp only [bridgeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at member
  rcases member with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  · exact derivesReversedPowerLaw
  · exact derivesReversedTripleLeftContractionLaw
  · exact derivesReversedTripleHeadSwitchLaw
  · exact derivesReversedEndpointTransferLaw
  · exact derivesReversedSplitEndpointContractionLaw
  · exact derivesReversedSquareInterleaveLaw
  · exact derivesReversedSquareFinalSwitchLaw
  · exact derivesReversedSquareInitialSwitchLaw
  · exact derivesReversedAttachmentYXXZYLaw
  · exact derivesReversedRightTripleExpansionLaw
  · exact derivesReversedHeadSquareRotationLaw
  · exact derivesReversedHeadSquareTransferLaw
  · exact derivesReversedPrefixedGatherLaw

/-- Replace a derivation from the reversed `S2_2 x S5_381` axioms by a
derivation from the `S2_2 x S5_348` candidate. -/
theorem transportReversedS2S5381Derivation
    {left right : Word Nat}
    (derivation :
      Derives (reversedBasis Order6FactorPairS2S5381.basis)
        left right) :
    Derives Order6FactorPairS2S5348.basis left right :=
  derivation.transport reversedS2S5381AxiomDerives

end SemigroupBasis.CoRoots.Order6FactorPairS2S5348ReversalBridge
