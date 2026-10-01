import SemigroupBasis.CoRoots.Order6FactorPairS2S5378Prelude
import SemigroupBasis.CoRoots.Order6LeeZhangCondition7Completeness
import SemigroupBasis.CoRoots.S5_441ParityEnvelopeComponents
import SemigroupBasis.CoRoots.S5_441ParityEnvelopeMerge
import SemigroupBasis.Examples.CyclicTwo
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Subdirect

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6FactorPairS2S5378

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.Order6LeeZhangAmbientConditions

/-!
This module proves unrestricted completeness of the fourteen-law
`S2_2 x S5_378` candidate basis. The two factors force:

* the support, exact unique-separator cuts, and globally simple variables
  supplied by `S5_378`;
* the parity of every variable multiplicity supplied by `S2_2`.

The proof transports the threshold-parity connected-component theorem,
normalizes exact-cut-free gaps to closed envelopes, and assembles aligned
gaps under arbitrary exact-cut contexts.
-/

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  Word.mk head tail

def xx : Word Nat := w 0 [0]
def xxxx : Word Nat := w 0 [0, 0, 0]
def xyx : Word Nat := w 0 [1, 0]
def xxxyx : Word Nat := w 0 [0, 0, 1, 0]
def xxxyy : Word Nat := w 0 [0, 0, 1, 1]
def yxxxy : Word Nat := w 1 [0, 0, 0, 1]
def xxyx : Word Nat := w 0 [0, 1, 0]
def xyxx : Word Nat := w 0 [1, 0, 0]
def xxyxx : Word Nat := w 0 [0, 1, 0, 0]
def xxyy : Word Nat := w 0 [0, 1, 1]
def xyxy : Word Nat := w 0 [1, 0, 1]
def xyyx : Word Nat := w 0 [1, 1, 0]
def yxxy : Word Nat := w 1 [0, 0, 1]
def xxyzy : Word Nat := w 0 [0, 1, 2, 1]
def xyxzy : Word Nat := w 0 [1, 0, 2, 1]
def xyyzx : Word Nat := w 0 [1, 1, 2, 0]
def xzxyy : Word Nat := w 0 [2, 0, 1, 1]
def yxxzy : Word Nat := w 1 [0, 0, 2, 1]
def xyxxx : Word Nat := w 0 [1, 0, 0, 0]
def xyzx : Word Nat := w 0 [1, 2, 0]
def xzyx : Word Nat := w 0 [2, 1, 0]

def powerLaw : Identity Nat := Identity.mk xx xxxx
def tripleLeftContractionLaw : Identity Nat := Identity.mk xxxyx xyx
def tripleHeadSwitchLaw : Identity Nat := Identity.mk xxxyy yxxxy
def endpointTransferLaw : Identity Nat := Identity.mk xxyx xyxx
def splitEndpointContractionLaw : Identity Nat := Identity.mk xxyxx xyx
def squareInterleaveLaw : Identity Nat := Identity.mk xxyy xyxy
def squareFinalSwitchLaw : Identity Nat := Identity.mk xxyy xyyx
def squareInitialSwitchLaw : Identity Nat := Identity.mk xxyy yxxy
def attachmentXYXZYLaw : Identity Nat := Identity.mk xxyzy xyxzy
def attachmentXYYZXLaw : Identity Nat := Identity.mk xxyzy xyyzx
def attachmentXZXYYLaw : Identity Nat := Identity.mk xxyzy xzxyy
def attachmentYXXZYLaw : Identity Nat := Identity.mk xxyzy yxxzy
def rightTripleExpansionLaw : Identity Nat := Identity.mk xyx xyxxx
def closedInteriorSwapLaw : Identity Nat := Identity.mk xyzx xzyx

theorem basis_length : basis.length = 14 := by
  decide

private def instantiateThreeWords
    (first second third : Word Nat) : Nat -> Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | n + 3 => Word.singleton (n + 3)

theorem derivesBasisSubstitution
    (identity : Identity Nat) (member : identity ∈ basis)
    (substitution : Nat -> Word Nat) :
    Derives basis
      (identity.lhs.bind substitution)
      (identity.rhs.bind substitution) :=
  Derives.subst (Derives.fromBasis member) substitution

/-- Contract four adjacent copies of a nonempty block to two. -/
theorem derivesFourToTwo (block : Word Nat) :
    Derives basis
      (((block ++ block) ++ block) ++ block)
      (block ++ block) := by
  have substituted :=
    derivesBasisSubstitution powerLaw
      (by decide)
      (instantiateThreeWords block block block)
  simpa [powerLaw, xx, xxxx, w, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted.symm

/-- Contract `u^3 v u` to `u v u`. -/
theorem derivesTripleLeftContraction (u v : Word Nat) :
    Derives basis
      ((((u ++ u) ++ u) ++ v) ++ u)
      ((u ++ v) ++ u) := by
  have substituted :=
    derivesBasisSubstitution tripleLeftContractionLaw
      (by decide)
      (instantiateThreeWords u v v)
  simpa [tripleLeftContractionLaw, xxxyx, xyx, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Switch `u^3 v^2` to `v u^3 v`. -/
theorem derivesTripleHeadSwitch (u v : Word Nat) :
    Derives basis
      ((((u ++ u) ++ u) ++ v) ++ v)
      ((((v ++ u) ++ u) ++ u) ++ v) := by
  have substituted :=
    derivesBasisSubstitution tripleHeadSwitchLaw
      (by decide)
      (instantiateThreeWords u v v)
  simpa [tripleHeadSwitchLaw, xxxyy, yxxxy, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Move one copy of a repeated endpoint from left to right. -/
theorem derivesEndpointTransfer (u v : Word Nat) :
    Derives basis
      (((u ++ u) ++ v) ++ u)
      ((u ++ v) ++ (u ++ u)) := by
  have substituted :=
    derivesBasisSubstitution endpointTransferLaw
      (by decide)
      (instantiateThreeWords u v v)
  simpa [endpointTransferLaw, xxyx, xyxx, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Contract two separated endpoint pairs to one endpoint pair. -/
theorem derivesSplitEndpointContraction (u v : Word Nat) :
    Derives basis
      ((((u ++ u) ++ v) ++ u) ++ u)
      ((u ++ v) ++ u) := by
  have substituted :=
    derivesBasisSubstitution splitEndpointContractionLaw
      (by decide)
      (instantiateThreeWords u v v)
  simpa [splitEndpointContractionLaw, xxyxx, xyx, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

theorem derivesSquareInterleave (u v : Word Nat) :
    Derives basis
      ((u ++ u) ++ (v ++ v))
      ((u ++ v) ++ (u ++ v)) := by
  have substituted :=
    derivesBasisSubstitution squareInterleaveLaw
      (by decide)
      (instantiateThreeWords u v v)
  simpa [squareInterleaveLaw, xxyy, xyxy, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

theorem derivesSquareFinalSwitch (u v : Word Nat) :
    Derives basis
      ((u ++ u) ++ (v ++ v))
      (((u ++ v) ++ v) ++ u) := by
  have substituted :=
    derivesBasisSubstitution squareFinalSwitchLaw
      (by decide)
      (instantiateThreeWords u v v)
  simpa [squareFinalSwitchLaw, xxyy, xyyx, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

theorem derivesSquareInitialSwitch (u v : Word Nat) :
    Derives basis
      ((u ++ u) ++ (v ++ v))
      (((v ++ u) ++ u) ++ v) := by
  have substituted :=
    derivesBasisSubstitution squareInitialSwitchLaw
      (by decide)
      (instantiateThreeWords u v v)
  simpa [squareInitialSwitchLaw, xxyy, yxxy, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

theorem derivesAttachmentXYXZY (u v z : Word Nat) :
    Derives basis
      ((((u ++ u) ++ v) ++ z) ++ v)
      ((((u ++ v) ++ u) ++ z) ++ v) := by
  have substituted :=
    derivesBasisSubstitution attachmentXYXZYLaw
      (by decide)
      (instantiateThreeWords u v z)
  simpa [attachmentXYXZYLaw, xxyzy, xyxzy, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

theorem derivesAttachmentXYYZX (u v z : Word Nat) :
    Derives basis
      ((((u ++ u) ++ v) ++ z) ++ v)
      ((((u ++ v) ++ v) ++ z) ++ u) := by
  have substituted :=
    derivesBasisSubstitution attachmentXYYZXLaw
      (by decide)
      (instantiateThreeWords u v z)
  simpa [attachmentXYYZXLaw, xxyzy, xyyzx, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

theorem derivesAttachmentXZXYY (u v z : Word Nat) :
    Derives basis
      ((((u ++ u) ++ v) ++ z) ++ v)
      ((((u ++ z) ++ u) ++ v) ++ v) := by
  have substituted :=
    derivesBasisSubstitution attachmentXZXYYLaw
      (by decide)
      (instantiateThreeWords u v z)
  simpa [attachmentXZXYYLaw, xxyzy, xzxyy, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

theorem derivesAttachmentYXXZY (u v z : Word Nat) :
    Derives basis
      ((((u ++ u) ++ v) ++ z) ++ v)
      ((((v ++ u) ++ u) ++ z) ++ v) := by
  have substituted :=
    derivesBasisSubstitution attachmentYXXZYLaw
      (by decide)
      (instantiateThreeWords u v z)
  simpa [attachmentYXXZYLaw, xxyzy, yxxzy, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

theorem derivesRightTripleExpansion (u v : Word Nat) :
    Derives basis
      ((u ++ v) ++ u)
      ((((u ++ v) ++ u) ++ u) ++ u) := by
  have substituted :=
    derivesBasisSubstitution rightTripleExpansionLaw
      (by decide)
      (instantiateThreeWords u v v)
  simpa [rightTripleExpansionLaw, xyx, xyxxx, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

theorem derivesClosedInteriorSwap (u v z : Word Nat) :
    Derives basis
      (((u ++ v) ++ z) ++ u)
      (((u ++ z) ++ v) ++ u) := by
  have substituted :=
    derivesBasisSubstitution closedInteriorSwapLaw
      (by decide)
      (instantiateThreeWords u v z)
  simpa [closedInteriorSwapLaw, xyzx, xzyx, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-! ## Threshold-parity connected components -/

private abbrev ListDerives : List Nat -> List Nat -> Prop :=
  SemigroupBasis.CoRoots.S5_107.ListDerives basis

private def wordOfCons (head : Nat) (tail : List Nat) : Word Nat :=
  Word.mk head tail

private theorem condition7Basis_eq :
    Condition7.basis =
      [ Identity.mk xxxx xx,
        Identity.mk xxxyx xyx,
        Identity.mk xyyx yxxy,
        Identity.mk xyzx xzyx ] :=
  rfl

/-- Every Condition 7 law follows from the fixed fourteen-law basis. -/
private theorem condition7BasisDerives
    (identity : Identity Nat) (member : identity ∈ Condition7.basis) :
    Derives basis identity.lhs identity.rhs := by
  rw [condition7Basis_eq] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · simpa [xxxx, xx, w, Word.singleton, Word.append,
      Word.append_assoc] using
      derivesFourToTwo (Word.singleton 0)
  · simpa [xxxyx, xyx, w, Word.singleton, Word.append,
      Word.append_assoc] using
      derivesTripleLeftContraction
        (Word.singleton 0) (Word.singleton 1)
  · have switch :=
      (derivesSquareFinalSwitch
        (Word.singleton 0) (Word.singleton 1)).symm.trans
        (derivesSquareInitialSwitch
          (Word.singleton 0) (Word.singleton 1))
    simpa [xyyx, yxxy, xxyy, w, Word.singleton, Word.append,
      Word.append_assoc] using switch
  · simpa [xyzx, xzyx, w, Word.singleton, Word.append,
      Word.append_assoc] using
      derivesClosedInteriorSwap
        (Word.singleton 0) (Word.singleton 1) (Word.singleton 2)

private theorem cyclicDerivesOfParityEq
    (identity : Identity Nat)
    (parity :
      forall tested,
        identity.lhs.toList.count tested % 2 =
          identity.rhs.toList.count tested % 2) :
    Derives cyclicTwoBasis identity.lhs identity.rhs := by
  have reducedPerm :
      (parityReduce identity.lhs.toList).Perm
        (parityReduce identity.rhs.toList) :=
    parityReduce_perm_of_parity_eq parity
  have lhsNormal := cyclicDerivesNormal identity.lhs
  have rhsNormal := cyclicDerivesNormal identity.rhs
  cases lhsShape : parityReduce identity.lhs.toList with
  | nil =>
      rw [lhsShape] at reducedPerm
      have rhsShape : parityReduce identity.rhs.toList = [] :=
        reducedPerm.nil_eq.symm
      rw [lhsShape] at lhsNormal
      rw [rhsShape] at rhsNormal
      exact lhsNormal.trans <|
        (cyclicDerivesCommonSquare
          (Word.singleton identity.lhs.head)
          (Word.singleton identity.rhs.head)).trans rhsNormal.symm
  | cons leftHead leftTail =>
      cases rhsShape : parityReduce identity.rhs.toList with
      | nil =>
          rw [lhsShape, rhsShape] at reducedPerm
          exact False.elim (List.not_perm_cons_nil reducedPerm)
      | cons rightHead rightTail =>
          rw [lhsShape] at lhsNormal
          rw [rhsShape] at rhsNormal
          rw [lhsShape, rhsShape] at reducedPerm
          have middle :=
            cyclicDerivesPermutation
              (wordOfCons leftHead leftTail)
              (wordOfCons rightHead rightTail)
              reducedPerm
          exact lhsNormal.trans <| middle.trans rhsNormal.symm

private theorem cyclicSatisfiedByOfParityEq
    (identity : Identity Nat)
    (parity :
      forall tested,
        identity.lhs.toList.count tested % 2 =
          identity.rhs.toList.count tested % 2) :
    identity.SatisfiedBy cyclicTwo.semigroup := by
  intro valuation
  exact
    (cyclicDerivesOfParityEq identity parity).sound
      cyclicTwoBasis_models valuation

/-- Candidate-basis transport of the complete threshold-parity theorem for
one support-connected component. -/
theorem listDerivesConnectedComponentsOfCappedParity
    {left right : List Nat}
    (leftNonempty : left ≠ [])
    (rightNonempty : right ≠ [])
    (leftConnected : ConnectedComponentSupportConnected left)
    (rightConnected : ConnectedComponentSupportConnected right)
    (sameCapped :
      forall tested,
        min (left.count tested) 2 =
          min (right.count tested) 2)
    (sameParity :
      forall tested,
        left.count tested % 2 =
          right.count tested % 2) :
    ListDerives left right := by
  obtain ⟨leftHead, leftTail, rfl⟩ :=
    List.exists_cons_of_ne_nil leftNonempty
  obtain ⟨rightHead, rightTail, rfl⟩ :=
    List.exists_cons_of_ne_nil rightNonempty
  let identity :=
    Identity.mk
      (wordOfCons leftHead leftTail)
      (wordOfCons rightHead rightTail)
  have coreListDerivation :=
    SemigroupBasis.CoRoots.S5_379.listDerivesConnectedComponents_of_cappedCounts
        (left := leftHead :: leftTail)
        (right := rightHead :: rightTail)
        (by simp) (by simp) leftConnected rightConnected sameCapped
  have coreWordDerivation :
      Derives SemigroupBasis.CoRoots.S5_379.basis
        (wordOfCons leftHead leftTail)
        (wordOfCons rightHead rightTail) := by
    simpa [wordOfCons, SemigroupBasis.CoRoots.S5_107.listWordOfCons] using
      SemigroupBasis.CoRoots.S5_107.ListDerives.toWord
        coreListDerivation
  have cyclicValid :
      identity.SatisfiedBy Condition7.cyclic := by
    have valid :=
      cyclicSatisfiedByOfParityEq identity (by
        intro tested
        simpa [identity, wordOfCons, Word.toList] using
          sameParity tested)
    simpa [Condition7.cyclic, Condition7.cyclicTable,
      SemigroupBasis.Generated.S2_2.table_eq_catalogue_model] using valid
  have coreValid :
      identity.SatisfiedBy Condition7.core := by
    have valid :
        identity.SatisfiedBy
          SemigroupBasis.CoRoots.S5_379.table.semigroup := by
      intro valuation
      exact coreWordDerivation.sound
        SemigroupBasis.CoRoots.S5_379.models valuation
    simpa [Condition7.core, Condition7.coreTable] using valid
  have condition7Derivation :=
    SemigroupBasis.CoRoots.Order6LeeZhangCondition7Completeness.complete
      identity cyclicValid coreValid
  have candidateDerivation :
      Derives basis
        (wordOfCons leftHead leftTail)
        (wordOfCons rightHead rightTail) :=
    condition7Derivation.transport condition7BasisDerives
  exact
    SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
      candidateDerivation

/-! ## Parity-safe closed-envelope assembly -/

private theorem listDerivesRightEnvelopePowerWithOptionalInterior
    (endpoint : Nat) (interior : List Nat) :
    ListDerives
      ([endpoint] ++ interior ++ [endpoint])
      ([endpoint] ++ interior ++ [endpoint, endpoint, endpoint]) := by
  cases interior with
  | nil =>
      simpa [Word.toList_append, List.append_assoc] using
        (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
          (derivesFourToTwo (Word.singleton endpoint)).symm)
  | cons interiorHead interiorTail =>
      let interiorWord :=
        SemigroupBasis.CoRoots.S5_107.listWordOfCons
          interiorHead interiorTail
      simpa [interiorWord,
        SemigroupBasis.CoRoots.S5_107.listWordOfCons, Word.toList,
        Word.toList_append, List.append_assoc] using
          (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
            (derivesRightTripleExpansion
              (Word.singleton endpoint) interiorWord))

private theorem listDerivesAttachmentXYYZXWithOptionalMiddle
    (x y : Nat) (middle : List Nat) :
    ListDerives
      ([x, x, y] ++ middle ++ [y])
      ([x, y, y] ++ middle ++ [x]) := by
  cases middle with
  | nil =>
      simpa [Word.toList_append, List.append_assoc] using
        (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
          (derivesSquareFinalSwitch
            (Word.singleton x) (Word.singleton y)))
  | cons middleHead middleTail =>
      let middleWord :=
        SemigroupBasis.CoRoots.S5_107.listWordOfCons
          middleHead middleTail
      simpa [middleWord,
        SemigroupBasis.CoRoots.S5_107.listWordOfCons, Word.toList,
        Word.toList_append, List.append_assoc] using
          (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
            (derivesAttachmentXYYZX
              (Word.singleton x) (Word.singleton y) middleWord))

private theorem listDerivesLeftEnvelopePowerContraction
    (endpoint : Nat) (middle : List Nat)
    (middleNonempty : middle ≠ []) :
    ListDerives
      ([endpoint, endpoint, endpoint] ++ middle ++ [endpoint])
      ([endpoint] ++ middle ++ [endpoint]) := by
  obtain ⟨middleHead, middleTail, rfl⟩ :=
    List.exists_cons_of_ne_nil middleNonempty
  let middleWord :=
    SemigroupBasis.CoRoots.S5_107.listWordOfCons
      middleHead middleTail
  simpa [middleWord,
    SemigroupBasis.CoRoots.S5_107.listWordOfCons, Word.toList,
    Word.toList_append, List.append_assoc] using
      (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
        (derivesTripleLeftContraction
          (Word.singleton endpoint) middleWord))

/-- Candidate-basis version of the unconditional S5_441 closed-envelope
combine. The only permutation step is between two support-connected
`a`-envelopes, so it is supplied by the threshold-parity component theorem. -/
theorem listDerivesAdjacentParityEnvelopeCombine
    (a b : Nat) (p q : List Nat) :
    ListDerives
      ([a] ++ p ++ [a] ++ [b] ++ q ++ [b])
      ([a] ++ p ++ [b, b] ++ q ++ [a]) := by
  have expand :
      ListDerives
        ([a] ++ p ++ [a] ++ [b] ++ q ++ [b])
        ([a] ++ p ++ [a, a, a] ++ [b] ++ q ++ [b]) := by
    simpa [List.append_assoc] using
      SemigroupBasis.CoRoots.S5_107.ListDerives.append
        (listDerivesRightEnvelopePowerWithOptionalInterior a p)
        ([b] ++ q ++ [b])
  have attach :
      ListDerives
        ([a] ++ p ++ [a, a, a] ++ [b] ++ q ++ [b])
        ([a] ++ p ++ [a, a] ++ [b, b] ++ q ++ [a]) := by
    simpa [List.append_assoc] using
      SemigroupBasis.CoRoots.S5_107.ListDerives.prepend
        ([a] ++ p ++ [a])
        (listDerivesAttachmentXYYZXWithOptionalMiddle a b q)
  have arrangePermutation :
      ([a] ++ p ++ [a, a] ++ [b, b] ++ q ++ [a]).Perm
        ([a, a, a] ++ p ++ [b, b] ++ q ++ [a]) := by
    rw [List.perm_iff_count]
    intro tested
    simp only [List.count_append, List.count_cons, List.count_nil]
    omega
  have arrange :
      ListDerives
        ([a] ++ p ++ [a, a] ++ [b, b] ++ q ++ [a])
        ([a, a, a] ++ p ++ [b, b] ++ q ++ [a]) := by
    apply listDerivesConnectedComponentsOfCappedParity
    · simp
    · simp
    · simpa [SemigroupBasis.CoRoots.S5_441.parityEnvelopeRender,
        List.append_assoc] using
        SemigroupBasis.CoRoots.S5_441.parityEnvelopeRender_supportConnected
            a (p ++ [a, a] ++ [b, b] ++ q)
    · simpa [SemigroupBasis.CoRoots.S5_441.parityEnvelopeRender,
        List.append_assoc] using
        SemigroupBasis.CoRoots.S5_441.parityEnvelopeRender_supportConnected
            a ([a, a] ++ p ++ [b, b] ++ q)
    · intro tested
      exact congrArg (fun count => min count 2)
        (List.perm_iff_count.mp arrangePermutation tested)
    · intro tested
      exact congrArg (fun count => count % 2)
        (List.perm_iff_count.mp arrangePermutation tested)
  have contract :
      ListDerives
        ([a, a, a] ++ p ++ [b, b] ++ q ++ [a])
        ([a] ++ p ++ [b, b] ++ q ++ [a]) := by
    have middleNonempty : p ++ [b, b] ++ q ≠ [] := by
      simp
    simpa [List.append_assoc] using
      listDerivesLeftEnvelopePowerContraction
        a (p ++ [b, b] ++ q) middleNonempty
  exact
    SemigroupBasis.CoRoots.S5_107.ListDerives.trans expand <|
      SemigroupBasis.CoRoots.S5_107.ListDerives.trans attach <|
        SemigroupBasis.CoRoots.S5_107.ListDerives.trans arrange contract

/-- A connected component derives to the envelope selected by the S5_441
scanner. Only the scanner's exact permutation is reused; its derivation is
discarded. -/
theorem existsParityEnvelopeDerivationOfConnectedWithPerm
    {head : Nat} {tail : List Nat}
    (connected :
      ConnectedComponentSupportConnected (head :: tail))
    (lengthAtLeastTwo : 2 ≤ (head :: tail).length) :
    ∃ finalInterior,
      ListDerives
          (head :: tail)
          (SemigroupBasis.CoRoots.S5_441.parityEnvelopeRender
            head finalInterior []) ∧
        (head :: tail).Perm
          (SemigroupBasis.CoRoots.S5_441.parityEnvelopeRender
            head finalInterior []) := by
  obtain ⟨finalInterior, _s5Derivation, permutation⟩ :=
    S5_441.exists_parityEnvelopeDerivation_of_connected_with_perm
        connected lengthAtLeastTwo
  have targetConnected :
      ConnectedComponentSupportConnected
        (SemigroupBasis.CoRoots.S5_441.parityEnvelopeRender
          head finalInterior []) :=
    S5_441.parityEnvelopeRender_supportConnected head finalInterior
  have candidateDerivation :
      ListDerives
        (head :: tail)
        (SemigroupBasis.CoRoots.S5_441.parityEnvelopeRender
          head finalInterior []) := by
    apply listDerivesConnectedComponentsOfCappedParity
    · simp
    · simp [SemigroupBasis.CoRoots.S5_441.parityEnvelopeRender]
    · exact connected
    · exact targetConnected
    · intro tested
      exact congrArg (fun count => min count 2)
        (List.perm_iff_count.mp permutation tested)
    · intro tested
      exact congrArg (fun count => count % 2)
        (List.perm_iff_count.mp permutation tested)
  exact ⟨finalInterior, candidateDerivation, permutation⟩

/-- Fold support-connected components into one parity envelope. Every step is
a candidate-basis derivation and the final envelope is an exact permutation
of the flattened components. -/
theorem existsParityEnvelopeDerivationOfComponents
    (components : List (List Nat))
    (componentsNonempty : components ≠ [])
    (supportConnected :
      ∀ component ∈ components,
        ConnectedComponentSupportConnected component)
    (lengthAtLeastTwo :
      ∀ component ∈ components, 2 ≤ component.length) :
    ∃ endpoint finalInterior,
      ListDerives
          components.flatten
          (SemigroupBasis.CoRoots.S5_441.parityEnvelopeRender
            endpoint finalInterior []) ∧
        components.flatten.Perm
          (SemigroupBasis.CoRoots.S5_441.parityEnvelopeRender
            endpoint finalInterior []) := by
  induction components with
  | nil =>
      exact False.elim (componentsNonempty rfl)
  | cons component rest induction =>
      have componentLengthAtLeastTwo :
          2 ≤ component.length :=
        lengthAtLeastTwo component (by simp)
      have componentNonempty : component ≠ [] := by
        intro componentEmpty
        subst component
        simp at componentLengthAtLeastTwo
      obtain ⟨endpoint, tail, rfl⟩ :=
        List.exists_cons_of_ne_nil componentNonempty
      obtain
        ⟨interior, componentDerivation, componentPermutation⟩ :=
          existsParityEnvelopeDerivationOfConnectedWithPerm
            (supportConnected (endpoint :: tail) (by simp))
            componentLengthAtLeastTwo
      cases rest with
      | nil =>
          refine ⟨endpoint, interior, ?_, ?_⟩
          · simpa using componentDerivation
          · simpa using componentPermutation
      | cons next remaining =>
          obtain
            ⟨restEndpoint, restInterior,
              restDerivation, restPermutation⟩ :=
            induction
              (by simp)
              (fun current member =>
                supportConnected current
                  (List.Mem.tail (endpoint :: tail) member))
              (fun current member =>
                lengthAtLeastTwo current
                  (List.Mem.tail (endpoint :: tail) member))
          have normalizeFirst :
              ListDerives
                ((endpoint :: tail) ++
                  (next :: remaining).flatten)
                (SemigroupBasis.CoRoots.S5_441.parityEnvelopeRender
                    endpoint interior [] ++
                  (next :: remaining).flatten) :=
            SemigroupBasis.CoRoots.S5_107.ListDerives.append
              componentDerivation (next :: remaining).flatten
          have normalizeRest :
              ListDerives
                (SemigroupBasis.CoRoots.S5_441.parityEnvelopeRender
                    endpoint interior [] ++
                  (next :: remaining).flatten)
                (SemigroupBasis.CoRoots.S5_441.parityEnvelopeRender
                    endpoint interior [] ++
                  SemigroupBasis.CoRoots.S5_441.parityEnvelopeRender
                    restEndpoint restInterior []) :=
            SemigroupBasis.CoRoots.S5_107.ListDerives.prepend
              (SemigroupBasis.CoRoots.S5_441.parityEnvelopeRender
                endpoint interior [])
              restDerivation
          have combine :
              ListDerives
                (SemigroupBasis.CoRoots.S5_441.parityEnvelopeRender
                    endpoint interior [] ++
                  SemigroupBasis.CoRoots.S5_441.parityEnvelopeRender
                    restEndpoint restInterior [])
                (SemigroupBasis.CoRoots.S5_441.parityEnvelopeRender
                  endpoint
                  (interior ++
                    [restEndpoint, restEndpoint] ++ restInterior)
                  []) := by
            simpa [
              SemigroupBasis.CoRoots.S5_441.parityEnvelopeRender,
              List.append_assoc] using
                listDerivesAdjacentParityEnvelopeCombine
                  endpoint restEndpoint interior restInterior
          have normalizePermutation :
              ((endpoint :: tail) ++
                  (next :: remaining).flatten).Perm
                (SemigroupBasis.CoRoots.S5_441.parityEnvelopeRender
                    endpoint interior [] ++
                  SemigroupBasis.CoRoots.S5_441.parityEnvelopeRender
                    restEndpoint restInterior []) :=
            List.Perm.append componentPermutation restPermutation
          have combinePermutation :
              (SemigroupBasis.CoRoots.S5_441.parityEnvelopeRender
                    endpoint interior [] ++
                  SemigroupBasis.CoRoots.S5_441.parityEnvelopeRender
                    restEndpoint restInterior []).Perm
                (SemigroupBasis.CoRoots.S5_441.parityEnvelopeRender
                  endpoint
                  (interior ++
                    [restEndpoint, restEndpoint] ++ restInterior)
                  []) :=
            S5_441.adjacentParityEnvelopeCombine_perm
                endpoint restEndpoint interior restInterior
          refine
            ⟨endpoint,
              interior ++
                [restEndpoint, restEndpoint] ++ restInterior,
              ?_, ?_⟩
          · simpa using
              SemigroupBasis.CoRoots.S5_107.ListDerives.trans
                normalizeFirst <|
                  SemigroupBasis.CoRoots.S5_107.ListDerives.trans
                    normalizeRest combine
          · simpa using
              normalizePermutation.trans combinePermutation

/-- Candidate-basis normalization of an arbitrary nonempty exact-cut-free
gap to a closed parity envelope, preserving every occurrence count. -/
theorem existsParityEnvelopeDerivationOfNoExactCut
    {gap : List Nat}
    (noExactCut :
      ¬ ∃ left separator right,
        UniqueSeparatorFourExactCut gap left separator right)
    (gapNonempty : gap ≠ []) :
    ∃ endpoint finalInterior,
      ListDerives
          gap
          (SemigroupBasis.CoRoots.S5_441.parityEnvelopeRender
            endpoint finalInterior []) ∧
        gap.Perm
          (SemigroupBasis.CoRoots.S5_441.parityEnvelopeRender
            endpoint finalInterior []) := by
  obtain
    ⟨endpoint, finalInterior, derivation, permutation⟩ :=
      existsParityEnvelopeDerivationOfComponents
        (connectedComponentDecomposeList gap)
        (connectedComponentDecomposeList_nonempty gapNonempty)
        (connectedComponentDecomposeList_supportConnected gap)
        (S5_441.connectedComponentDecomposeList_components_length_ge_two_of_no_exactCut
            noExactCut)
  rw [connectedComponentDecomposeList_flatten gap]
    at derivation permutation
  exact ⟨endpoint, finalInterior, derivation, permutation⟩

/-! ## Finite-factor soundness -/

private def toFinThree : Nat -> Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

private def finiteBasis : List (Identity (Fin 3)) :=
  basis.map fun identity => identity.map toFinThree

private theorem basisRoundTripChecked :
    basis.all (fun identity =>
      decide ((identity.map toFinThree).map Fin.val = identity)) = true := by
  decide

private theorem modelsOfFiniteChecks
    (table : FiniteTable)
    (checked : finiteBasis.all table.checkIdentity = true) :
    Models table.semigroup basis := by
  intro identity member
  have finiteMember : identity.map toFinThree ∈ finiteBasis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    table.checkIdentityNat_sound (identity.map toFinThree)
      ((List.all_eq_true.mp checked) _ finiteMember)
  have restored : (identity.map toFinThree).map Fin.val = identity :=
    of_decide_eq_true <|
      (List.all_eq_true.mp basisRoundTripChecked) identity member
  rw [restored] at finiteValid
  exact finiteValid

theorem modelsS2_2 :
    Models SemigroupBasis.Generated.S2_2.table.semigroup basis :=
  modelsOfFiniteChecks SemigroupBasis.Generated.S2_2.table (by decide)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem modelsS5_378 :
    Models SemigroupBasis.CoRoots.S5_378.table.semigroup basis :=
  modelsOfFiniteChecks SemigroupBasis.CoRoots.S5_378.table (by decide)

/-! ## Exact joint semantic signature -/

def SameOccurrenceParity (left right : Word Nat) : Prop :=
  forall tested,
    left.toList.count tested % 2 =
      right.toList.count tested % 2

/-- The exact semantic data supplied jointly by `S5_378` and `S2_2`. -/
structure SameThresholdParitySeparatorSignature
    (left right : Word Nat) : Prop where
  separatorSimple :
    SemigroupBasis.CoRoots.S5_378.SameSeparatorSimpleSignature left right
  parity : SameOccurrenceParity left right

theorem sameThresholdParitySeparatorSignature_of_factorValid
    (identity : Identity Nat)
    (cyclicValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S2_2.table.semigroup)
    (s5Valid :
      identity.SatisfiedBy
        SemigroupBasis.CoRoots.S5_378.table.semigroup) :
    SameThresholdParitySeparatorSignature
      identity.lhs identity.rhs := by
  have cyclicValid' :
      identity.SatisfiedBy cyclicTwo.semigroup := by
    rw [← SemigroupBasis.Generated.S2_2.table_eq_catalogue_model]
    exact cyclicValid
  exact
    ⟨SemigroupBasis.CoRoots.S5_378.valid_sameSignature
        identity s5Valid,
      cyclicValid_parity_eq identity cyclicValid'⟩

theorem derives_sameThresholdParitySeparatorSignature
    {left right : Word Nat}
    (derivation : Derives basis left right) :
    SameThresholdParitySeparatorSignature left right := by
  let identity := Identity.mk left right
  exact sameThresholdParitySeparatorSignature_of_factorValid
    identity
    (fun valuation => derivation.sound modelsS2_2 valuation)
    (fun valuation => derivation.sound modelsS5_378 valuation)

theorem cappedCount_eq_of_sameThresholdParitySeparatorSignature
    {left right : Word Nat}
    (same : SameThresholdParitySeparatorSignature left right)
    (tested : Nat) :
    min (left.toList.count tested) 2 =
      min (right.toList.count tested) 2 :=
  SemigroupBasis.CoRoots.S5_378.SameSeparatorSimpleSignature.cappedCount_eq
    same.separatorSimple tested

/-! ## Parity-safe contextual exact-cut assembly -/

private abbrev CutSegment :=
  SemigroupBasis.CoRoots.S5_441.ExactCutSegment

private theorem supportSkeleton_eq
    {left right : Word Nat}
    (sameSupport : SemigroupBasis.CoRoots.S5_378.SameSupport left right)
    (sameExactCuts :
      SemigroupBasis.CoRoots.S5_378.SameExactCutSignature left right) :
    SemigroupBasis.CoRoots.S5_441.exactCutSupportSkeleton
        left.toList =
      SemigroupBasis.CoRoots.S5_441.exactCutSupportSkeleton
        right.toList := by
  apply
    S5_441.exactCutSupportSkeleton_eq_of_sameSupport_sameExactCutSignature
  · intro tested
    exact sameSupport tested
  · intro separator leftSupport rightSupport
    simpa only [
      SemigroupBasis.CoRoots.S5_441Invariant.ExactCutSignature,
      SemigroupBasis.CoRoots.S5_378.ExactCutSignature
    ] using sameExactCuts separator leftSupport rightSupport

private theorem alignedGapCappedCounts
    {leftLetters rightLetters : List Nat}
    {leftSegment rightSegment : CutSegment}
    (leftMember :
      leftSegment ∈
        SemigroupBasis.CoRoots.S5_441.exactCutDecomposition
          leftLetters)
    (rightMember :
      rightSegment ∈
        SemigroupBasis.CoRoots.S5_441.exactCutDecomposition
          rightLetters)
    (supportEq :
      connectedComponentSortedSupport leftSegment.gap =
        connectedComponentSortedSupport rightSegment.gap)
    (globalCapped :
      ∀ tested,
        min (leftLetters.count tested) 2 =
          min (rightLetters.count tested) 2) :
    ∀ tested,
      min (leftSegment.gap.count tested) 2 =
        min (rightSegment.gap.count tested) 2 := by
  intro tested
  by_cases leftGapMember : tested ∈ leftSegment.gap
  · have leftSupportMember :
        tested ∈ connectedComponentSortedSupport leftSegment.gap :=
      (connectedComponentSortedSupport_mem_iff
        tested leftSegment.gap).2 leftGapMember
    have rightSupportMember :
        tested ∈ connectedComponentSortedSupport rightSegment.gap := by
      rw [← supportEq]
      exact leftSupportMember
    have rightGapMember : tested ∈ rightSegment.gap :=
      (connectedComponentSortedSupport_mem_iff
        tested rightSegment.gap).1 rightSupportMember
    have leftLocalized :=
      SemigroupBasis.CoRoots.S5_441.exactCutDecomposition_count_eq_gap_count
        leftMember leftGapMember
    have rightLocalized :=
      SemigroupBasis.CoRoots.S5_441.exactCutDecomposition_count_eq_gap_count
        rightMember rightGapMember
    rw [← leftLocalized, ← rightLocalized]
    exact globalCapped tested
  · have leftSupportAbsent :
        tested ∉ connectedComponentSortedSupport leftSegment.gap := by
      intro supportMember
      exact leftGapMember <|
        (connectedComponentSortedSupport_mem_iff
          tested leftSegment.gap).1 supportMember
    have rightSupportAbsent :
        tested ∉ connectedComponentSortedSupport rightSegment.gap := by
      rw [← supportEq]
      exact leftSupportAbsent
    have rightGapAbsent : tested ∉ rightSegment.gap := by
      intro rightMember'
      exact rightSupportAbsent <|
        (connectedComponentSortedSupport_mem_iff
          tested rightSegment.gap).2 rightMember'
    have leftZero : leftSegment.gap.count tested = 0 :=
      List.count_eq_zero.mpr leftGapMember
    have rightZero : rightSegment.gap.count tested = 0 :=
      List.count_eq_zero.mpr rightGapAbsent
    simp [leftZero, rightZero]

private theorem alignedGapParity
    {leftLetters rightLetters : List Nat}
    {leftSegment rightSegment : CutSegment}
    (leftMember :
      leftSegment ∈
        SemigroupBasis.CoRoots.S5_441.exactCutDecomposition
          leftLetters)
    (rightMember :
      rightSegment ∈
        SemigroupBasis.CoRoots.S5_441.exactCutDecomposition
          rightLetters)
    (supportEq :
      connectedComponentSortedSupport leftSegment.gap =
        connectedComponentSortedSupport rightSegment.gap)
    (globalParity :
      ∀ tested,
        leftLetters.count tested % 2 =
          rightLetters.count tested % 2) :
    ∀ tested,
      leftSegment.gap.count tested % 2 =
        rightSegment.gap.count tested % 2 := by
  intro tested
  by_cases leftGapMember : tested ∈ leftSegment.gap
  · have leftSupportMember :
        tested ∈ connectedComponentSortedSupport leftSegment.gap :=
      (connectedComponentSortedSupport_mem_iff
        tested leftSegment.gap).2 leftGapMember
    have rightSupportMember :
        tested ∈ connectedComponentSortedSupport rightSegment.gap := by
      rw [← supportEq]
      exact leftSupportMember
    have rightGapMember : tested ∈ rightSegment.gap :=
      (connectedComponentSortedSupport_mem_iff
        tested rightSegment.gap).1 rightSupportMember
    have leftLocalized :=
      S5_441.exactCutDecomposition_count_mod_two_eq_gap_count_mod_two
        leftMember leftGapMember
    have rightLocalized :=
      S5_441.exactCutDecomposition_count_mod_two_eq_gap_count_mod_two
        rightMember rightGapMember
    exact leftLocalized.symm.trans <|
      (globalParity tested).trans rightLocalized
  · have leftSupportAbsent :
        tested ∉ connectedComponentSortedSupport leftSegment.gap := by
      intro supportMember
      exact leftGapMember <|
        (connectedComponentSortedSupport_mem_iff
          tested leftSegment.gap).1 supportMember
    have rightSupportAbsent :
        tested ∉ connectedComponentSortedSupport rightSegment.gap := by
      rw [← supportEq]
      exact leftSupportAbsent
    have rightGapAbsent : tested ∉ rightSegment.gap := by
      intro rightMember'
      exact rightSupportAbsent <|
        (connectedComponentSortedSupport_mem_iff
          tested rightSegment.gap).2 rightMember'
    rw [List.count_eq_zero.mpr leftGapMember,
      List.count_eq_zero.mpr rightGapAbsent]

private theorem alignedSegments_common
    {leftLetters rightLetters : List Nat}
    {leftSegment rightSegment : CutSegment}
    (leftMember :
      leftSegment ∈
        SemigroupBasis.CoRoots.S5_441.exactCutDecomposition
          leftLetters)
    (rightMember :
      rightSegment ∈
        SemigroupBasis.CoRoots.S5_441.exactCutDecomposition
          rightLetters)
    (supportSegmentEq :
      SemigroupBasis.CoRoots.S5_441.exactCutSupportSegment
          leftSegment =
        SemigroupBasis.CoRoots.S5_441.exactCutSupportSegment
          rightSegment)
    (globalCapped :
      ∀ tested,
        min (leftLetters.count tested) 2 =
          min (rightLetters.count tested) 2)
    (globalParity :
      ∀ tested,
        leftLetters.count tested % 2 =
          rightLetters.count tested % 2) :
    ∃ common,
      ListDerives leftSegment.render common ∧
      ListDerives rightSegment.render common := by
  have supportEq :
      connectedComponentSortedSupport leftSegment.gap =
        connectedComponentSortedSupport rightSegment.gap :=
    congrArg
      UniqueSeparatorCanonicalSegment.quadratic supportSegmentEq
  have separatorEq :
      leftSegment.separator = rightSegment.separator :=
    congrArg
      UniqueSeparatorCanonicalSegment.separator supportSegmentEq
  by_cases leftGapEmpty : leftSegment.gap = []
  · have rightGapEmpty : rightSegment.gap = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro tested rightGapMember
      have rightSupportMember :
          tested ∈ connectedComponentSortedSupport rightSegment.gap :=
        (connectedComponentSortedSupport_mem_iff
          tested rightSegment.gap).2 rightGapMember
      rw [← supportEq] at rightSupportMember
      have leftGapMember : tested ∈ leftSegment.gap :=
        (connectedComponentSortedSupport_mem_iff
          tested leftSegment.gap).1 rightSupportMember
      simpa [leftGapEmpty] using leftGapMember
    refine ⟨leftSegment.separator.toList, ?_, ?_⟩
    · simpa [SemigroupBasis.CoRoots.S5_441.ExactCutSegment.render,
        leftGapEmpty] using
        (SemigroupBasis.CoRoots.S5_107.ListDerives.refl
          (basis := basis) leftSegment.separator.toList)
    · simpa [SemigroupBasis.CoRoots.S5_441.ExactCutSegment.render,
        rightGapEmpty, separatorEq] using
        (SemigroupBasis.CoRoots.S5_107.ListDerives.refl
          (basis := basis) rightSegment.separator.toList)
  · have rightGapNonempty : rightSegment.gap ≠ [] := by
      intro rightGapEmpty
      obtain ⟨tested, testedMember⟩ :=
        List.exists_mem_of_ne_nil leftSegment.gap leftGapEmpty
      have leftSupportMember :
          tested ∈ connectedComponentSortedSupport leftSegment.gap :=
        (connectedComponentSortedSupport_mem_iff
          tested leftSegment.gap).2 testedMember
      rw [supportEq] at leftSupportMember
      have rightGapMember : tested ∈ rightSegment.gap :=
        (connectedComponentSortedSupport_mem_iff
          tested rightSegment.gap).1 leftSupportMember
      exact (List.ne_nil_of_mem rightGapMember) rightGapEmpty
    have leftNoExactCut :=
      SemigroupBasis.CoRoots.S5_441.exactCutDecomposition_gap_no_exactCut
        leftMember
    have rightNoExactCut :=
      SemigroupBasis.CoRoots.S5_441.exactCutDecomposition_gap_no_exactCut
        rightMember
    obtain
      ⟨leftEndpoint, leftInterior,
        leftDerivation, leftPermutation⟩ :=
      existsParityEnvelopeDerivationOfNoExactCut
        leftNoExactCut leftGapEmpty
    obtain
      ⟨rightEndpoint, rightInterior,
        rightDerivation, rightPermutation⟩ :=
      existsParityEnvelopeDerivationOfNoExactCut
        rightNoExactCut rightGapNonempty
    have gapCapped :=
      alignedGapCappedCounts
        leftMember rightMember supportEq globalCapped
    have gapParity :=
      alignedGapParity
        leftMember rightMember supportEq globalParity
    let leftTarget :=
      SemigroupBasis.CoRoots.S5_441.parityEnvelopeRender
        leftEndpoint leftInterior []
    let rightTarget :=
      SemigroupBasis.CoRoots.S5_441.parityEnvelopeRender
        rightEndpoint rightInterior []
    have targetDerivation : ListDerives leftTarget rightTarget := by
      apply listDerivesConnectedComponentsOfCappedParity
      · simp [leftTarget,
          SemigroupBasis.CoRoots.S5_441.parityEnvelopeRender]
      · simp [rightTarget,
          SemigroupBasis.CoRoots.S5_441.parityEnvelopeRender]
      · exact
          S5_441.parityEnvelopeRender_supportConnected
            leftEndpoint leftInterior
      · exact
          S5_441.parityEnvelopeRender_supportConnected
            rightEndpoint rightInterior
      · intro tested
        have leftCount :=
          List.perm_iff_count.mp leftPermutation tested
        have rightCount :=
          List.perm_iff_count.mp rightPermutation tested
        change min (leftTarget.count tested) 2 =
          min (rightTarget.count tested) 2
        rw [← leftCount, ← rightCount]
        exact gapCapped tested
      · intro tested
        have leftCount :=
          List.perm_iff_count.mp leftPermutation tested
        have rightCount :=
          List.perm_iff_count.mp rightPermutation tested
        change leftTarget.count tested % 2 =
          rightTarget.count tested % 2
        rw [← leftCount, ← rightCount]
        exact gapParity tested
    let common := rightTarget ++ leftSegment.separator.toList
    have leftSegmentDerivation :
        ListDerives leftSegment.render common := by
      have gapDerivation :=
        leftDerivation.trans targetDerivation
      simpa [common, leftTarget, rightTarget,
        SemigroupBasis.CoRoots.S5_441.ExactCutSegment.render] using
        SemigroupBasis.CoRoots.S5_107.ListDerives.append
          gapDerivation leftSegment.separator.toList
    have rightSegmentDerivation :
        ListDerives rightSegment.render common := by
      simpa [common, rightTarget,
        SemigroupBasis.CoRoots.S5_441.ExactCutSegment.render,
        separatorEq] using
        SemigroupBasis.CoRoots.S5_107.ListDerives.append
          rightDerivation rightSegment.separator.toList
    exact
      ⟨common, leftSegmentDerivation, rightSegmentDerivation⟩

private def retainCutSegment (segment : CutSegment) : Bool :=
  decide (¬ (segment.gap = [] ∧ segment.separator = none))

private def retainedCutSegments
    (segments : List CutSegment) : List CutSegment :=
  segments.filter retainCutSegment

private theorem render_retainedCutSegments
    (segments : List CutSegment) :
    SemigroupBasis.CoRoots.S5_441.renderExactCutSegments
        (retainedCutSegments segments) =
      SemigroupBasis.CoRoots.S5_441.renderExactCutSegments
        segments := by
  induction segments with
  | nil => rfl
  | cons segment remaining induction =>
      unfold retainedCutSegments at induction
      by_cases omitted :
          segment.gap = [] ∧ segment.separator = none
      · simp [retainedCutSegments, retainCutSegment, omitted,
          SemigroupBasis.CoRoots.S5_441.ExactCutSegment.render,
          induction]
      · simp [retainedCutSegments, retainCutSegment, omitted,
          induction]

private theorem supportSegments_eq_map_retained
    (segments : List CutSegment) :
    SemigroupBasis.CoRoots.S5_441.exactCutSupportSegments segments =
      (retainedCutSegments segments).map
        SemigroupBasis.CoRoots.S5_441.exactCutSupportSegment := by
  induction segments with
  | nil => rfl
  | cons segment remaining induction =>
      unfold retainedCutSegments at induction
      unfold SemigroupBasis.CoRoots.S5_441.exactCutSupportSegments
        at induction
      by_cases omitted :
          segment.gap = [] ∧ segment.separator = none
      · simp [retainedCutSegments, retainCutSegment,
          SemigroupBasis.CoRoots.S5_441.exactCutSupportSegments,
          SemigroupBasis.CoRoots.S5_441.exactCutSupportSegment?,
          omitted, induction]
      · simp [retainedCutSegments, retainCutSegment,
          SemigroupBasis.CoRoots.S5_441.exactCutSupportSegments,
          SemigroupBasis.CoRoots.S5_441.exactCutSupportSegment?,
          omitted, induction]

private theorem retainedCutSegments_member
    {segment : CutSegment} {segments : List CutSegment}
    (member : segment ∈ retainedCutSegments segments) :
    segment ∈ segments :=
  (List.mem_filter.mp member).1

private theorem assembleRetainedSegments
    (leftLetters rightLetters : List Nat)
    (globalCapped :
      ∀ tested,
        min (leftLetters.count tested) 2 =
          min (rightLetters.count tested) 2)
    (globalParity :
      ∀ tested,
        leftLetters.count tested % 2 =
          rightLetters.count tested % 2) :
    ∀ (leftSegments rightSegments : List CutSegment),
      (∀ segment, segment ∈ leftSegments →
        segment ∈
          SemigroupBasis.CoRoots.S5_441.exactCutDecomposition
            leftLetters) →
      (∀ segment, segment ∈ rightSegments →
        segment ∈
          SemigroupBasis.CoRoots.S5_441.exactCutDecomposition
            rightLetters) →
      leftSegments.map
          SemigroupBasis.CoRoots.S5_441.exactCutSupportSegment =
        rightSegments.map
          SemigroupBasis.CoRoots.S5_441.exactCutSupportSegment →
      ∃ common,
        ListDerives
          (SemigroupBasis.CoRoots.S5_441.renderExactCutSegments
            leftSegments) common ∧
        ListDerives
          (SemigroupBasis.CoRoots.S5_441.renderExactCutSegments
            rightSegments) common
  | [], [], _, _, _ =>
      ⟨[],
        SemigroupBasis.CoRoots.S5_107.ListDerives.refl
          (basis := basis) [],
        SemigroupBasis.CoRoots.S5_107.ListDerives.refl
          (basis := basis) []⟩
  | [], _ :: _, _, _, supportEq => by
      simp at supportEq
  | _ :: _, [], _, _, supportEq => by
      simp at supportEq
  | leftSegment :: leftRemaining,
      rightSegment :: rightRemaining,
      leftMembers, rightMembers, supportEq => by
      simp only [List.map_cons, List.cons.injEq] at supportEq
      have leftSegmentMember :=
        leftMembers leftSegment (by simp)
      have rightSegmentMember :=
        rightMembers rightSegment (by simp)
      obtain
        ⟨headCommon, leftHeadDerivation,
          rightHeadDerivation⟩ :=
        alignedSegments_common
          leftSegmentMember rightSegmentMember supportEq.1
          globalCapped globalParity
      obtain
        ⟨tailCommon, leftTailDerivation,
          rightTailDerivation⟩ :=
        assembleRetainedSegments
          leftLetters rightLetters globalCapped globalParity
          leftRemaining rightRemaining
          (fun segment member =>
            leftMembers segment
              (List.Mem.tail leftSegment member))
          (fun segment member =>
            rightMembers segment
              (List.Mem.tail rightSegment member))
          supportEq.2
      have leftHeadStep :
          ListDerives
            (leftSegment.render ++
              SemigroupBasis.CoRoots.S5_441.renderExactCutSegments
                leftRemaining)
            (headCommon ++
              SemigroupBasis.CoRoots.S5_441.renderExactCutSegments
                leftRemaining) :=
        SemigroupBasis.CoRoots.S5_107.ListDerives.append
          leftHeadDerivation
          (SemigroupBasis.CoRoots.S5_441.renderExactCutSegments
            leftRemaining)
      have leftTailStep :
          ListDerives
            (headCommon ++
              SemigroupBasis.CoRoots.S5_441.renderExactCutSegments
                leftRemaining)
            (headCommon ++ tailCommon) :=
        SemigroupBasis.CoRoots.S5_107.ListDerives.prepend
          headCommon leftTailDerivation
      have rightHeadStep :
          ListDerives
            (rightSegment.render ++
              SemigroupBasis.CoRoots.S5_441.renderExactCutSegments
                rightRemaining)
            (headCommon ++
              SemigroupBasis.CoRoots.S5_441.renderExactCutSegments
                rightRemaining) :=
        SemigroupBasis.CoRoots.S5_107.ListDerives.append
          rightHeadDerivation
          (SemigroupBasis.CoRoots.S5_441.renderExactCutSegments
            rightRemaining)
      have rightTailStep :
          ListDerives
            (headCommon ++
              SemigroupBasis.CoRoots.S5_441.renderExactCutSegments
                rightRemaining)
            (headCommon ++ tailCommon) :=
        SemigroupBasis.CoRoots.S5_107.ListDerives.prepend
          headCommon rightTailDerivation
      exact
        ⟨headCommon ++ tailCommon,
          by simpa using leftHeadStep.trans leftTailStep,
          by simpa using rightHeadStep.trans rightTailStep⟩
termination_by leftSegments rightSegments =>
  leftSegments.length + rightSegments.length

/-- Full parity-safe contextual assembly across the deterministic exact-cut
decomposition. -/
theorem exactCutAssembly
    {left right : Word Nat}
    (sameSupport :
      SemigroupBasis.CoRoots.S5_378.SameSupport left right)
    (sameExactCuts :
      SemigroupBasis.CoRoots.S5_378.SameExactCutSignature left right)
    (globalCapped :
      ∀ tested,
        min (left.toList.count tested) 2 =
          min (right.toList.count tested) 2)
    (globalParity :
      ∀ tested,
        left.toList.count tested % 2 =
          right.toList.count tested % 2) :
    ∃ common : List Nat,
      ListDerives left.toList common ∧
      ListDerives right.toList common := by
  let leftSegments :=
    SemigroupBasis.CoRoots.S5_441.exactCutDecomposition left.toList
  let rightSegments :=
    SemigroupBasis.CoRoots.S5_441.exactCutDecomposition right.toList
  let leftRetained := retainedCutSegments leftSegments
  let rightRetained := retainedCutSegments rightSegments
  have skeletonEq :=
    supportSkeleton_eq sameSupport sameExactCuts
  have supportSegmentsEq :
      SemigroupBasis.CoRoots.S5_441.exactCutSupportSegments
          leftSegments =
        SemigroupBasis.CoRoots.S5_441.exactCutSupportSegments
          rightSegments := by
    simpa [leftSegments, rightSegments,
      SemigroupBasis.CoRoots.S5_441.exactCutSupportSkeleton] using
        skeletonEq
  have retainedSupportEq :
      leftRetained.map
          SemigroupBasis.CoRoots.S5_441.exactCutSupportSegment =
        rightRetained.map
          SemigroupBasis.CoRoots.S5_441.exactCutSupportSegment := by
    rw [← supportSegments_eq_map_retained,
      ← supportSegments_eq_map_retained]
    exact supportSegmentsEq
  have leftMembers :
      ∀ segment, segment ∈ leftRetained →
        segment ∈
          SemigroupBasis.CoRoots.S5_441.exactCutDecomposition
            left.toList := by
    intro segment member
    exact retainedCutSegments_member member
  have rightMembers :
      ∀ segment, segment ∈ rightRetained →
        segment ∈
          SemigroupBasis.CoRoots.S5_441.exactCutDecomposition
            right.toList := by
    intro segment member
    exact retainedCutSegments_member member
  obtain ⟨common, leftDerivation, rightDerivation⟩ :=
    assembleRetainedSegments
      left.toList right.toList globalCapped globalParity
      leftRetained rightRetained
      leftMembers rightMembers retainedSupportEq
  have leftRenderEq :
      SemigroupBasis.CoRoots.S5_441.renderExactCutSegments
          leftRetained = left.toList := by
    calc
      SemigroupBasis.CoRoots.S5_441.renderExactCutSegments
          leftRetained =
          SemigroupBasis.CoRoots.S5_441.renderExactCutSegments
            leftSegments :=
        render_retainedCutSegments leftSegments
      _ = left.toList := by
        simpa [leftSegments] using
          SemigroupBasis.CoRoots.S5_441.render_exactCutDecomposition
            left.toList
  have rightRenderEq :
      SemigroupBasis.CoRoots.S5_441.renderExactCutSegments
          rightRetained = right.toList := by
    calc
      SemigroupBasis.CoRoots.S5_441.renderExactCutSegments
          rightRetained =
          SemigroupBasis.CoRoots.S5_441.renderExactCutSegments
            rightSegments :=
        render_retainedCutSegments rightSegments
      _ = right.toList := by
        simpa [rightSegments] using
          SemigroupBasis.CoRoots.S5_441.render_exactCutDecomposition
            right.toList
  rw [leftRenderEq] at leftDerivation
  rw [rightRenderEq] at rightDerivation
  exact ⟨common, leftDerivation, rightDerivation⟩

/-- The joint unrestricted semantic signature is derivationally sufficient. -/
theorem listDerivesOfSameThresholdParitySeparatorSignature
    {left right : Word Nat}
    (same : SameThresholdParitySeparatorSignature left right) :
    ListDerives left.toList right.toList := by
  obtain ⟨common, leftDerivation, rightDerivation⟩ :=
    exactCutAssembly
      same.separatorSimple.support
      same.separatorSimple.exactCuts
      (fun tested =>
        cappedCount_eq_of_sameThresholdParitySeparatorSignature
          same tested)
      same.parity
  exact leftDerivation.trans rightDerivation.symm

/-- Word-level sufficiency of support, exact cuts, cap-two counts, and
coordinatewise parity for the fourteen-law basis. -/
theorem derivesOfSameThresholdParitySeparatorSignature
    {left right : Word Nat}
    (same : SameThresholdParitySeparatorSignature left right) :
    Derives basis left right := by
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail =>
          simpa [
            SemigroupBasis.CoRoots.S5_107.listWordOfCons,
            Word.toList] using
              SemigroupBasis.CoRoots.S5_107.ListDerives.toWord
                (listDerivesOfSameThresholdParitySeparatorSignature same)

/-- Every unrestricted identity valid in both factors is derivable from the
fixed fourteen laws. -/
theorem derivesOfFactorValid
    (identity : Identity Nat)
    (cyclicValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S2_2.table.semigroup)
    (s5Valid :
      identity.SatisfiedBy
        SemigroupBasis.CoRoots.S5_378.table.semigroup) :
    Derives basis identity.lhs identity.rhs :=
  derivesOfSameThresholdParitySeparatorSignature
    (sameThresholdParitySeparatorSignature_of_factorValid
      identity cyclicValid s5Valid)

/-- Unrestricted finite basis theorem for
`V(S2_2) ∩ V(S5_378)`. -/
def factorIntersectionBasis :
    IntersectionBasis
      SemigroupBasis.Generated.S2_2.table.semigroup
      SemigroupBasis.CoRoots.S5_378.table.semigroup
      basis where
  leftModels := modelsS2_2
  rightModels := modelsS5_378
  complete := derivesOfFactorValid

abbrev intersectionBasis := factorIntersectionBasis

/-! ## Threshold-parity multiplicity profile -/

/-- Retain one copy of a singleton, two copies of a positive even
multiplicity, and three copies of a larger odd multiplicity. -/
def thresholdParityReduce : List Nat -> List Nat
  | [] => []
  | x :: xs =>
      let reduced := thresholdParityReduce xs
      if reduced.count x < 3 then x :: reduced else reduced.erase x

theorem thresholdParityReduce_count_le_three
    (tested : Nat) (letters : List Nat) :
    (thresholdParityReduce letters).count tested <= 3 := by
  induction letters with
  | nil =>
      simp [thresholdParityReduce]
  | cons x xs induction =>
      simp only [thresholdParityReduce]
      split <;> rename_i countCondition
      · by_cases equal : tested = x
        · subst tested
          rw [List.count_cons_self]
          omega
        · rw [List.count_cons_of_ne (Ne.symm equal)]
          exact induction
      · by_cases equal : tested = x
        · subst tested
          rw [List.count_erase_self]
          omega
        · rw [List.count_erase_of_ne equal]
          exact induction

theorem mem_thresholdParityReduce_iff
    (tested : Nat) (letters : List Nat) :
    tested ∈ thresholdParityReduce letters ↔ tested ∈ letters := by
  induction letters with
  | nil =>
      simp [thresholdParityReduce]
  | cons x xs induction =>
      simp only [thresholdParityReduce]
      split <;> rename_i countCondition
      · simp [induction]
      · have countLe := thresholdParityReduce_count_le_three x xs
        have countEq : (thresholdParityReduce xs).count x = 3 := by
          omega
        by_cases equal : tested = x
        · subst tested
          have remains : x ∈ (thresholdParityReduce xs).erase x := by
            rw [← List.count_pos_iff, List.count_erase_self, countEq]
            omega
          simp [remains]
        · rw [List.mem_erase_of_ne equal]
          simp [induction, equal]

theorem thresholdParityReduce_count_mod_two
    (tested : Nat) (letters : List Nat) :
    (thresholdParityReduce letters).count tested % 2 =
      letters.count tested % 2 := by
  induction letters with
  | nil =>
      simp [thresholdParityReduce]
  | cons x xs induction =>
      simp only [thresholdParityReduce]
      split <;> rename_i countCondition
      · by_cases equal : tested = x
        · subst tested
          rw [List.count_cons_self, List.count_cons_self]
          omega
        · rw [List.count_cons_of_ne (Ne.symm equal),
            List.count_cons_of_ne (Ne.symm equal)]
          exact induction
      · by_cases equal : tested = x
        · subst tested
          have countLe := thresholdParityReduce_count_le_three x xs
          have countEq : (thresholdParityReduce xs).count x = 3 := by
            omega
          rw [List.count_erase_self, List.count_cons_self, countEq]
          omega
        · rw [List.count_erase_of_ne equal,
            List.count_cons_of_ne (Ne.symm equal)]
          exact induction

theorem thresholdParityReduce_capped_count
    (tested : Nat) (letters : List Nat) :
    min ((thresholdParityReduce letters).count tested) 2 =
      min (letters.count tested) 2 := by
  induction letters with
  | nil =>
      simp [thresholdParityReduce]
  | cons x xs induction =>
      simp only [thresholdParityReduce]
      split <;> rename_i countCondition
      · by_cases equal : tested = x
        · subst tested
          rw [List.count_cons_self, List.count_cons_self]
          have countLe := thresholdParityReduce_count_le_three x xs
          omega
        · rw [List.count_cons_of_ne (Ne.symm equal),
            List.count_cons_of_ne (Ne.symm equal)]
          exact induction
      · by_cases equal : tested = x
        · subst tested
          have countLe := thresholdParityReduce_count_le_three x xs
          have countEq : (thresholdParityReduce xs).count x = 3 := by
            omega
          rw [List.count_erase_self, List.count_cons_self, countEq]
          omega
        · rw [List.count_erase_of_ne equal,
            List.count_cons_of_ne (Ne.symm equal)]
          exact induction

theorem thresholdParityReduce_count_eq_of_signatures
    {left right : List Nat}
    (capped :
      forall tested,
        min (left.count tested) 2 =
          min (right.count tested) 2)
    (parity :
      forall tested,
        left.count tested % 2 =
          right.count tested % 2) :
    forall tested,
      (thresholdParityReduce left).count tested =
        (thresholdParityReduce right).count tested := by
  intro tested
  have leftLe := thresholdParityReduce_count_le_three tested left
  have rightLe := thresholdParityReduce_count_le_three tested right
  have reducedCapped :
      min ((thresholdParityReduce left).count tested) 2 =
        min ((thresholdParityReduce right).count tested) 2 := by
    rw [thresholdParityReduce_capped_count,
      thresholdParityReduce_capped_count, capped tested]
  have reducedParity :
      (thresholdParityReduce left).count tested % 2 =
        (thresholdParityReduce right).count tested % 2 := by
    rw [thresholdParityReduce_count_mod_two,
      thresholdParityReduce_count_mod_two, parity tested]
  omega

theorem thresholdParityReduce_perm_of_signatures
    {left right : List Nat}
    (capped :
      forall tested,
        min (left.count tested) 2 =
          min (right.count tested) 2)
    (parity :
      forall tested,
        left.count tested % 2 =
          right.count tested % 2) :
    (thresholdParityReduce left).Perm
      (thresholdParityReduce right) := by
  rw [List.perm_iff_count]
  exact thresholdParityReduce_count_eq_of_signatures capped parity

/-- Factor validity fixes the complete threshold-parity multiplicity
profile. -/
theorem thresholdParityReduce_perm_of_factorValid
    (identity : Identity Nat)
    (cyclicValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S2_2.table.semigroup)
    (s5Valid :
      identity.SatisfiedBy
        SemigroupBasis.CoRoots.S5_378.table.semigroup) :
    (thresholdParityReduce identity.lhs.toList).Perm
      (thresholdParityReduce identity.rhs.toList) := by
  have same :=
    sameThresholdParitySeparatorSignature_of_factorValid
      identity cyclicValid s5Valid
  apply thresholdParityReduce_perm_of_signatures
  · exact fun tested =>
      cappedCount_eq_of_sameThresholdParitySeparatorSignature
        same tested
  · exact same.parity

end SemigroupBasis.CoRoots.Order6FactorPairS2S5378
