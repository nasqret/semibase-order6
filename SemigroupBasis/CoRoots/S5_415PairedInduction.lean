import SemigroupBasis.CoRoots.S5_415Retarget

namespace SemigroupBasis.CoRoots.S5_415

open SemigroupBasis

/-! ## A constructive square-bank retarget -/

/-- The explorer's reusable retarget `F(A,B)`:
`A B A B²  ->  B² A²`.  Every intermediate below is one contextual
instance of the three exact basis laws or of `derivesEmptyExcursionSwap`. -/
theorem derivesRetargetF (A B : Word Nat) :
    Derives basis (((A ++ B) ++ A) ++ (B ++ B))
      ((B ++ B) ++ (A ++ A)) := by
  have step1 :
      Derives basis
        (((A ++ B) ++ A) ++ (B ++ B))
        ((((((A ++ B) ++ A) ++ B) ++ A) ++ B) ++ B) := by
    simpa [Word.append_assoc] using
      Derives.appendRight (derivesSandwichExpansion A B) (B ++ B)
  have step2 :
      Derives basis
        ((((((A ++ B) ++ A) ++ B) ++ A) ++ B) ++ B)
        ((((((A ++ B) ++ A) ++ B) ++ B) ++ A) ++ B) := by
    simpa [Word.append_assoc] using
      Derives.prepend ((A ++ B) ++ A)
        (derivesEmptyExcursionSwap B A).symm
  have step3 :
      Derives basis
        ((((((A ++ B) ++ A) ++ B) ++ B) ++ A) ++ B)
        ((((((A ++ B) ++ B) ++ A) ++ B) ++ A) ++ B) := by
    simpa [Word.append_assoc] using
      Derives.appendRight
        (Derives.prepend A
          (derivesEmptyExcursionSwap B A).symm)
        (A ++ B)
  have step4 :
      Derives basis
        ((((((A ++ B) ++ B) ++ A) ++ B) ++ A) ++ B)
        ((((((A ++ A) ++ B) ++ A) ++ B) ++ B) ++ B) := by
    simpa [Word.append_assoc] using
      Derives.prepend A
        (derivesSquareCommutation B (A ++ B))
  have step5 :
      Derives basis
        ((((((A ++ A) ++ B) ++ A) ++ B) ++ B) ++ B)
        (((((A ++ A) ++ B) ++ A) ++ B) ++ B) := by
    simpa [Word.append_assoc] using
      Derives.prepend (((A ++ A) ++ B) ++ A)
        (derivesPowerContraction B)
  have step6 :
      Derives basis
        (((((A ++ A) ++ B) ++ A) ++ B) ++ B)
        (((((A ++ B) ++ A) ++ A) ++ B) ++ B) := by
    simpa [Word.append_assoc] using
      Derives.appendRight
        (derivesEmptyExcursionSwap A B) (B ++ B)
  have step7 :
      Derives basis
        (((((A ++ B) ++ A) ++ A) ++ B) ++ B)
        (((((A ++ B) ++ B) ++ B) ++ A) ++ A) := by
    simpa [Word.append_assoc] using
      Derives.prepend (A ++ B)
        (derivesSquareCommutation A B)
  have step8 :
      Derives basis
        (((((A ++ B) ++ B) ++ B) ++ A) ++ A)
        ((((A ++ B) ++ B) ++ A) ++ A) := by
    simpa [Word.append_assoc] using
      Derives.appendRight
        (Derives.prepend A (derivesPowerContraction B))
        (A ++ A)
  have step9 :
      Derives basis
        ((((A ++ B) ++ B) ++ A) ++ A)
        ((((A ++ A) ++ A) ++ B) ++ B) := by
    simpa [Word.append_assoc] using
      Derives.prepend A (derivesSquareCommutation B A)
  have step10 :
      Derives basis
        ((((A ++ A) ++ A) ++ B) ++ B)
        (((A ++ A) ++ B) ++ B) := by
    simpa [Word.append_assoc] using
      Derives.appendRight (derivesPowerContraction A) (B ++ B)
  have finish :
      Derives basis
        (((A ++ A) ++ B) ++ B)
        ((B ++ B) ++ (A ++ A)) := by
    simpa [Word.append_assoc] using derivesSquareCommutation A B
  exact step1.trans <| step2.trans <| step3.trans <| step4.trans <|
    step5.trans <| step6.trans <| step7.trans <| step8.trans <|
      step9.trans <| step10.trans finish

/-- The reusable `F(A,B)` retarget is stable under arbitrary raw contexts.
Its target is written as a literal two-block commuting square bank, so later
normalization steps do not have to recover that provenance from a bare
`Derives` witness. -/
theorem derivesRetargetFUnderContext
    (left right : List Nat) (A B : Word Nat) :
    Derives basis
      (retargetContext left (((A ++ B) ++ A) ++ (B ++ B)) right)
      (retargetContext left (squaredWalkBank B [A]) right) := by
  simpa [squaredWalkBank] using
    derivesRetargetContext left right (derivesRetargetF A B)

/-- A head-anchored canonical bank is either a genuinely trailing word with
no return to the anchor, or a nonempty literal bank of commuting squares.
The latter form is exactly the target produced by contextual `F` when its
left context is empty. -/
inductive HeadAnchoredCommutingSquareBankShape
    (anchor : Nat) : Word Nat → Prop
  | trailing (suffix : List Nat) (anchorAbsent : anchor ∉ suffix) :
      HeadAnchoredCommutingSquareBankShape anchor
        (retargetContext [] (Word.singleton anchor) suffix)
  | bank (first : Word Nat) (rest : List (Word Nat))
      (suffix : List Nat) (firstHead : first.head = anchor) :
      HeadAnchoredCommutingSquareBankShape anchor
        (retargetContext [] (squaredWalkBank first rest) suffix)

theorem HeadAnchoredCommutingSquareBankShape.head_eq
    {anchor : Nat} {word : Word Nat}
    (shape : HeadAnchoredCommutingSquareBankShape anchor word) :
    word.head = anchor := by
  cases shape with
  | trailing suffix anchorAbsent =>
      simp [retargetContext, retargetPrependLetters]
  | bank first rest suffix firstHead =>
      simp [retargetContext, retargetPrependLetters, firstHead]

/-- A word with no later occurrence of its head is the zero-square case of
the canonical head-anchored bank. -/
theorem headAnchoredCommutingSquareBankShape_of_head_not_mem_tail
    (word : Word Nat) (headAbsent : word.head ∉ word.tail) :
    HeadAnchoredCommutingSquareBankShape word.head word := by
  cases word with
  | mk head tail =>
      have targetEq :
          retargetContext [] (Word.singleton head) tail =
            ⟨head, tail⟩ := by
        apply Word.toList_injective
        rw [retargetContext_toList]
        simp [Word.toList, Word.toList_singleton]
      have trailing :=
        HeadAnchoredCommutingSquareBankShape.trailing tail headAbsent
      rw [targetEq] at trailing
      exact trailing

/-- One contextual `F` step with no left context constructs an explicit
head-anchored two-square bank. -/
theorem existsDerivesRetargetFHeadAnchoredSquareBank
    (suffix : List Nat) (A B : Word Nat) :
    ∃ target : Word Nat,
      Derives basis
          (retargetContext [] (((A ++ B) ++ A) ++ (B ++ B)) suffix)
          target ∧
        HeadAnchoredCommutingSquareBankShape B.head target := by
  refine
    ⟨retargetContext [] (squaredWalkBank B [A]) suffix,
      derivesRetargetFUnderContext [] suffix A B, ?_⟩
  exact
    HeadAnchoredCommutingSquareBankShape.bank B [A] suffix rfl

/-! ## A head-preserving retarget through a transient square bank -/

/-- The exposing half of `G(A,B)`.  An empty-excursion swap exposes the
`F(A,B)` source, and `F` produces the transient bank `B² A²`. -/
theorem derivesEqualHeadRetargetGExpose (A B : Word Nat) :
    Derives basis
      ((((A ++ B) ++ B) ++ A) ++ B)
      ((B ++ B) ++ (A ++ A)) := by
  have exposeF :
      Derives basis
        ((((A ++ B) ++ B) ++ A) ++ B)
        (((A ++ B) ++ A) ++ (B ++ B)) := by
    simpa [Word.append_assoc] using
      Derives.prepend A (derivesEmptyExcursionSwap B A)
  exact exposeF.trans (derivesRetargetF A B)

/-- The replay half of `G(A,B)`.  It leaves the transient bank and restores
the original literal head while retaining the required semantic content. -/
theorem derivesEqualHeadRetargetGReplay (A B : Word Nat) :
    Derives basis
      ((B ++ B) ++ (A ++ A))
      (((A ++ A) ++ B) ++ A) := by
  have step1 :
      Derives basis
        ((B ++ B) ++ (A ++ A))
        ((A ++ A) ++ (B ++ B)) :=
    derivesSquareCommutation B A
  have step2 :
      Derives basis
        ((A ++ A) ++ (B ++ B))
        (((B ++ A) ++ B) ++ (A ++ A)) :=
    (derivesRetargetF B A).symm
  have step3 :
      Derives basis
        (((B ++ A) ++ B) ++ (A ++ A))
        (((((B ++ A) ++ B) ++ A) ++ A) ++ A) := by
    simpa [Word.append_assoc] using
      Derives.prepend ((B ++ A) ++ B)
        (derivesPowerExpansion A)
  have step4 :
      Derives basis
        (((((B ++ A) ++ B) ++ A) ++ A) ++ A)
        (((((A ++ A) ++ B) ++ A) ++ B) ++ A) := by
    simpa [Word.append_assoc] using
      (derivesSquareCommutation A (B ++ A)).symm
  have finish :
      Derives basis
        (((((A ++ A) ++ B) ++ A) ++ B) ++ A)
        (((A ++ A) ++ B) ++ A) := by
    simpa [Word.append_assoc] using
      Derives.prepend A (derivesSandwichContraction A B)
  exact step1.trans <| step2.trans <| step3.trans <| step4.trans finish

/-- The generalized head-preserving retarget embodied by the concrete
`xyyxy -> xxyx` derivation:
`A B² A B -> A² B A`. -/
theorem derivesEqualHeadRetargetG (A B : Word Nat) :
    Derives basis
      ((((A ++ B) ++ B) ++ A) ++ B)
      (((A ++ A) ++ B) ++ A) :=
  (derivesEqualHeadRetargetGExpose A B).trans
    (derivesEqualHeadRetargetGReplay A B)

/-! ## A same-head counterexample to literal decomposition alignment -/

/-- `xxyx`, with `x = 0` and `y = 1`. -/
def sameHeadAlignmentCounterexampleLeft : Word Nat :=
  ⟨0, [0, 1, 0]⟩

/-- `xyyxy`, with `x = 0` and `y = 1`. -/
def sameHeadAlignmentCounterexampleRight : Word Nat :=
  ⟨0, [1, 1, 0, 1]⟩

/-- The transient `yyxx` square bank used by the constructive replay. -/
def sameHeadAlignmentCounterexampleWorkspace : Word Nat :=
  ⟨1, [1, 0, 0]⟩

theorem sameHeadAlignmentCounterexample_sameHead :
    sameHeadAlignmentCounterexampleLeft.head =
      sameHeadAlignmentCounterexampleRight.head :=
  rfl

/-- Both sides of the counterexample are already fixed by the recursive
normalizer. -/
theorem sameHeadAlignmentCounterexampleLeft_normalized :
    normalizeBrandtWord sameHeadAlignmentCounterexampleLeft =
      sameHeadAlignmentCounterexampleLeft := by
  decide

theorem sameHeadAlignmentCounterexampleRight_normalized :
    normalizeBrandtWord sameHeadAlignmentCounterexampleRight =
      sameHeadAlignmentCounterexampleRight := by
  decide

/-- The left word has an empty excursion followed by the excursion `y`. -/
theorem sameHeadAlignmentCounterexampleLeft_excursions :
    headExcursions sameHeadAlignmentCounterexampleLeft =
      [none, some (Word.singleton 1)] := by
  decide

/-- The right word has one excursion `yy`. -/
theorem sameHeadAlignmentCounterexampleRight_excursions :
    headExcursions sameHeadAlignmentCounterexampleRight =
      [some ⟨1, [1]⟩] := by
  decide

theorem sameHeadAlignmentCounterexampleLeft_trailing :
    headTrailingSegment sameHeadAlignmentCounterexampleLeft = [] := by
  decide

theorem sameHeadAlignmentCounterexampleRight_trailing :
    headTrailingSegment sameHeadAlignmentCounterexampleRight = [1] := by
  decide

/-- The two concrete words have the same full Brandt signature.  Their
adjacency constraints each identify all four endpoint coordinates of `x`
and `y`; the proof records the two directions explicitly. -/
theorem sameHeadAlignmentCounterexample_sameBrandtSignature :
    SameBrandtSignature
      sameHeadAlignmentCounterexampleLeft
      sameHeadAlignmentCounterexampleRight := by
  constructor
  · intro letter
    simp [sameHeadAlignmentCounterexampleLeft,
      sameHeadAlignmentCounterexampleRight, Word.toList]
    omega
  · intro assignment
    constructor
    · constructor
      · intro leftCompatible
        have leftEdges :=
          (compatible_iff_adjacent_endpoint_eq assignment
            sameHeadAlignmentCounterexampleLeft).mp leftCompatible
        have edge00 := leftEdges 0 0 (by decide)
        have edge01 := leftEdges 0 1 (by decide)
        have edge10 := leftEdges 1 0 (by decide)
        have edge11 :
            (assignment 1).2 = (assignment 1).1 :=
          edge10.trans (edge00.symm.trans edge01)
        apply
          (compatible_iff_adjacent_endpoint_eq assignment
            sameHeadAlignmentCounterexampleRight).mpr
        intro source target member
        simp only [sameHeadAlignmentCounterexampleRight,
          Word.adjacentPairs, Word.adjacentPairsFrom, List.mem_cons,
          List.not_mem_nil, or_false, Prod.mk.injEq] at member
        rcases member with
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact edge01
        · exact edge11
        · exact edge10
        · exact edge01
      · intro rightCompatible
        have rightEdges :=
          (compatible_iff_adjacent_endpoint_eq assignment
            sameHeadAlignmentCounterexampleRight).mp rightCompatible
        have edge01 := rightEdges 0 1 (by decide)
        have edge11 := rightEdges 1 1 (by decide)
        have edge10 := rightEdges 1 0 (by decide)
        have edge00 :
            (assignment 0).2 = (assignment 0).1 :=
          edge01.trans (edge11.symm.trans edge10)
        apply
          (compatible_iff_adjacent_endpoint_eq assignment
            sameHeadAlignmentCounterexampleLeft).mpr
        intro source target member
        simp only [sameHeadAlignmentCounterexampleLeft,
          Word.adjacentPairs, Word.adjacentPairsFrom, List.mem_cons,
          List.not_mem_nil, or_false, Prod.mk.injEq] at member
        rcases member with
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact edge00
        · exact edge01
        · exact edge10
    · intro leftCompatible
      have leftEdges :=
        (compatible_iff_adjacent_endpoint_eq assignment
          sameHeadAlignmentCounterexampleLeft).mp leftCompatible
      have finalEquality :=
        (leftEdges 0 0 (by decide)).trans
          (leftEdges 1 0 (by decide)).symm
      exact ⟨rfl, by
        simpa [sameHeadAlignmentCounterexampleLeft,
          sameHeadAlignmentCounterexampleRight, Word.final] using
            finalEquality⟩

/-- Equal literal heads do not align the recursive decompositions, even
after normalization.  In particular, a sound completeness argument must
still construct a derivative of the right word before pairing subproblems. -/
theorem sameHeadAlignmentCounterexample_no_literal_alignment :
    ¬(List.Forall₂ OptionalGapDerives
          (headExcursions
            (normalizeBrandtWord sameHeadAlignmentCounterexampleLeft))
          (headExcursions
            (normalizeBrandtWord sameHeadAlignmentCounterexampleRight)) ∧
        TrailingLettersDerives
          (headTrailingSegment
            (normalizeBrandtWord sameHeadAlignmentCounterexampleLeft))
          (headTrailingSegment
            (normalizeBrandtWord sameHeadAlignmentCounterexampleRight))) := by
  intro aligned
  have trailing := aligned.2
  rw [sameHeadAlignmentCounterexampleLeft_normalized,
    sameHeadAlignmentCounterexampleRight_normalized,
    sameHeadAlignmentCounterexampleLeft_trailing,
    sameHeadAlignmentCounterexampleRight_trailing] at trailing
  cases trailing

/-- The constructive retarget found by the explorer.  This changes the
literal decomposition before any recursive pairing is attempted. -/
theorem derivesSameHeadAlignmentCounterexampleRetarget :
    Derives basis
      sameHeadAlignmentCounterexampleRight
      sameHeadAlignmentCounterexampleLeft := by
  let X := Word.singleton 0
  let Y := Word.singleton 1
  simpa [sameHeadAlignmentCounterexampleLeft,
    sameHeadAlignmentCounterexampleRight, X, Y,
    Word.singleton, Word.append, Word.append_assoc] using
      derivesEqualHeadRetargetG X Y

theorem derivesSameHeadAlignmentCounterexampleExpose :
    Derives basis
      (normalizeBrandtWord sameHeadAlignmentCounterexampleRight)
      sameHeadAlignmentCounterexampleWorkspace := by
  let X := Word.singleton 0
  let Y := Word.singleton 1
  rw [sameHeadAlignmentCounterexampleRight_normalized]
  simpa [sameHeadAlignmentCounterexampleRight,
    sameHeadAlignmentCounterexampleWorkspace, X, Y,
    Word.singleton, Word.append, Word.append_assoc] using
      derivesEqualHeadRetargetGExpose X Y

theorem derivesSameHeadAlignmentCounterexampleReplay :
    Derives basis
      sameHeadAlignmentCounterexampleWorkspace
      sameHeadAlignmentCounterexampleLeft := by
  let X := Word.singleton 0
  let Y := Word.singleton 1
  simpa [sameHeadAlignmentCounterexampleLeft,
    sameHeadAlignmentCounterexampleWorkspace, X, Y,
    Word.singleton, Word.append, Word.append_assoc] using
      derivesEqualHeadRetargetGReplay X Y

theorem sameHeadAlignmentCounterexampleWorkspace_shape :
    HeadAnchoredCommutingSquareBankShape
      sameHeadAlignmentCounterexampleWorkspace.head
      sameHeadAlignmentCounterexampleWorkspace := by
  let X := Word.singleton 0
  let Y := Word.singleton 1
  have workspaceShape :
      sameHeadAlignmentCounterexampleWorkspace =
        retargetContext [] (squaredWalkBank Y [X]) [] := by
    decide
  rw [workspaceShape]
  exact HeadAnchoredCommutingSquareBankShape.bank Y [X] [] rfl

/-! ## Independent audit counterexamples -/

/-- `xyx`, the reflexive witness showing that a square-bank shape cannot be
required of the final retarget: it has one genuine nonempty head gap. -/
def finalBankShapeCounterexample : Word Nat :=
  ⟨0, [1, 0]⟩

/-- `xyxyx`, a valid transient square-bank workspace for the reflexive
`xyx` case. -/
def finalBankShapeCounterexampleWorkspace : Word Nat :=
  ⟨0, [1, 0, 1, 0]⟩

theorem finalBankShapeCounterexample_normalized :
    normalizeBrandtWord finalBankShapeCounterexample =
      finalBankShapeCounterexample := by
  decide

theorem finalBankShapeCounterexample_excursions :
    headExcursions finalBankShapeCounterexample =
      [some (Word.singleton 1)] := by
  decide

theorem finalBankShapeCounterexample_trailing :
    headTrailingSegment finalBankShapeCounterexample = [] := by
  decide

theorem derivesFinalBankShapeCounterexampleExpose :
    Derives basis
      (normalizeBrandtWord finalBankShapeCounterexample)
      finalBankShapeCounterexampleWorkspace := by
  let X := Word.singleton 0
  let Y := Word.singleton 1
  rw [finalBankShapeCounterexample_normalized]
  simpa [finalBankShapeCounterexample,
    finalBankShapeCounterexampleWorkspace, X, Y,
    Word.singleton, Word.append, Word.append_assoc] using
      derivesSandwichExpansion X Y

theorem derivesFinalBankShapeCounterexampleReplay :
    Derives basis
      finalBankShapeCounterexampleWorkspace
      finalBankShapeCounterexample := by
  let X := Word.singleton 0
  let Y := Word.singleton 1
  simpa [finalBankShapeCounterexample,
    finalBankShapeCounterexampleWorkspace, X, Y,
    Word.singleton, Word.append, Word.append_assoc] using
      derivesSandwichContraction X Y

theorem finalBankShapeCounterexampleWorkspace_shape :
    HeadAnchoredCommutingSquareBankShape
      finalBankShapeCounterexampleWorkspace.head
      finalBankShapeCounterexampleWorkspace := by
  let X := Word.singleton 0
  let Y := Word.singleton 1
  have workspaceShape :
      finalBankShapeCounterexampleWorkspace =
        retargetContext [] (squaredWalkBank (X ++ Y) []) [0] := by
    decide
  rw [workspaceShape]
  exact
    HeadAnchoredCommutingSquareBankShape.bank
      (X ++ Y) [] [0] rfl

/-- `xabxbax`; its full Brandt signature agrees with `xabaxbx`, but the
second literal head gaps have different support. -/
def directSemanticGapCounterexampleLeft : Word Nat :=
  ⟨0, [1, 2, 0, 2, 1, 0]⟩

/-- `xabaxbx`. -/
def directSemanticGapCounterexampleRight : Word Nat :=
  ⟨0, [1, 2, 1, 0, 2, 0]⟩

theorem directSemanticGapCounterexample_adjacent_perm :
    directSemanticGapCounterexampleLeft.adjacentPairs.Perm
      directSemanticGapCounterexampleRight.adjacentPairs := by
  decide

theorem directSemanticGapCounterexample_sameBrandtSignature :
    SameBrandtSignature
      directSemanticGapCounterexampleLeft
      directSemanticGapCounterexampleRight := by
  have adjacent := directSemanticGapCounterexample_adjacent_perm
  constructor
  · intro letter
    simp [directSemanticGapCounterexampleLeft,
      directSemanticGapCounterexampleRight, Word.toList]
    omega
  · intro assignment
    constructor
    · rw [compatible_iff_adjacent_endpoint_eq,
        compatible_iff_adjacent_endpoint_eq]
      constructor
      · intro leftCompatible source target rightEdge
        exact leftCompatible source target
          (adjacent.mem_iff.mpr rightEdge)
      · intro rightCompatible source target leftEdge
        exact rightCompatible source target
          (adjacent.mem_iff.mp leftEdge)
    · intro leftCompatible
      exact ⟨rfl, rfl⟩

theorem directSemanticGapCounterexampleLeft_excursions :
    headExcursions directSemanticGapCounterexampleLeft =
      [some ⟨1, [2]⟩, some ⟨2, [1]⟩] := by
  decide

theorem directSemanticGapCounterexampleRight_excursions :
    headExcursions directSemanticGapCounterexampleRight =
      [some ⟨1, [2, 1]⟩, some (Word.singleton 2)] := by
  decide

theorem directSemanticGapCounterexample_trailing :
    headTrailingSegment directSemanticGapCounterexampleLeft = [] ∧
      headTrailingSegment directSemanticGapCounterexampleRight = [] := by
  decide

/-- The `F` source `01011`. -/
def residualPivotCounterexampleRight : Word Nat :=
  ⟨0, [1, 0, 1, 1]⟩

/-- The `F` target `1100`. -/
def residualPivotCounterexampleLeft : Word Nat :=
  ⟨1, [1, 0, 0]⟩

def residualPivotCounterexampleBlock : Word Nat :=
  ⟨0, [1]⟩

def residualPivotCounterexampleResidual : Word Nat :=
  ⟨0, [1, 1]⟩

def residualPivotCounterexampleStep :
    IncomingPivotStep residualPivotCounterexampleRight 0 1 where
  predecessor := 1
  leftEdge := by decide
  rightEdge := by decide

theorem residualPivotCounterexample_factor :
    residualPivotCounterexampleRight =
      residualPivotCounterexampleBlock ++
        residualPivotCounterexampleResidual := by
  decide

theorem residualPivotCounterexample_rightEdge_survives :
    (1, 1) ∈ residualPivotCounterexampleResidual.adjacentPairs := by
  decide

theorem residualPivotCounterexample_no_residual_step :
    IncomingPivotStep residualPivotCounterexampleResidual 0 1 → False := by
  intro step
  have impossible := step.leftEdge
  simp [residualPivotCounterexampleResidual,
    Word.adjacentPairs, Word.adjacentPairsFrom] at impossible

theorem derivesResidualPivotCounterexample :
    Derives basis
      residualPivotCounterexampleRight
      residualPivotCounterexampleLeft := by
  let A := Word.singleton 0
  let B := Word.singleton 1
  simpa [residualPivotCounterexampleRight,
    residualPivotCounterexampleLeft, A, B,
    Word.singleton, Word.append, Word.append_assoc] using
      derivesRetargetF A B

theorem residualPivotCounterexample_sameBrandtSignature :
    SameBrandtSignature
      residualPivotCounterexampleLeft
      residualPivotCounterexampleRight :=
  derives_sameBrandtSignature derivesResidualPivotCounterexample.symm

/-- The counterexample therefore has a valid paired certificate, but only
after the right word is retargeted all the way to the left word. -/
def sameHeadAlignmentCounterexample_pairedDecomposition :
    PairedBrandtDecomposition
      sameHeadAlignmentCounterexampleLeft
      sameHeadAlignmentCounterexampleRight where
  retargeted := sameHeadAlignmentCounterexampleLeft
  rightRetarget := by
    simpa only [sameHeadAlignmentCounterexampleRight_normalized] using
      derivesSameHeadAlignmentCounterexampleExpose.trans
        derivesSameHeadAlignmentCounterexampleReplay
  commonHead := rfl
  gaps := optionalGapDerivesForall₂_refl _
  trailing := TrailingLettersDerives.refl _

def sameHeadAlignmentCounterexample_normalizedPairedDecomposition :
    PairedBrandtDecomposition
      (normalizeBrandtWord sameHeadAlignmentCounterexampleLeft)
      (normalizeBrandtWord sameHeadAlignmentCounterexampleRight) := by
  simpa only [sameHeadAlignmentCounterexampleLeft_normalized,
    sameHeadAlignmentCounterexampleRight_normalized] using
      sameHeadAlignmentCounterexample_pairedDecomposition

/-! ## Explicit support and pivot-residual measures -/

/-- Keep the final occurrence of every letter.  This mirrors the proved
optional-gap deduplicator and provides a verification-oriented support list. -/
def deduplicateBrandtLetters : List Nat → List Nat
  | [] => []
  | letter :: letters =>
      if letter ∈ letters then
        deduplicateBrandtLetters letters
      else
        letter :: deduplicateBrandtLetters letters

theorem mem_deduplicateBrandtLetters (tested : Nat) :
    ∀ letters : List Nat,
      tested ∈ deduplicateBrandtLetters letters ↔ tested ∈ letters
  | [] => by simp [deduplicateBrandtLetters]
  | letter :: letters => by
      by_cases present : letter ∈ letters
      · rw [deduplicateBrandtLetters, if_pos present,
          mem_deduplicateBrandtLetters tested letters]
        constructor
        · exact List.Mem.tail letter
        · intro member
          rcases List.mem_cons.mp member with equal | tailMember
          · subst tested
            exact present
          · exact tailMember
      · simpa [deduplicateBrandtLetters, present,
          mem_deduplicateBrandtLetters tested letters]

theorem deduplicateBrandtLetters_nodup :
    ∀ letters : List Nat,
      (deduplicateBrandtLetters letters).Nodup
  | [] => by simp [deduplicateBrandtLetters]
  | letter :: letters => by
      by_cases present : letter ∈ letters
      · simpa [deduplicateBrandtLetters, present] using
          deduplicateBrandtLetters_nodup letters
      · simp [deduplicateBrandtLetters, present,
          mem_deduplicateBrandtLetters,
          deduplicateBrandtLetters_nodup letters]

/-- Number of distinct variables occurring in a word.  The recursive
certificate below carries strict inequalities explicitly; it never replaces
them by a word-length assumption. -/
def brandtSupportCard (word : Word Nat) : Nat :=
  (deduplicateBrandtLetters word.toList).length

theorem deduplicateBrandtLetters_perm_of_sameSupport
    {left right : List Nat}
    (sameSupport : ∀ tested, tested ∈ left ↔ tested ∈ right) :
    (deduplicateBrandtLetters left).Perm
      (deduplicateBrandtLetters right) := by
  rw [List.perm_iff_count]
  intro tested
  rw [(deduplicateBrandtLetters_nodup left).count,
    (deduplicateBrandtLetters_nodup right).count]
  have support := sameSupport tested
  by_cases leftMember : tested ∈ left
  · have rightMember : tested ∈ right := support.mp leftMember
    simp [mem_deduplicateBrandtLetters, leftMember, rightMember]
  · have rightMember : tested ∉ right :=
      fun member => leftMember (support.mpr member)
    simp [mem_deduplicateBrandtLetters, leftMember, rightMember]

theorem brandtSupportCard_eq_of_sameBrandtSignature
    {left right : Word Nat}
    (same : SameBrandtSignature left right) :
    brandtSupportCard left = brandtSupportCard right :=
  (deduplicateBrandtLetters_perm_of_sameSupport same.1).length_eq

namespace IncomingPivotPath

/-- Number of proof-relevant shared-predecessor steps still to replay. -/
def stepCount {word : Word Nat} {left right : Nat} :
    IncomingPivotPath word left right → Nat
  | .nil _ => 0
  | .cons _ rest => rest.stepCount + 1

end IncomingPivotPath

structure PivotResidualMeasure where
  remainingSteps : Nat
  residualLength : Nat
deriving Repr, DecidableEq

def pivotResidualMeasure
    {word : Word Nat} {left right : Nat}
    (path : IncomingPivotPath word left right)
    (residual : Word Nat) : PivotResidualMeasure :=
  ⟨path.stepCount, residual.toList.length⟩

/-- Strict lexicographic descent: consume a pivot first, or retain the pivot
and shorten the residual word. -/
def PivotResidualMeasure.LexLt
    (next current : PivotResidualMeasure) : Prop :=
  next.remainingSteps < current.remainingSteps ∨
    (next.remainingSteps = current.remainingSteps ∧
      next.residualLength < current.residualLength)

theorem pivotResidualMeasure_pathTail_lt
    {word residual : Word Nat} {left middle right : Nat}
    (step : IncomingPivotStep word left middle)
    (path : IncomingPivotPath word middle right) :
    PivotResidualMeasure.LexLt
      (pivotResidualMeasure path residual)
      (pivotResidualMeasure (IncomingPivotPath.cons step path) residual) :=
  Or.inl (by
    simp [pivotResidualMeasure, IncomingPivotPath.stepCount])

theorem pivotResidualMeasure_shorterResidual_lt
    {word residual nextResidual : Word Nat} {left right : Nat}
    (path : IncomingPivotPath word left right)
    (shorter : nextResidual.toList.length < residual.toList.length) :
    PivotResidualMeasure.LexLt
      (pivotResidualMeasure path nextResidual)
      (pivotResidualMeasure path residual) :=
  Or.inr ⟨rfl, shorter⟩

/-- The residual produced by the exact incoming-head square exposure is
strictly shorter than the source.  This is the second component of the
nested square-bank recursion measure; it does not claim that the paired
pivot edge is present in that residual. -/
theorem existsDerivesExposeSpecificIncomingHeadSquareWithDecrease
    (word : Word Nat) {predecessor : Nat}
    (edge : (predecessor, word.head) ∈ word.adjacentPairs) :
    ∃ block residual : Word Nat,
      block.head = word.head ∧
        block.final = predecessor ∧
          residual.head = word.head ∧
            word = block ++ residual ∧
              Derives basis word ((block ++ block) ++ residual) ∧
                residual.toList.length < word.toList.length := by
  rcases existsDerivesExposeSpecificIncomingHeadSquare word edge with
    ⟨block, residual, blockHead, blockFinal, residualHead,
      sourceFactor, exposure⟩
  have blockPositive : 0 < block.toList.length := by
    cases block
    simp [Word.toList]
  have factorLength :=
    congrArg (fun current : Word Nat => current.toList.length)
      sourceFactor
  have residualShorter :
      residual.toList.length < word.toList.length := by
    simp only [Word.toList_append, List.length_append] at factorLength
    omega
  exact
    ⟨block, residual, blockHead, blockFinal, residualHead,
      sourceFactor, exposure, residualShorter⟩

/-! ## Semantic recursive pairs after an explicit retarget -/

/-- A semantic optional-gap pair below one outer support bound.  Empty gaps
only pair with empty gaps. -/
inductive OptionalGapSameBrandtSignature (bound : Nat) :
    Option (Word Nat) → Option (Word Nat) → Prop
  | none : OptionalGapSameBrandtSignature bound none none
  | some {left right : Word Nat} :
      SameBrandtSignature left right →
        brandtSupportCard left < bound →
          OptionalGapSameBrandtSignature bound (some left) (some right)

/-- The second gaps in `xabxbax` and `xabaxbx` cannot be paired by the
semantic recursive relation: `ba` contains `a`, while `b` does not. -/
theorem directSemanticGapCounterexample_secondGap_not_related
    (bound : Nat) :
    ¬ OptionalGapSameBrandtSignature bound
        (some ⟨2, [1]⟩) (some (Word.singleton 2)) := by
  intro related
  cases related with
  | some same smaller =>
      have support := same.1 1
      simp [Word.toList, Word.singleton] at support

/-- A semantic trailing pair below one outer support bound. -/
inductive TrailingLettersSameBrandtSignature (bound : Nat) :
    List Nat → List Nat → Prop
  | nil : TrailingLettersSameBrandtSignature bound [] []
  | nonempty {leftHead rightHead : Nat}
      {leftTail rightTail : List Nat} :
      SameBrandtSignature
          ⟨leftHead, leftTail⟩ ⟨rightHead, rightTail⟩ →
        brandtSupportCard ⟨leftHead, leftTail⟩ < bound →
          TrailingLettersSameBrandtSignature bound
            (leftHead :: leftTail) (rightHead :: rightTail)

theorem OptionalGapSameBrandtSignature.toDerives
    {bound : Nat} {left right : Option (Word Nat)}
    (related : OptionalGapSameBrandtSignature bound left right)
    (recurse :
      ∀ {source target : Word Nat},
        SameBrandtSignature source target →
          brandtSupportCard source < bound →
            Derives basis source target) :
    OptionalGapDerives left right := by
  cases related with
  | none => exact OptionalGapDerives.none
  | some same smaller =>
      exact OptionalGapDerives.some (recurse same smaller)

theorem optionalGapSameBrandtSignatureForall₂_toDerives
    {bound : Nat} {left right : List (Option (Word Nat))}
    (related :
      List.Forall₂ (OptionalGapSameBrandtSignature bound) left right)
    (recurse :
      ∀ {source target : Word Nat},
        SameBrandtSignature source target →
          brandtSupportCard source < bound →
            Derives basis source target) :
    List.Forall₂ OptionalGapDerives left right := by
  induction related with
  | nil => exact List.Forall₂.nil
  | @cons gapLeft gapRight leftRest rightRest
      gapRelated restRelated ih =>
      exact List.Forall₂.cons
        (gapRelated.toDerives recurse) ih

theorem TrailingLettersSameBrandtSignature.toDerives
    {bound : Nat} {left right : List Nat}
    (related : TrailingLettersSameBrandtSignature bound left right)
    (recurse :
      ∀ {source target : Word Nat},
        SameBrandtSignature source target →
          brandtSupportCard source < bound →
            Derives basis source target) :
    TrailingLettersDerives left right := by
  cases related with
  | nil => exact TrailingLettersDerives.nil
  | nonempty same smaller =>
      exact TrailingLettersDerives.nonempty (recurse same smaller)

/-- Corrected recursive certificate.  Even when the displayed heads already
agree, the right word must first be derivably retargeted/rearranged.  Only
the resulting recursive pieces are paired semantically. -/
structure PairedBrandtSignatureDecomposition
    (bound : Nat) (left right : Word Nat) : Type where
  retargeted : Word Nat
  rightRetarget : Derives basis right retargeted
  commonHead : left.head = retargeted.head
  gaps :
    List.Forall₂ (OptionalGapSameBrandtSignature bound)
      (headExcursions left) (headExcursions retargeted)
  trailing :
    TrailingLettersSameBrandtSignature bound
      (headTrailingSegment left)
      (headTrailingSegment retargeted)

def PairedBrandtSignatureDecomposition.toPaired
    {bound : Nat} {left right : Word Nat}
    (paired : PairedBrandtSignatureDecomposition bound left right)
    (recurse :
      ∀ {source target : Word Nat},
        SameBrandtSignature source target →
          brandtSupportCard source < bound →
            Derives basis source target) :
    PairedBrandtDecomposition left right where
  retargeted := paired.retargeted
  rightRetarget := paired.rightRetarget
  commonHead := paired.commonHead
  gaps := optionalGapSameBrandtSignatureForall₂_toDerives
    paired.gaps recurse
  trailing := paired.trailing.toDerives recurse

/-- Square-bank provenance for the corrected semantic certificate. -/
structure PairedSemanticSquareBankDecomposition
    (bound : Nat) (left right : Word Nat) : Type where
  path : IncomingPivotPath right right.head left.head
  exposure : IncomingPivotPathSquareBankExposure right right path
  retargeted : Word Nat
  replay : IncomingPivotPathSquareBankReplay exposure retargeted
  gaps :
    List.Forall₂ (OptionalGapSameBrandtSignature bound)
      (headExcursions left) (headExcursions retargeted)
  trailing :
    TrailingLettersSameBrandtSignature bound
      (headTrailingSegment left)
      (headTrailingSegment retargeted)

def PairedSemanticSquareBankDecomposition.toSemanticRetarget
    {bound : Nat} {left right : Word Nat}
    (paired : PairedSemanticSquareBankDecomposition bound left right) :
    PairedBrandtSignatureDecomposition bound left right where
  retargeted := paired.retargeted
  rightRetarget := paired.replay.derivation
  commonHead := paired.replay.targetHead.symm
  gaps := paired.gaps
  trailing := paired.trailing

theorem sameBrandtSignature_refl (word : Word Nat) :
    SameBrandtSignature word word :=
  derives_sameBrandtSignature (Derives.refl word)

/-! ## Equal-head transient-bank replay branch -/

/-- A square bank is only a transient workspace.  After exposure, replay is
free to leave the bank and produce the final common-head retarget whose
recursive pieces are paired semantically with the left word. -/
structure EqualHeadBankReplayDecomposition
    (bound : Nat) (left right : Word Nat) : Type where
  workspace : Word Nat
  retargeted : Word Nat
  expose : Derives basis (normalizeBrandtWord right) workspace
  workspaceShape :
    HeadAnchoredCommutingSquareBankShape workspace.head workspace
  replay : Derives basis workspace retargeted
  commonHead : left.head = retargeted.head
  gaps :
    List.Forall₂ (OptionalGapSameBrandtSignature bound)
      (headExcursions left) (headExcursions retargeted)
  trailing :
    TrailingLettersSameBrandtSignature bound
      (headTrailingSegment left)
      (headTrailingSegment retargeted)

def EqualHeadBankReplayDecomposition.toSemanticRetarget
    {bound : Nat} {left right : Word Nat}
    (paired : EqualHeadBankReplayDecomposition bound left right) :
    PairedBrandtSignatureDecomposition bound left right where
  retargeted := paired.retargeted
  rightRetarget :=
    ((derivesNormalizeBrandtWord right).trans paired.expose).trans
      paired.replay
  commonHead := paired.commonHead
  gaps := paired.gaps
  trailing := paired.trailing

/-- The rejected reflexive `xyx` case is accepted by the corrected
interface: `xyxyx` is transient, while the final semantic retarget is the
original one-gap word. -/
def finalBankShapeCounterexample_equalHeadBankReplay :
    EqualHeadBankReplayDecomposition
      (brandtSupportCard finalBankShapeCounterexample)
      finalBankShapeCounterexample finalBankShapeCounterexample := by
  have gapSmaller :
      brandtSupportCard (Word.singleton 1) <
        brandtSupportCard finalBankShapeCounterexample := by
    decide
  refine
    { workspace := finalBankShapeCounterexampleWorkspace
      retargeted := finalBankShapeCounterexample
      expose := derivesFinalBankShapeCounterexampleExpose
      workspaceShape := finalBankShapeCounterexampleWorkspace_shape
      replay := derivesFinalBankShapeCounterexampleReplay
      commonHead := rfl
      gaps := ?_
      trailing := ?_ }
  · rw [finalBankShapeCounterexample_excursions]
    exact
      List.Forall₂.cons
        (OptionalGapSameBrandtSignature.some
          (sameBrandtSignature_refl (Word.singleton 1)) gapSmaller)
        List.Forall₂.nil
  · rw [finalBankShapeCounterexample_trailing]
    exact TrailingLettersSameBrandtSignature.nil

/-- The concrete counterexample uses `yyxx` only as a workspace.  Replay
then leaves that bank and reaches `xxyx`, where the recursive witnesses are
reflexive. -/
def sameHeadAlignmentCounterexample_equalHeadBankReplay :
    EqualHeadBankReplayDecomposition
      (brandtSupportCard sameHeadAlignmentCounterexampleLeft)
      sameHeadAlignmentCounterexampleLeft
      sameHeadAlignmentCounterexampleRight := by
  have gapSmaller :
      brandtSupportCard (Word.singleton 1) <
        brandtSupportCard sameHeadAlignmentCounterexampleLeft := by
    decide
  refine
    { workspace := sameHeadAlignmentCounterexampleWorkspace
      retargeted := sameHeadAlignmentCounterexampleLeft
      expose := derivesSameHeadAlignmentCounterexampleExpose
      workspaceShape :=
        sameHeadAlignmentCounterexampleWorkspace_shape
      replay := derivesSameHeadAlignmentCounterexampleReplay
      commonHead := rfl
      gaps := ?_
      trailing := ?_ }
  · rw [sameHeadAlignmentCounterexampleLeft_excursions]
    exact
      List.Forall₂.cons
        OptionalGapSameBrandtSignature.none
        (List.Forall₂.cons
          (OptionalGapSameBrandtSignature.some
            (sameBrandtSignature_refl (Word.singleton 1))
            gapSmaller)
          List.Forall₂.nil)
  · rw [sameHeadAlignmentCounterexampleLeft_trailing]
    exact TrailingLettersSameBrandtSignature.nil

/-- Honest equal-head residual: construct both halves around a transient
bank, then align only the final retarget with the left decomposition. -/
def EqualHeadBankReplayCompleteness : Type :=
  ∀ left right : Word Nat,
    SameBrandtSignature left right →
      left.head = right.head →
        EqualHeadBankReplayDecomposition
          (brandtSupportCard left) left right

/-- Conditional closure of exactly the corrected equal-head branch. -/
def pairedSemanticRetarget_of_equalHeadBankReplay
    (complete : EqualHeadBankReplayCompleteness)
    {left right : Word Nat}
    (same : SameBrandtSignature left right)
    (sameHead : left.head = right.head) :
    PairedBrandtSignatureDecomposition
      (brandtSupportCard left) left right :=
  (complete left right same sameHead).toSemanticRetarget

/-- The strictly corrected local residual.  It asks only for the explicit
retarget and smaller semantic pairs; strong support induction below supplies
all recursive `Derives` witnesses. -/
def PairedSemanticRetargetCompleteness : Type :=
  ∀ left right : Word Nat,
    SameBrandtSignature left right →
      PairedBrandtSignatureDecomposition
        (brandtSupportCard left) left right

/-- Once the corrected semantic-retarget certificate is available at every
support size, strong induction turns its smaller semantic subpairs into
derivations and closes the original two-word derivation. -/
theorem derives_of_pairedSemanticRetargetCompleteness
    (complete : PairedSemanticRetargetCompleteness)
    {left right : Word Nat}
    (same : SameBrandtSignature left right) :
    Derives basis left right := by
  have completeAtSupport :
      ∀ bound left right,
        brandtSupportCard left = bound →
          SameBrandtSignature left right →
            Derives basis left right := by
    intro bound
    induction bound using Nat.strongRecOn with
    | ind currentBound induction =>
        intro currentLeft currentRight supportEq currentSame
        have semantic := complete currentLeft currentRight currentSame
        have paired :
            PairedBrandtDecomposition currentLeft currentRight :=
          semantic.toPaired <| by
            intro source target sourceSame sourceSmaller
            have sourceSmaller' :
                brandtSupportCard source < currentBound := by
              simpa [supportEq] using sourceSmaller
            exact induction (brandtSupportCard source) sourceSmaller'
              source target rfl sourceSame
        exact paired.derives
  exact completeAtSupport
    (brandtSupportCard left) left right rfl same

end SemigroupBasis.CoRoots.S5_415
