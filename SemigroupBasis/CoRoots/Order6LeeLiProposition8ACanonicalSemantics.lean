import SemigroupBasis.CoRoots.Order6LeeLiProposition8ACanonicalization
import SemigroupBasis.CoRoots.Order6LeeLiProposition8ASemanticTransfer

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6LeeLiProposition8A

open SemigroupBasis

namespace Proposition8ACanonical

private instance instDecidableBinaryCompletePrecedence
    (letters : List (Fin 2)) :
    Decidable (Semantics.BinaryCompletePrecedence letters) := by
  unfold Semantics.BinaryCompletePrecedence
  infer_instance

/-- A literal binary cube remains visible after any binary prefix. -/
private theorem binaryHasTripleBlock_append_cube
    (bit : Fin 2) :
    ∀ (before after : List (Fin 2)),
      Semantics.binaryHasTripleBlock bit
          (before ++ [bit, bit, bit] ++ after) = true
  | [], after => by
      simp [Semantics.binaryHasTripleBlock]
  | first :: rest, after => by
      have tailCube :
          Semantics.binaryHasTripleBlock bit
            (rest ++ [bit, bit, bit] ++ after) = true :=
        binaryHasTripleBlock_append_cube bit rest after
      change (((first :: (rest ++ [bit, bit, bit] ++ after)).take 3 ==
        [bit, bit, bit]) || Semantics.binaryHasTripleBlock bit
          (rest ++ [bit, bit, bit] ++ after)) = true
      rw [tailCube]
      simp only [Bool.or_true]

/-- Conditions III and IV make every ordered two-letter projection ready for
the finite semantic classifier. -/
theorem projectionReady
    {letters : List Nat}
    (canonical : Proposition8ACanonical letters) :
    Semantics.CanonicalProjectionReady letters := by
  intro x y different
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [SemanticTransfer.pairProjection_count_zero]
    exact canonical.capThree x
  · rw [SemanticTransfer.pairProjection_count_one letters different]
    exact canonical.capThree y
  · intro projectedThree
    have originalThree : letters.count x = 3 := by
      rw [← SemanticTransfer.pairProjection_count_zero letters x y]
      exact projectedThree
    obtain ⟨before, after, shape⟩ :=
      canonical.cubeContiguous x originalThree
    rw [shape]
    simpa [Semantics.pairProjection] using
      binaryHasTripleBlock_append_cube (0 : Fin 2)
        (Semantics.pairProjection before x y)
        (Semantics.pairProjection after x y)
  · intro projectedThree
    have originalThree : letters.count y = 3 := by
      rw [← SemanticTransfer.pairProjection_count_one letters different]
      exact projectedThree
    obtain ⟨before, after, shape⟩ :=
      canonical.cubeContiguous y originalThree
    rw [shape]
    simpa [Semantics.pairProjection, Ne.symm different] using
      binaryHasTripleBlock_append_cube (1 : Fin 2)
        (Semantics.pairProjection before x y)
        (Semantics.pairProjection after x y)

/-! ## Excluding the two finite exceptional families -/

private def swapBit (bit : Fin 2) : Fin 2 :=
  if bit = 0 then 1 else 0

/-- Reversing the queried ordered pair swaps the two binary letters. -/
private theorem pairProjection_swap
    (letters : List Nat) {x y : Nat} (different : x ≠ y) :
    Semantics.pairProjection letters y x =
      (Semantics.pairProjection letters x y).map swapBit := by
  induction letters with
  | nil => rfl
  | cons letter rest induction =>
      simp only [Semantics.pairProjection] at induction ⊢
      by_cases isX : letter = x
      · subst letter
        simp [Semantics.pairProjection, swapBit, different,
          Ne.symm different, induction]
      · by_cases isY : letter = y
        · subst letter
          simp [Semantics.pairProjection, swapBit, isX, different,
            Ne.symm different, induction]
        · simp [Semantics.pairProjection, swapBit, isX, isY,
            induction]

private theorem exceptional23_impossible
    {ordered straddled : List Nat}
    (orderedCanonical : Proposition8ACanonical ordered)
    (straddledCanonical : Proposition8ACanonical straddled)
    {x y : Nat} (different : x ≠ y)
    (orderedXY : S5_841.CompletePrecedenceList ordered x y)
    (straddledXTwo : straddled.count x = 2)
    (straddledYThree : straddled.count y = 3)
    (notStraddledXY :
      ¬ S5_841.CompletePrecedenceList straddled x y)
    (notStraddledYX :
      ¬ S5_841.CompletePrecedenceList straddled y x)
    (transferSmall :
      ∀ {first second : Nat}, first ≠ second →
        (ordered.count second ≤ 2 ∨ straddled.count second ≤ 2) →
        (S5_841.CompletePrecedenceList ordered first second ↔
          S5_841.CompletePrecedenceList straddled first second)) :
    False := by
  obtain ⟨z, xNeZ, yNeZ, zSmall, straddledYZ,
      notStraddledXZ⟩ :=
    straddledCanonical.straddledCubeWitness different
      straddledXTwo straddledYThree notStraddledXY notStraddledYX
  have yzTransfer := transferSmall yNeZ (Or.inr zSmall)
  have xzTransfer := transferSmall xNeZ (Or.inr zSmall)
  have orderedYZ :
      S5_841.CompletePrecedenceList ordered y z :=
    yzTransfer.mpr straddledYZ
  have notOrderedXZ :
      ¬ S5_841.CompletePrecedenceList ordered x z := by
    intro orderedXZ
    exact notStraddledXZ (xzTransfer.mp orderedXZ)
  exact notOrderedXZ <|
    SemanticTransfer.completePrecedenceList_trans
      xNeZ orderedXY orderedYZ

private theorem exceptional33_impossible
    {forward backward : List Nat}
    (forwardCanonical : Proposition8ACanonical forward)
    (backwardCanonical : Proposition8ACanonical backward)
    {x y : Nat} (different : x ≠ y)
    (forwardXThree : forward.count x = 3)
    (forwardYThree : forward.count y = 3)
    (backwardXThree : backward.count x = 3)
    (backwardYThree : backward.count y = 3)
    (forwardXY : S5_841.CompletePrecedenceList forward x y)
    (backwardYX : S5_841.CompletePrecedenceList backward y x)
    (transferSmall :
      ∀ {first second : Nat}, first ≠ second →
        (forward.count second ≤ 2 ∨ backward.count second ≤ 2) →
        (S5_841.CompletePrecedenceList forward first second ↔
          S5_841.CompletePrecedenceList backward first second)) :
    False := by
  rcases forwardCanonical.orderedCubePairWitnessOrLt different
      forwardXThree forwardYThree forwardXY with
    forwardWitness | xLtY
  · obtain ⟨z, xNeZ, yNeZ, zSmall, forwardXZ,
        notForwardYZ⟩ := forwardWitness
    have xzTransfer := transferSmall xNeZ (Or.inl zSmall)
    have yzTransfer := transferSmall yNeZ (Or.inl zSmall)
    have backwardXZ :
        S5_841.CompletePrecedenceList backward x z :=
      xzTransfer.mp forwardXZ
    have notBackwardYZ :
        ¬ S5_841.CompletePrecedenceList backward y z := by
      intro backwardYZ
      exact notForwardYZ (yzTransfer.mpr backwardYZ)
    exact notBackwardYZ <|
      SemanticTransfer.completePrecedenceList_trans
        yNeZ backwardYX backwardXZ
  · rcases backwardCanonical.orderedCubePairWitnessOrLt
        (Ne.symm different) backwardYThree backwardXThree backwardYX with
      backwardWitness | yLtX
    · obtain ⟨z, yNeZ, xNeZ, zSmall, backwardYZ,
          notBackwardXZ⟩ := backwardWitness
      have yzTransfer := transferSmall yNeZ (Or.inr zSmall)
      have xzTransfer := transferSmall xNeZ (Or.inr zSmall)
      have forwardYZ :
          S5_841.CompletePrecedenceList forward y z :=
        yzTransfer.mpr backwardYZ
      have notForwardXZ :
          ¬ S5_841.CompletePrecedenceList forward x z := by
        intro forwardXZ
        exact notBackwardXZ (xzTransfer.mp forwardXZ)
      exact notForwardXZ <|
        SemanticTransfer.completePrecedenceList_trans
          xNeZ forwardXY forwardYZ
    · omega

/-- Conditions V and VI exclude both classifier exception families for every
ordered pair of variables on the two canonical sides of a valid identity. -/
theorem canonicalExceptionsExcluded
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy publishedTable.semigroup)
    (leftCanonical :
      Proposition8ACanonical identity.lhs.toList)
    (rightCanonical :
      Proposition8ACanonical identity.rhs.toList) :
    Semantics.CanonicalExceptionsExcluded
      identity.lhs.toList identity.rhs.toList := by
  let left := identity.lhs.toList
  let right := identity.rhs.toList
  have leftReady : Semantics.CanonicalProjectionReady left :=
    leftCanonical.projectionReady
  have rightReady : Semantics.CanonicalProjectionReady right :=
    rightCanonical.projectionReady
  have transferLeftRight :
      ∀ {first second : Nat}, first ≠ second →
        (left.count second ≤ 2 ∨ right.count second ≤ 2) →
        (S5_841.CompletePrecedenceList left first second ↔
          S5_841.CompletePrecedenceList right first second) := by
    intro first second different small
    exact SemanticTransfer.validCP_iff_of_second_count_le_two
      identity valid leftReady rightReady different small
  have transferRightLeft :
      ∀ {first second : Nat}, first ≠ second →
        (right.count second ≤ 2 ∨ left.count second ≤ 2) →
        (S5_841.CompletePrecedenceList right first second ↔
          S5_841.CompletePrecedenceList left first second) := by
    intro first second different small
    rcases small with rightSmall | leftSmall
    · exact (SemanticTransfer.validCP_iff_of_second_count_le_two
        identity valid leftReady rightReady different
          (Or.inr rightSmall)).symm
    · exact (SemanticTransfer.validCP_iff_of_second_count_le_two
        identity valid leftReady rightReady different
          (Or.inl leftSmall)).symm
  intro x y different exceptional
  unfold Semantics.BinaryExceptionalPair Semantics.binaryPairMatches at exceptional
  rcases exceptional with exceptional23 | exceptional33
  · rcases exceptional23 with direct | reversed
    · rcases direct with ⟨leftShape, rightShape⟩
      have leftXY : S5_841.CompletePrecedenceList left x y := by
        rw [Semantics.completePrecedenceList_iff_binaryProjection different,
          leftShape]
        decide
      have rightXTwo : right.count x = 2 := by
        rw [← SemanticTransfer.pairProjection_count_zero right x y,
          rightShape]
        decide
      have rightYThree : right.count y = 3 := by
        rw [← SemanticTransfer.pairProjection_count_one right different,
          rightShape]
        decide
      have notRightXY :
          ¬ S5_841.CompletePrecedenceList right x y := by
        rw [Semantics.completePrecedenceList_iff_binaryProjection different,
          rightShape]
        decide
      have notRightYX :
          ¬ S5_841.CompletePrecedenceList right y x := by
        rw [Semantics.completePrecedenceList_iff_binaryProjection
          (Ne.symm different)]
        rw [pairProjection_swap right different, rightShape]
        decide
      exact exceptional23_impossible leftCanonical rightCanonical different
        leftXY rightXTwo rightYThree notRightXY notRightYX
          transferLeftRight
    · rcases reversed with ⟨leftShape, rightShape⟩
      have rightXY : S5_841.CompletePrecedenceList right x y := by
        rw [Semantics.completePrecedenceList_iff_binaryProjection different,
          rightShape]
        decide
      have leftXTwo : left.count x = 2 := by
        rw [← SemanticTransfer.pairProjection_count_zero left x y,
          leftShape]
        decide
      have leftYThree : left.count y = 3 := by
        rw [← SemanticTransfer.pairProjection_count_one left different,
          leftShape]
        decide
      have notLeftXY :
          ¬ S5_841.CompletePrecedenceList left x y := by
        rw [Semantics.completePrecedenceList_iff_binaryProjection different,
          leftShape]
        decide
      have notLeftYX :
          ¬ S5_841.CompletePrecedenceList left y x := by
        rw [Semantics.completePrecedenceList_iff_binaryProjection
          (Ne.symm different)]
        rw [pairProjection_swap left different, leftShape]
        decide
      exact exceptional23_impossible rightCanonical leftCanonical different
        rightXY leftXTwo leftYThree notLeftXY notLeftYX transferRightLeft
  · rcases exceptional33 with direct | reversed
    · rcases direct with ⟨leftShape, rightShape⟩
      have leftXThree : left.count x = 3 := by
        rw [← SemanticTransfer.pairProjection_count_zero left x y,
          leftShape]
        decide
      have leftYThree : left.count y = 3 := by
        rw [← SemanticTransfer.pairProjection_count_one left different,
          leftShape]
        decide
      have rightXThree : right.count x = 3 := by
        rw [← SemanticTransfer.pairProjection_count_zero right x y,
          rightShape]
        decide
      have rightYThree : right.count y = 3 := by
        rw [← SemanticTransfer.pairProjection_count_one right different,
          rightShape]
        decide
      have leftXY : S5_841.CompletePrecedenceList left x y := by
        rw [Semantics.completePrecedenceList_iff_binaryProjection different,
          leftShape]
        decide
      have rightYX : S5_841.CompletePrecedenceList right y x := by
        rw [Semantics.completePrecedenceList_iff_binaryProjection
          (Ne.symm different)]
        rw [pairProjection_swap right different, rightShape]
        decide
      exact exceptional33_impossible leftCanonical rightCanonical different
        leftXThree leftYThree rightXThree rightYThree leftXY rightYX
          transferLeftRight
    · rcases reversed with ⟨leftShape, rightShape⟩
      have rightXThree : right.count x = 3 := by
        rw [← SemanticTransfer.pairProjection_count_zero right x y,
          rightShape]
        decide
      have rightYThree : right.count y = 3 := by
        rw [← SemanticTransfer.pairProjection_count_one right different,
          rightShape]
        decide
      have leftXThree : left.count x = 3 := by
        rw [← SemanticTransfer.pairProjection_count_zero left x y,
          leftShape]
        decide
      have leftYThree : left.count y = 3 := by
        rw [← SemanticTransfer.pairProjection_count_one left different,
          leftShape]
        decide
      have rightXY : S5_841.CompletePrecedenceList right x y := by
        rw [Semantics.completePrecedenceList_iff_binaryProjection different,
          rightShape]
        decide
      have leftYX : S5_841.CompletePrecedenceList left y x := by
        rw [Semantics.completePrecedenceList_iff_binaryProjection
          (Ne.symm different)]
        rw [pairProjection_swap left different, leftShape]
        decide
      exact exceptional33_impossible rightCanonical leftCanonical different
        rightXThree rightYThree leftXThree leftYThree rightXY leftYX
          transferRightLeft

/-- Complete precedence is identical on the two canonical sides of every
identity valid in the published monoid. -/
theorem canonicalCompletePrecedence
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy publishedTable.semigroup)
    (leftCanonical :
      Proposition8ACanonical identity.lhs.toList)
    (rightCanonical :
      Proposition8ACanonical identity.rhs.toList) :
    ∀ x y,
      S5_841.CompletePrecedenceList identity.lhs.toList x y ↔
        S5_841.CompletePrecedenceList identity.rhs.toList x y := by
  exact validCanonicalCompletePrecedence identity valid
    leftCanonical.projectionReady rightCanonical.projectionReady
    (canonicalExceptionsExcluded identity valid leftCanonical rightCanonical)

end Proposition8ACanonical

end SemigroupBasis.CoRoots.Order6LeeLiProposition8A
