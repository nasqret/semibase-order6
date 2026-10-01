import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0456FordNilAssembly
import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0456FordNilSeparatorOrder

/-! Literal canonicity of the amended B23 separator skeleton. Global first
order determines the new introductions in each gap; M18 prefix parity
determines the flip bits. This is an unrestricted induction on the actual
simple-separator decompositions, not a bounded render comparison. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.FordNil

open SemigroupBasis
open SemigroupBasis.Examples

theorem simpleSeparator_not_mem_before (whole prefixWords tail : List Nat) (separator : Nat)
    (shape : whole = prefixWords ++ separator :: tail) (simple : whole.count separator = 1) :
    separator ∉ prefixWords := by
  intro member
  have positive := List.count_pos_iff.mpr member
  rw [shape, List.count_append, List.count_cons_self] at simple
  omega

theorem canonicalSkeletonAlignmentAux {left right : Word Nat} (same : SameSignature left right)
    {leftSource rightSource : List Nat}
    {leftSegments rightSegments : List (List Nat × Nat)} {leftFinal rightFinal : List Nat}
    (leftDecomposition : S5_254.GloballySimpleSeparatorDecomposition
      left.toList leftSource leftSegments leftFinal)
    (rightDecomposition : S5_254.GloballySimpleSeparatorDecomposition
      right.toList rightSource rightSegments rightFinal)
    (leftPrefix rightPrefix common : List Nat)
    (leftShape : left.toList = leftPrefix ++ leftSource)
    (rightShape : right.toList = rightPrefix ++ rightSource)
    (prefixParity : ∀ tested, leftPrefix.count tested % 2 = rightPrefix.count tested % 2)
    (prefixOrder : firstOccurrenceSequence leftPrefix = firstOccurrenceSequence rightPrefix)
    (leftSeen : ∀ tested, tested ∈ common ↔ tested ∈ leftPrefix)
    (rightSeen : ∀ tested, tested ∈ common ↔ tested ∈ rightPrefix)
    (separatorEq : leftSegments.map Prod.snd = rightSegments.map Prod.snd) :
    canonicalSkeleton common leftSegments leftFinal = canonicalSkeleton common rightSegments rightFinal := by
  induction leftDecomposition generalizing rightSource rightSegments rightFinal leftPrefix rightPrefix common with
  | final leftGap leftRepeated =>
      cases rightDecomposition with
      | final rightGap rightRepeated =>
          have parity : ∀ tested, leftGap.count tested % 2 = rightSource.count tested % 2 := by
            intro tested
            have total := same.m18.totalParity tested
            have before := prefixParity tested
            rw [leftShape, rightShape, List.count_append, List.count_append] at total
            omega
          have fullOrder := same.firstOrder
          rw [leftShape, rightShape] at fullOrder
          have order := freshGap_order_of_prefixes common leftPrefix rightPrefix leftGap rightSource
            leftSeen rightSeen prefixOrder fullOrder
          exact canonicalGap_eq common common leftGap rightSource (fun _ => Iff.rfl) parity order
      | step rightGap rightSeparator rightRemainder rightRest rightFinal
          rightSeparatorSimple rightRepeated rightTail =>
          simp at separatorEq
  | step leftGap leftSeparator leftRemainder leftRest leftFinal
      leftSeparatorSimple leftRepeated leftTail induction =>
      cases rightDecomposition with
      | final rightGap rightRepeated =>
          simp at separatorEq
      | step rightGap rightSeparator rightRemainder rightRest rightFinal
          rightSeparatorSimple rightRepeated rightTail =>
          simp only [List.map_cons, List.cons.injEq] at separatorEq
          obtain ⟨separatorHeadEq, separatorTailEq⟩ := separatorEq
          subst rightSeparator
          have leftBeforeShape : left.toList = (leftPrefix ++ leftGap) ++ leftSeparator :: leftRemainder := by
            rw [leftShape]
            simp [List.append_assoc]
          have rightBeforeShape : right.toList = (rightPrefix ++ rightGap) ++ leftSeparator :: rightRemainder := by
            rw [rightShape]
            simp [List.append_assoc]
          have leftAbsent := simpleSeparator_not_mem_before left.toList (leftPrefix ++ leftGap)
            leftRemainder leftSeparator leftBeforeShape leftSeparatorSimple
          have rightAbsent := simpleSeparator_not_mem_before right.toList (rightPrefix ++ rightGap)
            rightRemainder leftSeparator rightBeforeShape rightSeparatorSimple
          have beforeOrder : firstOccurrenceSequence (leftPrefix ++ leftGap) =
              firstOccurrenceSequence (rightPrefix ++ rightGap) := by
            apply firstOrder_before_separator (leftPrefix ++ leftGap) (rightPrefix ++ rightGap)
              leftRemainder rightRemainder leftSeparator leftAbsent rightAbsent
            rw [← leftBeforeShape, ← rightBeforeShape]
            exact same.firstOrder
          have gapOrder := freshGap_order_of_prefixes common leftPrefix rightPrefix leftGap rightGap
            leftSeen rightSeen prefixOrder beforeOrder
          have cumulativeParity : ∀ tested,
              (leftPrefix ++ leftGap).count tested % 2 = (rightPrefix ++ rightGap).count tested % 2 := by
            intro tested
            have values := same.m18.prefixValue_eq leftSeparator tested leftSeparatorSimple rightSeparatorSimple
            rw [S5_254.simplePrefixBefore_eq_of_split leftSeparatorSimple
                (leftPrefix ++ leftGap) leftRemainder leftBeforeShape,
              S5_254.simplePrefixBefore_eq_of_split rightSeparatorSimple
                (rightPrefix ++ rightGap) rightRemainder rightBeforeShape] at values
            exact values
          have gapParity : ∀ tested, leftGap.count tested % 2 = rightGap.count tested % 2 := by
            intro tested
            have cumulative := cumulativeParity tested
            have before := prefixParity tested
            simp only [List.count_append] at cumulative
            omega
          have headEq := canonicalGap_eq common common leftGap rightGap (fun _ => Iff.rfl) gapParity gapOrder
          have nextPrefixParity : ∀ tested,
              (leftPrefix ++ leftGap ++ [leftSeparator]).count tested % 2 =
                (rightPrefix ++ rightGap ++ [leftSeparator]).count tested % 2 := by
            intro tested
            have cumulative := cumulativeParity tested
            simp only [List.count_append, List.count_cons, List.count_nil] at cumulative ⊢
            omega
          have nextPrefixOrder : firstOccurrenceSequence (leftPrefix ++ leftGap ++ [leftSeparator]) =
              firstOccurrenceSequence (rightPrefix ++ rightGap ++ [leftSeparator]) := by
            rw [firstOrder_append_fresh_separator (leftPrefix ++ leftGap) leftSeparator leftAbsent,
              firstOrder_append_fresh_separator (rightPrefix ++ rightGap) leftSeparator rightAbsent, beforeOrder]
          have leftNextSeen := seen_after_canonicalGap common leftPrefix leftGap leftSeparator leftSeen
          have rightNextSeen : ∀ tested,
              tested ∈ common ++ canonicalGap common leftGap ++ [leftSeparator] ↔
                tested ∈ rightPrefix ++ rightGap ++ [leftSeparator] := by
            rw [headEq]
            exact seen_after_canonicalGap common rightPrefix rightGap leftSeparator rightSeen
          have leftTailShape : left.toList = (leftPrefix ++ leftGap ++ [leftSeparator]) ++ leftRemainder := by
            rw [leftShape]
            simp [List.append_assoc]
          have rightTailShape : right.toList = (rightPrefix ++ rightGap ++ [leftSeparator]) ++ rightRemainder := by
            rw [rightShape]
            simp [List.append_assoc]
          have tailEq := induction rightTail
            (leftPrefix ++ leftGap ++ [leftSeparator]) (rightPrefix ++ rightGap ++ [leftSeparator])
            (common ++ canonicalGap common leftGap ++ [leftSeparator])
            leftTailShape rightTailShape nextPrefixParity nextPrefixOrder leftNextSeen rightNextSeen separatorTailEq
          simpa only [canonicalSkeleton, ← headEq] using
            congrArg (fun tail => canonicalGap common leftGap ++ leftSeparator :: tail) tailEq

/-- Signature equality forces literal equality of the complete first-order
separator skeletons selected from any valid decompositions. -/
theorem canonicalSkeleton_eq_of_sameSignature {left right : Word Nat} (same : SameSignature left right)
    (leftSegments rightSegments : List (List Nat × Nat)) (leftFinal rightFinal : List Nat)
    (leftDecomposition : S5_254.GloballySimpleSeparatorDecomposition
      left.toList left.toList leftSegments leftFinal)
    (rightDecomposition : S5_254.GloballySimpleSeparatorDecomposition
      right.toList right.toList rightSegments rightFinal) :
    canonicalSkeleton [] leftSegments leftFinal = canonicalSkeleton [] rightSegments rightFinal := by
  have separators : leftSegments.map Prod.snd = rightSegments.map Prod.snd := by
    calc
      leftSegments.map Prod.snd = S5_254.simpleSeparatorSequence left := by
        simpa [S5_254.simpleSeparatorSequence] using leftDecomposition.separatorSequence_eq
      _ = S5_254.simpleSeparatorSequence right := same.m18.simpleSeparatorSequence_eq
      _ = rightSegments.map Prod.snd := by
        simpa [S5_254.simpleSeparatorSequence] using rightDecomposition.separatorSequence_eq.symm
  exact canonicalSkeletonAlignmentAux same leftDecomposition rightDecomposition [] [] []
    (by simp) (by simp) (by simp) rfl (fun _ => Iff.rfl) (fun _ => Iff.rfl) separators

theorem separatorSkeleton_eq_of_sameSignature {left right : Word Nat} (same : SameSignature left right) :
    separatorSkeleton left = separatorSkeleton right :=
  canonicalSkeleton_eq_of_sameSignature same
    (S5_254.canonicalSeparatorDecompositionData left.toList).1
    (S5_254.canonicalSeparatorDecompositionData right.toList).1
    (S5_254.canonicalSeparatorDecompositionData left.toList).2
    (S5_254.canonicalSeparatorDecompositionData right.toList).2
    (S5_254.canonicalSeparatorDecompositionData_spec left.toList)
    (S5_254.canonicalSeparatorDecompositionData_spec right.toList)

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.FordNil
