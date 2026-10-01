import SemigroupBasis.CoRoots.Order6Sunday.Msg0456S6598Assembly

/-! Literal canonicity of the B25 sorted separator skeleton. Prefix support
determines new introductions and prefix parity determines flip bits.
An unrestricted induction on the actual simple-separator decomposition. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0456S6598Alignment

open SemigroupBasis
open Msg0456S6598Signature Msg0456S6598Gap Msg0456S6598Assembly

theorem seen_after_canonicalGap (seen prefixWords gap : List Nat) (separator : Nat)
    (same : ∀ tested, tested ∈ seen ↔ tested ∈ prefixWords) :
    ∀ tested,
      tested ∈ seen ++ canonicalGap seen gap ++ [separator] ↔
        tested ∈ prefixWords ++ gap ++ [separator] := by
  intro tested
  have support := canonicalGap_support seen gap tested
  simp only [List.mem_append] at support ⊢
  rw [support, same tested]

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
            have total := same.toM18.totalParity tested
            have before := prefixParity tested
            rw [leftShape, rightShape, List.count_append, List.count_append] at total
            omega
          have support : ∀ tested, tested ∈ common ++ leftGap ↔ tested ∈ common ++ rightSource := by
            intro tested
            have total := same.toM18.support tested
            rw [leftShape, rightShape] at total
            simpa only [List.mem_append, ← leftSeen tested, ← rightSeen tested] using total
          exact canonicalGap_eq common common leftGap rightSource (fun _ => Iff.rfl) support parity
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
          have cumulativeSupport : ∀ tested,
              tested ∈ leftPrefix ++ leftGap ↔ tested ∈ rightPrefix ++ rightGap := by
            intro tested
            have values := same.prefixSupport leftSeparator leftSeparatorSimple rightSeparatorSimple tested
            rw [S5_254.simplePrefixBefore_eq_of_split leftSeparatorSimple
                (leftPrefix ++ leftGap) leftRemainder leftBeforeShape,
              S5_254.simplePrefixBefore_eq_of_split rightSeparatorSimple
                (rightPrefix ++ rightGap) rightRemainder rightBeforeShape] at values
            exact values
          have gapSupport : ∀ tested, tested ∈ common ++ leftGap ↔ tested ∈ common ++ rightGap := by
            intro tested
            simpa only [List.mem_append, ← leftSeen tested, ← rightSeen tested] using cumulativeSupport tested
          have cumulativeParity : ∀ tested,
              (leftPrefix ++ leftGap).count tested % 2 = (rightPrefix ++ rightGap).count tested % 2 := by
            intro tested
            have values := same.toM18.prefixValue_eq leftSeparator tested leftSeparatorSimple rightSeparatorSimple
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
          have headEq := canonicalGap_eq common common leftGap rightGap (fun _ => Iff.rfl) gapSupport gapParity
          have nextPrefixParity : ∀ tested,
              (leftPrefix ++ leftGap ++ [leftSeparator]).count tested % 2 =
                (rightPrefix ++ rightGap ++ [leftSeparator]).count tested % 2 := by
            intro tested
            have cumulative := cumulativeParity tested
            simp only [List.count_append, List.count_cons, List.count_nil] at cumulative ⊢
            omega
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
            leftTailShape rightTailShape nextPrefixParity leftNextSeen rightNextSeen separatorTailEq
          simpa only [canonicalSkeleton, ← headEq] using
            congrArg (fun tail => canonicalGap common leftGap ++ leftSeparator :: tail) tailEq

/-- Signature equality forces literal equality of the complete sorted
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
      _ = S5_254.simpleSeparatorSequence right := same.toM18.simpleSeparatorSequence_eq
      _ = rightSegments.map Prod.snd := by
        simpa [S5_254.simpleSeparatorSequence] using rightDecomposition.separatorSequence_eq.symm
  exact canonicalSkeletonAlignmentAux same leftDecomposition rightDecomposition [] [] []
    (by simp) (by simp) (by simp) (fun _ => Iff.rfl) (fun _ => Iff.rfl) separators

theorem separatorSkeleton_eq_of_sameSignature {left right : Word Nat} (same : SameSignature left right) :
    separatorSkeleton left = separatorSkeleton right :=
  canonicalSkeleton_eq_of_sameSignature same
    (S5_254.canonicalSeparatorDecompositionData left.toList).1
    (S5_254.canonicalSeparatorDecompositionData right.toList).1
    (S5_254.canonicalSeparatorDecompositionData left.toList).2
    (S5_254.canonicalSeparatorDecompositionData right.toList).2
    (S5_254.canonicalSeparatorDecompositionData_spec left.toList)
    (S5_254.canonicalSeparatorDecompositionData_spec right.toList)

end SemigroupBasis.CoRoots.Order6Sunday.Msg0456S6598Alignment
