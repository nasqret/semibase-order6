import SemigroupBasis.CoRoots.Order6Sunday.Msg0456S6598Gap
import SemigroupBasis.CoRoots.S5_254Canonical

/-! Whole-word B25 assembly, using the original globally-simple separator
decomposition. Every gap reaches its amended sorted support/parity render, with exact
counts and retained bank anchors carried through every induction step. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0456S6598Assembly

open SemigroupBasis
open Msg0456S6598Semantics Msg0456S6598Rewrites Msg0456S6598Gap

private abbrev LD := S5_107.ListDerives basis
private abbrev bank := S5_254.renderSquareBank

def canonicalSkeleton (prefixWords : List Nat) : List (List Nat × Nat) → List Nat → List Nat
  | [], finalGap => canonicalGap prefixWords finalGap
  | (gap, separator) :: segments, finalGap =>
      let head := canonicalGap prefixWords gap
      head ++ separator :: canonicalSkeleton (prefixWords ++ head ++ [separator]) segments finalGap

/-- The source count invariant includes all earlier banks in the suffix.
Thus every later gap retains its original global multiplicities. -/
theorem assembleSeparatorContext
    {whole source : List Nat} {segments : List (List Nat × Nat)} {finalGap : List Nat}
    (decomposition : S5_254.GloballySimpleSeparatorDecomposition whole source segments finalGap)
    (prefixWords suffix : List Nat)
    (invariant : ∀ tested, (prefixWords ++ source ++ suffix).count tested = whole.count tested) :
    ∃ labels,
      LD (prefixWords ++ source ++ suffix)
        (prefixWords ++ canonicalSkeleton prefixWords segments finalGap ++ suffix ++ bank labels) ∧
      (∀ tested,
        (prefixWords ++ canonicalSkeleton prefixWords segments finalGap ++ suffix ++ bank labels).count tested =
          whole.count tested) ∧
      (∀ tested ∈ labels, tested ∈ prefixWords ++ canonicalSkeleton prefixWords segments finalGap) := by
  induction decomposition generalizing prefixWords suffix with
  | final gap gapRepeated =>
      have repeated : AllRepeated prefixWords gap suffix := by
        intro tested member
        rw [invariant tested]
        exact gapRepeated tested member
      obtain ⟨labels, normalized, counts, seen⟩ := normalizeRepeatedGap prefixWords gap suffix repeated
      refine ⟨labels, normalized, ?_, seen⟩
      intro tested
      have original := invariant tested
      have removed := counts tested
      simp only [canonicalSkeleton, List.count_append, S5_254.count_renderSquareBank] at original ⊢
      omega
  | step gap separator remainder segments finalGap separatorSimple gapRepeated tail induction =>
      let head := canonicalGap prefixWords gap
      let nextPrefix := prefixWords ++ head ++ [separator]
      have repeated : AllRepeated prefixWords gap ((separator :: remainder) ++ suffix) := by
        intro tested member
        have original : (prefixWords ++ gap ++ ((separator :: remainder) ++ suffix)).count tested =
            whole.count tested := by simpa [List.append_assoc] using invariant tested
        rw [original]
        exact gapRepeated tested member
      obtain ⟨headLabels, normalized, headCounts, headSeen⟩ :=
        normalizeRepeatedGap prefixWords gap ((separator :: remainder) ++ suffix) repeated
      have headStep : LD (prefixWords ++ (gap ++ separator :: remainder) ++ suffix)
          (nextPrefix ++ remainder ++ (suffix ++ bank headLabels)) := by
        simpa [nextPrefix, head, List.append_assoc] using normalized
      have nextInvariant : ∀ tested,
          (nextPrefix ++ remainder ++ (suffix ++ bank headLabels)).count tested = whole.count tested := by
        intro tested
        have original := invariant tested
        have removed := headCounts tested
        simp only [nextPrefix, head, List.count_append, List.count_cons, List.count_nil,
          S5_254.count_renderSquareBank] at original ⊢
        omega
      obtain ⟨tailLabels, tailStep, tailCounts, tailSeen⟩ :=
        induction nextPrefix (suffix ++ bank headLabels) nextInvariant
      have combined : LD (nextPrefix ++ remainder ++ (suffix ++ bank headLabels))
          (prefixWords ++ canonicalSkeleton prefixWords ((gap, separator) :: segments) finalGap ++
            suffix ++ bank (headLabels ++ tailLabels)) := by
        simpa [canonicalSkeleton, nextPrefix, head, bank, S5_254.renderSquareBank,
          List.flatMap_append, List.append_assoc] using tailStep
      refine ⟨headLabels ++ tailLabels, headStep.trans combined, ?_, ?_⟩
      · intro tested
        simpa [canonicalSkeleton, nextPrefix, head, bank, S5_254.renderSquareBank,
          List.flatMap_append, List.append_assoc] using tailCounts tested
      · intro tested member
        rcases List.mem_append.mp member with headMember | tailMember
        · have old := headSeen tested headMember
          have extended : tested ∈ (prefixWords ++ head) ++
              (separator :: canonicalSkeleton nextPrefix segments finalGap) :=
            List.mem_append_left _ old
          simpa [canonicalSkeleton, nextPrefix, head, List.append_assoc] using extended
        · simpa [canonicalSkeleton, nextPrefix, head, List.append_assoc] using tailSeen tested tailMember

noncomputable def separatorSkeleton (word : Word Nat) : List Nat :=
  canonicalSkeleton []
    (S5_254.canonicalSeparatorDecompositionData word.toList).1
    (S5_254.canonicalSeparatorDecompositionData word.toList).2

/-- Every arbitrary nonempty word reaches the sorted separator skeleton
and a raw square bank. The source multiplicities are preserved EXACTLY. -/
theorem rawAssembly (word : Word Nat) :
    ∃ labels,
      LD word.toList (separatorSkeleton word ++ bank labels) ∧
      (∀ tested, (separatorSkeleton word ++ bank labels).count tested = word.toList.count tested) ∧
      (∀ tested ∈ labels, tested ∈ separatorSkeleton word) := by
  simpa [separatorSkeleton] using
    assembleSeparatorContext (S5_254.canonicalSeparatorDecompositionData_spec word.toList)
      [] [] (by simp)

end SemigroupBasis.CoRoots.Order6Sunday.Msg0456S6598Assembly
