import SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank090FirstOrderSuccessorBridge

/-!
# Rank-090 prefix-generalized terminated-scanner state decomposition

The existing owner source proves stable scanner reachability and reduces both
class endpoints to `StableScannerSignatureAgreement`.  This separately
authored source introduces the exact arbitrary-prefix scanner state requested
in `msg-0293`: processed repeated markers, a reverse simple-letter accumulator,
and an arbitrary unprocessed suffix.  It does not assert the still-missing
signature agreement or claim a class carrier.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank090.FirstOrderSuccessorBridge

open SemigroupBasis

/-- Prefix-generalized stable fold with the owner's exact retained-marker rule. -/
def stableScannerFold
    (whole seen current : List Nat) : List Nat → List Nat
  | [] => current.reverse
  | letter :: rest =>
      if whole.count letter = 1 then
        stableScannerFold whole seen (letter :: current) rest
      else if current = [] ∧ letter ∈ seen then
        stableScannerFold whole seen [] rest
      else
        current.reverse ++ [letter, letter] ++
          stableScannerFold whole (seen ++ [letter]) [] rest

/-- Decompose the scanner at EVERY prefix state, not merely at empty state. -/
theorem stableScannerFold_eq_terminatedState
    (whole : List Nat) :
    ∀ (remaining current seen : List Nat),
      stableScannerFold whole seen current remaining =
        SemigroupBasis.CoRoots.S5_402.renderSquaredTerminatedBlocks
          (retainFirstOrBlockFactors seen
            (SemigroupBasis.CoRoots.S5_402.terminatedBlockScan
              whole current remaining).1) ++
          (SemigroupBasis.CoRoots.S5_402.terminatedBlockScan
            whole current remaining).2 := by
  intro remaining
  induction remaining with
  | nil =>
      intro current seen
      simp [stableScannerFold,
        SemigroupBasis.CoRoots.S5_402.terminatedBlockScan,
        retainFirstOrBlockFactors,
        SemigroupBasis.CoRoots.S5_402.renderSquaredTerminatedBlocks]
  | cons letter rest inductionHypothesis =>
      intro current seen
      by_cases simple : whole.count letter = 1
      · simpa [stableScannerFold,
          SemigroupBasis.CoRoots.S5_402.terminatedBlockScan,
          simple] using
          inductionHypothesis (letter :: current) seen
      · by_cases drop : current = [] ∧ letter ∈ seen
        · rcases drop with ⟨empty, present⟩
          subst current
          simpa [stableScannerFold,
            SemigroupBasis.CoRoots.S5_402.terminatedBlockScan,
            simple, retainFirstOrBlockFactors, present] using
            inductionHypothesis [] seen
        · have reverseDrop :
              ¬ (current.reverse = [] ∧ letter ∈ seen) := by
              intro impossible
              have empty : current = [] := by
                simpa using impossible.1
              exact drop ⟨empty, impossible.2⟩
          have tail :=
            inductionHypothesis [] (seen ++ [letter])
          have appended := congrArg
            (fun output : List Nat =>
              current.reverse ++ [letter, letter] ++ output)
            tail
          simpa [stableScannerFold,
            SemigroupBasis.CoRoots.S5_402.terminatedBlockScan,
            simple, drop, retainFirstOrBlockFactors,
            reverseDrop,
            SemigroupBasis.CoRoots.S5_402.renderSquaredTerminatedBlocks,
            List.append_assoc] using appended

/-- Empty state specializes to the owner's already-reachable canonical list. -/
theorem stableScannerFold_eq_ownerCanonical
    (letters : List Nat) :
    stableScannerFold letters [] [] letters =
      firstOrderSuccessorCanonicalList letters := by
  simpa [firstOrderSuccessorCanonicalList,
    SemigroupBasis.CoRoots.S5_402.terminatedBlocks,
    SemigroupBasis.CoRoots.S5_402.terminatedFinalBlock] using
    stableScannerFold_eq_terminatedState letters letters [] []

/-- A globally simple letter extends the reverse pending-block state. -/
theorem stableScannerFold_simplePrefix
    (whole seen current rest : List Nat) (letter : Nat)
    (simple : whole.count letter = 1) :
    stableScannerFold whole seen current (letter :: rest) =
      stableScannerFold whole seen (letter :: current) rest := by
  simp [stableScannerFold, simple]

/-- A seen repeated marker drops ONLY when its pending simple block is empty. -/
theorem stableScannerFold_seenMarkerEmptyBlock
    (whole seen rest : List Nat) (marker : Nat)
    (repeated : whole.count marker ≠ 1)
    (present : marker ∈ seen) :
    stableScannerFold whole seen [] (marker :: rest) =
      stableScannerFold whole seen [] rest := by
  simp [stableScannerFold, repeated, present]

/-- After a genuine simple block, a seen marker MUST still be retained. -/
theorem stableScannerFold_seenMarkerAfterSimpleBlock
    (whole seen current rest : List Nat) (marker : Nat)
    (repeated : whole.count marker ≠ 1)
    (nonempty : current ≠ []) :
    stableScannerFold whole seen current (marker :: rest) =
      current.reverse ++ [marker, marker] ++
        stableScannerFold whole (seen ++ [marker]) [] rest := by
  have keep : ¬ (current = [] ∧ marker ∈ seen) := by
    intro impossible
    exact nonempty impossible.1
  simp [stableScannerFold, repeated, keep]

end SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank090.FirstOrderSuccessorBridge

#print axioms SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank090.FirstOrderSuccessorBridge.stableScannerFold_eq_terminatedState
#print axioms SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank090.FirstOrderSuccessorBridge.stableScannerFold_eq_ownerCanonical
#print axioms SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank090.FirstOrderSuccessorBridge.stableScannerFold_simplePrefix
#print axioms SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank090.FirstOrderSuccessorBridge.stableScannerFold_seenMarkerEmptyBlock
#print axioms SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank090.FirstOrderSuccessorBridge.stableScannerFold_seenMarkerAfterSimpleBlock
