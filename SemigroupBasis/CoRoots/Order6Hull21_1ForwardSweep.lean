import SemigroupBasis.CoRoots.Order6Hull21_1BoundaryAnchor

/-!
# Hull 21.1 forward gap sweep

This module isolates the left-to-right redistribution of witnessed gap
letters.  Processing the current block moves its nonempty gap to the final
debt.  Recursing on the remaining blocks therefore accumulates block debts in
reverse block order while preserving the order inside each individual gap.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace SemigroupBasis
namespace CoRoots
namespace Order6Hull21_1ForwardSweep

open SemigroupBasis.CoRoots.Order6Hull21_1ProfileCountNormalization

abbrev HullListDerives : List Nat → List Nat → Prop :=
  SemigroupBasis.CoRoots.Order6Hull21_1JointCompleteness.HullListDerives

/-- Gap debt in the order produced by a left-to-right redistribution sweep. -/
def reverseBlockDebt
    (blocks :
      List SemigroupBasis.CoRoots.S5_870.FirstOccurrenceGapBlock) :
    List Nat :=
  SemigroupBasis.CoRoots.S5_870.gapBlockSeconds blocks.reverse

/-- The local old-letter invariant needed by the forward sweep.

After a nonempty gap is redistributed, one extra anchor is retained in the
seen prefix used by the recursive tail. -/
inductive ForwardSweepReady (anchor : Nat) :
    List Nat →
    List SemigroupBasis.CoRoots.S5_870.FirstOccurrenceGapBlock →
    Prop
  | nil (seen : List Nat) :
      ForwardSweepReady anchor seen []
  | cons (seen : List Nat)
      (block : SemigroupBasis.CoRoots.S5_870.FirstOccurrenceGapBlock)
      (rest :
        List SemigroupBasis.CoRoots.S5_870.FirstOccurrenceGapBlock)
      (oldLetters :
        ∀ letter, letter ∈ block.seconds →
          letter ∈ anchor :: (seen ++ [block.marker]))
      (tail :
        ForwardSweepReady anchor
          (seen ++ [block.marker] ++
            if block.seconds = [] then [] else [anchor])
          rest) :
      ForwardSweepReady anchor seen (block :: rest)

/-- Sweep witnessed gaps from left to right into a reverse-block-order debt. -/
theorem hullListDerivesForwardSweepReverse
    (pre : List Nat) (anchor lastMarker : Nat) :
    ∀ {seen : List Nat}
      {blocks :
        List SemigroupBasis.CoRoots.S5_870.FirstOccurrenceGapBlock}
      (post : List Nat),
      ForwardSweepReady anchor seen blocks →
      HullListDerives
        (pre ++ [anchor] ++ seen ++
          SemigroupBasis.CoRoots.S5_870.renderGapBlocks blocks ++
          [lastMarker, anchor] ++ post)
        (pre ++ [anchor] ++ seen ++
          renderSweptCorePrefix anchor blocks ++
          [lastMarker, anchor] ++
          reverseBlockDebt blocks ++ post) := by
  intro seen blocks post ready
  induction ready generalizing post with
  | nil seen =>
      simpa [SemigroupBasis.CoRoots.S5_870.renderGapBlocks,
        renderSweptCorePrefix, reverseBlockDebt,
        SemigroupBasis.CoRoots.S5_870.gapBlockSeconds,
        List.append_assoc] using
        (SemigroupBasis.CoRoots.S5_107.ListDerives.refl
          (basis :=
            SemigroupBasis.Order6Subdirect.Hull21_1_S5_831_S3_8.publishedBasis)
          (pre ++ [anchor] ++ seen ++ [lastMarker, anchor] ++ post))
  | cons seen block rest oldLetters tail induction =>
      by_cases gapEmpty : block.seconds = []
      · have tailDerivation := induction post
        simpa [SemigroupBasis.CoRoots.S5_870.renderGapBlocks,
          renderSweptCorePrefix, reverseBlockDebt, gapEmpty,
          List.reverse_cons,
          SemigroupBasis.CoRoots.S5_870.gapBlockSeconds,
          List.flatMap_append, List.append_assoc] using tailDerivation
      · have moveCurrent :
          HullListDerives
            (pre ++ [anchor] ++ seen ++
              SemigroupBasis.CoRoots.S5_870.renderGapBlocks
                (block :: rest) ++
              [lastMarker, anchor] ++ post)
            (pre ++ [anchor] ++
              (seen ++ [block.marker] ++ [anchor]) ++
              SemigroupBasis.CoRoots.S5_870.renderGapBlocks rest ++
              [lastMarker, anchor] ++ block.seconds ++ post) := by
          simpa [SemigroupBasis.CoRoots.S5_870.renderGapBlocks,
            List.append_assoc] using
            (hullListDerivesMoveSeenGapToDebt
              pre post
              (seen ++ [block.marker])
              (SemigroupBasis.CoRoots.S5_870.renderGapBlocks rest ++
                [lastMarker])
              block.seconds anchor gapEmpty oldLetters)
        have sweepRest :
          HullListDerives
            (pre ++ [anchor] ++
              (seen ++ [block.marker] ++ [anchor]) ++
              SemigroupBasis.CoRoots.S5_870.renderGapBlocks rest ++
              [lastMarker, anchor] ++ block.seconds ++ post)
            (pre ++ [anchor] ++
              (seen ++ [block.marker] ++ [anchor]) ++
              renderSweptCorePrefix anchor rest ++
              [lastMarker, anchor] ++
              reverseBlockDebt rest ++ block.seconds ++ post) := by
          simpa [gapEmpty, List.append_assoc] using
            (induction (block.seconds ++ post))
        simpa [renderSweptCorePrefix, reverseBlockDebt,
          List.reverse_cons,
          SemigroupBasis.CoRoots.S5_870.gapBlockSeconds,
          List.flatMap_append, gapEmpty, List.append_assoc] using
          moveCurrent.trans sweepRest

end Order6Hull21_1ForwardSweep
end CoRoots
end SemigroupBasis
