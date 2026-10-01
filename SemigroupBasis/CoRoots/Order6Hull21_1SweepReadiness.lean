import SemigroupBasis.CoRoots.Order6Hull21_1ForwardSweep
import SemigroupBasis.CoRoots.Order6Hull21_1BlockFacts

/-!
# Hull 21.1 forward-sweep readiness

This module derives the local readiness invariant for the forward gap sweep
from parser well-formedness. Historical letters need coverage only when they
actually occur in the remaining gap debt.
-/

namespace SemigroupBasis
namespace CoRoots
namespace Order6Hull21_1SweepReadiness

open Order6Hull21_1BlockFacts
open Order6Hull21_1ForwardSweep

theorem forwardSweepReady_of_wellFormed
    {anchor : Nat} {historical dynamic : List Nat}
    {blocks : List GapBlock}
    (formed : S5_870.GapBlocksWellFormed historical blocks)
    (covered :
      ∀ z, z ∈ historical →
        z ∈ S5_870.gapBlockSeconds blocks →
          z ∈ anchor :: dynamic) :
    ForwardSweepReady anchor dynamic blocks := by
  induction formed generalizing dynamic with
  | nil historical =>
      exact ForwardSweepReady.nil dynamic
  | cons historical block rest markerFresh secondsSeen tail induction =>
      refine ForwardSweepReady.cons dynamic block rest ?_ ?_
      · intro z zInSeconds
        rcases List.mem_cons.mp (secondsSeen z zInSeconds) with
          zMarker | zHistorical
        · subst z
          simp
        · have zInAllSeconds :
              z ∈ S5_870.gapBlockSeconds (block :: rest) := by
            simp only [S5_870.gapBlockSeconds, List.flatMap_cons,
              List.mem_append]
            exact Or.inl zInSeconds
          have zCovered := covered z zHistorical zInAllSeconds
          rcases List.mem_cons.mp zCovered with zAnchor | zDynamic
          · exact List.mem_cons.mpr (Or.inl zAnchor)
          · exact List.mem_cons.mpr
              (Or.inr (List.mem_append_left [block.marker] zDynamic))
      · apply induction
        intro z zHistorical zInTailSeconds
        rcases List.mem_cons.mp zHistorical with
          zMarker | zOldHistorical
        · subst z
          simp
        · have zInAllSeconds :
              z ∈ S5_870.gapBlockSeconds (block :: rest) := by
            simp only [S5_870.gapBlockSeconds, List.flatMap_cons,
              List.mem_append]
            exact Or.inr zInTailSeconds
          have zCovered :=
            covered z zOldHistorical zInAllSeconds
          rcases List.mem_cons.mp zCovered with zAnchor | zDynamic
          · exact List.mem_cons.mpr (Or.inl zAnchor)
          · exact List.mem_cons.mpr
              (Or.inr
                (List.mem_append_left
                  (if block.seconds = [] then [] else [anchor])
                  (List.mem_append_left [block.marker] zDynamic)))

end Order6Hull21_1SweepReadiness
end CoRoots
end SemigroupBasis
