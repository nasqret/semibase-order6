import SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395ReducedPairs

/-! Deterministic movement of an already-seen pair to the next actual
simple-marker boundary. No whole-word renderer or supplied endpoint. -/

namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395SectorEndpoint

open SemigroupBasis
open Msg0457S11395Semantics Msg0457S11395EvenInsertion Msg0457S11395SeenSwaps
open Msg0457S11395MixedPairs Msg0457S11395PairBlocks Msg0457S11395SectorPairs
open Msg0457S11395WordGaps Msg0457S11395WordReduction

def pushPair (letter : Nat) : Chain → Chain
  | .stop gap => .stop (gap ++ [letter,letter])
  | .step gap fresh tail =>
      if fresh ∈ flatten tail then .step gap fresh (pushPair letter tail)
      else .step (gap ++ [letter,letter]) fresh tail

theorem pushPair_introductions (letter : Nat) (chain : Chain) :
    introductions (pushPair letter chain) = introductions chain := by
  induction chain with
  | stop gap => rfl
  | step gap fresh tail ih =>
      by_cases repeated : fresh ∈ flatten tail <;> simp [pushPair, repeated, introductions, ih]

theorem pushPair_count (letter tested : Nat) (chain : Chain) :
    (flatten (pushPair letter chain)).count tested =
      (flatten chain).count tested + [letter,letter].count tested := by
  induction chain with
  | stop gap => simp [pushPair, flatten, List.count_append]
  | step gap fresh tail ih =>
      by_cases repeated : fresh ∈ flatten tail <;>
        simp [pushPair, repeated, flatten, List.count_append, List.count_cons, ih,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem pushPair_support (letter tested : Nat) (chain : Chain) :
    tested ∈ flatten (pushPair letter chain) ↔ tested = letter ∨ tested ∈ flatten chain := by
  induction chain with
  | stop gap => simp [pushPair, flatten, or_comm]
  | step gap fresh tail ih =>
      by_cases repeated : fresh ∈ flatten tail <;>
        simp [pushPair, repeated, flatten, ih, or_left_comm]

theorem pushPair_length (letter : Nat) (chain : Chain) :
    (flatten (pushPair letter chain)).length = (flatten chain).length + 2 := by
  induction chain with
  | stop gap => simp [pushPair, flatten]
  | step gap fresh tail ih =>
      by_cases repeated : fresh ∈ flatten tail <;>
        simp [pushPair, repeated, flatten, ih] <;> omega

theorem appendPair_seen (prefixWords gap : List Nat) (letter : Nat)
    (seen : AllSeen prefixWords gap) (earlier : letter ∈ prefixWords) :
    AllSeen prefixWords (gap ++ [letter,letter]) := by
  intro tested member
  rcases List.mem_append.mp member with inGap | inPair
  · exact seen tested inGap
  · have equal : tested = letter := by simpa using inPair
    simpa [equal] using earlier

theorem pushPair_wellFormed (prefixWords : List Nat) (letter : Nat) (chain : Chain)
    (good : WellFormed prefixWords chain) (earlier : letter ∈ prefixWords) :
    WellFormed prefixWords (pushPair letter chain) := by
  induction chain generalizing prefixWords with
  | stop gap => exact appendPair_seen prefixWords gap letter good earlier
  | step gap fresh tail ih =>
      by_cases repeated : fresh ∈ flatten tail
      · simp only [pushPair, if_pos repeated, WellFormed]
        refine ⟨good.1, good.2.1, ih _ good.2.2 ?_⟩
        exact List.mem_append_left _ (List.mem_append_left _ earlier)
      · simp only [pushPair, if_neg repeated, WellFormed]
        have seen := appendPair_seen prefixWords gap letter good.1 earlier
        refine ⟨seen, good.2.1, ?_⟩
        exact wellFormed_congr tail _ _
          (seen_prefix_extension_support prefixWords gap _ fresh good.1 seen) good.2.2

theorem allSeen_guard (prefixWords gap suffix : List Nat) (seen : AllSeen prefixWords gap) :
    NoSimpleInBlock prefixWords gap suffix := by
  intro tested member
  have past := member_count_positive prefixWords tested (seen tested member)
  have present := member_count_positive gap tested member
  simp only [List.count_append]
  omega

theorem pushPair_derives (prefixWords : List Nat) (letter : Nat) (chain : Chain)
    (good : WellFormed prefixWords chain) (earlier : letter ∈ prefixWords) :
    LD (prefixWords ++ [letter,letter] ++ flatten chain)
      (prefixWords ++ flatten (pushPair letter chain)) := by
  induction chain generalizing prefixWords with
  | stop gap =>
      simpa [pushPair, flatten, List.append_assoc] using
        movePairAcrossBlock prefixWords gap [] letter earlier (allSeen_guard prefixWords gap [] good)
  | step gap fresh tail ih =>
      have acrossGap := movePairAcrossBlock prefixWords gap (fresh :: flatten tail) letter earlier
        (allSeen_guard prefixWords gap _ good.1)
      by_cases repeated : fresh ∈ flatten tail
      · have pastGap : letter ∈ prefixWords ++ gap := List.mem_append_left _ earlier
        have acrossFresh := movePairPastFuture (prefixWords ++ gap) (flatten tail)
          letter fresh pastGap repeated
        have tailMove := ih (prefixWords ++ gap ++ [fresh]) good.2.2 (List.mem_append_left _ pastGap)
        have first : LD (prefixWords ++ [letter,letter] ++ flatten (.step gap fresh tail))
            ((prefixWords ++ gap) ++ [letter,letter] ++ fresh :: flatten tail) := by
          simpa [flatten, List.append_assoc] using acrossGap
        have second : LD ((prefixWords ++ gap) ++ [letter,letter] ++ fresh :: flatten tail)
            ((prefixWords ++ gap ++ [fresh]) ++ [letter,letter] ++ flatten tail) := by
          simpa [List.append_assoc] using acrossFresh
        simpa [pushPair, repeated, flatten, List.append_assoc] using (first.trans second).trans tailMove
      · simpa [pushPair, repeated, flatten, List.append_assoc] using acrossGap

theorem appendPair_bound (gap suffix : List Nat) (letter : Nat)
    (bound : GapBound gap suffix) (absent : letter ∉ gap ++ suffix) :
    GapBound (gap ++ [letter,letter]) suffix := by
  have missingGap : letter ∉ gap := fun member => absent (List.mem_append_left _ member)
  have missingSuffix : letter ∉ suffix := fun member => absent (List.mem_append_right _ member)
  intro tested
  by_cases equal : tested = letter
  · subst tested
    simp [List.count_append, List.count_eq_zero.mpr missingGap, missingSuffix]
  · have zero : [letter,letter].count tested = 0 := by simp [Ne.symm equal]
    simpa only [List.count_append, zero, Nat.add_zero] using bound tested

theorem pushPair_reduced (letter : Nat) (chain : Chain)
    (reduced : Reduced chain) (absent : letter ∉ flatten chain) :
    Reduced (pushPair letter chain) := by
  induction chain with
  | stop gap =>
      exact appendPair_bound gap [] letter reduced (by simpa [flatten] using absent)
  | step gap fresh tail ih =>
      have missingGap : letter ∉ gap := fun member => absent (List.mem_append_left _ member)
      have missingSuffix : letter ∉ fresh :: flatten tail :=
        fun member => absent (List.mem_append_right _ member)
      have missingTail : letter ∉ flatten tail := fun member => missingSuffix (List.mem_cons_of_mem _ member)
      by_cases repeated : fresh ∈ flatten tail
      · simp only [pushPair, if_pos repeated, Reduced]
        refine ⟨?_, ih reduced.2 missingTail⟩
        intro tested
        by_cases equal : tested = letter
        · subst tested
          simp only [List.count_eq_zero.mpr missingGap]
          exact Nat.zero_le _
        · have same : (tested ∈ fresh :: flatten (pushPair letter tail)) ↔
              tested ∈ fresh :: flatten tail := by
            simp only [List.mem_cons, pushPair_support, equal, false_or]
          simpa only [same] using reduced.1 tested
      · simp only [pushPair, if_neg repeated, Reduced]
        exact ⟨appendPair_bound gap (fresh :: flatten tail) letter reduced.1 absent, reduced.2⟩

end SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395SectorEndpoint
