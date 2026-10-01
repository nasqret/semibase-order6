import SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395SectorEndpoint

/-! The computed endpoint crosses exactly a simple-free prefix and stops
before an actual globally simple marker (or at the end). This is lifted
to placement of a selected pair in an actual reduced chain. -/

namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395SectorCut

open SemigroupBasis
open Msg0457S11395Semantics Msg0457S11395EvenInsertion Msg0457S11395SeenSwaps
open Msg0457S11395SectorPairs Msg0457S11395ReducedPairs Msg0457S11395SectorEndpoint
open Msg0457S11395WordGaps Msg0457S11395WordReduction

def cut : Chain → List Nat × List Nat
  | .stop gap => (gap, [])
  | .step gap fresh tail =>
      if fresh ∈ flatten tail then ((gap ++ [fresh]) ++ (cut tail).1, (cut tail).2)
      else (gap, fresh :: flatten tail)

theorem cut_join (chain : Chain) : (cut chain).1 ++ (cut chain).2 = flatten chain := by
  induction chain with
  | stop gap => simp [cut, flatten]
  | step gap fresh tail ih =>
      by_cases repeated : fresh ∈ flatten tail <;> simp [cut, repeated, flatten, List.append_assoc, ih]

theorem pushPair_flatten (letter : Nat) (chain : Chain) :
    flatten (pushPair letter chain) = (cut chain).1 ++ [letter,letter] ++ (cut chain).2 := by
  induction chain with
  | stop gap => simp [pushPair, cut, flatten]
  | step gap fresh tail ih =>
      by_cases repeated : fresh ∈ flatten tail <;>
        simp [pushPair, cut, repeated, flatten, ih, List.append_assoc]

theorem fresh_count (prefixWords gap : List Nat) (fresh : Nat) (tail : Chain)
    (good : WellFormed prefixWords (.step gap fresh tail)) :
    (prefixWords ++ flatten (.step gap fresh tail)).count fresh = 1 + (flatten tail).count fresh := by
  have missingGap : fresh ∉ gap := fun member => good.2.1 (good.1 fresh member)
  simp [flatten, List.count_append, List.count_eq_zero.mpr good.2.1,
    List.count_eq_zero.mpr missingGap, Nat.add_comm]

theorem fresh_simple_iff (prefixWords gap : List Nat) (fresh : Nat) (tail : Chain)
    (good : WellFormed prefixWords (.step gap fresh tail)) :
    (prefixWords ++ flatten (.step gap fresh tail)).count fresh = 1 ↔ fresh ∉ flatten tail := by
  rw [fresh_count prefixWords gap fresh tail good]
  constructor
  · intro one
    apply List.count_eq_zero.mp
    omega
  · intro absent
    rw [List.count_eq_zero.mpr absent]

theorem seenGap_simpleFree (prefixWords gap suffix : List Nat) (seen : AllSeen prefixWords gap) :
    SimpleFree (prefixWords ++ gap ++ suffix) gap := by
  intro tested member
  have bound := allSeen_guard prefixWords gap suffix seen tested member
  omega

theorem cut_spec (prefixWords : List Nat) (chain : Chain) (good : WellFormed prefixWords chain) :
    SimpleFree (prefixWords ++ flatten chain) (cut chain).1 ∧
    ((cut chain).2 = [] ∨ ∃ fresh rest, (cut chain).2 = fresh :: rest ∧
      (prefixWords ++ flatten chain).count fresh = 1) := by
  induction chain generalizing prefixWords with
  | stop gap =>
      refine ⟨?_, Or.inl rfl⟩
      simpa [cut, flatten] using seenGap_simpleFree prefixWords gap [] good
  | step gap fresh tail ih =>
      by_cases repeated : fresh ∈ flatten tail
      · have smaller := ih (prefixWords ++ gap ++ [fresh]) good.2.2
        simp only [cut, if_pos repeated]
        refine ⟨?_, ?_⟩
        · intro tested member
          simp only [List.mem_append, List.mem_singleton] at member
          rcases member with (inGap | equal) | inTail
          · have bound := allSeen_guard prefixWords gap (fresh :: flatten tail) good.1 tested inGap
            have large : 2 ≤ (prefixWords ++ flatten (.step gap fresh tail)).count tested := by
              simpa [flatten, List.append_assoc] using bound
            omega
          · subst tested
            have positive := member_count_positive (flatten tail) fresh repeated
            rw [fresh_count prefixWords gap fresh tail good]
            omega
          · simpa [flatten, List.append_assoc] using smaller.1 tested inTail
        · rcases smaller.2 with empty | ⟨next, rest, shape, simple⟩
          · exact Or.inl empty
          · exact Or.inr ⟨next, rest, shape, by simpa [flatten, List.append_assoc] using simple⟩
      · simp only [cut, if_neg repeated]
        refine ⟨?_, Or.inr ⟨fresh, flatten tail, rfl, (fresh_simple_iff _ _ _ _ good).2 repeated⟩⟩
        simpa [flatten, List.append_assoc] using seenGap_simpleFree prefixWords gap (fresh :: flatten tail) good.1

theorem pair_source_count (prefixWords : List Nat) (chain : Chain) (letter tested : Nat)
    (absent : letter ∉ flatten chain) (member : tested ∈ flatten chain) :
    (prefixWords ++ [letter,letter] ++ flatten chain).count tested =
      (prefixWords ++ flatten chain).count tested := by
  have unequal : letter ≠ tested := by
    intro equal
    subst tested
    exact absent member
  simp [List.count_append, unequal]

/-- The certificate refers to the original source INCLUDING the pair,
not only to the retained context. The pair's finality supplies count transport. -/
theorem cut_pair_source_spec (prefixWords : List Nat) (chain : Chain) (letter : Nat)
    (good : WellFormed prefixWords chain) (absent : letter ∉ flatten chain) :
    SimpleFree (prefixWords ++ [letter,letter] ++ flatten chain) (cut chain).1 ∧
    ((cut chain).2 = [] ∨ ∃ fresh rest, (cut chain).2 = fresh :: rest ∧
      (prefixWords ++ [letter,letter] ++ flatten chain).count fresh = 1) := by
  have parts := cut_spec prefixWords chain good
  refine ⟨?_, ?_⟩
  · intro tested member
    have original : tested ∈ flatten chain := by
      rw [← cut_join chain]
      exact List.mem_append_left _ member
    rw [pair_source_count prefixWords chain letter tested absent original]
    exact parts.1 tested member
  · rcases parts.2 with empty | ⟨fresh, rest, shape, simple⟩
    · exact Or.inl empty
    · refine Or.inr ⟨fresh, rest, shape, ?_⟩
      have original : fresh ∈ flatten chain := by
        rw [← cut_join chain, shape]
        exact List.mem_append_right _ (by simp)
      rw [pair_source_count prefixWords chain letter fresh absent original]
      exact simple

def placeStepPair (gap : List Nat) (fresh letter : Nat) (tail : Chain) : Chain :=
  pushPair letter (.step (removePair gap letter) fresh tail)

theorem placeStepPair_derives (prefixWords gap : List Nat) (fresh letter : Nat) (tail : Chain)
    (good : WellFormed prefixWords (.step gap fresh tail)) (pair : 2 ≤ gap.count letter) :
    LD (prefixWords ++ flatten (.step gap fresh tail))
      (prefixWords ++ flatten (placeStepPair gap fresh letter tail)) := by
  have earlier := good.1 letter (List.count_pos_iff.mp (by omega))
  have first := seenGapPermutation prefixWords (fresh :: flatten tail)
    (pair_permutation gap letter pair) good.1
  have placement := pushPair_derives prefixWords letter (.step (removePair gap letter) fresh tail)
    (removedChain_wellFormed prefixWords gap fresh letter tail good pair) earlier
  have firstTyped : LD (prefixWords ++ flatten (.step gap fresh tail))
      (prefixWords ++ [letter,letter] ++ flatten (.step (removePair gap letter) fresh tail)) := by
    simpa [flatten, List.append_assoc] using first
  exact firstTyped.trans placement

theorem placeStepPair_wellFormed (prefixWords gap : List Nat) (fresh letter : Nat) (tail : Chain)
    (good : WellFormed prefixWords (.step gap fresh tail)) (pair : 2 ≤ gap.count letter) :
    WellFormed prefixWords (placeStepPair gap fresh letter tail) :=
  pushPair_wellFormed prefixWords letter _
    (removedChain_wellFormed prefixWords gap fresh letter tail good pair)
    (good.1 letter (List.count_pos_iff.mp (by omega)))

theorem placeStepPair_reduced (gap : List Nat) (fresh letter : Nat) (tail : Chain)
    (reduced : Reduced (.step gap fresh tail)) (pair : 2 ≤ gap.count letter) :
    Reduced (placeStepPair gap fresh letter tail) :=
  pushPair_reduced letter _ (removedChain_reduced gap fresh letter tail reduced pair)
    (removePair_final gap (fresh :: flatten tail) letter reduced.1 pair)

theorem placeStepPair_introductions (gap : List Nat) (fresh letter : Nat) (tail : Chain) :
    introductions (placeStepPair gap fresh letter tail) = introductions (.step gap fresh tail) :=
  pushPair_introductions letter _

theorem placeStepPair_counts (gap : List Nat) (fresh letter tested : Nat) (tail : Chain)
    (pair : 2 ≤ gap.count letter) :
    (flatten (placeStepPair gap fresh letter tail)).count tested =
      (flatten (.step gap fresh tail)).count tested := by
  unfold placeStepPair
  rw [pushPair_count]
  simp only [flatten, List.count_append]
  rw [pair_count gap letter tested pair]
  omega

end SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395SectorCut
