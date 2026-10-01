import SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395SectorPairs
import SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395WordReduction

/-! Extract actual pairs from seen gaps, then absorb or relocate them
using source-word simple-marker guards. This is not yet the global
deterministic sector-allocation algorithm or SignatureReach. -/

namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395ReducedPairs

open SemigroupBasis
open Msg0457S11395Semantics Msg0457S11395EvenInsertion Msg0457S11395SeenSwaps
open Msg0457S11395WordGaps Msg0457S11395WordReduction Msg0457S11395SectorPairs

def removePair (gap : List Nat) (letter : Nat) : List Nat := (gap.erase letter).erase letter

theorem pair_permutation (gap : List Nat) (letter : Nat) (pair : 2 ≤ gap.count letter) :
    gap.Perm ([letter,letter] ++ removePair gap letter) := by
  have present : letter ∈ gap := List.count_pos_iff.mp (by omega)
  have second : letter ∈ gap.erase letter := by
    apply List.count_pos_iff.mp
    rw [List.count_erase_self]
    omega
  exact (List.perm_cons_erase present).trans
    (List.Perm.cons letter (List.perm_cons_erase second))

theorem pair_count (gap : List Nat) (letter tested : Nat) (pair : 2 ≤ gap.count letter) :
    gap.count tested = (removePair gap letter).count tested + [letter,letter].count tested := by
  have count := (pair_permutation gap letter pair).count tested
  change gap.count tested = ([letter,letter] ++ removePair gap letter).count tested at count
  rw [List.count_append] at count
  simpa only [Nat.add_comm] using count

theorem removePair_count_le (gap : List Nat) (letter tested : Nat) (pair : 2 ≤ gap.count letter) :
    (removePair gap letter).count tested ≤ gap.count tested := by
  have count := pair_count gap letter tested pair
  omega

theorem removePair_seen (prefixWords gap : List Nat) (letter : Nat)
    (seen : AllSeen prefixWords gap) (pair : 2 ≤ gap.count letter) :
    AllSeen prefixWords (removePair gap letter) := by
  intro tested member
  apply seen tested
  exact (pair_permutation gap letter pair).mem_iff.mpr (by simp [member])

theorem removePair_final (gap suffix : List Nat) (letter : Nat)
    (bound : GapBound gap suffix) (pair : 2 ≤ gap.count letter) :
    letter ∉ removePair gap letter ++ suffix := by
  have later : letter ∉ suffix := by
    intro member
    have upper := bound letter
    rw [if_pos member] at upper
    omega
  have upper := bound letter
  rw [if_neg later] at upper
  have removed : (removePair gap letter).count letter = 0 := by
    simp only [removePair, List.count_erase_self]
    omega
  simp only [List.mem_append, not_or]
  exact ⟨List.count_eq_zero.mp removed, later⟩

theorem extractGapPair (prefixWords gap suffix : List Nat) (letter : Nat)
    (seen : AllSeen prefixWords gap) (pair : 2 ≤ gap.count letter) :
    LD (prefixWords ++ gap ++ suffix)
      (prefixWords ++ removePair gap letter ++ [letter,letter] ++ suffix) := by
  have proof := compareSeenGaps prefixWords gap (removePair gap letter ++ [letter,letter]) suffix
    (fun tested => by simpa [List.count_append] using pair_count gap letter tested pair) seen
  simpa [List.append_assoc] using proof

theorem removedChain_wellFormed (prefixWords gap : List Nat) (fresh letter : Nat) (tail : Chain)
    (good : WellFormed prefixWords (.step gap fresh tail)) (pair : 2 ≤ gap.count letter) :
    WellFormed prefixWords (.step (removePair gap letter) fresh tail) := by
  have seen := removePair_seen prefixWords gap letter good.1 pair
  refine ⟨seen, good.2.1, ?_⟩
  exact wellFormed_congr tail _ _
    (seen_prefix_extension_support prefixWords gap _ fresh good.1 seen) good.2.2

theorem removedChain_reduced (gap : List Nat) (fresh letter : Nat) (tail : Chain)
    (reduced : Reduced (.step gap fresh tail)) (pair : 2 ≤ gap.count letter) :
    Reduced (.step (removePair gap letter) fresh tail) := by
  refine ⟨?_, reduced.2⟩
  intro tested
  exact Nat.le_trans (removePair_count_le gap letter tested pair) (reduced.1 tested)

/-- A pair selected from an actual reduced step is extracted and placed
after any simple-free prefix of its remaining suffix. The finality
certificate excludes its letter from the whole retained tail. -/
theorem relocateReducedPair (prefixWords gap block suffix : List Nat)
    (fresh letter : Nat) (tail : Chain)
    (good : WellFormed prefixWords (.step gap fresh tail))
    (reduced : Reduced (.step gap fresh tail)) (pair : 2 ≤ gap.count letter)
    (splitTail : fresh :: flatten tail = block ++ suffix)
    (free : SimpleFree (prefixWords ++ flatten (.step gap fresh tail)) block) :
    letter ∉ removePair gap letter ++ block ++ suffix ∧
    LD (prefixWords ++ flatten (.step gap fresh tail))
      (prefixWords ++ removePair gap letter ++ block ++ [letter,letter] ++ suffix) := by
  have finality := removePair_final gap (fresh :: flatten tail) letter reduced.1 pair
  rw [splitTail] at finality
  refine ⟨by simpa [List.append_assoc] using finality, ?_⟩
  have seen : letter ∈ prefixWords := good.1 letter (List.count_pos_iff.mp (by omega))
  have reordered : SimpleFree
      ((prefixWords ++ removePair gap letter) ++ [letter,letter] ++ block ++ suffix) block := by
    apply simpleFree_congr _ _ block (fun tested => ?_) free
    simp only [flatten, splitTail, List.count_append]
    rw [pair_count gap letter tested pair]
    omega
  have first := extractGapPair prefixWords gap (block ++ suffix) letter good.1 pair
  have move := movePairInSector (prefixWords ++ removePair gap letter) block suffix letter
    (List.mem_append_left _ seen) reordered
  have derivation : LD (prefixWords ++ gap ++ block ++ suffix)
      (prefixWords ++ removePair gap letter ++ block ++ [letter,letter] ++ suffix) := by
    apply (show LD (prefixWords ++ gap ++ block ++ suffix)
      ((prefixWords ++ removePair gap letter) ++ [letter,letter] ++ block ++ suffix) from
        by simpa [List.append_assoc] using first).trans move
  simpa [flatten, splitTail, List.append_assoc] using derivation

/-- The pair's gap remainder is automatically nonsimple: every one of
its letters already occurs before the gap. Only the intervening block
needs an explicit simple-marker-sector test on the original source. -/
theorem absorbGapPair (prior block gap suffix : List Nat) (letter : Nat)
    (earlier : letter ∈ prior)
    (seen : AllSeen (prior ++ [letter] ++ block) gap) (pair : 2 ≤ gap.count letter)
    (free : SimpleFree (prior ++ [letter] ++ block ++ gap ++ suffix) block) :
    LD (prior ++ [letter] ++ block ++ gap ++ suffix)
      (prior ++ [letter] ++ block ++ removePair gap letter ++ suffix) := by
  let prefixWords := prior ++ [letter] ++ block
  have remainingSeen := removePair_seen prefixWords gap letter seen pair
  have sourceCounts (tested : Nat) :
      (prior ++ [letter] ++ block ++ gap ++ suffix).count tested =
      (prior ++ [letter] ++ (block ++ removePair gap letter) ++ [letter,letter] ++ suffix).count tested := by
    simp only [List.count_append]
    rw [pair_count gap letter tested pair]
    omega
  have allFree : SimpleFree
      (prior ++ [letter] ++ (block ++ removePair gap letter) ++ [letter,letter] ++ suffix)
      (block ++ removePair gap letter) := by
    intro tested member
    rcases List.mem_append.mp member with inBlock | inRemainder
    · rw [← sourceCounts tested]
      exact free tested inBlock
    · have past := member_count_positive prefixWords tested (remainingSeen tested inRemainder)
      have present := member_count_positive (removePair gap letter) tested inRemainder
      simp only [prefixWords, List.count_append] at past ⊢
      omega
  have first := extractGapPair prefixWords gap suffix letter seen pair
  have second := absorbPairInSector prior (block ++ removePair gap letter) suffix letter earlier allFree
  have firstTyped : LD (prior ++ [letter] ++ block ++ gap ++ suffix)
      (prior ++ [letter] ++ (block ++ removePair gap letter) ++ [letter,letter] ++ suffix) := by
    simpa [prefixWords, List.append_assoc] using first
  simpa [List.append_assoc] using firstTyped.trans second

theorem absorbGapPair_length (prior block gap suffix : List Nat) (letter : Nat)
    (pair : 2 ≤ gap.count letter) :
    (prior ++ [letter] ++ block ++ removePair gap letter ++ suffix).length + 2 =
      (prior ++ [letter] ++ block ++ gap ++ suffix).length := by
  have sizes := (pair_permutation gap letter pair).length_eq
  simp only [List.length_append, List.length_cons, List.length_nil] at sizes ⊢
  omega

end SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395ReducedPairs
