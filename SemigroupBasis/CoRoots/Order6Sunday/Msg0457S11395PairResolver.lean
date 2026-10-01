import SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395Absorber

/-! Resolve an actual pair: absorb it using a certified same-sector
nonfirst witness, or place it at the computed sector endpoint. -/

namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395PairResolver

open SemigroupBasis
open Msg0457S11395Semantics Msg0457S11395EvenInsertion Msg0457S11395SeenSwaps
open Msg0457S11395SectorPairs Msg0457S11395ReducedPairs Msg0457S11395SectorEndpoint
open Msg0457S11395WordGaps Msg0457S11395WordReduction Msg0457S11395Absorber

def headGap : Chain → List Nat
  | .stop gap => gap
  | .step gap _ _ => gap

def dropPair (letter : Nat) : Chain → Chain
  | .stop gap => .stop (removePair gap letter)
  | .step gap fresh tail => .step (removePair gap letter) fresh tail

theorem pair_seen (prefixWords : List Nat) (letter : Nat) (chain : Chain)
    (good : WellFormed prefixWords chain) (pair : 2 ≤ (headGap chain).count letter) :
    letter ∈ prefixWords := by
  have present : letter ∈ headGap chain := List.count_pos_iff.mp (by omega)
  cases chain with
  | stop gap => exact good letter present
  | step gap fresh tail => exact good.1 letter present

theorem dropPair_wellFormed (prefixWords : List Nat) (letter : Nat) (chain : Chain)
    (good : WellFormed prefixWords chain) (pair : 2 ≤ (headGap chain).count letter) :
    WellFormed prefixWords (dropPair letter chain) := by
  cases chain with
  | stop gap => exact removePair_seen prefixWords gap letter good pair
  | step gap fresh tail => exact removedChain_wellFormed prefixWords gap fresh letter tail good pair

theorem dropPair_reduced (letter : Nat) (chain : Chain)
    (red : Reduced chain) (pair : 2 ≤ (headGap chain).count letter) :
    Reduced (dropPair letter chain) := by
  cases chain with
  | stop gap =>
      intro tested
      exact Nat.le_trans (removePair_count_le gap letter tested pair) (red tested)
  | step gap fresh tail => exact removedChain_reduced gap fresh letter tail red pair

theorem dropPair_final (letter : Nat) (chain : Chain)
    (red : Reduced chain) (pair : 2 ≤ (headGap chain).count letter) :
    letter ∉ flatten (dropPair letter chain) := by
  cases chain with
  | stop gap => simpa [dropPair, flatten] using removePair_final gap [] letter red pair
  | step gap fresh tail => exact removePair_final gap (fresh :: flatten tail) letter red.1 pair

theorem dropPair_counts (letter tested : Nat) (chain : Chain)
    (pair : 2 ≤ (headGap chain).count letter) :
    (flatten chain).count tested = (flatten (dropPair letter chain)).count tested + [letter,letter].count tested := by
  cases chain with
  | stop gap => exact pair_count gap letter tested pair
  | step gap fresh tail =>
      simp only [flatten, dropPair, List.count_append]
      rw [pair_count gap letter tested pair]
      omega

theorem dropPair_introductions (letter : Nat) (chain : Chain) :
    introductions (dropPair letter chain) = introductions chain := by
  cases chain <;> rfl

theorem dropPair_pull (prefixWords : List Nat) (letter : Nat) (chain : Chain)
    (good : WellFormed prefixWords chain) (pair : 2 ≤ (headGap chain).count letter) :
    LD (prefixWords ++ flatten chain) (prefixWords ++ [letter,letter] ++ flatten (dropPair letter chain)) := by
  cases chain with
  | stop gap =>
      simpa [dropPair, flatten, List.append_assoc] using
        seenGapPermutation prefixWords [] (pair_permutation gap letter pair) good
  | step gap fresh tail =>
      simpa [dropPair, flatten, List.append_assoc] using
        seenGapPermutation prefixWords (fresh :: flatten tail) (pair_permutation gap letter pair) good.1

theorem dropPair_absorb (prefixWords : List Nat) (letter : Nat) (chain : Chain)
    (good : WellFormed prefixWords chain) (pair : 2 ≤ (headGap chain).count letter)
    (parts : List Nat × List Nat)
    (found : find (prefixWords ++ flatten chain) prefixWords letter = some parts) :
    LD (prefixWords ++ flatten chain) (prefixWords ++ flatten (dropPair letter chain)) := by
  have witness := find_sound (prefixWords ++ flatten chain) prefixWords letter parts.1 parts.2 found
  cases chain with
  | stop gap =>
      have step := absorbGapPair parts.1 parts.2 gap [] letter witness.2.1
        (by simpa [witness.1, List.append_assoc] using good) pair
        (by simpa [flatten, witness.1, List.append_assoc] using witness.2.2)
      simpa [dropPair, flatten, witness.1, List.append_assoc] using step
  | step gap fresh tail =>
      have step := absorbGapPair parts.1 parts.2 gap (fresh :: flatten tail) letter witness.2.1
        (by simpa [witness.1, List.append_assoc] using good.1) pair
        (by simpa [flatten, witness.1, List.append_assoc] using witness.2.2)
      simpa [dropPair, flatten, witness.1, List.append_assoc] using step

def resolveHead (prefixWords : List Nat) (letter : Nat) (chain : Chain) : Chain :=
  match find (prefixWords ++ flatten chain) prefixWords letter with
  | none => pushPair letter (dropPair letter chain)
  | some _ => dropPair letter chain

theorem resolveHead_derives (prefixWords : List Nat) (letter : Nat) (chain : Chain)
    (good : WellFormed prefixWords chain) (pair : 2 ≤ (headGap chain).count letter) :
    LD (prefixWords ++ flatten chain) (prefixWords ++ flatten (resolveHead prefixWords letter chain)) := by
  cases found : find (prefixWords ++ flatten chain) prefixWords letter with
  | none =>
      have first := dropPair_pull prefixWords letter chain good pair
      have second := pushPair_derives prefixWords letter (dropPair letter chain)
        (dropPair_wellFormed prefixWords letter chain good pair) (pair_seen prefixWords letter chain good pair)
      simpa [resolveHead, found] using first.trans second
  | some parts => simpa [resolveHead, found] using dropPair_absorb prefixWords letter chain good pair parts found

theorem resolveHead_wellFormed (prefixWords : List Nat) (letter : Nat) (chain : Chain)
    (good : WellFormed prefixWords chain) (pair : 2 ≤ (headGap chain).count letter) :
    WellFormed prefixWords (resolveHead prefixWords letter chain) := by
  cases found : find (prefixWords ++ flatten chain) prefixWords letter with
  | none =>
      simpa [resolveHead, found] using pushPair_wellFormed prefixWords letter (dropPair letter chain)
        (dropPair_wellFormed prefixWords letter chain good pair) (pair_seen prefixWords letter chain good pair)
  | some parts => simpa [resolveHead, found] using dropPair_wellFormed prefixWords letter chain good pair

theorem resolveHead_reduced (prefixWords : List Nat) (letter : Nat) (chain : Chain)
    (red : Reduced chain) (pair : 2 ≤ (headGap chain).count letter) :
    Reduced (resolveHead prefixWords letter chain) := by
  cases found : find (prefixWords ++ flatten chain) prefixWords letter with
  | none =>
      simpa [resolveHead, found] using pushPair_reduced letter (dropPair letter chain)
        (dropPair_reduced letter chain red pair) (dropPair_final letter chain red pair)
  | some parts => simpa [resolveHead, found] using dropPair_reduced letter chain red pair

theorem resolveHead_introductions (prefixWords : List Nat) (letter : Nat) (chain : Chain) :
    introductions (resolveHead prefixWords letter chain) = introductions chain := by
  cases found : find (prefixWords ++ flatten chain) prefixWords letter <;>
    simp [resolveHead, found, pushPair_introductions, dropPair_introductions]

theorem pushDrop_counts (letter tested : Nat) (chain : Chain)
    (pair : 2 ≤ (headGap chain).count letter) :
    (flatten (pushPair letter (dropPair letter chain))).count tested = (flatten chain).count tested := by
  rw [pushPair_count]
  exact (dropPair_counts letter tested chain pair).symm

theorem resolveHead_count_le (prefixWords : List Nat) (letter tested : Nat) (chain : Chain)
    (pair : 2 ≤ (headGap chain).count letter) :
    (flatten (resolveHead prefixWords letter chain)).count tested ≤ (flatten chain).count tested := by
  cases found : find (prefixWords ++ flatten chain) prefixWords letter with
  | none => simp only [resolveHead, found, pushDrop_counts letter tested chain pair, Nat.le_refl]
  | some parts =>
      simp only [resolveHead, found]
      have counts := dropPair_counts letter tested chain pair
      omega

theorem resolveHead_counts_other (prefixWords : List Nat) (letter tested : Nat) (chain : Chain)
    (pair : 2 ≤ (headGap chain).count letter) (unequal : tested ≠ letter) :
    (flatten (resolveHead prefixWords letter chain)).count tested = (flatten chain).count tested := by
  cases found : find (prefixWords ++ flatten chain) prefixWords letter with
  | none => simpa [resolveHead, found] using pushDrop_counts letter tested chain pair
  | some parts =>
      have counts := dropPair_counts letter tested chain pair
      have zero : [letter,letter].count tested = 0 := by simp [Ne.symm unequal]
      rw [zero, Nat.add_zero] at counts
      simpa [resolveHead, found] using counts.symm

theorem resolveHead_support_subset (prefixWords : List Nat) (letter tested : Nat) (chain : Chain)
    (pair : 2 ≤ (headGap chain).count letter)
    (member : tested ∈ flatten (resolveHead prefixWords letter chain)) : tested ∈ flatten chain := by
  have positive := member_count_positive _ tested member
  have bound := resolveHead_count_le prefixWords letter tested chain pair
  exact List.count_pos_iff.mp (by omega)

theorem resolveHead_simple (prefixWords : List Nat) (letter tested : Nat) (chain : Chain)
    (pair : 2 ≤ (headGap chain).count letter) :
    (prefixWords ++ flatten (resolveHead prefixWords letter chain)).count tested = 1 ↔
      (prefixWords ++ flatten chain).count tested = 1 := by
  cases found : find (prefixWords ++ flatten chain) prefixWords letter with
  | none => simp only [resolveHead, found, List.count_append, pushDrop_counts letter tested chain pair]
  | some parts =>
      by_cases equal : tested = letter
      · subst tested
        have past := found_prefix_two (prefixWords ++ flatten chain) prefixWords letter parts found
        simp only [resolveHead, found, List.count_append]
        omega
      · have same := resolveHead_counts_other prefixWords letter tested chain pair equal
        simp only [List.count_append, same]

end SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395PairResolver
