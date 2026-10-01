import SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395PairBlocks
import SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395SeenGap

/-! Actual-count guards for B12 pair moves inside simple-marker sectors.
Absorption retains a nonfirst occurrence: the first occurrence alone is
not enough. No global sector renderer or completeness is assumed. -/

namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395SectorPairs

open SemigroupBasis
open Msg0457S11395Semantics Msg0457S11395EvenInsertion Msg0457S11395SeenGap
open Msg0457S11395PositiveRuns Msg0457S11395PairBlocks

def SimpleFree (word block : List Nat) : Prop :=
  ∀ tested ∈ block, word.count tested ≠ 1

theorem member_count_positive (word : List Nat) (letter : Nat) (member : letter ∈ word) :
    0 < word.count letter := by
  have nonzero : word.count letter ≠ 0 := fun zero => (List.count_eq_zero.mp zero) member
  omega

theorem simpleFree_congr (left right block : List Nat)
    (counts : ∀ tested, left.count tested = right.count tested)
    (free : SimpleFree left block) : SimpleFree right block := by
  intro tested member
  rw [← counts tested]
  exact free tested member

theorem simpleFree_subblock (word large small : List Nat)
    (contained : ∀ tested ∈ small, tested ∈ large) (free : SimpleFree word large) :
    SimpleFree word small := fun tested member => free tested (contained tested member)

/-- Removing the moved run cannot destroy a crossed letter's witness.
For the moved letter itself, the prefix and crossed block retain one each. -/
theorem retained_guard (prefixWords block suffix : List Nat) (letter copies : Nat)
    (seen : letter ∈ prefixWords)
    (free : SimpleFree (prefixWords ++ List.replicate copies letter ++ block ++ suffix) block) :
    NoSimpleInBlock prefixWords block suffix := by
  intro tested member
  have inBlock := member_count_positive block tested member
  by_cases equal : tested = letter
  · subst tested
    have inPrefix := member_count_positive prefixWords letter seen
    simp only [List.count_append]
    omega
  · have notOne := free tested member
    simp only [List.count_append, countReplicate, if_neg equal] at notOne
    simp only [List.count_append]
    omega

theorem movePairInSector (prefixWords block suffix : List Nat) (letter : Nat)
    (seen : letter ∈ prefixWords)
    (free : SimpleFree (prefixWords ++ [letter,letter] ++ block ++ suffix) block) :
    LD (prefixWords ++ [letter,letter] ++ block ++ suffix)
      (prefixWords ++ block ++ [letter,letter] ++ suffix) := by
  apply movePairAcrossBlock prefixWords block suffix letter seen
  apply retained_guard prefixWords block suffix letter 2 seen
  simpa using free

theorem moveEvenInSector (prefixWords block suffix : List Nat) (letter pairs : Nat)
    (seen : letter ∈ prefixWords)
    (free : SimpleFree (prefixWords ++ List.replicate (2*pairs) letter ++ block ++ suffix) block) :
    LD (prefixWords ++ List.replicate (2*pairs) letter ++ block ++ suffix)
      (prefixWords ++ block ++ List.replicate (2*pairs) letter ++ suffix) :=
  moveEvenAcrossBlock prefixWords block suffix letter pairs seen
    (retained_guard prefixWords block suffix letter (2*pairs) seen free)

/-- The explicit occurrence before the block is NONFIRST, witnessed in
prefixWords. Bring the final pair back, then reduce its seen run 3 to 1. -/
theorem absorbPairInSector (prefixWords block suffix : List Nat) (letter : Nat)
    (seen : letter ∈ prefixWords)
    (free : SimpleFree (prefixWords ++ [letter] ++ block ++ [letter,letter] ++ suffix) block) :
    LD (prefixWords ++ [letter] ++ block ++ [letter,letter] ++ suffix)
      (prefixWords ++ [letter] ++ block ++ suffix) := by
  have reordered : SimpleFree
      ((prefixWords ++ [letter]) ++ [letter,letter] ++ block ++ suffix) block := by
    apply simpleFree_congr _ _ block (fun tested => ?_) free
    simp only [List.count_append]
    omega
  have move := (movePairInSector (prefixWords ++ [letter]) block suffix letter
    (by simp) reordered).symm
  have reduce := normalizeSeenRun prefixWords (block ++ suffix) letter 3 seen
  have first : LD (prefixWords ++ [letter] ++ block ++ [letter,letter] ++ suffix)
      (prefixWords ++ [letter,letter,letter] ++ block ++ suffix) := by
    simpa [List.append_assoc] using move
  apply first.trans
  simpa [positiveCopies, SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0446TailBudget.cap,
    List.replicate_succ, List.append_assoc] using reduce

theorem absorption_strict_length (prefixWords block suffix : List Nat) (letter : Nat) :
    (prefixWords ++ [letter] ++ block ++ suffix).length + 2 =
      (prefixWords ++ [letter] ++ block ++ [letter,letter] ++ suffix).length := by
  simp only [List.length_append, List.length_cons, List.length_nil]
  omega

theorem absorbPairWord (head letter : Nat) (before block suffix : List Nat)
    (seen : letter ∈ head :: before)
    (free : SimpleFree ((head :: before) ++ [letter] ++ block ++ [letter,letter] ++ suffix) block) :
    Derives basis ⟨head, before ++ [letter] ++ block ++ [letter,letter] ++ suffix⟩
      ⟨head, before ++ [letter] ++ block ++ suffix⟩ := by
  exact (show LD
    (head :: (before ++ [letter] ++ block ++ [letter,letter] ++ suffix))
    (head :: (before ++ [letter] ++ block ++ suffix)) from
      by simpa using absorbPairInSector (head :: before) block suffix letter seen free).toWord

theorem absorbPair_signature (head letter : Nat) (before block suffix : List Nat)
    (seen : letter ∈ head :: before)
    (free : SimpleFree ((head :: before) ++ [letter] ++ block ++ [letter,letter] ++ suffix) block) :
    Msg0457S11395Observations.SameSignature
      ⟨head, before ++ [letter] ++ block ++ [letter,letter] ++ suffix⟩
      ⟨head, before ++ [letter] ++ block ++ suffix⟩ :=
  Msg0457S11395Signature.derives_preserve_signature
    (absorbPairWord head letter before block suffix seen free)

end SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395SectorPairs
