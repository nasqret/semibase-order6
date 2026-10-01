import SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395PairResolver

/-! Scan actual chains for one letter's final pair, then iterate over a
finite support selector. This constructs B12 reach for the complete candidate
sector normalizer. Signature-canonical uniqueness remains a separate proof. -/

namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395ResolveLetter

open SemigroupBasis
open Msg0457S11395Semantics Msg0457S11395EvenInsertion Msg0457S11395SeenSwaps
open Msg0457S11395SeenGap Msg0457S11395ReducedPairs Msg0457S11395SectorEndpoint
open Msg0457S11395WordGaps Msg0457S11395WordReduction Msg0457S11395PairResolver

def resolveLetter (prefixWords : List Nat) (letter : Nat) : Chain → Chain
  | .stop gap =>
      if 2 ≤ gap.count letter then resolveHead prefixWords letter (.stop gap) else .stop gap
  | .step gap fresh tail =>
      if 2 ≤ gap.count letter then resolveHead prefixWords letter (.step gap fresh tail)
      else .step gap fresh (resolveLetter (prefixWords ++ gap ++ [fresh]) letter tail)

theorem resolveLetter_derives (prefixWords : List Nat) (letter : Nat) (chain : Chain)
    (good : WellFormed prefixWords chain) :
    LD (prefixWords ++ flatten chain) (prefixWords ++ flatten (resolveLetter prefixWords letter chain)) := by
  induction chain generalizing prefixWords with
  | stop gap =>
      by_cases pair : 2 ≤ gap.count letter
      · simpa [resolveLetter, pair] using resolveHead_derives prefixWords letter (.stop gap) good pair
      · simp only [resolveLetter, if_neg pair]
        exact S5_107.ListDerives.refl _
  | step gap fresh tail ih =>
      by_cases pair : 2 ≤ gap.count letter
      · simpa [resolveLetter, pair] using resolveHead_derives prefixWords letter (.step gap fresh tail) good pair
      · simpa [resolveLetter, pair, flatten, List.append_assoc] using ih (prefixWords ++ gap ++ [fresh]) good.2.2

theorem resolveLetter_wellFormed (prefixWords : List Nat) (letter : Nat) (chain : Chain)
    (good : WellFormed prefixWords chain) : WellFormed prefixWords (resolveLetter prefixWords letter chain) := by
  induction chain generalizing prefixWords with
  | stop gap =>
      by_cases pair : 2 ≤ gap.count letter
      · simpa [resolveLetter, pair] using resolveHead_wellFormed prefixWords letter (.stop gap) good pair
      · simpa [resolveLetter, pair] using good
  | step gap fresh tail ih =>
      by_cases pair : 2 ≤ gap.count letter
      · simpa [resolveLetter, pair] using resolveHead_wellFormed prefixWords letter (.step gap fresh tail) good pair
      · simp only [resolveLetter, if_neg pair, WellFormed]
        exact ⟨good.1,good.2.1,ih _ good.2.2⟩

theorem resolveLetter_count_le (prefixWords : List Nat) (letter tested : Nat) (chain : Chain) :
    (flatten (resolveLetter prefixWords letter chain)).count tested ≤ (flatten chain).count tested := by
  induction chain generalizing prefixWords with
  | stop gap =>
      by_cases pair : 2 ≤ gap.count letter
      · simpa [resolveLetter, pair] using resolveHead_count_le prefixWords letter tested (.stop gap) pair
      · simp [resolveLetter, pair]
  | step gap fresh tail ih =>
      by_cases pair : 2 ≤ gap.count letter
      · simpa [resolveLetter, pair] using resolveHead_count_le prefixWords letter tested (.step gap fresh tail) pair
      · have smaller := ih (prefixWords ++ gap ++ [fresh])
        simp only [resolveLetter, if_neg pair, flatten, List.count_append, List.count_cons]
        omega

theorem resolveLetter_support_subset (prefixWords : List Nat) (letter tested : Nat) (chain : Chain)
    (member : tested ∈ flatten (resolveLetter prefixWords letter chain)) : tested ∈ flatten chain := by
  have positive := Msg0457S11395SectorPairs.member_count_positive _ tested member
  have upper := resolveLetter_count_le prefixWords letter tested chain
  exact List.count_pos_iff.mp (by omega)

theorem gapBound_suffix_subset (gap oldSuffix newSuffix : List Nat) (bound : GapBound gap oldSuffix)
    (subset : ∀ tested ∈ newSuffix, tested ∈ oldSuffix) : GapBound gap newSuffix := by
  intro tested
  by_cases present : tested ∈ newSuffix
  · have oldPresent := subset tested present
    simpa only [if_pos present, if_pos oldPresent] using bound tested
  · simp only [if_neg present]
    have upper : (if tested ∈ oldSuffix then 1 else 2) ≤ 2 := by split <;> omega
    exact Nat.le_trans (bound tested) upper

theorem resolveLetter_reduced (prefixWords : List Nat) (letter : Nat) (chain : Chain)
    (red : Reduced chain) : Reduced (resolveLetter prefixWords letter chain) := by
  induction chain generalizing prefixWords with
  | stop gap =>
      by_cases pair : 2 ≤ gap.count letter
      · simpa [resolveLetter, pair] using resolveHead_reduced prefixWords letter (.stop gap) red pair
      · simpa [resolveLetter, pair] using red
  | step gap fresh tail ih =>
      by_cases pair : 2 ≤ gap.count letter
      · simpa [resolveLetter, pair] using resolveHead_reduced prefixWords letter (.step gap fresh tail) red pair
      · simp only [resolveLetter, if_neg pair, Reduced]
        refine ⟨gapBound_suffix_subset gap _ _ red.1 ?_, ih _ red.2⟩
        intro tested member
        rcases List.mem_cons.mp member with equal | later
        · exact List.mem_cons.mpr (Or.inl equal)
        · exact List.mem_cons_of_mem fresh
            (resolveLetter_support_subset (prefixWords ++ gap ++ [fresh]) letter tested tail later)

theorem resolveLetter_introductions (prefixWords : List Nat) (letter : Nat) (chain : Chain) :
    introductions (resolveLetter prefixWords letter chain) = introductions chain := by
  induction chain generalizing prefixWords with
  | stop gap => by_cases pair : 2 ≤ gap.count letter <;> simp [resolveLetter, pair, resolveHead_introductions]
  | step gap fresh tail ih =>
      by_cases pair : 2 ≤ gap.count letter <;>
        simp [resolveLetter, pair, resolveHead_introductions, introductions, ih]

theorem resolveLetter_simple (prefixWords : List Nat) (letter tested : Nat) (chain : Chain) :
    (prefixWords ++ flatten (resolveLetter prefixWords letter chain)).count tested = 1 ↔
      (prefixWords ++ flatten chain).count tested = 1 := by
  induction chain generalizing prefixWords with
  | stop gap =>
      by_cases pair : 2 ≤ gap.count letter
      · simpa [resolveLetter, pair] using resolveHead_simple prefixWords letter tested (.stop gap) pair
      · simp [resolveLetter, pair]
  | step gap fresh tail ih =>
      by_cases pair : 2 ≤ gap.count letter
      · simpa [resolveLetter, pair] using resolveHead_simple prefixWords letter tested (.step gap fresh tail) pair
      · simpa [resolveLetter, pair, flatten, List.append_assoc] using ih (prefixWords ++ gap ++ [fresh])

/-- Counts in each literal first-introduction gap, not merely total counts. -/
def gapProfile (tested : Nat) : Chain → List Nat
  | .stop gap => [gap.count tested]
  | .step gap _ tail => gap.count tested :: gapProfile tested tail

theorem pushPair_profile_other (letter tested : Nat) (chain : Chain) (unequal : tested ≠ letter) :
    gapProfile tested (pushPair letter chain) = gapProfile tested chain := by
  induction chain with
  | stop gap => simp [pushPair, gapProfile, List.count_append, Ne.symm unequal]
  | step gap fresh tail ih =>
      by_cases repeated : fresh ∈ flatten tail <;>
        simp [pushPair, repeated, gapProfile, List.count_append, Ne.symm unequal, ih]

theorem dropPair_profile_other (letter tested : Nat) (chain : Chain) (unequal : tested ≠ letter) :
    gapProfile tested (dropPair letter chain) = gapProfile tested chain := by
  cases chain <;> simp [dropPair, gapProfile, removePair, List.count_erase_of_ne unequal]

theorem resolveHead_profile_other (prefixWords : List Nat) (letter tested : Nat) (chain : Chain)
    (unequal : tested ≠ letter) :
    gapProfile tested (resolveHead prefixWords letter chain) = gapProfile tested chain := by
  cases found : Msg0457S11395Absorber.find (prefixWords ++ flatten chain) prefixWords letter <;>
    simp [resolveHead, found, pushPair_profile_other letter tested _ unequal, dropPair_profile_other letter tested chain unequal]

theorem resolveLetter_profile_other (prefixWords : List Nat) (letter tested : Nat) (chain : Chain)
    (unequal : tested ≠ letter) :
    gapProfile tested (resolveLetter prefixWords letter chain) = gapProfile tested chain := by
  induction chain generalizing prefixWords with
  | stop gap =>
      by_cases pair : 2 ≤ gap.count letter <;>
        simp [resolveLetter, pair, resolveHead_profile_other _ letter tested _ unequal]
  | step gap fresh tail ih =>
      by_cases pair : 2 ≤ gap.count letter <;>
        simp [resolveLetter, pair, resolveHead_profile_other _ letter tested _ unequal, gapProfile, ih]

def resolveLetters (prefixWords : List Nat) : List Nat → Chain → Chain
  | [], chain => chain
  | letter :: rest, chain => resolveLetters prefixWords rest (resolveLetter prefixWords letter chain)

theorem resolveLetters_wellFormed (prefixWords letters : List Nat) (chain : Chain)
    (good : WellFormed prefixWords chain) : WellFormed prefixWords (resolveLetters prefixWords letters chain) := by
  induction letters generalizing chain with
  | nil => exact good
  | cons letter rest ih => exact ih _ (resolveLetter_wellFormed prefixWords letter chain good)

theorem resolveLetters_derives (prefixWords letters : List Nat) (chain : Chain)
    (good : WellFormed prefixWords chain) :
    LD (prefixWords ++ flatten chain) (prefixWords ++ flatten (resolveLetters prefixWords letters chain)) := by
  induction letters generalizing chain with
  | nil => exact S5_107.ListDerives.refl _
  | cons letter rest ih =>
      exact (resolveLetter_derives prefixWords letter chain good).trans
        (ih _ (resolveLetter_wellFormed prefixWords letter chain good))

theorem resolveLetters_reduced (prefixWords letters : List Nat) (chain : Chain)
    (red : Reduced chain) : Reduced (resolveLetters prefixWords letters chain) := by
  induction letters generalizing chain with
  | nil => exact red
  | cons letter rest ih => exact ih _ (resolveLetter_reduced prefixWords letter chain red)

theorem resolveLetters_introductions (prefixWords letters : List Nat) (chain : Chain) :
    introductions (resolveLetters prefixWords letters chain) = introductions chain := by
  induction letters generalizing chain with
  | nil => rfl
  | cons letter rest ih => simp only [resolveLetters, ih, resolveLetter_introductions]

theorem resolveLetters_simple (prefixWords letters : List Nat) (tested : Nat) (chain : Chain) :
    (prefixWords ++ flatten (resolveLetters prefixWords letters chain)).count tested = 1 ↔
      (prefixWords ++ flatten chain).count tested = 1 := by
  induction letters generalizing chain with
  | nil => rfl
  | cons letter rest ih =>
      exact (ih (resolveLetter prefixWords letter chain)).trans
        (resolveLetter_simple prefixWords letter tested chain)

theorem resolveLetters_profile_untouched (prefixWords letters : List Nat) (tested : Nat) (chain : Chain)
    (untouched : tested ∉ letters) :
    gapProfile tested (resolveLetters prefixWords letters chain) = gapProfile tested chain := by
  induction letters generalizing chain with
  | nil => rfl
  | cons letter rest ih =>
      have unequal : tested ≠ letter := fun equal => untouched (List.mem_cons.mpr (Or.inl equal))
      have tailAbsent : tested ∉ rest := fun member => untouched (List.mem_cons_of_mem _ member)
      exact (ih _ tailAbsent).trans (resolveLetter_profile_other prefixWords letter tested chain unequal)

def sectorWord (word : Word Nat) : Word Nat :=
  let prefixWords := [word.head]
  let reduced := reduceChain prefixWords (factor prefixWords word.tail)
  let placed := resolveLetters prefixWords (canonicalLabels word.toList) reduced
  ⟨word.head, flatten (reduceChain prefixWords placed)⟩

theorem sectorWord_derives (word : Word Nat) : Derives basis word (sectorWord word) := by
  rcases word with ⟨head,tail⟩
  let original := factor [head] tail
  have good : WellFormed [head] original := factor_wellFormed [head] tail
  have start := reduceChain_derives [head] original good
  have reducedGood := reduceChain_wellFormed [head] original good
  let letters := canonicalLabels (head :: tail)
  have allocated := resolveLetters_derives [head] letters (reduceChain [head] original) reducedGood
  have allocatedGood := resolveLetters_wellFormed [head] letters (reduceChain [head] original) reducedGood
  have finish := reduceChain_derives [head] (resolveLetters [head] letters (reduceChain [head] original)) allocatedGood
  have full := start.trans (allocated.trans finish)
  have typed : LD (head :: tail)
      (head :: flatten (reduceChain [head] (resolveLetters [head] letters (reduceChain [head] original)))) := by
    simpa [original, factor_flatten] using full
  simpa [sectorWord, Word.toList, letters, original] using typed.toWord

theorem sectorWord_signature (word : Word Nat) :
    Msg0457S11395Observations.SameSignature word (sectorWord word) :=
  Msg0457S11395Signature.derives_preserve_signature (sectorWord_derives word)

end SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395ResolveLetter
