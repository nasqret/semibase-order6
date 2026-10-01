import SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395ResolveLetter

/-! Final gap sorting does not change a reduced chain's coordinates.
The actual canonical chain is determined by its introductions and all gap
profiles. Signature-to-profile reconstruction remains a separate obligation. -/

namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395ProfileComparison

open SemigroupBasis
open Msg0457S11395SeenSwaps Msg0457S11395SeenGap Msg0457S11395PositiveRuns
open Msg0457S11395FutureRuns Msg0457S11395FutureGap Msg0457S11395WordGaps
open Msg0457S11395WordReduction Msg0457S11395ResolveLetter

theorem futureCopies_fixed (suffix : List Nat) (tested copies : Nat)
    (bound : copies ≤ if tested ∈ suffix then 1 else 2) :
    futureCopies suffix tested copies = copies := by
  by_cases present : tested ∈ suffix
  · have small : copies < 2 := by simpa only [if_pos present] using Nat.lt_succ_of_le bound
    simpa only [futureCopies, if_pos present] using Nat.mod_eq_of_lt small
  · have small : copies ≤ 2 := by simpa only [if_neg present] using bound
    simp only [futureCopies, if_neg present]
    rcases (show copies = 0 ∨ copies = 1 ∨ copies = 2 by omega) with zero | one | two
    · rw [zero]; rfl
    · rw [one]; rfl
    · rw [two]; rfl

theorem futureGap_count_of_bound (prefixWords gap suffix : List Nat)
    (seen : AllSeen prefixWords gap) (bound : GapBound gap suffix) (tested : Nat) :
    (futureGap prefixWords gap suffix).count tested = gap.count tested := by
  rw [futureGap_count _ _ _ seen]
  exact futureCopies_fixed suffix tested _ (bound tested)

theorem reduceChain_profile (prefixWords : List Nat) (chain : Chain)
    (good : WellFormed prefixWords chain) (red : Reduced chain) (tested : Nat) :
    gapProfile tested (reduceChain prefixWords chain) = gapProfile tested chain := by
  induction chain generalizing prefixWords with
  | stop gap =>
      exact congrArg (fun count => [count]) (futureGap_count_of_bound prefixWords gap [] good red tested)
  | step gap fresh tail ih =>
      have bound : GapBound gap (fresh :: flatten (reduceChain (prefixWords ++ gap ++ [fresh]) tail)) := by
        apply gapBound_suffix_subset gap _ _ red.1
        intro letter member
        rcases List.mem_cons.mp member with equal | later
        · exact List.mem_cons.mpr (Or.inl equal)
        · exact List.mem_cons_of_mem fresh
            ((reduceChain_support (prefixWords ++ gap ++ [fresh]) tail good.2.2 letter).mp later)
      change (futureGap prefixWords gap _).count tested ::
          gapProfile tested (reduceChain (prefixWords ++ gap ++ [fresh]) tail) =
        gap.count tested :: gapProfile tested tail
      rw [futureGap_count_of_bound prefixWords gap _ good.1 bound tested,
        ih (prefixWords ++ gap ++ [fresh]) good.2.2 red.2]

theorem futureGap_eq_of_counts (leftPrefix rightPrefix leftGap rightGap suffix : List Nat)
    (samePrefix : ∀ tested, tested ∈ leftPrefix ↔ tested ∈ rightPrefix)
    (sameCounts : ∀ tested, leftGap.count tested = rightGap.count tested) :
    futureGap leftPrefix leftGap suffix = futureGap rightPrefix rightGap suffix := by
  unfold futureGap
  rw [canonicalLabels_eq_of_support leftPrefix rightPrefix samePrefix]
  apply renderCounts_congr
  intro tested
  rw [sameCounts tested]

/-- No bounded-word, finite-alphabet or supplied-renderer premise. -/
theorem reduceChain_eq_of_profiles (left right : Chain) (leftPrefix rightPrefix : List Nat)
    (samePrefix : ∀ tested, tested ∈ leftPrefix ↔ tested ∈ rightPrefix)
    (sameIntroductions : introductions left = introductions right)
    (sameProfiles : ∀ tested, gapProfile tested left = gapProfile tested right) :
    reduceChain leftPrefix left = reduceChain rightPrefix right := by
  induction left generalizing right leftPrefix rightPrefix with
  | stop leftGap =>
      cases right with
      | stop rightGap =>
          apply congrArg Chain.stop
          exact futureGap_eq_of_counts leftPrefix rightPrefix leftGap rightGap [] samePrefix
            (fun tested => (List.cons.inj (sameProfiles tested)).1)
      | step rightGap fresh tail => simp [introductions] at sameIntroductions
  | step leftGap fresh leftTail ih =>
      cases right with
      | stop rightGap => simp [introductions] at sameIntroductions
      | step rightGap nextFresh rightTail =>
          have markers := List.cons.inj sameIntroductions
          have equalFresh : fresh = nextFresh := markers.1
          subst nextFresh
          have sameCounts : ∀ tested, leftGap.count tested = rightGap.count tested :=
            fun tested => (List.cons.inj (sameProfiles tested)).1
          have gapSupport : ∀ tested, tested ∈ leftGap ↔ tested ∈ rightGap := by
            intro tested
            rw [← List.count_pos_iff, ← List.count_pos_iff, sameCounts tested]
          have tailPrefix : ∀ tested,
              tested ∈ leftPrefix ++ leftGap ++ [fresh] ↔ tested ∈ rightPrefix ++ rightGap ++ [fresh] := by
            intro tested
            simp only [List.mem_append, samePrefix tested, gapSupport tested]
          have tailEqual := ih rightTail (leftPrefix ++ leftGap ++ [fresh])
            (rightPrefix ++ rightGap ++ [fresh]) tailPrefix markers.2
            (fun tested => (List.cons.inj (sameProfiles tested)).2)
          simp only [reduceChain, tailEqual]
          exact congrArg (fun gap => Chain.step gap fresh
              (reduceChain (rightPrefix ++ rightGap ++ [fresh]) rightTail))
            (futureGap_eq_of_counts leftPrefix rightPrefix leftGap rightGap _ samePrefix sameCounts)

theorem reduceChain_eq_iff_profiles (prefixWords : List Nat) (left right : Chain)
    (leftGood : WellFormed prefixWords left) (rightGood : WellFormed prefixWords right)
    (leftRed : Reduced left) (rightRed : Reduced right)
    (sameIntroductions : introductions left = introductions right) :
    reduceChain prefixWords left = reduceChain prefixWords right ↔
      ∀ tested, gapProfile tested left = gapProfile tested right := by
  constructor
  · intro equal tested
    rw [← reduceChain_profile prefixWords left leftGood leftRed tested,
      ← reduceChain_profile prefixWords right rightGood rightRed tested, equal]
  · exact reduceChain_eq_of_profiles left right prefixWords prefixWords (fun _ => Iff.rfl) sameIntroductions

def placedChain (word : Word Nat) : Chain :=
  resolveLetters [word.head] (canonicalLabels word.toList)
    (reduceChain [word.head] (factor [word.head] word.tail))

theorem placedChain_wellFormed (word : Word Nat) : WellFormed [word.head] (placedChain word) :=
  resolveLetters_wellFormed _ _ _
    (reduceChain_wellFormed _ _ (factor_wellFormed _ _))

theorem placedChain_reduced (word : Word Nat) : Reduced (placedChain word) :=
  resolveLetters_reduced _ _ _ (reduceChain_reduced _ _ (factor_wellFormed _ _))

theorem placedChain_introductions (word : Word Nat) :
    introductions (placedChain word) = introductions (factor [word.head] word.tail) := by
  unfold placedChain
  rw [resolveLetters_introductions, reduceChain_introductions]

theorem sectorWord_factor (word : Word Nat) :
    factor [word.head] (sectorWord word).tail = reduceChain [word.head] (placedChain word) :=
  factor_of_wellFormed _ _ (reduceChain_wellFormed _ _ (placedChain_wellFormed word))

theorem sectorWord_profile (word : Word Nat) (tested : Nat) :
    gapProfile tested (factor [word.head] (sectorWord word).tail) = gapProfile tested (placedChain word) := by
  rw [sectorWord_factor]
  exact reduceChain_profile _ _ (placedChain_wellFormed word) (placedChain_reduced word) tested

theorem sectorWord_eq_of_profiles (left right : Word Nat)
    (sameHead : left.head = right.head)
    (sameIntroductions : introductions (factor [left.head] left.tail) =
      introductions (factor [right.head] right.tail))
    (sameProfiles : ∀ tested, gapProfile tested (placedChain left) = gapProfile tested (placedChain right)) :
    sectorWord left = sectorWord right := by
  have chainEqual := reduceChain_eq_of_profiles (placedChain left) (placedChain right)
    [left.head] [right.head] (by intro tested; rw [sameHead])
    ((placedChain_introductions left).trans (sameIntroductions.trans (placedChain_introductions right).symm))
    sameProfiles
  apply Word.toList_injective
  change left.head :: flatten (reduceChain [left.head] (placedChain left)) =
    right.head :: flatten (reduceChain [right.head] (placedChain right))
  rw [chainEqual, sameHead]

theorem sectorWord_profiles_of_eq (left right : Word Nat)
    (equal : sectorWord left = sectorWord right) (tested : Nat) :
    gapProfile tested (placedChain left) = gapProfile tested (placedChain right) := by
  have sameHead : left.head = right.head := by
    have heads := congrArg (fun word : Word Nat => word.head) equal
    exact heads
  rw [← sectorWord_profile left tested, ← sectorWord_profile right tested, sameHead, equal]

theorem sectorWord_eq_iff_profiles (left right : Word Nat)
    (sameHead : left.head = right.head)
    (sameIntroductions : introductions (factor [left.head] left.tail) =
      introductions (factor [right.head] right.tail)) :
    sectorWord left = sectorWord right ↔
      ∀ tested, gapProfile tested (placedChain left) = gapProfile tested (placedChain right) :=
  ⟨sectorWord_profiles_of_eq left right, sectorWord_eq_of_profiles left right sameHead sameIntroductions⟩

end SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395ProfileComparison
