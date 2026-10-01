import SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395ProfileComparison

/-! An actual selected letter's gap profile is frozen through the unused
support suffix and final sorting. The selector cut is literal and nodup;
there is no caller-supplied canonicality certificate. -/

namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395ProcessedProfiles

open SemigroupBasis
open Msg0457S11395SeenGap Msg0457S11395WordGaps Msg0457S11395WordReduction
open Msg0457S11395ResolveLetter Msg0457S11395ProfileComparison

theorem resolveLetters_append (prefixWords before after : List Nat) (chain : Chain) :
    resolveLetters prefixWords (before ++ after) chain =
      resolveLetters prefixWords after (resolveLetters prefixWords before chain) := by
  induction before generalizing chain with
  | nil => rfl
  | cons letter rest ih =>
      exact ih (resolveLetter prefixWords letter chain)

theorem processed_profile_frozen (prefixWords before after : List Nat) (tested : Nat) (chain : Chain)
    (absent : tested ∉ after) :
    gapProfile tested (resolveLetters prefixWords (before ++ tested :: after) chain) =
      gapProfile tested (resolveLetter prefixWords tested (resolveLetters prefixWords before chain)) := by
  rw [resolveLetters_append]
  exact resolveLetters_profile_untouched prefixWords after tested _ absent

theorem processed_profile_final_sort (prefixWords before after : List Nat) (tested : Nat) (chain : Chain)
    (good : WellFormed prefixWords chain) (red : Reduced chain) (absent : tested ∉ after) :
    gapProfile tested (reduceChain prefixWords (resolveLetters prefixWords (before ++ tested :: after) chain)) =
      gapProfile tested (resolveLetter prefixWords tested (resolveLetters prefixWords before chain)) := by
  rw [reduceChain_profile prefixWords _ (resolveLetters_wellFormed _ _ _ good)
    (resolveLetters_reduced _ _ _ red)]
  exact processed_profile_frozen prefixWords before after tested chain absent

theorem selector_cut_no_repeat (word : Word Nat) (before after : List Nat) (tested : Nat)
    (cut : canonicalLabels word.toList = before ++ tested :: after) : tested ∉ after := by
  have unique := canonicalLabels_nodup word.toList
  rw [cut] at unique
  have suffixUnique : (tested :: after).Nodup := (List.nodup_append.mp unique).2.1
  exact (List.nodup_cons.mp suffixUnique).1

/-- Final, actually refactored output profile, at a literal selector cut. -/
theorem sectorWord_processed_profile (word : Word Nat) (before after : List Nat) (tested : Nat)
    (cut : canonicalLabels word.toList = before ++ tested :: after) :
    gapProfile tested (factor [word.head] (sectorWord word).tail) =
      gapProfile tested (resolveLetter [word.head] tested
        (resolveLetters [word.head] before (reduceChain [word.head] (factor [word.head] word.tail)))) := by
  rw [sectorWord_profile]
  unfold placedChain
  rw [cut]
  exact processed_profile_frozen [word.head] before after tested _ (selector_cut_no_repeat word before after tested cut)

theorem sectorWord_processed_profile_exists (word : Word Nat) (tested : Nat)
    (member : tested ∈ word.toList) :
    ∃ before after : List Nat,
      canonicalLabels word.toList = before ++ tested :: after ∧ tested ∉ after ∧
      gapProfile tested (factor [word.head] (sectorWord word).tail) =
        gapProfile tested (resolveLetter [word.head] tested
          (resolveLetters [word.head] before (reduceChain [word.head] (factor [word.head] word.tail)))) := by
  obtain ⟨before,after,cut⟩ := List.append_of_mem ((canonicalLabels_mem word.toList tested).mpr member)
  exact ⟨before,after,cut,selector_cut_no_repeat word before after tested cut,
    sectorWord_processed_profile word before after tested cut⟩

end SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395ProcessedProfiles
