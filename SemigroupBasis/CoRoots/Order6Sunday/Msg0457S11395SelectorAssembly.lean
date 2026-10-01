import SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395SignatureResolver

/-! Actual selector prefixes inherit the original signature. Once a target
is processed, its exact profile is signature-determined and remains frozen
through later selectors. This assembles every placedChain coordinate. -/

namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395SelectorAssembly

open SemigroupBasis
open Msg0457S11395Semantics Msg0457S11395EvenInsertion Msg0457S11395SeenGap
open Msg0457S11395WordGaps Msg0457S11395WordReduction Msg0457S11395ResolveLetter
open Msg0457S11395Observations Msg0457S11395Signature Msg0457S11395CoordinateSectors
open Msg0457S11395ProfileComparison Msg0457S11395ProcessedProfiles Msg0457S11395GapParity
open Msg0457S11395ProfileSupport Msg0457S11395SignatureResolver

def stageChain (word : Word Nat) (before : List Nat) : Chain :=
  resolveLetters [word.head] before (reduceChain [word.head] (factor [word.head] word.tail))

def stageWord (word : Word Nat) (before : List Nat) : Word Nat :=
  ⟨word.head,flatten (stageChain word before)⟩

theorem stageChain_wellFormed (word : Word Nat) (before : List Nat) :
    WellFormed [word.head] (stageChain word before) :=
  resolveLetters_wellFormed _ _ _ (reduceChain_wellFormed _ _ (factor_wellFormed _ _))

theorem stageChain_reduced (word : Word Nat) (before : List Nat) : Reduced (stageChain word before) :=
  resolveLetters_reduced _ _ _ (reduceChain_reduced _ _ (factor_wellFormed _ _))

theorem stageWord_derives (word : Word Nat) (before : List Nat) : Derives basis word (stageWord word before) := by
  have start := reduceChain_derives [word.head] (factor [word.head] word.tail) (factor_wellFormed _ _)
  have next := resolveLetters_derives [word.head] before (reduceChain [word.head] (factor [word.head] word.tail))
    (reduceChain_wellFormed _ _ (factor_wellFormed _ _))
  have full := start.trans next
  rw [factor_flatten] at full
  exact (show LD (word.head :: word.tail) (word.head :: flatten (stageChain word before)) from full).toWord

theorem stageWord_signature (word : Word Nat) (before : List Nat) : SameSignature word (stageWord word before) :=
  derives_preserve_signature (stageWord_derives word before)

theorem stageWords_sameSignature (left right : Word Nat) (leftBefore rightBefore : List Nat)
    (same : SameSignature left right) : SameSignature (stageWord left leftBefore) (stageWord right rightBefore) := by
  have leftSound := (stageWord_derives left leftBefore).sound models
  have rightSound := (stageWord_derives right rightBefore).sound models
  have original := valid_of_sameSignature ⟨left,right⟩ same
  apply sameSignature_of_valid ⟨stageWord left leftBefore,stageWord right rightBefore⟩
  intro valuation
  exact (leftSound valuation).symm.trans ((original valuation).trans (rightSound valuation))

theorem stage_profile_empty (word : Word Nat) (before : List Nat) (tested : Nat) (absent : tested ∉ word.toList) :
    positive (gapProfile tested (stageChain word before)) = false := by
  have signature := stageWord_signature word before
  have newAbsent : tested ∉ (stageWord word before).toList := fun member => absent ((signature.support tested).mpr member)
  have zero := List.count_eq_zero.mpr newAbsent
  apply profile_zero_of_small [word.head] (stageChain word before) tested (stageChain_wellFormed word before)
  change (stageWord word before).toList.count tested < 2
  rw [zero]
  decide

theorem signature_selected_profile (left right : Word Nat) (same : SameSignature left right)
    (before after : List Nat) (tested : Nat)
    (cut : canonicalLabels left.toList = before ++ tested :: after) :
    gapProfile tested (placedChain left) = gapProfile tested (placedChain right) := by
  have sameLabels := canonicalLabels_eq_of_support left.toList right.toList same.support
  have rightCut : canonicalLabels right.toList = before ++ tested :: after := sameLabels.symm.trans cut
  have leftProfile := sectorWord_processed_profile left before after tested cut
  have rightProfile := sectorWord_processed_profile right before after tested rightCut
  rw [sectorWord_profile] at leftProfile rightProfile
  have processed := signature_resolver_profile left.head right.head tested
    (stageChain left before) (stageChain right before)
    (stageChain_wellFormed left before) (stageChain_wellFormed right before)
    (stageChain_reduced left before) (stageChain_reduced right before)
    (stageWords_sameSignature left right before before same)
  exact leftProfile.trans (processed.trans rightProfile.symm)

theorem signature_placed_profiles (left right : Word Nat) (same : SameSignature left right) (tested : Nat) :
    gapProfile tested (placedChain left) = gapProfile tested (placedChain right) := by
  by_cases present : tested ∈ left.toList
  · obtain ⟨before,after,cut⟩ := List.append_of_mem ((canonicalLabels_mem left.toList tested).mpr present)
    exact signature_selected_profile left right same before after tested cut
  · have rightAbsent : tested ∉ right.toList := fun member => present ((same.support tested).mpr member)
    have leftEmpty := stage_profile_empty left (canonicalLabels left.toList) tested present
    have rightEmpty := stage_profile_empty right (canonicalLabels right.toList) tested rightAbsent
    have signatures := stageWords_sameSignature left right
      (canonicalLabels left.toList) (canonicalLabels right.toList) same
    have profileBits := signature_gapBits left.head right.head tested (placedChain left) (placedChain right)
      (placedChain_wellFormed left) (placedChain_wellFormed right) signatures
    change positive (gapProfile tested (placedChain left)) = false at leftEmpty
    change positive (gapProfile tested (placedChain right)) = false at rightEmpty
    rw [bits_of_no_positive _ leftEmpty, bits_of_no_positive _ rightEmpty] at profileBits
    exact profileBits

end SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395SelectorAssembly
