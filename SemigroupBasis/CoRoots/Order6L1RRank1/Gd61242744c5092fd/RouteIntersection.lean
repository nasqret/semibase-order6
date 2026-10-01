import SemigroupBasis.CoRoots.Order6L1RRank1.Gd61242744c5092fd.CapTwoConnectivity
import SemigroupBasis.Examples.UniqueSeparatorFourNormalForm
import SemigroupBasis.Subdirect

/-!
# Unrestricted Gd intersection from the recorded cap-two route

The frozen legacy `ComponentEnvelope`/`Completeness` chain does not elaborate:
its data-valued envelope eliminates propositional existence into `Type`.
This successor deliberately imports none of that chain.  Instead the four
displayed deletion laws normalize every nonempty word to its first/last
occurrence cap, the recorded contextual route connects the two capped words,
and route soundness converts that connection into an unrestricted derivation.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace SemigroupBasis.CoRoots.Order6L1RRank1.Gd61242744c5092fd

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.Order6L1RRank1

namespace CapTwoRouteCompletion

private abbrev ListDerives : List Nat → List Nat → Prop :=
  S5_107.ListDerives basis

private abbrev listWordOfCons :=
  S5_107.listWordOfCons

private theorem derivesPowerExpansion (block : Word Nat) :
    Derives basis (block ++ block) ((block ++ block) ++ block) := by
  simpa only [Word.append_assoc] using derivesDisplayedLaw000 block

private theorem derivesLeftContraction (endpoint middle : Word Nat) :
    Derives basis
      (((endpoint ++ endpoint) ++ middle) ++ endpoint)
      ((endpoint ++ middle) ++ endpoint) := by
  simpa only [Word.append_assoc] using
    derivesDisplayedLaw001 endpoint middle

private theorem derivesRightExpansion (endpoint middle : Word Nat) :
    Derives basis
      ((endpoint ++ middle) ++ endpoint)
      (((endpoint ++ middle) ++ endpoint) ++ endpoint) := by
  simpa only [Word.append_assoc] using
    derivesDisplayedLaw002 endpoint middle

private theorem derivesThirdOccurrenceDeletion
    (endpoint leftGap rightGap : Word Nat) :
    Derives basis
      ((((endpoint ++ leftGap) ++ endpoint) ++ rightGap) ++ endpoint)
      (((endpoint ++ leftGap) ++ rightGap) ++ endpoint) := by
  simpa only [Word.append_assoc] using
    derivesDisplayedLaw005 endpoint leftGap rightGap

private theorem listDerivesDeleteMiddleCore
    (letter : Nat) (leftGap rightGap : List Nat) :
    ListDerives
      ([letter] ++ leftGap ++ [letter] ++ rightGap ++ [letter])
      ([letter] ++ leftGap ++ rightGap ++ [letter]) := by
  cases leftGap with
  | nil =>
      cases rightGap with
      | nil =>
          exact S5_107.ListDerives.words <| by
            simpa [listWordOfCons, Word.singleton, Word.append,
              Word.append_assoc, List.append_assoc] using
                (derivesPowerExpansion (Word.singleton letter)).symm
      | cons rightHead rightTail =>
          exact S5_107.ListDerives.words <| by
            simpa [listWordOfCons, Word.singleton, Word.append,
              Word.append_assoc, List.append_assoc] using
                derivesLeftContraction
                  (Word.singleton letter)
                  (listWordOfCons rightHead rightTail)
  | cons leftHead leftTail =>
      cases rightGap with
      | nil =>
          exact S5_107.ListDerives.words <| by
            simpa [listWordOfCons, Word.singleton, Word.append,
              Word.append_assoc, List.append_assoc] using
                (derivesRightExpansion
                  (Word.singleton letter)
                  (listWordOfCons leftHead leftTail)).symm
      | cons rightHead rightTail =>
          exact S5_107.ListDerives.words <| by
            simpa [listWordOfCons, Word.singleton, Word.append,
              Word.append_assoc, List.append_assoc] using
                derivesThirdOccurrenceDeletion
                  (Word.singleton letter)
                  (listWordOfCons leftHead leftTail)
                  (listWordOfCons rightHead rightTail)

private theorem listDerivesDeleteCurrent
    (pre suffix : List Nat) (letter : Nat)
    (past : letter ∈ pre) (future : letter ∈ suffix) :
    ListDerives (pre ++ letter :: suffix) (pre ++ suffix) := by
  rcases List.append_of_mem past with ⟨before, firstGap, preShape⟩
  rcases List.append_of_mem future with ⟨secondGap, after, suffixShape⟩
  rw [preShape, suffixShape]
  simpa [List.append_assoc] using
    (listDerivesDeleteMiddleCore letter firstGap secondGap).context before after

private theorem listDerivesCapScanAux
    (pre seen : List Nat)
    (seenInPre : ∀ tested ∈ seen, tested ∈ pre) :
    ∀ suffix : List Nat,
      ListDerives
        (pre ++ suffix)
        (pre ++ uniqueSeparatorEndpointCapAux seen suffix)
  | [] => by
      simpa using S5_107.ListDerives.refl (basis := basis) pre
  | letter :: rest => by
      by_cases middle : letter ∈ seen ∧ letter ∈ rest
      · have letterInPre : letter ∈ pre := seenInPre letter middle.1
        have deleteCurrent :
            ListDerives (pre ++ letter :: rest) (pre ++ rest) :=
          listDerivesDeleteCurrent pre rest letter letterInPre middle.2
        have nextSeenInPre : ∀ tested ∈ letter :: seen, tested ∈ pre := by
          intro tested member
          rcases List.mem_cons.mp member with rfl | member
          · exact letterInPre
          · exact seenInPre tested member
        have recurse :=
          listDerivesCapScanAux pre (letter :: seen) nextSeenInPre rest
        rw [uniqueSeparatorEndpointCapAux, if_pos middle]
        exact deleteCurrent.trans recurse
      · have nextSeenInPre :
            ∀ tested ∈ letter :: seen, tested ∈ pre ++ [letter] := by
          intro tested member
          rcases List.mem_cons.mp member with rfl | member
          · exact List.mem_append_right pre (List.Mem.head [])
          · exact List.mem_append_left [letter] (seenInPre tested member)
        have recurse :=
          listDerivesCapScanAux
            (pre ++ [letter]) (letter :: seen) nextSeenInPre rest
        rw [uniqueSeparatorEndpointCapAux, if_neg middle]
        simpa [List.append_assoc] using recurse

/-- The recorded displayed laws reduce every list to its cap-two scan. -/
theorem listDerivesCapScan (letters : List Nat) :
    S5_107.ListDerives basis letters (uniqueSeparatorEndpointCap letters) := by
  simpa [uniqueSeparatorEndpointCap] using
    listDerivesCapScanAux [] [] (by simp) letters

/-- Keep the original head and scan only its tail after registering the head. -/
def cappedWord (word : Word Nat) : Word Nat :=
  ⟨word.head, uniqueSeparatorEndpointCapAux [word.head] word.tail⟩

theorem cappedWord_toList (word : Word Nat) :
    (cappedWord word).toList = uniqueSeparatorEndpointCap word.toList := by
  cases word with
  | mk head tail =>
      simp [cappedWord, Word.toList, uniqueSeparatorEndpointCap,
        uniqueSeparatorEndpointCapAux]

theorem cappedWord_limited (word : Word Nat) (letter : Nat) :
    (cappedWord word).toList.count letter ≤ 2 := by
  rw [cappedWord_toList]
  exact uniqueSeparatorEndpointCap_count_le_two letter word.toList

/-- The cap is an actual unrestricted semigroup-word derivation. -/
theorem derivesCappedWord (word : Word Nat) :
    Derives basis word (cappedWord word) := by
  cases word with
  | mk head tail =>
      have capped :
          S5_107.ListDerives basis
            (head :: tail)
            (head :: uniqueSeparatorEndpointCapAux [head] tail) := by
        simpa [uniqueSeparatorEndpointCap, uniqueSeparatorEndpointCapAux] using
          listDerivesCapScan (head :: tail)
      simpa [S5_107.listWordOfCons, cappedWord] using
        S5_107.ListDerives.toWord capped

end CapTwoRouteCompletion

/-- Soundness of the exact eleven-law route basis in the left factor. -/
theorem left_models :
    Models SemigroupBasis.Generated.S4_70.table.semigroup basis :=
  CapTwoRTCRoute.left_models

/-- Soundness of the exact eleven-law route basis in the right factor. -/
theorem right_models :
    Models SemanticBlockSignature.table.semigroup basis :=
  CapTwoRTCRoute.right_models

/-- Unrestricted completeness follows by capping, route connectivity, and
reversing the target cap derivation. No legacy envelope is imported. -/
theorem derivesOfFactorValid
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy SemigroupBasis.Generated.S4_70.table.semigroup)
    (rightValid : identity.SatisfiedBy SemanticBlockSignature.table.semigroup) :
    Derives basis identity.lhs identity.rhs := by
  have original :=
    CapTwoRTCRoute.sameFactor_of_factor_valid identity leftValid rightValid
  have leftCap := CapTwoRouteCompletion.derivesCappedWord identity.lhs
  have rightCap := CapTwoRouteCompletion.derivesCappedWord identity.rhs
  have leftSame := CapTwoRTCRoute.sameFactor_of_derives leftCap
  have rightSame := CapTwoRTCRoute.sameFactor_of_derives rightCap
  have cappedSame := (leftSame.symm.trans original).trans rightSame
  have reached := CapTwoRTCRoute.capTwo_sameFactor_rtc
    (CapTwoRouteCompletion.cappedWord_limited identity.lhs)
    (CapTwoRouteCompletion.cappedWord_limited identity.rhs)
    cappedSame
  have cappedDerivation :=
    CapTwoRTCRoute.contextualFrozenRTC_derives reached
  exact leftCap.trans (cappedDerivation.trans rightCap.symm)

/-- The real unrestricted intersection, now dependent on the recorded route. -/
def intersectionBasis :
    IntersectionBasis
      SemigroupBasis.Generated.S4_70.table.semigroup
      SemanticBlockSignature.table.semigroup
      basis where
  leftModels := left_models
  rightModels := right_models
  complete := derivesOfFactorValid

end SemigroupBasis.CoRoots.Order6L1RRank1.Gd61242744c5092fd
