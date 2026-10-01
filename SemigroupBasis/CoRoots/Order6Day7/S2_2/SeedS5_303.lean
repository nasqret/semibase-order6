import SemigroupBasis.CoRoots.Order6Day7.S2_2.SeedS5_303ParityGuard
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCQuotientNormal
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCTransportNormalizer

/-!
# Unrestricted cyclic-two / `S5_303` rank-038 family seed

The actual `S2_2` factor fixes per-letter occurrence parity, and the actual
independently complete `S5_303` factor fixes support, singleton status, the
literal final variable, and a globally unique final pair.  The parity-safe
guarded calculus separately normalizes repeated finals to a common doubled
terminal marker and preserves the literal penultimate marker when the final
is unique.  The unrestricted intersection is proved before quotient
normalization; both authenticated six-element classes receive both
orientation endpoints.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank038.Seed

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.S5_83

universe u v

private abbrev terminalPair :=
  SemigroupBasis.CoRoots.S5_303.wordOfTerminalPair

private theorem perm_cons_to_end (letter : Nat) :
    ∀ stem : List Nat,
      (letter :: stem).Perm (stem ++ [letter])
  | [] => List.Perm.refl _
  | next :: rest =>
      (List.Perm.swap next letter rest).trans <|
        List.Perm.cons next (perm_cons_to_end letter rest)

/-- The exact frozen rotation remains valid under every preserved prefix. -/
theorem derivesRotateWithPrefix :
    ∀ (stem : List Nat) (left right : Nat),
      Derives basis
        (wordOfPrefixFinal (stem ++ [left, right]) left)
        (wordOfPrefixFinal (stem ++ [right, left]) left)
  | [], left, right => by
      simpa [wordOfPrefixFinal, Word.append_assoc] using
        derivesRotate (Word.singleton left) (Word.singleton right)
  | letter :: stem, left, right => by
      simpa [wordOfPrefixFinal, List.append_assoc] using
        Derives.prepend (Word.singleton letter)
          (derivesRotateWithPrefix stem left right)

/-- A globally repeated final letter can become the literal doubled terminal
guard without discarding parity or inventing a factor-theory implication. -/
theorem derivesMakeRepeatedFinal
    (stem : List Nat) (penultimate final : Nat)
    (repeated : final = penultimate ∨ final ∈ stem) :
    ∃ repeatedPrefix,
      Derives basis
        (terminalPair stem penultimate final)
        (terminalPair repeatedPrefix final final) ∧
      (∀ letter,
        (letter ∈ repeatedPrefix ∨ letter = final) ↔
          (letter ∈ stem ∨ letter = penultimate ∨ letter = final)) := by
  rcases repeated with equal | finalMember
  · subst penultimate
    refine ⟨stem, Derives.refl _, ?_⟩
    intro letter
    simp
  · have arrange :
        stem.Perm (stem.erase final ++ [final]) :=
      (List.perm_cons_erase finalMember).trans <|
        perm_cons_to_end final (stem.erase final)
    have arranged :=
      derivesPrefixPermutation arrange penultimate final
    have rotated :
        Derives basis
          (terminalPair (stem.erase final ++ [final]) penultimate final)
          (terminalPair (stem.erase final ++ [penultimate]) final final) := by
      simpa [terminalPair,
        SemigroupBasis.CoRoots.S5_303.wordOfTerminalPair,
        wordOfPrefixFinal, Word.append_assoc, List.append_assoc] using
        derivesRotateWithPrefix (stem.erase final) final penultimate
    refine
      ⟨stem.erase final ++ [penultimate],
        arranged.trans rotated, ?_⟩
    intro letter
    simp only [List.mem_append, List.mem_singleton]
    by_cases sameFinal : letter = final
    · subst letter
      simp [finalMember]
    · rw [List.mem_erase_of_ne sameFinal]
      simp [sameFinal, or_comm]

/-- Exact unrestricted completeness for the ACTUAL `S5_303` content/endpoint
signature plus independent cyclic-two occurrence parity. -/
theorem derivesOfSameParityContentEndpoint
    {left right : Word Nat}
    (same :
      SemigroupBasis.CoRoots.S5_303.SameContentEndpointSignature left right)
    (sameParity :
      SemigroupBasis.CoRoots.S5_441Invariant.SameOccurrenceParity left right) :
    Derives basis left right := by
  classical
  have leftReconstruct := terminalSplit_renderWord left
  have rightReconstruct := terminalSplit_renderWord right
  cases leftSplit : terminalSplit left with
  | singleton leftFinal =>
      cases rightSplit : terminalSplit right with
      | singleton rightFinal =>
          have targetFinal :
              SemigroupBasis.CoRoots.S5_303.FinalLetter right leftFinal :=
            (same.finalLetter leftFinal).mp <| by
              simp [SemigroupBasis.CoRoots.S5_303.FinalLetter, leftSplit]
          have finals : rightFinal = leftFinal := by
            simpa [SemigroupBasis.CoRoots.S5_303.FinalLetter, rightSplit] using
              targetFinal
          subst rightFinal
          rw [leftSplit] at leftReconstruct
          rw [rightSplit] at rightReconstruct
          rw [← leftReconstruct, ← rightReconstruct]
          exact Derives.refl _
      | pair rightPrefix rightPenultimate rightFinal =>
          have singletonLeft : IsSingletonWord left := by
            simp [IsSingletonWord, leftSplit]
          have singletonRight := same.singleton.mp singletonLeft
          simp [IsSingletonWord, rightSplit] at singletonRight
  | pair leftPrefix leftPenultimate leftFinal =>
      cases rightSplit : terminalSplit right with
      | singleton rightFinal =>
          have singletonRight : IsSingletonWord right := by
            simp [IsSingletonWord, rightSplit]
          have singletonLeft := same.singleton.mpr singletonRight
          simp [IsSingletonWord, leftSplit] at singletonLeft
      | pair rightPrefix rightPenultimate rightFinal =>
          have targetFinal :
              SemigroupBasis.CoRoots.S5_303.FinalLetter right leftFinal :=
            (same.finalLetter leftFinal).mp <| by
              simp [SemigroupBasis.CoRoots.S5_303.FinalLetter, leftSplit]
          have finals : rightFinal = leftFinal := by
            simpa [SemigroupBasis.CoRoots.S5_303.FinalLetter, rightSplit] using
              targetFinal
          subst rightFinal
          have sourceSupport :
              ∀ letter,
                (letter ∈ leftPrefix ∨ letter = leftPenultimate ∨
                    letter = leftFinal) ↔
                  (letter ∈ rightPrefix ∨ letter = rightPenultimate ∨
                    letter = leftFinal) := by
            intro letter
            have supported := same.support letter
            rw [← terminalSplit_renderList left,
              ← terminalSplit_renderList right,
              leftSplit, rightSplit] at supported
            simpa [TerminalSplit.renderList, List.mem_append,
              or_assoc] using supported
          have sourceParity :
              ∀ letter,
                (leftPrefix ++ [leftPenultimate, leftFinal]).count letter % 2 =
                  (rightPrefix ++ [rightPenultimate, leftFinal]).count letter %
                    2 := by
            intro letter
            have parity := sameParity letter
            rw [← terminalSplit_renderList left,
              ← terminalSplit_renderList right,
              leftSplit, rightSplit] at parity
            simpa [TerminalSplit.renderList] using parity
          rw [leftSplit] at leftReconstruct
          rw [rightSplit] at rightReconstruct
          rw [← leftReconstruct, ← rightReconstruct]
          by_cases leftRepeated :
              leftFinal = leftPenultimate ∨ leftFinal ∈ leftPrefix
          · have rightRepeated :
                leftFinal = rightPenultimate ∨ leftFinal ∈ rightPrefix := by
              apply Decidable.byContradiction
              intro notRepeated
              have rightParts := not_or.mp notRepeated
              have uniqueRight :
                  SemigroupBasis.CoRoots.S5_303.UniqueFinalPair right
                    rightPenultimate leftFinal := by
                simp [SemigroupBasis.CoRoots.S5_303.UniqueFinalPair,
                  rightSplit, rightParts.1, rightParts.2]
              have uniqueLeft :=
                (same.uniqueFinalPair
                  rightPenultimate leftFinal).mpr uniqueRight
              have leftParts :
                  leftPenultimate = rightPenultimate ∧
                    leftFinal = leftFinal ∧
                    leftFinal ≠ leftPenultimate ∧
                    leftFinal ∉ leftPrefix := by
                simpa [SemigroupBasis.CoRoots.S5_303.UniqueFinalPair,
                  leftSplit] using uniqueLeft
              rcases leftRepeated with equal | member
              · exact leftParts.2.2.1 equal
              · exact leftParts.2.2.2 member
            obtain ⟨normalizedLeft, leftDerivation, leftSupport⟩ :=
              derivesMakeRepeatedFinal
                leftPrefix leftPenultimate leftFinal leftRepeated
            obtain ⟨normalizedRight, rightDerivation, rightSupport⟩ :=
              derivesMakeRepeatedFinal
                rightPrefix rightPenultimate leftFinal rightRepeated
            have normalizedSupport :
                ∀ letter,
                  (letter ∈ normalizedLeft ∨ letter = leftFinal) ↔
                    (letter ∈ normalizedRight ∨ letter = leftFinal) := by
              intro letter
              exact
                (leftSupport letter).trans <|
                  (sourceSupport letter).trans (rightSupport letter).symm
            have leftPreserved :=
              SemigroupBasis.CoRoots.S5_441Invariant.sameOccurrenceParity_of_s2_2_valid
                ⟨terminalPair leftPrefix leftPenultimate leftFinal,
                  terminalPair normalizedLeft leftFinal leftFinal⟩
                (leftDerivation.sound leftModels)
            have rightPreserved :=
              SemigroupBasis.CoRoots.S5_441Invariant.sameOccurrenceParity_of_s2_2_valid
                ⟨terminalPair rightPrefix rightPenultimate leftFinal,
                  terminalPair normalizedRight leftFinal leftFinal⟩
                (rightDerivation.sound leftModels)
            have normalizedParity :
                ∀ letter,
                  normalizedLeft.count letter % 2 =
                    normalizedRight.count letter % 2 := by
              intro letter
              have preserveLeft := leftPreserved letter
              have preserveRight := rightPreserved letter
              have original := sourceParity letter
              simp only [terminalPair,
                SemigroupBasis.CoRoots.S5_303.toList_wordOfTerminalPair,
                List.count_append] at preserveLeft preserveRight
              simp only [List.count_append] at original
              omega
            have middle :=
              derivesSameGuardedPair
                normalizedLeft normalizedRight leftFinal leftFinal
                normalizedSupport normalizedParity
            exact leftDerivation.trans (middle.trans rightDerivation.symm)
          · have leftUniqueParts := not_or.mp leftRepeated
            have uniqueLeft :
                SemigroupBasis.CoRoots.S5_303.UniqueFinalPair left
                  leftPenultimate leftFinal := by
              simp [SemigroupBasis.CoRoots.S5_303.UniqueFinalPair,
                leftSplit, leftUniqueParts.1, leftUniqueParts.2]
            have uniqueRight :=
              (same.uniqueFinalPair
                leftPenultimate leftFinal).mp uniqueLeft
            have rightParts :
                rightPenultimate = leftPenultimate ∧
                  leftFinal = leftFinal ∧
                  leftFinal ≠ rightPenultimate ∧
                  leftFinal ∉ rightPrefix := by
              simpa [SemigroupBasis.CoRoots.S5_303.UniqueFinalPair,
                rightSplit] using uniqueRight
            have penultimates : rightPenultimate = leftPenultimate :=
              rightParts.1
            subst rightPenultimate
            have guardedSupport :
                ∀ letter,
                  (letter ∈ leftPrefix ∨ letter = leftPenultimate) ↔
                    (letter ∈ rightPrefix ∨ letter = leftPenultimate) := by
              intro letter
              by_cases isFinal : letter = leftFinal
              · subst letter
                simp [leftUniqueParts.1, leftUniqueParts.2,
                  rightParts.2.2.2]
              · simpa [isFinal] using sourceSupport letter
            have guardedParity :
                ∀ letter,
                  leftPrefix.count letter % 2 =
                    rightPrefix.count letter % 2 := by
              intro letter
              have original := sourceParity letter
              simp only [List.count_append] at original
              omega
            exact
              derivesSameGuardedPair
                leftPrefix rightPrefix leftPenultimate leftFinal
                guardedSupport guardedParity

/-- The two ACTUAL factors independently discharge the exact unrestricted
content/endpoint and cyclic-parity obligations. -/
theorem derivesOfFactorValid
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy leftTable.semigroup)
    (rightValid : identity.SatisfiedBy rightTable.semigroup) :
    Derives basis identity.lhs identity.rhs := by
  have signature :=
    SemigroupBasis.CoRoots.S5_303.valid_signature identity rightValid
  have parity :=
    SemigroupBasis.CoRoots.S5_441Invariant.sameOccurrenceParity_of_s2_2_valid
      identity leftValid
  exact derivesOfSameParityContentEndpoint signature parity

/-- Genuine unrestricted factor-intersection completeness precedes quotient
normalization and both six-element class endpoints. -/
def intersectionBasis :
    IntersectionBasis leftTable.semigroup rightTable.semigroup basis where
  leftModels := leftModels
  rightModels := rightModels
  complete := derivesOfFactorValid

noncomputable def normalizer :
    IntersectionNormalizer leftTable.semigroup rightTable.semigroup basis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer
    intersectionBasis

theorem s6_4025_representative_basis :
    BasisFor S6_4025.table.semigroup basis :=
  S6_4025.representative_basis_of_normalizer normalizer

theorem s6_4025_opposite_basis :
    BasisFor S6_4025.table.semigroup.opposite (reversedBasis basis) :=
  S6_4025.opposite_basis_of_normalizer normalizer

theorem s6_4240_representative_basis :
    BasisFor S6_4240.table.semigroup basis :=
  S6_4240.representative_basis_of_normalizer normalizer

theorem s6_4240_opposite_basis :
    BasisFor S6_4240.table.semigroup.opposite (reversedBasis basis) :=
  S6_4240.opposite_basis_of_normalizer normalizer

/-- Reuse the reviewed generic transport only with independently supplied
displayed-law derivations and the actual two factor-theory implications. -/
noncomputable def transportedNormalizer
    {A : Type u} {B : Type v}
    {targetLeft : Semigroup A} {targetRight : Semigroup B}
    {targetBasis : List (Identity Nat)}
    (lawDerivations :
      ∀ law : Identity Nat,
        law ∈ basis → Derives targetBasis law.lhs law.rhs)
    (leftTheory :
      ∀ identity : Identity Nat,
        identity.SatisfiedBy targetLeft →
          identity.SatisfiedBy leftTable.semigroup)
    (rightTheory :
      ∀ identity : Identity Nat,
        identity.SatisfiedBy targetRight →
          identity.SatisfiedBy rightTable.semigroup) :
    IntersectionNormalizer targetLeft targetRight targetBasis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.transportNormalizer
    normalizer lawDerivations leftTheory rightTheory

end SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank038.Seed
