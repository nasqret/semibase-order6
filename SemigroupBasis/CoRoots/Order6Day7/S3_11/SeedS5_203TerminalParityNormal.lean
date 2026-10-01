import SemigroupBasis.CoRoots.Order6Day7.S3_11.SeedS5_203TerminalParitySyntax
import SemigroupBasis.CoRoots.S5_441Invariant

/-!
# Unrestricted D008 support / terminal-state / parity completeness

The singleton, globally unique final, globally unique terminal pair, protected
terminal doubleton, and non-doubleton repeated-final strata are separated by
the COMPLETE S5_203 theorem.  Inside each stratum all derivations are made
from the exact frozen B26 syntax and preserve per-variable parity.

Terminal doubletons are never silently converted into terminal cubes.  Only
a final already present in the stem may enter the cube-switch branch.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace SemigroupBasis.CoRoots.Order6Day7.S3_11.SeedS5_203

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.S5_83

private abbrev targetBasis : List (Identity Nat) := Rank008.basis

private abbrev terminalWord :=
  SemigroupBasis.CoRoots.S5_203.terminalPairWord

private abbrev SameSupportTerminalStateSignature
    (left right : Word Nat) : Prop :=
  SemigroupBasis.CoRoots.S5_203.DirectCompletenessArchitecture.SameSupportTerminalStateSignature
    left right

/-- Exact target-law derivations preserve the COMPLETE S5_203 terminal state. -/
theorem derivationTerminalSignature
    {left right : Word Nat}
    (derivation : Derives targetBasis left right) :
    SameSupportTerminalStateSignature left right := by
  let identity : Identity Nat := ⟨left, right⟩
  have valid :
      identity.SatisfiedBy SemigroupBasis.CoRoots.S5_203.table.semigroup := by
    intro valuation
    exact derivation.sound Rank008.rightModels valuation
  exact SemigroupBasis.CoRoots.S5_203.valid_sameSupportTerminalStateSignature
    identity valid

/-- Exact target-law derivations also preserve unrestricted pointwise parity. -/
theorem derivationOccurrenceParity
    {left right : Word Nat}
    (derivation : Derives targetBasis left right) :
    ∀ letter,
      left.toList.count letter % 2 = right.toList.count letter % 2 := by
  let identity : Identity Nat := ⟨left, right⟩
  have valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S3_11.table.semigroup := by
    intro valuation
    exact derivation.sound Rank008.leftModels valuation
  exact
    SemigroupBasis.CoRoots.S5_441Invariant.sameOccurrenceParity_of_s3_11_valid
      identity valid

/-- Push the exact support and parity signature through both frozen-law paths. -/
theorem transformedSupportAndParity
    {sourceLeft sourceRight targetLeft targetRight : Word Nat}
    (same : SameSupportTerminalStateSignature sourceLeft sourceRight)
    (parity : ∀ letter,
      sourceLeft.toList.count letter % 2 =
        sourceRight.toList.count letter % 2)
    (leftDerivation : Derives targetBasis sourceLeft targetLeft)
    (rightDerivation : Derives targetBasis sourceRight targetRight) :
    (∀ letter, letter ∈ targetLeft.toList ↔ letter ∈ targetRight.toList) ∧
      (∀ letter,
        targetLeft.toList.count letter % 2 =
          targetRight.toList.count letter % 2) := by
  have leftSignature := derivationTerminalSignature leftDerivation
  have rightSignature := derivationTerminalSignature rightDerivation
  have leftParity := derivationOccurrenceParity leftDerivation
  have rightParity := derivationOccurrenceParity rightDerivation
  constructor
  · intro letter
    exact (leftSignature.support letter).symm.trans <|
      (same.support letter).trans (rightSignature.support letter)
  · intro letter
    exact (leftParity letter).symm.trans <|
      (parity letter).trans (rightParity letter)

/-- Genuine unrestricted B26 completeness for the exact complete S5_203
terminal signature plus pointwise parity, over an arbitrary Nat alphabet. -/
theorem derivesOfSameTerminalParitySignature
    (left right : Word Nat)
    (same : SameSupportTerminalStateSignature left right)
    (parity : ∀ letter,
      left.toList.count letter % 2 = right.toList.count letter % 2) :
    Derives targetBasis left right := by
  classical
  have leftReconstruct := terminalSplit_renderWord left
  have rightReconstruct := terminalSplit_renderWord right
  cases leftSplit : terminalSplit left with
  | singleton leftFinal =>
      cases rightSplit : terminalSplit right with
      | singleton rightFinal =>
          have rightUnique : UniqueFinal right leftFinal :=
            (same.uniqueFinal leftFinal).mp <| by
              simp [UniqueFinal, leftSplit]
          have finals : rightFinal = leftFinal := by
            simpa [UniqueFinal, rightSplit] using rightUnique
          subst rightFinal
          rw [leftSplit] at leftReconstruct
          rw [rightSplit] at rightReconstruct
          rw [← leftReconstruct, ← rightReconstruct]
          exact Derives.refl _
      | pair rightStem rightPenultimate rightFinal =>
          have leftSingleton : IsSingletonWord left := by
            simp [IsSingletonWord, leftSplit]
          have rightSingleton := same.singleton.mp leftSingleton
          simp [IsSingletonWord, rightSplit] at rightSingleton
  | pair leftStem leftPenultimate leftFinal =>
      cases rightSplit : terminalSplit right with
      | singleton rightFinal =>
          have rightSingleton : IsSingletonWord right := by
            simp [IsSingletonWord, rightSplit]
          have leftSingleton := same.singleton.mpr rightSingleton
          simp [IsSingletonWord, leftSplit] at leftSingleton
      | pair rightStem rightPenultimate rightFinal =>
          rw [leftSplit] at leftReconstruct
          rw [rightSplit] at rightReconstruct
          let leftWord := terminalWord leftStem leftPenultimate leftFinal
          let rightWord := terminalWord rightStem rightPenultimate rightFinal
          have leftWordEqual : leftWord = left := by
            simpa [leftWord, terminalWord,
              SemigroupBasis.CoRoots.S5_203.terminalPairWord,
              wordOfTerminalPair] using leftReconstruct
          have rightWordEqual : rightWord = right := by
            simpa [rightWord, terminalWord,
              SemigroupBasis.CoRoots.S5_203.terminalPairWord,
              wordOfTerminalPair] using rightReconstruct
          have renderedSignature :
              SameSupportTerminalStateSignature leftWord rightWord := by
            simpa [leftWordEqual, rightWordEqual] using same
          have renderedParity : ∀ letter,
              leftWord.toList.count letter % 2 =
                rightWord.toList.count letter % 2 := by
            intro letter
            simpa [leftWordEqual, rightWordEqual] using parity letter
          rw [← leftWordEqual, ← rightWordEqual]
          change Derives targetBasis leftWord rightWord
          by_cases leftDoubleton :
              SemigroupBasis.CoRoots.S5_203.DirectCompletenessArchitecture.TerminalDoubleton
                left leftFinal
          · have rightDoubleton :=
              (same.terminalDoubleton leftFinal).mp leftDoubleton
            have leftParts :
                leftPenultimate = leftFinal ∧ leftFinal ∉ leftStem := by
              simpa [SemigroupBasis.CoRoots.S5_203.DirectCompletenessArchitecture.TerminalDoubleton,
                leftSplit] using leftDoubleton
            have rightParts :
                rightPenultimate = leftFinal ∧
                  rightFinal = leftFinal ∧ leftFinal ∉ rightStem := by
              simpa [SemigroupBasis.CoRoots.S5_203.DirectCompletenessArchitecture.TerminalDoubleton,
                rightSplit] using rightDoubleton
            have leftPenultimateEqual := leftParts.1
            have rightPenultimateEqual := rightParts.1
            have rightFinalEqual := rightParts.2.1
            subst leftPenultimate
            subst rightPenultimate
            subst rightFinal
            have support : ∀ letter,
                letter ∈ leftStem ++ [leftFinal, leftFinal] ↔
                  letter ∈ rightStem ++ [leftFinal, leftFinal] := by
              intro letter
              simpa [leftWord, rightWord,
                SemigroupBasis.CoRoots.S5_203.toList_terminalPairWord] using
                  renderedSignature.support letter
            have counts : ∀ letter,
                (leftStem ++ [leftFinal, leftFinal]).count letter % 2 =
                  (rightStem ++ [leftFinal, leftFinal]).count letter % 2 := by
              intro letter
              simpa [leftWord, rightWord,
                SemigroupBasis.CoRoots.S5_203.toList_terminalPairWord] using
                  renderedParity letter
            have absent : leftFinal ∈ leftStem ↔ leftFinal ∈ rightStem :=
              iff_of_false leftParts.2 rightParts.2.2
            exact derivesAlignedTerminalPair
              leftStem rightStem leftFinal leftFinal
              support counts absent absent
          · by_cases leftFinalUnique : UniqueFinal left leftFinal
            · have rightUnique :=
                (same.uniqueFinal leftFinal).mp leftFinalUnique
              have leftFinalParts :
                  leftFinal ≠ leftPenultimate ∧ leftFinal ∉ leftStem := by
                simpa [UniqueFinal, leftSplit] using leftFinalUnique
              have rightFinalParts :
                  rightFinal = leftFinal ∧
                    rightFinal ≠ rightPenultimate ∧
                      rightFinal ∉ rightStem := by
                simpa [UniqueFinal, rightSplit] using rightUnique
              have rightFinalEqual := rightFinalParts.1
              subst rightFinal
              by_cases leftPenultimateRepeated :
                  leftPenultimate ∈ leftStem
              · have rightPenultimateRepeated :
                    rightPenultimate ∈ rightStem := by
                  apply Decidable.byContradiction
                  intro rightPenultimateUnique
                  have rightPair :
                      UniqueTerminalPair right
                        rightPenultimate leftFinal := by
                    simp [UniqueTerminalPair, rightSplit,
                      rightPenultimateUnique,
                      rightFinalParts.2.1, rightFinalParts.2.2]
                  have leftPair :=
                    (same.uniqueTerminalPairOfUniqueFinal
                      rightPenultimate leftFinal leftFinalUnique).mpr rightPair
                  have leftPairParts :
                      leftPenultimate = rightPenultimate ∧
                        leftFinal = leftFinal ∧
                        rightPenultimate ∉ leftStem ∧
                        leftFinal ≠ rightPenultimate ∧
                        leftFinal ∉ leftStem := by
                    simpa [UniqueTerminalPair, leftSplit] using leftPair
                  exact leftPairParts.2.2.1 <| by
                    simpa [leftPairParts.1] using leftPenultimateRepeated
                have leftMarkerMember : leftPenultimate ∈ leftWord.toList := by
                  simp [leftWord,
                    SemigroupBasis.CoRoots.S5_203.toList_terminalPairWord]
                have rightMarkerMember :=
                  (renderedSignature.support leftPenultimate).mp
                    leftMarkerMember
                have rightMarkerSupported :
                    leftPenultimate ∈ rightStem ∨
                      leftPenultimate = rightPenultimate := by
                  simp only [rightWord,
                    SemigroupBasis.CoRoots.S5_203.toList_terminalPairWord,
                    List.mem_append, List.mem_cons,
                    List.not_mem_nil, or_false] at rightMarkerMember
                  rcases rightMarkerMember with member | equal | equal
                  · exact Or.inl member
                  · exact Or.inr equal
                  · exact False.elim
                      ((Ne.symm leftFinalParts.1) equal)
                obtain ⟨switchedStem, rightSwitch,
                    switchedMarkerMember, switchedFinalAbsent⟩ :=
                  derivesSwitchRepeatedPenultimate
                    rightStem rightPenultimate leftPenultimate leftFinal
                    rightPenultimateRepeated rightMarkerSupported
                    (Ne.symm rightFinalParts.2.1)
                    (Ne.symm leftFinalParts.1)
                    rightFinalParts.2.2
                have transformed :=
                  transformedSupportAndParity renderedSignature renderedParity
                    (Derives.refl leftWord) rightSwitch
                have support : ∀ letter,
                    letter ∈ leftStem ++ [leftPenultimate, leftFinal] ↔
                      letter ∈ switchedStem ++
                        [leftPenultimate, leftFinal] := by
                  intro letter
                  simpa [leftWord,
                    SemigroupBasis.CoRoots.S5_203.toList_terminalPairWord] using
                      transformed.1 letter
                have counts : ∀ letter,
                    (leftStem ++ [leftPenultimate, leftFinal]).count letter % 2 =
                      (switchedStem ++
                        [leftPenultimate, leftFinal]).count letter % 2 := by
                  intro letter
                  simpa [leftWord,
                    SemigroupBasis.CoRoots.S5_203.toList_terminalPairWord] using
                      transformed.2 letter
                have penultimateMembership :
                    leftPenultimate ∈ leftStem ↔
                      leftPenultimate ∈ switchedStem :=
                  ⟨fun _ => switchedMarkerMember,
                    fun _ => leftPenultimateRepeated⟩
                have finalMembership :
                    leftFinal ∈ leftStem ↔ leftFinal ∈ switchedStem :=
                  iff_of_false leftFinalParts.2 switchedFinalAbsent
                exact
                  (derivesAlignedTerminalPair
                    leftStem switchedStem leftPenultimate leftFinal
                    support counts penultimateMembership finalMembership).trans
                      rightSwitch.symm
              · have leftPair :
                    UniqueTerminalPair left leftPenultimate leftFinal := by
                  simp [UniqueTerminalPair, leftSplit,
                    leftPenultimateRepeated,
                    leftFinalParts.1, leftFinalParts.2]
                have rightPair :=
                  (same.uniqueTerminalPairOfUniqueFinal
                    leftPenultimate leftFinal leftFinalUnique).mp leftPair
                have rightPairParts :
                    rightPenultimate = leftPenultimate ∧
                      leftFinal = leftFinal ∧
                      leftPenultimate ∉ rightStem ∧
                      leftFinal ≠ leftPenultimate ∧
                      leftFinal ∉ rightStem := by
                  simpa [UniqueTerminalPair, rightSplit] using rightPair
                have rightPenultimateEqual := rightPairParts.1
                subst rightPenultimate
                have support : ∀ letter,
                    letter ∈ leftStem ++ [leftPenultimate, leftFinal] ↔
                      letter ∈ rightStem ++
                        [leftPenultimate, leftFinal] := by
                  intro letter
                  simpa [leftWord, rightWord,
                    SemigroupBasis.CoRoots.S5_203.toList_terminalPairWord] using
                      renderedSignature.support letter
                have counts : ∀ letter,
                    (leftStem ++ [leftPenultimate, leftFinal]).count letter % 2 =
                      (rightStem ++
                        [leftPenultimate, leftFinal]).count letter % 2 := by
                  intro letter
                  simpa [leftWord, rightWord,
                    SemigroupBasis.CoRoots.S5_203.toList_terminalPairWord] using
                      renderedParity letter
                exact derivesAlignedTerminalPair
                  leftStem rightStem leftPenultimate leftFinal support counts
                  (iff_of_false leftPenultimateRepeated
                    rightPairParts.2.2.1)
                  (iff_of_false leftFinalParts.2
                    rightPairParts.2.2.2.2)
            · have leftFinalMember : leftFinal ∈ leftStem := by
                apply Decidable.byContradiction
                intro leftFinalAbsent
                by_cases equal : leftPenultimate = leftFinal
                · apply leftDoubleton
                  simp [SemigroupBasis.CoRoots.S5_203.DirectCompletenessArchitecture.TerminalDoubleton,
                    leftSplit,
                    equal, leftFinalAbsent]
                · apply leftFinalUnique
                  simp [UniqueFinal, leftSplit,
                    Ne.symm equal, leftFinalAbsent]
              have rightFinalMember : rightFinal ∈ rightStem := by
                apply Decidable.byContradiction
                intro rightFinalAbsent
                by_cases equal : rightPenultimate = rightFinal
                · have rightDoubleton :
                      SemigroupBasis.CoRoots.S5_203.DirectCompletenessArchitecture.TerminalDoubleton
                        right rightFinal := by
                    simp [SemigroupBasis.CoRoots.S5_203.DirectCompletenessArchitecture.TerminalDoubleton,
                      rightSplit,
                      equal, rightFinalAbsent]
                  have leftRightDoubleton :=
                    (same.terminalDoubleton rightFinal).mpr
                      rightDoubleton
                  have leftParts :
                      leftPenultimate = rightFinal ∧
                        leftFinal = rightFinal ∧
                        rightFinal ∉ leftStem := by
                    simpa [SemigroupBasis.CoRoots.S5_203.DirectCompletenessArchitecture.TerminalDoubleton,
                      leftSplit] using
                      leftRightDoubleton
                  have finalEqual : leftFinal = rightFinal := leftParts.2.1
                  exact leftDoubleton <|
                    finalEqual.symm ▸ leftRightDoubleton
                · have rightUnique : UniqueFinal right rightFinal := by
                    simp [UniqueFinal, rightSplit,
                      Ne.symm equal, rightFinalAbsent]
                  have leftRightUnique :=
                    (same.uniqueFinal rightFinal).mpr rightUnique
                  have leftParts :
                      leftFinal = rightFinal ∧
                        leftFinal ≠ leftPenultimate ∧
                        leftFinal ∉ leftStem := by
                    simpa [UniqueFinal, leftSplit] using leftRightUnique
                  have finalEqual := leftParts.1
                  exact leftFinalUnique <|
                    finalEqual.symm ▸ leftRightUnique
              obtain ⟨leftCubeStem, leftMake, leftCubeMarker⟩ :=
                derivesMakeNonDoubletonFinal
                  leftStem leftPenultimate leftFinal leftFinalMember
              obtain ⟨rightCubeStem, rightMake, rightCubeMarker⟩ :=
                derivesMakeNonDoubletonFinal
                  rightStem rightPenultimate rightFinal rightFinalMember
              have markerInLeft : leftFinal ∈ leftWord.toList := by
                simp [leftWord,
                  SemigroupBasis.CoRoots.S5_203.toList_terminalPairWord]
              have markerInRight :=
                (renderedSignature.support leftFinal).mp markerInLeft
              have rightCubeSignature :=
                derivationTerminalSignature rightMake
              have markerInRightCubeWord :=
                (rightCubeSignature.support leftFinal).mp markerInRight
              have markerInRightCube : leftFinal ∈ rightCubeStem := by
                have possibilities :
                    leftFinal ∈ rightCubeStem ∨ leftFinal = rightFinal := by
                  simpa [SemigroupBasis.CoRoots.S5_203.toList_terminalPairWord] using
                    markerInRightCubeWord
                rcases possibilities with member | equal
                · exact member
                · simpa [equal] using rightCubeMarker
              obtain ⟨rightSwitchedStem, rightSwitch, rightMarker⟩ :=
                derivesSwitchTerminalCube
                  rightCubeStem rightFinal leftFinal
                  rightCubeMarker markerInRightCube
              have rightTransform := rightMake.trans rightSwitch
              have transformed :=
                transformedSupportAndParity renderedSignature renderedParity
                  leftMake rightTransform
              have support : ∀ letter,
                  letter ∈ leftCubeStem ++ [leftFinal, leftFinal] ↔
                    letter ∈ rightSwitchedStem ++
                      [leftFinal, leftFinal] := by
                intro letter
                simpa [SemigroupBasis.CoRoots.S5_203.toList_terminalPairWord] using
                  transformed.1 letter
              have counts : ∀ letter,
                  (leftCubeStem ++ [leftFinal, leftFinal]).count letter % 2 =
                    (rightSwitchedStem ++
                      [leftFinal, leftFinal]).count letter % 2 := by
                intro letter
                simpa [SemigroupBasis.CoRoots.S5_203.toList_terminalPairWord] using
                  transformed.2 letter
              have markerMembership :
                  leftFinal ∈ leftCubeStem ↔
                    leftFinal ∈ rightSwitchedStem :=
                ⟨fun _ => rightMarker, fun _ => leftCubeMarker⟩
              exact leftMake.trans <|
                (derivesAlignedTerminalPair
                  leftCubeStem rightSwitchedStem leftFinal leftFinal
                  support counts markerMembership markerMembership).trans
                    rightTransform.symm

end SemigroupBasis.CoRoots.Order6Day7.S3_11.SeedS5_203
