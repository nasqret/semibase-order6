import SemigroupBasis.CoRoots.Order6SporadicSection15BetaScaffoldData
import SemigroupBasis.CoRoots.Order6SporadicSection15BetaUnitMoves

namespace SemigroupBasis.CoRoots.Order6SporadicSection15

namespace BetaScaffoldMoves

def scaffoldPrefix (letters : List Nat) : List Nat :=
  S5_107.initialSimpleBlock letters ++
    CanonicalData.renderSquares (BetaScaffoldData.doubledLabels letters)

/-- The canonical renderer places an anchor before each unit. Appending one
terminal anchor is exactly the repeated-anchor renderer used by (15.1f). -/
theorem renderBetaUnits_append_anchor
    (anchor : List Nat) : ∀ units : List (List Nat),
      CanonicalData.renderBetaUnits anchor units ++ anchor =
        anchor ++ renderBetaUnitBlocks anchor units
  | [] => by simp [CanonicalData.renderBetaUnits, renderBetaUnitBlocks]
  | unit :: units => by
      simp [CanonicalData.renderBetaUnits, renderBetaUnitBlocks,
        renderBetaUnits_append_anchor anchor units, List.append_assoc]

/-- A final simple unit consumes the terminal anchor emitted after the
interior units and remains as the final list suffix. -/
theorem renderBetaUnits_append_final_unit
    (anchor final : List Nat) (units : List (List Nat)) :
    CanonicalData.renderBetaUnits anchor (units ++ [final]) =
      anchor ++ (renderBetaUnitBlocks anchor units ++ final) := by
  rw [CanonicalData.renderBetaUnits_append]
  simp only [CanonicalData.renderBetaUnits, List.append_nil]
  calc
    CanonicalData.renderBetaUnits anchor units ++ (anchor ++ final) =
        (CanonicalData.renderBetaUnits anchor units ++ anchor) ++ final := by
      rw [List.append_assoc]
    _ = (anchor ++ renderBetaUnitBlocks anchor units) ++ final := by
      rw [renderBetaUnits_append_anchor]
    _ = anchor ++ (renderBetaUnitBlocks anchor units ++ final) := by
      rw [List.append_assoc]

theorem scaffoldList_eq_anchor_context_of_final_nil
    (letters : List Nat)
    (finalShape : S5_107.finalSimpleBlock letters = []) :
    BetaScaffoldData.scaffoldList letters =
      scaffoldPrefix letters ++ BetaScaffoldData.highBlock letters ++
        renderBetaUnitBlocks (BetaScaffoldData.highBlock letters)
          (BetaScaffoldData.interiorUnits letters) := by
  simp [BetaScaffoldData.scaffoldList, BetaScaffoldData.scaffoldData,
    BetaScaffoldData.rawUnits, BetaScaffoldData.terminalHigh,
    BetaScaffoldData.interiorUnits, BetaScaffoldData.highBlock,
    BetaScaffoldData.highLabels, BetaScaffoldData.doubledLabels,
    scaffoldPrefix, CanonicalData.renderBetaData, finalShape,
    renderBetaUnits_append_anchor, List.append_assoc]

theorem sortedScaffoldList_eq_anchor_context_of_final_nil
    (letters : List Nat)
    (finalShape : S5_107.finalSimpleBlock letters = []) :
    BetaScaffoldData.sortedScaffoldList letters =
      scaffoldPrefix letters ++ BetaScaffoldData.highBlock letters ++
        renderBetaUnitBlocks (BetaScaffoldData.highBlock letters)
          (BetaScaffoldData.sortedInteriorUnits letters) := by
  rw [BetaScaffoldData.sortedScaffoldList_eq_betaCanonicalList]
  simp [CanonicalData.betaCanonicalList, CanonicalData.betaRenderData,
    CanonicalData.renderBetaData, BetaScaffoldData.sortedInteriorUnits,
    BetaScaffoldData.interiorUnits, BetaScaffoldData.highBlock,
    BetaScaffoldData.highLabels, BetaScaffoldData.doubledLabels,
    scaffoldPrefix, finalShape, renderBetaUnits_append_anchor,
    List.append_assoc]

theorem scaffoldList_eq_anchor_context_of_final_cons
    (letters : List Nat) (first : Nat) (rest : List Nat)
    (finalShape :
      S5_107.finalSimpleBlock letters = first :: rest) :
    BetaScaffoldData.scaffoldList letters =
      scaffoldPrefix letters ++ BetaScaffoldData.highBlock letters ++
        renderBetaUnitBlocks (BetaScaffoldData.highBlock letters)
          (BetaScaffoldData.interiorUnits letters) ++
            (first :: rest) := by
  rw [BetaScaffoldData.scaffoldList]
  simp [BetaScaffoldData.scaffoldData, BetaScaffoldData.rawUnits,
    BetaScaffoldData.terminalHigh, BetaScaffoldData.interiorUnits,
    BetaScaffoldData.highBlock, BetaScaffoldData.highLabels,
    BetaScaffoldData.doubledLabels, scaffoldPrefix,
    CanonicalData.renderBetaData, finalShape,
    renderBetaUnits_append_final_unit, List.append_assoc]

theorem sortedScaffoldList_eq_anchor_context_of_final_cons
    (letters : List Nat) (first : Nat) (rest : List Nat)
    (finalShape :
      S5_107.finalSimpleBlock letters = first :: rest) :
    BetaScaffoldData.sortedScaffoldList letters =
      scaffoldPrefix letters ++ BetaScaffoldData.highBlock letters ++
        renderBetaUnitBlocks (BetaScaffoldData.highBlock letters)
          (BetaScaffoldData.sortedInteriorUnits letters) ++
            (first :: rest) := by
  rw [BetaScaffoldData.sortedScaffoldList_eq_betaCanonicalList]
  simp [CanonicalData.betaCanonicalList, CanonicalData.betaRenderData,
    CanonicalData.renderBetaData, BetaScaffoldData.sortedInteriorUnits,
    BetaScaffoldData.interiorUnits, BetaScaffoldData.highBlock,
    BetaScaffoldData.highLabels, BetaScaffoldData.doubledLabels,
    scaffoldPrefix, finalShape, renderBetaUnits_append_final_unit,
    List.append_assoc]

/-- Once an arbitrary beta word reaches the raw scaffold, the repeated-anchor
(15.1f) move sorts all interior simple units and reaches the exact executable
beta canonical list. -/
theorem listDerivesScaffoldToCanonical
    (letters : List Nat)
    (branch : CanonicalData.canonicalBranch letters = .beta) :
    ListDerives
      (BetaScaffoldData.scaffoldList letters)
      (CanonicalData.betaCanonicalList letters) := by
  have anchorNonempty :=
    BetaScaffoldData.highBlock_ne_nil_of_branch_beta branch
  have permutation :=
    BetaScaffoldData.interiorUnits_perm_sortedInteriorUnits letters
  have unitsNonempty :
      ∀ unit ∈ BetaScaffoldData.interiorUnits letters, unit ≠ [] :=
    BetaScaffoldData.interiorUnits_nonempty letters
  cases finalShape : S5_107.finalSimpleBlock letters with
  | nil =>
      have step := listDerivesBetaUnitBlockPermutationInContext
        (scaffoldPrefix letters) [] (BetaScaffoldData.highBlock letters)
        anchorNonempty permutation unitsNonempty
      rw [← BetaScaffoldData.sortedScaffoldList_eq_betaCanonicalList]
      simpa [scaffoldList_eq_anchor_context_of_final_nil letters finalShape,
        sortedScaffoldList_eq_anchor_context_of_final_nil letters finalShape,
        List.append_assoc] using step
  | cons first rest =>
      have step := listDerivesBetaUnitBlockPermutationInContext
        (scaffoldPrefix letters) (first :: rest)
        (BetaScaffoldData.highBlock letters)
        anchorNonempty permutation unitsNonempty
      rw [← BetaScaffoldData.sortedScaffoldList_eq_betaCanonicalList]
      simpa [scaffoldList_eq_anchor_context_of_final_cons
          letters first rest finalShape,
        sortedScaffoldList_eq_anchor_context_of_final_cons
          letters first rest finalShape,
        List.append_assoc] using step

end BetaScaffoldMoves

end SemigroupBasis.CoRoots.Order6SporadicSection15
