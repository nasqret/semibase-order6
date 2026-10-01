import SemigroupBasis.CoRoots.Order6Sunday.Msg0606B30FactorSort

/-! Collect every repeated-marker occurrence into a cubic bank, retaining
exactly the first and block-bearing successor factors as squares. This
avoids any parity-breaking deletion: a retained cube is split as x^2 x^3
using x^3 = x^5, then the new cubic factor is permuted to the bank. -/

namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0606B30BankCollection

open SemigroupBasis
open Msg0521RepairedThirtyLawFinite (basis)
open Msg0604B30TripledFactors
open Msg0606B30FactorSort
open S5_402 (renderSquaredTerminatedBlocks renderSquaredTerminatedBlocks_append
  blockBearingFactors terminatedFactorMarkers sortedTerminatedBlocks
  retainedSortedFactors terminatedFinalBlock)

def cubeFactor (marker : Nat) : List Nat × Nat := ([marker], marker)

def cubeFactors (labels : List Nat) : List (List Nat × Nat) := labels.map cubeFactor

def renderCubeBank (labels : List Nat) : List Nat :=
  renderSquaredTerminatedBlocks (cubeFactors labels)

@[simp] theorem renderCubeBank_nil : renderCubeBank [] = [] := rfl

@[simp] theorem renderCubeBank_cons (x : Nat) (xs : List Nat) :
    renderCubeBank (x :: xs) = [x,x,x] ++ renderCubeBank xs := rfl

/-- Noninitial marker-only factors already belong to the bank. -/
def spreadTail : List (List Nat × Nat) → List (List Nat × Nat)
  | [] => []
  | (block, marker) :: rest =>
      if block = [] then cubeFactor marker :: spreadTail rest
      else (block, marker) :: cubeFactor marker :: spreadTail rest

private theorem perm_cons_append {α : Type} (item : α) :
    ∀ front back : List α, (item :: front ++ back).Perm (front ++ item :: back)
  | [], back => List.Perm.refl _
  | head :: tail, back => by
      have swap : (item :: head :: tail ++ back).Perm (head :: item :: tail ++ back) :=
        (List.Perm.swap item head (tail ++ back)).symm
      exact swap.trans (List.Perm.cons head (perm_cons_append item tail back))

theorem spreadTail_perm (factors : List (List Nat × Nat)) :
    (spreadTail factors).Perm
      (blockBearingFactors factors ++ cubeFactors (terminatedFactorMarkers factors)) := by
  induction factors with
  | nil => exact List.Perm.refl _
  | cons factor rest ih =>
      rcases factor with ⟨block, marker⟩
      have middle := (List.Perm.cons (cubeFactor marker) ih).trans
        (perm_cons_append (cubeFactor marker) (blockBearingFactors rest)
          (cubeFactors (terminatedFactorMarkers rest)))
      by_cases empty : block = []
      · simpa [spreadTail, blockBearingFactors, cubeFactors, terminatedFactorMarkers,
          empty] using middle
      · simpa [spreadTail, blockBearingFactors, cubeFactors, terminatedFactorMarkers,
          empty] using List.Perm.cons (block, marker) middle

theorem listDerivesCubeSplit (marker : Nat) :
    ListDerives [marker,marker,marker] [marker,marker,marker,marker,marker] := by
  have split := (derivesPairPower (Word.singleton marker)).appendRight (Word.singleton marker)
  simpa [Word.singleton, Word.append] using S5_107.ListDerives.ofWord split

theorem listDerivesSpreadTail (factors : List (List Nat × Nat)) :
    ListDerives (renderTripledTerminatedBlocks factors)
      (renderSquaredTerminatedBlocks (spreadTail factors)) := by
  induction factors with
  | nil => exact S5_107.ListDerives.empty
  | cons factor rest ih =>
      rcases factor with ⟨block, marker⟩
      by_cases empty : block = []
      · simpa [spreadTail, empty, cubeFactor, renderSquaredTerminatedBlocks,
          renderTripledTerminatedBlocks, List.append_assoc] using
          ih.prepend [marker,marker,marker]
      · have split := (listDerivesCubeSplit marker).context block
          (renderTripledTerminatedBlocks rest)
        have tail := ih.prepend (block ++ [marker,marker,marker,marker,marker])
        have result := split.trans tail
        simpa [spreadTail, empty, cubeFactor, renderSquaredTerminatedBlocks,
          renderTripledTerminatedBlocks, List.append_assoc] using result

/-- The first factor is retained even when its block is empty. -/
theorem listDerivesCollectCubicBank (first : List Nat × Nat)
    (rest : List (List Nat × Nat)) (final : List Nat) :
    ListDerives (renderTripledTerminatedBlocks (first :: rest) ++ final)
      (renderSquaredTerminatedBlocks (first :: blockBearingFactors rest) ++
        renderCubeBank (terminatedFactorMarkers (first :: rest)) ++ final) := by
  rcases first with ⟨block, marker⟩
  have split := (listDerivesCubeSplit marker).context block
    (renderTripledTerminatedBlocks rest ++ final)
  have tail := ((listDerivesSpreadTail rest).prepend
    (block ++ [marker,marker,marker,marker,marker])).append final
  simp only [List.append_assoc] at split tail
  have expanded :
      ListDerives (renderTripledTerminatedBlocks ((block,marker) :: rest) ++ final)
        (renderSquaredTerminatedBlocks
          ((block,marker) :: cubeFactor marker :: spreadTail rest) ++ final) := by
    simpa [renderTripledTerminatedBlocks, renderSquaredTerminatedBlocks,
      cubeFactor, List.append_assoc] using split.trans tail
  have permutation := (List.Perm.cons (cubeFactor marker) (spreadTail_perm rest)).trans
    (perm_cons_append (cubeFactor marker) (blockBearingFactors rest)
      (cubeFactors (terminatedFactorMarkers rest)))
  have rearranged := listDerivesSquaredTailPermutation permutation (block,marker) final
  have rearranged' :
      ListDerives (renderSquaredTerminatedBlocks
        ((block,marker) :: cubeFactor marker :: spreadTail rest) ++ final)
      (renderSquaredTerminatedBlocks ((block,marker) :: blockBearingFactors rest) ++
        renderCubeBank (terminatedFactorMarkers ((block,marker) :: rest)) ++ final) := by
    simpa [renderCubeBank, cubeFactors, terminatedFactorMarkers,
      renderSquaredTerminatedBlocks, renderSquaredTerminatedBlocks_append,
      List.append_assoc] using rearranged
  exact expanded.trans rearranged'

def sortedFactorLabels (letters : List Nat) : List Nat :=
  terminatedFactorMarkers (sortedTerminatedBlocks letters)

/-- Every arbitrary word list reaches its exact retained squared prefix,
one cubic bank entry per original repeated-marker occurrence, and the
unchanged final simple block. The cubic bank is not yet normalized. -/
theorem listDerivesSquaredPrefixCubicBank (letters : List Nat) :
    ListDerives letters
      (renderSquaredTerminatedBlocks (retainedSortedFactors letters) ++
        renderCubeBank (sortedFactorLabels letters) ++ terminatedFinalBlock letters) := by
  have sorted := listDerivesTripleAndSortTerminatedFactors letters
  cases shape : sortedTerminatedBlocks letters with
  | nil =>
      simpa [retainedSortedFactors, sortedFactorLabels, shape,
        terminatedFactorMarkers, renderCubeBank, cubeFactors,
        renderSquaredTerminatedBlocks, renderTripledTerminatedBlocks] using sorted
  | cons first rest =>
      have collected := listDerivesCollectCubicBank first rest (terminatedFinalBlock letters)
      rw [shape] at sorted
      simpa [retainedSortedFactors, sortedFactorLabels, shape] using sorted.trans collected

end SemigroupBasis.CoRoots.Order6Sunday.Msg0606B30BankCollection
