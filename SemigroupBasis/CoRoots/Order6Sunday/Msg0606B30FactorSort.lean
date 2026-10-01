import SemigroupBasis.CoRoots.Order6Sunday.Msg0604B30TripledFactors

/-!
Parity-preserving B30 factor sorting. The Lee-style square-tail calculation
is reused from S5_402FactorSort with its three primitives proved directly
from B30. No S5_402 derivation or parity-breaking axiom is transported.
Triple-ended factors are square-ended factors with one marker absorbed into
their arbitrary block; the same calculation then gives unrestricted sorting.
-/

namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0606B30FactorSort

open SemigroupBasis
open Msg0521RepairedThirtyLawFinite
open Msg0604B30TripledFactors
open S5_402 (renderSquaredTerminatedBlocks terminatedBlocks terminatedFinalBlock
  sortedTerminatedBlocks sortedTerminatedTail sortedTerminatedTail_perm)

private def instantiateThree (u v z : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | _ => z

theorem derivesFactorLeft (u v z : Word Nat) :
    Derives basis ((((u ++ u) ++ v) ++ z) ++ v)
      ((((u ++ u) ++ z) ++ v) ++ v) := by
  have law := Derives.fromBasis (basis := basis) (e := basisLaw9) (by simp [basis])
  have step := law.subst (instantiateThree u v z)
  simpa [basisLaw9, instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using step

theorem derivesFactorRight (u v z : Word Nat) :
    Derives basis ((((u ++ u) ++ v) ++ z) ++ v)
      ((((u ++ z) ++ v) ++ v) ++ u) := by
  have law := Derives.fromBasis (basis := basis) (e := basisLaw13) (by simp [basis])
  have step := law.subst (instantiateThree u v z)
  simpa [basisLaw13, instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using step

theorem derivesLeePowerFourToTwo (u : Word Nat) :
    Derives basis (((u ++ u) ++ u) ++ u) (u ++ u) :=
  (derivesPairPower u).symm

theorem derivesLeeSquareTailMove (u v z : Word Nat) :
    Derives basis ((((u ++ u) ++ v) ++ z) ++ z)
      ((((u ++ v) ++ z) ++ z) ++ u) :=
  (derivesFactorLeft u z v).symm.trans (derivesFactorRight u z v)

theorem derivesLeeSimpleBlockSwap (u v z : Word Nat) :
    Derives basis ((((u ++ v) ++ u) ++ z) ++ u)
      ((((u ++ z) ++ u) ++ v) ++ u) := by
  have law := Derives.fromBasis (basis := basis) (e := basisLaw14) (by simp [basis])
  have step := law.subst (instantiateThree u v z)
  simpa [basisLaw14, instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using step

private abbrev listWordOfCons :=
  S5_107.listWordOfCons

/-! ## Lee-style transposition of square-ended factors -/

/-- List-level anchored block swap for arbitrary nonempty blocks. -/
private theorem listDerivesAnchoredBlockSwapLists
    (anchor : Nat) {left right : List Nat}
    (leftNonempty : left ≠ [])
    (rightNonempty : right ≠ []) :
    ListDerives
      ([anchor] ++ left ++ [anchor] ++ right ++ [anchor])
      ([anchor] ++ right ++ [anchor] ++ left ++ [anchor]) := by
  obtain ⟨leftHead, leftTail, rfl⟩ :=
    List.exists_cons_of_ne_nil leftNonempty
  obtain ⟨rightHead, rightTail, rfl⟩ :=
    List.exists_cons_of_ne_nil rightNonempty
  simpa [listWordOfCons, Word.toList, Word.singleton,
    Word.append, List.append_assoc] using
      (S5_107.ListDerives.ofWord <|
        derivesLeeSimpleBlockSwap
          (Word.singleton anchor)
          (listWordOfCons leftHead leftTail)
          (listWordOfCons rightHead rightTail))

/-- Lee's factor-swap calculation after the controller and both factor
markers have been expanded. Two square moves expose the anchored swap; the
reverse square moves restore the square-ended factor shape. -/
theorem listDerivesExpandedFactorSwap
    (controller leftMarker rightMarker : Nat)
    (leftBlock rightBlock : List Nat) :
    ListDerives
      ([controller, controller, controller, controller] ++
        leftBlock ++ [leftMarker, leftMarker] ++
        rightBlock ++ [rightMarker, rightMarker])
      ([controller, controller, controller, controller] ++
        rightBlock ++ [rightMarker, rightMarker] ++
        leftBlock ++ [leftMarker, leftMarker]) := by
  let firstMiddle : Word Nat :=
    listWordOfCons controller (controller :: leftBlock)
  have firstMoveCore :=
    S5_107.ListDerives.ofWord <|
      derivesLeeSquareTailMove
        (Word.singleton controller)
        firstMiddle
        (Word.singleton leftMarker)
  have firstMove :
      ListDerives
        ([controller, controller, controller, controller] ++
          leftBlock ++ [leftMarker, leftMarker] ++
          rightBlock ++ [rightMarker, rightMarker])
        ([controller, controller, controller] ++
          leftBlock ++ [leftMarker, leftMarker, controller] ++
          rightBlock ++ [rightMarker, rightMarker]) := by
    simpa [firstMiddle, listWordOfCons, Word.toList,
      Word.singleton, Word.append, List.append_assoc] using
        firstMoveCore.append
          (rightBlock ++ [rightMarker, rightMarker])

  let secondMiddle : Word Nat :=
    listWordOfCons controller
      (leftBlock ++
        [leftMarker, leftMarker, controller] ++ rightBlock)
  have secondMove :
      ListDerives
        ([controller, controller, controller] ++
          leftBlock ++ [leftMarker, leftMarker, controller] ++
          rightBlock ++ [rightMarker, rightMarker])
        ([controller, controller] ++
          leftBlock ++ [leftMarker, leftMarker, controller] ++
          rightBlock ++
            [rightMarker, rightMarker, controller]) := by
    simpa [secondMiddle, listWordOfCons, S5_107.listWordOfCons, Word.toList,
      Word.singleton, Word.append, List.append_assoc] using
        (S5_107.ListDerives.ofWord <|
          derivesLeeSquareTailMove
            (Word.singleton controller)
            secondMiddle
            (Word.singleton rightMarker))

  have swapCore :=
    listDerivesAnchoredBlockSwapLists
      controller
      (left := leftBlock ++ [leftMarker, leftMarker])
      (right := rightBlock ++ [rightMarker, rightMarker])
      (by simp) (by simp)
  have swapped :
      ListDerives
        ([controller, controller] ++
          leftBlock ++ [leftMarker, leftMarker, controller] ++
          rightBlock ++
            [rightMarker, rightMarker, controller])
        ([controller, controller] ++
          rightBlock ++ [rightMarker, rightMarker, controller] ++
          leftBlock ++
            [leftMarker, leftMarker, controller]) := by
    simpa [Word.toList, Word.singleton, Word.append,
      List.append_assoc] using
      swapCore.prepend [controller]

  let thirdMiddle : Word Nat :=
    listWordOfCons controller
      (rightBlock ++
        [rightMarker, rightMarker, controller] ++ leftBlock)
  have thirdMoveForward :=
    S5_107.ListDerives.ofWord <|
      derivesLeeSquareTailMove
        (Word.singleton controller)
        thirdMiddle
        (Word.singleton leftMarker)
  have thirdMove :
      ListDerives
        ([controller, controller] ++
          rightBlock ++ [rightMarker, rightMarker, controller] ++
          leftBlock ++
            [leftMarker, leftMarker, controller])
        ([controller, controller, controller] ++
          rightBlock ++ [rightMarker, rightMarker, controller] ++
          leftBlock ++ [leftMarker, leftMarker]) := by
    simpa [thirdMiddle, listWordOfCons, S5_107.listWordOfCons, Word.toList,
      Word.singleton, Word.append, List.append_assoc] using
        thirdMoveForward.symm

  let fourthMiddle : Word Nat :=
    listWordOfCons controller (controller :: rightBlock)
  have fourthMoveCore :=
    S5_107.ListDerives.ofWord <|
      derivesLeeSquareTailMove
        (Word.singleton controller)
        fourthMiddle
        (Word.singleton rightMarker)
  have fourthMove :
      ListDerives
        ([controller, controller, controller] ++
          rightBlock ++ [rightMarker, rightMarker, controller] ++
          leftBlock ++ [leftMarker, leftMarker])
        ([controller, controller, controller, controller] ++
          rightBlock ++ [rightMarker, rightMarker] ++
          leftBlock ++ [leftMarker, leftMarker]) := by
    simpa [fourthMiddle, listWordOfCons, Word.toList,
      Word.singleton, Word.append, List.append_assoc] using
        fourthMoveCore.symm.append
          (leftBlock ++ [leftMarker, leftMarker])

  exact
    firstMove.trans <|
      secondMove.trans <|
        swapped.trans <|
          thirdMove.trans fourthMove

/-- Swap two adjacent square-ended factors using the square at the end of
the preceding factor as controller. The arbitrary prefix, controller block,
and suffix remain fixed. -/
theorem listDerivesSquaredFactorSwapAfterController
    (before controllerBlock leftBlock rightBlock after : List Nat)
    (controller leftMarker rightMarker : Nat) :
    ListDerives
      (before ++ controllerBlock ++ [controller, controller] ++
        leftBlock ++ [leftMarker, leftMarker] ++
        rightBlock ++ [rightMarker, rightMarker] ++ after)
      (before ++ controllerBlock ++ [controller, controller] ++
        rightBlock ++ [rightMarker, rightMarker] ++
        leftBlock ++ [leftMarker, leftMarker] ++ after) := by
  have expandController :=
    (S5_107.ListDerives.ofWord <|
      (derivesLeePowerFourToTwo
        (Word.singleton controller)).symm).context
        (before ++ controllerBlock)
        (leftBlock ++ [leftMarker, leftMarker] ++
          rightBlock ++ [rightMarker, rightMarker] ++ after)
  have expandStep :
      ListDerives
        (before ++ controllerBlock ++ [controller, controller] ++
          leftBlock ++ [leftMarker, leftMarker] ++
          rightBlock ++ [rightMarker, rightMarker] ++ after)
        (before ++ controllerBlock ++
          [controller, controller, controller, controller] ++
          leftBlock ++ [leftMarker, leftMarker] ++
          rightBlock ++ [rightMarker, rightMarker] ++ after) := by
    simpa [Word.toList, Word.singleton, Word.append,
      List.append_assoc] using expandController
  have swapStep :=
    (listDerivesExpandedFactorSwap
      controller leftMarker rightMarker
      leftBlock rightBlock).context
        (before ++ controllerBlock) after
  have swapStep' :
      ListDerives
        (before ++ controllerBlock ++
          [controller, controller, controller, controller] ++
          leftBlock ++ [leftMarker, leftMarker] ++
          rightBlock ++ [rightMarker, rightMarker] ++ after)
        (before ++ controllerBlock ++
          [controller, controller, controller, controller] ++
          rightBlock ++ [rightMarker, rightMarker] ++
          leftBlock ++ [leftMarker, leftMarker] ++ after) := by
    simpa [List.append_assoc] using swapStep
  have contractController :=
    (S5_107.ListDerives.ofWord <|
      derivesLeePowerFourToTwo
        (Word.singleton controller)).context
        (before ++ controllerBlock)
        (rightBlock ++ [rightMarker, rightMarker] ++
          leftBlock ++ [leftMarker, leftMarker] ++ after)
  have contractStep :
      ListDerives
        (before ++ controllerBlock ++
          [controller, controller, controller, controller] ++
          rightBlock ++ [rightMarker, rightMarker] ++
          leftBlock ++ [leftMarker, leftMarker] ++ after)
        (before ++ controllerBlock ++ [controller, controller] ++
          rightBlock ++ [rightMarker, rightMarker] ++
          leftBlock ++ [leftMarker, leftMarker] ++ after) := by
    simpa [Word.toList, Word.singleton, Word.append,
      List.append_assoc] using contractController
  exact expandStep.trans (swapStep'.trans contractStep)

/-- Every permutation of the square-ended factors after one fixed first
factor is derivable. This is the unrestricted Lee-style sorting boundary. -/
theorem listDerivesSquaredTailPermutation
    {source target : List (List Nat × Nat)}
    (permutation : source.Perm target) :
    ∀ (first : List Nat × Nat) (final : List Nat),
      ListDerives
        (renderSquaredTerminatedBlocks
            (first :: source) ++ final)
        (renderSquaredTerminatedBlocks
            (first :: target) ++ final) := by
  induction permutation with
  | nil =>
      intro first final
      exact S5_107.ListDerives.refl _
  | @cons factor source target permutation ih =>
      intro first final
      rcases first with ⟨firstBlock, firstMarker⟩
      have tailStep := ih factor final
      simpa [renderSquaredTerminatedBlocks,
        List.append_assoc] using
          tailStep.prepend
            (firstBlock ++ [firstMarker, firstMarker])
  | swap left right rest =>
      intro first final
      rcases first with ⟨controllerBlock, controller⟩
      rcases left with ⟨leftBlock, leftMarker⟩
      rcases right with ⟨rightBlock, rightMarker⟩
      have swapped :=
        listDerivesSquaredFactorSwapAfterController
          [] controllerBlock leftBlock rightBlock
          (renderSquaredTerminatedBlocks rest ++ final)
          controller leftMarker rightMarker
      simpa [renderSquaredTerminatedBlocks,
        List.append_assoc] using swapped.symm
  | @trans source middle target first second ihFirst ihSecond =>
      intro leading final
      exact
        (ihFirst leading final).trans
          (ihSecond leading final)

/-- Absorb each extra marker into its block and use square-ended swapping. -/
theorem listDerivesTripledFactorSwapAfterController
    (before controllerBlock leftBlock rightBlock after : List Nat)
    (controller leftMarker rightMarker : Nat) :
    ListDerives
      (before ++ controllerBlock ++ [controller, controller, controller] ++
        leftBlock ++ [leftMarker, leftMarker, leftMarker] ++
        rightBlock ++ [rightMarker, rightMarker, rightMarker] ++ after)
      (before ++ controllerBlock ++ [controller, controller, controller] ++
        rightBlock ++ [rightMarker, rightMarker, rightMarker] ++
        leftBlock ++ [leftMarker, leftMarker, leftMarker] ++ after) := by
  have swapped := listDerivesSquaredFactorSwapAfterController before
    (controllerBlock ++ [controller]) (leftBlock ++ [leftMarker])
    (rightBlock ++ [rightMarker]) after controller leftMarker rightMarker
  simpa [List.append_assoc] using swapped

/-- Every permutation of the triple-ended factors after one fixed first
factor is derivable. This is the unrestricted Lee-style sorting boundary. -/
theorem listDerivesTripledTailPermutation
    {source target : List (List Nat × Nat)}
    (permutation : source.Perm target) :
    ∀ (first : List Nat × Nat) (final : List Nat),
      ListDerives
        (renderTripledTerminatedBlocks
            (first :: source) ++ final)
        (renderTripledTerminatedBlocks
            (first :: target) ++ final) := by
  induction permutation with
  | nil =>
      intro first final
      exact S5_107.ListDerives.refl _
  | @cons factor source target permutation ih =>
      intro first final
      rcases first with ⟨firstBlock, firstMarker⟩
      have tailStep := ih factor final
      simpa [renderTripledTerminatedBlocks,
        List.append_assoc] using
          tailStep.prepend
            (firstBlock ++ [firstMarker, firstMarker, firstMarker])
  | swap left right rest =>
      intro first final
      rcases first with ⟨controllerBlock, controller⟩
      rcases left with ⟨leftBlock, leftMarker⟩
      rcases right with ⟨rightBlock, rightMarker⟩
      have swapped :=
        listDerivesTripledFactorSwapAfterController
          [] controllerBlock leftBlock rightBlock
          (renderTripledTerminatedBlocks rest ++ final)
          controller leftMarker rightMarker
      simpa [renderTripledTerminatedBlocks,
        List.append_assoc] using swapped.symm
  | @trans source middle target first second ihFirst ihSecond =>
      intro leading final
      exact
        (ihFirst leading final).trans
          (ihSecond leading final)

/-- Deterministically sort the noninitial triple-ended scanner factors. -/
theorem listDerivesSortTripledTerminatedTail (letters : List Nat) :
    ListDerives
      (renderTripledTerminatedBlocks (terminatedBlocks letters) ++ terminatedFinalBlock letters)
      (renderTripledTerminatedBlocks (sortedTerminatedBlocks letters) ++ terminatedFinalBlock letters) := by
  cases shape : terminatedBlocks letters with
  | nil =>
      simpa [sortedTerminatedBlocks, shape] using
        (S5_107.ListDerives.refl (basis := basis) (terminatedFinalBlock letters))
  | cons first rest =>
      have sorted := listDerivesTripledTailPermutation
        (sortedTerminatedTail_perm rest).symm first (terminatedFinalBlock letters)
      simpa [sortedTerminatedBlocks, shape] using sorted

/-- Unrestricted B30 derivation to deterministically sorted tripled factors.
The marker-only bank is still uncontracted; this is not completeness. -/
theorem listDerivesTripleAndSortTerminatedFactors (letters : List Nat) :
    ListDerives letters
      (renderTripledTerminatedBlocks (sortedTerminatedBlocks letters) ++ terminatedFinalBlock letters) :=
  (listDerivesTripleAllTerminatedMarkers letters).trans
    (listDerivesSortTripledTerminatedTail letters)

end SemigroupBasis.CoRoots.Order6Sunday.Msg0606B30FactorSort
