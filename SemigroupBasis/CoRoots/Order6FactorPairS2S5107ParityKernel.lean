import SemigroupBasis.CoRoots.Order6FactorPairS2S5107Prelude

namespace SemigroupBasis.CoRoots.Order6FactorPairS2S5107ParityKernel

open SemigroupBasis

private abbrev candidateBasis : List (Identity Nat) :=
  SemigroupBasis.CoRoots.Order6FactorPairS2S5107Prelude.basis

private abbrev s5Basis : List (Identity Nat) :=
  SemigroupBasis.CoRoots.S5_107.basis

private abbrev initialBasis : List (Identity Nat) :=
  SemigroupBasis.CoRoots.Order6S5_107InitialIntersection.basis

/-!
The sealed `S5_107` normalizer is directly reusable after its first three
laws. Those three laws change one occurrence parity, so transporting the full
normalizer requires a parity-kernel argument rather than a law-by-law
`Derives.transport`.
-/

/-- The prelude already transports the complete parity-preserving tail of the
sealed initial-intersection normalizer. -/
theorem transportInitialBalanced
    {left right : Word Nat}
    (derivation : Derives (initialBasis.drop 3) left right) :
    Derives candidateBasis left right :=
  SemigroupBasis.CoRoots.Order6FactorPairS2S5107Prelude.transportInitialBalanced
    derivation

/-- The parity-preserving tail of the sealed `S5_107` basis, stated using the
candidate's definitionally equal laws. -/
def s5BalancedTail : List (Identity Nat) :=
  [SemigroupBasis.CoRoots.Order6FactorPairS2S5107Prelude.squareInterleaveLaw,
    SemigroupBasis.CoRoots.Order6FactorPairS2S5107Prelude.squareFinalLaw,
    SemigroupBasis.CoRoots.Order6FactorPairS2S5107Prelude.squareInitialLaw,
    SemigroupBasis.CoRoots.Order6FactorPairS2S5107Prelude.attachmentXXZYYLaw,
    SemigroupBasis.CoRoots.Order6FactorPairS2S5107Prelude.attachmentXYXZYLaw,
    SemigroupBasis.CoRoots.Order6FactorPairS2S5107Prelude.attachmentXYYZXLaw,
    SemigroupBasis.CoRoots.Order6FactorPairS2S5107Prelude.attachmentXYZXYLaw,
    SemigroupBasis.CoRoots.Order6FactorPairS2S5107Prelude.attachmentXYZYXLaw,
    SemigroupBasis.CoRoots.Order6FactorPairS2S5107Prelude.attachmentXZXYYLaw,
    SemigroupBasis.CoRoots.Order6FactorPairS2S5107Prelude.attachmentXZYXYLaw,
    SemigroupBasis.CoRoots.Order6FactorPairS2S5107Prelude.attachmentXZYYXLaw,
    SemigroupBasis.CoRoots.Order6FactorPairS2S5107Prelude.attachmentYXXZYLaw,
    SemigroupBasis.CoRoots.Order6FactorPairS2S5107Prelude.blockSwapLaw]

theorem s5BalancedTail_matches :
    s5BalancedTail = s5Basis.drop 3 := by
  decide

theorem s5BalancedTailLawDerives
    (identity : Identity Nat) (member : identity ∈ s5BalancedTail) :
    Derives candidateBasis identity.lhs identity.rhs := by
  simp only [s5BalancedTail, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    exact Derives.fromBasis (by
      simp [candidateBasis,
        SemigroupBasis.CoRoots.Order6FactorPairS2S5107Prelude.basis])

/-- Every use of the balanced tail of the sealed normalizer transports to the
nineteen-law candidate. -/
theorem transportS5BalancedTail
    {left right : Word Nat}
    (derivation : Derives (s5Basis.drop 3) left right) :
    Derives candidateBasis left right := by
  rw [← s5BalancedTail_matches] at derivation
  exact Derives.transport s5BalancedTailLawDerives derivation

/-- The sealed power law changes the parity of `x`. -/
theorem s5PowerLaw_changesParity :
    SemigroupBasis.CoRoots.S5_107.powerLaw.lhs.toList.count 0 % 2 ≠
      SemigroupBasis.CoRoots.S5_107.powerLaw.rhs.toList.count 0 % 2 := by
  decide

/-- The sealed left-endpoint law changes the parity of `x`. -/
theorem s5LeftEndpointLaw_changesParity :
    SemigroupBasis.CoRoots.S5_107.leftEndpointLaw.lhs.toList.count 0 % 2 ≠
      SemigroupBasis.CoRoots.S5_107.leftEndpointLaw.rhs.toList.count 0 % 2 := by
  decide

/-- The sealed right-endpoint law changes the parity of `x`. -/
theorem s5RightEndpointLaw_changesParity :
    SemigroupBasis.CoRoots.S5_107.rightEndpointLaw.lhs.toList.count 0 % 2 ≠
      SemigroupBasis.CoRoots.S5_107.rightEndpointLaw.rhs.toList.count 0 % 2 := by
  decide

def SameOccurrenceParity (left right : Word Nat) : Prop :=
  ∀ letter,
    left.toList.count letter % 2 =
      right.toList.count letter % 2

private abbrev ListDerives (left right : List Nat) : Prop :=
  SemigroupBasis.CoRoots.S5_107.ListDerives
    candidateBasis left right

private def instantiateThreeWords
    (u v z : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => z
  | n + 3 => Word.singleton (n + 3)

/-- Lee's square move uses only two attachment laws, hence it is already
available in the parity-preserving candidate calculus. -/
private theorem derivesSquareMove
    (u v z : Word Nat) :
    Derives candidateBasis
      ((((u ++ u) ++ v) ++ z) ++ z)
      (((u ++ v) ++ (z ++ z)) ++ u) := by
  have firstRaw :=
    SemigroupBasis.CoRoots.Order6FactorPairS2S5107Prelude.derivesBasisSubstitution
      SemigroupBasis.CoRoots.Order6FactorPairS2S5107Prelude.attachmentXXZYYLaw
      (by
        simp [SemigroupBasis.CoRoots.Order6FactorPairS2S5107Prelude.basis])
      (instantiateThreeWords u z v)
  change
    Derives candidateBasis
      ((((u ++ u) ++ z) ++ v) ++ z)
      ((((u ++ u) ++ v) ++ z) ++ z) at firstRaw
  have first :
      Derives candidateBasis
        ((((u ++ u) ++ v) ++ z) ++ z)
        ((((u ++ u) ++ z) ++ v) ++ z) := by
    exact firstRaw.symm
  have secondRaw :=
    SemigroupBasis.CoRoots.Order6FactorPairS2S5107Prelude.derivesBasisSubstitution
      SemigroupBasis.CoRoots.Order6FactorPairS2S5107Prelude.attachmentXZYYXLaw
      (by
        simp [SemigroupBasis.CoRoots.Order6FactorPairS2S5107Prelude.basis])
      (instantiateThreeWords u z v)
  change
    Derives candidateBasis
      ((((u ++ u) ++ z) ++ v) ++ z)
      ((((u ++ v) ++ z) ++ z) ++ u) at secondRaw
  have second :
      Derives candidateBasis
        ((((u ++ u) ++ z) ++ v) ++ z)
        (((u ++ v) ++ (z ++ z)) ++ u) := by
    simpa [Word.append_assoc] using secondRaw
  exact first.trans second

/-- Commute two square blocks using the candidate's final and initial
square switches. This is the balanced controller used by all square-bank
permutations below. -/
private theorem derivesSquareBlockCommutation
    (left right : Word Nat) :
    Derives candidateBasis
      ((left ++ left) ++ (right ++ right))
      ((right ++ right) ++ (left ++ left)) := by
  have first :=
    SemigroupBasis.CoRoots.Order6FactorPairS2S5107Prelude.derivesSquareFinalSwitch
      left right
  have second :=
    SemigroupBasis.CoRoots.Order6FactorPairS2S5107Prelude.derivesSquareInitialSwitch
      right left
  exact first.trans second.symm

/-- List-level square commutation for singleton marker squares. -/
private theorem listDerivesSquareBlockCommutation
    (left right : Nat) :
    ListDerives
      (SemigroupBasis.CoRoots.S5_107.renderMultipleSquares [left, right])
      (SemigroupBasis.CoRoots.S5_107.renderMultipleSquares [right, left]) := by
  simpa [SemigroupBasis.CoRoots.S5_107.renderMultipleSquares,
    Word.singleton, Word.append, List.append_assoc] using
      (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord <|
        derivesSquareBlockCommutation
          (Word.singleton left) (Word.singleton right))

/-- Any permutation of a retained marker-square bank is derivable without
changing occurrence parity. -/
private theorem listDerivesMultipleSquarePermutation
    {source target : List Nat}
    (permutation : source.Perm target) :
    ListDerives
      (SemigroupBasis.CoRoots.S5_107.renderMultipleSquares source)
      (SemigroupBasis.CoRoots.S5_107.renderMultipleSquares target) := by
  induction permutation with
  | nil =>
      exact
        SemigroupBasis.CoRoots.S5_107.ListDerives.empty
          (basis := candidateBasis)
  | cons letter _ inductionHypothesis =>
      simpa [SemigroupBasis.CoRoots.S5_107.renderMultipleSquares] using
        inductionHypothesis.prepend [letter, letter]
  | swap left right rest =>
      have swapped :=
        listDerivesSquareBlockCommutation left right
      simpa [SemigroupBasis.CoRoots.S5_107.renderMultipleSquares] using
        (swapped.append
          (SemigroupBasis.CoRoots.S5_107.renderMultipleSquares rest)).symm
  | trans _ _ firstHypothesis secondHypothesis =>
      exact firstHypothesis.trans secondHypothesis

/-- Remove every later square carrying one selected label, retaining its
first square. -/
private theorem listDerivesRemoveRepeatedSquare
    (anchor : Nat) :
    ∀ labels : List Nat,
      ListDerives
        (SemigroupBasis.CoRoots.S5_107.renderMultipleSquares
          (anchor :: labels))
        (SemigroupBasis.CoRoots.S5_107.renderMultipleSquares
          (anchor ::
            labels.filter
              (fun label => decide (label ≠ anchor))))
  | [] =>
      SemigroupBasis.CoRoots.S5_107.ListDerives.refl
        (basis := candidateBasis) _
  | label :: labels => by
      by_cases equal : label = anchor
      · subst label
        have contract :=
          (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord <|
            SemigroupBasis.CoRoots.Order6FactorPairS2S5107Prelude.derivesFourToTwo
              (Word.singleton anchor)).append
              (SemigroupBasis.CoRoots.S5_107.renderMultipleSquares labels)
        have contractStep :
            ListDerives
              (SemigroupBasis.CoRoots.S5_107.renderMultipleSquares
                (anchor :: anchor :: labels))
              (SemigroupBasis.CoRoots.S5_107.renderMultipleSquares
                (anchor :: labels)) := by
          simpa [SemigroupBasis.CoRoots.S5_107.renderMultipleSquares,
            Word.singleton, Word.append,
            List.append_assoc] using contract
        simpa [SemigroupBasis.CoRoots.S5_107.renderMultipleSquares] using
          contractStep.trans
            (listDerivesRemoveRepeatedSquare anchor labels)
      · have commuteFront :
            ListDerives
              (SemigroupBasis.CoRoots.S5_107.renderMultipleSquares
                (anchor :: label :: labels))
              (SemigroupBasis.CoRoots.S5_107.renderMultipleSquares
                (label :: anchor :: labels)) := by
          simpa [SemigroupBasis.CoRoots.S5_107.renderMultipleSquares,
            List.append_assoc] using
              (listDerivesSquareBlockCommutation
                anchor label).append
                (SemigroupBasis.CoRoots.S5_107.renderMultipleSquares labels)
        have removeTail :
            ListDerives
              (SemigroupBasis.CoRoots.S5_107.renderMultipleSquares
                (label :: anchor :: labels))
              (SemigroupBasis.CoRoots.S5_107.renderMultipleSquares
                (label :: anchor ::
                  labels.filter
                    (fun next =>
                      decide (next ≠ anchor)))) := by
          simpa [SemigroupBasis.CoRoots.S5_107.renderMultipleSquares] using
            (listDerivesRemoveRepeatedSquare
              anchor labels).prepend [label, label]
        have commuteBack :
            ListDerives
              (SemigroupBasis.CoRoots.S5_107.renderMultipleSquares
                (label :: anchor ::
                  labels.filter
                    (fun next =>
                      decide (next ≠ anchor))))
              (SemigroupBasis.CoRoots.S5_107.renderMultipleSquares
                (anchor :: label ::
                  labels.filter
                    (fun next =>
                      decide (next ≠ anchor)))) := by
          simpa [SemigroupBasis.CoRoots.S5_107.renderMultipleSquares,
            List.append_assoc] using
              (listDerivesSquareBlockCommutation
                label anchor).append
                (SemigroupBasis.CoRoots.S5_107.renderMultipleSquares
                  (labels.filter
                    (fun next =>
                      decide (next ≠ anchor))))
        simpa [SemigroupBasis.CoRoots.S5_107.renderMultipleSquares,
          equal] using
            commuteFront.trans (removeTail.trans commuteBack)

/-- Deduplicate a retained marker-square bank using only balanced square
commutations and `x^4 = x^2`. -/
private theorem listDerivesMultipleSquareDedup :
    ∀ labels : List Nat,
      ListDerives
        (SemigroupBasis.CoRoots.S5_107.renderMultipleSquares labels)
        (SemigroupBasis.CoRoots.S5_107.renderMultipleSquares
          (SemigroupBasis.CoRoots.S5_107.distinctLetters labels))
  | [] =>
      SemigroupBasis.CoRoots.S5_107.ListDerives.empty
        (basis := candidateBasis)
  | label :: labels => by
      have dedupTail :
          ListDerives
            (SemigroupBasis.CoRoots.S5_107.renderMultipleSquares
              (label :: labels))
            (SemigroupBasis.CoRoots.S5_107.renderMultipleSquares
              (label ::
                SemigroupBasis.CoRoots.S5_107.distinctLetters labels)) := by
        simpa [SemigroupBasis.CoRoots.S5_107.renderMultipleSquares] using
          (listDerivesMultipleSquareDedup labels).prepend
            [label, label]
      exact
        dedupTail.trans <|
          listDerivesRemoveRepeatedSquare
            label
            (SemigroupBasis.CoRoots.S5_107.distinctLetters labels)

/-- Candidate version of the sealed anchored block swap for arbitrary
nonempty list blocks. -/
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
  simpa [SemigroupBasis.CoRoots.S5_107.listWordOfCons,
    Word.singleton, Word.append, List.append_assoc] using
      (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord <|
        SemigroupBasis.CoRoots.Order6FactorPairS2S5107Prelude.derivesAnchoredBlockSwap
          (Word.singleton anchor)
          (SemigroupBasis.CoRoots.S5_107.listWordOfCons
            leftHead leftTail)
          (SemigroupBasis.CoRoots.S5_107.listWordOfCons
            rightHead rightTail))

/-- Lee's expanded factor transposition, replayed entirely in the balanced
candidate calculus. -/
private theorem listDerivesExpandedFactorSwap
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
    SemigroupBasis.CoRoots.S5_107.listWordOfCons
      controller (controller :: leftBlock)
  have firstMoveCore :=
    SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord <|
      derivesSquareMove
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
    simpa [firstMiddle,
      SemigroupBasis.CoRoots.S5_107.listWordOfCons,
      Word.singleton, Word.append, List.append_assoc] using
        firstMoveCore.append
          (rightBlock ++ [rightMarker, rightMarker])

  let secondMiddle : Word Nat :=
    SemigroupBasis.CoRoots.S5_107.listWordOfCons
      controller
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
    simpa [secondMiddle,
      SemigroupBasis.CoRoots.S5_107.listWordOfCons,
      Word.singleton, Word.append, Word.toList,
      List.append_assoc] using
        (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord <|
          derivesSquareMove
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
    simpa [Word.singleton, Word.append,
      List.append_assoc] using
        swapCore.prepend [controller]

  let thirdMiddle : Word Nat :=
    SemigroupBasis.CoRoots.S5_107.listWordOfCons
      controller
      (rightBlock ++
        [rightMarker, rightMarker, controller] ++ leftBlock)
  have thirdMoveForward :=
    SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord <|
      derivesSquareMove
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
    simpa [thirdMiddle,
      SemigroupBasis.CoRoots.S5_107.listWordOfCons,
      Word.singleton, Word.append, Word.toList,
      List.append_assoc] using
        thirdMoveForward.symm

  let fourthMiddle : Word Nat :=
    SemigroupBasis.CoRoots.S5_107.listWordOfCons
      controller (controller :: rightBlock)
  have fourthMoveCore :=
    SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord <|
      derivesSquareMove
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
    simpa [fourthMiddle,
      SemigroupBasis.CoRoots.S5_107.listWordOfCons,
      Word.singleton, Word.append, List.append_assoc] using
        fourthMoveCore.symm.append
          (leftBlock ++ [leftMarker, leftMarker])

  exact
    firstMove.trans <|
      secondMove.trans <|
        swapped.trans <|
          thirdMove.trans fourthMove

/-- Swap adjacent square-ended factors after a retained square controller. -/
private theorem listDerivesSquaredFactorSwapAfterController
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
    (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord <|
      (SemigroupBasis.CoRoots.Order6FactorPairS2S5107Prelude.derivesFourToTwo
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
    simpa [Word.singleton, Word.append,
      List.append_assoc] using expandController
  have swapStep :=
    (listDerivesExpandedFactorSwap
      controller leftMarker rightMarker
      leftBlock rightBlock).context
        (before ++ controllerBlock) after
  have contractController :=
    (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord <|
      SemigroupBasis.CoRoots.Order6FactorPairS2S5107Prelude.derivesFourToTwo
        (Word.singleton controller)).context
        (before ++ controllerBlock)
        (rightBlock ++ [rightMarker, rightMarker] ++
          leftBlock ++ [leftMarker, leftMarker] ++ after)
  have contractStep :
      ListDerives
        (before ++ controllerBlock ++
          ([controller, controller, controller, controller] ++
            rightBlock ++ [rightMarker, rightMarker] ++
            leftBlock ++ [leftMarker, leftMarker]) ++ after)
        (before ++ controllerBlock ++
          ([controller, controller] ++
            rightBlock ++ [rightMarker, rightMarker] ++
            leftBlock ++ [leftMarker, leftMarker]) ++ after) := by
    simpa [Word.singleton, Word.append, Word.toList,
      List.append_assoc] using contractController
  have swappedAndContracted :=
    swapStep.trans contractStep
  exact expandStep.trans <| by
    simpa [List.append_assoc] using swappedAndContracted

/-- Every permutation of the square-ended factors after a fixed first factor
is available in the candidate calculus. -/
private theorem listDerivesSquaredTailPermutation
    {source target : List (List Nat × Nat)}
    (permutation : source.Perm target) :
    ∀ (first : List Nat × Nat) (final : List Nat),
      ListDerives
        (SemigroupBasis.CoRoots.S5_107.renderSquaredTerminatedBlocks
            (first :: source) ++ final)
        (SemigroupBasis.CoRoots.S5_107.renderSquaredTerminatedBlocks
            (first :: target) ++ final) := by
  induction permutation with
  | nil =>
      intro first final
      exact
        SemigroupBasis.CoRoots.S5_107.ListDerives.refl
          (basis := candidateBasis) _
  | @cons factor source target permutation inductionHypothesis =>
      intro first final
      rcases first with ⟨firstBlock, firstMarker⟩
      have tailStep := inductionHypothesis factor final
      simpa [
        SemigroupBasis.CoRoots.S5_107.renderSquaredTerminatedBlocks,
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
          (SemigroupBasis.CoRoots.S5_107.renderSquaredTerminatedBlocks
            rest ++ final)
          controller leftMarker rightMarker
      simpa [
        SemigroupBasis.CoRoots.S5_107.renderSquaredTerminatedBlocks,
        List.append_assoc] using swapped.symm
  | @trans source middle target first second
      firstHypothesis secondHypothesis =>
      intro leading final
      exact
        (firstHypothesis leading final).trans
          (secondHypothesis leading final)

/-- Install the marker of a square-ended nonempty factor as its leading
anchor. This is the balanced four-attachment calculation underlying the
sealed scanner extraction. -/
private theorem derivesInstallFactorMarkerAsAnchor
    (x y z : Word Nat) :
    Derives candidateBasis
      ((((x ++ x) ++ z) ++ y) ++ y)
      ((((y ++ z) ++ y) ++ x) ++ x) := by
  have exposeRaw :=
    SemigroupBasis.CoRoots.Order6FactorPairS2S5107Prelude.derivesBasisSubstitution
      SemigroupBasis.CoRoots.Order6FactorPairS2S5107Prelude.attachmentXXZYYLaw
      (by
        simp [SemigroupBasis.CoRoots.Order6FactorPairS2S5107Prelude.basis])
      (instantiateThreeWords x y z)
  change
    Derives candidateBasis
      ((((x ++ x) ++ y) ++ z) ++ y)
      ((((x ++ x) ++ z) ++ y) ++ y) at exposeRaw
  have expose := exposeRaw.symm
  have firstRetarget :=
    SemigroupBasis.CoRoots.Order6FactorPairS2S5107Prelude.derivesBasisSubstitution
      SemigroupBasis.CoRoots.Order6FactorPairS2S5107Prelude.attachmentXYYZXLaw
      (by
        simp [SemigroupBasis.CoRoots.Order6FactorPairS2S5107Prelude.basis])
      (instantiateThreeWords x y z)
  change
    Derives candidateBasis
      ((((x ++ x) ++ y) ++ z) ++ y)
      ((((x ++ y) ++ y) ++ z) ++ x) at firstRetarget
  have changeLeadingRaw :=
    SemigroupBasis.CoRoots.Order6FactorPairS2S5107Prelude.derivesBasisSubstitution
      SemigroupBasis.CoRoots.Order6FactorPairS2S5107Prelude.attachmentYXXZYLaw
      (by
        simp [SemigroupBasis.CoRoots.Order6FactorPairS2S5107Prelude.basis])
      (instantiateThreeWords y x z)
  change
    Derives candidateBasis
      ((((y ++ y) ++ x) ++ z) ++ x)
      ((((x ++ y) ++ y) ++ z) ++ x) at changeLeadingRaw
  have changeLeading := changeLeadingRaw.symm
  have finalRetarget :=
    SemigroupBasis.CoRoots.Order6FactorPairS2S5107Prelude.derivesBasisSubstitution
      SemigroupBasis.CoRoots.Order6FactorPairS2S5107Prelude.attachmentXZXYYLaw
      (by
        simp [SemigroupBasis.CoRoots.Order6FactorPairS2S5107Prelude.basis])
      (instantiateThreeWords y x z)
  change
    Derives candidateBasis
      ((((y ++ y) ++ x) ++ z) ++ x)
      ((((y ++ z) ++ y) ++ x) ++ x) at finalRetarget
  exact
    expose.trans <|
      firstRetarget.trans <|
        changeLeading.trans finalRetarget

private theorem listDerivesInstallFactorMarkerAsAnchor
    (x y zHead : Nat) (zTail : List Nat) :
    ListDerives
      ([x, x] ++ (zHead :: zTail) ++ [y, y])
      ([y] ++ (zHead :: zTail) ++ [y, x, x]) := by
  let z :=
    SemigroupBasis.CoRoots.S5_107.listWordOfCons zHead zTail
  simpa [z, SemigroupBasis.CoRoots.S5_107.listWordOfCons,
    Word.singleton, Word.append, List.append_assoc] using
      (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord <|
        derivesInstallFactorMarkerAsAnchor
          (Word.singleton x) (Word.singleton y) z)

/-- Add two copies to the left selected occurrence of a displayed repeated
letter. Unlike the corresponding `S5_107` operation, this preserves every
coordinate parity. -/
private theorem listDerivesTripleLeftOccurrence
    (letter : Nat) :
    ∀ middle : List Nat,
      ListDerives
        ([letter] ++ middle ++ [letter])
        ([letter, letter, letter] ++ middle ++ [letter])
  | [] => by
      simpa [Word.singleton, Word.append, List.append_assoc] using
        (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord <|
          (SemigroupBasis.CoRoots.Order6FactorPairS2S5107Prelude.derivesFourToTwo
            (Word.singleton letter)).symm)
  | head :: tail => by
      let middleWord :=
        SemigroupBasis.CoRoots.S5_107.listWordOfCons head tail
      simpa [middleWord,
        SemigroupBasis.CoRoots.S5_107.listWordOfCons,
        Word.singleton, Word.append, List.append_assoc] using
          (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord <|
            (SemigroupBasis.CoRoots.Order6FactorPairS2S5107Prelude.derivesTripleLeftContraction
              (Word.singleton letter) middleWord).symm)

/-- Add two copies to the right selected occurrence of a displayed repeated
letter. -/
private theorem listDerivesTripleRightOccurrence
    (letter : Nat) :
    ∀ middle : List Nat,
      ListDerives
        ([letter] ++ middle ++ [letter])
        ([letter] ++ middle ++ [letter, letter, letter])
  | [] => by
      simpa [Word.singleton, Word.append, List.append_assoc] using
        (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord <|
          (SemigroupBasis.CoRoots.Order6FactorPairS2S5107Prelude.derivesFourToTwo
            (Word.singleton letter)).symm)
  | head :: tail => by
      let middleWord :=
        SemigroupBasis.CoRoots.S5_107.listWordOfCons head tail
      simpa [middleWord,
        SemigroupBasis.CoRoots.S5_107.listWordOfCons,
        Word.singleton, Word.append, List.append_assoc] using
          (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord <|
            SemigroupBasis.CoRoots.Order6FactorPairS2S5107Prelude.derivesRightTripleExpansion
              (Word.singleton letter) middleWord)

/-- Triple one selected occurrence of a globally repeated letter. The
witness occurrence may lie on either side of the selected position. -/
private theorem listDerivesTripleSelectedOccurrence
    (letter : Nat) (before after : List Nat)
    (multiple :
      2 ≤ (before ++ [letter] ++ after).count letter) :
    ListDerives
      (before ++ [letter] ++ after)
      (before ++ [letter, letter, letter] ++ after) := by
  by_cases afterMember : letter ∈ after
  · obtain ⟨middle, suffix, split⟩ :=
      List.mem_iff_append.mp afterMember
    have expanded :=
      (listDerivesTripleLeftOccurrence
        letter middle).context before suffix
    simpa [split, List.append_assoc] using expanded
  · have beforeMember : letter ∈ before := by
      apply Classical.byContradiction
      intro beforeAbsent
      have beforeZero : before.count letter = 0 :=
        List.count_eq_zero.mpr beforeAbsent
      have afterZero : after.count letter = 0 :=
        List.count_eq_zero.mpr afterMember
      have countOne :
          (before ++ [letter] ++ after).count letter = 1 := by
        simp [List.count_append, beforeZero, afterZero]
      rw [countOne] at multiple
      omega
    obtain ⟨pre, middle, split⟩ :=
      List.mem_iff_append.mp beforeMember
    have expanded :=
      (listDerivesTripleRightOccurrence
        letter middle).context pre after
    simpa [split, List.append_assoc] using expanded

/-- Parity-safe replacement for
`S5_107.listDerivesPrependToAnchoredMiddle`. The selected terminal anchor is
tripled rather than duplicated; marker installation consumes two adjacent
copies and carries the third copy forward as explicit parity debt. -/
private theorem listDerivesPrependToAnchoredMiddleWithDebt
    (x anchor zHead : Nat) (zTail suffix : List Nat)
    (anchorInMiddle : anchor ∈ zHead :: zTail) :
    ListDerives
      ([x, x] ++ (zHead :: zTail) ++ [anchor] ++ suffix)
      ([anchor] ++ (zHead :: zTail) ++
        [anchor, x, x, anchor] ++ suffix) := by
  have middlePositive :
      0 < (zHead :: zTail).count anchor :=
    List.count_pos_iff.mpr anchorInMiddle
  have anchorMultiple :
      2 ≤
        (([x, x] ++ (zHead :: zTail)) ++
          [anchor] ++ suffix).count anchor := by
    have singletonCount :
        [anchor].count anchor = 1 := by
      simp
    rw [List.count_append, List.count_append,
      List.count_append, singletonCount]
    omega
  have tripled :=
    listDerivesTripleSelectedOccurrence
      anchor
      ([x, x] ++ (zHead :: zTail))
      suffix
      anchorMultiple
  have tripledStep :
      ListDerives
        ([x, x] ++ (zHead :: zTail) ++ [anchor] ++ suffix)
        ([x, x] ++ (zHead :: zTail) ++
          [anchor, anchor, anchor] ++ suffix) := by
    simpa [List.append_assoc] using tripled
  have installed :=
    (listDerivesInstallFactorMarkerAsAnchor
      x anchor zHead zTail).append ([anchor] ++ suffix)
  have installedStep :
      ListDerives
        ([x, x] ++ (zHead :: zTail) ++
          [anchor, anchor, anchor] ++ suffix)
        ([anchor] ++ (zHead :: zTail) ++
          [anchor, x, x, anchor] ++ suffix) := by
    simpa [List.append_assoc] using installed
  exact tripledStep.trans installedStep

/-- Render marker squares while retaining one anchor debt between successive
squares. The debt count is exactly the number of recursive anchor
installations in `listDerivesAnchorNonemptyFactorChainWithDebt`. -/
private def renderMarkerSquaresWithAnchorDebt
    (anchor : Nat) : List Nat → List Nat
  | [] => []
  | [marker] => [marker, marker]
  | marker :: next :: rest =>
      [marker, marker, anchor] ++
        renderMarkerSquaresWithAnchorDebt anchor (next :: rest)

/-- Balanced right-to-left anchor extraction for a nonempty chain of
square-ended factors. Every recursive prepend adds two anchor occurrences:
one becomes the new leading anchor and the other remains explicitly between
successive marker squares. -/
private theorem listDerivesAnchorNonemptyFactorChainWithDebt
    (leadingBlock : List Nat) (leadingMarker anchor : Nat)
    (front : List (List Nat × Nat))
    (lastHead : Nat) (lastTail suffix : List Nat)
    (frontBlocksNonempty :
      ∀ factor ∈ front, factor.1 ≠ []) :
    ListDerives
      (leadingBlock ++ [leadingMarker, leadingMarker] ++
        SemigroupBasis.CoRoots.S5_107.renderSquaredTerminatedBlocks
          (front ++ [((lastHead :: lastTail), anchor)]) ++
        suffix)
      (leadingBlock ++ [anchor] ++
        SemigroupBasis.CoRoots.S5_107.renderAnchoredBlocks anchor
          (SemigroupBasis.CoRoots.S5_107.terminatedFactorBlocks front ++
            [lastHead :: lastTail]) ++
        renderMarkerSquaresWithAnchorDebt anchor
          (leadingMarker ::
            SemigroupBasis.CoRoots.S5_107.terminatedFactorMarkers front) ++
        suffix) := by
  induction front generalizing leadingBlock leadingMarker with
  | nil =>
      have installed :=
        (listDerivesInstallFactorMarkerAsAnchor
          leadingMarker anchor lastHead lastTail).context
            leadingBlock suffix
      simpa [
        SemigroupBasis.CoRoots.S5_107.terminatedFactorBlocks,
        SemigroupBasis.CoRoots.S5_107.terminatedFactorMarkers,
        SemigroupBasis.CoRoots.S5_107.renderSquaredTerminatedBlocks,
        SemigroupBasis.CoRoots.S5_107.renderAnchoredBlocks,
        renderMarkerSquaresWithAnchorDebt,
        List.append_assoc] using installed
  | cons factor rest inductionHypothesis =>
      rcases factor with ⟨block, marker⟩
      have blockNonempty : block ≠ [] :=
        frontBlocksNonempty (block, marker) (by simp)
      obtain ⟨blockHead, blockTail, rfl⟩ :=
        List.exists_cons_of_ne_nil blockNonempty
      have restBlocksNonempty :
          ∀ candidate ∈ rest, candidate.1 ≠ [] := by
        intro candidate member
        exact
          frontBlocksNonempty candidate
            (List.mem_cons_of_mem
              (blockHead :: blockTail, marker) member)
      have tailStep :=
        inductionHypothesis
          (blockHead :: blockTail) marker restBlocksNonempty
      have tailStep' :=
        tailStep.prepend
          (leadingBlock ++ [leadingMarker, leadingMarker])
      let middleTail : List Nat :=
        blockTail ++ [anchor] ++
          SemigroupBasis.CoRoots.S5_107.renderAnchoredBlocks anchor
            (SemigroupBasis.CoRoots.S5_107.terminatedFactorBlocks rest) ++
          (lastHead :: lastTail)
      let debtSuffix : List Nat :=
        renderMarkerSquaresWithAnchorDebt anchor
            (marker ::
              SemigroupBasis.CoRoots.S5_107.terminatedFactorMarkers rest) ++
          suffix
      have tailNormalized :
          ListDerives
            (leadingBlock ++ [leadingMarker, leadingMarker] ++
              (blockHead :: blockTail) ++ [marker, marker] ++
              SemigroupBasis.CoRoots.S5_107.renderSquaredTerminatedBlocks
                (rest ++
                  [((lastHead :: lastTail), anchor)]) ++
              suffix)
            (leadingBlock ++ [leadingMarker, leadingMarker] ++
              (blockHead :: middleTail) ++
              [anchor] ++ debtSuffix) := by
        simpa [middleTail, debtSuffix,
          SemigroupBasis.CoRoots.S5_107.terminatedFactorBlocks,
          SemigroupBasis.CoRoots.S5_107.terminatedFactorMarkers,
          SemigroupBasis.CoRoots.S5_107.renderAnchoredBlocks,
          List.append_assoc] using tailStep'
      have anchorInMiddle :
          anchor ∈ blockHead :: middleTail := by
        simp [middleTail]
      have prependStep :=
        (listDerivesPrependToAnchoredMiddleWithDebt
          leadingMarker anchor blockHead middleTail
          debtSuffix anchorInMiddle).prepend leadingBlock
      have prepended :
          ListDerives
            (leadingBlock ++ [leadingMarker, leadingMarker] ++
              (blockHead :: middleTail) ++
              [anchor] ++ debtSuffix)
            (leadingBlock ++ [anchor] ++
              (blockHead :: middleTail) ++
              [anchor, leadingMarker, leadingMarker, anchor] ++
              debtSuffix) := by
        simpa [List.append_assoc] using prependStep
      have combined := tailNormalized.trans prepended
      simpa [middleTail, debtSuffix,
        SemigroupBasis.CoRoots.S5_107.terminatedFactorBlocks,
        SemigroupBasis.CoRoots.S5_107.terminatedFactorMarkers,
        SemigroupBasis.CoRoots.S5_107.renderSquaredTerminatedBlocks,
        SemigroupBasis.CoRoots.S5_107.renderAnchoredBlocks,
        renderMarkerSquaresWithAnchorDebt,
        List.append_assoc] using combined

/-- Render each scanner factor with three copies of its terminating marker.
This is the parity-preserving replacement for
`S5_107.renderSquaredTerminatedBlocks`. -/
private def renderTripledTerminatedBlocks :
    List (List Nat × Nat) → List Nat
  | [] => []
  | (block, marker) :: rest =>
      block ++ [marker, marker, marker] ++
        renderTripledTerminatedBlocks rest

/-- Regard the third copy of a tripled marker as part of its block. The
ordinary square renderer of these debt-attached factors is definitionally
the tripled renderer. -/
private def debtAttachedFactor
    (factor : List Nat × Nat) : List Nat × Nat :=
  (factor.1 ++ [factor.2], factor.2)

private theorem renderSquaredDebtAttachedFactors :
    ∀ factors : List (List Nat × Nat),
      SemigroupBasis.CoRoots.S5_107.renderSquaredTerminatedBlocks
          (factors.map debtAttachedFactor) =
        renderTripledTerminatedBlocks factors
  | [] => rfl
  | (block, marker) :: rest => by
      simp [debtAttachedFactor,
        SemigroupBasis.CoRoots.S5_107.renderSquaredTerminatedBlocks,
        renderTripledTerminatedBlocks,
        renderSquaredDebtAttachedFactors rest,
        List.append_assoc]

/-- Tripled scanner factors after the first factor can be permuted without
first separating their marker debt. -/
private theorem listDerivesTripledTailPermutation
    {source target : List (List Nat × Nat)}
    (permutation : source.Perm target) :
    ∀ (first : List Nat × Nat) (final : List Nat),
      ListDerives
        (renderTripledTerminatedBlocks (first :: source) ++ final)
        (renderTripledTerminatedBlocks (first :: target) ++ final) := by
  intro first final
  have mappedPermutation :
      (source.map debtAttachedFactor).Perm
        (target.map debtAttachedFactor) :=
    permutation.map debtAttachedFactor
  have permuted :=
    listDerivesSquaredTailPermutation
      mappedPermutation (debtAttachedFactor first) final
  change
    ListDerives
      (SemigroupBasis.CoRoots.S5_107.renderSquaredTerminatedBlocks
          ((first :: source).map debtAttachedFactor) ++ final)
      (SemigroupBasis.CoRoots.S5_107.renderSquaredTerminatedBlocks
          ((first :: target).map debtAttachedFactor) ++ final) at permuted
  simpa only [renderSquaredDebtAttachedFactors] using permuted

/-- Swap the final ordered pair in a repeated `x y` sandwich. The empty
middle is square interleaving followed by the final square switch; the
nonempty middle is the reverse `XYZXY` attachment followed by `XYZYX`. -/
private theorem listDerivesSwapRepeatedPair
    (x y : Nat) :
    ∀ middle : List Nat,
      ListDerives
        ([x, y] ++ middle ++ [x, y])
        ([x, y] ++ middle ++ [y, x])
  | [] => by
      have interleaved :=
        SemigroupBasis.CoRoots.Order6FactorPairS2S5107Prelude.derivesSquareInterleave
          (Word.singleton x) (Word.singleton y)
      have switched :=
        SemigroupBasis.CoRoots.Order6FactorPairS2S5107Prelude.derivesSquareFinalSwitch
          (Word.singleton x) (Word.singleton y)
      simpa [Word.singleton, Word.append,
        List.append_assoc] using
          (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord <|
            interleaved.symm.trans switched)
  | middleHead :: middleTail => by
      let middleWord :=
        SemigroupBasis.CoRoots.S5_107.listWordOfCons
          middleHead middleTail
      let xWord : Word Nat := Word.singleton x
      let yWord : Word Nat := Word.singleton y
      have firstRaw :=
        SemigroupBasis.CoRoots.Order6FactorPairS2S5107Prelude.derivesBasisSubstitution
          SemigroupBasis.CoRoots.Order6FactorPairS2S5107Prelude.attachmentXYZXYLaw
          (by
            simp [SemigroupBasis.CoRoots.Order6FactorPairS2S5107Prelude.basis])
          (instantiateThreeWords
            xWord yWord middleWord)
      change
        Derives candidateBasis
          (((((xWord ++ xWord) ++ yWord) ++ middleWord) ++ yWord))
          (((((xWord ++ yWord) ++ middleWord) ++ xWord) ++ yWord))
          at firstRaw
      have secondRaw :=
        SemigroupBasis.CoRoots.Order6FactorPairS2S5107Prelude.derivesBasisSubstitution
          SemigroupBasis.CoRoots.Order6FactorPairS2S5107Prelude.attachmentXYZYXLaw
          (by
            simp [SemigroupBasis.CoRoots.Order6FactorPairS2S5107Prelude.basis])
          (instantiateThreeWords
            xWord yWord middleWord)
      change
        Derives candidateBasis
          (((((xWord ++ xWord) ++ yWord) ++ middleWord) ++ yWord))
          (((((xWord ++ yWord) ++ middleWord) ++ yWord) ++ xWord))
          at secondRaw
      simpa [xWord, yWord, middleWord, Word.toList,
        SemigroupBasis.CoRoots.S5_107.listWordOfCons,
        Word.singleton, Word.append, List.append_assoc] using
          (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord <|
            firstRaw.symm.trans secondRaw)

/-- Adjacent marker debts can be transposed behind retained witness squares.
The witness bank is restored literally after the transposition. -/
private theorem listDerivesSwapDebtAfterSquareWitnesses
    (x y : Nat) (middle suffix : List Nat) :
    ListDerives
      ([x, x, y, y] ++ middle ++ [x, y] ++ suffix)
      ([x, x, y, y] ++ middle ++ [y, x] ++ suffix) := by
  have interleaved :=
    SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord <|
      SemigroupBasis.CoRoots.Order6FactorPairS2S5107Prelude.derivesSquareInterleave
        (Word.singleton x) (Word.singleton y)
  have expose :=
    interleaved.append
      (middle ++ [x, y] ++ suffix)
  have exposeStep :
      ListDerives
        ([x, x, y, y] ++ middle ++ [x, y] ++ suffix)
        ([x, y, x, y] ++ middle ++ [x, y] ++ suffix) := by
    simpa [SemigroupBasis.CoRoots.S5_107.renderMultipleSquares,
      List.append_assoc] using expose
  have swapStep :=
    (listDerivesSwapRepeatedPair
      x y ([x, y] ++ middle)).append suffix
  have swapStep' :
      ListDerives
        ([x, y, x, y] ++ middle ++ [x, y] ++ suffix)
        ([x, y, x, y] ++ middle ++ [y, x] ++ suffix) := by
    simpa [List.append_assoc] using swapStep
  have restore :=
    interleaved.symm.append
      (middle ++ [y, x] ++ suffix)
  have restoreStep :
      ListDerives
        ([x, y, x, y] ++ middle ++ [y, x] ++ suffix)
        ([x, x, y, y] ++ middle ++ [y, x] ++ suffix) := by
    simpa [SemigroupBasis.CoRoots.S5_107.renderMultipleSquares,
      List.append_assoc] using restore
  exact exposeStep.trans (swapStep'.trans restoreStep)

/-- A retained square for every debt label permits an arbitrary permutation
of the debt tail. The square bank itself is restored after every adjacent
transposition. -/
private theorem listDerivesDebtPermutationWithSquareBank
    {bank source target : List Nat}
    (permutation : source.Perm target) :
    (∀ letter ∈ source, letter ∈ bank) →
      ∀ (before suffix : List Nat),
        ListDerives
          (SemigroupBasis.CoRoots.S5_107.renderMultipleSquares bank ++
            before ++ source ++ suffix)
          (SemigroupBasis.CoRoots.S5_107.renderMultipleSquares bank ++
            before ++ target ++ suffix) := by
  induction permutation with
  | nil =>
      intro _ before suffix
      exact
        SemigroupBasis.CoRoots.S5_107.ListDerives.refl
          (basis := candidateBasis) _
  | @cons letter source target permutation inductionHypothesis =>
      intro covered before suffix
      have tailCovered :
          ∀ tested ∈ source, tested ∈ bank := by
        intro tested member
        exact covered tested (List.mem_cons_of_mem letter member)
      have tailStep :=
        inductionHypothesis tailCovered
          (before ++ [letter]) suffix
      simpa [List.append_assoc] using tailStep
  | swap left right rest =>
      intro covered before suffix
      by_cases equal : right = left
      · subst right
        exact
          SemigroupBasis.CoRoots.S5_107.ListDerives.refl
            (basis := candidateBasis) _
      · have rightMember : right ∈ bank :=
          covered right (by simp)
        have leftMember : left ∈ bank :=
          covered left (by simp)
        have leftInErase : left ∈ bank.erase right := by
          rw [List.mem_erase_of_ne (Ne.symm equal)]
          exact leftMember
        let remainder := (bank.erase right).erase left
        have arrangement :
            bank.Perm (right :: left :: remainder) :=
          (List.perm_cons_erase rightMember).trans <|
            List.Perm.cons right <| by
              simpa [remainder] using
                List.perm_cons_erase leftInErase
        have exposeBank :=
          (listDerivesMultipleSquarePermutation arrangement).context
            []
            (before ++ right :: left :: rest ++ suffix)
        have exposeBankStep :
            ListDerives
              (SemigroupBasis.CoRoots.S5_107.renderMultipleSquares bank ++
                before ++ right :: left :: rest ++ suffix)
              ([right, right, left, left] ++
                SemigroupBasis.CoRoots.S5_107.renderMultipleSquares
                  remainder ++
                before ++ right :: left :: rest ++ suffix) := by
          simpa [SemigroupBasis.CoRoots.S5_107.renderMultipleSquares,
            List.append_assoc] using exposeBank
        have swapped :=
          listDerivesSwapDebtAfterSquareWitnesses
            right left
            (SemigroupBasis.CoRoots.S5_107.renderMultipleSquares
              remainder ++ before)
            (rest ++ suffix)
        have swappedStep :
            ListDerives
              ([right, right, left, left] ++
                SemigroupBasis.CoRoots.S5_107.renderMultipleSquares
                  remainder ++
                before ++ right :: left :: rest ++ suffix)
              ([right, right, left, left] ++
                SemigroupBasis.CoRoots.S5_107.renderMultipleSquares
                  remainder ++
                before ++ left :: right :: rest ++ suffix) := by
          simpa [List.append_assoc] using swapped
        have restoreBank :=
          (listDerivesMultipleSquarePermutation arrangement).symm.context
            []
            (before ++ left :: right :: rest ++ suffix)
        have restoreBankStep :
            ListDerives
              ([right, right, left, left] ++
                SemigroupBasis.CoRoots.S5_107.renderMultipleSquares
                  remainder ++
                before ++ left :: right :: rest ++ suffix)
              (SemigroupBasis.CoRoots.S5_107.renderMultipleSquares bank ++
                before ++ left :: right :: rest ++ suffix) := by
          simpa [SemigroupBasis.CoRoots.S5_107.renderMultipleSquares,
            List.append_assoc] using restoreBank
        exact
          exposeBankStep.trans <|
            swappedStep.trans restoreBankStep
  | @trans source middle target first second
      firstHypothesis secondHypothesis =>
      intro covered before suffix
      have middleCovered :
          ∀ letter ∈ middle, letter ∈ bank := by
        intro letter member
        exact covered letter (first.mem_iff.mpr member)
      exact
        (firstHypothesis covered before suffix).trans
          (secondHypothesis middleCovered before suffix)

/-- Retain one copy of a singleton, two copies of a positive even
multiplicity, and three copies of a larger odd multiplicity. -/
private def parityDebtReduce : List Nat → List Nat
  | [] => []
  | letter :: rest =>
      let reduced := parityDebtReduce rest
      if reduced.count letter < 3 then
        letter :: reduced
      else
        reduced.erase letter

private theorem parityDebtReduce_count_le_three
    (tested : Nat) (letters : List Nat) :
    (parityDebtReduce letters).count tested ≤ 3 := by
  induction letters with
  | nil =>
      simp [parityDebtReduce]
  | cons letter rest inductionHypothesis =>
      simp only [parityDebtReduce]
      split <;> rename_i countTest
      · by_cases equal : tested = letter
        · subst tested
          rw [List.count_cons_self]
          omega
        · rw [List.count_cons_of_ne (Ne.symm equal)]
          exact inductionHypothesis
      · by_cases equal : tested = letter
        · subst tested
          rw [List.count_erase_self]
          omega
        · rw [List.count_erase_of_ne equal]
          exact inductionHypothesis

private theorem mem_parityDebtReduce_iff
    (tested : Nat) (letters : List Nat) :
    tested ∈ parityDebtReduce letters ↔ tested ∈ letters := by
  induction letters with
  | nil =>
      simp [parityDebtReduce]
  | cons letter rest inductionHypothesis =>
      simp only [parityDebtReduce]
      split <;> rename_i countTest
      · simp [inductionHypothesis]
      · have countBound :=
          parityDebtReduce_count_le_three letter rest
        have countEq :
            (parityDebtReduce rest).count letter = 3 := by
          omega
        by_cases equal : tested = letter
        · subst tested
          have remains :
              letter ∈ (parityDebtReduce rest).erase letter := by
            rw [← List.count_pos_iff,
              List.count_erase_self, countEq]
            omega
          simp [remains]
        · rw [List.mem_erase_of_ne equal]
          simp [inductionHypothesis, equal]

private theorem parityDebtReduce_count_mod_two
    (tested : Nat) (letters : List Nat) :
    (parityDebtReduce letters).count tested % 2 =
      letters.count tested % 2 := by
  induction letters with
  | nil =>
      simp [parityDebtReduce]
  | cons letter rest inductionHypothesis =>
      simp only [parityDebtReduce]
      split <;> rename_i countTest
      · by_cases equal : tested = letter
        · subst tested
          rw [List.count_cons_self, List.count_cons_self]
          omega
        · rw [List.count_cons_of_ne (Ne.symm equal),
            List.count_cons_of_ne (Ne.symm equal)]
          exact inductionHypothesis
      · by_cases equal : tested = letter
        · subst tested
          have countBound :=
            parityDebtReduce_count_le_three letter rest
          have countEq :
              (parityDebtReduce rest).count letter = 3 := by
            omega
          rw [List.count_erase_self,
            List.count_cons_self, countEq]
          omega
        · rw [List.count_erase_of_ne equal,
            List.count_cons_of_ne (Ne.symm equal)]
          exact inductionHypothesis

private theorem parityDebtReduce_capped_count
    (tested : Nat) (letters : List Nat) :
    Nat.min ((parityDebtReduce letters).count tested) 2 =
      Nat.min (letters.count tested) 2 := by
  induction letters with
  | nil =>
      simp [parityDebtReduce]
  | cons letter rest inductionHypothesis =>
      simp only [parityDebtReduce]
      split <;> rename_i countTest
      · by_cases equal : tested = letter
        · subst tested
          rw [List.count_cons_self, List.count_cons_self]
          by_cases reducedSmall :
              (parityDebtReduce rest).count letter < 2
          · have reducedMin :
                Nat.min
                    ((parityDebtReduce rest).count letter) 2 =
                  (parityDebtReduce rest).count letter :=
              Nat.min_eq_left (by omega)
            have originalSmall : rest.count letter < 2 := by
              by_cases small : rest.count letter < 2
              · exact small
              · have originalMin :
                    Nat.min (rest.count letter) 2 = 2 :=
                  Nat.min_eq_right (by omega)
                rw [reducedMin, originalMin] at inductionHypothesis
                omega
            have originalMin :
                Nat.min (rest.count letter) 2 =
                  rest.count letter :=
              Nat.min_eq_left (by omega)
            have countEq :
                (parityDebtReduce rest).count letter =
                  rest.count letter := by
              rw [reducedMin, originalMin] at inductionHypothesis
              exact inductionHypothesis
            rw [countEq]
          · have reducedLarge :
                2 ≤ (parityDebtReduce rest).count letter := by
              omega
            have originalLarge : 2 ≤ rest.count letter := by
              by_cases large : 2 ≤ rest.count letter
              · exact large
              · have reducedMin :
                    Nat.min
                        ((parityDebtReduce rest).count letter) 2 =
                      2 :=
                  Nat.min_eq_right reducedLarge
                have originalMin :
                    Nat.min (rest.count letter) 2 =
                      rest.count letter :=
                  Nat.min_eq_left (by omega)
                rw [reducedMin, originalMin] at inductionHypothesis
                omega
            have reducedSuccessorMin :
                Nat.min
                    ((parityDebtReduce rest).count letter + 1) 2 =
                  2 :=
              Nat.min_eq_right (by omega)
            have originalSuccessorMin :
                Nat.min (rest.count letter + 1) 2 = 2 :=
              Nat.min_eq_right (by omega)
            exact reducedSuccessorMin.trans originalSuccessorMin.symm
        · rw [List.count_cons_of_ne (Ne.symm equal),
            List.count_cons_of_ne (Ne.symm equal)]
          exact inductionHypothesis
      · by_cases equal : tested = letter
        · subst tested
          have countBound :=
            parityDebtReduce_count_le_three letter rest
          have countEq :
              (parityDebtReduce rest).count letter = 3 := by
            omega
          have reducedMin :
              Nat.min
                  ((parityDebtReduce rest).count letter) 2 =
                2 :=
            Nat.min_eq_right (by omega)
          have originalLarge : 2 ≤ rest.count letter := by
            by_cases large : 2 ≤ rest.count letter
            · exact large
            · have originalMin :
                  Nat.min (rest.count letter) 2 =
                    rest.count letter :=
                Nat.min_eq_left (by omega)
              rw [reducedMin, originalMin] at inductionHypothesis
              omega
          rw [List.count_erase_self,
            List.count_cons_self, countEq]
          simp [Nat.min_eq_right
            (by omega : 2 ≤ rest.count letter + 1)]
        · rw [List.count_erase_of_ne equal,
            List.count_cons_of_ne (Ne.symm equal)]
          exact inductionHypothesis

private theorem parityDebtReduce_count_eq_of_signatures
    {left right : List Nat}
    (capped :
      ∀ tested,
        Nat.min (left.count tested) 2 =
          Nat.min (right.count tested) 2)
    (parity :
      ∀ tested,
        left.count tested % 2 =
          right.count tested % 2) :
    ∀ tested,
      (parityDebtReduce left).count tested =
        (parityDebtReduce right).count tested := by
  intro tested
  have leftBound :=
    parityDebtReduce_count_le_three tested left
  have rightBound :=
    parityDebtReduce_count_le_three tested right
  have reducedCapped :
      Nat.min ((parityDebtReduce left).count tested) 2 =
        Nat.min ((parityDebtReduce right).count tested) 2 := by
    rw [parityDebtReduce_capped_count,
      parityDebtReduce_capped_count, capped tested]
  have reducedParity :
      (parityDebtReduce left).count tested % 2 =
        (parityDebtReduce right).count tested % 2 := by
    rw [parityDebtReduce_count_mod_two,
      parityDebtReduce_count_mod_two, parity tested]
  by_cases leftSmall :
      (parityDebtReduce left).count tested < 2
  · have leftMin :
        Nat.min ((parityDebtReduce left).count tested) 2 =
          (parityDebtReduce left).count tested :=
      Nat.min_eq_left (by omega)
    have rightSmall :
        (parityDebtReduce right).count tested < 2 := by
      by_cases small :
          (parityDebtReduce right).count tested < 2
      · exact small
      · have rightMin :
            Nat.min ((parityDebtReduce right).count tested) 2 = 2 :=
          Nat.min_eq_right (by omega)
        rw [leftMin, rightMin] at reducedCapped
        omega
    have rightMin :
        Nat.min ((parityDebtReduce right).count tested) 2 =
          (parityDebtReduce right).count tested :=
      Nat.min_eq_left (by omega)
    rw [leftMin, rightMin] at reducedCapped
    exact reducedCapped
  · have leftLarge :
        2 ≤ (parityDebtReduce left).count tested := by
      omega
    have rightLarge :
        2 ≤ (parityDebtReduce right).count tested := by
      by_cases large :
          2 ≤ (parityDebtReduce right).count tested
      · exact large
      · have leftMin :
            Nat.min ((parityDebtReduce left).count tested) 2 = 2 :=
          Nat.min_eq_right leftLarge
        have rightMin :
            Nat.min ((parityDebtReduce right).count tested) 2 =
              (parityDebtReduce right).count tested :=
          Nat.min_eq_left (by omega)
        rw [leftMin, rightMin] at reducedCapped
        omega
    omega

private theorem parityDebtReduce_perm_of_signatures
    {left right : List Nat}
    (capped :
      ∀ tested,
        Nat.min (left.count tested) 2 =
          Nat.min (right.count tested) 2)
    (parity :
      ∀ tested,
        left.count tested % 2 =
          right.count tested % 2) :
    (parityDebtReduce left).Perm
      (parityDebtReduce right) := by
  rw [List.perm_iff_count]
  exact parityDebtReduce_count_eq_of_signatures capped parity

private theorem listDerivesDebtToParityReduce
    (bank : List Nat) :
    ∀ (source before suffix : List Nat),
      (∀ letter ∈ source, letter ∈ bank) →
        ListDerives
          (SemigroupBasis.CoRoots.S5_107.renderMultipleSquares bank ++
            before ++ source ++ suffix)
          (SemigroupBasis.CoRoots.S5_107.renderMultipleSquares bank ++
            before ++ parityDebtReduce source ++ suffix)
  | [], before, suffix, _ => by
      simpa [parityDebtReduce] using
        (SemigroupBasis.CoRoots.S5_107.ListDerives.refl
          (basis := candidateBasis)
          (SemigroupBasis.CoRoots.S5_107.renderMultipleSquares bank ++
            before ++ suffix))
  | letter :: rest, before, suffix, covered => by
      have letterMember : letter ∈ bank :=
        covered letter (by simp)
      have restCovered :
          ∀ tested ∈ rest, tested ∈ bank := by
        intro tested member
        exact covered tested (List.mem_cons_of_mem letter member)
      have tailStep :=
        listDerivesDebtToParityReduce
          bank rest (before ++ [letter]) suffix restCovered
      have tailStep' :
          ListDerives
            (SemigroupBasis.CoRoots.S5_107.renderMultipleSquares bank ++
              before ++ letter :: rest ++ suffix)
            (SemigroupBasis.CoRoots.S5_107.renderMultipleSquares bank ++
              before ++ letter :: parityDebtReduce rest ++ suffix) := by
        simpa [List.append_assoc] using tailStep
      by_cases room :
          (parityDebtReduce rest).count letter < 3
      · simpa [parityDebtReduce, room,
          List.append_assoc] using tailStep'
      · have countBound :=
          parityDebtReduce_count_le_three letter rest
        have countEq :
            (parityDebtReduce rest).count letter = 3 := by
          omega
        let remainder :=
          (((parityDebtReduce rest).erase letter).erase letter).erase
            letter
        have firstErase :
            ((parityDebtReduce rest).erase letter).count letter = 2 := by
          rw [List.count_erase_self, countEq]
        have secondErase :
            (((parityDebtReduce rest).erase letter).erase letter).count
              letter = 1 := by
          rw [List.count_erase_self, firstErase]
        have thirdErase :
            remainder.count letter = 0 := by
          simp only [remainder]
          rw [List.count_erase_self, secondErase]
        have sourcePermutation :
            (letter :: parityDebtReduce rest).Perm
              (letter :: letter :: letter :: letter :: remainder) := by
          rw [List.perm_iff_count]
          intro tested
          by_cases equal : tested = letter
          · subst tested
            simp [countEq, thirdErase]
          · simp [remainder, equal, Ne.symm equal]
        have targetPermutation :
            ((parityDebtReduce rest).erase letter).Perm
              (letter :: letter :: remainder) := by
          rw [List.perm_iff_count]
          intro tested
          by_cases equal : tested = letter
          · subst tested
            simp [firstErase, thirdErase]
          · simp [remainder, equal, Ne.symm equal]
        have reducedCovered :
            ∀ tested ∈ parityDebtReduce rest, tested ∈ bank := by
          intro tested member
          exact restCovered tested <|
            (mem_parityDebtReduce_iff tested rest).mp member
        have sourceCovered :
            ∀ tested ∈ letter :: parityDebtReduce rest,
              tested ∈ bank := by
          intro tested member
          rcases List.mem_cons.mp member with rfl | member
          · exact letterMember
          · exact reducedCovered tested member
        have arrangeSource :=
          listDerivesDebtPermutationWithSquareBank
            sourcePermutation sourceCovered before suffix
        have contract :=
          (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord <|
            SemigroupBasis.CoRoots.Order6FactorPairS2S5107Prelude.derivesFourToTwo
              (Word.singleton letter)).context
                (SemigroupBasis.CoRoots.S5_107.renderMultipleSquares bank ++
                  before)
                (remainder ++ suffix)
        have contractStep :
            ListDerives
              (SemigroupBasis.CoRoots.S5_107.renderMultipleSquares bank ++
                before ++
                letter :: letter :: letter :: letter :: remainder ++
                suffix)
              (SemigroupBasis.CoRoots.S5_107.renderMultipleSquares bank ++
                before ++ letter :: letter :: remainder ++ suffix) := by
          simpa [Word.singleton, Word.append,
            List.append_assoc] using contract
        have targetCovered :
            ∀ tested ∈ (parityDebtReduce rest).erase letter,
              tested ∈ bank := by
          intro tested member
          exact reducedCovered tested (List.mem_of_mem_erase member)
        have groupedTargetCovered :
            ∀ tested ∈ letter :: letter :: remainder,
              tested ∈ bank := by
          intro tested member
          exact targetCovered tested
            (targetPermutation.mem_iff.mpr member)
        have restoreTarget :=
          listDerivesDebtPermutationWithSquareBank
            targetPermutation.symm groupedTargetCovered before suffix
        have reducedStep :=
          arrangeSource.trans <|
            contractStep.trans restoreTarget
        exact tailStep'.trans <| by
          simpa [parityDebtReduce, room,
            List.append_assoc] using reducedStep

private theorem count_le_count_tripleSelected
    (tested inserted : Nat)
    (before after : List Nat) :
    (before ++ [inserted] ++ after).count tested ≤
      (before ++ [inserted, inserted, inserted] ++ after).count tested := by
  by_cases equality : tested = inserted
  · subst inserted
    simp [List.count_append]
  · have reverseEquality : inserted ≠ tested :=
      Ne.symm equality
    simp [List.count_append, reverseEquality]

/-- Triple every terminating marker while preserving an arbitrary processed
prefix. Every step adds exactly two copies of one globally repeated marker. -/
private theorem listDerivesTripleTerminatedMarkersAux
    (final : List Nat) :
    ∀ (factors : List (List Nat × Nat))
      (before : List Nat),
      (∀ factor ∈ factors,
        2 ≤
          (before ++
            SemigroupBasis.CoRoots.S5_107.renderTerminatedBlocks factors ++
              final).count factor.2) →
      ListDerives
        (before ++
          SemigroupBasis.CoRoots.S5_107.renderTerminatedBlocks factors ++
            final)
        (before ++ renderTripledTerminatedBlocks factors ++ final)
  | [], before, _ => by
      simpa [SemigroupBasis.CoRoots.S5_107.renderTerminatedBlocks,
        renderTripledTerminatedBlocks] using
          (SemigroupBasis.CoRoots.S5_107.ListDerives.refl
            (basis := candidateBasis) (before ++ final))
  | (block, marker) :: rest, before, multiples => by
      have markerMultiple :
          2 ≤
            ((before ++ block) ++ [marker] ++
              (SemigroupBasis.CoRoots.S5_107.renderTerminatedBlocks rest ++
                final)).count marker := by
        simpa [SemigroupBasis.CoRoots.S5_107.renderTerminatedBlocks,
          List.append_assoc] using
            multiples (block, marker) (by simp)
      have firstRaw :=
        listDerivesTripleSelectedOccurrence
          marker (before ++ block)
          (SemigroupBasis.CoRoots.S5_107.renderTerminatedBlocks rest ++
            final)
          markerMultiple
      have firstStep :
          ListDerives
            (before ++
              SemigroupBasis.CoRoots.S5_107.renderTerminatedBlocks
                ((block, marker) :: rest) ++ final)
            ((before ++ block ++ [marker, marker, marker]) ++
              SemigroupBasis.CoRoots.S5_107.renderTerminatedBlocks rest ++
                final) := by
        simpa [SemigroupBasis.CoRoots.S5_107.renderTerminatedBlocks,
          List.append_assoc] using firstRaw
      have restMultiples :
          ∀ factor ∈ rest,
            2 ≤
              ((before ++ block ++ [marker, marker, marker]) ++
                SemigroupBasis.CoRoots.S5_107.renderTerminatedBlocks rest ++
                  final).count factor.2 := by
        intro factor member
        have oldMultiple :
            2 ≤
              ((before ++ block) ++ [marker] ++
                (SemigroupBasis.CoRoots.S5_107.renderTerminatedBlocks rest ++
                  final)).count factor.2 := by
          simpa [SemigroupBasis.CoRoots.S5_107.renderTerminatedBlocks,
            List.append_assoc] using
              multiples factor (by simp [member])
        have monotone :=
          count_le_count_tripleSelected
            factor.2 marker (before ++ block)
              (SemigroupBasis.CoRoots.S5_107.renderTerminatedBlocks rest ++
                final)
        have newMultiple :=
          Nat.le_trans oldMultiple monotone
        simpa [List.append_assoc] using newMultiple
      have restStep :=
        listDerivesTripleTerminatedMarkersAux
          final rest
          (before ++ block ++ [marker, marker, marker])
          restMultiples
      have restStep' :
          ListDerives
            ((before ++ block ++ [marker, marker, marker]) ++
              SemigroupBasis.CoRoots.S5_107.renderTerminatedBlocks rest ++
                final)
            ((before ++ block ++ [marker, marker, marker]) ++
              renderTripledTerminatedBlocks rest ++ final) := by
        simpa [List.append_assoc] using restStep
      have combined := firstStep.trans restStep'
      simpa [renderTripledTerminatedBlocks,
        List.append_assoc] using combined

/-- Every word derives to its terminated decomposition with every
non-simple marker occurrence tripled. -/
private theorem listDerivesTripleAllTerminatedMarkers
    (letters : List Nat) :
    ListDerives letters
      (renderTripledTerminatedBlocks
          (SemigroupBasis.CoRoots.S5_107.terminatedBlocks letters) ++
        SemigroupBasis.CoRoots.S5_107.terminatedFinalBlock letters) := by
  have multiples :
      ∀ factor ∈
          SemigroupBasis.CoRoots.S5_107.terminatedBlocks letters,
        2 ≤
          (SemigroupBasis.CoRoots.S5_107.renderTerminatedBlocks
              (SemigroupBasis.CoRoots.S5_107.terminatedBlocks letters) ++
            SemigroupBasis.CoRoots.S5_107.terminatedFinalBlock letters).count
              factor.2 := by
    intro factor member
    rw [SemigroupBasis.CoRoots.S5_107.terminatedBlocks_render letters]
    exact
      SemigroupBasis.CoRoots.S5_107.terminatedBlocks_marker_multiple
        letters factor member
  have tripled :=
    listDerivesTripleTerminatedMarkersAux
      (SemigroupBasis.CoRoots.S5_107.terminatedFinalBlock letters)
      (SemigroupBasis.CoRoots.S5_107.terminatedBlocks letters) [] <| by
        simpa using multiples
  simpa [SemigroupBasis.CoRoots.S5_107.terminatedBlocks_render letters] using
    tripled

/-- Move the third copy of a marker across a prefix ending in a square.
The first two copies remain as a square controller. -/
private theorem listDerivesMoveThirdAcrossLastSquare
    (marker lastMarker : Nat) (pre suffix : List Nat) :
    ListDerives
      ([marker, marker, marker] ++ pre ++
        [lastMarker, lastMarker] ++ suffix)
      ([marker, marker] ++ pre ++
        [lastMarker, lastMarker, marker] ++ suffix) := by
  let middle :=
    SemigroupBasis.CoRoots.S5_107.listWordOfCons marker pre
  have moved :=
    SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord <|
      derivesSquareMove
        (Word.singleton marker) middle (Word.singleton lastMarker)
  simpa [middle, SemigroupBasis.CoRoots.S5_107.listWordOfCons,
    Word.singleton, Word.append, List.append_assoc] using
      moved.append suffix

private theorem exists_append_singleton_of_ne_nil
    {α : Type u} :
    ∀ (items : List α), items ≠ [] →
      ∃ front last, items = front ++ [last]
  | [], nonempty => False.elim (nonempty rfl)
  | item :: rest, _ => by
      cases rest with
      | nil =>
          exact ⟨[], item, by simp⟩
      | cons next tail =>
          obtain ⟨front, last, shape⟩ :=
            exists_append_singleton_of_ne_nil
              (next :: tail) (by simp)
          exact ⟨item :: front, last, by simp [shape]⟩

/-- The pure anchor-debt list corresponding to
`renderMarkerSquaresWithAnchorDebt`. -/
private def markerSquareAnchorDebt
    (anchor : Nat) : List Nat → List Nat
  | [] => []
  | [_] => []
  | _ :: next :: rest =>
      anchor :: markerSquareAnchorDebt anchor (next :: rest)

/-- Move one displayed anchor debt across a nonempty contiguous marker-square
bank. The reverse final-square switch first exposes an anchor square; one
square move then carries the second anchor occurrence past the final square. -/
private theorem listDerivesMoveAnchorDebtAcrossSquareBank
    (anchor first : Nat)
    (labels : List Nat) (suffix : List Nat)
    (labelsNonempty : labels ≠ []) :
    ListDerives
      ([anchor, first, first, anchor] ++
        SemigroupBasis.CoRoots.S5_107.renderMultipleSquares labels ++
        suffix)
      ([anchor, first, first] ++
        SemigroupBasis.CoRoots.S5_107.renderMultipleSquares labels ++
        [anchor] ++ suffix) := by
  obtain ⟨front, last, labelsShape⟩ :=
    exists_append_singleton_of_ne_nil labels labelsNonempty
  subst labels
  have exposeAnchor :=
    (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord <|
      SemigroupBasis.CoRoots.Order6FactorPairS2S5107Prelude.derivesSquareFinalSwitch
        (Word.singleton anchor)
        (Word.singleton first)).symm.append
          (SemigroupBasis.CoRoots.S5_107.renderMultipleSquares
            (front ++ [last]) ++ suffix)
  have exposeStep :
      ListDerives
        ([anchor, first, first, anchor] ++
          SemigroupBasis.CoRoots.S5_107.renderMultipleSquares
            (front ++ [last]) ++ suffix)
        ([anchor, anchor, first, first] ++
          SemigroupBasis.CoRoots.S5_107.renderMultipleSquares
            (front ++ [last]) ++ suffix) := by
    simpa [Word.singleton, Word.append,
      SemigroupBasis.CoRoots.S5_107.renderMultipleSquares,
      List.append_assoc] using exposeAnchor
  let middle :=
    SemigroupBasis.CoRoots.S5_107.listWordOfCons first
      (first ::
        SemigroupBasis.CoRoots.S5_107.renderMultipleSquares front)
  have moved :=
    (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord <|
      derivesSquareMove
        (Word.singleton anchor) middle (Word.singleton last)).append suffix
  have movedStep :
      ListDerives
        ([anchor, anchor, first, first] ++
          SemigroupBasis.CoRoots.S5_107.renderMultipleSquares
            (front ++ [last]) ++ suffix)
        ([anchor, first, first] ++
          SemigroupBasis.CoRoots.S5_107.renderMultipleSquares
            (front ++ [last]) ++ [anchor] ++ suffix) := by
    simpa [middle,
      SemigroupBasis.CoRoots.S5_107.listWordOfCons,
      SemigroupBasis.CoRoots.S5_107.renderMultipleSquares,
      Word.singleton, Word.append, List.append_assoc] using moved
  exact exposeStep.trans movedStep

/-- Flatten interleaved marker squares and anchor debts behind a retained
boundary anchor. Optional trailing marker squares are absorbed into the same
contiguous bank. -/
private theorem listDerivesFlattenMarkerSquareDebt
    (anchor : Nat) :
    ∀ (labels trailing suffix : List Nat),
      ListDerives
        ([anchor] ++
          renderMarkerSquaresWithAnchorDebt anchor labels ++
          SemigroupBasis.CoRoots.S5_107.renderMultipleSquares trailing ++
          suffix)
        ([anchor] ++
          SemigroupBasis.CoRoots.S5_107.renderMultipleSquares
            (labels ++ trailing) ++
          markerSquareAnchorDebt anchor labels ++ suffix)
  | [], trailing, suffix => by
      simpa [renderMarkerSquaresWithAnchorDebt,
        markerSquareAnchorDebt] using
          (SemigroupBasis.CoRoots.S5_107.ListDerives.refl
            (basis := candidateBasis)
            ([anchor] ++
              SemigroupBasis.CoRoots.S5_107.renderMultipleSquares trailing ++
              suffix))
  | [marker], trailing, suffix => by
      simpa [renderMarkerSquaresWithAnchorDebt,
        markerSquareAnchorDebt,
        SemigroupBasis.CoRoots.S5_107.renderMultipleSquares,
        List.append_assoc] using
          (SemigroupBasis.CoRoots.S5_107.ListDerives.refl
            (basis := candidateBasis)
            ([anchor, marker, marker] ++
              SemigroupBasis.CoRoots.S5_107.renderMultipleSquares trailing ++
              suffix))
  | marker :: next :: rest, trailing, suffix => by
      let tailLabels := next :: rest
      let tailDebt := markerSquareAnchorDebt anchor tailLabels
      have tailStep :=
        listDerivesFlattenMarkerSquareDebt
          anchor tailLabels trailing suffix
      have tailStep' :=
        tailStep.prepend [anchor, marker, marker]
      have tailFlattened :
          ListDerives
            ([anchor, marker, marker, anchor] ++
              renderMarkerSquaresWithAnchorDebt
                anchor tailLabels ++
              SemigroupBasis.CoRoots.S5_107.renderMultipleSquares
                trailing ++ suffix)
            ([anchor, marker, marker, anchor] ++
              SemigroupBasis.CoRoots.S5_107.renderMultipleSquares
                (tailLabels ++ trailing) ++
              tailDebt ++ suffix) := by
        simpa [tailLabels, tailDebt,
          List.append_assoc] using tailStep'
      have moved :=
        listDerivesMoveAnchorDebtAcrossSquareBank
          anchor marker (tailLabels ++ trailing)
          (tailDebt ++ suffix) (by simp [tailLabels])
      have movedStep :
          ListDerives
            ([anchor, marker, marker, anchor] ++
              SemigroupBasis.CoRoots.S5_107.renderMultipleSquares
                (tailLabels ++ trailing) ++
              tailDebt ++ suffix)
            ([anchor, marker, marker] ++
              SemigroupBasis.CoRoots.S5_107.renderMultipleSquares
                (tailLabels ++ trailing) ++
              [anchor] ++ tailDebt ++ suffix) := by
        simpa [List.append_assoc] using moved
      have combined := tailFlattened.trans movedStep
      simpa [tailLabels, tailDebt,
        renderMarkerSquaresWithAnchorDebt,
        markerSquareAnchorDebt,
        SemigroupBasis.CoRoots.S5_107.renderMultipleSquares,
        List.append_assoc] using combined

/-- Move a third marker copy across a nonempty sequence of square-ended
scanner factors in one square move, using the square of the final factor. -/
private theorem listDerivesMoveThirdAcrossSquaredFactors
    (marker : Nat)
    (factors : List (List Nat × Nat))
    (suffix : List Nat) :
    ListDerives
      ([marker, marker, marker] ++
        SemigroupBasis.CoRoots.S5_107.renderSquaredTerminatedBlocks factors ++
          suffix)
      ([marker, marker] ++
        SemigroupBasis.CoRoots.S5_107.renderSquaredTerminatedBlocks factors ++
          [marker] ++ suffix) := by
  by_cases empty : factors = []
  · subst factors
    simpa [SemigroupBasis.CoRoots.S5_107.renderSquaredTerminatedBlocks,
      List.append_assoc] using
        (SemigroupBasis.CoRoots.S5_107.ListDerives.refl
          (basis := candidateBasis)
          ([marker, marker, marker] ++ suffix))
  · obtain ⟨front, last, shape⟩ :=
      exists_append_singleton_of_ne_nil factors empty
    rcases last with ⟨block, lastMarker⟩
    subst factors
    have moved :=
      listDerivesMoveThirdAcrossLastSquare
        marker lastMarker
        (SemigroupBasis.CoRoots.S5_107.renderSquaredTerminatedBlocks front ++
          block)
        suffix
    simpa [SemigroupBasis.CoRoots.S5_107.renderSquaredTerminatedBlocks_append,
      SemigroupBasis.CoRoots.S5_107.renderSquaredTerminatedBlocks,
      List.append_assoc] using moved

/-- Separate a tripled scanner rendering into the ordinary square rendering
and an explicit parity-debt tail containing one copy of every scanner marker
occurrence. -/
private theorem listDerivesSeparateTripledMarkers :
    ∀ (factors : List (List Nat × Nat)) (final : List Nat),
      ListDerives
        (renderTripledTerminatedBlocks factors ++ final)
        (SemigroupBasis.CoRoots.S5_107.renderSquaredTerminatedBlocks factors ++
          SemigroupBasis.CoRoots.S5_107.terminatedFactorMarkers factors ++
          final)
  | [], final => by
      simpa [renderTripledTerminatedBlocks,
        SemigroupBasis.CoRoots.S5_107.renderSquaredTerminatedBlocks,
        SemigroupBasis.CoRoots.S5_107.terminatedFactorMarkers] using
          (SemigroupBasis.CoRoots.S5_107.ListDerives.refl
            (basis := candidateBasis) final)
  | (block, marker) :: rest, final => by
      have restStep :=
        (listDerivesSeparateTripledMarkers rest final).prepend
          (block ++ [marker, marker, marker])
      have restStep' :
          ListDerives
            (block ++ [marker, marker, marker] ++
              renderTripledTerminatedBlocks rest ++ final)
            (block ++ [marker, marker, marker] ++
              SemigroupBasis.CoRoots.S5_107.renderSquaredTerminatedBlocks
                rest ++
              SemigroupBasis.CoRoots.S5_107.terminatedFactorMarkers rest ++
              final) := by
        simpa [List.append_assoc] using restStep
      have moved :=
        (listDerivesMoveThirdAcrossSquaredFactors
          marker rest
          (SemigroupBasis.CoRoots.S5_107.terminatedFactorMarkers rest ++
            final)).prepend block
      have moved' :
          ListDerives
            (block ++ [marker, marker, marker] ++
              SemigroupBasis.CoRoots.S5_107.renderSquaredTerminatedBlocks
                rest ++
              SemigroupBasis.CoRoots.S5_107.terminatedFactorMarkers rest ++
              final)
            (block ++ [marker, marker] ++
              SemigroupBasis.CoRoots.S5_107.renderSquaredTerminatedBlocks
                rest ++
              [marker] ++
              SemigroupBasis.CoRoots.S5_107.terminatedFactorMarkers rest ++
              final) := by
        simpa [List.append_assoc] using moved
      exact restStep'.trans <| by
        simpa [renderTripledTerminatedBlocks,
          SemigroupBasis.CoRoots.S5_107.renderSquaredTerminatedBlocks,
          SemigroupBasis.CoRoots.S5_107.terminatedFactorMarkers,
          List.append_assoc] using moved'

/-- Source-level parity preparation for the S5_107 scanner. The square
rendering is exactly the input expected by the sealed extraction phase; the
additional marker tail records the full mod-two debt that phase must retain. -/
theorem listDerivesParityPreparedTerminatedForm
    (letters : List Nat) :
    ListDerives letters
      (SemigroupBasis.CoRoots.S5_107.renderSquaredTerminatedBlocks
          (SemigroupBasis.CoRoots.S5_107.terminatedBlocks letters) ++
        SemigroupBasis.CoRoots.S5_107.terminatedFactorMarkers
          (SemigroupBasis.CoRoots.S5_107.terminatedBlocks letters) ++
        SemigroupBasis.CoRoots.S5_107.terminatedFinalBlock letters) := by
  exact
    (listDerivesTripleAllTerminatedMarkers letters).trans <| by
      simpa [List.append_assoc] using
        listDerivesSeparateTripledMarkers
          (SemigroupBasis.CoRoots.S5_107.terminatedBlocks letters)
          (SemigroupBasis.CoRoots.S5_107.terminatedFinalBlock letters)

/-- The deterministic endpoint produced by
`listDerivesParityPreparedTerminatedForm`. Keeping this endpoint named makes
the remaining parity argument a statement about two concrete scanner
renderings rather than about arbitrary equational derivation trees. -/
def parityPreparedTerminatedList (letters : List Nat) : List Nat :=
  SemigroupBasis.CoRoots.S5_107.renderSquaredTerminatedBlocks
      (SemigroupBasis.CoRoots.S5_107.terminatedBlocks letters) ++
    SemigroupBasis.CoRoots.S5_107.terminatedFactorMarkers
      (SemigroupBasis.CoRoots.S5_107.terminatedBlocks letters) ++
    SemigroupBasis.CoRoots.S5_107.terminatedFinalBlock letters

theorem listDerivesParityPreparedTerminatedList
    (letters : List Nat) :
    ListDerives letters (parityPreparedTerminatedList letters) := by
  simpa [parityPreparedTerminatedList] using
    listDerivesParityPreparedTerminatedForm letters

/-- Exact residual after both balanced-tail transports: parity-cancelling
uses of the first three sealed laws must be replaced by candidate derivations
in arbitrary contexts and after arbitrary substitutions. -/
def ParityKernelLift : Prop :=
  ∀ {left right : Word Nat},
    Derives s5Basis left right →
      SameOccurrenceParity left right →
        Derives candidateBasis left right

private theorem sameSimpleAdjacencySignatureOfS5Derivation
    {left right : Word Nat}
    (derivation : Derives s5Basis left right) :
    SemigroupBasis.CoRoots.S5_107.SameSimpleAdjacencySignature left right := by
  apply
    SemigroupBasis.CoRoots.S5_107.valid_sameSimpleAdjacencySignature
      (Identity.mk left right)
  intro valuation
  exact derivation.sound
    SemigroupBasis.CoRoots.S5_107Family.S5_107.basisFor.1 valuation

/-- The marker occurrences separated from the squared scanner rendering.
These are precisely the occurrences whose parity must survive the
`S5_107` canonical extraction. -/
def parityPreparedMarkerDebt (letters : List Nat) : List Nat :=
  SemigroupBasis.CoRoots.S5_107.terminatedFactorMarkers
    (SemigroupBasis.CoRoots.S5_107.terminatedBlocks letters)

/-- One debt occurrence for every structural anchor displayed by the
canonical scanner: the leading anchor and one terminator for each interior
simple block. These occurrences must be included in the parity ledger before
the debt is reduced. -/
private def parityPreparedStructuralAnchorDebt
    (letters : List Nat) (anchor : Nat) : List Nat :=
  List.replicate
    (Nat.succ
      (SemigroupBasis.CoRoots.S5_107.interiorSimpleBlocks letters).length)
    anchor

private theorem listDerivesExpandSquareToFourthBalanced
    (letter : Nat) :
    ListDerives
      [letter, letter]
      [letter, letter, letter, letter] := by
  simpa [Word.toList, Word.singleton, Word.append,
    List.append_assoc] using
      (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord <|
        (SemigroupBasis.CoRoots.Order6FactorPairS2S5107Prelude.derivesFourToTwo
          (Word.singleton letter)).symm)

private theorem listDerivesExpandSquareToSixBalanced
    (letter : Nat) :
    ListDerives
      [letter, letter]
      [letter, letter, letter, letter, letter, letter] := by
  have fourth :=
    listDerivesExpandSquareToFourthBalanced letter
  have sixthRaw := fourth.prepend [letter, letter]
  have sixth :
      ListDerives
        [letter, letter, letter, letter]
        [letter, letter, letter, letter, letter, letter] := by
    simpa [List.append_assoc] using sixthRaw
  exact fourth.trans sixth

/-- Parity-safe empty-factor seed. Compared with the sealed `S5_107` seed,
the displaced anchor occurrence is retained after the marker-square bank. -/
private theorem listDerivesLeadingSquareAnchorFourthWithDebt
    (leading anchor : Nat) :
    ListDerives
      ([leading, leading] ++
        [anchor, anchor, anchor, anchor])
      ([anchor] ++
        SemigroupBasis.CoRoots.S5_107.renderMultipleSquares
          [anchor, leading] ++
        [anchor]) := by
  have firstRaw :=
    (listDerivesSquareBlockCommutation leading anchor).append
      [anchor, anchor]
  have first :
      ListDerives
        ([leading, leading] ++
          [anchor, anchor, anchor, anchor])
        ([anchor, anchor, leading, leading] ++
          [anchor, anchor]) := by
    simpa [SemigroupBasis.CoRoots.S5_107.renderMultipleSquares,
      List.append_assoc] using firstRaw
  have secondRaw :=
    (listDerivesSquareBlockCommutation leading anchor).prepend
      [anchor, anchor]
  have second :
      ListDerives
        ([anchor, anchor, leading, leading] ++
          [anchor, anchor])
        ([anchor, anchor, anchor, anchor] ++
          [leading, leading]) := by
    simpa [SemigroupBasis.CoRoots.S5_107.renderMultipleSquares,
      List.append_assoc] using secondRaw
  have finalRaw :=
    (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord <|
      SemigroupBasis.CoRoots.Order6FactorPairS2S5107Prelude.derivesSquareFinalSwitch
        (Word.singleton anchor)
        (Word.singleton leading)).prepend [anchor, anchor]
  have final :
      ListDerives
        ([anchor, anchor, anchor, anchor] ++
          [leading, leading])
        ([anchor] ++
          SemigroupBasis.CoRoots.S5_107.renderMultipleSquares
            [anchor, leading] ++
          [anchor]) := by
    simpa [SemigroupBasis.CoRoots.S5_107.renderMultipleSquares,
      Word.toList, Word.singleton, Word.append,
      List.append_assoc] using finalRaw
  exact first.trans (second.trans final)

private theorem markerSquareAnchorDebt_eq_replicate
    (anchor : Nat) :
    ∀ labels,
      markerSquareAnchorDebt anchor labels =
        List.replicate (labels.length - 1) anchor
  | [] => by
      simp [markerSquareAnchorDebt]
  | [_] => by
      simp [markerSquareAnchorDebt]
  | first :: second :: rest => by
      rw [markerSquareAnchorDebt,
        markerSquareAnchorDebt_eq_replicate anchor (second :: rest)]
      simp [List.replicate_succ]

private theorem replicate_append_two
    (anchor : Nat) :
    ∀ count,
      List.replicate count anchor ++ [anchor, anchor] =
        List.replicate (Nat.succ (Nat.succ count)) anchor
  | 0 => by
      rfl
  | Nat.succ count => by
      simp [List.replicate_succ, replicate_append_two anchor count]

private theorem listDerivesMoveAnchorDebtAcrossMaybeEmptySquareBank
    (anchor first : Nat) :
    ∀ (labels suffix : List Nat),
      ListDerives
        ([anchor, first, first, anchor] ++
          SemigroupBasis.CoRoots.S5_107.renderMultipleSquares labels ++
          suffix)
        ([anchor, first, first] ++
          SemigroupBasis.CoRoots.S5_107.renderMultipleSquares labels ++
          [anchor] ++ suffix)
  | [], suffix => by
      simpa [SemigroupBasis.CoRoots.S5_107.renderMultipleSquares,
        List.append_assoc] using
          (SemigroupBasis.CoRoots.S5_107.ListDerives.refl
            (basis := candidateBasis)
            ([anchor, first, first, anchor] ++ suffix))
  | label :: labels, suffix => by
      simpa [List.append_assoc] using
        listDerivesMoveAnchorDebtAcrossSquareBank
          anchor first (label :: labels) suffix (by simp)

/-- Normalize a chain of nonempty square-ended factors when a following
empty factor supplies the selected anchor. Every recursive installation
retains one structural anchor after the complete marker-square bank. -/
private theorem listDerivesAnchorFactorChainFromEmptySeedWithDebt
    (leadingBlock : List Nat) (leadingMarker anchor : Nat)
    (factors : List (List Nat × Nat))
    (trailing suffix : List Nat)
    (blocksNonempty :
      ∀ factor ∈ factors, factor.1 ≠ []) :
    ListDerives
      (leadingBlock ++ [leadingMarker, leadingMarker] ++
        SemigroupBasis.CoRoots.S5_107.renderSquaredTerminatedBlocks factors ++
        [anchor, anchor, anchor, anchor] ++
        SemigroupBasis.CoRoots.S5_107.renderMultipleSquares trailing ++
        suffix)
      (leadingBlock ++ [anchor] ++
        SemigroupBasis.CoRoots.S5_107.renderAnchoredBlocks anchor
          (SemigroupBasis.CoRoots.S5_107.terminatedFactorBlocks factors) ++
        SemigroupBasis.CoRoots.S5_107.renderMultipleSquares
          (anchor :: leadingMarker ::
            SemigroupBasis.CoRoots.S5_107.terminatedFactorMarkers factors ++
              trailing) ++
        List.replicate (Nat.succ factors.length) anchor ++
        suffix) := by
  induction factors generalizing leadingBlock leadingMarker with
  | nil =>
      have seeded :=
        (listDerivesLeadingSquareAnchorFourthWithDebt
          leadingMarker anchor).context
            leadingBlock
            (SemigroupBasis.CoRoots.S5_107.renderMultipleSquares trailing ++
              suffix)
      have seededStep :
          ListDerives
            (leadingBlock ++ [leadingMarker, leadingMarker] ++
              [anchor, anchor, anchor, anchor] ++
              SemigroupBasis.CoRoots.S5_107.renderMultipleSquares trailing ++
              suffix)
            (leadingBlock ++ [anchor] ++
              SemigroupBasis.CoRoots.S5_107.renderMultipleSquares
                [anchor, leadingMarker] ++
              [anchor] ++
              SemigroupBasis.CoRoots.S5_107.renderMultipleSquares trailing ++
              suffix) := by
        simpa [List.append_assoc] using seeded
      have moved :=
        (listDerivesMoveAnchorDebtAcrossMaybeEmptySquareBank
          anchor leadingMarker trailing suffix).prepend
            (leadingBlock ++ [anchor, anchor])
      have movedStep :
          ListDerives
            (leadingBlock ++ [anchor] ++
              SemigroupBasis.CoRoots.S5_107.renderMultipleSquares
                [anchor, leadingMarker] ++
              [anchor] ++
              SemigroupBasis.CoRoots.S5_107.renderMultipleSquares trailing ++
              suffix)
            (leadingBlock ++ [anchor] ++
              SemigroupBasis.CoRoots.S5_107.renderMultipleSquares
                (anchor :: leadingMarker :: trailing) ++
              [anchor] ++ suffix) := by
        simpa [SemigroupBasis.CoRoots.S5_107.renderMultipleSquares,
          List.append_assoc] using moved
      simpa [
        SemigroupBasis.CoRoots.S5_107.terminatedFactorBlocks,
        SemigroupBasis.CoRoots.S5_107.terminatedFactorMarkers,
        SemigroupBasis.CoRoots.S5_107.renderSquaredTerminatedBlocks,
        SemigroupBasis.CoRoots.S5_107.renderAnchoredBlocks,
        List.append_assoc] using seededStep.trans movedStep
  | cons factor rest inductionHypothesis =>
      rcases factor with ⟨block, marker⟩
      have blockNonempty : block ≠ [] :=
        blocksNonempty (block, marker) (by simp)
      obtain ⟨blockHead, blockTail, rfl⟩ :=
        List.exists_cons_of_ne_nil blockNonempty
      have restBlocksNonempty :
          ∀ candidate ∈ rest, candidate.1 ≠ [] := by
        intro candidate member
        exact
          blocksNonempty candidate
            (List.mem_cons_of_mem
              (blockHead :: blockTail, marker) member)
      have tailStep :=
        inductionHypothesis
          (blockHead :: blockTail) marker restBlocksNonempty
      have tailStep' :=
        tailStep.prepend
          (leadingBlock ++ [leadingMarker, leadingMarker])
      let anchoredCore : List Nat :=
        (blockHead :: blockTail) ++ [anchor] ++
          SemigroupBasis.CoRoots.S5_107.renderAnchoredBlocks anchor
            (SemigroupBasis.CoRoots.S5_107.terminatedFactorBlocks rest)
      let remainingLabels : List Nat :=
        marker ::
          SemigroupBasis.CoRoots.S5_107.terminatedFactorMarkers rest ++
            trailing
      let tailDebt : List Nat :=
        List.replicate (Nat.succ rest.length) anchor
      have tailNormalized :
          ListDerives
            (leadingBlock ++ [leadingMarker, leadingMarker] ++
              (blockHead :: blockTail) ++ [marker, marker] ++
              SemigroupBasis.CoRoots.S5_107.renderSquaredTerminatedBlocks rest ++
              [anchor, anchor, anchor, anchor] ++
              SemigroupBasis.CoRoots.S5_107.renderMultipleSquares trailing ++
              suffix)
            (leadingBlock ++ [leadingMarker, leadingMarker] ++
              anchoredCore ++
              SemigroupBasis.CoRoots.S5_107.renderMultipleSquares
                (anchor :: remainingLabels) ++
              tailDebt ++ suffix) := by
        simpa [anchoredCore, remainingLabels, tailDebt,
          SemigroupBasis.CoRoots.S5_107.terminatedFactorBlocks,
          SemigroupBasis.CoRoots.S5_107.terminatedFactorMarkers,
          SemigroupBasis.CoRoots.S5_107.renderAnchoredBlocks,
          List.append_assoc] using tailStep'
      have middleNonempty :
          anchoredCore ++ [anchor] ≠ [] := by
        simp
      obtain ⟨middleHead, middleTail, middleShape⟩ :=
        List.exists_cons_of_ne_nil middleNonempty
      let debtSuffix : List Nat :=
        SemigroupBasis.CoRoots.S5_107.renderMultipleSquares remainingLabels ++
          tailDebt ++ suffix
      have anchorInMiddle :
          anchor ∈ middleHead :: middleTail := by
        rw [← middleShape]
        simp
      have prependStep :=
        (listDerivesPrependToAnchoredMiddleWithDebt
          leadingMarker anchor middleHead middleTail
          debtSuffix anchorInMiddle).prepend leadingBlock
      have prepended :
          ListDerives
            (leadingBlock ++ [leadingMarker, leadingMarker] ++
              anchoredCore ++
              SemigroupBasis.CoRoots.S5_107.renderMultipleSquares
                (anchor :: remainingLabels) ++
              tailDebt ++ suffix)
            (leadingBlock ++ [anchor] ++
              anchoredCore ++ [anchor, anchor,
                leadingMarker, leadingMarker, anchor] ++
              debtSuffix) := by
        simpa only [← middleShape,
          SemigroupBasis.CoRoots.S5_107.renderMultipleSquares,
          debtSuffix, List.append_assoc] using prependStep
      have moved :=
        (listDerivesMoveAnchorDebtAcrossMaybeEmptySquareBank
          anchor leadingMarker remainingLabels
          (tailDebt ++ suffix)).prepend
            (leadingBlock ++ [anchor] ++ anchoredCore ++ [anchor])
      have movedStep :
          ListDerives
            (leadingBlock ++ [anchor] ++
              anchoredCore ++ [anchor, anchor,
                leadingMarker, leadingMarker, anchor] ++
              debtSuffix)
            (leadingBlock ++ [anchor] ++
              anchoredCore ++
              SemigroupBasis.CoRoots.S5_107.renderMultipleSquares
                (anchor :: leadingMarker :: remainingLabels) ++
              [anchor] ++ tailDebt ++ suffix) := by
        simpa [debtSuffix,
          SemigroupBasis.CoRoots.S5_107.renderMultipleSquares,
          List.append_assoc] using moved
      have combined :=
        tailNormalized.trans <| prepended.trans movedStep
      simpa [anchoredCore, remainingLabels, tailDebt,
        SemigroupBasis.CoRoots.S5_107.terminatedFactorBlocks,
        SemigroupBasis.CoRoots.S5_107.terminatedFactorMarkers,
        SemigroupBasis.CoRoots.S5_107.renderSquaredTerminatedBlocks,
        SemigroupBasis.CoRoots.S5_107.renderAnchoredBlocks,
        List.replicate_succ, List.append_assoc] using combined

/-- Expand the selected empty anchor square and invoke the structural-debt
seed while preserving every trailing marker-only square. -/
private theorem listDerivesAnchorFactorChainFromEmptyFactorWithDebt
    (leadingBlock : List Nat) (leadingMarker anchor : Nat)
    (factors : List (List Nat × Nat))
    (trailing suffix : List Nat)
    (blocksNonempty :
      ∀ factor ∈ factors, factor.1 ≠ []) :
    ListDerives
      (leadingBlock ++ [leadingMarker, leadingMarker] ++
        SemigroupBasis.CoRoots.S5_107.renderSquaredTerminatedBlocks factors ++
        [anchor, anchor] ++
        SemigroupBasis.CoRoots.S5_107.renderMultipleSquares trailing ++
        suffix)
      (leadingBlock ++ [anchor] ++
        SemigroupBasis.CoRoots.S5_107.renderAnchoredBlocks anchor
          (SemigroupBasis.CoRoots.S5_107.terminatedFactorBlocks factors) ++
        SemigroupBasis.CoRoots.S5_107.renderMultipleSquares
          (anchor :: leadingMarker ::
            SemigroupBasis.CoRoots.S5_107.terminatedFactorMarkers factors ++
              trailing) ++
        List.replicate (Nat.succ factors.length) anchor ++
        suffix) := by
  let beforeAnchor : List Nat :=
    leadingBlock ++ [leadingMarker, leadingMarker] ++
      SemigroupBasis.CoRoots.S5_107.renderSquaredTerminatedBlocks factors
  have expanded :=
    (listDerivesExpandSquareToFourthBalanced anchor).context
      beforeAnchor
      (SemigroupBasis.CoRoots.S5_107.renderMultipleSquares trailing ++
        suffix)
  have expandedStep :
      ListDerives
        (leadingBlock ++ [leadingMarker, leadingMarker] ++
          SemigroupBasis.CoRoots.S5_107.renderSquaredTerminatedBlocks factors ++
          [anchor, anchor] ++
          SemigroupBasis.CoRoots.S5_107.renderMultipleSquares trailing ++
          suffix)
        (leadingBlock ++ [leadingMarker, leadingMarker] ++
          SemigroupBasis.CoRoots.S5_107.renderSquaredTerminatedBlocks factors ++
          [anchor, anchor, anchor, anchor] ++
          SemigroupBasis.CoRoots.S5_107.renderMultipleSquares trailing ++
          suffix) := by
    simpa [beforeAnchor, List.append_assoc] using expanded
  exact expandedStep.trans <|
    listDerivesAnchorFactorChainFromEmptySeedWithDebt
      leadingBlock leadingMarker anchor factors trailing suffix
      blocksNonempty

/-- Select a nonempty anchor factor. Six copies of its terminal anchor supply
the selected square, one retained square in the bank, and the final two
structural-debt occurrences. -/
private theorem
    listDerivesAnchorNonemptyFactorChainRetainingSquareWithStructuralDebt
    (leadingBlock : List Nat) (leadingMarker anchor : Nat)
    (front : List (List Nat × Nat))
    (lastHead : Nat) (lastTail trailing suffix : List Nat)
    (frontBlocksNonempty :
      ∀ factor ∈ front, factor.1 ≠ []) :
    ListDerives
      (leadingBlock ++ [leadingMarker, leadingMarker] ++
        SemigroupBasis.CoRoots.S5_107.renderSquaredTerminatedBlocks
          (front ++ [((lastHead :: lastTail), anchor)]) ++
        SemigroupBasis.CoRoots.S5_107.renderMultipleSquares trailing ++
        suffix)
      (leadingBlock ++ [anchor] ++
        SemigroupBasis.CoRoots.S5_107.renderAnchoredBlocks anchor
          (SemigroupBasis.CoRoots.S5_107.terminatedFactorBlocks front ++
            [lastHead :: lastTail]) ++
        SemigroupBasis.CoRoots.S5_107.renderMultipleSquares
          (leadingMarker ::
            SemigroupBasis.CoRoots.S5_107.terminatedFactorMarkers front ++
              anchor :: trailing) ++
        List.replicate
          (Nat.succ (Nat.succ front.length)) anchor ++
        suffix) := by
  let beforeAnchor : List Nat :=
    leadingBlock ++ [leadingMarker, leadingMarker] ++
      SemigroupBasis.CoRoots.S5_107.renderSquaredTerminatedBlocks front ++
      (lastHead :: lastTail)
  have expanded :=
    (listDerivesExpandSquareToSixBalanced anchor).context
      beforeAnchor
      (SemigroupBasis.CoRoots.S5_107.renderMultipleSquares trailing ++
        suffix)
  have expandedStep :
      ListDerives
        (leadingBlock ++ [leadingMarker, leadingMarker] ++
          SemigroupBasis.CoRoots.S5_107.renderSquaredTerminatedBlocks
            (front ++ [((lastHead :: lastTail), anchor)]) ++
          SemigroupBasis.CoRoots.S5_107.renderMultipleSquares trailing ++
          suffix)
        (beforeAnchor ++
          [anchor, anchor, anchor, anchor, anchor, anchor] ++
          SemigroupBasis.CoRoots.S5_107.renderMultipleSquares trailing ++
          suffix) := by
    simpa [beforeAnchor,
      SemigroupBasis.CoRoots.S5_107.renderSquaredTerminatedBlocks,
      List.append_assoc] using expanded
  have rotateAnchorSquare :
      (anchor :: anchor :: trailing).Perm
        (anchor :: trailing ++ [anchor]) := by
    exact
      List.Perm.cons anchor <| by
        simpa using
          (List.perm_append_comm :
            ([anchor] ++ trailing).Perm
              (trailing ++ [anchor]))
  have rearrangedRaw :=
    (listDerivesMultipleSquarePermutation rotateAnchorSquare).context
      (beforeAnchor ++ [anchor, anchor])
      suffix
  have rearranged :
      ListDerives
        (beforeAnchor ++
          [anchor, anchor, anchor, anchor, anchor, anchor] ++
          SemigroupBasis.CoRoots.S5_107.renderMultipleSquares trailing ++
          suffix)
        (beforeAnchor ++ [anchor, anchor] ++
          SemigroupBasis.CoRoots.S5_107.renderMultipleSquares
            (anchor :: trailing) ++
          [anchor, anchor] ++ suffix) := by
    simpa [SemigroupBasis.CoRoots.S5_107.renderMultipleSquares,
      List.append_assoc] using rearrangedRaw
  have extracted :=
    listDerivesAnchorNonemptyFactorChainWithDebt
      leadingBlock leadingMarker anchor front
      lastHead lastTail
      (SemigroupBasis.CoRoots.S5_107.renderMultipleSquares
          (anchor :: trailing) ++
        [anchor, anchor] ++ suffix)
      frontBlocksNonempty
  have extractedStep :
      ListDerives
        (beforeAnchor ++ [anchor, anchor] ++
          SemigroupBasis.CoRoots.S5_107.renderMultipleSquares
            (anchor :: trailing) ++
          [anchor, anchor] ++ suffix)
        (leadingBlock ++ [anchor] ++
          SemigroupBasis.CoRoots.S5_107.renderAnchoredBlocks anchor
            (SemigroupBasis.CoRoots.S5_107.terminatedFactorBlocks front ++
              [lastHead :: lastTail]) ++
          renderMarkerSquaresWithAnchorDebt anchor
            (leadingMarker ::
              SemigroupBasis.CoRoots.S5_107.terminatedFactorMarkers front) ++
          SemigroupBasis.CoRoots.S5_107.renderMultipleSquares
            (anchor :: trailing) ++
          [anchor, anchor] ++ suffix) := by
    simpa [beforeAnchor,
      SemigroupBasis.CoRoots.S5_107.renderSquaredTerminatedBlocks,
      List.append_assoc] using extracted
  let labels : List Nat :=
    leadingMarker ::
      SemigroupBasis.CoRoots.S5_107.terminatedFactorMarkers front
  let anchoredPrefix : List Nat :=
    leadingBlock ++ [anchor] ++
      SemigroupBasis.CoRoots.S5_107.renderAnchoredBlocks anchor
        (SemigroupBasis.CoRoots.S5_107.terminatedFactorBlocks front) ++
      (lastHead :: lastTail)
  have flattenedRaw :=
    (listDerivesFlattenMarkerSquareDebt
      anchor labels (anchor :: trailing)
      ([anchor, anchor] ++ suffix)).prepend anchoredPrefix
  have flattened :
      ListDerives
        (leadingBlock ++ [anchor] ++
          SemigroupBasis.CoRoots.S5_107.renderAnchoredBlocks anchor
            (SemigroupBasis.CoRoots.S5_107.terminatedFactorBlocks front ++
              [lastHead :: lastTail]) ++
          renderMarkerSquaresWithAnchorDebt anchor labels ++
          SemigroupBasis.CoRoots.S5_107.renderMultipleSquares
            (anchor :: trailing) ++
          [anchor, anchor] ++ suffix)
        (leadingBlock ++ [anchor] ++
          SemigroupBasis.CoRoots.S5_107.renderAnchoredBlocks anchor
            (SemigroupBasis.CoRoots.S5_107.terminatedFactorBlocks front ++
              [lastHead :: lastTail]) ++
          SemigroupBasis.CoRoots.S5_107.renderMultipleSquares
            (labels ++ anchor :: trailing) ++
          markerSquareAnchorDebt anchor labels ++
          [anchor, anchor] ++ suffix) := by
    simpa [anchoredPrefix,
      SemigroupBasis.CoRoots.S5_107.renderAnchoredBlocks,
      List.append_assoc] using flattenedRaw
  have debtShape :
      markerSquareAnchorDebt anchor labels ++ [anchor, anchor] =
        List.replicate
          (Nat.succ (Nat.succ front.length)) anchor := by
    rw [markerSquareAnchorDebt_eq_replicate]
    simp [labels, replicate_append_two,
      SemigroupBasis.CoRoots.S5_107.terminatedFactorMarkers]
  have debtShapeWithSuffix :=
    congrArg (fun debt : List Nat => debt ++ suffix) debtShape
  have combined :=
    expandedStep.trans <| rearranged.trans <|
      extractedStep.trans flattened
  simpa [labels, debtShapeWithSuffix, List.append_assoc] using combined

/-- Every permutation of nonempty anchored blocks is available in the
balanced candidate calculus. -/
private theorem listDerivesAnchoredBlockPermutationBalanced
    (anchor : Nat) {source target : List (List Nat)}
    (permutation : source.Perm target) :
    ∀ suffix : List Nat,
      (∀ block ∈ source, block ≠ []) →
      ListDerives
        ([anchor] ++
          SemigroupBasis.CoRoots.S5_107.renderAnchoredBlocks
            anchor source ++ suffix)
        ([anchor] ++
          SemigroupBasis.CoRoots.S5_107.renderAnchoredBlocks
            anchor target ++ suffix) := by
  induction permutation with
  | nil =>
      intro suffix _
      simpa [SemigroupBasis.CoRoots.S5_107.renderAnchoredBlocks] using
        (SemigroupBasis.CoRoots.S5_107.ListDerives.refl
          (basis := candidateBasis) ([anchor] ++ suffix))
  | @cons block source target permutation inductionHypothesis =>
      intro suffix nonempty
      have tailNonempty :
          ∀ candidate ∈ source, candidate ≠ [] := by
        intro candidate member
        exact nonempty candidate
          (List.mem_cons_of_mem block member)
      have tailStep :=
        inductionHypothesis suffix tailNonempty
      simpa [SemigroupBasis.CoRoots.S5_107.renderAnchoredBlocks,
        List.append_assoc] using
          tailStep.prepend ([anchor] ++ block)
  | swap left right rest =>
      intro suffix nonempty
      have leftNonempty : left ≠ [] :=
        nonempty left (by simp)
      have rightNonempty : right ≠ [] :=
        nonempty right (by simp)
      have swapped :=
        listDerivesAnchoredBlockSwapLists
          anchor leftNonempty rightNonempty
      simpa [SemigroupBasis.CoRoots.S5_107.renderAnchoredBlocks,
        List.append_assoc] using
          (swapped.append
            (SemigroupBasis.CoRoots.S5_107.renderAnchoredBlocks
              anchor rest ++ suffix)).symm
  | @trans source middle target first second
      inductionFirst inductionSecond =>
      intro suffix nonempty
      have middleNonempty :
          ∀ block ∈ middle, block ≠ [] := by
        intro block member
        exact nonempty block (first.mem_iff.mpr member)
      exact
        (inductionFirst suffix nonempty).trans
          (inductionSecond suffix middleNonempty)

/-- Independently permute an extracted block list and marker-square bank
while preserving the structural and marker debt in the suffix. -/
private theorem listDerivesRenderedCanonicalCoreBalanced
    (initial final : List Nat) (anchor : Nat)
    {sourceBlocks targetBlocks : List (List Nat)}
    {sourceMultiples targetMultiples : List Nat}
    (blockPermutation : sourceBlocks.Perm targetBlocks)
    (multiplePermutation : sourceMultiples.Perm targetMultiples)
    (blocksNonempty : ∀ block ∈ sourceBlocks, block ≠ []) :
    ListDerives
      (initial ++ [anchor] ++
        SemigroupBasis.CoRoots.S5_107.renderAnchoredBlocks
          anchor sourceBlocks ++
        SemigroupBasis.CoRoots.S5_107.renderMultipleSquares
          sourceMultiples ++ final)
      (initial ++ [anchor] ++
        SemigroupBasis.CoRoots.S5_107.renderAnchoredBlocks
          anchor targetBlocks ++
        SemigroupBasis.CoRoots.S5_107.renderMultipleSquares
          targetMultiples ++ final) := by
  let middle : List Nat :=
    initial ++ [anchor] ++
      SemigroupBasis.CoRoots.S5_107.renderAnchoredBlocks
        anchor targetBlocks ++
      SemigroupBasis.CoRoots.S5_107.renderMultipleSquares
        sourceMultiples ++ final
  have blockStep :=
    (listDerivesAnchoredBlockPermutationBalanced
      anchor blockPermutation
      (SemigroupBasis.CoRoots.S5_107.renderMultipleSquares
          sourceMultiples ++ final)
      blocksNonempty).prepend initial
  have blockStep' :
      ListDerives
        (initial ++ [anchor] ++
          SemigroupBasis.CoRoots.S5_107.renderAnchoredBlocks
            anchor sourceBlocks ++
          SemigroupBasis.CoRoots.S5_107.renderMultipleSquares
            sourceMultiples ++ final)
        middle := by
    dsimp [middle]
    simpa [List.append_assoc] using blockStep
  have squareStep :=
    (listDerivesMultipleSquarePermutation
      multiplePermutation).context
        (initial ++ [anchor] ++
          SemigroupBasis.CoRoots.S5_107.renderAnchoredBlocks
            anchor targetBlocks)
        final
  have squareStep' :
      ListDerives middle
        (initial ++ [anchor] ++
          SemigroupBasis.CoRoots.S5_107.renderAnchoredBlocks
            anchor targetBlocks ++
          SemigroupBasis.CoRoots.S5_107.renderMultipleSquares
            targetMultiples ++ final) := by
    dsimp [middle]
    simpa [List.append_assoc] using squareStep
  exact blockStep'.trans squareStep'

/-- Extract any selected tail occurrence of the anchor while retaining one
structural-debt occurrence for the leading anchor and every nonempty tail
block. Marker-only trailing factors stay in the contiguous square bank. -/
private theorem listDerivesExtractTerminatedWithAnchorStructuralDebt
    (first : List Nat × Nat)
    (tail : List (List Nat × Nat))
    (selected : List Nat × Nat)
    (final : List Nat)
    (anchor : Nat)
    (selectedMember : selected ∈ tail)
    (selectedMarker : selected.2 = anchor) :
    ListDerives
      (SemigroupBasis.CoRoots.S5_107.renderSquaredTerminatedBlocks
          (first :: tail) ++ final)
      (first.1 ++ [anchor] ++
        SemigroupBasis.CoRoots.S5_107.renderAnchoredBlocks anchor
          (SemigroupBasis.CoRoots.S5_107.nonemptyTerminatedBlocks tail) ++
        SemigroupBasis.CoRoots.S5_107.renderMultipleSquares
          (SemigroupBasis.CoRoots.S5_107.terminatedFactorMarkers
            (first :: tail)) ++
        List.replicate
          (Nat.succ
            (SemigroupBasis.CoRoots.S5_107.nonemptyTerminatedBlocks
              tail).length)
          anchor ++
        final) := by
  rcases selected with ⟨selectedBlock, marker⟩
  simp only [Prod.snd] at selectedMarker
  subst marker
  let remainder :=
    tail.erase (selectedBlock, anchor)
  let nonempty :=
    SemigroupBasis.CoRoots.S5_107.blockBearingFactors remainder
  let empty :=
    SemigroupBasis.CoRoots.S5_107.markerOnlyFactors remainder
  let arranged :=
    nonempty ++ (selectedBlock, anchor) :: empty
  have tailPermutation :
      tail.Perm arranged := by
    simpa [remainder, nonempty, empty, arranged] using
      (SemigroupBasis.CoRoots.S5_107.perm_selected_factor_after_blockBearing
        selectedMember)
  have rearranged :=
    listDerivesSquaredTailPermutation
      tailPermutation first final
  have nonemptyBlocks :
      ∀ factor ∈ nonempty, factor.1 ≠ [] := by
    simpa [nonempty] using
      SemigroupBasis.CoRoots.S5_107.blockBearingFactors_blocks_nonempty
        remainder
  have emptyBlocks :
      ∀ factor ∈ empty, factor.1 = [] := by
    simpa [empty] using
      SemigroupBasis.CoRoots.S5_107.markerOnlyFactors_blocks_empty
        remainder
  have emptyRendering :
      SemigroupBasis.CoRoots.S5_107.renderSquaredTerminatedBlocks empty =
        SemigroupBasis.CoRoots.S5_107.renderMultipleSquares
          (SemigroupBasis.CoRoots.S5_107.terminatedFactorMarkers empty) :=
    SemigroupBasis.CoRoots.S5_107.renderSquaredTerminatedBlocks_eq_renderMultipleSquares_of_blocks_empty
      empty emptyBlocks
  have emptyNonemptyBlocks :
      SemigroupBasis.CoRoots.S5_107.nonemptyTerminatedBlocks empty = [] :=
    SemigroupBasis.CoRoots.S5_107.nonemptyTerminatedBlocks_eq_nil_of_blocks_empty
      empty emptyBlocks
  have nonemptyProjection :
      SemigroupBasis.CoRoots.S5_107.nonemptyTerminatedBlocks nonempty =
        SemigroupBasis.CoRoots.S5_107.terminatedFactorBlocks nonempty :=
    SemigroupBasis.CoRoots.S5_107.nonemptyTerminatedBlocks_eq_terminatedFactorBlocks_of_blocks_nonempty
      nonempty nonemptyBlocks
  by_cases selectedEmpty : selectedBlock = []
  · subst selectedBlock
    let sourceBlocks :=
      SemigroupBasis.CoRoots.S5_107.terminatedFactorBlocks nonempty
    let sourceMultiples :=
      anchor :: first.2 ::
        SemigroupBasis.CoRoots.S5_107.terminatedFactorMarkers nonempty ++
          SemigroupBasis.CoRoots.S5_107.terminatedFactorMarkers empty
    have extractedCore :=
      listDerivesAnchorFactorChainFromEmptyFactorWithDebt
        first.1 first.2 anchor nonempty
        (SemigroupBasis.CoRoots.S5_107.terminatedFactorMarkers empty)
        final nonemptyBlocks
    have extracted :
        ListDerives
          (SemigroupBasis.CoRoots.S5_107.renderSquaredTerminatedBlocks
              (first :: arranged) ++ final)
          (first.1 ++ [anchor] ++
            SemigroupBasis.CoRoots.S5_107.renderAnchoredBlocks
              anchor sourceBlocks ++
            SemigroupBasis.CoRoots.S5_107.renderMultipleSquares
              sourceMultiples ++
            List.replicate (Nat.succ nonempty.length) anchor ++
            final) := by
      simpa [arranged, sourceBlocks, sourceMultiples,
        emptyRendering,
        SemigroupBasis.CoRoots.S5_107.renderSquaredTerminatedBlocks,
        SemigroupBasis.CoRoots.S5_107.terminatedFactorMarkers,
        SemigroupBasis.CoRoots.S5_107.renderMultipleSquares,
        List.append_assoc] using extractedCore
    have arrangedBlocks :
        SemigroupBasis.CoRoots.S5_107.nonemptyTerminatedBlocks arranged =
          sourceBlocks := by
      dsimp [arranged, sourceBlocks]
      rw [
        SemigroupBasis.CoRoots.S5_107.nonemptyTerminatedBlocks_append]
      change
        SemigroupBasis.CoRoots.S5_107.nonemptyTerminatedBlocks nonempty ++
            SemigroupBasis.CoRoots.S5_107.nonemptyTerminatedBlocks empty =
          SemigroupBasis.CoRoots.S5_107.terminatedFactorBlocks nonempty
      rw [nonemptyProjection, emptyNonemptyBlocks]
      simp
    have blockPermutation :
        sourceBlocks.Perm
          (SemigroupBasis.CoRoots.S5_107.nonemptyTerminatedBlocks tail) := by
      have projected :=
        SemigroupBasis.CoRoots.S5_107.nonemptyTerminatedBlocks_perm
          tailPermutation
      rw [arrangedBlocks] at projected
      exact projected.symm
    have sourceToArranged :
        sourceMultiples.Perm
          (SemigroupBasis.CoRoots.S5_107.terminatedFactorMarkers
            (first :: arranged)) := by
      have moved :=
        SemigroupBasis.CoRoots.S5_107.perm_cons_append anchor
          (first.2 ::
            SemigroupBasis.CoRoots.S5_107.terminatedFactorMarkers nonempty)
          (SemigroupBasis.CoRoots.S5_107.terminatedFactorMarkers empty)
      simpa [sourceMultiples, arranged,
        SemigroupBasis.CoRoots.S5_107.terminatedFactorMarkers,
        List.append_assoc] using moved
    have arrangedToOriginal :
        (SemigroupBasis.CoRoots.S5_107.terminatedFactorMarkers
            (first :: arranged)).Perm
          (SemigroupBasis.CoRoots.S5_107.terminatedFactorMarkers
            (first :: tail)) :=
      SemigroupBasis.CoRoots.S5_107.terminatedFactorMarkers_perm <|
        (List.Perm.cons first tailPermutation).symm
    have multiplePermutation :
        sourceMultiples.Perm
          (SemigroupBasis.CoRoots.S5_107.terminatedFactorMarkers
            (first :: tail)) :=
      sourceToArranged.trans arrangedToOriginal
    have sourceBlocksNonempty :
        ∀ block ∈ sourceBlocks, block ≠ [] := by
      intro block member
      exact
        SemigroupBasis.CoRoots.S5_107.nonemptyTerminatedBlocks_blocks_nonempty
          tail block (blockPermutation.mem_iff.mp member)
    have reordered :=
      listDerivesRenderedCanonicalCoreBalanced
        first.1
        (List.replicate (Nat.succ nonempty.length) anchor ++ final)
        anchor blockPermutation multiplePermutation
        sourceBlocksNonempty
    have blockLength :
        nonempty.length =
          (SemigroupBasis.CoRoots.S5_107.nonemptyTerminatedBlocks
            tail).length := by
      have lengthEqual := blockPermutation.length_eq
      simpa [sourceBlocks,
        SemigroupBasis.CoRoots.S5_107.terminatedFactorBlocks] using
          lengthEqual
    have reorderedStep :
        ListDerives
          (first.1 ++ [anchor] ++
            SemigroupBasis.CoRoots.S5_107.renderAnchoredBlocks
              anchor sourceBlocks ++
            SemigroupBasis.CoRoots.S5_107.renderMultipleSquares
              sourceMultiples ++
            List.replicate (Nat.succ nonempty.length) anchor ++
            final)
          (first.1 ++ [anchor] ++
            SemigroupBasis.CoRoots.S5_107.renderAnchoredBlocks anchor
              (SemigroupBasis.CoRoots.S5_107.nonemptyTerminatedBlocks
                tail) ++
            SemigroupBasis.CoRoots.S5_107.renderMultipleSquares
              (SemigroupBasis.CoRoots.S5_107.terminatedFactorMarkers
                (first :: tail)) ++
            List.replicate
              (Nat.succ
                (SemigroupBasis.CoRoots.S5_107.nonemptyTerminatedBlocks
                  tail).length)
              anchor ++
            final) := by
      simpa [blockLength, List.append_assoc] using reordered
    exact rearranged.trans <| extracted.trans reorderedStep
  · obtain ⟨selectedHead, selectedTail, selectedShape⟩ :=
      List.exists_cons_of_ne_nil selectedEmpty
    subst selectedBlock
    let sourceBlocks :=
      SemigroupBasis.CoRoots.S5_107.terminatedFactorBlocks nonempty ++
        [selectedHead :: selectedTail]
    let sourceMultiples :=
      first.2 ::
        SemigroupBasis.CoRoots.S5_107.terminatedFactorMarkers nonempty ++
          [anchor] ++
            SemigroupBasis.CoRoots.S5_107.terminatedFactorMarkers empty
    have extractedCore :=
      listDerivesAnchorNonemptyFactorChainRetainingSquareWithStructuralDebt
        first.1 first.2 anchor nonempty
        selectedHead selectedTail
        (SemigroupBasis.CoRoots.S5_107.terminatedFactorMarkers empty)
        final nonemptyBlocks
    have extracted :
        ListDerives
          (SemigroupBasis.CoRoots.S5_107.renderSquaredTerminatedBlocks
              (first :: arranged) ++ final)
          (first.1 ++ [anchor] ++
            SemigroupBasis.CoRoots.S5_107.renderAnchoredBlocks
              anchor sourceBlocks ++
            SemigroupBasis.CoRoots.S5_107.renderMultipleSquares
              sourceMultiples ++
            List.replicate
              (Nat.succ (Nat.succ nonempty.length)) anchor ++
            final) := by
      simpa [arranged, sourceBlocks, sourceMultiples,
        emptyRendering,
        SemigroupBasis.CoRoots.S5_107.renderSquaredTerminatedBlocks,
        SemigroupBasis.CoRoots.S5_107.terminatedFactorMarkers,
        SemigroupBasis.CoRoots.S5_107.renderMultipleSquares,
        List.append_assoc] using extractedCore
    have arrangedBlocks :
        SemigroupBasis.CoRoots.S5_107.nonemptyTerminatedBlocks arranged =
          sourceBlocks := by
      simp [arranged, sourceBlocks, nonemptyProjection,
        emptyNonemptyBlocks,
        SemigroupBasis.CoRoots.S5_107.nonemptyTerminatedBlocks]
    have blockPermutation :
        sourceBlocks.Perm
          (SemigroupBasis.CoRoots.S5_107.nonemptyTerminatedBlocks tail) := by
      have projected :=
        SemigroupBasis.CoRoots.S5_107.nonemptyTerminatedBlocks_perm
          tailPermutation
      rw [arrangedBlocks] at projected
      exact projected.symm
    have sourceToArranged :
        sourceMultiples.Perm
          (SemigroupBasis.CoRoots.S5_107.terminatedFactorMarkers
            (first :: arranged)) := by
      simpa [sourceMultiples, arranged,
        SemigroupBasis.CoRoots.S5_107.terminatedFactorMarkers,
        List.append_assoc] using
          (List.Perm.refl sourceMultiples)
    have arrangedToOriginal :
        (SemigroupBasis.CoRoots.S5_107.terminatedFactorMarkers
            (first :: arranged)).Perm
          (SemigroupBasis.CoRoots.S5_107.terminatedFactorMarkers
            (first :: tail)) :=
      SemigroupBasis.CoRoots.S5_107.terminatedFactorMarkers_perm <|
        (List.Perm.cons first tailPermutation).symm
    have multiplePermutation :
        sourceMultiples.Perm
          (SemigroupBasis.CoRoots.S5_107.terminatedFactorMarkers
            (first :: tail)) :=
      sourceToArranged.trans arrangedToOriginal
    have sourceBlocksNonempty :
        ∀ block ∈ sourceBlocks, block ≠ [] := by
      intro block member
      exact
        SemigroupBasis.CoRoots.S5_107.nonemptyTerminatedBlocks_blocks_nonempty
          tail block (blockPermutation.mem_iff.mp member)
    have reordered :=
      listDerivesRenderedCanonicalCoreBalanced
        first.1
        (List.replicate
            (Nat.succ (Nat.succ nonempty.length)) anchor ++
          final)
        anchor blockPermutation multiplePermutation
        sourceBlocksNonempty
    have blockLength :
        Nat.succ nonempty.length =
          (SemigroupBasis.CoRoots.S5_107.nonemptyTerminatedBlocks
            tail).length := by
      have lengthEqual := blockPermutation.length_eq
      simpa [sourceBlocks,
        SemigroupBasis.CoRoots.S5_107.terminatedFactorBlocks] using
          lengthEqual
    have reorderedStep :
        ListDerives
          (first.1 ++ [anchor] ++
            SemigroupBasis.CoRoots.S5_107.renderAnchoredBlocks
              anchor sourceBlocks ++
            SemigroupBasis.CoRoots.S5_107.renderMultipleSquares
              sourceMultiples ++
            List.replicate
              (Nat.succ (Nat.succ nonempty.length)) anchor ++
            final)
          (first.1 ++ [anchor] ++
            SemigroupBasis.CoRoots.S5_107.renderAnchoredBlocks anchor
              (SemigroupBasis.CoRoots.S5_107.nonemptyTerminatedBlocks
                tail) ++
            SemigroupBasis.CoRoots.S5_107.renderMultipleSquares
              (SemigroupBasis.CoRoots.S5_107.terminatedFactorMarkers
                (first :: tail)) ++
            List.replicate
              (Nat.succ
                (SemigroupBasis.CoRoots.S5_107.nonemptyTerminatedBlocks
                  tail).length)
              anchor ++
            final) := by
      rw [← blockLength]
      simpa [List.append_assoc] using reordered
    exact rearranged.trans <| extracted.trans reorderedStep

/-- The `S5_107` canonical list with its marker-parity debt retained between
the sorted square bank and the final simple block. The surrounding scanner
data is exactly the data used by
`S5_107.listDerivesExtractScannerCanonicalCore` and the sealed normalizer. -/
def parityPreparedScannerCanonicalList
    (letters : List Nat) : List Nat :=
  match
      SemigroupBasis.CoRoots.S5_107.sortedMultipleLetters letters with
  | [] => letters
  | anchor :: remainingMultiples =>
      SemigroupBasis.CoRoots.S5_107.initialSimpleBlock letters ++
        [anchor] ++
        SemigroupBasis.CoRoots.S5_107.renderAnchoredBlocks anchor
          (SemigroupBasis.CoRoots.S5_107.sortedSimpleBlocks
            (SemigroupBasis.CoRoots.S5_107.interiorSimpleBlocks letters)) ++
        SemigroupBasis.CoRoots.S5_107.renderMultipleSquares
          (anchor :: remainingMultiples) ++
        parityDebtReduce
          (parityPreparedStructuralAnchorDebt letters anchor ++
            parityPreparedMarkerDebt letters) ++
        SemigroupBasis.CoRoots.S5_107.finalSimpleBlock letters

private theorem parityPreparedMarkerDebt_capped_eq
    {left right : Word Nat}
    (same :
      SemigroupBasis.CoRoots.S5_107.SameSimpleAdjacencySignature
        left right) :
    ∀ tested,
      Nat.min
          ((parityPreparedMarkerDebt left.toList).count tested) 2 =
        Nat.min
          ((parityPreparedMarkerDebt right.toList).count tested) 2 := by
  intro tested
  have multipleIff := same.multiple tested
  by_cases leftMultiple : 2 ≤ left.toList.count tested
  · have rightMultiple :
        2 ≤ right.toList.count tested :=
      multipleIff.mp leftMultiple
    have leftCount :
        (parityPreparedMarkerDebt left.toList).count tested =
          left.toList.count tested := by
      simpa [parityPreparedMarkerDebt] using
        SemigroupBasis.CoRoots.S5_107.count_terminatedFactorMarkers_of_multiple
          tested left.toList leftMultiple
    have rightCount :
        (parityPreparedMarkerDebt right.toList).count tested =
          right.toList.count tested := by
      simpa [parityPreparedMarkerDebt] using
        SemigroupBasis.CoRoots.S5_107.count_terminatedFactorMarkers_of_multiple
          tested right.toList rightMultiple
    rw [leftCount, rightCount]
    have leftMin :
        Nat.min (left.toList.count tested) 2 = 2 :=
      Nat.min_eq_right leftMultiple
    have rightMin :
        Nat.min (right.toList.count tested) 2 = 2 :=
      Nat.min_eq_right rightMultiple
    exact leftMin.trans rightMin.symm
  · have rightNotMultiple :
        ¬2 ≤ right.toList.count tested :=
      fun rightMultiple =>
        leftMultiple (multipleIff.mpr rightMultiple)
    have leftAbsent :
        tested ∉ parityPreparedMarkerDebt left.toList := by
      intro member
      apply leftMultiple
      exact
        (SemigroupBasis.CoRoots.S5_107.mem_terminatedFactorMarkers_iff
          tested left.toList).mp member
    have rightAbsent :
        tested ∉ parityPreparedMarkerDebt right.toList := by
      intro member
      apply rightNotMultiple
      exact
        (SemigroupBasis.CoRoots.S5_107.mem_terminatedFactorMarkers_iff
          tested right.toList).mp member
    rw [List.count_eq_zero.mpr leftAbsent,
      List.count_eq_zero.mpr rightAbsent]

private theorem parityPreparedMarkerDebt_parity_eq
    {left right : Word Nat}
    (same :
      SemigroupBasis.CoRoots.S5_107.SameSimpleAdjacencySignature
        left right)
    (parity : SameOccurrenceParity left right) :
    ∀ tested,
      (parityPreparedMarkerDebt left.toList).count tested % 2 =
        (parityPreparedMarkerDebt right.toList).count tested % 2 := by
  intro tested
  have multipleIff := same.multiple tested
  by_cases leftMultiple : 2 ≤ left.toList.count tested
  · have rightMultiple :
        2 ≤ right.toList.count tested :=
      multipleIff.mp leftMultiple
    have leftCount :
        (parityPreparedMarkerDebt left.toList).count tested =
          left.toList.count tested := by
      simpa [parityPreparedMarkerDebt] using
        SemigroupBasis.CoRoots.S5_107.count_terminatedFactorMarkers_of_multiple
          tested left.toList leftMultiple
    have rightCount :
        (parityPreparedMarkerDebt right.toList).count tested =
          right.toList.count tested := by
      simpa [parityPreparedMarkerDebt] using
        SemigroupBasis.CoRoots.S5_107.count_terminatedFactorMarkers_of_multiple
          tested right.toList rightMultiple
    rw [leftCount, rightCount]
    exact parity tested
  · have rightNotMultiple :
        ¬2 ≤ right.toList.count tested :=
      fun rightMultiple =>
        leftMultiple (multipleIff.mpr rightMultiple)
    have leftAbsent :
        tested ∉ parityPreparedMarkerDebt left.toList := by
      intro member
      apply leftMultiple
      exact
        (SemigroupBasis.CoRoots.S5_107.mem_terminatedFactorMarkers_iff
          tested left.toList).mp member
    have rightAbsent :
        tested ∉ parityPreparedMarkerDebt right.toList := by
      intro member
      apply rightNotMultiple
      exact
        (SemigroupBasis.CoRoots.S5_107.mem_terminatedFactorMarkers_iff
          tested right.toList).mp member
    rw [List.count_eq_zero.mpr leftAbsent,
      List.count_eq_zero.mpr rightAbsent]

/-- Equal scanner signatures display the same number of structural anchors. -/
private theorem parityPreparedStructuralAnchorDebt_eq
    {left right : Word Nat}
    (same :
      SemigroupBasis.CoRoots.S5_107.SameSimpleAdjacencySignature
        left right)
    (anchor : Nat) :
    parityPreparedStructuralAnchorDebt left.toList anchor =
      parityPreparedStructuralAnchorDebt right.toList anchor := by
  unfold parityPreparedStructuralAnchorDebt
  rw [same.interiorSimpleBlocks_perm.length_eq]

private theorem parityPreparedCanonicalDebt_capped_eq
    {left right : Word Nat}
    (same :
      SemigroupBasis.CoRoots.S5_107.SameSimpleAdjacencySignature
        left right)
    (anchor : Nat)
    (anchorMultiple : 2 ≤ left.toList.count anchor) :
    ∀ tested,
      Nat.min
          ((parityPreparedStructuralAnchorDebt left.toList anchor ++
              parityPreparedMarkerDebt left.toList).count tested) 2 =
        Nat.min
          ((parityPreparedStructuralAnchorDebt right.toList anchor ++
              parityPreparedMarkerDebt right.toList).count tested) 2 := by
  intro tested
  by_cases equal : tested = anchor
  · subst tested
    have rightMultiple : 2 ≤ right.toList.count anchor :=
      (same.multiple anchor).mp anchorMultiple
    have leftMarkerCount :
        (parityPreparedMarkerDebt left.toList).count anchor =
          left.toList.count anchor := by
      simpa [parityPreparedMarkerDebt] using
        SemigroupBasis.CoRoots.S5_107.count_terminatedFactorMarkers_of_multiple
          anchor left.toList anchorMultiple
    have rightMarkerCount :
        (parityPreparedMarkerDebt right.toList).count anchor =
          right.toList.count anchor := by
      simpa [parityPreparedMarkerDebt] using
        SemigroupBasis.CoRoots.S5_107.count_terminatedFactorMarkers_of_multiple
          anchor right.toList rightMultiple
    have leftTotal :
        2 ≤
          (parityPreparedStructuralAnchorDebt left.toList anchor ++
            parityPreparedMarkerDebt left.toList).count anchor := by
      rw [List.count_append, leftMarkerCount]
      omega
    have rightTotal :
        2 ≤
          (parityPreparedStructuralAnchorDebt right.toList anchor ++
            parityPreparedMarkerDebt right.toList).count anchor := by
      rw [List.count_append, rightMarkerCount]
      omega
    exact
      (Nat.min_eq_right leftTotal).trans
        (Nat.min_eq_right rightTotal).symm
  · simpa [parityPreparedStructuralAnchorDebt,
      List.count_append, List.count_replicate, equal, Ne.symm equal] using
        parityPreparedMarkerDebt_capped_eq same tested

private theorem parityPreparedCanonicalDebt_parity_eq
    {left right : Word Nat}
    (same :
      SemigroupBasis.CoRoots.S5_107.SameSimpleAdjacencySignature
        left right)
    (parity : SameOccurrenceParity left right)
    (anchor : Nat) :
    ∀ tested,
      (parityPreparedStructuralAnchorDebt left.toList anchor ++
          parityPreparedMarkerDebt left.toList).count tested % 2 =
        (parityPreparedStructuralAnchorDebt right.toList anchor ++
          parityPreparedMarkerDebt right.toList).count tested % 2 := by
  intro tested
  have structuralEqual :=
    congrArg (fun debt : List Nat => debt.count tested)
      (parityPreparedStructuralAnchorDebt_eq same anchor)
  have structuralCountEqual :
      (parityPreparedStructuralAnchorDebt left.toList anchor).count tested =
        (parityPreparedStructuralAnchorDebt right.toList anchor).count tested := by
    simpa using structuralEqual
  have markerParity :=
    parityPreparedMarkerDebt_parity_eq same parity tested
  rw [List.count_append, List.count_append, structuralCountEqual]
  omega

/-- A common retained square bank reduces two marker debts to their canonical
capped-parity representatives and then permutes those representatives. This
is the deterministic reduction step after the scanner extraction. -/
theorem listDerivesAlignParityMarkerDebt
    {bank leftDebt rightDebt : List Nat}
    (leftCovered :
      ∀ letter ∈ leftDebt, letter ∈ bank)
    (rightCovered :
      ∀ letter ∈ rightDebt, letter ∈ bank)
    (capped :
      ∀ tested,
        Nat.min (leftDebt.count tested) 2 =
          Nat.min (rightDebt.count tested) 2)
    (parity :
      ∀ tested,
        leftDebt.count tested % 2 =
          rightDebt.count tested % 2)
    (before suffix : List Nat) :
    ListDerives
      (before ++
        SemigroupBasis.CoRoots.S5_107.renderMultipleSquares bank ++
        leftDebt ++ suffix)
      (before ++
        SemigroupBasis.CoRoots.S5_107.renderMultipleSquares bank ++
        rightDebt ++ suffix) := by
  have leftReductionRaw :=
    listDerivesDebtToParityReduce
      bank leftDebt [] suffix leftCovered
  have leftReduction :
      ListDerives
        (before ++
          SemigroupBasis.CoRoots.S5_107.renderMultipleSquares bank ++
          leftDebt ++ suffix)
        (before ++
          SemigroupBasis.CoRoots.S5_107.renderMultipleSquares bank ++
          parityDebtReduce leftDebt ++ suffix) := by
    simpa [List.append_assoc] using
      leftReductionRaw.prepend before
  have reducedPermutation :=
    parityDebtReduce_perm_of_signatures capped parity
  have reducedCovered :
      ∀ letter ∈ parityDebtReduce leftDebt, letter ∈ bank := by
    intro letter member
    exact leftCovered letter <|
      (mem_parityDebtReduce_iff letter leftDebt).mp member
  have permutationRaw :=
    listDerivesDebtPermutationWithSquareBank
      reducedPermutation reducedCovered [] suffix
  have permutationStep :
      ListDerives
        (before ++
          SemigroupBasis.CoRoots.S5_107.renderMultipleSquares bank ++
          parityDebtReduce leftDebt ++ suffix)
        (before ++
          SemigroupBasis.CoRoots.S5_107.renderMultipleSquares bank ++
          parityDebtReduce rightDebt ++ suffix) := by
    simpa [List.append_assoc] using
      permutationRaw.prepend before
  have rightReductionRaw :=
    listDerivesDebtToParityReduce
      bank rightDebt [] suffix rightCovered
  have rightReduction :
      ListDerives
        (before ++
          SemigroupBasis.CoRoots.S5_107.renderMultipleSquares bank ++
          rightDebt ++ suffix)
        (before ++
          SemigroupBasis.CoRoots.S5_107.renderMultipleSquares bank ++
          parityDebtReduce rightDebt ++ suffix) := by
    simpa [List.append_assoc] using
      rightReductionRaw.prepend before
  exact
    leftReduction.trans <|
      permutationStep.trans rightReduction.symm

/-- One-word reach contract for the corrected scanner target. Its debt ledger
includes the leading anchor and every anchor terminating an interior simple
block, followed by the separated marker occurrences. -/
def ParityPreparedScannerCanonicalization : Prop :=
  ∀ word : Word Nat,
    ListDerives
      (parityPreparedTerminatedList word.toList)
      (parityPreparedScannerCanonicalList word.toList)

/-- The corrected one-word scanner canonicalization. The no-multiple branch
reverses the balanced preparation directly. In the multiple branch the
structural extractor retains every parity occurrence, after which balanced
block/square permutations and the square-bank debt reducer reach the
deterministic target. -/
theorem parityPreparedScannerCanonicalization_proved :
    ParityPreparedScannerCanonicalization := by
  intro word
  let letters := word.toList
  cases multiplesShape :
      SemigroupBasis.CoRoots.S5_107.sortedMultipleLetters letters with
  | nil =>
      have reversed :=
        (listDerivesParityPreparedTerminatedList letters).symm
      simpa [letters, parityPreparedScannerCanonicalList,
        multiplesShape] using reversed
  | cons anchor remainingMultiples =>
      have anchorMultiple :
          2 ≤ letters.count anchor :=
        (SemigroupBasis.CoRoots.S5_107.sortedMultipleLetters_mem_iff
          anchor letters).mp <| by
            rw [multiplesShape]
            simp
      have markerMember :
          anchor ∈
            SemigroupBasis.CoRoots.S5_107.terminatedFactorMarkers
              (SemigroupBasis.CoRoots.S5_107.terminatedBlocks letters) :=
        (SemigroupBasis.CoRoots.S5_107.mem_terminatedFactorMarkers_iff
          anchor letters).mpr anchorMultiple
      have factorsNonempty :
          SemigroupBasis.CoRoots.S5_107.terminatedBlocks letters ≠ [] := by
        intro factorsEmpty
        rw [factorsEmpty] at markerMember
        simp [SemigroupBasis.CoRoots.S5_107.terminatedFactorMarkers] at markerMember
      obtain ⟨first, tail, factorsShape⟩ :=
        List.exists_cons_of_ne_nil factorsNonempty
      obtain ⟨selected, selectedMember, selectedMarker⟩ :=
        SemigroupBasis.CoRoots.S5_107.exists_tail_factor_with_marker_of_multiple
          letters first tail anchor factorsShape anchorMultiple
      have extractedRaw :=
        listDerivesExtractTerminatedWithAnchorStructuralDebt
          first tail selected
          (parityPreparedMarkerDebt letters ++
            SemigroupBasis.CoRoots.S5_107.terminatedFinalBlock letters)
          anchor selectedMember selectedMarker
      have endpoints :=
        SemigroupBasis.CoRoots.S5_107.terminatedBlocks_cons_endpoint_blocks
          letters first tail factorsShape
      have finalEndpoint :=
        SemigroupBasis.CoRoots.S5_107.terminatedFinalBlock_eq_finalSimpleBlock
          letters
      have extracted :
          ListDerives
            (parityPreparedTerminatedList letters)
            (SemigroupBasis.CoRoots.S5_107.initialSimpleBlock letters ++
              [anchor] ++
              SemigroupBasis.CoRoots.S5_107.renderAnchoredBlocks anchor
                (SemigroupBasis.CoRoots.S5_107.interiorSimpleBlocks
                  letters) ++
              SemigroupBasis.CoRoots.S5_107.renderMultipleSquares
                (SemigroupBasis.CoRoots.S5_107.terminatedFactorMarkers
                  (SemigroupBasis.CoRoots.S5_107.terminatedBlocks
                    letters)) ++
              parityPreparedStructuralAnchorDebt letters anchor ++
              parityPreparedMarkerDebt letters ++
              SemigroupBasis.CoRoots.S5_107.finalSimpleBlock letters) := by
        simpa [parityPreparedTerminatedList,
          parityPreparedStructuralAnchorDebt, parityPreparedMarkerDebt,
          factorsShape, endpoints.1, endpoints.2, finalEndpoint,
          List.append_assoc] using extractedRaw
      let markerLabels : List Nat :=
        SemigroupBasis.CoRoots.S5_107.terminatedFactorMarkers
          (SemigroupBasis.CoRoots.S5_107.terminatedBlocks letters)
      let reducedLabels : List Nat :=
        SemigroupBasis.CoRoots.S5_107.distinctLetters markerLabels
      let debt : List Nat :=
        parityPreparedStructuralAnchorDebt letters anchor ++
          parityPreparedMarkerDebt letters
      have deduplicatedRaw :=
        (listDerivesMultipleSquareDedup markerLabels).context
          (SemigroupBasis.CoRoots.S5_107.initialSimpleBlock letters ++
            [anchor] ++
            SemigroupBasis.CoRoots.S5_107.renderAnchoredBlocks anchor
              (SemigroupBasis.CoRoots.S5_107.interiorSimpleBlocks letters))
          (debt ++
            SemigroupBasis.CoRoots.S5_107.finalSimpleBlock letters)
      have deduplicated :
          ListDerives
            (SemigroupBasis.CoRoots.S5_107.initialSimpleBlock letters ++
              [anchor] ++
              SemigroupBasis.CoRoots.S5_107.renderAnchoredBlocks anchor
                (SemigroupBasis.CoRoots.S5_107.interiorSimpleBlocks
                  letters) ++
              SemigroupBasis.CoRoots.S5_107.renderMultipleSquares
                markerLabels ++
              debt ++
              SemigroupBasis.CoRoots.S5_107.finalSimpleBlock letters)
            (SemigroupBasis.CoRoots.S5_107.initialSimpleBlock letters ++
              [anchor] ++
              SemigroupBasis.CoRoots.S5_107.renderAnchoredBlocks anchor
                (SemigroupBasis.CoRoots.S5_107.interiorSimpleBlocks
                  letters) ++
              SemigroupBasis.CoRoots.S5_107.renderMultipleSquares
                reducedLabels ++
              debt ++
              SemigroupBasis.CoRoots.S5_107.finalSimpleBlock letters) := by
        simpa [markerLabels, reducedLabels, debt,
          List.append_assoc] using deduplicatedRaw
      have extractedDeduplicated :
          ListDerives
            (parityPreparedTerminatedList letters)
            (SemigroupBasis.CoRoots.S5_107.initialSimpleBlock letters ++
              [anchor] ++
              SemigroupBasis.CoRoots.S5_107.renderAnchoredBlocks anchor
                (SemigroupBasis.CoRoots.S5_107.interiorSimpleBlocks
                  letters) ++
              SemigroupBasis.CoRoots.S5_107.renderMultipleSquares
                reducedLabels ++
              debt ++
              SemigroupBasis.CoRoots.S5_107.finalSimpleBlock letters) := by
        exact extracted.trans <| by
          simpa [markerLabels, debt,
            List.append_assoc] using deduplicated
      have blockPermutation :
          (SemigroupBasis.CoRoots.S5_107.interiorSimpleBlocks letters).Perm
            (SemigroupBasis.CoRoots.S5_107.sortedSimpleBlocks
              (SemigroupBasis.CoRoots.S5_107.interiorSimpleBlocks
                letters)) := by
        unfold SemigroupBasis.CoRoots.S5_107.sortedSimpleBlocks
        exact (List.mergeSort_perm _ _).symm
      have multiplePermutation :
          reducedLabels.Perm (anchor :: remainingMultiples) := by
        have markers :=
          SemigroupBasis.CoRoots.S5_107.distinctTerminatedMarkers_perm_sortedMultipleLetters
            letters
        rw [multiplesShape] at markers
        simpa [reducedLabels, markerLabels] using markers
      have blocksNonempty :
          ∀ block ∈
              SemigroupBasis.CoRoots.S5_107.interiorSimpleBlocks letters,
            block ≠ [] := by
        intro block member
        exact
          SemigroupBasis.CoRoots.S5_107.simpleBlocks_blocks_nonempty
            letters block
            ((SemigroupBasis.CoRoots.S5_107.mem_interiorSimpleBlocks_iff
              letters block).mp member).1
      have reordered :=
        listDerivesRenderedCanonicalCoreBalanced
          (SemigroupBasis.CoRoots.S5_107.initialSimpleBlock letters)
          (debt ++
            SemigroupBasis.CoRoots.S5_107.finalSimpleBlock letters)
          anchor blockPermutation multiplePermutation blocksNonempty
      have canonicalCore :
          ListDerives
            (parityPreparedTerminatedList letters)
            (SemigroupBasis.CoRoots.S5_107.initialSimpleBlock letters ++
              [anchor] ++
              SemigroupBasis.CoRoots.S5_107.renderAnchoredBlocks anchor
                (SemigroupBasis.CoRoots.S5_107.sortedSimpleBlocks
                  (SemigroupBasis.CoRoots.S5_107.interiorSimpleBlocks
                    letters)) ++
              SemigroupBasis.CoRoots.S5_107.renderMultipleSquares
                (anchor :: remainingMultiples) ++
              debt ++
              SemigroupBasis.CoRoots.S5_107.finalSimpleBlock letters) := by
        exact extractedDeduplicated.trans <| by
          simpa [List.append_assoc] using reordered
      have debtCovered :
          ∀ letter ∈ debt, letter ∈ anchor :: remainingMultiples := by
        intro letter member
        change
          letter ∈
            parityPreparedStructuralAnchorDebt letters anchor ++
              parityPreparedMarkerDebt letters at member
        rcases List.mem_append.mp member with
          structuralMember | markerDebtMember
        · have equal : letter = anchor := by
            simpa [parityPreparedStructuralAnchorDebt] using
              structuralMember
          subst letter
          simp
        · have multiple :
              2 ≤ letters.count letter :=
            (SemigroupBasis.CoRoots.S5_107.mem_terminatedFactorMarkers_iff
              letter letters).mp <| by
                  simpa [parityPreparedMarkerDebt] using markerDebtMember
          have canonicalMember :
              letter ∈
                SemigroupBasis.CoRoots.S5_107.sortedMultipleLetters
                  letters :=
            (SemigroupBasis.CoRoots.S5_107.sortedMultipleLetters_mem_iff
              letter letters).mpr multiple
          simpa [multiplesShape] using canonicalMember
      have reducedDebtRaw :=
        listDerivesDebtToParityReduce
          (anchor :: remainingMultiples) debt []
          (SemigroupBasis.CoRoots.S5_107.finalSimpleBlock letters)
          debtCovered
      have reducedDebt :=
        reducedDebtRaw.prepend
          (SemigroupBasis.CoRoots.S5_107.initialSimpleBlock letters ++
            [anchor] ++
            SemigroupBasis.CoRoots.S5_107.renderAnchoredBlocks anchor
              (SemigroupBasis.CoRoots.S5_107.sortedSimpleBlocks
                (SemigroupBasis.CoRoots.S5_107.interiorSimpleBlocks
                  letters)))
      have reached :
          ListDerives
            (parityPreparedTerminatedList letters)
            (SemigroupBasis.CoRoots.S5_107.initialSimpleBlock letters ++
              [anchor] ++
              SemigroupBasis.CoRoots.S5_107.renderAnchoredBlocks anchor
                (SemigroupBasis.CoRoots.S5_107.sortedSimpleBlocks
                  (SemigroupBasis.CoRoots.S5_107.interiorSimpleBlocks
                    letters)) ++
              SemigroupBasis.CoRoots.S5_107.renderMultipleSquares
                (anchor :: remainingMultiples) ++
              parityDebtReduce debt ++
              SemigroupBasis.CoRoots.S5_107.finalSimpleBlock letters) := by
        exact canonicalCore.trans <| by
          simpa [List.append_assoc] using reducedDebt
      simpa [letters, parityPreparedScannerCanonicalList,
        multiplesShape, debt, List.append_assoc] using reached

/-- The exact scanner-level residual left after the WMI-green preparation
theorem. The hypotheses contain only the two invariants of the factor
intersection, and the endpoints are deterministic functions of the two
source words. A proof should align the square scanner cores while consuming
the explicit marker-debt tails; no arbitrary `S5_107` derivation remains. -/
def ParityPreparedScannerAlignment : Prop :=
  ∀ {left right : Word Nat},
    SemigroupBasis.CoRoots.S5_107.SameSimpleAdjacencySignature left right →
      SameOccurrenceParity left right →
        ListDerives
          (parityPreparedTerminatedList left.toList)
          (parityPreparedTerminatedList right.toList)

/-- Canonicalizing each prepared scanner separately suffices for the original
pairwise residual. Equal `S5_107` signatures identify the canonical scanner
context and square bank; marker-count preservation and occurrence parity
then identify the reduced marker debts. -/
theorem parityPreparedScannerAlignment_of_canonicalization
    (canonicalization : ParityPreparedScannerCanonicalization) :
    ParityPreparedScannerAlignment := by
  intro left right same parity
  have leftCanonical := canonicalization left
  have rightCanonical := canonicalization right
  have multipleEqual := same.sortedMultipleLetters_eq
  cases leftShape :
      SemigroupBasis.CoRoots.S5_107.sortedMultipleLetters left.toList with
  | nil =>
      have rightShape :
          SemigroupBasis.CoRoots.S5_107.sortedMultipleLetters
              right.toList = [] := by
        calc
          SemigroupBasis.CoRoots.S5_107.sortedMultipleLetters
                right.toList =
              SemigroupBasis.CoRoots.S5_107.sortedMultipleLetters
                left.toList :=
            multipleEqual.symm
          _ = [] := leftShape
      have sourceEqual : left.toList = right.toList := by
        have canonicalEqual := same.canonicalList_eq
        simpa
          [SemigroupBasis.CoRoots.S5_107.simpleAdjacencyCanonicalList,
            leftShape, rightShape] using canonicalEqual
      have canonicalEqual :
          parityPreparedScannerCanonicalList left.toList =
            parityPreparedScannerCanonicalList right.toList := by
        simp [parityPreparedScannerCanonicalList,
          leftShape, rightShape, sourceEqual]
      have alignedCanonical :
          ListDerives
            (parityPreparedScannerCanonicalList left.toList)
            (parityPreparedScannerCanonicalList right.toList) := by
        rw [canonicalEqual]
        exact
          SemigroupBasis.CoRoots.S5_107.ListDerives.refl
            (basis := candidateBasis) _
      exact
        leftCanonical.trans <|
          alignedCanonical.trans rightCanonical.symm
  | cons anchor remainingMultiples =>
      have rightShape :
          SemigroupBasis.CoRoots.S5_107.sortedMultipleLetters
              right.toList =
            anchor :: remainingMultiples := by
        calc
          SemigroupBasis.CoRoots.S5_107.sortedMultipleLetters
                right.toList =
              SemigroupBasis.CoRoots.S5_107.sortedMultipleLetters
                left.toList :=
            multipleEqual.symm
          _ = anchor :: remainingMultiples := leftShape
      have leftCovered :
          ∀ letter ∈ parityPreparedMarkerDebt left.toList,
            letter ∈ anchor :: remainingMultiples := by
        intro letter member
        have multiple :
            2 ≤ left.toList.count letter :=
          (SemigroupBasis.CoRoots.S5_107.mem_terminatedFactorMarkers_iff
            letter left.toList).mp member
        have sortedMember :=
          (SemigroupBasis.CoRoots.S5_107.sortedMultipleLetters_mem_iff
            letter left.toList).mpr multiple
        simpa [leftShape] using sortedMember
      have anchorMultiple :
          2 ≤ left.toList.count anchor :=
        (SemigroupBasis.CoRoots.S5_107.sortedMultipleLetters_mem_iff
          anchor left.toList).mp <| by
            rw [leftShape]
            simp
      have leftCanonicalDebtCovered :
          ∀ letter ∈
              parityPreparedStructuralAnchorDebt left.toList anchor ++
                parityPreparedMarkerDebt left.toList,
            letter ∈ anchor :: remainingMultiples := by
        intro letter member
        rcases List.mem_append.mp member with structural | marker
        · have equal : letter = anchor := by
            simpa [parityPreparedStructuralAnchorDebt] using structural
          subst letter
          simp
        · exact leftCovered letter marker
      have initialEqual := same.initialSimpleBlock_eq
      have finalEqual := same.finalSimpleBlock_eq
      have structuralDebtEqual :=
        parityPreparedStructuralAnchorDebt_eq same anchor
      have sortedInteriorEqual :
          SemigroupBasis.CoRoots.S5_107.sortedSimpleBlocks
              (SemigroupBasis.CoRoots.S5_107.interiorSimpleBlocks
                left.toList) =
            SemigroupBasis.CoRoots.S5_107.sortedSimpleBlocks
              (SemigroupBasis.CoRoots.S5_107.interiorSimpleBlocks
                right.toList) :=
        SemigroupBasis.CoRoots.S5_107.sortedSimpleBlocks_eq_of_perm
          same.interiorSimpleBlocks_perm
      let before :=
        SemigroupBasis.CoRoots.S5_107.initialSimpleBlock left.toList ++
          [anchor] ++
          SemigroupBasis.CoRoots.S5_107.renderAnchoredBlocks anchor
            (SemigroupBasis.CoRoots.S5_107.sortedSimpleBlocks
              (SemigroupBasis.CoRoots.S5_107.interiorSimpleBlocks
                left.toList))
      have reducedPermutation :=
        parityDebtReduce_perm_of_signatures
          (parityPreparedCanonicalDebt_capped_eq
            same anchor anchorMultiple)
          (parityPreparedCanonicalDebt_parity_eq
            same parity anchor)
      have reducedCovered :
          ∀ letter ∈
              parityDebtReduce
                (parityPreparedStructuralAnchorDebt left.toList anchor ++
                  parityPreparedMarkerDebt left.toList),
            letter ∈ anchor :: remainingMultiples := by
        intro letter member
        exact leftCanonicalDebtCovered letter <|
          (mem_parityDebtReduce_iff
            letter
            (parityPreparedStructuralAnchorDebt left.toList anchor ++
              parityPreparedMarkerDebt left.toList)).mp member
      have debtPermutation :=
        listDerivesDebtPermutationWithSquareBank
          reducedPermutation reducedCovered []
          (SemigroupBasis.CoRoots.S5_107.finalSimpleBlock left.toList)
      have debtAlignment :=
        debtPermutation.prepend before
      have alignedCanonical :
          ListDerives
            (parityPreparedScannerCanonicalList left.toList)
            (parityPreparedScannerCanonicalList right.toList) := by
        simpa [parityPreparedScannerCanonicalList,
          leftShape, rightShape, before, initialEqual,
          finalEqual, structuralDebtEqual,
          sortedInteriorEqual, List.append_assoc] using
            debtAlignment
      exact
        leftCanonical.trans <|
          alignedCanonical.trans rightCanonical.symm

/-- Closing the concrete prepared-scanner alignment closes the original
occurrence-parity kernel. -/
theorem parityKernelLift_of_parityPreparedScannerAlignment
    (alignment : ParityPreparedScannerAlignment) :
    ParityKernelLift := by
  intro left right s5Derivation parity
  have same :=
    sameSimpleAdjacencySignatureOfS5Derivation s5Derivation
  have leftPrepared :=
    listDerivesParityPreparedTerminatedList left.toList
  have rightPrepared :=
    listDerivesParityPreparedTerminatedList right.toList
  have preparedAlignment := alignment same parity
  have listed :=
    leftPrepared.trans
      (preparedAlignment.trans rightPrepared.symm)
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail =>
          simpa [SemigroupBasis.CoRoots.S5_107.listWordOfCons] using
            SemigroupBasis.CoRoots.S5_107.ListDerives.toWord listed

/-- The corrected structural-ledger construction closes the parity kernel
without any residual hypothesis. -/
theorem parityKernelLift_proved :
    ParityKernelLift :=
  parityKernelLift_of_parityPreparedScannerAlignment <|
    parityPreparedScannerAlignment_of_canonicalization
      parityPreparedScannerCanonicalization_proved

/-- `SameFactorSignature` supplies the sealed normalizer derivation required
by `ParityKernelLift`. -/
theorem sealedS5DerivationOfSameFactorSignature
    {left right : Word Nat}
    (same :
      SemigroupBasis.CoRoots.Order6FactorPairS2S5107Prelude.SameFactorSignature
        left right) :
    Derives s5Basis left right := by
  have leftNormal :=
    SemigroupBasis.CoRoots.S5_107.derivesCanonicalUnrestricted left
  have rightNormal :=
    SemigroupBasis.CoRoots.S5_107.derivesCanonicalUnrestricted right
  rw [same.s5.canonicalWord_eq] at leftNormal
  exact leftNormal.trans rightNormal.symm

theorem parityKernelInputOfSameFactorSignature
    {left right : Word Nat}
    (same :
      SemigroupBasis.CoRoots.Order6FactorPairS2S5107Prelude.SameFactorSignature
        left right) :
    Derives s5Basis left right ∧ SameOccurrenceParity left right :=
  ⟨sealedS5DerivationOfSameFactorSignature same, same.parity⟩

end SemigroupBasis.CoRoots.Order6FactorPairS2S5107ParityKernel
