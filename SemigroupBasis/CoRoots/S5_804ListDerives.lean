import SemigroupBasis.CoRoots.S5_107ListDerives
import SemigroupBasis.CoRoots.S5_804

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.S5_804

open SemigroupBasis

/-- List-level derivability for the eight-law `S5_804` basis. -/
abbrev ListDerives : List Nat → List Nat → Prop :=
  S5_107.ListDerives basis

private abbrev listWordOfCons :=
  S5_107.listWordOfCons

/-! ## Common seven-law envelope calculus -/

/-- Delete a middle occurrence from three separated occurrences of one
nonempty block. -/
theorem derivesThirdOccurrenceDeletion
    (u v z : Word Nat) :
    Derives basis
      ((((u ++ v) ++ u) ++ z) ++ u)
      (((u ++ v) ++ z) ++ u) := by
  have first :=
    derivesClosedInteriorSwap u v (u ++ z)
  have second :=
    (derivesLeftEndpointExpansion u (z ++ v)).symm
  have third :=
    derivesClosedInteriorSwap u z v
  have firstAligned :
      Derives basis
        ((((u ++ v) ++ u) ++ z) ++ u)
        ((((u ++ u) ++ z) ++ v) ++ u) := by
    simpa [Word.append_assoc] using first
  have secondAligned :
      Derives basis
        ((((u ++ u) ++ z) ++ v) ++ u)
        (((u ++ z) ++ v) ++ u) := by
    simpa [Word.append_assoc] using second
  have thirdAligned :
      Derives basis
        (((u ++ z) ++ v) ++ u)
        (((u ++ v) ++ z) ++ u) := by
    simpa [Word.append_assoc] using third
  exact firstAligned.trans (secondAligned.trans thirdAligned)

/-- Swap two possibly empty list blocks inside matching endpoints. -/
theorem listDerivesInteriorSwap
    (endpoint : Nat) (left right : List Nat) :
    ListDerives
      (endpoint :: left ++ right ++ [endpoint])
      (endpoint :: right ++ left ++ [endpoint]) := by
  cases left with
  | nil =>
      simpa [List.append_assoc] using
        (S5_107.ListDerives.refl (basis := basis)
          (endpoint :: right ++ [endpoint]))
  | cons leftHead leftTail =>
      cases right with
      | nil =>
          simpa [List.append_assoc] using
            (S5_107.ListDerives.refl (basis := basis)
              (endpoint :: leftHead :: leftTail ++ [endpoint]))
      | cons rightHead rightTail =>
          exact S5_107.ListDerives.words <| by
            simpa [listWordOfCons, Word.singleton, Word.append,
              Word.append_assoc, List.append_assoc] using
                derivesClosedInteriorSwap
                  (Word.singleton endpoint)
                  (listWordOfCons leftHead leftTail)
                  (listWordOfCons rightHead rightTail)

/-- Delete the middle of three displayed occurrences, including every
empty/nonempty combination of the two intervening gaps. -/
theorem listDerivesDeleteMiddleCore
    (letter : Nat) (left right : List Nat) :
    ListDerives
      ([letter] ++ left ++ [letter] ++ right ++ [letter])
      ([letter] ++ left ++ right ++ [letter]) := by
  cases left with
  | nil =>
      cases right with
      | nil =>
          exact S5_107.ListDerives.words <| by
            simpa [listWordOfCons, Word.singleton, Word.append,
              Word.append_assoc, List.append_assoc] using
                (derivesPowerExpansion (Word.singleton letter)).symm
      | cons rightHead rightTail =>
          exact S5_107.ListDerives.words <| by
            simpa [listWordOfCons, Word.singleton, Word.append,
              Word.append_assoc, List.append_assoc] using
                (derivesLeftEndpointExpansion
                  (Word.singleton letter)
                  (listWordOfCons rightHead rightTail)).symm
  | cons leftHead leftTail =>
      cases right with
      | nil =>
          exact S5_107.ListDerives.words <| by
            simpa [listWordOfCons, Word.singleton, Word.append,
              Word.append_assoc, List.append_assoc] using
                (derivesRightEndpointExpansion
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

/-- Delete another endpoint occurrence from an unprocessed suffix. -/
theorem listDerivesEndpointAbsorption
    (endpoint : Nat) (interior before after : List Nat) :
    ListDerives
      (endpoint :: interior ++ endpoint :: before ++ endpoint :: after)
      (endpoint :: (interior ++ before) ++ endpoint :: after) := by
  simpa [List.append_assoc] using
    (listDerivesDeleteMiddleCore endpoint interior before).append after

/-- Lift an interior derivation past one fixed interior letter. -/
theorem listDerivesInteriorCons
    (endpoint letter : Nat) (suffix : List Nat)
    {left right : List Nat}
    (derivation :
      ListDerives
        (endpoint :: left ++ endpoint :: suffix)
        (endpoint :: right ++ endpoint :: suffix)) :
    ListDerives
      (endpoint :: letter :: left ++ endpoint :: suffix)
      (endpoint :: letter :: right ++ endpoint :: suffix) := by
  have first :
      ListDerives
        (endpoint :: letter :: left ++ endpoint :: suffix)
        (endpoint :: letter :: endpoint :: left ++ endpoint :: suffix) := by
    simpa [List.append_assoc] using
      ((listDerivesDeleteMiddleCore endpoint [letter] left).symm).append
        suffix
  have second :
      ListDerives
        (endpoint :: letter :: endpoint :: left ++ endpoint :: suffix)
        (endpoint :: letter :: endpoint :: right ++ endpoint :: suffix) := by
    simpa [List.append_assoc] using
      derivation.prepend [endpoint, letter]
  have third :
      ListDerives
        (endpoint :: letter :: endpoint :: right ++ endpoint :: suffix)
        (endpoint :: letter :: right ++ endpoint :: suffix) := by
    simpa [List.append_assoc] using
      (listDerivesDeleteMiddleCore endpoint [letter] right).append suffix
  exact first.trans (second.trans third)

private theorem listDerivesSwapFirstInterior
    (endpoint first second : Nat) (rest suffix : List Nat) :
    ListDerives
      (endpoint :: first :: second :: rest ++ endpoint :: suffix)
      (endpoint :: second :: first :: rest ++ endpoint :: suffix) := by
  cases rest with
  | nil =>
      have core :=
        listDerivesInteriorSwap endpoint [first] [second]
      simpa [List.append_assoc] using core.append suffix
  | cons restHead restTail =>
      let restWord := listWordOfCons restHead restTail
      have firstStep :=
        (derivesThirdOccurrenceDeletion
          (Word.singleton endpoint)
          (Word.singleton first ++ Word.singleton second)
          restWord).symm
      have secondStep :=
        Derives.appendRight
          (derivesClosedInteriorSwap
            (Word.singleton endpoint)
            (Word.singleton first) (Word.singleton second))
          (restWord ++ Word.singleton endpoint)
      have thirdStep :=
        derivesThirdOccurrenceDeletion
          (Word.singleton endpoint)
          (Word.singleton second ++ Word.singleton first)
          restWord
      have firstAligned :
          Derives basis
            (((((Word.singleton endpoint ++ Word.singleton first) ++
              Word.singleton second) ++ restWord) ++
              Word.singleton endpoint))
            ((((((Word.singleton endpoint ++ Word.singleton first) ++
              Word.singleton second) ++ Word.singleton endpoint) ++
              restWord) ++ Word.singleton endpoint)) := by
        simpa [Word.append_assoc] using firstStep
      have secondAligned :
          Derives basis
            ((((((Word.singleton endpoint ++ Word.singleton first) ++
              Word.singleton second) ++ Word.singleton endpoint) ++
              restWord) ++ Word.singleton endpoint))
            ((((((Word.singleton endpoint ++ Word.singleton second) ++
              Word.singleton first) ++ Word.singleton endpoint) ++
              restWord) ++ Word.singleton endpoint)) := by
        simpa [Word.append_assoc] using secondStep
      have thirdAligned :
          Derives basis
            ((((((Word.singleton endpoint ++ Word.singleton second) ++
              Word.singleton first) ++ Word.singleton endpoint) ++
              restWord) ++ Word.singleton endpoint))
            (((((Word.singleton endpoint ++ Word.singleton second) ++
              Word.singleton first) ++ restWord) ++
              Word.singleton endpoint)) := by
        simpa [Word.append_assoc] using thirdStep
      have core :
          ListDerives
            (endpoint :: first :: second :: restHead :: restTail ++
              [endpoint])
            (endpoint :: second :: first :: restHead :: restTail ++
              [endpoint]) :=
        S5_107.ListDerives.words <| by
          simpa [restWord, listWordOfCons, Word.singleton,
            Word.append, Word.append_assoc, List.append_assoc] using
              firstAligned.trans (secondAligned.trans thirdAligned)
      simpa [List.append_assoc] using core.append suffix

/-- Any permutation of an envelope interior is derivable while preserving
an arbitrary suffix after its closing endpoint. -/
theorem listDerivesInteriorPermutation
    (endpoint : Nat) (suffix : List Nat)
    {left right : List Nat} (permutation : left.Perm right) :
    ListDerives
      (endpoint :: left ++ endpoint :: suffix)
      (endpoint :: right ++ endpoint :: suffix) := by
  induction permutation with
  | nil =>
      exact S5_107.ListDerives.refl _
  | cons letter _ induction =>
      exact listDerivesInteriorCons endpoint letter suffix induction
  | swap first second rest =>
      exact listDerivesSwapFirstInterior
        endpoint second first rest suffix
  | trans _ _ first second =>
      exact first.trans second

/-! ## Quantified eighth-law absorption -/

/-- The eighth law contracts `y x y Z x` to `x y Z x`. The empty `Z`
branch is supplied by the fifth law, so no empty semigroup substitution is
used. An arbitrary right context is preserved. -/
theorem listDerivesEighthLawAbsorption
    (endpoint crossing : Nat) (middle after : List Nat) :
    ListDerives
      (crossing :: endpoint :: crossing :: middle ++ endpoint :: after)
      (endpoint :: crossing :: middle ++ endpoint :: after) := by
  cases middle with
  | nil =>
      have core :=
        (derivesPrefixedSandwich
          (Word.singleton endpoint) (Word.singleton crossing)).symm
      have listed :
          ListDerives
            [crossing, endpoint, crossing, endpoint]
            [endpoint, crossing, endpoint] :=
        S5_107.ListDerives.words <| by
          simpa [listWordOfCons, Word.singleton, Word.append,
            Word.append_assoc] using core
      simpa [List.append_assoc] using listed.append after
  | cons middleHead middleTail =>
      have core :=
        (derivesEighthLawAbsorption
          (Word.singleton endpoint) (Word.singleton crossing)
          (listWordOfCons middleHead middleTail)).symm
      have listed :
          ListDerives
            (crossing :: endpoint :: crossing :: middleHead ::
              middleTail ++ [endpoint])
            (endpoint :: crossing :: middleHead :: middleTail ++
              [endpoint]) :=
        S5_107.ListDerives.words <| by
          simpa [listWordOfCons, Word.singleton, Word.append,
            Word.append_assoc, List.append_assoc] using core
      simpa [List.append_assoc] using listed.append after

private theorem count_rearrangement
    (before middle : List Nat) (endpoint tested : Nat) :
    (before ++ endpoint :: middle).count tested =
      (endpoint :: before ++ middle).count tested := by
  simp [List.count_append, List.count_cons, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm]

private theorem count_crossing_front
    (before middle : List Nat) (crossing tested : Nat) :
    (before ++ middle ++ [crossing]).count tested =
      (crossing :: before ++ middle).count tested := by
  simp [List.count_append, List.count_cons, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm]

/-- Absorb a crossing interval while retaining the actual right endpoint.
All three filler lists may be empty. The proof first permutes the two active
envelopes, applies the quantified eighth-law contraction, and restores the
interior order. -/
theorem listDerivesRightCrossingAbsorption
    (endpoint crossing : Nat)
    (before middle after : List Nat) :
    ListDerives
      (crossing :: before ++ endpoint :: middle ++ crossing ::
        endpoint :: after)
      (endpoint :: before ++ middle ++ crossing :: endpoint :: after) := by
  have moveEndpoint :
      (before ++ endpoint :: middle).Perm
        (endpoint :: before ++ middle) := by
    rw [List.perm_iff_count]
    exact count_rearrangement before middle endpoint
  have firstCore :=
    listDerivesInteriorPermutation crossing (endpoint :: after)
      moveEndpoint
  have first :
      ListDerives
        (crossing :: before ++ endpoint :: middle ++ crossing ::
          endpoint :: after)
        (crossing :: endpoint :: before ++ middle ++ crossing ::
          endpoint :: after) := by
    simpa [List.append_assoc] using firstCore
  have moveCrossing :
      (before ++ middle ++ [crossing]).Perm
        (crossing :: before ++ middle) := by
    rw [List.perm_iff_count]
    exact count_crossing_front before middle crossing
  have secondCore :=
    listDerivesInteriorPermutation endpoint after moveCrossing
  have second :
      ListDerives
        (crossing :: endpoint :: before ++ middle ++ crossing ::
          endpoint :: after)
        (crossing :: endpoint :: crossing :: before ++ middle ++
          endpoint :: after) := by
    simpa [List.append_assoc] using secondCore.prepend [crossing]
  have third :=
    listDerivesEighthLawAbsorption endpoint crossing
      (before ++ middle) after
  have restore :
      (crossing :: before ++ middle).Perm
        (before ++ middle ++ [crossing]) :=
    moveCrossing.symm
  have fourth :=
    listDerivesInteriorPermutation endpoint after restore
  exact first.trans <| second.trans <| third.trans <| by
    simpa [List.append_assoc] using fourth

end SemigroupBasis.CoRoots.S5_804
