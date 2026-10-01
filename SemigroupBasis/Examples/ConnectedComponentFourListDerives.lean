import SemigroupBasis.Examples.ConnectedComponentFour
import SemigroupBasis.Examples.UniqueSeparatorFourNormalForm

namespace SemigroupBasis.Examples

open SemigroupBasis

/-- The nonempty word represented by a head and tail list. -/
def connectedComponentWordOfCons (head : Nat) (tail : List Nat) :
    Word Nat :=
  ⟨head, tail⟩

/-- List-level derivability. The empty list is related only to itself;
nonempty lists carry a derivation from the `S4_70` basis. -/
inductive ConnectedComponentListDerives :
    List Nat → List Nat → Prop
  | empty : ConnectedComponentListDerives [] []
  | words {leftHead rightHead : Nat}
      {leftTail rightTail : List Nat} :
      Derives connectedComponentFourBasis
          (connectedComponentWordOfCons leftHead leftTail)
          (connectedComponentWordOfCons rightHead rightTail) →
        ConnectedComponentListDerives
          (leftHead :: leftTail) (rightHead :: rightTail)

namespace ConnectedComponentListDerives

theorem refl :
    ∀ letters : List Nat,
      ConnectedComponentListDerives letters letters
  | [] => .empty
  | _ :: _ => .words (Derives.refl _)

theorem symm {left right : List Nat}
    (derivation : ConnectedComponentListDerives left right) :
    ConnectedComponentListDerives right left := by
  cases derivation with
  | empty =>
      exact .empty
  | words wordDerivation =>
      exact .words wordDerivation.symm

theorem trans {left middle right : List Nat}
    (first : ConnectedComponentListDerives left middle)
    (second : ConnectedComponentListDerives middle right) :
    ConnectedComponentListDerives left right := by
  cases first with
  | empty =>
      cases second
      exact .empty
  | words firstWord =>
      cases second with
      | words secondWord =>
          exact .words (firstWord.trans secondWord)

theorem prepend (pre : List Nat) {left right : List Nat}
    (derivation : ConnectedComponentListDerives left right) :
    ConnectedComponentListDerives
      (pre ++ left) (pre ++ right) := by
  cases pre with
  | nil =>
      simpa using derivation
  | cons head tail =>
      cases derivation with
      | empty =>
          simpa using refl (head :: tail)
      | @words leftHead rightHead leftTail rightTail wordDerivation =>
          exact .words <| by
            have prefixed :=
              Derives.prepend
                (connectedComponentWordOfCons head tail)
                wordDerivation
            simpa [connectedComponentWordOfCons, Word.append,
              List.append_assoc] using prefixed

theorem append {left right : List Nat}
    (derivation : ConnectedComponentListDerives left right)
    (suffix : List Nat) :
    ConnectedComponentListDerives
      (left ++ suffix) (right ++ suffix) := by
  cases derivation with
  | empty =>
      simpa using refl suffix
  | @words leftHead rightHead leftTail rightTail wordDerivation =>
      cases suffix with
      | nil =>
          simpa using
            (ConnectedComponentListDerives.words wordDerivation)
      | cons head tail =>
          exact .words <| by
            have appended :=
              Derives.appendRight wordDerivation
                (connectedComponentWordOfCons head tail)
            simpa [connectedComponentWordOfCons, Word.append,
              List.append_assoc] using appended

theorem context (pre suffix : List Nat)
    {left right : List Nat}
    (derivation : ConnectedComponentListDerives left right) :
    ConnectedComponentListDerives
      (pre ++ left ++ suffix)
      (pre ++ right ++ suffix) := by
  simpa [List.append_assoc] using
    (derivation.prepend pre).append suffix

theorem ofWord {left right : Word Nat}
    (derivation :
      Derives connectedComponentFourBasis left right) :
    ConnectedComponentListDerives left.toList right.toList := by
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail =>
          exact .words derivation

theorem toWord {leftHead rightHead : Nat}
    {leftTail rightTail : List Nat}
    (derivation :
      ConnectedComponentListDerives
        (leftHead :: leftTail) (rightHead :: rightTail)) :
    Derives connectedComponentFourBasis
      (connectedComponentWordOfCons leftHead leftTail)
      (connectedComponentWordOfCons rightHead rightTail) := by
  cases derivation with
  | words wordDerivation =>
      exact wordDerivation

theorem from_cons {leftHead : Nat} {leftTail target : List Nat}
    (derivation :
      ConnectedComponentListDerives
        (leftHead :: leftTail) target) :
    ∃ rightHead rightTail,
      target = rightHead :: rightTail ∧
        Derives connectedComponentFourBasis
          (connectedComponentWordOfCons leftHead leftTail)
          (connectedComponentWordOfCons rightHead rightTail) := by
  cases derivation with
  | words wordDerivation =>
      exact ⟨_, _, rfl, wordDerivation⟩

theorem target_ne_nil {leftHead : Nat} {leftTail target : List Nat}
    (derivation :
      ConnectedComponentListDerives
        (leftHead :: leftTail) target) :
    target ≠ [] := by
  obtain ⟨rightHead, rightTail, rfl, _⟩ :=
    from_cons derivation
  simp

end ConnectedComponentListDerives

/-- Swap two possibly empty blocks inside matching singleton endpoints. -/
theorem connectedComponentListDerivesInteriorSwap
    (x : Nat) (left right : List Nat) :
    ConnectedComponentListDerives
      ([x] ++ left ++ right ++ [x])
      ([x] ++ right ++ left ++ [x]) := by
  cases left with
  | nil =>
      simpa [List.append_assoc] using
        ConnectedComponentListDerives.refl
          ([x] ++ right ++ [x])
  | cons leftHead leftTail =>
      cases right with
      | nil =>
          simpa [List.append_assoc] using
            ConnectedComponentListDerives.refl
              ([x] ++ leftHead :: leftTail ++ [x])
      | cons rightHead rightTail =>
          exact ConnectedComponentListDerives.words <| by
            simpa [connectedComponentWordOfCons, Word.singleton,
              Word.append, Word.append_assoc, List.append_assoc] using
              connectedComponentDerivesInteriorSwap
                (Word.singleton x)
                (connectedComponentWordOfCons leftHead leftTail)
                (connectedComponentWordOfCons rightHead rightTail)

/-- Absorb a crossing pair for all four empty/nonempty filler cases:
`xy z x u y = xy z u x`. -/
theorem connectedComponentListDerivesCrossing
    (x y : Nat) (z u : List Nat) :
    ConnectedComponentListDerives
      ([x, y] ++ z ++ [x] ++ u ++ [y])
      ([x, y] ++ z ++ u ++ [x]) := by
  cases z with
  | nil =>
      cases u with
      | nil =>
          exact ConnectedComponentListDerives.words <| by
            simpa [connectedComponentWordOfCons, Word.singleton,
              Word.append, Word.append_assoc, List.append_assoc] using
              (Derives.symm <|
                connectedComponentDerivesAlternating
                  (Word.singleton x) (Word.singleton y))
      | cons uHead uTail =>
          exact ConnectedComponentListDerives.words <| by
            simpa [connectedComponentWordOfCons, Word.singleton,
              Word.append, Word.append_assoc, List.append_assoc] using
              connectedComponentDerivesShortCrossing
                (Word.singleton x) (Word.singleton y)
                (connectedComponentWordOfCons uHead uTail)
  | cons zHead zTail =>
      cases u with
      | nil =>
          exact ConnectedComponentListDerives.words <| by
            have first :=
              Derives.prepend (Word.singleton x) <|
                connectedComponentDerivesInteriorSwap
                  (Word.singleton y)
                  (connectedComponentWordOfCons zHead zTail)
                  (Word.singleton x)
            have second :=
              connectedComponentDerivesShortCrossing
                (Word.singleton x) (Word.singleton y)
                (connectedComponentWordOfCons zHead zTail)
            exact Derives.trans
              (by simpa [connectedComponentWordOfCons, Word.singleton,
                Word.append, Word.append_assoc, List.append_assoc] using
                  first)
              (by simpa [connectedComponentWordOfCons, Word.singleton,
                Word.append, Word.append_assoc, List.append_assoc] using
                  second)
      | cons uHead uTail =>
          exact ConnectedComponentListDerives.words <| by
            simpa [connectedComponentWordOfCons, Word.singleton,
              Word.append, Word.append_assoc, List.append_assoc] using
              connectedComponentDerivesCrossing
                (Word.singleton x) (Word.singleton y)
                (connectedComponentWordOfCons zHead zTail)
                (connectedComponentWordOfCons uHead uTail)

/-- Delete the middle of three occurrences of `x`, including the cases where
one or both intervening gaps are empty. -/
theorem connectedComponentDeleteMiddleCore
    (x : Nat) (left right : List Nat) :
    ConnectedComponentListDerives
      ([x] ++ left ++ [x] ++ right ++ [x])
      ([x] ++ left ++ right ++ [x]) := by
  cases left with
  | nil =>
      cases right with
      | nil =>
          exact ConnectedComponentListDerives.words <| by
            simpa [connectedComponentWordOfCons, Word.singleton,
              Word.append, Word.append_assoc, List.append_assoc] using
              (connectedComponentDerivesPowerExpansion
                (Word.singleton x)).symm
      | cons y ys =>
          exact ConnectedComponentListDerives.words <| by
            simpa [connectedComponentWordOfCons, Word.singleton,
              Word.append, Word.append_assoc, List.append_assoc] using
              (connectedComponentDerivesLeftDuplication
                (Word.singleton x)
                (connectedComponentWordOfCons y ys)).symm
  | cons y ys =>
      cases right with
      | nil =>
          exact ConnectedComponentListDerives.words <| by
            simpa [connectedComponentWordOfCons, Word.singleton,
              Word.append, Word.append_assoc, List.append_assoc] using
              (connectedComponentDerivesRightDuplication
                (Word.singleton x)
                (connectedComponentWordOfCons y ys)).symm
      | cons z zs =>
          exact ConnectedComponentListDerives.words <| by
            simpa [connectedComponentWordOfCons, Word.singleton,
              Word.append, Word.append_assoc, List.append_assoc] using
              connectedComponentDerivesThirdOccurrenceDeletion
                (Word.singleton x)
                (connectedComponentWordOfCons y ys)
                (connectedComponentWordOfCons z zs)

/-- Absorb another occurrence of the current endpoint from the unprocessed
suffix into the endpoint envelope. -/
theorem connectedComponentListDerivesEndpointAbsorption
    (endpoint : Nat) (interior before after : List Nat) :
    ConnectedComponentListDerives
      (endpoint :: interior ++ endpoint :: before ++ endpoint :: after)
      (endpoint :: (interior ++ before) ++ endpoint :: after) := by
  simpa [List.append_assoc] using
    (connectedComponentDeleteMiddleCore
      endpoint interior before).append after

/-- Contract two adjacent copies of an interior letter while preserving the
outer endpoint and an arbitrary suffix. -/
theorem connectedComponentListDerivesInteriorContractionContext
    (endpoint repeated : Nat)
    (left right suffix : List Nat) :
    ConnectedComponentListDerives
      (endpoint :: left ++ repeated :: repeated :: right ++
        endpoint :: suffix)
      (endpoint :: left ++ repeated :: right ++ endpoint :: suffix) := by
  cases left with
  | nil =>
      cases right with
      | nil =>
          have core :=
            connectedComponentDerivesMiddleContraction
              (Word.singleton endpoint) (Word.singleton repeated)
          have coreList :
              ConnectedComponentListDerives
                [endpoint, repeated, repeated, endpoint]
                [endpoint, repeated, endpoint] :=
            ConnectedComponentListDerives.words <| by
            simpa [connectedComponentWordOfCons, Word.singleton,
              Word.append, Word.append_assoc, List.append_assoc] using core
          simpa [List.append_assoc] using coreList.append suffix
      | cons rightHead rightTail =>
          have core :=
            connectedComponentDerivesLeftInteriorContraction
              (Word.singleton endpoint) (Word.singleton repeated)
              (connectedComponentWordOfCons rightHead rightTail)
          have coreList :
              ConnectedComponentListDerives
                (endpoint :: repeated :: repeated ::
                  rightHead :: rightTail ++ [endpoint])
                (endpoint :: repeated ::
                  rightHead :: rightTail ++ [endpoint]) :=
            ConnectedComponentListDerives.words <| by
            simpa [connectedComponentWordOfCons, Word.singleton,
              Word.append, Word.append_assoc, List.append_assoc] using core
          simpa [List.append_assoc] using coreList.append suffix
  | cons leftHead leftTail =>
      cases right with
      | nil =>
          have core :=
            connectedComponentDerivesRightInteriorContraction
              (Word.singleton endpoint)
              (connectedComponentWordOfCons leftHead leftTail)
              (Word.singleton repeated)
          have coreList :
              ConnectedComponentListDerives
                (endpoint :: leftHead :: leftTail ++
                  repeated :: repeated :: [endpoint])
                (endpoint :: leftHead :: leftTail ++
                  repeated :: [endpoint]) :=
            ConnectedComponentListDerives.words <| by
            simpa [connectedComponentWordOfCons, Word.singleton,
              Word.append, Word.append_assoc, List.append_assoc] using core
          simpa [List.append_assoc] using coreList.append suffix
      | cons rightHead rightTail =>
          have core :=
            connectedComponentDerivesInteriorContraction
              (Word.singleton endpoint)
              (connectedComponentWordOfCons leftHead leftTail)
              (Word.singleton repeated)
              (connectedComponentWordOfCons rightHead rightTail)
          have coreList :
              ConnectedComponentListDerives
                (endpoint :: leftHead :: leftTail ++
                  repeated :: repeated ::
                  rightHead :: rightTail ++ [endpoint])
                (endpoint :: leftHead :: leftTail ++ repeated ::
                  rightHead :: rightTail ++ [endpoint]) :=
            ConnectedComponentListDerives.words <| by
            simpa [connectedComponentWordOfCons, Word.singleton,
              Word.append, Word.append_assoc, List.append_assoc] using core
          simpa [List.append_assoc] using coreList.append suffix

/-- Switch an envelope from `oldEndpoint` to a doubled interior
`newEndpoint`, preserving an arbitrary suffix. -/
theorem connectedComponentListDerivesEndpointSwitchContext
    (oldEndpoint newEndpoint : Nat)
    (middle suffix : List Nat) :
    ConnectedComponentListDerives
      (oldEndpoint :: newEndpoint :: newEndpoint :: middle ++
        oldEndpoint :: suffix)
      (newEndpoint :: oldEndpoint :: oldEndpoint :: middle ++
        newEndpoint :: suffix) := by
  cases middle with
  | nil =>
      have core :=
        connectedComponentDerivesShortEndpointSwitch
          (Word.singleton oldEndpoint) (Word.singleton newEndpoint)
      have coreList :
          ConnectedComponentListDerives
            [oldEndpoint, newEndpoint, newEndpoint, oldEndpoint]
            [newEndpoint, oldEndpoint, oldEndpoint, newEndpoint] :=
        ConnectedComponentListDerives.words <| by
        simpa [connectedComponentWordOfCons, Word.singleton,
          Word.append, Word.append_assoc, List.append_assoc] using core
      simpa [List.append_assoc] using coreList.append suffix
  | cons middleHead middleTail =>
      have core :=
        connectedComponentDerivesEndpointSwitch
          (Word.singleton oldEndpoint) (Word.singleton newEndpoint)
          (connectedComponentWordOfCons middleHead middleTail)
      have coreList :
          ConnectedComponentListDerives
            (oldEndpoint :: newEndpoint :: newEndpoint ::
              middleHead :: middleTail ++ [oldEndpoint])
            (newEndpoint :: oldEndpoint :: oldEndpoint ::
              middleHead :: middleTail ++ [newEndpoint]) :=
        ConnectedComponentListDerives.words <| by
        simpa [connectedComponentWordOfCons, Word.singleton,
          Word.append, Word.append_assoc, List.append_assoc] using core
      simpa [List.append_assoc] using coreList.append suffix

/-- Swap the first two letters of an envelope interior while preserving the
rest of the interior and everything after the closing endpoint. -/
private theorem connectedComponentListDerivesSwapFirstInterior
    (endpoint first second : Nat)
    (rest suffix : List Nat) :
    ConnectedComponentListDerives
      (endpoint :: first :: second :: rest ++ endpoint :: suffix)
      (endpoint :: second :: first :: rest ++ endpoint :: suffix) := by
  cases rest with
  | nil =>
      have core :
          ConnectedComponentListDerives
            [endpoint, first, second, endpoint]
            [endpoint, second, first, endpoint] :=
        ConnectedComponentListDerives.words <| by
          simpa [connectedComponentWordOfCons, Word.singleton,
            Word.append, Word.append_assoc] using
              connectedComponentDerivesInteriorSwap
                (Word.singleton endpoint)
                (Word.singleton first) (Word.singleton second)
      simpa [List.append_assoc] using core.append suffix
  | cons restHead restTail =>
      let restWord :=
        connectedComponentWordOfCons restHead restTail
      have firstStep :=
        Derives.symm <|
          connectedComponentDerivesThirdOccurrenceDeletion
            (Word.singleton endpoint)
            (Word.singleton first ++ Word.singleton second)
            restWord
      have secondStep :=
        Derives.appendRight
          (connectedComponentDerivesInteriorSwap
            (Word.singleton endpoint)
            (Word.singleton first) (Word.singleton second))
          (restWord ++ Word.singleton endpoint)
      have thirdStep :=
        connectedComponentDerivesThirdOccurrenceDeletion
          (Word.singleton endpoint)
          (Word.singleton second ++ Word.singleton first)
          restWord
      have core :
          ConnectedComponentListDerives
            (endpoint :: first :: second ::
              restHead :: restTail ++ [endpoint])
            (endpoint :: second :: first ::
              restHead :: restTail ++ [endpoint]) :=
        ConnectedComponentListDerives.words <| by
          exact Derives.trans
            (by simpa [restWord, connectedComponentWordOfCons,
              Word.singleton, Word.append, Word.append_assoc,
              List.append_assoc] using firstStep) <|
            Derives.trans
              (by simpa [restWord, connectedComponentWordOfCons,
                Word.singleton, Word.append, Word.append_assoc,
                List.append_assoc] using secondStep)
              (by simpa [restWord, connectedComponentWordOfCons,
                Word.singleton, Word.append, Word.append_assoc,
                List.append_assoc] using thirdStep)
      simpa [List.append_assoc] using core.append suffix

/-- Lift an interior derivation past one fixed leading interior letter. -/
theorem connectedComponentListDerivesInteriorCons
    (endpoint letter : Nat) (suffix : List Nat)
    {left right : List Nat}
    (derivation :
      ConnectedComponentListDerives
        (endpoint :: left ++ endpoint :: suffix)
        (endpoint :: right ++ endpoint :: suffix)) :
    ConnectedComponentListDerives
      (endpoint :: letter :: left ++ endpoint :: suffix)
      (endpoint :: letter :: right ++ endpoint :: suffix) := by
  have first :
      ConnectedComponentListDerives
        (endpoint :: letter :: left ++ endpoint :: suffix)
        (endpoint :: letter :: endpoint ::
          left ++ endpoint :: suffix) := by
    simpa [List.append_assoc] using
      ((connectedComponentDeleteMiddleCore
        endpoint [letter] left).symm).append suffix
  have second :
      ConnectedComponentListDerives
        (endpoint :: letter :: endpoint ::
          left ++ endpoint :: suffix)
        (endpoint :: letter :: endpoint ::
          right ++ endpoint :: suffix) := by
    simpa [List.append_assoc] using
      derivation.prepend [endpoint, letter]
  have third :
      ConnectedComponentListDerives
        (endpoint :: letter :: endpoint ::
          right ++ endpoint :: suffix)
        (endpoint :: letter :: right ++ endpoint :: suffix) := by
    simpa [List.append_assoc] using
      (connectedComponentDeleteMiddleCore
        endpoint [letter] right).append suffix
  exact first.trans (second.trans third)

/-- Any permutation of an envelope interior is derivable while preserving
the matching endpoint and an arbitrary suffix after it. -/
theorem connectedComponentListDerivesInteriorPermutationContext
    (endpoint : Nat) (suffix : List Nat)
    {left right : List Nat}
    (permutation : left.Perm right) :
    ConnectedComponentListDerives
      (endpoint :: left ++ endpoint :: suffix)
      (endpoint :: right ++ endpoint :: suffix) := by
  induction permutation with
  | nil =>
      exact ConnectedComponentListDerives.refl _
  | cons letter _ ih =>
      exact connectedComponentListDerivesInteriorCons
        endpoint letter suffix ih
  | swap first second rest =>
      exact connectedComponentListDerivesSwapFirstInterior
        endpoint second first rest suffix
  | trans _ _ first second =>
      exact first.trans second

/-- Any permutation of the interior between matching endpoints is
derivable. -/
theorem connectedComponentListDerivesInteriorPermutation
    (endpoint : Nat) {left right : List Nat}
    (permutation : left.Perm right) :
    ConnectedComponentListDerives
      ([endpoint] ++ left ++ [endpoint])
      ([endpoint] ++ right ++ [endpoint]) := by
  simpa [List.append_assoc] using
    connectedComponentListDerivesInteriorPermutationContext
      endpoint [] permutation

/-- If `x` occurs in both a processed prefix and the remaining suffix, then
the current occurrence between them may be deleted. -/
private theorem connectedComponentDeleteCurrent
    (pre suffix : List Nat) (x : Nat)
    (past : x ∈ pre) (future : x ∈ suffix) :
    ConnectedComponentListDerives
      (pre ++ x :: suffix) (pre ++ suffix) := by
  rcases List.append_of_mem past with
    ⟨before, left, preShape⟩
  rcases List.append_of_mem future with
    ⟨right, after, suffixShape⟩
  rw [preShape, suffixShape]
  simpa [List.append_assoc] using
    (connectedComponentDeleteMiddleCore x left right).context
      before after

/-- The scanner cap is derivable whenever every letter recorded in `seen`
already occurs in the fixed processed prefix. -/
private theorem connectedComponentEndpointCapAux_derives
    (pre seen : List Nat)
    (seenInPre : ∀ z ∈ seen, z ∈ pre) :
    ∀ suffix : List Nat,
      ConnectedComponentListDerives
        (pre ++ suffix)
        (pre ++ uniqueSeparatorEndpointCapAux seen suffix)
  | [] => by
      simpa using ConnectedComponentListDerives.refl pre
  | x :: xs => by
      by_cases middle : x ∈ seen ∧ x ∈ xs
      · have xInPre : x ∈ pre :=
          seenInPre x middle.1
        have deleteCurrent :
            ConnectedComponentListDerives
              (pre ++ x :: xs) (pre ++ xs) :=
          connectedComponentDeleteCurrent pre xs x xInPre middle.2
        have nextSeenInPre :
            ∀ z ∈ x :: seen, z ∈ pre := by
          intro z hz
          rcases List.mem_cons.mp hz with rfl | hz
          · exact xInPre
          · exact seenInPre z hz
        have recurse :=
          connectedComponentEndpointCapAux_derives
            pre (x :: seen) nextSeenInPre xs
        rw [uniqueSeparatorEndpointCapAux, if_pos middle]
        exact deleteCurrent.trans recurse
      · have nextSeenInPre :
            ∀ z ∈ x :: seen, z ∈ pre ++ [x] := by
          intro z hz
          rcases List.mem_cons.mp hz with rfl | hz
          · exact List.mem_append_right pre (List.Mem.head [])
          · exact List.mem_append_left [x] (seenInPre z hz)
        have recurse :=
          connectedComponentEndpointCapAux_derives
            (pre ++ [x]) (x :: seen) nextSeenInPre xs
        rw [uniqueSeparatorEndpointCapAux, if_neg middle]
        simpa [List.append_assoc] using recurse

/-- Every word derives its deterministic endpoint cap under the `S4_70`
basis. The cap itself is the pure definition shared with
`UniqueSeparatorFourNormalForm`. -/
theorem connectedComponentEndpointCap_derives (xs : List Nat) :
    ConnectedComponentListDerives
      xs (uniqueSeparatorEndpointCap xs) := by
  simpa [uniqueSeparatorEndpointCap] using
    connectedComponentEndpointCapAux_derives
      [] [] (by simp) xs

end SemigroupBasis.Examples
