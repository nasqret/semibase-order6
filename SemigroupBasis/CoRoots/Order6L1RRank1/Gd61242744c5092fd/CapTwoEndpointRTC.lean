import SemigroupBasis.CoRoots.Order6L1RRank1.Gd61242744c5092fd.CapTwoContextualFrozen

/-!
# Direct RTC endpoint moves and inversion dispatchers

Every theorem in this module constructs the contextual symmetric RTC directly
from named frozen paths.  No displayed-law derivation is read backwards, and
no component-envelope module is imported.
-/

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6L1RRank1.Gd61242744c5092fd
namespace CapTwoRTCRoute

open SemigroupBasis

private abbrev listWordOfCons := S5_107.listWordOfCons

/-! ## Three-occurrence deletion from four exact path cases -/

/-- Delete the middle of three occurrences for arbitrary possibly empty gaps. -/
theorem frozenDeleteMiddleCore
    (letter : Nat) (leftGap rightGap : List Nat) :
    ContextualFrozenRTC
      ([letter] ++ leftGap ++ [letter] ++ rightGap ++ [letter])
      ([letter] ++ leftGap ++ rightGap ++ [letter]) := by
  cases leftGap with
  | nil =>
      cases rightGap with
      | nil =>
          simpa [listWordOfCons, Word.singleton, Word.append,
            Word.append_assoc, List.append_assoc] using
              contextualFrozenRTC_of_core
                (FrozenCoreStep.Path00000 (Word.singleton letter))
      | cons rightHead rightTail =>
          simpa [listWordOfCons, Word.singleton, Word.append,
            Word.append_assoc, List.append_assoc] using
              contextualFrozenRTC_of_core
                (FrozenCoreStep.Path00001
                  (Word.singleton letter)
                  (listWordOfCons rightHead rightTail))
  | cons leftHead leftTail =>
      cases rightGap with
      | nil =>
          simpa [listWordOfCons, Word.singleton, Word.append,
            Word.append_assoc, List.append_assoc] using
              contextualFrozenRTC_of_core
                (FrozenCoreStep.Path00002
                  (Word.singleton letter)
                  (listWordOfCons leftHead leftTail))
      | cons rightHead rightTail =>
          simpa [listWordOfCons, Word.singleton, Word.append,
            Word.append_assoc, List.append_assoc] using
              contextualFrozenRTC_of_core
                (FrozenCoreStep.Path00013
                  (Word.singleton letter)
                  (listWordOfCons leftHead leftTail)
                  (listWordOfCons rightHead rightTail))

/-! ## Retarget and alternating close -/

/-- Retarget `c e c M e` to `e c c M e` for an arbitrary middle. -/
private theorem frozenEndpointRetarget
    (crossing endpoint : Nat) (middle : List Nat) :
    ContextualFrozenRTC
      ([crossing, endpoint, crossing] ++ middle ++ [endpoint])
      ([endpoint, crossing, crossing] ++ middle ++ [endpoint]) := by
  cases middle with
  | nil =>
      simpa [listWordOfCons, Word.singleton, Word.append,
        Word.append_assoc, List.append_assoc] using
          (contextualFrozenRTC_of_core
            (FrozenCoreStep.Path00005
              (Word.singleton endpoint)
              (Word.singleton crossing))).symm
  | cons middleHead middleTail =>
      simpa [listWordOfCons, Word.singleton, Word.append,
        Word.append_assoc, List.append_assoc] using
          contextualFrozenRTC_of_core
            (FrozenCoreStep.Path00014
              (Word.singleton crossing)
              (Word.singleton endpoint)
              (listWordOfCons middleHead middleTail))

/-- Move an arbitrary list in the alternating law-008 pattern. -/
private theorem frozenLaw008Reverse
    (crossing endpoint : Nat) :
    ∀ before : List Nat,
      ContextualFrozenRTC
        ([crossing] ++ before ++ [endpoint, crossing, endpoint])
        ([crossing, endpoint] ++ before ++ [crossing, endpoint])
  | [] => .refl _
  | beforeHead :: beforeTail => by
      simpa [listWordOfCons, Word.singleton, Word.append,
        Word.append_assoc, List.append_assoc] using
          (contextualFrozenRTC_of_core
            (FrozenCoreStep.Path00018
              (Word.singleton crossing)
              (Word.singleton endpoint)
              (listWordOfCons beforeHead beforeTail))).symm

private theorem frozenCloseAlternating
    (crossing endpoint : Nat) (middle : List Nat) :
    ContextualFrozenRTC
      ([crossing, endpoint] ++ middle ++ [crossing, endpoint])
      ([endpoint, crossing] ++ middle ++ [crossing, endpoint]) := by
  have insertCrossing :
      ContextualFrozenRTC
        ([crossing, endpoint] ++ middle ++ [crossing, endpoint])
        ([crossing, endpoint, crossing] ++ middle ++
          [crossing, endpoint]) := by
    simpa [List.append_assoc] using
      ((frozenDeleteMiddleCore crossing [endpoint] middle).symm.context
        [] [endpoint])
  have retarget :
      ContextualFrozenRTC
        ([crossing, endpoint, crossing] ++ middle ++
          [crossing, endpoint])
        ([endpoint, crossing, crossing] ++ middle ++
          [crossing, endpoint]) := by
    simpa [List.append_assoc] using
      frozenEndpointRetarget crossing endpoint (middle ++ [crossing])
  have deleteCrossing :
      ContextualFrozenRTC
        ([endpoint, crossing, crossing] ++ middle ++
          [crossing, endpoint])
        ([endpoint, crossing] ++ middle ++ [crossing, endpoint]) := by
    simpa [List.append_assoc] using
      (frozenDeleteMiddleCore crossing [] middle).context
        [endpoint] [endpoint]
  exact insertCrossing.trans (retarget.trans deleteCrossing)

/-! ## Interleaving and nested E/F pulls -/

private theorem frozenPullEndpointCore
    (crossing endpoint : Nat) (before middle : List Nat) :
    ContextualFrozenRTC
      ([crossing] ++ before ++ [endpoint] ++ middle ++
        [crossing, endpoint])
      ([endpoint, crossing] ++ before ++ middle ++
        [crossing, endpoint]) := by
  have insertCrossing :
      ContextualFrozenRTC
        ([crossing] ++ before ++ [endpoint] ++ middle ++
          [crossing, endpoint])
        ([crossing] ++ before ++ [endpoint, crossing] ++ middle ++
          [crossing, endpoint]) := by
    simpa [List.append_assoc] using
      ((frozenDeleteMiddleCore crossing
        (before ++ [endpoint]) middle).symm.context [] [endpoint])
  have insertEndpoint :
      ContextualFrozenRTC
        ([crossing] ++ before ++ [endpoint, crossing] ++ middle ++
          [crossing, endpoint])
        ([crossing] ++ before ++ [endpoint, crossing, endpoint] ++
          middle ++ [crossing, endpoint]) := by
    simpa [List.append_assoc] using
      (frozenDeleteMiddleCore endpoint [crossing]
        (middle ++ [crossing])).symm.context
          ([crossing] ++ before) []
  have moveBefore :
      ContextualFrozenRTC
        ([crossing] ++ before ++ [endpoint, crossing, endpoint] ++
          middle ++ [crossing, endpoint])
        ([crossing, endpoint] ++ before ++ [crossing, endpoint] ++
          middle ++ [crossing, endpoint]) := by
    simpa [List.append_assoc] using
      (frozenLaw008Reverse crossing endpoint before).context
        [] (middle ++ [crossing, endpoint])
  have deleteCrossing :
      ContextualFrozenRTC
        ([crossing, endpoint] ++ before ++ [crossing, endpoint] ++
          middle ++ [crossing, endpoint])
        ([crossing, endpoint] ++ before ++ [endpoint] ++ middle ++
          [crossing, endpoint]) := by
    simpa [List.append_assoc] using
      (frozenDeleteMiddleCore crossing
        (endpoint :: before) (endpoint :: middle)).context [] [endpoint]
  have deleteEndpoint :
      ContextualFrozenRTC
        ([crossing, endpoint] ++ before ++ [endpoint] ++ middle ++
          [crossing, endpoint])
        ([crossing, endpoint] ++ before ++ middle ++
          [crossing, endpoint]) := by
    simpa [List.append_assoc] using
      (frozenDeleteMiddleCore endpoint before
        (middle ++ [crossing])).context [crossing] []
  have close :=
    frozenCloseAlternating crossing endpoint (before ++ middle)
  simpa [List.append_assoc] using
    insertCrossing.trans <| insertEndpoint.trans <| moveBefore.trans <|
      deleteCrossing.trans <| deleteEndpoint.trans close

/-- Interleaving order: `c P e M c Q e -> e c P M c Q e`. -/
theorem frozenPullEndpointCrossing
    (crossing endpoint : Nat)
    (before middle after : List Nat) :
    ContextualFrozenRTC
      ([crossing] ++ before ++ [endpoint] ++ middle ++
        [crossing] ++ after ++ [endpoint])
      ([endpoint, crossing] ++ before ++ middle ++
        [crossing] ++ after ++ [endpoint]) := by
  have insertEndpoint :
      ContextualFrozenRTC
        ([crossing] ++ before ++ [endpoint] ++ middle ++
          [crossing] ++ after ++ [endpoint])
        ([crossing] ++ before ++ [endpoint] ++ middle ++
          [crossing, endpoint] ++ after ++ [endpoint]) := by
    simpa [List.append_assoc] using
      (frozenDeleteMiddleCore endpoint
        (middle ++ [crossing]) after).symm.context
          ([crossing] ++ before) []
  have pullCore :
      ContextualFrozenRTC
        ([crossing] ++ before ++ [endpoint] ++ middle ++
          [crossing, endpoint] ++ after ++ [endpoint])
        ([endpoint, crossing] ++ before ++ middle ++
          [crossing, endpoint] ++ after ++ [endpoint]) := by
    simpa [List.append_assoc] using
      (frozenPullEndpointCore
        crossing endpoint before middle).context [] (after ++ [endpoint])
  have deleteEndpoint :
      ContextualFrozenRTC
        ([endpoint, crossing] ++ before ++ middle ++
          [crossing, endpoint] ++ after ++ [endpoint])
        ([endpoint, crossing] ++ before ++ middle ++
          [crossing] ++ after ++ [endpoint]) := by
    simpa [List.append_assoc] using
      frozenDeleteMiddleCore endpoint
        ([crossing] ++ before ++ middle ++ [crossing]) after
  exact insertEndpoint.trans (pullCore.trans deleteEndpoint)

/-- Nested order: `c P e M e Q c -> e c P M e Q c`. -/
theorem frozenPullEndpointNested
    (crossing endpoint : Nat)
    (before middle after : List Nat) :
    ContextualFrozenRTC
      ([crossing] ++ before ++ [endpoint] ++ middle ++
        [endpoint] ++ after ++ [crossing])
      ([endpoint, crossing] ++ before ++ middle ++
        [endpoint] ++ after ++ [crossing]) := by
  have insertCrossing :
      ContextualFrozenRTC
        ([crossing] ++ before ++ [endpoint] ++ middle ++
          [endpoint] ++ after ++ [crossing])
        ([crossing] ++ before ++ [endpoint] ++ middle ++
          [crossing, endpoint] ++ after ++ [crossing]) := by
    simpa [List.append_assoc] using
      (frozenDeleteMiddleCore crossing
        (before ++ [endpoint] ++ middle)
        ([endpoint] ++ after)).symm
  have pullCrossing :
      ContextualFrozenRTC
        ([crossing] ++ before ++ [endpoint] ++ middle ++
          [crossing, endpoint] ++ after ++ [crossing])
        ([endpoint, crossing] ++ before ++ middle ++
          [crossing, endpoint] ++ after ++ [crossing]) := by
    simpa [List.append_assoc] using
      (frozenPullEndpointCrossing crossing endpoint
        before middle []).context [] (after ++ [crossing])
  have deleteCrossing :
      ContextualFrozenRTC
        ([endpoint, crossing] ++ before ++ middle ++
          [crossing, endpoint] ++ after ++ [crossing])
        ([endpoint, crossing] ++ before ++ middle ++
          [endpoint] ++ after ++ [crossing]) := by
    simpa [List.append_assoc] using
      (frozenDeleteMiddleCore crossing
        (before ++ middle) ([endpoint] ++ after)).context [endpoint] []
  exact insertCrossing.trans (pullCrossing.trans deleteCrossing)

/-! ## Adjacent first-endpoint dispatchers -/

/-- Swap adjacent first endpoints when their later endpoints occur `x,y`. -/
theorem frozenSwapFirstLaterXY
    (x y : Nat) (gapA gapB : List Nat) :
    ContextualFrozenRTC
      ([x, y] ++ gapA ++ [x] ++ gapB ++ [y])
      ([y, x] ++ gapA ++ [x] ++ gapB ++ [y]) := by
  cases gapA with
  | nil =>
      cases gapB with
      | nil =>
          simpa [Word.singleton, Word.append, Word.append_assoc,
            List.append_assoc] using
              (contextualFrozenRTC_of_core
                (FrozenCoreStep.Path00005
                  (Word.singleton y) (Word.singleton x))).symm
      | cons gapBHead gapBTail =>
          simpa [listWordOfCons, Word.singleton, Word.append,
            Word.append_assoc, List.append_assoc] using
              contextualFrozenRTC_of_core
                (FrozenCoreStep.Path00014
                  (Word.singleton x) (Word.singleton y)
                  (listWordOfCons gapBHead gapBTail))
  | cons gapAHead gapATail =>
      cases gapB with
      | nil =>
          have first := contextualFrozenRTC_of_core
            (FrozenCoreStep.Path00019
              (Word.singleton x) (Word.singleton y)
              (listWordOfCons gapAHead gapATail))
          have second := (contextualFrozenRTC_of_core
            (FrozenCoreStep.Path00024
              (Word.singleton y) (Word.singleton x)
              (listWordOfCons gapAHead gapATail))).symm
          simpa [listWordOfCons, Word.singleton, Word.append,
            Word.append_assoc, List.append_assoc] using first.trans second
      | cons gapBHead gapBTail =>
          simpa [listWordOfCons, Word.singleton, Word.append,
            Word.append_assoc, List.append_assoc] using
              contextualFrozenRTC_of_core
                (FrozenCoreStep.Path00100
                  (Word.singleton x) (Word.singleton y)
                  (listWordOfCons gapAHead gapATail)
                  (listWordOfCons gapBHead gapBTail))

/-- Swap adjacent first endpoints when their later endpoints occur `y,x`. -/
theorem frozenSwapFirstLaterYX
    (x y : Nat) (gapA gapB : List Nat) :
    ContextualFrozenRTC
      ([x, y] ++ gapA ++ [y] ++ gapB ++ [x])
      ([y, x] ++ gapA ++ [y] ++ gapB ++ [x]) := by
  cases gapA with
  | nil =>
      cases gapB with
      | nil =>
          simpa [Word.singleton, Word.append, Word.append_assoc,
            List.append_assoc] using
              contextualFrozenRTC_of_core
                (FrozenCoreStep.Path00005
                  (Word.singleton x) (Word.singleton y))
      | cons gapBHead gapBTail =>
          simpa [listWordOfCons, Word.singleton, Word.append,
            Word.append_assoc, List.append_assoc] using
              contextualFrozenRTC_of_core
                (FrozenCoreStep.Path00015
                  (Word.singleton x) (Word.singleton y)
                  (listWordOfCons gapBHead gapBTail))
  | cons gapAHead gapATail =>
      cases gapB with
      | nil =>
          have first := contextualFrozenRTC_of_core
            (FrozenCoreStep.Path00024
              (Word.singleton x) (Word.singleton y)
              (listWordOfCons gapAHead gapATail))
          have second := contextualFrozenRTC_of_core
            (FrozenCoreStep.Path00019
              (Word.singleton x) (Word.singleton y)
              (listWordOfCons gapAHead gapATail))
          simpa [listWordOfCons, Word.singleton, Word.append,
            Word.append_assoc, List.append_assoc] using first.trans second
      | cons gapBHead gapBTail =>
          simpa [listWordOfCons, Word.singleton, Word.append,
            Word.append_assoc, List.append_assoc] using
              contextualFrozenRTC_of_core
                (FrozenCoreStep.Path00111
                  (Word.singleton x) (Word.singleton y)
                  (listWordOfCons gapAHead gapATail)
                  (listWordOfCons gapBHead gapBTail))

/-! ## Adjacent last-endpoint dispatcher -/

/-- With first `x` before first `y`, swap adjacent final endpoints `y,x`. -/
theorem frozenSwapLastYX
    (x y : Nat) (gapA gapB : List Nat) :
    ContextualFrozenRTC
      ([x] ++ gapA ++ [y] ++ gapB ++ [y, x])
      ([x] ++ gapA ++ [y] ++ gapB ++ [x, y]) := by
  cases gapA with
  | nil =>
      cases gapB with
      | nil =>
          simpa [Word.singleton, Word.append, Word.append_assoc,
            List.append_assoc] using
              contextualFrozenRTC_of_core
                (FrozenCoreStep.Path00004
                  (Word.singleton x) (Word.singleton y))
      | cons gapBHead gapBTail =>
          simpa [listWordOfCons, Word.singleton, Word.append,
            Word.append_assoc, List.append_assoc] using
              contextualFrozenRTC_of_core
                (FrozenCoreStep.Path00024
                  (Word.singleton x) (Word.singleton y)
                  (listWordOfCons gapBHead gapBTail))
  | cons gapAHead gapATail =>
      cases gapB with
      | nil =>
          simpa [listWordOfCons, Word.singleton, Word.append,
            Word.append_assoc, List.append_assoc] using
              contextualFrozenRTC_of_core
                (FrozenCoreStep.Path00030
                  (Word.singleton x)
                  (listWordOfCons gapAHead gapATail)
                  (Word.singleton y))
      | cons gapBHead gapBTail =>
          simpa [listWordOfCons, Word.singleton, Word.append,
            Word.append_assoc, List.append_assoc] using
              contextualFrozenRTC_of_core
                (FrozenCoreStep.Path00149
                  (Word.singleton x)
                  (listWordOfCons gapAHead gapATail)
                  (Word.singleton y)
                  (listWordOfCons gapBHead gapBTail))

end CapTwoRTCRoute
end SemigroupBasis.CoRoots.Order6L1RRank1.Gd61242744c5092fd
