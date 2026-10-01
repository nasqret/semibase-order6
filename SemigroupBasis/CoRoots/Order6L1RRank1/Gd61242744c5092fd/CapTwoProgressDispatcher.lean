import SemigroupBasis.CoRoots.Order6L1RRank1.Gd61242744c5092fd.CapTwoEndpointRTC

/-!
# Exact route dispatcher for endpoint disorder

This module is deliberately below the semantic/measure layer.  Its input is
one of the six literal decompositions selected by the structural proof, and
its output is the corresponding nonempty contextual frozen RTC.  The separate
measure module must prove that a positive lexicographic measure supplies one
of these cases and that the displayed target is smaller.
-/

namespace SemigroupBasis.CoRoots.Order6L1RRank1.Gd61242744c5092fd
namespace CapTwoRTCRoute

/-- Literal cases required by the endpoint-disorder proof. -/
inductive EndpointDisorderCase (letters : List Nat) : Prop where
  | efCrossing
      (front suffix : List Nat)
      (crossing endpoint : Nat)
      (before middle after : List Nat)
      (shape :
        letters = front ++ [crossing] ++ before ++ [endpoint] ++
          middle ++ [crossing] ++ after ++ [endpoint] ++ suffix) :
      EndpointDisorderCase letters
  | efNested
      (front suffix : List Nat)
      (crossing endpoint : Nat)
      (before middle after : List Nat)
      (shape :
        letters = front ++ [crossing] ++ before ++ [endpoint] ++
          middle ++ [endpoint] ++ after ++ [crossing] ++ suffix) :
      EndpointDisorderCase letters
  | ffLaterXY
      (front suffix : List Nat)
      (x y : Nat) (gapA gapB : List Nat)
      (shape :
        letters = front ++ [x, y] ++ gapA ++ [x] ++ gapB ++ [y] ++
          suffix) :
      EndpointDisorderCase letters
  | ffLaterYX
      (front suffix : List Nat)
      (x y : Nat) (gapA gapB : List Nat)
      (shape :
        letters = front ++ [x, y] ++ gapA ++ [y] ++ gapB ++ [x] ++
          suffix) :
      EndpointDisorderCase letters
  | eeFirstXY
      (front suffix : List Nat)
      (x y : Nat) (gapA gapB : List Nat)
      (shape :
        letters = front ++ [x] ++ gapA ++ [y] ++ gapB ++ [y, x] ++
          suffix) :
      EndpointDisorderCase letters
  | eeFirstYX
      (front suffix : List Nat)
      (x y : Nat) (gapA gapB : List Nat)
      (shape :
        letters = front ++ [y] ++ gapA ++ [x] ++ gapB ++ [y, x] ++
          suffix) :
      EndpointDisorderCase letters

/-- Concrete existential result of dispatching one structural disorder case.
This is an inductive proposition, so the target list is eliminated only into
later proof propositions. -/
inductive EndpointRouteResult (letters : List Nat) : Prop where
  | intro (next : List Nat)
      (reachable : ContextualFrozenRTC letters next) :
      EndpointRouteResult letters

/-- Apply the exact frozen route selected by a literal disorder case. -/
theorem endpointDisorder_dispatch
    {letters : List Nat}
    (selected : EndpointDisorderCase letters) :
    EndpointRouteResult letters := by
  cases selected with
  | efCrossing front suffix crossing endpoint before middle after shape =>
      let next :=
        front ++ [endpoint, crossing] ++ before ++ middle ++
          [crossing] ++ after ++ [endpoint] ++ suffix
      refine ⟨next, ?_⟩
      rw [shape]
      simpa [next, List.append_assoc] using
        (frozenPullEndpointCrossing crossing endpoint
          before middle after).context front suffix
  | efNested front suffix crossing endpoint before middle after shape =>
      let next :=
        front ++ [endpoint, crossing] ++ before ++ middle ++
          [endpoint] ++ after ++ [crossing] ++ suffix
      refine ⟨next, ?_⟩
      rw [shape]
      simpa [next, List.append_assoc] using
        (frozenPullEndpointNested crossing endpoint
          before middle after).context front suffix
  | ffLaterXY front suffix x y gapA gapB shape =>
      let next :=
        front ++ [y, x] ++ gapA ++ [x] ++ gapB ++ [y] ++ suffix
      refine ⟨next, ?_⟩
      rw [shape]
      simpa [next, List.append_assoc] using
        (frozenSwapFirstLaterXY x y gapA gapB).context front suffix
  | ffLaterYX front suffix x y gapA gapB shape =>
      let next :=
        front ++ [y, x] ++ gapA ++ [y] ++ gapB ++ [x] ++ suffix
      refine ⟨next, ?_⟩
      rw [shape]
      simpa [next, List.append_assoc] using
        (frozenSwapFirstLaterYX x y gapA gapB).context front suffix
  | eeFirstXY front suffix x y gapA gapB shape =>
      let next :=
        front ++ [x] ++ gapA ++ [y] ++ gapB ++ [x, y] ++ suffix
      refine ⟨next, ?_⟩
      rw [shape]
      simpa [next, List.append_assoc] using
        (frozenSwapLastYX x y gapA gapB).context front suffix
  | eeFirstYX front suffix x y gapA gapB shape =>
      let next :=
        front ++ [y] ++ gapA ++ [x] ++ gapB ++ [x, y] ++ suffix
      refine ⟨next, ?_⟩
      rw [shape]
      simpa [next, List.append_assoc] using
        (frozenSwapLastYX y x gapA gapB).symm.context front suffix

end CapTwoRTCRoute
end SemigroupBasis.CoRoots.Order6L1RRank1.Gd61242744c5092fd
