import SemigroupBasis.CoRoots.Order6SporadicSection18RawChainBridge

/-! Pointwise support inclusion through C7 canonical saturation. Unlike
global content preservation, this keeps the original first/last block anchors. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical

def BlockExtends (left right : Slot) : Prop :=
  left.gap = right.gap ∧ ∀ x ∈ left.block, x ∈ right.block

inductive ChainExtends : List Slot → List Slot → Prop where
  | nil : ChainExtends [] []
  | cons {left right : Slot} {restLeft restRight : List Slot} :
      BlockExtends left right → ChainExtends restLeft restRight →
      ChainExtends (left :: restLeft) (right :: restRight)

theorem ChainExtends.refl (chain : List Slot) : ChainExtends chain chain := by
  induction chain with
  | nil => exact .nil
  | cons head tail ih => exact .cons ⟨rfl, fun _ member => member⟩ ih

theorem ChainExtends.trans {left middle right : List Slot}
    (first : ChainExtends left middle) (second : ChainExtends middle right) :
    ChainExtends left right := by
  induction first generalizing right with
  | nil => cases second; exact .nil
  | cons head tail ih =>
      cases second with
      | cons next rest =>
          exact .cons ⟨head.1.trans next.1, fun x member => next.2 x (head.2 x member)⟩ (ih rest)

theorem ChainExtends.append {left right afterLeft afterRight : List Slot}
    (first : ChainExtends left right) (second : ChainExtends afterLeft afterRight) :
    ChainExtends (left ++ afterLeft) (right ++ afterRight) := by
  induction first with
  | nil => exact second
  | cons head tail ih => exact .cons head ih

theorem ChainExtends.head {first next : Slot} {rest tail : List Slot}
    (extended : ChainExtends (first :: rest) (next :: tail)) : BlockExtends first next := by
  cases extended with
  | cons head _ => exact head

theorem ChainExtends.last (before : List Slot) (last : Slot) {output : List Slot}
    (extended : ChainExtends (before ++ [last]) output) :
    ∃ outBefore outLast, output = outBefore ++ [outLast] ∧ BlockExtends last outLast := by
  induction before generalizing output with
  | nil =>
      cases extended with
      | @cons leftHead rightHead restLeft restRight head tail =>
          cases tail
          exact ⟨[], rightHead, rfl, head⟩
  | cons first before ih =>
      cases extended with
      | @cons leftHead rightHead restLeft restRight head tail =>
          obtain ⟨outBefore, outLast, shape, member⟩ := ih tail
          exact ⟨rightHead :: outBefore, outLast, congrArg (List.cons rightHead) shape, member⟩

private theorem left_join_extends (alphabet gap left right : List Nat)
    (leftGood : GoodBlock alphabet left) (rightGood : GoodBlock alphabet right) :
    BlockExtends ⟨gap, left⟩ ⟨gap, joinBlock alphabet left right⟩ := by
  refine ⟨rfl, ?_⟩
  intro x member
  exact (joinBlock_content alphabet left right leftGood rightGood x).mp
    (List.mem_append.mpr (Or.inl member))

private theorem right_join_extends (alphabet gap left right : List Nat)
    (leftGood : GoodBlock alphabet left) (rightGood : GoodBlock alphabet right) :
    BlockExtends ⟨gap, right⟩ ⟨gap, joinBlock alphabet left right⟩ := by
  refine ⟨rfl, ?_⟩
  intro x member
  exact (joinBlock_content alphabet left right leftGood rightGood x).mp
    (List.mem_append.mpr (Or.inr member))

theorem Step.blockExtends {alphabet : List Nat} {input output : List Slot}
    (move : Step alphabet input output) (valid : Valid alphabet input) :
    ChainExtends input output := by
  cases move with
  | overlap before middle after g1 g2 left right x inLeft inRight different =>
      simp only [valid_append_iff, valid_cons_iff] at valid
      obtain ⟨_, leftGood, _, rightGood, _⟩ := valid
      exact (ChainExtends.refl before).append
        (.cons (left_join_extends alphabet g1 left right leftGood rightGood)
          ((ChainExtends.refl middle).append
            (.cons (right_join_extends alphabet g2 left right leftGood rightGood)
              (ChainExtends.refl after))))
  | crossing before middle1 middle2 middle3 after g1 g2 g3 g4 left right different =>
      simp only [valid_append_iff, valid_cons_iff] at valid
      obtain ⟨_, leftGood, _, rightGood, _, _, _, _, _⟩ := valid
      exact (ChainExtends.refl before).append
        (.cons (left_join_extends alphabet g1 left right leftGood rightGood)
          ((ChainExtends.refl middle1).append
            (.cons (right_join_extends alphabet g2 left right leftGood rightGood)
              ((ChainExtends.refl middle2).append
                (.cons (left_join_extends alphabet g3 left right leftGood rightGood)
                  ((ChainExtends.refl middle3).append
                    (.cons (right_join_extends alphabet g4 left right leftGood rightGood)
                      (ChainExtends.refl after))))))))

theorem Reach.blockExtends {alphabet : List Nat} {input output : List Slot}
    (reached : Reach alphabet input output) (valid : Valid alphabet input) :
    ChainExtends input output := by
  induction reached with
  | refl => exact ChainExtends.refl input
  | tail previous move ih => exact ih.trans (move.blockExtends (previous.valid valid))

theorem normalizeChain_extends (alphabet : List Nat) (input : List Slot)
    (bounded : BoundedNonempty alphabet input) :
    ChainExtends input (normalizeChain alphabet input) := by
  induction input with
  | nil => exact .nil
  | cons head tail ih =>
      have headBound := bounded head (List.Mem.head tail)
      have tailBound : BoundedNonempty alphabet tail :=
        fun slot member => bounded slot (List.Mem.tail head member)
      refine .cons ⟨rfl, ?_⟩ (ih tailBound)
      intro x member
      exact (normalizeBlock_content alphabet head.block headBound.2 x).mp member

theorem exists_saturated_squareChain_withAnchors
    (alphabet : List Nat) (input : List Slot) (bounded : BoundedNonempty alphabet input) :
    ∃ output, CanonicalChain alphabet output ∧
      ListDerives (render input) (render output) ∧
      input.map Slot.gap = output.map Slot.gap ∧ ChainExtends input output := by
  have normalizedValid := normalizeChain_valid alphabet input bounded
  obtain ⟨output, canonical, derivation, gaps, reached⟩ :=
    exists_canonicalChain alphabet (normalizeChain alphabet input) normalizedValid
  exact ⟨output, canonical, (normalizeChain_sound alphabet input bounded).trans derivation,
    (normalizeChain_gaps alphabet input).trans gaps,
    (normalizeChain_extends alphabet input bounded).trans (reached.blockExtends normalizedValid)⟩

theorem exists_saturated_rawChain_withAnchors
    (alphabet : List Nat) (input : List Slot) (before after : List Nat)
    (bounded : BoundedNonempty alphabet input)
    (nonsimple : ∀ slot ∈ input, ∀ x ∈ slot.block,
      (before ++ rawRender input ++ after).count x ≠ 1) :
    ∃ output, CanonicalChain alphabet output ∧
      ListDerives (before ++ rawRender input ++ after) (before ++ render output ++ after) ∧
      input.map Slot.gap = output.map Slot.gap ∧ ChainExtends input output := by
  obtain ⟨output, canonical, derivation, gaps, extended⟩ :=
    exists_saturated_squareChain_withAnchors alphabet input bounded
  exact ⟨output, canonical, (doubleChain input before after nonsimple).trans
    (derivation.context before after), gaps, extended⟩

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.ChainExtends.head
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.ChainExtends.last
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.Step.blockExtends
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.Reach.blockExtends
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.normalizeChain_extends
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.exists_saturated_squareChain_withAnchors
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.exists_saturated_rawChain_withAnchors

end SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical
