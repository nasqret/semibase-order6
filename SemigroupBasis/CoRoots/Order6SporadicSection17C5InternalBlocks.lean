import SemigroupBasis.CoRoots.Order6SporadicSection17C5InputBlockContexts

/-! The actual internal gaps are exactly maximal simple blocks that are
neither initial nor terminal. Common-marker uniqueness supplies the reverse
inclusion; semantic equivalence therefore gives the actual gap permutation. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6
open SemigroupBasis

def InternalSimpleBlock (word part : List Nat) : Prop :=
  MaximalSimpleBlock word part ∧
    ¬ InitialSimpleBlock word part ∧ ¬ TerminalSimpleBlock word part

namespace Semantics

theorem SameEval.internalSimpleBlock {which : Bool} {left right : List Nat}
    (same : SameEval which left right) (part : List Nat) :
    InternalSimpleBlock left part ↔ InternalSimpleBlock right part := by
  simp only [InternalSimpleBlock,same.maximalSimpleBlock,same.initialSimpleBlock,same.terminalSimpleBlock]

end Semantics

theorem populatedInternal_block (original gap : List Nat) (member : gap ∈ populatedInternal original) :
    InternalSimpleBlock original gap := by
  have derived := Semantics.derives_sameEval false (populatedInputForm_derives original)
  rcases bodyInternalGaps_member_split (populatedInputForm original).pieces gap member with
    ⟨before,tiles,after,piecesShape,afterNonempty⟩
  have piecesGood := (populatedInputForm_good original).2
  rw [piecesShape] at piecesGood
  have tailGood := BodyPiecesGood.drop_prefix original before ((tiles,gap) :: after) piecesGood
  let leading := (populatedInputForm original).initial ++ bodyPiecesWord before ++ powerTileBody tiles
  let trailing := bodyPiecesWord after
  have formShape : bodyFormWord (populatedInputForm original) = leading ++ gap ++ trailing := by
    simp only [bodyFormWord,piecesShape,bodyPiecesWord_append,bodyPiecesWord,leading,trailing,List.append_assoc]
  have simple : ∀ x ∈ gap, (bodyFormWord (populatedInputForm original)).count x = 1 := by
    intro x found
    exact (derived.countOne x).mp (tailGood.1.2.2 x found)
  have leftBlocked : ∀ front x, leading = front ++ [x] →
      (bodyFormWord (populatedInputForm original)).count x ≠ 1 := by
    intro front x shape one
    exact powerTileBody_tail_not_simple original tiles tailGood.1.1 tailGood.1.2.1
      ((populatedInputForm original).initial ++ bodyPiecesWord before) front x shape
      ((derived.countOne x).mpr one)
  have rightBlocked : ∀ x rest, trailing = x :: rest →
      (bodyFormWord (populatedInputForm original)).count x ≠ 1 := by
    intro x rest shape one
    exact bodyPiecesWord_head_not_simple original after tailGood.2.2 x rest shape
      ((derived.countOne x).mpr one)
  have leadingNonempty : leading ≠ [] :=
    listAppend_ne_nil_right _ _ (powerTileBody_nonempty tiles tailGood.1.1)
  have trailingNonempty : trailing ≠ [] :=
    bodyPiecesWord_nonempty original after tailGood.2.2 afterNonempty
  have maximal := maximalSimpleBlock_of_context _ leading gap trailing formShape
    (tailGood.2.1 afterNonempty) simple leftBlocked rightBlocked
  have block : InternalSimpleBlock (bodyFormWord (populatedInputForm original)) gap :=
    ⟨maximal,
      simpleBlock_not_initial_of_before _ leading gap trailing formShape leadingNonempty simple,
      simpleBlock_not_terminal_of_after _ leading gap trailing formShape trailingNonempty simple⟩
  exact (derived.internalSimpleBlock gap).mpr block

theorem populatedInternal_of_block (original gap : List Nat) (block : InternalSimpleBlock original gap) :
    gap ∈ populatedInternal original := by
  have maximal := block.1
  cases gap with
  | nil => exact False.elim (maximal.1 rfl)
  | cons x xs =>
      have one := maximal.2.1.countOne x List.mem_cons_self
      have inOriginal : x ∈ original := List.count_pos_iff.mp (by omega)
      have derived := Semantics.derives_sameEval false (populatedInputForm_derives original)
      have inForm := (derived.mem x).mp inOriginal
      change x ∈ (populatedInputForm original).initial ++
        bodyPiecesWord (populatedInputForm original).pieces at inForm
      rcases List.mem_append.mp inForm with initial | body
      · have nonempty : (populatedInputForm original).initial ≠ [] := by
          intro empty
          rw [empty] at initial
          cases initial
        have initialBlock := populatedInitial_block original nonempty
        have equal := maximal.eq_of_common_marker initialBlock.1 x List.mem_cons_self initial
        apply False.elim
        apply block.2.1
        rw [equal]
        exact initialBlock
      · rcases (bodyPiecesWord_mem (populatedInputForm original).pieces x).mp body with
          ⟨piece,pieceMember,inPower | inGap⟩
        · have valid := (populatedInputForm_good original).2.pieceValid piece pieceMember
          exact False.elim (powerTileBody_member_not_simple original piece.1 valid.2.1 x inPower one)
        · have piecesNonempty : (populatedInputForm original).pieces ≠ [] := by
            intro empty
            rw [empty] at pieceMember
            cases pieceMember
          have gapMember : piece.2 ∈ (populatedInputForm original).pieces.map Prod.snd :=
            List.mem_map.mpr ⟨piece,pieceMember,rfl⟩
          rw [bodyPieces_gaps_split (populatedInputForm original).pieces piecesNonempty] at gapMember
          rcases List.mem_append.mp gapMember with internal | terminal
          · have actual : piece.2 ∈ populatedInternal original := internal
            have actualBlock := populatedInternal_block original piece.2 actual
            have equal := maximal.eq_of_common_marker actualBlock.1 x List.mem_cons_self inGap
            rw [equal]
            exact actual
          · have terminalEqual : piece.2 = bodyTerminal (populatedInputForm original).pieces :=
              List.mem_singleton.mp terminal
            have inTerminal : x ∈ populatedTerminal original := by
              change x ∈ bodyTerminal (populatedInputForm original).pieces
              rw [← terminalEqual]
              exact inGap
            have terminalNonempty : populatedTerminal original ≠ [] := by
              intro empty
              rw [empty] at inTerminal
              cases inTerminal
            have terminalBlock := populatedTerminal_block original piecesNonempty terminalNonempty
            have equal := maximal.eq_of_common_marker terminalBlock.1 x List.mem_cons_self inTerminal
            apply False.elim
            apply block.2.2
            rw [equal]
            exact terminalBlock

theorem populatedInternal_iff (original gap : List Nat) :
    gap ∈ populatedInternal original ↔ InternalSimpleBlock original gap :=
  ⟨populatedInternal_block original gap,populatedInternal_of_block original gap⟩

namespace Semantics

theorem SameEval.populatedInternal_perm {which : Bool} {left right : List Nat}
    (same : SameEval which left right) :
    (populatedInternal left).Perm (populatedInternal right) := by
  apply List.perm_iff_count.mpr
  intro gap
  have membership : gap ∈ populatedInternal left ↔ gap ∈ populatedInternal right :=
    (populatedInternal_iff left gap).trans
      ((same.internalSimpleBlock gap).trans (populatedInternal_iff right gap).symm)
  simp only [(populatedInternal_nodup left).count,(populatedInternal_nodup right).count]
  by_cases present : gap ∈ populatedInternal left
  · rw [if_pos present,if_pos (membership.mp present)]
  · rw [if_neg present,if_neg (fun found => present (membership.mpr found))]

end Semantics

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.Semantics.SameEval.internalSimpleBlock
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.populatedInternal_block
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.populatedInternal_of_block
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.populatedInternal_iff
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.Semantics.SameEval.populatedInternal_perm

end SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6
