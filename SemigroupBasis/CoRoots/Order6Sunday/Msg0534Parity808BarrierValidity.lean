import SemigroupBasis.CoRoots.Order6Sunday.Msg0534Parity808BarrierCuts
import SemigroupBasis.CoRoots.Order6Sunday.Msg0534Parity808BarrierProbe

/-! Actual S4_71 validity supplies every singleton cut, closing the mixed-run
gap of the Parity808 raw basis. No bounded key equality is used as a premise. -/
namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0534Parity808BarrierValidity

open SemigroupBasis
open Msg0524Parity808Gather (basis)
open Msg0524Parity808RunSort
open Msg0524Parity808RunMultiplicity
open Msg0524Parity808Canonical
open Msg0524Parity808LastNecessary
open Msg0534Parity808CanonicalSpine
open Msg0534Parity808BarrierCuts
open Msg0534Parity808BarrierProbe

theorem beforeBlock_mem (marker : Nat × Nat) (blocks : List (Nat × Nat))
    (block : Nat × Nat) (member : block ∈ beforeBlock marker blocks) : block ∈ blocks := by
  induction blocks with
  | nil => cases member
  | cons head tail ih =>
    by_cases same : head = marker
    · simp only [beforeBlock,if_pos same] at member
      cases member
    · simp only [beforeBlock,if_neg same] at member
      rcases List.mem_cons.mp member with equal | remaining
      · exact List.mem_cons.mpr (Or.inl equal)
      · exact List.mem_cons_of_mem head (ih remaining)

theorem beforeBlock_nodup (marker : Nat × Nat) (blocks : List (Nat × Nat))
    (unique : blocks.Nodup) : (beforeBlock marker blocks).Nodup := by
  induction blocks with
  | nil => exact List.nodup_nil
  | cons head tail ih =>
    have parts := List.nodup_cons.mp unique
    by_cases same : head = marker
    · simp only [beforeBlock,if_pos same]
      exact List.nodup_nil
    · simp only [beforeBlock,if_neg same]
      exact List.nodup_cons.mpr
        ⟨fun member => parts.1 (beforeBlock_mem marker tail head member),ih parts.2⟩

theorem marker_key_absent (front : List (Nat × Nat)) (marker : Nat × Nat) (tail : List (Nat × Nat))
    (distinct : ((front ++ marker :: tail).map Prod.fst).Nodup) :
    marker.1 ∉ render front ∧ marker.1 ∉ render tail := by
  have split : (front.map Prod.fst ++ marker.1 :: tail.map Prod.fst).Nodup := by
    simpa only [List.map_append,List.map_cons] using distinct
  have parts := List.nodup_append.mp split
  constructor
  · intro member
    exact parts.2.2 marker.1 ((render_mem_iff front marker.1).mp member)
      marker.1 (List.mem_cons_self) rfl
  · intro member
    exact (List.nodup_cons.mp parts.2.1).1 ((render_mem_iff tail marker.1).mp member)

theorem front_key_absent (front tail : List (Nat × Nat))
    (distinct : ((front ++ tail).map Prod.fst).Nodup)
    (block : Nat × Nat) (member : block ∈ front) : block.1 ∉ render tail := by
  have split : (front.map Prod.fst ++ tail.map Prod.fst).Nodup := by
    simpa only [List.map_append] using distinct
  intro present
  exact (List.nodup_append.mp split).2.2 block.1 (List.mem_map_of_mem member)
    block.1 ((render_mem_iff tail block.1).mp present) rfl

theorem render_singleton_split (front : List (Nat × Nat)) (marker : Nat × Nat)
    (tail : List (Nat × Nat)) (single : marker.2 = 0) :
    render (front ++ marker :: tail) = render front ++ marker.1 :: render tail := by
  simp [render,blockWord,single]

theorem cut_member_transfer (leftWord rightWord : Word Nat) (left right : List (Nat × Nat))
    (leftWordList : leftWord.toList = render left) (rightWordList : rightWord.toList = render right)
    (leftDistinct : (left.map Prod.fst).Nodup) (rightDistinct : (right.map Prod.fst).Nodup)
    (whole : left.Perm right) (valid : (Identity.mk leftWord rightWord).SatisfiedBy blockFactor)
    (marker : Nat × Nat) (single : marker.2 = 0) (markerMember : marker ∈ left)
    (block : Nat × Nat) (member : block ∈ beforeBlock marker left) :
    block ∈ beforeBlock marker right := by
  have markerRight := whole.mem_iff.mp markerMember
  obtain ⟨leftFront,leftTail,leftForm⟩ := List.append_of_mem markerMember
  obtain ⟨rightFront,rightTail,rightForm⟩ := List.append_of_mem markerRight
  subst left
  subst right
  have leftAbsent := marker_absent_parts leftFront marker leftTail leftDistinct
  have rightAbsent := marker_absent_parts rightFront marker rightTail rightDistinct
  rw [beforeBlock_append marker leftFront _ leftAbsent.1,beforeBlock_self,List.append_nil] at member
  rw [beforeBlock_append marker rightFront _ rightAbsent.1,beforeBlock_self,List.append_nil]
  have leftKeyAbsent := marker_key_absent leftFront marker leftTail leftDistinct
  have rightKeyAbsent := marker_key_absent rightFront marker rightTail rightDistinct
  have different : block.1 ≠ marker.1 := by
    intro same
    apply leftKeyAbsent.1
    rw [← same]
    exact (render_mem_iff leftFront block.1).mpr (List.mem_map_of_mem member)
  have selectedAbsentAll := front_key_absent leftFront (marker :: leftTail) leftDistinct block member
  have selectedAbsent : block.1 ∉ render leftTail := by
    intro present
    apply selectedAbsentAll
    change block.1 ∈ blockWord marker ++ render leftTail
    exact List.mem_append_right _ present
  rw [render_singleton_split leftFront marker leftTail single] at leftWordList
  rw [render_singleton_split rightFront marker rightTail single] at rightWordList
  have leftEval : blockFactor.eval (probe block.1 marker.1) leftWord = 1 := by
    rw [eval_singleton_split leftWord _ _ block.1 marker.1 leftWordList different
      leftKeyAbsent.1 leftKeyAbsent.2,if_neg selectedAbsent]
  have observed := valid (probe block.1 marker.1)
  change blockFactor.eval (probe block.1 marker.1) leftWord =
    blockFactor.eval (probe block.1 marker.1) rightWord at observed
  rw [leftEval,eval_singleton_split rightWord _ _ block.1 marker.1 rightWordList different
    rightKeyAbsent.1 rightKeyAbsent.2] at observed
  have rightTailAbsent : block.1 ∉ render rightTail := by
    intro present
    rw [if_pos present] at observed
    exact (by decide : (1 : Fin 4) ≠ 0) observed
  have rightMember := whole.mem_iff.mp (List.mem_append_left (marker :: leftTail) member)
  rcases List.mem_append.mp rightMember with frontMember | restMember
  · exact frontMember
  · rcases List.mem_cons.mp restMember with equal | tailMember
    · exact False.elim (different (congrArg Prod.fst equal))
    · exact False.elim (rightTailAbsent
        ((render_mem_iff rightTail block.1).mpr (List.mem_map_of_mem tailMember)))

theorem barrierCuts_of_valid (leftWord rightWord : Word Nat) (left right : List (Nat × Nat))
    (leftWordList : leftWord.toList = render left) (rightWordList : rightWord.toList = render right)
    (leftDistinct : (left.map Prod.fst).Nodup) (rightDistinct : (right.map Prod.fst).Nodup)
    (whole : left.Perm right) (valid : (Identity.mk leftWord rightWord).SatisfiedBy blockFactor) :
    SameBarrierCuts left right := by
  intro marker single markerMember
  have otherMember := whole.mem_iff.mp markerMember
  have forward := cut_member_transfer leftWord rightWord left right leftWordList rightWordList
    leftDistinct rightDistinct whole valid marker single markerMember
  have backward := cut_member_transfer rightWord leftWord right left rightWordList leftWordList
    rightDistinct leftDistinct whole.symm (fun valuation => (valid valuation).symm) marker single otherMember
  have sameMembership : ∀ block, block ∈ beforeBlock marker left ↔ block ∈ beforeBlock marker right :=
    fun block => ⟨forward block,backward block⟩
  rw [List.perm_iff_count]
  intro block
  rw [(beforeBlock_nodup marker left (blocks_nodup_of_keys left leftDistinct)).count,
    (beforeBlock_nodup marker right (blocks_nodup_of_keys right rightDistinct)).count]
  simp only [sameMembership block]

theorem beforeBlock_append_present (marker : Nat × Nat) (front tail : List (Nat × Nat))
    (present : marker ∈ front) : beforeBlock marker (front ++ tail) = beforeBlock marker front := by
  induction front with
  | nil => cases present
  | cons head rest ih =>
    by_cases same : head = marker
    · simp only [List.cons_append,beforeBlock,if_pos same]
    · have restMember : marker ∈ rest := (List.mem_cons.mp present).resolve_left (Ne.symm same)
      simp only [List.cons_append,beforeBlock,if_neg same,ih restMember]

theorem canonical_block_valid {left right : Word Nat} (same : JointSignature left right) :
    (Identity.mk (canonicalWord left) (canonicalWord right)).SatisfiedBy blockFactor := by
  have reversedValid := (canonical_signature same).blockTheory
  have direct := (Identity.satisfiedBy_opposite_iff_reversed
    (Identity.mk (canonicalWord left).reverse (canonicalWord right).reverse) blockFactor).mp reversedValid
  simpa only [Identity.reversed,Word.reverse_reverse] using direct

theorem canonical_full_cuts {left right : Word Nat} (same : JointSignature left right) :
    SameBarrierCuts (blocks left) (blocks right) :=
  barrierCuts_of_valid (canonicalWord left) (canonicalWord right) (blocks left) (blocks right)
    ((canonicalWord_toList left).trans (blocks_render left).symm)
    ((canonicalWord_toList right).trans (blocks_render right).symm)
    (blocks_distinct left) (blocks_distinct right) (blocks_perm same) (canonical_block_valid same)

theorem canonical_prefix_cuts {left right : Word Nat} (same : JointSignature left right) :
    SameBarrierCuts (canonicalPrefix left) (canonicalPrefix right) := by
  intro marker single member
  have rightMember := (canonicalPrefix_perm same).mem_iff.mp member
  have fullMember : marker ∈ blocks left := by
    rw [blocks_decomposition]
    exact List.mem_append_left _ member
  have cuts := canonical_full_cuts same marker single fullMember
  rw [blocks_decomposition,blocks_decomposition,
    beforeBlock_append_present marker _ _ member,
    beforeBlock_append_present marker _ _ rightMember] at cuts
  exact cuts

theorem joint_complete {left right : Word Nat} (same : JointSignature left right) :
    Derives basis left right := derives_of_barrierCuts same (canonical_prefix_cuts same)

theorem actual_factors_complete (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy Msg0524Parity808FactorEval.factor)
    (rightValid : identity.SatisfiedBy rightFactor) : Derives basis identity.lhs identity.rhs :=
  joint_complete (joint_signature_necessary identity leftValid rightValid)

end SemigroupBasis.CoRoots.Order6Sunday.Msg0534Parity808BarrierValidity
