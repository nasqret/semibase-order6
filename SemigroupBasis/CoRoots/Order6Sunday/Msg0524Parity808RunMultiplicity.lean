import SemigroupBasis.CoRoots.Order6Sunday.Msg0524Parity808RunUnique

/-! Rendered letter counts recover a distinct-key positive block list up to
permutation. Count certificates then reuse the existing singleton-separated
run normal form. This is not semantic necessity or whole-word completeness. -/
namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0524Parity808RunMultiplicity

open Msg0524Parity808RunSort
open Msg0524Parity808RunUnique
open Msg0524Parity808Gather (LD)

theorem render_mem_iff (blocks : List (Nat × Nat)) (letter : Nat) :
    letter ∈ render blocks ↔ letter ∈ blocks.map Prod.fst := by
  constructor
  · intro member
    rcases List.mem_flatMap.mp member with ⟨block, hb, hx⟩
    have key : letter = block.1 := (List.mem_replicate.mp hx).2
    rw [key]
    exact List.mem_map_of_mem hb
  · intro member
    rcases List.mem_map.mp member with ⟨block, hb, key⟩
    apply List.mem_flatMap.mpr
    exact ⟨block, hb, List.mem_replicate.mpr ⟨by omega, key.symm⟩⟩

theorem render_count_of_not_key (blocks : List (Nat × Nat)) (letter : Nat)
    (absent : letter ∉ blocks.map Prod.fst) : (render blocks).count letter = 0 :=
  List.count_eq_zero.mpr (fun member => absent ((render_mem_iff blocks letter).mp member))

theorem render_count_of_mem (blocks : List (Nat × Nat)) :
    (blocks.map Prod.fst).Nodup → ∀ block ∈ blocks,
      (render blocks).count block.1 = block.2 + 1 := by
  induction blocks with
  | nil => intro _ block member; cases member
  | cons head tail ih =>
    intro distinct block member
    have hd : head.1 ∉ tail.map Prod.fst ∧ (tail.map Prod.fst).Nodup := by
      simpa only [List.map_cons, List.nodup_cons] using distinct
    rcases List.mem_cons.mp member with same | member
    · subst block
      change (blockWord head ++ render tail).count head.1 = head.2 + 1
      rw [List.count_append, render_count_of_not_key tail head.1 hd.1]
      simp [blockWord]
    · have different : head.1 ≠ block.1 := by
        intro same
        apply hd.1
        rw [same]
        exact List.mem_map_of_mem member
      change (blockWord head ++ render tail).count block.1 = block.2 + 1
      rw [List.count_append, ih hd.2 block member]
      simp [blockWord, List.count_replicate, different]

theorem blocks_nodup_of_keys (blocks : List (Nat × Nat)) :
    (blocks.map Prod.fst).Nodup → blocks.Nodup := by
  induction blocks with
  | nil => intro _; exact List.nodup_nil
  | cons head tail ih =>
    intro distinct
    have hd : head.1 ∉ tail.map Prod.fst ∧ (tail.map Prod.fst).Nodup := by
      simpa only [List.map_cons, List.nodup_cons] using distinct
    exact List.nodup_cons.mpr ⟨fun member => hd.1 (List.mem_map_of_mem member), ih hd.2⟩

theorem block_mem_of_render_counts (left right : List (Nat × Nat))
    (leftDistinct : (left.map Prod.fst).Nodup)
    (rightDistinct : (right.map Prod.fst).Nodup)
    (counts : ∀ letter, (render left).count letter = (render right).count letter)
    (block : Nat × Nat) (member : block ∈ left) : block ∈ right := by
  have positive : 0 < (render right).count block.1 := by
    rw [← counts block.1, render_count_of_mem left leftDistinct block member]
    omega
  have keyMember : block.1 ∈ right.map Prod.fst :=
    (render_mem_iff right block.1).mp (List.count_pos_iff.mp positive)
  rcases List.mem_map.mp keyMember with ⟨other, otherMember, sameKey⟩
  have sameCount : block.2 + 1 = other.2 + 1 := by
    calc
      block.2 + 1 = (render left).count block.1 :=
        (render_count_of_mem left leftDistinct block member).symm
      _ = (render right).count block.1 := counts block.1
      _ = (render right).count other.1 :=
        congrArg (fun key => (render right).count key) sameKey.symm
      _ = other.2 + 1 := render_count_of_mem right rightDistinct other otherMember
  have same : block = other := Prod.ext sameKey.symm (by omega)
  rw [same]
  exact otherMember

theorem perm_of_render_counts (left right : List (Nat × Nat))
    (leftDistinct : (left.map Prod.fst).Nodup)
    (rightDistinct : (right.map Prod.fst).Nodup)
    (counts : ∀ letter, (render left).count letter = (render right).count letter) :
    left.Perm right := by
  have sameMembership : ∀ block, block ∈ left ↔ block ∈ right := by
    intro block
    exact ⟨block_mem_of_render_counts left right leftDistinct rightDistinct counts block,
      block_mem_of_render_counts right left rightDistinct leftDistinct
        (fun letter => (counts letter).symm) block⟩
  rw [List.perm_iff_count]
  intro block
  rw [(blocks_nodup_of_keys left leftDistinct).count,
      (blocks_nodup_of_keys right rightDistinct).count]
  simp only [sameMembership block]

theorem render_counts_of_perm (left right : List (Nat × Nat)) (perm : left.Perm right)
    (letter : Nat) : (render left).count letter = (render right).count letter :=
  (List.Perm.flatMap_right blockWord perm).count_eq letter

theorem perm_iff_render_counts (left right : List (Nat × Nat))
    (leftDistinct : (left.map Prod.fst).Nodup)
    (rightDistinct : (right.map Prod.fst).Nodup) :
    left.Perm right ↔ ∀ letter, (render left).count letter = (render right).count letter :=
  ⟨render_counts_of_perm left right,
    perm_of_render_counts left right leftDistinct rightDistinct⟩

theorem sortRuns_eq_of_render_counts (left right : List (Nat × Nat))
    (leftDistinct : (left.map Prod.fst).Nodup)
    (rightDistinct : (right.map Prod.fst).Nodup) (pure : AllRepeated left)
    (counts : ∀ letter, (render left).count letter = (render right).count letter) :
    sortRuns left = sortRuns right :=
  sortRuns_perm_eq_of_nodup left right
    (perm_of_render_counts left right leftDistinct rightDistinct counts) pure leftDistinct

theorem pure_counts_sameRuns (left right : List (Nat × Nat))
    (leftDistinct : (left.map Prod.fst).Nodup)
    (rightDistinct : (right.map Prod.fst).Nodup) (pure : AllRepeated left)
    (counts : ∀ letter, (render left).count letter = (render right).count letter) :
    SameRuns left right :=
  SameRuns.last left right pure (faithfulKeys_of_nodup left leftDistinct)
    (perm_of_render_counts left right leftDistinct rightDistinct counts)

theorem pure_counts_derives (left right : List (Nat × Nat))
    (leftDistinct : (left.map Prod.fst).Nodup)
    (rightDistinct : (right.map Prod.fst).Nodup) (pure : AllRepeated left)
    (counts : ∀ letter, (render left).count letter = (render right).count letter)
    (suffix : List Nat) (nonempty : suffix ≠ []) :
    LD (render left ++ suffix) (render right ++ suffix) :=
  sameRuns_derives (pure_counts_sameRuns left right leftDistinct rightDistinct pure counts)
    suffix nonempty

inductive SameRunCounts : List (Nat × Nat) → List (Nat × Nat) → Prop
  | last (left right : List (Nat × Nat))
      (leftDistinct : (left.map Prod.fst).Nodup)
      (rightDistinct : (right.map Prod.fst).Nodup) (pure : AllRepeated left)
      (counts : ∀ letter, (render left).count letter = (render right).count letter) :
      SameRunCounts left right
  | split (left right : List (Nat × Nat)) (marker : Nat × Nat)
      (leftTail rightTail : List (Nat × Nat))
      (leftDistinct : (left.map Prod.fst).Nodup)
      (rightDistinct : (right.map Prod.fst).Nodup) (pure : AllRepeated left)
      (counts : ∀ letter, (render left).count letter = (render right).count letter)
      (single : marker.2 = 0) (remaining : SameRunCounts leftTail rightTail) :
      SameRunCounts (left ++ marker :: leftTail) (right ++ marker :: rightTail)

theorem sameRunCounts_sameRuns {left right : List (Nat × Nat)}
    (same : SameRunCounts left right) : SameRuns left right := by
  induction same with
  | last left right leftDistinct rightDistinct pure counts =>
    exact pure_counts_sameRuns left right leftDistinct rightDistinct pure counts
  | split left right marker leftTail rightTail leftDistinct rightDistinct pure counts single remaining ih =>
    exact SameRuns.split left right marker leftTail rightTail pure
      (faithfulKeys_of_nodup left leftDistinct)
      (perm_of_render_counts left right leftDistinct rightDistinct counts) single ih

theorem sameRunCounts_sort_eq {left right : List (Nat × Nat)}
    (same : SameRunCounts left right) : sortRuns left = sortRuns right :=
  sameRuns_sort_eq (sameRunCounts_sameRuns same)

theorem sameRunCounts_derives {left right : List (Nat × Nat)}
    (same : SameRunCounts left right) (suffix : List Nat) (nonempty : suffix ≠ []) :
    LD (render left ++ suffix) (render right ++ suffix) :=
  sameRuns_derives (sameRunCounts_sameRuns same) suffix nonempty

end SemigroupBasis.CoRoots.Order6Sunday.Msg0524Parity808RunMultiplicity
