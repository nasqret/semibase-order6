import SemigroupBasis.CoRoots.Order6SporadicSection16CanonicalWords

/-! The ini and simple-letter invariants determine the entire Section16
canonical skeleton. Only the admissible anchor-marker bits remain. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection16.CanonicalShape

open SemigroupBasis CanonicalCounts

theorem split_at_first_failure (P : Nat → Prop) :
    ∀ (left right : List Nat) (a b : Nat) (xs ys : List Nat),
      left ++ a :: xs = right ++ b :: ys →
      (∀ x ∈ left, P x) → (∀ x ∈ right, P x) → ¬ P a → ¬ P b →
      left = right ∧ a = b ∧ xs = ys
  | [], [], a, b, xs, ys, equal, _, _, _, _ => by
      exact ⟨rfl, List.cons.inj equal⟩
  | [], y :: rest, a, b, xs, ys, equal, _, rightGood, leftBad, _ => by
      have heads : a = y := (List.cons.inj equal).1
      exact False.elim (leftBad (heads.symm ▸ rightGood y (List.Mem.head rest)))
  | x :: rest, [], a, b, xs, ys, equal, leftGood, _, _, rightBad => by
      have heads : x = b := (List.cons.inj equal).1
      exact False.elim (rightBad (heads ▸ leftGood x (List.Mem.head rest)))
  | x :: left, y :: right, a, b, xs, ys, equal, leftGood, rightGood, leftBad, rightBad => by
      have parts := List.cons.inj equal
      have rest := split_at_first_failure P left right a b xs ys parts.2
        (fun z member => leftGood z (List.Mem.tail x member))
        (fun z member => rightGood z (List.Mem.tail y member)) leftBad rightBad
      exact ⟨by rw [parts.1, rest.1], rest.2⟩

theorem prefix_anchor_labels (left right : CanonicalData)
    (leftWF : CanonicalWellFormed left) (rightWF : CanonicalWellFormed right)
    (same : FactorInvariants (canonicalWord left) (canonicalWord right)) :
    left.initial = right.initial ∧ left.anchor = right.anchor ∧
      left.blocks.map CanonicalBlock.letter = right.blocks.map CanonicalBlock.letter := by
  have labels := same.ini
  rw [canonicalWord_ini left leftWF, canonicalWord_ini right rightWF] at labels
  have split : left.initial ++ left.anchor :: left.blocks.map CanonicalBlock.letter =
      right.initial ++ right.anchor :: right.blocks.map CanonicalBlock.letter := by
    simpa only [canonicalLabels, List.append_assoc, List.cons_append, List.nil_append] using labels
  have simple : ∀ x, (renderCanonical left).count x = 1 ↔ (renderCanonical right).count x = 1 := by
    intro x
    simpa only [canonicalWord_toList] using same.simple x
  apply split_at_first_failure (fun x => (renderCanonical left).count x = 1)
    left.initial right.initial left.anchor right.anchor
    (left.blocks.map CanonicalBlock.letter) (right.blocks.map CanonicalBlock.letter) split
  · exact count_initial left leftWF
  · intro x member
    exact (simple x).mpr (count_initial right rightWF x member)
  · have bound := count_anchor left
    omega
  · intro h
    have bad := (simple right.anchor).mp h
    have bound := count_anchor right
    omega

theorem block_doubled_eq (left right : CanonicalData)
    (leftWF : CanonicalWellFormed left) (rightWF : CanonicalWellFormed right)
    (same : FactorInvariants (canonicalWord left) (canonicalWord right))
    (a b : CanonicalBlock) (aMem : a ∈ left.blocks) (bMem : b ∈ right.blocks)
    (letterEq : a.letter = b.letter) : a.doubled = b.doubled := by
  have simple : (renderCanonical left).count a.letter = 1 ↔
      (renderCanonical right).count b.letter = 1 := by
    simpa only [canonicalWord_toList, letterEq] using same.simple a.letter
  have flags : a.doubled = false ↔ b.doubled = false :=
    (simple_block_iff left leftWF a aMem).symm.trans
      (simple.trans (simple_block_iff right rightWF b bMem))
  cases ha : a.doubled <;> cases hb : b.doubled <;> simp_all

def blockShape (block : CanonicalBlock) : Nat × Bool := (block.letter,block.doubled)

theorem map_shapes_of_labels : ∀ (left right : List CanonicalBlock),
    left.map CanonicalBlock.letter = right.map CanonicalBlock.letter →
    (∀ a ∈ left, ∀ b ∈ right, a.letter = b.letter → a.doubled = b.doubled) →
    left.map blockShape = right.map blockShape
  | [], [], _, _ => rfl
  | [], _ :: _, equal, _ => by simp at equal
  | _ :: _, [], equal, _ => by simp at equal
  | a :: left, b :: right, equal, flags => by
      have labels := List.cons.inj equal
      have first : blockShape a = blockShape b :=
        Prod.ext labels.1 (flags a (List.Mem.head left) b (List.Mem.head right) labels.1)
      have rest := map_shapes_of_labels left right labels.2
        (fun x hx y hy h => flags x (List.Mem.tail a hx) y (List.Mem.tail b hy) h)
      change blockShape a :: left.map blockShape = blockShape b :: right.map blockShape
      rw [first, rest]

theorem same_skeleton (left right : CanonicalData)
    (leftWF : CanonicalWellFormed left) (rightWF : CanonicalWellFormed right)
    (same : FactorInvariants (canonicalWord left) (canonicalWord right)) :
    left.initial = right.initial ∧ left.anchor = right.anchor ∧
      left.blocks.map blockShape = right.blocks.map blockShape := by
  have labels := prefix_anchor_labels left right leftWF rightWF same
  exact ⟨labels.1, labels.2.1, map_shapes_of_labels left.blocks right.blocks labels.2.2
    (fun a ha b hb h => block_doubled_eq left right leftWF rightWF same a b ha hb h)⟩

#print axioms split_at_first_failure
#print axioms prefix_anchor_labels
#print axioms block_doubled_eq
#print axioms same_skeleton

end SemigroupBasis.CoRoots.Order6SporadicSection16.CanonicalShape
