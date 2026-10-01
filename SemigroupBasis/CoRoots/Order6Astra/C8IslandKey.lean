import SemigroupBasis.CoRoots.Order6Astra.C8StarFrames
import SemigroupBasis.CoRoots.Order6Astra.C8KeyCalculus

namespace SemigroupBasis.CoRoots.Order6Astra.C8IslandKey

open C8TailCuts C8SemanticKey C8CutCalculus C8KeyCalculus C8StarFrames

/-- A literal support-isolated subword; the two exterior lists may share
letters with one another, but neither shares a letter with the subword. -/
structure Island (whole part : List Nat) where
  left : List Nat
  right : List Nat
  literal : whole = left ++ part ++ right
  isolated : Disjoint part (left ++ right)

theorem Island.count {whole part : List Nat} (island : Island whole part)
    (x : Nat) (member : x ∈ part) : whole.count x = part.count x := by
  rw [island.literal]
  exact count_in_frame island.left part island.right x member island.isolated

theorem Island.member {whole part : List Nat} (island : Island whole part)
    (x : Nat) (member : x ∈ part) : x ∈ whole := by
  rw [island.literal]
  exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr member)))

theorem Island.tail {whole part : List Nat} (island : Island whole part)
    (marker : Nat) (simple : part.count marker = 1) (z : List Nat)
    (covered : ∀ x ∈ z, x ∈ part) : TailAt whole marker z ↔ TailAt part marker z := by
  have member : marker ∈ part := List.one_le_count_iff.mp (by omega)
  obtain ⟨p, s, split⟩ := List.mem_iff_append.mp member
  have wholeSplit : whole = (island.left ++ p) ++ marker :: (s ++ island.right) := by
    exact island.literal.trans
      ((congrArg (fun middle => island.left ++ middle ++ island.right) split).trans
        (by simp only [List.append_assoc, List.cons_append]))
  have wholeSimple : whole.count marker = 1 := (island.count marker member).trans simple
  rw [tailAt_at_split whole marker _ _ z wholeSplit wholeSimple,
    tailAt_at_split part marker p s z split simple]
  exact tail_frame_disjoint island.left island.right p s z
    (fun x hx => island.isolated x (covered x hx))

theorem island_simple {left right p q : List Nat} (key : Key left right)
    (first : Island left p) (second : Island right q) (same : SameSupport p q) :
    ∀ marker, p.count marker = 1 ↔ q.count marker = 1 := by
  intro marker
  by_cases present : marker ∈ p
  · have target := (same marker).mp present
    simpa only [first.count marker present, second.count marker target] using key.simple marker
  · have absent : marker ∉ q := fun h => present ((same marker).mpr h)
    simp only [List.count_eq_zero.mpr present, List.count_eq_zero.mpr absent]

theorem island_tail_forward {left right p q : List Nat} (key : Key left right)
    (first : Island left p) (second : Island right q) (same : SameSupport p q)
    (marker : Nat) (simple : p.count marker = 1) (z : List Nat) (tail : TailAt p marker z) :
    TailAt q marker z := by
  have covered : ∀ x ∈ z, x ∈ p := by
    obtain ⟨before, after, split, actual⟩ := tail
    intro x hx
    rw [split]
    exact List.mem_append.mpr (Or.inl (tail_coverage before after z actual x hx))
  have targetCovered : ∀ x ∈ z, x ∈ q := fun x hx => (same x).mp (covered x hx)
  have present : marker ∈ p := List.one_le_count_iff.mp (by omega)
  have wholeSimple : left.count marker = 1 := (first.count marker present).trans simple
  have targetSimple := (island_simple key first second same marker).mp simple
  exact (second.tail marker targetSimple z targetCovered).mp
    ((key.tails marker wholeSimple z).mp ((first.tail marker simple z covered).mpr tail))

/-- After matching subword support and its ordered cut family, every remaining
key field restricts automatically. The full flag is reconstructed, not assumed. -/
theorem key_islands {left right p q : List Nat} (key : Key left right)
    (first : Island left p) (second : Island right q) (same : SameSupport p q)
    (cuts : ∀ z, Cut p z ↔ Cut q z) : Key p q := by
  have simple := island_simple key first second same
  refine ⟨same, simple, cuts, ?_, ?_⟩
  · intro marker once z
    exact ⟨island_tail_forward key first second same marker once z,
      island_tail_forward key.symm second first (same_symm same) marker ((simple marker).mp once) z⟩
  · intro marker once
    exact ⟨full_of_cuts_forward p q marker once ((simple marker).mp once) (fun z => (cuts z).mp),
      full_of_cuts_forward q p marker ((simple marker).mp once) once (fun z => (cuts z).mpr)⟩

end SemigroupBasis.CoRoots.Order6Astra.C8IslandKey

#print axioms SemigroupBasis.CoRoots.Order6Astra.C8IslandKey.Island.tail
#print axioms SemigroupBasis.CoRoots.Order6Astra.C8IslandKey.key_islands
