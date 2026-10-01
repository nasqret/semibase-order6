import SemigroupBasis.CoRoots.Order6Day15.B16.B16OptionalObservation

namespace SemigroupBasis.CoRoots.Order6Day15.B16.Reach

open Literal

def MarkersSimple (ns xs : List Nat) : Prop :=
  ∀ a ∈ xs, a ∉ ns → xs.count a = 1

def MarkedObservation (ns xs ys : List Nat) : Prop :=
  SameOptionalKey xs ys ∧
  ∀ a ∈ xs, a ∉ ns → SameOptionalKey (afterLetter a xs) (afterLetter a ys)

theorem markersSimple_suffix (ns pre post : List Nat) (h : MarkersSimple ns (pre ++ post)) :
    MarkersSimple ns post := by
  intro a ha hn
  have one := h a (List.mem_append.mpr (Or.inr ha)) hn
  have positive : 0 < post.count a := Nat.pos_of_ne_zero (fun hz => (List.count_eq_zero.mp hz) ha)
  rw [List.count_append] at one
  omega

theorem simple_separator_absent (pre post : List Nat) (s : Nat)
    (one : (pre ++ s :: post).count s = 1) : s ∉ post := by
  rw [List.count_append, List.count_cons_self] at one
  have zero : post.count s = 0 := by omega
  exact List.count_eq_zero.mp zero

theorem covered_avoids (ns gap : List Nat) (covered : ∀ a ∈ gap, a ∈ ns)
    (a : Nat) (outside : a ∉ ns) : a ∉ gap := fun mem => outside (covered a mem)

/-- The first globally simple separator is forced by the observed suffix supports. -/
theorem first_separator_eq (ns g post g' post' : List Nat) (s t : Nat)
    (leftCovered : ∀ a ∈ g, a ∈ ns) (rightCovered : ∀ a ∈ g', a ∈ ns)
    (hs : s ∉ ns) (ht : t ∉ ns)
    (rightSimple : MarkersSimple ns (g' ++ t :: post'))
    (obs : MarkedObservation ns (g ++ s :: post) (g' ++ t :: post')) : s = t := by
  by_cases eq : s = t
  · exact eq
  have tInTarget : t ∈ g' ++ t :: post' := List.mem_append.mpr (Or.inr (List.Mem.head _))
  have tInSource := (optional_support obs.1 t).mpr tInTarget
  have tInPost : t ∈ post := by
    rcases List.mem_append.mp tInSource with first | rest
    · exact False.elim (ht (leftCovered t first))
    · rcases List.mem_cons.mp rest with same | mem
      · exact False.elim (eq same.symm)
      · exact mem
  have old := obs.2 s (List.mem_append.mpr (Or.inr (List.Mem.head _))) hs
  have sAbsentG : s ∉ g := covered_avoids ns g leftCovered s hs
  have sAbsentG' : s ∉ g' := covered_avoids ns g' rightCovered s hs
  have ts : t ≠ s := fun h => eq h.symm
  rw [afterLetter_prefix s g post sAbsentG,
    afterLetter_append_absent s g' (t :: post') sAbsentG', afterLetter, if_neg ts] at old
  have future : t ∈ afterLetter s post' := (optional_support old t).mp tInPost
  have absent : t ∉ post' := simple_separator_absent g' post' t (rightSimple t tInTarget ht)
  exact False.elim (absent (afterLetter_subset s post' t future))

theorem markedObservation_tail (ns g post g' post' : List Nat) (s : Nat)
    (leftCovered : ∀ a ∈ g, a ∈ ns) (rightCovered : ∀ a ∈ g', a ∈ ns)
    (hs : s ∉ ns) (leftAbsent : s ∉ post)
    (obs : MarkedObservation ns (g ++ s :: post) (g' ++ s :: post')) :
    MarkedObservation ns post post' := by
  have key := obs.2 s (List.mem_append.mpr (Or.inr (List.Mem.head _))) hs
  rw [afterLetter_prefix s g post (covered_avoids ns g leftCovered s hs),
    afterLetter_prefix s g' post' (covered_avoids ns g' rightCovered s hs)] at key
  refine ⟨key,?_⟩
  intro a ha hn
  have ne : s ≠ a := fun eq => leftAbsent (eq.symm ▸ ha)
  have old := obs.2 a (List.mem_append.mpr (Or.inr (List.Mem.tail _ ha))) hn
  have left : afterLetter a (g ++ s :: post) = afterLetter a post := by
    rw [afterLetter_append_absent a g (s :: post) (covered_avoids ns g leftCovered a hn)]
    rw [afterLetter, if_neg ne]
  have right : afterLetter a (g' ++ s :: post') = afterLetter a post' := by
    rw [afterLetter_append_absent a g' (s :: post') (covered_avoids ns g' rightCovered a hn)]
    rw [afterLetter, if_neg ne]
  rw [left,right] at old
  exact old

theorem markersSimple_word (u : Word Nat) : MarkersSimple (nonsimpleSupport u.toList) u.toList := by
  intro a ha hn
  exact (single_iff_not_nonsimple a u.toList ha).mpr hn

theorem sameObservation_marked {u v : Word Nat} (obs : SameObservation u v) :
    MarkedObservation (nonsimpleSupport u.toList) u.toList v.toList := by
  refine ⟨?_,?_⟩
  · cases u; cases v; exact obs.1
  · intro a ha hn
    exact obs.2.2 a (markersSimple_word u a ha hn)

end SemigroupBasis.CoRoots.Order6Day15.B16.Reach
