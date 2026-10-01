import SemigroupBasis.CoRoots.Order6Astra.C8TailProbe

namespace SemigroupBasis.CoRoots.Order6Astra.C8TailCuts

open C8TailProbe
open Order6SporadicSection19.Published.SemanticSimpleAdjacency

def SameSupport (u v : List Nat) : Prop := ∀ x, x ∈ u ↔ x ∈ v
def Disjoint (u v : List Nat) : Prop := ∀ x ∈ u, x ∉ v

/-- The support of any trailing sequence of prefix components avoiding the
suffix. Empty tails are permitted; empty semigroup substitutions are not used. -/
def Tail (before after support : List Nat) : Prop :=
  ∃ a b : List Nat, before = a ++ b ∧ SameSupport b support ∧ Disjoint b (a ++ after)

theorem allE_iff (d : Nat → Bool) (xs : List Nat) :
    allE d xs = true ↔ ∀ x ∈ xs, d x = false := by
  simp only [allE, List.all_eq_true]
  constructor
  · intro h x hx
    have n := h x hx
    cases dx : d x <;> simp_all
  · intro h x hx
    rw [h x hx]
    rfl

theorem allD_iff (d : Nat → Bool) (xs : List Nat) :
    allD d xs = true ↔ ∀ x ∈ xs, d x = true := List.all_eq_true

theorem allD_ordered (d : Nat → Bool) (xs : List Nat) (h : allD d xs = true) :
    ordered d xs = true := by
  cases xs with
  | nil => rfl
  | cons x xs =>
    have both : d x = true ∧ allD d xs = true := by
      simpa only [allD, List.all_cons, Bool.and_eq_true] using h
    simp only [ordered, both.1]
    exact both.2

theorem ordered_append_allE (d : Nat → Bool) (a b : List Nat)
    (ha : allE d a = true) : ordered d (a ++ b) = ordered d b := by
  induction a with
  | nil => rfl
  | cons x a ih =>
    have hx : d x = false := (allE_iff d (x :: a)).mp ha x List.mem_cons_self
    have ht : allE d a = true := (allE_iff d a).mpr
      (fun y hy => (allE_iff d (x :: a)).mp ha y (List.mem_cons_of_mem x hy))
    simp only [List.cons_append, ordered, hx, Bool.false_eq_true, if_false]
    exact ih ht

theorem ordered_iff_cut (d : Nat → Bool) (xs : List Nat) :
    ordered d xs = true ↔
      ∃ a b : List Nat, xs = a ++ b ∧ allE d a = true ∧ allD d b = true := by
  constructor
  · intro h
    induction xs with
    | nil => exact ⟨[], [], rfl, rfl, rfl⟩
    | cons x xs ih =>
      cases hx : d x with
      | true =>
        have ht : allD d xs = true := by simpa only [ordered, hx, if_true] using h
        refine ⟨[], x :: xs, rfl, rfl, ?_⟩
        simp only [allD, List.all_cons, hx, Bool.true_and]
        exact ht
      | false =>
        have ht : ordered d xs = true := by
          simpa only [ordered, hx, Bool.false_eq_true, if_false] using h
        obtain ⟨a, b, eq, ea, db⟩ := ih ht
        refine ⟨x :: a, b, ?_, ?_, db⟩
        · simp only [List.cons_append, eq]
        · simp only [allE, List.all_cons, hx, Bool.not_false, Bool.true_and]
          exact ea
  · rintro ⟨a, b, rfl, ea, db⟩
    rw [ordered_append_allE d a b ea]
    exact allD_ordered d b db

def indicator (support : List Nat) (x : Nat) : Bool := decide (x ∈ support)

theorem indicator_true (support : List Nat) (x : Nat) :
    indicator support x = true ↔ x ∈ support := by simp only [indicator, decide_eq_true_eq]

theorem indicator_false (support : List Nat) (x : Nat) :
    indicator support x = false ↔ x ∉ support := by simp only [indicator, decide_eq_false_iff_not]

theorem tail_coverage (p s z : List Nat) (h : Tail p s z) :
    ∀ x ∈ z, x ∈ p := by
  obtain ⟨a, b, split, same, _⟩ := h
  intro x hx
  rw [split]
  exact List.mem_append.mpr (Or.inr ((same x).mpr hx))

/-- A binary cut query recovers its entire support, provided the tested support
is present in the word. It cannot hide extra letters outside the word. -/
theorem query_iff_tail (p s z : List Nat) (covered : ∀ x ∈ z, x ∈ p ++ s) :
    ((ordered (indicator z) p && allE (indicator z) s) = true) ↔ Tail p s z := by
  constructor
  · intro h
    have both : ordered (indicator z) p = true ∧ allE (indicator z) s = true := by
      simpa only [Bool.and_eq_true] using h
    obtain ⟨a, b, split, ea, db⟩ := (ordered_iff_cut (indicator z) p).mp both.1
    have avoidA : ∀ x ∈ a, x ∉ z := fun x hx =>
      (indicator_false z x).mp ((allE_iff _ _).mp ea x hx)
    have avoidS : ∀ x ∈ s, x ∉ z := fun x hx =>
      (indicator_false z x).mp ((allE_iff _ _).mp both.2 x hx)
    have insideB : ∀ x ∈ b, x ∈ z := fun x hx =>
      (indicator_true z x).mp ((allD_iff _ _).mp db x hx)
    refine ⟨a, b, split, ?_, ?_⟩
    · intro x
      constructor
      · exact insideB x
      · intro hx
        have present := covered x hx
        rw [split] at present
        rcases List.mem_append.mp present with inP | inS
        · rcases List.mem_append.mp inP with inA | inB
          · exact False.elim (avoidA x inA hx)
          · exact inB
        · exact False.elim (avoidS x inS hx)
    · intro x hx present
      rcases List.mem_append.mp present with inA | inS
      · exact avoidA x inA (insideB x hx)
      · exact avoidS x inS (insideB x hx)
  · rintro ⟨a, b, split, same, disjoint⟩
    have ea : allE (indicator z) a = true := by
      apply (allE_iff _ _).mpr
      intro x hx
      apply (indicator_false z x).mpr
      intro hz
      exact disjoint x ((same x).mpr hz) (List.mem_append.mpr (Or.inl hx))
    have db : allD (indicator z) b = true := by
      apply (allD_iff _ _).mpr
      intro x hx
      exact (indicator_true z x).mpr ((same x).mp hx)
    rw [Bool.and_eq_true]
    refine ⟨(ordered_iff_cut _ _).mpr ⟨a, b, split, ea, db⟩, ?_⟩
    apply (allE_iff _ _).mpr
    intro x hx
    apply (indicator_false z x).mpr
    intro hz
    exact disjoint x ((same x).mpr hz) (List.mem_append.mpr (Or.inr hx))

theorem semantic_support (u v : Word Nat) (same : EqualEval u v) :
    SameSupport u.toList v.toList := by
  intro x
  have zero := (semantic_occurrence_categories u v same x).1
  constructor
  · intro hx
    apply Classical.byContradiction
    intro absent
    exact List.count_eq_zero.mp (zero.mpr (List.count_eq_zero.mpr absent)) hx
  · intro hx
    apply Classical.byContradiction
    intro absent
    exact List.count_eq_zero.mp (zero.mp (List.count_eq_zero.mpr absent)) hx

theorem semantic_tail_forward (u v : Word Nat) (same : EqualEval u v)
    (t : Nat) (p s q r z : List Nat) (hu : u.toList = p ++ t :: s)
    (hv : v.toList = q ++ t :: r) (simple : u.toList.count t = 1)
    (tail : Tail p s z) : Tail q r z := by
  have simpleV : v.toList.count t = 1 :=
    (semantic_occurrence_categories u v same t).2.1.mp simple
  have cover := tail_coverage p s z tail
  have counts : p.count t + (s.count t + 1) = 1 := by
    simpa only [hu, List.count_append, List.count_cons_self] using simple
  have absent : t ∉ p := List.count_eq_zero.mp (by omega)
  have coverTarget : ∀ x ∈ z, x ∈ q ++ r := by
    intro x hx
    have inU : x ∈ u.toList := by
      rw [hu]
      exact List.mem_append.mpr (Or.inl (cover x hx))
    have inV := (semantic_support u v same x).mp inU
    rw [hv] at inV
    rcases List.mem_append.mp inV with inQ | later
    · exact List.mem_append.mpr (Or.inl inQ)
    · rcases List.mem_cons.mp later with equal | inR
      · subst x
        exact False.elim (absent (cover t hx))
      · exact List.mem_append.mpr (Or.inr inR)
  apply (query_iff_tail q r z coverTarget).mp
  rw [← equal_eval_cut u v same t p s q r hu hv simple simpleV (indicator z)]
  exact (query_iff_tail p s z
    (fun x hx => List.mem_append.mpr (Or.inl (cover x hx)))).mpr tail

/-- The complete family of suffix-cut supports at every simple marker is an
unrestricted semantic invariant of the literal C8 table. -/
theorem semantic_tail_iff (u v : Word Nat) (same : EqualEval u v)
    (t : Nat) (p s q r z : List Nat) (hu : u.toList = p ++ t :: s)
    (hv : v.toList = q ++ t :: r) (simple : u.toList.count t = 1) :
    Tail p s z ↔ Tail q r z := by
  constructor
  · exact semantic_tail_forward u v same t p s q r z hu hv simple
  · have simpleV : v.toList.count t = 1 :=
      (semantic_occurrence_categories u v same t).2.1.mp simple
    exact semantic_tail_forward v u (fun a => (same a).symm) t q r p s z hv hu simpleV

end SemigroupBasis.CoRoots.Order6Astra.C8TailCuts

#print axioms SemigroupBasis.CoRoots.Order6Astra.C8TailCuts.ordered_iff_cut
#print axioms SemigroupBasis.CoRoots.Order6Astra.C8TailCuts.query_iff_tail
#print axioms SemigroupBasis.CoRoots.Order6Astra.C8TailCuts.semantic_tail_iff
