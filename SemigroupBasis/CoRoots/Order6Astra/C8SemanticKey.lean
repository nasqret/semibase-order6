import SemigroupBasis.CoRoots.Order6Astra.C8TailCuts
import SemigroupBasis.CoRoots.Order6SporadicSection19PublishedConnectedNormalization

namespace SemigroupBasis.CoRoots.Order6Astra.C8SemanticKey

open C8TailCuts Examples
open Order6SporadicSection19.Published
open SemanticSimpleAdjacency ConnectedNormalization

/-- All disjoint prefix cuts, including the two empty-context boundary cuts. -/
def Cut (letters support : List Nat) : Prop :=
  ∃ left right, letters = left ++ right ∧ SameSupport left support ∧ Disjoint left right

def TailAt (letters : List Nat) (marker : Nat) (support : List Nat) : Prop :=
  ∃ before after, letters = before ++ marker :: after ∧ Tail before after support

/-- Retain the report's full-prefix flag explicitly. -/
def FullAt (letters : List Nat) (marker : Nat) : Prop :=
  ∃ before after, letters = before ++ marker :: after ∧ Disjoint before after

structure Key (left right : List Nat) : Prop where
  support : SameSupport left right
  simple : ∀ marker, left.count marker = 1 ↔ right.count marker = 1
  cuts : ∀ support, Cut left support ↔ Cut right support
  tails : ∀ marker, left.count marker = 1 → ∀ support,
    TailAt left marker support ↔ TailAt right marker support
  full : ∀ marker, left.count marker = 1 → (FullAt left marker ↔ FullAt right marker)

theorem small_equal (u v : Word Nat) (same : EqualEval u v) :
    ∀ valuation : Nat → Fin 4,
      connectedComponentFour.semigroup.eval valuation u =
        connectedComponentFour.semigroup.eval valuation v := by
  intro valuation
  apply includeFour_injective
  rw [includeFour_eval, includeFour_eval]
  exact same _

theorem cut_forward (u v : Word Nat) (same : EqualEval u v) (z : List Nat)
    (cut : Cut u.toList z) : Cut v.toList z := by
  obtain ⟨left, right, split, support, disjoint⟩ := cut
  by_cases emptyLeft : left = []
  · subst left
    refine ⟨[], v.toList, rfl, support, ?_⟩
    intro x impossible
    cases impossible
  by_cases emptyRight : right = []
  · subst right
    have whole : u.toList = left := by simpa only [List.append_nil] using split
    refine ⟨v.toList, [], (List.append_nil _).symm, ?_, ?_⟩
    · intro x
      exact ((semantic_support u v same x).symm.trans
        (by simpa only [whole] using support x))
    · intro x _ impossible
      cases impossible
  have covered : ∀ x, x ∈ z → x ∈ u.toList := by
    intro x hx
    rw [split]
    exact List.mem_append.mpr (Or.inl ((support x).mpr hx))
  have actual : connectedComponentFourPrefixUnionCut z u.toList :=
    ⟨left, right, split, emptyLeft, emptyRight, support, disjoint⟩
  obtain ⟨left', right', split', _, _, support', disjoint'⟩ :=
    (connectedComponentFourEqualEval_prefixUnionCut_iff u v (small_equal u v same)
      z covered).mp actual
  exact ⟨left', right', split', support', disjoint'⟩

theorem marker_absent (letters before after : List Nat) (marker : Nat)
    (split : letters = before ++ marker :: after) (simple : letters.count marker = 1) :
    marker ∉ before ∧ marker ∉ after := by
  have counts : before.count marker + (after.count marker + 1) = 1 := by
    simpa only [split, List.count_append, List.count_cons_self] using simple
  exact ⟨List.count_eq_zero.mp (by omega), List.count_eq_zero.mp (by omega)⟩

theorem tailAt_forward (u v : Word Nat) (same : EqualEval u v) (t : Nat)
    (simple : u.toList.count t = 1) (z : List Nat) (tail : TailAt u.toList t z) :
    TailAt v.toList t z := by
  obtain ⟨p, s, split, tail⟩ := tail
  have present : t ∈ u.toList := by
    rw [split]
    exact List.mem_append.mpr (Or.inr List.mem_cons_self)
  obtain ⟨q, r, target⟩ := List.mem_iff_append.mp ((semantic_support u v same t).mp present)
  exact ⟨q, r, target, (semantic_tail_iff u v same t p s q r z split target simple).mp tail⟩

theorem fullAt_forward (u v : Word Nat) (same : EqualEval u v) (t : Nat)
    (simple : u.toList.count t = 1) (full : FullAt u.toList t) : FullAt v.toList t := by
  obtain ⟨p, s, split, disjoint⟩ := full
  have absent := marker_absent u.toList p s t split simple
  have present : t ∈ u.toList := by
    rw [split]
    exact List.mem_append.mpr (Or.inr List.mem_cons_self)
  have covered : ∀ x, x ∈ p → x ∈ u.toList := by
    intro x hx
    rw [split]
    exact List.mem_append.mpr (Or.inl hx)
  have actual : connectedComponentFourUnaryCut p t u.toList :=
    ⟨p, s, split, (fun _ => Iff.rfl), absent.2, disjoint⟩
  obtain ⟨q, r, target, _, _, apart⟩ :=
    (connectedComponentFourEqualEval_unaryCut_iff u v (small_equal u v same)
      p t absent.1 present covered).mp actual
  exact ⟨q, r, target, apart⟩

/-- Necessary semantic data are proved on arbitrary words. The full flag is
not omitted on the strength of an unproved redundancy argument. -/
theorem semantic_key (u v : Word Nat) (same : EqualEval u v) : Key u.toList v.toList := by
  have reverse : EqualEval v u := fun valuation => (same valuation).symm
  refine ⟨semantic_support u v same, ?_, ?_, ?_, ?_⟩
  · intro t
    exact (semantic_occurrence_categories u v same t).2.1
  · intro z
    exact ⟨cut_forward u v same z, cut_forward v u reverse z⟩
  · intro t simple z
    have simpleV := (semantic_occurrence_categories u v same t).2.1.mp simple
    exact ⟨tailAt_forward u v same t simple z, tailAt_forward v u reverse t simpleV z⟩
  · intro t simple
    have simpleV := (semantic_occurrence_categories u v same t).2.1.mp simple
    exact ⟨fullAt_forward u v same t simple, fullAt_forward v u reverse t simpleV⟩

theorem Key.symm {u v : List Nat} (key : Key u v) : Key v u := by
  refine ⟨fun x => (key.support x).symm, fun t => (key.simple t).symm,
    fun z => (key.cuts z).symm, ?_, ?_⟩
  · intro t simple z
    exact (key.tails t ((key.simple t).mpr simple) z).symm
  · intro t simple
    exact (key.full t ((key.simple t).mpr simple)).symm

theorem Key.trans {u v w : List Nat} (first : Key u v) (second : Key v w) : Key u w := by
  refine ⟨fun x => (first.support x).trans (second.support x),
    fun t => (first.simple t).trans (second.simple t),
    fun z => (first.cuts z).trans (second.cuts z), ?_, ?_⟩
  · intro t simple z
    exact (first.tails t simple z).trans (second.tails t ((first.simple t).mp simple) z)
  · intro t simple
    exact (first.full t simple).trans (second.full t ((first.simple t).mp simple))

end SemigroupBasis.CoRoots.Order6Astra.C8SemanticKey

#print axioms SemigroupBasis.CoRoots.Order6Astra.C8SemanticKey.semantic_key
#print axioms SemigroupBasis.CoRoots.Order6Astra.C8SemanticKey.Key.trans
