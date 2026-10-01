import SemigroupBasis.CoRoots.Order6Astra.C8Star

namespace SemigroupBasis.CoRoots.Order6Astra.C8StarRecursion

open Order6SporadicSection19.Published
open C8TailCuts C8ListDerives C8Star C8BranchAlgebra

def withLast (leading : List Nat) (marker : Nat) : Word Nat :=
  match leading with
  | [] => Word.singleton marker
  | x :: xs => ⟨x, xs ++ [marker]⟩

theorem withLast_list (leading : List Nat) (marker : Nat) :
    (withLast leading marker).toList = leading ++ [marker] := by
  cases leading <;> rfl

def Marked (property : List Nat → Prop) (word : Word Nat) : Prop :=
  ∃ leading : List Nat, ∃ marker : Nat,
    word.toList = leading ++ [marker] ∧ marker ∉ leading ∧ property leading

theorem lift_marked (property : List Nat → Prop) (word : Word Nat)
    (leading : List Nat) (marker : Nat) (literal : word.toList = leading ++ [marker])
    (fresh : marker ∉ leading) (normal : List Nat) (derived : Rel leading normal)
    (good : property normal) :
    ∃ next : Word Nat, Derives basis word next ∧ Marked property next := by
  refine ⟨withLast normal marker, ?_, normal, marker, withLast_list normal marker, ?_, good⟩
  · apply to_words
    rw [literal, withLast_list]
    exact C8ListDerives.append derived (C8ListDerives.refl [marker])
  · intro present
    exact fresh ((C8ListDerives.support derived marker).mpr present)

theorem choose_branches (property : List Nat → Prop) (branches : List (Word Nat))
    (available : ∀ branch ∈ branches, ∃ next : Word Nat,
      Derives basis branch next ∧ Marked property next) :
    ∃ next : List (Word Nat), Aligned (Derives basis) branches next ∧
      ∀ branch ∈ next, Marked property branch := by
  induction branches with
  | nil => exact ⟨[], Aligned.nil, fun _ h => False.elim (List.not_mem_nil h)⟩
  | cons first rest ih =>
    obtain ⟨next, headDerived, headGood⟩ := available first List.mem_cons_self
    obtain ⟨tail, tailDerived, tailGood⟩ := ih
      (fun b hb => available b (List.mem_cons_of_mem first hb))
    refine ⟨next :: tail, Aligned.cons headDerived tailDerived, ?_⟩
    intro b hb
    rcases List.mem_cons.mp hb with same | later
    · subst b
      exact headGood
    · exact tailGood b later

theorem aligned_back {α β : Type} {relation : α → β → Prop} {left : List α} {right : List β}
    (aligned : Aligned relation left right) (value : β) (member : value ∈ right) :
    ∃ original ∈ left, relation original value := by
  induction aligned with
  | nil => cases member
  | @cons x xs y ys head tail ih =>
    rcases List.mem_cons.mp member with same | later
    · subst value
      exact ⟨x, List.mem_cons_self, head⟩
    · obtain ⟨original, present, related⟩ := ih later
      exact ⟨original, List.mem_cons_of_mem x present, related⟩

theorem aligned_pairwise {left right : List (Word Nat)}
    (aligned : Aligned (Derives basis) left right)
    (pairwise : left.Pairwise (fun a b => Disjoint a.toList b.toList)) :
    right.Pairwise (fun a b => Disjoint a.toList b.toList) := by
  induction aligned with
  | nil => exact List.Pairwise.nil
  | @cons x xs y ys head tail ih =>
    have both := List.pairwise_cons.mp pairwise
    apply List.pairwise_cons.mpr
    refine ⟨?_, ih both.2⟩
    intro other member value inY inOther
    obtain ⟨original, present, related⟩ := aligned_back tail other member
    exact both.1 original present value
      ((C8ListDerives.support (of_words head) value).mpr inY)
      ((C8ListDerives.support (of_words related) value).mpr inOther)

theorem chain_aligned (separator : Word Nat) {left right : List (Word Nat)}
    (aligned : Aligned (Derives basis) left right) :
    Derives basis (chain separator left) (chain separator right) := by
  induction aligned with
  | nil => exact Derives.refl _
  | @cons x xs y ys head tail ih =>
    exact (Derives.appendRight (Derives.prepend separator head) (chain separator xs)).trans
      (Derives.prepend (separator ++ y) ih)

/-- Recursive prefix derivations are lifted through the actual marked branch
words. The new star's support conditions are transported by soundness. -/
theorem rewrite_star (property : List Nat → Prop) (star : Star)
    (available : ∀ branch ∈ star.branches, ∃ next : Word Nat,
      Derives basis branch next ∧ Marked property next) :
    ∃ next : Star, Derives basis star.word next.word ∧
      ∀ branch ∈ next.branches, Marked property branch := by
  obtain ⟨branches, aligned, good⟩ := choose_branches property star.branches available
  have apart : ∀ branch ∈ branches, Disjoint branch.toList star.root.toList := by
    intro branch member value inside contrary
    obtain ⟨original, present, related⟩ := aligned_back aligned branch member
    exact star.apart original present value
      ((C8ListDerives.support (of_words related) value).mpr inside) contrary
  have marked : ∀ branch ∈ branches, ∃ leading : List Nat, ∃ marker : Nat,
      branch.toList = leading ++ [marker] ∧ marker ∉ leading := by
    intro branch member
    obtain ⟨leading, marker, literal, fresh, _⟩ := good branch member
    exact ⟨leading, marker, literal, fresh⟩
  let next : Star := ⟨star.root, branches, star.shape,
    aligned_pairwise aligned star.pairwise, apart, marked⟩
  exact ⟨next, chain_aligned (star.root ++ star.root) aligned, good⟩

end SemigroupBasis.CoRoots.Order6Astra.C8StarRecursion

#print axioms SemigroupBasis.CoRoots.Order6Astra.C8StarRecursion.lift_marked
#print axioms SemigroupBasis.CoRoots.Order6Astra.C8StarRecursion.rewrite_star
