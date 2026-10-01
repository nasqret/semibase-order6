import SemigroupBasis.CoRoots.Order6Day15.B16.B16GapRender
import SemigroupBasis.CoRoots.Order6Day15.B16.B16CanonicalSupport

namespace SemigroupBasis.CoRoots.Order6Day15.B16.Reach

open SemigroupBasis.CoRoots.Order6Sunday.Msg0514RepairedSixteenLawFinite

def activeLetters (ns tail : List Nat) : List Nat := ns.filter (fun a => decide (a ∈ tail))

theorem mem_activeLetters (a : Nat) (ns tail : List Nat) :
    a ∈ activeLetters ns tail ↔ a ∈ ns ∧ a ∈ tail := by
  simp only [activeLetters, List.mem_filter, decide_eq_true_eq]

def leastActive (ns : List Nat) (a : Nat) (xs post : List Nat) : Nat :=
  (canonicalSupport (activeLetters ns (a :: (xs ++ post)))).headD a

theorem leastActive_spec (ns : List Nat) (a : Nat) (xs post : List Nat) (ha : a ∈ ns) :
    leastActive ns a xs post ∈ ns ∧
      (leastActive ns a xs post = a ∨ leastActive ns a xs post ∈ xs ++ post) ∧
      ∀ c ∈ ns, c ∈ a :: (xs ++ post) → leastActive ns a xs post ≤ c := by
  have aIn : a ∈ canonicalSupport (activeLetters ns (a :: (xs ++ post))) :=
    (mem_canonicalSupport a _).mpr ((mem_activeLetters a _ _).mpr ⟨ha,List.Mem.head _⟩)
  cases eq : canonicalSupport (activeLetters ns (a :: (xs ++ post))) with
  | nil =>
      rw [eq] at aIn
      exact False.elim (List.not_mem_nil aIn)
  | cons b bs =>
      have value : leastActive ns a xs post = b := by
        unfold leastActive
        rw [eq]
        rfl
      have bIn : b ∈ canonicalSupport (activeLetters ns (a :: (xs ++ post))) := by
        rw [eq]
        exact List.Mem.head _
      have selected : b ∈ ns ∧ b ∈ a :: (xs ++ post) :=
        (mem_activeLetters b _ _).mp ((mem_canonicalSupport b _).mp bIn)
      have sorted : List.Pairwise (fun x y : Nat => x < y) (b :: bs) :=
        eq ▸ canonicalSupport_sorted (activeLetters ns (a :: (xs ++ post)))
      simp only [value]
      refine ⟨selected.1, List.mem_cons.mp selected.2, ?_⟩
      intro c hc active
      have cIn : c ∈ canonicalSupport (activeLetters ns (a :: (xs ++ post))) :=
        (mem_canonicalSupport c _).mpr ((mem_activeLetters c _ _).mpr ⟨hc,active⟩)
      rw [eq] at cIn
      rcases List.mem_cons.mp cIn with same | tail
      · subst c; exact Nat.le_refl _
      · exact Nat.le_of_lt ((List.pairwise_cons.mp sorted).1 c tail)

theorem canonical_final_without_anchor (xs post : List Nat) (b c : Nat) :
    c ∈ canonicalSupport (finalLetters xs (b :: post)) ↔ c ∈ xs ∧ c ∉ post ∧ c ≠ b := by
  rw [mem_canonicalSupport, mem_finalLetters_iff]
  constructor
  · intro h
    refine ⟨h.1, ?_, ?_⟩
    · intro mem; exact h.2 (List.Mem.tail _ mem)
    · intro eq; exact h.2 (List.mem_cons.mpr (Or.inl eq))
  · intro h
    refine ⟨h.1, ?_⟩
    intro mem
    rcases List.mem_cons.mp mem with eq | tail
    · exact h.2.2 eq
    · exact h.2.1 tail

def renderedGap (ns : List Nat) : List Nat → List Nat → List Nat
  | [], _ => []
  | a :: xs, post =>
      if a ∈ xs ++ post then
        let b := leastActive ns a xs post
        b :: b :: squares (canonicalSupport (finalLetters (a :: xs) (b :: post)))
      else a :: squares (canonicalSupport (finalLetters xs post))

theorem renderedGap_nonempty (ns : List Nat) (a : Nat) (xs post : List Nat) :
    renderedGap ns (a :: xs) post ≠ [] := by
  by_cases later : a ∈ xs ++ post
  · rw [renderedGap, if_pos later]
    intro eq; cases eq
  · rw [renderedGap, if_neg later]
    intro eq; cases eq

/-- Uniform G: render exactly one gap while retaining its reservoir and all outside context. -/
theorem render_gap (ns pre gap post : List Nat) (covered : ∀ a ∈ gap, a ∈ ns) :
    Rel (squares ns ++ (pre ++ (gap ++ post)))
      (squares ns ++ (pre ++ (renderedGap ns gap post ++ post))) := by
  cases gap with
  | nil => exact Rel.refl _
  | cons a xs =>
      have ha : a ∈ ns := covered a (List.Mem.head _)
      have tailCovered : ∀ b ∈ xs, b ∈ ns := fun b hb => covered b (List.Mem.tail _ hb)
      by_cases later : a ∈ xs ++ post
      · let b := leastActive ns a xs post
        have choice := leastActive_spec ns a xs post ha
        have rendered := gap_render_unpinned ns pre a xs post b
          (canonicalSupport (finalLetters (a :: xs) (b :: post)))
          ha tailCovered later choice.1 choice.2.1
          (fun c => canonical_final_without_anchor (a :: xs) post b c)
        simpa only [renderedGap, if_pos later, List.cons_append] using rendered
      · have rendered := gap_render_preserving_head ns pre a xs post
          (canonicalSupport (finalLetters xs post)) ha tailCovered
          (fun c => (mem_canonicalSupport c _).trans (mem_finalLetters_iff c xs post))
        simpa only [renderedGap, if_neg later, List.cons_append] using rendered

theorem render_gap_framed (front ns pre gap post : List Nat) (covered : ∀ a ∈ gap, a ∈ ns) :
    Rel (front ++ (squares ns ++ (pre ++ (gap ++ post))))
      (front ++ (squares ns ++ (pre ++ (renderedGap ns gap post ++ post)))) :=
  Rel.prependCtx front (render_gap ns pre gap post covered)

theorem render_gap_derives (u v : Word Nat) (front ns pre gap post : List Nat)
    (source : u.toList = front ++ (squares ns ++ (pre ++ (gap ++ post))))
    (target : v.toList = front ++ (squares ns ++ (pre ++ (renderedGap ns gap post ++ post))))
    (covered : ∀ a ∈ gap, a ∈ ns) : Derives basis u v := by
  have actual : Rel u.toList v.toList := by
    rw [source,target]
    exact render_gap_framed front ns pre gap post covered
  exact Rel.toDerives actual

end SemigroupBasis.CoRoots.Order6Day15.B16.Reach
