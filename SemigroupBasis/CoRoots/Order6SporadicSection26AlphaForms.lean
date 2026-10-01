import SemigroupBasis.CoRoots.Order6SporadicSection26Absorption

/-! Loose published alpha forms: fresh heads, positive powers, and tails that
are empty or one strictly earlier head. This is syntax and its proved
invariants, not an assumed normalization or completeness interface. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection26.F7
open SemigroupBasis

def headRun (head extra : Nat) : List Nat := head :: List.replicate extra head

theorem mem_headRun (x head extra : Nat) : x ∈ headRun head extra ↔ x = head := by
  induction extra with
  | zero => simp [headRun]
  | succ n ih =>
      change x ∈ head :: headRun head n ↔ x = head
      simp only [List.mem_cons, ih, or_self]

theorem headRun_append_head (head extra : Nat) :
    headRun head extra ++ [head] = headRun head (extra + 1) := by
  induction extra with
  | zero => rfl
  | succ n ih =>
      change head :: (headRun head n ++ [head]) = head :: headRun head (n + 1)
      exact congrArg (List.cons head) ih

inductive AlphaForm where
  | nil
  | snoc (init : AlphaForm) (head extra : Nat) (tail : Option Nat)
  deriving DecidableEq

namespace AlphaForm

def heads : AlphaForm → List Nat
  | nil => []
  | snoc init head _ _ => init.heads ++ [head]

def render : AlphaForm → List Nat
  | nil => []
  | snoc init head extra tail => init.render ++ (headRun head extra ++ tail.toList)

def Valid : AlphaForm → Prop
  | nil => True
  | snoc init head _ tail =>
      init.Valid ∧ head ∉ init.heads ∧ ∀ x ∈ tail.toList, x ∈ init.heads

def bump (form : AlphaForm) (x : Nat) : AlphaForm :=
  match form with
  | nil => nil
  | snoc init head extra tail =>
      if head = x then snoc init head (extra + 1) tail
      else snoc (init.bump x) head extra tail

theorem heads_bump (form : AlphaForm) (x : Nat) : (form.bump x).heads = form.heads := by
  induction form with
  | nil => rfl
  | snoc init head extra tail ih =>
      simp only [bump]
      split
      · rfl
      · simpa only [heads] using congrArg (fun xs => xs ++ [head]) ih

theorem valid_bump (form : AlphaForm) (x : Nat) (valid : form.Valid) :
    (form.bump x).Valid := by
  induction form with
  | nil => trivial
  | snoc init head extra tail ih =>
      rcases valid with ⟨initValid, fresh, earlier⟩
      simp only [bump]
      split
      · exact ⟨initValid, fresh, earlier⟩
      · refine ⟨ih initValid, ?_, ?_⟩
        · simpa only [heads_bump] using fresh
        · simpa only [heads_bump] using earlier

theorem mem_render_iff (form : AlphaForm) (x : Nat) (valid : form.Valid) :
    x ∈ form.render ↔ x ∈ form.heads := by
  induction form with
  | nil => rfl
  | snoc init head extra tail ih =>
      rcases valid with ⟨initValid, fresh, earlier⟩
      simp only [render, heads, List.mem_append, List.mem_singleton, mem_headRun,
        ih initValid]
      constructor
      · intro present
        rcases present with old | same | inTail
        · exact Or.inl old
        · exact Or.inr same
        · exact Or.inl (earlier x inTail)
      · intro present
        rcases present with old | same
        · exact Or.inl old
        · exact Or.inr (Or.inl same)

theorem render_eq_nil_iff (form : AlphaForm) : form.render = [] ↔ form = nil := by
  cases form <;> simp [render, headRun]

end AlphaForm

theorem bumpFirst_append_of_mem (x : Nat) (before after : List Nat)
    (present : x ∈ before) :
    bumpFirst x (before ++ after) = bumpFirst x before ++ after := by
  induction before with
  | nil => simp at present
  | cons head tail ih =>
      by_cases same : head = x
      · simp only [List.cons_append, bumpFirst, if_pos same]
      · have inTail : x ∈ tail := by simpa [same, Ne.symm same] using present
        simp only [List.cons_append, bumpFirst, if_neg same, ih inTail]

namespace AlphaForm

theorem bumpFirst_render (form : AlphaForm) (x : Nat)
    (valid : form.Valid) (present : x ∈ form.heads) :
    bumpFirst x form.render = (form.bump x).render := by
  induction form with
  | nil => simp [heads] at present
  | snoc init head extra tail ih =>
      rcases valid with ⟨initValid, fresh, earlier⟩
      by_cases same : head = x
      · subst x
        have missing : head ∉ init.render := by
          intro inRender
          exact fresh ((mem_render_iff init head initValid).mp inRender)
        simp only [bump, render]
        rw [bumpFirst_append_of_not_mem head init.render
          (headRun head extra ++ tail.toList) missing]
        simp [render, headRun, bumpFirst, List.replicate_succ]
      · have inInit : x ∈ init.heads := by
          simpa [heads, same, Ne.symm same] using present
        have inRender : x ∈ init.render := (mem_render_iff init x initValid).mpr inInit
        simp only [bump, if_neg same, render]
        rw [bumpFirst_append_of_mem x init.render (headRun head extra ++ tail.toList) inRender]
        rw [ih initValid inInit]

end AlphaForm

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.mem_headRun
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.headRun_append_head
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.AlphaForm.heads_bump
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.AlphaForm.valid_bump
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.AlphaForm.mem_render_iff
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.AlphaForm.render_eq_nil_iff
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.bumpFirst_append_of_mem
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.AlphaForm.bumpFirst_render
end SemigroupBasis.CoRoots.Order6SporadicSection26.F7
