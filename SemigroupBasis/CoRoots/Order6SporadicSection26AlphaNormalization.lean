import SemigroupBasis.CoRoots.Order6SporadicSection26AlphaForms

/-! Arbitrary-word loose alpha normalization by right insertion.
Only the exact raw basis and the unrestricted pair-absorption theorem are
used. Powers are still positive and unbounded at this intermediate stage. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection26.F7
open SemigroupBasis
namespace AlphaForm

def extendLast (init : AlphaForm) (head extra y : Nat) : AlphaForm :=
  if head = y then snoc init head (extra + 1) none
  else snoc init head extra (some y)

theorem heads_extendLast (init : AlphaForm) (head extra y : Nat) :
    (extendLast init head extra y).heads = init.heads ++ [head] := by
  unfold extendLast
  split <;> rfl

theorem valid_extendLast (init : AlphaForm) (head extra y : Nat)
    (valid : init.Valid) (fresh : head ∉ init.heads)
    (seen : y ∈ init.heads ++ [head]) : (extendLast init head extra y).Valid := by
  unfold extendLast
  split
  · exact ⟨valid, fresh, by simp⟩
  · rename_i different
    have old : y ∈ init.heads := by simpa [different, Ne.symm different] using seen
    exact ⟨valid, fresh, by simpa using old⟩

theorem render_extendLast (init : AlphaForm) (head extra y : Nat) :
    (extendLast init head extra y).render = init.render ++ (headRun head extra ++ [y]) := by
  by_cases same : head = y
  · subst y
    unfold extendLast
    rw [if_pos (show head = head from rfl)]
    change init.render ++ (headRun head (extra + 1) ++ []) =
      init.render ++ (headRun head extra ++ [head])
    rw [List.append_nil]
    exact congrArg (fun xs => init.render ++ xs) (headRun_append_head head extra).symm
  · simp [extendLast, same, render]

def push (form : AlphaForm) (y : Nat) : AlphaForm :=
  if y ∈ form.heads then
    match form with
    | nil => nil
    | snoc init head extra none => extendLast init head extra y
    | snoc init head extra (some x) => extendLast (init.bump x) head extra y
  else snoc form y 0 none

theorem heads_push (form : AlphaForm) (y : Nat) :
    (form.push y).heads =
      if y ∈ form.heads then form.heads else form.heads ++ [y] := by
  by_cases seen : y ∈ form.heads
  · simp only [push, if_pos seen]
    cases form with
    | nil => rfl
    | snoc init head extra tail =>
        cases tail <;> simp only [heads_extendLast, heads_bump, heads]
  · simp only [push, if_neg seen, heads]

theorem valid_push (form : AlphaForm) (y : Nat) (valid : form.Valid) :
    (form.push y).Valid := by
  by_cases seen : y ∈ form.heads
  · cases form with
    | nil => simp [heads] at seen
    | snoc init head extra tail =>
        rcases valid with ⟨initValid, fresh, earlier⟩
        cases tail with
        | none =>
            simp only [push, if_pos seen]
            exact valid_extendLast init head extra y initValid fresh seen
        | some x =>
            simp only [push, if_pos seen]
            apply valid_extendLast (init.bump x) head extra y (valid_bump init x initValid)
            · simpa only [heads_bump] using fresh
            · simpa only [heads_bump] using seen
  · simp only [push, if_neg seen]
    exact ⟨valid, seen, by simp⟩

theorem derives_push (form : AlphaForm) (y : Nat) (valid : form.Valid) :
    ListDerives (form.render ++ [y]) (form.push y).render := by
  by_cases seen : y ∈ form.heads
  · cases form with
    | nil => simp [heads] at seen
    | snoc init head extra tail =>
        rcases valid with ⟨initValid, fresh, earlier⟩
        cases tail with
        | none =>
            simp only [push, if_pos seen]
            rw [render_extendLast]
            simpa [render, List.append_assoc] using
              (S5_107.ListDerives.refl (basis := basis) (init.render ++ (headRun head extra ++ [y])))
        | some x =>
            have oldX : x ∈ init.heads := earlier x (by simp)
            have different : head ≠ x := by
              intro same
              subst x
              exact fresh oldX
            let stem : AlphaForm := snoc init head extra none
            have stemValid : stem.Valid := ⟨initValid, fresh, by simp⟩
            have seenX : x ∈ stem.heads := by simp [stem, heads, oldX]
            have seenY : y ∈ stem.heads := seen
            have raw := absorbPair stem.render x y
              ((mem_render_iff stem x stemValid).mpr seenX)
              ((mem_render_iff stem y stemValid).mpr seenY)
            have bumped : bumpFirst x stem.render = (init.bump x).render ++ headRun head extra := by
              rw [bumpFirst_render stem x stemValid seenX]
              simp [stem, bump, different, render]
            rw [bumped] at raw
            simp only [push, if_pos seen]
            rw [render_extendLast]
            simpa [stem, render, List.append_assoc] using raw
  · simp only [push, if_neg seen]
    simpa [render, headRun] using
      (S5_107.ListDerives.refl (basis := basis) (form.render ++ [y]))

def insertAll (form : AlphaForm) : List Nat → AlphaForm
  | [] => form
  | y :: rest => insertAll (form.push y) rest

theorem valid_insertAll (form : AlphaForm) (letters : List Nat) (valid : form.Valid) :
    (form.insertAll letters).Valid := by
  induction letters generalizing form with
  | nil => exact valid
  | cons y rest ih => exact ih (form.push y) (valid_push form y valid)

theorem derives_insertAll (form : AlphaForm) (letters : List Nat) (valid : form.Valid) :
    ListDerives (form.render ++ letters) (form.insertAll letters).render := by
  induction letters generalizing form with
  | nil => simpa [insertAll] using (S5_107.ListDerives.refl (basis := basis) form.render)
  | cons y rest ih =>
      have first := (derives_push form y valid).append rest
      have remaining := ih (form.push y) (valid_push form y valid)
      simpa [insertAll, List.append_assoc] using first.trans remaining

end AlphaForm

def normalizeAlpha (letters : List Nat) : AlphaForm := AlphaForm.nil.insertAll letters

theorem normalizeAlpha_valid (letters : List Nat) : (normalizeAlpha letters).Valid :=
  AlphaForm.valid_insertAll AlphaForm.nil letters trivial

theorem derives_normalizeAlpha (letters : List Nat) :
    ListDerives letters (normalizeAlpha letters).render := by
  simpa [normalizeAlpha, AlphaForm.render] using
    AlphaForm.derives_insertAll AlphaForm.nil letters trivial

theorem exists_loose_alpha (word : Word Nat) :
    ∃ form : AlphaForm, form.Valid ∧ form.render ≠ [] ∧ ListDerives word.toList form.render := by
  refine ⟨normalizeAlpha word.toList, normalizeAlpha_valid word.toList, ?_,
    derives_normalizeAlpha word.toList⟩
  exact S5_107.ListDerives.target_ne_nil (derives_normalizeAlpha word.toList)

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.AlphaForm.heads_extendLast
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.AlphaForm.valid_extendLast
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.AlphaForm.render_extendLast
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.AlphaForm.heads_push
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.AlphaForm.valid_push
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.AlphaForm.derives_push
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.AlphaForm.valid_insertAll
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.AlphaForm.derives_insertAll
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.normalizeAlpha_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.derives_normalizeAlpha
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.exists_loose_alpha
end SemigroupBasis.CoRoots.Order6SporadicSection26.F7
