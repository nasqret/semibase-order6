import SemigroupBasis.CoRoots.Order6SporadicSection19PublishedPropagation

namespace SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MiddleSweep

open CrossFactor CrossSweep CrossLeftSweep AnchorPropagation

theorem join_assoc (left middle right : Option (Word Nat)) :
    joinGap (joinGap left middle) right = joinGap left (joinGap middle right) := by
  cases left <;> cases middle <;> cases right <;>
    simp only [joinGap, Word.append_assoc]

/-- Exact optional-word representation of the marked middle, without a
bound on the number of marked occurrences or the size of any separator. -/
def foldGap (substitution : Letter → Word Nat) : List Segment → Option (Word Nat)
  | [] => none
  | item :: tail => joinGap (pushGap item.1 (substitution item.2)) (foldGap substitution tail)

theorem render_foldGap (substitution : Letter → Word Nat) (segments : List Segment)
    (initial : Word Nat) :
    render substitution initial segments = gap initial (foldGap substitution segments) := by
  induction segments generalizing initial with
  | nil => rfl
  | cons item tail ih =>
      change render substitution (gap initial item.1 ++ substitution item.2) tail =
        gap initial (joinGap (pushGap item.1 (substitution item.2)) (foldGap substitution tail))
      rw [ih, gap_join, gap_push]

theorem cons_gap (substitution : Letter → Word Nat) (item : Segment) (tail : List Segment)
    (hGap kGap : Option (Word Nat)) :
    joinGap (joinGap hGap (foldGap substitution (item :: tail))) kGap =
      joinGap (pushGap (joinGap hGap item.1) (substitution item.2))
        (joinGap (foldGap substitution tail) kGap) := by
  simp only [foldGap, pushGap, join_assoc]

theorem middle_one (u v : Word Nat) (hGap kGap : Option (Word Nat)) (a : Letter) :
    Derives basis
      (anchor u v (joinGap (pushGap hGap (value u v a)) kGap))
      (anchor u v (joinGap (pushGap hGap u) kGap)) := by
  have alternatives : ∀ a : Letter, a = 0 ∨ a = 1 := by decide
  rcases alternatives a with rfl | rfl
  · exact Derives.refl _
  · have step := CrossFactor.f_middle u v hGap kGap
    simpa only [value, anchor, gap_join, gap_push] using step

/-- The third f-sweep, inside the C1 seed. The initial and final middle
contexts may be empty; all other explicit contexts retain their exact words. -/
theorem middle_sweep (u v : Word Nat) (hGap kGap : Option (Word Nat))
    (segments : List Segment) :
    Derives basis
      (anchor u v (joinGap (joinGap hGap (foldGap (value u v) segments)) kGap))
      (anchor u v (joinGap (joinGap hGap (foldGap (fun _ => u) segments)) kGap)) := by
  induction segments generalizing hGap with
  | nil => exact Derives.refl _
  | cons item tail ih =>
      have headStep := middle_one u v (joinGap hGap item.1)
        (joinGap (foldGap (value u v) tail) kGap) item.2
      have tailStep : Derives basis
          (anchor u v (joinGap (pushGap (joinGap hGap item.1) u)
            (joinGap (foldGap (value u v) tail) kGap)))
          (anchor u v (joinGap (pushGap (joinGap hGap item.1) u)
            (joinGap (foldGap (fun _ => u) tail) kGap))) := by
        have step := ih (pushGap (joinGap hGap item.1) u)
        simpa only [join_assoc] using step
      simpa only [cons_gap] using headStep.trans tailStep

theorem middle_bud_one (u v : Word Nat) (hGap kGap : Option (Word Nat)) :
    Derives basis
      (anchor u v (joinGap (pushGap hGap u) kGap))
      (anchor u v (joinGap (pushGap hGap (bud u v)) kGap)) := by
  have step := Derives.prepend (gap u hGap) (seed_left u v kGap)
  simpa only [anchor, bud, gap_join, gap_push, gap_append, Word.append_assoc] using step

/-- Propagation at every marked occurrence inside the anchor, using the
unchanged trailing seed. This does not erase or merge any external separator. -/
theorem middle_propagate (u v : Word Nat) (hGap kGap : Option (Word Nat))
    (segments : List Segment) :
    Derives basis
      (anchor u v (joinGap (joinGap hGap (foldGap (fun _ => u) segments)) kGap))
      (anchor u v (joinGap (joinGap hGap (foldGap (fun _ => bud u v) segments)) kGap)) := by
  induction segments generalizing hGap with
  | nil => exact Derives.refl _
  | cons item tail ih =>
      have headStep := middle_bud_one u v (joinGap hGap item.1)
        (joinGap (foldGap (fun _ => u) tail) kGap)
      have tailStep : Derives basis
          (anchor u v (joinGap (pushGap (joinGap hGap item.1) (bud u v))
            (joinGap (foldGap (fun _ => u) tail) kGap)))
          (anchor u v (joinGap (pushGap (joinGap hGap item.1) (bud u v))
            (joinGap (foldGap (fun _ => bud u v) tail) kGap))) := by
        have step := ih (pushGap (joinGap hGap item.1) (bud u v))
        simpa only [join_assoc] using step
      simpa only [cons_gap] using headStep.trans tailStep

/-- All three marked regions of a C1 word are handled in one unbounded
derivation. The vvu blocks are an intermediate form, not perfect squares. -/
theorem three_zone_marked_blocks (u v : Word Nat) (hGap kGap : Option (Word Nat))
    (before middle after : List Segment) :
    Derives basis
      (render (value u v)
        (renderLeft (value u v)
          (anchor u v (joinGap (joinGap hGap (foldGap (value u v) middle)) kGap)) before) after)
      (render (fun _ => bud u v)
        (renderLeft (fun _ => bud u v)
          (anchor u v (joinGap (joinGap hGap (foldGap (fun _ => bud u v) middle)) kGap)) before) after) := by
  have middleStep := (middle_sweep u v hGap kGap middle).trans
    (middle_propagate u v hGap kGap middle)
  have framedStep := render_congr (value u v) after
    (renderLeft_congr (value u v) before middleStep)
  exact framedStep.trans
    (c1_marked_blocks u v
      (joinGap (joinGap hGap (foldGap (fun _ => bud u v) middle)) kGap) before after)

end SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MiddleSweep

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MiddleSweep.join_assoc
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MiddleSweep.render_foldGap
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MiddleSweep.cons_gap
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MiddleSweep.middle_one
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MiddleSweep.middle_sweep
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MiddleSweep.middle_bud_one
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MiddleSweep.middle_propagate
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MiddleSweep.three_zone_marked_blocks
