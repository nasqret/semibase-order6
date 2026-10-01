import SemigroupBasis.CoRoots.Order6SporadicSection19PublishedSweeps

namespace SemigroupBasis.CoRoots.Order6SporadicSection19.Published.AnchorPropagation

open CrossFactor CrossSweep CrossLeftSweep

/-- The nonempty block inserted by the two propagation identities. -/
def bud (u v : Word Nat) : Word Nat := (v ++ v) ++ u

theorem seed_left (u v : Word Nat) (hGap : Option (Word Nat)) :
    Derives basis (anchor u v hGap) ((v ++ v) ++ anchor u v hGap) := by
  have step := CrossFactor.d_left u v hGap
  cases hGap <;>
    simpa only [anchor, gap, Word.append_assoc] using step

theorem right_one (u v : Word Nat) (hGap kGap : Option (Word Nat)) :
    Derives basis (gap (anchor u v hGap) kGap ++ u)
      (gap (anchor u v hGap) kGap ++ bud u v) := by
  have step := CrossFactor.d_right u v hGap kGap
  simpa only [anchor, bud, Word.append_assoc] using step

/-- Propagate the binary seed to arbitrarily many marked occurrences on its
right. All explicit intervening words are retained. -/
theorem right_propagate (u v : Word Nat) (hGap : Option (Word Nat))
    (segments : List Segment) (kGap : Option (Word Nat)) :
    Derives basis
      (render (fun _ => u) (gap (anchor u v hGap) kGap) segments)
      (render (fun _ => bud u v) (gap (anchor u v hGap) kGap) segments) := by
  induction segments generalizing kGap with
  | nil => exact Derives.refl _
  | cons item tail ih =>
      let combined : Option (Word Nat) := joinGap kGap item.1
      have first : Derives basis
          (gap (gap (anchor u v hGap) kGap) item.1 ++ u)
          (gap (gap (anchor u v hGap) kGap) item.1 ++ bud u v) := by
        have step := right_one u v hGap combined
        dsimp only [combined] at step
        rw [gap_join] at step
        exact step
      have headStep := render_congr (fun _ => u) tail first
      have tailStep := ih (pushGap combined (bud u v))
      rw [gap_push] at tailStep
      dsimp only [combined] at tailStep
      rw [gap_join] at tailStep
      exact headStep.trans tailStep

/-- The left propagation is performed before rewriting the tail, so the
original uniform anchor remains available at each representation boundary. -/
theorem left_propagate (u v : Word Nat) (hGap : Option (Word Nat))
    (segments : List Segment) :
    Derives basis
      (renderLeft (fun _ => u) (anchor u v hGap) segments)
      (renderLeft (fun _ => bud u v) (anchor u v hGap) segments) := by
  induction segments with
  | nil => exact Derives.refl _
  | cons item tail ih =>
      have first : Derives basis
          (gap u item.1 ++ renderLeft (fun _ => u) (anchor u v hGap) tail)
          (gap (bud u v) item.1 ++ renderLeft (fun _ => u) (anchor u v hGap) tail) := by
        rw [left_render_uniform]
        have step := seed_left u v
          (some (gap (frontGap item.1 u) (leftGap u hGap tail)))
        rw [← stack_anchors u v item.1 (leftGap u hGap tail)] at step
        simpa only [bud, gap_append, Word.append_assoc] using step
      have tailStep : Derives basis
          (gap (bud u v) item.1 ++ renderLeft (fun _ => u) (anchor u v hGap) tail)
          (gap (bud u v) item.1 ++ renderLeft (fun _ => bud u v) (anchor u v hGap) tail) :=
        Derives.prepend (gap (bud u v) item.1) ih
      exact first.trans tailStep

theorem two_sided_propagate (u v : Word Nat) (hGap : Option (Word Nat))
    (before after : List Segment) :
    Derives basis
      (render (fun _ => u) (renderLeft (fun _ => u) (anchor u v hGap) before) after)
      (render (fun _ => bud u v)
        (renderLeft (fun _ => bud u v) (anchor u v hGap) before) after) := by
  have rightStep : Derives basis
      (render (fun _ => u) (renderLeft (fun _ => u) (anchor u v hGap) before) after)
      (render (fun _ => bud u v) (renderLeft (fun _ => u) (anchor u v hGap) before) after) := by
    rw [left_render_uniform]
    exact right_propagate u v (leftGap u hGap before) after none
  have leftStep := render_congr (fun _ => bud u v) after
    (left_propagate u v hGap before)
  exact rightStep.trans leftStep

/-- The f-sweeps followed by the d-propagation, without any length bound.
The result has marked vvu blocks; it is not yet a perfect-square normal form. -/
theorem c1_marked_blocks (u v : Word Nat) (hGap : Option (Word Nat))
    (before after : List Segment) :
    Derives basis
      (render (value u v) (renderLeft (value u v) (anchor u v hGap) before) after)
      (render (fun _ => bud u v)
        (renderLeft (fun _ => bud u v) (anchor u v hGap) before) after) :=
  (two_sided_sweep u v hGap before after).trans
    (two_sided_propagate u v hGap before after)

theorem renderLeft_congr (substitution : Letter → Word Nat) (segments : List Segment)
    {left right : Word Nat} (h : Derives basis left right) :
    Derives basis (renderLeft substitution left segments)
      (renderLeft substitution right segments) := by
  induction segments with
  | nil => exact h
  | cons item tail ih =>
      exact Derives.prepend (gap (substitution item.2) item.1) ih

def crossing (u v : Word Nat) (hGap kGap tGap : Option (Word Nat)) : Word Nat :=
  gap (gap (gap u hGap ++ v) kGap ++ u) tGap ++ v

def crossingGap (u : Word Nat) (hGap kGap tGap : Option (Word Nat)) : Option (Word Nat) :=
  joinGap (pushGap (joinGap (pushGap hGap u) kGap) u) tGap

/-- All eight empty/nonempty context combinations of C2 lead to a C1 seed.
This includes the long expansions omitted by the bounded screen. -/
theorem crossing_seed (u v : Word Nat) (hGap kGap tGap : Option (Word Nat)) :
    Derives basis (crossing u v hGap kGap tGap)
      (anchor u v (crossingGap u hGap kGap tGap)) := by
  have step := CrossFactor.c u v hGap kGap tGap
  simpa only [crossing, crossingGap, anchor, gap_join, gap_push] using step

theorem c2_marked_blocks (u v : Word Nat) (hGap kGap tGap : Option (Word Nat))
    (before after : List Segment) :
    Derives basis
      (render (value u v)
        (renderLeft (value u v) (crossing u v hGap kGap tGap) before) after)
      (render (fun _ => bud u v)
        (renderLeft (fun _ => bud u v)
          (anchor u v (crossingGap u hGap kGap tGap)) before) after) := by
  have seedStep := render_congr (value u v) after
    (renderLeft_congr (value u v) before (crossing_seed u v hGap kGap tGap))
  exact seedStep.trans (c1_marked_blocks u v (crossingGap u hGap kGap tGap) before after)

theorem c1_marked_blocks_context (u v : Word Nat) (hGap : Option (Word Nat))
    (before after : List Segment) (leftContext rightContext : Option (Word Nat)) :
    Derives basis
      (Context.frame leftContext rightContext
        (render (value u v) (renderLeft (value u v) (anchor u v hGap) before) after))
      (Context.frame leftContext rightContext
        (render (fun _ => bud u v)
          (renderLeft (fun _ => bud u v) (anchor u v hGap) before) after)) :=
  Context.frame_derives (c1_marked_blocks u v hGap before after) leftContext rightContext

end SemigroupBasis.CoRoots.Order6SporadicSection19.Published.AnchorPropagation

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.AnchorPropagation.seed_left
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.AnchorPropagation.right_one
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.AnchorPropagation.right_propagate
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.AnchorPropagation.left_propagate
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.AnchorPropagation.two_sided_propagate
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.AnchorPropagation.c1_marked_blocks
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.AnchorPropagation.renderLeft_congr
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.AnchorPropagation.crossing_seed
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.AnchorPropagation.c2_marked_blocks
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.AnchorPropagation.c1_marked_blocks_context
