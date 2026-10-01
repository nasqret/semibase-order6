import SemigroupBasis.CoRoots.Order6SporadicSection19PublishedSquareAlgebra

namespace SemigroupBasis.CoRoots.Order6SporadicSection19.Published.PerfectSweeps

open CrossFactor CrossSweep CrossLeftSweep AnchorPropagation MiddleSweep BinaryPowers SquareAlgebra

theorem right_perfect_one (u v : Word Nat) (hGap kGap : Option (Word Nat)) :
    Derives basis (gap (anchor u v hGap) kGap ++ u)
      (gap (anchor u v hGap) kGap ++ square u v) :=
  (AnchorPropagation.right_one u v hGap kGap).trans (right_bud_square u v hGap kGap)

theorem left_perfect_one (u v : Word Nat) (hGap kGap : Option (Word Nat)) :
    Derives basis (gap u kGap ++ anchor u v hGap)
      (gap (square u v) kGap ++ anchor u v hGap) := by
  have seed : Derives basis (gap u kGap ++ anchor u v hGap)
      (gap (bud u v) kGap ++ anchor u v hGap) := by
    have step := seed_left u v (some (gap (frontGap kGap u) hGap))
    rw [← stack_anchors u v kGap hGap] at step
    simpa only [bud, gap_append, Word.append_assoc] using step
  exact seed.trans (left_bud_square u v hGap kGap)

theorem right_perfect_sweep (u v : Word Nat) (hGap : Option (Word Nat))
    (segments : List Segment) (kGap : Option (Word Nat)) :
    Derives basis
      (render (fun _ => u) (gap (anchor u v hGap) kGap) segments)
      (render (fun _ => square u v) (gap (anchor u v hGap) kGap) segments) := by
  induction segments generalizing kGap with
  | nil => exact Derives.refl _
  | cons item tail ih =>
      let combined : Option (Word Nat) := joinGap kGap item.1
      have first : Derives basis
          (gap (gap (anchor u v hGap) kGap) item.1 ++ u)
          (gap (gap (anchor u v hGap) kGap) item.1 ++ square u v) := by
        have step := right_perfect_one u v hGap combined
        dsimp only [combined] at step
        rw [gap_join] at step
        exact step
      have headStep := render_congr (fun _ => u) tail first
      have tailStep := ih (pushGap combined (square u v))
      rw [gap_push] at tailStep
      dsimp only [combined] at tailStep
      rw [gap_join] at tailStep
      exact headStep.trans tailStep

theorem left_perfect_sweep (u v : Word Nat) (hGap : Option (Word Nat))
    (segments : List Segment) :
    Derives basis
      (renderLeft (fun _ => u) (anchor u v hGap) segments)
      (renderLeft (fun _ => square u v) (anchor u v hGap) segments) := by
  induction segments with
  | nil => exact Derives.refl _
  | cons item tail ih =>
      have first : Derives basis
          (gap u item.1 ++ renderLeft (fun _ => u) (anchor u v hGap) tail)
          (gap (square u v) item.1 ++ renderLeft (fun _ => u) (anchor u v hGap) tail) := by
        rw [left_render_uniform]
        exact left_perfect_one u v (leftGap u hGap tail) item.1
      have tailStep : Derives basis
          (gap (square u v) item.1 ++ renderLeft (fun _ => u) (anchor u v hGap) tail)
          (gap (square u v) item.1 ++ renderLeft (fun _ => square u v) (anchor u v hGap) tail) :=
        Derives.prepend (gap (square u v) item.1) ih
      exact first.trans tailStep

theorem two_sided_perfect_sweep (u v : Word Nat) (hGap : Option (Word Nat))
    (before after : List Segment) :
    Derives basis
      (render (fun _ => u) (renderLeft (fun _ => u) (anchor u v hGap) before) after)
      (render (fun _ => square u v)
        (renderLeft (fun _ => square u v) (anchor u v hGap) before) after) := by
  have rightStep : Derives basis
      (render (fun _ => u) (renderLeft (fun _ => u) (anchor u v hGap) before) after)
      (render (fun _ => square u v) (renderLeft (fun _ => u) (anchor u v hGap) before) after) := by
    rw [left_render_uniform]
    exact right_perfect_sweep u v (leftGap u hGap before) after none
  have leftStep := render_congr (fun _ => square u v) after
    (left_perfect_sweep u v hGap before)
  exact rightStep.trans leftStep

theorem middle_perfect_sweep (u v : Word Nat) (hGap kGap : Option (Word Nat))
    (segments : List Segment) :
    Derives basis
      (anchor u v (joinGap (joinGap hGap (foldGap (fun _ => u) segments)) kGap))
      (anchor u v (joinGap (joinGap hGap (foldGap (fun _ => square u v) segments)) kGap)) := by
  induction segments generalizing hGap with
  | nil => exact Derives.refl _
  | cons item tail ih =>
      have headStep := middle_square_one u v (joinGap hGap item.1)
        (joinGap (foldGap (fun _ => u) tail) kGap)
      have tailStep : Derives basis
          (anchor u v (joinGap (pushGap (joinGap hGap item.1) (square u v))
            (joinGap (foldGap (fun _ => u) tail) kGap)))
          (anchor u v (joinGap (pushGap (joinGap hGap item.1) (square u v))
            (joinGap (foldGap (fun _ => square u v) tail) kGap))) := by
        have step := ih (pushGap (joinGap hGap item.1) (square u v))
        simpa only [join_assoc] using step
      simpa only [cons_gap] using headStep.trans tailStep

/-- All marked occurrences in all three regions, and both ends of the
distinguished anchor, become binary squares. Separators are unchanged.
Maximal-factor coverage of an arbitrary word remains a separate obligation. -/
theorem three_zone_square_blocks (u v : Word Nat) (hGap kGap : Option (Word Nat))
    (before middle after : List Segment) :
    Derives basis
      (render (value u v)
        (renderLeft (value u v)
          (anchor u v (joinGap (joinGap hGap (foldGap (value u v) middle)) kGap)) before) after)
      (render (fun _ => square u v)
        (renderLeft (fun _ => square u v)
          (gap (square u v)
            (joinGap (joinGap hGap (foldGap (fun _ => square u v) middle)) kGap) ++
              square u v) before) after) := by
  let middleGap := joinGap (joinGap hGap (foldGap (fun _ => square u v) middle)) kGap
  have inside := (middle_sweep u v hGap kGap middle).trans
    (middle_perfect_sweep u v hGap kGap middle)
  have begin := render_congr (value u v) after
    (renderLeft_congr (value u v) before inside)
  have outside := (two_sided_sweep u v middleGap before after).trans
    (two_sided_perfect_sweep u v middleGap before after)
  have finish := render_congr (fun _ => square u v) after
    (renderLeft_congr (fun _ => square u v) before (anchor_perfect u v middleGap))
  exact begin.trans (outside.trans finish)

theorem three_zone_square_blocks_context (u v : Word Nat)
    (hGap kGap leftContext rightContext : Option (Word Nat))
    (before middle after : List Segment) :
    Derives basis
      (Context.frame leftContext rightContext
        (render (value u v)
          (renderLeft (value u v)
            (anchor u v (joinGap (joinGap hGap (foldGap (value u v) middle)) kGap)) before) after))
      (Context.frame leftContext rightContext
        (render (fun _ => square u v)
          (renderLeft (fun _ => square u v)
            (gap (square u v)
              (joinGap (joinGap hGap (foldGap (fun _ => square u v) middle)) kGap) ++
                square u v) before) after)) :=
  Context.frame_derives (three_zone_square_blocks u v hGap kGap before middle after)
    leftContext rightContext

def crossingMiddle (kGap : Option (Word Nat)) : List Segment := [(none, 0), (kGap, 0)]

theorem crossing_middle (u v : Word Nat) (hGap kGap tGap : Option (Word Nat)) :
    crossingGap u hGap kGap tGap =
      joinGap (joinGap hGap (foldGap (value u v) (crossingMiddle kGap))) tGap := by
  have value_zero : value u v (0 : Letter) = u := rfl
  cases hGap <;> cases kGap <;> cases tGap <;>
    simp only [crossingGap, crossingMiddle, foldGap, pushGap, joinGap, value_zero, Word.append_assoc]

/-- C2's four distinguished occurrences become four square blocks. The
three original C2 gaps, and every exterior separator, retain their words. -/
theorem c2_square_blocks (u v : Word Nat) (hGap kGap tGap : Option (Word Nat))
    (before after : List Segment) :
    Derives basis
      (render (value u v)
        (renderLeft (value u v) (crossing u v hGap kGap tGap) before) after)
      (render (fun _ => square u v)
        (renderLeft (fun _ => square u v)
          (gap (square u v)
            (joinGap (joinGap hGap (foldGap (fun _ => square u v) (crossingMiddle kGap))) tGap) ++
              square u v) before) after) := by
  have seed := render_congr (value u v) after
    (renderLeft_congr (value u v) before (crossing_seed u v hGap kGap tGap))
  have finish := three_zone_square_blocks u v hGap tGap before (crossingMiddle kGap) after
  rw [← crossing_middle u v hGap kGap tGap] at finish
  exact seed.trans finish

end SemigroupBasis.CoRoots.Order6SporadicSection19.Published.PerfectSweeps

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.PerfectSweeps.right_perfect_one
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.PerfectSweeps.left_perfect_one
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.PerfectSweeps.right_perfect_sweep
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.PerfectSweeps.left_perfect_sweep
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.PerfectSweeps.two_sided_perfect_sweep
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.PerfectSweeps.middle_perfect_sweep
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.PerfectSweeps.three_zone_square_blocks
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.PerfectSweeps.three_zone_square_blocks_context
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.PerfectSweeps.crossing_middle
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.PerfectSweeps.c2_square_blocks
