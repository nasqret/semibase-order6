import SemigroupBasis.CoRoots.Order6SporadicSection19PublishedCrossFactor

namespace SemigroupBasis.CoRoots.Order6SporadicSection19.Published.Context

def frame (left right : Option (Word Nat)) (word : Word Nat) : Word Nat :=
  match left, right with
  | none, none => word
  | some before, none => before ++ word
  | none, some after => word ++ after
  | some before, some after => (before ++ word) ++ after

theorem frame_derives {left right : Word Nat} (h : Derives basis left right)
    (before after : Option (Word Nat)) :
    Derives basis (frame before after left) (frame before after right) := by
  cases before with
  | none =>
      cases after with
      | none => exact h
      | some suffix => exact Derives.appendRight h suffix
  | some leftWord =>
      cases after with
      | none => exact Derives.prepend leftWord h
      | some suffix => exact Derives.appendRight (Derives.prepend leftWord h) suffix

end SemigroupBasis.CoRoots.Order6SporadicSection19.Published.Context

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.Context.frame_derives

namespace SemigroupBasis.CoRoots.Order6SporadicSection19.Published.CrossSweep

open CrossFactor

abbrev Letter := Fin 2
abbrev Segment := Option (Word Nat) × Letter

def value (u v : Word Nat) (a : Letter) : Word Nat :=
  if a.val = 0 then u else v

/-- The seed in the C1 case; all gaps may contain arbitrary other letters. -/
def anchor (u v : Word Nat) (hGap : Option (Word Nat)) : Word Nat :=
  ((gap u hGap ++ v) ++ v) ++ u

def joinGap : Option (Word Nat) → Option (Word Nat) → Option (Word Nat)
  | none, right => right
  | some left, none => some left
  | some left, some right => some (left ++ right)

def pushGap (before : Option (Word Nat)) (w : Word Nat) : Option (Word Nat) :=
  joinGap before (some w)

theorem gap_join (w : Word Nat) (left right : Option (Word Nat)) :
    gap w (joinGap left right) = gap (gap w left) right := by
  cases left with
  | none => rfl
  | some a =>
      cases right with
      | none => rfl
      | some b => exact (Word.append_assoc w a b).symm

theorem gap_push (w next : Word Nat) (before : Option (Word Nat)) :
    gap w (pushGap before next) = gap w before ++ next := by
  exact gap_join w before (some next)

theorem gap_derives {u v : Word Nat} (h : Derives basis u v)
    (middle : Option (Word Nat)) :
    Derives basis (gap u middle) (gap v middle) := by
  cases middle with
  | none => exact h
  | some w => exact Derives.appendRight h w

/-- Explicit separators are retained, including their order and entire words. -/
def render (substitution : Letter → Word Nat) (initial : Word Nat)
    (segments : List Segment) : Word Nat :=
  segments.foldl (fun acc item => gap acc item.1 ++ substitution item.2) initial

theorem render_congr (substitution : Letter → Word Nat) (segments : List Segment)
    {left right : Word Nat} (h : Derives basis left right) :
    Derives basis (render substitution left segments)
      (render substitution right segments) := by
  induction segments generalizing left right with
  | nil => exact h
  | cons item tail ih =>
      have first : Derives basis
          (gap left item.1 ++ substitution item.2)
          (gap right item.1 ++ substitution item.2) :=
        Derives.appendRight (gap_derives h item.1) (substitution item.2)
      exact ih first

theorem right_one (u v : Word Nat) (hGap kGap : Option (Word Nat))
    (a : Letter) :
    Derives basis (gap (anchor u v hGap) kGap ++ value u v a)
      (gap (anchor u v hGap) kGap ++ u) := by
  have alternatives : ∀ a : Letter, a = 0 ∨ a = 1 := by decide
  rcases alternatives a with rfl | rfl
  · exact Derives.refl _
  · exact CrossFactor.f_right u v hGap kGap

/-- Unbounded right-hand C1 sweep across any number of arbitrary separators.
Every selected binary occurrence is changed to u; no separator is erased.
This is the right-of-seed part of Lemma 19.2, not full perfectification. -/
theorem right_sweep (u v : Word Nat) (hGap : Option (Word Nat))
    (segments : List Segment) (kGap : Option (Word Nat)) :
    Derives basis
      (render (value u v) (gap (anchor u v hGap) kGap) segments)
      (render (fun _ => u) (gap (anchor u v hGap) kGap) segments) := by
  induction segments generalizing kGap with
  | nil => exact Derives.refl _
  | cons item tail ih =>
      let combined : Option (Word Nat) := joinGap kGap item.1
      have first : Derives basis
          (gap (gap (anchor u v hGap) kGap) item.1 ++ value u v item.2)
          (gap (gap (anchor u v hGap) kGap) item.1 ++ u) := by
        have step := right_one u v hGap combined item.2
        dsimp only [combined] at step
        rw [gap_join] at step
        exact step
      have prefixStep := render_congr (value u v) tail first
      have tailStep := ih (pushGap combined u)
      rw [gap_push] at tailStep
      dsimp only [combined] at tailStep
      rw [gap_join] at tailStep
      exact prefixStep.trans tailStep

theorem right_sweep_context (u v : Word Nat) (hGap kGap : Option (Word Nat))
    (segments : List Segment) (leftContext rightContext : Option (Word Nat)) :
    Derives basis
      (Context.frame leftContext rightContext
        (render (value u v) (gap (anchor u v hGap) kGap) segments))
      (Context.frame leftContext rightContext
        (render (fun _ => u) (gap (anchor u v hGap) kGap) segments)) :=
  Context.frame_derives (right_sweep u v hGap segments kGap)
    leftContext rightContext

end SemigroupBasis.CoRoots.Order6SporadicSection19.Published.CrossSweep

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.CrossSweep.gap_join
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.CrossSweep.gap_push
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.CrossSweep.gap_derives
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.CrossSweep.render_congr
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.CrossSweep.right_one
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.CrossSweep.right_sweep
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.CrossSweep.right_sweep_context

namespace SemigroupBasis.CoRoots.Order6SporadicSection19.Published.CrossLeftSweep

open CrossFactor CrossSweep

theorem gap_append (u v : Word Nat) (middle : Option (Word Nat)) :
    gap (u ++ v) middle = u ++ gap v middle := by
  cases middle with
  | none => rfl
  | some w => exact Word.append_assoc u v w

def frontGap : Option (Word Nat) → Word Nat → Word Nat
  | none, w => w
  | some middle, w => middle ++ w

def renderLeft (substitution : Letter → Word Nat) (finalWord : Word Nat) :
    List Segment → Word Nat
  | [] => finalWord
  | item :: tail => gap (substitution item.2) item.1 ++
      renderLeft substitution finalWord tail

def leftGap (u : Word Nat) (hGap : Option (Word Nat)) :
    List Segment → Option (Word Nat)
  | [] => hGap
  | item :: tail => some (gap (frontGap item.1 u) (leftGap u hGap tail))

theorem stack_anchors (u v : Word Nat) (gGap hGap : Option (Word Nat)) :
    gap u gGap ++ anchor u v hGap =
      anchor u v (some (gap (frontGap gGap u) hGap)) := by
  cases gGap <;> cases hGap <;>
    simp only [frontGap, gap, anchor, Word.append_assoc]

theorem left_render_uniform (u v : Word Nat) (hGap : Option (Word Nat))
    (segments : List Segment) :
    renderLeft (fun _ => u) (anchor u v hGap) segments =
      anchor u v (leftGap u hGap segments) := by
  induction segments with
  | nil => rfl
  | cons item tail ih =>
      change gap u item.1 ++ renderLeft (fun _ => u) (anchor u v hGap) tail =
        anchor u v (some (gap (frontGap item.1 u) (leftGap u hGap tail)))
      rw [ih]
      exact stack_anchors u v item.1 (leftGap u hGap tail)

theorem left_one (u v : Word Nat) (hGap gGap : Option (Word Nat)) (a : Letter) :
    Derives basis
      (gap (value u v a) gGap ++ anchor u v hGap)
      (gap u gGap ++ anchor u v hGap) := by
  have alternatives : ∀ a : Letter, a = 0 ∨ a = 1 := by decide
  rcases alternatives a with rfl | rfl
  · exact Derives.refl _
  · change Derives basis (gap v gGap ++ anchor u v hGap)
      (gap u gGap ++ anchor u v hGap)
    have step := CrossFactor.f_left u v gGap hGap
    simpa only [anchor, gap_append, Word.append_assoc] using step

/-- Arbitrarily many selected occurrences before the C1 seed, with every
intervening word preserved verbatim and in place. -/
theorem left_sweep (u v : Word Nat) (hGap : Option (Word Nat))
    (segments : List Segment) :
    Derives basis
      (renderLeft (value u v) (anchor u v hGap) segments)
      (renderLeft (fun _ => u) (anchor u v hGap) segments) := by
  induction segments with
  | nil => exact Derives.refl _
  | cons item tail ih =>
      have first : Derives basis
          (gap (value u v item.2) item.1 ++ renderLeft (value u v) (anchor u v hGap) tail)
          (gap (value u v item.2) item.1 ++ renderLeft (fun _ => u) (anchor u v hGap) tail) :=
        Derives.prepend (gap (value u v item.2) item.1) ih
      have last : Derives basis
          (gap (value u v item.2) item.1 ++
            renderLeft (fun _ => u) (anchor u v hGap) tail)
          (gap u item.1 ++ renderLeft (fun _ => u) (anchor u v hGap) tail) := by
        rw [left_render_uniform]
        exact left_one u v (leftGap u hGap tail) item.1 item.2
      exact first.trans last

theorem left_sweep_context (u v : Word Nat) (hGap : Option (Word Nat))
    (segments : List Segment) (leftContext rightContext : Option (Word Nat)) :
    Derives basis
      (Context.frame leftContext rightContext
        (renderLeft (value u v) (anchor u v hGap) segments))
      (Context.frame leftContext rightContext
        (renderLeft (fun _ => u) (anchor u v hGap) segments)) :=
  Context.frame_derives (left_sweep u v hGap segments) leftContext rightContext

end SemigroupBasis.CoRoots.Order6SporadicSection19.Published.CrossLeftSweep

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.CrossLeftSweep.gap_append
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.CrossLeftSweep.stack_anchors
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.CrossLeftSweep.left_render_uniform
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.CrossLeftSweep.left_one
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.CrossLeftSweep.left_sweep
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.CrossLeftSweep.left_sweep_context

namespace SemigroupBasis.CoRoots.Order6SporadicSection19.Published.CrossLeftSweep

open CrossFactor CrossSweep

/-- Both sides of a C1 seed, at arbitrary lengths and with every explicit
separator preserved. This is a rewriting lemma, not a completeness theorem. -/
theorem two_sided_sweep (u v : Word Nat) (hGap : Option (Word Nat))
    (before after : List Segment) :
    Derives basis
      (render (value u v) (renderLeft (value u v) (anchor u v hGap) before) after)
      (render (fun _ => u) (renderLeft (fun _ => u) (anchor u v hGap) before) after) := by
  have leftStep : Derives basis
      (render (value u v) (renderLeft (value u v) (anchor u v hGap) before) after)
      (render (value u v) (renderLeft (fun _ => u) (anchor u v hGap) before) after) :=
    render_congr (value u v) after (left_sweep u v hGap before)
  have rightStep : Derives basis
      (render (value u v) (renderLeft (fun _ => u) (anchor u v hGap) before) after)
      (render (fun _ => u) (renderLeft (fun _ => u) (anchor u v hGap) before) after) := by
    rw [left_render_uniform]
    exact right_sweep u v (leftGap u hGap before) after none
  exact leftStep.trans rightStep

theorem two_sided_sweep_context (u v : Word Nat) (hGap : Option (Word Nat))
    (before after : List Segment) (leftContext rightContext : Option (Word Nat)) :
    Derives basis
      (Context.frame leftContext rightContext
        (render (value u v) (renderLeft (value u v) (anchor u v hGap) before) after))
      (Context.frame leftContext rightContext
        (render (fun _ => u) (renderLeft (fun _ => u) (anchor u v hGap) before) after)) :=
  Context.frame_derives (two_sided_sweep u v hGap before after) leftContext rightContext

end SemigroupBasis.CoRoots.Order6SporadicSection19.Published.CrossLeftSweep

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.CrossLeftSweep.two_sided_sweep
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.CrossLeftSweep.two_sided_sweep_context
