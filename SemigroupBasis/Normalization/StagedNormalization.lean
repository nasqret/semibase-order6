/-
  Staged normalization — one theorem for every "canonical form" completeness kernel.

  Motivation (empirical).  A census of the 990 hand-authored `SemigroupBasis/CoRoots`
  modules (303,248 lines) shows that the bespoke inner kernels, which is where all the
  authoring cost sits, are built from a tiny shared vocabulary: declaration names contain
  Canonical/Normal 826x, Signature 458x, Marker 361x, Block 349x, Swap 326x, Gap 288x,
  Support 259x, Contraction 135x, Cut 122x.  Every hard case re-derives the same argument
  locally:

      "push the word through a chain of derivable rewriting stages until it reaches a
       normal form, then observe that the case invariant forces the two normal forms
       to coincide."

  This module states and proves that argument ONCE, abstractly enough that a case
  supplies only (a) the per-stage soundness proofs and (b) the fact that its invariant
  determines the normal form.  Nothing else.

  It is deliberately independent of `Word`, of `Derives`, and of any particular case:
  the derivability notion is an arbitrary equivalence-shaped relation, so case-local
  notions (`HullListDerives`, per-basis restricted derivability, block-level relations)
  are instances on equal footing with `Derives basis`.

  Mathlib-free.  Lean 4.28.0.
-/

import SemigroupBasis.Equational

namespace SemigroupBasis
namespace Normalization

universe u v w x

/-! ## The abstract derivability system -/

/-- A derivability relation, packaged with the only three closure properties any
staged-normalization argument uses.  `Derives basis` is an instance (`derivesSystem`
below); so is every case-local derivability notion in `CoRoots`, e.g. `HullListDerives`. -/
structure System (β : Type v) where
  rel : β → β → Prop
  refl : ∀ x, rel x x
  symm : ∀ {x y}, rel x y → rel y x
  trans : ∀ {x y z}, rel x y → rel y z → rel x z

namespace System

variable {β : Type v} (D : System β)

/-- Definitional equality is derivability.  This is the step that converts the
"equal normal forms" computation into a derivation. -/
theorem rel_of_eq {x y : β} (h : x = y) : D.rel x y :=
  h ▸ D.refl x

end System

/-! ## Stages -/

/-- One normalization stage.

`ρ` is the *representation* the stage manipulates (a block list, a signature record,
a raw word) and `render : ρ → β` displays it in the derivability system.  Keeping `ρ`
separate from `β` is what lets a case do its combinatorics on a structured type while
the theorem still concludes something about rendered words.

`sound` is the entire per-stage obligation. -/
structure Stage {β : Type v} (D : System β) (ρ : Type w) (render : ρ → β) where
  run : ρ → ρ
  sound : ∀ x, D.rel (render x) (render (run x))

/-- Run a pipeline of stages, left to right. -/
def runStages {β : Type v} {D : System β} {ρ : Type w} {render : ρ → β} :
    List (Stage D ρ render) → ρ → ρ
  | [], x => x
  | s :: rest, x => runStages rest (s.run x)

@[simp] theorem runStages_nil {β : Type v} {D : System β} {ρ : Type w} {render : ρ → β}
    (x : ρ) : runStages (D := D) (render := render) [] x = x := rfl

@[simp] theorem runStages_cons {β : Type v} {D : System β} {ρ : Type w} {render : ρ → β}
    (s : Stage D ρ render) (rest : List (Stage D ρ render)) (x : ρ) :
    runStages (s :: rest) x = runStages rest (s.run x) := rfl

/-- A pipeline is sound: the input is derivable to its normal form.  This is the
single induction that every case currently re-does by hand. -/
theorem runStages_sound {β : Type v} {D : System β} {ρ : Type w} {render : ρ → β} :
    ∀ (stages : List (Stage D ρ render)) (x : ρ),
      D.rel (render x) (render (runStages stages x))
  | [], x => D.refl _
  | s :: rest, x => D.trans (s.sound x) (runStages_sound rest (s.run x))

/-! ## The staged-normalization theorem -/

/-- **Staged normalization.**

If a pipeline of derivable stages sends `x` and `y` to a common normal form whenever
the invariant `I` relates them, then `I` implies derivability.

Every "completeness kernel" in the campaign is an instance.  The case supplies:
  * `stages`  — the rewriting chain, each with its local soundness proof;
  * `hdet`    — a *pure, computational* statement with no derivability content.

The separation matters: `hdet` is combinatorics on lists that can be attacked by
`decide`, `simp`, or induction with no equational-logic reasoning in sight, and the
derivability content is confined to the per-stage `sound` fields. -/
theorem rel_of_invariant {β : Type v} {D : System β} {ρ : Type w} {render : ρ → β}
    (stages : List (Stage D ρ render)) {I : ρ → ρ → Prop}
    (hdet : ∀ {x y : ρ}, I x y → runStages stages x = runStages stages y)
    {x y : ρ} (h : I x y) : D.rel (render x) (render y) :=
  D.trans (runStages_sound stages x)
    (D.trans (D.rel_of_eq (congrArg render (hdet h)))
      (D.symm (runStages_sound stages y)))

/-- **Key form.**  The overwhelmingly common special case: the invariant is equality of
a computed key `key : ρ → κ`, and the normal form is a function `nf` of that key alone.

This is exactly the shape of the profile/signature kernels — "the capped count profile
determines the canonical block list", "the joint signature determines the canonical
word" — with `hnf` the one fact to prove and `hnf` again purely computational. -/
theorem rel_of_key {β : Type v} {D : System β} {ρ : Type w} {render : ρ → β}
    {κ : Type x} (stages : List (Stage D ρ render)) (key : ρ → κ) (nf : κ → ρ)
    (hnf : ∀ z, runStages stages z = nf (key z))
    {x y : ρ} (h : key x = key y) : D.rel (render x) (render y) :=
  rel_of_invariant stages (I := fun a b => key a = key b)
    (fun {a b} hab => by rw [hnf a, hnf b, hab]) h

/-- **Chain form.**  When a case has already been factored into named intermediate
forms — `render b → swept b → canonical b`, the current Hull 21.1 shape — it can be
assembled directly without building `Stage` records. -/
theorem rel_of_chain {β : Type v} (D : System β) {ρ : Type w} (render : ρ → β)
    (mid final : ρ → ρ)
    (h₁ : ∀ z, D.rel (render z) (render (mid z)))
    (h₂ : ∀ z, D.rel (render (mid z)) (render (final z)))
    {x y : ρ} (h : final x = final y) : D.rel (render x) (render y) :=
  D.trans (D.trans (h₁ x) (h₂ x))
    (D.trans (D.rel_of_eq (congrArg render h))
      (D.symm (D.trans (h₁ y) (h₂ y))))

/-! ## Instantiation at `Derives` -/

/-- `Derives basis` as a normalization system. -/
def derivesSystem {α : Type u} (basis : List (Identity α)) : System (Word α) where
  rel := Derives basis
  refl := Derives.refl
  symm := Derives.symm
  trans := Derives.trans

/-- The headline word-level corollary: an invariant that determines a normal form
is a completeness proof. -/
theorem derives_of_invariant {α : Type u} {basis : List (Identity α)} {ρ : Type w}
    {render : ρ → Word α} (stages : List (Stage (derivesSystem basis) ρ render))
    {I : ρ → ρ → Prop}
    (hdet : ∀ {x y : ρ}, I x y → runStages stages x = runStages stages y)
    {x y : ρ} (h : I x y) : Derives basis (render x) (render y) :=
  rel_of_invariant stages hdet h

/-- Same, with the key/normal-form packaging. -/
theorem derives_of_key {α : Type u} {basis : List (Identity α)} {ρ : Type w}
    {render : ρ → Word α} {κ : Type x}
    (stages : List (Stage (derivesSystem basis) ρ render)) (key : ρ → κ) (nf : κ → ρ)
    (hnf : ∀ z, runStages stages z = nf (key z))
    {x y : ρ} (h : key x = key y) : Derives basis (render x) (render y) :=
  rel_of_key stages key nf hnf h

/-! ## Context congruence

The other pattern the census surfaces (Swap 326x, Segment 99x): a stage acts on one
segment and leaves the surrounding context alone.  Stated once, so no case has to
re-assemble `prepend`/`appendRight`. -/

/-- Derivability inside a fixed two-sided context. -/
theorem Derives.inContext {α : Type u} {basis : List (Identity α)} (p q : Word α)
    {u v : Word α} (h : Derives basis u v) :
    Derives basis (p ++ (u ++ q)) (p ++ (v ++ q)) :=
  Derives.prepend p (Derives.appendRight h q)

/-- A stage that rewrites a segment in a fixed context is a stage on the whole word. -/
def Stage.ofSegment {α : Type u} {basis : List (Identity α)} {ρ : Type w}
    (split : ρ → Word α × Word α × Word α) (rebuild : ρ → ρ)
    (step : ∀ z, Derives basis (split z).2.1 ((split (rebuild z)).2.1))
    (hctx : ∀ z, (split (rebuild z)).1 = (split z).1 ∧
                 (split (rebuild z)).2.2 = (split z).2.2)
    (render : ρ → Word α)
    (hrender : ∀ z, render z = (split z).1 ++ ((split z).2.1 ++ (split z).2.2)) :
    Stage (derivesSystem basis) ρ render where
  run := rebuild
  sound := fun z => by
    have hc := hctx z
    rw [hrender z, hrender (rebuild z), hc.1, hc.2]
    exact Derives.inContext _ _ (step z)

end Normalization
end SemigroupBasis
