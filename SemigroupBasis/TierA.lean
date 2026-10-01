import SemigroupBasis.Fingerprint

/-!
# TIER A — the fingerprint → unbounded (Nat-variable) lift

`Fingerprint.lean` collapses a per-class completeness proof into a finite
certificate and yields `BasisFor G Σ` **at a fixed finite alphabet** `α = Fin n`
("Σ derives every `G`-valid identity in ≤ n variables").  Tier A upgrades this
to the honest **unbounded** statement `BasisFor G Σ` at `α = Nat` for the
*equivariant / letter-local* profile languages (codex's first-checker scope:
content, per-letter parities, first/last occurrence, ordered blocks,
occurrence caps, absorbing cutoffs).

Two generic ingredients, each fully proved here (`{propext, Quot.sound}` /
`Classical.choice`-free unless the caller's tables need it):

* **(A1) SEMANTIC COLLAPSE** (`satisfiedBy_iff_collapse`).  For a semigroup `G`
  on a carrier that is a retract of `Fin k` (any finite table: `S = Fin k`,
  `enc = dec = id`), an identity `u ≈ v` over `Nat` holds in `G` **iff every
  identification of its variables onto ≤ k letters holds** — because any
  valuation `Nat → S` takes ≤ k distinct values, hence factors through some
  `q : Nat → Fin k`.  This turns the intrinsically-infinite necessity
  hypothesis (`∀ val : Nat → S, …`) into a `Fin k`-collapse-checkable form.

* **(A2) EQUIVARIANT CERTIFICATE / RENAMING FUNCTORIALITY**
  (`Derives.rename`).  A derivation over alphabet `α` transports along **any**
  substitution `r : α → Word β` into a derivation over `β`, provided each
  `α`-basis law's `r`-instance is `β`-derivable.  This is the exact engine by
  which chains and separators established at the base arity `n0` are *renamed*
  to every arity `n` (higher-arity data are renamings of the `n0` data): it is
  naturality of `Derives` in the variable alphabet.  The same-alphabet case
  `α = β = Nat` is the equivariance step (relabel canonical letters to
  arbitrary ones); the cross-alphabet case `Fin n0 → Nat` is the lift proper.

Assembly (`basisForNat_of_equivariant`): an equivariant profile `φ : Word Nat →
P` with normal form `nf`, a renaming-uniform reach `∀ w, Σ ⊢ w ≈ nf (φ w)`
(built from the `n0` chains via `Derives.rename`), and A1-reduced necessity,
feed `Fingerprint.basisFor_of_profile` at `α = Nat` to yield the sealed
`BasisFor G Σ`.

## Honest scope boundary (see `TIER_A.md`)

Tier A **alone** seals the Nat endpoint exactly when the reach is
renaming-uniform, i.e. the profile is letter-local with a fixed finite width:
`content` / `first-letter` / `last-letter` / `per-letter parity` /
`occurrence-cap` / `absorbing-cutoff` languages.  For these the reach chains at
arity `n` really are renamings of the `n0` chains, so A2 lifts them and A1
discharges necessity.  Languages whose reach requires a genuine
**support-descent** — the 2-local parity/projection case (T5): deriving a
width-`m` word from its ≤ n0 collapses needs invariants that GROW with `m`, so
the reach chains are *not* renamings of a bounded set — still need a per-family
**Tier B** descent lemma (T5's Compression → gap-swap → Bridge → Descent is the
prototype).  The boundary is exactly: *is the reach renaming-uniform, or does it
need an m-indexed descent?*
-/

namespace SemigroupBasis
namespace TierA

open Fingerprint

/-! ## `Word.bind` infrastructure (naturality of substitution) -/

private theorem list_flatMap_flatMap {α β γ : Type _}
    (l : List α) (f : α → List β) (g : β → List γ) :
    (l.flatMap f).flatMap g = l.flatMap (fun x => (f x).flatMap g) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      simp only [List.flatMap_cons, List.flatMap_append, ih]

/-- Substitution distributes over word concatenation. -/
theorem bind_append {α β : Type _} (u v : Word α) (σ : α → Word β) :
    (u ++ v).bind σ = u.bind σ ++ v.bind σ := by
  apply Word.toList_injective
  rw [Word.toList_bind, Word.toList_append, Word.toList_append,
      Word.toList_bind, Word.toList_bind, List.flatMap_append]

/-- Substitution composes: `(w[σ])[τ] = w[x ↦ (σ x)[τ]]`. -/
theorem bind_bind {α β γ : Type _} (w : Word α) (σ : α → Word β) (τ : β → Word γ) :
    (w.bind σ).bind τ = w.bind (fun x => (σ x).bind τ) := by
  apply Word.toList_injective
  rw [Word.toList_bind, Word.toList_bind, list_flatMap_flatMap, Word.toList_bind]
  congr 1
  funext x
  rw [Word.toList_bind]

/-! ## (A2) Renaming functoriality — the equivariant-certificate engine -/

/-- **RENAME / functoriality of `Derives` in the variable alphabet.**  A
derivation over `basisα` transports, under an arbitrary letter-substitution
`r : α → Word β`, to a derivation over `basisβ`, provided every `α`-basis law's
`r`-instance is `β`-derivable.  Chains/separators at base arity `n0` are lifted
to any arity by choosing `r` a renaming; the same-alphabet instance
(`α = β`, `basisα = basisβ`) is the equivariance relabel. -/
theorem Derives.rename {α β : Type _}
    {basisα : List (Identity α)} {basisβ : List (Identity β)}
    (hbase : ∀ e ∈ basisα, ∀ r : α → Word β,
      Derives basisβ (e.lhs.bind r) (e.rhs.bind r))
    {u v : Word α} (h : Derives basisα u v) :
    ∀ r : α → Word β, Derives basisβ (u.bind r) (v.bind r) := by
  induction h with
  | fromBasis hmem => intro r; exact hbase _ hmem r
  | refl u => intro r; exact Derives.refl _
  | symm _ ih => intro r; exact Derives.symm (ih r)
  | trans _ _ ih₁ ih₂ => intro r; exact Derives.trans (ih₁ r) (ih₂ r)
  | prepend p _ ih =>
      intro r
      rw [bind_append, bind_append]
      exact Derives.prepend (p.bind r) (ih r)
  | appendRight _ q ih =>
      intro r
      rw [bind_append, bind_append]
      exact Derives.appendRight (ih r) (q.bind r)
  | subst _ σ ih =>
      intro r
      rw [bind_bind, bind_bind]
      exact ih (fun x => (σ x).bind r)

/-- Same-alphabet corollary: **equivariance**.  Any derivation relabels along a
substitution `r : Nat → Word Nat` against the same basis (each basis law is
`subst`-closed automatically).  This is the tool that turns one canonical reach
chain into the reach chain for arbitrary letters. -/
theorem Derives.relabel {α : Type _} {basis : List (Identity α)}
    {u v : Word α} (h : Derives basis u v) (r : α → Word α) :
    Derives basis (u.bind r) (v.bind r) :=
  Derives.rename
    (fun _e he r => Derives.subst (Derives.fromBasis he) r) h r

/-! ## (A1) Semantic collapse -/

/-- **SEMANTIC COLLAPSE.**  If the carrier `S` is a retract of `Fin k`
(`dec ∘ enc = id`; every finite table has `S = Fin k`, `enc = dec = id`), then
an identity `u ≈ v` over `Nat` is satisfied by `G` **iff** it is satisfied by
every identification of its variables onto ≤ k letters (`q : Nat → Fin k`,
evaluated by an arbitrary `dval : Fin k → S`).  Any valuation `Nat → S` takes
≤ k distinct values, so factors as `dec ∘ (enc ∘ val)`; the `Fin k`-quantified
right-hand side is what a finite certificate can check. -/
theorem satisfiedBy_iff_collapse {S : Type _} {G : Semigroup S} {k : Nat}
    (enc : S → Fin k) (dec : Fin k → S) (hdec : ∀ s, dec (enc s) = s)
    (u v : Word Nat) :
    (∀ val : Nat → S, G.eval val u = G.eval val v)
      ↔ (∀ (q : Nat → Fin k) (dval : Fin k → S),
          G.eval (fun x => dval (q x)) u = G.eval (fun x => dval (q x)) v) := by
  constructor
  · intro h q dval; exact h (fun x => dval (q x))
  · intro h val
    simpa only [hdec] using h (fun x => enc (val x)) dec

/-- Finite-table specialization of A1 (`S = Fin k`, `enc = dec = id`). -/
theorem satisfiedBy_iff_collapse_table (T : FiniteTable) (u v : Word Nat) :
    (∀ val : Nat → Fin T.order, T.semigroup.eval val u = T.semigroup.eval val v)
      ↔ (∀ (q : Nat → Fin T.order) (dval : Fin T.order → Fin T.order),
          T.semigroup.eval (fun x => dval (q x)) u
            = T.semigroup.eval (fun x => dval (q x)) v) :=
  satisfiedBy_iff_collapse id id (fun _ => rfl) u v

/-! ## Assembly: the Tier-A Nat endpoint -/

/-- **TIER-A LIFT.**  From an equivariant profile over `Nat` — a profile map
`φ`, a normal form `nf`, a renaming-uniform reach `hReach`, soundness `hM`, and
necessity phrased in A1's collapse form `hSep` — obtain the sealed
unbounded-variable basis theorem `BasisFor G basis` at `α = Nat`.

Every hypothesis is explicit:

* `hM` — `Models G basis` (soundness of the displayed basis; one finite sweep).
* `hReach` — `∀ w : Word Nat, Derives basis w (nf (φ w))`.  For letter-local
  languages this is the `n0` chains transported by `Derives.rename` / `.relabel`
  to every word (the equivariant reach).  **This is the load-bearing hypothesis
  a Tier-B family must instead supply by support-descent.**
* `hSep` — necessity, already reduced by A1: T-equality of `u,v` *in the
  `Fin k`-collapse form* forces equal normal forms.  A finite certificate's
  separating valuations discharge this (the collapse quantifier ranges over
  `Fin k`, not all of `S`, matching decidable separation data). -/
theorem basisForNat_of_equivariant {S : Type _} {G : Semigroup S}
    {basis : List (Identity Nat)} {P : Type _}
    (φ : Word Nat → P) (nf : P → Word Nat) {k : Nat}
    (enc : S → Fin k) (dec : Fin k → S) (hdec : ∀ s, dec (enc s) = s)
    (hM : Models G basis)
    (hReach : ∀ w : Word Nat, Derives basis w (nf (φ w)))
    (hSep : ∀ u v : Word Nat,
      (∀ (q : Nat → Fin k) (dval : Fin k → S),
        G.eval (fun x => dval (q x)) u = G.eval (fun x => dval (q x)) v)
      → nf (φ u) = nf (φ v)) :
    BasisFor G basis := by
  refine basisFor_of_profile φ nf hM hReach ?_
  intro u v valid
  exact hSep u v ((satisfiedBy_iff_collapse enc dec hdec u v).mp valid)

/-- Finite-table flavor of the lift (carrier `Fin T.order`). -/
theorem basisForNat_of_equivariant_table (T : FiniteTable)
    {basis : List (Identity Nat)} {P : Type _}
    (φ : Word Nat → P) (nf : P → Word Nat)
    (hM : Models T.semigroup basis)
    (hReach : ∀ w : Word Nat, Derives basis w (nf (φ w)))
    (hSep : ∀ u v : Word Nat,
      (∀ (q : Nat → Fin T.order) (dval : Fin T.order → Fin T.order),
        T.semigroup.eval (fun x => dval (q x)) u
          = T.semigroup.eval (fun x => dval (q x)) v)
      → nf (φ u) = nf (φ v)) :
    BasisFor T.semigroup basis :=
  basisForNat_of_equivariant φ nf id id (fun _ => rfl) hM hReach hSep

end TierA
end SemigroupBasis
