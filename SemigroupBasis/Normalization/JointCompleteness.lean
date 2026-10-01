import SemigroupBasis.Order6Subdirect.Common
import SemigroupBasis.Fingerprint
import SemigroupBasis.TierA
import SemigroupBasis.Normalization.StagedNormalization

/-!
# Generic joint completeness for factor-pair / hull obligations

Every `OBL-JOINT-*` node of the proof DAG and every
`Hull*.DerivationalObligation` has the same statement

```lean
∀ e : Identity Nat, e.SatisfiedBy G → e.SatisfiedBy H → Derives Σ e.lhs e.rhs
```

with `G`, `H` of order ≤ 5 carrying sealed bases and `Σ` the displayed system.
This module records the *generic* content of that statement:

1. `obligation_iff_prod_basisFor` — the obligation is **equivalent** to
   `BasisFor (G.prod H) Σ`: joint completeness is single-semigroup completeness
   for the hull, a finite semigroup of order `|G|·|H| ≤ 25`.  Nothing "joint"
   survives the reduction.
2. `obligation_of_normalizer` — the obligation follows from (and, with choice,
   is equivalent to) a **normalizer** `nf : Word Nat → Word Nat` with
   *determinacy* (`nf` is constant on the meet theory) and *reach*
   (`Σ ⊢ w ≈ nf w`).  This is `Fingerprint.basisFor_of_profile` specialised to
   the hull; the frame is lossless, so the per-pair residual is exactly one
   reach lemma.
3. `obligation_of_factorProfiles` — the production form.  Determinacy is
   **discharged generically** from the two factors' sealed profile
   presentations (`FactorProfile`), leaving `hReach` as the single per-pair
   Prop.  This is the shape codex's worked instances converge on by hand
   (`ParityPreparedScannerCanonicalization`, `JointSignatureCanonicalization`,
   `ProfileCountCanonicalization`).

What is **not** here: any route from a fixed-arity certificate to the `Nat`
conclusion.  `Fingerprint.Certificate.basisFor` proves `BasisFor G Σ` at
`α = Fin n` only; `FiniteAlphabetBridge.basisFor_of_finiteAlphabetFamily`
needs one such certificate per arity.  See `JOINT_COMPLETENESS_GENERIC.md`.
-/

namespace SemigroupBasis
namespace JointCompleteness

open Order6Subdirect

variable {A B : Type _} {G : Semigroup A} {H : Semigroup B}
variable {basis : List (Identity Nat)}

/-- The campaign's obligation shape, stated once. -/
def DerivationalObligation (G : Semigroup A) (H : Semigroup B)
    (basis : List (Identity Nat)) : Prop :=
  ∀ e : Identity Nat, e.SatisfiedBy G → e.SatisfiedBy H →
    Derives basis e.lhs e.rhs

/-- **Reduction to the hull.**  With soundness in both factors, the joint
obligation is *equivalent* to completeness of `basis` for the single finite
semigroup `G × H`.  (`←` is `Identity.satisfiedBy_prod`; `→` is the split
projections, i.e. the existing `prod_basisFor_of_obligation` argument.) -/
theorem obligation_iff_prod_basisFor (a : A) (b : B)
    (hM : Models (G.prod H) basis) :
    DerivationalObligation G H basis ↔ BasisFor (G.prod H) basis := by
  constructor
  · intro h
    refine ⟨hM, ?_⟩
    intro e valid
    exact h e ((prodFstSplit G H b).pushforwardIdentity e valid)
      ((prodSndSplit G H a).pushforwardIdentity e valid)
  · rintro ⟨_, hc⟩ e hG hH
    exact hc e (Identity.satisfiedBy_prod hG hH)

/-- **Normalizer form** (lossless).  A normal form that is constant on the meet
theory and reachable by `basis` discharges the obligation.  Conversely a
normalizer always exists when the obligation holds (choose a representative of
each `Derives`-class), so demanding a normalizer costs no generality. -/
theorem obligation_of_normalizer (nf : Word Nat → Word Nat)
    (hDet : ∀ u v : Word Nat,
      (∀ val : Nat → A, G.eval val u = G.eval val v) →
      (∀ val : Nat → B, H.eval val u = H.eval val v) → nf u = nf v)
    (hReach : ∀ w : Word Nat, Derives basis w (nf w)) :
    DerivationalObligation G H basis := by
  intro e hG hH
  have h : nf e.lhs = nf e.rhs := hDet e.lhs e.rhs hG hH
  exact Derives.trans (hReach e.lhs) (h ▸ Derives.symm (hReach e.rhs))

/-- A **profile presentation** of one factor: a profile map on `Nat`-words
together with the necessity half — semantically equal words have equal
profiles.  Every sealed order-≤5 factor whose completeness proof went through
`Fingerprint.basisFor_of_profile` / `TierA.basisForNat_of_equivariant` already
exports this datum; the canonical (always available) choice is
`φ w := fun val => G.eval val w`, for which `nec` is `funext`. -/
structure FactorProfile {A : Type u} (G : Semigroup A) (P : Type v) where
  φ : Word Nat → P
  nec : ∀ u v : Word Nat,
    (∀ val : Nat → A, G.eval val u = G.eval val v) → φ u = φ v

/-- The canonical term-function profile; `nec` is definitional. -/
def FactorProfile.canonical (G : Semigroup A) :
    FactorProfile G ((Nat → A) → A) where
  φ := fun w val => G.eval val w
  nec := fun _ _ h => funext h

/-- **PRODUCTION FORM — joint completeness from the two sealed factor profiles
plus one reach lemma.**  Determinacy is generic: the joint profile is the pair
of factor profiles, so an identity of the meet theory has equal joint profile
by the factors' own necessity halves.  The *only* per-pair hypothesis is
`hReach`. -/
theorem obligation_of_factorProfiles {PG PH : Type _}
    (pG : FactorProfile G PG) (pH : FactorProfile H PH)
    (render : PG × PH → Word Nat)
    (hReach : ∀ w : Word Nat, Derives basis w (render (pG.φ w, pH.φ w))) :
    DerivationalObligation G H basis :=
  obligation_of_normalizer (fun w => render (pG.φ w, pH.φ w))
    (fun u v hG hH => by
      dsimp only
      rw [pG.nec u v hG, pH.nec u v hH])
    hReach

/-- Staged normalization supplies the one reach lemma required by the two
factor profiles. -/
theorem obligation_of_stages {PG PH : Type _}
    (pG : FactorProfile G PG) (pH : FactorProfile H PH)
    (stages : List (Normalization.Stage
        (Normalization.derivesSystem basis) (Word Nat) id))
    (render : PG × PH → Word Nat)
    (hnf : ∀ w, Normalization.runStages stages w = render (pG.φ w, pH.φ w)) :
    DerivationalObligation G H basis :=
  obligation_of_factorProfiles pG pH render
    (fun w => (hnf w) ▸ Normalization.runStages_sound stages w)

/-- Hull consumption: the obligation upgrades the displayed system to a basis
of the product hull, which is what every `Hull*.prod_basisFor_of_obligation`
and every `T-SUBDIRECT` wrapper consumes. -/
theorem prod_basisFor_of_factorProfiles {PG PH : Type _} (a : A) (b : B)
    (hM : Models (G.prod H) basis)
    (pG : FactorProfile G PG) (pH : FactorProfile H PH)
    (render : PG × PH → Word Nat)
    (hReach : ∀ w : Word Nat, Derives basis w (render (pG.φ w, pH.φ w))) :
    BasisFor (G.prod H) basis :=
  (obligation_iff_prod_basisFor a b hM).mp
    (obligation_of_factorProfiles pG pH render hReach)

/-! ## The 1-local (letter-local) profile family

For 91 of the 116 distinct order-≤5 factors occurring in the 248 pair
obligations, the factor's identity theory is *determined by 1-local data*:

  `ι w = (ford w, lord w, cappedCounts t p w)`

(first-occurrence order, last-occurrence order, per-letter occurrence counts
reduced by the factor's index/period).  For such factors the profile above may
be taken letter-local, and `TierA.Derives.rename` transports base-arity reach
chains to every arity, so `hReach` is a *per-family* lemma rather than a
per-pair one.  The classification is a proof, not a sample: `ι` commutes with
letter identification (ford/lord of a collapse are induced; capped counts is
the canonical monoid hom `ℕ → ℕ/(t = t+p)`, so counts add), hence by
`TierA.satisfiedBy_iff_collapse` the condition need only be checked at width
`≤ |S|`. -/

/-- Capped-count reduction: the canonical hom `ℕ → ℕ/(t = t+p)`. -/
def capped (t p n : Nat) : Nat := if n ≤ t then n else t + ((n - t) % p)

end JointCompleteness
end SemigroupBasis
