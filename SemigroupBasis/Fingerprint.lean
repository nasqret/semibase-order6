import SemigroupBasis.ChainReplay
import SemigroupBasis.FiniteTable

/-!
# Fingerprint completeness: certificate-driven `BasisFor`

The fixed-alphabet theorem that collapses a completeness proof into finite
certificate data plus an essential semantic soundness hypothesis. A
certificate consists of

* a deterministic profile automaton over the letter alphabet `α`,
* a canonical representative word per automaton state,
* replayable derivation chains realizing the Transition Closure through the
  shared `SemigroupBasis.ChainReplay` kernel
  (BASE_CASE.md §2.3, genericized): `[x] ⟶ rep (init x)` and
  `rep q ⧺ c ⟶ rep (step q c)`,
* a separating valuation for every pair of states whose representatives
  differ as words.

Together with `Models G basis`, these data let `Certificate.basisFor` produce
`BasisFor G basis` for the fixed alphabet `α`: `basis` derives every
`G`-valid identity in those variables. The chains prove normalization only.
Semantic soundness comes from `Models`, and completeness uses both
normalization and the separating valuations (see DESIGN.md §0).

`Certificate.basisFor` has no word-length cutoff: it covers every nonempty word
over the certificate's chosen alphabet. The alphabet is nevertheless fixed by
each theorem application. In particular, an instance at `α := Fin n` proves
full word-length completeness only for identities with variables in `Fin n`;
it does not itself discharge the separate bridge to `Nat` or to an
unbounded-variable family. That bridge must come from an independent
variable-renaming theorem or from a profile argument instantiated at `Nat`.

Everything is Mathlib-free and `decide`-friendly; the only classical
content is `propext`/`Quot.sound` via `decide` at instantiation time.
-/

namespace SemigroupBasis
namespace Fingerprint

/-- A deterministic profile automaton over letter alphabet `α` with state
type `Q`: `init` reads the first letter, `step` consumes subsequent letters.
In practice `Q` is a product of finite monoid readers (parity counters,
last-occurrence data, …); the theorem needs no structure on `Q` at all. -/
structure ProfileAutomaton (α : Type u) (Q : Type v) where
  init : α → Q
  step : Q → α → Q

namespace ProfileAutomaton

/-- The state reached after reading a (nonempty) word. -/
def run (A : ProfileAutomaton α Q) (w : Word α) : Q :=
  w.tail.foldl A.step (A.init w.head)

@[simp] theorem run_singleton (A : ProfileAutomaton α Q) (x : α) :
    A.run (Word.singleton x) = A.init x := rfl

theorem run_snoc (A : ProfileAutomaton α Q) (h : α) (t : List α) (c : α) :
    A.run ⟨h, t ++ [c]⟩ = A.step (A.run ⟨h, t⟩) c := by
  simp [run, List.foldl_append]

end ProfileAutomaton

/-- The fingerprint certificate: automaton, canonical representatives,
transition-closure chains, and separating valuations.  `S` is the carrier
of the target semigroup. -/
structure Certificate (α : Type u) (Q : Type v) (S : Type w) where
  auto : ProfileAutomaton α Q
  rep : Q → Word α
  denseIndex : α → Nat
  initChain : α → ChainReplay.Chain α
  stepChain : Q → α → ChainReplay.Chain α
  sep : Q → Q → α → S

namespace Certificate

variable [DecidableEq α]

/-- Finite check: every initial chain replays `[x]` to `rep (init x)`. -/
abbrev InitChainsOk (C : Certificate α Q S) (basis : List (Identity α)) : Prop :=
  ∀ x : α,
    ChainReplay.replay C.denseIndex basis (Word.singleton x) (C.initChain x)
      = some (C.rep (C.auto.init x))

/-- Finite check (the Transition Closure): every step chain replays
`rep q ⧺ c` to `rep (step q c)`. -/
abbrev StepChainsOk (C : Certificate α Q S) (basis : List (Identity α)) : Prop :=
  ∀ (q : Q) (c : α),
    ChainReplay.replay C.denseIndex basis
      (C.rep q ++ Word.singleton c) (C.stepChain q c)
      = some (C.rep (C.auto.step q c))

/-- Finite check: states with distinct representative words are separated
in `G` by the recorded valuation. -/
abbrev SepOk (C : Certificate α Q S) (G : Semigroup S) : Prop :=
  ∀ q q' : Q, C.rep q ≠ C.rep q' →
    G.eval (C.sep q q') (C.rep q) ≠ G.eval (C.sep q q') (C.rep q')

/-- One row of the Transition Closure check (chunked-`decide` unit). -/
abbrev StepRowOk (C : Certificate α Q S) (basis : List (Identity α))
    (q : Q) : Prop :=
  ∀ c : α,
    ChainReplay.replay C.denseIndex basis
      (C.rep q ++ Word.singleton c) (C.stepChain q c)
      = some (C.rep (C.auto.step q c))

theorem stepChainsOk_of_rows {C : Certificate α Q S}
    {basis : List (Identity α)}
    (h : ∀ q : Q, C.StepRowOk basis q) : C.StepChainsOk basis :=
  fun q => h q

/-- One row of the separation check (chunked-`decide` unit). -/
abbrev SepRowOk (C : Certificate α Q S) (G : Semigroup S) (q : Q) : Prop :=
  ∀ q' : Q, C.rep q ≠ C.rep q' →
    G.eval (C.sep q q') (C.rep q) ≠ G.eval (C.sep q q') (C.rep q')

omit [DecidableEq α] in
theorem sepOk_of_rows {C : Certificate α Q S} {G : Semigroup S}
    (h : ∀ q : Q, C.SepRowOk G q) : C.SepOk G :=
  fun q => h q

/-- **REACH** — the constructive Contraction Lemma: every word derives to
the representative of its profile state.  This is BASE_CASE.md §2.3's
induction, genericized; no length bound appears. -/
theorem reach {C : Certificate α Q S} {basis : List (Identity α)}
    (hI : C.InitChainsOk basis) (hS : C.StepChainsOk basis) :
    ∀ w : Word α, Derives basis w (C.rep (C.auto.run w)) := by
  suffices aux : ∀ (h : α) (rt : List α),
      Derives basis ⟨h, rt.reverse⟩ (C.rep (C.auto.run ⟨h, rt.reverse⟩)) by
    intro w
    have hw := aux w.head w.tail.reverse
    rw [List.reverse_reverse] at hw
    exact hw
  intro h rt
  induction rt with
  | nil => exact ChainReplay.replay_sound (hI h)
  | cons c rt ih =>
      rw [List.reverse_cons]
      rw [ProfileAutomaton.run_snoc]
      have happ :
          (⟨h, rt.reverse ++ [c]⟩ : Word α)
            = (⟨h, rt.reverse⟩ : Word α) ++ Word.singleton c := rfl
      rw [happ]
      have h1 :
          Derives basis ((⟨h, rt.reverse⟩ : Word α) ++ Word.singleton c)
            (C.rep (C.auto.run ⟨h, rt.reverse⟩) ++ Word.singleton c) :=
        Derives.appendRight ih (Word.singleton c)
      have h2 :=
        ChainReplay.replay_sound (hS (C.auto.run ⟨h, rt.reverse⟩) c)
      exact Derives.trans h1 h2

end Certificate

/-- **Abstract two-layer H2 interface** (the profile layer of the design):
a profile map `φ` into an arbitrary type, a normal form `nf` on profiles
with a derivable normalization (`hReach`), and the *necessity* half of
profile completeness restricted through `nf` (`hNec`: valid identities have
equal normal forms) yield a basis theorem.  This layer is descriptor-language
agnostic and works for any alphabet, including `Nat` — hand-written
unbounded-variable completeness proofs can target it directly.  Note that
only necessity is load-bearing: the sufficiency half of `ProfileComplete`
follows a posteriori from `hM` + `hReach` and is never assumed. -/
theorem basisFor_of_profile {S : Type u} {α : Type v} {P : Type w}
    {G : Semigroup S} {basis : List (Identity α)}
    (φ : Word α → P) (nf : P → Word α)
    (hM : Models G basis)
    (hReach : ∀ w : Word α, Derives basis w (nf (φ w)))
    (hNec : ∀ u v : Word α,
      (∀ val : α → S, G.eval val u = G.eval val v) → nf (φ u) = nf (φ v)) :
    BasisFor G basis := by
  refine ⟨hM, ?_⟩
  intro e valid
  have hu := hReach e.lhs
  have hv := hReach e.rhs
  have heq : nf (φ e.lhs) = nf (φ e.rhs) := hNec e.lhs e.rhs valid
  exact Derives.trans hu (heq ▸ Derives.symm hv)

namespace Certificate

variable [DecidableEq α]

/-- **FIXED-ALPHABET FINGERPRINT COMPLETENESS.** A certificate whose checks
pass, together with the essential `Models G basis` hypothesis, yields a basis
theorem over `α`. The replayed chains supply normalization; `Models` and the
separating valuations jointly supply the semantic necessity argument. There is
no word-length bound. For `α = Fin n`, this remains a theorem only over
`Fin n`; it does not supply the terminal bridge to `Nat`. -/
theorem basisFor {G : Semigroup S} {basis : List (Identity α)}
    (C : Certificate α Q S)
    (hM : Models G basis)
    (hI : C.InitChainsOk basis)
    (hS : C.StepChainsOk basis)
    (hSep : C.SepOk G) :
    BasisFor G basis := by
  refine basisFor_of_profile C.auto.run C.rep hM (reach hI hS) ?_
  intro u v valid
  apply Decidable.byContradiction
  intro hne
  apply hSep _ _ hne
  have hu := reach hI hS (C := C) u
  have hv := reach hI hS (C := C) v
  have h1 := (Derives.sound hM hu (C.sep (C.auto.run u) (C.auto.run v))).symm
  have h2 := Derives.sound hM hv (C.sep (C.auto.run u) (C.auto.run v))
  exact h1.trans ((valid _).trans h2)

end Certificate

/-- Discharge `Models` for a finite table by one boolean sweep
(`FiniteTable.checkIdentity` over the explicit valuation enumeration). -/
theorem models_of_checkList (T : FiniteTable) {n : Nat}
    (basis : List (Identity (Fin n)))
    (h : (basis.all fun e => T.checkIdentity e) = true) :
    Models T.semigroup basis := by
  intro e he
  exact T.checkIdentity_sound e (List.all_eq_true.mp h e he)

/-- Letter relabeling within one alphabet is derivability-preserving
(substitution by singletons).  Used by the equivariant upgrade (DESIGN §4). -/
theorem derives_relabel {basis : List (Identity α)} {u v : Word α}
    (h : Derives basis u v) (f : α → α) :
    Derives basis (u.bind fun x => Word.singleton (f x))
      (v.bind fun x => Word.singleton (f x)) :=
  Derives.subst h _

end Fingerprint
end SemigroupBasis
