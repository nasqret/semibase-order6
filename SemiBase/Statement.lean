import SemigroupBasis.Nonfinite
import SemigroupBasis.Opposite
import SemigroupBasis.HomomorphicImage

/-!
# The statement of the order-six classification

This module fixes what the repository proves about the semigroups of order six.

A catalogue entry (`Entry`) is a class number `k` of the GAP library Smallsemi
(the class `[6, k]`) together with its multiplication table, written row by row
with the elements `0, …, 5` (Smallsemi's `1, …, 6`). `HasTable G rows` says that
the semigroup structure `G` on `Fin 6` has exactly this table. `Classified e` is
the claim made for one entry: the table is the table of a semigroup, and every
semigroup with this table is nonfinitely based if the class is one of the four
exceptional classes, and finitely based otherwise.

`FinitelyBased` and `NonfinitelyBased` are the predicates of
`SemigroupBasis.Nonfinite`: a semigroup is finitely based when some finite list
of identities over the variables `Nat` is a basis (`BasisFor`) for it, that is,
the identities hold in the semigroup and derive every identity that holds in it.

The second half of the module contains the lemmas that turn an endpoint theorem
of the proof development into the claim for a catalogue entry.
-/

universe u

namespace SemiBase

open SemigroupBasis

/-- One class of the catalogue: its Smallsemi number `id` (the class `[6, id]`)
and its multiplication table, where row `a` lists the products
`a * 0, …, a * 5`. -/
structure Entry where
  id : Nat
  rows : List (List Nat)

/-- The entry in row `a` and column `b` of a table (`0` when absent). -/
def entry (rows : List (List Nat)) (a b : Nat) : Nat :=
  (rows.getD a []).getD b 0

/-- The semigroup structure `G` on `Fin 6` has multiplication table `rows`:
the product `a * b` is the entry in row `a` and column `b`. -/
def HasTable (G : Semigroup (Fin 6)) (rows : List (List Nat)) : Prop :=
  ∀ a b : Fin 6, (G.mul a b).val = entry rows a.val b.val

instance (G : Semigroup (Fin 6)) (rows : List (List Nat)) :
    Decidable (HasTable G rows) :=
  inferInstanceAs (Decidable (∀ a b : Fin 6, (G.mul a b).val = entry rows a.val b.val))

/-- The Smallsemi numbers of the four nonfinitely based semigroups of order six:
`L`, `B₂¹`, `A₂ᵍ` and `A₂¹` (Lee and Zhang 2015, Main Theorem). -/
def nonfinitelyBasedIds : List Nat := [3843, 8564, 8878, 13747]

/-- The claim of the classification for one catalogue entry `e`: the table of
`e` is the multiplication table of a semigroup, and every semigroup on `Fin 6`
with this table is nonfinitely based if `e` is one of the four exceptional
classes and finitely based otherwise. -/
def Classified (e : Entry) : Prop :=
  (∃ G : Semigroup (Fin 6), HasTable G e.rows) ∧
    ∀ G : Semigroup (Fin 6), HasTable G e.rows →
      (e.id ∈ nonfinitelyBasedIds → NonfinitelyBased G) ∧
        (e.id ∉ nonfinitelyBasedIds → FinitelyBased G)

/-- Every entry of the list is classified. -/
def AllClassified : List Entry → Prop
  | [] => True
  | e :: es => Classified e ∧ AllClassified es

/-! ## From endpoint theorems to the claim -/

/-- A semigroup structure on `Fin 6` is determined by its table. -/
theorem eq_of_hasTable {G H : Semigroup (Fin 6)} {rows : List (List Nat)}
    (hG : HasTable G rows) (hH : HasTable H rows) : G = H := by
  have hmul : G.mul = H.mul := by
    funext a b
    exact Fin.ext ((hG a b).trans (hH a b).symm)
  cases G
  cases H
  cases hmul
  rfl

theorem opposite_opposite {S : Type u} (G : Semigroup S) :
    G.opposite.opposite = G := by
  cases G
  rfl

/-- A basis of `G`, read backwards, is a basis of the opposite semigroup. -/
theorem finitelyBased_opposite {S : Type u} {G : Semigroup S}
    (h : FinitelyBased G) : FinitelyBased G.opposite := by
  obtain ⟨basis, hbasis⟩ := h
  exact hbasis.oppositeReversed.finitelyBased

theorem nonfinitelyBased_opposite {S : Type u} {G : Semigroup S}
    (h : NonfinitelyBased G) : NonfinitelyBased G.opposite := by
  intro hop
  apply h
  have hback := finitelyBased_opposite hop
  rw [opposite_opposite] at hback
  exact hback

/-- The claim for a finitely based class, from one semigroup with its table. -/
theorem classified_of_finitelyBased {e : Entry}
    (hid : e.id ∉ nonfinitelyBasedIds) {H : Semigroup (Fin 6)}
    (hH : FinitelyBased H) (hrows : HasTable H e.rows) : Classified e := by
  unfold Classified
  refine ⟨⟨H, hrows⟩, fun G hG => ?_⟩
  have hGH : G = H := eq_of_hasTable hG hrows
  subst hGH
  exact ⟨fun h => absurd h hid, fun _ => hH⟩

/-- The claim for a nonfinitely based class, from one semigroup with its table. -/
theorem classified_of_nonfinitelyBased {e : Entry}
    (hid : e.id ∈ nonfinitelyBasedIds) {H : Semigroup (Fin 6)}
    (hH : NonfinitelyBased H) (hrows : HasTable H e.rows) : Classified e := by
  unfold Classified
  refine ⟨⟨H, hrows⟩, fun G hG => ?_⟩
  have hGH : G = H := eq_of_hasTable hG hrows
  subst hGH
  exact ⟨fun _ => hH, fun h => absurd hid h⟩

/-- The permutation of `Fin 6` given by the list `p` of images. -/
def perm6 (p : List Nat) (a : Fin 6) : Fin 6 :=
  ⟨p.getD a.val 0 % 6, Nat.mod_lt _ (by decide)⟩

/-- The semigroup structure carried over from `G` along a permutation `φ` of
`Fin 6` with inverse `ψ`. -/
def transport (G : Semigroup (Fin 6)) (φ ψ : Fin 6 → Fin 6)
    (hψφ : ∀ a, ψ (φ a) = a) : Semigroup (Fin 6) where
  mul a b := φ (G.mul (ψ a) (ψ b))
  assoc a b c := by
    simp only [hψφ, G.assoc]

/-- A semigroup and its copy along a permutation satisfy the same identities. -/
theorem sameIdentityTheory_transport (G : Semigroup (Fin 6))
    (φ ψ : Fin 6 → Fin 6) (hψφ : ∀ a, ψ (φ a) = a) (hφψ : ∀ b, φ (ψ b) = b) :
    SameIdentityTheory G (transport G φ ψ hψφ) := by
  intro e
  constructor
  · intro h
    exact Identity.satisfiedBy_homomorphicImage e h
      ⟨φ, fun a b => by simp only [transport, hψφ]⟩ (fun b => ⟨ψ b, hφψ b⟩)
  · intro h
    exact Identity.satisfiedBy_homomorphicImage e h
      ⟨ψ, fun a b => by simp only [transport, hψφ]⟩ (fun a => ⟨φ a, hψφ a⟩)

theorem finitelyBased_transport {G : Semigroup (Fin 6)}
    (φ ψ : Fin 6 → Fin 6) (hψφ : ∀ a, ψ (φ a) = a) (hφψ : ∀ b, φ (ψ b) = b)
    (h : FinitelyBased G) : FinitelyBased (transport G φ ψ hψφ) :=
  (finitelyBased_iff_of_sameIdentityTheory
    (sameIdentityTheory_transport G φ ψ hψφ hφψ)).mp h

/-! ## Lists of entries -/

theorem AllClassified.nil : AllClassified [] := True.intro

theorem AllClassified.cons {e : Entry} {es : List Entry}
    (h : Classified e) (hs : AllClassified es) : AllClassified (e :: es) :=
  And.intro h hs

theorem AllClassified.append :
    ∀ {l₁ l₂ : List Entry}, AllClassified l₁ → AllClassified l₂ →
      AllClassified (l₁ ++ l₂)
  | [], _, _, h₂ => h₂
  | _ :: _, _, h₁, h₂ => And.intro h₁.1 (AllClassified.append h₁.2 h₂)

theorem AllClassified.mem :
    ∀ {l : List Entry}, AllClassified l → ∀ e ∈ l, Classified e
  | [], _, _, he => nomatch he
  | _ :: _, h, e, he => by
      cases he with
      | head => exact h.1
      | tail _ hmem => exact AllClassified.mem h.2 e hmem

end SemiBase
