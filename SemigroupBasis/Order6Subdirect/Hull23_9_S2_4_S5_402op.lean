import SemigroupBasis.Order6Subdirect.Common
import SemigroupBasis.Generated.CatalogueOrder2
import SemigroupBasis.Generated.CatalogueOrder5Part04

/-!
# Product hull for Proposition 23.9 over S2_4 × S5_402^op

Covers the order-6 sporadic classes E10 = S6_8448, F5 = S6_11262
(Lee--Zhang, *Finite basis problem for semigroups of order six*, Section 23).
The published identity system is expanded below with every optional symbol
resolved (deleted / instantiated), giving 4 concrete identities in
≤ 6 variables.
Closure-search evidence (generator, 2026-07-14): the hull has 0 subdirect subsemigroups of order ≤ 5; no proper quotient of the member classes carries a proved basis modeled by both factors; of the 2133 proved order-≤5 basis records, 0 are modeled by both factors. Hence no order-≤5 transport can close the obligation: it is genuinely order-6 derivational work.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace SemigroupBasis
namespace Order6Subdirect
namespace Hull23_9_S2_4_S5_402op

/-- Left factor: catalogue class `S2_4` (proved basis in the P5 library). -/
def leftTable : FiniteTable := Generated.Catalogue.S2_4.table

/-- Right factor: catalogue class `S5_402` in the opposite orientation (proved basis in the P5 library). -/
def rightTable : FiniteTable := oppositeTable Generated.Catalogue.S5_402.table

/-- Left factor semigroup. -/
def G : Semigroup (Fin 2) := leftTable.semigroup

/-- Right factor semigroup. -/
def H : Semigroup (Fin 5) := rightTable.semigroup

/-- The product hull `G × H`; by the subdirect screen it generates the same
variety as each member class. -/
def P : Semigroup (Fin 2 × Fin 5) := G.prod H

private def powerIdentity6 : Identity (Fin 6) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [0]⟩⟩

private def leftIdentity6 : Identity (Fin 6) :=
  ⟨⟨0, [0, 1, 0]⟩, ⟨0, [1, 0]⟩⟩

private def rightIdentity6 : Identity (Fin 6) :=
  ⟨⟨0, [1, 0, 0]⟩, ⟨0, [1, 0]⟩⟩

private def longIdentity6 : Identity (Fin 6) :=
  ⟨⟨0, [1, 1, 2, 3, 3, 4, 5, 5]⟩, ⟨0, [3, 3, 4, 1, 1, 2, 5, 5]⟩⟩

/-- The published Proposition 23.9 system, expanded over `Fin 6`. -/
def finBasis : List (Identity (Fin 6)) :=
  [powerIdentity6,  -- 23.4a-power: xxx = xx
   leftIdentity6,   -- 23.4a-left: xxyx = xyx
   rightIdentity6,  -- 23.4a-right: xyxx = xyx
   longIdentity6]   -- 23.4b: hxxkyytzz = hyytxxkzz

/-- The published system over `Nat` variables (campaign convention). -/
def publishedBasis : List (Identity Nat) :=
  finBasis.map (Identity.map Fin.val)

private def powerIdentity2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [0]⟩⟩

private def leftIdentity2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 0]⟩, ⟨0, [1, 0]⟩⟩

private def rightIdentity2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0, 0]⟩, ⟨0, [1, 0]⟩⟩

private theorem powerIdentity_map :
    powerIdentity2.map Fin.val = powerIdentity6.map Fin.val :=
  rfl

private theorem leftIdentity_map :
    leftIdentity2.map Fin.val = leftIdentity6.map Fin.val :=
  rfl

private theorem rightIdentity_map :
    rightIdentity2.map Fin.val = rightIdentity6.map Fin.val :=
  rfl

/-- A six-coordinate valuation assembled without materializing the full list
of `order ^ 6` assignments. -/
private def valuation6 {S : Type u}
    (a0 a1 a2 a3 a4 a5 : S) : Fin 6 → S :=
  Fin.cases a0 <| Fin.cases a1 <| Fin.cases a2 <|
    Fin.cases a3 <| Fin.cases a4 <| Fin.cases a5 Fin.elim0

private theorem valuation6_eta {S : Type u} (valuation : Fin 6 → S) :
    valuation6 (valuation 0) (valuation 1) (valuation 2)
      (valuation 3) (valuation 4) (valuation 5) = valuation := by
  funext i
  refine Fin.cases rfl (fun i => ?_) i
  refine Fin.cases rfl (fun i => ?_) i
  refine Fin.cases rfl (fun i => ?_) i
  refine Fin.cases rfl (fun i => ?_) i
  refine Fin.cases rfl (fun i => ?_) i
  refine Fin.cases rfl (fun i => Fin.elim0 i) i

/-- Stack-bounded exhaustive checker for identities over exactly six
variables. Each list traversal has length `T.order`; no traversal has length
`T.order ^ 6`. -/
private def checkIdentity6 (T : FiniteTable)
    (identity : Identity (Fin 6)) : Bool :=
  (List.finRange T.order).all fun a0 =>
    (List.finRange T.order).all fun a1 =>
      (List.finRange T.order).all fun a2 =>
        (List.finRange T.order).all fun a3 =>
          (List.finRange T.order).all fun a4 =>
            (List.finRange T.order).all fun a5 =>
              decide
                (T.semigroup.eval (valuation6 a0 a1 a2 a3 a4 a5) identity.lhs =
                  T.semigroup.eval (valuation6 a0 a1 a2 a3 a4 a5) identity.rhs)

private theorem checkIdentity6_sound (T : FiniteTable)
    (identity : Identity (Fin 6))
    (checked : checkIdentity6 T identity = true) :
    identity.SatisfiedBy T.semigroup := by
  intro valuation
  have checked0 := (List.all_eq_true.mp checked)
    (valuation 0) (List.mem_finRange (valuation 0))
  have checked1 := (List.all_eq_true.mp checked0)
    (valuation 1) (List.mem_finRange (valuation 1))
  have checked2 := (List.all_eq_true.mp checked1)
    (valuation 2) (List.mem_finRange (valuation 2))
  have checked3 := (List.all_eq_true.mp checked2)
    (valuation 3) (List.mem_finRange (valuation 3))
  have checked4 := (List.all_eq_true.mp checked3)
    (valuation 4) (List.mem_finRange (valuation 4))
  have checked5 := (List.all_eq_true.mp checked4)
    (valuation 5) (List.mem_finRange (valuation 5))
  have concrete := of_decide_eq_true checked5
  simpa only [valuation6_eta] using concrete

private theorem models_of_four_checks (T : FiniteTable)
    (powerCheck : T.checkIdentity powerIdentity2 = true)
    (leftCheck : T.checkIdentity leftIdentity2 = true)
    (rightCheck : T.checkIdentity rightIdentity2 = true)
    (longCheck : checkIdentity6 T longIdentity6 = true) :
    Models T.semigroup publishedBasis := by
  intro identity member
  obtain ⟨finiteIdentity, finiteMember, rfl⟩ := List.mem_map.mp member
  simp only [finBasis, List.mem_cons, List.not_mem_nil, or_false] at finiteMember
  rcases finiteMember with rfl | rfl | rfl | rfl
  · rw [← powerIdentity_map]
    exact T.checkIdentityNat_sound powerIdentity2 powerCheck
  · rw [← leftIdentity_map]
    exact T.checkIdentityNat_sound leftIdentity2 leftCheck
  · rw [← rightIdentity_map]
    exact T.checkIdentityNat_sound rightIdentity2 rightCheck
  · exact longIdentity6.satisfiedBy_map Fin.val T.semigroup
      (checkIdentity6_sound T longIdentity6 longCheck)

/-- Soundness of the published system in the left factor (exhaustive check). -/
theorem models_left : Models G publishedBasis :=
  models_of_four_checks leftTable (by decide) (by decide) (by decide) (by decide)

/-- Soundness of the published system in the right factor (exhaustive check). -/
theorem models_right : Models H publishedBasis :=
  models_of_four_checks rightTable (by decide) (by decide) (by decide) (by decide)

/-- Soundness of the published system in the product hull. -/
theorem models_prod : Models P publishedBasis := by
  intro e he
  exact Identity.satisfiedBy_prod (models_left e he) (models_right e he)

/-- **Open derivational obligation `O(23.9 | S2_4 × S5_402^op)`.**
Completeness of the published Proposition 23.9 system for the meet theory
`Id(S2_4) ∩ Id(S5_402^op)`.
Stated as an explicit named `Prop` (campaign style; never an axiom).
What it needs: a canonical-form/derivation argument showing that every
identity valid in both factors is `Derives`-reachable from the published
system.  The generator's closure scan proves no order-≤5 transport exists. -/
def DerivationalObligation : Prop :=
  ∀ e : Identity Nat,
    e.SatisfiedBy G → e.SatisfiedBy H →
      Derives publishedBasis e.lhs e.rhs

/-- Conditional closure: the obligation upgrades the published system to a
full finite basis of the product hull. -/
theorem prod_basisFor_of_obligation (h : DerivationalObligation) :
    BasisFor P publishedBasis := by
  refine ⟨models_prod, ?_⟩
  intro e valid
  exact h e ((prodFstSplit G H 0).pushforwardIdentity e valid)
    ((prodSndSplit G H 0).pushforwardIdentity e valid)

end Hull23_9_S2_4_S5_402op
end Order6Subdirect
end SemigroupBasis
