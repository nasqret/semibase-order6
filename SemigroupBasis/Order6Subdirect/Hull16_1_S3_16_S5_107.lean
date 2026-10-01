import SemigroupBasis.Order6Subdirect.Common
import SemigroupBasis.Generated.CatalogueOrder3
import SemigroupBasis.Generated.CatalogueOrder5Part01

/-!
# Product hull for Proposition 16.1 over S3_16 × S5_107

Covers the order-6 sporadic classes C1 = S6_3813, D3 = S6_6437
(Lee--Zhang, *Finite basis problem for semigroups of order six*, Section 16).
The published identity system is expanded below with every optional symbol
resolved (deleted / instantiated), giving 10 concrete identities in
≤ 4 variables.
Closure-search evidence (generator, 2026-07-14): the hull has 0 subdirect subsemigroups of order ≤ 5; no proper quotient of the member classes carries a proved basis modeled by both factors; of the 2133 proved order-≤5 basis records, 0 are modeled by both factors. Hence no order-≤5 transport can close the obligation: it is genuinely order-6 derivational work.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace SemigroupBasis
namespace Order6Subdirect
namespace Hull16_1_S3_16_S5_107

/-- Left factor: catalogue class `S3_16` (proved basis in the P5 library). -/
def leftTable : FiniteTable := Generated.Catalogue.S3_16.table

/-- Right factor: catalogue class `S5_107` (proved basis in the P5 library). -/
def rightTable : FiniteTable := Generated.Catalogue.S5_107.table

/-- Left factor semigroup. -/
def G : Semigroup (Fin 3) := leftTable.semigroup

/-- Right factor semigroup. -/
def H : Semigroup (Fin 5) := rightTable.semigroup

/-- The product hull `G × H`; by the subdirect screen it generates the same
variety as each member class. -/
def P : Semigroup (Fin 3 × Fin 5) := G.prod H

/-- The published Proposition 16.1 system, expanded over `Fin 4`. -/
def finBasis : List (Identity (Fin 4)) :=
  [   -- 16.1a-power: xxx = xx
   ⟨⟨0, [0, 0]⟩, ⟨0, [0]⟩⟩,
   -- 16.1a-left: xxyx = xyx
   ⟨⟨0, [0, 1, 0]⟩, ⟨0, [1, 0]⟩⟩,
   -- 16.1a-right: xyxx = xyx
   ⟨⟨0, [1, 0, 0]⟩, ⟨0, [1, 0]⟩⟩,
   -- 16.1b: xyxzz = xxyzz
   ⟨⟨0, [1, 0, 2, 2]⟩, ⟨0, [0, 1, 2, 2]⟩⟩,
   -- 16.1c[-]: xxyy = xyyx
   ⟨⟨0, [0, 1, 1]⟩, ⟨0, [1, 1, 0]⟩⟩,
   -- 16.1c[h]: xxhyy = xhyyx
   ⟨⟨0, [0, 1, 2, 2]⟩, ⟨0, [1, 2, 2, 0]⟩⟩,
   -- 16.1d[-]: xyxy = xyyx
   ⟨⟨0, [1, 0, 1]⟩, ⟨0, [1, 1, 0]⟩⟩,
   -- 16.1d[k]: xykxy = xykyx
   ⟨⟨0, [1, 2, 0, 1]⟩, ⟨0, [1, 2, 1, 0]⟩⟩,
   -- 16.1d[h]: xhyxy = xhyyx
   ⟨⟨0, [1, 2, 0, 2]⟩, ⟨0, [1, 2, 2, 0]⟩⟩,
   -- 16.1d[hk]: xhykxy = xhykyx
   ⟨⟨0, [1, 2, 3, 0, 2]⟩, ⟨0, [1, 2, 3, 2, 0]⟩⟩]

/-- The published system over `Nat` variables (campaign convention). -/
def publishedBasis : List (Identity Nat) :=
  finBasis.map (Identity.map Fin.val)

/-- Soundness of the published system in the left factor (exhaustive check). -/
theorem models_left : Models G publishedBasis :=
  models_of_finite_checks leftTable finBasis (by decide)

/-- Soundness of the published system in the right factor (exhaustive check). -/
theorem models_right : Models H publishedBasis :=
  models_of_finite_checks rightTable finBasis (by decide)

/-- Soundness of the published system in the product hull. -/
theorem models_prod : Models P publishedBasis := by
  intro e he
  exact Identity.satisfiedBy_prod (models_left e he) (models_right e he)

/-- **Open derivational obligation `O(16.1 | S3_16 × S5_107)`.**
Completeness of the published Proposition 16.1 system for the meet theory
`Id(S3_16) ∩ Id(S5_107)`.
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

end Hull16_1_S3_16_S5_107
end Order6Subdirect
end SemigroupBasis
