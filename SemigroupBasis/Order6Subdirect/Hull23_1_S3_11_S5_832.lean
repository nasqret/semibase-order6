import SemigroupBasis.Order6Subdirect.Common
import SemigroupBasis.Generated.CatalogueOrder3
import SemigroupBasis.Generated.CatalogueOrder5Part07

/-!
# Product hull for Proposition 23.1 over S3_11 × S5_832

Covers the order-6 sporadic classes E9 = S6_11166
(Lee--Zhang, *Finite basis problem for semigroups of order six*, Section 23).
The published identity system is expanded below with every optional symbol
resolved (deleted / instantiated), giving 15 concrete identities in
≤ 5 variables.
Closure-search evidence (generator, 2026-07-14): the hull has 0 subdirect subsemigroups of order ≤ 5; no proper quotient of the member classes carries a proved basis modeled by both factors; of the 2133 proved order-≤5 basis records, 0 are modeled by both factors. Hence no order-≤5 transport can close the obligation: it is genuinely order-6 derivational work.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace SemigroupBasis
namespace Order6Subdirect
namespace Hull23_1_S3_11_S5_832

/-- Left factor: catalogue class `S3_11` (proved basis in the P5 library). -/
def leftTable : FiniteTable := Generated.Catalogue.S3_11.table

/-- Right factor: catalogue class `S5_832` (proved basis in the P5 library). -/
def rightTable : FiniteTable := Generated.Catalogue.S5_832.table

/-- Left factor semigroup. -/
def G : Semigroup (Fin 3) := leftTable.semigroup

/-- Right factor semigroup. -/
def H : Semigroup (Fin 5) := rightTable.semigroup

/-- The product hull `G × H`; by the subdirect screen it generates the same
variety as each member class. -/
def P : Semigroup (Fin 3 × Fin 5) := G.prod H

/-- The published Proposition 23.1 system, expanded over `Fin 5`. -/
def finBasis : List (Identity (Fin 5)) :=
  [   -- 23.1a: xxyx = xxxyyy
   ⟨⟨0, [0, 1, 0]⟩, ⟨0, [0, 0, 1, 1, 1]⟩⟩,
   -- 23.1b[-]: xxxx = xx
   ⟨⟨0, [0, 0, 0]⟩, ⟨0, [0]⟩⟩,
   -- 23.1b[h]: xhxxx = xhx
   ⟨⟨0, [1, 0, 0, 0]⟩, ⟨0, [1, 0]⟩⟩,
   -- 23.1c[-]: xyxx = xyyy
   ⟨⟨0, [1, 0, 0]⟩, ⟨0, [1, 1, 1]⟩⟩,
   -- 23.1c[h]: xhyxx = xhyyy
   ⟨⟨0, [1, 2, 0, 0]⟩, ⟨0, [1, 2, 2, 2]⟩⟩,
   -- 23.1d[-]: xyyyx = xyx
   ⟨⟨0, [1, 1, 1, 0]⟩, ⟨0, [1, 0]⟩⟩,
   -- 23.1d[h]: xhyyyx = xhyx
   ⟨⟨0, [1, 2, 2, 2, 0]⟩, ⟨0, [1, 2, 0]⟩⟩,
   -- 23.1e[-]: xyxy = xyyx
   ⟨⟨0, [1, 0, 1]⟩, ⟨0, [1, 1, 0]⟩⟩,
   -- 23.1e[k]: xykxy = xykyx
   ⟨⟨0, [1, 2, 0, 1]⟩, ⟨0, [1, 2, 1, 0]⟩⟩,
   -- 23.1e[h]: xhyxy = xhyyx
   ⟨⟨0, [1, 2, 0, 2]⟩, ⟨0, [1, 2, 2, 0]⟩⟩,
   -- 23.1e[hk]: xhykxy = xhykyx
   ⟨⟨0, [1, 2, 3, 0, 2]⟩, ⟨0, [1, 2, 3, 2, 0]⟩⟩,
   -- 23.1f[-]: yxyzz = yxxzzxy
   ⟨⟨0, [1, 0, 2, 2]⟩, ⟨0, [1, 1, 2, 2, 1, 0]⟩⟩,
   -- 23.1f[k]: yxykzz = yxxkzzxy
   ⟨⟨0, [1, 0, 2, 3, 3]⟩, ⟨0, [1, 1, 2, 3, 3, 1, 0]⟩⟩,
   -- 23.1f[h]: yhxyzz = yhxxzzxy
   ⟨⟨0, [1, 2, 0, 3, 3]⟩, ⟨0, [1, 2, 2, 3, 3, 2, 0]⟩⟩,
   -- 23.1f[hk]: yhxykzz = yhxxkzzxy
   ⟨⟨0, [1, 2, 0, 3, 4, 4]⟩, ⟨0, [1, 2, 2, 3, 4, 4, 2, 0]⟩⟩]

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

/-- **Open derivational obligation `O(23.1 | S3_11 × S5_832)`.**
Completeness of the published Proposition 23.1 system for the meet theory
`Id(S3_11) ∩ Id(S5_832)`.
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

end Hull23_1_S3_11_S5_832
end Order6Subdirect
end SemigroupBasis
