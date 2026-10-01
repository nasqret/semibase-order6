import SemigroupBasis.Order6Subdirect.Hull21_1_S5_831_S3_8

/-!
# `S6_8222` (label D6, Section 21, Proposition 21.1)

Order-6 sporadic class, Smallsemi id `[6, 8222]`
(published table; catalogue orientation direct).
Subdirect presentation from the verified screen
`research/order6/subdirect_screen_2026-07-14.json`:
congruence pair `[0, 0, 1, 2, 3, 4]` / `[0, 1, 0, 0, 0, 2]` (class maps), factors
S5_831 × S3_8 via the recorded isomorphism `[0, 1, 2, 4, 3]` and
isomorphism `[0, 1, 2]`, set-level sections
`[0, 2, 3, 5, 4]` / `[0, 1, 5]` (composed with the isos below).
Endpoints: identity theory of `S6_8222` = identity theory of the product hull.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace SemigroupBasis
namespace Order6Subdirect
namespace S6_8222

open Hull21_1_S5_831_S3_8
/-- Published multiplication table of `S6_8222`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6)) else if a = 1 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6)) else if a = 2 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (3 : Fin 6) else (0 : Fin 6)) else if a = 3 then (if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6)) else if a = 4 then (if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6)) else (if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (5 : Fin 6))

/-- Stored table with decided associativity. -/
def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

/-- The published Cayley matrix, row-major (zero-based). -/
def publishedRows : List (List Nat) :=
  [[0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 1],
   [0, 0, 0, 0, 3, 0],
   [3, 3, 3, 3, 3, 3],
   [4, 4, 4, 4, 4, 4],
   [0, 1, 2, 3, 0, 5]]

/-- `decide`-binding of the stored multiplication to the published matrix. -/
theorem mul_matches_published :
    ((List.finRange 6).map fun a =>
      (List.finRange 6).map fun b => (mul a b).val) = publishedRows := by
  decide
/-- Quotient factor 1 table from the screen witness (class map `[0, 0, 1, 2, 3, 4]`). -/
def factor1Mul (a b : Fin 5) : Fin 5 :=
  if a = 0 then (if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5)) else if a = 1 then (if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (2 : Fin 5) else (0 : Fin 5)) else if a = 2 then (if b = 0 then (2 : Fin 5) else if b = 1 then (2 : Fin 5) else if b = 2 then (2 : Fin 5) else if b = 3 then (2 : Fin 5) else (2 : Fin 5)) else if a = 3 then (if b = 0 then (3 : Fin 5) else if b = 1 then (3 : Fin 5) else if b = 2 then (3 : Fin 5) else if b = 3 then (3 : Fin 5) else (3 : Fin 5)) else (if b = 0 then (0 : Fin 5) else if b = 1 then (1 : Fin 5) else if b = 2 then (2 : Fin 5) else if b = 3 then (0 : Fin 5) else (4 : Fin 5))
/-- Recorded isomorphism perm `[0, 1, 2, 4, 3]` onto catalogue `S5_831`. -/
def iso1 (a : Fin 5) : Fin 5 :=
  if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else if a = 3 then (4 : Fin 5) else (3 : Fin 5)

/-- Witness factor 1 is carried onto the catalogue class by `iso1`
(the orientation is absorbed in `G`). -/
theorem factor1_matches_catalogue :
    ∀ a b : Fin 5, iso1 (factor1Mul a b) = G.mul (iso1 a) (iso1 b) := by
  decide
/-- Projection onto the left catalogue factor (congruence class map composed with `iso1`). -/
def projLeft (a : Fin 6) : Fin 5 :=
  if a = 0 then (0 : Fin 5) else if a = 1 then (0 : Fin 5) else if a = 2 then (1 : Fin 5) else if a = 3 then (2 : Fin 5) else if a = 4 then (4 : Fin 5) else (3 : Fin 5)
/-- Set-level section of `projLeft` (block representatives; right inverse only, no hom claim needed). -/
def secLeft (a : Fin 5) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (2 : Fin 6) else if a = 2 then (3 : Fin 6) else if a = 3 then (5 : Fin 6) else (4 : Fin 6)

/-- The left projection as a split surjection (all fields `decide`). -/
def ontoLeft : SplitSurjection table.semigroup G where
  toFun := projLeft
  map_mul := by decide
  preimage := secLeft
  right_inverse := by decide
/-- Quotient factor 2 table from the screen witness (class map `[0, 1, 0, 0, 0, 2]`). -/
def factor2Mul (a b : Fin 3) : Fin 3 :=
  if a = 0 then (if b = 0 then (0 : Fin 3) else if b = 1 then (0 : Fin 3) else (0 : Fin 3)) else if a = 1 then (if b = 0 then (0 : Fin 3) else if b = 1 then (0 : Fin 3) else (1 : Fin 3)) else (if b = 0 then (0 : Fin 3) else if b = 1 then (1 : Fin 3) else (2 : Fin 3))
/-- Recorded isomorphism perm `[0, 1, 2]` onto catalogue `S3_8`. -/
def iso2 (a : Fin 3) : Fin 3 :=
  if a = 0 then (0 : Fin 3) else if a = 1 then (1 : Fin 3) else (2 : Fin 3)

/-- Witness factor 2 is carried onto the catalogue class by `iso2`
(the orientation is absorbed in `H`). -/
theorem factor2_matches_catalogue :
    ∀ a b : Fin 3, iso2 (factor2Mul a b) = H.mul (iso2 a) (iso2 b) := by
  decide
/-- Projection onto the right catalogue factor (congruence class map composed with `iso2`). -/
def projRight (a : Fin 6) : Fin 3 :=
  if a = 0 then (0 : Fin 3) else if a = 1 then (1 : Fin 3) else if a = 2 then (0 : Fin 3) else if a = 3 then (0 : Fin 3) else if a = 4 then (0 : Fin 3) else (2 : Fin 3)
/-- Set-level section of `projRight` (block representatives; right inverse only, no hom claim needed). -/
def secRight (a : Fin 3) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (5 : Fin 6)

/-- The right projection as a split surjection (all fields `decide`). -/
def ontoRight : SplitSurjection table.semigroup H where
  toFun := projRight
  map_mul := by decide
  preimage := secRight
  right_inverse := by decide

/-- The subdirect embedding map into the product hull. -/
def embed (t : Fin 6) : Fin 5 × Fin 3 :=
  (projLeft t, projRight t)

private theorem embed_injective :
    ∀ a b : Fin 6, embed a = embed b → a = b := by
  decide

/-- The embedding `S6_8222 ↪ S5_831 × S3_8`. -/
def intoProd : Embedding table.semigroup P where
  toFun := embed
  map_mul := by decide
  injective := by
    intro a b h
    exact embed_injective a b h

/-- **Identity-theory reduction to the product hull** (universe-polymorphic):
`S6_8222` satisfies exactly the identities of S5_831 × S3_8. -/
theorem sameIdentityTheoryOver_prod (α : Type u) :
    SameIdentityTheoryOver table.semigroup P α :=
  sameIdentityTheoryOver_prod_of_subdirect intoProd ontoLeft ontoRight α

/-- `var(S6_8222) = var(S5_831 × S3_8)` over the standard variable type. -/
theorem sameIdentityTheory_prod : SameIdentityTheory table.semigroup P :=
  sameIdentityTheoryOver_prod Nat

/-- Every basis transfers between `S6_8222` and its product hull, in both
directions. -/
theorem basisFor_iff {α : Type u} (basis : List (Identity α)) :
    BasisFor table.semigroup basis ↔ BasisFor P basis :=
  basisFor_iff_prod_of_subdirect intoProd ontoLeft ontoRight

/-- Finite basability is equivalent for `S6_8222` and its hull. -/
theorem finitelyBased_iff_prod :
    FinitelyBased table.semigroup ↔ FinitelyBased P :=
  finitelyBased_iff_prod_of_subdirect intoProd ontoLeft ontoRight

/-- The published Proposition 21.1 system is sound for `S6_8222`. -/
theorem models_published : Models table.semigroup publishedBasis := by
  intro e he
  exact (sameIdentityTheory_prod e).mpr (models_prod e he)

/-- Conditional representative basis: the named open derivational obligation
`O(21.1 | S5_831 × S3_8)` upgrades the published system to a
finite basis of `S6_8222` itself. -/
theorem representative_basis_of_obligation
    (h : Hull21_1_S5_831_S3_8.DerivationalObligation) :
    BasisFor table.semigroup Hull21_1_S5_831_S3_8.publishedBasis :=
  (basisFor_iff _).mpr (prod_basisFor_of_obligation h)

end S6_8222
end Order6Subdirect
end SemigroupBasis
