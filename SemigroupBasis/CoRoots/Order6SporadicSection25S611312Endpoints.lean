import SemigroupBasis.CoRoots.Order6SporadicSection25F4Completeness
import SemigroupBasis.CoRoots.Order6SporadicSection25F4Soundness

namespace SemigroupBasis.CoRoots.Order6SporadicSection25.S6_11312
open SemigroupBasis

/-! Exact published F4 witness data, explicitly transported to the actual
catalogue table. Every finite field and relabeling is re-proved here. -/

namespace Published

def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6)) else if a = 1 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6)) else if a = 2 then (if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6)) else if a = 3 then (if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6)) else if a = 4 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)) else (if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (5 : Fin 6) else (4 : Fin 6))

def projLeft (a : Fin 6) : Fin 4 :=
  if a = 0 then (2 : Fin 4) else if a = 1 then (2 : Fin 4) else if a = 2 then (2 : Fin 4) else if a = 3 then (3 : Fin 4) else if a = 4 then (0 : Fin 4) else (1 : Fin 4)
/-- Set-level section of `projLeft` (block representatives; right inverse only, no hom claim needed). -/
def secLeft (a : Fin 4) : Fin 6 :=
  if a = 0 then (4 : Fin 6) else if a = 1 then (5 : Fin 6) else if a = 2 then (0 : Fin 6) else (3 : Fin 6)

def projRight (a : Fin 6) : Fin 4 :=
  if a = 0 then (0 : Fin 4) else if a = 1 then (1 : Fin 4) else if a = 2 then (2 : Fin 4) else if a = 3 then (0 : Fin 4) else if a = 4 then (3 : Fin 4) else (3 : Fin 4)
/-- Set-level section of `projRight` (block representatives; right inverse only, no hom claim needed). -/
def secRight (a : Fin 4) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else (4 : Fin 6)

end Published

def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6)) else if a = 1 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6)) else if a = 2 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (5 : Fin 6)) else if a = 3 then (if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (5 : Fin 6) else (0 : Fin 6)) else if a = 4 then (if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (4 : Fin 6) else (0 : Fin 6)) else (if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6))

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def catalogueRows : List (List Nat) := [[0, 0, 0, 0, 0, 0], [0, 0, 1, 1, 0, 0], [0, 0, 2, 3, 0, 5], [5, 5, 3, 2, 5, 0], [0, 1, 1, 1, 4, 0], [5, 5, 5, 5, 5, 5]]

theorem table_literal_exact :
    (List.finRange 6).map (fun a => (List.finRange 6).map (fun b => (mul a b).val)) =
      catalogueRows := by decide

def publishedToActual (a : Fin 6) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (4 : Fin 6) else if a = 3 then (5 : Fin 6) else if a = 4 then (2 : Fin 6) else (3 : Fin 6)

def actualToPublished (a : Fin 6) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (4 : Fin 6) else if a = 3 then (5 : Fin 6) else if a = 4 then (2 : Fin 6) else (3 : Fin 6)

theorem publishedToActual_mul (a b : Fin 6) :
    publishedToActual (Published.mul a b) = mul (publishedToActual a) (publishedToActual b) := by decide +revert

theorem publishedToActual_left_inverse (a : Fin 6) :
    actualToPublished (publishedToActual a) = a := by decide +revert

theorem publishedToActual_right_inverse (a : Fin 6) :
    publishedToActual (actualToPublished a) = a := by decide +revert

def G : Semigroup (Fin 4) := Generated.Catalogue.S4_96.table.semigroup.opposite
def H : Semigroup (Fin 4) := Generated.Catalogue.S4_70.table.semigroup
def P : Semigroup (Fin 4 × Fin 4) := G.prod H

def projLeft (a : Fin 6) : Fin 4 := Published.projLeft (actualToPublished a)
def projRight (a : Fin 6) : Fin 4 := Published.projRight (actualToPublished a)
def secLeft (a : Fin 4) : Fin 6 := publishedToActual (Published.secLeft a)
def secRight (a : Fin 4) : Fin 6 := publishedToActual (Published.secRight a)

theorem left_map_mul (a b : Fin 6) :
    projLeft (mul a b) = G.mul (projLeft a) (projLeft b) := by decide +revert

theorem right_map_mul (a b : Fin 6) :
    projRight (mul a b) = H.mul (projRight a) (projRight b) := by decide +revert

theorem left_section (a : Fin 4) : projLeft (secLeft a) = a := by decide +revert
theorem right_section (a : Fin 4) : projRight (secRight a) = a := by decide +revert

def ontoLeft : SplitSurjection table.semigroup G where
  toFun := projLeft
  map_mul := left_map_mul
  preimage := secLeft
  right_inverse := left_section

def ontoRight : SplitSurjection table.semigroup H where
  toFun := projRight
  map_mul := right_map_mul
  preimage := secRight
  right_inverse := right_section

def embed (a : Fin 6) : Fin 4 × Fin 4 := (projLeft a, projRight a)

theorem embed_injective (a b : Fin 6) (equal : embed a = embed b) : a = b := by decide +revert

def intoProd : Embedding table.semigroup P where
  toFun := embed
  map_mul := by
    intro a b
    exact Prod.ext (left_map_mul a b) (right_map_mul a b)
  injective := by
    intro a b equal
    exact embed_injective a b equal

theorem sameIdentityTheoryOver_actual_factors (alphabet : Type) :
    SameIdentityTheoryOver table.semigroup P alphabet :=
  Order6Subdirect.sameIdentityTheoryOver_prod_of_subdirect intoProd ontoLeft ontoRight alphabet

theorem models_raw : Models table.semigroup (basis false) := by
  intro identity member
  have affine : identity.SatisfiedBy G := core_models_affine identity member
  have component : identity.SatisfiedBy H := core_models_component identity member
  exact intoProd.pullback_identity identity (Identity.satisfiedBy_prod affine component)

theorem representative_basis : BasisFor table.semigroup (basis false) := by
  refine ⟨models_raw, ?_⟩
  intro identity valid
  exact F4_derives_of_actual_factors identity
    (ontoLeft.pushforwardIdentity identity valid) (ontoRight.pushforwardIdentity identity valid)

theorem opposite_basis : BasisFor table.semigroup.opposite (reversedBasis (basis false)) :=
  representative_basis.oppositeReversed

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.S6_11312.table_literal_exact
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.S6_11312.publishedToActual_mul
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.S6_11312.publishedToActual_left_inverse
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.S6_11312.publishedToActual_right_inverse
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.S6_11312.left_map_mul
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.S6_11312.right_map_mul
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.S6_11312.left_section
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.S6_11312.right_section
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.S6_11312.ontoLeft
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.S6_11312.ontoRight
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.S6_11312.embed_injective
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.S6_11312.intoProd
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.S6_11312.sameIdentityTheoryOver_actual_factors
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.S6_11312.models_raw
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.S6_11312.representative_basis
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.S6_11312.opposite_basis

end SemigroupBasis.CoRoots.Order6SporadicSection25.S6_11312
