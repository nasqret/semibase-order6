import SemigroupBasis.CoRoots.Order6Day10.Rank084SigmaPlus.Rank084SigmaPlusIntersection

/-! Exact S6_5686 B7 endpoints. The frozen raw6 contract is not altered.
Both actual factor Models were proved before the owner converse; actual
target Models is independently checked before either class endpoint. -/

namespace SemigroupBasis.CoRoots.Order6Day10.Rank084SigmaPlus.Rank084SigmaPlusClassEndpoints

open SemigroupBasis
open SemigroupBasis.CoRoots.Order6Day10.Rank084SigmaPlus.Rank084SigmaPlusIntersection

namespace S6_5686

/-- One-based catalogue table SHA256: 4a5db53bcef2313c21b51aaf3e9e69f2d39682bef7303578d6bca80f40dc9e60. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6)) else if a = 1 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6)) else if a = 2 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6)) else if a = 3 then (if b = 0 then (0 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (4 : Fin 6)) else if a = 4 then (if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6)) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def catalogueRows : List (List Nat) :=
  [[1, 1, 1, 1, 1, 1], [1, 1, 1, 3, 1, 1], [1, 1, 1, 1, 1, 1], [1, 3, 1, 2, 1, 5], [5, 5, 5, 5, 5, 5], [6, 6, 6, 6, 6, 6]]

theorem catalogueRows_exact :
    List.ofFn (fun a : Fin 6 => List.ofFn (fun b : Fin 6 => (mul a b).val + 1)) = catalogueRows := by decide

private def toFinFour : Nat → Fin 4
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem models : Models table.semigroup basis :=
  FiniteCertificate.checkModels_sound table basis toFinFour (by decide)

def ontoLeftMap (a : Fin 6) : Fin 4 :=
  if a = 0 then (0 : Fin 4) else if a = 1 then (1 : Fin 4) else if a = 2 then (2 : Fin 4) else if a = 3 then (3 : Fin 4) else if a = 4 then (0 : Fin 4) else (0 : Fin 4)

def ontoLeftSection (a : Fin 4) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else (3 : Fin 6)

def ontoLeft : SplitSurjection table.semigroup leftTable.semigroup where
  toFun := ontoLeftMap
  map_mul := by decide
  preimage := ontoLeftSection
  right_inverse := by
    intro value
    exact by decide +revert

def ontoRightMap (a : Fin 6) : Fin 4 :=
  if a = 0 then (0 : Fin 4) else if a = 1 then (0 : Fin 4) else if a = 2 then (0 : Fin 4) else if a = 3 then (1 : Fin 4) else if a = 4 then (2 : Fin 4) else (3 : Fin 4)

def ontoRightSection (a : Fin 4) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (3 : Fin 6) else if a = 2 then (4 : Fin 6) else (5 : Fin 6)

def ontoRight : SplitSurjection table.semigroup rightTable.semigroup where
  toFun := ontoRightMap
  map_mul := by decide
  preimage := ontoRightSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : FinitePair table where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := by
    intro a b
    exact by decide +revert

def ontoLeftOpposite : SplitSurjection table.semigroup.opposite leftTable.semigroup.opposite where
  toFun := ontoLeftMap
  map_mul := fun a b => ontoLeft.map_mul b a
  preimage := ontoLeftSection
  right_inverse := ontoLeft.right_inverse

def ontoRightOpposite : SplitSurjection table.semigroup.opposite rightTable.semigroup.opposite where
  toFun := ontoRightMap
  map_mul := fun a b => ontoRight.map_mul b a
  preimage := ontoRightSection
  right_inverse := ontoRight.right_inverse

def pairOpposite : SubdirectPair table.semigroup.opposite leftTable.semigroup.opposite rightTable.semigroup.opposite where
  left := ontoLeftOpposite
  right := ontoRightOpposite
  jointlyInjective := pair.jointlyInjective

theorem basisFor : BasisFor table.semigroup basis := by
  refine ⟨models, ?_⟩
  intro identity valid
  have factors := (pair.satisfiedBy_iff identity).mp valid
  exact valid_in_both_derives identity factors.1 factors.2

theorem basisForOpposite : BasisFor table.semigroup.opposite (reversedBasis basis) :=
  intersectionBasis.oppositeReversed.basisFor pairOpposite

theorem modelsOpposite : Models table.semigroup.opposite (reversedBasis basis) := basisForOpposite.1

end S6_5686

end SemigroupBasis.CoRoots.Order6Day10.Rank084SigmaPlus.Rank084SigmaPlusClassEndpoints
