import SemigroupBasis.CoRoots.Order6Hash8aSiblingFixedHead

set_option maxRecDepth 100000

/-!
# S3_8-factor endpoints for the hash8a sibling family

The right factors already expose the separator and first-letter quotients
needed by the shared fixed-head normalizer.  No new detector embedding or
bounded invariant is used in these endpoint proofs.
-/

namespace SemigroupBasis.Generated.Order6Hash8aSiblingFactorTargets

open SemigroupBasis

namespace S6_8131

def mul (left right : Fin 6) : Fin 6 :=
  match left.val, right.val with
  | 1, 5 => 1
  | 2, 4 => 2
  | 3, _ => 3
  | 4, 4 => 4
  | 5, 1 => 1
  | 5, 2 => 2
  | 5, 5 => 5
  | _, _ => 0

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "7cd700805f83f6707d4e8c4e820d72d7ebee672722e304ac4e53a605a304fede"

def publishedRows : List (List Nat) :=
  [[0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 1],
   [0, 0, 0, 0, 2, 0],
   [3, 3, 3, 3, 3, 3],
   [0, 0, 0, 0, 4, 0],
   [0, 1, 2, 0, 0, 5]]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def ontoLeftMap (value : Fin 6) : Fin 3 :=
  if value = 1 then 1
  else if value = 5 then 2
  else 0

def ontoLeftSection (value : Fin 3) : Fin 6 :=
  if value = 0 then 0
  else if value = 1 then 1
  else 5

def ontoLeft : SplitSurjection table.semigroup
    SemigroupBasis.Generated.S3_8.table.semigroup where
  toFun := ontoLeftMap
  map_mul := by decide
  preimage := ontoLeftSection
  right_inverse := by
    intro value
    exact by decide +revert

def ontoRightMap (value : Fin 6) : Fin 5 :=
  if value = 0 then 0
  else if value = 1 then 0
  else if value = 2 then 1
  else if value = 3 then 3
  else if value = 4 then 4
  else 2

def ontoRightSection (value : Fin 5) : Fin 6 :=
  if value = 0 then 0
  else if value = 1 then 2
  else if value = 2 then 5
  else if value = 3 then 3
  else 4

def ontoRight : SplitSurjection table.semigroup
    SemigroupBasis.Generated.Catalogue.S5_787.table.semigroup where
  toFun := ontoRightMap
  map_mul := by decide
  preimage := ontoRightSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup
    SemigroupBasis.Generated.S3_8.table.semigroup
    SemigroupBasis.Generated.Catalogue.S5_787.table.semigroup where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) :=
  SemigroupBasis.CoRoots.Order6Hash8aSiblingFixedHead.basis

theorem representative_basis : BasisFor table.semigroup basis :=
  SemigroupBasis.CoRoots.Order6Hash8aSiblingFixedHead.intersectionBasisS3_8S5_787.basisFor
    pair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_8131

namespace S6_8156

def mul (left right : Fin 6) : Fin 6 :=
  match left.val, right.val with
  | 1, 5 => 1
  | 2, 4 => 2
  | 3, _ => 3
  | 4, 1 => 1
  | 4, 2 => 2
  | 4, 4 => 4
  | 5, 5 => 5
  | 5, _ => 3
  | _, _ => 0

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "a1a95cde0edf36a51393088b194ea221974e33e7f84bdb78b2bebfb7ef5ba937"

def publishedRows : List (List Nat) :=
  [[0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 1],
   [0, 0, 0, 0, 2, 0],
   [3, 3, 3, 3, 3, 3],
   [0, 1, 2, 0, 4, 0],
   [3, 3, 3, 3, 3, 5]]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def ontoLeftMap (value : Fin 6) : Fin 3 :=
  if value = 2 then 1
  else if value = 4 then 2
  else 0

def ontoLeftSection (value : Fin 3) : Fin 6 :=
  if value = 0 then 0
  else if value = 1 then 2
  else 4

def ontoLeft : SplitSurjection table.semigroup
    SemigroupBasis.Generated.S3_8.table.semigroup where
  toFun := ontoLeftMap
  map_mul := by decide
  preimage := ontoLeftSection
  right_inverse := by
    intro value
    exact by decide +revert

def ontoRightMap (value : Fin 6) : Fin 5 :=
  if value = 0 then 0
  else if value = 1 then 1
  else if value = 2 then 0
  else if value = 3 then 3
  else if value = 4 then 2
  else 4

def ontoRightSection (value : Fin 5) : Fin 6 :=
  if value = 0 then 0
  else if value = 1 then 1
  else if value = 2 then 4
  else if value = 3 then 3
  else 5

def ontoRight : SplitSurjection table.semigroup
    SemigroupBasis.Generated.Catalogue.S5_789.table.semigroup where
  toFun := ontoRightMap
  map_mul := by decide
  preimage := ontoRightSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup
    SemigroupBasis.Generated.S3_8.table.semigroup
    SemigroupBasis.Generated.Catalogue.S5_789.table.semigroup where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) :=
  SemigroupBasis.CoRoots.Order6Hash8aSiblingFixedHead.basis

theorem representative_basis : BasisFor table.semigroup basis :=
  SemigroupBasis.CoRoots.Order6Hash8aSiblingFixedHead.intersectionBasisS3_8S5_789.basisFor
    pair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_8156

namespace S6_8249

def mul (left right : Fin 6) : Fin 6 :=
  match left.val, right.val with
  | 1, 5 => 1
  | 2, 3 => 2
  | 2, 4 => 2
  | 3, 1 => 1
  | 3, 2 => 2
  | 3, 3 => 3
  | 3, 4 => 3
  | 4, 1 => 1
  | 4, 2 => 2
  | 4, 3 => 4
  | 4, 4 => 4
  | 5, 5 => 5
  | _, _ => 0

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "e41fd63657a9fa6e7197de7b8f5e2a268b8274a5e289ecc6bbb8e20086cb2db1"

def publishedRows : List (List Nat) :=
  [[0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 1],
   [0, 0, 0, 2, 2, 0],
   [0, 1, 2, 3, 3, 0],
   [0, 1, 2, 4, 4, 0],
   [0, 0, 0, 0, 0, 5]]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def ontoLeftMap (value : Fin 6) : Fin 3 :=
  if value = 2 then 1
  else if value = 3 then 2
  else if value = 4 then 2
  else 0

def ontoLeftSection (value : Fin 3) : Fin 6 :=
  if value = 0 then 0
  else if value = 1 then 2
  else 3

def ontoLeft : SplitSurjection table.semigroup
    SemigroupBasis.Generated.S3_8.table.semigroup where
  toFun := ontoLeftMap
  map_mul := by decide
  preimage := ontoLeftSection
  right_inverse := by
    intro value
    exact by decide +revert

def ontoRightMap (value : Fin 6) : Fin 5 :=
  if value = 0 then 0
  else if value = 1 then 1
  else if value = 2 then 0
  else if value = 3 then 2
  else if value = 4 then 3
  else 4

def ontoRightSection (value : Fin 5) : Fin 6 :=
  if value = 0 then 0
  else if value = 1 then 1
  else if value = 2 then 3
  else if value = 3 then 4
  else 5

def ontoRight : SplitSurjection table.semigroup
    SemigroupBasis.Generated.Catalogue.S5_796.table.semigroup where
  toFun := ontoRightMap
  map_mul := by decide
  preimage := ontoRightSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup
    SemigroupBasis.Generated.S3_8.table.semigroup
    SemigroupBasis.Generated.Catalogue.S5_796.table.semigroup where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) :=
  SemigroupBasis.CoRoots.Order6Hash8aSiblingFixedHead.basis

theorem representative_basis : BasisFor table.semigroup basis :=
  SemigroupBasis.CoRoots.Order6Hash8aSiblingFixedHead.intersectionBasisS3_8S5_796.basisFor
    pair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_8249

end SemigroupBasis.Generated.Order6Hash8aSiblingFactorTargets
