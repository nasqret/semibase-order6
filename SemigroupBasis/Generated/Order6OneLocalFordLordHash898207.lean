import SemigroupBasis.CoRoots.Order6FordLordD378Semantics
import SemigroupBasis.CoRoots.S5_378Family
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Generated.S3_16
import SemigroupBasis.Subdirect

set_option maxRecDepth 100000

/-!
# Nine Ford/Lord `D_378` table certificates

Each representative is exhibited subdirectly in `S3_16` and the
appropriate orientation of `S5_378`. Finite decisions here authenticate the
tables, factor maps, and soundness of the corrected seven-law `D_378` system.
The thin endpoint lemmas are parameterized by the two shared intersection
theorems so this table-side module remains independent of the normalizer's
private implementation.
-/

namespace SemigroupBasis.Generated.Order6OneLocalFordLordHash898207

open SemigroupBasis
open SemigroupBasis.Examples

private def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

namespace S6_7947

/-- Authenticated order-six table, SHA-256 `af04b8113599d3389ed77fec2d7c72e00cc424e3de202cac42195362b7650306`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "af04b8113599d3389ed77fec2d7c72e00cc424e3de202cac42195362b7650306"

def publishedRows : List (List Nat) :=
  [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 2], [0, 0, 2, 3, 0, 0], [4, 4, 4, 4, 4, 4], [0, 1, 0, 0, 4, 5]]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def ontoS3Map (a : Fin 6) : Fin 3 :=
  if a = 0 then (0 : Fin 3) else if a = 1 then (0 : Fin 3) else if a = 2 then (0 : Fin 3) else if a = 3 then (0 : Fin 3) else if a = 4 then (2 : Fin 3) else (1 : Fin 3)

def ontoS3Section (a : Fin 3) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (5 : Fin 6) else (4 : Fin 6)

def ontoS3 : SplitSurjection table.semigroup SemigroupBasis.Generated.S3_16.table.semigroup where
  toFun := ontoS3Map
  map_mul := by decide
  preimage := ontoS3Section
  right_inverse := by
    intro value
    exact by decide +revert

def ontoS5Map (a : Fin 6) : Fin 5 :=
  if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else if a = 3 then (3 : Fin 5) else if a = 4 then (0 : Fin 5) else (4 : Fin 5)

def ontoS5Section (a : Fin 5) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (3 : Fin 6) else (5 : Fin 6)

def ontoS5 : SplitSurjection table.semigroup SemigroupBasis.CoRoots.S5_378.table.semigroup where
  toFun := ontoS5Map
  map_mul := by decide
  preimage := ontoS5Section
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.S3_16.table.semigroup SemigroupBasis.CoRoots.S5_378.table.semigroup where
  left := ontoS3
  right := ontoS5
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6FordLordD378.basis

theorem models_basis : Models table.semigroup basis :=
  FiniteCertificate.checkModels_sound table basis toFinThree (by decide)

theorem representative_basis_of_intersection
    (intersection :
      IntersectionBasis
        SemigroupBasis.Generated.S3_16.table.semigroup
        SemigroupBasis.CoRoots.S5_378.table.semigroup basis) :
    BasisFor table.semigroup basis :=
  intersection.basisFor pair

theorem opposite_basis_of_intersection
    (intersection :
      IntersectionBasis
        SemigroupBasis.Generated.S3_16.table.semigroup
        SemigroupBasis.CoRoots.S5_378.table.semigroup basis) :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  (representative_basis_of_intersection intersection).oppositeReversed

theorem representative_basis : BasisFor table.semigroup basis :=
  representative_basis_of_intersection
    SemigroupBasis.CoRoots.Order6FordLordD378.directIntersectionBasis

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  opposite_basis_of_intersection
    SemigroupBasis.CoRoots.Order6FordLordD378.directIntersectionBasis

end S6_7947

namespace S6_7979

/-- Authenticated order-six table, SHA-256 `31116b336339d4ec6b7fd124c969e874e30389f9f05543bc2a70eb4a830617f4`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "31116b336339d4ec6b7fd124c969e874e30389f9f05543bc2a70eb4a830617f4"

def publishedRows : List (List Nat) :=
  [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 2], [0, 0, 2, 3, 4, 0], [4, 4, 4, 4, 4, 4], [0, 1, 0, 0, 0, 5]]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def ontoS3Map (a : Fin 6) : Fin 3 :=
  if a = 0 then (0 : Fin 3) else if a = 1 then (0 : Fin 3) else if a = 2 then (0 : Fin 3) else if a = 3 then (1 : Fin 3) else if a = 4 then (2 : Fin 3) else (0 : Fin 3)

def ontoS3Section (a : Fin 3) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (3 : Fin 6) else (4 : Fin 6)

def ontoS3 : SplitSurjection table.semigroup SemigroupBasis.Generated.S3_16.table.semigroup where
  toFun := ontoS3Map
  map_mul := by decide
  preimage := ontoS3Section
  right_inverse := by
    intro value
    exact by decide +revert

def ontoS5Map (a : Fin 6) : Fin 5 :=
  if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else if a = 3 then (3 : Fin 5) else if a = 4 then (0 : Fin 5) else (4 : Fin 5)

def ontoS5Section (a : Fin 5) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (3 : Fin 6) else (5 : Fin 6)

def ontoS5 : SplitSurjection table.semigroup SemigroupBasis.CoRoots.S5_378.table.semigroup where
  toFun := ontoS5Map
  map_mul := by decide
  preimage := ontoS5Section
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.S3_16.table.semigroup SemigroupBasis.CoRoots.S5_378.table.semigroup where
  left := ontoS3
  right := ontoS5
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6FordLordD378.basis

theorem models_basis : Models table.semigroup basis :=
  FiniteCertificate.checkModels_sound table basis toFinThree (by decide)

theorem representative_basis_of_intersection
    (intersection :
      IntersectionBasis
        SemigroupBasis.Generated.S3_16.table.semigroup
        SemigroupBasis.CoRoots.S5_378.table.semigroup basis) :
    BasisFor table.semigroup basis :=
  intersection.basisFor pair

theorem opposite_basis_of_intersection
    (intersection :
      IntersectionBasis
        SemigroupBasis.Generated.S3_16.table.semigroup
        SemigroupBasis.CoRoots.S5_378.table.semigroup basis) :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  (representative_basis_of_intersection intersection).oppositeReversed

theorem representative_basis : BasisFor table.semigroup basis :=
  representative_basis_of_intersection
    SemigroupBasis.CoRoots.Order6FordLordD378.directIntersectionBasis

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  opposite_basis_of_intersection
    SemigroupBasis.CoRoots.Order6FordLordD378.directIntersectionBasis

end S6_7979

namespace S6_8133

/-- Authenticated order-six table, SHA-256 `14399eebce64a7b9bb0a2becccdeb736f26c6fad71eb5c77ee4f72f2bde101ca`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (2 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (0 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "14399eebce64a7b9bb0a2becccdeb736f26c6fad71eb5c77ee4f72f2bde101ca"

def publishedRows : List (List Nat) :=
  [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 2, 0], [3, 3, 3, 3, 3, 3], [0, 0, 0, 0, 4, 0], [0, 1, 2, 3, 0, 5]]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def ontoS3Map (a : Fin 6) : Fin 3 :=
  if a = 0 then (0 : Fin 3) else if a = 1 then (0 : Fin 3) else if a = 2 then (0 : Fin 3) else if a = 3 then (2 : Fin 3) else if a = 4 then (0 : Fin 3) else (1 : Fin 3)

def ontoS3Section (a : Fin 3) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (5 : Fin 6) else (3 : Fin 6)

def ontoS3 : SplitSurjection table.semigroup SemigroupBasis.Generated.S3_16.table.semigroup where
  toFun := ontoS3Map
  map_mul := by decide
  preimage := ontoS3Section
  right_inverse := by
    intro value
    exact by decide +revert

def ontoS5Map (a : Fin 6) : Fin 5 :=
  if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else if a = 3 then (0 : Fin 5) else if a = 4 then (3 : Fin 5) else (4 : Fin 5)

def ontoS5Section (a : Fin 5) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (4 : Fin 6) else (5 : Fin 6)

def ontoS5 : SplitSurjection table.semigroup SemigroupBasis.CoRoots.S5_378.table.semigroup.opposite where
  toFun := ontoS5Map
  map_mul := by decide
  preimage := ontoS5Section
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.S3_16.table.semigroup SemigroupBasis.CoRoots.S5_378.table.semigroup.opposite where
  left := ontoS3
  right := ontoS5
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6FordLordD378.basis

theorem models_basis : Models table.semigroup basis :=
  FiniteCertificate.checkModels_sound table basis toFinThree (by decide)

theorem representative_basis_of_intersection
    (intersection :
      IntersectionBasis
        SemigroupBasis.Generated.S3_16.table.semigroup
        SemigroupBasis.CoRoots.S5_378.table.semigroup.opposite basis) :
    BasisFor table.semigroup basis :=
  intersection.basisFor pair

theorem opposite_basis_of_intersection
    (intersection :
      IntersectionBasis
        SemigroupBasis.Generated.S3_16.table.semigroup
        SemigroupBasis.CoRoots.S5_378.table.semigroup.opposite basis) :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  (representative_basis_of_intersection intersection).oppositeReversed

theorem representative_basis : BasisFor table.semigroup basis :=
  representative_basis_of_intersection
    SemigroupBasis.CoRoots.Order6FordLordD378.oppositeIntersectionBasis

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  opposite_basis_of_intersection
    SemigroupBasis.CoRoots.Order6FordLordD378.oppositeIntersectionBasis

end S6_8133

namespace S6_8139

/-- Authenticated order-six table, SHA-256 `3d6a4cfc4a8494798475882e2d22ae73b54883a1c6da17fb5fb2c112ef099941`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (2 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (0 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "3d6a4cfc4a8494798475882e2d22ae73b54883a1c6da17fb5fb2c112ef099941"

def publishedRows : List (List Nat) :=
  [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 2, 0], [3, 3, 3, 3, 3, 3], [0, 0, 0, 3, 4, 0], [0, 1, 2, 0, 0, 5]]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def ontoS3Map (a : Fin 6) : Fin 3 :=
  if a = 0 then (0 : Fin 3) else if a = 1 then (0 : Fin 3) else if a = 2 then (0 : Fin 3) else if a = 3 then (2 : Fin 3) else if a = 4 then (1 : Fin 3) else (0 : Fin 3)

def ontoS3Section (a : Fin 3) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (4 : Fin 6) else (3 : Fin 6)

def ontoS3 : SplitSurjection table.semigroup SemigroupBasis.Generated.S3_16.table.semigroup where
  toFun := ontoS3Map
  map_mul := by decide
  preimage := ontoS3Section
  right_inverse := by
    intro value
    exact by decide +revert

def ontoS5Map (a : Fin 6) : Fin 5 :=
  if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else if a = 3 then (0 : Fin 5) else if a = 4 then (3 : Fin 5) else (4 : Fin 5)

def ontoS5Section (a : Fin 5) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (4 : Fin 6) else (5 : Fin 6)

def ontoS5 : SplitSurjection table.semigroup SemigroupBasis.CoRoots.S5_378.table.semigroup.opposite where
  toFun := ontoS5Map
  map_mul := by decide
  preimage := ontoS5Section
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.S3_16.table.semigroup SemigroupBasis.CoRoots.S5_378.table.semigroup.opposite where
  left := ontoS3
  right := ontoS5
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6FordLordD378.basis

theorem models_basis : Models table.semigroup basis :=
  FiniteCertificate.checkModels_sound table basis toFinThree (by decide)

theorem representative_basis_of_intersection
    (intersection :
      IntersectionBasis
        SemigroupBasis.Generated.S3_16.table.semigroup
        SemigroupBasis.CoRoots.S5_378.table.semigroup.opposite basis) :
    BasisFor table.semigroup basis :=
  intersection.basisFor pair

theorem opposite_basis_of_intersection
    (intersection :
      IntersectionBasis
        SemigroupBasis.Generated.S3_16.table.semigroup
        SemigroupBasis.CoRoots.S5_378.table.semigroup.opposite basis) :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  (representative_basis_of_intersection intersection).oppositeReversed

theorem representative_basis : BasisFor table.semigroup basis :=
  representative_basis_of_intersection
    SemigroupBasis.CoRoots.Order6FordLordD378.oppositeIntersectionBasis

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  opposite_basis_of_intersection
    SemigroupBasis.CoRoots.Order6FordLordD378.oppositeIntersectionBasis

end S6_8139

namespace S6_8158

/-- Authenticated order-six table, SHA-256 `3fd1080cc62ef88f48737c2879a5406e3f9f8a5264b4119235f8745f21606b13`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (2 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (3 : Fin 6) else if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "3fd1080cc62ef88f48737c2879a5406e3f9f8a5264b4119235f8745f21606b13"

def publishedRows : List (List Nat) :=
  [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 2, 0], [3, 3, 3, 3, 3, 3], [0, 1, 2, 3, 4, 3], [3, 3, 3, 3, 3, 5]]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def ontoS3Map (a : Fin 6) : Fin 3 :=
  if a = 0 then (0 : Fin 3) else if a = 1 then (0 : Fin 3) else if a = 2 then (0 : Fin 3) else if a = 3 then (2 : Fin 3) else if a = 4 then (1 : Fin 3) else (2 : Fin 3)

def ontoS3Section (a : Fin 3) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (4 : Fin 6) else (3 : Fin 6)

def ontoS3 : SplitSurjection table.semigroup SemigroupBasis.Generated.S3_16.table.semigroup where
  toFun := ontoS3Map
  map_mul := by decide
  preimage := ontoS3Section
  right_inverse := by
    intro value
    exact by decide +revert

def ontoS5Map (a : Fin 6) : Fin 5 :=
  if a = 0 then (0 : Fin 5) else if a = 1 then (2 : Fin 5) else if a = 2 then (1 : Fin 5) else if a = 3 then (0 : Fin 5) else if a = 4 then (4 : Fin 5) else (3 : Fin 5)

def ontoS5Section (a : Fin 5) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (2 : Fin 6) else if a = 2 then (1 : Fin 6) else if a = 3 then (5 : Fin 6) else (4 : Fin 6)

def ontoS5 : SplitSurjection table.semigroup SemigroupBasis.CoRoots.S5_378.table.semigroup.opposite where
  toFun := ontoS5Map
  map_mul := by decide
  preimage := ontoS5Section
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.S3_16.table.semigroup SemigroupBasis.CoRoots.S5_378.table.semigroup.opposite where
  left := ontoS3
  right := ontoS5
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6FordLordD378.basis

theorem models_basis : Models table.semigroup basis :=
  FiniteCertificate.checkModels_sound table basis toFinThree (by decide)

theorem representative_basis_of_intersection
    (intersection :
      IntersectionBasis
        SemigroupBasis.Generated.S3_16.table.semigroup
        SemigroupBasis.CoRoots.S5_378.table.semigroup.opposite basis) :
    BasisFor table.semigroup basis :=
  intersection.basisFor pair

theorem opposite_basis_of_intersection
    (intersection :
      IntersectionBasis
        SemigroupBasis.Generated.S3_16.table.semigroup
        SemigroupBasis.CoRoots.S5_378.table.semigroup.opposite basis) :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  (representative_basis_of_intersection intersection).oppositeReversed

theorem representative_basis : BasisFor table.semigroup basis :=
  representative_basis_of_intersection
    SemigroupBasis.CoRoots.Order6FordLordD378.oppositeIntersectionBasis

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  opposite_basis_of_intersection
    SemigroupBasis.CoRoots.Order6FordLordD378.oppositeIntersectionBasis

end S6_8158

namespace S6_11016

/-- Authenticated order-six table, SHA-256 `4f757d6c8943b56ff7a85ddf4d82801a53ddb099cf9e38d913dae08fb5e7f958`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (0 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "4f757d6c8943b56ff7a85ddf4d82801a53ddb099cf9e38d913dae08fb5e7f958"

def publishedRows : List (List Nat) :=
  [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1], [2, 2, 2, 2, 2, 2], [2, 2, 2, 2, 2, 3], [0, 0, 2, 3, 4, 0], [0, 1, 0, 0, 0, 5]]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def ontoS3Map (a : Fin 6) : Fin 3 :=
  if a = 0 then (0 : Fin 3) else if a = 1 then (0 : Fin 3) else if a = 2 then (2 : Fin 3) else if a = 3 then (2 : Fin 3) else if a = 4 then (1 : Fin 3) else (0 : Fin 3)

def ontoS3Section (a : Fin 3) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (4 : Fin 6) else (2 : Fin 6)

def ontoS3 : SplitSurjection table.semigroup SemigroupBasis.Generated.S3_16.table.semigroup where
  toFun := ontoS3Map
  map_mul := by decide
  preimage := ontoS3Section
  right_inverse := by
    intro value
    exact by decide +revert

def ontoS5Map (a : Fin 6) : Fin 5 :=
  if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (0 : Fin 5) else if a = 3 then (2 : Fin 5) else if a = 4 then (3 : Fin 5) else (4 : Fin 5)

def ontoS5Section (a : Fin 5) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (3 : Fin 6) else if a = 3 then (4 : Fin 6) else (5 : Fin 6)

def ontoS5 : SplitSurjection table.semigroup SemigroupBasis.CoRoots.S5_378.table.semigroup where
  toFun := ontoS5Map
  map_mul := by decide
  preimage := ontoS5Section
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.S3_16.table.semigroup SemigroupBasis.CoRoots.S5_378.table.semigroup where
  left := ontoS3
  right := ontoS5
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6FordLordD378.basis

theorem models_basis : Models table.semigroup basis :=
  FiniteCertificate.checkModels_sound table basis toFinThree (by decide)

theorem representative_basis_of_intersection
    (intersection :
      IntersectionBasis
        SemigroupBasis.Generated.S3_16.table.semigroup
        SemigroupBasis.CoRoots.S5_378.table.semigroup basis) :
    BasisFor table.semigroup basis :=
  intersection.basisFor pair

theorem opposite_basis_of_intersection
    (intersection :
      IntersectionBasis
        SemigroupBasis.Generated.S3_16.table.semigroup
        SemigroupBasis.CoRoots.S5_378.table.semigroup basis) :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  (representative_basis_of_intersection intersection).oppositeReversed

theorem representative_basis : BasisFor table.semigroup basis :=
  representative_basis_of_intersection
    SemigroupBasis.CoRoots.Order6FordLordD378.directIntersectionBasis

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  opposite_basis_of_intersection
    SemigroupBasis.CoRoots.Order6FordLordD378.directIntersectionBasis

end S6_11016

namespace S6_11023

/-- Authenticated order-six table, SHA-256 `fc803856a9bcce0434d8d1f28854a753a77ce270de9fbc2032b7dd0bd1a18d16`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (0 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "fc803856a9bcce0434d8d1f28854a753a77ce270de9fbc2032b7dd0bd1a18d16"

def publishedRows : List (List Nat) :=
  [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1], [2, 2, 2, 2, 2, 2], [2, 2, 2, 2, 2, 3], [0, 1, 0, 0, 4, 0], [0, 0, 2, 3, 0, 5]]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def ontoS3Map (a : Fin 6) : Fin 3 :=
  if a = 0 then (0 : Fin 3) else if a = 1 then (0 : Fin 3) else if a = 2 then (2 : Fin 3) else if a = 3 then (2 : Fin 3) else if a = 4 then (0 : Fin 3) else (1 : Fin 3)

def ontoS3Section (a : Fin 3) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (5 : Fin 6) else (2 : Fin 6)

def ontoS3 : SplitSurjection table.semigroup SemigroupBasis.Generated.S3_16.table.semigroup where
  toFun := ontoS3Map
  map_mul := by decide
  preimage := ontoS3Section
  right_inverse := by
    intro value
    exact by decide +revert

def ontoS5Map (a : Fin 6) : Fin 5 :=
  if a = 0 then (0 : Fin 5) else if a = 1 then (2 : Fin 5) else if a = 2 then (0 : Fin 5) else if a = 3 then (1 : Fin 5) else if a = 4 then (3 : Fin 5) else (4 : Fin 5)

def ontoS5Section (a : Fin 5) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (3 : Fin 6) else if a = 2 then (1 : Fin 6) else if a = 3 then (4 : Fin 6) else (5 : Fin 6)

def ontoS5 : SplitSurjection table.semigroup SemigroupBasis.CoRoots.S5_378.table.semigroup where
  toFun := ontoS5Map
  map_mul := by decide
  preimage := ontoS5Section
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.S3_16.table.semigroup SemigroupBasis.CoRoots.S5_378.table.semigroup where
  left := ontoS3
  right := ontoS5
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6FordLordD378.basis

theorem models_basis : Models table.semigroup basis :=
  FiniteCertificate.checkModels_sound table basis toFinThree (by decide)

theorem representative_basis_of_intersection
    (intersection :
      IntersectionBasis
        SemigroupBasis.Generated.S3_16.table.semigroup
        SemigroupBasis.CoRoots.S5_378.table.semigroup basis) :
    BasisFor table.semigroup basis :=
  intersection.basisFor pair

theorem opposite_basis_of_intersection
    (intersection :
      IntersectionBasis
        SemigroupBasis.Generated.S3_16.table.semigroup
        SemigroupBasis.CoRoots.S5_378.table.semigroup basis) :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  (representative_basis_of_intersection intersection).oppositeReversed

theorem representative_basis : BasisFor table.semigroup basis :=
  representative_basis_of_intersection
    SemigroupBasis.CoRoots.Order6FordLordD378.directIntersectionBasis

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  opposite_basis_of_intersection
    SemigroupBasis.CoRoots.Order6FordLordD378.directIntersectionBasis

end S6_11023

namespace S6_11066

/-- Authenticated order-six table, SHA-256 `a8548c670eb03e8f19ffd509fa3a8c039ba553e63d91f7bb5c9d10215a1e7c01`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (3 : Fin 6) else (2 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (0 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "a8548c670eb03e8f19ffd509fa3a8c039ba553e63d91f7bb5c9d10215a1e7c01"

def publishedRows : List (List Nat) :=
  [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1], [2, 2, 2, 2, 2, 2], [2, 2, 2, 2, 3, 2], [0, 0, 0, 0, 4, 0], [0, 1, 2, 3, 0, 5]]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def ontoS3Map (a : Fin 6) : Fin 3 :=
  if a = 0 then (0 : Fin 3) else if a = 1 then (0 : Fin 3) else if a = 2 then (2 : Fin 3) else if a = 3 then (2 : Fin 3) else if a = 4 then (0 : Fin 3) else (1 : Fin 3)

def ontoS3Section (a : Fin 3) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (5 : Fin 6) else (2 : Fin 6)

def ontoS3 : SplitSurjection table.semigroup SemigroupBasis.Generated.S3_16.table.semigroup where
  toFun := ontoS3Map
  map_mul := by decide
  preimage := ontoS3Section
  right_inverse := by
    intro value
    exact by decide +revert

def ontoS5Map (a : Fin 6) : Fin 5 :=
  if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (0 : Fin 5) else if a = 3 then (2 : Fin 5) else if a = 4 then (3 : Fin 5) else (4 : Fin 5)

def ontoS5Section (a : Fin 5) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (3 : Fin 6) else if a = 3 then (4 : Fin 6) else (5 : Fin 6)

def ontoS5 : SplitSurjection table.semigroup SemigroupBasis.CoRoots.S5_378.table.semigroup.opposite where
  toFun := ontoS5Map
  map_mul := by decide
  preimage := ontoS5Section
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.S3_16.table.semigroup SemigroupBasis.CoRoots.S5_378.table.semigroup.opposite where
  left := ontoS3
  right := ontoS5
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6FordLordD378.basis

theorem models_basis : Models table.semigroup basis :=
  FiniteCertificate.checkModels_sound table basis toFinThree (by decide)

theorem representative_basis_of_intersection
    (intersection :
      IntersectionBasis
        SemigroupBasis.Generated.S3_16.table.semigroup
        SemigroupBasis.CoRoots.S5_378.table.semigroup.opposite basis) :
    BasisFor table.semigroup basis :=
  intersection.basisFor pair

theorem opposite_basis_of_intersection
    (intersection :
      IntersectionBasis
        SemigroupBasis.Generated.S3_16.table.semigroup
        SemigroupBasis.CoRoots.S5_378.table.semigroup.opposite basis) :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  (representative_basis_of_intersection intersection).oppositeReversed

theorem representative_basis : BasisFor table.semigroup basis :=
  representative_basis_of_intersection
    SemigroupBasis.CoRoots.Order6FordLordD378.oppositeIntersectionBasis

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  opposite_basis_of_intersection
    SemigroupBasis.CoRoots.Order6FordLordD378.oppositeIntersectionBasis

end S6_11066

namespace S6_11085

/-- Authenticated order-six table, SHA-256 `367b5baf4bbfc371a7e3b34f260b3dbdff5cafb4e3585e42ec1c5405e1586513`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (3 : Fin 6) else (2 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (0 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "367b5baf4bbfc371a7e3b34f260b3dbdff5cafb4e3585e42ec1c5405e1586513"

def publishedRows : List (List Nat) :=
  [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1], [2, 2, 2, 2, 2, 2], [2, 2, 2, 2, 3, 2], [0, 1, 2, 3, 4, 0], [0, 0, 0, 0, 0, 5]]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def ontoS3Map (a : Fin 6) : Fin 3 :=
  if a = 0 then (0 : Fin 3) else if a = 1 then (0 : Fin 3) else if a = 2 then (2 : Fin 3) else if a = 3 then (2 : Fin 3) else if a = 4 then (1 : Fin 3) else (0 : Fin 3)

def ontoS3Section (a : Fin 3) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (4 : Fin 6) else (2 : Fin 6)

def ontoS3 : SplitSurjection table.semigroup SemigroupBasis.Generated.S3_16.table.semigroup where
  toFun := ontoS3Map
  map_mul := by decide
  preimage := ontoS3Section
  right_inverse := by
    intro value
    exact by decide +revert

def ontoS5Map (a : Fin 6) : Fin 5 :=
  if a = 0 then (0 : Fin 5) else if a = 1 then (2 : Fin 5) else if a = 2 then (0 : Fin 5) else if a = 3 then (1 : Fin 5) else if a = 4 then (4 : Fin 5) else (3 : Fin 5)

def ontoS5Section (a : Fin 5) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (3 : Fin 6) else if a = 2 then (1 : Fin 6) else if a = 3 then (5 : Fin 6) else (4 : Fin 6)

def ontoS5 : SplitSurjection table.semigroup SemigroupBasis.CoRoots.S5_378.table.semigroup.opposite where
  toFun := ontoS5Map
  map_mul := by decide
  preimage := ontoS5Section
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.S3_16.table.semigroup SemigroupBasis.CoRoots.S5_378.table.semigroup.opposite where
  left := ontoS3
  right := ontoS5
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6FordLordD378.basis

theorem models_basis : Models table.semigroup basis :=
  FiniteCertificate.checkModels_sound table basis toFinThree (by decide)

theorem representative_basis_of_intersection
    (intersection :
      IntersectionBasis
        SemigroupBasis.Generated.S3_16.table.semigroup
        SemigroupBasis.CoRoots.S5_378.table.semigroup.opposite basis) :
    BasisFor table.semigroup basis :=
  intersection.basisFor pair

theorem opposite_basis_of_intersection
    (intersection :
      IntersectionBasis
        SemigroupBasis.Generated.S3_16.table.semigroup
        SemigroupBasis.CoRoots.S5_378.table.semigroup.opposite basis) :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  (representative_basis_of_intersection intersection).oppositeReversed

theorem representative_basis : BasisFor table.semigroup basis :=
  representative_basis_of_intersection
    SemigroupBasis.CoRoots.Order6FordLordD378.oppositeIntersectionBasis

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  opposite_basis_of_intersection
    SemigroupBasis.CoRoots.Order6FordLordD378.oppositeIntersectionBasis

end S6_11085

end SemigroupBasis.Generated.Order6OneLocalFordLordHash898207

#print axioms SemigroupBasis.Generated.Order6OneLocalFordLordHash898207.S6_7947.representative_basis
#print axioms SemigroupBasis.Generated.Order6OneLocalFordLordHash898207.S6_7947.opposite_basis
#print axioms SemigroupBasis.Generated.Order6OneLocalFordLordHash898207.S6_7979.representative_basis
#print axioms SemigroupBasis.Generated.Order6OneLocalFordLordHash898207.S6_7979.opposite_basis
#print axioms SemigroupBasis.Generated.Order6OneLocalFordLordHash898207.S6_8133.representative_basis
#print axioms SemigroupBasis.Generated.Order6OneLocalFordLordHash898207.S6_8133.opposite_basis
#print axioms SemigroupBasis.Generated.Order6OneLocalFordLordHash898207.S6_8139.representative_basis
#print axioms SemigroupBasis.Generated.Order6OneLocalFordLordHash898207.S6_8139.opposite_basis
#print axioms SemigroupBasis.Generated.Order6OneLocalFordLordHash898207.S6_8158.representative_basis
#print axioms SemigroupBasis.Generated.Order6OneLocalFordLordHash898207.S6_8158.opposite_basis
#print axioms SemigroupBasis.Generated.Order6OneLocalFordLordHash898207.S6_11016.representative_basis
#print axioms SemigroupBasis.Generated.Order6OneLocalFordLordHash898207.S6_11016.opposite_basis
#print axioms SemigroupBasis.Generated.Order6OneLocalFordLordHash898207.S6_11023.representative_basis
#print axioms SemigroupBasis.Generated.Order6OneLocalFordLordHash898207.S6_11023.opposite_basis
#print axioms SemigroupBasis.Generated.Order6OneLocalFordLordHash898207.S6_11066.representative_basis
#print axioms SemigroupBasis.Generated.Order6OneLocalFordLordHash898207.S6_11066.opposite_basis
#print axioms SemigroupBasis.Generated.Order6OneLocalFordLordHash898207.S6_11085.representative_basis
#print axioms SemigroupBasis.Generated.Order6OneLocalFordLordHash898207.S6_11085.opposite_basis
