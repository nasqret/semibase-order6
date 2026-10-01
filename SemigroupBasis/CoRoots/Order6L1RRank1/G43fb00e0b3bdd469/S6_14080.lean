import SemigroupBasis.CoRoots.Order6L1RRank1.G43fb00e0b3bdd469.Variants
import SemigroupBasis.Generated.S3_16
import SemigroupBasis.Generated.S4_64
import SemigroupBasis.FiniteReflection

/-!
# Exact direct L1R endpoint `S6_14080` via `S3_16op x S4_64`

Generated mechanically from the pinned rank-1 input manifest, the order-six
catalogue SHA-256 `944f356c42b8e703988f5684cd81b650f99cc0ccd1ef1d7fc6e900f2c95f287c`, and msg-0118
subdirect408 SHA-256 `e3ad378307410423b9c32e1b31562e8b7deafef737ea8801573a3aa9a8a05d0e`.  This is
computed-replayable-not-acceptance source material, not acceptance evidence.  Do not edit by hand.
-/

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6L1RRank1.G43fb00e0b3bdd469

open SemigroupBasis

namespace S6_14080

/-! Authenticated zero-based order-six table. Compact-row SHA-256:
`750a632c867f0db146e6512f6bcf8660b98878aa73bdcde82228d5065800aa84`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then
    if b = 0 then (0 : Fin 6)
    else if b = 1 then (0 : Fin 6)
    else if b = 2 then (0 : Fin 6)
    else if b = 3 then (0 : Fin 6)
    else if b = 4 then (4 : Fin 6)
    else (4 : Fin 6)
  else if a = 1 then
    if b = 0 then (0 : Fin 6)
    else if b = 1 then (0 : Fin 6)
    else if b = 2 then (0 : Fin 6)
    else if b = 3 then (0 : Fin 6)
    else if b = 4 then (4 : Fin 6)
    else (4 : Fin 6)
  else if a = 2 then
    if b = 0 then (0 : Fin 6)
    else if b = 1 then (1 : Fin 6)
    else if b = 2 then (2 : Fin 6)
    else if b = 3 then (3 : Fin 6)
    else if b = 4 then (4 : Fin 6)
    else (5 : Fin 6)
  else if a = 3 then
    if b = 0 then (3 : Fin 6)
    else if b = 1 then (3 : Fin 6)
    else if b = 2 then (3 : Fin 6)
    else if b = 3 then (3 : Fin 6)
    else if b = 4 then (5 : Fin 6)
    else (5 : Fin 6)
  else if a = 4 then
    if b = 0 then (0 : Fin 6)
    else if b = 1 then (0 : Fin 6)
    else if b = 2 then (4 : Fin 6)
    else if b = 3 then (0 : Fin 6)
    else if b = 4 then (4 : Fin 6)
    else (4 : Fin 6)
  else
    if b = 0 then (3 : Fin 6)
    else if b = 1 then (3 : Fin 6)
    else if b = 2 then (5 : Fin 6)
    else if b = 3 then (3 : Fin 6)
    else if b = 4 then (5 : Fin 6)
    else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "750a632c867f0db146e6512f6bcf8660b98878aa73bdcde82228d5065800aa84"

def publishedRows : List (List Nat) :=
  [[0, 0, 0, 0, 4, 4], [0, 0, 0, 0, 4, 4], [0, 1, 2, 3, 4, 5], [3, 3, 3, 3, 5, 5], [0, 0, 4, 0, 4, 4], [3, 3, 5, 3, 5, 5]]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def ontoLeftMap (a : Fin 6) : Fin 3 :=
  if a = 0 then (0 : Fin 3)
  else if a = 1 then (0 : Fin 3)
  else if a = 2 then (1 : Fin 3)
  else if a = 3 then (0 : Fin 3)
  else if a = 4 then (2 : Fin 3)
  else (2 : Fin 3)

def ontoLeftSection (a : Fin 3) : Fin 6 :=
  if a = 0 then (0 : Fin 6)
  else if a = 1 then (2 : Fin 6)
  else (4 : Fin 6)

def ontoLeft :
    SplitSurjection table.semigroup
      SemigroupBasis.CoRoots.Order6L1RRank1.G43fb00e0b3bdd469.s3_16op.semigroup where
  toFun := ontoLeftMap
  map_mul := by decide
  preimage := ontoLeftSection
  right_inverse := by
    intro value
    exact by decide +revert

def ontoRightMap (a : Fin 6) : Fin 4 :=
  if a = 0 then (0 : Fin 4)
  else if a = 1 then (1 : Fin 4)
  else if a = 2 then (2 : Fin 4)
  else if a = 3 then (3 : Fin 4)
  else if a = 4 then (0 : Fin 4)
  else (3 : Fin 4)

def ontoRightSection (a : Fin 4) : Fin 6 :=
  if a = 0 then (0 : Fin 6)
  else if a = 1 then (1 : Fin 6)
  else if a = 2 then (2 : Fin 6)
  else (3 : Fin 6)

def ontoRight :
    SplitSurjection table.semigroup
      SemigroupBasis.CoRoots.Order6L1RRank1.FactorTables.s4_64.semigroup where
  toFun := ontoRightMap
  map_mul := by decide
  preimage := ontoRightSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair :
    SubdirectPair table.semigroup
      SemigroupBasis.CoRoots.Order6L1RRank1.G43fb00e0b3bdd469.s3_16op.semigroup
      SemigroupBasis.CoRoots.Order6L1RRank1.FactorTables.s4_64.semigroup where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev endpointBasis : List (Identity Nat) :=
  SemigroupBasis.CoRoots.Order6L1RRank1.G43fb00e0b3bdd469.basis

theorem representative_basis :
    BasisFor table.semigroup endpointBasis :=
  SemigroupBasis.CoRoots.Order6L1RRank1.G43fb00e0b3bdd469.intersectionBasisS3_16opS4_64.basisFor pair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis endpointBasis) :=
  representative_basis.oppositeReversed

end S6_14080

end SemigroupBasis.CoRoots.Order6L1RRank1.G43fb00e0b3bdd469
