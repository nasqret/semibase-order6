import SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank105
import SemigroupBasis.CoRoots.S5_379Family
import SemigroupBasis.Order6Subdirect.Common

/-!
# Source-pinned rank105 finite subdirect fanout

The six target tables are transcribed in zero-based catalogue coordinates
from the frozen new map search, SHA-256
`7ef03842b8397ebbf00ed8e94696fdf93eaa30d462b163aeb465f2459d706f1c`.
All maps and sections below are checked by Lean's ordinary kernel reduction.
Three representatives use the direct right factor and three its opposite.
The right theory implication is proved from the existing complete opposite
basis and a new finite soundness check; it is not assumed from table labels.
These finite maps alone make no completeness claim.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank105.FiniteFanout

open SemigroupBasis
open SemigroupBasis.CoRoots

def rightOppositeTable : FiniteTable := Order6Subdirect.oppositeTable rightTable

private def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

theorem rightOppositeModels : Models rightOppositeTable.semigroup basis :=
  FiniteCertificate.checkModels_sound rightOppositeTable basis toFinThree (by decide)

/-- The actual direct table satisfies the complete opposite six-law basis. -/
theorem rightModelsReversedFactorBasis :
    Models rightTable.semigroup S5_379.oppositeBasis :=
  FiniteCertificate.checkModels_sound rightTable S5_379.oppositeBasis toFinThree (by decide)

/-- Unrestricted implication, obtained by soundness of an actual derivation
from the independently established complete opposite-factor basis. -/
theorem rightTheoryFromOpposite (identity : Identity Nat)
    (valid : identity.SatisfiedBy rightOppositeTable.semigroup) :
    identity.SatisfiedBy rightTable.semigroup := by
  have derivation := S5_379Family.S5_379.oppositeBasisFor.2 identity valid
  intro valuation
  exact derivation.sound rightModelsReversedFactorBasis valuation

namespace S6_7954

/-- Exact one-based compact catalogue-table SHA-256: 9181d060a594a6579b5493fc5b1b6b07eb8718afda08a0a87e313e88b7abbd84. -/
def sourceTableSHA256 : String := "9181d060a594a6579b5493fc5b1b6b07eb8718afda08a0a87e313e88b7abbd84"

def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then
    if right = 0 then (0 : Fin 6)
    else if right = 1 then (0 : Fin 6)
    else if right = 2 then (0 : Fin 6)
    else if right = 3 then (0 : Fin 6)
    else if right = 4 then (0 : Fin 6)
    else (0 : Fin 6)
  else if left = 1 then
    if right = 0 then (0 : Fin 6)
    else if right = 1 then (0 : Fin 6)
    else if right = 2 then (0 : Fin 6)
    else if right = 3 then (0 : Fin 6)
    else if right = 4 then (0 : Fin 6)
    else (1 : Fin 6)
  else if left = 2 then
    if right = 0 then (0 : Fin 6)
    else if right = 1 then (0 : Fin 6)
    else if right = 2 then (0 : Fin 6)
    else if right = 3 then (0 : Fin 6)
    else if right = 4 then (0 : Fin 6)
    else (2 : Fin 6)
  else if left = 3 then
    if right = 0 then (0 : Fin 6)
    else if right = 1 then (0 : Fin 6)
    else if right = 2 then (2 : Fin 6)
    else if right = 3 then (3 : Fin 6)
    else if right = 4 then (0 : Fin 6)
    else (2 : Fin 6)
  else if left = 4 then
    if right = 0 then (4 : Fin 6)
    else if right = 1 then (4 : Fin 6)
    else if right = 2 then (4 : Fin 6)
    else if right = 3 then (4 : Fin 6)
    else if right = 4 then (4 : Fin 6)
    else (4 : Fin 6)
  else
    if right = 0 then (0 : Fin 6)
    else if right = 1 then (1 : Fin 6)
    else if right = 2 then (0 : Fin 6)
    else if right = 3 then (0 : Fin 6)
    else if right = 4 then (4 : Fin 6)
    else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

abbrev factorTable : FiniteTable := rightTable

def ontoLeftMap (value : Fin 6) : Fin 3 :=
  if value = 0 then (0 : Fin 3)
  else if value = 1 then (0 : Fin 3)
  else if value = 2 then (0 : Fin 3)
  else if value = 3 then (0 : Fin 3)
  else if value = 4 then (2 : Fin 3)
  else (1 : Fin 3)

def ontoLeftSection (value : Fin 3) : Fin 6 :=
  if value = 0 then (0 : Fin 6)
  else if value = 1 then (5 : Fin 6)
  else (4 : Fin 6)

def ontoLeft : SplitSurjection table.semigroup leftTable.semigroup where
  toFun := ontoLeftMap
  map_mul := by decide
  preimage := ontoLeftSection
  right_inverse := by
    intro value
    exact by decide +revert

def ontoRightMap (value : Fin 6) : Fin 5 :=
  if value = 0 then (0 : Fin 5)
  else if value = 1 then (1 : Fin 5)
  else if value = 2 then (2 : Fin 5)
  else if value = 3 then (3 : Fin 5)
  else if value = 4 then (0 : Fin 5)
  else (4 : Fin 5)

def ontoRightSection (value : Fin 5) : Fin 6 :=
  if value = 0 then (0 : Fin 6)
  else if value = 1 then (1 : Fin 6)
  else if value = 2 then (2 : Fin 6)
  else if value = 3 then (3 : Fin 6)
  else (5 : Fin 6)

def ontoRight : SplitSurjection table.semigroup factorTable.semigroup where
  toFun := ontoRightMap
  map_mul := by decide
  preimage := ontoRightSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup leftTable.semigroup factorTable.semigroup where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := by
    intro left right
    exact by decide +revert

end S6_7954

namespace S6_7984

/-- Exact one-based compact catalogue-table SHA-256: 6a5e81a3c29579588875e72ea949878523ad9eefbf64cef39e1d68d8ab3fb273. -/
def sourceTableSHA256 : String := "6a5e81a3c29579588875e72ea949878523ad9eefbf64cef39e1d68d8ab3fb273"

def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then
    if right = 0 then (0 : Fin 6)
    else if right = 1 then (0 : Fin 6)
    else if right = 2 then (0 : Fin 6)
    else if right = 3 then (0 : Fin 6)
    else if right = 4 then (0 : Fin 6)
    else (0 : Fin 6)
  else if left = 1 then
    if right = 0 then (0 : Fin 6)
    else if right = 1 then (0 : Fin 6)
    else if right = 2 then (0 : Fin 6)
    else if right = 3 then (0 : Fin 6)
    else if right = 4 then (0 : Fin 6)
    else (1 : Fin 6)
  else if left = 2 then
    if right = 0 then (0 : Fin 6)
    else if right = 1 then (0 : Fin 6)
    else if right = 2 then (0 : Fin 6)
    else if right = 3 then (0 : Fin 6)
    else if right = 4 then (0 : Fin 6)
    else (2 : Fin 6)
  else if left = 3 then
    if right = 0 then (0 : Fin 6)
    else if right = 1 then (0 : Fin 6)
    else if right = 2 then (2 : Fin 6)
    else if right = 3 then (3 : Fin 6)
    else if right = 4 then (4 : Fin 6)
    else (2 : Fin 6)
  else if left = 4 then
    if right = 0 then (4 : Fin 6)
    else if right = 1 then (4 : Fin 6)
    else if right = 2 then (4 : Fin 6)
    else if right = 3 then (4 : Fin 6)
    else if right = 4 then (4 : Fin 6)
    else (4 : Fin 6)
  else
    if right = 0 then (0 : Fin 6)
    else if right = 1 then (1 : Fin 6)
    else if right = 2 then (0 : Fin 6)
    else if right = 3 then (0 : Fin 6)
    else if right = 4 then (0 : Fin 6)
    else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

abbrev factorTable : FiniteTable := rightTable

def ontoLeftMap (value : Fin 6) : Fin 3 :=
  if value = 0 then (0 : Fin 3)
  else if value = 1 then (0 : Fin 3)
  else if value = 2 then (0 : Fin 3)
  else if value = 3 then (1 : Fin 3)
  else if value = 4 then (2 : Fin 3)
  else (0 : Fin 3)

def ontoLeftSection (value : Fin 3) : Fin 6 :=
  if value = 0 then (0 : Fin 6)
  else if value = 1 then (3 : Fin 6)
  else (4 : Fin 6)

def ontoLeft : SplitSurjection table.semigroup leftTable.semigroup where
  toFun := ontoLeftMap
  map_mul := by decide
  preimage := ontoLeftSection
  right_inverse := by
    intro value
    exact by decide +revert

def ontoRightMap (value : Fin 6) : Fin 5 :=
  if value = 0 then (0 : Fin 5)
  else if value = 1 then (1 : Fin 5)
  else if value = 2 then (2 : Fin 5)
  else if value = 3 then (3 : Fin 5)
  else if value = 4 then (0 : Fin 5)
  else (4 : Fin 5)

def ontoRightSection (value : Fin 5) : Fin 6 :=
  if value = 0 then (0 : Fin 6)
  else if value = 1 then (1 : Fin 6)
  else if value = 2 then (2 : Fin 6)
  else if value = 3 then (3 : Fin 6)
  else (5 : Fin 6)

def ontoRight : SplitSurjection table.semigroup factorTable.semigroup where
  toFun := ontoRightMap
  map_mul := by decide
  preimage := ontoRightSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup leftTable.semigroup factorTable.semigroup where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := by
    intro left right
    exact by decide +revert

end S6_7984

namespace S6_8134

/-- Exact one-based compact catalogue-table SHA-256: aaf40f81b4c93d81736dcf0977d69365b6242ac319540fa27b36a4ff8d38f82d. -/
def sourceTableSHA256 : String := "aaf40f81b4c93d81736dcf0977d69365b6242ac319540fa27b36a4ff8d38f82d"

def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then
    if right = 0 then (0 : Fin 6)
    else if right = 1 then (0 : Fin 6)
    else if right = 2 then (0 : Fin 6)
    else if right = 3 then (0 : Fin 6)
    else if right = 4 then (0 : Fin 6)
    else (0 : Fin 6)
  else if left = 1 then
    if right = 0 then (0 : Fin 6)
    else if right = 1 then (0 : Fin 6)
    else if right = 2 then (0 : Fin 6)
    else if right = 3 then (0 : Fin 6)
    else if right = 4 then (0 : Fin 6)
    else (1 : Fin 6)
  else if left = 2 then
    if right = 0 then (0 : Fin 6)
    else if right = 1 then (0 : Fin 6)
    else if right = 2 then (0 : Fin 6)
    else if right = 3 then (0 : Fin 6)
    else if right = 4 then (2 : Fin 6)
    else (0 : Fin 6)
  else if left = 3 then
    if right = 0 then (3 : Fin 6)
    else if right = 1 then (3 : Fin 6)
    else if right = 2 then (3 : Fin 6)
    else if right = 3 then (3 : Fin 6)
    else if right = 4 then (3 : Fin 6)
    else (3 : Fin 6)
  else if left = 4 then
    if right = 0 then (0 : Fin 6)
    else if right = 1 then (0 : Fin 6)
    else if right = 2 then (0 : Fin 6)
    else if right = 3 then (0 : Fin 6)
    else if right = 4 then (4 : Fin 6)
    else (0 : Fin 6)
  else
    if right = 0 then (0 : Fin 6)
    else if right = 1 then (1 : Fin 6)
    else if right = 2 then (2 : Fin 6)
    else if right = 3 then (3 : Fin 6)
    else if right = 4 then (2 : Fin 6)
    else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

abbrev factorTable : FiniteTable := rightOppositeTable

def ontoLeftMap (value : Fin 6) : Fin 3 :=
  if value = 0 then (0 : Fin 3)
  else if value = 1 then (0 : Fin 3)
  else if value = 2 then (0 : Fin 3)
  else if value = 3 then (2 : Fin 3)
  else if value = 4 then (0 : Fin 3)
  else (1 : Fin 3)

def ontoLeftSection (value : Fin 3) : Fin 6 :=
  if value = 0 then (0 : Fin 6)
  else if value = 1 then (5 : Fin 6)
  else (3 : Fin 6)

def ontoLeft : SplitSurjection table.semigroup leftTable.semigroup where
  toFun := ontoLeftMap
  map_mul := by decide
  preimage := ontoLeftSection
  right_inverse := by
    intro value
    exact by decide +revert

def ontoRightMap (value : Fin 6) : Fin 5 :=
  if value = 0 then (0 : Fin 5)
  else if value = 1 then (1 : Fin 5)
  else if value = 2 then (2 : Fin 5)
  else if value = 3 then (0 : Fin 5)
  else if value = 4 then (3 : Fin 5)
  else (4 : Fin 5)

def ontoRightSection (value : Fin 5) : Fin 6 :=
  if value = 0 then (0 : Fin 6)
  else if value = 1 then (1 : Fin 6)
  else if value = 2 then (2 : Fin 6)
  else if value = 3 then (4 : Fin 6)
  else (5 : Fin 6)

def ontoRight : SplitSurjection table.semigroup factorTable.semigroup where
  toFun := ontoRightMap
  map_mul := by decide
  preimage := ontoRightSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup leftTable.semigroup factorTable.semigroup where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := by
    intro left right
    exact by decide +revert

end S6_8134

namespace S6_8140

/-- Exact one-based compact catalogue-table SHA-256: 53aa95ccdcd05a7578676f907a5b5d32edd896f1b9f0ea3707df2f7e674232dc. -/
def sourceTableSHA256 : String := "53aa95ccdcd05a7578676f907a5b5d32edd896f1b9f0ea3707df2f7e674232dc"

def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then
    if right = 0 then (0 : Fin 6)
    else if right = 1 then (0 : Fin 6)
    else if right = 2 then (0 : Fin 6)
    else if right = 3 then (0 : Fin 6)
    else if right = 4 then (0 : Fin 6)
    else (0 : Fin 6)
  else if left = 1 then
    if right = 0 then (0 : Fin 6)
    else if right = 1 then (0 : Fin 6)
    else if right = 2 then (0 : Fin 6)
    else if right = 3 then (0 : Fin 6)
    else if right = 4 then (0 : Fin 6)
    else (1 : Fin 6)
  else if left = 2 then
    if right = 0 then (0 : Fin 6)
    else if right = 1 then (0 : Fin 6)
    else if right = 2 then (0 : Fin 6)
    else if right = 3 then (0 : Fin 6)
    else if right = 4 then (2 : Fin 6)
    else (0 : Fin 6)
  else if left = 3 then
    if right = 0 then (3 : Fin 6)
    else if right = 1 then (3 : Fin 6)
    else if right = 2 then (3 : Fin 6)
    else if right = 3 then (3 : Fin 6)
    else if right = 4 then (3 : Fin 6)
    else (3 : Fin 6)
  else if left = 4 then
    if right = 0 then (0 : Fin 6)
    else if right = 1 then (0 : Fin 6)
    else if right = 2 then (0 : Fin 6)
    else if right = 3 then (3 : Fin 6)
    else if right = 4 then (4 : Fin 6)
    else (0 : Fin 6)
  else
    if right = 0 then (0 : Fin 6)
    else if right = 1 then (1 : Fin 6)
    else if right = 2 then (2 : Fin 6)
    else if right = 3 then (0 : Fin 6)
    else if right = 4 then (2 : Fin 6)
    else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

abbrev factorTable : FiniteTable := rightOppositeTable

def ontoLeftMap (value : Fin 6) : Fin 3 :=
  if value = 0 then (0 : Fin 3)
  else if value = 1 then (0 : Fin 3)
  else if value = 2 then (0 : Fin 3)
  else if value = 3 then (2 : Fin 3)
  else if value = 4 then (1 : Fin 3)
  else (0 : Fin 3)

def ontoLeftSection (value : Fin 3) : Fin 6 :=
  if value = 0 then (0 : Fin 6)
  else if value = 1 then (4 : Fin 6)
  else (3 : Fin 6)

def ontoLeft : SplitSurjection table.semigroup leftTable.semigroup where
  toFun := ontoLeftMap
  map_mul := by decide
  preimage := ontoLeftSection
  right_inverse := by
    intro value
    exact by decide +revert

def ontoRightMap (value : Fin 6) : Fin 5 :=
  if value = 0 then (0 : Fin 5)
  else if value = 1 then (1 : Fin 5)
  else if value = 2 then (2 : Fin 5)
  else if value = 3 then (0 : Fin 5)
  else if value = 4 then (3 : Fin 5)
  else (4 : Fin 5)

def ontoRightSection (value : Fin 5) : Fin 6 :=
  if value = 0 then (0 : Fin 6)
  else if value = 1 then (1 : Fin 6)
  else if value = 2 then (2 : Fin 6)
  else if value = 3 then (4 : Fin 6)
  else (5 : Fin 6)

def ontoRight : SplitSurjection table.semigroup factorTable.semigroup where
  toFun := ontoRightMap
  map_mul := by decide
  preimage := ontoRightSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup leftTable.semigroup factorTable.semigroup where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := by
    intro left right
    exact by decide +revert

end S6_8140

namespace S6_11028

/-- Exact one-based compact catalogue-table SHA-256: ac6dc463494890cdbac6e5f22121a87c31baaba1d4b8162d8f561cf2f32de5dd. -/
def sourceTableSHA256 : String := "ac6dc463494890cdbac6e5f22121a87c31baaba1d4b8162d8f561cf2f32de5dd"

def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then
    if right = 0 then (0 : Fin 6)
    else if right = 1 then (0 : Fin 6)
    else if right = 2 then (0 : Fin 6)
    else if right = 3 then (0 : Fin 6)
    else if right = 4 then (0 : Fin 6)
    else (0 : Fin 6)
  else if left = 1 then
    if right = 0 then (0 : Fin 6)
    else if right = 1 then (0 : Fin 6)
    else if right = 2 then (0 : Fin 6)
    else if right = 3 then (0 : Fin 6)
    else if right = 4 then (0 : Fin 6)
    else (1 : Fin 6)
  else if left = 2 then
    if right = 0 then (2 : Fin 6)
    else if right = 1 then (2 : Fin 6)
    else if right = 2 then (2 : Fin 6)
    else if right = 3 then (2 : Fin 6)
    else if right = 4 then (2 : Fin 6)
    else (2 : Fin 6)
  else if left = 3 then
    if right = 0 then (2 : Fin 6)
    else if right = 1 then (2 : Fin 6)
    else if right = 2 then (2 : Fin 6)
    else if right = 3 then (2 : Fin 6)
    else if right = 4 then (2 : Fin 6)
    else (3 : Fin 6)
  else if left = 4 then
    if right = 0 then (0 : Fin 6)
    else if right = 1 then (1 : Fin 6)
    else if right = 2 then (0 : Fin 6)
    else if right = 3 then (0 : Fin 6)
    else if right = 4 then (4 : Fin 6)
    else (1 : Fin 6)
  else
    if right = 0 then (0 : Fin 6)
    else if right = 1 then (0 : Fin 6)
    else if right = 2 then (2 : Fin 6)
    else if right = 3 then (3 : Fin 6)
    else if right = 4 then (0 : Fin 6)
    else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

abbrev factorTable : FiniteTable := rightTable

def ontoLeftMap (value : Fin 6) : Fin 3 :=
  if value = 0 then (0 : Fin 3)
  else if value = 1 then (0 : Fin 3)
  else if value = 2 then (2 : Fin 3)
  else if value = 3 then (2 : Fin 3)
  else if value = 4 then (0 : Fin 3)
  else (1 : Fin 3)

def ontoLeftSection (value : Fin 3) : Fin 6 :=
  if value = 0 then (0 : Fin 6)
  else if value = 1 then (5 : Fin 6)
  else (2 : Fin 6)

def ontoLeft : SplitSurjection table.semigroup leftTable.semigroup where
  toFun := ontoLeftMap
  map_mul := by decide
  preimage := ontoLeftSection
  right_inverse := by
    intro value
    exact by decide +revert

def ontoRightMap (value : Fin 6) : Fin 5 :=
  if value = 0 then (0 : Fin 5)
  else if value = 1 then (2 : Fin 5)
  else if value = 2 then (0 : Fin 5)
  else if value = 3 then (1 : Fin 5)
  else if value = 4 then (3 : Fin 5)
  else (4 : Fin 5)

def ontoRightSection (value : Fin 5) : Fin 6 :=
  if value = 0 then (0 : Fin 6)
  else if value = 1 then (3 : Fin 6)
  else if value = 2 then (1 : Fin 6)
  else if value = 3 then (4 : Fin 6)
  else (5 : Fin 6)

def ontoRight : SplitSurjection table.semigroup factorTable.semigroup where
  toFun := ontoRightMap
  map_mul := by decide
  preimage := ontoRightSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup leftTable.semigroup factorTable.semigroup where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := by
    intro left right
    exact by decide +revert

end S6_11028

namespace S6_11086

/-- Exact one-based compact catalogue-table SHA-256: 4e7c6c8b0d22057cb0ee5d67ece1204eaee961b4cf98ef238823d14f19bdf41e. -/
def sourceTableSHA256 : String := "4e7c6c8b0d22057cb0ee5d67ece1204eaee961b4cf98ef238823d14f19bdf41e"

def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then
    if right = 0 then (0 : Fin 6)
    else if right = 1 then (0 : Fin 6)
    else if right = 2 then (0 : Fin 6)
    else if right = 3 then (0 : Fin 6)
    else if right = 4 then (0 : Fin 6)
    else (0 : Fin 6)
  else if left = 1 then
    if right = 0 then (0 : Fin 6)
    else if right = 1 then (0 : Fin 6)
    else if right = 2 then (0 : Fin 6)
    else if right = 3 then (0 : Fin 6)
    else if right = 4 then (0 : Fin 6)
    else (1 : Fin 6)
  else if left = 2 then
    if right = 0 then (2 : Fin 6)
    else if right = 1 then (2 : Fin 6)
    else if right = 2 then (2 : Fin 6)
    else if right = 3 then (2 : Fin 6)
    else if right = 4 then (2 : Fin 6)
    else (2 : Fin 6)
  else if left = 3 then
    if right = 0 then (2 : Fin 6)
    else if right = 1 then (2 : Fin 6)
    else if right = 2 then (2 : Fin 6)
    else if right = 3 then (2 : Fin 6)
    else if right = 4 then (3 : Fin 6)
    else (2 : Fin 6)
  else if left = 4 then
    if right = 0 then (0 : Fin 6)
    else if right = 1 then (1 : Fin 6)
    else if right = 2 then (2 : Fin 6)
    else if right = 3 then (3 : Fin 6)
    else if right = 4 then (4 : Fin 6)
    else (1 : Fin 6)
  else
    if right = 0 then (0 : Fin 6)
    else if right = 1 then (0 : Fin 6)
    else if right = 2 then (0 : Fin 6)
    else if right = 3 then (0 : Fin 6)
    else if right = 4 then (0 : Fin 6)
    else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

abbrev factorTable : FiniteTable := rightOppositeTable

def ontoLeftMap (value : Fin 6) : Fin 3 :=
  if value = 0 then (0 : Fin 3)
  else if value = 1 then (0 : Fin 3)
  else if value = 2 then (2 : Fin 3)
  else if value = 3 then (2 : Fin 3)
  else if value = 4 then (1 : Fin 3)
  else (0 : Fin 3)

def ontoLeftSection (value : Fin 3) : Fin 6 :=
  if value = 0 then (0 : Fin 6)
  else if value = 1 then (4 : Fin 6)
  else (2 : Fin 6)

def ontoLeft : SplitSurjection table.semigroup leftTable.semigroup where
  toFun := ontoLeftMap
  map_mul := by decide
  preimage := ontoLeftSection
  right_inverse := by
    intro value
    exact by decide +revert

def ontoRightMap (value : Fin 6) : Fin 5 :=
  if value = 0 then (0 : Fin 5)
  else if value = 1 then (2 : Fin 5)
  else if value = 2 then (0 : Fin 5)
  else if value = 3 then (1 : Fin 5)
  else if value = 4 then (4 : Fin 5)
  else (3 : Fin 5)

def ontoRightSection (value : Fin 5) : Fin 6 :=
  if value = 0 then (0 : Fin 6)
  else if value = 1 then (3 : Fin 6)
  else if value = 2 then (1 : Fin 6)
  else if value = 3 then (5 : Fin 6)
  else (4 : Fin 6)

def ontoRight : SplitSurjection table.semigroup factorTable.semigroup where
  toFun := ontoRightMap
  map_mul := by decide
  preimage := ontoRightSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup leftTable.semigroup factorTable.semigroup where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := by
    intro left right
    exact by decide +revert

end S6_11086

end SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank105.FiniteFanout
