import SemigroupBasis.CoRoots.Order6Day7.Level2.Rank127

/-!
# Exact finite fanout for the two final-multiplicity systems

Four source-pinned catalogue tables and split-subdirect pairs, transcribed
from the NEW finite search with SHA-256
`6abc2e443a1cbedce71cd4fa93b8d9ddcf6e46b61ea07868a88559d03490461e`.
All obligations use ordinary kernel reduction, never native_decide.
S6_8254 uses the opposite S5_379 table; the remaining three right factors
have their displayed direct orientation. Finite maps alone are not a
completeness proof.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace SemigroupBasis.CoRoots.Order6Day7.Level2.FinalMultiplicityFiniteFanout

open SemigroupBasis

namespace S6_7975

/-- Exact one-based compact catalogue-table SHA-256. -/
def sourceTableSHA256 : String := "dfde8269547f42e43bf5e69f01fb6fcb475f4f076793bfc1246744ae72190878"

abbrev leftFactorTable : FiniteTable := Rank109.leftTable
abbrev rightFactorTable : FiniteTable := Rank109.rightTable

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
    else (0 : Fin 6)
  else if left = 4 then
    if right = 0 then (0 : Fin 6)
    else if right = 1 then (0 : Fin 6)
    else if right = 2 then (2 : Fin 6)
    else if right = 3 then (3 : Fin 6)
    else if right = 4 then (4 : Fin 6)
    else (2 : Fin 6)
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

def ontoLeftMap (value : Fin 6) : Fin 3 :=
  if value = 0 then (0 : Fin 3)
  else if value = 1 then (1 : Fin 3)
  else if value = 2 then (0 : Fin 3)
  else if value = 3 then (0 : Fin 3)
  else if value = 4 then (0 : Fin 3)
  else (2 : Fin 3)

def ontoLeftSection (value : Fin 3) : Fin 6 :=
  if value = 0 then (0 : Fin 6)
  else if value = 1 then (1 : Fin 6)
  else (5 : Fin 6)

def ontoLeft : SplitSurjection table.semigroup leftFactorTable.semigroup where
  toFun := ontoLeftMap
  map_mul := by decide
  preimage := ontoLeftSection
  right_inverse := by
    intro value
    exact by decide +revert

def ontoRightMap (value : Fin 6) : Fin 5 :=
  if value = 0 then (0 : Fin 5)
  else if value = 1 then (0 : Fin 5)
  else if value = 2 then (1 : Fin 5)
  else if value = 3 then (2 : Fin 5)
  else if value = 4 then (3 : Fin 5)
  else (4 : Fin 5)

def ontoRightSection (value : Fin 5) : Fin 6 :=
  if value = 0 then (0 : Fin 6)
  else if value = 1 then (2 : Fin 6)
  else if value = 2 then (3 : Fin 6)
  else if value = 3 then (4 : Fin 6)
  else (5 : Fin 6)

def ontoRight : SplitSurjection table.semigroup rightFactorTable.semigroup where
  toFun := ontoRightMap
  map_mul := by decide
  preimage := ontoRightSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup leftFactorTable.semigroup rightFactorTable.semigroup where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := by
    intro left right
    exact by decide +revert

end S6_7975

namespace S6_8253

/-- Exact one-based compact catalogue-table SHA-256. -/
def sourceTableSHA256 : String := "b5ea048448bb6b280d5cbe4324175fbddcbf63ec61f77d0da2eb4f2c604c91fc"

abbrev leftFactorTable : FiniteTable := Rank109.leftTable
abbrev rightFactorTable : FiniteTable := Rank109.rightTable

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
    else if right = 3 then (2 : Fin 6)
    else if right = 4 then (2 : Fin 6)
    else (0 : Fin 6)
  else if left = 3 then
    if right = 0 then (0 : Fin 6)
    else if right = 1 then (1 : Fin 6)
    else if right = 2 then (2 : Fin 6)
    else if right = 3 then (3 : Fin 6)
    else if right = 4 then (4 : Fin 6)
    else (0 : Fin 6)
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

def ontoLeftMap (value : Fin 6) : Fin 3 :=
  if value = 0 then (0 : Fin 3)
  else if value = 1 then (0 : Fin 3)
  else if value = 2 then (1 : Fin 3)
  else if value = 3 then (2 : Fin 3)
  else if value = 4 then (2 : Fin 3)
  else (0 : Fin 3)

def ontoLeftSection (value : Fin 3) : Fin 6 :=
  if value = 0 then (0 : Fin 6)
  else if value = 1 then (2 : Fin 6)
  else (3 : Fin 6)

def ontoLeft : SplitSurjection table.semigroup leftFactorTable.semigroup where
  toFun := ontoLeftMap
  map_mul := by decide
  preimage := ontoLeftSection
  right_inverse := by
    intro value
    exact by decide +revert

def ontoRightMap (value : Fin 6) : Fin 5 :=
  if value = 0 then (0 : Fin 5)
  else if value = 1 then (1 : Fin 5)
  else if value = 2 then (0 : Fin 5)
  else if value = 3 then (2 : Fin 5)
  else if value = 4 then (3 : Fin 5)
  else (4 : Fin 5)

def ontoRightSection (value : Fin 5) : Fin 6 :=
  if value = 0 then (0 : Fin 6)
  else if value = 1 then (1 : Fin 6)
  else if value = 2 then (3 : Fin 6)
  else if value = 3 then (4 : Fin 6)
  else (5 : Fin 6)

def ontoRight : SplitSurjection table.semigroup rightFactorTable.semigroup where
  toFun := ontoRightMap
  map_mul := by decide
  preimage := ontoRightSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup leftFactorTable.semigroup rightFactorTable.semigroup where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := by
    intro left right
    exact by decide +revert

end S6_8253

namespace S6_7980

/-- Exact one-based compact catalogue-table SHA-256. -/
def sourceTableSHA256 : String := "b4a4c687ff37a4a5d480c05b889a3b1f976f3a0dd884aed43b3ca6408b6883b5"

abbrev leftFactorTable : FiniteTable := Rank127.leftTable
abbrev rightFactorTable : FiniteTable := Rank127.rightTable

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
    if right = 0 then (0 : Fin 6)
    else if right = 1 then (0 : Fin 6)
    else if right = 2 then (2 : Fin 6)
    else if right = 3 then (3 : Fin 6)
    else if right = 4 then (4 : Fin 6)
    else (2 : Fin 6)
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

def ontoLeft : SplitSurjection table.semigroup leftFactorTable.semigroup where
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
  else if value = 4 then (3 : Fin 5)
  else (4 : Fin 5)

def ontoRightSection (value : Fin 5) : Fin 6 :=
  if value = 0 then (0 : Fin 6)
  else if value = 1 then (1 : Fin 6)
  else if value = 2 then (2 : Fin 6)
  else if value = 3 then (3 : Fin 6)
  else (5 : Fin 6)

def ontoRight : SplitSurjection table.semigroup rightFactorTable.semigroup where
  toFun := ontoRightMap
  map_mul := by decide
  preimage := ontoRightSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup leftFactorTable.semigroup rightFactorTable.semigroup where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := by
    intro left right
    exact by decide +revert

end S6_7980

namespace S6_8254

/-- Exact one-based compact catalogue-table SHA-256. -/
def sourceTableSHA256 : String := "6ca416fc9b23be561ae5f6c622ca23bb274175e394dec873d1f5daed7c667628"

abbrev leftFactorTable : FiniteTable := Rank127.leftTable
abbrev rightFactorTable : FiniteTable := Rank127.rightOppositeTable

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
    else if right = 3 then (2 : Fin 6)
    else if right = 4 then (2 : Fin 6)
    else (0 : Fin 6)
  else if left = 3 then
    if right = 0 then (0 : Fin 6)
    else if right = 1 then (1 : Fin 6)
    else if right = 2 then (2 : Fin 6)
    else if right = 3 then (3 : Fin 6)
    else if right = 4 then (4 : Fin 6)
    else (1 : Fin 6)
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

def ontoLeft : SplitSurjection table.semigroup leftFactorTable.semigroup where
  toFun := ontoLeftMap
  map_mul := by decide
  preimage := ontoLeftSection
  right_inverse := by
    intro value
    exact by decide +revert

def ontoRightMap (value : Fin 6) : Fin 5 :=
  if value = 0 then (0 : Fin 5)
  else if value = 1 then (2 : Fin 5)
  else if value = 2 then (1 : Fin 5)
  else if value = 3 then (4 : Fin 5)
  else if value = 4 then (4 : Fin 5)
  else (3 : Fin 5)

def ontoRightSection (value : Fin 5) : Fin 6 :=
  if value = 0 then (0 : Fin 6)
  else if value = 1 then (2 : Fin 6)
  else if value = 2 then (1 : Fin 6)
  else if value = 3 then (5 : Fin 6)
  else (3 : Fin 6)

def ontoRight : SplitSurjection table.semigroup rightFactorTable.semigroup where
  toFun := ontoRightMap
  map_mul := by decide
  preimage := ontoRightSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup leftFactorTable.semigroup rightFactorTable.semigroup where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := by
    intro left right
    exact by decide +revert

end S6_8254

end SemigroupBasis.CoRoots.Order6Day7.Level2.FinalMultiplicityFiniteFanout
