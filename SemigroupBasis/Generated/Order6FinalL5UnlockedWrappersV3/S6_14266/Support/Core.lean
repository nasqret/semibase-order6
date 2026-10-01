import SemigroupBasis.FiniteNilpotentCounterexample
import SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7631Representative
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14266.Shards.DecodeState
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14266.Shards.DecodeStateProof
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14266.Shards.RepresentativeHead
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14266.Shards.RepresentativeTail
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14266.Shards.SourceLabel
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14266.Shards.StateVector
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14266.Shards.Transition
import SemigroupBasis.Nonfinite
import SemigroupBasis.Opposite
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14266

open SemigroupBasis

def routeManifestRowSHA256 : String := "139777929faa44959636507d460b31b51706688cfbb1e679518ff0b1052998e1"
def witnessRecordSHA256 : String := "d6074ae32605568ad33338b40bb16bcbcdc47fab7319a128905ee380e5bdb38b"
def transferComponentSHA256 : String := "d6074ae32605568ad33338b40bb16bcbcdc47fab7319a128905ee380e5bdb38b"
def powerCertificateSHA256 : String := "d4b492b474c2dd3893d6ae6f417597d6320c9a6c956de089574f7169efa9cd84"

private def row6
    (c0 c1 c2 c3 c4 c5 : Fin 6) (column : Fin 6) : Fin 6 :=
  if column = 0 then c0 else
    if column = 1 then c1 else
      if column = 2 then c2 else
        if column = 3 then c3 else
          if column = 4 then c4 else c5

/-- Exact one-based catalogue table committed by the portable witness. -/
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 2 2 4 4 right else
    if left = 1 then row6 0 0 2 2 4 4 right else
      if left = 2 then row6 0 0 2 2 4 4 right else
        if left = 3 then row6 0 1 2 3 4 4 right else
          if left = 4 then row6 4 4 4 4 4 4 right else
            row6 5 5 5 5 5 5 right

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def oppositeTable : FiniteTable where
  order := 6
  mul := fun left right => mul right left
  assoc := by decide

theorem oppositeTable_semigroup :
    oppositeTable.semigroup = table.semigroup.opposite :=
  rfl

def targetTableSHA256 : String :=
  "3fbc4b72e689a9f55a3b6036f604fadfdacd0c939c0dd26e65bdf3216c2d838f"

def stateVector (state : Fin 1158)
    (coordinate : Fin 24) : Fin 6 :=
  Shards.stateVector state coordinate

def generatorVector (generator : Fin 6)
    (coordinate : Fin 24) : Fin 6 :=
  match generator.val with
  | 0 =>
      match coordinate.val with
      | 0 => (1 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (3 : Fin 6)
      | 7 => (3 : Fin 6)
      | 8 => (3 : Fin 6)
      | 9 => (3 : Fin 6)
      | 10 => (3 : Fin 6)
      | 11 => (0 : Fin 6)
      | 12 => (3 : Fin 6)
      | 13 => (0 : Fin 6)
      | 14 => (0 : Fin 6)
      | 15 => (0 : Fin 6)
      | 16 => (5 : Fin 6)
      | 17 => (0 : Fin 6)
      | 18 => (3 : Fin 6)
      | 19 => (3 : Fin 6)
      | 20 => (3 : Fin 6)
      | 21 => (1 : Fin 6)
      | 22 => (3 : Fin 6)
      | _ => (3 : Fin 6)
  | 1 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (1 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (3 : Fin 6)
      | 8 => (3 : Fin 6)
      | 9 => (3 : Fin 6)
      | 10 => (0 : Fin 6)
      | 11 => (3 : Fin 6)
      | 12 => (3 : Fin 6)
      | 13 => (0 : Fin 6)
      | 14 => (0 : Fin 6)
      | 15 => (5 : Fin 6)
      | 16 => (0 : Fin 6)
      | 17 => (0 : Fin 6)
      | 18 => (3 : Fin 6)
      | 19 => (3 : Fin 6)
      | 20 => (1 : Fin 6)
      | 21 => (3 : Fin 6)
      | 22 => (3 : Fin 6)
      | _ => (3 : Fin 6)
  | 2 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (1 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (0 : Fin 6)
      | 8 => (3 : Fin 6)
      | 9 => (3 : Fin 6)
      | 10 => (3 : Fin 6)
      | 11 => (1 : Fin 6)
      | 12 => (0 : Fin 6)
      | 13 => (0 : Fin 6)
      | 14 => (0 : Fin 6)
      | 15 => (0 : Fin 6)
      | 16 => (0 : Fin 6)
      | 17 => (5 : Fin 6)
      | 18 => (3 : Fin 6)
      | 19 => (3 : Fin 6)
      | 20 => (3 : Fin 6)
      | 21 => (3 : Fin 6)
      | 22 => (3 : Fin 6)
      | _ => (1 : Fin 6)
  | 3 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (1 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (0 : Fin 6)
      | 8 => (0 : Fin 6)
      | 9 => (3 : Fin 6)
      | 10 => (3 : Fin 6)
      | 11 => (3 : Fin 6)
      | 12 => (1 : Fin 6)
      | 13 => (0 : Fin 6)
      | 14 => (5 : Fin 6)
      | 15 => (0 : Fin 6)
      | 16 => (0 : Fin 6)
      | 17 => (0 : Fin 6)
      | 18 => (3 : Fin 6)
      | 19 => (3 : Fin 6)
      | 20 => (3 : Fin 6)
      | 21 => (3 : Fin 6)
      | 22 => (1 : Fin 6)
      | _ => (3 : Fin 6)
  | 4 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (1 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (0 : Fin 6)
      | 8 => (0 : Fin 6)
      | 9 => (0 : Fin 6)
      | 10 => (3 : Fin 6)
      | 11 => (3 : Fin 6)
      | 12 => (3 : Fin 6)
      | 13 => (5 : Fin 6)
      | 14 => (0 : Fin 6)
      | 15 => (0 : Fin 6)
      | 16 => (0 : Fin 6)
      | 17 => (0 : Fin 6)
      | 18 => (3 : Fin 6)
      | 19 => (1 : Fin 6)
      | 20 => (3 : Fin 6)
      | 21 => (3 : Fin 6)
      | 22 => (3 : Fin 6)
      | _ => (3 : Fin 6)
  | _ =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (1 : Fin 6)
      | 6 => (1 : Fin 6)
      | 7 => (1 : Fin 6)
      | 8 => (1 : Fin 6)
      | 9 => (1 : Fin 6)
      | 10 => (1 : Fin 6)
      | 11 => (3 : Fin 6)
      | 12 => (3 : Fin 6)
      | 13 => (0 : Fin 6)
      | 14 => (0 : Fin 6)
      | 15 => (0 : Fin 6)
      | 16 => (0 : Fin 6)
      | 17 => (0 : Fin 6)
      | 18 => (1 : Fin 6)
      | 19 => (3 : Fin 6)
      | 20 => (3 : Fin 6)
      | 21 => (3 : Fin 6)
      | 22 => (3 : Fin 6)
      | _ => (3 : Fin 6)

def transition (state : Fin 1158)
    (generator : Fin 6) : Fin 1158 :=
  Shards.transition state generator

def representativeHead (state : Fin 1158) : Fin 6 :=
  Shards.representativeHead state

def representativeTail (state : Fin 1158) :
    List (Fin 6) :=
  Shards.representativeTail state

def sourceLabel (state : Fin 1158) : Fin 6 :=
  Shards.sourceLabel state

def generatorSourceLabel (generator : Fin 6) : Fin 6 :=
  match generator.val with
  | 0 => (0 : Fin 6)
  | 1 => (1 : Fin 6)
  | 2 => (2 : Fin 6)
  | 3 => (3 : Fin 6)
  | 4 => (4 : Fin 6)
  | _ => (5 : Fin 6)

def sourcePreimage (value : Fin 6) : Fin 1158 :=
  match value.val with
  | 0 => (0 : Fin 1158)
  | 1 => (1 : Fin 1158)
  | 2 => (2 : Fin 1158)
  | 3 => (3 : Fin 1158)
  | 4 => (4 : Fin 1158)
  | _ => (5 : Fin 1158)

abbrev decodeState :
    (Fin 24 -> Fin 6) -> Fin 1158 :=
  Shards.decodeState

theorem decodeState_stateVector (state : Fin 1158) :
    decodeState (stateVector state) = state :=
  Shards.decodeState_stateVector state

def generatorState
    (generator : Fin 6) :
    Fin 1158 :=
  ⟨generator.val, by omega⟩

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14266
