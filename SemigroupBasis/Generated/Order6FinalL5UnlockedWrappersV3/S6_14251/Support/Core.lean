import SemigroupBasis.FiniteNilpotentCounterexample
import SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Representative
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.Shards.DecodeState
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.Shards.DecodeStateProof
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.Shards.RepresentativeHead
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.Shards.RepresentativeTail
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.Shards.SourceLabel
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.Shards.StateVector
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251.Shards.Transition
import SemigroupBasis.Nonfinite
import SemigroupBasis.Opposite
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251

open SemigroupBasis

def routeManifestRowSHA256 : String := "6b3b6c1564b4fd77d39a80304b55737436aa5dab77b2d9c88bea86e46c834db3"
def witnessRecordSHA256 : String := "0ebf8be228fa41cd675789965f9c6b2972c9c1c89b8725e8d9fe0790830dd0ba"
def transferComponentSHA256 : String := "0ebf8be228fa41cd675789965f9c6b2972c9c1c89b8725e8d9fe0790830dd0ba"
def powerCertificateSHA256 : String := "0b2bc599bb550d56c69dd5f96320e10a7231e1f0e70526d29ca563164b303a8f"

private def row6
    (c0 c1 c2 c3 c4 c5 : Fin 6) (column : Fin 6) : Fin 6 :=
  if column = 0 then c0 else
    if column = 1 then c1 else
      if column = 2 then c2 else
        if column = 3 then c3 else
          if column = 4 then c4 else c5

/-- Exact one-based catalogue table committed by the portable witness. -/
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 2 0 4 4 right else
    if left = 1 then row6 0 0 2 0 4 4 right else
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
  "351be0ab9b052fec02cc3aa39b9701fe577446b87dae7e157598a8522fd7e247"

def stateVector (state : Fin 17622)
    (coordinate : Fin 59) : Fin 6 :=
  Shards.stateVector state coordinate

def generatorVector (generator : Fin 6)
    (coordinate : Fin 59) : Fin 6 :=
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
      | 7 => (1 : Fin 6)
      | 8 => (1 : Fin 6)
      | 9 => (1 : Fin 6)
      | 10 => (3 : Fin 6)
      | 11 => (3 : Fin 6)
      | 12 => (0 : Fin 6)
      | 13 => (0 : Fin 6)
      | 14 => (3 : Fin 6)
      | 15 => (3 : Fin 6)
      | 16 => (1 : Fin 6)
      | 17 => (0 : Fin 6)
      | 18 => (3 : Fin 6)
      | 19 => (3 : Fin 6)
      | 20 => (5 : Fin 6)
      | 21 => (0 : Fin 6)
      | 22 => (3 : Fin 6)
      | 23 => (2 : Fin 6)
      | 24 => (0 : Fin 6)
      | 25 => (3 : Fin 6)
      | 26 => (3 : Fin 6)
      | 27 => (0 : Fin 6)
      | 28 => (2 : Fin 6)
      | 29 => (3 : Fin 6)
      | 30 => (2 : Fin 6)
      | 31 => (2 : Fin 6)
      | 32 => (3 : Fin 6)
      | 33 => (3 : Fin 6)
      | 34 => (1 : Fin 6)
      | 35 => (3 : Fin 6)
      | 36 => (3 : Fin 6)
      | 37 => (3 : Fin 6)
      | 38 => (3 : Fin 6)
      | 39 => (0 : Fin 6)
      | 40 => (3 : Fin 6)
      | 41 => (3 : Fin 6)
      | 42 => (3 : Fin 6)
      | 43 => (2 : Fin 6)
      | 44 => (3 : Fin 6)
      | 45 => (2 : Fin 6)
      | 46 => (3 : Fin 6)
      | 47 => (0 : Fin 6)
      | 48 => (3 : Fin 6)
      | 49 => (3 : Fin 6)
      | 50 => (2 : Fin 6)
      | 51 => (3 : Fin 6)
      | 52 => (3 : Fin 6)
      | 53 => (2 : Fin 6)
      | 54 => (3 : Fin 6)
      | 55 => (2 : Fin 6)
      | 56 => (2 : Fin 6)
      | 57 => (2 : Fin 6)
      | _ => (2 : Fin 6)
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
      | 8 => (0 : Fin 6)
      | 9 => (0 : Fin 6)
      | 10 => (0 : Fin 6)
      | 11 => (3 : Fin 6)
      | 12 => (3 : Fin 6)
      | 13 => (1 : Fin 6)
      | 14 => (0 : Fin 6)
      | 15 => (0 : Fin 6)
      | 16 => (3 : Fin 6)
      | 17 => (0 : Fin 6)
      | 18 => (3 : Fin 6)
      | 19 => (1 : Fin 6)
      | 20 => (0 : Fin 6)
      | 21 => (0 : Fin 6)
      | 22 => (2 : Fin 6)
      | 23 => (0 : Fin 6)
      | 24 => (0 : Fin 6)
      | 25 => (3 : Fin 6)
      | 26 => (3 : Fin 6)
      | 27 => (5 : Fin 6)
      | 28 => (3 : Fin 6)
      | 29 => (3 : Fin 6)
      | 30 => (0 : Fin 6)
      | 31 => (3 : Fin 6)
      | 32 => (3 : Fin 6)
      | 33 => (2 : Fin 6)
      | 34 => (3 : Fin 6)
      | 35 => (2 : Fin 6)
      | 36 => (0 : Fin 6)
      | 37 => (1 : Fin 6)
      | 38 => (3 : Fin 6)
      | 39 => (3 : Fin 6)
      | 40 => (3 : Fin 6)
      | 41 => (3 : Fin 6)
      | 42 => (3 : Fin 6)
      | 43 => (0 : Fin 6)
      | 44 => (3 : Fin 6)
      | 45 => (3 : Fin 6)
      | 46 => (3 : Fin 6)
      | 47 => (2 : Fin 6)
      | 48 => (3 : Fin 6)
      | 49 => (2 : Fin 6)
      | 50 => (3 : Fin 6)
      | 51 => (3 : Fin 6)
      | 52 => (2 : Fin 6)
      | 53 => (3 : Fin 6)
      | 54 => (2 : Fin 6)
      | 55 => (3 : Fin 6)
      | 56 => (3 : Fin 6)
      | 57 => (0 : Fin 6)
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
      | 9 => (0 : Fin 6)
      | 10 => (0 : Fin 6)
      | 11 => (0 : Fin 6)
      | 12 => (3 : Fin 6)
      | 13 => (0 : Fin 6)
      | 14 => (3 : Fin 6)
      | 15 => (1 : Fin 6)
      | 16 => (3 : Fin 6)
      | 17 => (5 : Fin 6)
      | 18 => (3 : Fin 6)
      | 19 => (3 : Fin 6)
      | 20 => (0 : Fin 6)
      | 21 => (0 : Fin 6)
      | 22 => (0 : Fin 6)
      | 23 => (0 : Fin 6)
      | 24 => (0 : Fin 6)
      | 25 => (2 : Fin 6)
      | 26 => (0 : Fin 6)
      | 27 => (0 : Fin 6)
      | 28 => (3 : Fin 6)
      | 29 => (0 : Fin 6)
      | 30 => (3 : Fin 6)
      | 31 => (0 : Fin 6)
      | 32 => (3 : Fin 6)
      | 33 => (3 : Fin 6)
      | 34 => (3 : Fin 6)
      | 35 => (3 : Fin 6)
      | 36 => (2 : Fin 6)
      | 37 => (3 : Fin 6)
      | 38 => (3 : Fin 6)
      | 39 => (3 : Fin 6)
      | 40 => (3 : Fin 6)
      | 41 => (1 : Fin 6)
      | 42 => (3 : Fin 6)
      | 43 => (3 : Fin 6)
      | 44 => (3 : Fin 6)
      | 45 => (0 : Fin 6)
      | 46 => (2 : Fin 6)
      | 47 => (3 : Fin 6)
      | 48 => (2 : Fin 6)
      | 49 => (3 : Fin 6)
      | 50 => (3 : Fin 6)
      | 51 => (3 : Fin 6)
      | 52 => (3 : Fin 6)
      | 53 => (0 : Fin 6)
      | 54 => (0 : Fin 6)
      | 55 => (3 : Fin 6)
      | 56 => (3 : Fin 6)
      | 57 => (3 : Fin 6)
      | _ => (3 : Fin 6)
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
      | 10 => (2 : Fin 6)
      | 11 => (3 : Fin 6)
      | 12 => (3 : Fin 6)
      | 13 => (3 : Fin 6)
      | 14 => (3 : Fin 6)
      | 15 => (3 : Fin 6)
      | 16 => (0 : Fin 6)
      | 17 => (0 : Fin 6)
      | 18 => (0 : Fin 6)
      | 19 => (0 : Fin 6)
      | 20 => (0 : Fin 6)
      | 21 => (0 : Fin 6)
      | 22 => (3 : Fin 6)
      | 23 => (0 : Fin 6)
      | 24 => (5 : Fin 6)
      | 25 => (3 : Fin 6)
      | 26 => (2 : Fin 6)
      | 27 => (0 : Fin 6)
      | 28 => (0 : Fin 6)
      | 29 => (3 : Fin 6)
      | 30 => (3 : Fin 6)
      | 31 => (3 : Fin 6)
      | 32 => (2 : Fin 6)
      | 33 => (0 : Fin 6)
      | 34 => (3 : Fin 6)
      | 35 => (3 : Fin 6)
      | 36 => (3 : Fin 6)
      | 37 => (3 : Fin 6)
      | 38 => (2 : Fin 6)
      | 39 => (3 : Fin 6)
      | 40 => (3 : Fin 6)
      | 41 => (3 : Fin 6)
      | 42 => (1 : Fin 6)
      | 43 => (3 : Fin 6)
      | 44 => (3 : Fin 6)
      | 45 => (0 : Fin 6)
      | 46 => (0 : Fin 6)
      | 47 => (0 : Fin 6)
      | 48 => (3 : Fin 6)
      | 49 => (3 : Fin 6)
      | 50 => (0 : Fin 6)
      | 51 => (3 : Fin 6)
      | 52 => (0 : Fin 6)
      | 53 => (3 : Fin 6)
      | 54 => (3 : Fin 6)
      | 55 => (3 : Fin 6)
      | 56 => (0 : Fin 6)
      | 57 => (3 : Fin 6)
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
      | 11 => (0 : Fin 6)
      | 12 => (0 : Fin 6)
      | 13 => (3 : Fin 6)
      | 14 => (2 : Fin 6)
      | 15 => (3 : Fin 6)
      | 16 => (3 : Fin 6)
      | 17 => (0 : Fin 6)
      | 18 => (3 : Fin 6)
      | 19 => (3 : Fin 6)
      | 20 => (0 : Fin 6)
      | 21 => (5 : Fin 6)
      | 22 => (3 : Fin 6)
      | 23 => (0 : Fin 6)
      | 24 => (0 : Fin 6)
      | 25 => (3 : Fin 6)
      | 26 => (0 : Fin 6)
      | 27 => (0 : Fin 6)
      | 28 => (3 : Fin 6)
      | 29 => (2 : Fin 6)
      | 30 => (0 : Fin 6)
      | 31 => (3 : Fin 6)
      | 32 => (3 : Fin 6)
      | 33 => (0 : Fin 6)
      | 34 => (3 : Fin 6)
      | 35 => (3 : Fin 6)
      | 36 => (0 : Fin 6)
      | 37 => (3 : Fin 6)
      | 38 => (0 : Fin 6)
      | 39 => (2 : Fin 6)
      | 40 => (3 : Fin 6)
      | 41 => (3 : Fin 6)
      | 42 => (3 : Fin 6)
      | 43 => (3 : Fin 6)
      | 44 => (1 : Fin 6)
      | 45 => (3 : Fin 6)
      | 46 => (3 : Fin 6)
      | 47 => (3 : Fin 6)
      | 48 => (0 : Fin 6)
      | 49 => (0 : Fin 6)
      | 50 => (0 : Fin 6)
      | 51 => (2 : Fin 6)
      | 52 => (3 : Fin 6)
      | 53 => (3 : Fin 6)
      | 54 => (3 : Fin 6)
      | 55 => (3 : Fin 6)
      | 56 => (3 : Fin 6)
      | 57 => (3 : Fin 6)
      | _ => (0 : Fin 6)
  | _ =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (1 : Fin 6)
      | 6 => (1 : Fin 6)
      | 7 => (3 : Fin 6)
      | 8 => (3 : Fin 6)
      | 9 => (3 : Fin 6)
      | 10 => (0 : Fin 6)
      | 11 => (1 : Fin 6)
      | 12 => (1 : Fin 6)
      | 13 => (3 : Fin 6)
      | 14 => (0 : Fin 6)
      | 15 => (3 : Fin 6)
      | 16 => (3 : Fin 6)
      | 17 => (0 : Fin 6)
      | 18 => (1 : Fin 6)
      | 19 => (3 : Fin 6)
      | 20 => (0 : Fin 6)
      | 21 => (0 : Fin 6)
      | 22 => (0 : Fin 6)
      | 23 => (3 : Fin 6)
      | 24 => (0 : Fin 6)
      | 25 => (0 : Fin 6)
      | 26 => (3 : Fin 6)
      | 27 => (0 : Fin 6)
      | 28 => (0 : Fin 6)
      | 29 => (0 : Fin 6)
      | 30 => (3 : Fin 6)
      | 31 => (0 : Fin 6)
      | 32 => (0 : Fin 6)
      | 33 => (3 : Fin 6)
      | 34 => (3 : Fin 6)
      | 35 => (0 : Fin 6)
      | 36 => (3 : Fin 6)
      | 37 => (3 : Fin 6)
      | 38 => (3 : Fin 6)
      | 39 => (0 : Fin 6)
      | 40 => (1 : Fin 6)
      | 41 => (3 : Fin 6)
      | 42 => (3 : Fin 6)
      | 43 => (0 : Fin 6)
      | 44 => (3 : Fin 6)
      | 45 => (3 : Fin 6)
      | 46 => (3 : Fin 6)
      | 47 => (3 : Fin 6)
      | 48 => (3 : Fin 6)
      | 49 => (3 : Fin 6)
      | 50 => (3 : Fin 6)
      | 51 => (0 : Fin 6)
      | 52 => (3 : Fin 6)
      | 53 => (3 : Fin 6)
      | 54 => (3 : Fin 6)
      | 55 => (0 : Fin 6)
      | 56 => (3 : Fin 6)
      | 57 => (3 : Fin 6)
      | _ => (3 : Fin 6)

def transition (state : Fin 17622)
    (generator : Fin 6) : Fin 17622 :=
  Shards.transition state generator

def representativeHead (state : Fin 17622) : Fin 6 :=
  Shards.representativeHead state

def representativeTail (state : Fin 17622) :
    List (Fin 6) :=
  Shards.representativeTail state

def sourceLabel (state : Fin 17622) : Fin 6 :=
  Shards.sourceLabel state

def generatorSourceLabel (generator : Fin 6) : Fin 6 :=
  match generator.val with
  | 0 => (0 : Fin 6)
  | 1 => (1 : Fin 6)
  | 2 => (2 : Fin 6)
  | 3 => (3 : Fin 6)
  | 4 => (4 : Fin 6)
  | _ => (5 : Fin 6)

def sourcePreimage (value : Fin 6) : Fin 17622 :=
  match value.val with
  | 0 => (0 : Fin 17622)
  | 1 => (1 : Fin 17622)
  | 2 => (2 : Fin 17622)
  | 3 => (3 : Fin 17622)
  | 4 => (4 : Fin 17622)
  | _ => (5 : Fin 17622)

abbrev decodeState :
    (Fin 59 -> Fin 6) -> Fin 17622 :=
  Shards.decodeState

theorem decodeState_stateVector (state : Fin 17622) :
    decodeState (stateVector state) = state :=
  Shards.decodeState_stateVector state

def generatorState
    (generator : Fin 6) :
    Fin 17622 :=
  ⟨generator.val, by omega⟩

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14251
