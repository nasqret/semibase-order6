import SemigroupBasis.FiniteNilpotentCounterexample
import SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.Shards.DecodeState
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.Shards.DecodeStateProof
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.Shards.RepresentativeHead
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.Shards.RepresentativeTail
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.Shards.SourceLabel
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.Shards.StateVector
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.Shards.Transition
import SemigroupBasis.Nonfinite
import SemigroupBasis.Opposite
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389

open SemigroupBasis

def routeManifestRowSHA256 : String := "2998e33697b84fea49be15fec4146bc5c598a3398b2781d2ff6a42006eb72d00"
def witnessRecordSHA256 : String := "280600f52475ab38c41f850a6023fffed89227738c0b6a19c990e1a061e5fee8"
def transferComponentSHA256 : String := "280600f52475ab38c41f850a6023fffed89227738c0b6a19c990e1a061e5fee8"
def powerCertificateSHA256 : String := "f46ecb91da74d38422003cdf7f1a0b1e72323672a832f0daa1fe047e392fe1be"

private def row6
    (c0 c1 c2 c3 c4 c5 : Fin 6) (column : Fin 6) : Fin 6 :=
  if column = 0 then c0 else
    if column = 1 then c1 else
      if column = 2 then c2 else
        if column = 3 then c3 else
          if column = 4 then c4 else c5

/-- Exact one-based catalogue table committed by the portable witness. -/
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 0 3 0 0 right else
    if left = 1 then row6 0 0 1 3 1 1 right else
      if left = 2 then row6 0 0 2 3 2 2 right else
        if left = 3 then row6 0 0 0 3 0 0 right else
          if left = 4 then row6 0 0 2 3 4 5 right else
            row6 0 0 5 3 5 5 right

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
  "c3154d1b6f5b02e725600d3e5bd7f147bfc95a8f6a7ba44b4166d36c34a03d22"

def stateVector (state : Fin 17622)
    (coordinate : Fin 56) : Fin 6 :=
  Shards.stateVector state coordinate

def generatorVector (generator : Fin 6)
    (coordinate : Fin 56) : Fin 6 :=
  match generator.val with
  | 0 =>
      match coordinate.val with
      | 0 => (1 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (2 : Fin 6)
      | 7 => (2 : Fin 6)
      | 8 => (2 : Fin 6)
      | 9 => (2 : Fin 6)
      | 10 => (2 : Fin 6)
      | 11 => (1 : Fin 6)
      | 12 => (0 : Fin 6)
      | 13 => (0 : Fin 6)
      | 14 => (0 : Fin 6)
      | 15 => (1 : Fin 6)
      | 16 => (0 : Fin 6)
      | 17 => (0 : Fin 6)
      | 18 => (0 : Fin 6)
      | 19 => (1 : Fin 6)
      | 20 => (0 : Fin 6)
      | 21 => (0 : Fin 6)
      | 22 => (2 : Fin 6)
      | 23 => (0 : Fin 6)
      | 24 => (4 : Fin 6)
      | 25 => (2 : Fin 6)
      | 26 => (2 : Fin 6)
      | 27 => (2 : Fin 6)
      | 28 => (5 : Fin 6)
      | 29 => (3 : Fin 6)
      | 30 => (2 : Fin 6)
      | 31 => (4 : Fin 6)
      | 32 => (2 : Fin 6)
      | 33 => (4 : Fin 6)
      | 34 => (0 : Fin 6)
      | 35 => (5 : Fin 6)
      | 36 => (4 : Fin 6)
      | 37 => (2 : Fin 6)
      | 38 => (4 : Fin 6)
      | 39 => (5 : Fin 6)
      | 40 => (0 : Fin 6)
      | 41 => (4 : Fin 6)
      | 42 => (0 : Fin 6)
      | 43 => (4 : Fin 6)
      | 44 => (4 : Fin 6)
      | 45 => (2 : Fin 6)
      | 46 => (5 : Fin 6)
      | 47 => (4 : Fin 6)
      | 48 => (4 : Fin 6)
      | 49 => (1 : Fin 6)
      | 50 => (4 : Fin 6)
      | 51 => (5 : Fin 6)
      | 52 => (0 : Fin 6)
      | 53 => (2 : Fin 6)
      | 54 => (2 : Fin 6)
      | _ => (4 : Fin 6)
  | 1 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (1 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (1 : Fin 6)
      | 8 => (0 : Fin 6)
      | 9 => (0 : Fin 6)
      | 10 => (0 : Fin 6)
      | 11 => (2 : Fin 6)
      | 12 => (2 : Fin 6)
      | 13 => (2 : Fin 6)
      | 14 => (2 : Fin 6)
      | 15 => (0 : Fin 6)
      | 16 => (1 : Fin 6)
      | 17 => (0 : Fin 6)
      | 18 => (0 : Fin 6)
      | 19 => (0 : Fin 6)
      | 20 => (1 : Fin 6)
      | 21 => (0 : Fin 6)
      | 22 => (2 : Fin 6)
      | 23 => (0 : Fin 6)
      | 24 => (4 : Fin 6)
      | 25 => (2 : Fin 6)
      | 26 => (0 : Fin 6)
      | 27 => (0 : Fin 6)
      | 28 => (4 : Fin 6)
      | 29 => (0 : Fin 6)
      | 30 => (2 : Fin 6)
      | 31 => (4 : Fin 6)
      | 32 => (5 : Fin 6)
      | 33 => (2 : Fin 6)
      | 34 => (3 : Fin 6)
      | 35 => (4 : Fin 6)
      | 36 => (2 : Fin 6)
      | 37 => (2 : Fin 6)
      | 38 => (4 : Fin 6)
      | 39 => (4 : Fin 6)
      | 40 => (0 : Fin 6)
      | 41 => (5 : Fin 6)
      | 42 => (0 : Fin 6)
      | 43 => (5 : Fin 6)
      | 44 => (4 : Fin 6)
      | 45 => (1 : Fin 6)
      | 46 => (4 : Fin 6)
      | 47 => (4 : Fin 6)
      | 48 => (4 : Fin 6)
      | 49 => (2 : Fin 6)
      | 50 => (5 : Fin 6)
      | 51 => (2 : Fin 6)
      | 52 => (0 : Fin 6)
      | 53 => (2 : Fin 6)
      | 54 => (2 : Fin 6)
      | _ => (5 : Fin 6)
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
      | 8 => (1 : Fin 6)
      | 9 => (0 : Fin 6)
      | 10 => (0 : Fin 6)
      | 11 => (0 : Fin 6)
      | 12 => (1 : Fin 6)
      | 13 => (0 : Fin 6)
      | 14 => (0 : Fin 6)
      | 15 => (2 : Fin 6)
      | 16 => (2 : Fin 6)
      | 17 => (2 : Fin 6)
      | 18 => (2 : Fin 6)
      | 19 => (0 : Fin 6)
      | 20 => (0 : Fin 6)
      | 21 => (1 : Fin 6)
      | 22 => (5 : Fin 6)
      | 23 => (4 : Fin 6)
      | 24 => (4 : Fin 6)
      | 25 => (1 : Fin 6)
      | 26 => (2 : Fin 6)
      | 27 => (2 : Fin 6)
      | 28 => (4 : Fin 6)
      | 29 => (0 : Fin 6)
      | 30 => (2 : Fin 6)
      | 31 => (5 : Fin 6)
      | 32 => (4 : Fin 6)
      | 33 => (2 : Fin 6)
      | 34 => (0 : Fin 6)
      | 35 => (4 : Fin 6)
      | 36 => (4 : Fin 6)
      | 37 => (1 : Fin 6)
      | 38 => (4 : Fin 6)
      | 39 => (4 : Fin 6)
      | 40 => (3 : Fin 6)
      | 41 => (2 : Fin 6)
      | 42 => (0 : Fin 6)
      | 43 => (4 : Fin 6)
      | 44 => (5 : Fin 6)
      | 45 => (2 : Fin 6)
      | 46 => (2 : Fin 6)
      | 47 => (5 : Fin 6)
      | 48 => (4 : Fin 6)
      | 49 => (2 : Fin 6)
      | 50 => (4 : Fin 6)
      | 51 => (4 : Fin 6)
      | 52 => (0 : Fin 6)
      | 53 => (2 : Fin 6)
      | 54 => (2 : Fin 6)
      | _ => (4 : Fin 6)
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
      | 9 => (1 : Fin 6)
      | 10 => (0 : Fin 6)
      | 11 => (0 : Fin 6)
      | 12 => (0 : Fin 6)
      | 13 => (1 : Fin 6)
      | 14 => (0 : Fin 6)
      | 15 => (0 : Fin 6)
      | 16 => (0 : Fin 6)
      | 17 => (1 : Fin 6)
      | 18 => (0 : Fin 6)
      | 19 => (2 : Fin 6)
      | 20 => (2 : Fin 6)
      | 21 => (2 : Fin 6)
      | 22 => (4 : Fin 6)
      | 23 => (5 : Fin 6)
      | 24 => (5 : Fin 6)
      | 25 => (2 : Fin 6)
      | 26 => (2 : Fin 6)
      | 27 => (1 : Fin 6)
      | 28 => (4 : Fin 6)
      | 29 => (0 : Fin 6)
      | 30 => (2 : Fin 6)
      | 31 => (2 : Fin 6)
      | 32 => (4 : Fin 6)
      | 33 => (2 : Fin 6)
      | 34 => (0 : Fin 6)
      | 35 => (2 : Fin 6)
      | 36 => (5 : Fin 6)
      | 37 => (2 : Fin 6)
      | 38 => (4 : Fin 6)
      | 39 => (4 : Fin 6)
      | 40 => (0 : Fin 6)
      | 41 => (4 : Fin 6)
      | 42 => (3 : Fin 6)
      | 43 => (4 : Fin 6)
      | 44 => (4 : Fin 6)
      | 45 => (2 : Fin 6)
      | 46 => (4 : Fin 6)
      | 47 => (4 : Fin 6)
      | 48 => (5 : Fin 6)
      | 49 => (2 : Fin 6)
      | 50 => (2 : Fin 6)
      | 51 => (4 : Fin 6)
      | 52 => (0 : Fin 6)
      | 53 => (1 : Fin 6)
      | 54 => (2 : Fin 6)
      | _ => (4 : Fin 6)
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
      | 10 => (1 : Fin 6)
      | 11 => (0 : Fin 6)
      | 12 => (0 : Fin 6)
      | 13 => (0 : Fin 6)
      | 14 => (1 : Fin 6)
      | 15 => (0 : Fin 6)
      | 16 => (0 : Fin 6)
      | 17 => (0 : Fin 6)
      | 18 => (1 : Fin 6)
      | 19 => (0 : Fin 6)
      | 20 => (0 : Fin 6)
      | 21 => (0 : Fin 6)
      | 22 => (4 : Fin 6)
      | 23 => (2 : Fin 6)
      | 24 => (4 : Fin 6)
      | 25 => (0 : Fin 6)
      | 26 => (1 : Fin 6)
      | 27 => (2 : Fin 6)
      | 28 => (2 : Fin 6)
      | 29 => (0 : Fin 6)
      | 30 => (2 : Fin 6)
      | 31 => (4 : Fin 6)
      | 32 => (4 : Fin 6)
      | 33 => (5 : Fin 6)
      | 34 => (0 : Fin 6)
      | 35 => (4 : Fin 6)
      | 36 => (2 : Fin 6)
      | 37 => (2 : Fin 6)
      | 38 => (5 : Fin 6)
      | 39 => (4 : Fin 6)
      | 40 => (0 : Fin 6)
      | 41 => (4 : Fin 6)
      | 42 => (0 : Fin 6)
      | 43 => (2 : Fin 6)
      | 44 => (2 : Fin 6)
      | 45 => (2 : Fin 6)
      | 46 => (4 : Fin 6)
      | 47 => (4 : Fin 6)
      | 48 => (2 : Fin 6)
      | 49 => (2 : Fin 6)
      | 50 => (4 : Fin 6)
      | 51 => (4 : Fin 6)
      | 52 => (3 : Fin 6)
      | 53 => (2 : Fin 6)
      | 54 => (1 : Fin 6)
      | _ => (4 : Fin 6)
  | _ =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (1 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (2 : Fin 6)
      | 8 => (2 : Fin 6)
      | 9 => (2 : Fin 6)
      | 10 => (2 : Fin 6)
      | 11 => (0 : Fin 6)
      | 12 => (2 : Fin 6)
      | 13 => (2 : Fin 6)
      | 14 => (2 : Fin 6)
      | 15 => (0 : Fin 6)
      | 16 => (0 : Fin 6)
      | 17 => (2 : Fin 6)
      | 18 => (2 : Fin 6)
      | 19 => (0 : Fin 6)
      | 20 => (0 : Fin 6)
      | 21 => (0 : Fin 6)
      | 22 => (2 : Fin 6)
      | 23 => (2 : Fin 6)
      | 24 => (2 : Fin 6)
      | 25 => (2 : Fin 6)
      | 26 => (2 : Fin 6)
      | 27 => (2 : Fin 6)
      | 28 => (4 : Fin 6)
      | 29 => (0 : Fin 6)
      | 30 => (1 : Fin 6)
      | 31 => (4 : Fin 6)
      | 32 => (2 : Fin 6)
      | 33 => (2 : Fin 6)
      | 34 => (0 : Fin 6)
      | 35 => (4 : Fin 6)
      | 36 => (4 : Fin 6)
      | 37 => (2 : Fin 6)
      | 38 => (2 : Fin 6)
      | 39 => (2 : Fin 6)
      | 40 => (0 : Fin 6)
      | 41 => (4 : Fin 6)
      | 42 => (0 : Fin 6)
      | 43 => (4 : Fin 6)
      | 44 => (4 : Fin 6)
      | 45 => (2 : Fin 6)
      | 46 => (4 : Fin 6)
      | 47 => (2 : Fin 6)
      | 48 => (4 : Fin 6)
      | 49 => (2 : Fin 6)
      | 50 => (4 : Fin 6)
      | 51 => (4 : Fin 6)
      | 52 => (0 : Fin 6)
      | 53 => (2 : Fin 6)
      | 54 => (2 : Fin 6)
      | _ => (2 : Fin 6)

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
    (Fin 56 -> Fin 6) -> Fin 17622 :=
  Shards.decodeState

theorem decodeState_stateVector (state : Fin 17622) :
    decodeState (stateVector state) = state :=
  Shards.decodeState_stateVector state

def generatorState
    (generator : Fin 6) :
    Fin 17622 :=
  ⟨generator.val, by omega⟩

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389
