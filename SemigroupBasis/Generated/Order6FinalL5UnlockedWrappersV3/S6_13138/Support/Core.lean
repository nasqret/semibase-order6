import SemigroupBasis.FiniteNilpotentCounterexample
import SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Opposite
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.Shards.DecodeState
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.Shards.DecodeStateProof
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.Shards.RepresentativeHead
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.Shards.RepresentativeTail
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.Shards.SourceLabel
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.Shards.StateVector
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.Shards.Transition
import SemigroupBasis.Nonfinite
import SemigroupBasis.Opposite
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138

open SemigroupBasis

def routeManifestRowSHA256 : String := "206ee7706dfe26863f129738a3b39cde1de13faf36260df1e90ecbfe305952ba"
def witnessRecordSHA256 : String := "b49e26b1eb1826c19ae8bb174905104598c20ac7cc9ad7c3643a9da1134e9891"
def transferComponentSHA256 : String := "b49e26b1eb1826c19ae8bb174905104598c20ac7cc9ad7c3643a9da1134e9891"
def powerCertificateSHA256 : String := "a21f34eb8a33b87f0c6b973330cb16d81f9ce391281469b358889c9e10805eb9"

private def row6
    (c0 c1 c2 c3 c4 c5 : Fin 6) (column : Fin 6) : Fin 6 :=
  if column = 0 then c0 else
    if column = 1 then c1 else
      if column = 2 then c2 else
        if column = 3 then c3 else
          if column = 4 then c4 else c5

/-- Exact one-based catalogue table committed by the portable witness. -/
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 2 2 2 2 right else
    if left = 1 then row6 0 0 2 2 2 2 right else
      if left = 2 then row6 0 0 2 2 2 2 right else
        if left = 3 then row6 0 0 2 3 3 3 right else
          if left = 4 then row6 0 0 2 4 4 4 right else
            row6 0 1 2 3 4 5 right

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
  "3d843616d499b775e62f259d9a25a21923c76aedc18045fc8d126a07d7f6a282"

def stateVector (state : Fin 11742)
    (coordinate : Fin 36) : Fin 6 :=
  Shards.stateVector state coordinate

def generatorVector (generator : Fin 6)
    (coordinate : Fin 36) : Fin 6 :=
  match generator.val with
  | 0 =>
      match coordinate.val with
      | 0 => (1 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (5 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (5 : Fin 6)
      | 10 => (4 : Fin 6)
      | 11 => (5 : Fin 6)
      | 12 => (5 : Fin 6)
      | 13 => (5 : Fin 6)
      | 14 => (1 : Fin 6)
      | 15 => (5 : Fin 6)
      | 16 => (3 : Fin 6)
      | 17 => (5 : Fin 6)
      | 18 => (5 : Fin 6)
      | 19 => (4 : Fin 6)
      | 20 => (5 : Fin 6)
      | 21 => (5 : Fin 6)
      | 22 => (5 : Fin 6)
      | 23 => (5 : Fin 6)
      | 24 => (5 : Fin 6)
      | 25 => (5 : Fin 6)
      | 26 => (4 : Fin 6)
      | 27 => (4 : Fin 6)
      | 28 => (4 : Fin 6)
      | 29 => (5 : Fin 6)
      | 30 => (5 : Fin 6)
      | 31 => (5 : Fin 6)
      | 32 => (4 : Fin 6)
      | 33 => (4 : Fin 6)
      | 34 => (4 : Fin 6)
      | _ => (4 : Fin 6)
  | 1 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (1 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (1 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (3 : Fin 6)
      | 10 => (5 : Fin 6)
      | 11 => (4 : Fin 6)
      | 12 => (5 : Fin 6)
      | 13 => (5 : Fin 6)
      | 14 => (5 : Fin 6)
      | 15 => (5 : Fin 6)
      | 16 => (4 : Fin 6)
      | 17 => (5 : Fin 6)
      | 18 => (4 : Fin 6)
      | 19 => (5 : Fin 6)
      | 20 => (5 : Fin 6)
      | 21 => (5 : Fin 6)
      | 22 => (5 : Fin 6)
      | 23 => (1 : Fin 6)
      | 24 => (5 : Fin 6)
      | 25 => (5 : Fin 6)
      | 26 => (5 : Fin 6)
      | 27 => (5 : Fin 6)
      | 28 => (3 : Fin 6)
      | 29 => (4 : Fin 6)
      | 30 => (5 : Fin 6)
      | 31 => (4 : Fin 6)
      | 32 => (5 : Fin 6)
      | 33 => (5 : Fin 6)
      | 34 => (5 : Fin 6)
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
      | 8 => (5 : Fin 6)
      | 9 => (5 : Fin 6)
      | 10 => (3 : Fin 6)
      | 11 => (5 : Fin 6)
      | 12 => (4 : Fin 6)
      | 13 => (5 : Fin 6)
      | 14 => (5 : Fin 6)
      | 15 => (4 : Fin 6)
      | 16 => (3 : Fin 6)
      | 17 => (5 : Fin 6)
      | 18 => (5 : Fin 6)
      | 19 => (5 : Fin 6)
      | 20 => (4 : Fin 6)
      | 21 => (5 : Fin 6)
      | 22 => (5 : Fin 6)
      | 23 => (5 : Fin 6)
      | 24 => (5 : Fin 6)
      | 25 => (1 : Fin 6)
      | 26 => (5 : Fin 6)
      | 27 => (3 : Fin 6)
      | 28 => (5 : Fin 6)
      | 29 => (5 : Fin 6)
      | 30 => (5 : Fin 6)
      | 31 => (3 : Fin 6)
      | 32 => (3 : Fin 6)
      | 33 => (5 : Fin 6)
      | 34 => (5 : Fin 6)
      | _ => (5 : Fin 6)
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
      | 9 => (5 : Fin 6)
      | 10 => (5 : Fin 6)
      | 11 => (3 : Fin 6)
      | 12 => (5 : Fin 6)
      | 13 => (5 : Fin 6)
      | 14 => (5 : Fin 6)
      | 15 => (3 : Fin 6)
      | 16 => (5 : Fin 6)
      | 17 => (4 : Fin 6)
      | 18 => (5 : Fin 6)
      | 19 => (3 : Fin 6)
      | 20 => (5 : Fin 6)
      | 21 => (1 : Fin 6)
      | 22 => (4 : Fin 6)
      | 23 => (5 : Fin 6)
      | 24 => (5 : Fin 6)
      | 25 => (5 : Fin 6)
      | 26 => (5 : Fin 6)
      | 27 => (3 : Fin 6)
      | 28 => (5 : Fin 6)
      | 29 => (5 : Fin 6)
      | 30 => (5 : Fin 6)
      | 31 => (5 : Fin 6)
      | 32 => (5 : Fin 6)
      | 33 => (3 : Fin 6)
      | 34 => (5 : Fin 6)
      | _ => (5 : Fin 6)
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
      | 9 => (4 : Fin 6)
      | 10 => (5 : Fin 6)
      | 11 => (5 : Fin 6)
      | 12 => (3 : Fin 6)
      | 13 => (5 : Fin 6)
      | 14 => (5 : Fin 6)
      | 15 => (5 : Fin 6)
      | 16 => (5 : Fin 6)
      | 17 => (3 : Fin 6)
      | 18 => (5 : Fin 6)
      | 19 => (3 : Fin 6)
      | 20 => (5 : Fin 6)
      | 21 => (5 : Fin 6)
      | 22 => (5 : Fin 6)
      | 23 => (5 : Fin 6)
      | 24 => (1 : Fin 6)
      | 25 => (5 : Fin 6)
      | 26 => (3 : Fin 6)
      | 27 => (5 : Fin 6)
      | 28 => (5 : Fin 6)
      | 29 => (3 : Fin 6)
      | 30 => (4 : Fin 6)
      | 31 => (5 : Fin 6)
      | 32 => (5 : Fin 6)
      | 33 => (5 : Fin 6)
      | 34 => (3 : Fin 6)
      | _ => (5 : Fin 6)
  | _ =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (1 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (1 : Fin 6)
      | 8 => (1 : Fin 6)
      | 9 => (3 : Fin 6)
      | 10 => (3 : Fin 6)
      | 11 => (5 : Fin 6)
      | 12 => (5 : Fin 6)
      | 13 => (1 : Fin 6)
      | 14 => (5 : Fin 6)
      | 15 => (5 : Fin 6)
      | 16 => (5 : Fin 6)
      | 17 => (5 : Fin 6)
      | 18 => (3 : Fin 6)
      | 19 => (5 : Fin 6)
      | 20 => (3 : Fin 6)
      | 21 => (5 : Fin 6)
      | 22 => (3 : Fin 6)
      | 23 => (5 : Fin 6)
      | 24 => (5 : Fin 6)
      | 25 => (5 : Fin 6)
      | 26 => (3 : Fin 6)
      | 27 => (5 : Fin 6)
      | 28 => (5 : Fin 6)
      | 29 => (5 : Fin 6)
      | 30 => (3 : Fin 6)
      | 31 => (5 : Fin 6)
      | 32 => (5 : Fin 6)
      | 33 => (5 : Fin 6)
      | 34 => (5 : Fin 6)
      | _ => (3 : Fin 6)

def transition (state : Fin 11742)
    (generator : Fin 6) : Fin 11742 :=
  Shards.transition state generator

def representativeHead (state : Fin 11742) : Fin 6 :=
  Shards.representativeHead state

def representativeTail (state : Fin 11742) :
    List (Fin 6) :=
  Shards.representativeTail state

def sourceLabel (state : Fin 11742) : Fin 6 :=
  Shards.sourceLabel state

def generatorSourceLabel (generator : Fin 6) : Fin 6 :=
  match generator.val with
  | 0 => (0 : Fin 6)
  | 1 => (1 : Fin 6)
  | 2 => (2 : Fin 6)
  | 3 => (3 : Fin 6)
  | 4 => (4 : Fin 6)
  | _ => (5 : Fin 6)

def sourcePreimage (value : Fin 6) : Fin 11742 :=
  match value.val with
  | 0 => (0 : Fin 11742)
  | 1 => (1 : Fin 11742)
  | 2 => (2 : Fin 11742)
  | 3 => (3 : Fin 11742)
  | 4 => (4 : Fin 11742)
  | _ => (5 : Fin 11742)

abbrev decodeState :
    (Fin 36 -> Fin 6) -> Fin 11742 :=
  Shards.decodeState

theorem decodeState_stateVector (state : Fin 11742) :
    decodeState (stateVector state) = state :=
  Shards.decodeState_stateVector state

def generatorState
    (generator : Fin 6) :
    Fin 11742 :=
  ⟨generator.val, by omega⟩

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138
