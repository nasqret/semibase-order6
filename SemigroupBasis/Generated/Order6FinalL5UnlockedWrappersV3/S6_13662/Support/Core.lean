import SemigroupBasis.FiniteNilpotentCounterexample
import SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Opposite
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13662.Shards.DecodeState
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13662.Shards.DecodeStateProof
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13662.Shards.RepresentativeHead
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13662.Shards.RepresentativeTail
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13662.Shards.SourceLabel
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13662.Shards.StateVector
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13662.Shards.Transition
import SemigroupBasis.Nonfinite
import SemigroupBasis.Opposite
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13662

open SemigroupBasis

def routeManifestRowSHA256 : String := "d71477ef32047e4322cbb6c8180f1fb2c003d236f71a03b615fe8b5097beb4a4"
def witnessRecordSHA256 : String := "3546110347165e1cf09c2b4151f07cb9f0618c00f9b52721f20f7c631a522737"
def transferComponentSHA256 : String := "3546110347165e1cf09c2b4151f07cb9f0618c00f9b52721f20f7c631a522737"
def powerCertificateSHA256 : String := "0856bfaebfe51fa9b595637b1813e846d1d9fd21f3988cc8d7e2e76aa13bed3b"

private def row6
    (c0 c1 c2 c3 c4 c5 : Fin 6) (column : Fin 6) : Fin 6 :=
  if column = 0 then c0 else
    if column = 1 then c1 else
      if column = 2 then c2 else
        if column = 3 then c3 else
          if column = 4 then c4 else c5

/-- Exact one-based catalogue table committed by the portable witness. -/
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 2 0 0 0 right else
    if left = 1 then row6 0 0 2 0 0 0 right else
      if left = 2 then row6 0 0 2 0 0 0 right else
        if left = 3 then row6 0 1 2 3 3 3 right else
          if left = 4 then row6 0 1 2 3 4 5 right else
            row6 0 1 2 5 5 5 right

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
  "f1931114874717497da0d88ec324db500ad9132994793dd100e0a1192fe25b27"

def stateVector (state : Fin 11742)
    (coordinate : Fin 44) : Fin 6 :=
  Shards.stateVector state coordinate

def generatorVector (generator : Fin 6)
    (coordinate : Fin 44) : Fin 6 :=
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
      | 11 => (3 : Fin 6)
      | 12 => (5 : Fin 6)
      | 13 => (5 : Fin 6)
      | 14 => (3 : Fin 6)
      | 15 => (4 : Fin 6)
      | 16 => (3 : Fin 6)
      | 17 => (3 : Fin 6)
      | 18 => (3 : Fin 6)
      | 19 => (1 : Fin 6)
      | 20 => (3 : Fin 6)
      | 21 => (4 : Fin 6)
      | 22 => (4 : Fin 6)
      | 23 => (2 : Fin 6)
      | 24 => (4 : Fin 6)
      | 25 => (4 : Fin 6)
      | 26 => (0 : Fin 6)
      | 27 => (4 : Fin 6)
      | 28 => (5 : Fin 6)
      | 29 => (0 : Fin 6)
      | 30 => (4 : Fin 6)
      | 31 => (0 : Fin 6)
      | 32 => (0 : Fin 6)
      | 33 => (5 : Fin 6)
      | 34 => (4 : Fin 6)
      | 35 => (4 : Fin 6)
      | 36 => (5 : Fin 6)
      | 37 => (5 : Fin 6)
      | 38 => (4 : Fin 6)
      | 39 => (4 : Fin 6)
      | 40 => (5 : Fin 6)
      | 41 => (4 : Fin 6)
      | 42 => (4 : Fin 6)
      | _ => (5 : Fin 6)
  | 1 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (1 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (1 : Fin 6)
      | 7 => (3 : Fin 6)
      | 8 => (0 : Fin 6)
      | 9 => (0 : Fin 6)
      | 10 => (0 : Fin 6)
      | 11 => (0 : Fin 6)
      | 12 => (4 : Fin 6)
      | 13 => (4 : Fin 6)
      | 14 => (1 : Fin 6)
      | 15 => (4 : Fin 6)
      | 16 => (3 : Fin 6)
      | 17 => (3 : Fin 6)
      | 18 => (3 : Fin 6)
      | 19 => (3 : Fin 6)
      | 20 => (3 : Fin 6)
      | 21 => (3 : Fin 6)
      | 22 => (3 : Fin 6)
      | 23 => (0 : Fin 6)
      | 24 => (3 : Fin 6)
      | 25 => (5 : Fin 6)
      | 26 => (2 : Fin 6)
      | 27 => (5 : Fin 6)
      | 28 => (3 : Fin 6)
      | 29 => (0 : Fin 6)
      | 30 => (4 : Fin 6)
      | 31 => (0 : Fin 6)
      | 32 => (0 : Fin 6)
      | 33 => (4 : Fin 6)
      | 34 => (4 : Fin 6)
      | 35 => (4 : Fin 6)
      | 36 => (4 : Fin 6)
      | 37 => (4 : Fin 6)
      | 38 => (5 : Fin 6)
      | 39 => (4 : Fin 6)
      | 40 => (3 : Fin 6)
      | 41 => (4 : Fin 6)
      | 42 => (5 : Fin 6)
      | _ => (4 : Fin 6)
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
      | 12 => (4 : Fin 6)
      | 13 => (3 : Fin 6)
      | 14 => (3 : Fin 6)
      | 15 => (4 : Fin 6)
      | 16 => (1 : Fin 6)
      | 17 => (3 : Fin 6)
      | 18 => (3 : Fin 6)
      | 19 => (3 : Fin 6)
      | 20 => (3 : Fin 6)
      | 21 => (3 : Fin 6)
      | 22 => (5 : Fin 6)
      | 23 => (0 : Fin 6)
      | 24 => (4 : Fin 6)
      | 25 => (4 : Fin 6)
      | 26 => (0 : Fin 6)
      | 27 => (4 : Fin 6)
      | 28 => (3 : Fin 6)
      | 29 => (2 : Fin 6)
      | 30 => (5 : Fin 6)
      | 31 => (0 : Fin 6)
      | 32 => (0 : Fin 6)
      | 33 => (4 : Fin 6)
      | 34 => (4 : Fin 6)
      | 35 => (5 : Fin 6)
      | 36 => (4 : Fin 6)
      | 37 => (4 : Fin 6)
      | 38 => (3 : Fin 6)
      | 39 => (5 : Fin 6)
      | 40 => (4 : Fin 6)
      | 41 => (4 : Fin 6)
      | 42 => (4 : Fin 6)
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
      | 10 => (0 : Fin 6)
      | 11 => (0 : Fin 6)
      | 12 => (3 : Fin 6)
      | 13 => (4 : Fin 6)
      | 14 => (3 : Fin 6)
      | 15 => (4 : Fin 6)
      | 16 => (3 : Fin 6)
      | 17 => (1 : Fin 6)
      | 18 => (3 : Fin 6)
      | 19 => (3 : Fin 6)
      | 20 => (3 : Fin 6)
      | 21 => (5 : Fin 6)
      | 22 => (4 : Fin 6)
      | 23 => (0 : Fin 6)
      | 24 => (5 : Fin 6)
      | 25 => (4 : Fin 6)
      | 26 => (0 : Fin 6)
      | 27 => (4 : Fin 6)
      | 28 => (4 : Fin 6)
      | 29 => (0 : Fin 6)
      | 30 => (4 : Fin 6)
      | 31 => (2 : Fin 6)
      | 32 => (0 : Fin 6)
      | 33 => (3 : Fin 6)
      | 34 => (5 : Fin 6)
      | 35 => (3 : Fin 6)
      | 36 => (4 : Fin 6)
      | 37 => (4 : Fin 6)
      | 38 => (4 : Fin 6)
      | 39 => (4 : Fin 6)
      | 40 => (4 : Fin 6)
      | 41 => (5 : Fin 6)
      | 42 => (3 : Fin 6)
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
      | 10 => (3 : Fin 6)
      | 11 => (0 : Fin 6)
      | 12 => (3 : Fin 6)
      | 13 => (3 : Fin 6)
      | 14 => (3 : Fin 6)
      | 15 => (5 : Fin 6)
      | 16 => (3 : Fin 6)
      | 17 => (3 : Fin 6)
      | 18 => (1 : Fin 6)
      | 19 => (3 : Fin 6)
      | 20 => (3 : Fin 6)
      | 21 => (3 : Fin 6)
      | 22 => (3 : Fin 6)
      | 23 => (0 : Fin 6)
      | 24 => (4 : Fin 6)
      | 25 => (3 : Fin 6)
      | 26 => (0 : Fin 6)
      | 27 => (4 : Fin 6)
      | 28 => (4 : Fin 6)
      | 29 => (0 : Fin 6)
      | 30 => (4 : Fin 6)
      | 31 => (0 : Fin 6)
      | 32 => (2 : Fin 6)
      | 33 => (4 : Fin 6)
      | 34 => (3 : Fin 6)
      | 35 => (4 : Fin 6)
      | 36 => (4 : Fin 6)
      | 37 => (3 : Fin 6)
      | 38 => (4 : Fin 6)
      | 39 => (3 : Fin 6)
      | 40 => (4 : Fin 6)
      | 41 => (4 : Fin 6)
      | 42 => (4 : Fin 6)
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
      | 7 => (1 : Fin 6)
      | 8 => (1 : Fin 6)
      | 9 => (1 : Fin 6)
      | 10 => (1 : Fin 6)
      | 11 => (3 : Fin 6)
      | 12 => (3 : Fin 6)
      | 13 => (3 : Fin 6)
      | 14 => (3 : Fin 6)
      | 15 => (3 : Fin 6)
      | 16 => (3 : Fin 6)
      | 17 => (3 : Fin 6)
      | 18 => (3 : Fin 6)
      | 19 => (3 : Fin 6)
      | 20 => (1 : Fin 6)
      | 21 => (4 : Fin 6)
      | 22 => (4 : Fin 6)
      | 23 => (0 : Fin 6)
      | 24 => (3 : Fin 6)
      | 25 => (4 : Fin 6)
      | 26 => (0 : Fin 6)
      | 27 => (3 : Fin 6)
      | 28 => (4 : Fin 6)
      | 29 => (0 : Fin 6)
      | 30 => (3 : Fin 6)
      | 31 => (0 : Fin 6)
      | 32 => (0 : Fin 6)
      | 33 => (4 : Fin 6)
      | 34 => (4 : Fin 6)
      | 35 => (4 : Fin 6)
      | 36 => (3 : Fin 6)
      | 37 => (4 : Fin 6)
      | 38 => (4 : Fin 6)
      | 39 => (4 : Fin 6)
      | 40 => (4 : Fin 6)
      | 41 => (3 : Fin 6)
      | 42 => (4 : Fin 6)
      | _ => (4 : Fin 6)

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
    (Fin 44 -> Fin 6) -> Fin 11742 :=
  Shards.decodeState

theorem decodeState_stateVector (state : Fin 11742) :
    decodeState (stateVector state) = state :=
  Shards.decodeState_stateVector state

def generatorState
    (generator : Fin 6) :
    Fin 11742 :=
  ⟨generator.val, by omega⟩

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13662
