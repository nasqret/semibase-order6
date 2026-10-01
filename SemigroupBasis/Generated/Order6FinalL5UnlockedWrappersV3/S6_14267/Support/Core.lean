import SemigroupBasis.FiniteNilpotentCounterexample
import SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Opposite
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.Shards.DecodeState
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.Shards.DecodeStateProof
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.Shards.RepresentativeHead
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.Shards.RepresentativeTail
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.Shards.SourceLabel
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.Shards.StateVector
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.Shards.Transition
import SemigroupBasis.Nonfinite
import SemigroupBasis.Opposite
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267

open SemigroupBasis

def routeManifestRowSHA256 : String := "b5d63cee560be2f1720a2bba75558804592c21fac074aaf9e569595f41b4d1c7"
def witnessRecordSHA256 : String := "19ede90e63f38c876b594052e3bc58d140472a029adaa7f1085760a1d83d0cc5"
def transferComponentSHA256 : String := "19ede90e63f38c876b594052e3bc58d140472a029adaa7f1085760a1d83d0cc5"
def powerCertificateSHA256 : String := "27892a183f036025d0575b9a508eb0a8df5a15524301104a4ef69af0883eed4e"

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
        if left = 3 then row6 0 1 2 3 4 5 right else
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
  "d9ba008e54b7b1c403f3a1ae3a77435234aa446887ec9efb20f80dff2e1624e3"

def stateVector (state : Fin 11742)
    (coordinate : Fin 45) : Fin 6 :=
  Shards.stateVector state coordinate

def generatorVector (generator : Fin 6)
    (coordinate : Fin 45) : Fin 6 :=
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
      | 10 => (5 : Fin 6)
      | 11 => (3 : Fin 6)
      | 12 => (3 : Fin 6)
      | 13 => (0 : Fin 6)
      | 14 => (3 : Fin 6)
      | 15 => (3 : Fin 6)
      | 16 => (5 : Fin 6)
      | 17 => (3 : Fin 6)
      | 18 => (3 : Fin 6)
      | 19 => (3 : Fin 6)
      | 20 => (3 : Fin 6)
      | 21 => (1 : Fin 6)
      | 22 => (5 : Fin 6)
      | 23 => (0 : Fin 6)
      | 24 => (3 : Fin 6)
      | 25 => (5 : Fin 6)
      | 26 => (3 : Fin 6)
      | 27 => (3 : Fin 6)
      | 28 => (3 : Fin 6)
      | 29 => (3 : Fin 6)
      | 30 => (3 : Fin 6)
      | 31 => (3 : Fin 6)
      | 32 => (5 : Fin 6)
      | 33 => (0 : Fin 6)
      | 34 => (0 : Fin 6)
      | 35 => (3 : Fin 6)
      | 36 => (3 : Fin 6)
      | 37 => (3 : Fin 6)
      | 38 => (5 : Fin 6)
      | 39 => (5 : Fin 6)
      | 40 => (5 : Fin 6)
      | 41 => (5 : Fin 6)
      | 42 => (5 : Fin 6)
      | 43 => (3 : Fin 6)
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
      | 9 => (5 : Fin 6)
      | 10 => (3 : Fin 6)
      | 11 => (3 : Fin 6)
      | 12 => (3 : Fin 6)
      | 13 => (3 : Fin 6)
      | 14 => (0 : Fin 6)
      | 15 => (0 : Fin 6)
      | 16 => (0 : Fin 6)
      | 17 => (3 : Fin 6)
      | 18 => (3 : Fin 6)
      | 19 => (1 : Fin 6)
      | 20 => (5 : Fin 6)
      | 21 => (3 : Fin 6)
      | 22 => (0 : Fin 6)
      | 23 => (3 : Fin 6)
      | 24 => (3 : Fin 6)
      | 25 => (3 : Fin 6)
      | 26 => (5 : Fin 6)
      | 27 => (5 : Fin 6)
      | 28 => (3 : Fin 6)
      | 29 => (3 : Fin 6)
      | 30 => (3 : Fin 6)
      | 31 => (3 : Fin 6)
      | 32 => (3 : Fin 6)
      | 33 => (3 : Fin 6)
      | 34 => (5 : Fin 6)
      | 35 => (3 : Fin 6)
      | 36 => (3 : Fin 6)
      | 37 => (5 : Fin 6)
      | 38 => (3 : Fin 6)
      | 39 => (3 : Fin 6)
      | 40 => (3 : Fin 6)
      | 41 => (3 : Fin 6)
      | 42 => (0 : Fin 6)
      | 43 => (5 : Fin 6)
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
      | 10 => (0 : Fin 6)
      | 11 => (0 : Fin 6)
      | 12 => (5 : Fin 6)
      | 13 => (3 : Fin 6)
      | 14 => (3 : Fin 6)
      | 15 => (5 : Fin 6)
      | 16 => (3 : Fin 6)
      | 17 => (3 : Fin 6)
      | 18 => (3 : Fin 6)
      | 19 => (3 : Fin 6)
      | 20 => (0 : Fin 6)
      | 21 => (3 : Fin 6)
      | 22 => (3 : Fin 6)
      | 23 => (5 : Fin 6)
      | 24 => (3 : Fin 6)
      | 25 => (3 : Fin 6)
      | 26 => (3 : Fin 6)
      | 27 => (3 : Fin 6)
      | 28 => (1 : Fin 6)
      | 29 => (5 : Fin 6)
      | 30 => (3 : Fin 6)
      | 31 => (3 : Fin 6)
      | 32 => (0 : Fin 6)
      | 33 => (3 : Fin 6)
      | 34 => (0 : Fin 6)
      | 35 => (3 : Fin 6)
      | 36 => (5 : Fin 6)
      | 37 => (3 : Fin 6)
      | 38 => (3 : Fin 6)
      | 39 => (0 : Fin 6)
      | 40 => (3 : Fin 6)
      | 41 => (3 : Fin 6)
      | 42 => (3 : Fin 6)
      | 43 => (0 : Fin 6)
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
      | 10 => (3 : Fin 6)
      | 11 => (5 : Fin 6)
      | 12 => (3 : Fin 6)
      | 13 => (3 : Fin 6)
      | 14 => (5 : Fin 6)
      | 15 => (3 : Fin 6)
      | 16 => (0 : Fin 6)
      | 17 => (3 : Fin 6)
      | 18 => (1 : Fin 6)
      | 19 => (3 : Fin 6)
      | 20 => (0 : Fin 6)
      | 21 => (3 : Fin 6)
      | 22 => (3 : Fin 6)
      | 23 => (0 : Fin 6)
      | 24 => (5 : Fin 6)
      | 25 => (0 : Fin 6)
      | 26 => (3 : Fin 6)
      | 27 => (3 : Fin 6)
      | 28 => (3 : Fin 6)
      | 29 => (3 : Fin 6)
      | 30 => (3 : Fin 6)
      | 31 => (3 : Fin 6)
      | 32 => (3 : Fin 6)
      | 33 => (5 : Fin 6)
      | 34 => (3 : Fin 6)
      | 35 => (5 : Fin 6)
      | 36 => (0 : Fin 6)
      | 37 => (0 : Fin 6)
      | 38 => (3 : Fin 6)
      | 39 => (3 : Fin 6)
      | 40 => (0 : Fin 6)
      | 41 => (3 : Fin 6)
      | 42 => (3 : Fin 6)
      | 43 => (3 : Fin 6)
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
      | 9 => (0 : Fin 6)
      | 10 => (3 : Fin 6)
      | 11 => (0 : Fin 6)
      | 12 => (0 : Fin 6)
      | 13 => (5 : Fin 6)
      | 14 => (3 : Fin 6)
      | 15 => (3 : Fin 6)
      | 16 => (3 : Fin 6)
      | 17 => (3 : Fin 6)
      | 18 => (3 : Fin 6)
      | 19 => (3 : Fin 6)
      | 20 => (3 : Fin 6)
      | 21 => (3 : Fin 6)
      | 22 => (0 : Fin 6)
      | 23 => (3 : Fin 6)
      | 24 => (0 : Fin 6)
      | 25 => (3 : Fin 6)
      | 26 => (0 : Fin 6)
      | 27 => (3 : Fin 6)
      | 28 => (3 : Fin 6)
      | 29 => (3 : Fin 6)
      | 30 => (5 : Fin 6)
      | 31 => (1 : Fin 6)
      | 32 => (0 : Fin 6)
      | 33 => (0 : Fin 6)
      | 34 => (3 : Fin 6)
      | 35 => (3 : Fin 6)
      | 36 => (3 : Fin 6)
      | 37 => (3 : Fin 6)
      | 38 => (3 : Fin 6)
      | 39 => (3 : Fin 6)
      | 40 => (3 : Fin 6)
      | 41 => (0 : Fin 6)
      | 42 => (3 : Fin 6)
      | 43 => (3 : Fin 6)
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
      | 7 => (1 : Fin 6)
      | 8 => (1 : Fin 6)
      | 9 => (0 : Fin 6)
      | 10 => (0 : Fin 6)
      | 11 => (3 : Fin 6)
      | 12 => (3 : Fin 6)
      | 13 => (0 : Fin 6)
      | 14 => (0 : Fin 6)
      | 15 => (0 : Fin 6)
      | 16 => (3 : Fin 6)
      | 17 => (1 : Fin 6)
      | 18 => (3 : Fin 6)
      | 19 => (3 : Fin 6)
      | 20 => (3 : Fin 6)
      | 21 => (3 : Fin 6)
      | 22 => (3 : Fin 6)
      | 23 => (3 : Fin 6)
      | 24 => (0 : Fin 6)
      | 25 => (0 : Fin 6)
      | 26 => (3 : Fin 6)
      | 27 => (0 : Fin 6)
      | 28 => (3 : Fin 6)
      | 29 => (0 : Fin 6)
      | 30 => (0 : Fin 6)
      | 31 => (3 : Fin 6)
      | 32 => (3 : Fin 6)
      | 33 => (3 : Fin 6)
      | 34 => (3 : Fin 6)
      | 35 => (0 : Fin 6)
      | 36 => (3 : Fin 6)
      | 37 => (3 : Fin 6)
      | 38 => (0 : Fin 6)
      | 39 => (3 : Fin 6)
      | 40 => (3 : Fin 6)
      | 41 => (3 : Fin 6)
      | 42 => (3 : Fin 6)
      | 43 => (3 : Fin 6)
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
    (Fin 45 -> Fin 6) -> Fin 11742 :=
  Shards.decodeState

theorem decodeState_stateVector (state : Fin 11742) :
    decodeState (stateVector state) = state :=
  Shards.decodeState_stateVector state

def generatorState
    (generator : Fin 6) :
    Fin 11742 :=
  ⟨generator.val, by omega⟩

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267
