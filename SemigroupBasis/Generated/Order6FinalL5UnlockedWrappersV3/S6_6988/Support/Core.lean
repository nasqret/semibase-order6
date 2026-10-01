import SemigroupBasis.FiniteNilpotentCounterexample
import SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6196Representative
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6988.Shards.DecodeState
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6988.Shards.DecodeStateProof
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6988.Shards.RepresentativeHead
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6988.Shards.RepresentativeTail
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6988.Shards.SourceLabel
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6988.Shards.StateVector
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6988.Shards.Transition
import SemigroupBasis.Nonfinite
import SemigroupBasis.Opposite
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6988

open SemigroupBasis

def routeManifestRowSHA256 : String := "da9c7d241a59c89681be192e11c9a8ef74b69f7980b190ec218a60caedb22c21"
def witnessRecordSHA256 : String := "c30fe8344a6bdfd38d6089d4c92826ac72973b164e3ab6708009d61082722c8b"
def transferComponentSHA256 : String := "c30fe8344a6bdfd38d6089d4c92826ac72973b164e3ab6708009d61082722c8b"
def powerCertificateSHA256 : String := "9c94bf01680a172e0eab7f0b09f9b73e23114364036488d933eea8ba24471c1d"

private def row6
    (c0 c1 c2 c3 c4 c5 : Fin 6) (column : Fin 6) : Fin 6 :=
  if column = 0 then c0 else
    if column = 1 then c1 else
      if column = 2 then c2 else
        if column = 3 then c3 else
          if column = 4 then c4 else c5

/-- Exact one-based catalogue table committed by the portable witness. -/
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 1 1 3 4 3 right else
    if left = 1 then row6 1 0 0 4 3 4 right else
      if left = 2 then row6 1 0 0 4 3 4 right else
        if left = 3 then row6 0 1 1 3 4 3 right else
          if left = 4 then row6 1 0 0 4 3 4 right else
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
  "ba0ecdf1becf2144d7759310530d6724526d227c4b0308d689f97c8caca5cb28"

def stateVector (state : Fin 4374)
    (coordinate : Fin 10) : Fin 6 :=
  Shards.stateVector state coordinate

def generatorVector (generator : Fin 6)
    (coordinate : Fin 10) : Fin 6 :=
  match generator.val with
  | 0 =>
      match coordinate.val with
      | 0 => (5 : Fin 6)
      | 1 => (5 : Fin 6)
      | 2 => (5 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (5 : Fin 6)
      | 5 => (5 : Fin 6)
      | 6 => (2 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (5 : Fin 6)
      | _ => (5 : Fin 6)
  | 1 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (5 : Fin 6)
      | 2 => (5 : Fin 6)
      | 3 => (5 : Fin 6)
      | 4 => (5 : Fin 6)
      | 5 => (2 : Fin 6)
      | 6 => (5 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (5 : Fin 6)
      | _ => (5 : Fin 6)
  | 2 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (5 : Fin 6)
      | 3 => (5 : Fin 6)
      | 4 => (5 : Fin 6)
      | 5 => (5 : Fin 6)
      | 6 => (5 : Fin 6)
      | 7 => (2 : Fin 6)
      | 8 => (5 : Fin 6)
      | _ => (5 : Fin 6)
  | 3 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (5 : Fin 6)
      | 4 => (5 : Fin 6)
      | 5 => (5 : Fin 6)
      | 6 => (5 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (2 : Fin 6)
      | _ => (5 : Fin 6)
  | 4 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (5 : Fin 6)
      | 5 => (5 : Fin 6)
      | 6 => (5 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (5 : Fin 6)
      | _ => (2 : Fin 6)
  | _ =>
      match coordinate.val with
      | 0 => (5 : Fin 6)
      | 1 => (5 : Fin 6)
      | 2 => (5 : Fin 6)
      | 3 => (5 : Fin 6)
      | 4 => (2 : Fin 6)
      | 5 => (5 : Fin 6)
      | 6 => (5 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (5 : Fin 6)
      | _ => (5 : Fin 6)

def transition (state : Fin 4374)
    (generator : Fin 6) : Fin 4374 :=
  Shards.transition state generator

def representativeHead (state : Fin 4374) : Fin 6 :=
  Shards.representativeHead state

def representativeTail (state : Fin 4374) :
    List (Fin 6) :=
  Shards.representativeTail state

def sourceLabel (state : Fin 4374) : Fin 6 :=
  Shards.sourceLabel state

def generatorSourceLabel (generator : Fin 6) : Fin 6 :=
  match generator.val with
  | 0 => (0 : Fin 6)
  | 1 => (1 : Fin 6)
  | 2 => (2 : Fin 6)
  | 3 => (3 : Fin 6)
  | 4 => (4 : Fin 6)
  | _ => (5 : Fin 6)

def sourcePreimage (value : Fin 6) : Fin 4374 :=
  match value.val with
  | 0 => (0 : Fin 4374)
  | 1 => (1 : Fin 4374)
  | 2 => (2 : Fin 4374)
  | 3 => (3 : Fin 4374)
  | 4 => (4 : Fin 4374)
  | _ => (5 : Fin 4374)

abbrev decodeState :
    (Fin 10 -> Fin 6) -> Fin 4374 :=
  Shards.decodeState

theorem decodeState_stateVector (state : Fin 4374) :
    decodeState (stateVector state) = state :=
  Shards.decodeState_stateVector state

def generatorState
    (generator : Fin 6) :
    Fin 4374 :=
  ⟨generator.val, by omega⟩

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6988
