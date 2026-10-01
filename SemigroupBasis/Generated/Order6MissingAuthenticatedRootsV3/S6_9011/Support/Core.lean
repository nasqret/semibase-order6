import SemigroupBasis.FiniteNilpotentCounterexample
import SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.Shards.DecodeState
import SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.Shards.DecodeStateProof
import SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.Shards.RepresentativeHead
import SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.Shards.RepresentativeTail
import SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.Shards.SourceLabel
import SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.Shards.StateVector
import SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.Shards.Transition
import SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_11390
import SemigroupBasis.Nonfinite
import SemigroupBasis.Opposite
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011

open SemigroupBasis

def routeManifestRowSHA256 : String := "3a4645023897a4bc05eea06f73bd68a7417737eed497f531a22549fa390bbc52"
def witnessRecordSHA256 : String := "fc1a36521ad4f72e83caad59fafa10ea5c02e1b2ad46331a7a8a6a6e8c7f0934"
def transferComponentSHA256 : String := "fc1a36521ad4f72e83caad59fafa10ea5c02e1b2ad46331a7a8a6a6e8c7f0934"
def powerCertificateSHA256 : String := "a8fef1e36ede15d2b5ae5f332cbea25c65f1dcb037cff705b880c297450acb69"

private def row6
    (c0 c1 c2 c3 c4 c5 : Fin 6) (column : Fin 6) : Fin 6 :=
  if column = 0 then c0 else
    if column = 1 then c1 else
      if column = 2 then c2 else
        if column = 3 then c3 else
          if column = 4 then c4 else c5

/-- Exact one-based catalogue table committed by the portable witness. -/
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 1 1 0 0 0 right else
    if left = 1 then row6 1 0 0 1 1 1 right else
      if left = 2 then row6 1 0 0 2 2 2 right else
        if left = 3 then row6 0 1 1 3 3 3 right else
          if left = 4 then row6 0 1 1 4 4 4 right else
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
  "afc1a6e07c1e0c680314f0bf69951de6d3cdf40db643eeee73e8177e87ebed5b"

def stateVector (state : Fin 2712)
    (coordinate : Fin 17) : Fin 6 :=
  Shards.stateVector state coordinate

def generatorVector (generator : Fin 4)
    (coordinate : Fin 17) : Fin 6 :=
  match generator.val with
  | 0 =>
      match coordinate.val with
      | 0 => (2 : Fin 6)
      | 1 => (3 : Fin 6)
      | 2 => (4 : Fin 6)
      | 3 => (3 : Fin 6)
      | 4 => (4 : Fin 6)
      | 5 => (3 : Fin 6)
      | 6 => (2 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (4 : Fin 6)
      | 10 => (5 : Fin 6)
      | 11 => (5 : Fin 6)
      | 12 => (5 : Fin 6)
      | 13 => (4 : Fin 6)
      | 14 => (5 : Fin 6)
      | 15 => (5 : Fin 6)
      | _ => (4 : Fin 6)
  | 1 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (2 : Fin 6)
      | 2 => (3 : Fin 6)
      | 3 => (4 : Fin 6)
      | 4 => (3 : Fin 6)
      | 5 => (2 : Fin 6)
      | 6 => (5 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (5 : Fin 6)
      | 10 => (4 : Fin 6)
      | 11 => (5 : Fin 6)
      | 12 => (2 : Fin 6)
      | 13 => (5 : Fin 6)
      | 14 => (5 : Fin 6)
      | 15 => (4 : Fin 6)
      | _ => (3 : Fin 6)
  | 2 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (2 : Fin 6)
      | 3 => (3 : Fin 6)
      | 4 => (2 : Fin 6)
      | 5 => (5 : Fin 6)
      | 6 => (5 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (3 : Fin 6)
      | 10 => (3 : Fin 6)
      | 11 => (5 : Fin 6)
      | 12 => (5 : Fin 6)
      | 13 => (5 : Fin 6)
      | 14 => (2 : Fin 6)
      | 15 => (5 : Fin 6)
      | _ => (5 : Fin 6)
  | _ =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (5 : Fin 6)
      | 5 => (5 : Fin 6)
      | 6 => (5 : Fin 6)
      | 7 => (3 : Fin 6)
      | 8 => (3 : Fin 6)
      | 9 => (5 : Fin 6)
      | 10 => (5 : Fin 6)
      | 11 => (2 : Fin 6)
      | 12 => (5 : Fin 6)
      | 13 => (3 : Fin 6)
      | 14 => (5 : Fin 6)
      | 15 => (3 : Fin 6)
      | _ => (5 : Fin 6)

def transition (state : Fin 2712)
    (generator : Fin 4) : Fin 2712 :=
  Shards.transition state generator

def representativeHead (state : Fin 2712) : Fin 4 :=
  Shards.representativeHead state

def representativeTail (state : Fin 2712) :
    List (Fin 4) :=
  Shards.representativeTail state

def sourceLabel (state : Fin 2712) : Fin 6 :=
  Shards.sourceLabel state

def generatorSourceLabel (generator : Fin 4) : Fin 6 :=
  match generator.val with
  | 0 => (5 : Fin 6)
  | 1 => (4 : Fin 6)
  | 2 => (3 : Fin 6)
  | _ => (1 : Fin 6)

def sourcePreimage (value : Fin 6) : Fin 2712 :=
  match value.val with
  | 0 => (16 : Fin 2712)
  | 1 => (3 : Fin 2712)
  | 2 => (14 : Fin 2712)
  | 3 => (2 : Fin 2712)
  | 4 => (1 : Fin 2712)
  | _ => (0 : Fin 2712)

abbrev decodeState :
    (Fin 17 -> Fin 6) -> Fin 2712 :=
  Shards.decodeState

theorem decodeState_stateVector (state : Fin 2712) :
    decodeState (stateVector state) = state :=
  Shards.decodeState_stateVector state

def generatorState
    (generator : Fin 4) :
    Fin 2712 :=
  ⟨generator.val, by omega⟩

end SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011
