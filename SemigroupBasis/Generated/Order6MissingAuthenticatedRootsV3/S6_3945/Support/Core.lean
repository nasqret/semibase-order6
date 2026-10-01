import SemigroupBasis.FiniteNilpotentCounterexample
import SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3945.Shards.DecodeState
import SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3945.Shards.DecodeStateProof
import SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3945.Shards.RepresentativeHead
import SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3945.Shards.RepresentativeTail
import SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3945.Shards.SourceLabel
import SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3945.Shards.StateVector
import SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3945.Shards.Transition
import SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_3944
import SemigroupBasis.Nonfinite
import SemigroupBasis.Opposite
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3945

open SemigroupBasis

def routeManifestRowSHA256 : String := "7f3070d0f58152f8e444bd6033bf117aa4e18cbd69a6ff862d8824126d29fcc1"
def witnessRecordSHA256 : String := "c4b0ceeffede1bedcc6f19ff3f30bf5b9b164e4b9f3a754bfaecf8886510563a"
def transferComponentSHA256 : String := "c4b0ceeffede1bedcc6f19ff3f30bf5b9b164e4b9f3a754bfaecf8886510563a"
def powerCertificateSHA256 : String := "13777fea6f00991a540af76fa8294433e28ae11c1dc561705b884dbca9e16c9d"

private def row6
    (c0 c1 c2 c3 c4 c5 : Fin 6) (column : Fin 6) : Fin 6 :=
  if column = 0 then c0 else
    if column = 1 then c1 else
      if column = 2 then c2 else
        if column = 3 then c3 else
          if column = 4 then c4 else c5

/-- Exact one-based catalogue table committed by the portable witness. -/
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 0 0 0 0 right else
    if left = 1 then row6 0 0 0 0 1 1 right else
      if left = 2 then row6 0 0 0 1 1 2 right else
        if left = 3 then row6 0 0 0 0 3 3 right else
          if left = 4 then row6 0 1 2 0 4 4 right else
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
  "9ee4137a80966c4da996974897d408969b345e6c646bb07435e66583f8bf2e64"

def stateVector (state : Fin 1447)
    (coordinate : Fin 93) : Fin 6 :=
  Shards.stateVector state coordinate

def generatorVector (generator : Fin 4)
    (coordinate : Fin 93) : Fin 6 :=
  match generator.val with
  | 0 =>
      match coordinate.val with
      | 0 => (1 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (4 : Fin 6)
      | 5 => (3 : Fin 6)
      | 6 => (3 : Fin 6)
      | 7 => (3 : Fin 6)
      | 8 => (2 : Fin 6)
      | 9 => (0 : Fin 6)
      | 10 => (0 : Fin 6)
      | 11 => (0 : Fin 6)
      | 12 => (2 : Fin 6)
      | 13 => (0 : Fin 6)
      | 14 => (0 : Fin 6)
      | 15 => (0 : Fin 6)
      | 16 => (2 : Fin 6)
      | 17 => (0 : Fin 6)
      | 18 => (0 : Fin 6)
      | 19 => (0 : Fin 6)
      | 20 => (4 : Fin 6)
      | 21 => (4 : Fin 6)
      | 22 => (4 : Fin 6)
      | 23 => (4 : Fin 6)
      | 24 => (2 : Fin 6)
      | 25 => (4 : Fin 6)
      | 26 => (4 : Fin 6)
      | 27 => (4 : Fin 6)
      | 28 => (3 : Fin 6)
      | 29 => (2 : Fin 6)
      | 30 => (5 : Fin 6)
      | 31 => (2 : Fin 6)
      | 32 => (3 : Fin 6)
      | 33 => (5 : Fin 6)
      | 34 => (5 : Fin 6)
      | 35 => (2 : Fin 6)
      | 36 => (5 : Fin 6)
      | 37 => (4 : Fin 6)
      | 38 => (4 : Fin 6)
      | 39 => (5 : Fin 6)
      | 40 => (5 : Fin 6)
      | 41 => (4 : Fin 6)
      | 42 => (5 : Fin 6)
      | 43 => (5 : Fin 6)
      | 44 => (2 : Fin 6)
      | 45 => (3 : Fin 6)
      | 46 => (3 : Fin 6)
      | 47 => (4 : Fin 6)
      | 48 => (5 : Fin 6)
      | 49 => (4 : Fin 6)
      | 50 => (5 : Fin 6)
      | 51 => (4 : Fin 6)
      | 52 => (5 : Fin 6)
      | 53 => (5 : Fin 6)
      | 54 => (3 : Fin 6)
      | 55 => (4 : Fin 6)
      | 56 => (2 : Fin 6)
      | 57 => (3 : Fin 6)
      | 58 => (2 : Fin 6)
      | 59 => (3 : Fin 6)
      | 60 => (2 : Fin 6)
      | 61 => (5 : Fin 6)
      | 62 => (4 : Fin 6)
      | 63 => (4 : Fin 6)
      | 64 => (3 : Fin 6)
      | 65 => (4 : Fin 6)
      | 66 => (3 : Fin 6)
      | 67 => (4 : Fin 6)
      | 68 => (4 : Fin 6)
      | 69 => (4 : Fin 6)
      | 70 => (2 : Fin 6)
      | 71 => (5 : Fin 6)
      | 72 => (3 : Fin 6)
      | 73 => (5 : Fin 6)
      | 74 => (5 : Fin 6)
      | 75 => (2 : Fin 6)
      | 76 => (5 : Fin 6)
      | 77 => (3 : Fin 6)
      | 78 => (5 : Fin 6)
      | 79 => (2 : Fin 6)
      | 80 => (3 : Fin 6)
      | 81 => (2 : Fin 6)
      | 82 => (4 : Fin 6)
      | 83 => (3 : Fin 6)
      | 84 => (4 : Fin 6)
      | 85 => (4 : Fin 6)
      | 86 => (2 : Fin 6)
      | 87 => (4 : Fin 6)
      | 88 => (3 : Fin 6)
      | 89 => (4 : Fin 6)
      | 90 => (2 : Fin 6)
      | 91 => (3 : Fin 6)
      | _ => (2 : Fin 6)
  | 1 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (1 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (2 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (0 : Fin 6)
      | 8 => (3 : Fin 6)
      | 9 => (4 : Fin 6)
      | 10 => (3 : Fin 6)
      | 11 => (3 : Fin 6)
      | 12 => (0 : Fin 6)
      | 13 => (2 : Fin 6)
      | 14 => (0 : Fin 6)
      | 15 => (0 : Fin 6)
      | 16 => (0 : Fin 6)
      | 17 => (2 : Fin 6)
      | 18 => (0 : Fin 6)
      | 19 => (0 : Fin 6)
      | 20 => (3 : Fin 6)
      | 21 => (0 : Fin 6)
      | 22 => (0 : Fin 6)
      | 23 => (2 : Fin 6)
      | 24 => (4 : Fin 6)
      | 25 => (3 : Fin 6)
      | 26 => (3 : Fin 6)
      | 27 => (2 : Fin 6)
      | 28 => (2 : Fin 6)
      | 29 => (3 : Fin 6)
      | 30 => (4 : Fin 6)
      | 31 => (4 : Fin 6)
      | 32 => (5 : Fin 6)
      | 33 => (2 : Fin 6)
      | 34 => (5 : Fin 6)
      | 35 => (4 : Fin 6)
      | 36 => (4 : Fin 6)
      | 37 => (5 : Fin 6)
      | 38 => (3 : Fin 6)
      | 39 => (4 : Fin 6)
      | 40 => (5 : Fin 6)
      | 41 => (4 : Fin 6)
      | 42 => (2 : Fin 6)
      | 43 => (5 : Fin 6)
      | 44 => (5 : Fin 6)
      | 45 => (4 : Fin 6)
      | 46 => (5 : Fin 6)
      | 47 => (5 : Fin 6)
      | 48 => (5 : Fin 6)
      | 49 => (5 : Fin 6)
      | 50 => (3 : Fin 6)
      | 51 => (2 : Fin 6)
      | 52 => (3 : Fin 6)
      | 53 => (4 : Fin 6)
      | 54 => (4 : Fin 6)
      | 55 => (5 : Fin 6)
      | 56 => (4 : Fin 6)
      | 57 => (5 : Fin 6)
      | 58 => (5 : Fin 6)
      | 59 => (4 : Fin 6)
      | 60 => (4 : Fin 6)
      | 61 => (4 : Fin 6)
      | 62 => (4 : Fin 6)
      | 63 => (2 : Fin 6)
      | 64 => (2 : Fin 6)
      | 65 => (3 : Fin 6)
      | 66 => (4 : Fin 6)
      | 67 => (3 : Fin 6)
      | 68 => (2 : Fin 6)
      | 69 => (5 : Fin 6)
      | 70 => (5 : Fin 6)
      | 71 => (3 : Fin 6)
      | 72 => (5 : Fin 6)
      | 73 => (4 : Fin 6)
      | 74 => (2 : Fin 6)
      | 75 => (5 : Fin 6)
      | 76 => (3 : Fin 6)
      | 77 => (5 : Fin 6)
      | 78 => (2 : Fin 6)
      | 79 => (5 : Fin 6)
      | 80 => (2 : Fin 6)
      | 81 => (3 : Fin 6)
      | 82 => (3 : Fin 6)
      | 83 => (4 : Fin 6)
      | 84 => (5 : Fin 6)
      | 85 => (2 : Fin 6)
      | 86 => (4 : Fin 6)
      | 87 => (3 : Fin 6)
      | 88 => (4 : Fin 6)
      | 89 => (2 : Fin 6)
      | 90 => (4 : Fin 6)
      | 91 => (2 : Fin 6)
      | _ => (3 : Fin 6)
  | 2 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (1 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (2 : Fin 6)
      | 7 => (0 : Fin 6)
      | 8 => (0 : Fin 6)
      | 9 => (0 : Fin 6)
      | 10 => (2 : Fin 6)
      | 11 => (0 : Fin 6)
      | 12 => (3 : Fin 6)
      | 13 => (3 : Fin 6)
      | 14 => (4 : Fin 6)
      | 15 => (3 : Fin 6)
      | 16 => (0 : Fin 6)
      | 17 => (0 : Fin 6)
      | 18 => (2 : Fin 6)
      | 19 => (0 : Fin 6)
      | 20 => (0 : Fin 6)
      | 21 => (3 : Fin 6)
      | 22 => (0 : Fin 6)
      | 23 => (0 : Fin 6)
      | 24 => (0 : Fin 6)
      | 25 => (2 : Fin 6)
      | 26 => (1 : Fin 6)
      | 27 => (3 : Fin 6)
      | 28 => (5 : Fin 6)
      | 29 => (4 : Fin 6)
      | 30 => (3 : Fin 6)
      | 31 => (4 : Fin 6)
      | 32 => (2 : Fin 6)
      | 33 => (5 : Fin 6)
      | 34 => (4 : Fin 6)
      | 35 => (5 : Fin 6)
      | 36 => (2 : Fin 6)
      | 37 => (5 : Fin 6)
      | 38 => (5 : Fin 6)
      | 39 => (5 : Fin 6)
      | 40 => (2 : Fin 6)
      | 41 => (3 : Fin 6)
      | 42 => (4 : Fin 6)
      | 43 => (4 : Fin 6)
      | 44 => (4 : Fin 6)
      | 45 => (5 : Fin 6)
      | 46 => (4 : Fin 6)
      | 47 => (5 : Fin 6)
      | 48 => (3 : Fin 6)
      | 49 => (2 : Fin 6)
      | 50 => (5 : Fin 6)
      | 51 => (5 : Fin 6)
      | 52 => (4 : Fin 6)
      | 53 => (5 : Fin 6)
      | 54 => (5 : Fin 6)
      | 55 => (3 : Fin 6)
      | 56 => (3 : Fin 6)
      | 57 => (5 : Fin 6)
      | 58 => (4 : Fin 6)
      | 59 => (2 : Fin 6)
      | 60 => (5 : Fin 6)
      | 61 => (3 : Fin 6)
      | 62 => (2 : Fin 6)
      | 63 => (4 : Fin 6)
      | 64 => (4 : Fin 6)
      | 65 => (4 : Fin 6)
      | 66 => (4 : Fin 6)
      | 67 => (2 : Fin 6)
      | 68 => (3 : Fin 6)
      | 69 => (3 : Fin 6)
      | 70 => (5 : Fin 6)
      | 71 => (4 : Fin 6)
      | 72 => (4 : Fin 6)
      | 73 => (2 : Fin 6)
      | 74 => (4 : Fin 6)
      | 75 => (4 : Fin 6)
      | 76 => (2 : Fin 6)
      | 77 => (2 : Fin 6)
      | 78 => (3 : Fin 6)
      | 79 => (3 : Fin 6)
      | 80 => (5 : Fin 6)
      | 81 => (5 : Fin 6)
      | 82 => (5 : Fin 6)
      | 83 => (5 : Fin 6)
      | 84 => (2 : Fin 6)
      | 85 => (5 : Fin 6)
      | 86 => (5 : Fin 6)
      | 87 => (2 : Fin 6)
      | 88 => (2 : Fin 6)
      | 89 => (3 : Fin 6)
      | 90 => (3 : Fin 6)
      | 91 => (4 : Fin 6)
      | _ => (4 : Fin 6)
  | _ =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (1 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (2 : Fin 6)
      | 8 => (0 : Fin 6)
      | 9 => (0 : Fin 6)
      | 10 => (0 : Fin 6)
      | 11 => (2 : Fin 6)
      | 12 => (0 : Fin 6)
      | 13 => (0 : Fin 6)
      | 14 => (0 : Fin 6)
      | 15 => (2 : Fin 6)
      | 16 => (3 : Fin 6)
      | 17 => (3 : Fin 6)
      | 18 => (3 : Fin 6)
      | 19 => (4 : Fin 6)
      | 20 => (0 : Fin 6)
      | 21 => (0 : Fin 6)
      | 22 => (3 : Fin 6)
      | 23 => (0 : Fin 6)
      | 24 => (0 : Fin 6)
      | 25 => (0 : Fin 6)
      | 26 => (2 : Fin 6)
      | 27 => (1 : Fin 6)
      | 28 => (0 : Fin 6)
      | 29 => (4 : Fin 6)
      | 30 => (2 : Fin 6)
      | 31 => (3 : Fin 6)
      | 32 => (5 : Fin 6)
      | 33 => (4 : Fin 6)
      | 34 => (2 : Fin 6)
      | 35 => (4 : Fin 6)
      | 36 => (5 : Fin 6)
      | 37 => (3 : Fin 6)
      | 38 => (5 : Fin 6)
      | 39 => (3 : Fin 6)
      | 40 => (4 : Fin 6)
      | 41 => (5 : Fin 6)
      | 42 => (5 : Fin 6)
      | 43 => (3 : Fin 6)
      | 44 => (4 : Fin 6)
      | 45 => (4 : Fin 6)
      | 46 => (5 : Fin 6)
      | 47 => (2 : Fin 6)
      | 48 => (4 : Fin 6)
      | 49 => (5 : Fin 6)
      | 50 => (4 : Fin 6)
      | 51 => (5 : Fin 6)
      | 52 => (5 : Fin 6)
      | 53 => (2 : Fin 6)
      | 54 => (5 : Fin 6)
      | 55 => (5 : Fin 6)
      | 56 => (4 : Fin 6)
      | 57 => (4 : Fin 6)
      | 58 => (5 : Fin 6)
      | 59 => (4 : Fin 6)
      | 60 => (5 : Fin 6)
      | 61 => (5 : Fin 6)
      | 62 => (3 : Fin 6)
      | 63 => (3 : Fin 6)
      | 64 => (4 : Fin 6)
      | 65 => (2 : Fin 6)
      | 66 => (2 : Fin 6)
      | 67 => (4 : Fin 6)
      | 68 => (4 : Fin 6)
      | 69 => (2 : Fin 6)
      | 70 => (4 : Fin 6)
      | 71 => (2 : Fin 6)
      | 72 => (2 : Fin 6)
      | 73 => (3 : Fin 6)
      | 74 => (3 : Fin 6)
      | 75 => (3 : Fin 6)
      | 76 => (4 : Fin 6)
      | 77 => (4 : Fin 6)
      | 78 => (4 : Fin 6)
      | 79 => (4 : Fin 6)
      | 80 => (4 : Fin 6)
      | 81 => (4 : Fin 6)
      | 82 => (2 : Fin 6)
      | 83 => (2 : Fin 6)
      | 84 => (3 : Fin 6)
      | 85 => (3 : Fin 6)
      | 86 => (3 : Fin 6)
      | 87 => (5 : Fin 6)
      | 88 => (5 : Fin 6)
      | 89 => (5 : Fin 6)
      | 90 => (5 : Fin 6)
      | 91 => (5 : Fin 6)
      | _ => (5 : Fin 6)

def transition (state : Fin 1447)
    (generator : Fin 4) : Fin 1447 :=
  Shards.transition state generator

def representativeHead (state : Fin 1447) : Fin 4 :=
  Shards.representativeHead state

def representativeTail (state : Fin 1447) :
    List (Fin 4) :=
  Shards.representativeTail state

def sourceLabel (state : Fin 1447) : Fin 6 :=
  Shards.sourceLabel state

def generatorSourceLabel (generator : Fin 4) : Fin 6 :=
  match generator.val with
  | 0 => (5 : Fin 6)
  | 1 => (4 : Fin 6)
  | 2 => (3 : Fin 6)
  | _ => (2 : Fin 6)

def sourcePreimage (value : Fin 6) : Fin 1447 :=
  match value.val with
  | 0 => (11 : Fin 1447)
  | 1 => (15 : Fin 1447)
  | 2 => (3 : Fin 1447)
  | 3 => (2 : Fin 1447)
  | 4 => (1 : Fin 1447)
  | _ => (0 : Fin 1447)

abbrev decodeState :
    (Fin 93 -> Fin 6) -> Fin 1447 :=
  Shards.decodeState

theorem decodeState_stateVector (state : Fin 1447) :
    decodeState (stateVector state) = state :=
  Shards.decodeState_stateVector state

def generatorState
    (generator : Fin 4) :
    Fin 1447 :=
  ⟨generator.val, by omega⟩

end SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3945
