import SemigroupBasis.FiniteNilpotentCounterexample
import SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.Shards.DecodeState
import SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.Shards.DecodeStateProof
import SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.Shards.RepresentativeHead
import SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.Shards.RepresentativeTail
import SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.Shards.SourceLabel
import SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.Shards.StateVector
import SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.Shards.Transition
import SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_11390
import SemigroupBasis.Nonfinite
import SemigroupBasis.Opposite
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867

open SemigroupBasis

def routeManifestRowSHA256 : String := "ed7d5e2c06695661f3258bd54ad0152ccdcb6d58503a00fbd3832cf2145e0ce3"
def witnessRecordSHA256 : String := "b26eddbffc0271b25b63630048e4774e388ec2aae28073d7fa1a8d07e5ebce4a"
def transferComponentSHA256 : String := "b26eddbffc0271b25b63630048e4774e388ec2aae28073d7fa1a8d07e5ebce4a"
def powerCertificateSHA256 : String := "e73e09f07c7c80b9a78681b9cc11e3a150d006330e655cb4452e24d2723ced21"

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
    if left = 1 then row6 0 0 2 1 1 1 right else
      if left = 2 then row6 2 2 0 2 2 2 right else
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
  "f01cafef58cfe587655837ae4acb91ccca44086177301030cb9ab539bfcac51b"

def stateVector (state : Fin 2712)
    (coordinate : Fin 29) : Fin 6 :=
  Shards.stateVector state coordinate

def generatorVector (generator : Fin 4)
    (coordinate : Fin 29) : Fin 6 :=
  match generator.val with
  | 0 =>
      match coordinate.val with
      | 0 => (1 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (3 : Fin 6)
      | 5 => (3 : Fin 6)
      | 6 => (3 : Fin 6)
      | 7 => (3 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (2 : Fin 6)
      | 10 => (1 : Fin 6)
      | 11 => (1 : Fin 6)
      | 12 => (5 : Fin 6)
      | 13 => (3 : Fin 6)
      | 14 => (4 : Fin 6)
      | 15 => (3 : Fin 6)
      | 16 => (5 : Fin 6)
      | 17 => (1 : Fin 6)
      | 18 => (5 : Fin 6)
      | 19 => (5 : Fin 6)
      | 20 => (4 : Fin 6)
      | 21 => (5 : Fin 6)
      | 22 => (5 : Fin 6)
      | 23 => (5 : Fin 6)
      | 24 => (1 : Fin 6)
      | 25 => (5 : Fin 6)
      | 26 => (4 : Fin 6)
      | 27 => (4 : Fin 6)
      | _ => (4 : Fin 6)
  | 1 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (1 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (1 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (0 : Fin 6)
      | 8 => (1 : Fin 6)
      | 9 => (3 : Fin 6)
      | 10 => (1 : Fin 6)
      | 11 => (1 : Fin 6)
      | 12 => (4 : Fin 6)
      | 13 => (1 : Fin 6)
      | 14 => (3 : Fin 6)
      | 15 => (5 : Fin 6)
      | 16 => (2 : Fin 6)
      | 17 => (5 : Fin 6)
      | 18 => (4 : Fin 6)
      | 19 => (5 : Fin 6)
      | 20 => (5 : Fin 6)
      | 21 => (1 : Fin 6)
      | 22 => (4 : Fin 6)
      | 23 => (5 : Fin 6)
      | 24 => (5 : Fin 6)
      | 25 => (5 : Fin 6)
      | 26 => (3 : Fin 6)
      | 27 => (3 : Fin 6)
      | _ => (5 : Fin 6)
  | 2 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (1 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (1 : Fin 6)
      | 7 => (0 : Fin 6)
      | 8 => (0 : Fin 6)
      | 9 => (0 : Fin 6)
      | 10 => (5 : Fin 6)
      | 11 => (2 : Fin 6)
      | 12 => (3 : Fin 6)
      | 13 => (5 : Fin 6)
      | 14 => (1 : Fin 6)
      | 15 => (5 : Fin 6)
      | 16 => (1 : Fin 6)
      | 17 => (5 : Fin 6)
      | 18 => (5 : Fin 6)
      | 19 => (4 : Fin 6)
      | 20 => (3 : Fin 6)
      | 21 => (5 : Fin 6)
      | 22 => (3 : Fin 6)
      | 23 => (5 : Fin 6)
      | 24 => (5 : Fin 6)
      | 25 => (1 : Fin 6)
      | 26 => (5 : Fin 6)
      | 27 => (5 : Fin 6)
      | _ => (5 : Fin 6)
  | _ =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (1 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (1 : Fin 6)
      | 8 => (0 : Fin 6)
      | 9 => (0 : Fin 6)
      | 10 => (0 : Fin 6)
      | 11 => (5 : Fin 6)
      | 12 => (1 : Fin 6)
      | 13 => (5 : Fin 6)
      | 14 => (5 : Fin 6)
      | 15 => (1 : Fin 6)
      | 16 => (2 : Fin 6)
      | 17 => (3 : Fin 6)
      | 18 => (3 : Fin 6)
      | 19 => (3 : Fin 6)
      | 20 => (5 : Fin 6)
      | 21 => (5 : Fin 6)
      | 22 => (5 : Fin 6)
      | 23 => (1 : Fin 6)
      | 24 => (5 : Fin 6)
      | 25 => (5 : Fin 6)
      | 26 => (2 : Fin 6)
      | 27 => (5 : Fin 6)
      | _ => (3 : Fin 6)

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
    (Fin 29 -> Fin 6) -> Fin 2712 :=
  Shards.decodeState

theorem decodeState_stateVector (state : Fin 2712) :
    decodeState (stateVector state) = state :=
  Shards.decodeState_stateVector state

def generatorState
    (generator : Fin 4) :
    Fin 2712 :=
  ⟨generator.val, by omega⟩

end SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867
