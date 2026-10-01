import SemigroupBasis.FiniteNilpotentCounterexample
import SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6196Representative
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.Shards.DecodeState
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.Shards.DecodeStateProof
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.Shards.RepresentativeHead
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.Shards.RepresentativeTail
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.Shards.SourceLabel
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.Shards.StateVector
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.Shards.Transition
import SemigroupBasis.Nonfinite
import SemigroupBasis.Opposite
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841

open SemigroupBasis

def routeManifestRowSHA256 : String := "d7c90d31448a4946fc34d9f597e0259e11e2bd7302109898d6cd1d85c43e8832"
def witnessRecordSHA256 : String := "8c06fbbd6dc5860d82d9eb8e225f130a0a129d31bc6ae4b46e3b4de6fa1c8629"
def transferComponentSHA256 : String := "8c06fbbd6dc5860d82d9eb8e225f130a0a129d31bc6ae4b46e3b4de6fa1c8629"
def powerCertificateSHA256 : String := "42147d33dfaa2d529f2cdaa2fba481cf5fcc08245bf4354d86a3edc8cf482aa2"

private def row6
    (c0 c1 c2 c3 c4 c5 : Fin 6) (column : Fin 6) : Fin 6 :=
  if column = 0 then c0 else
    if column = 1 then c1 else
      if column = 2 then c2 else
        if column = 3 then c3 else
          if column = 4 then c4 else c5

/-- Exact one-based catalogue table committed by the portable witness. -/
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 2 3 4 0 right else
    if left = 1 then row6 0 0 2 3 4 0 right else
      if left = 2 then row6 2 2 0 4 3 2 right else
        if left = 3 then row6 0 0 2 3 4 0 right else
          if left = 4 then row6 2 2 0 4 3 2 right else
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
  "074bfaab7a16175fb3ed790a1cc1089a1ba9bfc4cb8ab202c5039a4b679c6c27"

def stateVector (state : Fin 4374)
    (coordinate : Fin 28) : Fin 6 :=
  Shards.stateVector state coordinate

def generatorVector (generator : Fin 6)
    (coordinate : Fin 28) : Fin 6 :=
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
      | 8 => (1 : Fin 6)
      | 9 => (5 : Fin 6)
      | 10 => (5 : Fin 6)
      | 11 => (5 : Fin 6)
      | 12 => (5 : Fin 6)
      | 13 => (5 : Fin 6)
      | 14 => (5 : Fin 6)
      | 15 => (5 : Fin 6)
      | 16 => (5 : Fin 6)
      | 17 => (2 : Fin 6)
      | 18 => (0 : Fin 6)
      | 19 => (0 : Fin 6)
      | 20 => (0 : Fin 6)
      | 21 => (0 : Fin 6)
      | 22 => (0 : Fin 6)
      | 23 => (3 : Fin 6)
      | 24 => (0 : Fin 6)
      | 25 => (0 : Fin 6)
      | 26 => (0 : Fin 6)
      | _ => (0 : Fin 6)
  | 1 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (1 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (5 : Fin 6)
      | 10 => (5 : Fin 6)
      | 11 => (1 : Fin 6)
      | 12 => (5 : Fin 6)
      | 13 => (5 : Fin 6)
      | 14 => (5 : Fin 6)
      | 15 => (5 : Fin 6)
      | 16 => (5 : Fin 6)
      | 17 => (0 : Fin 6)
      | 18 => (2 : Fin 6)
      | 19 => (0 : Fin 6)
      | 20 => (0 : Fin 6)
      | 21 => (0 : Fin 6)
      | 22 => (0 : Fin 6)
      | 23 => (0 : Fin 6)
      | 24 => (3 : Fin 6)
      | 25 => (0 : Fin 6)
      | 26 => (0 : Fin 6)
      | _ => (0 : Fin 6)
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
      | 10 => (0 : Fin 6)
      | 11 => (5 : Fin 6)
      | 12 => (5 : Fin 6)
      | 13 => (0 : Fin 6)
      | 14 => (5 : Fin 6)
      | 15 => (1 : Fin 6)
      | 16 => (5 : Fin 6)
      | 17 => (0 : Fin 6)
      | 18 => (0 : Fin 6)
      | 19 => (2 : Fin 6)
      | 20 => (0 : Fin 6)
      | 21 => (0 : Fin 6)
      | 22 => (0 : Fin 6)
      | 23 => (0 : Fin 6)
      | 24 => (0 : Fin 6)
      | 25 => (3 : Fin 6)
      | 26 => (0 : Fin 6)
      | _ => (0 : Fin 6)
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
      | 8 => (5 : Fin 6)
      | 9 => (0 : Fin 6)
      | 10 => (5 : Fin 6)
      | 11 => (5 : Fin 6)
      | 12 => (5 : Fin 6)
      | 13 => (0 : Fin 6)
      | 14 => (5 : Fin 6)
      | 15 => (5 : Fin 6)
      | 16 => (1 : Fin 6)
      | 17 => (0 : Fin 6)
      | 18 => (0 : Fin 6)
      | 19 => (0 : Fin 6)
      | 20 => (2 : Fin 6)
      | 21 => (0 : Fin 6)
      | 22 => (0 : Fin 6)
      | 23 => (0 : Fin 6)
      | 24 => (0 : Fin 6)
      | 25 => (0 : Fin 6)
      | 26 => (3 : Fin 6)
      | _ => (0 : Fin 6)
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
      | 8 => (5 : Fin 6)
      | 9 => (0 : Fin 6)
      | 10 => (0 : Fin 6)
      | 11 => (5 : Fin 6)
      | 12 => (5 : Fin 6)
      | 13 => (5 : Fin 6)
      | 14 => (1 : Fin 6)
      | 15 => (5 : Fin 6)
      | 16 => (5 : Fin 6)
      | 17 => (0 : Fin 6)
      | 18 => (0 : Fin 6)
      | 19 => (0 : Fin 6)
      | 20 => (0 : Fin 6)
      | 21 => (2 : Fin 6)
      | 22 => (0 : Fin 6)
      | 23 => (0 : Fin 6)
      | 24 => (0 : Fin 6)
      | 25 => (0 : Fin 6)
      | 26 => (0 : Fin 6)
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
      | 7 => (5 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (5 : Fin 6)
      | 10 => (5 : Fin 6)
      | 11 => (5 : Fin 6)
      | 12 => (1 : Fin 6)
      | 13 => (5 : Fin 6)
      | 14 => (5 : Fin 6)
      | 15 => (5 : Fin 6)
      | 16 => (5 : Fin 6)
      | 17 => (0 : Fin 6)
      | 18 => (0 : Fin 6)
      | 19 => (0 : Fin 6)
      | 20 => (0 : Fin 6)
      | 21 => (0 : Fin 6)
      | 22 => (2 : Fin 6)
      | 23 => (0 : Fin 6)
      | 24 => (0 : Fin 6)
      | 25 => (0 : Fin 6)
      | 26 => (0 : Fin 6)
      | _ => (0 : Fin 6)

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
    (Fin 28 -> Fin 6) -> Fin 4374 :=
  Shards.decodeState

theorem decodeState_stateVector (state : Fin 4374) :
    decodeState (stateVector state) = state :=
  Shards.decodeState_stateVector state

def generatorState
    (generator : Fin 6) :
    Fin 4374 :=
  ⟨generator.val, by omega⟩

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841
