import SemigroupBasis.FiniteNilpotentCounterexample
import SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Representative
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14221.Shards.DecodeState
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14221.Shards.DecodeStateProof
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14221.Shards.RepresentativeHead
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14221.Shards.RepresentativeTail
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14221.Shards.SourceLabel
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14221.Shards.StateVector
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14221.Shards.Transition
import SemigroupBasis.Nonfinite
import SemigroupBasis.Opposite
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14221

open SemigroupBasis

def routeManifestRowSHA256 : String := "6d2cf9f117fa3e3761342188f8d207b4f27c57fc852a9e64ae2b631fab7e2839"
def witnessRecordSHA256 : String := "83dc7d10c99511dc5a7e49249a605c933a81b4ccd2951ce7ce85ce849204d058"
def transferComponentSHA256 : String := "83dc7d10c99511dc5a7e49249a605c933a81b4ccd2951ce7ce85ce849204d058"
def powerCertificateSHA256 : String := "557266dc78f9ced2c3809f33ae5b981bc190e2cca880311c26e04feb1358e9a2"

private def row6
    (c0 c1 c2 c3 c4 c5 : Fin 6) (column : Fin 6) : Fin 6 :=
  if column = 0 then c0 else
    if column = 1 then c1 else
      if column = 2 then c2 else
        if column = 3 then c3 else
          if column = 4 then c4 else c5

/-- Exact one-based catalogue table committed by the portable witness. -/
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 0 3 4 4 right else
    if left = 1 then row6 0 0 1 3 4 4 right else
      if left = 2 then row6 0 0 2 3 4 4 right else
        if left = 3 then row6 0 0 3 3 4 4 right else
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
  "4dbc28f7c9c530348b2df7e08416cde1b5391680ce758084ca7a4eb6b22c42a8"

def stateVector (state : Fin 11742)
    (coordinate : Fin 53) : Fin 6 :=
  Shards.stateVector state coordinate

def generatorVector (generator : Fin 6)
    (coordinate : Fin 53) : Fin 6 :=
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
      | 14 => (2 : Fin 6)
      | 15 => (3 : Fin 6)
      | 16 => (2 : Fin 6)
      | 17 => (2 : Fin 6)
      | 18 => (2 : Fin 6)
      | 19 => (5 : Fin 6)
      | 20 => (0 : Fin 6)
      | 21 => (0 : Fin 6)
      | 22 => (3 : Fin 6)
      | 23 => (2 : Fin 6)
      | 24 => (2 : Fin 6)
      | 25 => (2 : Fin 6)
      | 26 => (0 : Fin 6)
      | 27 => (0 : Fin 6)
      | 28 => (2 : Fin 6)
      | 29 => (0 : Fin 6)
      | 30 => (0 : Fin 6)
      | 31 => (3 : Fin 6)
      | 32 => (2 : Fin 6)
      | 33 => (2 : Fin 6)
      | 34 => (2 : Fin 6)
      | 35 => (2 : Fin 6)
      | 36 => (2 : Fin 6)
      | 37 => (2 : Fin 6)
      | 38 => (1 : Fin 6)
      | 39 => (2 : Fin 6)
      | 40 => (3 : Fin 6)
      | 41 => (0 : Fin 6)
      | 42 => (3 : Fin 6)
      | 43 => (2 : Fin 6)
      | 44 => (3 : Fin 6)
      | 45 => (2 : Fin 6)
      | 46 => (2 : Fin 6)
      | 47 => (2 : Fin 6)
      | 48 => (2 : Fin 6)
      | 49 => (3 : Fin 6)
      | 50 => (2 : Fin 6)
      | 51 => (2 : Fin 6)
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
      | 7 => (1 : Fin 6)
      | 8 => (0 : Fin 6)
      | 9 => (0 : Fin 6)
      | 10 => (0 : Fin 6)
      | 11 => (2 : Fin 6)
      | 12 => (2 : Fin 6)
      | 13 => (2 : Fin 6)
      | 14 => (3 : Fin 6)
      | 15 => (2 : Fin 6)
      | 16 => (2 : Fin 6)
      | 17 => (2 : Fin 6)
      | 18 => (2 : Fin 6)
      | 19 => (0 : Fin 6)
      | 20 => (5 : Fin 6)
      | 21 => (0 : Fin 6)
      | 22 => (0 : Fin 6)
      | 23 => (2 : Fin 6)
      | 24 => (2 : Fin 6)
      | 25 => (3 : Fin 6)
      | 26 => (0 : Fin 6)
      | 27 => (2 : Fin 6)
      | 28 => (2 : Fin 6)
      | 29 => (2 : Fin 6)
      | 30 => (0 : Fin 6)
      | 31 => (0 : Fin 6)
      | 32 => (2 : Fin 6)
      | 33 => (3 : Fin 6)
      | 34 => (2 : Fin 6)
      | 35 => (2 : Fin 6)
      | 36 => (3 : Fin 6)
      | 37 => (2 : Fin 6)
      | 38 => (2 : Fin 6)
      | 39 => (1 : Fin 6)
      | 40 => (2 : Fin 6)
      | 41 => (3 : Fin 6)
      | 42 => (2 : Fin 6)
      | 43 => (2 : Fin 6)
      | 44 => (2 : Fin 6)
      | 45 => (3 : Fin 6)
      | 46 => (3 : Fin 6)
      | 47 => (2 : Fin 6)
      | 48 => (2 : Fin 6)
      | 49 => (0 : Fin 6)
      | 50 => (3 : Fin 6)
      | 51 => (3 : Fin 6)
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
      | 8 => (1 : Fin 6)
      | 9 => (0 : Fin 6)
      | 10 => (0 : Fin 6)
      | 11 => (0 : Fin 6)
      | 12 => (1 : Fin 6)
      | 13 => (0 : Fin 6)
      | 14 => (2 : Fin 6)
      | 15 => (2 : Fin 6)
      | 16 => (0 : Fin 6)
      | 17 => (2 : Fin 6)
      | 18 => (1 : Fin 6)
      | 19 => (0 : Fin 6)
      | 20 => (0 : Fin 6)
      | 21 => (0 : Fin 6)
      | 22 => (0 : Fin 6)
      | 23 => (3 : Fin 6)
      | 24 => (2 : Fin 6)
      | 25 => (0 : Fin 6)
      | 26 => (5 : Fin 6)
      | 27 => (2 : Fin 6)
      | 28 => (2 : Fin 6)
      | 29 => (3 : Fin 6)
      | 30 => (0 : Fin 6)
      | 31 => (2 : Fin 6)
      | 32 => (3 : Fin 6)
      | 33 => (0 : Fin 6)
      | 34 => (2 : Fin 6)
      | 35 => (2 : Fin 6)
      | 36 => (2 : Fin 6)
      | 37 => (2 : Fin 6)
      | 38 => (2 : Fin 6)
      | 39 => (2 : Fin 6)
      | 40 => (2 : Fin 6)
      | 41 => (2 : Fin 6)
      | 42 => (2 : Fin 6)
      | 43 => (3 : Fin 6)
      | 44 => (0 : Fin 6)
      | 45 => (0 : Fin 6)
      | 46 => (2 : Fin 6)
      | 47 => (3 : Fin 6)
      | 48 => (3 : Fin 6)
      | 49 => (2 : Fin 6)
      | 50 => (0 : Fin 6)
      | 51 => (2 : Fin 6)
      | _ => (2 : Fin 6)
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
      | 13 => (2 : Fin 6)
      | 14 => (0 : Fin 6)
      | 15 => (2 : Fin 6)
      | 16 => (2 : Fin 6)
      | 17 => (1 : Fin 6)
      | 18 => (2 : Fin 6)
      | 19 => (0 : Fin 6)
      | 20 => (0 : Fin 6)
      | 21 => (0 : Fin 6)
      | 22 => (0 : Fin 6)
      | 23 => (0 : Fin 6)
      | 24 => (3 : Fin 6)
      | 25 => (2 : Fin 6)
      | 26 => (0 : Fin 6)
      | 27 => (3 : Fin 6)
      | 28 => (2 : Fin 6)
      | 29 => (2 : Fin 6)
      | 30 => (5 : Fin 6)
      | 31 => (2 : Fin 6)
      | 32 => (0 : Fin 6)
      | 33 => (2 : Fin 6)
      | 34 => (3 : Fin 6)
      | 35 => (2 : Fin 6)
      | 36 => (0 : Fin 6)
      | 37 => (2 : Fin 6)
      | 38 => (2 : Fin 6)
      | 39 => (2 : Fin 6)
      | 40 => (2 : Fin 6)
      | 41 => (2 : Fin 6)
      | 42 => (0 : Fin 6)
      | 43 => (2 : Fin 6)
      | 44 => (2 : Fin 6)
      | 45 => (0 : Fin 6)
      | 46 => (2 : Fin 6)
      | 47 => (2 : Fin 6)
      | 48 => (0 : Fin 6)
      | 49 => (2 : Fin 6)
      | 50 => (2 : Fin 6)
      | 51 => (0 : Fin 6)
      | _ => (2 : Fin 6)
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
      | 10 => (2 : Fin 6)
      | 11 => (0 : Fin 6)
      | 12 => (0 : Fin 6)
      | 13 => (3 : Fin 6)
      | 14 => (0 : Fin 6)
      | 15 => (2 : Fin 6)
      | 16 => (2 : Fin 6)
      | 17 => (2 : Fin 6)
      | 18 => (2 : Fin 6)
      | 19 => (0 : Fin 6)
      | 20 => (0 : Fin 6)
      | 21 => (5 : Fin 6)
      | 22 => (2 : Fin 6)
      | 23 => (2 : Fin 6)
      | 24 => (2 : Fin 6)
      | 25 => (2 : Fin 6)
      | 26 => (0 : Fin 6)
      | 27 => (0 : Fin 6)
      | 28 => (3 : Fin 6)
      | 29 => (2 : Fin 6)
      | 30 => (0 : Fin 6)
      | 31 => (0 : Fin 6)
      | 32 => (0 : Fin 6)
      | 33 => (0 : Fin 6)
      | 34 => (0 : Fin 6)
      | 35 => (2 : Fin 6)
      | 36 => (2 : Fin 6)
      | 37 => (1 : Fin 6)
      | 38 => (2 : Fin 6)
      | 39 => (2 : Fin 6)
      | 40 => (0 : Fin 6)
      | 41 => (2 : Fin 6)
      | 42 => (2 : Fin 6)
      | 43 => (0 : Fin 6)
      | 44 => (2 : Fin 6)
      | 45 => (2 : Fin 6)
      | 46 => (0 : Fin 6)
      | 47 => (2 : Fin 6)
      | 48 => (2 : Fin 6)
      | 49 => (2 : Fin 6)
      | 50 => (2 : Fin 6)
      | 51 => (2 : Fin 6)
      | _ => (2 : Fin 6)
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
      | 10 => (1 : Fin 6)
      | 11 => (2 : Fin 6)
      | 12 => (2 : Fin 6)
      | 13 => (0 : Fin 6)
      | 14 => (2 : Fin 6)
      | 15 => (0 : Fin 6)
      | 16 => (1 : Fin 6)
      | 17 => (2 : Fin 6)
      | 18 => (2 : Fin 6)
      | 19 => (0 : Fin 6)
      | 20 => (0 : Fin 6)
      | 21 => (0 : Fin 6)
      | 22 => (2 : Fin 6)
      | 23 => (0 : Fin 6)
      | 24 => (0 : Fin 6)
      | 25 => (0 : Fin 6)
      | 26 => (0 : Fin 6)
      | 27 => (2 : Fin 6)
      | 28 => (0 : Fin 6)
      | 29 => (0 : Fin 6)
      | 30 => (0 : Fin 6)
      | 31 => (2 : Fin 6)
      | 32 => (2 : Fin 6)
      | 33 => (2 : Fin 6)
      | 34 => (2 : Fin 6)
      | 35 => (1 : Fin 6)
      | 36 => (0 : Fin 6)
      | 37 => (2 : Fin 6)
      | 38 => (2 : Fin 6)
      | 39 => (2 : Fin 6)
      | 40 => (2 : Fin 6)
      | 41 => (0 : Fin 6)
      | 42 => (2 : Fin 6)
      | 43 => (2 : Fin 6)
      | 44 => (2 : Fin 6)
      | 45 => (2 : Fin 6)
      | 46 => (2 : Fin 6)
      | 47 => (0 : Fin 6)
      | 48 => (2 : Fin 6)
      | 49 => (2 : Fin 6)
      | 50 => (2 : Fin 6)
      | 51 => (2 : Fin 6)
      | _ => (0 : Fin 6)

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
    (Fin 53 -> Fin 6) -> Fin 11742 :=
  Shards.decodeState

theorem decodeState_stateVector (state : Fin 11742) :
    decodeState (stateVector state) = state :=
  Shards.decodeState_stateVector state

def generatorState
    (generator : Fin 6) :
    Fin 11742 :=
  ⟨generator.val, by omega⟩

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14221
