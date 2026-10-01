import SemigroupBasis.CoRoots.Order6GenericCASSubdirectS6_2862
import SemigroupBasis.Nonfinite
import SemigroupBasis.Opposite
import SemigroupBasis.RightGeneratedPowerCertificate

set_option maxRecDepth 2048

namespace SemigroupBasis.Generated.Order6GenericCASRootWrappers.S6_2898

open SemigroupBasis

def routeManifestRowSHA256 : String := "0d8e858a6c6b8c16385aa3723e745d201e87f7f8a283f29793ad9e8905a66aa4"
def witnessRecordSHA256 : String := "fac078586c8fe22a964f6c6ce257c06277a0faa42c4d0eb12d444f326ab91f3b"
def transferComponentSHA256 : String := "aef4fadff424a8e93f3dc73dea4112b427d57a7f8682d3de4671b35f8c9c52ac"
def powerCertificateSHA256 : String := "1ecac29eb72cdfb352aa5651912768173215a0a7a463ac0546e1d02350a0da1b"

private def row6
    (c0 c1 c2 c3 c4 c5 : Fin 6) (column : Fin 6) : Fin 6 :=
  if column = 0 then c0 else
    if column = 1 then c1 else
      if column = 2 then c2 else
        if column = 3 then c3 else
          if column = 4 then c4 else c5

/-- Exact one-based catalogue table committed by the portable witness. -/
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 2 2 2 0 right else
    if left = 1 then row6 0 0 2 2 3 0 right else
      if left = 2 then row6 2 2 0 0 0 2 right else
        if left = 3 then row6 2 2 0 0 0 2 right else
          if left = 4 then row6 2 3 0 0 1 2 right else
            row6 0 0 2 2 2 5 right

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
  "260e8f7b9652e5b1d496ae34fb78140c102cf9faeb5c69989a8df0e702f130c8"

private def stateVectorChunk0 (index : Nat)
    (coordinate : Fin 5) : Fin 6 :=
  match index with
  | 0 =>
      match coordinate.val with
      | 0 => (5 : Fin 6)
      | 1 => (4 : Fin 6)
      | 2 => (5 : Fin 6)
      | 3 => (0 : Fin 6)
      | _ => (5 : Fin 6)
  | 1 =>
      match coordinate.val with
      | 0 => (4 : Fin 6)
      | 1 => (4 : Fin 6)
      | 2 => (5 : Fin 6)
      | 3 => (5 : Fin 6)
      | _ => (0 : Fin 6)
  | 2 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (4 : Fin 6)
      | 2 => (4 : Fin 6)
      | 3 => (5 : Fin 6)
      | _ => (5 : Fin 6)
  | 3 =>
      match coordinate.val with
      | 0 => (5 : Fin 6)
      | 1 => (1 : Fin 6)
      | 2 => (5 : Fin 6)
      | 3 => (0 : Fin 6)
      | _ => (5 : Fin 6)
  | 4 =>
      match coordinate.val with
      | 0 => (2 : Fin 6)
      | 1 => (1 : Fin 6)
      | 2 => (5 : Fin 6)
      | 3 => (0 : Fin 6)
      | _ => (0 : Fin 6)
  | 5 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (1 : Fin 6)
      | 2 => (2 : Fin 6)
      | 3 => (0 : Fin 6)
      | _ => (5 : Fin 6)
  | 6 =>
      match coordinate.val with
      | 0 => (1 : Fin 6)
      | 1 => (1 : Fin 6)
      | 2 => (5 : Fin 6)
      | 3 => (5 : Fin 6)
      | _ => (0 : Fin 6)
  | 7 =>
      match coordinate.val with
      | 0 => (2 : Fin 6)
      | 1 => (1 : Fin 6)
      | 2 => (2 : Fin 6)
      | 3 => (5 : Fin 6)
      | _ => (0 : Fin 6)
  | 8 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (1 : Fin 6)
      | 2 => (1 : Fin 6)
      | 3 => (5 : Fin 6)
      | _ => (5 : Fin 6)
  | 9 =>
      match coordinate.val with
      | 0 => (5 : Fin 6)
      | 1 => (3 : Fin 6)
      | 2 => (5 : Fin 6)
      | 3 => (0 : Fin 6)
      | _ => (5 : Fin 6)
  | 10 =>
      match coordinate.val with
      | 0 => (2 : Fin 6)
      | 1 => (3 : Fin 6)
      | 2 => (5 : Fin 6)
      | 3 => (0 : Fin 6)
      | _ => (0 : Fin 6)
  | 11 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (3 : Fin 6)
      | 2 => (2 : Fin 6)
      | 3 => (0 : Fin 6)
      | _ => (5 : Fin 6)
  | 12 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (3 : Fin 6)
      | 2 => (5 : Fin 6)
      | 3 => (0 : Fin 6)
      | _ => (0 : Fin 6)
  | 13 =>
      match coordinate.val with
      | 0 => (2 : Fin 6)
      | 1 => (3 : Fin 6)
      | 2 => (2 : Fin 6)
      | 3 => (0 : Fin 6)
      | _ => (0 : Fin 6)
  | 14 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (3 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | _ => (5 : Fin 6)
  | 15 =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | 1 => (3 : Fin 6)
      | 2 => (5 : Fin 6)
      | 3 => (5 : Fin 6)
      | _ => (0 : Fin 6)
  | 16 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (3 : Fin 6)
      | 2 => (2 : Fin 6)
      | 3 => (5 : Fin 6)
      | _ => (0 : Fin 6)
  | 17 =>
      match coordinate.val with
      | 0 => (2 : Fin 6)
      | 1 => (3 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (5 : Fin 6)
      | _ => (0 : Fin 6)
  | 18 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (3 : Fin 6)
      | 2 => (3 : Fin 6)
      | 3 => (5 : Fin 6)
      | _ => (5 : Fin 6)
  | 19 =>
      match coordinate.val with
      | 0 => (5 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (5 : Fin 6)
      | 3 => (0 : Fin 6)
      | _ => (5 : Fin 6)
  | 20 =>
      match coordinate.val with
      | 0 => (2 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (5 : Fin 6)
      | 3 => (0 : Fin 6)
      | _ => (0 : Fin 6)
  | 21 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (2 : Fin 6)
      | 3 => (0 : Fin 6)
      | _ => (5 : Fin 6)
  | 22 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (5 : Fin 6)
      | 3 => (0 : Fin 6)
      | _ => (0 : Fin 6)
  | 23 =>
      match coordinate.val with
      | 0 => (2 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (2 : Fin 6)
      | 3 => (0 : Fin 6)
      | _ => (0 : Fin 6)
  | 24 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | _ => (5 : Fin 6)
  | 25 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (2 : Fin 6)
      | 3 => (0 : Fin 6)
      | _ => (0 : Fin 6)
  | 26 =>
      match coordinate.val with
      | 0 => (2 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | _ => (0 : Fin 6)
  | 27 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (5 : Fin 6)
      | 3 => (5 : Fin 6)
      | _ => (0 : Fin 6)
  | 28 =>
      match coordinate.val with
      | 0 => (2 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (2 : Fin 6)
      | 3 => (5 : Fin 6)
      | _ => (0 : Fin 6)
  | 29 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (5 : Fin 6)
      | _ => (0 : Fin 6)
  | 30 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (5 : Fin 6)
      | _ => (5 : Fin 6)
  | _ =>
      match coordinate.val with
      | 0 => (5 : Fin 6)
      | 1 => (2 : Fin 6)
      | 2 => (5 : Fin 6)
      | 3 => (0 : Fin 6)
      | _ => (5 : Fin 6)

private def stateVectorChunk1 (index : Nat)
    (coordinate : Fin 5) : Fin 6 :=
  match index with
  | 0 =>
      match coordinate.val with
      | 0 => (2 : Fin 6)
      | 1 => (2 : Fin 6)
      | 2 => (5 : Fin 6)
      | 3 => (0 : Fin 6)
      | _ => (0 : Fin 6)
  | 1 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (2 : Fin 6)
      | 2 => (2 : Fin 6)
      | 3 => (0 : Fin 6)
      | _ => (5 : Fin 6)
  | 2 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (2 : Fin 6)
      | 2 => (5 : Fin 6)
      | 3 => (0 : Fin 6)
      | _ => (0 : Fin 6)
  | 3 =>
      match coordinate.val with
      | 0 => (2 : Fin 6)
      | 1 => (2 : Fin 6)
      | 2 => (2 : Fin 6)
      | 3 => (0 : Fin 6)
      | _ => (0 : Fin 6)
  | 4 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (2 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | _ => (5 : Fin 6)
  | 5 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (2 : Fin 6)
      | 2 => (2 : Fin 6)
      | 3 => (0 : Fin 6)
      | _ => (0 : Fin 6)
  | 6 =>
      match coordinate.val with
      | 0 => (2 : Fin 6)
      | 1 => (2 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | _ => (0 : Fin 6)
  | 7 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (2 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | _ => (0 : Fin 6)
  | 8 =>
      match coordinate.val with
      | 0 => (2 : Fin 6)
      | 1 => (2 : Fin 6)
      | 2 => (5 : Fin 6)
      | 3 => (5 : Fin 6)
      | _ => (0 : Fin 6)
  | 9 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (2 : Fin 6)
      | 2 => (2 : Fin 6)
      | 3 => (5 : Fin 6)
      | _ => (0 : Fin 6)
  | 10 =>
      match coordinate.val with
      | 0 => (2 : Fin 6)
      | 1 => (2 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (5 : Fin 6)
      | _ => (0 : Fin 6)
  | 11 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (2 : Fin 6)
      | 2 => (2 : Fin 6)
      | 3 => (5 : Fin 6)
      | _ => (5 : Fin 6)
  | _ =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | _ => (0 : Fin 6)

def stateVector (state : Fin 45)
    (coordinate : Fin 5) : Fin 6 :=
  if state.val < 32 then stateVectorChunk0 state.val coordinate else
    stateVectorChunk1 (state.val - 32) coordinate

def generatorVector (generator : Fin 3)
    (coordinate : Fin 5) : Fin 6 :=
  match generator.val with
  | 0 =>
      match coordinate.val with
      | 0 => (5 : Fin 6)
      | 1 => (4 : Fin 6)
      | 2 => (5 : Fin 6)
      | 3 => (0 : Fin 6)
      | _ => (5 : Fin 6)
  | 1 =>
      match coordinate.val with
      | 0 => (4 : Fin 6)
      | 1 => (4 : Fin 6)
      | 2 => (5 : Fin 6)
      | 3 => (5 : Fin 6)
      | _ => (0 : Fin 6)
  | _ =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (4 : Fin 6)
      | 2 => (4 : Fin 6)
      | 3 => (5 : Fin 6)
      | _ => (5 : Fin 6)

private def transitionChunk0 (index : Nat)
    (generator : Fin 3) : Fin 45 :=
  match index with
  | 0 =>
      match generator.val with
      | 0 => (3 : Fin 45)
      | 1 => (4 : Fin 45)
      | _ => (5 : Fin 45)
  | 1 =>
      match generator.val with
      | 0 => (4 : Fin 45)
      | 1 => (6 : Fin 45)
      | _ => (7 : Fin 45)
  | 2 =>
      match generator.val with
      | 0 => (5 : Fin 45)
      | 1 => (7 : Fin 45)
      | _ => (8 : Fin 45)
  | 3 =>
      match generator.val with
      | 0 => (9 : Fin 45)
      | 1 => (10 : Fin 45)
      | _ => (11 : Fin 45)
  | 4 =>
      match generator.val with
      | 0 => (10 : Fin 45)
      | 1 => (12 : Fin 45)
      | _ => (13 : Fin 45)
  | 5 =>
      match generator.val with
      | 0 => (11 : Fin 45)
      | 1 => (13 : Fin 45)
      | _ => (14 : Fin 45)
  | 6 =>
      match generator.val with
      | 0 => (12 : Fin 45)
      | 1 => (15 : Fin 45)
      | _ => (16 : Fin 45)
  | 7 =>
      match generator.val with
      | 0 => (13 : Fin 45)
      | 1 => (16 : Fin 45)
      | _ => (17 : Fin 45)
  | 8 =>
      match generator.val with
      | 0 => (14 : Fin 45)
      | 1 => (17 : Fin 45)
      | _ => (18 : Fin 45)
  | 9 =>
      match generator.val with
      | 0 => (19 : Fin 45)
      | 1 => (20 : Fin 45)
      | _ => (21 : Fin 45)
  | 10 =>
      match generator.val with
      | 0 => (20 : Fin 45)
      | 1 => (22 : Fin 45)
      | _ => (23 : Fin 45)
  | 11 =>
      match generator.val with
      | 0 => (21 : Fin 45)
      | 1 => (23 : Fin 45)
      | _ => (24 : Fin 45)
  | 12 =>
      match generator.val with
      | 0 => (22 : Fin 45)
      | 1 => (20 : Fin 45)
      | _ => (25 : Fin 45)
  | 13 =>
      match generator.val with
      | 0 => (23 : Fin 45)
      | 1 => (25 : Fin 45)
      | _ => (26 : Fin 45)
  | 14 =>
      match generator.val with
      | 0 => (24 : Fin 45)
      | 1 => (26 : Fin 45)
      | _ => (21 : Fin 45)
  | 15 =>
      match generator.val with
      | 0 => (20 : Fin 45)
      | 1 => (27 : Fin 45)
      | _ => (28 : Fin 45)
  | 16 =>
      match generator.val with
      | 0 => (25 : Fin 45)
      | 1 => (28 : Fin 45)
      | _ => (29 : Fin 45)
  | 17 =>
      match generator.val with
      | 0 => (26 : Fin 45)
      | 1 => (29 : Fin 45)
      | _ => (28 : Fin 45)
  | 18 =>
      match generator.val with
      | 0 => (21 : Fin 45)
      | 1 => (28 : Fin 45)
      | _ => (30 : Fin 45)
  | 19 =>
      match generator.val with
      | 0 => (31 : Fin 45)
      | 1 => (32 : Fin 45)
      | _ => (33 : Fin 45)
  | 20 =>
      match generator.val with
      | 0 => (32 : Fin 45)
      | 1 => (34 : Fin 45)
      | _ => (35 : Fin 45)
  | 21 =>
      match generator.val with
      | 0 => (33 : Fin 45)
      | 1 => (35 : Fin 45)
      | _ => (36 : Fin 45)
  | 22 =>
      match generator.val with
      | 0 => (34 : Fin 45)
      | 1 => (32 : Fin 45)
      | _ => (37 : Fin 45)
  | 23 =>
      match generator.val with
      | 0 => (35 : Fin 45)
      | 1 => (37 : Fin 45)
      | _ => (38 : Fin 45)
  | 24 =>
      match generator.val with
      | 0 => (36 : Fin 45)
      | 1 => (38 : Fin 45)
      | _ => (33 : Fin 45)
  | 25 =>
      match generator.val with
      | 0 => (37 : Fin 45)
      | 1 => (35 : Fin 45)
      | _ => (39 : Fin 45)
  | 26 =>
      match generator.val with
      | 0 => (38 : Fin 45)
      | 1 => (39 : Fin 45)
      | _ => (35 : Fin 45)
  | 27 =>
      match generator.val with
      | 0 => (34 : Fin 45)
      | 1 => (40 : Fin 45)
      | _ => (41 : Fin 45)
  | 28 =>
      match generator.val with
      | 0 => (35 : Fin 45)
      | 1 => (41 : Fin 45)
      | _ => (42 : Fin 45)
  | 29 =>
      match generator.val with
      | 0 => (39 : Fin 45)
      | 1 => (42 : Fin 45)
      | _ => (41 : Fin 45)
  | 30 =>
      match generator.val with
      | 0 => (36 : Fin 45)
      | 1 => (42 : Fin 45)
      | _ => (43 : Fin 45)
  | _ =>
      match generator.val with
      | 0 => (19 : Fin 45)
      | 1 => (20 : Fin 45)
      | _ => (21 : Fin 45)

private def transitionChunk1 (index : Nat)
    (generator : Fin 3) : Fin 45 :=
  match index with
  | 0 =>
      match generator.val with
      | 0 => (20 : Fin 45)
      | 1 => (22 : Fin 45)
      | _ => (23 : Fin 45)
  | 1 =>
      match generator.val with
      | 0 => (21 : Fin 45)
      | 1 => (23 : Fin 45)
      | _ => (24 : Fin 45)
  | 2 =>
      match generator.val with
      | 0 => (22 : Fin 45)
      | 1 => (20 : Fin 45)
      | _ => (25 : Fin 45)
  | 3 =>
      match generator.val with
      | 0 => (23 : Fin 45)
      | 1 => (25 : Fin 45)
      | _ => (26 : Fin 45)
  | 4 =>
      match generator.val with
      | 0 => (24 : Fin 45)
      | 1 => (26 : Fin 45)
      | _ => (21 : Fin 45)
  | 5 =>
      match generator.val with
      | 0 => (25 : Fin 45)
      | 1 => (23 : Fin 45)
      | _ => (44 : Fin 45)
  | 6 =>
      match generator.val with
      | 0 => (26 : Fin 45)
      | 1 => (44 : Fin 45)
      | _ => (23 : Fin 45)
  | 7 =>
      match generator.val with
      | 0 => (44 : Fin 45)
      | 1 => (26 : Fin 45)
      | _ => (25 : Fin 45)
  | 8 =>
      match generator.val with
      | 0 => (20 : Fin 45)
      | 1 => (27 : Fin 45)
      | _ => (28 : Fin 45)
  | 9 =>
      match generator.val with
      | 0 => (25 : Fin 45)
      | 1 => (28 : Fin 45)
      | _ => (29 : Fin 45)
  | 10 =>
      match generator.val with
      | 0 => (26 : Fin 45)
      | 1 => (29 : Fin 45)
      | _ => (28 : Fin 45)
  | 11 =>
      match generator.val with
      | 0 => (21 : Fin 45)
      | 1 => (28 : Fin 45)
      | _ => (30 : Fin 45)
  | _ =>
      match generator.val with
      | 0 => (39 : Fin 45)
      | 1 => (38 : Fin 45)
      | _ => (37 : Fin 45)

def transition (state : Fin 45)
    (generator : Fin 3) : Fin 45 :=
  if state.val < 32 then transitionChunk0 state.val generator else
    transitionChunk1 (state.val - 32) generator

private def representativeHeadChunk0 (index : Nat) : Fin 3 :=
  match index with
  | 0 => (0 : Fin 3)
  | 1 => (1 : Fin 3)
  | 2 => (2 : Fin 3)
  | 3 => (0 : Fin 3)
  | 4 => (0 : Fin 3)
  | 5 => (0 : Fin 3)
  | 6 => (1 : Fin 3)
  | 7 => (1 : Fin 3)
  | 8 => (2 : Fin 3)
  | 9 => (0 : Fin 3)
  | 10 => (0 : Fin 3)
  | 11 => (0 : Fin 3)
  | 12 => (0 : Fin 3)
  | 13 => (0 : Fin 3)
  | 14 => (0 : Fin 3)
  | 15 => (1 : Fin 3)
  | 16 => (1 : Fin 3)
  | 17 => (1 : Fin 3)
  | 18 => (2 : Fin 3)
  | 19 => (0 : Fin 3)
  | 20 => (0 : Fin 3)
  | 21 => (0 : Fin 3)
  | 22 => (0 : Fin 3)
  | 23 => (0 : Fin 3)
  | 24 => (0 : Fin 3)
  | 25 => (0 : Fin 3)
  | 26 => (0 : Fin 3)
  | 27 => (1 : Fin 3)
  | 28 => (1 : Fin 3)
  | 29 => (1 : Fin 3)
  | 30 => (2 : Fin 3)
  | _ => (0 : Fin 3)

private def representativeHeadChunk1 (index : Nat) : Fin 3 :=
  match index with
  | 0 => (0 : Fin 3)
  | 1 => (0 : Fin 3)
  | 2 => (0 : Fin 3)
  | 3 => (0 : Fin 3)
  | 4 => (0 : Fin 3)
  | 5 => (0 : Fin 3)
  | 6 => (0 : Fin 3)
  | 7 => (0 : Fin 3)
  | 8 => (1 : Fin 3)
  | 9 => (1 : Fin 3)
  | 10 => (1 : Fin 3)
  | 11 => (2 : Fin 3)
  | _ => (0 : Fin 3)

def representativeHead (state : Fin 45) : Fin 3 :=
  if state.val < 32 then representativeHeadChunk0 state.val else
    representativeHeadChunk1 (state.val - 32)

private def representativeTailChunk0 (index : Nat) :
    List (Fin 3) :=
  match index with
  | 0 => []
  | 1 => []
  | 2 => []
  | 3 => [0]
  | 4 => [1]
  | 5 => [2]
  | 6 => [1]
  | 7 => [2]
  | 8 => [2]
  | 9 => [0, 0]
  | 10 => [0, 1]
  | 11 => [0, 2]
  | 12 => [1, 1]
  | 13 => [1, 2]
  | 14 => [2, 2]
  | 15 => [1, 1]
  | 16 => [1, 2]
  | 17 => [2, 2]
  | 18 => [2, 2]
  | 19 => [0, 0, 0]
  | 20 => [0, 0, 1]
  | 21 => [0, 0, 2]
  | 22 => [0, 1, 1]
  | 23 => [0, 1, 2]
  | 24 => [0, 2, 2]
  | 25 => [1, 1, 2]
  | 26 => [1, 2, 2]
  | 27 => [1, 1, 1]
  | 28 => [1, 1, 2]
  | 29 => [1, 2, 2]
  | 30 => [2, 2, 2]
  | _ => [0, 0, 0, 0]

private def representativeTailChunk1 (index : Nat) :
    List (Fin 3) :=
  match index with
  | 0 => [0, 0, 0, 1]
  | 1 => [0, 0, 0, 2]
  | 2 => [0, 0, 1, 1]
  | 3 => [0, 0, 1, 2]
  | 4 => [0, 0, 2, 2]
  | 5 => [0, 1, 1, 2]
  | 6 => [0, 1, 2, 2]
  | 7 => [1, 1, 2, 2]
  | 8 => [1, 1, 1, 1]
  | 9 => [1, 1, 1, 2]
  | 10 => [1, 1, 2, 2]
  | 11 => [2, 2, 2, 2]
  | _ => [0, 1, 1, 2, 2]

def representativeTail (state : Fin 45) :
    List (Fin 3) :=
  if state.val < 32 then representativeTailChunk0 state.val else
    representativeTailChunk1 (state.val - 32)

private def sourceLabelChunk0 (index : Nat) : Fin 6 :=
  match index with
  | 0 => (5 : Fin 6)
  | 1 => (4 : Fin 6)
  | 2 => (3 : Fin 6)
  | 3 => (5 : Fin 6)
  | 4 => (0 : Fin 6)
  | 5 => (3 : Fin 6)
  | 6 => (1 : Fin 6)
  | 7 => (3 : Fin 6)
  | 8 => (0 : Fin 6)
  | 9 => (5 : Fin 6)
  | 10 => (0 : Fin 6)
  | 11 => (3 : Fin 6)
  | 12 => (0 : Fin 6)
  | 13 => (3 : Fin 6)
  | 14 => (0 : Fin 6)
  | 15 => (2 : Fin 6)
  | 16 => (3 : Fin 6)
  | 17 => (0 : Fin 6)
  | 18 => (3 : Fin 6)
  | 19 => (5 : Fin 6)
  | 20 => (0 : Fin 6)
  | 21 => (3 : Fin 6)
  | 22 => (0 : Fin 6)
  | 23 => (3 : Fin 6)
  | 24 => (0 : Fin 6)
  | 25 => (3 : Fin 6)
  | 26 => (0 : Fin 6)
  | 27 => (0 : Fin 6)
  | 28 => (3 : Fin 6)
  | 29 => (0 : Fin 6)
  | 30 => (0 : Fin 6)
  | _ => (5 : Fin 6)

private def sourceLabelChunk1 (index : Nat) : Fin 6 :=
  match index with
  | 0 => (0 : Fin 6)
  | 1 => (3 : Fin 6)
  | 2 => (0 : Fin 6)
  | 3 => (3 : Fin 6)
  | 4 => (0 : Fin 6)
  | 5 => (3 : Fin 6)
  | 6 => (0 : Fin 6)
  | 7 => (0 : Fin 6)
  | 8 => (0 : Fin 6)
  | 9 => (3 : Fin 6)
  | 10 => (0 : Fin 6)
  | 11 => (3 : Fin 6)
  | _ => (0 : Fin 6)

def sourceLabel (state : Fin 45) : Fin 6 :=
  if state.val < 32 then sourceLabelChunk0 state.val else
    sourceLabelChunk1 (state.val - 32)

def generatorSourceLabel (generator : Fin 3) : Fin 6 :=
  match generator.val with
  | 0 => (5 : Fin 6)
  | 1 => (4 : Fin 6)
  | _ => (3 : Fin 6)

def sourcePreimage (value : Fin 6) : Fin 45 :=
  match value.val with
  | 0 => (4 : Fin 45)
  | 1 => (6 : Fin 45)
  | 2 => (15 : Fin 45)
  | 3 => (2 : Fin 45)
  | 4 => (1 : Fin 45)
  | _ => (0 : Fin 45)

private def stateVectorCode
    (vector : Fin 5 -> Fin 6) : Nat :=
  (vector (0 : Fin 5)).val + 6 * ((vector (1 : Fin 5)).val + 6 * ((vector (2 : Fin 5)).val + 6 * ((vector (3 : Fin 5)).val + 6 * ((vector (4 : Fin 5)).val))))

private def decodeStateCode (code : Nat) : Fin 45 :=
  if code < 1170 then
    if code < 188 then
      if code < 74 then
        if code < 12 then
          if code < 2 then
            if code = 0 then (44 : Fin 45) else (0 : Fin 45)
          else if code = 2 then (26 : Fin 45) else
            (0 : Fin 45)
        else if code = 12 then (39 : Fin 45) else
          if code < 72 then
            if code = 14 then (38 : Fin 45) else (0 : Fin 45)
          else if code = 72 then (25 : Fin 45) else
            (0 : Fin 45)
      else if code = 74 then (23 : Fin 45) else
        if code < 92 then
          if code < 86 then
            if code = 84 then (37 : Fin 45) else (0 : Fin 45)
          else if code = 86 then (35 : Fin 45) else
            (0 : Fin 45)
        else if code = 92 then (13 : Fin 45) else
          if code < 182 then
            if code = 180 then (22 : Fin 45) else (0 : Fin 45)
          else if code = 182 then (20 : Fin 45) else
            (0 : Fin 45)
    else if code = 188 then (4 : Fin 45) else
      if code < 1094 then
        if code < 198 then
          if code < 194 then
            if code = 192 then (34 : Fin 45) else (0 : Fin 45)
          else if code = 194 then (32 : Fin 45) else
            (0 : Fin 45)
        else if code = 198 then (12 : Fin 45) else
          if code < 1080 then
            if code = 200 then (10 : Fin 45) else (0 : Fin 45)
          else if code = 1080 then (29 : Fin 45) else
            (0 : Fin 45)
      else if code = 1094 then (42 : Fin 45) else
        if code < 1160 then
          if code < 1154 then
            if code = 1100 then (17 : Fin 45) else (0 : Fin 45)
          else if code = 1154 then (28 : Fin 45) else
            (0 : Fin 45)
        else if code = 1160 then (7 : Fin 45) else
          if code = 1164 then (41 : Fin 45) else (0 : Fin 45)
  else if code = 1170 then (16 : Fin 45) else
    if code < 6570 then
      if code < 6480 then
        if code < 1274 then
          if code < 1267 then
            if code = 1260 then (27 : Fin 45) else (0 : Fin 45)
          else if code = 1267 then (6 : Fin 45) else
            (0 : Fin 45)
        else if code = 1274 then (40 : Fin 45) else
          if code < 1288 then
            if code = 1281 then (15 : Fin 45) else (0 : Fin 45)
          else if code = 1288 then (1 : Fin 45) else
            (0 : Fin 45)
      else if code = 6480 then (24 : Fin 45) else
        if code < 6552 then
          if code < 6498 then
            if code = 6492 then (36 : Fin 45) else (0 : Fin 45)
          else if code = 6498 then (14 : Fin 45) else
            (0 : Fin 45)
        else if code = 6552 then (21 : Fin 45) else
          if code < 6564 then
            if code = 6558 then (5 : Fin 45) else (0 : Fin 45)
          else if code = 6564 then (33 : Fin 45) else
            (0 : Fin 45)
    else if code = 6570 then (11 : Fin 45) else
      if code < 7560 then
        if code < 6677 then
          if code < 6671 then
            if code = 6665 then (19 : Fin 45) else (0 : Fin 45)
          else if code = 6671 then (3 : Fin 45) else
            (0 : Fin 45)
        else if code = 6677 then (31 : Fin 45) else
          if code < 6689 then
            if code = 6683 then (9 : Fin 45) else (0 : Fin 45)
          else if code = 6689 then (0 : Fin 45) else
            (0 : Fin 45)
      else if code = 7560 then (30 : Fin 45) else
        if code < 7686 then
          if code < 7644 then
            if code = 7602 then (8 : Fin 45) else (0 : Fin 45)
          else if code = 7644 then (43 : Fin 45) else
            (0 : Fin 45)
        else if code = 7686 then (18 : Fin 45) else
          if code = 7728 then (2 : Fin 45) else (0 : Fin 45)

private def decodeState
    (vector : Fin 5 -> Fin 6) : Fin 45 :=
  decodeStateCode (stateVectorCode vector)

set_option maxHeartbeats 2000000 in
private theorem decodeState_stateVector (state : Fin 45) :
    decodeState (stateVector state) = state := by
  decide +revert

set_option maxHeartbeats 2000000 in
private theorem transitionMap :
    forall (state : Fin 45)
      (generator : Fin 3)
      (coordinate : Fin 5),
      stateVector (transition state generator) coordinate =
        oppositeTable.semigroup.mul (stateVector state coordinate)
          (generatorVector generator coordinate) := by
  intro state generator coordinate
  apply Fin.ext
  exact by decide +revert

set_option maxHeartbeats 2000000 in
private theorem representativeMap :
    forall (state : Fin 45)
      (coordinate : Fin 5),
      stateVector state coordinate =
        (representativeTail state).foldl
          (fun value generator =>
            oppositeTable.semigroup.mul value
              (generatorVector generator coordinate))
          (generatorVector (representativeHead state) coordinate) := by
  intro state coordinate
  apply Fin.ext
  exact by decide +revert

/-- Reduced term-function states embedded in a finite power of the target. -/
def powerCertificate : RightGeneratedPowerCertificate
    (U := Fin 45)
    (G := Fin 3)
    (I := Fin 5) oppositeTable.semigroup where
  stateVector := stateVector
  generatorVector := generatorVector
  transition := transition
  representativeHead := representativeHead
  representativeTail := representativeTail
  injective := by
    intro left right equalVectors
    exact
      (decodeState_stateVector left).symm.trans <|
        (congrArg decodeState equalVectors).trans <|
          decodeState_stateVector right
  transition_map := transitionMap
  representative_map := representativeMap

set_option maxHeartbeats 2000000 in
private theorem sourceLabelTransition :
    forall (state : Fin 45)
      (generator : Fin 3),
      sourceLabel (transition state generator) =
        SemigroupBasis.Generated.Order6GenericCASRootData.S6_2862.oppositeTable.semigroup.mul (sourceLabel state)
          (generatorSourceLabel generator) := by
  intro state generator
  apply Fin.ext
  exact by decide +revert

set_option maxHeartbeats 2000000 in
private theorem sourceLabelRepresentative :
    forall state : Fin 45,
      sourceLabel state =
        (representativeTail state).foldl
          (fun value generator =>
            SemigroupBasis.Generated.Order6GenericCASRootData.S6_2862.oppositeTable.semigroup.mul value
              (generatorSourceLabel generator))
          (generatorSourceLabel (representativeHead state)) := by
  intro state
  apply Fin.ext
  exact by decide +revert

private theorem sourceLabelRightMultiplyWord
    (state : Fin 45)
    (word : List (Fin 3)) :
    sourceLabel (powerCertificate.rightMultiplyWord state word) =
      word.foldl
        (fun value generator =>
          SemigroupBasis.Generated.Order6GenericCASRootData.S6_2862.oppositeTable.semigroup.mul value
            (generatorSourceLabel generator))
        (sourceLabel state) := by
  induction word generalizing state with
  | nil => rfl
  | cons generator word inductionHypothesis =>
      change
        sourceLabel
            (powerCertificate.rightMultiplyWord
              (transition state generator) word) =
          word.foldl
            (fun value nextGenerator =>
              SemigroupBasis.Generated.Order6GenericCASRootData.S6_2862.oppositeTable.semigroup.mul value
                (generatorSourceLabel nextGenerator))
            (SemigroupBasis.Generated.Order6GenericCASRootData.S6_2862.oppositeTable.semigroup.mul (sourceLabel state)
              (generatorSourceLabel generator))
      rw [inductionHypothesis]
      rw [sourceLabelTransition]

private theorem sourceFoldlGeneratorAssoc
    (left right : Fin 6)
    (word : List (Fin 3)) :
    word.foldl
        (fun value generator =>
          SemigroupBasis.Generated.Order6GenericCASRootData.S6_2862.oppositeTable.semigroup.mul value
            (generatorSourceLabel generator))
        (SemigroupBasis.Generated.Order6GenericCASRootData.S6_2862.oppositeTable.semigroup.mul left right) =
      SemigroupBasis.Generated.Order6GenericCASRootData.S6_2862.oppositeTable.semigroup.mul left
        (word.foldl
          (fun value generator =>
            SemigroupBasis.Generated.Order6GenericCASRootData.S6_2862.oppositeTable.semigroup.mul value
              (generatorSourceLabel generator))
          right) := by
  induction word generalizing right with
  | nil => rfl
  | cons generator word inductionHypothesis =>
      simp only [List.foldl_cons]
      rw [SemigroupBasis.Generated.Order6GenericCASRootData.S6_2862.oppositeTable.semigroup.assoc]
      exact inductionHypothesis
        (SemigroupBasis.Generated.Order6GenericCASRootData.S6_2862.oppositeTable.semigroup.mul right (generatorSourceLabel generator))

private theorem sourceLabelMapMul :
    forall (left right : Fin 45),
      sourceLabel (powerCertificate.semigroup.mul left right) =
        SemigroupBasis.Generated.Order6GenericCASRootData.S6_2862.oppositeTable.semigroup.mul (sourceLabel left) (sourceLabel right) := by
  intro left right
  calc
    sourceLabel (powerCertificate.semigroup.mul left right) =
        sourceLabel
          (powerCertificate.rightMultiplyWord
            (transition left (representativeHead right))
            (representativeTail right)) := rfl
    _ = (representativeTail right).foldl
          (fun value generator =>
            SemigroupBasis.Generated.Order6GenericCASRootData.S6_2862.oppositeTable.semigroup.mul value
              (generatorSourceLabel generator))
          (sourceLabel (transition left (representativeHead right))) :=
      sourceLabelRightMultiplyWord _ _
    _ = (representativeTail right).foldl
          (fun value generator =>
            SemigroupBasis.Generated.Order6GenericCASRootData.S6_2862.oppositeTable.semigroup.mul value
              (generatorSourceLabel generator))
          (SemigroupBasis.Generated.Order6GenericCASRootData.S6_2862.oppositeTable.semigroup.mul (sourceLabel left)
            (generatorSourceLabel (representativeHead right))) :=
      congrArg
        (fun initial =>
          (representativeTail right).foldl
            (fun value generator =>
              SemigroupBasis.Generated.Order6GenericCASRootData.S6_2862.oppositeTable.semigroup.mul value
                (generatorSourceLabel generator))
            initial)
        (sourceLabelTransition left (representativeHead right))
    _ = SemigroupBasis.Generated.Order6GenericCASRootData.S6_2862.oppositeTable.semigroup.mul (sourceLabel left)
          ((representativeTail right).foldl
            (fun value generator =>
              SemigroupBasis.Generated.Order6GenericCASRootData.S6_2862.oppositeTable.semigroup.mul value
                (generatorSourceLabel generator))
            (generatorSourceLabel (representativeHead right))) :=
      sourceFoldlGeneratorAssoc _ _ _
    _ = SemigroupBasis.Generated.Order6GenericCASRootData.S6_2862.oppositeTable.semigroup.mul (sourceLabel left) (sourceLabel right) :=
      congrArg (SemigroupBasis.Generated.Order6GenericCASRootData.S6_2862.oppositeTable.semigroup.mul (sourceLabel left))
        (sourceLabelRepresentative right).symm

set_option maxHeartbeats 1000000 in
private theorem sourceLabelRightInverse :
    forall value : Fin 6, sourceLabel (sourcePreimage value) = value := by
  intro value
  apply Fin.ext
  exact by decide +revert

/-- The generated term-function semigroup maps onto the selected root. -/
def quotient : SplitSurjection powerCertificate.semigroup
    SemigroupBasis.Generated.Order6GenericCASRootData.S6_2862.oppositeTable.semigroup where
  toFun := sourceLabel
  map_mul := sourceLabelMapMul
  preimage := sourcePreimage
  right_inverse := sourceLabelRightInverse

private def targetLaw0ToFinite : Nat -> Fin 2
  | 0 => (0 : Fin 2)
  | 1 => (1 : Fin 2)
  | _ => (0 : Fin 2)

private def targetLaw0FromFinite (index : Fin 2) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
private theorem targetLaw0Valid :
    SemigroupBasis.Generated.Order6GenericCASRootData.S6_2862.law0.SatisfiedBy oppositeTable.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    oppositeTable SemigroupBasis.Generated.Order6GenericCASRootData.S6_2862.law0
    targetLaw0ToFinite targetLaw0FromFinite (by decide) (by decide)

private def targetLaw1ToFinite : Nat -> Fin 1
  | 0 => (0 : Fin 1)
  | _ => (0 : Fin 1)

private def targetLaw1FromFinite (index : Fin 1) : Nat :=
  match index.val with
  | 0 => 0
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
private theorem targetLaw1Valid :
    SemigroupBasis.Generated.Order6GenericCASRootData.S6_2862.law1.SatisfiedBy oppositeTable.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    oppositeTable SemigroupBasis.Generated.Order6GenericCASRootData.S6_2862.law1
    targetLaw1ToFinite targetLaw1FromFinite (by decide) (by decide)

private def targetLaw2ToFinite : Nat -> Fin 2
  | 0 => (0 : Fin 2)
  | 1 => (1 : Fin 2)
  | _ => (0 : Fin 2)

private def targetLaw2FromFinite (index : Fin 2) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
private theorem targetLaw2Valid :
    SemigroupBasis.Generated.Order6GenericCASRootData.S6_2862.law2.SatisfiedBy oppositeTable.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    oppositeTable SemigroupBasis.Generated.Order6GenericCASRootData.S6_2862.law2
    targetLaw2ToFinite targetLaw2FromFinite (by decide) (by decide)

private def targetLaw3ToFinite : Nat -> Fin 2
  | 0 => (0 : Fin 2)
  | 1 => (1 : Fin 2)
  | _ => (0 : Fin 2)

private def targetLaw3FromFinite (index : Fin 2) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
private theorem targetLaw3Valid :
    SemigroupBasis.Generated.Order6GenericCASRootData.S6_2862.law3.SatisfiedBy oppositeTable.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    oppositeTable SemigroupBasis.Generated.Order6GenericCASRootData.S6_2862.law3
    targetLaw3ToFinite targetLaw3FromFinite (by decide) (by decide)

private def targetLaw4ToFinite : Nat -> Fin 2
  | 0 => (0 : Fin 2)
  | 1 => (1 : Fin 2)
  | _ => (0 : Fin 2)

private def targetLaw4FromFinite (index : Fin 2) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
private theorem targetLaw4Valid :
    SemigroupBasis.Generated.Order6GenericCASRootData.S6_2862.law4.SatisfiedBy oppositeTable.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    oppositeTable SemigroupBasis.Generated.Order6GenericCASRootData.S6_2862.law4
    targetLaw4ToFinite targetLaw4FromFinite (by decide) (by decide)

private def targetLaw5ToFinite : Nat -> Fin 3
  | 0 => (0 : Fin 3)
  | 1 => (1 : Fin 3)
  | 2 => (2 : Fin 3)
  | _ => (0 : Fin 3)

private def targetLaw5FromFinite (index : Fin 3) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
private theorem targetLaw5Valid :
    SemigroupBasis.Generated.Order6GenericCASRootData.S6_2862.law5.SatisfiedBy oppositeTable.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    oppositeTable SemigroupBasis.Generated.Order6GenericCASRootData.S6_2862.law5
    targetLaw5ToFinite targetLaw5FromFinite (by decide) (by decide)

private def targetLaw6ToFinite : Nat -> Fin 4
  | 0 => (0 : Fin 4)
  | 1 => (1 : Fin 4)
  | 2 => (2 : Fin 4)
  | 3 => (3 : Fin 4)
  | _ => (0 : Fin 4)

private def targetLaw6FromFinite (index : Fin 4) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
private theorem targetLaw6Valid :
    SemigroupBasis.Generated.Order6GenericCASRootData.S6_2862.law6.SatisfiedBy oppositeTable.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    oppositeTable SemigroupBasis.Generated.Order6GenericCASRootData.S6_2862.law6
    targetLaw6ToFinite targetLaw6FromFinite (by decide) (by decide)

/-- Exact finite checks that the selected target models the root basis. -/
theorem targetModels :
    Models oppositeTable.semigroup SemigroupBasis.Generated.Order6GenericCASRootData.S6_2862.basis := by
  unfold SemigroupBasis.Generated.Order6GenericCASRootData.S6_2862.basis
  exact
    FiniteNilpotentCounterexample.models_cons targetLaw0Valid <|
      FiniteNilpotentCounterexample.models_cons targetLaw1Valid <|
        FiniteNilpotentCounterexample.models_cons targetLaw2Valid <|
          FiniteNilpotentCounterexample.models_cons targetLaw3Valid <|
            FiniteNilpotentCounterexample.models_cons targetLaw4Valid <|
              FiniteNilpotentCounterexample.models_cons targetLaw5Valid <|
                FiniteNilpotentCounterexample.models_cons targetLaw6Valid <|
                  FiniteNilpotentCounterexample.models_nil oppositeTable.semigroup

/-- Exact identity-theory transfer authenticated by the finite certificate. -/
theorem sameIdentityTheory :
    SameIdentityTheoryOver SemigroupBasis.Generated.Order6GenericCASRootData.S6_2862.oppositeTable.semigroup
      oppositeTable.semigroup Nat := by
  intro identity
  constructor
  · intro sourceValid valuation
    exact Derives.sound targetModels
      (SemigroupBasis.CoRoots.Order6GenericCASSubdirectS6_2862.basisFor.2 identity sourceValid) valuation
  · intro targetValid
    have powerValid :=
      identity.satisfiedByPi oppositeTable.semigroup
        (Fin 5) targetValid
    have subValid :=
      powerCertificate.embedding.pullback_identity identity powerValid
    exact quotient.pushforwardIdentity identity subValid

/-- First-layer generic-CAS basis wrapper for `S6_2898`. -/
theorem opposite_basis :
    BasisFor table.semigroup.opposite SemigroupBasis.Generated.Order6GenericCASRootData.S6_2862.basis := by
  have transferred :
      BasisFor oppositeTable.semigroup SemigroupBasis.Generated.Order6GenericCASRootData.S6_2862.basis :=
    (basisFor_iff_of_sameIdentityTheoryOver sameIdentityTheory).mp
      SemigroupBasis.CoRoots.Order6GenericCASSubdirectS6_2862.basisFor
  simpa only [oppositeTable_semigroup] using transferred

end SemigroupBasis.Generated.Order6GenericCASRootWrappers.S6_2898
