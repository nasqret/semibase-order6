import SemigroupBasis.CoRoots.Order6GenericCASSubdirectS6_4336
import SemigroupBasis.Nonfinite
import SemigroupBasis.Opposite
import SemigroupBasis.RightGeneratedPowerCertificate

set_option maxRecDepth 2048

namespace SemigroupBasis.Generated.Order6GenericCASRootWrappers.S6_14992

open SemigroupBasis

def routeManifestRowSHA256 : String := "453343613af58288e4a9a819dff9d10ec7bd76cc3d85f474a6044c9f05e85097"
def witnessRecordSHA256 : String := "c4496b831a0600de9a6d6e378eb467e2a27ee443371d34b7f076d51cf9dd9347"
def transferComponentSHA256 : String := "3c72b6c56d4d22e406758f2a458bcaf83411e7622a375804baa0dbbfe3ae79af"
def powerCertificateSHA256 : String := "34db9668e9db7613c08e3c86ef3989e4ef12d505019868e6cdd7ea09a04db4bc"

private def row6
    (c0 c1 c2 c3 c4 c5 : Fin 6) (column : Fin 6) : Fin 6 :=
  if column = 0 then c0 else
    if column = 1 then c1 else
      if column = 2 then c2 else
        if column = 3 then c3 else
          if column = 4 then c4 else c5

/-- Exact one-based catalogue table committed by the portable witness. -/
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 2 3 3 3 right else
    if left = 1 then row6 0 0 2 3 3 4 right else
      if left = 2 then row6 2 2 3 0 0 0 right else
        if left = 3 then row6 3 3 0 2 2 2 right else
          if left = 4 then row6 3 3 0 2 2 2 right else
            row6 3 4 0 2 2 2 right

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
  "ead5c3e21323b5a6e1a463746755c393838a997e357a1fcd3e69c1661b2eb567"

private def stateVectorChunk0 (index : Nat)
    (coordinate : Fin 3) : Fin 6 :=
  match index with
  | 0 =>
      match coordinate.val with
      | 0 => (5 : Fin 6)
      | 1 => (5 : Fin 6)
      | _ => (0 : Fin 6)
  | 1 =>
      match coordinate.val with
      | 0 => (1 : Fin 6)
      | 1 => (5 : Fin 6)
      | _ => (0 : Fin 6)
  | 2 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (1 : Fin 6)
      | _ => (2 : Fin 6)
  | 3 =>
      match coordinate.val with
      | 0 => (2 : Fin 6)
      | 1 => (2 : Fin 6)
      | _ => (0 : Fin 6)
  | 4 =>
      match coordinate.val with
      | 0 => (4 : Fin 6)
      | 1 => (2 : Fin 6)
      | _ => (0 : Fin 6)
  | 5 =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | 1 => (4 : Fin 6)
      | _ => (2 : Fin 6)
  | 6 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (2 : Fin 6)
      | _ => (0 : Fin 6)
  | 7 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (4 : Fin 6)
      | _ => (2 : Fin 6)
  | 8 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | _ => (3 : Fin 6)
  | 9 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | _ => (0 : Fin 6)
  | 10 =>
      match coordinate.val with
      | 0 => (2 : Fin 6)
      | 1 => (0 : Fin 6)
      | _ => (0 : Fin 6)
  | 11 =>
      match coordinate.val with
      | 0 => (2 : Fin 6)
      | 1 => (2 : Fin 6)
      | _ => (2 : Fin 6)
  | 12 =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | 1 => (0 : Fin 6)
      | _ => (0 : Fin 6)
  | 13 =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | 1 => (2 : Fin 6)
      | _ => (2 : Fin 6)
  | 14 =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | 1 => (3 : Fin 6)
      | _ => (3 : Fin 6)
  | 15 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (2 : Fin 6)
      | _ => (2 : Fin 6)
  | 16 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (3 : Fin 6)
      | _ => (3 : Fin 6)
  | 17 =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | 1 => (3 : Fin 6)
      | _ => (0 : Fin 6)
  | 18 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (3 : Fin 6)
      | _ => (0 : Fin 6)
  | 19 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | _ => (2 : Fin 6)
  | 20 =>
      match coordinate.val with
      | 0 => (2 : Fin 6)
      | 1 => (3 : Fin 6)
      | _ => (0 : Fin 6)
  | 21 =>
      match coordinate.val with
      | 0 => (2 : Fin 6)
      | 1 => (0 : Fin 6)
      | _ => (2 : Fin 6)
  | 22 =>
      match coordinate.val with
      | 0 => (2 : Fin 6)
      | 1 => (2 : Fin 6)
      | _ => (3 : Fin 6)
  | 23 =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | 1 => (0 : Fin 6)
      | _ => (2 : Fin 6)
  | 24 =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | 1 => (2 : Fin 6)
      | _ => (3 : Fin 6)
  | 25 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (2 : Fin 6)
      | _ => (3 : Fin 6)
  | 26 =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | 1 => (2 : Fin 6)
      | _ => (0 : Fin 6)
  | 27 =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | 1 => (3 : Fin 6)
      | _ => (2 : Fin 6)
  | 28 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (3 : Fin 6)
      | _ => (2 : Fin 6)
  | 29 =>
      match coordinate.val with
      | 0 => (2 : Fin 6)
      | 1 => (3 : Fin 6)
      | _ => (2 : Fin 6)
  | 30 =>
      match coordinate.val with
      | 0 => (2 : Fin 6)
      | 1 => (0 : Fin 6)
      | _ => (3 : Fin 6)
  | _ =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | 1 => (0 : Fin 6)
      | _ => (3 : Fin 6)

private def stateVectorChunk1 (index : Nat)
    (coordinate : Fin 3) : Fin 6 :=
  match index with
  | _ =>
      match coordinate.val with
      | 0 => (2 : Fin 6)
      | 1 => (3 : Fin 6)
      | _ => (3 : Fin 6)

def stateVector (state : Fin 33)
    (coordinate : Fin 3) : Fin 6 :=
  if state.val < 32 then stateVectorChunk0 state.val coordinate else
    stateVectorChunk1 (state.val - 32) coordinate

def generatorVector (generator : Fin 3)
    (coordinate : Fin 3) : Fin 6 :=
  match generator.val with
  | 0 =>
      match coordinate.val with
      | 0 => (5 : Fin 6)
      | 1 => (5 : Fin 6)
      | _ => (0 : Fin 6)
  | 1 =>
      match coordinate.val with
      | 0 => (1 : Fin 6)
      | 1 => (5 : Fin 6)
      | _ => (0 : Fin 6)
  | _ =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (1 : Fin 6)
      | _ => (2 : Fin 6)

private def transitionChunk0 (index : Nat)
    (generator : Fin 3) : Fin 33 :=
  match index with
  | 0 =>
      match generator.val with
      | 0 => (3 : Fin 33)
      | 1 => (4 : Fin 33)
      | _ => (5 : Fin 33)
  | 1 =>
      match generator.val with
      | 0 => (4 : Fin 33)
      | 1 => (6 : Fin 33)
      | _ => (7 : Fin 33)
  | 2 =>
      match generator.val with
      | 0 => (5 : Fin 33)
      | 1 => (7 : Fin 33)
      | _ => (8 : Fin 33)
  | 3 =>
      match generator.val with
      | 0 => (9 : Fin 33)
      | 1 => (10 : Fin 33)
      | _ => (11 : Fin 33)
  | 4 =>
      match generator.val with
      | 0 => (10 : Fin 33)
      | 1 => (12 : Fin 33)
      | _ => (13 : Fin 33)
  | 5 =>
      match generator.val with
      | 0 => (11 : Fin 33)
      | 1 => (13 : Fin 33)
      | _ => (14 : Fin 33)
  | 6 =>
      match generator.val with
      | 0 => (12 : Fin 33)
      | 1 => (9 : Fin 33)
      | _ => (15 : Fin 33)
  | 7 =>
      match generator.val with
      | 0 => (13 : Fin 33)
      | 1 => (15 : Fin 33)
      | _ => (16 : Fin 33)
  | 8 =>
      match generator.val with
      | 0 => (14 : Fin 33)
      | 1 => (16 : Fin 33)
      | _ => (9 : Fin 33)
  | 9 =>
      match generator.val with
      | 0 => (17 : Fin 33)
      | 1 => (18 : Fin 33)
      | _ => (19 : Fin 33)
  | 10 =>
      match generator.val with
      | 0 => (18 : Fin 33)
      | 1 => (20 : Fin 33)
      | _ => (21 : Fin 33)
  | 11 =>
      match generator.val with
      | 0 => (19 : Fin 33)
      | 1 => (21 : Fin 33)
      | _ => (22 : Fin 33)
  | 12 =>
      match generator.val with
      | 0 => (20 : Fin 33)
      | 1 => (17 : Fin 33)
      | _ => (23 : Fin 33)
  | 13 =>
      match generator.val with
      | 0 => (21 : Fin 33)
      | 1 => (23 : Fin 33)
      | _ => (24 : Fin 33)
  | 14 =>
      match generator.val with
      | 0 => (22 : Fin 33)
      | 1 => (24 : Fin 33)
      | _ => (17 : Fin 33)
  | 15 =>
      match generator.val with
      | 0 => (23 : Fin 33)
      | 1 => (19 : Fin 33)
      | _ => (25 : Fin 33)
  | 16 =>
      match generator.val with
      | 0 => (24 : Fin 33)
      | 1 => (25 : Fin 33)
      | _ => (18 : Fin 33)
  | 17 =>
      match generator.val with
      | 0 => (3 : Fin 33)
      | 1 => (26 : Fin 33)
      | _ => (27 : Fin 33)
  | 18 =>
      match generator.val with
      | 0 => (26 : Fin 33)
      | 1 => (6 : Fin 33)
      | _ => (28 : Fin 33)
  | 19 =>
      match generator.val with
      | 0 => (27 : Fin 33)
      | 1 => (28 : Fin 33)
      | _ => (8 : Fin 33)
  | 20 =>
      match generator.val with
      | 0 => (6 : Fin 33)
      | 1 => (3 : Fin 33)
      | _ => (29 : Fin 33)
  | 21 =>
      match generator.val with
      | 0 => (28 : Fin 33)
      | 1 => (29 : Fin 33)
      | _ => (30 : Fin 33)
  | 22 =>
      match generator.val with
      | 0 => (8 : Fin 33)
      | 1 => (30 : Fin 33)
      | _ => (3 : Fin 33)
  | 23 =>
      match generator.val with
      | 0 => (29 : Fin 33)
      | 1 => (27 : Fin 33)
      | _ => (31 : Fin 33)
  | 24 =>
      match generator.val with
      | 0 => (30 : Fin 33)
      | 1 => (31 : Fin 33)
      | _ => (26 : Fin 33)
  | 25 =>
      match generator.val with
      | 0 => (31 : Fin 33)
      | 1 => (8 : Fin 33)
      | _ => (6 : Fin 33)
  | 26 =>
      match generator.val with
      | 0 => (10 : Fin 33)
      | 1 => (12 : Fin 33)
      | _ => (13 : Fin 33)
  | 27 =>
      match generator.val with
      | 0 => (11 : Fin 33)
      | 1 => (13 : Fin 33)
      | _ => (14 : Fin 33)
  | 28 =>
      match generator.val with
      | 0 => (13 : Fin 33)
      | 1 => (15 : Fin 33)
      | _ => (16 : Fin 33)
  | 29 =>
      match generator.val with
      | 0 => (15 : Fin 33)
      | 1 => (11 : Fin 33)
      | _ => (32 : Fin 33)
  | 30 =>
      match generator.val with
      | 0 => (16 : Fin 33)
      | 1 => (32 : Fin 33)
      | _ => (10 : Fin 33)
  | _ =>
      match generator.val with
      | 0 => (32 : Fin 33)
      | 1 => (14 : Fin 33)
      | _ => (12 : Fin 33)

private def transitionChunk1 (index : Nat)
    (generator : Fin 3) : Fin 33 :=
  match index with
  | _ =>
      match generator.val with
      | 0 => (25 : Fin 33)
      | 1 => (22 : Fin 33)
      | _ => (20 : Fin 33)

def transition (state : Fin 33)
    (generator : Fin 3) : Fin 33 :=
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
  | 17 => (0 : Fin 3)
  | 18 => (0 : Fin 3)
  | 19 => (0 : Fin 3)
  | 20 => (0 : Fin 3)
  | 21 => (0 : Fin 3)
  | 22 => (0 : Fin 3)
  | 23 => (0 : Fin 3)
  | 24 => (0 : Fin 3)
  | 25 => (1 : Fin 3)
  | 26 => (0 : Fin 3)
  | 27 => (0 : Fin 3)
  | 28 => (0 : Fin 3)
  | 29 => (0 : Fin 3)
  | 30 => (0 : Fin 3)
  | _ => (0 : Fin 3)

private def representativeHeadChunk1 (index : Nat) : Fin 3 :=
  match index with
  | _ => (0 : Fin 3)

def representativeHead (state : Fin 33) : Fin 3 :=
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
  | 15 => [1, 2]
  | 16 => [2, 2]
  | 17 => [0, 0, 0]
  | 18 => [0, 0, 1]
  | 19 => [0, 0, 2]
  | 20 => [0, 1, 1]
  | 21 => [0, 1, 2]
  | 22 => [0, 2, 2]
  | 23 => [1, 1, 2]
  | 24 => [1, 2, 2]
  | 25 => [1, 2, 2]
  | 26 => [0, 0, 0, 1]
  | 27 => [0, 0, 0, 2]
  | 28 => [0, 0, 1, 2]
  | 29 => [0, 1, 1, 2]
  | 30 => [0, 1, 2, 2]
  | _ => [1, 1, 2, 2]

private def representativeTailChunk1 (index : Nat) :
    List (Fin 3) :=
  match index with
  | _ => [0, 1, 1, 2, 2]

def representativeTail (state : Fin 33) :
    List (Fin 3) :=
  if state.val < 32 then representativeTailChunk0 state.val else
    representativeTailChunk1 (state.val - 32)

private def sourceLabelChunk0 (index : Nat) : Fin 6 :=
  match index with
  | 0 => (4 : Fin 6)
  | 1 => (3 : Fin 6)
  | 2 => (2 : Fin 6)
  | 3 => (5 : Fin 6)
  | 4 => (4 : Fin 6)
  | 5 => (4 : Fin 6)
  | 6 => (0 : Fin 6)
  | 7 => (1 : Fin 6)
  | 8 => (0 : Fin 6)
  | 9 => (0 : Fin 6)
  | 10 => (5 : Fin 6)
  | 11 => (5 : Fin 6)
  | 12 => (4 : Fin 6)
  | 13 => (4 : Fin 6)
  | 14 => (4 : Fin 6)
  | 15 => (0 : Fin 6)
  | 16 => (0 : Fin 6)
  | 17 => (4 : Fin 6)
  | 18 => (0 : Fin 6)
  | 19 => (0 : Fin 6)
  | 20 => (5 : Fin 6)
  | 21 => (5 : Fin 6)
  | 22 => (5 : Fin 6)
  | 23 => (4 : Fin 6)
  | 24 => (4 : Fin 6)
  | 25 => (0 : Fin 6)
  | 26 => (4 : Fin 6)
  | 27 => (4 : Fin 6)
  | 28 => (0 : Fin 6)
  | 29 => (5 : Fin 6)
  | 30 => (5 : Fin 6)
  | _ => (4 : Fin 6)

private def sourceLabelChunk1 (index : Nat) : Fin 6 :=
  match index with
  | _ => (5 : Fin 6)

def sourceLabel (state : Fin 33) : Fin 6 :=
  if state.val < 32 then sourceLabelChunk0 state.val else
    sourceLabelChunk1 (state.val - 32)

def generatorSourceLabel (generator : Fin 3) : Fin 6 :=
  match generator.val with
  | 0 => (4 : Fin 6)
  | 1 => (3 : Fin 6)
  | _ => (2 : Fin 6)

def sourcePreimage (value : Fin 6) : Fin 33 :=
  match value.val with
  | 0 => (6 : Fin 33)
  | 1 => (7 : Fin 33)
  | 2 => (2 : Fin 33)
  | 3 => (1 : Fin 33)
  | 4 => (0 : Fin 33)
  | _ => (3 : Fin 33)

private def stateVectorCode
    (vector : Fin 3 -> Fin 6) : Nat :=
  (vector (0 : Fin 3)).val + 6 * ((vector (1 : Fin 3)).val + 6 * ((vector (2 : Fin 3)).val))

private def decodeStateCode (code : Nat) : Fin 33 :=
  if code < 84 then
    if code < 20 then
      if code < 14 then
        if code < 3 then
          if code < 2 then
            if code = 0 then (9 : Fin 33) else (0 : Fin 33)
          else if code = 2 then (10 : Fin 33) else
            (0 : Fin 33)
        else if code = 3 then (12 : Fin 33) else
          if code = 12 then (6 : Fin 33) else (0 : Fin 33)
      else if code = 14 then (3 : Fin 33) else
        if code < 16 then
          if code = 15 then (26 : Fin 33) else (0 : Fin 33)
        else if code = 16 then (4 : Fin 33) else
          if code = 18 then (18 : Fin 33) else (0 : Fin 33)
    else if code = 20 then (20 : Fin 33) else
      if code < 72 then
        if code < 31 then
          if code = 21 then (17 : Fin 33) else (0 : Fin 33)
        else if code = 31 then (1 : Fin 33) else
          if code = 35 then (0 : Fin 33) else (0 : Fin 33)
      else if code = 72 then (19 : Fin 33) else
        if code < 75 then
          if code = 74 then (21 : Fin 33) else (0 : Fin 33)
        else if code = 75 then (23 : Fin 33) else
          if code = 78 then (2 : Fin 33) else (0 : Fin 33)
  else if code = 84 then (15 : Fin 33) else
    if code < 110 then
      if code < 93 then
        if code < 90 then
          if code < 87 then
            if code = 86 then (11 : Fin 33) else (0 : Fin 33)
          else if code = 87 then (13 : Fin 33) else
            (0 : Fin 33)
        else if code = 90 then (28 : Fin 33) else
          if code = 92 then (29 : Fin 33) else (0 : Fin 33)
      else if code = 93 then (27 : Fin 33) else
        if code < 99 then
          if code = 96 then (7 : Fin 33) else (0 : Fin 33)
        else if code = 99 then (5 : Fin 33) else
          if code = 108 then (8 : Fin 33) else (0 : Fin 33)
    else if code = 110 then (30 : Fin 33) else
      if code < 123 then
        if code < 120 then
          if code = 111 then (31 : Fin 33) else (0 : Fin 33)
        else if code = 120 then (25 : Fin 33) else
          if code = 122 then (22 : Fin 33) else (0 : Fin 33)
      else if code = 123 then (24 : Fin 33) else
        if code < 128 then
          if code = 126 then (16 : Fin 33) else (0 : Fin 33)
        else if code = 128 then (32 : Fin 33) else
          if code = 129 then (14 : Fin 33) else (0 : Fin 33)

private def decodeState
    (vector : Fin 3 -> Fin 6) : Fin 33 :=
  decodeStateCode (stateVectorCode vector)

set_option maxHeartbeats 2000000 in
private theorem decodeState_stateVector (state : Fin 33) :
    decodeState (stateVector state) = state := by
  decide +revert

set_option maxHeartbeats 2000000 in
private theorem transitionMap :
    forall (state : Fin 33)
      (generator : Fin 3)
      (coordinate : Fin 3),
      stateVector (transition state generator) coordinate =
        oppositeTable.semigroup.mul (stateVector state coordinate)
          (generatorVector generator coordinate) := by
  intro state generator coordinate
  apply Fin.ext
  exact by decide +revert

set_option maxHeartbeats 2000000 in
private theorem representativeMap :
    forall (state : Fin 33)
      (coordinate : Fin 3),
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
    (U := Fin 33)
    (G := Fin 3)
    (I := Fin 3) oppositeTable.semigroup where
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
    forall (state : Fin 33)
      (generator : Fin 3),
      sourceLabel (transition state generator) =
        SemigroupBasis.Generated.Order6GenericCASRootData.S6_4336.oppositeTable.semigroup.mul (sourceLabel state)
          (generatorSourceLabel generator) := by
  intro state generator
  apply Fin.ext
  exact by decide +revert

set_option maxHeartbeats 2000000 in
private theorem sourceLabelRepresentative :
    forall state : Fin 33,
      sourceLabel state =
        (representativeTail state).foldl
          (fun value generator =>
            SemigroupBasis.Generated.Order6GenericCASRootData.S6_4336.oppositeTable.semigroup.mul value
              (generatorSourceLabel generator))
          (generatorSourceLabel (representativeHead state)) := by
  intro state
  apply Fin.ext
  exact by decide +revert

private theorem sourceLabelRightMultiplyWord
    (state : Fin 33)
    (word : List (Fin 3)) :
    sourceLabel (powerCertificate.rightMultiplyWord state word) =
      word.foldl
        (fun value generator =>
          SemigroupBasis.Generated.Order6GenericCASRootData.S6_4336.oppositeTable.semigroup.mul value
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
              SemigroupBasis.Generated.Order6GenericCASRootData.S6_4336.oppositeTable.semigroup.mul value
                (generatorSourceLabel nextGenerator))
            (SemigroupBasis.Generated.Order6GenericCASRootData.S6_4336.oppositeTable.semigroup.mul (sourceLabel state)
              (generatorSourceLabel generator))
      rw [inductionHypothesis]
      rw [sourceLabelTransition]

private theorem sourceFoldlGeneratorAssoc
    (left right : Fin 6)
    (word : List (Fin 3)) :
    word.foldl
        (fun value generator =>
          SemigroupBasis.Generated.Order6GenericCASRootData.S6_4336.oppositeTable.semigroup.mul value
            (generatorSourceLabel generator))
        (SemigroupBasis.Generated.Order6GenericCASRootData.S6_4336.oppositeTable.semigroup.mul left right) =
      SemigroupBasis.Generated.Order6GenericCASRootData.S6_4336.oppositeTable.semigroup.mul left
        (word.foldl
          (fun value generator =>
            SemigroupBasis.Generated.Order6GenericCASRootData.S6_4336.oppositeTable.semigroup.mul value
              (generatorSourceLabel generator))
          right) := by
  induction word generalizing right with
  | nil => rfl
  | cons generator word inductionHypothesis =>
      simp only [List.foldl_cons]
      rw [SemigroupBasis.Generated.Order6GenericCASRootData.S6_4336.oppositeTable.semigroup.assoc]
      exact inductionHypothesis
        (SemigroupBasis.Generated.Order6GenericCASRootData.S6_4336.oppositeTable.semigroup.mul right (generatorSourceLabel generator))

private theorem sourceLabelMapMul :
    forall (left right : Fin 33),
      sourceLabel (powerCertificate.semigroup.mul left right) =
        SemigroupBasis.Generated.Order6GenericCASRootData.S6_4336.oppositeTable.semigroup.mul (sourceLabel left) (sourceLabel right) := by
  intro left right
  calc
    sourceLabel (powerCertificate.semigroup.mul left right) =
        sourceLabel
          (powerCertificate.rightMultiplyWord
            (transition left (representativeHead right))
            (representativeTail right)) := rfl
    _ = (representativeTail right).foldl
          (fun value generator =>
            SemigroupBasis.Generated.Order6GenericCASRootData.S6_4336.oppositeTable.semigroup.mul value
              (generatorSourceLabel generator))
          (sourceLabel (transition left (representativeHead right))) :=
      sourceLabelRightMultiplyWord _ _
    _ = (representativeTail right).foldl
          (fun value generator =>
            SemigroupBasis.Generated.Order6GenericCASRootData.S6_4336.oppositeTable.semigroup.mul value
              (generatorSourceLabel generator))
          (SemigroupBasis.Generated.Order6GenericCASRootData.S6_4336.oppositeTable.semigroup.mul (sourceLabel left)
            (generatorSourceLabel (representativeHead right))) :=
      congrArg
        (fun initial =>
          (representativeTail right).foldl
            (fun value generator =>
              SemigroupBasis.Generated.Order6GenericCASRootData.S6_4336.oppositeTable.semigroup.mul value
                (generatorSourceLabel generator))
            initial)
        (sourceLabelTransition left (representativeHead right))
    _ = SemigroupBasis.Generated.Order6GenericCASRootData.S6_4336.oppositeTable.semigroup.mul (sourceLabel left)
          ((representativeTail right).foldl
            (fun value generator =>
              SemigroupBasis.Generated.Order6GenericCASRootData.S6_4336.oppositeTable.semigroup.mul value
                (generatorSourceLabel generator))
            (generatorSourceLabel (representativeHead right))) :=
      sourceFoldlGeneratorAssoc _ _ _
    _ = SemigroupBasis.Generated.Order6GenericCASRootData.S6_4336.oppositeTable.semigroup.mul (sourceLabel left) (sourceLabel right) :=
      congrArg (SemigroupBasis.Generated.Order6GenericCASRootData.S6_4336.oppositeTable.semigroup.mul (sourceLabel left))
        (sourceLabelRepresentative right).symm

set_option maxHeartbeats 1000000 in
private theorem sourceLabelRightInverse :
    forall value : Fin 6, sourceLabel (sourcePreimage value) = value := by
  intro value
  apply Fin.ext
  exact by decide +revert

/-- The generated term-function semigroup maps onto the selected root. -/
def quotient : SplitSurjection powerCertificate.semigroup
    SemigroupBasis.Generated.Order6GenericCASRootData.S6_4336.oppositeTable.semigroup where
  toFun := sourceLabel
  map_mul := sourceLabelMapMul
  preimage := sourcePreimage
  right_inverse := sourceLabelRightInverse

private def targetLaw0ToFinite : Nat -> Fin 1
  | 0 => (0 : Fin 1)
  | _ => (0 : Fin 1)

private def targetLaw0FromFinite (index : Fin 1) : Nat :=
  match index.val with
  | 0 => 0
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
private theorem targetLaw0Valid :
    SemigroupBasis.Generated.Order6GenericCASRootData.S6_4336.law0.SatisfiedBy oppositeTable.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    oppositeTable SemigroupBasis.Generated.Order6GenericCASRootData.S6_4336.law0
    targetLaw0ToFinite targetLaw0FromFinite (by decide) (by decide)

private def targetLaw1ToFinite : Nat -> Fin 2
  | 0 => (0 : Fin 2)
  | 1 => (1 : Fin 2)
  | _ => (0 : Fin 2)

private def targetLaw1FromFinite (index : Fin 2) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
private theorem targetLaw1Valid :
    SemigroupBasis.Generated.Order6GenericCASRootData.S6_4336.law1.SatisfiedBy oppositeTable.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    oppositeTable SemigroupBasis.Generated.Order6GenericCASRootData.S6_4336.law1
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
    SemigroupBasis.Generated.Order6GenericCASRootData.S6_4336.law2.SatisfiedBy oppositeTable.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    oppositeTable SemigroupBasis.Generated.Order6GenericCASRootData.S6_4336.law2
    targetLaw2ToFinite targetLaw2FromFinite (by decide) (by decide)

private def targetLaw3ToFinite : Nat -> Fin 3
  | 0 => (0 : Fin 3)
  | 1 => (1 : Fin 3)
  | 2 => (2 : Fin 3)
  | _ => (0 : Fin 3)

private def targetLaw3FromFinite (index : Fin 3) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
private theorem targetLaw3Valid :
    SemigroupBasis.Generated.Order6GenericCASRootData.S6_4336.law3.SatisfiedBy oppositeTable.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    oppositeTable SemigroupBasis.Generated.Order6GenericCASRootData.S6_4336.law3
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
    SemigroupBasis.Generated.Order6GenericCASRootData.S6_4336.law4.SatisfiedBy oppositeTable.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    oppositeTable SemigroupBasis.Generated.Order6GenericCASRootData.S6_4336.law4
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
    SemigroupBasis.Generated.Order6GenericCASRootData.S6_4336.law5.SatisfiedBy oppositeTable.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    oppositeTable SemigroupBasis.Generated.Order6GenericCASRootData.S6_4336.law5
    targetLaw5ToFinite targetLaw5FromFinite (by decide) (by decide)

/-- Exact finite checks that the selected target models the root basis. -/
theorem targetModels :
    Models oppositeTable.semigroup SemigroupBasis.Generated.Order6GenericCASRootData.S6_4336.basis := by
  unfold SemigroupBasis.Generated.Order6GenericCASRootData.S6_4336.basis
  exact
    FiniteNilpotentCounterexample.models_cons targetLaw0Valid <|
      FiniteNilpotentCounterexample.models_cons targetLaw1Valid <|
        FiniteNilpotentCounterexample.models_cons targetLaw2Valid <|
          FiniteNilpotentCounterexample.models_cons targetLaw3Valid <|
            FiniteNilpotentCounterexample.models_cons targetLaw4Valid <|
              FiniteNilpotentCounterexample.models_cons targetLaw5Valid <|
                FiniteNilpotentCounterexample.models_nil oppositeTable.semigroup

/-- Exact identity-theory transfer authenticated by the finite certificate. -/
theorem sameIdentityTheory :
    SameIdentityTheoryOver SemigroupBasis.Generated.Order6GenericCASRootData.S6_4336.oppositeTable.semigroup
      oppositeTable.semigroup Nat := by
  intro identity
  constructor
  · intro sourceValid valuation
    exact Derives.sound targetModels
      (SemigroupBasis.CoRoots.Order6GenericCASSubdirectS6_4336.basisFor.2 identity sourceValid) valuation
  · intro targetValid
    have powerValid :=
      identity.satisfiedByPi oppositeTable.semigroup
        (Fin 3) targetValid
    have subValid :=
      powerCertificate.embedding.pullback_identity identity powerValid
    exact quotient.pushforwardIdentity identity subValid

/-- First-layer generic-CAS basis wrapper for `S6_14992`. -/
theorem opposite_basis :
    BasisFor table.semigroup.opposite SemigroupBasis.Generated.Order6GenericCASRootData.S6_4336.basis := by
  have transferred :
      BasisFor oppositeTable.semigroup SemigroupBasis.Generated.Order6GenericCASRootData.S6_4336.basis :=
    (basisFor_iff_of_sameIdentityTheoryOver sameIdentityTheory).mp
      SemigroupBasis.CoRoots.Order6GenericCASSubdirectS6_4336.basisFor
  simpa only [oppositeTable_semigroup] using transferred

end SemigroupBasis.Generated.Order6GenericCASRootWrappers.S6_14992
