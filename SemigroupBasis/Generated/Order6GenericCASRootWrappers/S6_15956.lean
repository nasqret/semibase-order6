import SemigroupBasis.CoRoots.Order6GenericCASMonoidPower
import SemigroupBasis.Nonfinite
import SemigroupBasis.Opposite
import SemigroupBasis.RightGeneratedPowerCertificate

set_option maxRecDepth 2048

namespace SemigroupBasis.Generated.Order6GenericCASRootWrappers.S6_15956

open SemigroupBasis

def routeManifestRowSHA256 : String := "52a9a7893d10cc46f0260950bcee5fd447dfdbb83923928030566dfefef3601e"
def witnessRecordSHA256 : String := "63f6815ab62805bf17538be52665e547f81ed347810313bdf934a836665d5a96"
def transferComponentSHA256 : String := "7349273e2a4681c1352329cd1ca40066c7dd9d287a5294cd67f7912851022dd2"
def powerCertificateSHA256 : String := "5de0c2d3d63e40617bbccd117d9af6dc845c6dd55ba9eeaabbfcd416cbc8b013"

private def row6
    (c0 c1 c2 c3 c4 c5 : Fin 6) (column : Fin 6) : Fin 6 :=
  if column = 0 then c0 else
    if column = 1 then c1 else
      if column = 2 then c2 else
        if column = 3 then c3 else
          if column = 4 then c4 else c5

/-- Exact one-based catalogue table committed by the portable witness. -/
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 2 3 3 2 right else
    if left = 1 then row6 0 1 2 3 4 5 right else
      if left = 2 then row6 2 2 3 0 0 3 right else
        if left = 3 then row6 3 3 0 2 2 0 right else
          if left = 4 then row6 3 4 0 2 2 0 right else
            row6 2 5 3 0 0 4 right

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
  "44c3ab74b92b86ef48a0865f4503d163a7ee0905c1727166185b0ab01e3c687c"

private def stateVectorChunk0 (index : Nat)
    (coordinate : Fin 2) : Fin 6 :=
  match index with
  | 0 =>
      match coordinate.val with
      | 0 => (5 : Fin 6)
      | _ => (1 : Fin 6)
  | 1 =>
      match coordinate.val with
      | 0 => (1 : Fin 6)
      | _ => (5 : Fin 6)
  | 2 =>
      match coordinate.val with
      | 0 => (4 : Fin 6)
      | _ => (1 : Fin 6)
  | 3 =>
      match coordinate.val with
      | 0 => (5 : Fin 6)
      | _ => (5 : Fin 6)
  | 4 =>
      match coordinate.val with
      | 0 => (1 : Fin 6)
      | _ => (4 : Fin 6)
  | 5 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | _ => (1 : Fin 6)
  | 6 =>
      match coordinate.val with
      | 0 => (4 : Fin 6)
      | _ => (5 : Fin 6)
  | 7 =>
      match coordinate.val with
      | 0 => (5 : Fin 6)
      | _ => (4 : Fin 6)
  | 8 =>
      match coordinate.val with
      | 0 => (1 : Fin 6)
      | _ => (0 : Fin 6)
  | 9 =>
      match coordinate.val with
      | 0 => (2 : Fin 6)
      | _ => (1 : Fin 6)
  | 10 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | _ => (5 : Fin 6)
  | 11 =>
      match coordinate.val with
      | 0 => (4 : Fin 6)
      | _ => (4 : Fin 6)
  | 12 =>
      match coordinate.val with
      | 0 => (5 : Fin 6)
      | _ => (0 : Fin 6)
  | 13 =>
      match coordinate.val with
      | 0 => (1 : Fin 6)
      | _ => (2 : Fin 6)
  | 14 =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | _ => (1 : Fin 6)
  | 15 =>
      match coordinate.val with
      | 0 => (2 : Fin 6)
      | _ => (5 : Fin 6)
  | 16 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | _ => (4 : Fin 6)
  | 17 =>
      match coordinate.val with
      | 0 => (4 : Fin 6)
      | _ => (0 : Fin 6)
  | 18 =>
      match coordinate.val with
      | 0 => (5 : Fin 6)
      | _ => (2 : Fin 6)
  | 19 =>
      match coordinate.val with
      | 0 => (1 : Fin 6)
      | _ => (3 : Fin 6)
  | 20 =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | _ => (5 : Fin 6)
  | 21 =>
      match coordinate.val with
      | 0 => (2 : Fin 6)
      | _ => (4 : Fin 6)
  | 22 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | _ => (0 : Fin 6)
  | 23 =>
      match coordinate.val with
      | 0 => (4 : Fin 6)
      | _ => (2 : Fin 6)
  | 24 =>
      match coordinate.val with
      | 0 => (5 : Fin 6)
      | _ => (3 : Fin 6)
  | 25 =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | _ => (4 : Fin 6)
  | 26 =>
      match coordinate.val with
      | 0 => (2 : Fin 6)
      | _ => (0 : Fin 6)
  | 27 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | _ => (2 : Fin 6)
  | 28 =>
      match coordinate.val with
      | 0 => (4 : Fin 6)
      | _ => (3 : Fin 6)
  | 29 =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | _ => (0 : Fin 6)
  | 30 =>
      match coordinate.val with
      | 0 => (2 : Fin 6)
      | _ => (2 : Fin 6)
  | _ =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | _ => (3 : Fin 6)

private def stateVectorChunk1 (index : Nat)
    (coordinate : Fin 2) : Fin 6 :=
  match index with
  | 0 =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | _ => (2 : Fin 6)
  | 1 =>
      match coordinate.val with
      | 0 => (2 : Fin 6)
      | _ => (3 : Fin 6)
  | _ =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | _ => (3 : Fin 6)

def stateVector (state : Fin 35)
    (coordinate : Fin 2) : Fin 6 :=
  if state.val < 32 then stateVectorChunk0 state.val coordinate else
    stateVectorChunk1 (state.val - 32) coordinate

def generatorVector (generator : Fin 2)
    (coordinate : Fin 2) : Fin 6 :=
  match generator.val with
  | 0 =>
      match coordinate.val with
      | 0 => (5 : Fin 6)
      | _ => (1 : Fin 6)
  | _ =>
      match coordinate.val with
      | 0 => (1 : Fin 6)
      | _ => (5 : Fin 6)

private def transitionChunk0 (index : Nat)
    (generator : Fin 2) : Fin 35 :=
  match index with
  | 0 =>
      match generator.val with
      | 0 => (2 : Fin 35)
      | _ => (3 : Fin 35)
  | 1 =>
      match generator.val with
      | 0 => (3 : Fin 35)
      | _ => (4 : Fin 35)
  | 2 =>
      match generator.val with
      | 0 => (5 : Fin 35)
      | _ => (6 : Fin 35)
  | 3 =>
      match generator.val with
      | 0 => (6 : Fin 35)
      | _ => (7 : Fin 35)
  | 4 =>
      match generator.val with
      | 0 => (7 : Fin 35)
      | _ => (8 : Fin 35)
  | 5 =>
      match generator.val with
      | 0 => (9 : Fin 35)
      | _ => (10 : Fin 35)
  | 6 =>
      match generator.val with
      | 0 => (10 : Fin 35)
      | _ => (11 : Fin 35)
  | 7 =>
      match generator.val with
      | 0 => (11 : Fin 35)
      | _ => (12 : Fin 35)
  | 8 =>
      match generator.val with
      | 0 => (12 : Fin 35)
      | _ => (13 : Fin 35)
  | 9 =>
      match generator.val with
      | 0 => (14 : Fin 35)
      | _ => (15 : Fin 35)
  | 10 =>
      match generator.val with
      | 0 => (15 : Fin 35)
      | _ => (16 : Fin 35)
  | 11 =>
      match generator.val with
      | 0 => (16 : Fin 35)
      | _ => (17 : Fin 35)
  | 12 =>
      match generator.val with
      | 0 => (17 : Fin 35)
      | _ => (18 : Fin 35)
  | 13 =>
      match generator.val with
      | 0 => (18 : Fin 35)
      | _ => (19 : Fin 35)
  | 14 =>
      match generator.val with
      | 0 => (5 : Fin 35)
      | _ => (20 : Fin 35)
  | 15 =>
      match generator.val with
      | 0 => (20 : Fin 35)
      | _ => (21 : Fin 35)
  | 16 =>
      match generator.val with
      | 0 => (21 : Fin 35)
      | _ => (22 : Fin 35)
  | 17 =>
      match generator.val with
      | 0 => (22 : Fin 35)
      | _ => (23 : Fin 35)
  | 18 =>
      match generator.val with
      | 0 => (23 : Fin 35)
      | _ => (24 : Fin 35)
  | 19 =>
      match generator.val with
      | 0 => (24 : Fin 35)
      | _ => (8 : Fin 35)
  | 20 =>
      match generator.val with
      | 0 => (10 : Fin 35)
      | _ => (25 : Fin 35)
  | 21 =>
      match generator.val with
      | 0 => (25 : Fin 35)
      | _ => (26 : Fin 35)
  | 22 =>
      match generator.val with
      | 0 => (26 : Fin 35)
      | _ => (27 : Fin 35)
  | 23 =>
      match generator.val with
      | 0 => (27 : Fin 35)
      | _ => (28 : Fin 35)
  | 24 =>
      match generator.val with
      | 0 => (28 : Fin 35)
      | _ => (12 : Fin 35)
  | 25 =>
      match generator.val with
      | 0 => (16 : Fin 35)
      | _ => (29 : Fin 35)
  | 26 =>
      match generator.val with
      | 0 => (29 : Fin 35)
      | _ => (30 : Fin 35)
  | 27 =>
      match generator.val with
      | 0 => (30 : Fin 35)
      | _ => (31 : Fin 35)
  | 28 =>
      match generator.val with
      | 0 => (31 : Fin 35)
      | _ => (17 : Fin 35)
  | 29 =>
      match generator.val with
      | 0 => (22 : Fin 35)
      | _ => (32 : Fin 35)
  | 30 =>
      match generator.val with
      | 0 => (32 : Fin 35)
      | _ => (33 : Fin 35)
  | _ =>
      match generator.val with
      | 0 => (33 : Fin 35)
      | _ => (22 : Fin 35)

private def transitionChunk1 (index : Nat)
    (generator : Fin 2) : Fin 35 :=
  match index with
  | 0 =>
      match generator.val with
      | 0 => (27 : Fin 35)
      | _ => (34 : Fin 35)
  | 1 =>
      match generator.val with
      | 0 => (34 : Fin 35)
      | _ => (26 : Fin 35)
  | _ =>
      match generator.val with
      | 0 => (31 : Fin 35)
      | _ => (29 : Fin 35)

def transition (state : Fin 35)
    (generator : Fin 2) : Fin 35 :=
  if state.val < 32 then transitionChunk0 state.val generator else
    transitionChunk1 (state.val - 32) generator

private def representativeHeadChunk0 (index : Nat) : Fin 2 :=
  match index with
  | 0 => (0 : Fin 2)
  | 1 => (1 : Fin 2)
  | 2 => (0 : Fin 2)
  | 3 => (0 : Fin 2)
  | 4 => (1 : Fin 2)
  | 5 => (0 : Fin 2)
  | 6 => (0 : Fin 2)
  | 7 => (0 : Fin 2)
  | 8 => (1 : Fin 2)
  | 9 => (0 : Fin 2)
  | 10 => (0 : Fin 2)
  | 11 => (0 : Fin 2)
  | 12 => (0 : Fin 2)
  | 13 => (1 : Fin 2)
  | 14 => (0 : Fin 2)
  | 15 => (0 : Fin 2)
  | 16 => (0 : Fin 2)
  | 17 => (0 : Fin 2)
  | 18 => (0 : Fin 2)
  | 19 => (1 : Fin 2)
  | 20 => (0 : Fin 2)
  | 21 => (0 : Fin 2)
  | 22 => (0 : Fin 2)
  | 23 => (0 : Fin 2)
  | 24 => (0 : Fin 2)
  | 25 => (0 : Fin 2)
  | 26 => (0 : Fin 2)
  | 27 => (0 : Fin 2)
  | 28 => (0 : Fin 2)
  | 29 => (0 : Fin 2)
  | 30 => (0 : Fin 2)
  | _ => (0 : Fin 2)

private def representativeHeadChunk1 (index : Nat) : Fin 2 :=
  match index with
  | 0 => (0 : Fin 2)
  | 1 => (0 : Fin 2)
  | _ => (0 : Fin 2)

def representativeHead (state : Fin 35) : Fin 2 :=
  if state.val < 32 then representativeHeadChunk0 state.val else
    representativeHeadChunk1 (state.val - 32)

private def representativeTailChunk0 (index : Nat) :
    List (Fin 2) :=
  match index with
  | 0 => []
  | 1 => []
  | 2 => [0]
  | 3 => [1]
  | 4 => [1]
  | 5 => [0, 0]
  | 6 => [0, 1]
  | 7 => [1, 1]
  | 8 => [1, 1]
  | 9 => [0, 0, 0]
  | 10 => [0, 0, 1]
  | 11 => [0, 1, 1]
  | 12 => [1, 1, 1]
  | 13 => [1, 1, 1]
  | 14 => [0, 0, 0, 0]
  | 15 => [0, 0, 0, 1]
  | 16 => [0, 0, 1, 1]
  | 17 => [0, 1, 1, 1]
  | 18 => [1, 1, 1, 1]
  | 19 => [1, 1, 1, 1]
  | 20 => [0, 0, 0, 0, 1]
  | 21 => [0, 0, 0, 1, 1]
  | 22 => [0, 0, 1, 1, 1]
  | 23 => [0, 1, 1, 1, 1]
  | 24 => [1, 1, 1, 1, 1]
  | 25 => [0, 0, 0, 0, 1, 1]
  | 26 => [0, 0, 0, 1, 1, 1]
  | 27 => [0, 0, 1, 1, 1, 1]
  | 28 => [0, 1, 1, 1, 1, 1]
  | 29 => [0, 0, 0, 0, 1, 1, 1]
  | 30 => [0, 0, 0, 1, 1, 1, 1]
  | _ => [0, 0, 1, 1, 1, 1, 1]

private def representativeTailChunk1 (index : Nat) :
    List (Fin 2) :=
  match index with
  | 0 => [0, 0, 0, 0, 1, 1, 1, 1]
  | 1 => [0, 0, 0, 1, 1, 1, 1, 1]
  | _ => [0, 0, 0, 0, 1, 1, 1, 1, 1]

def representativeTail (state : Fin 35) :
    List (Fin 2) :=
  if state.val < 32 then representativeTailChunk0 state.val else
    representativeTailChunk1 (state.val - 32)

private def sourceLabelChunk0 (index : Nat) : Fin 6 :=
  match index with
  | 0 => (4 : Fin 6)
  | 1 => (2 : Fin 6)
  | 2 => (5 : Fin 6)
  | 3 => (2 : Fin 6)
  | 4 => (1 : Fin 6)
  | 5 => (3 : Fin 6)
  | 6 => (2 : Fin 6)
  | 7 => (1 : Fin 6)
  | 8 => (0 : Fin 6)
  | 9 => (4 : Fin 6)
  | 10 => (2 : Fin 6)
  | 11 => (1 : Fin 6)
  | 12 => (0 : Fin 6)
  | 13 => (0 : Fin 6)
  | 14 => (5 : Fin 6)
  | 15 => (2 : Fin 6)
  | 16 => (1 : Fin 6)
  | 17 => (0 : Fin 6)
  | 18 => (0 : Fin 6)
  | 19 => (0 : Fin 6)
  | 20 => (2 : Fin 6)
  | 21 => (1 : Fin 6)
  | 22 => (0 : Fin 6)
  | 23 => (0 : Fin 6)
  | 24 => (0 : Fin 6)
  | 25 => (1 : Fin 6)
  | 26 => (0 : Fin 6)
  | 27 => (0 : Fin 6)
  | 28 => (0 : Fin 6)
  | 29 => (0 : Fin 6)
  | 30 => (0 : Fin 6)
  | _ => (0 : Fin 6)

private def sourceLabelChunk1 (index : Nat) : Fin 6 :=
  match index with
  | 0 => (0 : Fin 6)
  | 1 => (0 : Fin 6)
  | _ => (0 : Fin 6)

def sourceLabel (state : Fin 35) : Fin 6 :=
  if state.val < 32 then sourceLabelChunk0 state.val else
    sourceLabelChunk1 (state.val - 32)

def generatorSourceLabel (generator : Fin 2) : Fin 6 :=
  match generator.val with
  | 0 => (4 : Fin 6)
  | _ => (2 : Fin 6)

def sourcePreimage (value : Fin 6) : Fin 35 :=
  match value.val with
  | 0 => (8 : Fin 35)
  | 1 => (4 : Fin 35)
  | 2 => (1 : Fin 35)
  | 3 => (5 : Fin 35)
  | 4 => (0 : Fin 35)
  | _ => (2 : Fin 35)

private def stateVectorCode
    (vector : Fin 2 -> Fin 6) : Nat :=
  (vector (0 : Fin 2)).val + 6 * ((vector (1 : Fin 2)).val)

private def decodeStateCode (code : Nat) : Fin 35 :=
  if code < 18 then
    if code < 9 then
      if code < 4 then
        if code < 2 then
          if code < 1 then
            if code = 0 then (22 : Fin 35) else (0 : Fin 35)
          else if code = 1 then (8 : Fin 35) else
            (0 : Fin 35)
        else if code = 2 then (26 : Fin 35) else
          if code = 3 then (29 : Fin 35) else (0 : Fin 35)
      else if code = 4 then (17 : Fin 35) else
        if code < 6 then
          if code = 5 then (12 : Fin 35) else (0 : Fin 35)
        else if code = 6 then (5 : Fin 35) else
          if code = 8 then (9 : Fin 35) else (0 : Fin 35)
    else if code = 9 then (14 : Fin 35) else
      if code < 14 then
        if code < 12 then
          if code < 11 then
            if code = 10 then (2 : Fin 35) else (0 : Fin 35)
          else if code = 11 then (0 : Fin 35) else
            (0 : Fin 35)
        else if code = 12 then (27 : Fin 35) else
          if code = 13 then (13 : Fin 35) else (0 : Fin 35)
      else if code = 14 then (30 : Fin 35) else
        if code < 16 then
          if code = 15 then (32 : Fin 35) else (0 : Fin 35)
        else if code = 16 then (23 : Fin 35) else
          if code = 17 then (18 : Fin 35) else (0 : Fin 35)
  else if code = 18 then (31 : Fin 35) else
    if code < 27 then
      if code < 23 then
        if code < 21 then
          if code < 20 then
            if code = 19 then (19 : Fin 35) else (0 : Fin 35)
          else if code = 20 then (33 : Fin 35) else
            (0 : Fin 35)
        else if code = 21 then (34 : Fin 35) else
          if code = 22 then (28 : Fin 35) else (0 : Fin 35)
      else if code = 23 then (24 : Fin 35) else
        if code < 25 then
          if code = 24 then (16 : Fin 35) else (0 : Fin 35)
        else if code = 25 then (4 : Fin 35) else
          if code = 26 then (21 : Fin 35) else (0 : Fin 35)
    else if code = 27 then (25 : Fin 35) else
      if code < 32 then
        if code < 30 then
          if code < 29 then
            if code = 28 then (11 : Fin 35) else (0 : Fin 35)
          else if code = 29 then (7 : Fin 35) else
            (0 : Fin 35)
        else if code = 30 then (10 : Fin 35) else
          if code = 31 then (1 : Fin 35) else (0 : Fin 35)
      else if code = 32 then (15 : Fin 35) else
        if code < 34 then
          if code = 33 then (20 : Fin 35) else (0 : Fin 35)
        else if code = 34 then (6 : Fin 35) else
          if code = 35 then (3 : Fin 35) else (0 : Fin 35)

private def decodeState
    (vector : Fin 2 -> Fin 6) : Fin 35 :=
  decodeStateCode (stateVectorCode vector)

set_option maxHeartbeats 2000000 in
private theorem decodeState_stateVector (state : Fin 35) :
    decodeState (stateVector state) = state := by
  decide +revert

set_option maxHeartbeats 2000000 in
private theorem transitionMap :
    forall (state : Fin 35)
      (generator : Fin 2)
      (coordinate : Fin 2),
      stateVector (transition state generator) coordinate =
        oppositeTable.semigroup.mul (stateVector state coordinate)
          (generatorVector generator coordinate) := by
  intro state generator coordinate
  apply Fin.ext
  exact by decide +revert

set_option maxHeartbeats 2000000 in
private theorem representativeMap :
    forall (state : Fin 35)
      (coordinate : Fin 2),
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
    (U := Fin 35)
    (G := Fin 2)
    (I := Fin 2) oppositeTable.semigroup where
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
    forall (state : Fin 35)
      (generator : Fin 2),
      sourceLabel (transition state generator) =
        SemigroupBasis.Generated.Order6GenericCASRootData.S6_9801.oppositeTable.semigroup.mul (sourceLabel state)
          (generatorSourceLabel generator) := by
  intro state generator
  apply Fin.ext
  exact by decide +revert

set_option maxHeartbeats 2000000 in
private theorem sourceLabelRepresentative :
    forall state : Fin 35,
      sourceLabel state =
        (representativeTail state).foldl
          (fun value generator =>
            SemigroupBasis.Generated.Order6GenericCASRootData.S6_9801.oppositeTable.semigroup.mul value
              (generatorSourceLabel generator))
          (generatorSourceLabel (representativeHead state)) := by
  intro state
  apply Fin.ext
  exact by decide +revert

private theorem sourceLabelRightMultiplyWord
    (state : Fin 35)
    (word : List (Fin 2)) :
    sourceLabel (powerCertificate.rightMultiplyWord state word) =
      word.foldl
        (fun value generator =>
          SemigroupBasis.Generated.Order6GenericCASRootData.S6_9801.oppositeTable.semigroup.mul value
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
              SemigroupBasis.Generated.Order6GenericCASRootData.S6_9801.oppositeTable.semigroup.mul value
                (generatorSourceLabel nextGenerator))
            (SemigroupBasis.Generated.Order6GenericCASRootData.S6_9801.oppositeTable.semigroup.mul (sourceLabel state)
              (generatorSourceLabel generator))
      rw [inductionHypothesis]
      rw [sourceLabelTransition]

private theorem sourceFoldlGeneratorAssoc
    (left right : Fin 6)
    (word : List (Fin 2)) :
    word.foldl
        (fun value generator =>
          SemigroupBasis.Generated.Order6GenericCASRootData.S6_9801.oppositeTable.semigroup.mul value
            (generatorSourceLabel generator))
        (SemigroupBasis.Generated.Order6GenericCASRootData.S6_9801.oppositeTable.semigroup.mul left right) =
      SemigroupBasis.Generated.Order6GenericCASRootData.S6_9801.oppositeTable.semigroup.mul left
        (word.foldl
          (fun value generator =>
            SemigroupBasis.Generated.Order6GenericCASRootData.S6_9801.oppositeTable.semigroup.mul value
              (generatorSourceLabel generator))
          right) := by
  induction word generalizing right with
  | nil => rfl
  | cons generator word inductionHypothesis =>
      simp only [List.foldl_cons]
      rw [SemigroupBasis.Generated.Order6GenericCASRootData.S6_9801.oppositeTable.semigroup.assoc]
      exact inductionHypothesis
        (SemigroupBasis.Generated.Order6GenericCASRootData.S6_9801.oppositeTable.semigroup.mul right (generatorSourceLabel generator))

private theorem sourceLabelMapMul :
    forall (left right : Fin 35),
      sourceLabel (powerCertificate.semigroup.mul left right) =
        SemigroupBasis.Generated.Order6GenericCASRootData.S6_9801.oppositeTable.semigroup.mul (sourceLabel left) (sourceLabel right) := by
  intro left right
  calc
    sourceLabel (powerCertificate.semigroup.mul left right) =
        sourceLabel
          (powerCertificate.rightMultiplyWord
            (transition left (representativeHead right))
            (representativeTail right)) := rfl
    _ = (representativeTail right).foldl
          (fun value generator =>
            SemigroupBasis.Generated.Order6GenericCASRootData.S6_9801.oppositeTable.semigroup.mul value
              (generatorSourceLabel generator))
          (sourceLabel (transition left (representativeHead right))) :=
      sourceLabelRightMultiplyWord _ _
    _ = (representativeTail right).foldl
          (fun value generator =>
            SemigroupBasis.Generated.Order6GenericCASRootData.S6_9801.oppositeTable.semigroup.mul value
              (generatorSourceLabel generator))
          (SemigroupBasis.Generated.Order6GenericCASRootData.S6_9801.oppositeTable.semigroup.mul (sourceLabel left)
            (generatorSourceLabel (representativeHead right))) :=
      congrArg
        (fun initial =>
          (representativeTail right).foldl
            (fun value generator =>
              SemigroupBasis.Generated.Order6GenericCASRootData.S6_9801.oppositeTable.semigroup.mul value
                (generatorSourceLabel generator))
            initial)
        (sourceLabelTransition left (representativeHead right))
    _ = SemigroupBasis.Generated.Order6GenericCASRootData.S6_9801.oppositeTable.semigroup.mul (sourceLabel left)
          ((representativeTail right).foldl
            (fun value generator =>
              SemigroupBasis.Generated.Order6GenericCASRootData.S6_9801.oppositeTable.semigroup.mul value
                (generatorSourceLabel generator))
            (generatorSourceLabel (representativeHead right))) :=
      sourceFoldlGeneratorAssoc _ _ _
    _ = SemigroupBasis.Generated.Order6GenericCASRootData.S6_9801.oppositeTable.semigroup.mul (sourceLabel left) (sourceLabel right) :=
      congrArg (SemigroupBasis.Generated.Order6GenericCASRootData.S6_9801.oppositeTable.semigroup.mul (sourceLabel left))
        (sourceLabelRepresentative right).symm

set_option maxHeartbeats 1000000 in
private theorem sourceLabelRightInverse :
    forall value : Fin 6, sourceLabel (sourcePreimage value) = value := by
  intro value
  apply Fin.ext
  exact by decide +revert

/-- The generated term-function semigroup maps onto the selected root. -/
def quotient : SplitSurjection powerCertificate.semigroup
    SemigroupBasis.Generated.Order6GenericCASRootData.S6_9801.oppositeTable.semigroup where
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
    SemigroupBasis.Generated.Order6GenericCASRootData.S6_9801.law0.SatisfiedBy oppositeTable.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    oppositeTable SemigroupBasis.Generated.Order6GenericCASRootData.S6_9801.law0
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
    SemigroupBasis.Generated.Order6GenericCASRootData.S6_9801.law1.SatisfiedBy oppositeTable.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    oppositeTable SemigroupBasis.Generated.Order6GenericCASRootData.S6_9801.law1
    targetLaw1ToFinite targetLaw1FromFinite (by decide) (by decide)

/-- Exact finite checks that the selected target models the root basis. -/
theorem targetModels :
    Models oppositeTable.semigroup SemigroupBasis.Generated.Order6GenericCASRootData.S6_9801.basis := by
  unfold SemigroupBasis.Generated.Order6GenericCASRootData.S6_9801.basis
  exact
    FiniteNilpotentCounterexample.models_cons targetLaw0Valid <|
      FiniteNilpotentCounterexample.models_cons targetLaw1Valid <|
        FiniteNilpotentCounterexample.models_nil oppositeTable.semigroup

/-- Exact identity-theory transfer authenticated by the finite certificate. -/
theorem sameIdentityTheory :
    SameIdentityTheoryOver SemigroupBasis.Generated.Order6GenericCASRootData.S6_9801.oppositeTable.semigroup
      oppositeTable.semigroup Nat := by
  intro identity
  constructor
  · intro sourceValid valuation
    exact Derives.sound targetModels
      (SemigroupBasis.CoRoots.Order6GenericCASMonoidPower.S6_9801_oppositeBasisFor.2 identity sourceValid) valuation
  · intro targetValid
    have powerValid :=
      identity.satisfiedByPi oppositeTable.semigroup
        (Fin 2) targetValid
    have subValid :=
      powerCertificate.embedding.pullback_identity identity powerValid
    exact quotient.pushforwardIdentity identity subValid

/-- First-layer generic-CAS basis wrapper for `S6_15956`. -/
theorem opposite_basis :
    BasisFor table.semigroup.opposite SemigroupBasis.Generated.Order6GenericCASRootData.S6_9801.basis := by
  have transferred :
      BasisFor oppositeTable.semigroup SemigroupBasis.Generated.Order6GenericCASRootData.S6_9801.basis :=
    (basisFor_iff_of_sameIdentityTheoryOver sameIdentityTheory).mp
      SemigroupBasis.CoRoots.Order6GenericCASMonoidPower.S6_9801_oppositeBasisFor
  simpa only [oppositeTable_semigroup] using transferred

end SemigroupBasis.Generated.Order6GenericCASRootWrappers.S6_15956
