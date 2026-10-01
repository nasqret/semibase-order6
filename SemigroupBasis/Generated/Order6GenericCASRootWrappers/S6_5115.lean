import SemigroupBasis.CoRoots.Order6GenericCASSubdirectS6_5113
import SemigroupBasis.Nonfinite
import SemigroupBasis.Opposite
import SemigroupBasis.RightGeneratedPowerCertificate

set_option maxRecDepth 2048

namespace SemigroupBasis.Generated.Order6GenericCASRootWrappers.S6_5115

open SemigroupBasis

def routeManifestRowSHA256 : String := "7b354243e3553687008b5ad184158bb268921ee9b18ef9c65c014e8063d87eb8"
def witnessRecordSHA256 : String := "7909e3f917e566d18fdf865a7127cdfdd2d6b83fe8e8fad6908e2a4fb6d5b638"
def transferComponentSHA256 : String := "b7df00658e3fa3ca321d415eb316a9bd02e195df7244d9ed583a324b9d91e18e"
def powerCertificateSHA256 : String := "f754e8c3d0a656cb79afb70c5970b553286773b6c75ee607890c0a28fbfdde77"

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
        if left = 3 then row6 3 4 4 1 0 1 right else
          if left = 4 then row6 4 3 3 0 1 0 right else
            row6 3 4 4 1 0 2 right

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
  "37f2a1a942e99278749c2b90b97bfa1ce5ac65b1966ca60c615f76e0f5ba5086"

def stateVector (state : Fin 21)
    (coordinate : Fin 2) : Fin 6 :=
  match state.val with
  | 0 =>
      match coordinate.val with
      | 0 => (5 : Fin 6)
      | _ => (5 : Fin 6)
  | 1 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | _ => (5 : Fin 6)
  | 2 =>
      match coordinate.val with
      | 0 => (2 : Fin 6)
      | _ => (2 : Fin 6)
  | 3 =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | _ => (2 : Fin 6)
  | 4 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | _ => (2 : Fin 6)
  | 5 =>
      match coordinate.val with
      | 0 => (4 : Fin 6)
      | _ => (4 : Fin 6)
  | 6 =>
      match coordinate.val with
      | 0 => (1 : Fin 6)
      | _ => (4 : Fin 6)
  | 7 =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | _ => (4 : Fin 6)
  | 8 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | _ => (4 : Fin 6)
  | 9 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | _ => (0 : Fin 6)
  | 10 =>
      match coordinate.val with
      | 0 => (4 : Fin 6)
      | _ => (0 : Fin 6)
  | 11 =>
      match coordinate.val with
      | 0 => (1 : Fin 6)
      | _ => (0 : Fin 6)
  | 12 =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | _ => (0 : Fin 6)
  | 13 =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | _ => (3 : Fin 6)
  | 14 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | _ => (3 : Fin 6)
  | 15 =>
      match coordinate.val with
      | 0 => (4 : Fin 6)
      | _ => (3 : Fin 6)
  | 16 =>
      match coordinate.val with
      | 0 => (1 : Fin 6)
      | _ => (3 : Fin 6)
  | 17 =>
      match coordinate.val with
      | 0 => (1 : Fin 6)
      | _ => (1 : Fin 6)
  | 18 =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | _ => (1 : Fin 6)
  | 19 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | _ => (1 : Fin 6)
  | _ =>
      match coordinate.val with
      | 0 => (4 : Fin 6)
      | _ => (1 : Fin 6)

def generatorVector (generator : Fin 2)
    (coordinate : Fin 2) : Fin 6 :=
  match generator.val with
  | 0 =>
      match coordinate.val with
      | 0 => (5 : Fin 6)
      | _ => (5 : Fin 6)
  | _ =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | _ => (5 : Fin 6)

def transition (state : Fin 21)
    (generator : Fin 2) : Fin 21 :=
  match state.val with
  | 0 =>
      match generator.val with
      | 0 => (2 : Fin 21)
      | _ => (3 : Fin 21)
  | 1 =>
      match generator.val with
      | 0 => (3 : Fin 21)
      | _ => (4 : Fin 21)
  | 2 =>
      match generator.val with
      | 0 => (5 : Fin 21)
      | _ => (6 : Fin 21)
  | 3 =>
      match generator.val with
      | 0 => (6 : Fin 21)
      | _ => (7 : Fin 21)
  | 4 =>
      match generator.val with
      | 0 => (7 : Fin 21)
      | _ => (8 : Fin 21)
  | 5 =>
      match generator.val with
      | 0 => (9 : Fin 21)
      | _ => (10 : Fin 21)
  | 6 =>
      match generator.val with
      | 0 => (10 : Fin 21)
      | _ => (11 : Fin 21)
  | 7 =>
      match generator.val with
      | 0 => (11 : Fin 21)
      | _ => (12 : Fin 21)
  | 8 =>
      match generator.val with
      | 0 => (12 : Fin 21)
      | _ => (9 : Fin 21)
  | 9 =>
      match generator.val with
      | 0 => (13 : Fin 21)
      | _ => (14 : Fin 21)
  | 10 =>
      match generator.val with
      | 0 => (14 : Fin 21)
      | _ => (15 : Fin 21)
  | 11 =>
      match generator.val with
      | 0 => (15 : Fin 21)
      | _ => (16 : Fin 21)
  | 12 =>
      match generator.val with
      | 0 => (16 : Fin 21)
      | _ => (13 : Fin 21)
  | 13 =>
      match generator.val with
      | 0 => (17 : Fin 21)
      | _ => (18 : Fin 21)
  | 14 =>
      match generator.val with
      | 0 => (18 : Fin 21)
      | _ => (19 : Fin 21)
  | 15 =>
      match generator.val with
      | 0 => (19 : Fin 21)
      | _ => (20 : Fin 21)
  | 16 =>
      match generator.val with
      | 0 => (20 : Fin 21)
      | _ => (17 : Fin 21)
  | 17 =>
      match generator.val with
      | 0 => (5 : Fin 21)
      | _ => (6 : Fin 21)
  | 18 =>
      match generator.val with
      | 0 => (6 : Fin 21)
      | _ => (7 : Fin 21)
  | 19 =>
      match generator.val with
      | 0 => (7 : Fin 21)
      | _ => (8 : Fin 21)
  | _ =>
      match generator.val with
      | 0 => (8 : Fin 21)
      | _ => (5 : Fin 21)

def representativeHead (state : Fin 21) : Fin 2 :=
  match state.val with
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
  | 13 => (0 : Fin 2)
  | 14 => (0 : Fin 2)
  | 15 => (0 : Fin 2)
  | 16 => (0 : Fin 2)
  | 17 => (0 : Fin 2)
  | 18 => (0 : Fin 2)
  | 19 => (0 : Fin 2)
  | _ => (0 : Fin 2)

def representativeTail (state : Fin 21) :
    List (Fin 2) :=
  match state.val with
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
  | 13 => [0, 0, 0, 0]
  | 14 => [0, 0, 0, 1]
  | 15 => [0, 0, 1, 1]
  | 16 => [0, 1, 1, 1]
  | 17 => [0, 0, 0, 0, 0]
  | 18 => [0, 0, 0, 0, 1]
  | 19 => [0, 0, 0, 1, 1]
  | _ => [0, 0, 1, 1, 1]

def sourceLabel (state : Fin 21) : Fin 6 :=
  match state.val with
  | 0 => (5 : Fin 6)
  | 1 => (3 : Fin 6)
  | 2 => (2 : Fin 6)
  | 3 => (3 : Fin 6)
  | 4 => (1 : Fin 6)
  | 5 => (0 : Fin 6)
  | 6 => (3 : Fin 6)
  | 7 => (1 : Fin 6)
  | 8 => (4 : Fin 6)
  | 9 => (0 : Fin 6)
  | 10 => (3 : Fin 6)
  | 11 => (1 : Fin 6)
  | 12 => (4 : Fin 6)
  | 13 => (0 : Fin 6)
  | 14 => (3 : Fin 6)
  | 15 => (1 : Fin 6)
  | 16 => (4 : Fin 6)
  | 17 => (0 : Fin 6)
  | 18 => (3 : Fin 6)
  | 19 => (1 : Fin 6)
  | _ => (4 : Fin 6)

def generatorSourceLabel (generator : Fin 2) : Fin 6 :=
  match generator.val with
  | 0 => (5 : Fin 6)
  | _ => (3 : Fin 6)

def sourcePreimage (value : Fin 6) : Fin 21 :=
  match value.val with
  | 0 => (5 : Fin 21)
  | 1 => (4 : Fin 21)
  | 2 => (2 : Fin 21)
  | 3 => (1 : Fin 21)
  | 4 => (8 : Fin 21)
  | _ => (0 : Fin 21)

private def stateVectorCode
    (vector : Fin 2 -> Fin 6) : Nat :=
  (vector (0 : Fin 2)).val + 6 * ((vector (1 : Fin 2)).val)

private def decodeStateCode (code : Nat) : Fin 21 :=
  if code < 15 then
    if code < 7 then
      if code < 3 then
        if code < 1 then
          if code = 0 then (9 : Fin 21) else (0 : Fin 21)
        else if code = 1 then (11 : Fin 21) else
          (0 : Fin 21)
      else if code = 3 then (12 : Fin 21) else
        if code < 6 then
          if code = 4 then (10 : Fin 21) else (0 : Fin 21)
        else if code = 6 then (19 : Fin 21) else
          (0 : Fin 21)
    else if code = 7 then (17 : Fin 21) else
      if code < 12 then
        if code < 10 then
          if code = 9 then (18 : Fin 21) else (0 : Fin 21)
        else if code = 10 then (20 : Fin 21) else
          (0 : Fin 21)
      else if code = 12 then (4 : Fin 21) else
        if code = 14 then (2 : Fin 21) else (0 : Fin 21)
  else if code = 15 then (3 : Fin 21) else
    if code < 25 then
      if code < 21 then
        if code < 19 then
          if code = 18 then (14 : Fin 21) else (0 : Fin 21)
        else if code = 19 then (16 : Fin 21) else
          (0 : Fin 21)
      else if code = 21 then (13 : Fin 21) else
        if code < 24 then
          if code = 22 then (15 : Fin 21) else (0 : Fin 21)
        else if code = 24 then (8 : Fin 21) else
          (0 : Fin 21)
    else if code = 25 then (6 : Fin 21) else
      if code < 30 then
        if code < 28 then
          if code = 27 then (7 : Fin 21) else (0 : Fin 21)
        else if code = 28 then (5 : Fin 21) else
          (0 : Fin 21)
      else if code = 30 then (1 : Fin 21) else
        if code = 35 then (0 : Fin 21) else (0 : Fin 21)

private def decodeState
    (vector : Fin 2 -> Fin 6) : Fin 21 :=
  decodeStateCode (stateVectorCode vector)

set_option maxHeartbeats 2000000 in
private theorem decodeState_stateVector (state : Fin 21) :
    decodeState (stateVector state) = state := by
  decide +revert

set_option maxHeartbeats 2000000 in
private theorem transitionMap :
    forall (state : Fin 21)
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
    forall (state : Fin 21)
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
    (U := Fin 21)
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
    forall (state : Fin 21)
      (generator : Fin 2),
      sourceLabel (transition state generator) =
        SemigroupBasis.Generated.Order6GenericCASRootData.S6_5113.oppositeTable.semigroup.mul (sourceLabel state)
          (generatorSourceLabel generator) := by
  intro state generator
  apply Fin.ext
  exact by decide +revert

set_option maxHeartbeats 2000000 in
private theorem sourceLabelRepresentative :
    forall state : Fin 21,
      sourceLabel state =
        (representativeTail state).foldl
          (fun value generator =>
            SemigroupBasis.Generated.Order6GenericCASRootData.S6_5113.oppositeTable.semigroup.mul value
              (generatorSourceLabel generator))
          (generatorSourceLabel (representativeHead state)) := by
  intro state
  apply Fin.ext
  exact by decide +revert

private theorem sourceLabelRightMultiplyWord
    (state : Fin 21)
    (word : List (Fin 2)) :
    sourceLabel (powerCertificate.rightMultiplyWord state word) =
      word.foldl
        (fun value generator =>
          SemigroupBasis.Generated.Order6GenericCASRootData.S6_5113.oppositeTable.semigroup.mul value
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
              SemigroupBasis.Generated.Order6GenericCASRootData.S6_5113.oppositeTable.semigroup.mul value
                (generatorSourceLabel nextGenerator))
            (SemigroupBasis.Generated.Order6GenericCASRootData.S6_5113.oppositeTable.semigroup.mul (sourceLabel state)
              (generatorSourceLabel generator))
      rw [inductionHypothesis]
      rw [sourceLabelTransition]

private theorem sourceFoldlGeneratorAssoc
    (left right : Fin 6)
    (word : List (Fin 2)) :
    word.foldl
        (fun value generator =>
          SemigroupBasis.Generated.Order6GenericCASRootData.S6_5113.oppositeTable.semigroup.mul value
            (generatorSourceLabel generator))
        (SemigroupBasis.Generated.Order6GenericCASRootData.S6_5113.oppositeTable.semigroup.mul left right) =
      SemigroupBasis.Generated.Order6GenericCASRootData.S6_5113.oppositeTable.semigroup.mul left
        (word.foldl
          (fun value generator =>
            SemigroupBasis.Generated.Order6GenericCASRootData.S6_5113.oppositeTable.semigroup.mul value
              (generatorSourceLabel generator))
          right) := by
  induction word generalizing right with
  | nil => rfl
  | cons generator word inductionHypothesis =>
      simp only [List.foldl_cons]
      rw [SemigroupBasis.Generated.Order6GenericCASRootData.S6_5113.oppositeTable.semigroup.assoc]
      exact inductionHypothesis
        (SemigroupBasis.Generated.Order6GenericCASRootData.S6_5113.oppositeTable.semigroup.mul right (generatorSourceLabel generator))

private theorem sourceLabelMapMul :
    forall (left right : Fin 21),
      sourceLabel (powerCertificate.semigroup.mul left right) =
        SemigroupBasis.Generated.Order6GenericCASRootData.S6_5113.oppositeTable.semigroup.mul (sourceLabel left) (sourceLabel right) := by
  intro left right
  calc
    sourceLabel (powerCertificate.semigroup.mul left right) =
        sourceLabel
          (powerCertificate.rightMultiplyWord
            (transition left (representativeHead right))
            (representativeTail right)) := rfl
    _ = (representativeTail right).foldl
          (fun value generator =>
            SemigroupBasis.Generated.Order6GenericCASRootData.S6_5113.oppositeTable.semigroup.mul value
              (generatorSourceLabel generator))
          (sourceLabel (transition left (representativeHead right))) :=
      sourceLabelRightMultiplyWord _ _
    _ = (representativeTail right).foldl
          (fun value generator =>
            SemigroupBasis.Generated.Order6GenericCASRootData.S6_5113.oppositeTable.semigroup.mul value
              (generatorSourceLabel generator))
          (SemigroupBasis.Generated.Order6GenericCASRootData.S6_5113.oppositeTable.semigroup.mul (sourceLabel left)
            (generatorSourceLabel (representativeHead right))) :=
      congrArg
        (fun initial =>
          (representativeTail right).foldl
            (fun value generator =>
              SemigroupBasis.Generated.Order6GenericCASRootData.S6_5113.oppositeTable.semigroup.mul value
                (generatorSourceLabel generator))
            initial)
        (sourceLabelTransition left (representativeHead right))
    _ = SemigroupBasis.Generated.Order6GenericCASRootData.S6_5113.oppositeTable.semigroup.mul (sourceLabel left)
          ((representativeTail right).foldl
            (fun value generator =>
              SemigroupBasis.Generated.Order6GenericCASRootData.S6_5113.oppositeTable.semigroup.mul value
                (generatorSourceLabel generator))
            (generatorSourceLabel (representativeHead right))) :=
      sourceFoldlGeneratorAssoc _ _ _
    _ = SemigroupBasis.Generated.Order6GenericCASRootData.S6_5113.oppositeTable.semigroup.mul (sourceLabel left) (sourceLabel right) :=
      congrArg (SemigroupBasis.Generated.Order6GenericCASRootData.S6_5113.oppositeTable.semigroup.mul (sourceLabel left))
        (sourceLabelRepresentative right).symm

set_option maxHeartbeats 1000000 in
private theorem sourceLabelRightInverse :
    forall value : Fin 6, sourceLabel (sourcePreimage value) = value := by
  intro value
  apply Fin.ext
  exact by decide +revert

/-- The generated term-function semigroup maps onto the selected root. -/
def quotient : SplitSurjection powerCertificate.semigroup
    SemigroupBasis.Generated.Order6GenericCASRootData.S6_5113.oppositeTable.semigroup where
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
    SemigroupBasis.Generated.Order6GenericCASRootData.S6_5113.law0.SatisfiedBy oppositeTable.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    oppositeTable SemigroupBasis.Generated.Order6GenericCASRootData.S6_5113.law0
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
    SemigroupBasis.Generated.Order6GenericCASRootData.S6_5113.law1.SatisfiedBy oppositeTable.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    oppositeTable SemigroupBasis.Generated.Order6GenericCASRootData.S6_5113.law1
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
    SemigroupBasis.Generated.Order6GenericCASRootData.S6_5113.law2.SatisfiedBy oppositeTable.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    oppositeTable SemigroupBasis.Generated.Order6GenericCASRootData.S6_5113.law2
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
    SemigroupBasis.Generated.Order6GenericCASRootData.S6_5113.law3.SatisfiedBy oppositeTable.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    oppositeTable SemigroupBasis.Generated.Order6GenericCASRootData.S6_5113.law3
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
    SemigroupBasis.Generated.Order6GenericCASRootData.S6_5113.law4.SatisfiedBy oppositeTable.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    oppositeTable SemigroupBasis.Generated.Order6GenericCASRootData.S6_5113.law4
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
    SemigroupBasis.Generated.Order6GenericCASRootData.S6_5113.law5.SatisfiedBy oppositeTable.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    oppositeTable SemigroupBasis.Generated.Order6GenericCASRootData.S6_5113.law5
    targetLaw5ToFinite targetLaw5FromFinite (by decide) (by decide)

private def targetLaw6ToFinite : Nat -> Fin 3
  | 0 => (0 : Fin 3)
  | 1 => (1 : Fin 3)
  | 2 => (2 : Fin 3)
  | _ => (0 : Fin 3)

private def targetLaw6FromFinite (index : Fin 3) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
private theorem targetLaw6Valid :
    SemigroupBasis.Generated.Order6GenericCASRootData.S6_5113.law6.SatisfiedBy oppositeTable.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    oppositeTable SemigroupBasis.Generated.Order6GenericCASRootData.S6_5113.law6
    targetLaw6ToFinite targetLaw6FromFinite (by decide) (by decide)

private def targetLaw7ToFinite : Nat -> Fin 2
  | 0 => (0 : Fin 2)
  | 1 => (1 : Fin 2)
  | _ => (0 : Fin 2)

private def targetLaw7FromFinite (index : Fin 2) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
private theorem targetLaw7Valid :
    SemigroupBasis.Generated.Order6GenericCASRootData.S6_5113.law7.SatisfiedBy oppositeTable.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    oppositeTable SemigroupBasis.Generated.Order6GenericCASRootData.S6_5113.law7
    targetLaw7ToFinite targetLaw7FromFinite (by decide) (by decide)

/-- Exact finite checks that the selected target models the root basis. -/
theorem targetModels :
    Models oppositeTable.semigroup SemigroupBasis.Generated.Order6GenericCASRootData.S6_5113.basis := by
  unfold SemigroupBasis.Generated.Order6GenericCASRootData.S6_5113.basis
  exact
    FiniteNilpotentCounterexample.models_cons targetLaw0Valid <|
      FiniteNilpotentCounterexample.models_cons targetLaw1Valid <|
        FiniteNilpotentCounterexample.models_cons targetLaw2Valid <|
          FiniteNilpotentCounterexample.models_cons targetLaw3Valid <|
            FiniteNilpotentCounterexample.models_cons targetLaw4Valid <|
              FiniteNilpotentCounterexample.models_cons targetLaw5Valid <|
                FiniteNilpotentCounterexample.models_cons targetLaw6Valid <|
                  FiniteNilpotentCounterexample.models_cons targetLaw7Valid <|
                    FiniteNilpotentCounterexample.models_nil oppositeTable.semigroup

/-- Exact identity-theory transfer authenticated by the finite certificate. -/
theorem sameIdentityTheory :
    SameIdentityTheoryOver SemigroupBasis.Generated.Order6GenericCASRootData.S6_5113.oppositeTable.semigroup
      oppositeTable.semigroup Nat := by
  intro identity
  constructor
  · intro sourceValid valuation
    exact Derives.sound targetModels
      (SemigroupBasis.CoRoots.Order6GenericCASSubdirectS6_5113.basisFor.2 identity sourceValid) valuation
  · intro targetValid
    have powerValid :=
      identity.satisfiedByPi oppositeTable.semigroup
        (Fin 2) targetValid
    have subValid :=
      powerCertificate.embedding.pullback_identity identity powerValid
    exact quotient.pushforwardIdentity identity subValid

/-- First-layer generic-CAS basis wrapper for `S6_5115`. -/
theorem opposite_basis :
    BasisFor table.semigroup.opposite SemigroupBasis.Generated.Order6GenericCASRootData.S6_5113.basis := by
  have transferred :
      BasisFor oppositeTable.semigroup SemigroupBasis.Generated.Order6GenericCASRootData.S6_5113.basis :=
    (basisFor_iff_of_sameIdentityTheoryOver sameIdentityTheory).mp
      SemigroupBasis.CoRoots.Order6GenericCASSubdirectS6_5113.basisFor
  simpa only [oppositeTable_semigroup] using transferred

end SemigroupBasis.Generated.Order6GenericCASRootWrappers.S6_5115
