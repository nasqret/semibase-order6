import SemigroupBasis.CoRoots.Order6GenericCASSubdirectS6_5765
import SemigroupBasis.Nonfinite
import SemigroupBasis.Opposite
import SemigroupBasis.RightGeneratedPowerCertificate

set_option maxRecDepth 2048

namespace SemigroupBasis.Generated.Order6GenericCASRootWrappers.S6_14998

open SemigroupBasis

def routeManifestRowSHA256 : String := "22f34ecf67cc14931254d22228ac8a420673c6345f966540fcf64edf48495b6a"
def witnessRecordSHA256 : String := "6aaa23176efcdb8a289e27fa26dd08a7f45bd9c38bb181201f6f7dc214aca31d"
def transferComponentSHA256 : String := "7db558717e2624be9c50ddfb79b6beec96f85c49af78e5ff3c1a1fef46687790"
def powerCertificateSHA256 : String := "fb0288e0ffe55ef06018f4a158cf8a406fc01c43bb6b0b805849bb4ae7730e45"

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
    if left = 1 then row6 0 0 2 3 3 2 right else
      if left = 2 then row6 2 2 3 0 0 3 right else
        if left = 3 then row6 3 3 0 2 2 0 right else
          if left = 4 then row6 3 3 0 2 2 1 right else
            row6 2 2 3 0 1 4 right

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
  "b4ee1a5177f5bb0a7e4d5fdd5a153014b464fc2b656bace43e131181d154260c"

def stateVector (state : Fin 18)
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
      | 0 => (4 : Fin 6)
      | _ => (4 : Fin 6)
  | 3 =>
      match coordinate.val with
      | 0 => (2 : Fin 6)
      | _ => (4 : Fin 6)
  | 4 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | _ => (4 : Fin 6)
  | 5 =>
      match coordinate.val with
      | 0 => (1 : Fin 6)
      | _ => (1 : Fin 6)
  | 6 =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | _ => (1 : Fin 6)
  | 7 =>
      match coordinate.val with
      | 0 => (2 : Fin 6)
      | _ => (1 : Fin 6)
  | 8 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | _ => (1 : Fin 6)
  | 9 =>
      match coordinate.val with
      | 0 => (2 : Fin 6)
      | _ => (2 : Fin 6)
  | 10 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | _ => (2 : Fin 6)
  | 11 =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | _ => (2 : Fin 6)
  | 12 =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | _ => (3 : Fin 6)
  | 13 =>
      match coordinate.val with
      | 0 => (2 : Fin 6)
      | _ => (3 : Fin 6)
  | 14 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | _ => (3 : Fin 6)
  | 15 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | _ => (0 : Fin 6)
  | 16 =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | _ => (0 : Fin 6)
  | _ =>
      match coordinate.val with
      | 0 => (2 : Fin 6)
      | _ => (0 : Fin 6)

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

def transition (state : Fin 18)
    (generator : Fin 2) : Fin 18 :=
  match state.val with
  | 0 =>
      match generator.val with
      | 0 => (2 : Fin 18)
      | _ => (3 : Fin 18)
  | 1 =>
      match generator.val with
      | 0 => (3 : Fin 18)
      | _ => (4 : Fin 18)
  | 2 =>
      match generator.val with
      | 0 => (5 : Fin 18)
      | _ => (6 : Fin 18)
  | 3 =>
      match generator.val with
      | 0 => (6 : Fin 18)
      | _ => (7 : Fin 18)
  | 4 =>
      match generator.val with
      | 0 => (7 : Fin 18)
      | _ => (8 : Fin 18)
  | 5 =>
      match generator.val with
      | 0 => (9 : Fin 18)
      | _ => (10 : Fin 18)
  | 6 =>
      match generator.val with
      | 0 => (10 : Fin 18)
      | _ => (11 : Fin 18)
  | 7 =>
      match generator.val with
      | 0 => (11 : Fin 18)
      | _ => (9 : Fin 18)
  | 8 =>
      match generator.val with
      | 0 => (9 : Fin 18)
      | _ => (10 : Fin 18)
  | 9 =>
      match generator.val with
      | 0 => (12 : Fin 18)
      | _ => (13 : Fin 18)
  | 10 =>
      match generator.val with
      | 0 => (13 : Fin 18)
      | _ => (14 : Fin 18)
  | 11 =>
      match generator.val with
      | 0 => (14 : Fin 18)
      | _ => (12 : Fin 18)
  | 12 =>
      match generator.val with
      | 0 => (15 : Fin 18)
      | _ => (16 : Fin 18)
  | 13 =>
      match generator.val with
      | 0 => (16 : Fin 18)
      | _ => (17 : Fin 18)
  | 14 =>
      match generator.val with
      | 0 => (17 : Fin 18)
      | _ => (15 : Fin 18)
  | 15 =>
      match generator.val with
      | 0 => (9 : Fin 18)
      | _ => (10 : Fin 18)
  | 16 =>
      match generator.val with
      | 0 => (10 : Fin 18)
      | _ => (11 : Fin 18)
  | _ =>
      match generator.val with
      | 0 => (11 : Fin 18)
      | _ => (9 : Fin 18)

def representativeHead (state : Fin 18) : Fin 2 :=
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
  | _ => (0 : Fin 2)

def representativeTail (state : Fin 18) :
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
  | 12 => [0, 0, 0, 0]
  | 13 => [0, 0, 0, 1]
  | 14 => [0, 0, 1, 1]
  | 15 => [0, 0, 0, 0, 0]
  | 16 => [0, 0, 0, 0, 1]
  | _ => [0, 0, 0, 1, 1]

def sourceLabel (state : Fin 18) : Fin 6 :=
  match state.val with
  | 0 => (4 : Fin 6)
  | 1 => (3 : Fin 6)
  | 2 => (5 : Fin 6)
  | 3 => (4 : Fin 6)
  | 4 => (1 : Fin 6)
  | 5 => (0 : Fin 6)
  | 6 => (5 : Fin 6)
  | 7 => (4 : Fin 6)
  | 8 => (2 : Fin 6)
  | 9 => (4 : Fin 6)
  | 10 => (0 : Fin 6)
  | 11 => (5 : Fin 6)
  | 12 => (5 : Fin 6)
  | 13 => (4 : Fin 6)
  | 14 => (0 : Fin 6)
  | 15 => (0 : Fin 6)
  | 16 => (5 : Fin 6)
  | _ => (4 : Fin 6)

def generatorSourceLabel (generator : Fin 2) : Fin 6 :=
  match generator.val with
  | 0 => (4 : Fin 6)
  | _ => (3 : Fin 6)

def sourcePreimage (value : Fin 6) : Fin 18 :=
  match value.val with
  | 0 => (5 : Fin 18)
  | 1 => (4 : Fin 18)
  | 2 => (8 : Fin 18)
  | 3 => (1 : Fin 18)
  | 4 => (0 : Fin 18)
  | _ => (2 : Fin 18)

private def stateVectorCode
    (vector : Fin 2 -> Fin 6) : Nat :=
  (vector (0 : Fin 2)).val + 6 * ((vector (1 : Fin 2)).val)

private def decodeStateCode (code : Nat) : Fin 18 :=
  if code < 15 then
    if code < 7 then
      if code < 3 then
        if code < 2 then
          if code = 0 then (15 : Fin 18) else (0 : Fin 18)
        else if code = 2 then (17 : Fin 18) else
          (0 : Fin 18)
      else if code = 3 then (16 : Fin 18) else
        if code = 6 then (8 : Fin 18) else (0 : Fin 18)
    else if code = 7 then (5 : Fin 18) else
      if code < 12 then
        if code < 9 then
          if code = 8 then (7 : Fin 18) else (0 : Fin 18)
        else if code = 9 then (6 : Fin 18) else
          (0 : Fin 18)
      else if code = 12 then (10 : Fin 18) else
        if code = 14 then (9 : Fin 18) else (0 : Fin 18)
  else if code = 15 then (11 : Fin 18) else
    if code < 26 then
      if code < 21 then
        if code < 20 then
          if code = 18 then (14 : Fin 18) else (0 : Fin 18)
        else if code = 20 then (13 : Fin 18) else
          (0 : Fin 18)
      else if code = 21 then (12 : Fin 18) else
        if code = 24 then (4 : Fin 18) else (0 : Fin 18)
    else if code = 26 then (3 : Fin 18) else
      if code < 30 then
        if code = 28 then (2 : Fin 18) else (0 : Fin 18)
      else if code = 30 then (1 : Fin 18) else
        if code = 35 then (0 : Fin 18) else (0 : Fin 18)

private def decodeState
    (vector : Fin 2 -> Fin 6) : Fin 18 :=
  decodeStateCode (stateVectorCode vector)

set_option maxHeartbeats 2000000 in
private theorem decodeState_stateVector (state : Fin 18) :
    decodeState (stateVector state) = state := by
  decide +revert

set_option maxHeartbeats 2000000 in
private theorem transitionMap :
    forall (state : Fin 18)
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
    forall (state : Fin 18)
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
    (U := Fin 18)
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
    forall (state : Fin 18)
      (generator : Fin 2),
      sourceLabel (transition state generator) =
        SemigroupBasis.Generated.Order6GenericCASRootData.S6_5765.oppositeTable.semigroup.mul (sourceLabel state)
          (generatorSourceLabel generator) := by
  intro state generator
  apply Fin.ext
  exact by decide +revert

set_option maxHeartbeats 2000000 in
private theorem sourceLabelRepresentative :
    forall state : Fin 18,
      sourceLabel state =
        (representativeTail state).foldl
          (fun value generator =>
            SemigroupBasis.Generated.Order6GenericCASRootData.S6_5765.oppositeTable.semigroup.mul value
              (generatorSourceLabel generator))
          (generatorSourceLabel (representativeHead state)) := by
  intro state
  apply Fin.ext
  exact by decide +revert

private theorem sourceLabelRightMultiplyWord
    (state : Fin 18)
    (word : List (Fin 2)) :
    sourceLabel (powerCertificate.rightMultiplyWord state word) =
      word.foldl
        (fun value generator =>
          SemigroupBasis.Generated.Order6GenericCASRootData.S6_5765.oppositeTable.semigroup.mul value
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
              SemigroupBasis.Generated.Order6GenericCASRootData.S6_5765.oppositeTable.semigroup.mul value
                (generatorSourceLabel nextGenerator))
            (SemigroupBasis.Generated.Order6GenericCASRootData.S6_5765.oppositeTable.semigroup.mul (sourceLabel state)
              (generatorSourceLabel generator))
      rw [inductionHypothesis]
      rw [sourceLabelTransition]

private theorem sourceFoldlGeneratorAssoc
    (left right : Fin 6)
    (word : List (Fin 2)) :
    word.foldl
        (fun value generator =>
          SemigroupBasis.Generated.Order6GenericCASRootData.S6_5765.oppositeTable.semigroup.mul value
            (generatorSourceLabel generator))
        (SemigroupBasis.Generated.Order6GenericCASRootData.S6_5765.oppositeTable.semigroup.mul left right) =
      SemigroupBasis.Generated.Order6GenericCASRootData.S6_5765.oppositeTable.semigroup.mul left
        (word.foldl
          (fun value generator =>
            SemigroupBasis.Generated.Order6GenericCASRootData.S6_5765.oppositeTable.semigroup.mul value
              (generatorSourceLabel generator))
          right) := by
  induction word generalizing right with
  | nil => rfl
  | cons generator word inductionHypothesis =>
      simp only [List.foldl_cons]
      rw [SemigroupBasis.Generated.Order6GenericCASRootData.S6_5765.oppositeTable.semigroup.assoc]
      exact inductionHypothesis
        (SemigroupBasis.Generated.Order6GenericCASRootData.S6_5765.oppositeTable.semigroup.mul right (generatorSourceLabel generator))

private theorem sourceLabelMapMul :
    forall (left right : Fin 18),
      sourceLabel (powerCertificate.semigroup.mul left right) =
        SemigroupBasis.Generated.Order6GenericCASRootData.S6_5765.oppositeTable.semigroup.mul (sourceLabel left) (sourceLabel right) := by
  intro left right
  calc
    sourceLabel (powerCertificate.semigroup.mul left right) =
        sourceLabel
          (powerCertificate.rightMultiplyWord
            (transition left (representativeHead right))
            (representativeTail right)) := rfl
    _ = (representativeTail right).foldl
          (fun value generator =>
            SemigroupBasis.Generated.Order6GenericCASRootData.S6_5765.oppositeTable.semigroup.mul value
              (generatorSourceLabel generator))
          (sourceLabel (transition left (representativeHead right))) :=
      sourceLabelRightMultiplyWord _ _
    _ = (representativeTail right).foldl
          (fun value generator =>
            SemigroupBasis.Generated.Order6GenericCASRootData.S6_5765.oppositeTable.semigroup.mul value
              (generatorSourceLabel generator))
          (SemigroupBasis.Generated.Order6GenericCASRootData.S6_5765.oppositeTable.semigroup.mul (sourceLabel left)
            (generatorSourceLabel (representativeHead right))) :=
      congrArg
        (fun initial =>
          (representativeTail right).foldl
            (fun value generator =>
              SemigroupBasis.Generated.Order6GenericCASRootData.S6_5765.oppositeTable.semigroup.mul value
                (generatorSourceLabel generator))
            initial)
        (sourceLabelTransition left (representativeHead right))
    _ = SemigroupBasis.Generated.Order6GenericCASRootData.S6_5765.oppositeTable.semigroup.mul (sourceLabel left)
          ((representativeTail right).foldl
            (fun value generator =>
              SemigroupBasis.Generated.Order6GenericCASRootData.S6_5765.oppositeTable.semigroup.mul value
                (generatorSourceLabel generator))
            (generatorSourceLabel (representativeHead right))) :=
      sourceFoldlGeneratorAssoc _ _ _
    _ = SemigroupBasis.Generated.Order6GenericCASRootData.S6_5765.oppositeTable.semigroup.mul (sourceLabel left) (sourceLabel right) :=
      congrArg (SemigroupBasis.Generated.Order6GenericCASRootData.S6_5765.oppositeTable.semigroup.mul (sourceLabel left))
        (sourceLabelRepresentative right).symm

set_option maxHeartbeats 1000000 in
private theorem sourceLabelRightInverse :
    forall value : Fin 6, sourceLabel (sourcePreimage value) = value := by
  intro value
  apply Fin.ext
  exact by decide +revert

/-- The generated term-function semigroup maps onto the selected root. -/
def quotient : SplitSurjection powerCertificate.semigroup
    SemigroupBasis.Generated.Order6GenericCASRootData.S6_5765.oppositeTable.semigroup where
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
    SemigroupBasis.Generated.Order6GenericCASRootData.S6_5765.law0.SatisfiedBy oppositeTable.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    oppositeTable SemigroupBasis.Generated.Order6GenericCASRootData.S6_5765.law0
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
    SemigroupBasis.Generated.Order6GenericCASRootData.S6_5765.law1.SatisfiedBy oppositeTable.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    oppositeTable SemigroupBasis.Generated.Order6GenericCASRootData.S6_5765.law1
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
    SemigroupBasis.Generated.Order6GenericCASRootData.S6_5765.law2.SatisfiedBy oppositeTable.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    oppositeTable SemigroupBasis.Generated.Order6GenericCASRootData.S6_5765.law2
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
    SemigroupBasis.Generated.Order6GenericCASRootData.S6_5765.law3.SatisfiedBy oppositeTable.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    oppositeTable SemigroupBasis.Generated.Order6GenericCASRootData.S6_5765.law3
    targetLaw3ToFinite targetLaw3FromFinite (by decide) (by decide)

private def targetLaw4ToFinite : Nat -> Fin 4
  | 0 => (0 : Fin 4)
  | 1 => (1 : Fin 4)
  | 2 => (2 : Fin 4)
  | 3 => (3 : Fin 4)
  | _ => (0 : Fin 4)

private def targetLaw4FromFinite (index : Fin 4) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
private theorem targetLaw4Valid :
    SemigroupBasis.Generated.Order6GenericCASRootData.S6_5765.law4.SatisfiedBy oppositeTable.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    oppositeTable SemigroupBasis.Generated.Order6GenericCASRootData.S6_5765.law4
    targetLaw4ToFinite targetLaw4FromFinite (by decide) (by decide)

/-- Exact finite checks that the selected target models the root basis. -/
theorem targetModels :
    Models oppositeTable.semigroup SemigroupBasis.Generated.Order6GenericCASRootData.S6_5765.basis := by
  unfold SemigroupBasis.Generated.Order6GenericCASRootData.S6_5765.basis
  exact
    FiniteNilpotentCounterexample.models_cons targetLaw0Valid <|
      FiniteNilpotentCounterexample.models_cons targetLaw1Valid <|
        FiniteNilpotentCounterexample.models_cons targetLaw2Valid <|
          FiniteNilpotentCounterexample.models_cons targetLaw3Valid <|
            FiniteNilpotentCounterexample.models_cons targetLaw4Valid <|
              FiniteNilpotentCounterexample.models_nil oppositeTable.semigroup

/-- Exact identity-theory transfer authenticated by the finite certificate. -/
theorem sameIdentityTheory :
    SameIdentityTheoryOver SemigroupBasis.Generated.Order6GenericCASRootData.S6_5765.oppositeTable.semigroup
      oppositeTable.semigroup Nat := by
  intro identity
  constructor
  · intro sourceValid valuation
    exact Derives.sound targetModels
      (SemigroupBasis.CoRoots.Order6GenericCASSubdirectS6_5765.basisFor.2 identity sourceValid) valuation
  · intro targetValid
    have powerValid :=
      identity.satisfiedByPi oppositeTable.semigroup
        (Fin 2) targetValid
    have subValid :=
      powerCertificate.embedding.pullback_identity identity powerValid
    exact quotient.pushforwardIdentity identity subValid

/-- First-layer generic-CAS basis wrapper for `S6_14998`. -/
theorem opposite_basis :
    BasisFor table.semigroup.opposite SemigroupBasis.Generated.Order6GenericCASRootData.S6_5765.basis := by
  have transferred :
      BasisFor oppositeTable.semigroup SemigroupBasis.Generated.Order6GenericCASRootData.S6_5765.basis :=
    (basisFor_iff_of_sameIdentityTheoryOver sameIdentityTheory).mp
      SemigroupBasis.CoRoots.Order6GenericCASSubdirectS6_5765.basisFor
  simpa only [oppositeTable_semigroup] using transferred

end SemigroupBasis.Generated.Order6GenericCASRootWrappers.S6_14998
