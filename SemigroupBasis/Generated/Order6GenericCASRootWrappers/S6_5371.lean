import SemigroupBasis.CoRoots.Order6GenericCASSubdirectS6_5368
import SemigroupBasis.Nonfinite
import SemigroupBasis.Opposite
import SemigroupBasis.RightGeneratedPowerCertificate

set_option maxRecDepth 2048

namespace SemigroupBasis.Generated.Order6GenericCASRootWrappers.S6_5371

open SemigroupBasis

def routeManifestRowSHA256 : String := "a29fcef17207c94ce2a7a28793f1f77a279dc6fdb779300289a8248af7080acc"
def witnessRecordSHA256 : String := "609c9d7f3c03cd036e5e2cc903187d25450fdd9c9b42bd24983924ab53aafe25"
def transferComponentSHA256 : String := "618d4c69f92454ed4c37ac5e302cc69fb760bef83210060c29bd869a052f7812"
def powerCertificateSHA256 : String := "0f08abbd3b208c1f172c66ce3d24f55805484340ae2fd821ede8d5010ea95bda"

private def row6
    (c0 c1 c2 c3 c4 c5 : Fin 6) (column : Fin 6) : Fin 6 :=
  if column = 0 then c0 else
    if column = 1 then c1 else
      if column = 2 then c2 else
        if column = 3 then c3 else
          if column = 4 then c4 else c5

/-- Exact one-based catalogue table committed by the portable witness. -/
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 0 0 0 5 right else
    if left = 1 then row6 0 0 0 0 0 5 right else
      if left = 2 then row6 0 0 0 0 1 5 right else
        if left = 3 then row6 0 0 0 1 2 5 right else
          if left = 4 then row6 0 0 1 2 3 5 right else
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
  "b277b84b1418ea84f9a9c43fa57b5571626b9033baf5da6571cbfdc2eed1019e"

def stateVector (state : Fin 15)
    (coordinate : Fin 4) : Fin 6 :=
  match state.val with
  | 0 =>
      match coordinate.val with
      | 0 => (5 : Fin 6)
      | 1 => (4 : Fin 6)
      | 2 => (4 : Fin 6)
      | _ => (4 : Fin 6)
  | 1 =>
      match coordinate.val with
      | 0 => (4 : Fin 6)
      | 1 => (5 : Fin 6)
      | 2 => (4 : Fin 6)
      | _ => (3 : Fin 6)
  | 2 =>
      match coordinate.val with
      | 0 => (5 : Fin 6)
      | 1 => (3 : Fin 6)
      | 2 => (3 : Fin 6)
      | _ => (3 : Fin 6)
  | 3 =>
      match coordinate.val with
      | 0 => (5 : Fin 6)
      | 1 => (5 : Fin 6)
      | 2 => (3 : Fin 6)
      | _ => (2 : Fin 6)
  | 4 =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | 1 => (5 : Fin 6)
      | 2 => (3 : Fin 6)
      | _ => (1 : Fin 6)
  | 5 =>
      match coordinate.val with
      | 0 => (5 : Fin 6)
      | 1 => (2 : Fin 6)
      | 2 => (2 : Fin 6)
      | _ => (2 : Fin 6)
  | 6 =>
      match coordinate.val with
      | 0 => (5 : Fin 6)
      | 1 => (5 : Fin 6)
      | 2 => (2 : Fin 6)
      | _ => (1 : Fin 6)
  | 7 =>
      match coordinate.val with
      | 0 => (5 : Fin 6)
      | 1 => (5 : Fin 6)
      | 2 => (2 : Fin 6)
      | _ => (0 : Fin 6)
  | 8 =>
      match coordinate.val with
      | 0 => (2 : Fin 6)
      | 1 => (5 : Fin 6)
      | 2 => (2 : Fin 6)
      | _ => (0 : Fin 6)
  | 9 =>
      match coordinate.val with
      | 0 => (5 : Fin 6)
      | 1 => (1 : Fin 6)
      | 2 => (1 : Fin 6)
      | _ => (1 : Fin 6)
  | 10 =>
      match coordinate.val with
      | 0 => (5 : Fin 6)
      | 1 => (5 : Fin 6)
      | 2 => (1 : Fin 6)
      | _ => (0 : Fin 6)
  | 11 =>
      match coordinate.val with
      | 0 => (1 : Fin 6)
      | 1 => (5 : Fin 6)
      | 2 => (1 : Fin 6)
      | _ => (0 : Fin 6)
  | 12 =>
      match coordinate.val with
      | 0 => (5 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | _ => (0 : Fin 6)
  | 13 =>
      match coordinate.val with
      | 0 => (5 : Fin 6)
      | 1 => (5 : Fin 6)
      | 2 => (0 : Fin 6)
      | _ => (0 : Fin 6)
  | _ =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (5 : Fin 6)
      | 2 => (0 : Fin 6)
      | _ => (0 : Fin 6)

def generatorVector (generator : Fin 2)
    (coordinate : Fin 4) : Fin 6 :=
  match generator.val with
  | 0 =>
      match coordinate.val with
      | 0 => (5 : Fin 6)
      | 1 => (4 : Fin 6)
      | 2 => (4 : Fin 6)
      | _ => (4 : Fin 6)
  | _ =>
      match coordinate.val with
      | 0 => (4 : Fin 6)
      | 1 => (5 : Fin 6)
      | 2 => (4 : Fin 6)
      | _ => (3 : Fin 6)

def transition (state : Fin 15)
    (generator : Fin 2) : Fin 15 :=
  match state.val with
  | 0 =>
      match generator.val with
      | 0 => (2 : Fin 15)
      | _ => (3 : Fin 15)
  | 1 =>
      match generator.val with
      | 0 => (3 : Fin 15)
      | _ => (4 : Fin 15)
  | 2 =>
      match generator.val with
      | 0 => (5 : Fin 15)
      | _ => (6 : Fin 15)
  | 3 =>
      match generator.val with
      | 0 => (6 : Fin 15)
      | _ => (7 : Fin 15)
  | 4 =>
      match generator.val with
      | 0 => (7 : Fin 15)
      | _ => (8 : Fin 15)
  | 5 =>
      match generator.val with
      | 0 => (9 : Fin 15)
      | _ => (10 : Fin 15)
  | 6 =>
      match generator.val with
      | 0 => (10 : Fin 15)
      | _ => (10 : Fin 15)
  | 7 =>
      match generator.val with
      | 0 => (10 : Fin 15)
      | _ => (10 : Fin 15)
  | 8 =>
      match generator.val with
      | 0 => (10 : Fin 15)
      | _ => (11 : Fin 15)
  | 9 =>
      match generator.val with
      | 0 => (12 : Fin 15)
      | _ => (13 : Fin 15)
  | 10 =>
      match generator.val with
      | 0 => (13 : Fin 15)
      | _ => (13 : Fin 15)
  | 11 =>
      match generator.val with
      | 0 => (13 : Fin 15)
      | _ => (14 : Fin 15)
  | 12 =>
      match generator.val with
      | 0 => (12 : Fin 15)
      | _ => (13 : Fin 15)
  | 13 =>
      match generator.val with
      | 0 => (13 : Fin 15)
      | _ => (13 : Fin 15)
  | _ =>
      match generator.val with
      | 0 => (13 : Fin 15)
      | _ => (14 : Fin 15)

def representativeHead (state : Fin 15) : Fin 2 :=
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
  | 11 => (1 : Fin 2)
  | 12 => (0 : Fin 2)
  | 13 => (0 : Fin 2)
  | _ => (1 : Fin 2)

def representativeTail (state : Fin 15) :
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
  | 11 => [1, 1, 1]
  | 12 => [0, 0, 0, 0]
  | 13 => [0, 0, 0, 1]
  | _ => [1, 1, 1, 1]

def sourceLabel (state : Fin 15) : Fin 6 :=
  match state.val with
  | 0 => (5 : Fin 6)
  | 1 => (4 : Fin 6)
  | 2 => (5 : Fin 6)
  | 3 => (0 : Fin 6)
  | 4 => (3 : Fin 6)
  | 5 => (5 : Fin 6)
  | 6 => (0 : Fin 6)
  | 7 => (0 : Fin 6)
  | 8 => (2 : Fin 6)
  | 9 => (5 : Fin 6)
  | 10 => (0 : Fin 6)
  | 11 => (1 : Fin 6)
  | 12 => (5 : Fin 6)
  | 13 => (0 : Fin 6)
  | _ => (0 : Fin 6)

def generatorSourceLabel (generator : Fin 2) : Fin 6 :=
  match generator.val with
  | 0 => (5 : Fin 6)
  | _ => (4 : Fin 6)

def sourcePreimage (value : Fin 6) : Fin 15 :=
  match value.val with
  | 0 => (3 : Fin 15)
  | 1 => (11 : Fin 15)
  | 2 => (8 : Fin 15)
  | 3 => (4 : Fin 15)
  | 4 => (1 : Fin 15)
  | _ => (0 : Fin 15)

private def stateVectorCode
    (vector : Fin 4 -> Fin 6) : Nat :=
  (vector (0 : Fin 4)).val + 6 * ((vector (1 : Fin 4)).val + 6 * ((vector (2 : Fin 4)).val + 6 * ((vector (3 : Fin 4)).val)))

private def decodeStateCode (code : Nat) : Fin 15 :=
  if code < 263 then
    if code < 67 then
      if code < 30 then
        if code = 5 then (12 : Fin 15) else (0 : Fin 15)
      else if code = 30 then (14 : Fin 15) else
        if code = 35 then (13 : Fin 15) else (0 : Fin 15)
    else if code = 67 then (11 : Fin 15) else
      if code < 104 then
        if code = 71 then (10 : Fin 15) else (0 : Fin 15)
      else if code = 104 then (8 : Fin 15) else
        if code = 107 then (7 : Fin 15) else (0 : Fin 15)
  else if code = 263 then (9 : Fin 15) else
    if code < 575 then
      if code < 357 then
        if code = 323 then (6 : Fin 15) else (0 : Fin 15)
      else if code = 357 then (4 : Fin 15) else
        if code = 521 then (5 : Fin 15) else (0 : Fin 15)
    else if code = 575 then (3 : Fin 15) else
      if code < 826 then
        if code = 779 then (2 : Fin 15) else (0 : Fin 15)
      else if code = 826 then (1 : Fin 15) else
        if code = 1037 then (0 : Fin 15) else (0 : Fin 15)

private def decodeState
    (vector : Fin 4 -> Fin 6) : Fin 15 :=
  decodeStateCode (stateVectorCode vector)

set_option maxHeartbeats 2000000 in
private theorem decodeState_stateVector (state : Fin 15) :
    decodeState (stateVector state) = state := by
  decide +revert

set_option maxHeartbeats 2000000 in
private theorem transitionMap :
    forall (state : Fin 15)
      (generator : Fin 2)
      (coordinate : Fin 4),
      stateVector (transition state generator) coordinate =
        oppositeTable.semigroup.mul (stateVector state coordinate)
          (generatorVector generator coordinate) := by
  intro state generator coordinate
  apply Fin.ext
  exact by decide +revert

set_option maxHeartbeats 2000000 in
private theorem representativeMap :
    forall (state : Fin 15)
      (coordinate : Fin 4),
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
    (U := Fin 15)
    (G := Fin 2)
    (I := Fin 4) oppositeTable.semigroup where
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
    forall (state : Fin 15)
      (generator : Fin 2),
      sourceLabel (transition state generator) =
        SemigroupBasis.Generated.Order6GenericCASRootData.S6_5368.oppositeTable.semigroup.mul (sourceLabel state)
          (generatorSourceLabel generator) := by
  intro state generator
  apply Fin.ext
  exact by decide +revert

set_option maxHeartbeats 2000000 in
private theorem sourceLabelRepresentative :
    forall state : Fin 15,
      sourceLabel state =
        (representativeTail state).foldl
          (fun value generator =>
            SemigroupBasis.Generated.Order6GenericCASRootData.S6_5368.oppositeTable.semigroup.mul value
              (generatorSourceLabel generator))
          (generatorSourceLabel (representativeHead state)) := by
  intro state
  apply Fin.ext
  exact by decide +revert

private theorem sourceLabelRightMultiplyWord
    (state : Fin 15)
    (word : List (Fin 2)) :
    sourceLabel (powerCertificate.rightMultiplyWord state word) =
      word.foldl
        (fun value generator =>
          SemigroupBasis.Generated.Order6GenericCASRootData.S6_5368.oppositeTable.semigroup.mul value
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
              SemigroupBasis.Generated.Order6GenericCASRootData.S6_5368.oppositeTable.semigroup.mul value
                (generatorSourceLabel nextGenerator))
            (SemigroupBasis.Generated.Order6GenericCASRootData.S6_5368.oppositeTable.semigroup.mul (sourceLabel state)
              (generatorSourceLabel generator))
      rw [inductionHypothesis]
      rw [sourceLabelTransition]

private theorem sourceFoldlGeneratorAssoc
    (left right : Fin 6)
    (word : List (Fin 2)) :
    word.foldl
        (fun value generator =>
          SemigroupBasis.Generated.Order6GenericCASRootData.S6_5368.oppositeTable.semigroup.mul value
            (generatorSourceLabel generator))
        (SemigroupBasis.Generated.Order6GenericCASRootData.S6_5368.oppositeTable.semigroup.mul left right) =
      SemigroupBasis.Generated.Order6GenericCASRootData.S6_5368.oppositeTable.semigroup.mul left
        (word.foldl
          (fun value generator =>
            SemigroupBasis.Generated.Order6GenericCASRootData.S6_5368.oppositeTable.semigroup.mul value
              (generatorSourceLabel generator))
          right) := by
  induction word generalizing right with
  | nil => rfl
  | cons generator word inductionHypothesis =>
      simp only [List.foldl_cons]
      rw [SemigroupBasis.Generated.Order6GenericCASRootData.S6_5368.oppositeTable.semigroup.assoc]
      exact inductionHypothesis
        (SemigroupBasis.Generated.Order6GenericCASRootData.S6_5368.oppositeTable.semigroup.mul right (generatorSourceLabel generator))

private theorem sourceLabelMapMul :
    forall (left right : Fin 15),
      sourceLabel (powerCertificate.semigroup.mul left right) =
        SemigroupBasis.Generated.Order6GenericCASRootData.S6_5368.oppositeTable.semigroup.mul (sourceLabel left) (sourceLabel right) := by
  intro left right
  calc
    sourceLabel (powerCertificate.semigroup.mul left right) =
        sourceLabel
          (powerCertificate.rightMultiplyWord
            (transition left (representativeHead right))
            (representativeTail right)) := rfl
    _ = (representativeTail right).foldl
          (fun value generator =>
            SemigroupBasis.Generated.Order6GenericCASRootData.S6_5368.oppositeTable.semigroup.mul value
              (generatorSourceLabel generator))
          (sourceLabel (transition left (representativeHead right))) :=
      sourceLabelRightMultiplyWord _ _
    _ = (representativeTail right).foldl
          (fun value generator =>
            SemigroupBasis.Generated.Order6GenericCASRootData.S6_5368.oppositeTable.semigroup.mul value
              (generatorSourceLabel generator))
          (SemigroupBasis.Generated.Order6GenericCASRootData.S6_5368.oppositeTable.semigroup.mul (sourceLabel left)
            (generatorSourceLabel (representativeHead right))) :=
      congrArg
        (fun initial =>
          (representativeTail right).foldl
            (fun value generator =>
              SemigroupBasis.Generated.Order6GenericCASRootData.S6_5368.oppositeTable.semigroup.mul value
                (generatorSourceLabel generator))
            initial)
        (sourceLabelTransition left (representativeHead right))
    _ = SemigroupBasis.Generated.Order6GenericCASRootData.S6_5368.oppositeTable.semigroup.mul (sourceLabel left)
          ((representativeTail right).foldl
            (fun value generator =>
              SemigroupBasis.Generated.Order6GenericCASRootData.S6_5368.oppositeTable.semigroup.mul value
                (generatorSourceLabel generator))
            (generatorSourceLabel (representativeHead right))) :=
      sourceFoldlGeneratorAssoc _ _ _
    _ = SemigroupBasis.Generated.Order6GenericCASRootData.S6_5368.oppositeTable.semigroup.mul (sourceLabel left) (sourceLabel right) :=
      congrArg (SemigroupBasis.Generated.Order6GenericCASRootData.S6_5368.oppositeTable.semigroup.mul (sourceLabel left))
        (sourceLabelRepresentative right).symm

set_option maxHeartbeats 1000000 in
private theorem sourceLabelRightInverse :
    forall value : Fin 6, sourceLabel (sourcePreimage value) = value := by
  intro value
  apply Fin.ext
  exact by decide +revert

/-- The generated term-function semigroup maps onto the selected root. -/
def quotient : SplitSurjection powerCertificate.semigroup
    SemigroupBasis.Generated.Order6GenericCASRootData.S6_5368.oppositeTable.semigroup where
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
    SemigroupBasis.Generated.Order6GenericCASRootData.S6_5368.law0.SatisfiedBy oppositeTable.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    oppositeTable SemigroupBasis.Generated.Order6GenericCASRootData.S6_5368.law0
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
    SemigroupBasis.Generated.Order6GenericCASRootData.S6_5368.law1.SatisfiedBy oppositeTable.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    oppositeTable SemigroupBasis.Generated.Order6GenericCASRootData.S6_5368.law1
    targetLaw1ToFinite targetLaw1FromFinite (by decide) (by decide)

private def targetLaw2ToFinite : Nat -> Fin 3
  | 0 => (0 : Fin 3)
  | 1 => (1 : Fin 3)
  | 2 => (2 : Fin 3)
  | _ => (0 : Fin 3)

private def targetLaw2FromFinite (index : Fin 3) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
private theorem targetLaw2Valid :
    SemigroupBasis.Generated.Order6GenericCASRootData.S6_5368.law2.SatisfiedBy oppositeTable.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    oppositeTable SemigroupBasis.Generated.Order6GenericCASRootData.S6_5368.law2
    targetLaw2ToFinite targetLaw2FromFinite (by decide) (by decide)

private def targetLaw3ToFinite : Nat -> Fin 5
  | 0 => (0 : Fin 5)
  | 1 => (1 : Fin 5)
  | 2 => (2 : Fin 5)
  | 3 => (3 : Fin 5)
  | 4 => (4 : Fin 5)
  | _ => (0 : Fin 5)

private def targetLaw3FromFinite (index : Fin 5) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
private theorem targetLaw3Valid :
    SemigroupBasis.Generated.Order6GenericCASRootData.S6_5368.law3.SatisfiedBy oppositeTable.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    oppositeTable SemigroupBasis.Generated.Order6GenericCASRootData.S6_5368.law3
    targetLaw3ToFinite targetLaw3FromFinite (by decide) (by decide)

/-- Exact finite checks that the selected target models the root basis. -/
theorem targetModels :
    Models oppositeTable.semigroup SemigroupBasis.Generated.Order6GenericCASRootData.S6_5368.basis := by
  unfold SemigroupBasis.Generated.Order6GenericCASRootData.S6_5368.basis
  exact
    FiniteNilpotentCounterexample.models_cons targetLaw0Valid <|
      FiniteNilpotentCounterexample.models_cons targetLaw1Valid <|
        FiniteNilpotentCounterexample.models_cons targetLaw2Valid <|
          FiniteNilpotentCounterexample.models_cons targetLaw3Valid <|
            FiniteNilpotentCounterexample.models_nil oppositeTable.semigroup

/-- Exact identity-theory transfer authenticated by the finite certificate. -/
theorem sameIdentityTheory :
    SameIdentityTheoryOver SemigroupBasis.Generated.Order6GenericCASRootData.S6_5368.oppositeTable.semigroup
      oppositeTable.semigroup Nat := by
  intro identity
  constructor
  · intro sourceValid valuation
    exact Derives.sound targetModels
      (SemigroupBasis.CoRoots.Order6GenericCASSubdirectS6_5368.basisFor.2 identity sourceValid) valuation
  · intro targetValid
    have powerValid :=
      identity.satisfiedByPi oppositeTable.semigroup
        (Fin 4) targetValid
    have subValid :=
      powerCertificate.embedding.pullback_identity identity powerValid
    exact quotient.pushforwardIdentity identity subValid

/-- First-layer generic-CAS basis wrapper for `S6_5371`. -/
theorem opposite_basis :
    BasisFor table.semigroup.opposite SemigroupBasis.Generated.Order6GenericCASRootData.S6_5368.basis := by
  have transferred :
      BasisFor oppositeTable.semigroup SemigroupBasis.Generated.Order6GenericCASRootData.S6_5368.basis :=
    (basisFor_iff_of_sameIdentityTheoryOver sameIdentityTheory).mp
      SemigroupBasis.CoRoots.Order6GenericCASSubdirectS6_5368.basisFor
  simpa only [oppositeTable_semigroup] using transferred

end SemigroupBasis.Generated.Order6GenericCASRootWrappers.S6_5371
