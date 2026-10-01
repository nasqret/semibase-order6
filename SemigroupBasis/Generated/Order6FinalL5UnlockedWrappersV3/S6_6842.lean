import SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6483Representative
import SemigroupBasis.FiniteNilpotentCounterexample
import SemigroupBasis.Nonfinite
import SemigroupBasis.Opposite
import SemigroupBasis.RightGeneratedPowerCertificate

set_option maxRecDepth 2048

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6842

open SemigroupBasis

def routeManifestRowSHA256 : String := "dab0d0f53c3f0421f6a5acf635f9a825f31532d625ae45bc9b3ffd3ea9ed2eeb"
def witnessRecordSHA256 : String := "56494d9d2f1e35746b9d4cf299b6f45be9d910164b182d7e6f528940495afb31"
def transferComponentSHA256 : String := "56494d9d2f1e35746b9d4cf299b6f45be9d910164b182d7e6f528940495afb31"
def powerCertificateSHA256 : String := "926a35865ffe02322566017a762c97273429c7dc2fb2406d9f2a6c26a937d265"

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
        if left = 3 then row6 0 0 2 3 4 3 right else
          if left = 4 then row6 2 2 0 4 3 4 right else
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
  "92f9e6da149d8be8aecd0c92e63e7bb75182a4bc2fa20c5dff48ab3e95b8357b"

private def packedStateVectorCodeChunk0 (index : Nat) : Nat :=
  match index with
  | 0 => 50787912169
  | 1 => 73764044502
  | 2 => 2131238340
  | 3 => 50424826104
  | 4 => 46131790032
  | 5 => 39855055968
  | 6 => 45828944640
  | 7 => 73703236176
  | 8 => 8411812416
  | 9 => 316934208
  | 10 => 1827437760
  | 11 => 2117754720
  | 12 => 50425106040
  | 13 => 45768711744
  | 14 => 39491971200
  | 15 => 46131774480
  | 16 => 46083079872
  | 17 => 39552732864
  | 18 => 39853376352
  | 19 => 45828384768
  | 20 => 45768416256
  | 21 => 45780189120
  | 22 => 73703251728
  | 23 => 8351050752
  | 24 => 6598107072
  | 25 => 8410132800
  | 26 => 316654272
  | 27 => 14572224
  | 28 => 303450624
  | 29 => 14012352
  | 30 => 1827422208
  | _ => 1814000832

private def packedStateVectorCodeChunk1 (index : Nat) : Nat :=
  match index with
  | 0 => 2121113952
  | 1 => 45768991680
  | 2 => 39492251136
  | 3 => 45768696192
  | 4 => 45720002880
  | 5 => 39189655872
  | 6 => 39490291584
  | 7 => 46083064320
  | 8 => 46081400256
  | 9 => 39552717312
  | 10 => 39551053248
  | 11 => 45767856384
  | 12 => 45779629248
  | 13 => 45768431808
  | 14 => 45719707392
  | 15 => 45778509504
  | 16 => 8351066304
  | 17 => 6537625344
  | 18 => 8349371136
  | 19 => 6597547200
  | 20 => 6596427456
  | 21 => 14292288
  | 22 => 303170688
  | 23 => 14556672
  | 24 => 1135296
  | 25 => 306809856
  | 26 => 13452480
  | 27 => 13996800
  | 28 => 575424
  | 29 => 1813985280
  | 30 => 1817360064
  | _ => 45768976128

private def packedStateVectorCodeChunk2 (index : Nat) : Nat :=
  match index with
  | 0 => 45720282816
  | 1 => 39189935808
  | 2 => 39490571520
  | 3 => 45719987328
  | 4 => 45718323264
  | 5 => 39189640320
  | 6 => 39187976256
  | 7 => 46081384704
  | 8 => 39551037696
  | 9 => 45767871936
  | 10 => 45719147520
  | 11 => 45777949632
  | 12 => 45719722944
  | 13 => 45718027776
  | 14 => 6537640896
  | 15 => 8349386688
  | 16 => 6537065472
  | 17 => 6535945728
  | 18 => 6595867584
  | 19 => 14276736
  | 20 => 855360
  | 21 => 306529920
  | 22 => 1119744
  | 23 => 4494528
  | 24 => 13436928
  | 25 => 15552
  | 26 => 559872
  | 27 => 3934656
  | 28 => 1817344512
  | 29 => 45720267264
  | 30 => 45718603200
  | _ => 39189920256

private def packedStateVectorCodeChunk3 (index : Nat) : Nat :=
  match index with
  | 0 => 39188256192
  | 1 => 45718307712
  | 2 => 39187960704
  | 3 => 45719163072
  | 4 => 45717467904
  | 5 => 45718043328
  | 6 => 6537081024
  | 7 => 6535961280
  | 8 => 6535385856
  | 9 => 839808
  | 10 => 4214592
  | 11 => 4478976
  | 12 => 0
  | 13 => 3374784
  | 14 => 3919104
  | 15 => 45718587648
  | 16 => 39188240640
  | 17 => 45717483456
  | 18 => 6535401408
  | 19 => 4199040
  | _ => 3359232

private def packedStateVectorCode (state : Fin 117) : Nat :=
  if state.val < 32 then packedStateVectorCodeChunk0 state.val else
    if state.val < 64 then packedStateVectorCodeChunk1 (state.val - 32) else
      if state.val < 96 then packedStateVectorCodeChunk2 (state.val - 64) else
        packedStateVectorCodeChunk3 (state.val - 96)

def stateVector (state : Fin 117)
    (coordinate : Fin 14) : Fin 6 :=
  ⟨(packedStateVectorCode state / 6 ^ coordinate.val) % 6,
    Nat.mod_lt _ (by decide)⟩

def generatorVector (generator : Fin 3)
    (coordinate : Fin 14) : Fin 6 :=
  match generator.val with
  | 0 =>
      match coordinate.val with
      | 0 => (1 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (5 : Fin 6)
      | 4 => (1 : Fin 6)
      | 5 => (1 : Fin 6)
      | 6 => (5 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (3 : Fin 6)
      | 9 => (5 : Fin 6)
      | 10 => (5 : Fin 6)
      | 11 => (1 : Fin 6)
      | 12 => (5 : Fin 6)
      | _ => (3 : Fin 6)
  | 1 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (1 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (5 : Fin 6)
      | 5 => (2 : Fin 6)
      | 6 => (1 : Fin 6)
      | 7 => (1 : Fin 6)
      | 8 => (3 : Fin 6)
      | 9 => (5 : Fin 6)
      | 10 => (1 : Fin 6)
      | 11 => (5 : Fin 6)
      | 12 => (3 : Fin 6)
      | _ => (5 : Fin 6)
  | _ =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (1 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (5 : Fin 6)
      | 6 => (1 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (2 : Fin 6)
      | 9 => (1 : Fin 6)
      | 10 => (5 : Fin 6)
      | 11 => (5 : Fin 6)
      | 12 => (0 : Fin 6)
      | _ => (0 : Fin 6)

private def packedTransitionCodeChunk0 (index : Nat) : Nat :=
  match index with
  | 0 => 68916
  | 1 => 110337
  | 2 => 151758
  | 3 => 193179
  | 4 => 220792
  | 5 => 248405
  | 6 => 289828
  | 7 => 317441
  | 8 => 344940
  | 9 => 386477
  | 10 => 427898
  | 11 => 441703
  | 12 => 469290
  | 13 => 496932
  | 14 => 524545
  | 15 => 534374
  | 16 => 552159
  | 17 => 579772
  | 18 => 73397
  | 19 => 607353
  | 20 => 635002
  | 21 => 648809
  | 22 => 657936
  | 23 => 690115
  | 24 => 717612
  | 25 => 115414
  | 26 => 745416
  | 27 => 773072
  | 28 => 786879
  | 29 => 828301
  | 30 => 836258
  | _ => 855915

private def packedTransitionCodeChunk1 (index : Nat) : Nat :=
  match index with
  | 0 => 157890
  | 1 => 883480
  | 2 => 911093
  | 3 => 918747
  | 4 => 938755
  | 5 => 966368
  | 6 => 199902
  | 7 => 973858
  | 8 => 227399
  | 9 => 987666
  | 10 => 241207
  | 11 => 1021547
  | 12 => 1035354
  | 13 => 1042777
  | 14 => 1063019
  | 15 => 296553
  | 16 => 1084200
  | 17 => 1118015
  | 18 => 324171
  | 19 => 1131882
  | 20 => 338095
  | 21 => 1159614
  | 22 => 1173421
  | 23 => 1180496
  | 24 => 1201089
  | 25 => 393556
  | 26 => 1228646
  | 27 => 1235491
  | 28 => 1256318
  | 29 => 1263105
  | 30 => 435214
  | _ => 1276973

private def packedTransitionCodeChunk2 (index : Nat) : Nat :=
  match index with
  | 0 => 1297683
  | 1 => 1325296
  | 2 => 476696
  | 3 => 1332138
  | 4 => 504247
  | 5 => 1345946
  | 6 => 518055
  | 7 => 538648
  | 8 => 566261
  | 9 => 1360287
  | 10 => 1380529
  | 11 => 614063
  | 12 => 1388070
  | 13 => 641611
  | 14 => 1415802
  | 15 => 663025
  | 16 => 1435639
  | 17 => 682916
  | 18 => 710359
  | 19 => 1443601
  | 20 => 1463375
  | 21 => 751665
  | 22 => 1471380
  | 23 => 779209
  | 24 => 1485257
  | 25 => 1504797
  | 26 => 1512918
  | 27 => 834319
  | 28 => 842393
  | 29 => 1527034
  | 30 => 889151
  | _ => 1540842

private def packedTransitionCodeChunk3 (index : Nat) : Nat :=
  match index with
  | 0 => 902959
  | 1 => 925230
  | 2 => 952843
  | 3 => 1555591
  | 4 => 1026284
  | 5 => 1049486
  | 6 => 1569984
  | 7 => 1077333
  | 8 => 1108539
  | 9 => 1584149
  | 10 => 1163418
  | 11 => 1187548
  | 12 => 1598427
  | 13 => 1231984
  | 14 => 1242773
  | 15 => 1284172
  | 16 => 1311785
  | 17 => 1367012
  | 18 => 1408549
  | 19 => 1449854
  | _ => 1491275

private def packedTransitionCode (state : Fin 117) : Nat :=
  if state.val < 32 then packedTransitionCodeChunk0 state.val else
    if state.val < 64 then packedTransitionCodeChunk1 (state.val - 32) else
      if state.val < 96 then packedTransitionCodeChunk2 (state.val - 64) else
        packedTransitionCodeChunk3 (state.val - 96)

def transition (state : Fin 117)
    (generator : Fin 3) : Fin 117 :=
  ⟨(packedTransitionCode state / 117 ^ generator.val) % 117,
    Nat.mod_lt _ (by decide)⟩

private def packedRepresentativeHeadBlockCode (index : Nat) : Nat :=
  match index with
  | 0 => 1144551581643880728967785791133
  | _ => 18213319574440558413465348

def representativeHead (state : Fin 117) : Fin 3 :=
  ⟨(packedRepresentativeHeadBlockCode (state.val / 64) /
      3 ^ (state.val % 64)) % 3,
    Nat.mod_lt _ (by decide)⟩

private def representativeTailChunk0 (index : Nat) :
    List (Fin 3) :=
  match index with
  | 0 => []
  | 1 => []
  | 2 => []
  | 3 => [0]
  | 4 => [1]
  | 5 => [2]
  | 6 => [0]
  | 7 => [1]
  | 8 => [2]
  | 9 => [0]
  | 10 => [1]
  | 11 => [2]
  | 12 => [0, 0]
  | 13 => [0, 1]
  | 14 => [0, 2]
  | 15 => [1, 1]
  | 16 => [1, 2]
  | 17 => [2, 1]
  | 18 => [2, 2]
  | 19 => [0, 0]
  | 20 => [0, 1]
  | 21 => [0, 2]
  | 22 => [1, 1]
  | 23 => [1, 2]
  | 24 => [2, 0]
  | 25 => [2, 2]
  | 26 => [0, 0]
  | 27 => [0, 1]
  | 28 => [0, 2]
  | 29 => [1, 0]
  | 30 => [1, 1]
  | _ => [1, 2]

private def representativeTailChunk1 (index : Nat) :
    List (Fin 3) :=
  match index with
  | 0 => [2, 2]
  | 1 => [0, 0, 1]
  | 2 => [0, 0, 2]
  | 3 => [0, 1, 1]
  | 4 => [0, 1, 2]
  | 5 => [0, 2, 1]
  | 6 => [0, 2, 2]
  | 7 => [1, 1, 2]
  | 8 => [1, 2, 2]
  | 9 => [2, 1, 1]
  | 10 => [2, 1, 2]
  | 11 => [0, 0, 1]
  | 12 => [0, 0, 2]
  | 13 => [0, 1, 1]
  | 14 => [0, 1, 2]
  | 15 => [0, 2, 2]
  | 16 => [1, 1, 2]
  | 17 => [1, 2, 0]
  | 18 => [1, 2, 2]
  | 19 => [2, 0, 0]
  | 20 => [2, 0, 2]
  | 21 => [0, 0, 1]
  | 22 => [0, 0, 2]
  | 23 => [0, 1, 1]
  | 24 => [0, 1, 2]
  | 25 => [0, 2, 2]
  | 26 => [1, 0, 0]
  | 27 => [1, 0, 1]
  | 28 => [1, 0, 2]
  | 29 => [1, 1, 2]
  | 30 => [1, 2, 2]
  | _ => [0, 0, 1, 1]

private def representativeTailChunk2 (index : Nat) :
    List (Fin 3) :=
  match index with
  | 0 => [0, 0, 1, 2]
  | 1 => [0, 0, 2, 1]
  | 2 => [0, 0, 2, 2]
  | 3 => [0, 1, 1, 2]
  | 4 => [0, 1, 2, 2]
  | 5 => [0, 2, 1, 1]
  | 6 => [0, 2, 1, 2]
  | 7 => [1, 1, 2, 2]
  | 8 => [2, 1, 1, 2]
  | 9 => [0, 0, 1, 1]
  | 10 => [0, 0, 1, 2]
  | 11 => [0, 0, 2, 2]
  | 12 => [0, 1, 1, 2]
  | 13 => [0, 1, 2, 2]
  | 14 => [1, 1, 2, 0]
  | 15 => [1, 1, 2, 2]
  | 16 => [1, 2, 0, 0]
  | 17 => [1, 2, 0, 2]
  | 18 => [2, 0, 0, 2]
  | 19 => [0, 0, 1, 1]
  | 20 => [0, 0, 1, 2]
  | 21 => [0, 0, 2, 2]
  | 22 => [0, 1, 1, 2]
  | 23 => [0, 1, 2, 2]
  | 24 => [1, 0, 0, 1]
  | 25 => [1, 0, 0, 2]
  | 26 => [1, 0, 1, 2]
  | 27 => [1, 0, 2, 2]
  | 28 => [1, 1, 2, 2]
  | 29 => [0, 0, 1, 1, 2]
  | 30 => [0, 0, 1, 2, 2]
  | _ => [0, 0, 2, 1, 1]

private def representativeTailChunk3 (index : Nat) :
    List (Fin 3) :=
  match index with
  | 0 => [0, 0, 2, 1, 2]
  | 1 => [0, 1, 1, 2, 2]
  | 2 => [0, 2, 1, 1, 2]
  | 3 => [0, 0, 1, 1, 2]
  | 4 => [0, 0, 1, 2, 2]
  | 5 => [0, 1, 1, 2, 2]
  | 6 => [1, 1, 2, 0, 0]
  | 7 => [1, 1, 2, 0, 2]
  | 8 => [1, 2, 0, 0, 2]
  | 9 => [0, 0, 1, 1, 2]
  | 10 => [0, 0, 1, 2, 2]
  | 11 => [0, 1, 1, 2, 2]
  | 12 => [1, 0, 0, 1, 2]
  | 13 => [1, 0, 0, 2, 2]
  | 14 => [1, 0, 1, 2, 2]
  | 15 => [0, 0, 1, 1, 2, 2]
  | 16 => [0, 0, 2, 1, 1, 2]
  | 17 => [0, 0, 1, 1, 2, 2]
  | 18 => [1, 1, 2, 0, 0, 2]
  | 19 => [0, 0, 1, 1, 2, 2]
  | _ => [1, 0, 0, 1, 2, 2]

def representativeTail (state : Fin 117) :
    List (Fin 3) :=
  if state.val < 32 then representativeTailChunk0 state.val else
    if state.val < 64 then representativeTailChunk1 (state.val - 32) else
      if state.val < 96 then representativeTailChunk2 (state.val - 64) else
        representativeTailChunk3 (state.val - 96)

private def packedSourceLabelBlockCode (index : Nat) : Nat :=
  match index with
  | 0 => 52783572219166850346175879482024577536882658552205
  | _ => 804539234884857557003131058220898861055

def sourceLabel (state : Fin 117) : Fin 6 :=
  ⟨(packedSourceLabelBlockCode (state.val / 64) /
      6 ^ (state.val % 64)) % 6,
    Nat.mod_lt _ (by decide)⟩

def generatorSourceLabel (generator : Fin 3) : Fin 6 :=
  match generator.val with
  | 0 => (5 : Fin 6)
  | 1 => (4 : Fin 6)
  | _ => (2 : Fin 6)

def sourcePreimage (value : Fin 6) : Fin 117 :=
  match value.val with
  | 0 => (8 : Fin 117)
  | 1 => (10 : Fin 117)
  | 2 => (2 : Fin 117)
  | 3 => (7 : Fin 117)
  | 4 => (1 : Fin 117)
  | _ => (0 : Fin 117)

private def decodeStateCodeChunk0 (code : Nat) : Fin 117 :=
  if code = 0 then (108 : Fin 117) else
  if code = 15552 then (89 : Fin 117) else
  if code = 559872 then (90 : Fin 117) else
  if code = 575424 then (60 : Fin 117) else
  if code = 839808 then (105 : Fin 117) else
  if code = 855360 then (84 : Fin 117) else
  if code = 1119744 then (86 : Fin 117) else
  if code = 1135296 then (56 : Fin 117) else
  if code = 3359232 then (116 : Fin 117) else
  if code = 3374784 then (109 : Fin 117) else
  if code = 3919104 then (110 : Fin 117) else
  if code = 3934656 then (91 : Fin 117) else
  if code = 4199040 then (115 : Fin 117) else
  if code = 4214592 then (106 : Fin 117) else
  if code = 4478976 then (107 : Fin 117) else
  if code = 4494528 then (87 : Fin 117) else
  if code = 13436928 then (88 : Fin 117) else
  if code = 13452480 then (58 : Fin 117) else
  if code = 13996800 then (59 : Fin 117) else
  if code = 14012352 then (29 : Fin 117) else
  if code = 14276736 then (83 : Fin 117) else
  if code = 14292288 then (53 : Fin 117) else
  if code = 14556672 then (55 : Fin 117) else
  if code = 14572224 then (27 : Fin 117) else
  if code = 303170688 then (54 : Fin 117) else
  if code = 303450624 then (28 : Fin 117) else
  if code = 306529920 then (85 : Fin 117) else
  if code = 306809856 then (57 : Fin 117) else
  if code = 316654272 then (26 : Fin 117) else
  if code = 316934208 then (9 : Fin 117) else
  if code = 1813985280 then (61 : Fin 117) else
  if code = 1814000832 then (31 : Fin 117) else
  (0 : Fin 117)

private def decodeStateCodeChunk1 (code : Nat) : Fin 117 :=
  if code = 1817344512 then (92 : Fin 117) else
  if code = 1817360064 then (62 : Fin 117) else
  if code = 1827422208 then (30 : Fin 117) else
  if code = 1827437760 then (10 : Fin 117) else
  if code = 2117754720 then (11 : Fin 117) else
  if code = 2121113952 then (32 : Fin 117) else
  if code = 2131238340 then (2 : Fin 117) else
  if code = 6535385856 then (104 : Fin 117) else
  if code = 6535401408 then (114 : Fin 117) else
  if code = 6535945728 then (81 : Fin 117) else
  if code = 6535961280 then (103 : Fin 117) else
  if code = 6537065472 then (80 : Fin 117) else
  if code = 6537081024 then (102 : Fin 117) else
  if code = 6537625344 then (49 : Fin 117) else
  if code = 6537640896 then (78 : Fin 117) else
  if code = 6595867584 then (82 : Fin 117) else
  if code = 6596427456 then (52 : Fin 117) else
  if code = 6597547200 then (51 : Fin 117) else
  if code = 6598107072 then (24 : Fin 117) else
  if code = 8349371136 then (50 : Fin 117) else
  if code = 8349386688 then (79 : Fin 117) else
  if code = 8351050752 then (23 : Fin 117) else
  if code = 8351066304 then (48 : Fin 117) else
  if code = 8410132800 then (25 : Fin 117) else
  if code = 8411812416 then (8 : Fin 117) else
  if code = 39187960704 then (98 : Fin 117) else
  if code = 39187976256 then (70 : Fin 117) else
  if code = 39188240640 then (112 : Fin 117) else
  if code = 39188256192 then (96 : Fin 117) else
  if code = 39189640320 then (69 : Fin 117) else
  if code = 39189655872 then (37 : Fin 117) else
  if code = 39189920256 then (95 : Fin 117) else
  (0 : Fin 117)

private def decodeStateCodeChunk2 (code : Nat) : Fin 117 :=
  if code = 39189935808 then (65 : Fin 117) else
  if code = 39490291584 then (38 : Fin 117) else
  if code = 39490571520 then (66 : Fin 117) else
  if code = 39491971200 then (14 : Fin 117) else
  if code = 39492251136 then (34 : Fin 117) else
  if code = 39551037696 then (72 : Fin 117) else
  if code = 39551053248 then (42 : Fin 117) else
  if code = 39552717312 then (41 : Fin 117) else
  if code = 39552732864 then (17 : Fin 117) else
  if code = 39853376352 then (18 : Fin 117) else
  if code = 39855055968 then (5 : Fin 117) else
  if code = 45717467904 then (100 : Fin 117) else
  if code = 45717483456 then (113 : Fin 117) else
  if code = 45718027776 then (77 : Fin 117) else
  if code = 45718043328 then (101 : Fin 117) else
  if code = 45718307712 then (97 : Fin 117) else
  if code = 45718323264 then (68 : Fin 117) else
  if code = 45718587648 then (111 : Fin 117) else
  if code = 45718603200 then (94 : Fin 117) else
  if code = 45719147520 then (74 : Fin 117) else
  if code = 45719163072 then (99 : Fin 117) else
  if code = 45719707392 then (46 : Fin 117) else
  if code = 45719722944 then (76 : Fin 117) else
  if code = 45719987328 then (67 : Fin 117) else
  if code = 45720002880 then (36 : Fin 117) else
  if code = 45720267264 then (93 : Fin 117) else
  if code = 45720282816 then (64 : Fin 117) else
  if code = 45767856384 then (43 : Fin 117) else
  if code = 45767871936 then (73 : Fin 117) else
  if code = 45768416256 then (20 : Fin 117) else
  if code = 45768431808 then (45 : Fin 117) else
  if code = 45768696192 then (35 : Fin 117) else
  (0 : Fin 117)

private def decodeStateCodeChunk3 (code : Nat) : Fin 117 :=
  if code = 45768711744 then (13 : Fin 117) else
  if code = 45768976128 then (63 : Fin 117) else
  if code = 45768991680 then (33 : Fin 117) else
  if code = 45777949632 then (75 : Fin 117) else
  if code = 45778509504 then (47 : Fin 117) else
  if code = 45779629248 then (44 : Fin 117) else
  if code = 45780189120 then (21 : Fin 117) else
  if code = 45828384768 then (19 : Fin 117) else
  if code = 45828944640 then (6 : Fin 117) else
  if code = 46081384704 then (71 : Fin 117) else
  if code = 46081400256 then (40 : Fin 117) else
  if code = 46083064320 then (39 : Fin 117) else
  if code = 46083079872 then (16 : Fin 117) else
  if code = 46131774480 then (15 : Fin 117) else
  if code = 46131790032 then (4 : Fin 117) else
  if code = 50424826104 then (3 : Fin 117) else
  if code = 50425106040 then (12 : Fin 117) else
  if code = 50787912169 then (0 : Fin 117) else
  if code = 73703236176 then (7 : Fin 117) else
  if code = 73703251728 then (22 : Fin 117) else
  if code = 73764044502 then (1 : Fin 117) else
  (0 : Fin 117)

private def stateVectorCode
    (vector : Fin 14 -> Fin 6) : Nat :=
  (vector (0 : Fin 14)).val + 6 * ((vector (1 : Fin 14)).val + 6 * ((vector (2 : Fin 14)).val + 6 * ((vector (3 : Fin 14)).val + 6 * ((vector (4 : Fin 14)).val + 6 * ((vector (5 : Fin 14)).val + 6 * ((vector (6 : Fin 14)).val + 6 * ((vector (7 : Fin 14)).val + 6 * ((vector (8 : Fin 14)).val + 6 * ((vector (9 : Fin 14)).val + 6 * ((vector (10 : Fin 14)).val + 6 * ((vector (11 : Fin 14)).val + 6 * ((vector (12 : Fin 14)).val + 6 * ((vector (13 : Fin 14)).val)))))))))))))

private def decodeStateCode (code : Nat) : Fin 117 :=
  if code < 1817344512 then decodeStateCodeChunk0 code else
  if code < 39189935808 then decodeStateCodeChunk1 code else
  if code < 45768711744 then decodeStateCodeChunk2 code else
  decodeStateCodeChunk3 code

private def decodeState
    (vector : Fin 14 -> Fin 6) : Fin 117 :=
  decodeStateCode (stateVectorCode vector)

set_option maxHeartbeats 2000000 in
private theorem decodeState_stateVector (state : Fin 117) :
    decodeState (stateVector state) = state := by
  decide +revert

set_option maxHeartbeats 2000000 in
private theorem transitionMap :
    forall (state : Fin 117)
      (generator : Fin 3)
      (coordinate : Fin 14),
      stateVector (transition state generator) coordinate =
        oppositeTable.semigroup.mul (stateVector state coordinate)
          (generatorVector generator coordinate) := by
  intro state generator coordinate
  apply Fin.ext
  exact by decide +revert

set_option maxHeartbeats 2000000 in
private theorem representativeMap :
    forall (state : Fin 117)
      (coordinate : Fin 14),
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
    (U := Fin 117)
    (G := Fin 3)
    (I := Fin 14) oppositeTable.semigroup where
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
    forall (state : Fin 117)
      (generator : Fin 3),
      sourceLabel (transition state generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6483Representative.sourceSemigroup.mul (sourceLabel state)
          (generatorSourceLabel generator) := by
  intro state generator
  apply Fin.ext
  exact by decide +revert

set_option maxHeartbeats 2000000 in
private theorem sourceLabelRepresentative :
    forall state : Fin 117,
      sourceLabel state =
        (representativeTail state).foldl
          (fun value generator =>
            SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6483Representative.sourceSemigroup.mul value
              (generatorSourceLabel generator))
          (generatorSourceLabel (representativeHead state)) := by
  intro state
  apply Fin.ext
  exact by decide +revert

private theorem sourceLabelRightMultiplyWord
    (state : Fin 117)
    (word : List (Fin 3)) :
    sourceLabel (powerCertificate.rightMultiplyWord state word) =
      word.foldl
        (fun value generator =>
          SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6483Representative.sourceSemigroup.mul value
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
              SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6483Representative.sourceSemigroup.mul value
                (generatorSourceLabel nextGenerator))
            (SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6483Representative.sourceSemigroup.mul (sourceLabel state)
              (generatorSourceLabel generator))
      rw [inductionHypothesis]
      rw [sourceLabelTransition]

private theorem sourceFoldlGeneratorAssoc
    (left right : Fin 6)
    (word : List (Fin 3)) :
    word.foldl
        (fun value generator =>
          SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6483Representative.sourceSemigroup.mul value
            (generatorSourceLabel generator))
        (SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6483Representative.sourceSemigroup.mul left right) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6483Representative.sourceSemigroup.mul left
        (word.foldl
          (fun value generator =>
            SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6483Representative.sourceSemigroup.mul value
              (generatorSourceLabel generator))
          right) := by
  induction word generalizing right with
  | nil => rfl
  | cons generator word inductionHypothesis =>
      simp only [List.foldl_cons]
      rw [SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6483Representative.sourceSemigroup.assoc]
      exact inductionHypothesis
        (SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6483Representative.sourceSemigroup.mul right (generatorSourceLabel generator))

private theorem sourceLabelMapMul :
    forall (left right : Fin 117),
      sourceLabel (powerCertificate.semigroup.mul left right) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6483Representative.sourceSemigroup.mul (sourceLabel left) (sourceLabel right) := by
  intro left right
  calc
    sourceLabel (powerCertificate.semigroup.mul left right) =
        sourceLabel
          (powerCertificate.rightMultiplyWord
            (transition left (representativeHead right))
            (representativeTail right)) := rfl
    _ = (representativeTail right).foldl
          (fun value generator =>
            SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6483Representative.sourceSemigroup.mul value
              (generatorSourceLabel generator))
          (sourceLabel (transition left (representativeHead right))) :=
      sourceLabelRightMultiplyWord _ _
    _ = (representativeTail right).foldl
          (fun value generator =>
            SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6483Representative.sourceSemigroup.mul value
              (generatorSourceLabel generator))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6483Representative.sourceSemigroup.mul (sourceLabel left)
            (generatorSourceLabel (representativeHead right))) :=
      congrArg
        (fun initial =>
          (representativeTail right).foldl
            (fun value generator =>
              SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6483Representative.sourceSemigroup.mul value
                (generatorSourceLabel generator))
            initial)
        (sourceLabelTransition left (representativeHead right))
    _ = SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6483Representative.sourceSemigroup.mul (sourceLabel left)
          ((representativeTail right).foldl
            (fun value generator =>
              SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6483Representative.sourceSemigroup.mul value
                (generatorSourceLabel generator))
            (generatorSourceLabel (representativeHead right))) :=
      sourceFoldlGeneratorAssoc _ _ _
    _ = SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6483Representative.sourceSemigroup.mul (sourceLabel left) (sourceLabel right) :=
      congrArg (SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6483Representative.sourceSemigroup.mul (sourceLabel left))
        (sourceLabelRepresentative right).symm

set_option maxHeartbeats 1000000 in
private theorem sourceLabelRightInverse :
    forall value : Fin 6, sourceLabel (sourcePreimage value) = value := by
  intro value
  apply Fin.ext
  exact by decide +revert

/-- The generated term-function semigroup maps onto the selected root. -/
def quotient : SplitSurjection powerCertificate.semigroup
    SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6483Representative.sourceSemigroup where
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
    SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6483Representative.law0.SatisfiedBy oppositeTable.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    oppositeTable SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6483Representative.law0
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
    SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6483Representative.law1.SatisfiedBy oppositeTable.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    oppositeTable SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6483Representative.law1
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
    SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6483Representative.law2.SatisfiedBy oppositeTable.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    oppositeTable SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6483Representative.law2
    targetLaw2ToFinite targetLaw2FromFinite (by decide) (by decide)

/-- Exact finite checks that the selected target models the root basis. -/
theorem targetModels :
    Models oppositeTable.semigroup SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6483Representative.basis := by
  unfold SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6483Representative.basis
  exact
    FiniteNilpotentCounterexample.models_cons targetLaw0Valid <|
      FiniteNilpotentCounterexample.models_cons targetLaw1Valid <|
        FiniteNilpotentCounterexample.models_cons targetLaw2Valid <|
          FiniteNilpotentCounterexample.models_nil oppositeTable.semigroup

/-- Exact identity-theory transfer authenticated by the finite certificate. -/
theorem sameIdentityTheory :
    SameIdentityTheoryOver SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6483Representative.sourceSemigroup
      oppositeTable.semigroup Nat := by
  intro identity
  constructor
  · intro sourceValid valuation
    exact Derives.sound targetModels
      (SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6483Representative.basis_complete.2 identity sourceValid) valuation
  · intro targetValid
    have powerValid :=
      identity.satisfiedByPi oppositeTable.semigroup
        (Fin 14) targetValid
    have subValid :=
      powerCertificate.embedding.pullback_identity identity powerValid
    exact quotient.pushforwardIdentity identity subValid

/-- First-layer generic-CAS basis wrapper for `S6_6842`. -/
theorem representative_basis :
    BasisFor table.semigroup.opposite SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6483Representative.basis := by
  have transferred :
      BasisFor oppositeTable.semigroup SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6483Representative.basis :=
    (basisFor_iff_of_sameIdentityTheoryOver sameIdentityTheory).mp
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6483Representative.basis_complete
  simpa only [oppositeTable_semigroup] using transferred


theorem opposite_basis :
    BasisFor table.semigroup (reversedBasis SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6483Representative.basis) :=
  representative_basis.oppositeReversed

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6842
