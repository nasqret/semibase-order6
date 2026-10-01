import SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6483Representative
import SemigroupBasis.FiniteNilpotentCounterexample
import SemigroupBasis.Nonfinite
import SemigroupBasis.Opposite
import SemigroupBasis.RightGeneratedPowerCertificate

set_option maxRecDepth 2048

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9050

open SemigroupBasis

def routeManifestRowSHA256 : String := "26f7d6db1bf251ae5ca5ef3d128d932101ba2f8a8a3f1d54984ad1b700e27d2f"
def witnessRecordSHA256 : String := "2903da3a10a7029f7db9233bf1b9f7274cce9667486715a190469c2dd0b302c3"
def transferComponentSHA256 : String := "2903da3a10a7029f7db9233bf1b9f7274cce9667486715a190469c2dd0b302c3"
def powerCertificateSHA256 : String := "8e7472b3c65832eca93de6accf52409abc026c36fa4ee38d2416d337bafe7f9e"

private def row6
    (c0 c1 c2 c3 c4 c5 : Fin 6) (column : Fin 6) : Fin 6 :=
  if column = 0 then c0 else
    if column = 1 then c1 else
      if column = 2 then c2 else
        if column = 3 then c3 else
          if column = 4 then c4 else c5

/-- Exact one-based catalogue table committed by the portable witness. -/
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 1 1 0 4 5 right else
    if left = 1 then row6 1 0 0 1 4 5 right else
      if left = 2 then row6 1 0 0 1 4 5 right else
        if left = 3 then row6 0 1 2 3 4 5 right else
          if left = 4 then row6 4 4 4 4 4 5 right else
            row6 4 4 4 5 4 5 right

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
  "515d363778581450865fba663de8b6ee34987e1097b5b036152f5e7f2d9effbd"

private def packedStateVectorCodeChunk0 (index : Nat) : Nat :=
  match index with
  | 0 => 4378622
  | 1 => 5722578
  | 2 => 6116364
  | 3 => 1019304
  | 4 => 3730549
  | 5 => 4471495
  | 6 => 2378815
  | 7 => 5069322
  | 8 => 5792112
  | 9 => 2784283
  | 10 => 5559012
  | 11 => 6115932
  | 12 => 2698963
  | 13 => 371340
  | 14 => 1112184
  | 15 => 3403993
  | 16 => 3870079
  | 17 => 3916735
  | 18 => 4471279
  | 19 => 699228
  | 20 => 1725667
  | 21 => 2471695
  | 22 => 5395950
  | 23 => 5232168
  | 24 => 2463919
  | 25 => 5791896
  | 26 => 1104624
  | 27 => 2229559
  | 28 => 2783851
  | 29 => 2230855
  | 30 => 5279040
  | _ => 5558580

private def packedStateVectorCodeChunk1 (index : Nat) : Nat :=
  match index with
  | 0 => 6116148
  | 1 => 2050927
  | 2 => 2791843
  | 3 => 44712
  | 4 => 510876
  | 5 => 557532
  | 6 => 1111968
  | 7 => 3590179
  | 8 => 3869863
  | 9 => 3636835
  | 10 => 3916519
  | 11 => 46008
  | 12 => 792108
  | 13 => 2052223
  | 14 => 1911859
  | 15 => 2471479
  | 16 => 5512140
  | 17 => 1904083
  | 18 => 5231952
  | 19 => 784332
  | 20 => 2463703
  | 21 => 549972
  | 22 => 1104192
  | 23 => 1949659
  | 24 => 2229127
  | 25 => 2784067
  | 26 => 551268
  | 27 => 1950955
  | 28 => 2230423
  | 29 => 5278608
  | 30 => 5558796
  | _ => 1724371

private def packedStateVectorCodeChunk2 (index : Nat) : Nat :=
  match index with
  | 0 => 2190463
  | 1 => 2237119
  | 2 => 2791627
  | 3 => 230904
  | 4 => 510660
  | 5 => 277560
  | 6 => 557316
  | 7 => 3589963
  | 8 => 3636619
  | 9 => 372636
  | 10 => 232200
  | 11 => 791892
  | 12 => 2191759
  | 13 => 1911643
  | 14 => 2183983
  | 15 => 5511924
  | 16 => 224424
  | 17 => 1903867
  | 18 => 784116
  | 19 => 270000
  | 20 => 549540
  | 21 => 1104408
  | 22 => 1949227
  | 23 => 2229343
  | 24 => 271296
  | 25 => 550836
  | 26 => 1950523
  | 27 => 2230639
  | 28 => 5278824
  | 29 => 1910563
  | 30 => 2190247
  | _ => 1957219

private def packedStateVectorCodeChunk3 (index : Nat) : Nat :=
  match index with
  | 0 => 2236903
  | 1 => 230688
  | 2 => 277344
  | 3 => 512172
  | 4 => 231984
  | 5 => 2191543
  | 6 => 504396
  | 7 => 2183767
  | 8 => 224208
  | 9 => 269568
  | 10 => 549756
  | 11 => 1949443
  | 12 => 270864
  | 13 => 551052
  | 14 => 1950739
  | 15 => 1910347
  | 16 => 1957003
  | 17 => 511956
  | 18 => 504180
  | 19 => 269784
  | _ => 271080

private def packedStateVectorCode (state : Fin 117) : Nat :=
  if state.val < 32 then packedStateVectorCodeChunk0 state.val else
    if state.val < 64 then packedStateVectorCodeChunk1 (state.val - 32) else
      if state.val < 96 then packedStateVectorCodeChunk2 (state.val - 64) else
        packedStateVectorCodeChunk3 (state.val - 96)

def stateVector (state : Fin 117)
    (coordinate : Fin 9) : Fin 6 :=
  ⟨(packedStateVectorCode state / 6 ^ coordinate.val) % 6,
    Nat.mod_lt _ (by decide)⟩

def generatorVector (generator : Fin 3)
    (coordinate : Fin 9) : Fin 6 :=
  match generator.val with
  | 0 =>
      match coordinate.val with
      | 0 => (2 : Fin 6)
      | 1 => (2 : Fin 6)
      | 2 => (2 : Fin 6)
      | 3 => (3 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (5 : Fin 6)
      | 6 => (3 : Fin 6)
      | 7 => (3 : Fin 6)
      | _ => (2 : Fin 6)
  | 1 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (3 : Fin 6)
      | 2 => (2 : Fin 6)
      | 3 => (3 : Fin 6)
      | 4 => (5 : Fin 6)
      | 5 => (3 : Fin 6)
      | 6 => (2 : Fin 6)
      | 7 => (2 : Fin 6)
      | _ => (3 : Fin 6)
  | _ =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (3 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (3 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (5 : Fin 6)
      | 7 => (3 : Fin 6)
      | _ => (3 : Fin 6)

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
  if code = 44712 then (35 : Fin 117) else
  if code = 46008 then (43 : Fin 117) else
  if code = 224208 then (104 : Fin 117) else
  if code = 224424 then (80 : Fin 117) else
  if code = 230688 then (97 : Fin 117) else
  if code = 230904 then (67 : Fin 117) else
  if code = 231984 then (100 : Fin 117) else
  if code = 232200 then (74 : Fin 117) else
  if code = 269568 then (105 : Fin 117) else
  if code = 269784 then (115 : Fin 117) else
  if code = 270000 then (83 : Fin 117) else
  if code = 270864 then (108 : Fin 117) else
  if code = 271080 then (116 : Fin 117) else
  if code = 271296 then (88 : Fin 117) else
  if code = 277344 then (98 : Fin 117) else
  if code = 277560 then (69 : Fin 117) else
  if code = 371340 then (13 : Fin 117) else
  if code = 372636 then (73 : Fin 117) else
  if code = 504180 then (114 : Fin 117) else
  if code = 504396 then (102 : Fin 117) else
  if code = 510660 then (68 : Fin 117) else
  if code = 510876 then (36 : Fin 117) else
  if code = 511956 then (113 : Fin 117) else
  if code = 512172 then (99 : Fin 117) else
  if code = 549540 then (84 : Fin 117) else
  if code = 549756 then (106 : Fin 117) else
  if code = 549972 then (53 : Fin 117) else
  if code = 550836 then (89 : Fin 117) else
  if code = 551052 then (109 : Fin 117) else
  if code = 551268 then (58 : Fin 117) else
  if code = 557316 then (70 : Fin 117) else
  if code = 557532 then (37 : Fin 117) else
  (0 : Fin 117)

private def decodeStateCodeChunk1 (code : Nat) : Fin 117 :=
  if code = 699228 then (19 : Fin 117) else
  if code = 784116 then (82 : Fin 117) else
  if code = 784332 then (51 : Fin 117) else
  if code = 791892 then (75 : Fin 117) else
  if code = 792108 then (44 : Fin 117) else
  if code = 1019304 then (3 : Fin 117) else
  if code = 1104192 then (54 : Fin 117) else
  if code = 1104408 then (85 : Fin 117) else
  if code = 1104624 then (26 : Fin 117) else
  if code = 1111968 then (38 : Fin 117) else
  if code = 1112184 then (14 : Fin 117) else
  if code = 1724371 then (63 : Fin 117) else
  if code = 1725667 then (20 : Fin 117) else
  if code = 1903867 then (81 : Fin 117) else
  if code = 1904083 then (49 : Fin 117) else
  if code = 1910347 then (111 : Fin 117) else
  if code = 1910563 then (93 : Fin 117) else
  if code = 1911643 then (77 : Fin 117) else
  if code = 1911859 then (46 : Fin 117) else
  if code = 1949227 then (86 : Fin 117) else
  if code = 1949443 then (107 : Fin 117) else
  if code = 1949659 then (55 : Fin 117) else
  if code = 1950523 then (90 : Fin 117) else
  if code = 1950739 then (110 : Fin 117) else
  if code = 1950955 then (59 : Fin 117) else
  if code = 1957003 then (112 : Fin 117) else
  if code = 1957219 then (95 : Fin 117) else
  if code = 2050927 then (33 : Fin 117) else
  if code = 2052223 then (45 : Fin 117) else
  if code = 2183767 then (103 : Fin 117) else
  if code = 2183983 then (78 : Fin 117) else
  if code = 2190247 then (94 : Fin 117) else
  (0 : Fin 117)

private def decodeStateCodeChunk2 (code : Nat) : Fin 117 :=
  if code = 2190463 then (64 : Fin 117) else
  if code = 2191543 then (101 : Fin 117) else
  if code = 2191759 then (76 : Fin 117) else
  if code = 2229127 then (56 : Fin 117) else
  if code = 2229343 then (87 : Fin 117) else
  if code = 2229559 then (27 : Fin 117) else
  if code = 2230423 then (60 : Fin 117) else
  if code = 2230639 then (91 : Fin 117) else
  if code = 2230855 then (29 : Fin 117) else
  if code = 2236903 then (96 : Fin 117) else
  if code = 2237119 then (65 : Fin 117) else
  if code = 2378815 then (6 : Fin 117) else
  if code = 2463703 then (52 : Fin 117) else
  if code = 2463919 then (24 : Fin 117) else
  if code = 2471479 then (47 : Fin 117) else
  if code = 2471695 then (21 : Fin 117) else
  if code = 2698963 then (12 : Fin 117) else
  if code = 2783851 then (28 : Fin 117) else
  if code = 2784067 then (57 : Fin 117) else
  if code = 2784283 then (9 : Fin 117) else
  if code = 2791627 then (66 : Fin 117) else
  if code = 2791843 then (34 : Fin 117) else
  if code = 3403993 then (15 : Fin 117) else
  if code = 3589963 then (71 : Fin 117) else
  if code = 3590179 then (39 : Fin 117) else
  if code = 3636619 then (72 : Fin 117) else
  if code = 3636835 then (41 : Fin 117) else
  if code = 3730549 then (4 : Fin 117) else
  if code = 3869863 then (40 : Fin 117) else
  if code = 3870079 then (16 : Fin 117) else
  if code = 3916519 then (42 : Fin 117) else
  if code = 3916735 then (17 : Fin 117) else
  (0 : Fin 117)

private def decodeStateCodeChunk3 (code : Nat) : Fin 117 :=
  if code = 4378622 then (0 : Fin 117) else
  if code = 4471279 then (18 : Fin 117) else
  if code = 4471495 then (5 : Fin 117) else
  if code = 5069322 then (7 : Fin 117) else
  if code = 5231952 then (50 : Fin 117) else
  if code = 5232168 then (23 : Fin 117) else
  if code = 5278608 then (61 : Fin 117) else
  if code = 5278824 then (92 : Fin 117) else
  if code = 5279040 then (30 : Fin 117) else
  if code = 5395950 then (22 : Fin 117) else
  if code = 5511924 then (79 : Fin 117) else
  if code = 5512140 then (48 : Fin 117) else
  if code = 5558580 then (31 : Fin 117) else
  if code = 5558796 then (62 : Fin 117) else
  if code = 5559012 then (10 : Fin 117) else
  if code = 5722578 then (1 : Fin 117) else
  if code = 5791896 then (25 : Fin 117) else
  if code = 5792112 then (8 : Fin 117) else
  if code = 6115932 then (11 : Fin 117) else
  if code = 6116148 then (32 : Fin 117) else
  if code = 6116364 then (2 : Fin 117) else
  (0 : Fin 117)

private def stateVectorCode
    (vector : Fin 9 -> Fin 6) : Nat :=
  (vector (0 : Fin 9)).val + 6 * ((vector (1 : Fin 9)).val + 6 * ((vector (2 : Fin 9)).val + 6 * ((vector (3 : Fin 9)).val + 6 * ((vector (4 : Fin 9)).val + 6 * ((vector (5 : Fin 9)).val + 6 * ((vector (6 : Fin 9)).val + 6 * ((vector (7 : Fin 9)).val + 6 * ((vector (8 : Fin 9)).val))))))))

private def decodeStateCode (code : Nat) : Fin 117 :=
  if code < 699228 then decodeStateCodeChunk0 code else
  if code < 2190463 then decodeStateCodeChunk1 code else
  if code < 4378622 then decodeStateCodeChunk2 code else
  decodeStateCodeChunk3 code

private def decodeState
    (vector : Fin 9 -> Fin 6) : Fin 117 :=
  decodeStateCode (stateVectorCode vector)

set_option maxHeartbeats 2000000 in
private theorem decodeState_stateVector (state : Fin 117) :
    decodeState (stateVector state) = state := by
  decide +revert

set_option maxHeartbeats 2000000 in
private theorem transitionMap :
    forall (state : Fin 117)
      (generator : Fin 3)
      (coordinate : Fin 9),
      stateVector (transition state generator) coordinate =
        oppositeTable.semigroup.mul (stateVector state coordinate)
          (generatorVector generator coordinate) := by
  intro state generator coordinate
  apply Fin.ext
  exact by decide +revert

set_option maxHeartbeats 2000000 in
private theorem representativeMap :
    forall (state : Fin 117)
      (coordinate : Fin 9),
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
    (I := Fin 9) oppositeTable.semigroup where
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
        (Fin 9) targetValid
    have subValid :=
      powerCertificate.embedding.pullback_identity identity powerValid
    exact quotient.pushforwardIdentity identity subValid

/-- First-layer generic-CAS basis wrapper for `S6_9050`. -/
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

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9050
