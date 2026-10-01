import SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6483Representative
import SemigroupBasis.FiniteNilpotentCounterexample
import SemigroupBasis.Nonfinite
import SemigroupBasis.Opposite
import SemigroupBasis.RightGeneratedPowerCertificate

set_option maxRecDepth 2048

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11778

open SemigroupBasis

def routeManifestRowSHA256 : String := "0aecba166cd57d765a88dd37f8db455073d233b84fb3fbbafd6cab26d71a60e2"
def witnessRecordSHA256 : String := "14845380f409715530db0ae48299f23d7f2ba39dbe829be3b7f3174583b49b69"
def transferComponentSHA256 : String := "14845380f409715530db0ae48299f23d7f2ba39dbe829be3b7f3174583b49b69"
def powerCertificateSHA256 : String := "1f696d467d799b0a2260de3e59d231baaefc014bf9de7add0b70550074bd7225"

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
      if left = 2 then row6 2 2 2 3 2 2 right else
        if left = 3 then row6 3 3 3 2 3 3 right else
          if left = 4 then row6 0 0 2 3 4 4 right else
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
  "0c85114d5d7b6705931652a1cf44cc5d84b383d6535b9d6d89aaf0c4f35515a6"

private def packedStateVectorCodeChunk0 (index : Nat) : Nat :=
  match index with
  | 0 => 156302742313
  | 1 => 460007661174
  | 2 => 417650134212
  | 3 => 77938289208
  | 4 => 145408767408
  | 5 => 90948834720
  | 6 => 67763291040
  | 7 => 457468074000
  | 8 => 394401993696
  | 9 => 25406851392
  | 10 => 404942143968
  | 11 => 404518849632
  | 12 => 77938569144
  | 13 => 67044322080
  | 14 => 12584382912
  | 15 => 145408759632
  | 16 => 80105249376
  | 17 => 80064938592
  | 18 => 90948788064
  | 19 => 67763011104
  | 20 => 65586500928
  | 21 => 2459960928
  | 22 => 457468081776
  | 23 => 391862406528
  | 24 => 2218096224
  | 25 => 394401947040
  | 26 => 25406571456
  | 27 => 14512885344
  | 28 => 12336033024
  | 29 => 13061697120
  | 30 => 404942136192
  | _ => 391820937120

private def packedStateVectorCodeChunk1 (index : Nat) : Nat :=
  match index with
  | 0 => 404518896288
  | 1 => 67044602016
  | 2 => 12584662848
  | 3 => 67044314304
  | 4 => 1740805344
  | 5 => 1700494560
  | 6 => 12584336256
  | 7 => 80105241600
  | 8 => 80105202720
  | 9 => 80064930816
  | 10 => 80064891936
  | 11 => 65586220992
  | 12 => 2459680992
  | 13 => 65586508704
  | 14 => 283170816
  | 15 => 2459914272
  | 16 => 391862414304
  | 17 => 41306112
  | 18 => 391862359872
  | 19 => 2217816288
  | 20 => 2218049568
  | 21 => 14512605408
  | 22 => 12335753088
  | 23 => 14512877568
  | 24 => 1452144672
  | 25 => 12336079680
  | 26 => 13061417184
  | 27 => 13061689344
  | 28 => 956448
  | 29 => 391820929344
  | 30 => 391820983776
  | _ => 67044594240

private def packedStateVectorCodeChunk2 (index : Nat) : Nat :=
  match index with
  | 0 => 1741085280
  | 1 => 1700774496
  | 2 => 12584616192
  | 3 => 1740797568
  | 4 => 1740758688
  | 5 => 1700486784
  | 6 => 1700447904
  | 7 => 80105194944
  | 8 => 80064884160
  | 9 => 65586228768
  | 10 => 282890880
  | 11 => 2459634336
  | 12 => 283178592
  | 13 => 283124160
  | 14 => 41313888
  | 15 => 391862367648
  | 16 => 41026176
  | 17 => 41259456
  | 18 => 2217769632
  | 19 => 14512597632
  | 20 => 1451864736
  | 21 => 12335799744
  | 22 => 1452136896
  | 23 => 1452191328
  | 24 => 13061409408
  | 25 => 676512
  | 26 => 948672
  | 27 => 1003104
  | 28 => 391820976000
  | 29 => 1741077504
  | 30 => 1741038624
  | _ => 1700766720

private def packedStateVectorCodeChunk3 (index : Nat) : Nat :=
  match index with
  | 0 => 1700727840
  | 1 => 1740750912
  | 2 => 1700440128
  | 3 => 282898656
  | 4 => 282844224
  | 5 => 283131936
  | 6 => 41033952
  | 7 => 41267232
  | 8 => 40979520
  | 9 => 1451856960
  | 10 => 1451911392
  | 11 => 1452183552
  | 12 => 668736
  | 13 => 723168
  | 14 => 995328
  | 15 => 1741030848
  | 16 => 1700720064
  | 17 => 282852000
  | 18 => 40987296
  | 19 => 1451903616
  | _ => 715392

private def packedStateVectorCode (state : Fin 117) : Nat :=
  if state.val < 32 then packedStateVectorCodeChunk0 state.val else
    if state.val < 64 then packedStateVectorCodeChunk1 (state.val - 32) else
      if state.val < 96 then packedStateVectorCodeChunk2 (state.val - 64) else
        packedStateVectorCodeChunk3 (state.val - 96)

def stateVector (state : Fin 117)
    (coordinate : Fin 15) : Fin 6 :=
  ⟨(packedStateVectorCode state / 6 ^ coordinate.val) % 6,
    Nat.mod_lt _ (by decide)⟩

def generatorVector (generator : Fin 3)
    (coordinate : Fin 15) : Fin 6 :=
  match generator.val with
  | 0 =>
      match coordinate.val with
      | 0 => (1 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (5 : Fin 6)
      | 4 => (1 : Fin 6)
      | 5 => (1 : Fin 6)
      | 6 => (4 : Fin 6)
      | 7 => (3 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (5 : Fin 6)
      | 10 => (4 : Fin 6)
      | 11 => (4 : Fin 6)
      | 12 => (5 : Fin 6)
      | 13 => (5 : Fin 6)
      | _ => (1 : Fin 6)
  | 1 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (1 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (5 : Fin 6)
      | 5 => (3 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (0 : Fin 6)
      | 9 => (4 : Fin 6)
      | 10 => (5 : Fin 6)
      | 11 => (1 : Fin 6)
      | 12 => (1 : Fin 6)
      | 13 => (5 : Fin 6)
      | _ => (5 : Fin 6)
  | _ =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (1 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (5 : Fin 6)
      | 6 => (3 : Fin 6)
      | 7 => (0 : Fin 6)
      | 8 => (0 : Fin 6)
      | 9 => (1 : Fin 6)
      | 10 => (1 : Fin 6)
      | 11 => (5 : Fin 6)
      | 12 => (5 : Fin 6)
      | 13 => (1 : Fin 6)
      | _ => (5 : Fin 6)

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
  if code = 668736 then (108 : Fin 117) else
  if code = 676512 then (89 : Fin 117) else
  if code = 715392 then (116 : Fin 117) else
  if code = 723168 then (109 : Fin 117) else
  if code = 948672 then (90 : Fin 117) else
  if code = 956448 then (60 : Fin 117) else
  if code = 995328 then (110 : Fin 117) else
  if code = 1003104 then (91 : Fin 117) else
  if code = 40979520 then (104 : Fin 117) else
  if code = 40987296 then (114 : Fin 117) else
  if code = 41026176 then (80 : Fin 117) else
  if code = 41033952 then (102 : Fin 117) else
  if code = 41259456 then (81 : Fin 117) else
  if code = 41267232 then (103 : Fin 117) else
  if code = 41306112 then (49 : Fin 117) else
  if code = 41313888 then (78 : Fin 117) else
  if code = 282844224 then (100 : Fin 117) else
  if code = 282852000 then (113 : Fin 117) else
  if code = 282890880 then (74 : Fin 117) else
  if code = 282898656 then (99 : Fin 117) else
  if code = 283124160 then (77 : Fin 117) else
  if code = 283131936 then (101 : Fin 117) else
  if code = 283170816 then (46 : Fin 117) else
  if code = 283178592 then (76 : Fin 117) else
  if code = 1451856960 then (105 : Fin 117) else
  if code = 1451864736 then (84 : Fin 117) else
  if code = 1451903616 then (115 : Fin 117) else
  if code = 1451911392 then (106 : Fin 117) else
  if code = 1452136896 then (86 : Fin 117) else
  if code = 1452144672 then (56 : Fin 117) else
  if code = 1452183552 then (107 : Fin 117) else
  if code = 1452191328 then (87 : Fin 117) else
  (0 : Fin 117)

private def decodeStateCodeChunk1 (code : Nat) : Fin 117 :=
  if code = 1700440128 then (98 : Fin 117) else
  if code = 1700447904 then (70 : Fin 117) else
  if code = 1700486784 then (69 : Fin 117) else
  if code = 1700494560 then (37 : Fin 117) else
  if code = 1700720064 then (112 : Fin 117) else
  if code = 1700727840 then (96 : Fin 117) else
  if code = 1700766720 then (95 : Fin 117) else
  if code = 1700774496 then (65 : Fin 117) else
  if code = 1740750912 then (97 : Fin 117) else
  if code = 1740758688 then (68 : Fin 117) else
  if code = 1740797568 then (67 : Fin 117) else
  if code = 1740805344 then (36 : Fin 117) else
  if code = 1741030848 then (111 : Fin 117) else
  if code = 1741038624 then (94 : Fin 117) else
  if code = 1741077504 then (93 : Fin 117) else
  if code = 1741085280 then (64 : Fin 117) else
  if code = 2217769632 then (82 : Fin 117) else
  if code = 2217816288 then (51 : Fin 117) else
  if code = 2218049568 then (52 : Fin 117) else
  if code = 2218096224 then (24 : Fin 117) else
  if code = 2459634336 then (75 : Fin 117) else
  if code = 2459680992 then (44 : Fin 117) else
  if code = 2459914272 then (47 : Fin 117) else
  if code = 2459960928 then (21 : Fin 117) else
  if code = 12335753088 then (54 : Fin 117) else
  if code = 12335799744 then (85 : Fin 117) else
  if code = 12336033024 then (28 : Fin 117) else
  if code = 12336079680 then (57 : Fin 117) else
  if code = 12584336256 then (38 : Fin 117) else
  if code = 12584382912 then (14 : Fin 117) else
  if code = 12584616192 then (66 : Fin 117) else
  if code = 12584662848 then (34 : Fin 117) else
  (0 : Fin 117)

private def decodeStateCodeChunk2 (code : Nat) : Fin 117 :=
  if code = 13061409408 then (88 : Fin 117) else
  if code = 13061417184 then (58 : Fin 117) else
  if code = 13061689344 then (59 : Fin 117) else
  if code = 13061697120 then (29 : Fin 117) else
  if code = 14512597632 then (83 : Fin 117) else
  if code = 14512605408 then (53 : Fin 117) else
  if code = 14512877568 then (55 : Fin 117) else
  if code = 14512885344 then (27 : Fin 117) else
  if code = 25406571456 then (26 : Fin 117) else
  if code = 25406851392 then (9 : Fin 117) else
  if code = 65586220992 then (43 : Fin 117) else
  if code = 65586228768 then (73 : Fin 117) else
  if code = 65586500928 then (20 : Fin 117) else
  if code = 65586508704 then (45 : Fin 117) else
  if code = 67044314304 then (35 : Fin 117) else
  if code = 67044322080 then (13 : Fin 117) else
  if code = 67044594240 then (63 : Fin 117) else
  if code = 67044602016 then (33 : Fin 117) else
  if code = 67763011104 then (19 : Fin 117) else
  if code = 67763291040 then (6 : Fin 117) else
  if code = 77938289208 then (3 : Fin 117) else
  if code = 77938569144 then (12 : Fin 117) else
  if code = 80064884160 then (72 : Fin 117) else
  if code = 80064891936 then (42 : Fin 117) else
  if code = 80064930816 then (41 : Fin 117) else
  if code = 80064938592 then (17 : Fin 117) else
  if code = 80105194944 then (71 : Fin 117) else
  if code = 80105202720 then (40 : Fin 117) else
  if code = 80105241600 then (39 : Fin 117) else
  if code = 80105249376 then (16 : Fin 117) else
  if code = 90948788064 then (18 : Fin 117) else
  if code = 90948834720 then (5 : Fin 117) else
  (0 : Fin 117)

private def decodeStateCodeChunk3 (code : Nat) : Fin 117 :=
  if code = 145408759632 then (15 : Fin 117) else
  if code = 145408767408 then (4 : Fin 117) else
  if code = 156302742313 then (0 : Fin 117) else
  if code = 391820929344 then (61 : Fin 117) else
  if code = 391820937120 then (31 : Fin 117) else
  if code = 391820976000 then (92 : Fin 117) else
  if code = 391820983776 then (62 : Fin 117) else
  if code = 391862359872 then (50 : Fin 117) else
  if code = 391862367648 then (79 : Fin 117) else
  if code = 391862406528 then (23 : Fin 117) else
  if code = 391862414304 then (48 : Fin 117) else
  if code = 394401947040 then (25 : Fin 117) else
  if code = 394401993696 then (8 : Fin 117) else
  if code = 404518849632 then (11 : Fin 117) else
  if code = 404518896288 then (32 : Fin 117) else
  if code = 404942136192 then (30 : Fin 117) else
  if code = 404942143968 then (10 : Fin 117) else
  if code = 417650134212 then (2 : Fin 117) else
  if code = 457468074000 then (7 : Fin 117) else
  if code = 457468081776 then (22 : Fin 117) else
  if code = 460007661174 then (1 : Fin 117) else
  (0 : Fin 117)

private def stateVectorCode
    (vector : Fin 15 -> Fin 6) : Nat :=
  (vector (0 : Fin 15)).val + 6 * ((vector (1 : Fin 15)).val + 6 * ((vector (2 : Fin 15)).val + 6 * ((vector (3 : Fin 15)).val + 6 * ((vector (4 : Fin 15)).val + 6 * ((vector (5 : Fin 15)).val + 6 * ((vector (6 : Fin 15)).val + 6 * ((vector (7 : Fin 15)).val + 6 * ((vector (8 : Fin 15)).val + 6 * ((vector (9 : Fin 15)).val + 6 * ((vector (10 : Fin 15)).val + 6 * ((vector (11 : Fin 15)).val + 6 * ((vector (12 : Fin 15)).val + 6 * ((vector (13 : Fin 15)).val + 6 * ((vector (14 : Fin 15)).val))))))))))))))

private def decodeStateCode (code : Nat) : Fin 117 :=
  if code < 1700440128 then decodeStateCodeChunk0 code else
  if code < 13061409408 then decodeStateCodeChunk1 code else
  if code < 145408759632 then decodeStateCodeChunk2 code else
  decodeStateCodeChunk3 code

private def decodeState
    (vector : Fin 15 -> Fin 6) : Fin 117 :=
  decodeStateCode (stateVectorCode vector)

set_option maxHeartbeats 2000000 in
private theorem decodeState_stateVector (state : Fin 117) :
    decodeState (stateVector state) = state := by
  decide +revert

set_option maxHeartbeats 2000000 in
private theorem transitionMap :
    forall (state : Fin 117)
      (generator : Fin 3)
      (coordinate : Fin 15),
      stateVector (transition state generator) coordinate =
        oppositeTable.semigroup.mul (stateVector state coordinate)
          (generatorVector generator coordinate) := by
  intro state generator coordinate
  apply Fin.ext
  exact by decide +revert

set_option maxHeartbeats 2000000 in
private theorem representativeMap :
    forall (state : Fin 117)
      (coordinate : Fin 15),
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
    (I := Fin 15) oppositeTable.semigroup where
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
        (Fin 15) targetValid
    have subValid :=
      powerCertificate.embedding.pullback_identity identity powerValid
    exact quotient.pushforwardIdentity identity subValid

/-- First-layer generic-CAS basis wrapper for `S6_11778`. -/
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

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11778
