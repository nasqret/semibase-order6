import SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_5983Representative
import SemigroupBasis.FiniteNilpotentCounterexample
import SemigroupBasis.Nonfinite
import SemigroupBasis.Opposite
import SemigroupBasis.RightGeneratedPowerCertificate

set_option maxRecDepth 2048

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11769

open SemigroupBasis

def routeManifestRowSHA256 : String := "332edd53e330a669fda276648483a6821633f48fc7e76f0370f48aeed2cd9981"
def witnessRecordSHA256 : String := "4823642f648636031224e5a9fb0ad580a0be1c561f362031f7d4fde78f082d07"
def transferComponentSHA256 : String := "4823642f648636031224e5a9fb0ad580a0be1c561f362031f7d4fde78f082d07"
def powerCertificateSHA256 : String := "8a94e3dddb7fb7caeacc5aaff3ce36fd4222e3fb3d5e0b4ce79d3fe05a1a2cb1"

private def row6
    (c0 c1 c2 c3 c4 c5 : Fin 6) (column : Fin 6) : Fin 6 :=
  if column = 0 then c0 else
    if column = 1 then c1 else
      if column = 2 then c2 else
        if column = 3 then c3 else
          if column = 4 then c4 else c5

/-- Exact one-based catalogue table committed by the portable witness. -/
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 2 3 0 5 right else
    if left = 1 then row6 0 0 2 3 1 5 right else
      if left = 2 then row6 2 2 2 3 2 2 right else
        if left = 3 then row6 3 3 3 2 3 3 right else
          if left = 4 then row6 0 0 2 3 4 5 right else
            row6 0 0 2 3 5 5 right

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
  "8a7438bc1226c8c684fb8120f677ad2b929f60e8df89d7d2b2a5b68db6c8a604"

private def packedStateVectorCodeChunk0 (index : Nat) : Nat :=
  match index with
  | 0 => 5169487776481
  | 1 => 12091669425942
  | 2 => 13219636365828
  | 3 => 2348375862816
  | 4 => 938188989072
  | 5 => 2340374422752
  | 6 => 3223457767872
  | 7 => 11608422066432
  | 8 => 11288465949312
  | 9 => 4767186068352
  | 10 => 11767720580352
  | 11 => 13217449218048
  | 12 => 2348376142752
  | 13 => 938188709136
  | 14 => 2340374142816
  | 15 => 468003723264
  | 16 => 468002323584
  | 17 => 461453500800
  | 18 => 2338197352704
  | 19 => 927647717760
  | 20 => 2338187554944
  | 21 => 402347533824
  | 22 => 402346134144
  | 23 => 395847699840
  | 24 => 3223456088256
  | 25 => 11608423746048
  | 26 => 11288464269696
  | 27 => 2822960004480
  | 28 => 11286287207424
  | 29 => 11286278809344
  | 30 => 1946074201344
  | _ => 535524566400

private def packedStateVectorCodeChunk1 (index : Nat) : Nat :=
  match index with
  | 0 => 1946064403584
  | 1 => 2821146019200
  | 2 => 11284473222144
  | 3 => 11284464824064
  | 4 => 4767175990656
  | 5 => 11767710502656
  | 6 => 13217459295744
  | 7 => 468004003200
  | 8 => 468002043648
  | 9 => 461453220864
  | 10 => 2338197632640
  | 11 => 927647437824
  | 12 => 2338187275008
  | 13 => 461451821184
  | 14 => 459276438528
  | 15 => 459275038848
  | 16 => 459266640768
  | 17 => 457462453248
  | 18 => 457461053568
  | 19 => 457452655488
  | 20 => 927637640064
  | 21 => 402347813760
  | 22 => 402345854208
  | 23 => 395847419904
  | 24 => 395846020224
  | 25 => 393670637568
  | 26 => 393669237888
  | 27 => 393660839808
  | 28 => 2822958324864
  | 29 => 11286288887040
  | 30 => 11286277129728
  | _ => 1849817088

private def packedStateVectorCodeChunk2 (index : Nat) : Nat :=
  match index with
  | 0 => 1848417408
  | 1 => 1840019328
  | 2 => 2822949926784
  | 3 => 1946074481280
  | 4 => 535524286464
  | 5 => 1946064123648
  | 6 => 65339301888
  | 7 => 65337902208
  | 8 => 65329504128
  | 9 => 535514488704
  | 10 => 35831808
  | 11 => 34432128
  | 12 => 26034048
  | 13 => 2821144339584
  | 14 => 11284474901760
  | 15 => 11284463144448
  | 16 => 2821135941504
  | 17 => 461451541248
  | 18 => 459276718464
  | 19 => 459274758912
  | 20 => 459266360832
  | 21 => 457462733184
  | 22 => 457460773632
  | 23 => 457452375552
  | 24 => 927637360128
  | 25 => 459264961152
  | 26 => 457450975872
  | 27 => 395845740288
  | 28 => 393670917504
  | 29 => 393668957952
  | 30 => 393660559872
  | _ => 393659160192

private def packedStateVectorCodeChunk3 (index : Nat) : Nat :=
  match index with
  | 0 => 1848137472
  | 1 => 1850097024
  | 2 => 1838339712
  | 3 => 2822948247168
  | 4 => 1839739392
  | 5 => 65339581824
  | 6 => 65337622272
  | 7 => 65329224192
  | 8 => 535514208768
  | 9 => 65327824512
  | 10 => 36111744
  | 11 => 34152192
  | 12 => 25754112
  | 13 => 24354432
  | 14 => 2821134261888
  | 15 => 459264681216
  | 16 => 457450695936
  | 17 => 393658880256
  | 18 => 1838059776
  | 19 => 65327544576
  | _ => 24074496

private def packedStateVectorCode (state : Fin 117) : Nat :=
  if state.val < 32 then packedStateVectorCodeChunk0 state.val else
    if state.val < 64 then packedStateVectorCodeChunk1 (state.val - 32) else
      if state.val < 96 then packedStateVectorCodeChunk2 (state.val - 64) else
        packedStateVectorCodeChunk3 (state.val - 96)

def stateVector (state : Fin 117)
    (coordinate : Fin 17) : Fin 6 :=
  ⟨(packedStateVectorCode state / 6 ^ coordinate.val) % 6,
    Nat.mod_lt _ (by decide)⟩

def generatorVector (generator : Fin 3)
    (coordinate : Fin 17) : Fin 6 :=
  match generator.val with
  | 0 =>
      match coordinate.val with
      | 0 => (1 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (4 : Fin 6)
      | 4 => (4 : Fin 6)
      | 5 => (4 : Fin 6)
      | 6 => (1 : Fin 6)
      | 7 => (3 : Fin 6)
      | 8 => (1 : Fin 6)
      | 9 => (5 : Fin 6)
      | 10 => (5 : Fin 6)
      | 11 => (4 : Fin 6)
      | 12 => (4 : Fin 6)
      | 13 => (5 : Fin 6)
      | 14 => (5 : Fin 6)
      | 15 => (4 : Fin 6)
      | _ => (1 : Fin 6)
  | 1 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (1 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (1 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (4 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (3 : Fin 6)
      | 9 => (0 : Fin 6)
      | 10 => (0 : Fin 6)
      | 11 => (5 : Fin 6)
      | 12 => (4 : Fin 6)
      | 13 => (1 : Fin 6)
      | 14 => (4 : Fin 6)
      | 15 => (1 : Fin 6)
      | _ => (4 : Fin 6)
  | _ =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (1 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (1 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (1 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (3 : Fin 6)
      | 10 => (0 : Fin 6)
      | 11 => (0 : Fin 6)
      | 12 => (1 : Fin 6)
      | 13 => (4 : Fin 6)
      | 14 => (0 : Fin 6)
      | 15 => (4 : Fin 6)
      | _ => (4 : Fin 6)

private def packedTransitionCodeChunk0 (index : Nat) : Nat :=
  match index with
  | 0 => 68916
  | 1 => 110337
  | 2 => 151758
  | 3 => 193179
  | 4 => 234600
  | 5 => 276021
  | 6 => 317442
  | 7 => 358863
  | 8 => 400284
  | 9 => 441705
  | 10 => 483126
  | 11 => 524547
  | 12 => 68916
  | 13 => 565968
  | 14 => 607389
  | 15 => 565968
  | 16 => 620608
  | 17 => 662617
  | 18 => 607389
  | 19 => 704038
  | 20 => 581066
  | 21 => 759266
  | 22 => 772839
  | 23 => 814494
  | 24 => 772839
  | 25 => 110337
  | 26 => 855915
  | 27 => 897336
  | 28 => 855915
  | 29 => 842349
  | 30 => 952564
  | _ => 993985

private def packedTransitionCodeChunk1 (index : Nat) : Nat :=
  match index with
  | 0 => 925773
  | 1 => 1049213
  | 2 => 1090634
  | 3 => 1077065
  | 4 => 925773
  | 5 => 1077065
  | 6 => 151758
  | 7 => 234600
  | 8 => 1110580
  | 9 => 1159669
  | 10 => 276021
  | 11 => 1201090
  | 12 => 256718
  | 13 => 1227998
  | 14 => 1159669
  | 15 => 1227998
  | 16 => 1132995
  | 17 => 1201090
  | 18 => 1242041
  | 19 => 1174182
  | 20 => 1174182
  | 21 => 317442
  | 22 => 1248178
  | 23 => 1297739
  | 24 => 1311312
  | 25 => 1297739
  | 26 => 1311312
  | 27 => 1270597
  | 28 => 1352967
  | 29 => 400284
  | 30 => 386784
  | _ => 1380229

private def packedTransitionCodeChunk2 (index : Nat) : Nat :=
  match index with
  | 0 => 1352967
  | 1 => 1339399
  | 2 => 1339399
  | 3 => 441705
  | 4 => 1422002
  | 5 => 422870
  | 6 => 1422002
  | 7 => 1449264
  | 8 => 1394977
  | 9 => 1394977
  | 10 => 1491037
  | 11 => 1504610
  | 12 => 1463895
  | 13 => 1504610
  | 14 => 483126
  | 15 => 469631
  | 16 => 1463895
  | 17 => 1524908
  | 18 => 662617
  | 19 => 1524908
  | 20 => 642729
  | 21 => 704038
  | 22 => 1538951
  | 23 => 683916
  | 24 => 683916
  | 25 => 649110
  | 26 => 690529
  | 27 => 1553584
  | 28 => 814494
  | 29 => 1553584
  | 30 => 793553
  | _ => 800978

private def packedTransitionCodeChunk3 (index : Nat) : Nat :=
  match index with
  | 0 => 1567981
  | 1 => 897336
  | 2 => 883815
  | 3 => 883815
  | 4 => 875810
  | 5 => 993985
  | 6 => 1582496
  | 7 => 971757
  | 8 => 971757
  | 9 => 980458
  | 10 => 1049213
  | 11 => 1596657
  | 12 => 1026634
  | 13 => 1035683
  | 14 => 1035683
  | 15 => 1146104
  | 16 => 1187523
  | 17 => 1284170
  | 18 => 1325942
  | 19 => 1408434
  | _ => 1477468

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
  | 0 => 1716832218527474854521199419876
  | _ => 18213337610740124137033069

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
  | 15 => [1, 0]
  | 16 => [1, 1]
  | 17 => [1, 2]
  | 18 => [2, 0]
  | 19 => [2, 1]
  | 20 => [2, 2]
  | 21 => [0, 0]
  | 22 => [0, 1]
  | 23 => [0, 2]
  | 24 => [1, 0]
  | 25 => [1, 1]
  | 26 => [1, 2]
  | 27 => [2, 0]
  | 28 => [2, 1]
  | 29 => [2, 2]
  | 30 => [0, 0]
  | _ => [0, 1]

private def representativeTailChunk1 (index : Nat) :
    List (Fin 3) :=
  match index with
  | 0 => [0, 2]
  | 1 => [1, 0]
  | 2 => [1, 1]
  | 3 => [1, 2]
  | 4 => [2, 0]
  | 5 => [2, 1]
  | 6 => [2, 2]
  | 7 => [0, 1, 0]
  | 8 => [0, 1, 1]
  | 9 => [0, 1, 2]
  | 10 => [0, 2, 0]
  | 11 => [0, 2, 1]
  | 12 => [0, 2, 2]
  | 13 => [1, 1, 2]
  | 14 => [1, 2, 0]
  | 15 => [1, 2, 1]
  | 16 => [1, 2, 2]
  | 17 => [2, 1, 0]
  | 18 => [2, 1, 1]
  | 19 => [2, 1, 2]
  | 20 => [2, 2, 1]
  | 21 => [0, 0, 0]
  | 22 => [0, 0, 1]
  | 23 => [0, 0, 2]
  | 24 => [0, 1, 2]
  | 25 => [0, 2, 0]
  | 26 => [0, 2, 1]
  | 27 => [0, 2, 2]
  | 28 => [1, 2, 0]
  | 29 => [1, 2, 1]
  | 30 => [1, 2, 2]
  | _ => [2, 0, 0]

private def representativeTailChunk2 (index : Nat) :
    List (Fin 3) :=
  match index with
  | 0 => [2, 0, 1]
  | 1 => [2, 0, 2]
  | 2 => [2, 2, 0]
  | 3 => [0, 0, 0]
  | 4 => [0, 0, 1]
  | 5 => [0, 0, 2]
  | 6 => [0, 1, 0]
  | 7 => [0, 1, 1]
  | 8 => [0, 1, 2]
  | 9 => [0, 2, 1]
  | 10 => [1, 0, 0]
  | 11 => [1, 0, 1]
  | 12 => [1, 0, 2]
  | 13 => [1, 1, 0]
  | 14 => [1, 1, 1]
  | 15 => [1, 1, 2]
  | 16 => [1, 2, 0]
  | 17 => [0, 1, 1, 2]
  | 18 => [0, 1, 2, 0]
  | 19 => [0, 1, 2, 1]
  | 20 => [0, 1, 2, 2]
  | 21 => [0, 2, 1, 0]
  | 22 => [0, 2, 1, 1]
  | 23 => [0, 2, 1, 2]
  | 24 => [0, 2, 2, 1]
  | 25 => [1, 1, 2, 2]
  | 26 => [2, 1, 1, 2]
  | 27 => [0, 0, 1, 2]
  | 28 => [0, 0, 2, 0]
  | 29 => [0, 0, 2, 1]
  | 30 => [0, 0, 2, 2]
  | _ => [0, 1, 2, 2]

private def representativeTailChunk3 (index : Nat) :
    List (Fin 3) :=
  match index with
  | 0 => [1, 2, 0, 0]
  | 1 => [1, 2, 0, 1]
  | 2 => [1, 2, 0, 2]
  | 3 => [1, 2, 2, 0]
  | 4 => [2, 0, 0, 2]
  | 5 => [0, 0, 1, 0]
  | 6 => [0, 0, 1, 1]
  | 7 => [0, 0, 1, 2]
  | 8 => [0, 0, 2, 1]
  | 9 => [0, 1, 1, 2]
  | 10 => [1, 0, 0, 0]
  | 11 => [1, 0, 0, 1]
  | 12 => [1, 0, 0, 2]
  | 13 => [1, 0, 1, 2]
  | 14 => [1, 1, 2, 0]
  | 15 => [0, 1, 1, 2, 2]
  | 16 => [0, 2, 1, 1, 2]
  | 17 => [0, 0, 1, 2, 2]
  | 18 => [1, 2, 0, 0, 2]
  | 19 => [0, 0, 1, 1, 2]
  | _ => [1, 0, 0, 1, 2]

def representativeTail (state : Fin 117) :
    List (Fin 3) :=
  if state.val < 32 then representativeTailChunk0 state.val else
    if state.val < 64 then representativeTailChunk1 (state.val - 32) else
      if state.val < 96 then representativeTailChunk2 (state.val - 64) else
        representativeTailChunk3 (state.val - 96)

private def packedSourceLabelBlockCode (index : Nat) : Nat :=
  match index with
  | 0 => 48873677980689255261406996112552094219572586125
  | _ => 804539234513546259764234994743462461440

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
  | 0 => (9 : Fin 117)
  | 1 => (8 : Fin 117)
  | 2 => (2 : Fin 117)
  | 3 => (7 : Fin 117)
  | 4 => (1 : Fin 117)
  | _ => (0 : Fin 117)

private def decodeStateCodeChunk0 (code : Nat) : Fin 117 :=
  if code = 24074496 then (116 : Fin 117) else
  if code = 24354432 then (109 : Fin 117) else
  if code = 25754112 then (108 : Fin 117) else
  if code = 26034048 then (76 : Fin 117) else
  if code = 34152192 then (107 : Fin 117) else
  if code = 34432128 then (75 : Fin 117) else
  if code = 35831808 then (74 : Fin 117) else
  if code = 36111744 then (106 : Fin 117) else
  if code = 1838059776 then (114 : Fin 117) else
  if code = 1838339712 then (98 : Fin 117) else
  if code = 1839739392 then (100 : Fin 117) else
  if code = 1840019328 then (65 : Fin 117) else
  if code = 1848137472 then (96 : Fin 117) else
  if code = 1848417408 then (64 : Fin 117) else
  if code = 1849817088 then (63 : Fin 117) else
  if code = 1850097024 then (97 : Fin 117) else
  if code = 65327544576 then (115 : Fin 117) else
  if code = 65327824512 then (105 : Fin 117) else
  if code = 65329224192 then (103 : Fin 117) else
  if code = 65329504128 then (72 : Fin 117) else
  if code = 65337622272 then (102 : Fin 117) else
  if code = 65337902208 then (71 : Fin 117) else
  if code = 65339301888 then (70 : Fin 117) else
  if code = 65339581824 then (101 : Fin 117) else
  if code = 393658880256 then (113 : Fin 117) else
  if code = 393659160192 then (95 : Fin 117) else
  if code = 393660559872 then (94 : Fin 117) else
  if code = 393660839808 then (59 : Fin 117) else
  if code = 393668957952 then (93 : Fin 117) else
  if code = 393669237888 then (58 : Fin 117) else
  if code = 393670637568 then (57 : Fin 117) else
  if code = 393670917504 then (92 : Fin 117) else
  (0 : Fin 117)

private def decodeStateCodeChunk1 (code : Nat) : Fin 117 :=
  if code = 395845740288 then (91 : Fin 117) else
  if code = 395846020224 then (56 : Fin 117) else
  if code = 395847419904 then (55 : Fin 117) else
  if code = 395847699840 then (23 : Fin 117) else
  if code = 402345854208 then (54 : Fin 117) else
  if code = 402346134144 then (22 : Fin 117) else
  if code = 402347533824 then (21 : Fin 117) else
  if code = 402347813760 then (53 : Fin 117) else
  if code = 457450695936 then (112 : Fin 117) else
  if code = 457450975872 then (90 : Fin 117) else
  if code = 457452375552 then (87 : Fin 117) else
  if code = 457452655488 then (51 : Fin 117) else
  if code = 457460773632 then (86 : Fin 117) else
  if code = 457461053568 then (50 : Fin 117) else
  if code = 457462453248 then (49 : Fin 117) else
  if code = 457462733184 then (85 : Fin 117) else
  if code = 459264681216 then (111 : Fin 117) else
  if code = 459264961152 then (89 : Fin 117) else
  if code = 459266360832 then (84 : Fin 117) else
  if code = 459266640768 then (48 : Fin 117) else
  if code = 459274758912 then (83 : Fin 117) else
  if code = 459275038848 then (47 : Fin 117) else
  if code = 459276438528 then (46 : Fin 117) else
  if code = 459276718464 then (82 : Fin 117) else
  if code = 461451541248 then (81 : Fin 117) else
  if code = 461451821184 then (45 : Fin 117) else
  if code = 461453220864 then (41 : Fin 117) else
  if code = 461453500800 then (17 : Fin 117) else
  if code = 468002043648 then (40 : Fin 117) else
  if code = 468002323584 then (16 : Fin 117) else
  if code = 468003723264 then (15 : Fin 117) else
  if code = 468004003200 then (39 : Fin 117) else
  (0 : Fin 117)

private def decodeStateCodeChunk2 (code : Nat) : Fin 117 :=
  if code = 535514208768 then (104 : Fin 117) else
  if code = 535514488704 then (73 : Fin 117) else
  if code = 535524286464 then (68 : Fin 117) else
  if code = 535524566400 then (31 : Fin 117) else
  if code = 927637360128 then (88 : Fin 117) else
  if code = 927637640064 then (52 : Fin 117) else
  if code = 927647437824 then (43 : Fin 117) else
  if code = 927647717760 then (19 : Fin 117) else
  if code = 938188709136 then (13 : Fin 117) else
  if code = 938188989072 then (4 : Fin 117) else
  if code = 1946064123648 then (69 : Fin 117) else
  if code = 1946064403584 then (32 : Fin 117) else
  if code = 1946074201344 then (30 : Fin 117) else
  if code = 1946074481280 then (67 : Fin 117) else
  if code = 2338187275008 then (44 : Fin 117) else
  if code = 2338187554944 then (20 : Fin 117) else
  if code = 2338197352704 then (18 : Fin 117) else
  if code = 2338197632640 then (42 : Fin 117) else
  if code = 2340374142816 then (14 : Fin 117) else
  if code = 2340374422752 then (5 : Fin 117) else
  if code = 2348375862816 then (3 : Fin 117) else
  if code = 2348376142752 then (12 : Fin 117) else
  if code = 2821134261888 then (110 : Fin 117) else
  if code = 2821135941504 then (80 : Fin 117) else
  if code = 2821144339584 then (77 : Fin 117) else
  if code = 2821146019200 then (33 : Fin 117) else
  if code = 2822948247168 then (99 : Fin 117) else
  if code = 2822949926784 then (66 : Fin 117) else
  if code = 2822958324864 then (60 : Fin 117) else
  if code = 2822960004480 then (27 : Fin 117) else
  if code = 3223456088256 then (24 : Fin 117) else
  if code = 3223457767872 then (6 : Fin 117) else
  (0 : Fin 117)

private def decodeStateCodeChunk3 (code : Nat) : Fin 117 :=
  if code = 4767175990656 then (36 : Fin 117) else
  if code = 4767186068352 then (9 : Fin 117) else
  if code = 5169487776481 then (0 : Fin 117) else
  if code = 11284463144448 then (79 : Fin 117) else
  if code = 11284464824064 then (35 : Fin 117) else
  if code = 11284473222144 then (34 : Fin 117) else
  if code = 11284474901760 then (78 : Fin 117) else
  if code = 11286277129728 then (62 : Fin 117) else
  if code = 11286278809344 then (29 : Fin 117) else
  if code = 11286287207424 then (28 : Fin 117) else
  if code = 11286288887040 then (61 : Fin 117) else
  if code = 11288464269696 then (26 : Fin 117) else
  if code = 11288465949312 then (8 : Fin 117) else
  if code = 11608422066432 then (7 : Fin 117) else
  if code = 11608423746048 then (25 : Fin 117) else
  if code = 11767710502656 then (37 : Fin 117) else
  if code = 11767720580352 then (10 : Fin 117) else
  if code = 12091669425942 then (1 : Fin 117) else
  if code = 13217449218048 then (11 : Fin 117) else
  if code = 13217459295744 then (38 : Fin 117) else
  if code = 13219636365828 then (2 : Fin 117) else
  (0 : Fin 117)

private def stateVectorCode
    (vector : Fin 17 -> Fin 6) : Nat :=
  (vector (0 : Fin 17)).val + 6 * ((vector (1 : Fin 17)).val + 6 * ((vector (2 : Fin 17)).val + 6 * ((vector (3 : Fin 17)).val + 6 * ((vector (4 : Fin 17)).val + 6 * ((vector (5 : Fin 17)).val + 6 * ((vector (6 : Fin 17)).val + 6 * ((vector (7 : Fin 17)).val + 6 * ((vector (8 : Fin 17)).val + 6 * ((vector (9 : Fin 17)).val + 6 * ((vector (10 : Fin 17)).val + 6 * ((vector (11 : Fin 17)).val + 6 * ((vector (12 : Fin 17)).val + 6 * ((vector (13 : Fin 17)).val + 6 * ((vector (14 : Fin 17)).val + 6 * ((vector (15 : Fin 17)).val + 6 * ((vector (16 : Fin 17)).val))))))))))))))))

private def decodeStateCode (code : Nat) : Fin 117 :=
  if code < 395845740288 then decodeStateCodeChunk0 code else
  if code < 535514208768 then decodeStateCodeChunk1 code else
  if code < 4767175990656 then decodeStateCodeChunk2 code else
  decodeStateCodeChunk3 code

private def decodeState
    (vector : Fin 17 -> Fin 6) : Fin 117 :=
  decodeStateCode (stateVectorCode vector)

set_option maxHeartbeats 2000000 in
private theorem decodeState_stateVector (state : Fin 117) :
    decodeState (stateVector state) = state := by
  decide +revert

set_option maxHeartbeats 2000000 in
private theorem transitionMap :
    forall (state : Fin 117)
      (generator : Fin 3)
      (coordinate : Fin 17),
      stateVector (transition state generator) coordinate =
        oppositeTable.semigroup.mul (stateVector state coordinate)
          (generatorVector generator coordinate) := by
  intro state generator coordinate
  apply Fin.ext
  exact by decide +revert

set_option maxHeartbeats 2000000 in
private theorem representativeMap :
    forall (state : Fin 117)
      (coordinate : Fin 17),
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
    (I := Fin 17) oppositeTable.semigroup where
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
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_5983Representative.sourceSemigroup.mul (sourceLabel state)
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
            SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_5983Representative.sourceSemigroup.mul value
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
          SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_5983Representative.sourceSemigroup.mul value
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
              SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_5983Representative.sourceSemigroup.mul value
                (generatorSourceLabel nextGenerator))
            (SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_5983Representative.sourceSemigroup.mul (sourceLabel state)
              (generatorSourceLabel generator))
      rw [inductionHypothesis]
      rw [sourceLabelTransition]

private theorem sourceFoldlGeneratorAssoc
    (left right : Fin 6)
    (word : List (Fin 3)) :
    word.foldl
        (fun value generator =>
          SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_5983Representative.sourceSemigroup.mul value
            (generatorSourceLabel generator))
        (SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_5983Representative.sourceSemigroup.mul left right) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_5983Representative.sourceSemigroup.mul left
        (word.foldl
          (fun value generator =>
            SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_5983Representative.sourceSemigroup.mul value
              (generatorSourceLabel generator))
          right) := by
  induction word generalizing right with
  | nil => rfl
  | cons generator word inductionHypothesis =>
      simp only [List.foldl_cons]
      rw [SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_5983Representative.sourceSemigroup.assoc]
      exact inductionHypothesis
        (SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_5983Representative.sourceSemigroup.mul right (generatorSourceLabel generator))

private theorem sourceLabelMapMul :
    forall (left right : Fin 117),
      sourceLabel (powerCertificate.semigroup.mul left right) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_5983Representative.sourceSemigroup.mul (sourceLabel left) (sourceLabel right) := by
  intro left right
  calc
    sourceLabel (powerCertificate.semigroup.mul left right) =
        sourceLabel
          (powerCertificate.rightMultiplyWord
            (transition left (representativeHead right))
            (representativeTail right)) := rfl
    _ = (representativeTail right).foldl
          (fun value generator =>
            SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_5983Representative.sourceSemigroup.mul value
              (generatorSourceLabel generator))
          (sourceLabel (transition left (representativeHead right))) :=
      sourceLabelRightMultiplyWord _ _
    _ = (representativeTail right).foldl
          (fun value generator =>
            SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_5983Representative.sourceSemigroup.mul value
              (generatorSourceLabel generator))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_5983Representative.sourceSemigroup.mul (sourceLabel left)
            (generatorSourceLabel (representativeHead right))) :=
      congrArg
        (fun initial =>
          (representativeTail right).foldl
            (fun value generator =>
              SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_5983Representative.sourceSemigroup.mul value
                (generatorSourceLabel generator))
            initial)
        (sourceLabelTransition left (representativeHead right))
    _ = SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_5983Representative.sourceSemigroup.mul (sourceLabel left)
          ((representativeTail right).foldl
            (fun value generator =>
              SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_5983Representative.sourceSemigroup.mul value
                (generatorSourceLabel generator))
            (generatorSourceLabel (representativeHead right))) :=
      sourceFoldlGeneratorAssoc _ _ _
    _ = SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_5983Representative.sourceSemigroup.mul (sourceLabel left) (sourceLabel right) :=
      congrArg (SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_5983Representative.sourceSemigroup.mul (sourceLabel left))
        (sourceLabelRepresentative right).symm

set_option maxHeartbeats 1000000 in
private theorem sourceLabelRightInverse :
    forall value : Fin 6, sourceLabel (sourcePreimage value) = value := by
  intro value
  apply Fin.ext
  exact by decide +revert

/-- The generated term-function semigroup maps onto the selected root. -/
def quotient : SplitSurjection powerCertificate.semigroup
    SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_5983Representative.sourceSemigroup where
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
    SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_5983Representative.law0.SatisfiedBy oppositeTable.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    oppositeTable SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_5983Representative.law0
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
    SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_5983Representative.law1.SatisfiedBy oppositeTable.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    oppositeTable SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_5983Representative.law1
    targetLaw1ToFinite targetLaw1FromFinite (by decide) (by decide)

/-- Exact finite checks that the selected target models the root basis. -/
theorem targetModels :
    Models oppositeTable.semigroup SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_5983Representative.basis := by
  unfold SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_5983Representative.basis
  exact
    FiniteNilpotentCounterexample.models_cons targetLaw0Valid <|
      FiniteNilpotentCounterexample.models_cons targetLaw1Valid <|
        FiniteNilpotentCounterexample.models_nil oppositeTable.semigroup

/-- Exact identity-theory transfer authenticated by the finite certificate. -/
theorem sameIdentityTheory :
    SameIdentityTheoryOver SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_5983Representative.sourceSemigroup
      oppositeTable.semigroup Nat := by
  intro identity
  constructor
  · intro sourceValid valuation
    exact Derives.sound targetModels
      (SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_5983Representative.basis_complete.2 identity sourceValid) valuation
  · intro targetValid
    have powerValid :=
      identity.satisfiedByPi oppositeTable.semigroup
        (Fin 17) targetValid
    have subValid :=
      powerCertificate.embedding.pullback_identity identity powerValid
    exact quotient.pushforwardIdentity identity subValid

/-- First-layer generic-CAS basis wrapper for `S6_11769`. -/
theorem representative_basis :
    BasisFor table.semigroup.opposite SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_5983Representative.basis := by
  have transferred :
      BasisFor oppositeTable.semigroup SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_5983Representative.basis :=
    (basisFor_iff_of_sameIdentityTheoryOver sameIdentityTheory).mp
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_5983Representative.basis_complete
  simpa only [oppositeTable_semigroup] using transferred


theorem opposite_basis :
    BasisFor table.semigroup (reversedBasis SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_5983Representative.basis) :=
  representative_basis.oppositeReversed

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11769
