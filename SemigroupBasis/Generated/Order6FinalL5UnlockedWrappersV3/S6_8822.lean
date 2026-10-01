import SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_5983Representative
import SemigroupBasis.FiniteNilpotentCounterexample
import SemigroupBasis.Nonfinite
import SemigroupBasis.Opposite
import SemigroupBasis.RightGeneratedPowerCertificate

set_option maxRecDepth 2048

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_8822

open SemigroupBasis

def routeManifestRowSHA256 : String := "8dc8a1a4e70c07d2e466cf2f390aeb7294dbdd2ba883c52e4d9784ca7af058a0"
def witnessRecordSHA256 : String := "db559d1cb4a79b01086ceec2f1ad9c7352c6acbce749ac4646cd2f4e79f63320"
def transferComponentSHA256 : String := "db559d1cb4a79b01086ceec2f1ad9c7352c6acbce749ac4646cd2f4e79f63320"
def powerCertificateSHA256 : String := "f3ce5829151367ef269ac6f1831956fa9b74d708214a66283a6ba9e040747877"

private def row6
    (c0 c1 c2 c3 c4 c5 : Fin 6) (column : Fin 6) : Fin 6 :=
  if column = 0 then c0 else
    if column = 1 then c1 else
      if column = 2 then c2 else
        if column = 3 then c3 else
          if column = 4 then c4 else c5

/-- Exact one-based catalogue table committed by the portable witness. -/
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 2 0 0 0 right else
    if left = 1 then row6 0 0 2 0 0 1 right else
      if left = 2 then row6 2 2 0 2 2 2 right else
        if left = 3 then row6 0 0 2 3 4 3 right else
          if left = 4 then row6 0 0 2 3 4 4 right else
            row6 0 0 2 3 4 5 right

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
  "2cc5e6537f0e1c4a69d349386245b0287912339922b1c85cdfa01c63b6a0f03c"

private def packedStateVectorCodeChunk0 (index : Nat) : Nat :=
  match index with
  | 0 => 81759503453689
  | 1 => 65822787146454
  | 2 => 95599048481028
  | 3 => 81746440473528
  | 4 => 79863403335696
  | 5 => 81428610618720
  | 6 => 62479246771008
  | 7 => 65352479548608
  | 8 => 59396912578944
  | 9 => 78541775649792
  | 10 => 59786558016768
  | 11 => 95520663873792
  | 12 => 81746441033400
  | 13 => 79863402775824
  | 14 => 81428610058848
  | 15 => 79393217789952
  | 16 => 79393097417472
  | 17 => 79079741538048
  | 18 => 81350245886976
  | 19 => 79469385576192
  | 20 => 81350226291456
  | 21 => 62466185470464
  | 22 => 62466065097984
  | 23 => 62152719296256
  | 24 => 62479125838656
  | 25 => 65352600480960
  | 26 => 59396791646592
  | 27 => 59266305918720
  | 28 => 59318427202560
  | 29 => 59318527979520
  | 30 => 78528712716288
  | _ => 76647912871680

private def packedStateVectorCodeChunk1 (index : Nat) : Nat :=
  match index with
  | 0 => 78528693120768
  | 1 => 59264129136384
  | 2 => 59316250420224
  | 3 => 59316351197184
  | 4 => 78541755494400
  | 5 => 59786537861376
  | 6 => 95520684029184
  | 7 => 79393218349824
  | 8 => 79393096857600
  | 9 => 79079740978176
  | 10 => 81350246446848
  | 11 => 79469385016320
  | 12 => 81350225731584
  | 13 => 79079620605696
  | 14 => 79001376814080
  | 15 => 79001256441600
  | 16 => 79001357218560
  | 17 => 78999200031744
  | 18 => 78999079659264
  | 19 => 78999180436224
  | 20 => 79469365420800
  | 21 => 62466186030336
  | 22 => 62466064538112
  | 23 => 62152718736384
  | 24 => 62152598363904
  | 25 => 62074354572288
  | 26 => 62074234199808
  | 27 => 62074334976768
  | 28 => 59266184986368
  | 29 => 59318548134912
  | 30 => 59318407047168
  | _ => 59253244664832

private def packedStateVectorCodeChunk2 (index : Nat) : Nat :=
  match index with
  | 0 => 59253124292352
  | 1 => 59253225069312
  | 2 => 59266285763328
  | 3 => 78528713276160
  | 4 => 76647912311808
  | 5 => 78528692560896
  | 6 => 76177727327232
  | 7 => 76177606954752
  | 8 => 76177707731712
  | 9 => 76647892716288
  | 10 => 59251067882496
  | 11 => 59250947510016
  | 12 => 59251048286976
  | 13 => 59264008204032
  | 14 => 59316371352576
  | 15 => 59316230264832
  | 16 => 59264108980992
  | 17 => 79079620045824
  | 18 => 79001377373952
  | 19 => 79001255881728
  | 20 => 79001356658688
  | 21 => 78999200591616
  | 22 => 78999079099392
  | 23 => 78999179876352
  | 24 => 79469364860928
  | 25 => 79001236286208
  | 26 => 78999059503872
  | 27 => 62152597804032
  | 28 => 62074355132160
  | 29 => 62074233639936
  | 30 => 62074334416896
  | _ => 62074214044416

private def packedStateVectorCodeChunk3 (index : Nat) : Nat :=
  match index with
  | 0 => 59253123732480
  | 1 => 59253245224704
  | 2 => 59253104136960
  | 3 => 59266164830976
  | 4 => 59253224509440
  | 5 => 76177727887104
  | 6 => 76177606394880
  | 7 => 76177707171840
  | 8 => 76647892156416
  | 9 => 76177586799360
  | 10 => 59251068442368
  | 11 => 59250946950144
  | 12 => 59251047727104
  | 13 => 59250927354624
  | 14 => 59263988048640
  | 15 => 79001235726336
  | 16 => 78999058944000
  | 17 => 62074213484544
  | 18 => 59253103577088
  | 19 => 76177586239488
  | _ => 59250926794752

private def packedStateVectorCode (state : Fin 117) : Nat :=
  if state.val < 32 then packedStateVectorCodeChunk0 state.val else
    if state.val < 64 then packedStateVectorCodeChunk1 (state.val - 32) else
      if state.val < 96 then packedStateVectorCodeChunk2 (state.val - 64) else
        packedStateVectorCodeChunk3 (state.val - 96)

def stateVector (state : Fin 117)
    (coordinate : Fin 18) : Fin 6 :=
  ⟨(packedStateVectorCode state / 6 ^ coordinate.val) % 6,
    Nat.mod_lt _ (by decide)⟩

def generatorVector (generator : Fin 3)
    (coordinate : Fin 18) : Fin 6 :=
  match generator.val with
  | 0 =>
      match coordinate.val with
      | 0 => (1 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (3 : Fin 6)
      | 4 => (5 : Fin 6)
      | 5 => (5 : Fin 6)
      | 6 => (1 : Fin 6)
      | 7 => (2 : Fin 6)
      | 8 => (1 : Fin 6)
      | 9 => (4 : Fin 6)
      | 10 => (4 : Fin 6)
      | 11 => (4 : Fin 6)
      | 12 => (5 : Fin 6)
      | 13 => (1 : Fin 6)
      | 14 => (5 : Fin 6)
      | 15 => (5 : Fin 6)
      | 16 => (4 : Fin 6)
      | _ => (4 : Fin 6)
  | 1 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (1 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (1 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (5 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (1 : Fin 6)
      | 9 => (3 : Fin 6)
      | 10 => (2 : Fin 6)
      | 11 => (3 : Fin 6)
      | 12 => (4 : Fin 6)
      | 13 => (5 : Fin 6)
      | 14 => (5 : Fin 6)
      | 15 => (1 : Fin 6)
      | 16 => (5 : Fin 6)
      | _ => (3 : Fin 6)
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
      | 8 => (5 : Fin 6)
      | 9 => (2 : Fin 6)
      | 10 => (3 : Fin 6)
      | 11 => (3 : Fin 6)
      | 12 => (3 : Fin 6)
      | 13 => (5 : Fin 6)
      | 14 => (1 : Fin 6)
      | 15 => (5 : Fin 6)
      | 16 => (3 : Fin 6)
      | _ => (5 : Fin 6)

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
  if code = 59250926794752 then (116 : Fin 117) else
  if code = 59250927354624 then (109 : Fin 117) else
  if code = 59250946950144 then (107 : Fin 117) else
  if code = 59250947510016 then (75 : Fin 117) else
  if code = 59251047727104 then (108 : Fin 117) else
  if code = 59251048286976 then (76 : Fin 117) else
  if code = 59251067882496 then (74 : Fin 117) else
  if code = 59251068442368 then (106 : Fin 117) else
  if code = 59253103577088 then (114 : Fin 117) else
  if code = 59253104136960 then (98 : Fin 117) else
  if code = 59253123732480 then (96 : Fin 117) else
  if code = 59253124292352 then (64 : Fin 117) else
  if code = 59253224509440 then (100 : Fin 117) else
  if code = 59253225069312 then (65 : Fin 117) else
  if code = 59253244664832 then (63 : Fin 117) else
  if code = 59253245224704 then (97 : Fin 117) else
  if code = 59263988048640 then (110 : Fin 117) else
  if code = 59264008204032 then (77 : Fin 117) else
  if code = 59264108980992 then (80 : Fin 117) else
  if code = 59264129136384 then (33 : Fin 117) else
  if code = 59266164830976 then (99 : Fin 117) else
  if code = 59266184986368 then (60 : Fin 117) else
  if code = 59266285763328 then (66 : Fin 117) else
  if code = 59266305918720 then (27 : Fin 117) else
  if code = 59316230264832 then (79 : Fin 117) else
  if code = 59316250420224 then (34 : Fin 117) else
  if code = 59316351197184 then (35 : Fin 117) else
  if code = 59316371352576 then (78 : Fin 117) else
  if code = 59318407047168 then (62 : Fin 117) else
  if code = 59318427202560 then (28 : Fin 117) else
  if code = 59318527979520 then (29 : Fin 117) else
  if code = 59318548134912 then (61 : Fin 117) else
  (0 : Fin 117)

private def decodeStateCodeChunk1 (code : Nat) : Fin 117 :=
  if code = 59396791646592 then (26 : Fin 117) else
  if code = 59396912578944 then (8 : Fin 117) else
  if code = 59786537861376 then (37 : Fin 117) else
  if code = 59786558016768 then (10 : Fin 117) else
  if code = 62074213484544 then (113 : Fin 117) else
  if code = 62074214044416 then (95 : Fin 117) else
  if code = 62074233639936 then (93 : Fin 117) else
  if code = 62074234199808 then (58 : Fin 117) else
  if code = 62074334416896 then (94 : Fin 117) else
  if code = 62074334976768 then (59 : Fin 117) else
  if code = 62074354572288 then (57 : Fin 117) else
  if code = 62074355132160 then (92 : Fin 117) else
  if code = 62152597804032 then (91 : Fin 117) else
  if code = 62152598363904 then (56 : Fin 117) else
  if code = 62152718736384 then (55 : Fin 117) else
  if code = 62152719296256 then (23 : Fin 117) else
  if code = 62466064538112 then (54 : Fin 117) else
  if code = 62466065097984 then (22 : Fin 117) else
  if code = 62466185470464 then (21 : Fin 117) else
  if code = 62466186030336 then (53 : Fin 117) else
  if code = 62479125838656 then (24 : Fin 117) else
  if code = 62479246771008 then (6 : Fin 117) else
  if code = 65352479548608 then (7 : Fin 117) else
  if code = 65352600480960 then (25 : Fin 117) else
  if code = 65822787146454 then (1 : Fin 117) else
  if code = 76177586239488 then (115 : Fin 117) else
  if code = 76177586799360 then (105 : Fin 117) else
  if code = 76177606394880 then (102 : Fin 117) else
  if code = 76177606954752 then (71 : Fin 117) else
  if code = 76177707171840 then (103 : Fin 117) else
  if code = 76177707731712 then (72 : Fin 117) else
  if code = 76177727327232 then (70 : Fin 117) else
  (0 : Fin 117)

private def decodeStateCodeChunk2 (code : Nat) : Fin 117 :=
  if code = 76177727887104 then (101 : Fin 117) else
  if code = 76647892156416 then (104 : Fin 117) else
  if code = 76647892716288 then (73 : Fin 117) else
  if code = 76647912311808 then (68 : Fin 117) else
  if code = 76647912871680 then (31 : Fin 117) else
  if code = 78528692560896 then (69 : Fin 117) else
  if code = 78528693120768 then (32 : Fin 117) else
  if code = 78528712716288 then (30 : Fin 117) else
  if code = 78528713276160 then (67 : Fin 117) else
  if code = 78541755494400 then (36 : Fin 117) else
  if code = 78541775649792 then (9 : Fin 117) else
  if code = 78999058944000 then (112 : Fin 117) else
  if code = 78999059503872 then (90 : Fin 117) else
  if code = 78999079099392 then (86 : Fin 117) else
  if code = 78999079659264 then (50 : Fin 117) else
  if code = 78999179876352 then (87 : Fin 117) else
  if code = 78999180436224 then (51 : Fin 117) else
  if code = 78999200031744 then (49 : Fin 117) else
  if code = 78999200591616 then (85 : Fin 117) else
  if code = 79001235726336 then (111 : Fin 117) else
  if code = 79001236286208 then (89 : Fin 117) else
  if code = 79001255881728 then (83 : Fin 117) else
  if code = 79001256441600 then (47 : Fin 117) else
  if code = 79001356658688 then (84 : Fin 117) else
  if code = 79001357218560 then (48 : Fin 117) else
  if code = 79001376814080 then (46 : Fin 117) else
  if code = 79001377373952 then (82 : Fin 117) else
  if code = 79079620045824 then (81 : Fin 117) else
  if code = 79079620605696 then (45 : Fin 117) else
  if code = 79079740978176 then (41 : Fin 117) else
  if code = 79079741538048 then (17 : Fin 117) else
  if code = 79393096857600 then (40 : Fin 117) else
  (0 : Fin 117)

private def decodeStateCodeChunk3 (code : Nat) : Fin 117 :=
  if code = 79393097417472 then (16 : Fin 117) else
  if code = 79393217789952 then (15 : Fin 117) else
  if code = 79393218349824 then (39 : Fin 117) else
  if code = 79469364860928 then (88 : Fin 117) else
  if code = 79469365420800 then (52 : Fin 117) else
  if code = 79469385016320 then (43 : Fin 117) else
  if code = 79469385576192 then (19 : Fin 117) else
  if code = 79863402775824 then (13 : Fin 117) else
  if code = 79863403335696 then (4 : Fin 117) else
  if code = 81350225731584 then (44 : Fin 117) else
  if code = 81350226291456 then (20 : Fin 117) else
  if code = 81350245886976 then (18 : Fin 117) else
  if code = 81350246446848 then (42 : Fin 117) else
  if code = 81428610058848 then (14 : Fin 117) else
  if code = 81428610618720 then (5 : Fin 117) else
  if code = 81746440473528 then (3 : Fin 117) else
  if code = 81746441033400 then (12 : Fin 117) else
  if code = 81759503453689 then (0 : Fin 117) else
  if code = 95520663873792 then (11 : Fin 117) else
  if code = 95520684029184 then (38 : Fin 117) else
  if code = 95599048481028 then (2 : Fin 117) else
  (0 : Fin 117)

private def stateVectorCode
    (vector : Fin 18 -> Fin 6) : Nat :=
  (vector (0 : Fin 18)).val + 6 * ((vector (1 : Fin 18)).val + 6 * ((vector (2 : Fin 18)).val + 6 * ((vector (3 : Fin 18)).val + 6 * ((vector (4 : Fin 18)).val + 6 * ((vector (5 : Fin 18)).val + 6 * ((vector (6 : Fin 18)).val + 6 * ((vector (7 : Fin 18)).val + 6 * ((vector (8 : Fin 18)).val + 6 * ((vector (9 : Fin 18)).val + 6 * ((vector (10 : Fin 18)).val + 6 * ((vector (11 : Fin 18)).val + 6 * ((vector (12 : Fin 18)).val + 6 * ((vector (13 : Fin 18)).val + 6 * ((vector (14 : Fin 18)).val + 6 * ((vector (15 : Fin 18)).val + 6 * ((vector (16 : Fin 18)).val + 6 * ((vector (17 : Fin 18)).val)))))))))))))))))

private def decodeStateCode (code : Nat) : Fin 117 :=
  if code < 59396791646592 then decodeStateCodeChunk0 code else
  if code < 76177727887104 then decodeStateCodeChunk1 code else
  if code < 79393097417472 then decodeStateCodeChunk2 code else
  decodeStateCodeChunk3 code

private def decodeState
    (vector : Fin 18 -> Fin 6) : Fin 117 :=
  decodeStateCode (stateVectorCode vector)

set_option maxHeartbeats 2000000 in
private theorem decodeState_stateVector (state : Fin 117) :
    decodeState (stateVector state) = state := by
  decide +revert

set_option maxHeartbeats 2000000 in
private theorem transitionMap :
    forall (state : Fin 117)
      (generator : Fin 3)
      (coordinate : Fin 18),
      stateVector (transition state generator) coordinate =
        oppositeTable.semigroup.mul (stateVector state coordinate)
          (generatorVector generator coordinate) := by
  intro state generator coordinate
  apply Fin.ext
  exact by decide +revert

set_option maxHeartbeats 2000000 in
private theorem representativeMap :
    forall (state : Fin 117)
      (coordinate : Fin 18),
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
    (I := Fin 18) oppositeTable.semigroup where
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
        (Fin 18) targetValid
    have subValid :=
      powerCertificate.embedding.pullback_identity identity powerValid
    exact quotient.pushforwardIdentity identity subValid

/-- First-layer generic-CAS basis wrapper for `S6_8822`. -/
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

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_8822
