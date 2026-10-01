import SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_5983Representative
import SemigroupBasis.FiniteNilpotentCounterexample
import SemigroupBasis.Nonfinite
import SemigroupBasis.Opposite
import SemigroupBasis.RightGeneratedPowerCertificate

set_option maxRecDepth 2048

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_8833

open SemigroupBasis

def routeManifestRowSHA256 : String := "61fac3f7b6091bc4cc127d9837bdd8f28cbb357fd23b470f72c227c817bf3ae3"
def witnessRecordSHA256 : String := "95a69cfedeea697257c8bc0ca53fb9c1065ce91bfbfc0d528841568fb3e091ab"
def transferComponentSHA256 : String := "95a69cfedeea697257c8bc0ca53fb9c1065ce91bfbfc0d528841568fb3e091ab"
def powerCertificateSHA256 : String := "80c43e79baf5124cb425231df19b3ecae2c4398b09f72cd58597b16b9f875cd9"

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
    if left = 1 then row6 0 0 2 1 1 1 right else
      if left = 2 then row6 2 2 0 2 2 2 right else
        if left = 3 then row6 0 0 2 3 3 5 right else
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
  "c3affe0ffbd51ad9dbe01c33433fef3b4a0843b0558821fe74f236cae9478be9"

private def packedStateVectorCodeChunk0 (index : Nat) : Nat :=
  match index with
  | 0 => 100408431048985
  | 1 => 62821003651926
  | 2 => 77705894319876
  | 3 => 100395368068824
  | 4 => 99456994016784
  | 5 => 100236433264992
  | 6 => 65145805132608
  | 7 => 62350696054080
  | 8 => 59372967973248
  | 9 => 94528065125376
  | 10 => 59760436628736
  | 11 => 77627509712640
  | 12 => 100395368628696
  | 13 => 99456993456912
  | 14 => 100236432705120
  | 15 => 98986808471040
  | 16 => 98986688098560
  | 17 => 98830050469632
  | 18 => 100158068533248
  | 19 => 99217517725440
  | 20 => 100158048937728
  | 21 => 65132743832064
  | 22 => 65132623459584
  | 23 => 64976005986048
  | 24 => 65145684200256
  | 25 => 62350816986432
  | 26 => 59372847040896
  | 27 => 59268482701056
  | 28 => 59294482596864
  | 29 => 59294583373824
  | 30 => 94515002191872
  | _ => 93574572316416

private def packedStateVectorCodeChunk1 (index : Nat) : Nat :=
  match index with
  | 0 => 94514982596352
  | 1 => 59264129136384
  | 2 => 59290129032192
  | 3 => 59290229809152
  | 4 => 94528044969984
  | 5 => 59760416473344
  | 6 => 77627529868032
  | 7 => 98986809030912
  | 8 => 98986687538688
  | 9 => 98830049909760
  | 10 => 100158069093120
  | 11 => 99217517165568
  | 12 => 100158048377856
  | 13 => 98829929537280
  | 14 => 98751685745664
  | 15 => 98751565373184
  | 16 => 98751666150144
  | 17 => 98747332180992
  | 18 => 98747211808512
  | 19 => 98747312585472
  | 20 => 99217497570048
  | 21 => 65132744391936
  | 22 => 65132622899712
  | 23 => 64976005426176
  | 24 => 64975885053696
  | 25 => 64897641262080
  | 26 => 64897520889600
  | 27 => 64897621666560
  | 28 => 59268361768704
  | 29 => 59294603529216
  | 30 => 59294462441472
  | _ => 59255421447168

private def packedStateVectorCodeChunk2 (index : Nat) : Nat :=
  match index with
  | 0 => 59255301074688
  | 1 => 59255401851648
  | 2 => 59268462545664
  | 3 => 94515002751744
  | 4 => 93574571756544
  | 5 => 94514982036480
  | 6 => 93104386771968
  | 7 => 93104266399488
  | 8 => 93104367176448
  | 9 => 93574552161024
  | 10 => 59251067882496
  | 11 => 59250947510016
  | 12 => 59251048286976
  | 13 => 59264008204032
  | 14 => 59290249964544
  | 15 => 59290108876800
  | 16 => 59264108980992
  | 17 => 98829928977408
  | 18 => 98751686305536
  | 19 => 98751564813312
  | 20 => 98751665590272
  | 21 => 98747332740864
  | 22 => 98747211248640
  | 23 => 98747312025600
  | 24 => 99217497010176
  | 25 => 98751545217792
  | 26 => 98747191653120
  | 27 => 64975884493824
  | 28 => 64897641821952
  | 29 => 64897520329728
  | 30 => 64897621106688
  | _ => 64897500734208

private def packedStateVectorCodeChunk3 (index : Nat) : Nat :=
  match index with
  | 0 => 59255300514816
  | 1 => 59255422007040
  | 2 => 59255280919296
  | 3 => 59268341613312
  | 4 => 59255401291776
  | 5 => 93104387331840
  | 6 => 93104265839616
  | 7 => 93104366616576
  | 8 => 93574551601152
  | 9 => 93104246244096
  | 10 => 59251068442368
  | 11 => 59250946950144
  | 12 => 59251047727104
  | 13 => 59250927354624
  | 14 => 59263988048640
  | 15 => 98751544657920
  | 16 => 98747191093248
  | 17 => 64897500174336
  | 18 => 59255280359424
  | 19 => 93104245684224
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
      | 4 => (3 : Fin 6)
      | 5 => (3 : Fin 6)
      | 6 => (1 : Fin 6)
      | 7 => (2 : Fin 6)
      | 8 => (1 : Fin 6)
      | 9 => (5 : Fin 6)
      | 10 => (5 : Fin 6)
      | 11 => (5 : Fin 6)
      | 12 => (4 : Fin 6)
      | 13 => (1 : Fin 6)
      | 14 => (3 : Fin 6)
      | 15 => (3 : Fin 6)
      | 16 => (5 : Fin 6)
      | _ => (5 : Fin 6)
  | 1 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (1 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (1 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (3 : Fin 6)
      | 7 => (3 : Fin 6)
      | 8 => (1 : Fin 6)
      | 9 => (3 : Fin 6)
      | 10 => (2 : Fin 6)
      | 11 => (3 : Fin 6)
      | 12 => (5 : Fin 6)
      | 13 => (3 : Fin 6)
      | 14 => (3 : Fin 6)
      | 15 => (1 : Fin 6)
      | 16 => (4 : Fin 6)
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
      | 8 => (3 : Fin 6)
      | 9 => (2 : Fin 6)
      | 10 => (3 : Fin 6)
      | 11 => (3 : Fin 6)
      | 12 => (3 : Fin 6)
      | 13 => (3 : Fin 6)
      | 14 => (1 : Fin 6)
      | 15 => (3 : Fin 6)
      | 16 => (3 : Fin 6)
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
  if code = 59250926794752 then (116 : Fin 117) else
  if code = 59250927354624 then (109 : Fin 117) else
  if code = 59250946950144 then (107 : Fin 117) else
  if code = 59250947510016 then (75 : Fin 117) else
  if code = 59251047727104 then (108 : Fin 117) else
  if code = 59251048286976 then (76 : Fin 117) else
  if code = 59251067882496 then (74 : Fin 117) else
  if code = 59251068442368 then (106 : Fin 117) else
  if code = 59255280359424 then (114 : Fin 117) else
  if code = 59255280919296 then (98 : Fin 117) else
  if code = 59255300514816 then (96 : Fin 117) else
  if code = 59255301074688 then (64 : Fin 117) else
  if code = 59255401291776 then (100 : Fin 117) else
  if code = 59255401851648 then (65 : Fin 117) else
  if code = 59255421447168 then (63 : Fin 117) else
  if code = 59255422007040 then (97 : Fin 117) else
  if code = 59263988048640 then (110 : Fin 117) else
  if code = 59264008204032 then (77 : Fin 117) else
  if code = 59264108980992 then (80 : Fin 117) else
  if code = 59264129136384 then (33 : Fin 117) else
  if code = 59268341613312 then (99 : Fin 117) else
  if code = 59268361768704 then (60 : Fin 117) else
  if code = 59268462545664 then (66 : Fin 117) else
  if code = 59268482701056 then (27 : Fin 117) else
  if code = 59290108876800 then (79 : Fin 117) else
  if code = 59290129032192 then (34 : Fin 117) else
  if code = 59290229809152 then (35 : Fin 117) else
  if code = 59290249964544 then (78 : Fin 117) else
  if code = 59294462441472 then (62 : Fin 117) else
  if code = 59294482596864 then (28 : Fin 117) else
  if code = 59294583373824 then (29 : Fin 117) else
  if code = 59294603529216 then (61 : Fin 117) else
  (0 : Fin 117)

private def decodeStateCodeChunk1 (code : Nat) : Fin 117 :=
  if code = 59372847040896 then (26 : Fin 117) else
  if code = 59372967973248 then (8 : Fin 117) else
  if code = 59760416473344 then (37 : Fin 117) else
  if code = 59760436628736 then (10 : Fin 117) else
  if code = 62350696054080 then (7 : Fin 117) else
  if code = 62350816986432 then (25 : Fin 117) else
  if code = 62821003651926 then (1 : Fin 117) else
  if code = 64897500174336 then (113 : Fin 117) else
  if code = 64897500734208 then (95 : Fin 117) else
  if code = 64897520329728 then (93 : Fin 117) else
  if code = 64897520889600 then (58 : Fin 117) else
  if code = 64897621106688 then (94 : Fin 117) else
  if code = 64897621666560 then (59 : Fin 117) else
  if code = 64897641262080 then (57 : Fin 117) else
  if code = 64897641821952 then (92 : Fin 117) else
  if code = 64975884493824 then (91 : Fin 117) else
  if code = 64975885053696 then (56 : Fin 117) else
  if code = 64976005426176 then (55 : Fin 117) else
  if code = 64976005986048 then (23 : Fin 117) else
  if code = 65132622899712 then (54 : Fin 117) else
  if code = 65132623459584 then (22 : Fin 117) else
  if code = 65132743832064 then (21 : Fin 117) else
  if code = 65132744391936 then (53 : Fin 117) else
  if code = 65145684200256 then (24 : Fin 117) else
  if code = 65145805132608 then (6 : Fin 117) else
  if code = 77627509712640 then (11 : Fin 117) else
  if code = 77627529868032 then (38 : Fin 117) else
  if code = 77705894319876 then (2 : Fin 117) else
  if code = 93104245684224 then (115 : Fin 117) else
  if code = 93104246244096 then (105 : Fin 117) else
  if code = 93104265839616 then (102 : Fin 117) else
  if code = 93104266399488 then (71 : Fin 117) else
  (0 : Fin 117)

private def decodeStateCodeChunk2 (code : Nat) : Fin 117 :=
  if code = 93104366616576 then (103 : Fin 117) else
  if code = 93104367176448 then (72 : Fin 117) else
  if code = 93104386771968 then (70 : Fin 117) else
  if code = 93104387331840 then (101 : Fin 117) else
  if code = 93574551601152 then (104 : Fin 117) else
  if code = 93574552161024 then (73 : Fin 117) else
  if code = 93574571756544 then (68 : Fin 117) else
  if code = 93574572316416 then (31 : Fin 117) else
  if code = 94514982036480 then (69 : Fin 117) else
  if code = 94514982596352 then (32 : Fin 117) else
  if code = 94515002191872 then (30 : Fin 117) else
  if code = 94515002751744 then (67 : Fin 117) else
  if code = 94528044969984 then (36 : Fin 117) else
  if code = 94528065125376 then (9 : Fin 117) else
  if code = 98747191093248 then (112 : Fin 117) else
  if code = 98747191653120 then (90 : Fin 117) else
  if code = 98747211248640 then (86 : Fin 117) else
  if code = 98747211808512 then (50 : Fin 117) else
  if code = 98747312025600 then (87 : Fin 117) else
  if code = 98747312585472 then (51 : Fin 117) else
  if code = 98747332180992 then (49 : Fin 117) else
  if code = 98747332740864 then (85 : Fin 117) else
  if code = 98751544657920 then (111 : Fin 117) else
  if code = 98751545217792 then (89 : Fin 117) else
  if code = 98751564813312 then (83 : Fin 117) else
  if code = 98751565373184 then (47 : Fin 117) else
  if code = 98751665590272 then (84 : Fin 117) else
  if code = 98751666150144 then (48 : Fin 117) else
  if code = 98751685745664 then (46 : Fin 117) else
  if code = 98751686305536 then (82 : Fin 117) else
  if code = 98829928977408 then (81 : Fin 117) else
  if code = 98829929537280 then (45 : Fin 117) else
  (0 : Fin 117)

private def decodeStateCodeChunk3 (code : Nat) : Fin 117 :=
  if code = 98830049909760 then (41 : Fin 117) else
  if code = 98830050469632 then (17 : Fin 117) else
  if code = 98986687538688 then (40 : Fin 117) else
  if code = 98986688098560 then (16 : Fin 117) else
  if code = 98986808471040 then (15 : Fin 117) else
  if code = 98986809030912 then (39 : Fin 117) else
  if code = 99217497010176 then (88 : Fin 117) else
  if code = 99217497570048 then (52 : Fin 117) else
  if code = 99217517165568 then (43 : Fin 117) else
  if code = 99217517725440 then (19 : Fin 117) else
  if code = 99456993456912 then (13 : Fin 117) else
  if code = 99456994016784 then (4 : Fin 117) else
  if code = 100158048377856 then (44 : Fin 117) else
  if code = 100158048937728 then (20 : Fin 117) else
  if code = 100158068533248 then (18 : Fin 117) else
  if code = 100158069093120 then (42 : Fin 117) else
  if code = 100236432705120 then (14 : Fin 117) else
  if code = 100236433264992 then (5 : Fin 117) else
  if code = 100395368068824 then (3 : Fin 117) else
  if code = 100395368628696 then (12 : Fin 117) else
  if code = 100408431048985 then (0 : Fin 117) else
  (0 : Fin 117)

private def stateVectorCode
    (vector : Fin 18 -> Fin 6) : Nat :=
  (vector (0 : Fin 18)).val + 6 * ((vector (1 : Fin 18)).val + 6 * ((vector (2 : Fin 18)).val + 6 * ((vector (3 : Fin 18)).val + 6 * ((vector (4 : Fin 18)).val + 6 * ((vector (5 : Fin 18)).val + 6 * ((vector (6 : Fin 18)).val + 6 * ((vector (7 : Fin 18)).val + 6 * ((vector (8 : Fin 18)).val + 6 * ((vector (9 : Fin 18)).val + 6 * ((vector (10 : Fin 18)).val + 6 * ((vector (11 : Fin 18)).val + 6 * ((vector (12 : Fin 18)).val + 6 * ((vector (13 : Fin 18)).val + 6 * ((vector (14 : Fin 18)).val + 6 * ((vector (15 : Fin 18)).val + 6 * ((vector (16 : Fin 18)).val + 6 * ((vector (17 : Fin 18)).val)))))))))))))))))

private def decodeStateCode (code : Nat) : Fin 117 :=
  if code < 59372847040896 then decodeStateCodeChunk0 code else
  if code < 93104366616576 then decodeStateCodeChunk1 code else
  if code < 98830049909760 then decodeStateCodeChunk2 code else
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

/-- First-layer generic-CAS basis wrapper for `S6_8833`. -/
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

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_8833
