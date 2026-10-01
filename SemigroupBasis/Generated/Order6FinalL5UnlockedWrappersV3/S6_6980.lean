import SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_5983Representative
import SemigroupBasis.FiniteNilpotentCounterexample
import SemigroupBasis.Nonfinite
import SemigroupBasis.Opposite
import SemigroupBasis.RightGeneratedPowerCertificate

set_option maxRecDepth 2048

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6980

open SemigroupBasis

def routeManifestRowSHA256 : String := "b7399d0d276ace4ddf22f75f30409f98dde5ff84dd8257de19971a8f68d00948"
def witnessRecordSHA256 : String := "04888bb1abd7076aaafed3a4cffa2d86750106103c54f3d0c26294d4e7b3cf4e"
def transferComponentSHA256 : String := "04888bb1abd7076aaafed3a4cffa2d86750106103c54f3d0c26294d4e7b3cf4e"
def powerCertificateSHA256 : String := "5fddcced83c09d20a090915cf9975986c10c8a9aeb2ff1fe11fde70f19798388"

private def row6
    (c0 c1 c2 c3 c4 c5 : Fin 6) (column : Fin 6) : Fin 6 :=
  if column = 0 then c0 else
    if column = 1 then c1 else
      if column = 2 then c2 else
        if column = 3 then c3 else
          if column = 4 then c4 else c5

/-- Exact one-based catalogue table committed by the portable witness. -/
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 1 1 3 4 0 right else
    if left = 1 then row6 1 0 0 4 3 1 right else
      if left = 2 then row6 1 0 0 4 3 2 right else
        if left = 3 then row6 0 1 1 3 4 3 right else
          if left = 4 then row6 1 0 0 4 3 4 right else
            row6 0 1 1 3 4 5 right

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
  "960e5c4afc2461127222bc2a273231518423b190f021e7977dd494064bd993f4"

private def packedStateVectorCodeChunk0 (index : Nat) : Nat :=
  match index with
  | 0 => 1535324
  | 1 => 823584
  | 2 => 1638000
  | 3 => 1439418
  | 4 => 632209
  | 5 => 1448353
  | 6 => 399571
  | 7 => 263268
  | 8 => 540726
  | 9 => 1498861
  | 10 => 797514
  | 11 => 1637928
  | 12 => 1487371
  | 13 => 584256
  | 14 => 1400400
  | 15 => 304314
  | 16 => 72109
  | 17 => 352159
  | 18 => 1400364
  | 19 => 608731
  | 20 => 1448281
  | 21 => 303666
  | 22 => 71461
  | 23 => 351511
  | 24 => 119413
  | 25 => 543426
  | 26 => 260568
  | 27 => 402019
  | 28 => 260532
  | 29 => 540654
  | 30 => 1404252
  | _ => 612619

private def packedStateVectorCodeChunk1 (index : Nat) : Nat :=
  match index with
  | 0 => 1452169
  | 1 => 378691
  | 2 => 237204
  | 3 => 517326
  | 4 => 1498825
  | 5 => 797478
  | 6 => 1637964
  | 7 => 352267
  | 8 => 24156
  | 9 => 304206
  | 10 => 1448317
  | 11 => 560778
  | 12 => 1400328
  | 13 => 72001
  | 14 => 304170
  | 15 => 71965
  | 16 => 352087
  | 17 => 280842
  | 18 => 48637
  | 19 => 328759
  | 20 => 608695
  | 21 => 351619
  | 22 => 23508
  | 23 => 303558
  | 24 => 71353
  | 25 => 303522
  | 26 => 71317
  | 27 => 351439
  | 28 => 121861
  | 29 => 540690
  | 30 => 260496
  | _ => 307410

private def packedStateVectorCodeChunk2 (index : Nat) : Nat :=
  match index with
  | 0 => 75205
  | 1 => 355327
  | 2 => 401983
  | 3 => 1452205
  | 4 => 564666
  | 5 => 1404216
  | 6 => 284730
  | 7 => 52525
  | 8 => 332647
  | 9 => 612583
  | 10 => 284082
  | 11 => 51877
  | 12 => 331999
  | 13 => 98533
  | 14 => 517362
  | 15 => 237168
  | 16 => 378655
  | 17 => 24048
  | 18 => 352123
  | 19 => 24012
  | 20 => 304134
  | 21 => 328795
  | 22 => 684
  | 23 => 280806
  | 24 => 560742
  | 25 => 71929
  | 26 => 48601
  | 27 => 23400
  | 28 => 351475
  | 29 => 23364
  | 30 => 303486
  | _ => 71281

private def packedStateVectorCodeChunk3 (index : Nat) : Nat :=
  match index with
  | 0 => 27252
  | 1 => 355363
  | 2 => 75169
  | 3 => 121825
  | 4 => 307374
  | 5 => 332683
  | 6 => 4572
  | 7 => 284694
  | 8 => 564630
  | 9 => 52489
  | 10 => 332035
  | 11 => 3924
  | 12 => 284046
  | 13 => 51841
  | 14 => 98497
  | 15 => 23976
  | 16 => 648
  | 17 => 23328
  | 18 => 27216
  | 19 => 4536
  | _ => 3888

private def packedStateVectorCode (state : Fin 117) : Nat :=
  if state.val < 32 then packedStateVectorCodeChunk0 state.val else
    if state.val < 64 then packedStateVectorCodeChunk1 (state.val - 32) else
      if state.val < 96 then packedStateVectorCodeChunk2 (state.val - 64) else
        packedStateVectorCodeChunk3 (state.val - 96)

def stateVector (state : Fin 117)
    (coordinate : Fin 8) : Fin 6 :=
  ⟨(packedStateVectorCode state / 6 ^ coordinate.val) % 6,
    Nat.mod_lt _ (by decide)⟩

def generatorVector (generator : Fin 3)
    (coordinate : Fin 8) : Fin 6 :=
  match generator.val with
  | 0 =>
      match coordinate.val with
      | 0 => (2 : Fin 6)
      | 1 => (5 : Fin 6)
      | 2 => (5 : Fin 6)
      | 3 => (3 : Fin 6)
      | 4 => (2 : Fin 6)
      | 5 => (5 : Fin 6)
      | 6 => (2 : Fin 6)
      | _ => (5 : Fin 6)
  | 1 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (2 : Fin 6)
      | 2 => (5 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (5 : Fin 6)
      | 5 => (3 : Fin 6)
      | 6 => (5 : Fin 6)
      | _ => (2 : Fin 6)
  | _ =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (2 : Fin 6)
      | 3 => (5 : Fin 6)
      | 4 => (3 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (5 : Fin 6)
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
  if code = 648 then (112 : Fin 117) else
  if code = 684 then (86 : Fin 117) else
  if code = 3888 then (116 : Fin 117) else
  if code = 3924 then (107 : Fin 117) else
  if code = 4536 then (115 : Fin 117) else
  if code = 4572 then (102 : Fin 117) else
  if code = 23328 then (113 : Fin 117) else
  if code = 23364 then (93 : Fin 117) else
  if code = 23400 then (91 : Fin 117) else
  if code = 23508 then (54 : Fin 117) else
  if code = 23976 then (111 : Fin 117) else
  if code = 24012 then (83 : Fin 117) else
  if code = 24048 then (81 : Fin 117) else
  if code = 24156 then (40 : Fin 117) else
  if code = 27216 then (114 : Fin 117) else
  if code = 27252 then (96 : Fin 117) else
  if code = 48601 then (90 : Fin 117) else
  if code = 48637 then (50 : Fin 117) else
  if code = 51841 then (109 : Fin 117) else
  if code = 51877 then (75 : Fin 117) else
  if code = 52489 then (105 : Fin 117) else
  if code = 52525 then (71 : Fin 117) else
  if code = 71281 then (95 : Fin 117) else
  if code = 71317 then (58 : Fin 117) else
  if code = 71353 then (56 : Fin 117) else
  if code = 71461 then (22 : Fin 117) else
  if code = 71929 then (89 : Fin 117) else
  if code = 71965 then (47 : Fin 117) else
  if code = 72001 then (45 : Fin 117) else
  if code = 72109 then (16 : Fin 117) else
  if code = 75169 then (98 : Fin 117) else
  if code = 75205 then (64 : Fin 117) else
  (0 : Fin 117)

private def decodeStateCodeChunk1 (code : Nat) : Fin 117 :=
  if code = 98497 then (110 : Fin 117) else
  if code = 98533 then (77 : Fin 117) else
  if code = 119413 then (24 : Fin 117) else
  if code = 121825 then (99 : Fin 117) else
  if code = 121861 then (60 : Fin 117) else
  if code = 237168 then (79 : Fin 117) else
  if code = 237204 then (34 : Fin 117) else
  if code = 260496 then (62 : Fin 117) else
  if code = 260532 then (28 : Fin 117) else
  if code = 260568 then (26 : Fin 117) else
  if code = 263268 then (7 : Fin 117) else
  if code = 280806 then (87 : Fin 117) else
  if code = 280842 then (49 : Fin 117) else
  if code = 284046 then (108 : Fin 117) else
  if code = 284082 then (74 : Fin 117) else
  if code = 284694 then (103 : Fin 117) else
  if code = 284730 then (70 : Fin 117) else
  if code = 303486 then (94 : Fin 117) else
  if code = 303522 then (57 : Fin 117) else
  if code = 303558 then (55 : Fin 117) else
  if code = 303666 then (21 : Fin 117) else
  if code = 304134 then (84 : Fin 117) else
  if code = 304170 then (46 : Fin 117) else
  if code = 304206 then (41 : Fin 117) else
  if code = 304314 then (15 : Fin 117) else
  if code = 307374 then (100 : Fin 117) else
  if code = 307410 then (63 : Fin 117) else
  if code = 328759 then (51 : Fin 117) else
  if code = 328795 then (85 : Fin 117) else
  if code = 331999 then (76 : Fin 117) else
  if code = 332035 then (106 : Fin 117) else
  if code = 332647 then (72 : Fin 117) else
  (0 : Fin 117)

private def decodeStateCodeChunk2 (code : Nat) : Fin 117 :=
  if code = 332683 then (101 : Fin 117) else
  if code = 351439 then (59 : Fin 117) else
  if code = 351475 then (92 : Fin 117) else
  if code = 351511 then (23 : Fin 117) else
  if code = 351619 then (53 : Fin 117) else
  if code = 352087 then (48 : Fin 117) else
  if code = 352123 then (82 : Fin 117) else
  if code = 352159 then (17 : Fin 117) else
  if code = 352267 then (39 : Fin 117) else
  if code = 355327 then (65 : Fin 117) else
  if code = 355363 then (97 : Fin 117) else
  if code = 378655 then (80 : Fin 117) else
  if code = 378691 then (33 : Fin 117) else
  if code = 399571 then (6 : Fin 117) else
  if code = 401983 then (66 : Fin 117) else
  if code = 402019 then (27 : Fin 117) else
  if code = 517326 then (35 : Fin 117) else
  if code = 517362 then (78 : Fin 117) else
  if code = 540654 then (29 : Fin 117) else
  if code = 540690 then (61 : Fin 117) else
  if code = 540726 then (8 : Fin 117) else
  if code = 543426 then (25 : Fin 117) else
  if code = 560742 then (88 : Fin 117) else
  if code = 560778 then (43 : Fin 117) else
  if code = 564630 then (104 : Fin 117) else
  if code = 564666 then (68 : Fin 117) else
  if code = 584256 then (13 : Fin 117) else
  if code = 608695 then (52 : Fin 117) else
  if code = 608731 then (19 : Fin 117) else
  if code = 612583 then (73 : Fin 117) else
  if code = 612619 then (31 : Fin 117) else
  if code = 632209 then (4 : Fin 117) else
  (0 : Fin 117)

private def decodeStateCodeChunk3 (code : Nat) : Fin 117 :=
  if code = 797478 then (37 : Fin 117) else
  if code = 797514 then (10 : Fin 117) else
  if code = 823584 then (1 : Fin 117) else
  if code = 1400328 then (44 : Fin 117) else
  if code = 1400364 then (18 : Fin 117) else
  if code = 1400400 then (14 : Fin 117) else
  if code = 1404216 then (69 : Fin 117) else
  if code = 1404252 then (30 : Fin 117) else
  if code = 1439418 then (3 : Fin 117) else
  if code = 1448281 then (20 : Fin 117) else
  if code = 1448317 then (42 : Fin 117) else
  if code = 1448353 then (5 : Fin 117) else
  if code = 1452169 then (32 : Fin 117) else
  if code = 1452205 then (67 : Fin 117) else
  if code = 1487371 then (12 : Fin 117) else
  if code = 1498825 then (36 : Fin 117) else
  if code = 1498861 then (9 : Fin 117) else
  if code = 1535324 then (0 : Fin 117) else
  if code = 1637928 then (11 : Fin 117) else
  if code = 1637964 then (38 : Fin 117) else
  if code = 1638000 then (2 : Fin 117) else
  (0 : Fin 117)

private def stateVectorCode
    (vector : Fin 8 -> Fin 6) : Nat :=
  (vector (0 : Fin 8)).val + 6 * ((vector (1 : Fin 8)).val + 6 * ((vector (2 : Fin 8)).val + 6 * ((vector (3 : Fin 8)).val + 6 * ((vector (4 : Fin 8)).val + 6 * ((vector (5 : Fin 8)).val + 6 * ((vector (6 : Fin 8)).val + 6 * ((vector (7 : Fin 8)).val)))))))

private def decodeStateCode (code : Nat) : Fin 117 :=
  if code < 98497 then decodeStateCodeChunk0 code else
  if code < 332683 then decodeStateCodeChunk1 code else
  if code < 797478 then decodeStateCodeChunk2 code else
  decodeStateCodeChunk3 code

private def decodeState
    (vector : Fin 8 -> Fin 6) : Fin 117 :=
  decodeStateCode (stateVectorCode vector)

set_option maxHeartbeats 2000000 in
private theorem decodeState_stateVector (state : Fin 117) :
    decodeState (stateVector state) = state := by
  decide +revert

set_option maxHeartbeats 2000000 in
private theorem transitionMap :
    forall (state : Fin 117)
      (generator : Fin 3)
      (coordinate : Fin 8),
      stateVector (transition state generator) coordinate =
        oppositeTable.semigroup.mul (stateVector state coordinate)
          (generatorVector generator coordinate) := by
  intro state generator coordinate
  apply Fin.ext
  exact by decide +revert

set_option maxHeartbeats 2000000 in
private theorem representativeMap :
    forall (state : Fin 117)
      (coordinate : Fin 8),
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
    (I := Fin 8) oppositeTable.semigroup where
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
        (Fin 8) targetValid
    have subValid :=
      powerCertificate.embedding.pullback_identity identity powerValid
    exact quotient.pushforwardIdentity identity subValid

/-- First-layer generic-CAS basis wrapper for `S6_6980`. -/
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

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6980
