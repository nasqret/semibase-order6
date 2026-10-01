import SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6494Representative
import SemigroupBasis.FiniteNilpotentCounterexample
import SemigroupBasis.Nonfinite
import SemigroupBasis.Opposite
import SemigroupBasis.RightGeneratedPowerCertificate

set_option maxRecDepth 2048

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9025

open SemigroupBasis

def routeManifestRowSHA256 : String := "4e784e32f961d524e53658c24a4967246bd4ca53f6b6e09b5430f1d0520bc029"
def witnessRecordSHA256 : String := "a8be514dc5251d988c4ae775e67646446e545c66b750d322f674161a14e1d6ca"
def transferComponentSHA256 : String := "a8be514dc5251d988c4ae775e67646446e545c66b750d322f674161a14e1d6ca"
def powerCertificateSHA256 : String := "1522d01251be60b609deaca11b42b024a8cc9e56390196f3d30ea3ac4a19a6af"

private def row6
    (c0 c1 c2 c3 c4 c5 : Fin 6) (column : Fin 6) : Fin 6 :=
  if column = 0 then c0 else
    if column = 1 then c1 else
      if column = 2 then c2 else
        if column = 3 then c3 else
          if column = 4 then c4 else c5

/-- Exact one-based catalogue table committed by the portable witness. -/
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 1 1 0 0 0 right else
    if left = 1 then row6 1 0 0 1 1 1 right else
      if left = 2 then row6 1 0 0 2 2 2 right else
        if left = 3 then row6 0 1 2 3 3 5 right else
          if left = 4 then row6 0 1 2 3 4 5 right else
            row6 0 1 2 3 5 5 right

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
  "63b6b35ab2405986be215a29c995fc68ebdd1cd12a025db4fefbb801419d715f"

private def packedStateVectorCodeChunk0 (index : Nat) : Nat :=
  match index with
  | 0 => 9797096
  | 1 => 6652272
  | 2 => 7726176
  | 3 => 9796662
  | 4 => 10073137
  | 5 => 9517033
  | 6 => 6698281
  | 7 => 6649668
  | 8 => 6605574
  | 9 => 9405577
  | 10 => 6045270
  | 11 => 7726104
  | 12 => 9796879
  | 13 => 10072704
  | 14 => 9516600
  | 15 => 10070533
  | 16 => 10073023
  | 17 => 9513151
  | 18 => 9516961
  | 19 => 6697848
  | 20 => 6695677
  | 21 => 6698239
  | 22 => 6650970
  | 23 => 6602976
  | 24 => 6604927
  | 25 => 6605502
  | 26 => 9405144
  | 27 => 9404287
  | 28 => 9405505
  | 29 => 6045055
  | 30 => 6042672
  | _ => 6045198

private def packedStateVectorCodeChunk1 (index : Nat) : Nat :=
  match index with
  | 0 => 7726140
  | 1 => 10072921
  | 2 => 9516817
  | 3 => 10070100
  | 4 => 10072590
  | 5 => 9512718
  | 6 => 9516528
  | 7 => 10071835
  | 8 => 10070425
  | 9 => 10072951
  | 10 => 9510553
  | 11 => 9513079
  | 12 => 9516997
  | 13 => 6698065
  | 14 => 6695244
  | 15 => 6697806
  | 16 => 6696979
  | 17 => 6695641
  | 18 => 6698167
  | 19 => 6604278
  | 20 => 6602329
  | 21 => 6602904
  | 22 => 6604494
  | 23 => 6604855
  | 24 => 6605538
  | 25 => 9405361
  | 26 => 9403854
  | 27 => 9405072
  | 28 => 9401689
  | 29 => 9404215
  | 30 => 9405541
  | _ => 6044622

private def packedStateVectorCodeChunk2 (index : Nat) : Nat :=
  match index with
  | 0 => 6042457
  | 1 => 6044983
  | 2 => 6043974
  | 3 => 6042600
  | 4 => 6045234
  | 5 => 10070317
  | 6 => 10072807
  | 7 => 9512935
  | 8 => 9516745
  | 9 => 10071402
  | 10 => 10069992
  | 11 => 10072518
  | 12 => 9510120
  | 13 => 9512646
  | 14 => 9516564
  | 15 => 10071727
  | 16 => 10070353
  | 17 => 10072987
  | 18 => 9511855
  | 19 => 9510481
  | 20 => 9513115
  | 21 => 6695461
  | 22 => 6698023
  | 23 => 6696546
  | 24 => 6695208
  | 25 => 6697734
  | 26 => 6696943
  | 27 => 6695569
  | 28 => 6698203
  | 29 => 6603631
  | 30 => 6604206
  | _ => 6601896

private def packedStateVectorCodeChunk3 (index : Nat) : Nat :=
  match index with
  | 0 => 6602257
  | 1 => 6602940
  | 2 => 6604711
  | 3 => 6604422
  | 4 => 6604891
  | 5 => 9404071
  | 6 => 9405289
  | 7 => 9401256
  | 8 => 9403782
  | 9 => 9405108
  | 10 => 9402991
  | 11 => 9401617
  | 12 => 9404251
  | 13 => 6044839
  | 14 => 6042024
  | 15 => 6044550
  | 16 => 6043759
  | 17 => 6042385
  | 18 => 6045019
  | 19 => 6043902
  | 20 => 6042636
  | 21 => 10071619
  | 22 => 10070209
  | 23 => 10072735
  | 24 => 9510337
  | 25 => 9512863
  | 26 => 9516781
  | 27 => 10071294
  | 28 => 10069920
  | 29 => 10072554
  | 30 => 9511422
  | _ => 9510048

private def packedStateVectorCodeChunk4 (index : Nat) : Nat :=
  match index with
  | 0 => 9512682
  | 1 => 10071655
  | 2 => 10070389
  | 3 => 9511783
  | 4 => 9510517
  | 5 => 6696763
  | 6 => 6695425
  | 7 => 6697951
  | 8 => 6696510
  | 9 => 6695136
  | 10 => 6697770
  | 11 => 6696871
  | 12 => 6695605
  | 13 => 6603198
  | 14 => 6603559
  | 15 => 6604242
  | 16 => 6602113
  | 17 => 6601824
  | 18 => 6602293
  | 19 => 6604639
  | 20 => 6604458
  | 21 => 9401473
  | 22 => 9403999
  | 23 => 9405325
  | 24 => 9402558
  | 25 => 9401184
  | 26 => 9403818
  | 27 => 9402919
  | 28 => 9401653
  | 29 => 6042241
  | 30 => 6044767
  | _ => 6043326

private def packedStateVectorCodeChunk5 (index : Nat) : Nat :=
  match index with
  | 0 => 6041952
  | 1 => 6044586
  | 2 => 6043687
  | 3 => 6042421
  | 4 => 6043938
  | 5 => 10071511
  | 6 => 10070137
  | 7 => 10072771
  | 8 => 9511639
  | 9 => 9510265
  | 10 => 9512899
  | 11 => 10071222
  | 12 => 10069956
  | 13 => 9511350
  | 14 => 9510084
  | 15 => 10071691
  | 16 => 9511819
  | 17 => 6696727
  | 18 => 6695353
  | 19 => 6697987
  | 20 => 6696438
  | 21 => 6695172
  | 22 => 6696907
  | 23 => 6603415
  | 24 => 6603126
  | 25 => 6603595
  | 26 => 6602041
  | 27 => 6601860
  | 28 => 6604675
  | 29 => 9402775
  | 30 => 9401401
  | _ => 9404035

private def packedStateVectorCodeChunk6 (index : Nat) : Nat :=
  match index with
  | 0 => 9402486
  | 1 => 9401220
  | 2 => 9402955
  | 3 => 6043543
  | 4 => 6042169
  | 5 => 6044803
  | 6 => 6043254
  | 7 => 6041988
  | 8 => 6043723
  | 9 => 10071439
  | 10 => 10070173
  | 11 => 9511567
  | 12 => 9510301
  | 13 => 10071258
  | 14 => 9511386
  | 15 => 6696655
  | 16 => 6695389
  | 17 => 6696474
  | 18 => 6603343
  | 19 => 6603162
  | 20 => 6602077
  | 21 => 9402703
  | 22 => 9401437
  | 23 => 9402522
  | 24 => 6043471
  | 25 => 6042205
  | 26 => 6043290
  | 27 => 10071475
  | 28 => 9511603
  | 29 => 6696691
  | 30 => 6603379
  | _ => 9402739

private def packedStateVectorCodeChunk7 (index : Nat) : Nat :=
  match index with
  | _ => 6043507

private def packedStateVectorCode (state : Fin 225) : Nat :=
  if state.val < 32 then packedStateVectorCodeChunk0 state.val else
    if state.val < 64 then packedStateVectorCodeChunk1 (state.val - 32) else
      if state.val < 96 then packedStateVectorCodeChunk2 (state.val - 64) else
        if state.val < 128 then packedStateVectorCodeChunk3 (state.val - 96) else
          if state.val < 160 then packedStateVectorCodeChunk4 (state.val - 128) else
            if state.val < 192 then packedStateVectorCodeChunk5 (state.val - 160) else
              if state.val < 224 then packedStateVectorCodeChunk6 (state.val - 192) else
                packedStateVectorCodeChunk7 (state.val - 224)

def stateVector (state : Fin 225)
    (coordinate : Fin 9) : Fin 6 :=
  ⟨(packedStateVectorCode state / 6 ^ coordinate.val) % 6,
    Nat.mod_lt _ (by decide)⟩

def generatorVector (generator : Fin 3)
    (coordinate : Fin 9) : Fin 6 :=
  match generator.val with
  | 0 =>
      match coordinate.val with
      | 0 => (2 : Fin 6)
      | 1 => (3 : Fin 6)
      | 2 => (5 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (5 : Fin 6)
      | 5 => (5 : Fin 6)
      | 6 => (5 : Fin 6)
      | 7 => (4 : Fin 6)
      | _ => (5 : Fin 6)
  | 1 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (2 : Fin 6)
      | 2 => (3 : Fin 6)
      | 3 => (5 : Fin 6)
      | 4 => (2 : Fin 6)
      | 5 => (3 : Fin 6)
      | 6 => (4 : Fin 6)
      | 7 => (5 : Fin 6)
      | _ => (3 : Fin 6)
  | _ =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (2 : Fin 6)
      | 3 => (3 : Fin 6)
      | 4 => (3 : Fin 6)
      | 5 => (3 : Fin 6)
      | 6 => (3 : Fin 6)
      | 7 => (3 : Fin 6)
      | _ => (4 : Fin 6)

private def packedTransitionCodeChunk0 (index : Nat) : Nat :=
  match index with
  | 0 => 254028
  | 1 => 406581
  | 2 => 559134
  | 3 => 711687
  | 4 => 813388
  | 5 => 915089
  | 6 => 1067644
  | 7 => 1169345
  | 8 => 1270824
  | 9 => 1423601
  | 10 => 1576154
  | 11 => 1627003
  | 12 => 1728678
  | 13 => 1830408
  | 14 => 1932109
  | 15 => 2033810
  | 16 => 2084661
  | 17 => 2186362
  | 18 => 2237213
  | 19 => 2389770
  | 20 => 2491471
  | 21 => 2542322
  | 22 => 2583498
  | 23 => 2694652
  | 24 => 2796129
  | 25 => 2846980
  | 26 => 2999982
  | 27 => 3101683
  | 28 => 3152534
  | 29 => 3305088
  | 30 => 3406789
  | _ => 3457640

private def packedTransitionCodeChunk1 (index : Nat) : Nat :=
  match index with
  | 0 => 572237
  | 1 => 3559288
  | 2 => 3660989
  | 3 => 3762744
  | 4 => 3813595
  | 5 => 3915296
  | 6 => 3966147
  | 7 => 4002823
  | 8 => 4067849
  | 9 => 4118700
  | 10 => 4220401
  | 11 => 4271252
  | 12 => 930228
  | 13 => 4372894
  | 14 => 4474660
  | 15 => 4525511
  | 16 => 4560837
  | 17 => 4627213
  | 18 => 4678064
  | 19 => 4764018
  | 20 => 4881020
  | 21 => 4931871
  | 22 => 5033348
  | 23 => 5084199
  | 24 => 1287550
  | 25 => 5186501
  | 26 => 5288276
  | 27 => 5339127
  | 28 => 5440828
  | 29 => 5491679
  | 30 => 1441905
  | _ => 5644234

private def packedTransitionCodeChunk2 (index : Nat) : Nat :=
  match index with
  | 0 => 5745935
  | 1 => 5796786
  | 2 => 5828737
  | 3 => 5898488
  | 4 => 1595589
  | 5 => 6000110
  | 6 => 6050961
  | 7 => 6152662
  | 8 => 6203513
  | 9 => 6234867
  | 10 => 6305293
  | 11 => 6356144
  | 12 => 6457845
  | 13 => 6508696
  | 14 => 1952672
  | 15 => 6539748
  | 16 => 6610399
  | 17 => 2105000
  | 18 => 6641451
  | 19 => 6712102
  | 20 => 2206703
  | 21 => 6813721
  | 22 => 6864572
  | 23 => 6895483
  | 24 => 6966359
  | 25 => 7017210
  | 26 => 7048036
  | 27 => 7118912
  | 28 => 2562888
  | 29 => 7200591
  | 30 => 7251442
  | _ => 7372494

private def packedTransitionCodeChunk3 (index : Nat) : Nat :=
  match index with
  | 0 => 7423345
  | 1 => 2715446
  | 2 => 7474329
  | 3 => 7525272
  | 4 => 2817373
  | 5 => 7627333
  | 6 => 7678184
  | 7 => 7779974
  | 8 => 7830825
  | 9 => 3021676
  | 10 => 7860527
  | 11 => 7932528
  | 12 => 3123379
  | 13 => 8034138
  | 14 => 8135932
  | 15 => 8186783
  | 16 => 8215809
  | 17 => 8288485
  | 18 => 3327461
  | 19 => 8317737
  | 20 => 3428938
  | 21 => 8368723
  | 22 => 8440949
  | 23 => 8491800
  | 24 => 8593501
  | 25 => 8644352
  | 26 => 3683328
  | 27 => 8673690
  | 28 => 8746141
  | 29 => 3835742
  | 30 => 8775393
  | _ => 8847844

private def packedTransitionCodeChunk4 (index : Nat) : Nat :=
  match index with
  | 0 => 3937445
  | 1 => 8877546
  | 2 => 4089547
  | 3 => 8928848
  | 4 => 4241649
  | 5 => 8979837
  | 6 => 9051163
  | 7 => 9102014
  | 8 => 9132477
  | 9 => 9203803
  | 10 => 4546529
  | 11 => 9234405
  | 12 => 4648006
  | 13 => 9336558
  | 14 => 9387409
  | 15 => 4780760
  | 16 => 9457520
  | 17 => 9508461
  | 18 => 4901812
  | 19 => 9559449
  | 20 => 5054138
  | 21 => 9661378
  | 22 => 9712229
  | 23 => 5206830
  | 24 => 9743364
  | 25 => 9814015
  | 26 => 5308616
  | 27 => 9845517
  | 28 => 5460718
  | 29 => 9966485
  | 30 => 10017336
  | _ => 10048695

private def packedTransitionCodeChunk5 (index : Nat) : Nat :=
  match index with
  | 0 => 10119121
  | 1 => 5664347
  | 2 => 10150623
  | 3 => 5765824
  | 4 => 5848175
  | 5 => 10202298
  | 6 => 10271599
  | 7 => 6069950
  | 8 => 10304001
  | 9 => 10373302
  | 10 => 6171653
  | 11 => 10406226
  | 12 => 6323827
  | 13 => 10457528
  | 14 => 6475929
  | 15 => 6560080
  | 16 => 6661781
  | 17 => 10509661
  | 18 => 10576712
  | 19 => 6881313
  | 20 => 10611657
  | 21 => 6982858
  | 22 => 7068584
  | 23 => 10663791
  | 24 => 10714710
  | 25 => 7221811
  | 26 => 10779895
  | 27 => 7388312
  | 28 => 7489723
  | 29 => 10816802
  | 30 => 10881828
  | _ => 7642054

private def packedTransitionCodeChunk6 (index : Nat) : Nat :=
  match index with
  | 0 => 10919013
  | 1 => 7794214
  | 2 => 7882190
  | 3 => 10970484
  | 4 => 11034385
  | 5 => 8047736
  | 6 => 11072466
  | 7 => 8149267
  | 8 => 8238143
  | 9 => 11124396
  | 10 => 8453197
  | 11 => 11175698
  | 12 => 8605299
  | 13 => 8695794
  | 14 => 8797495
  | 15 => 11228355
  | 16 => 9061156
  | 17 => 9153446
  | 18 => 11280784
  | 19 => 9357297
  | 20 => 9466387
  | 21 => 11332317
  | 22 => 9669118
  | 23 => 9763648
  | 24 => 11384298
  | 25 => 9973099
  | 26 => 10068749
  | 27 => 10221280
  | 28 => 10322981
  | 29 => 10526384
  | 30 => 10679161
  | _ => 10831490

private def packedTransitionCodeChunk7 (index : Nat) : Nat :=
  match index with
  | _ => 10984043

private def packedTransitionCode (state : Fin 225) : Nat :=
  if state.val < 32 then packedTransitionCodeChunk0 state.val else
    if state.val < 64 then packedTransitionCodeChunk1 (state.val - 32) else
      if state.val < 96 then packedTransitionCodeChunk2 (state.val - 64) else
        if state.val < 128 then packedTransitionCodeChunk3 (state.val - 96) else
          if state.val < 160 then packedTransitionCodeChunk4 (state.val - 128) else
            if state.val < 192 then packedTransitionCodeChunk5 (state.val - 160) else
              if state.val < 224 then packedTransitionCodeChunk6 (state.val - 192) else
                packedTransitionCodeChunk7 (state.val - 224)

def transition (state : Fin 225)
    (generator : Fin 3) : Fin 225 :=
  ⟨(packedTransitionCode state / 225 ^ generator.val) % 225,
    Nat.mod_lt _ (by decide)⟩

private def packedRepresentativeHeadBlockCode (index : Nat) : Nat :=
  match index with
  | 0 => 3432898797365820648365665004559
  | 1 => 19383245442538061721121682
  | 2 => 3370096963230473847978303465078
  | _ => 5223529039884722

def representativeHead (state : Fin 225) : Fin 3 :=
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
  | 7 => [1, 1, 1]
  | 8 => [1, 1, 2]
  | 9 => [1, 2, 2]
  | 10 => [2, 1, 1]
  | 11 => [2, 1, 2]
  | 12 => [2, 2, 2]
  | 13 => [0, 0, 0]
  | 14 => [0, 0, 1]
  | 15 => [0, 0, 2]
  | 16 => [0, 1, 1]
  | 17 => [0, 1, 2]
  | 18 => [0, 2, 2]
  | 19 => [1, 1, 2]
  | 20 => [1, 2, 0]
  | 21 => [1, 2, 2]
  | 22 => [2, 0, 0]
  | 23 => [2, 0, 2]
  | 24 => [2, 2, 2]
  | 25 => [0, 0, 0]
  | 26 => [0, 0, 1]
  | 27 => [0, 0, 2]
  | 28 => [0, 1, 1]
  | 29 => [0, 1, 2]
  | 30 => [0, 2, 2]
  | _ => [1, 0, 0]

private def representativeTailChunk2 (index : Nat) :
    List (Fin 3) :=
  match index with
  | 0 => [1, 0, 1]
  | 1 => [1, 0, 2]
  | 2 => [1, 1, 1]
  | 3 => [1, 1, 2]
  | 4 => [1, 2, 2]
  | 5 => [0, 0, 1, 1]
  | 6 => [0, 0, 1, 2]
  | 7 => [0, 0, 2, 1]
  | 8 => [0, 0, 2, 2]
  | 9 => [0, 1, 1, 1]
  | 10 => [0, 1, 1, 2]
  | 11 => [0, 1, 2, 2]
  | 12 => [0, 2, 1, 1]
  | 13 => [0, 2, 1, 2]
  | 14 => [0, 2, 2, 2]
  | 15 => [1, 1, 1, 2]
  | 16 => [1, 1, 2, 2]
  | 17 => [1, 2, 2, 2]
  | 18 => [2, 1, 1, 1]
  | 19 => [2, 1, 1, 2]
  | 20 => [2, 1, 2, 2]
  | 21 => [0, 0, 0, 1]
  | 22 => [0, 0, 0, 2]
  | 23 => [0, 0, 1, 1]
  | 24 => [0, 0, 1, 2]
  | 25 => [0, 0, 2, 2]
  | 26 => [0, 1, 1, 2]
  | 27 => [0, 1, 2, 2]
  | 28 => [0, 2, 2, 2]
  | 29 => [1, 1, 2, 0]
  | 30 => [1, 1, 2, 2]
  | _ => [1, 2, 0, 0]

private def representativeTailChunk3 (index : Nat) :
    List (Fin 3) :=
  match index with
  | 0 => [1, 2, 0, 2]
  | 1 => [1, 2, 2, 2]
  | 2 => [2, 0, 0, 0]
  | 3 => [2, 0, 0, 2]
  | 4 => [2, 0, 2, 2]
  | 5 => [0, 0, 0, 1]
  | 6 => [0, 0, 0, 2]
  | 7 => [0, 0, 1, 1]
  | 8 => [0, 0, 1, 2]
  | 9 => [0, 0, 2, 2]
  | 10 => [0, 1, 1, 1]
  | 11 => [0, 1, 1, 2]
  | 12 => [0, 1, 2, 2]
  | 13 => [1, 0, 0, 0]
  | 14 => [1, 0, 0, 1]
  | 15 => [1, 0, 0, 2]
  | 16 => [1, 0, 1, 1]
  | 17 => [1, 0, 1, 2]
  | 18 => [1, 0, 2, 2]
  | 19 => [1, 1, 1, 2]
  | 20 => [1, 1, 2, 2]
  | 21 => [0, 0, 1, 1, 1]
  | 22 => [0, 0, 1, 1, 2]
  | 23 => [0, 0, 1, 2, 2]
  | 24 => [0, 0, 2, 1, 1]
  | 25 => [0, 0, 2, 1, 2]
  | 26 => [0, 0, 2, 2, 2]
  | 27 => [0, 1, 1, 1, 2]
  | 28 => [0, 1, 1, 2, 2]
  | 29 => [0, 1, 2, 2, 2]
  | 30 => [0, 2, 1, 1, 1]
  | _ => [0, 2, 1, 1, 2]

private def representativeTailChunk4 (index : Nat) :
    List (Fin 3) :=
  match index with
  | 0 => [0, 2, 1, 2, 2]
  | 1 => [1, 1, 1, 2, 2]
  | 2 => [1, 1, 2, 2, 2]
  | 3 => [2, 1, 1, 1, 2]
  | 4 => [2, 1, 1, 2, 2]
  | 5 => [0, 0, 0, 1, 1]
  | 6 => [0, 0, 0, 1, 2]
  | 7 => [0, 0, 0, 2, 2]
  | 8 => [0, 0, 1, 1, 2]
  | 9 => [0, 0, 1, 2, 2]
  | 10 => [0, 0, 2, 2, 2]
  | 11 => [0, 1, 1, 2, 2]
  | 12 => [0, 1, 2, 2, 2]
  | 13 => [1, 1, 2, 0, 0]
  | 14 => [1, 1, 2, 0, 2]
  | 15 => [1, 1, 2, 2, 2]
  | 16 => [1, 2, 0, 0, 0]
  | 17 => [1, 2, 0, 0, 2]
  | 18 => [1, 2, 0, 2, 2]
  | 19 => [2, 0, 0, 0, 2]
  | 20 => [2, 0, 0, 2, 2]
  | 21 => [0, 0, 0, 1, 1]
  | 22 => [0, 0, 0, 1, 2]
  | 23 => [0, 0, 0, 2, 2]
  | 24 => [0, 0, 1, 1, 1]
  | 25 => [0, 0, 1, 1, 2]
  | 26 => [0, 0, 1, 2, 2]
  | 27 => [0, 1, 1, 1, 2]
  | 28 => [0, 1, 1, 2, 2]
  | 29 => [1, 0, 0, 0, 1]
  | 30 => [1, 0, 0, 0, 2]
  | _ => [1, 0, 0, 1, 1]

private def representativeTailChunk5 (index : Nat) :
    List (Fin 3) :=
  match index with
  | 0 => [1, 0, 0, 1, 2]
  | 1 => [1, 0, 0, 2, 2]
  | 2 => [1, 0, 1, 1, 2]
  | 3 => [1, 0, 1, 2, 2]
  | 4 => [1, 1, 1, 2, 2]
  | 5 => [0, 0, 1, 1, 1, 2]
  | 6 => [0, 0, 1, 1, 2, 2]
  | 7 => [0, 0, 1, 2, 2, 2]
  | 8 => [0, 0, 2, 1, 1, 1]
  | 9 => [0, 0, 2, 1, 1, 2]
  | 10 => [0, 0, 2, 1, 2, 2]
  | 11 => [0, 1, 1, 1, 2, 2]
  | 12 => [0, 1, 1, 2, 2, 2]
  | 13 => [0, 2, 1, 1, 1, 2]
  | 14 => [0, 2, 1, 1, 2, 2]
  | 15 => [1, 1, 1, 2, 2, 2]
  | 16 => [2, 1, 1, 1, 2, 2]
  | 17 => [0, 0, 0, 1, 1, 2]
  | 18 => [0, 0, 0, 1, 2, 2]
  | 19 => [0, 0, 0, 2, 2, 2]
  | 20 => [0, 0, 1, 1, 2, 2]
  | 21 => [0, 0, 1, 2, 2, 2]
  | 22 => [0, 1, 1, 2, 2, 2]
  | 23 => [1, 1, 2, 0, 0, 0]
  | 24 => [1, 1, 2, 0, 0, 2]
  | 25 => [1, 1, 2, 0, 2, 2]
  | 26 => [1, 2, 0, 0, 0, 2]
  | 27 => [1, 2, 0, 0, 2, 2]
  | 28 => [2, 0, 0, 0, 2, 2]
  | 29 => [0, 0, 0, 1, 1, 1]
  | 30 => [0, 0, 0, 1, 1, 2]
  | _ => [0, 0, 0, 1, 2, 2]

private def representativeTailChunk6 (index : Nat) :
    List (Fin 3) :=
  match index with
  | 0 => [0, 0, 1, 1, 1, 2]
  | 1 => [0, 0, 1, 1, 2, 2]
  | 2 => [0, 1, 1, 1, 2, 2]
  | 3 => [1, 0, 0, 0, 1, 1]
  | 4 => [1, 0, 0, 0, 1, 2]
  | 5 => [1, 0, 0, 0, 2, 2]
  | 6 => [1, 0, 0, 1, 1, 2]
  | 7 => [1, 0, 0, 1, 2, 2]
  | 8 => [1, 0, 1, 1, 2, 2]
  | 9 => [0, 0, 1, 1, 1, 2, 2]
  | 10 => [0, 0, 1, 1, 2, 2, 2]
  | 11 => [0, 0, 2, 1, 1, 1, 2]
  | 12 => [0, 0, 2, 1, 1, 2, 2]
  | 13 => [0, 1, 1, 1, 2, 2, 2]
  | 14 => [0, 2, 1, 1, 1, 2, 2]
  | 15 => [0, 0, 0, 1, 1, 2, 2]
  | 16 => [0, 0, 0, 1, 2, 2, 2]
  | 17 => [0, 0, 1, 1, 2, 2, 2]
  | 18 => [1, 1, 2, 0, 0, 0, 2]
  | 19 => [1, 1, 2, 0, 0, 2, 2]
  | 20 => [1, 2, 0, 0, 0, 2, 2]
  | 21 => [0, 0, 0, 1, 1, 1, 2]
  | 22 => [0, 0, 0, 1, 1, 2, 2]
  | 23 => [0, 0, 1, 1, 1, 2, 2]
  | 24 => [1, 0, 0, 0, 1, 1, 2]
  | 25 => [1, 0, 0, 0, 1, 2, 2]
  | 26 => [1, 0, 0, 1, 1, 2, 2]
  | 27 => [0, 0, 1, 1, 1, 2, 2, 2]
  | 28 => [0, 0, 2, 1, 1, 1, 2, 2]
  | 29 => [0, 0, 0, 1, 1, 2, 2, 2]
  | 30 => [1, 1, 2, 0, 0, 0, 2, 2]
  | _ => [0, 0, 0, 1, 1, 1, 2, 2]

private def representativeTailChunk7 (index : Nat) :
    List (Fin 3) :=
  match index with
  | _ => [1, 0, 0, 0, 1, 1, 2, 2]

def representativeTail (state : Fin 225) :
    List (Fin 3) :=
  if state.val < 32 then representativeTailChunk0 state.val else
    if state.val < 64 then representativeTailChunk1 (state.val - 32) else
      if state.val < 96 then representativeTailChunk2 (state.val - 64) else
        if state.val < 128 then representativeTailChunk3 (state.val - 96) else
          if state.val < 160 then representativeTailChunk4 (state.val - 128) else
            if state.val < 192 then representativeTailChunk5 (state.val - 160) else
              if state.val < 224 then representativeTailChunk6 (state.val - 192) else
                representativeTailChunk7 (state.val - 224)

private def packedSourceLabelBlockCode (index : Nat) : Nat :=
  match index with
  | 0 => 9699375329577121196826383086546638490253
  | 1 => 63340286488384521773773249884739386198073515434436
  | 2 => 6285195213565943449012262589936762246291455
  | _ => 220050429453215835240960

def sourceLabel (state : Fin 225) : Fin 6 :=
  ⟨(packedSourceLabelBlockCode (state.val / 64) /
      6 ^ (state.val % 64)) % 6,
    Nat.mod_lt _ (by decide)⟩

def generatorSourceLabel (generator : Fin 3) : Fin 6 :=
  match generator.val with
  | 0 => (5 : Fin 6)
  | 1 => (4 : Fin 6)
  | _ => (2 : Fin 6)

def sourcePreimage (value : Fin 6) : Fin 225 :=
  match value.val with
  | 0 => (9 : Fin 225)
  | 1 => (8 : Fin 225)
  | 2 => (2 : Fin 225)
  | 3 => (7 : Fin 225)
  | 4 => (1 : Fin 225)
  | _ => (0 : Fin 225)

private def decodeStateCodeChunk0 (code : Nat) : Fin 225 :=
  if code = 6041952 then (160 : Fin 225) else
  if code = 6041988 then (199 : Fin 225) else
  if code = 6042024 then (110 : Fin 225) else
  if code = 6042169 then (196 : Fin 225) else
  if code = 6042205 then (217 : Fin 225) else
  if code = 6042241 then (157 : Fin 225) else
  if code = 6042385 then (113 : Fin 225) else
  if code = 6042421 then (163 : Fin 225) else
  if code = 6042457 then (64 : Fin 225) else
  if code = 6042600 then (67 : Fin 225) else
  if code = 6042636 then (116 : Fin 225) else
  if code = 6042672 then (30 : Fin 225) else
  if code = 6043254 then (198 : Fin 225) else
  if code = 6043290 then (218 : Fin 225) else
  if code = 6043326 then (159 : Fin 225) else
  if code = 6043471 then (216 : Fin 225) else
  if code = 6043507 then (224 : Fin 225) else
  if code = 6043543 then (195 : Fin 225) else
  if code = 6043687 then (162 : Fin 225) else
  if code = 6043723 then (200 : Fin 225) else
  if code = 6043759 then (112 : Fin 225) else
  if code = 6043902 then (115 : Fin 225) else
  if code = 6043938 then (164 : Fin 225) else
  if code = 6043974 then (66 : Fin 225) else
  if code = 6044550 then (111 : Fin 225) else
  if code = 6044586 then (161 : Fin 225) else
  if code = 6044622 then (63 : Fin 225) else
  if code = 6044767 then (158 : Fin 225) else
  if code = 6044803 then (197 : Fin 225) else
  if code = 6044839 then (109 : Fin 225) else
  if code = 6044983 then (65 : Fin 225) else
  if code = 6045019 then (114 : Fin 225) else
  (0 : Fin 225)

private def decodeStateCodeChunk1 (code : Nat) : Fin 225 :=
  if code = 6045055 then (29 : Fin 225) else
  if code = 6045198 then (31 : Fin 225) else
  if code = 6045234 then (68 : Fin 225) else
  if code = 6045270 then (10 : Fin 225) else
  if code = 6601824 then (145 : Fin 225) else
  if code = 6601860 then (187 : Fin 225) else
  if code = 6601896 then (95 : Fin 225) else
  if code = 6602041 then (186 : Fin 225) else
  if code = 6602077 then (212 : Fin 225) else
  if code = 6602113 then (144 : Fin 225) else
  if code = 6602257 then (96 : Fin 225) else
  if code = 6602293 then (146 : Fin 225) else
  if code = 6602329 then (52 : Fin 225) else
  if code = 6602904 then (53 : Fin 225) else
  if code = 6602940 then (97 : Fin 225) else
  if code = 6602976 then (23 : Fin 225) else
  if code = 6603126 then (184 : Fin 225) else
  if code = 6603162 then (211 : Fin 225) else
  if code = 6603198 then (141 : Fin 225) else
  if code = 6603343 then (210 : Fin 225) else
  if code = 6603379 then (222 : Fin 225) else
  if code = 6603415 then (183 : Fin 225) else
  if code = 6603559 then (142 : Fin 225) else
  if code = 6603595 then (185 : Fin 225) else
  if code = 6603631 then (93 : Fin 225) else
  if code = 6604206 then (94 : Fin 225) else
  if code = 6604242 then (143 : Fin 225) else
  if code = 6604278 then (51 : Fin 225) else
  if code = 6604422 then (99 : Fin 225) else
  if code = 6604458 then (148 : Fin 225) else
  if code = 6604494 then (54 : Fin 225) else
  if code = 6604639 then (147 : Fin 225) else
  (0 : Fin 225)

private def decodeStateCodeChunk2 (code : Nat) : Fin 225 :=
  if code = 6604675 then (188 : Fin 225) else
  if code = 6604711 then (98 : Fin 225) else
  if code = 6604855 then (55 : Fin 225) else
  if code = 6604891 then (100 : Fin 225) else
  if code = 6604927 then (24 : Fin 225) else
  if code = 6605502 then (25 : Fin 225) else
  if code = 6605538 then (56 : Fin 225) else
  if code = 6605574 then (8 : Fin 225) else
  if code = 6649668 then (7 : Fin 225) else
  if code = 6650970 then (22 : Fin 225) else
  if code = 6652272 then (1 : Fin 225) else
  if code = 6695136 then (137 : Fin 225) else
  if code = 6695172 then (181 : Fin 225) else
  if code = 6695208 then (88 : Fin 225) else
  if code = 6695244 then (46 : Fin 225) else
  if code = 6695353 then (178 : Fin 225) else
  if code = 6695389 then (208 : Fin 225) else
  if code = 6695425 then (134 : Fin 225) else
  if code = 6695461 then (85 : Fin 225) else
  if code = 6695569 then (91 : Fin 225) else
  if code = 6695605 then (140 : Fin 225) else
  if code = 6695641 then (49 : Fin 225) else
  if code = 6695677 then (20 : Fin 225) else
  if code = 6696438 then (180 : Fin 225) else
  if code = 6696474 then (209 : Fin 225) else
  if code = 6696510 then (136 : Fin 225) else
  if code = 6696546 then (87 : Fin 225) else
  if code = 6696655 then (207 : Fin 225) else
  if code = 6696691 then (221 : Fin 225) else
  if code = 6696727 then (177 : Fin 225) else
  if code = 6696763 then (133 : Fin 225) else
  if code = 6696871 then (139 : Fin 225) else
  (0 : Fin 225)

private def decodeStateCodeChunk3 (code : Nat) : Fin 225 :=
  if code = 6696907 then (182 : Fin 225) else
  if code = 6696943 then (90 : Fin 225) else
  if code = 6696979 then (48 : Fin 225) else
  if code = 6697734 then (89 : Fin 225) else
  if code = 6697770 then (138 : Fin 225) else
  if code = 6697806 then (47 : Fin 225) else
  if code = 6697848 then (19 : Fin 225) else
  if code = 6697951 then (135 : Fin 225) else
  if code = 6697987 then (179 : Fin 225) else
  if code = 6698023 then (86 : Fin 225) else
  if code = 6698065 then (45 : Fin 225) else
  if code = 6698167 then (50 : Fin 225) else
  if code = 6698203 then (92 : Fin 225) else
  if code = 6698239 then (21 : Fin 225) else
  if code = 6698281 then (6 : Fin 225) else
  if code = 7726104 then (11 : Fin 225) else
  if code = 7726140 then (32 : Fin 225) else
  if code = 7726176 then (2 : Fin 225) else
  if code = 9401184 then (153 : Fin 225) else
  if code = 9401220 then (193 : Fin 225) else
  if code = 9401256 then (103 : Fin 225) else
  if code = 9401401 then (190 : Fin 225) else
  if code = 9401437 then (214 : Fin 225) else
  if code = 9401473 then (149 : Fin 225) else
  if code = 9401617 then (107 : Fin 225) else
  if code = 9401653 then (156 : Fin 225) else
  if code = 9401689 then (60 : Fin 225) else
  if code = 9402486 then (192 : Fin 225) else
  if code = 9402522 then (215 : Fin 225) else
  if code = 9402558 then (152 : Fin 225) else
  if code = 9402703 then (213 : Fin 225) else
  if code = 9402739 then (223 : Fin 225) else
  (0 : Fin 225)

private def decodeStateCodeChunk4 (code : Nat) : Fin 225 :=
  if code = 9402775 then (189 : Fin 225) else
  if code = 9402919 then (155 : Fin 225) else
  if code = 9402955 then (194 : Fin 225) else
  if code = 9402991 then (106 : Fin 225) else
  if code = 9403782 then (104 : Fin 225) else
  if code = 9403818 then (154 : Fin 225) else
  if code = 9403854 then (58 : Fin 225) else
  if code = 9403999 then (150 : Fin 225) else
  if code = 9404035 then (191 : Fin 225) else
  if code = 9404071 then (101 : Fin 225) else
  if code = 9404215 then (61 : Fin 225) else
  if code = 9404251 then (108 : Fin 225) else
  if code = 9404287 then (27 : Fin 225) else
  if code = 9405072 then (59 : Fin 225) else
  if code = 9405108 then (105 : Fin 225) else
  if code = 9405144 then (26 : Fin 225) else
  if code = 9405289 then (102 : Fin 225) else
  if code = 9405325 then (151 : Fin 225) else
  if code = 9405361 then (57 : Fin 225) else
  if code = 9405505 then (28 : Fin 225) else
  if code = 9405541 then (62 : Fin 225) else
  if code = 9405577 then (9 : Fin 225) else
  if code = 9510048 then (127 : Fin 225) else
  if code = 9510084 then (174 : Fin 225) else
  if code = 9510120 then (76 : Fin 225) else
  if code = 9510265 then (169 : Fin 225) else
  if code = 9510301 then (204 : Fin 225) else
  if code = 9510337 then (120 : Fin 225) else
  if code = 9510481 then (83 : Fin 225) else
  if code = 9510517 then (132 : Fin 225) else
  if code = 9510553 then (42 : Fin 225) else
  if code = 9511350 then (173 : Fin 225) else
  (0 : Fin 225)

private def decodeStateCodeChunk5 (code : Nat) : Fin 225 :=
  if code = 9511386 then (206 : Fin 225) else
  if code = 9511422 then (126 : Fin 225) else
  if code = 9511567 then (203 : Fin 225) else
  if code = 9511603 then (220 : Fin 225) else
  if code = 9511639 then (168 : Fin 225) else
  if code = 9511783 then (131 : Fin 225) else
  if code = 9511819 then (176 : Fin 225) else
  if code = 9511855 then (82 : Fin 225) else
  if code = 9512646 then (77 : Fin 225) else
  if code = 9512682 then (128 : Fin 225) else
  if code = 9512718 then (37 : Fin 225) else
  if code = 9512863 then (121 : Fin 225) else
  if code = 9512899 then (170 : Fin 225) else
  if code = 9512935 then (71 : Fin 225) else
  if code = 9513079 then (43 : Fin 225) else
  if code = 9513115 then (84 : Fin 225) else
  if code = 9513151 then (17 : Fin 225) else
  if code = 9516528 then (38 : Fin 225) else
  if code = 9516564 then (78 : Fin 225) else
  if code = 9516600 then (14 : Fin 225) else
  if code = 9516745 then (72 : Fin 225) else
  if code = 9516781 then (122 : Fin 225) else
  if code = 9516817 then (34 : Fin 225) else
  if code = 9516961 then (18 : Fin 225) else
  if code = 9516997 then (44 : Fin 225) else
  if code = 9517033 then (5 : Fin 225) else
  if code = 9796662 then (3 : Fin 225) else
  if code = 9796879 then (12 : Fin 225) else
  if code = 9797096 then (0 : Fin 225) else
  if code = 10069920 then (124 : Fin 225) else
  if code = 10069956 then (172 : Fin 225) else
  if code = 10069992 then (74 : Fin 225) else
  (0 : Fin 225)

private def decodeStateCodeChunk6 (code : Nat) : Fin 225 :=
  if code = 10070100 then (35 : Fin 225) else
  if code = 10070137 then (166 : Fin 225) else
  if code = 10070173 then (202 : Fin 225) else
  if code = 10070209 then (118 : Fin 225) else
  if code = 10070317 then (69 : Fin 225) else
  if code = 10070353 then (80 : Fin 225) else
  if code = 10070389 then (130 : Fin 225) else
  if code = 10070425 then (40 : Fin 225) else
  if code = 10070533 then (15 : Fin 225) else
  if code = 10071222 then (171 : Fin 225) else
  if code = 10071258 then (205 : Fin 225) else
  if code = 10071294 then (123 : Fin 225) else
  if code = 10071402 then (73 : Fin 225) else
  if code = 10071439 then (201 : Fin 225) else
  if code = 10071475 then (219 : Fin 225) else
  if code = 10071511 then (165 : Fin 225) else
  if code = 10071619 then (117 : Fin 225) else
  if code = 10071655 then (129 : Fin 225) else
  if code = 10071691 then (175 : Fin 225) else
  if code = 10071727 then (79 : Fin 225) else
  if code = 10071835 then (39 : Fin 225) else
  if code = 10072518 then (75 : Fin 225) else
  if code = 10072554 then (125 : Fin 225) else
  if code = 10072590 then (36 : Fin 225) else
  if code = 10072704 then (13 : Fin 225) else
  if code = 10072735 then (119 : Fin 225) else
  if code = 10072771 then (167 : Fin 225) else
  if code = 10072807 then (70 : Fin 225) else
  if code = 10072921 then (33 : Fin 225) else
  if code = 10072951 then (41 : Fin 225) else
  if code = 10072987 then (81 : Fin 225) else
  if code = 10073023 then (16 : Fin 225) else
  (0 : Fin 225)

private def decodeStateCodeChunk7 (code : Nat) : Fin 225 :=
  if code = 10073137 then (4 : Fin 225) else
  (0 : Fin 225)

private def stateVectorCode
    (vector : Fin 9 -> Fin 6) : Nat :=
  (vector (0 : Fin 9)).val + 6 * ((vector (1 : Fin 9)).val + 6 * ((vector (2 : Fin 9)).val + 6 * ((vector (3 : Fin 9)).val + 6 * ((vector (4 : Fin 9)).val + 6 * ((vector (5 : Fin 9)).val + 6 * ((vector (6 : Fin 9)).val + 6 * ((vector (7 : Fin 9)).val + 6 * ((vector (8 : Fin 9)).val))))))))

private def decodeStateCode (code : Nat) : Fin 225 :=
  if code < 6045055 then decodeStateCodeChunk0 code else
  if code < 6604675 then decodeStateCodeChunk1 code else
  if code < 6696907 then decodeStateCodeChunk2 code else
  if code < 9402775 then decodeStateCodeChunk3 code else
  if code < 9511386 then decodeStateCodeChunk4 code else
  if code < 10070100 then decodeStateCodeChunk5 code else
  if code < 10073137 then decodeStateCodeChunk6 code else
  decodeStateCodeChunk7 code

private def decodeState
    (vector : Fin 9 -> Fin 6) : Fin 225 :=
  decodeStateCode (stateVectorCode vector)

set_option maxHeartbeats 2000000 in
private theorem decodeState_stateVector (state : Fin 225) :
    decodeState (stateVector state) = state := by
  decide +revert

set_option maxHeartbeats 2000000 in
private theorem transitionMap :
    forall (state : Fin 225)
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
    forall (state : Fin 225)
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
    (U := Fin 225)
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
    forall (state : Fin 225)
      (generator : Fin 3),
      sourceLabel (transition state generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6494Representative.sourceSemigroup.mul (sourceLabel state)
          (generatorSourceLabel generator) := by
  intro state generator
  apply Fin.ext
  exact by decide +revert

set_option maxHeartbeats 2000000 in
private theorem sourceLabelRepresentative :
    forall state : Fin 225,
      sourceLabel state =
        (representativeTail state).foldl
          (fun value generator =>
            SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6494Representative.sourceSemigroup.mul value
              (generatorSourceLabel generator))
          (generatorSourceLabel (representativeHead state)) := by
  intro state
  apply Fin.ext
  exact by decide +revert

private theorem sourceLabelRightMultiplyWord
    (state : Fin 225)
    (word : List (Fin 3)) :
    sourceLabel (powerCertificate.rightMultiplyWord state word) =
      word.foldl
        (fun value generator =>
          SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6494Representative.sourceSemigroup.mul value
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
              SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6494Representative.sourceSemigroup.mul value
                (generatorSourceLabel nextGenerator))
            (SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6494Representative.sourceSemigroup.mul (sourceLabel state)
              (generatorSourceLabel generator))
      rw [inductionHypothesis]
      rw [sourceLabelTransition]

private theorem sourceFoldlGeneratorAssoc
    (left right : Fin 6)
    (word : List (Fin 3)) :
    word.foldl
        (fun value generator =>
          SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6494Representative.sourceSemigroup.mul value
            (generatorSourceLabel generator))
        (SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6494Representative.sourceSemigroup.mul left right) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6494Representative.sourceSemigroup.mul left
        (word.foldl
          (fun value generator =>
            SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6494Representative.sourceSemigroup.mul value
              (generatorSourceLabel generator))
          right) := by
  induction word generalizing right with
  | nil => rfl
  | cons generator word inductionHypothesis =>
      simp only [List.foldl_cons]
      rw [SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6494Representative.sourceSemigroup.assoc]
      exact inductionHypothesis
        (SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6494Representative.sourceSemigroup.mul right (generatorSourceLabel generator))

private theorem sourceLabelMapMul :
    forall (left right : Fin 225),
      sourceLabel (powerCertificate.semigroup.mul left right) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6494Representative.sourceSemigroup.mul (sourceLabel left) (sourceLabel right) := by
  intro left right
  calc
    sourceLabel (powerCertificate.semigroup.mul left right) =
        sourceLabel
          (powerCertificate.rightMultiplyWord
            (transition left (representativeHead right))
            (representativeTail right)) := rfl
    _ = (representativeTail right).foldl
          (fun value generator =>
            SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6494Representative.sourceSemigroup.mul value
              (generatorSourceLabel generator))
          (sourceLabel (transition left (representativeHead right))) :=
      sourceLabelRightMultiplyWord _ _
    _ = (representativeTail right).foldl
          (fun value generator =>
            SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6494Representative.sourceSemigroup.mul value
              (generatorSourceLabel generator))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6494Representative.sourceSemigroup.mul (sourceLabel left)
            (generatorSourceLabel (representativeHead right))) :=
      congrArg
        (fun initial =>
          (representativeTail right).foldl
            (fun value generator =>
              SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6494Representative.sourceSemigroup.mul value
                (generatorSourceLabel generator))
            initial)
        (sourceLabelTransition left (representativeHead right))
    _ = SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6494Representative.sourceSemigroup.mul (sourceLabel left)
          ((representativeTail right).foldl
            (fun value generator =>
              SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6494Representative.sourceSemigroup.mul value
                (generatorSourceLabel generator))
            (generatorSourceLabel (representativeHead right))) :=
      sourceFoldlGeneratorAssoc _ _ _
    _ = SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6494Representative.sourceSemigroup.mul (sourceLabel left) (sourceLabel right) :=
      congrArg (SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6494Representative.sourceSemigroup.mul (sourceLabel left))
        (sourceLabelRepresentative right).symm

set_option maxHeartbeats 1000000 in
private theorem sourceLabelRightInverse :
    forall value : Fin 6, sourceLabel (sourcePreimage value) = value := by
  intro value
  apply Fin.ext
  exact by decide +revert

/-- The generated term-function semigroup maps onto the selected root. -/
def quotient : SplitSurjection powerCertificate.semigroup
    SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6494Representative.sourceSemigroup where
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
    SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6494Representative.law0.SatisfiedBy oppositeTable.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    oppositeTable SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6494Representative.law0
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
    SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6494Representative.law1.SatisfiedBy oppositeTable.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    oppositeTable SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6494Representative.law1
    targetLaw1ToFinite targetLaw1FromFinite (by decide) (by decide)

/-- Exact finite checks that the selected target models the root basis. -/
theorem targetModels :
    Models oppositeTable.semigroup SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6494Representative.basis := by
  unfold SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6494Representative.basis
  exact
    FiniteNilpotentCounterexample.models_cons targetLaw0Valid <|
      FiniteNilpotentCounterexample.models_cons targetLaw1Valid <|
        FiniteNilpotentCounterexample.models_nil oppositeTable.semigroup

/-- Exact identity-theory transfer authenticated by the finite certificate. -/
theorem sameIdentityTheory :
    SameIdentityTheoryOver SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6494Representative.sourceSemigroup
      oppositeTable.semigroup Nat := by
  intro identity
  constructor
  · intro sourceValid valuation
    exact Derives.sound targetModels
      (SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6494Representative.basis_complete.2 identity sourceValid) valuation
  · intro targetValid
    have powerValid :=
      identity.satisfiedByPi oppositeTable.semigroup
        (Fin 9) targetValid
    have subValid :=
      powerCertificate.embedding.pullback_identity identity powerValid
    exact quotient.pushforwardIdentity identity subValid

/-- First-layer generic-CAS basis wrapper for `S6_9025`. -/
theorem representative_basis :
    BasisFor table.semigroup.opposite SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6494Representative.basis := by
  have transferred :
      BasisFor oppositeTable.semigroup SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6494Representative.basis :=
    (basisFor_iff_of_sameIdentityTheoryOver sameIdentityTheory).mp
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6494Representative.basis_complete
  simpa only [oppositeTable_semigroup] using transferred


theorem opposite_basis :
    BasisFor table.semigroup (reversedBasis SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6494Representative.basis) :=
  representative_basis.oppositeReversed

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9025
