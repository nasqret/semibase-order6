import SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6494Representative
import SemigroupBasis.FiniteNilpotentCounterexample
import SemigroupBasis.Nonfinite
import SemigroupBasis.Opposite
import SemigroupBasis.RightGeneratedPowerCertificate

set_option maxRecDepth 2048

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9054

open SemigroupBasis

def routeManifestRowSHA256 : String := "ece62d78216eaba920e7abad799aac3f54c5d4b7d22e9d0df6316a96cfafd9fc"
def witnessRecordSHA256 : String := "4de4f93ec27002ef3c0f40dd17cf09b6c258e03d7416993625a62ee9542abdb4"
def transferComponentSHA256 : String := "4de4f93ec27002ef3c0f40dd17cf09b6c258e03d7416993625a62ee9542abdb4"
def powerCertificateSHA256 : String := "102c47ee87223c46ba49b7f81b4443c13d2c0a50eed8f05d661c9b48c1750514"

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
      if left = 2 then row6 1 0 0 2 4 5 right else
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
  "37e5d9286bd3ee9350ab691b3449674c66491d27a58a0def657b5f9fdb88bde8"

private def packedStateVectorCodeChunk0 (index : Nat) : Nat :=
  match index with
  | 0 => 9958016
  | 1 => 963588
  | 2 => 5202648
  | 3 => 9942462
  | 4 => 9913945
  | 5 => 9953893
  | 6 => 8234293
  | 7 => 870264
  | 8 => 123594
  | 9 => 9673921
  | 10 => 122298
  | 11 => 5202144
  | 12 => 9950239
  | 13 => 9898392
  | 14 => 9938340
  | 15 => 9820621
  | 16 => 9913723
  | 17 => 9912427
  | 18 => 9953461
  | 19 => 8218740
  | 20 => 8140969
  | 21 => 8234071
  | 22 => 916926
  | 23 => 30276
  | 24 => 7954135
  | 25 => 123126
  | 26 => 9658368
  | 27 => 9632455
  | 28 => 9673489
  | 29 => 7952839
  | 30 => 28980
  | _ => 121830

private def packedStateVectorCodeChunk1 (index : Nat) : Nat :=
  match index with
  | 0 => 5202396
  | 1 => 9906169
  | 2 => 9946117
  | 3 => 9805068
  | 4 => 9898170
  | 5 => 9896874
  | 6 => 9937908
  | 7 => 9867283
  | 8 => 9820405
  | 9 => 9913291
  | 10 => 9819109
  | 11 => 9911995
  | 12 => 9953677
  | 13 => 8226517
  | 14 => 8125416
  | 15 => 8218518
  | 16 => 8187631
  | 17 => 8140753
  | 18 => 8233639
  | 19 => 76938
  | 20 => 7860817
  | 21 => 29808
  | 22 => 7938582
  | 23 => 7953703
  | 24 => 123378
  | 25 => 9666145
  | 26 => 9616902
  | 27 => 9657936
  | 28 => 9539137
  | 29 => 9632023
  | 30 => 9673705
  | _ => 7937286

private def packedStateVectorCodeChunk2 (index : Nat) : Nat :=
  match index with
  | 0 => 7859521
  | 1 => 7952407
  | 2 => 75642
  | 3 => 28512
  | 4 => 122082
  | 5 => 9812845
  | 6 => 9905947
  | 7 => 9904651
  | 8 => 9945685
  | 9 => 9851730
  | 10 => 9804852
  | 11 => 9897738
  | 12 => 9803556
  | 13 => 9896442
  | 14 => 9938124
  | 15 => 9867067
  | 16 => 9819973
  | 17 => 9913507
  | 18 => 9865771
  | 19 => 9818677
  | 20 => 9912211
  | 21 => 8133193
  | 22 => 8226295
  | 23 => 8172078
  | 24 => 8125200
  | 25 => 8218086
  | 26 => 8187415
  | 27 => 8140321
  | 28 => 8233855
  | 29 => 7907479
  | 30 => 76470
  | _ => 7845264

private def packedStateVectorCodeChunk3 (index : Nat) : Nat :=
  match index with
  | 0 => 7860385
  | 1 => 30060
  | 2 => 7946359
  | 3 => 7938150
  | 4 => 7953919
  | 5 => 9624679
  | 6 => 9665713
  | 7 => 9523584
  | 8 => 9616470
  | 9 => 9658152
  | 10 => 9585799
  | 11 => 9538705
  | 12 => 9632239
  | 13 => 7945063
  | 14 => 7843968
  | 15 => 7936854
  | 16 => 7906183
  | 17 => 7859089
  | 18 => 7952623
  | 19 => 75174
  | 20 => 28764
  | 21 => 9859507
  | 22 => 9812629
  | 23 => 9905515
  | 24 => 9811333
  | 25 => 9904219
  | 26 => 9945901
  | 27 => 9851514
  | 28 => 9804420
  | 29 => 9897954
  | 30 => 9850218
  | _ => 9803124

private def packedStateVectorCodeChunk4 (index : Nat) : Nat :=
  match index with
  | 0 => 9896658
  | 1 => 9866635
  | 2 => 9820189
  | 3 => 9865339
  | 4 => 9818893
  | 5 => 8179855
  | 6 => 8132977
  | 7 => 8225863
  | 8 => 8171862
  | 9 => 8124768
  | 10 => 8218302
  | 11 => 8186983
  | 12 => 8140537
  | 13 => 7891926
  | 14 => 7907047
  | 15 => 76722
  | 16 => 7853041
  | 17 => 7844832
  | 18 => 7860601
  | 19 => 7945927
  | 20 => 7938366
  | 21 => 9531361
  | 22 => 9624247
  | 23 => 9665929
  | 24 => 9570246
  | 25 => 9523152
  | 26 => 9616686
  | 27 => 9585367
  | 28 => 9538921
  | 29 => 7851745
  | 30 => 7944631
  | _ => 7890630

private def packedStateVectorCodeChunk5 (index : Nat) : Nat :=
  match index with
  | 0 => 7843536
  | 1 => 7937070
  | 2 => 7905751
  | 3 => 7859305
  | 4 => 75426
  | 5 => 9859291
  | 6 => 9812197
  | 7 => 9905731
  | 8 => 9857995
  | 9 => 9810901
  | 10 => 9904435
  | 11 => 9851082
  | 12 => 9804636
  | 13 => 9849786
  | 14 => 9803340
  | 15 => 9866851
  | 16 => 9865555
  | 17 => 8179639
  | 18 => 8132545
  | 19 => 8226079
  | 20 => 8171430
  | 21 => 8124984
  | 22 => 8187199
  | 23 => 7899703
  | 24 => 7891494
  | 25 => 7907263
  | 26 => 7852609
  | 27 => 7845048
  | 28 => 7946143
  | 29 => 9578023
  | 30 => 9530929
  | _ => 9624463

private def packedStateVectorCodeChunk6 (index : Nat) : Nat :=
  match index with
  | 0 => 9569814
  | 1 => 9523368
  | 2 => 9585583
  | 3 => 7898407
  | 4 => 7851313
  | 5 => 7944847
  | 6 => 7890198
  | 7 => 7843752
  | 8 => 7905967
  | 9 => 9858859
  | 10 => 9812413
  | 11 => 9857563
  | 12 => 9811117
  | 13 => 9851298
  | 14 => 9850002
  | 15 => 8179207
  | 16 => 8132761
  | 17 => 8171646
  | 18 => 7899271
  | 19 => 7891710
  | 20 => 7852825
  | 21 => 9577591
  | 22 => 9531145
  | 23 => 9570030
  | 24 => 7897975
  | 25 => 7851529
  | 26 => 7890414
  | 27 => 9859075
  | 28 => 9857779
  | 29 => 8179423
  | 30 => 7899487
  | _ => 9577807

private def packedStateVectorCodeChunk7 (index : Nat) : Nat :=
  match index with
  | _ => 7898191

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
      | 3 => (3 : Fin 6)
      | 4 => (3 : Fin 6)
      | 5 => (2 : Fin 6)
      | 6 => (3 : Fin 6)
      | 7 => (5 : Fin 6)
      | _ => (5 : Fin 6)
  | 1 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (2 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (3 : Fin 6)
      | 4 => (5 : Fin 6)
      | 5 => (3 : Fin 6)
      | 6 => (2 : Fin 6)
      | 7 => (3 : Fin 6)
      | _ => (0 : Fin 6)
  | _ =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (2 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (3 : Fin 6)
      | 6 => (3 : Fin 6)
      | 7 => (0 : Fin 6)
      | _ => (3 : Fin 6)

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
  if code = 28512 then (67 : Fin 225) else
  if code = 28764 then (116 : Fin 225) else
  if code = 28980 then (30 : Fin 225) else
  if code = 29808 then (53 : Fin 225) else
  if code = 30060 then (97 : Fin 225) else
  if code = 30276 then (23 : Fin 225) else
  if code = 75174 then (115 : Fin 225) else
  if code = 75426 then (164 : Fin 225) else
  if code = 75642 then (66 : Fin 225) else
  if code = 76470 then (94 : Fin 225) else
  if code = 76722 then (143 : Fin 225) else
  if code = 76938 then (51 : Fin 225) else
  if code = 121830 then (31 : Fin 225) else
  if code = 122082 then (68 : Fin 225) else
  if code = 122298 then (10 : Fin 225) else
  if code = 123126 then (25 : Fin 225) else
  if code = 123378 then (56 : Fin 225) else
  if code = 123594 then (8 : Fin 225) else
  if code = 870264 then (7 : Fin 225) else
  if code = 916926 then (22 : Fin 225) else
  if code = 963588 then (1 : Fin 225) else
  if code = 5202144 then (11 : Fin 225) else
  if code = 5202396 then (32 : Fin 225) else
  if code = 5202648 then (2 : Fin 225) else
  if code = 7843536 then (160 : Fin 225) else
  if code = 7843752 then (199 : Fin 225) else
  if code = 7843968 then (110 : Fin 225) else
  if code = 7844832 then (145 : Fin 225) else
  if code = 7845048 then (187 : Fin 225) else
  if code = 7845264 then (95 : Fin 225) else
  if code = 7851313 then (196 : Fin 225) else
  if code = 7851529 then (217 : Fin 225) else
  (0 : Fin 225)

private def decodeStateCodeChunk1 (code : Nat) : Fin 225 :=
  if code = 7851745 then (157 : Fin 225) else
  if code = 7852609 then (186 : Fin 225) else
  if code = 7852825 then (212 : Fin 225) else
  if code = 7853041 then (144 : Fin 225) else
  if code = 7859089 then (113 : Fin 225) else
  if code = 7859305 then (163 : Fin 225) else
  if code = 7859521 then (64 : Fin 225) else
  if code = 7860385 then (96 : Fin 225) else
  if code = 7860601 then (146 : Fin 225) else
  if code = 7860817 then (52 : Fin 225) else
  if code = 7890198 then (198 : Fin 225) else
  if code = 7890414 then (218 : Fin 225) else
  if code = 7890630 then (159 : Fin 225) else
  if code = 7891494 then (184 : Fin 225) else
  if code = 7891710 then (211 : Fin 225) else
  if code = 7891926 then (141 : Fin 225) else
  if code = 7897975 then (216 : Fin 225) else
  if code = 7898191 then (224 : Fin 225) else
  if code = 7898407 then (195 : Fin 225) else
  if code = 7899271 then (210 : Fin 225) else
  if code = 7899487 then (222 : Fin 225) else
  if code = 7899703 then (183 : Fin 225) else
  if code = 7905751 then (162 : Fin 225) else
  if code = 7905967 then (200 : Fin 225) else
  if code = 7906183 then (112 : Fin 225) else
  if code = 7907047 then (142 : Fin 225) else
  if code = 7907263 then (185 : Fin 225) else
  if code = 7907479 then (93 : Fin 225) else
  if code = 7936854 then (111 : Fin 225) else
  if code = 7937070 then (161 : Fin 225) else
  if code = 7937286 then (63 : Fin 225) else
  if code = 7938150 then (99 : Fin 225) else
  (0 : Fin 225)

private def decodeStateCodeChunk2 (code : Nat) : Fin 225 :=
  if code = 7938366 then (148 : Fin 225) else
  if code = 7938582 then (54 : Fin 225) else
  if code = 7944631 then (158 : Fin 225) else
  if code = 7944847 then (197 : Fin 225) else
  if code = 7945063 then (109 : Fin 225) else
  if code = 7945927 then (147 : Fin 225) else
  if code = 7946143 then (188 : Fin 225) else
  if code = 7946359 then (98 : Fin 225) else
  if code = 7952407 then (65 : Fin 225) else
  if code = 7952623 then (114 : Fin 225) else
  if code = 7952839 then (29 : Fin 225) else
  if code = 7953703 then (55 : Fin 225) else
  if code = 7953919 then (100 : Fin 225) else
  if code = 7954135 then (24 : Fin 225) else
  if code = 8124768 then (137 : Fin 225) else
  if code = 8124984 then (181 : Fin 225) else
  if code = 8125200 then (88 : Fin 225) else
  if code = 8125416 then (46 : Fin 225) else
  if code = 8132545 then (178 : Fin 225) else
  if code = 8132761 then (208 : Fin 225) else
  if code = 8132977 then (134 : Fin 225) else
  if code = 8133193 then (85 : Fin 225) else
  if code = 8140321 then (91 : Fin 225) else
  if code = 8140537 then (140 : Fin 225) else
  if code = 8140753 then (49 : Fin 225) else
  if code = 8140969 then (20 : Fin 225) else
  if code = 8171430 then (180 : Fin 225) else
  if code = 8171646 then (209 : Fin 225) else
  if code = 8171862 then (136 : Fin 225) else
  if code = 8172078 then (87 : Fin 225) else
  if code = 8179207 then (207 : Fin 225) else
  if code = 8179423 then (221 : Fin 225) else
  (0 : Fin 225)

private def decodeStateCodeChunk3 (code : Nat) : Fin 225 :=
  if code = 8179639 then (177 : Fin 225) else
  if code = 8179855 then (133 : Fin 225) else
  if code = 8186983 then (139 : Fin 225) else
  if code = 8187199 then (182 : Fin 225) else
  if code = 8187415 then (90 : Fin 225) else
  if code = 8187631 then (48 : Fin 225) else
  if code = 8218086 then (89 : Fin 225) else
  if code = 8218302 then (138 : Fin 225) else
  if code = 8218518 then (47 : Fin 225) else
  if code = 8218740 then (19 : Fin 225) else
  if code = 8225863 then (135 : Fin 225) else
  if code = 8226079 then (179 : Fin 225) else
  if code = 8226295 then (86 : Fin 225) else
  if code = 8226517 then (45 : Fin 225) else
  if code = 8233639 then (50 : Fin 225) else
  if code = 8233855 then (92 : Fin 225) else
  if code = 8234071 then (21 : Fin 225) else
  if code = 8234293 then (6 : Fin 225) else
  if code = 9523152 then (153 : Fin 225) else
  if code = 9523368 then (193 : Fin 225) else
  if code = 9523584 then (103 : Fin 225) else
  if code = 9530929 then (190 : Fin 225) else
  if code = 9531145 then (214 : Fin 225) else
  if code = 9531361 then (149 : Fin 225) else
  if code = 9538705 then (107 : Fin 225) else
  if code = 9538921 then (156 : Fin 225) else
  if code = 9539137 then (60 : Fin 225) else
  if code = 9569814 then (192 : Fin 225) else
  if code = 9570030 then (215 : Fin 225) else
  if code = 9570246 then (152 : Fin 225) else
  if code = 9577591 then (213 : Fin 225) else
  if code = 9577807 then (223 : Fin 225) else
  (0 : Fin 225)

private def decodeStateCodeChunk4 (code : Nat) : Fin 225 :=
  if code = 9578023 then (189 : Fin 225) else
  if code = 9585367 then (155 : Fin 225) else
  if code = 9585583 then (194 : Fin 225) else
  if code = 9585799 then (106 : Fin 225) else
  if code = 9616470 then (104 : Fin 225) else
  if code = 9616686 then (154 : Fin 225) else
  if code = 9616902 then (58 : Fin 225) else
  if code = 9624247 then (150 : Fin 225) else
  if code = 9624463 then (191 : Fin 225) else
  if code = 9624679 then (101 : Fin 225) else
  if code = 9632023 then (61 : Fin 225) else
  if code = 9632239 then (108 : Fin 225) else
  if code = 9632455 then (27 : Fin 225) else
  if code = 9657936 then (59 : Fin 225) else
  if code = 9658152 then (105 : Fin 225) else
  if code = 9658368 then (26 : Fin 225) else
  if code = 9665713 then (102 : Fin 225) else
  if code = 9665929 then (151 : Fin 225) else
  if code = 9666145 then (57 : Fin 225) else
  if code = 9673489 then (28 : Fin 225) else
  if code = 9673705 then (62 : Fin 225) else
  if code = 9673921 then (9 : Fin 225) else
  if code = 9803124 then (127 : Fin 225) else
  if code = 9803340 then (174 : Fin 225) else
  if code = 9803556 then (76 : Fin 225) else
  if code = 9804420 then (124 : Fin 225) else
  if code = 9804636 then (172 : Fin 225) else
  if code = 9804852 then (74 : Fin 225) else
  if code = 9805068 then (35 : Fin 225) else
  if code = 9810901 then (169 : Fin 225) else
  if code = 9811117 then (204 : Fin 225) else
  if code = 9811333 then (120 : Fin 225) else
  (0 : Fin 225)

private def decodeStateCodeChunk5 (code : Nat) : Fin 225 :=
  if code = 9812197 then (166 : Fin 225) else
  if code = 9812413 then (202 : Fin 225) else
  if code = 9812629 then (118 : Fin 225) else
  if code = 9812845 then (69 : Fin 225) else
  if code = 9818677 then (83 : Fin 225) else
  if code = 9818893 then (132 : Fin 225) else
  if code = 9819109 then (42 : Fin 225) else
  if code = 9819973 then (80 : Fin 225) else
  if code = 9820189 then (130 : Fin 225) else
  if code = 9820405 then (40 : Fin 225) else
  if code = 9820621 then (15 : Fin 225) else
  if code = 9849786 then (173 : Fin 225) else
  if code = 9850002 then (206 : Fin 225) else
  if code = 9850218 then (126 : Fin 225) else
  if code = 9851082 then (171 : Fin 225) else
  if code = 9851298 then (205 : Fin 225) else
  if code = 9851514 then (123 : Fin 225) else
  if code = 9851730 then (73 : Fin 225) else
  if code = 9857563 then (203 : Fin 225) else
  if code = 9857779 then (220 : Fin 225) else
  if code = 9857995 then (168 : Fin 225) else
  if code = 9858859 then (201 : Fin 225) else
  if code = 9859075 then (219 : Fin 225) else
  if code = 9859291 then (165 : Fin 225) else
  if code = 9859507 then (117 : Fin 225) else
  if code = 9865339 then (131 : Fin 225) else
  if code = 9865555 then (176 : Fin 225) else
  if code = 9865771 then (82 : Fin 225) else
  if code = 9866635 then (129 : Fin 225) else
  if code = 9866851 then (175 : Fin 225) else
  if code = 9867067 then (79 : Fin 225) else
  if code = 9867283 then (39 : Fin 225) else
  (0 : Fin 225)

private def decodeStateCodeChunk6 (code : Nat) : Fin 225 :=
  if code = 9896442 then (77 : Fin 225) else
  if code = 9896658 then (128 : Fin 225) else
  if code = 9896874 then (37 : Fin 225) else
  if code = 9897738 then (75 : Fin 225) else
  if code = 9897954 then (125 : Fin 225) else
  if code = 9898170 then (36 : Fin 225) else
  if code = 9898392 then (13 : Fin 225) else
  if code = 9904219 then (121 : Fin 225) else
  if code = 9904435 then (170 : Fin 225) else
  if code = 9904651 then (71 : Fin 225) else
  if code = 9905515 then (119 : Fin 225) else
  if code = 9905731 then (167 : Fin 225) else
  if code = 9905947 then (70 : Fin 225) else
  if code = 9906169 then (33 : Fin 225) else
  if code = 9911995 then (43 : Fin 225) else
  if code = 9912211 then (84 : Fin 225) else
  if code = 9912427 then (17 : Fin 225) else
  if code = 9913291 then (41 : Fin 225) else
  if code = 9913507 then (81 : Fin 225) else
  if code = 9913723 then (16 : Fin 225) else
  if code = 9913945 then (4 : Fin 225) else
  if code = 9937908 then (38 : Fin 225) else
  if code = 9938124 then (78 : Fin 225) else
  if code = 9938340 then (14 : Fin 225) else
  if code = 9942462 then (3 : Fin 225) else
  if code = 9945685 then (72 : Fin 225) else
  if code = 9945901 then (122 : Fin 225) else
  if code = 9946117 then (34 : Fin 225) else
  if code = 9950239 then (12 : Fin 225) else
  if code = 9953461 then (18 : Fin 225) else
  if code = 9953677 then (44 : Fin 225) else
  if code = 9953893 then (5 : Fin 225) else
  (0 : Fin 225)

private def decodeStateCodeChunk7 (code : Nat) : Fin 225 :=
  if code = 9958016 then (0 : Fin 225) else
  (0 : Fin 225)

private def stateVectorCode
    (vector : Fin 9 -> Fin 6) : Nat :=
  (vector (0 : Fin 9)).val + 6 * ((vector (1 : Fin 9)).val + 6 * ((vector (2 : Fin 9)).val + 6 * ((vector (3 : Fin 9)).val + 6 * ((vector (4 : Fin 9)).val + 6 * ((vector (5 : Fin 9)).val + 6 * ((vector (6 : Fin 9)).val + 6 * ((vector (7 : Fin 9)).val + 6 * ((vector (8 : Fin 9)).val))))))))

private def decodeStateCode (code : Nat) : Fin 225 :=
  if code < 7851745 then decodeStateCodeChunk0 code else
  if code < 7938366 then decodeStateCodeChunk1 code else
  if code < 8179639 then decodeStateCodeChunk2 code else
  if code < 9578023 then decodeStateCodeChunk3 code else
  if code < 9812197 then decodeStateCodeChunk4 code else
  if code < 9896442 then decodeStateCodeChunk5 code else
  if code < 9958016 then decodeStateCodeChunk6 code else
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

/-- First-layer generic-CAS basis wrapper for `S6_9054`. -/
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

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9054
