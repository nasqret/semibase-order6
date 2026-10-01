import SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6494Representative
import SemigroupBasis.FiniteNilpotentCounterexample
import SemigroupBasis.Nonfinite
import SemigroupBasis.Opposite
import SemigroupBasis.RightGeneratedPowerCertificate

set_option maxRecDepth 2048

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9064

open SemigroupBasis

def routeManifestRowSHA256 : String := "912ff4b7183b06ef58624cffe6a62c0dc16f5133b121a7d885598cef1e0b1d5a"
def witnessRecordSHA256 : String := "9862627ec63dbc5d49f7849a5787e151a75179fb2d2eeb0e1167c026fccdd910"
def transferComponentSHA256 : String := "9862627ec63dbc5d49f7849a5787e151a75179fb2d2eeb0e1167c026fccdd910"
def powerCertificateSHA256 : String := "22ede2f0129e6e278ecddfbf4fc32d3149b8271b168b32ad7ac47891133f0acd"

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
            row6 5 5 5 5 4 5 right

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
  "3d307467aa7c70398ce5bfb1efeb2854c3f8df8ac6a745a8dcbb121fed600186"

private def packedStateVectorCodeChunk0 (index : Nat) : Nat :=
  match index with
  | 0 => 9828128
  | 1 => 1374528
  | 2 => 6934320
  | 3 => 9827694
  | 4 => 10053625
  | 5 => 10014697
  | 6 => 9772393
  | 7 => 1358964
  | 8 => 8092950
  | 9 => 8333785
  | 10 => 8046294
  | 11 => 6934248
  | 12 => 9827911
  | 13 => 10053192
  | 14 => 10014264
  | 15 => 10038061
  | 16 => 10053583
  | 17 => 10006927
  | 18 => 10014625
  | 19 => 9771960
  | 20 => 9756829
  | 21 => 9772351
  | 22 => 1366746
  | 23 => 8077392
  | 24 => 8092735
  | 25 => 8092878
  | 26 => 8333352
  | 27 => 8326015
  | 28 => 8333713
  | 29 => 8046079
  | 30 => 8030736
  | _ => 8046222

private def packedStateVectorCodeChunk1 (index : Nat) : Nat :=
  match index with
  | 0 => 6934284
  | 1 => 10053409
  | 2 => 10014481
  | 3 => 10037628
  | 4 => 10053150
  | 5 => 10006494
  | 6 => 10014192
  | 7 => 10045843
  | 8 => 10038025
  | 9 => 10053511
  | 10 => 9991369
  | 11 => 10006855
  | 12 => 10014661
  | 13 => 9772177
  | 14 => 9756396
  | 15 => 9771918
  | 16 => 9764611
  | 17 => 9756793
  | 18 => 9772279
  | 19 => 8085174
  | 20 => 8077177
  | 21 => 8077320
  | 22 => 8092302
  | 23 => 8092663
  | 24 => 8092914
  | 25 => 8333569
  | 26 => 8325582
  | 27 => 8333280
  | 28 => 8310457
  | 29 => 8325943
  | 30 => 8333749
  | _ => 8045646

private def packedStateVectorCodeChunk2 (index : Nat) : Nat :=
  match index with
  | 0 => 8030521
  | 1 => 8046007
  | 2 => 8038518
  | 3 => 8030664
  | 4 => 8046258
  | 5 => 10037845
  | 6 => 10053367
  | 7 => 10006711
  | 8 => 10014409
  | 9 => 10045410
  | 10 => 10037592
  | 11 => 10053078
  | 12 => 9990936
  | 13 => 10006422
  | 14 => 10014228
  | 15 => 10045807
  | 16 => 10037953
  | 17 => 10053547
  | 18 => 9999151
  | 19 => 9991297
  | 20 => 10006891
  | 21 => 9756613
  | 22 => 9772135
  | 23 => 9764178
  | 24 => 9756360
  | 25 => 9771846
  | 26 => 9764575
  | 27 => 9756721
  | 28 => 9772315
  | 29 => 8084959
  | 30 => 8085102
  | _ => 8076744

private def packedStateVectorCodeChunk3 (index : Nat) : Nat :=
  match index with
  | 0 => 8077105
  | 1 => 8077356
  | 2 => 8092519
  | 3 => 8092230
  | 4 => 8092699
  | 5 => 8325799
  | 6 => 8333497
  | 7 => 8310024
  | 8 => 8325510
  | 9 => 8333316
  | 10 => 8318239
  | 11 => 8310385
  | 12 => 8325979
  | 13 => 8045863
  | 14 => 8030088
  | 15 => 8045574
  | 16 => 8038303
  | 17 => 8030449
  | 18 => 8046043
  | 19 => 8038446
  | 20 => 8030700
  | 21 => 10045627
  | 22 => 10037809
  | 23 => 10053295
  | 24 => 9991153
  | 25 => 10006639
  | 26 => 10014445
  | 27 => 10045374
  | 28 => 10037520
  | 29 => 10053114
  | 30 => 9998718
  | _ => 9990864

private def packedStateVectorCodeChunk4 (index : Nat) : Nat :=
  match index with
  | 0 => 10006458
  | 1 => 10045735
  | 2 => 10037989
  | 3 => 9999079
  | 4 => 9991333
  | 5 => 9764395
  | 6 => 9756577
  | 7 => 9772063
  | 8 => 9764142
  | 9 => 9756288
  | 10 => 9771882
  | 11 => 9764503
  | 12 => 9756757
  | 13 => 8084526
  | 14 => 8084887
  | 15 => 8085138
  | 16 => 8076961
  | 17 => 8076672
  | 18 => 8077141
  | 19 => 8092447
  | 20 => 8092266
  | 21 => 8310241
  | 22 => 8325727
  | 23 => 8333533
  | 24 => 8317806
  | 25 => 8309952
  | 26 => 8325546
  | 27 => 8318167
  | 28 => 8310421
  | 29 => 8030305
  | 30 => 8045791
  | _ => 8037870

private def packedStateVectorCodeChunk5 (index : Nat) : Nat :=
  match index with
  | 0 => 8030016
  | 1 => 8045610
  | 2 => 8038231
  | 3 => 8030485
  | 4 => 8038482
  | 5 => 10045591
  | 6 => 10037737
  | 7 => 10053331
  | 8 => 9998935
  | 9 => 9991081
  | 10 => 10006675
  | 11 => 10045302
  | 12 => 10037556
  | 13 => 9998646
  | 14 => 9990900
  | 15 => 10045771
  | 16 => 9999115
  | 17 => 9764359
  | 18 => 9756505
  | 19 => 9772099
  | 20 => 9764070
  | 21 => 9756324
  | 22 => 9764539
  | 23 => 8084743
  | 24 => 8084454
  | 25 => 8084923
  | 26 => 8076889
  | 27 => 8076708
  | 28 => 8092483
  | 29 => 8318023
  | 30 => 8310169
  | _ => 8325763

private def packedStateVectorCodeChunk6 (index : Nat) : Nat :=
  match index with
  | 0 => 8317734
  | 1 => 8309988
  | 2 => 8318203
  | 3 => 8038087
  | 4 => 8030233
  | 5 => 8045827
  | 6 => 8037798
  | 7 => 8030052
  | 8 => 8038267
  | 9 => 10045519
  | 10 => 10037773
  | 11 => 9998863
  | 12 => 9991117
  | 13 => 10045338
  | 14 => 9998682
  | 15 => 9764287
  | 16 => 9756541
  | 17 => 9764106
  | 18 => 8084671
  | 19 => 8084490
  | 20 => 8076925
  | 21 => 8317951
  | 22 => 8310205
  | 23 => 8317770
  | 24 => 8038015
  | 25 => 8030269
  | 26 => 8037834
  | 27 => 10045555
  | 28 => 9998899
  | 29 => 9764323
  | 30 => 8084707
  | _ => 8317987

private def packedStateVectorCodeChunk7 (index : Nat) : Nat :=
  match index with
  | _ => 8038051

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
      | 2 => (3 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (5 : Fin 6)
      | 5 => (3 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (5 : Fin 6)
      | _ => (5 : Fin 6)
  | 1 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (2 : Fin 6)
      | 2 => (3 : Fin 6)
      | 3 => (3 : Fin 6)
      | 4 => (4 : Fin 6)
      | 5 => (2 : Fin 6)
      | 6 => (5 : Fin 6)
      | 7 => (4 : Fin 6)
      | _ => (0 : Fin 6)
  | _ =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (2 : Fin 6)
      | 3 => (3 : Fin 6)
      | 4 => (4 : Fin 6)
      | 5 => (3 : Fin 6)
      | 6 => (4 : Fin 6)
      | 7 => (0 : Fin 6)
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
  if code = 1358964 then (7 : Fin 225) else
  if code = 1366746 then (22 : Fin 225) else
  if code = 1374528 then (1 : Fin 225) else
  if code = 6934248 then (11 : Fin 225) else
  if code = 6934284 then (32 : Fin 225) else
  if code = 6934320 then (2 : Fin 225) else
  if code = 8030016 then (160 : Fin 225) else
  if code = 8030052 then (199 : Fin 225) else
  if code = 8030088 then (110 : Fin 225) else
  if code = 8030233 then (196 : Fin 225) else
  if code = 8030269 then (217 : Fin 225) else
  if code = 8030305 then (157 : Fin 225) else
  if code = 8030449 then (113 : Fin 225) else
  if code = 8030485 then (163 : Fin 225) else
  if code = 8030521 then (64 : Fin 225) else
  if code = 8030664 then (67 : Fin 225) else
  if code = 8030700 then (116 : Fin 225) else
  if code = 8030736 then (30 : Fin 225) else
  if code = 8037798 then (198 : Fin 225) else
  if code = 8037834 then (218 : Fin 225) else
  if code = 8037870 then (159 : Fin 225) else
  if code = 8038015 then (216 : Fin 225) else
  if code = 8038051 then (224 : Fin 225) else
  if code = 8038087 then (195 : Fin 225) else
  if code = 8038231 then (162 : Fin 225) else
  if code = 8038267 then (200 : Fin 225) else
  if code = 8038303 then (112 : Fin 225) else
  if code = 8038446 then (115 : Fin 225) else
  if code = 8038482 then (164 : Fin 225) else
  if code = 8038518 then (66 : Fin 225) else
  if code = 8045574 then (111 : Fin 225) else
  if code = 8045610 then (161 : Fin 225) else
  (0 : Fin 225)

private def decodeStateCodeChunk1 (code : Nat) : Fin 225 :=
  if code = 8045646 then (63 : Fin 225) else
  if code = 8045791 then (158 : Fin 225) else
  if code = 8045827 then (197 : Fin 225) else
  if code = 8045863 then (109 : Fin 225) else
  if code = 8046007 then (65 : Fin 225) else
  if code = 8046043 then (114 : Fin 225) else
  if code = 8046079 then (29 : Fin 225) else
  if code = 8046222 then (31 : Fin 225) else
  if code = 8046258 then (68 : Fin 225) else
  if code = 8046294 then (10 : Fin 225) else
  if code = 8076672 then (145 : Fin 225) else
  if code = 8076708 then (187 : Fin 225) else
  if code = 8076744 then (95 : Fin 225) else
  if code = 8076889 then (186 : Fin 225) else
  if code = 8076925 then (212 : Fin 225) else
  if code = 8076961 then (144 : Fin 225) else
  if code = 8077105 then (96 : Fin 225) else
  if code = 8077141 then (146 : Fin 225) else
  if code = 8077177 then (52 : Fin 225) else
  if code = 8077320 then (53 : Fin 225) else
  if code = 8077356 then (97 : Fin 225) else
  if code = 8077392 then (23 : Fin 225) else
  if code = 8084454 then (184 : Fin 225) else
  if code = 8084490 then (211 : Fin 225) else
  if code = 8084526 then (141 : Fin 225) else
  if code = 8084671 then (210 : Fin 225) else
  if code = 8084707 then (222 : Fin 225) else
  if code = 8084743 then (183 : Fin 225) else
  if code = 8084887 then (142 : Fin 225) else
  if code = 8084923 then (185 : Fin 225) else
  if code = 8084959 then (93 : Fin 225) else
  if code = 8085102 then (94 : Fin 225) else
  (0 : Fin 225)

private def decodeStateCodeChunk2 (code : Nat) : Fin 225 :=
  if code = 8085138 then (143 : Fin 225) else
  if code = 8085174 then (51 : Fin 225) else
  if code = 8092230 then (99 : Fin 225) else
  if code = 8092266 then (148 : Fin 225) else
  if code = 8092302 then (54 : Fin 225) else
  if code = 8092447 then (147 : Fin 225) else
  if code = 8092483 then (188 : Fin 225) else
  if code = 8092519 then (98 : Fin 225) else
  if code = 8092663 then (55 : Fin 225) else
  if code = 8092699 then (100 : Fin 225) else
  if code = 8092735 then (24 : Fin 225) else
  if code = 8092878 then (25 : Fin 225) else
  if code = 8092914 then (56 : Fin 225) else
  if code = 8092950 then (8 : Fin 225) else
  if code = 8309952 then (153 : Fin 225) else
  if code = 8309988 then (193 : Fin 225) else
  if code = 8310024 then (103 : Fin 225) else
  if code = 8310169 then (190 : Fin 225) else
  if code = 8310205 then (214 : Fin 225) else
  if code = 8310241 then (149 : Fin 225) else
  if code = 8310385 then (107 : Fin 225) else
  if code = 8310421 then (156 : Fin 225) else
  if code = 8310457 then (60 : Fin 225) else
  if code = 8317734 then (192 : Fin 225) else
  if code = 8317770 then (215 : Fin 225) else
  if code = 8317806 then (152 : Fin 225) else
  if code = 8317951 then (213 : Fin 225) else
  if code = 8317987 then (223 : Fin 225) else
  if code = 8318023 then (189 : Fin 225) else
  if code = 8318167 then (155 : Fin 225) else
  if code = 8318203 then (194 : Fin 225) else
  if code = 8318239 then (106 : Fin 225) else
  (0 : Fin 225)

private def decodeStateCodeChunk3 (code : Nat) : Fin 225 :=
  if code = 8325510 then (104 : Fin 225) else
  if code = 8325546 then (154 : Fin 225) else
  if code = 8325582 then (58 : Fin 225) else
  if code = 8325727 then (150 : Fin 225) else
  if code = 8325763 then (191 : Fin 225) else
  if code = 8325799 then (101 : Fin 225) else
  if code = 8325943 then (61 : Fin 225) else
  if code = 8325979 then (108 : Fin 225) else
  if code = 8326015 then (27 : Fin 225) else
  if code = 8333280 then (59 : Fin 225) else
  if code = 8333316 then (105 : Fin 225) else
  if code = 8333352 then (26 : Fin 225) else
  if code = 8333497 then (102 : Fin 225) else
  if code = 8333533 then (151 : Fin 225) else
  if code = 8333569 then (57 : Fin 225) else
  if code = 8333713 then (28 : Fin 225) else
  if code = 8333749 then (62 : Fin 225) else
  if code = 8333785 then (9 : Fin 225) else
  if code = 9756288 then (137 : Fin 225) else
  if code = 9756324 then (181 : Fin 225) else
  if code = 9756360 then (88 : Fin 225) else
  if code = 9756396 then (46 : Fin 225) else
  if code = 9756505 then (178 : Fin 225) else
  if code = 9756541 then (208 : Fin 225) else
  if code = 9756577 then (134 : Fin 225) else
  if code = 9756613 then (85 : Fin 225) else
  if code = 9756721 then (91 : Fin 225) else
  if code = 9756757 then (140 : Fin 225) else
  if code = 9756793 then (49 : Fin 225) else
  if code = 9756829 then (20 : Fin 225) else
  if code = 9764070 then (180 : Fin 225) else
  if code = 9764106 then (209 : Fin 225) else
  (0 : Fin 225)

private def decodeStateCodeChunk4 (code : Nat) : Fin 225 :=
  if code = 9764142 then (136 : Fin 225) else
  if code = 9764178 then (87 : Fin 225) else
  if code = 9764287 then (207 : Fin 225) else
  if code = 9764323 then (221 : Fin 225) else
  if code = 9764359 then (177 : Fin 225) else
  if code = 9764395 then (133 : Fin 225) else
  if code = 9764503 then (139 : Fin 225) else
  if code = 9764539 then (182 : Fin 225) else
  if code = 9764575 then (90 : Fin 225) else
  if code = 9764611 then (48 : Fin 225) else
  if code = 9771846 then (89 : Fin 225) else
  if code = 9771882 then (138 : Fin 225) else
  if code = 9771918 then (47 : Fin 225) else
  if code = 9771960 then (19 : Fin 225) else
  if code = 9772063 then (135 : Fin 225) else
  if code = 9772099 then (179 : Fin 225) else
  if code = 9772135 then (86 : Fin 225) else
  if code = 9772177 then (45 : Fin 225) else
  if code = 9772279 then (50 : Fin 225) else
  if code = 9772315 then (92 : Fin 225) else
  if code = 9772351 then (21 : Fin 225) else
  if code = 9772393 then (6 : Fin 225) else
  if code = 9827694 then (3 : Fin 225) else
  if code = 9827911 then (12 : Fin 225) else
  if code = 9828128 then (0 : Fin 225) else
  if code = 9990864 then (127 : Fin 225) else
  if code = 9990900 then (174 : Fin 225) else
  if code = 9990936 then (76 : Fin 225) else
  if code = 9991081 then (169 : Fin 225) else
  if code = 9991117 then (204 : Fin 225) else
  if code = 9991153 then (120 : Fin 225) else
  if code = 9991297 then (83 : Fin 225) else
  (0 : Fin 225)

private def decodeStateCodeChunk5 (code : Nat) : Fin 225 :=
  if code = 9991333 then (132 : Fin 225) else
  if code = 9991369 then (42 : Fin 225) else
  if code = 9998646 then (173 : Fin 225) else
  if code = 9998682 then (206 : Fin 225) else
  if code = 9998718 then (126 : Fin 225) else
  if code = 9998863 then (203 : Fin 225) else
  if code = 9998899 then (220 : Fin 225) else
  if code = 9998935 then (168 : Fin 225) else
  if code = 9999079 then (131 : Fin 225) else
  if code = 9999115 then (176 : Fin 225) else
  if code = 9999151 then (82 : Fin 225) else
  if code = 10006422 then (77 : Fin 225) else
  if code = 10006458 then (128 : Fin 225) else
  if code = 10006494 then (37 : Fin 225) else
  if code = 10006639 then (121 : Fin 225) else
  if code = 10006675 then (170 : Fin 225) else
  if code = 10006711 then (71 : Fin 225) else
  if code = 10006855 then (43 : Fin 225) else
  if code = 10006891 then (84 : Fin 225) else
  if code = 10006927 then (17 : Fin 225) else
  if code = 10014192 then (38 : Fin 225) else
  if code = 10014228 then (78 : Fin 225) else
  if code = 10014264 then (14 : Fin 225) else
  if code = 10014409 then (72 : Fin 225) else
  if code = 10014445 then (122 : Fin 225) else
  if code = 10014481 then (34 : Fin 225) else
  if code = 10014625 then (18 : Fin 225) else
  if code = 10014661 then (44 : Fin 225) else
  if code = 10014697 then (5 : Fin 225) else
  if code = 10037520 then (124 : Fin 225) else
  if code = 10037556 then (172 : Fin 225) else
  if code = 10037592 then (74 : Fin 225) else
  (0 : Fin 225)

private def decodeStateCodeChunk6 (code : Nat) : Fin 225 :=
  if code = 10037628 then (35 : Fin 225) else
  if code = 10037737 then (166 : Fin 225) else
  if code = 10037773 then (202 : Fin 225) else
  if code = 10037809 then (118 : Fin 225) else
  if code = 10037845 then (69 : Fin 225) else
  if code = 10037953 then (80 : Fin 225) else
  if code = 10037989 then (130 : Fin 225) else
  if code = 10038025 then (40 : Fin 225) else
  if code = 10038061 then (15 : Fin 225) else
  if code = 10045302 then (171 : Fin 225) else
  if code = 10045338 then (205 : Fin 225) else
  if code = 10045374 then (123 : Fin 225) else
  if code = 10045410 then (73 : Fin 225) else
  if code = 10045519 then (201 : Fin 225) else
  if code = 10045555 then (219 : Fin 225) else
  if code = 10045591 then (165 : Fin 225) else
  if code = 10045627 then (117 : Fin 225) else
  if code = 10045735 then (129 : Fin 225) else
  if code = 10045771 then (175 : Fin 225) else
  if code = 10045807 then (79 : Fin 225) else
  if code = 10045843 then (39 : Fin 225) else
  if code = 10053078 then (75 : Fin 225) else
  if code = 10053114 then (125 : Fin 225) else
  if code = 10053150 then (36 : Fin 225) else
  if code = 10053192 then (13 : Fin 225) else
  if code = 10053295 then (119 : Fin 225) else
  if code = 10053331 then (167 : Fin 225) else
  if code = 10053367 then (70 : Fin 225) else
  if code = 10053409 then (33 : Fin 225) else
  if code = 10053511 then (41 : Fin 225) else
  if code = 10053547 then (81 : Fin 225) else
  if code = 10053583 then (16 : Fin 225) else
  (0 : Fin 225)

private def decodeStateCodeChunk7 (code : Nat) : Fin 225 :=
  if code = 10053625 then (4 : Fin 225) else
  (0 : Fin 225)

private def stateVectorCode
    (vector : Fin 9 -> Fin 6) : Nat :=
  (vector (0 : Fin 9)).val + 6 * ((vector (1 : Fin 9)).val + 6 * ((vector (2 : Fin 9)).val + 6 * ((vector (3 : Fin 9)).val + 6 * ((vector (4 : Fin 9)).val + 6 * ((vector (5 : Fin 9)).val + 6 * ((vector (6 : Fin 9)).val + 6 * ((vector (7 : Fin 9)).val + 6 * ((vector (8 : Fin 9)).val))))))))

private def decodeStateCode (code : Nat) : Fin 225 :=
  if code < 8045646 then decodeStateCodeChunk0 code else
  if code < 8085138 then decodeStateCodeChunk1 code else
  if code < 8325510 then decodeStateCodeChunk2 code else
  if code < 9764142 then decodeStateCodeChunk3 code else
  if code < 9991333 then decodeStateCodeChunk4 code else
  if code < 10037628 then decodeStateCodeChunk5 code else
  if code < 10053625 then decodeStateCodeChunk6 code else
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

/-- First-layer generic-CAS basis wrapper for `S6_9064`. -/
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

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9064
