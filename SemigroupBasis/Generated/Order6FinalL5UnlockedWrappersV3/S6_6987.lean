import SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6494Representative
import SemigroupBasis.FiniteNilpotentCounterexample
import SemigroupBasis.Nonfinite
import SemigroupBasis.Opposite
import SemigroupBasis.RightGeneratedPowerCertificate

set_option maxRecDepth 2048

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6987

open SemigroupBasis

def routeManifestRowSHA256 : String := "754bd8a21ad0c90f7b465cf3e4e5fea616fb0eabf06db6a6ae4020e7dfa7860c"
def witnessRecordSHA256 : String := "1d0e221c5b5f44bef5e05d9161426a22f90b9499bd92051c4939df6fae0abb26"
def transferComponentSHA256 : String := "1d0e221c5b5f44bef5e05d9161426a22f90b9499bd92051c4939df6fae0abb26"
def powerCertificateSHA256 : String := "31dd6546aed8d975f5460de700ed720fda1437c46135bb9860fb3fbc7f3e7095"

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
  "093ff381941ce6a78ecdbcaaa120bb05c42ca2ead7735254075236a31792d0d8"

private def packedStateVectorCodeChunk0 (index : Nat) : Nat :=
  match index with
  | 0 => 1115780
  | 1 => 139512
  | 2 => 1655496
  | 3 => 1113186
  | 4 => 975361
  | 5 => 1091809
  | 6 => 135553
  | 7 => 46188
  | 8 => 116286
  | 9 => 1091701
  | 10 => 115638
  | 11 => 1639440
  | 12 => 1114483
  | 13 => 972768
  | 14 => 1089216
  | 15 => 882037
  | 16 => 952279
  | 17 => 951631
  | 18 => 1075789
  | 19 => 132960
  | 20 => 42229
  | 21 => 112471
  | 22 => 92850
  | 23 => 22968
  | 24 => 112363
  | 25 => 100446
  | 26 => 1089108
  | 27 => 951523
  | 28 => 1075681
  | 29 => 111715
  | 30 => 22320
  | _ => 99798

private def packedStateVectorCodeChunk1 (index : Nat) : Nat :=
  match index with
  | 0 => 1647468
  | 1 => 974065
  | 2 => 1090513
  | 3 => 879444
  | 4 => 949686
  | 5 => 949038
  | 6 => 1073196
  | 7 => 928699
  | 8 => 858961
  | 9 => 936475
  | 10 => 858313
  | 11 => 935827
  | 12 => 1083817
  | 13 => 134257
  | 14 => 39636
  | 15 => 109878
  | 16 => 88891
  | 17 => 19153
  | 18 => 96667
  | 19 => 69630
  | 20 => 19045
  | 21 => 7128
  | 22 => 109770
  | 23 => 96559
  | 24 => 108474
  | 25 => 1090405
  | 26 => 948930
  | 27 => 1073088
  | 28 => 858205
  | 29 => 935719
  | 30 => 1083709
  | _ => 109122

private def packedStateVectorCodeChunk2 (index : Nat) : Nat :=
  match index with
  | 0 => 18397
  | 1 => 95911
  | 2 => 68982
  | 3 => 6480
  | 4 => 107826
  | 5 => 880741
  | 6 => 950983
  | 7 => 950335
  | 8 => 1074493
  | 9 => 926106
  | 10 => 856368
  | 11 => 933882
  | 12 => 855720
  | 13 => 933234
  | 14 => 1081224
  | 15 => 905623
  | 16 => 843157
  | 17 => 944503
  | 18 => 904975
  | 19 => 842509
  | 20 => 943855
  | 21 => 40933
  | 22 => 111175
  | 23 => 86298
  | 24 => 16560
  | 25 => 94074
  | 26 => 65815
  | 27 => 3349
  | 28 => 104695
  | 29 => 65707
  | 30 => 53790
  | _ => 16452

private def packedStateVectorCodeChunk3 (index : Nat) : Nat :=
  match index with
  | 0 => 3241
  | 1 => 15156
  | 2 => 111067
  | 3 => 93966
  | 4 => 104587
  | 5 => 950227
  | 6 => 1074385
  | 7 => 855612
  | 8 => 933126
  | 9 => 1081116
  | 10 => 904867
  | 11 => 842401
  | 12 => 943747
  | 13 => 110419
  | 14 => 15804
  | 15 => 93318
  | 16 => 65059
  | 17 => 2593
  | 18 => 103939
  | 19 => 53142
  | 20 => 14508
  | 21 => 927403
  | 22 => 857665
  | 23 => 935179
  | 24 => 857017
  | 25 => 934531
  | 26 => 1082521
  | 27 => 903030
  | 28 => 840564
  | 29 => 941910
  | 30 => 902382
  | _ => 839916

private def packedStateVectorCodeChunk4 (index : Nat) : Nat :=
  match index with
  | 0 => 941262
  | 1 => 889819
  | 2 => 851185
  | 3 => 889171
  | 4 => 850537
  | 5 => 87595
  | 6 => 17857
  | 7 => 95371
  | 8 => 63222
  | 9 => 756
  | 10 => 102102
  | 11 => 50011
  | 12 => 11377
  | 13 => 63114
  | 14 => 49903
  | 15 => 61818
  | 16 => 17749
  | 17 => 648
  | 18 => 11269
  | 19 => 95263
  | 20 => 101994
  | 21 => 856909
  | 22 => 934423
  | 23 => 1082413
  | 24 => 902274
  | 25 => 839808
  | 26 => 941154
  | 27 => 889063
  | 28 => 850429
  | 29 => 17101
  | 30 => 94615
  | _ => 62466

private def packedStateVectorCodeChunk5 (index : Nat) : Nat :=
  match index with
  | 0 => 0
  | 1 => 101346
  | 2 => 49255
  | 3 => 10621
  | 4 => 61170
  | 5 => 904327
  | 6 => 841861
  | 7 => 943207
  | 8 => 903679
  | 9 => 841213
  | 10 => 942559
  | 11 => 887226
  | 12 => 848592
  | 13 => 886578
  | 14 => 847944
  | 15 => 897847
  | 16 => 897199
  | 17 => 64519
  | 18 => 2053
  | 19 => 103399
  | 20 => 47418
  | 21 => 8784
  | 22 => 58039
  | 23 => 64411
  | 24 => 47310
  | 25 => 57931
  | 26 => 1945
  | 27 => 8676
  | 28 => 103291
  | 29 => 903571
  | 30 => 841105
  | _ => 942451

private def packedStateVectorCodeChunk6 (index : Nat) : Nat :=
  match index with
  | 0 => 886470
  | 1 => 847836
  | 2 => 897091
  | 3 => 63763
  | 4 => 1297
  | 5 => 102643
  | 6 => 46662
  | 7 => 8028
  | 8 => 57283
  | 9 => 888523
  | 10 => 849889
  | 11 => 887875
  | 12 => 849241
  | 13 => 895254
  | 14 => 894606
  | 15 => 48715
  | 16 => 10081
  | 17 => 55446
  | 18 => 48607
  | 19 => 55338
  | 20 => 9973
  | 21 => 887767
  | 22 => 849133
  | 23 => 894498
  | 24 => 47959
  | 25 => 9325
  | 26 => 54690
  | 27 => 896551
  | 28 => 895903
  | 29 => 56743
  | 30 => 56635
  | _ => 895795

private def packedStateVectorCodeChunk7 (index : Nat) : Nat :=
  match index with
  | _ => 55987

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
      | 2 => (3 : Fin 6)
      | 3 => (5 : Fin 6)
      | 4 => (2 : Fin 6)
      | 5 => (5 : Fin 6)
      | 6 => (5 : Fin 6)
      | _ => (3 : Fin 6)
  | 1 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (2 : Fin 6)
      | 2 => (5 : Fin 6)
      | 3 => (3 : Fin 6)
      | 4 => (5 : Fin 6)
      | 5 => (5 : Fin 6)
      | 6 => (2 : Fin 6)
      | _ => (0 : Fin 6)
  | _ =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (2 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (5 : Fin 6)
      | 5 => (2 : Fin 6)
      | 6 => (5 : Fin 6)
      | _ => (5 : Fin 6)

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
  if code = 0 then (160 : Fin 225) else
  if code = 648 then (145 : Fin 225) else
  if code = 756 then (137 : Fin 225) else
  if code = 1297 then (196 : Fin 225) else
  if code = 1945 then (186 : Fin 225) else
  if code = 2053 then (178 : Fin 225) else
  if code = 2593 then (113 : Fin 225) else
  if code = 3241 then (96 : Fin 225) else
  if code = 3349 then (91 : Fin 225) else
  if code = 6480 then (67 : Fin 225) else
  if code = 7128 then (53 : Fin 225) else
  if code = 8028 then (199 : Fin 225) else
  if code = 8676 then (187 : Fin 225) else
  if code = 8784 then (181 : Fin 225) else
  if code = 9325 then (217 : Fin 225) else
  if code = 9973 then (212 : Fin 225) else
  if code = 10081 then (208 : Fin 225) else
  if code = 10621 then (163 : Fin 225) else
  if code = 11269 then (146 : Fin 225) else
  if code = 11377 then (140 : Fin 225) else
  if code = 14508 then (116 : Fin 225) else
  if code = 15156 then (97 : Fin 225) else
  if code = 15804 then (110 : Fin 225) else
  if code = 16452 then (95 : Fin 225) else
  if code = 16560 then (88 : Fin 225) else
  if code = 17101 then (157 : Fin 225) else
  if code = 17749 then (144 : Fin 225) else
  if code = 17857 then (134 : Fin 225) else
  if code = 18397 then (64 : Fin 225) else
  if code = 19045 then (52 : Fin 225) else
  if code = 19153 then (49 : Fin 225) else
  if code = 22320 then (30 : Fin 225) else
  (0 : Fin 225)

private def decodeStateCodeChunk1 (code : Nat) : Fin 225 :=
  if code = 22968 then (23 : Fin 225) else
  if code = 39636 then (46 : Fin 225) else
  if code = 40933 then (85 : Fin 225) else
  if code = 42229 then (20 : Fin 225) else
  if code = 46188 then (7 : Fin 225) else
  if code = 46662 then (198 : Fin 225) else
  if code = 47310 then (184 : Fin 225) else
  if code = 47418 then (180 : Fin 225) else
  if code = 47959 then (216 : Fin 225) else
  if code = 48607 then (210 : Fin 225) else
  if code = 48715 then (207 : Fin 225) else
  if code = 49255 then (162 : Fin 225) else
  if code = 49903 then (142 : Fin 225) else
  if code = 50011 then (139 : Fin 225) else
  if code = 53142 then (115 : Fin 225) else
  if code = 53790 then (94 : Fin 225) else
  if code = 54690 then (218 : Fin 225) else
  if code = 55338 then (211 : Fin 225) else
  if code = 55446 then (209 : Fin 225) else
  if code = 55987 then (224 : Fin 225) else
  if code = 56635 then (222 : Fin 225) else
  if code = 56743 then (221 : Fin 225) else
  if code = 57283 then (200 : Fin 225) else
  if code = 57931 then (185 : Fin 225) else
  if code = 58039 then (182 : Fin 225) else
  if code = 61170 then (164 : Fin 225) else
  if code = 61818 then (143 : Fin 225) else
  if code = 62466 then (159 : Fin 225) else
  if code = 63114 then (141 : Fin 225) else
  if code = 63222 then (136 : Fin 225) else
  if code = 63763 then (195 : Fin 225) else
  if code = 64411 then (183 : Fin 225) else
  (0 : Fin 225)

private def decodeStateCodeChunk2 (code : Nat) : Fin 225 :=
  if code = 64519 then (177 : Fin 225) else
  if code = 65059 then (112 : Fin 225) else
  if code = 65707 then (93 : Fin 225) else
  if code = 65815 then (90 : Fin 225) else
  if code = 68982 then (66 : Fin 225) else
  if code = 69630 then (51 : Fin 225) else
  if code = 86298 then (87 : Fin 225) else
  if code = 87595 then (133 : Fin 225) else
  if code = 88891 then (48 : Fin 225) else
  if code = 92850 then (22 : Fin 225) else
  if code = 93318 then (111 : Fin 225) else
  if code = 93966 then (99 : Fin 225) else
  if code = 94074 then (89 : Fin 225) else
  if code = 94615 then (158 : Fin 225) else
  if code = 95263 then (147 : Fin 225) else
  if code = 95371 then (135 : Fin 225) else
  if code = 95911 then (65 : Fin 225) else
  if code = 96559 then (55 : Fin 225) else
  if code = 96667 then (50 : Fin 225) else
  if code = 99798 then (31 : Fin 225) else
  if code = 100446 then (25 : Fin 225) else
  if code = 101346 then (161 : Fin 225) else
  if code = 101994 then (148 : Fin 225) else
  if code = 102102 then (138 : Fin 225) else
  if code = 102643 then (197 : Fin 225) else
  if code = 103291 then (188 : Fin 225) else
  if code = 103399 then (179 : Fin 225) else
  if code = 103939 then (114 : Fin 225) else
  if code = 104587 then (100 : Fin 225) else
  if code = 104695 then (92 : Fin 225) else
  if code = 107826 then (68 : Fin 225) else
  if code = 108474 then (56 : Fin 225) else
  (0 : Fin 225)

private def decodeStateCodeChunk3 (code : Nat) : Fin 225 :=
  if code = 109122 then (63 : Fin 225) else
  if code = 109770 then (54 : Fin 225) else
  if code = 109878 then (47 : Fin 225) else
  if code = 110419 then (109 : Fin 225) else
  if code = 111067 then (98 : Fin 225) else
  if code = 111175 then (86 : Fin 225) else
  if code = 111715 then (29 : Fin 225) else
  if code = 112363 then (24 : Fin 225) else
  if code = 112471 then (21 : Fin 225) else
  if code = 115638 then (10 : Fin 225) else
  if code = 116286 then (8 : Fin 225) else
  if code = 132960 then (19 : Fin 225) else
  if code = 134257 then (45 : Fin 225) else
  if code = 135553 then (6 : Fin 225) else
  if code = 139512 then (1 : Fin 225) else
  if code = 839808 then (153 : Fin 225) else
  if code = 839916 then (127 : Fin 225) else
  if code = 840564 then (124 : Fin 225) else
  if code = 841105 then (190 : Fin 225) else
  if code = 841213 then (169 : Fin 225) else
  if code = 841861 then (166 : Fin 225) else
  if code = 842401 then (107 : Fin 225) else
  if code = 842509 then (83 : Fin 225) else
  if code = 843157 then (80 : Fin 225) else
  if code = 847836 then (193 : Fin 225) else
  if code = 847944 then (174 : Fin 225) else
  if code = 848592 then (172 : Fin 225) else
  if code = 849133 then (214 : Fin 225) else
  if code = 849241 then (204 : Fin 225) else
  if code = 849889 then (202 : Fin 225) else
  if code = 850429 then (156 : Fin 225) else
  if code = 850537 then (132 : Fin 225) else
  (0 : Fin 225)

private def decodeStateCodeChunk4 (code : Nat) : Fin 225 :=
  if code = 851185 then (130 : Fin 225) else
  if code = 855612 then (103 : Fin 225) else
  if code = 855720 then (76 : Fin 225) else
  if code = 856368 then (74 : Fin 225) else
  if code = 856909 then (149 : Fin 225) else
  if code = 857017 then (120 : Fin 225) else
  if code = 857665 then (118 : Fin 225) else
  if code = 858205 then (60 : Fin 225) else
  if code = 858313 then (42 : Fin 225) else
  if code = 858961 then (40 : Fin 225) else
  if code = 879444 then (35 : Fin 225) else
  if code = 880741 then (69 : Fin 225) else
  if code = 882037 then (15 : Fin 225) else
  if code = 886470 then (192 : Fin 225) else
  if code = 886578 then (173 : Fin 225) else
  if code = 887226 then (171 : Fin 225) else
  if code = 887767 then (213 : Fin 225) else
  if code = 887875 then (203 : Fin 225) else
  if code = 888523 then (201 : Fin 225) else
  if code = 889063 then (155 : Fin 225) else
  if code = 889171 then (131 : Fin 225) else
  if code = 889819 then (129 : Fin 225) else
  if code = 894498 then (215 : Fin 225) else
  if code = 894606 then (206 : Fin 225) else
  if code = 895254 then (205 : Fin 225) else
  if code = 895795 then (223 : Fin 225) else
  if code = 895903 then (220 : Fin 225) else
  if code = 896551 then (219 : Fin 225) else
  if code = 897091 then (194 : Fin 225) else
  if code = 897199 then (176 : Fin 225) else
  if code = 897847 then (175 : Fin 225) else
  if code = 902274 then (152 : Fin 225) else
  (0 : Fin 225)

private def decodeStateCodeChunk5 (code : Nat) : Fin 225 :=
  if code = 902382 then (126 : Fin 225) else
  if code = 903030 then (123 : Fin 225) else
  if code = 903571 then (189 : Fin 225) else
  if code = 903679 then (168 : Fin 225) else
  if code = 904327 then (165 : Fin 225) else
  if code = 904867 then (106 : Fin 225) else
  if code = 904975 then (82 : Fin 225) else
  if code = 905623 then (79 : Fin 225) else
  if code = 926106 then (73 : Fin 225) else
  if code = 927403 then (117 : Fin 225) else
  if code = 928699 then (39 : Fin 225) else
  if code = 933126 then (104 : Fin 225) else
  if code = 933234 then (77 : Fin 225) else
  if code = 933882 then (75 : Fin 225) else
  if code = 934423 then (150 : Fin 225) else
  if code = 934531 then (121 : Fin 225) else
  if code = 935179 then (119 : Fin 225) else
  if code = 935719 then (61 : Fin 225) else
  if code = 935827 then (43 : Fin 225) else
  if code = 936475 then (41 : Fin 225) else
  if code = 941154 then (154 : Fin 225) else
  if code = 941262 then (128 : Fin 225) else
  if code = 941910 then (125 : Fin 225) else
  if code = 942451 then (191 : Fin 225) else
  if code = 942559 then (170 : Fin 225) else
  if code = 943207 then (167 : Fin 225) else
  if code = 943747 then (108 : Fin 225) else
  if code = 943855 then (84 : Fin 225) else
  if code = 944503 then (81 : Fin 225) else
  if code = 948930 then (58 : Fin 225) else
  if code = 949038 then (37 : Fin 225) else
  if code = 949686 then (36 : Fin 225) else
  (0 : Fin 225)

private def decodeStateCodeChunk6 (code : Nat) : Fin 225 :=
  if code = 950227 then (101 : Fin 225) else
  if code = 950335 then (71 : Fin 225) else
  if code = 950983 then (70 : Fin 225) else
  if code = 951523 then (27 : Fin 225) else
  if code = 951631 then (17 : Fin 225) else
  if code = 952279 then (16 : Fin 225) else
  if code = 972768 then (13 : Fin 225) else
  if code = 974065 then (33 : Fin 225) else
  if code = 975361 then (4 : Fin 225) else
  if code = 1073088 then (59 : Fin 225) else
  if code = 1073196 then (38 : Fin 225) else
  if code = 1074385 then (102 : Fin 225) else
  if code = 1074493 then (72 : Fin 225) else
  if code = 1075681 then (28 : Fin 225) else
  if code = 1075789 then (18 : Fin 225) else
  if code = 1081116 then (105 : Fin 225) else
  if code = 1081224 then (78 : Fin 225) else
  if code = 1082413 then (151 : Fin 225) else
  if code = 1082521 then (122 : Fin 225) else
  if code = 1083709 then (62 : Fin 225) else
  if code = 1083817 then (44 : Fin 225) else
  if code = 1089108 then (26 : Fin 225) else
  if code = 1089216 then (14 : Fin 225) else
  if code = 1090405 then (57 : Fin 225) else
  if code = 1090513 then (34 : Fin 225) else
  if code = 1091701 then (9 : Fin 225) else
  if code = 1091809 then (5 : Fin 225) else
  if code = 1113186 then (3 : Fin 225) else
  if code = 1114483 then (12 : Fin 225) else
  if code = 1115780 then (0 : Fin 225) else
  if code = 1639440 then (11 : Fin 225) else
  if code = 1647468 then (32 : Fin 225) else
  (0 : Fin 225)

private def decodeStateCodeChunk7 (code : Nat) : Fin 225 :=
  if code = 1655496 then (2 : Fin 225) else
  (0 : Fin 225)

private def stateVectorCode
    (vector : Fin 8 -> Fin 6) : Nat :=
  (vector (0 : Fin 8)).val + 6 * ((vector (1 : Fin 8)).val + 6 * ((vector (2 : Fin 8)).val + 6 * ((vector (3 : Fin 8)).val + 6 * ((vector (4 : Fin 8)).val + 6 * ((vector (5 : Fin 8)).val + 6 * ((vector (6 : Fin 8)).val + 6 * ((vector (7 : Fin 8)).val)))))))

private def decodeStateCode (code : Nat) : Fin 225 :=
  if code < 22968 then decodeStateCodeChunk0 code else
  if code < 64519 then decodeStateCodeChunk1 code else
  if code < 109122 then decodeStateCodeChunk2 code else
  if code < 851185 then decodeStateCodeChunk3 code else
  if code < 902382 then decodeStateCodeChunk4 code else
  if code < 950227 then decodeStateCodeChunk5 code else
  if code < 1655496 then decodeStateCodeChunk6 code else
  decodeStateCodeChunk7 code

private def decodeState
    (vector : Fin 8 -> Fin 6) : Fin 225 :=
  decodeStateCode (stateVectorCode vector)

set_option maxHeartbeats 2000000 in
private theorem decodeState_stateVector (state : Fin 225) :
    decodeState (stateVector state) = state := by
  decide +revert

set_option maxHeartbeats 2000000 in
private theorem transitionMap :
    forall (state : Fin 225)
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
    forall (state : Fin 225)
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
    (U := Fin 225)
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
        (Fin 8) targetValid
    have subValid :=
      powerCertificate.embedding.pullback_identity identity powerValid
    exact quotient.pushforwardIdentity identity subValid

/-- First-layer generic-CAS basis wrapper for `S6_6987`. -/
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

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6987
