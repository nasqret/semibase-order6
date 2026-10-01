import SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6494Representative
import SemigroupBasis.FiniteNilpotentCounterexample
import SemigroupBasis.Nonfinite
import SemigroupBasis.Opposite
import SemigroupBasis.RightGeneratedPowerCertificate

set_option maxRecDepth 2048

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6844

open SemigroupBasis

def routeManifestRowSHA256 : String := "af46217c7a43ee927a9db8554c439cdc1c908e6cbcd01c7b9f8869369d7b4723"
def witnessRecordSHA256 : String := "cc0145d97225578a11910aa11c2722d6510f14ca106458d2dbb62eb46be14c18"
def transferComponentSHA256 : String := "cc0145d97225578a11910aa11c2722d6510f14ca106458d2dbb62eb46be14c18"
def powerCertificateSHA256 : String := "ecaae8ffebe77be294ec2ed88a3cd62e6df39c6bba2e2ed646d8d45b2bfe1f44"

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
    if left = 1 then row6 0 0 2 3 4 1 right else
      if left = 2 then row6 2 2 0 4 3 2 right else
        if left = 3 then row6 0 0 2 3 4 3 right else
          if left = 4 then row6 2 2 0 4 3 4 right else
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
  "24a764c9f740483fc433607dd97c66cff11e62c54a972f9ed5e5fd6863e2e57d"

private def packedStateVectorCodeChunk0 (index : Nat) : Nat :=
  match index with
  | 0 => 120854377
  | 1 => 1071572982
  | 2 => 331203204
  | 3 => 60333768
  | 4 => 829638288
  | 5 => 89493984
  | 6 => 829661616
  | 7 => 334220256
  | 8 => 1060140960
  | 9 => 89400672
  | 10 => 1029907872
  | 11 => 310767840
  | 12 => 60380424
  | 13 => 769125456
  | 14 => 28973376
  | 15 => 92285568
  | 16 => 818439552
  | 17 => 788206464
  | 18 => 69058656
  | 19 => 769148784
  | 20 => 92308896
  | 21 => 818462880
  | 22 => 1069892064
  | 23 => 342944928
  | 24 => 818369568
  | 25 => 1069938720
  | 26 => 28833408
  | 27 => 788113152
  | 28 => 68965344
  | 29 => 788136480
  | 30 => 322789536
  | _ => 1049783328

private def packedStateVectorCodeChunk1 (index : Nat) : Nat :=
  match index with
  | 0 => 330923232
  | 1 => 769172112
  | 2 => 29020032
  | 3 => 31772736
  | 4 => 757926720
  | 5 => 727693632
  | 6 => 8538048
  | 7 => 827957376
  | 8 => 101243520
  | 9 => 828237312
  | 10 => 81088128
  | 11 => 808081920
  | 12 => 89214048
  | 13 => 769195440
  | 14 => 31796064
  | 15 => 757950048
  | 16 => 827980704
  | 17 => 101266848
  | 18 => 828260640
  | 19 => 1058461344
  | 20 => 101173536
  | 21 => 332587296
  | 22 => 757810080
  | 23 => 828167328
  | 24 => 1059861024
  | 25 => 28926720
  | 26 => 727553664
  | 27 => 8398080
  | 28 => 80994816
  | 29 => 807988608
  | 30 => 89120736
  | _ => 727576992

private def packedStateVectorCodeChunk2 (index : Nat) : Nat :=
  match index with
  | 0 => 81018144
  | 1 => 808011936
  | 2 => 1028228256
  | 3 => 302354208
  | 4 => 1029627936
  | 5 => 31819392
  | 6 => 757973376
  | 7 => 727740288
  | 8 => 8584704
  | 9 => 767444544
  | 10 => 40730688
  | 11 => 767724480
  | 12 => 20575296
  | 13 => 747569088
  | 14 => 28693440
  | 15 => 816759936
  | 16 => 90885888
  | 17 => 818159616
  | 18 => 786526848
  | 19 => 60652800
  | 20 => 787926528
  | 21 => 31842720
  | 22 => 757996704
  | 23 => 767467872
  | 24 => 40754016
  | 25 => 767747808
  | 26 => 816783264
  | 27 => 90909216
  | 28 => 818182944
  | 29 => 816689952
  | 30 => 1068259104
  | _ => 40614048

private def packedStateVectorCodeChunk3 (index : Nat) : Nat :=
  match index with
  | 0 => 90815904
  | 1 => 342664992
  | 2 => 757903392
  | 3 => 767607840
  | 4 => 818089632
  | 5 => 727646976
  | 6 => 8491392
  | 7 => 20435328
  | 8 => 747429120
  | 9 => 28553472
  | 10 => 786433536
  | 11 => 60559488
  | 12 => 787833216
  | 13 => 727670304
  | 14 => 20458656
  | 15 => 747452448
  | 16 => 786456864
  | 17 => 60582816
  | 18 => 787856544
  | 19 => 1048103712
  | 20 => 322509600
  | 21 => 767491200
  | 22 => 40777344
  | 23 => 767771136
  | 24 => 20621952
  | 25 => 747615744
  | 26 => 28740096
  | 27 => 756247104
  | 28 => 30373056
  | 29 => 757646784
  | 30 => 726014016
  | _ => 139968

private def packedStateVectorCodeChunk4 (index : Nat) : Nat :=
  match index with
  | 0 => 727413696
  | 1 => 826557696
  | 2 => 100963584
  | 3 => 806402304
  | 4 => 80808192
  | 5 => 767514528
  | 6 => 40800672
  | 7 => 767794464
  | 8 => 756270432
  | 9 => 30396384
  | 10 => 757670112
  | 11 => 826581024
  | 12 => 100986912
  | 13 => 756130464
  | 14 => 826487712
  | 15 => 1058181408
  | 16 => 40707360
  | 17 => 30256416
  | 18 => 100893600
  | 19 => 767701152
  | 20 => 757530144
  | 21 => 20528640
  | 22 => 747522432
  | 23 => 28646784
  | 24 => 725874048
  | 25 => 0
  | 26 => 727273728
  | 27 => 806308992
  | 28 => 80714880
  | 29 => 20551968
  | 30 => 747545760
  | _ => 725897376

private def packedStateVectorCodeChunk5 (index : Nat) : Nat :=
  match index with
  | 0 => 23328
  | 1 => 727297056
  | 2 => 806332320
  | 3 => 80738208
  | 4 => 1027948320
  | 5 => 756293760
  | 6 => 30419712
  | 7 => 757693440
  | 8 => 726060672
  | 9 => 186624
  | 10 => 727460352
  | 11 => 766044864
  | 12 => 40450752
  | 13 => 745889472
  | 14 => 20295360
  | 15 => 816480000
  | 16 => 786246912
  | 17 => 756317088
  | 18 => 30443040
  | 19 => 757716768
  | 20 => 766068192
  | 21 => 40474080
  | 22 => 816503328
  | 23 => 756223776
  | 24 => 765928224
  | 25 => 816410016
  | 26 => 30349728
  | 27 => 40334112
  | 28 => 757623456
  | 29 => 725967360
  | 30 => 93312
  | _ => 727367040

private def packedStateVectorCodeChunk6 (index : Nat) : Nat :=
  match index with
  | 0 => 745749504
  | 1 => 20155392
  | 2 => 786153600
  | 3 => 725990688
  | 4 => 116640
  | 5 => 727390368
  | 6 => 745772832
  | 7 => 20178720
  | 8 => 786176928
  | 9 => 766091520
  | 10 => 40497408
  | 11 => 745936128
  | 12 => 20342016
  | 13 => 755967168
  | 14 => 725734080
  | 15 => 766114848
  | 16 => 40520736
  | 17 => 755990496
  | 18 => 766021536
  | 19 => 755850528
  | 20 => 40427424
  | 21 => 745842816
  | 22 => 20248704
  | 23 => 725594112
  | 24 => 745866144
  | 25 => 20272032
  | 26 => 725617440
  | 27 => 756013824
  | 28 => 725780736
  | 29 => 756037152
  | 30 => 755943840
  | _ => 725687424

private def packedStateVectorCodeChunk7 (index : Nat) : Nat :=
  match index with
  | _ => 725710752

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
    (coordinate : Fin 12) : Fin 6 :=
  ⟨(packedStateVectorCode state / 6 ^ coordinate.val) % 6,
    Nat.mod_lt _ (by decide)⟩

def generatorVector (generator : Fin 3)
    (coordinate : Fin 12) : Fin 6 :=
  match generator.val with
  | 0 =>
      match coordinate.val with
      | 0 => (1 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (5 : Fin 6)
      | 4 => (5 : Fin 6)
      | 5 => (1 : Fin 6)
      | 6 => (4 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (5 : Fin 6)
      | 10 => (1 : Fin 6)
      | _ => (0 : Fin 6)
  | 1 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (1 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (1 : Fin 6)
      | 5 => (3 : Fin 6)
      | 6 => (5 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (1 : Fin 6)
      | 9 => (4 : Fin 6)
      | 10 => (5 : Fin 6)
      | _ => (2 : Fin 6)
  | _ =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (1 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (5 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (1 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (2 : Fin 6)
      | 10 => (5 : Fin 6)
      | _ => (0 : Fin 6)

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
  if code = 0 then (153 : Fin 225) else
  if code = 23328 then (160 : Fin 225) else
  if code = 93312 then (190 : Fin 225) else
  if code = 116640 then (196 : Fin 225) else
  if code = 139968 then (127 : Fin 225) else
  if code = 186624 then (169 : Fin 225) else
  if code = 8398080 then (59 : Fin 225) else
  if code = 8491392 then (102 : Fin 225) else
  if code = 8538048 then (38 : Fin 225) else
  if code = 8584704 then (72 : Fin 225) else
  if code = 20155392 then (193 : Fin 225) else
  if code = 20178720 then (199 : Fin 225) else
  if code = 20248704 then (214 : Fin 225) else
  if code = 20272032 then (217 : Fin 225) else
  if code = 20295360 then (174 : Fin 225) else
  if code = 20342016 then (204 : Fin 225) else
  if code = 20435328 then (103 : Fin 225) else
  if code = 20458656 then (110 : Fin 225) else
  if code = 20528640 then (149 : Fin 225) else
  if code = 20551968 then (157 : Fin 225) else
  if code = 20575296 then (76 : Fin 225) else
  if code = 20621952 then (120 : Fin 225) else
  if code = 28553472 then (105 : Fin 225) else
  if code = 28646784 then (151 : Fin 225) else
  if code = 28693440 then (78 : Fin 225) else
  if code = 28740096 then (122 : Fin 225) else
  if code = 28833408 then (26 : Fin 225) else
  if code = 28926720 then (57 : Fin 225) else
  if code = 28973376 then (14 : Fin 225) else
  if code = 29020032 then (34 : Fin 225) else
  if code = 30256416 then (145 : Fin 225) else
  if code = 30349728 then (186 : Fin 225) else
  (0 : Fin 225)

private def decodeStateCodeChunk1 (code : Nat) : Fin 225 :=
  if code = 30373056 then (124 : Fin 225) else
  if code = 30396384 then (137 : Fin 225) else
  if code = 30419712 then (166 : Fin 225) else
  if code = 30443040 then (178 : Fin 225) else
  if code = 31772736 then (35 : Fin 225) else
  if code = 31796064 then (46 : Fin 225) else
  if code = 31819392 then (69 : Fin 225) else
  if code = 31842720 then (85 : Fin 225) else
  if code = 40334112 then (187 : Fin 225) else
  if code = 40427424 then (212 : Fin 225) else
  if code = 40450752 then (172 : Fin 225) else
  if code = 40474080 then (181 : Fin 225) else
  if code = 40497408 then (202 : Fin 225) else
  if code = 40520736 then (208 : Fin 225) else
  if code = 40614048 then (95 : Fin 225) else
  if code = 40707360 then (144 : Fin 225) else
  if code = 40730688 then (74 : Fin 225) else
  if code = 40754016 then (88 : Fin 225) else
  if code = 40777344 then (118 : Fin 225) else
  if code = 40800672 then (134 : Fin 225) else
  if code = 60333768 then (3 : Fin 225) else
  if code = 60380424 then (12 : Fin 225) else
  if code = 60559488 then (107 : Fin 225) else
  if code = 60582816 then (113 : Fin 225) else
  if code = 60652800 then (83 : Fin 225) else
  if code = 68965344 then (28 : Fin 225) else
  if code = 69058656 then (18 : Fin 225) else
  if code = 80714880 then (156 : Fin 225) else
  if code = 80738208 then (163 : Fin 225) else
  if code = 80808192 then (132 : Fin 225) else
  if code = 80994816 then (60 : Fin 225) else
  if code = 81018144 then (64 : Fin 225) else
  (0 : Fin 225)

private def decodeStateCodeChunk2 (code : Nat) : Fin 225 :=
  if code = 81088128 then (42 : Fin 225) else
  if code = 89120736 then (62 : Fin 225) else
  if code = 89214048 then (44 : Fin 225) else
  if code = 89400672 then (9 : Fin 225) else
  if code = 89493984 then (5 : Fin 225) else
  if code = 90815904 then (96 : Fin 225) else
  if code = 90885888 then (80 : Fin 225) else
  if code = 90909216 then (91 : Fin 225) else
  if code = 92285568 then (15 : Fin 225) else
  if code = 92308896 then (20 : Fin 225) else
  if code = 100893600 then (146 : Fin 225) else
  if code = 100963584 then (130 : Fin 225) else
  if code = 100986912 then (140 : Fin 225) else
  if code = 101173536 then (52 : Fin 225) else
  if code = 101243520 then (40 : Fin 225) else
  if code = 101266848 then (49 : Fin 225) else
  if code = 120854377 then (0 : Fin 225) else
  if code = 302354208 then (67 : Fin 225) else
  if code = 310767840 then (11 : Fin 225) else
  if code = 322509600 then (116 : Fin 225) else
  if code = 322789536 then (30 : Fin 225) else
  if code = 330923232 then (32 : Fin 225) else
  if code = 331203204 then (2 : Fin 225) else
  if code = 332587296 then (53 : Fin 225) else
  if code = 334220256 then (7 : Fin 225) else
  if code = 342664992 then (97 : Fin 225) else
  if code = 342944928 then (23 : Fin 225) else
  if code = 725594112 then (215 : Fin 225) else
  if code = 725617440 then (218 : Fin 225) else
  if code = 725687424 then (223 : Fin 225) else
  if code = 725710752 then (224 : Fin 225) else
  if code = 725734080 then (206 : Fin 225) else
  (0 : Fin 225)

private def decodeStateCodeChunk3 (code : Nat) : Fin 225 :=
  if code = 725780736 then (220 : Fin 225) else
  if code = 725874048 then (152 : Fin 225) else
  if code = 725897376 then (159 : Fin 225) else
  if code = 725967360 then (189 : Fin 225) else
  if code = 725990688 then (195 : Fin 225) else
  if code = 726014016 then (126 : Fin 225) else
  if code = 726060672 then (168 : Fin 225) else
  if code = 727273728 then (154 : Fin 225) else
  if code = 727297056 then (161 : Fin 225) else
  if code = 727367040 then (191 : Fin 225) else
  if code = 727390368 then (197 : Fin 225) else
  if code = 727413696 then (128 : Fin 225) else
  if code = 727460352 then (170 : Fin 225) else
  if code = 727553664 then (58 : Fin 225) else
  if code = 727576992 then (63 : Fin 225) else
  if code = 727646976 then (101 : Fin 225) else
  if code = 727670304 then (109 : Fin 225) else
  if code = 727693632 then (37 : Fin 225) else
  if code = 727740288 then (71 : Fin 225) else
  if code = 745749504 then (192 : Fin 225) else
  if code = 745772832 then (198 : Fin 225) else
  if code = 745842816 then (213 : Fin 225) else
  if code = 745866144 then (216 : Fin 225) else
  if code = 745889472 then (173 : Fin 225) else
  if code = 745936128 then (203 : Fin 225) else
  if code = 747429120 then (104 : Fin 225) else
  if code = 747452448 then (111 : Fin 225) else
  if code = 747522432 then (150 : Fin 225) else
  if code = 747545760 then (158 : Fin 225) else
  if code = 747569088 then (77 : Fin 225) else
  if code = 747615744 then (121 : Fin 225) else
  if code = 755850528 then (211 : Fin 225) else
  (0 : Fin 225)

private def decodeStateCodeChunk4 (code : Nat) : Fin 225 :=
  if code = 755943840 then (222 : Fin 225) else
  if code = 755967168 then (205 : Fin 225) else
  if code = 755990496 then (209 : Fin 225) else
  if code = 756013824 then (219 : Fin 225) else
  if code = 756037152 then (221 : Fin 225) else
  if code = 756130464 then (141 : Fin 225) else
  if code = 756223776 then (183 : Fin 225) else
  if code = 756247104 then (123 : Fin 225) else
  if code = 756270432 then (136 : Fin 225) else
  if code = 756293760 then (165 : Fin 225) else
  if code = 756317088 then (177 : Fin 225) else
  if code = 757530144 then (148 : Fin 225) else
  if code = 757623456 then (188 : Fin 225) else
  if code = 757646784 then (125 : Fin 225) else
  if code = 757670112 then (138 : Fin 225) else
  if code = 757693440 then (167 : Fin 225) else
  if code = 757716768 then (179 : Fin 225) else
  if code = 757810080 then (54 : Fin 225) else
  if code = 757903392 then (98 : Fin 225) else
  if code = 757926720 then (36 : Fin 225) else
  if code = 757950048 then (47 : Fin 225) else
  if code = 757973376 then (70 : Fin 225) else
  if code = 757996704 then (86 : Fin 225) else
  if code = 765928224 then (184 : Fin 225) else
  if code = 766021536 then (210 : Fin 225) else
  if code = 766044864 then (171 : Fin 225) else
  if code = 766068192 then (180 : Fin 225) else
  if code = 766091520 then (201 : Fin 225) else
  if code = 766114848 then (207 : Fin 225) else
  if code = 767444544 then (73 : Fin 225) else
  if code = 767467872 then (87 : Fin 225) else
  if code = 767491200 then (117 : Fin 225) else
  (0 : Fin 225)

private def decodeStateCodeChunk5 (code : Nat) : Fin 225 :=
  if code = 767514528 then (133 : Fin 225) else
  if code = 767607840 then (99 : Fin 225) else
  if code = 767701152 then (147 : Fin 225) else
  if code = 767724480 then (75 : Fin 225) else
  if code = 767747808 then (89 : Fin 225) else
  if code = 767771136 then (119 : Fin 225) else
  if code = 767794464 then (135 : Fin 225) else
  if code = 769125456 then (13 : Fin 225) else
  if code = 769148784 then (19 : Fin 225) else
  if code = 769172112 then (33 : Fin 225) else
  if code = 769195440 then (45 : Fin 225) else
  if code = 786153600 then (194 : Fin 225) else
  if code = 786176928 then (200 : Fin 225) else
  if code = 786246912 then (176 : Fin 225) else
  if code = 786433536 then (106 : Fin 225) else
  if code = 786456864 then (112 : Fin 225) else
  if code = 786526848 then (82 : Fin 225) else
  if code = 787833216 then (108 : Fin 225) else
  if code = 787856544 then (114 : Fin 225) else
  if code = 787926528 then (84 : Fin 225) else
  if code = 788113152 then (27 : Fin 225) else
  if code = 788136480 then (29 : Fin 225) else
  if code = 788206464 then (17 : Fin 225) else
  if code = 806308992 then (155 : Fin 225) else
  if code = 806332320 then (162 : Fin 225) else
  if code = 806402304 then (131 : Fin 225) else
  if code = 807988608 then (61 : Fin 225) else
  if code = 808011936 then (65 : Fin 225) else
  if code = 808081920 then (43 : Fin 225) else
  if code = 816410016 then (185 : Fin 225) else
  if code = 816480000 then (175 : Fin 225) else
  if code = 816503328 then (182 : Fin 225) else
  (0 : Fin 225)

private def decodeStateCodeChunk6 (code : Nat) : Fin 225 :=
  if code = 816689952 then (93 : Fin 225) else
  if code = 816759936 then (79 : Fin 225) else
  if code = 816783264 then (90 : Fin 225) else
  if code = 818089632 then (100 : Fin 225) else
  if code = 818159616 then (81 : Fin 225) else
  if code = 818182944 then (92 : Fin 225) else
  if code = 818369568 then (24 : Fin 225) else
  if code = 818439552 then (16 : Fin 225) else
  if code = 818462880 then (21 : Fin 225) else
  if code = 826487712 then (142 : Fin 225) else
  if code = 826557696 then (129 : Fin 225) else
  if code = 826581024 then (139 : Fin 225) else
  if code = 827957376 then (39 : Fin 225) else
  if code = 827980704 then (48 : Fin 225) else
  if code = 828167328 then (55 : Fin 225) else
  if code = 828237312 then (41 : Fin 225) else
  if code = 828260640 then (50 : Fin 225) else
  if code = 829638288 then (4 : Fin 225) else
  if code = 829661616 then (6 : Fin 225) else
  if code = 1027948320 then (164 : Fin 225) else
  if code = 1028228256 then (66 : Fin 225) else
  if code = 1029627936 then (68 : Fin 225) else
  if code = 1029907872 then (10 : Fin 225) else
  if code = 1048103712 then (115 : Fin 225) else
  if code = 1049783328 then (31 : Fin 225) else
  if code = 1058181408 then (143 : Fin 225) else
  if code = 1058461344 then (51 : Fin 225) else
  if code = 1059861024 then (56 : Fin 225) else
  if code = 1060140960 then (8 : Fin 225) else
  if code = 1068259104 then (94 : Fin 225) else
  if code = 1069892064 then (22 : Fin 225) else
  if code = 1069938720 then (25 : Fin 225) else
  (0 : Fin 225)

private def decodeStateCodeChunk7 (code : Nat) : Fin 225 :=
  if code = 1071572982 then (1 : Fin 225) else
  (0 : Fin 225)

private def stateVectorCode
    (vector : Fin 12 -> Fin 6) : Nat :=
  (vector (0 : Fin 12)).val + 6 * ((vector (1 : Fin 12)).val + 6 * ((vector (2 : Fin 12)).val + 6 * ((vector (3 : Fin 12)).val + 6 * ((vector (4 : Fin 12)).val + 6 * ((vector (5 : Fin 12)).val + 6 * ((vector (6 : Fin 12)).val + 6 * ((vector (7 : Fin 12)).val + 6 * ((vector (8 : Fin 12)).val + 6 * ((vector (9 : Fin 12)).val + 6 * ((vector (10 : Fin 12)).val + 6 * ((vector (11 : Fin 12)).val)))))))))))

private def decodeStateCode (code : Nat) : Fin 225 :=
  if code < 30373056 then decodeStateCodeChunk0 code else
  if code < 81088128 then decodeStateCodeChunk1 code else
  if code < 725780736 then decodeStateCodeChunk2 code else
  if code < 755943840 then decodeStateCodeChunk3 code else
  if code < 767514528 then decodeStateCodeChunk4 code else
  if code < 816689952 then decodeStateCodeChunk5 code else
  if code < 1071572982 then decodeStateCodeChunk6 code else
  decodeStateCodeChunk7 code

private def decodeState
    (vector : Fin 12 -> Fin 6) : Fin 225 :=
  decodeStateCode (stateVectorCode vector)

set_option maxHeartbeats 2000000 in
private theorem decodeState_stateVector (state : Fin 225) :
    decodeState (stateVector state) = state := by
  decide +revert

set_option maxHeartbeats 2000000 in
private theorem transitionMap :
    forall (state : Fin 225)
      (generator : Fin 3)
      (coordinate : Fin 12),
      stateVector (transition state generator) coordinate =
        oppositeTable.semigroup.mul (stateVector state coordinate)
          (generatorVector generator coordinate) := by
  intro state generator coordinate
  apply Fin.ext
  exact by decide +revert

set_option maxHeartbeats 2000000 in
private theorem representativeMap :
    forall (state : Fin 225)
      (coordinate : Fin 12),
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
    (I := Fin 12) oppositeTable.semigroup where
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
        (Fin 12) targetValid
    have subValid :=
      powerCertificate.embedding.pullback_identity identity powerValid
    exact quotient.pushforwardIdentity identity subValid

/-- First-layer generic-CAS basis wrapper for `S6_6844`. -/
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

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6844
