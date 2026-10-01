import SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6494Representative
import SemigroupBasis.FiniteNilpotentCounterexample
import SemigroupBasis.Nonfinite
import SemigroupBasis.Opposite
import SemigroupBasis.RightGeneratedPowerCertificate

set_option maxRecDepth 2048

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_8883

open SemigroupBasis

def routeManifestRowSHA256 : String := "114a529e7a291655b5128523993c8c994e6f09df4b0005ed99d94c68c6c1b3a0"
def witnessRecordSHA256 : String := "1ce0bf2e42093ec5492faea7424831f13ee787bfafb6cc881ab6b8ffb89c4ca3"
def transferComponentSHA256 : String := "1ce0bf2e42093ec5492faea7424831f13ee787bfafb6cc881ab6b8ffb89c4ca3"
def powerCertificateSHA256 : String := "7be25c330da55e25b8c10881a31c69a4e7b204b1bd25558366cd1e25e4dd7c47"

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
  "05998cdce3f4b7f2ca6e8e35087548c7ab5d8f8e630c295721c6a113dcdafd3b"

private def packedStateVectorCodeChunk0 (index : Nat) : Nat :=
  match index with
  | 0 => 2748731689369
  | 1 => 1752100856214
  | 2 => 2117077453764
  | 3 => 2744257145688
  | 4 => 2775088197072
  | 5 => 2748246820128
  | 6 => 1834697512656
  | 7 => 1725856854912
  | 8 => 1673615151936
  | 9 => 2591494977312
  | 10 => 1672889557824
  | 11 => 2116956233664
  | 12 => 2748731642712
  | 13 => 2770855518096
  | 14 => 2744014141152
  | 15 => 2749086060480
  | 16 => 2775208008384
  | 17 => 2774482414272
  | 18 => 2748367464768
  | 19 => 1830464833680
  | 20 => 1808695376064
  | 21 => 1834817883840
  | 22 => 1752099175296
  | 23 => 1647613016640
  | 24 => 1678089555648
  | 25 => 1673735804352
  | 26 => 2587262298336
  | 27 => 2617733930688
  | 28 => 2591615621952
  | 29 => 1677363961536
  | 30 => 1646887422528
  | _ => 1673010210240

private def packedStateVectorCodeChunk1 (index : Nat) : Nat :=
  match index with
  | 0 => 2117077166016
  | 1 => 2775088150416
  | 2 => 2748246773472
  | 3 => 2744611516800
  | 4 => 2770733464704
  | 5 => 2770007870592
  | 6 => 2743892921088
  | 7 => 2775086516160
  | 8 => 2748964008384
  | 9 => 2775086796096
  | 10 => 2748238414272
  | 11 => 2774361201984
  | 12 => 2748246532416
  | 13 => 1834697466000
  | 14 => 1804220832384
  | 15 => 1830343340160
  | 16 => 1834695831744
  | 17 => 1808573883840
  | 18 => 1834696671552
  | 19 => 1673613472320
  | 20 => 1651845555648
  | 21 => 1647491804352
  | 22 => 1673615011968
  | 23 => 1677968343360
  | 24 => 1673614872000
  | 25 => 2591494930656
  | 26 => 2613259387008
  | 27 => 2587141078272
  | 28 => 2591489930688
  | 29 => 2617612718400
  | 30 => 2591494689600
  | _ => 1672889417856

private def packedStateVectorCodeChunk2 (index : Nat) : Nat :=
  match index with
  | 0 => 1651119961536
  | 1 => 1677242749248
  | 2 => 1672887878208
  | 3 => 1646766210240
  | 4 => 1672889277888
  | 5 => 2749086013824
  | 6 => 2775207961728
  | 7 => 2774482367616
  | 8 => 2748367418112
  | 9 => 2770853837184
  | 10 => 2744731329408
  | 11 => 2770854117120
  | 12 => 2744005735296
  | 13 => 2770128523008
  | 14 => 2744013853440
  | 15 => 2775206328768
  | 16 => 2749084660800
  | 17 => 2775207728448
  | 18 => 2774480734656
  | 19 => 2748359066688
  | 20 => 2774482134336
  | 21 => 1808695329408
  | 22 => 1834817837184
  | 23 => 1830463152768
  | 24 => 1804341204864
  | 25 => 1830463992576
  | 26 => 1834816204224
  | 27 => 1808694536256
  | 28 => 1834817603904
  | 29 => 1678087876032
  | 30 => 1673734124736
  | _ => 1647612876672

private def packedStateVectorCodeChunk3 (index : Nat) : Nat :=
  match index with
  | 0 => 1651966208064
  | 1 => 1647612736704
  | 2 => 1678089508992
  | 3 => 1673735664384
  | 4 => 1678089275712
  | 5 => 2617733884032
  | 6 => 2591615575296
  | 7 => 2587257251712
  | 8 => 2613380039424
  | 9 => 2587262010624
  | 10 => 2617732251072
  | 11 => 2591610583104
  | 12 => 2617733650752
  | 13 => 1677363914880
  | 14 => 1646887282560
  | 15 => 1673010070272
  | 16 => 1677362281920
  | 17 => 1651240613952
  | 18 => 1677363681600
  | 19 => 1673008530624
  | 20 => 1646887142592
  | 21 => 2775086469504
  | 22 => 2748963961728
  | 23 => 2775086749440
  | 24 => 2748238367616
  | 25 => 2774361155328
  | 26 => 2748246485760
  | 27 => 2770731785088
  | 28 => 2744610117120
  | 29 => 2770733184768
  | 30 => 2770006190976
  | _ => 2743884523008

private def packedStateVectorCodeChunk4 (index : Nat) : Nat :=
  match index with
  | 0 => 2770007590656
  | 1 => 2775085116480
  | 2 => 2748963728448
  | 3 => 2774359522368
  | 4 => 2748238134336
  | 5 => 1834695785088
  | 6 => 1808573837184
  | 7 => 1834696624896
  | 8 => 1830341660544
  | 9 => 1804219992576
  | 10 => 1830343060224
  | 11 => 1834694991936
  | 12 => 1808573603904
  | 13 => 1673613332352
  | 14 => 1677966663744
  | 15 => 1673613192384
  | 16 => 1651845508992
  | 17 => 1647491664384
  | 18 => 1651845275712
  | 19 => 1677968296704
  | 20 => 1673614732032
  | 21 => 2591489884032
  | 22 => 2617612671744
  | 23 => 2591494642944
  | 24 => 2613257707392
  | 25 => 2587136039424
  | 26 => 2613259107072
  | 27 => 2617611038784
  | 28 => 2591489650752
  | 29 => 1651119914880
  | 30 => 1677242702592
  | _ => 1672887738240

private def packedStateVectorCodeChunk5 (index : Nat) : Nat :=
  match index with
  | 0 => 1646766070272
  | 1 => 1672889137920
  | 2 => 1677241069632
  | 3 => 1651119681600
  | 4 => 1672887598272
  | 5 => 2775206282112
  | 6 => 2749084614144
  | 7 => 2775207681792
  | 8 => 2774480688000
  | 9 => 2748359020032
  | 10 => 2774482087680
  | 11 => 2770852437504
  | 12 => 2744731049472
  | 13 => 2770126843392
  | 14 => 2744005455360
  | 15 => 2775206048832
  | 16 => 2774480454720
  | 17 => 1834816157568
  | 18 => 1808694489600
  | 19 => 1834817557248
  | 20 => 1830462312960
  | 21 => 1804340924928
  | 22 => 1834815924288
  | 23 => 1678087829376
  | 24 => 1673733984768
  | 25 => 1678087596096
  | 26 => 1651966161408
  | 27 => 1647612596736
  | 28 => 1678089229056
  | 29 => 2617732204416
  | 30 => 2591610536448
  | _ => 2617733604096

private def packedStateVectorCodeChunk6 (index : Nat) : Nat :=
  match index with
  | 0 => 2613378359808
  | 1 => 2587256971776
  | 2 => 2617731971136
  | 3 => 1677362235264
  | 4 => 1651240567296
  | 5 => 1677363634944
  | 6 => 1673008390656
  | 7 => 1646887002624
  | 8 => 1677362001984
  | 9 => 2775085069824
  | 10 => 2748963681792
  | 11 => 2774359475712
  | 12 => 2748238087680
  | 13 => 2770731505152
  | 14 => 2770005911040
  | 15 => 1834694945280
  | 16 => 1808573557248
  | 17 => 1830341380608
  | 18 => 1677966617088
  | 19 => 1673613052416
  | 20 => 1651845229056
  | 21 => 2617610992128
  | 22 => 2591489604096
  | 23 => 2613257427456
  | 24 => 1677241022976
  | 25 => 1651119634944
  | 26 => 1672887458304
  | 27 => 2775206002176
  | 28 => 2774480408064
  | 29 => 1834815877632
  | 30 => 1678087549440
  | _ => 2617731924480

private def packedStateVectorCodeChunk7 (index : Nat) : Nat :=
  match index with
  | _ => 1677361955328

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
    (coordinate : Fin 16) : Fin 6 :=
  ⟨(packedStateVectorCode state / 6 ^ coordinate.val) % 6,
    Nat.mod_lt _ (by decide)⟩

def generatorVector (generator : Fin 3)
    (coordinate : Fin 16) : Fin 6 :=
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
      | 7 => (5 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (5 : Fin 6)
      | 10 => (2 : Fin 6)
      | 11 => (4 : Fin 6)
      | 12 => (2 : Fin 6)
      | 13 => (0 : Fin 6)
      | 14 => (5 : Fin 6)
      | _ => (5 : Fin 6)
  | 1 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (1 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (1 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (4 : Fin 6)
      | 7 => (3 : Fin 6)
      | 8 => (1 : Fin 6)
      | 9 => (3 : Fin 6)
      | 10 => (2 : Fin 6)
      | 11 => (5 : Fin 6)
      | 12 => (0 : Fin 6)
      | 13 => (2 : Fin 6)
      | 14 => (4 : Fin 6)
      | _ => (3 : Fin 6)
  | _ =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (1 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (1 : Fin 6)
      | 6 => (3 : Fin 6)
      | 7 => (1 : Fin 6)
      | 8 => (3 : Fin 6)
      | 9 => (3 : Fin 6)
      | 10 => (2 : Fin 6)
      | 11 => (3 : Fin 6)
      | 12 => (0 : Fin 6)
      | 13 => (0 : Fin 6)
      | 14 => (3 : Fin 6)
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
  if code = 1646766070272 then (160 : Fin 225) else
  if code = 1646766210240 then (67 : Fin 225) else
  if code = 1646887002624 then (199 : Fin 225) else
  if code = 1646887142592 then (116 : Fin 225) else
  if code = 1646887282560 then (110 : Fin 225) else
  if code = 1646887422528 then (30 : Fin 225) else
  if code = 1647491664384 then (145 : Fin 225) else
  if code = 1647491804352 then (53 : Fin 225) else
  if code = 1647612596736 then (187 : Fin 225) else
  if code = 1647612736704 then (97 : Fin 225) else
  if code = 1647612876672 then (95 : Fin 225) else
  if code = 1647613016640 then (23 : Fin 225) else
  if code = 1651119634944 then (217 : Fin 225) else
  if code = 1651119681600 then (163 : Fin 225) else
  if code = 1651119914880 then (157 : Fin 225) else
  if code = 1651119961536 then (64 : Fin 225) else
  if code = 1651240567296 then (196 : Fin 225) else
  if code = 1651240613952 then (113 : Fin 225) else
  if code = 1651845229056 then (212 : Fin 225) else
  if code = 1651845275712 then (146 : Fin 225) else
  if code = 1651845508992 then (144 : Fin 225) else
  if code = 1651845555648 then (52 : Fin 225) else
  if code = 1651966161408 then (186 : Fin 225) else
  if code = 1651966208064 then (96 : Fin 225) else
  if code = 1672887458304 then (218 : Fin 225) else
  if code = 1672887598272 then (164 : Fin 225) else
  if code = 1672887738240 then (159 : Fin 225) else
  if code = 1672887878208 then (66 : Fin 225) else
  if code = 1672889137920 then (161 : Fin 225) else
  if code = 1672889277888 then (68 : Fin 225) else
  if code = 1672889417856 then (63 : Fin 225) else
  if code = 1672889557824 then (10 : Fin 225) else
  (0 : Fin 225)

private def decodeStateCodeChunk1 (code : Nat) : Fin 225 :=
  if code = 1673008390656 then (198 : Fin 225) else
  if code = 1673008530624 then (115 : Fin 225) else
  if code = 1673010070272 then (111 : Fin 225) else
  if code = 1673010210240 then (31 : Fin 225) else
  if code = 1673613052416 then (211 : Fin 225) else
  if code = 1673613192384 then (143 : Fin 225) else
  if code = 1673613332352 then (141 : Fin 225) else
  if code = 1673613472320 then (51 : Fin 225) else
  if code = 1673614732032 then (148 : Fin 225) else
  if code = 1673614872000 then (56 : Fin 225) else
  if code = 1673615011968 then (54 : Fin 225) else
  if code = 1673615151936 then (8 : Fin 225) else
  if code = 1673733984768 then (184 : Fin 225) else
  if code = 1673734124736 then (94 : Fin 225) else
  if code = 1673735664384 then (99 : Fin 225) else
  if code = 1673735804352 then (25 : Fin 225) else
  if code = 1677241022976 then (216 : Fin 225) else
  if code = 1677241069632 then (162 : Fin 225) else
  if code = 1677242702592 then (158 : Fin 225) else
  if code = 1677242749248 then (65 : Fin 225) else
  if code = 1677361955328 then (224 : Fin 225) else
  if code = 1677362001984 then (200 : Fin 225) else
  if code = 1677362235264 then (195 : Fin 225) else
  if code = 1677362281920 then (112 : Fin 225) else
  if code = 1677363634944 then (197 : Fin 225) else
  if code = 1677363681600 then (114 : Fin 225) else
  if code = 1677363914880 then (109 : Fin 225) else
  if code = 1677363961536 then (29 : Fin 225) else
  if code = 1677966617088 then (210 : Fin 225) else
  if code = 1677966663744 then (142 : Fin 225) else
  if code = 1677968296704 then (147 : Fin 225) else
  if code = 1677968343360 then (55 : Fin 225) else
  (0 : Fin 225)

private def decodeStateCodeChunk2 (code : Nat) : Fin 225 :=
  if code = 1678087549440 then (222 : Fin 225) else
  if code = 1678087596096 then (185 : Fin 225) else
  if code = 1678087829376 then (183 : Fin 225) else
  if code = 1678087876032 then (93 : Fin 225) else
  if code = 1678089229056 then (188 : Fin 225) else
  if code = 1678089275712 then (100 : Fin 225) else
  if code = 1678089508992 then (98 : Fin 225) else
  if code = 1678089555648 then (24 : Fin 225) else
  if code = 1725856854912 then (7 : Fin 225) else
  if code = 1752099175296 then (22 : Fin 225) else
  if code = 1752100856214 then (1 : Fin 225) else
  if code = 1804219992576 then (137 : Fin 225) else
  if code = 1804220832384 then (46 : Fin 225) else
  if code = 1804340924928 then (181 : Fin 225) else
  if code = 1804341204864 then (88 : Fin 225) else
  if code = 1808573557248 then (208 : Fin 225) else
  if code = 1808573603904 then (140 : Fin 225) else
  if code = 1808573837184 then (134 : Fin 225) else
  if code = 1808573883840 then (49 : Fin 225) else
  if code = 1808694489600 then (178 : Fin 225) else
  if code = 1808694536256 then (91 : Fin 225) else
  if code = 1808695329408 then (85 : Fin 225) else
  if code = 1808695376064 then (20 : Fin 225) else
  if code = 1830341380608 then (209 : Fin 225) else
  if code = 1830341660544 then (136 : Fin 225) else
  if code = 1830343060224 then (138 : Fin 225) else
  if code = 1830343340160 then (47 : Fin 225) else
  if code = 1830462312960 then (180 : Fin 225) else
  if code = 1830463152768 then (87 : Fin 225) else
  if code = 1830463992576 then (89 : Fin 225) else
  if code = 1830464833680 then (19 : Fin 225) else
  if code = 1834694945280 then (207 : Fin 225) else
  (0 : Fin 225)

private def decodeStateCodeChunk3 (code : Nat) : Fin 225 :=
  if code = 1834694991936 then (139 : Fin 225) else
  if code = 1834695785088 then (133 : Fin 225) else
  if code = 1834695831744 then (48 : Fin 225) else
  if code = 1834696624896 then (135 : Fin 225) else
  if code = 1834696671552 then (50 : Fin 225) else
  if code = 1834697466000 then (45 : Fin 225) else
  if code = 1834697512656 then (6 : Fin 225) else
  if code = 1834815877632 then (221 : Fin 225) else
  if code = 1834815924288 then (182 : Fin 225) else
  if code = 1834816157568 then (177 : Fin 225) else
  if code = 1834816204224 then (90 : Fin 225) else
  if code = 1834817557248 then (179 : Fin 225) else
  if code = 1834817603904 then (92 : Fin 225) else
  if code = 1834817837184 then (86 : Fin 225) else
  if code = 1834817883840 then (21 : Fin 225) else
  if code = 2116956233664 then (11 : Fin 225) else
  if code = 2117077166016 then (32 : Fin 225) else
  if code = 2117077453764 then (2 : Fin 225) else
  if code = 2587136039424 then (153 : Fin 225) else
  if code = 2587141078272 then (59 : Fin 225) else
  if code = 2587256971776 then (193 : Fin 225) else
  if code = 2587257251712 then (103 : Fin 225) else
  if code = 2587262010624 then (105 : Fin 225) else
  if code = 2587262298336 then (26 : Fin 225) else
  if code = 2591489604096 then (214 : Fin 225) else
  if code = 2591489650752 then (156 : Fin 225) else
  if code = 2591489884032 then (149 : Fin 225) else
  if code = 2591489930688 then (60 : Fin 225) else
  if code = 2591494642944 then (151 : Fin 225) else
  if code = 2591494689600 then (62 : Fin 225) else
  if code = 2591494930656 then (57 : Fin 225) else
  if code = 2591494977312 then (9 : Fin 225) else
  (0 : Fin 225)

private def decodeStateCodeChunk4 (code : Nat) : Fin 225 :=
  if code = 2591610536448 then (190 : Fin 225) else
  if code = 2591610583104 then (107 : Fin 225) else
  if code = 2591615575296 then (102 : Fin 225) else
  if code = 2591615621952 then (28 : Fin 225) else
  if code = 2613257427456 then (215 : Fin 225) else
  if code = 2613257707392 then (152 : Fin 225) else
  if code = 2613259107072 then (154 : Fin 225) else
  if code = 2613259387008 then (58 : Fin 225) else
  if code = 2613378359808 then (192 : Fin 225) else
  if code = 2613380039424 then (104 : Fin 225) else
  if code = 2617610992128 then (213 : Fin 225) else
  if code = 2617611038784 then (155 : Fin 225) else
  if code = 2617612671744 then (150 : Fin 225) else
  if code = 2617612718400 then (61 : Fin 225) else
  if code = 2617731924480 then (223 : Fin 225) else
  if code = 2617731971136 then (194 : Fin 225) else
  if code = 2617732204416 then (189 : Fin 225) else
  if code = 2617732251072 then (106 : Fin 225) else
  if code = 2617733604096 then (191 : Fin 225) else
  if code = 2617733650752 then (108 : Fin 225) else
  if code = 2617733884032 then (101 : Fin 225) else
  if code = 2617733930688 then (27 : Fin 225) else
  if code = 2743884523008 then (127 : Fin 225) else
  if code = 2743892921088 then (38 : Fin 225) else
  if code = 2744005455360 then (174 : Fin 225) else
  if code = 2744005735296 then (76 : Fin 225) else
  if code = 2744013853440 then (78 : Fin 225) else
  if code = 2744014141152 then (14 : Fin 225) else
  if code = 2744257145688 then (3 : Fin 225) else
  if code = 2744610117120 then (124 : Fin 225) else
  if code = 2744611516800 then (35 : Fin 225) else
  if code = 2744731049472 then (172 : Fin 225) else
  (0 : Fin 225)

private def decodeStateCodeChunk5 (code : Nat) : Fin 225 :=
  if code = 2744731329408 then (74 : Fin 225) else
  if code = 2748238087680 then (204 : Fin 225) else
  if code = 2748238134336 then (132 : Fin 225) else
  if code = 2748238367616 then (120 : Fin 225) else
  if code = 2748238414272 then (42 : Fin 225) else
  if code = 2748246485760 then (122 : Fin 225) else
  if code = 2748246532416 then (44 : Fin 225) else
  if code = 2748246773472 then (34 : Fin 225) else
  if code = 2748246820128 then (5 : Fin 225) else
  if code = 2748359020032 then (169 : Fin 225) else
  if code = 2748359066688 then (83 : Fin 225) else
  if code = 2748367418112 then (72 : Fin 225) else
  if code = 2748367464768 then (18 : Fin 225) else
  if code = 2748731642712 then (12 : Fin 225) else
  if code = 2748731689369 then (0 : Fin 225) else
  if code = 2748963681792 then (202 : Fin 225) else
  if code = 2748963728448 then (130 : Fin 225) else
  if code = 2748963961728 then (118 : Fin 225) else
  if code = 2748964008384 then (40 : Fin 225) else
  if code = 2749084614144 then (166 : Fin 225) else
  if code = 2749084660800 then (80 : Fin 225) else
  if code = 2749086013824 then (69 : Fin 225) else
  if code = 2749086060480 then (15 : Fin 225) else
  if code = 2770005911040 then (206 : Fin 225) else
  if code = 2770006190976 then (126 : Fin 225) else
  if code = 2770007590656 then (128 : Fin 225) else
  if code = 2770007870592 then (37 : Fin 225) else
  if code = 2770126843392 then (173 : Fin 225) else
  if code = 2770128523008 then (77 : Fin 225) else
  if code = 2770731505152 then (205 : Fin 225) else
  if code = 2770731785088 then (123 : Fin 225) else
  if code = 2770733184768 then (125 : Fin 225) else
  (0 : Fin 225)

private def decodeStateCodeChunk6 (code : Nat) : Fin 225 :=
  if code = 2770733464704 then (36 : Fin 225) else
  if code = 2770852437504 then (171 : Fin 225) else
  if code = 2770853837184 then (73 : Fin 225) else
  if code = 2770854117120 then (75 : Fin 225) else
  if code = 2770855518096 then (13 : Fin 225) else
  if code = 2774359475712 then (203 : Fin 225) else
  if code = 2774359522368 then (131 : Fin 225) else
  if code = 2774361155328 then (121 : Fin 225) else
  if code = 2774361201984 then (43 : Fin 225) else
  if code = 2774480408064 then (220 : Fin 225) else
  if code = 2774480454720 then (176 : Fin 225) else
  if code = 2774480688000 then (168 : Fin 225) else
  if code = 2774480734656 then (82 : Fin 225) else
  if code = 2774482087680 then (170 : Fin 225) else
  if code = 2774482134336 then (84 : Fin 225) else
  if code = 2774482367616 then (71 : Fin 225) else
  if code = 2774482414272 then (17 : Fin 225) else
  if code = 2775085069824 then (201 : Fin 225) else
  if code = 2775085116480 then (129 : Fin 225) else
  if code = 2775086469504 then (117 : Fin 225) else
  if code = 2775086516160 then (39 : Fin 225) else
  if code = 2775086749440 then (119 : Fin 225) else
  if code = 2775086796096 then (41 : Fin 225) else
  if code = 2775088150416 then (33 : Fin 225) else
  if code = 2775088197072 then (4 : Fin 225) else
  if code = 2775206002176 then (219 : Fin 225) else
  if code = 2775206048832 then (175 : Fin 225) else
  if code = 2775206282112 then (165 : Fin 225) else
  if code = 2775206328768 then (79 : Fin 225) else
  if code = 2775207681792 then (167 : Fin 225) else
  if code = 2775207728448 then (81 : Fin 225) else
  if code = 2775207961728 then (70 : Fin 225) else
  (0 : Fin 225)

private def decodeStateCodeChunk7 (code : Nat) : Fin 225 :=
  if code = 2775208008384 then (16 : Fin 225) else
  (0 : Fin 225)

private def stateVectorCode
    (vector : Fin 16 -> Fin 6) : Nat :=
  (vector (0 : Fin 16)).val + 6 * ((vector (1 : Fin 16)).val + 6 * ((vector (2 : Fin 16)).val + 6 * ((vector (3 : Fin 16)).val + 6 * ((vector (4 : Fin 16)).val + 6 * ((vector (5 : Fin 16)).val + 6 * ((vector (6 : Fin 16)).val + 6 * ((vector (7 : Fin 16)).val + 6 * ((vector (8 : Fin 16)).val + 6 * ((vector (9 : Fin 16)).val + 6 * ((vector (10 : Fin 16)).val + 6 * ((vector (11 : Fin 16)).val + 6 * ((vector (12 : Fin 16)).val + 6 * ((vector (13 : Fin 16)).val + 6 * ((vector (14 : Fin 16)).val + 6 * ((vector (15 : Fin 16)).val)))))))))))))))

private def decodeStateCode (code : Nat) : Fin 225 :=
  if code < 1673008390656 then decodeStateCodeChunk0 code else
  if code < 1678087549440 then decodeStateCodeChunk1 code else
  if code < 1834694991936 then decodeStateCodeChunk2 code else
  if code < 2591610536448 then decodeStateCodeChunk3 code else
  if code < 2744731329408 then decodeStateCodeChunk4 code else
  if code < 2770733464704 then decodeStateCodeChunk5 code else
  if code < 2775208008384 then decodeStateCodeChunk6 code else
  decodeStateCodeChunk7 code

private def decodeState
    (vector : Fin 16 -> Fin 6) : Fin 225 :=
  decodeStateCode (stateVectorCode vector)

set_option maxHeartbeats 2000000 in
private theorem decodeState_stateVector (state : Fin 225) :
    decodeState (stateVector state) = state := by
  decide +revert

set_option maxHeartbeats 2000000 in
private theorem transitionMap :
    forall (state : Fin 225)
      (generator : Fin 3)
      (coordinate : Fin 16),
      stateVector (transition state generator) coordinate =
        oppositeTable.semigroup.mul (stateVector state coordinate)
          (generatorVector generator coordinate) := by
  intro state generator coordinate
  apply Fin.ext
  exact by decide +revert

set_option maxHeartbeats 2000000 in
private theorem representativeMap :
    forall (state : Fin 225)
      (coordinate : Fin 16),
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
    (I := Fin 16) oppositeTable.semigroup where
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
        (Fin 16) targetValid
    have subValid :=
      powerCertificate.embedding.pullback_identity identity powerValid
    exact quotient.pushforwardIdentity identity subValid

/-- First-layer generic-CAS basis wrapper for `S6_8883`. -/
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

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_8883
