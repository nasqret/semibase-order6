import SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6494Representative
import SemigroupBasis.FiniteNilpotentCounterexample
import SemigroupBasis.Nonfinite
import SemigroupBasis.Opposite
import SemigroupBasis.RightGeneratedPowerCertificate

set_option maxRecDepth 2048

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_8852

open SemigroupBasis

def routeManifestRowSHA256 : String := "418304e73781909f066cf668eed825f65653fd6cdb8c9843939f400c79a051fa"
def witnessRecordSHA256 : String := "f5975db2d7ab6877626a43b29017982b604c99f99b16af4f81055c1e1bf3ba8f"
def transferComponentSHA256 : String := "f5975db2d7ab6877626a43b29017982b604c99f99b16af4f81055c1e1bf3ba8f"
def powerCertificateSHA256 : String := "e064a45b1deba343df5e4f0177cf1e41f000f5b349829d23371b2600831479d9"

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
  "410aaf69b15c0cb8e5f24f0979f1156173087eb9ed341710630ccfbbce5ba48d"

private def packedStateVectorCodeChunk0 (index : Nat) : Nat :=
  match index with
  | 0 => 13189475632825
  | 1 => 11046054951510
  | 2 => 15588763287300
  | 3 => 13176414565560
  | 4 => 13344746009616
  | 5 => 13185605479392
  | 6 => 10523626024464
  | 7 => 10888599348288
  | 8 => 10104716262528
  | 9 => 12715410417120
  | 10 => 10102539480192
  | 11 => 15587976939264
  | 12 => 13176414658872
  | 13 => 13331684942352
  | 14 => 13172544692064
  | 15 => 13187290406400
  | 16 => 13343778269568
  | 17 => 13341601487232
  | 18 => 13184819411328
  | 19 => 10510564957200
  | 20 => 10366170421248
  | 21 => 10522658284416
  | 22 => 11046053270592
  | 23 => 9948711848832
  | 24 => 10052473299840
  | 25 => 10105381110528
  | 26 => 12702349629792
  | 27 => 12871406424960
  | 28 => 12714624349056
  | 29 => 10050296517504
  | 30 => 9946535066496
  | _ => 10103204328192

private def packedStateVectorCodeChunk1 (index : Nat) : Nat :=
  match index with
  | 0 => 15588702533376
  | 1 => 13331685035664
  | 2 => 13172544785376
  | 3 => 13174229339136
  | 4 => 13330717482240
  | 5 => 13328540699904
  | 6 => 13171758624000
  | 7 => 13344744328704
  | 8 => 13187773855872
  | 9 => 13344443397504
  | 10 => 13185597073536
  | 11 => 13342266615168
  | 12 => 13185545005440
  | 13 => 10510565050512
  | 14 => 10353109353984
  | 15 => 10509597497088
  | 16 => 10523624343552
  | 17 => 10366653870720
  | 18 => 10523323412352
  | 19 => 10104714582912
  | 20 => 9896468886144
  | 21 => 9947925508608
  | 22 => 10039412512512
  | 23 => 10053138427776
  | 24 => 10104655516416
  | 25 => 12702349723104
  | 26 => 12858345637632
  | 27 => 12701563561728
  | 28 => 12715402011264
  | 29 => 12872071552896
  | 30 => 12715349943168
  | _ => 10037235730176

private def packedStateVectorCodeChunk2 (index : Nat) : Nat :=
  match index with
  | 0 => 9894292103808
  | 1 => 10050961645440
  | 2 => 10102537800576
  | 3 => 9945748726272
  | 4 => 10102478734080
  | 5 => 13174229432448
  | 6 => 13330717575552
  | 7 => 13328540793216
  | 8 => 13171758717312
  | 9 => 13331683261440
  | 10 => 13174713068544
  | 11 => 13331382610176
  | 12 => 13172536286208
  | 13 => 13329205827840
  | 14 => 13172484218112
  | 15 => 13343776589952
  | 16 => 13186987795584
  | 17 => 13343717803392
  | 18 => 13341599807616
  | 19 => 13184811013248
  | 20 => 13341541021056
  | 21 => 10353109447296
  | 22 => 10509597590400
  | 23 => 10510563276288
  | 24 => 10353593083392
  | 25 => 10510262625024
  | 26 => 10522656604800
  | 27 => 10365867810432
  | 28 => 10522597818240
  | 29 => 10052471620224
  | 30 => 10105379430912
  | _ => 9883408098816

private def packedStateVectorCodeChunk3 (index : Nat) : Nat :=
  match index with
  | 0 => 9895682825856
  | 1 => 9948651102720
  | 2 => 10039412605824
  | 3 => 10040077640448
  | 4 => 10052412833664
  | 5 => 12858345730944
  | 6 => 12701563655040
  | 7 => 12702341223936
  | 8 => 12859010765568
  | 9 => 12702289155840
  | 10 => 12871404745344
  | 11 => 12714615950976
  | 12 => 12871345958784
  | 13 => 10037235823488
  | 14 => 9881231316480
  | 15 => 10037900858112
  | 16 => 10050294837888
  | 17 => 9893506043520
  | 18 => 10050236051328
  | 19 => 10103202648576
  | 20 => 9946474320384
  | 21 => 13331683354752
  | 22 => 13174713161856
  | 23 => 13331382703488
  | 24 => 13172536379520
  | 25 => 13329205921152
  | 26 => 13172484311424
  | 27 => 13330715802624
  | 28 => 13173927008256
  | 29 => 13330657016064
  | 30 => 13328539020288
  | _ => 13171750225920

private def packedStateVectorCodeChunk4 (index : Nat) : Nat :=
  match index with
  | 0 => 13328480233728
  | 1 => 13344441717888
  | 2 => 13187713389696
  | 3 => 13342264935552
  | 4 => 13185536607360
  | 5 => 10510563369600
  | 6 => 10353593176704
  | 7 => 10510262718336
  | 8 => 10509595817472
  | 9 => 10352807023104
  | 10 => 10509537030912
  | 11 => 10523321732736
  | 12 => 10366593404544
  | 13 => 10039410832896
  | 14 => 10053136748160
  | 15 => 10104653836800
  | 16 => 9883408192128
  | 17 => 9882622038528
  | 18 => 9896408419968
  | 19 => 10040077733760
  | 20 => 10039352046336
  | 21 => 12702341317248
  | 22 => 12859010858880
  | 23 => 12702289249152
  | 24 => 12858343958016
  | 25 => 12701555163648
  | 26 => 12858285171456
  | 27 => 12872069873280
  | 28 => 12715341545088
  | 29 => 9881231409792
  | 30 => 10037900951424
  | _ => 10037234050560

private def packedStateVectorCodeChunk5 (index : Nat) : Nat :=
  match index with
  | 0 => 9880445256192
  | 1 => 10037175264000
  | 2 => 10050959965824
  | 3 => 9894231637632
  | 4 => 10102477054464
  | 5 => 13330715895936
  | 6 => 13173927101568
  | 7 => 13330657109376
  | 8 => 13328539113600
  | 9 => 13171750319232
  | 10 => 13328480327040
  | 11 => 13331380930560
  | 12 => 13174652602368
  | 13 => 13329204148224
  | 14 => 13172475820032
  | 15 => 13343716123776
  | 16 => 13341539341440
  | 17 => 10509595910784
  | 18 => 10352807116416
  | 19 => 10509537124224
  | 20 => 10510260945408
  | 21 => 10353532617216
  | 22 => 10522596138624
  | 23 => 10039410926208
  | 24 => 10040075960832
  | 25 => 10052411154048
  | 26 => 9882622131840
  | 27 => 9883347632640
  | 28 => 10039352139648
  | 29 => 12858344051328
  | 30 => 12701555256960
  | _ => 12858285264768

private def packedStateVectorCodeChunk6 (index : Nat) : Nat :=
  match index with
  | 0 => 12859009085952
  | 1 => 12702280757760
  | 2 => 12871344279168
  | 3 => 10037234143872
  | 4 => 9880445349504
  | 5 => 10037175357312
  | 6 => 10037899178496
  | 7 => 9881170850304
  | 8 => 10050234371712
  | 9 => 13331381023872
  | 10 => 13174652695680
  | 11 => 13329204241536
  | 12 => 13172475913344
  | 13 => 13330655336448
  | 14 => 13328478554112
  | 15 => 10510261038720
  | 16 => 10353532710528
  | 17 => 10509535351296
  | 18 => 10040076054144
  | 19 => 10039350366720
  | 20 => 9883347725952
  | 21 => 12859009179264
  | 22 => 12702280851072
  | 23 => 12858283491840
  | 24 => 10037899271808
  | 25 => 9881170943616
  | 26 => 10037173584384
  | 27 => 13330655429760
  | 28 => 13328478647424
  | 29 => 10509535444608
  | 30 => 10039350460032
  | _ => 12858283585152

private def packedStateVectorCodeChunk7 (index : Nat) : Nat :=
  match index with
  | _ => 10037173677696

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
      | 3 => (3 : Fin 6)
      | 4 => (5 : Fin 6)
      | 5 => (5 : Fin 6)
      | 6 => (2 : Fin 6)
      | 7 => (1 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (4 : Fin 6)
      | 10 => (5 : Fin 6)
      | 11 => (0 : Fin 6)
      | 12 => (5 : Fin 6)
      | 13 => (1 : Fin 6)
      | 14 => (0 : Fin 6)
      | 15 => (4 : Fin 6)
      | _ => (4 : Fin 6)
  | 1 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (1 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (1 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (3 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (1 : Fin 6)
      | 9 => (3 : Fin 6)
      | 10 => (5 : Fin 6)
      | 11 => (2 : Fin 6)
      | 12 => (4 : Fin 6)
      | 13 => (5 : Fin 6)
      | 14 => (2 : Fin 6)
      | 15 => (5 : Fin 6)
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
      | 9 => (3 : Fin 6)
      | 10 => (1 : Fin 6)
      | 11 => (2 : Fin 6)
      | 12 => (3 : Fin 6)
      | 13 => (5 : Fin 6)
      | 14 => (0 : Fin 6)
      | 15 => (3 : Fin 6)
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
  if code = 9880445256192 then (160 : Fin 225) else
  if code = 9880445349504 then (196 : Fin 225) else
  if code = 9881170850304 then (199 : Fin 225) else
  if code = 9881170943616 then (217 : Fin 225) else
  if code = 9881231316480 then (110 : Fin 225) else
  if code = 9881231409792 then (157 : Fin 225) else
  if code = 9882622038528 then (145 : Fin 225) else
  if code = 9882622131840 then (186 : Fin 225) else
  if code = 9883347632640 then (187 : Fin 225) else
  if code = 9883347725952 then (212 : Fin 225) else
  if code = 9883408098816 then (95 : Fin 225) else
  if code = 9883408192128 then (144 : Fin 225) else
  if code = 9893506043520 then (113 : Fin 225) else
  if code = 9894231637632 then (163 : Fin 225) else
  if code = 9894292103808 then (64 : Fin 225) else
  if code = 9895682825856 then (96 : Fin 225) else
  if code = 9896408419968 then (146 : Fin 225) else
  if code = 9896468886144 then (52 : Fin 225) else
  if code = 9945748726272 then (67 : Fin 225) else
  if code = 9946474320384 then (116 : Fin 225) else
  if code = 9946535066496 then (30 : Fin 225) else
  if code = 9947925508608 then (53 : Fin 225) else
  if code = 9948651102720 then (97 : Fin 225) else
  if code = 9948711848832 then (23 : Fin 225) else
  if code = 10037173584384 then (218 : Fin 225) else
  if code = 10037173677696 then (224 : Fin 225) else
  if code = 10037175264000 then (161 : Fin 225) else
  if code = 10037175357312 then (197 : Fin 225) else
  if code = 10037234050560 then (159 : Fin 225) else
  if code = 10037234143872 then (195 : Fin 225) else
  if code = 10037235730176 then (63 : Fin 225) else
  if code = 10037235823488 then (109 : Fin 225) else
  (0 : Fin 225)

private def decodeStateCodeChunk1 (code : Nat) : Fin 225 :=
  if code = 10037899178496 then (198 : Fin 225) else
  if code = 10037899271808 then (216 : Fin 225) else
  if code = 10037900858112 then (111 : Fin 225) else
  if code = 10037900951424 then (158 : Fin 225) else
  if code = 10039350366720 then (211 : Fin 225) else
  if code = 10039350460032 then (222 : Fin 225) else
  if code = 10039352046336 then (148 : Fin 225) else
  if code = 10039352139648 then (188 : Fin 225) else
  if code = 10039410832896 then (141 : Fin 225) else
  if code = 10039410926208 then (183 : Fin 225) else
  if code = 10039412512512 then (54 : Fin 225) else
  if code = 10039412605824 then (98 : Fin 225) else
  if code = 10040075960832 then (184 : Fin 225) else
  if code = 10040076054144 then (210 : Fin 225) else
  if code = 10040077640448 then (99 : Fin 225) else
  if code = 10040077733760 then (147 : Fin 225) else
  if code = 10050234371712 then (200 : Fin 225) else
  if code = 10050236051328 then (114 : Fin 225) else
  if code = 10050294837888 then (112 : Fin 225) else
  if code = 10050296517504 then (29 : Fin 225) else
  if code = 10050959965824 then (162 : Fin 225) else
  if code = 10050961645440 then (65 : Fin 225) else
  if code = 10052411154048 then (185 : Fin 225) else
  if code = 10052412833664 then (100 : Fin 225) else
  if code = 10052471620224 then (93 : Fin 225) else
  if code = 10052473299840 then (24 : Fin 225) else
  if code = 10053136748160 then (142 : Fin 225) else
  if code = 10053138427776 then (55 : Fin 225) else
  if code = 10102477054464 then (164 : Fin 225) else
  if code = 10102478734080 then (68 : Fin 225) else
  if code = 10102537800576 then (66 : Fin 225) else
  if code = 10102539480192 then (10 : Fin 225) else
  (0 : Fin 225)

private def decodeStateCodeChunk2 (code : Nat) : Fin 225 :=
  if code = 10103202648576 then (115 : Fin 225) else
  if code = 10103204328192 then (31 : Fin 225) else
  if code = 10104653836800 then (143 : Fin 225) else
  if code = 10104655516416 then (56 : Fin 225) else
  if code = 10104714582912 then (51 : Fin 225) else
  if code = 10104716262528 then (8 : Fin 225) else
  if code = 10105379430912 then (94 : Fin 225) else
  if code = 10105381110528 then (25 : Fin 225) else
  if code = 10352807023104 then (137 : Fin 225) else
  if code = 10352807116416 then (178 : Fin 225) else
  if code = 10353109353984 then (46 : Fin 225) else
  if code = 10353109447296 then (85 : Fin 225) else
  if code = 10353532617216 then (181 : Fin 225) else
  if code = 10353532710528 then (208 : Fin 225) else
  if code = 10353593083392 then (88 : Fin 225) else
  if code = 10353593176704 then (134 : Fin 225) else
  if code = 10365867810432 then (91 : Fin 225) else
  if code = 10366170421248 then (20 : Fin 225) else
  if code = 10366593404544 then (140 : Fin 225) else
  if code = 10366653870720 then (49 : Fin 225) else
  if code = 10509535351296 then (209 : Fin 225) else
  if code = 10509535444608 then (221 : Fin 225) else
  if code = 10509537030912 then (138 : Fin 225) else
  if code = 10509537124224 then (179 : Fin 225) else
  if code = 10509595817472 then (136 : Fin 225) else
  if code = 10509595910784 then (177 : Fin 225) else
  if code = 10509597497088 then (47 : Fin 225) else
  if code = 10509597590400 then (86 : Fin 225) else
  if code = 10510260945408 then (180 : Fin 225) else
  if code = 10510261038720 then (207 : Fin 225) else
  if code = 10510262625024 then (89 : Fin 225) else
  if code = 10510262718336 then (135 : Fin 225) else
  (0 : Fin 225)

private def decodeStateCodeChunk3 (code : Nat) : Fin 225 :=
  if code = 10510563276288 then (87 : Fin 225) else
  if code = 10510563369600 then (133 : Fin 225) else
  if code = 10510564957200 then (19 : Fin 225) else
  if code = 10510565050512 then (45 : Fin 225) else
  if code = 10522596138624 then (182 : Fin 225) else
  if code = 10522597818240 then (92 : Fin 225) else
  if code = 10522656604800 then (90 : Fin 225) else
  if code = 10522658284416 then (21 : Fin 225) else
  if code = 10523321732736 then (139 : Fin 225) else
  if code = 10523323412352 then (50 : Fin 225) else
  if code = 10523624343552 then (48 : Fin 225) else
  if code = 10523626024464 then (6 : Fin 225) else
  if code = 10888599348288 then (7 : Fin 225) else
  if code = 11046053270592 then (22 : Fin 225) else
  if code = 11046054951510 then (1 : Fin 225) else
  if code = 12701555163648 then (153 : Fin 225) else
  if code = 12701555256960 then (190 : Fin 225) else
  if code = 12701563561728 then (59 : Fin 225) else
  if code = 12701563655040 then (102 : Fin 225) else
  if code = 12702280757760 then (193 : Fin 225) else
  if code = 12702280851072 then (214 : Fin 225) else
  if code = 12702289155840 then (105 : Fin 225) else
  if code = 12702289249152 then (151 : Fin 225) else
  if code = 12702341223936 then (103 : Fin 225) else
  if code = 12702341317248 then (149 : Fin 225) else
  if code = 12702349629792 then (26 : Fin 225) else
  if code = 12702349723104 then (57 : Fin 225) else
  if code = 12714615950976 then (107 : Fin 225) else
  if code = 12714624349056 then (28 : Fin 225) else
  if code = 12715341545088 then (156 : Fin 225) else
  if code = 12715349943168 then (62 : Fin 225) else
  if code = 12715402011264 then (60 : Fin 225) else
  (0 : Fin 225)

private def decodeStateCodeChunk4 (code : Nat) : Fin 225 :=
  if code = 12715410417120 then (9 : Fin 225) else
  if code = 12858283491840 then (215 : Fin 225) else
  if code = 12858283585152 then (223 : Fin 225) else
  if code = 12858285171456 then (154 : Fin 225) else
  if code = 12858285264768 then (191 : Fin 225) else
  if code = 12858343958016 then (152 : Fin 225) else
  if code = 12858344051328 then (189 : Fin 225) else
  if code = 12858345637632 then (58 : Fin 225) else
  if code = 12858345730944 then (101 : Fin 225) else
  if code = 12859009085952 then (192 : Fin 225) else
  if code = 12859009179264 then (213 : Fin 225) else
  if code = 12859010765568 then (104 : Fin 225) else
  if code = 12859010858880 then (150 : Fin 225) else
  if code = 12871344279168 then (194 : Fin 225) else
  if code = 12871345958784 then (108 : Fin 225) else
  if code = 12871404745344 then (106 : Fin 225) else
  if code = 12871406424960 then (27 : Fin 225) else
  if code = 12872069873280 then (155 : Fin 225) else
  if code = 12872071552896 then (61 : Fin 225) else
  if code = 13171750225920 then (127 : Fin 225) else
  if code = 13171750319232 then (169 : Fin 225) else
  if code = 13171758624000 then (38 : Fin 225) else
  if code = 13171758717312 then (72 : Fin 225) else
  if code = 13172475820032 then (174 : Fin 225) else
  if code = 13172475913344 then (204 : Fin 225) else
  if code = 13172484218112 then (78 : Fin 225) else
  if code = 13172484311424 then (122 : Fin 225) else
  if code = 13172536286208 then (76 : Fin 225) else
  if code = 13172536379520 then (120 : Fin 225) else
  if code = 13172544692064 then (14 : Fin 225) else
  if code = 13172544785376 then (34 : Fin 225) else
  if code = 13173927008256 then (124 : Fin 225) else
  (0 : Fin 225)

private def decodeStateCodeChunk5 (code : Nat) : Fin 225 :=
  if code = 13173927101568 then (166 : Fin 225) else
  if code = 13174229339136 then (35 : Fin 225) else
  if code = 13174229432448 then (69 : Fin 225) else
  if code = 13174652602368 then (172 : Fin 225) else
  if code = 13174652695680 then (202 : Fin 225) else
  if code = 13174713068544 then (74 : Fin 225) else
  if code = 13174713161856 then (118 : Fin 225) else
  if code = 13176414565560 then (3 : Fin 225) else
  if code = 13176414658872 then (12 : Fin 225) else
  if code = 13184811013248 then (83 : Fin 225) else
  if code = 13184819411328 then (18 : Fin 225) else
  if code = 13185536607360 then (132 : Fin 225) else
  if code = 13185545005440 then (44 : Fin 225) else
  if code = 13185597073536 then (42 : Fin 225) else
  if code = 13185605479392 then (5 : Fin 225) else
  if code = 13186987795584 then (80 : Fin 225) else
  if code = 13187290406400 then (15 : Fin 225) else
  if code = 13187713389696 then (130 : Fin 225) else
  if code = 13187773855872 then (40 : Fin 225) else
  if code = 13189475632825 then (0 : Fin 225) else
  if code = 13328478554112 then (206 : Fin 225) else
  if code = 13328478647424 then (220 : Fin 225) else
  if code = 13328480233728 then (128 : Fin 225) else
  if code = 13328480327040 then (170 : Fin 225) else
  if code = 13328539020288 then (126 : Fin 225) else
  if code = 13328539113600 then (168 : Fin 225) else
  if code = 13328540699904 then (37 : Fin 225) else
  if code = 13328540793216 then (71 : Fin 225) else
  if code = 13329204148224 then (173 : Fin 225) else
  if code = 13329204241536 then (203 : Fin 225) else
  if code = 13329205827840 then (77 : Fin 225) else
  if code = 13329205921152 then (121 : Fin 225) else
  (0 : Fin 225)

private def decodeStateCodeChunk6 (code : Nat) : Fin 225 :=
  if code = 13330655336448 then (205 : Fin 225) else
  if code = 13330655429760 then (219 : Fin 225) else
  if code = 13330657016064 then (125 : Fin 225) else
  if code = 13330657109376 then (167 : Fin 225) else
  if code = 13330715802624 then (123 : Fin 225) else
  if code = 13330715895936 then (165 : Fin 225) else
  if code = 13330717482240 then (36 : Fin 225) else
  if code = 13330717575552 then (70 : Fin 225) else
  if code = 13331380930560 then (171 : Fin 225) else
  if code = 13331381023872 then (201 : Fin 225) else
  if code = 13331382610176 then (75 : Fin 225) else
  if code = 13331382703488 then (119 : Fin 225) else
  if code = 13331683261440 then (73 : Fin 225) else
  if code = 13331683354752 then (117 : Fin 225) else
  if code = 13331684942352 then (13 : Fin 225) else
  if code = 13331685035664 then (33 : Fin 225) else
  if code = 13341539341440 then (176 : Fin 225) else
  if code = 13341541021056 then (84 : Fin 225) else
  if code = 13341599807616 then (82 : Fin 225) else
  if code = 13341601487232 then (17 : Fin 225) else
  if code = 13342264935552 then (131 : Fin 225) else
  if code = 13342266615168 then (43 : Fin 225) else
  if code = 13343716123776 then (175 : Fin 225) else
  if code = 13343717803392 then (81 : Fin 225) else
  if code = 13343776589952 then (79 : Fin 225) else
  if code = 13343778269568 then (16 : Fin 225) else
  if code = 13344441717888 then (129 : Fin 225) else
  if code = 13344443397504 then (41 : Fin 225) else
  if code = 13344744328704 then (39 : Fin 225) else
  if code = 13344746009616 then (4 : Fin 225) else
  if code = 15587976939264 then (11 : Fin 225) else
  if code = 15588702533376 then (32 : Fin 225) else
  (0 : Fin 225)

private def decodeStateCodeChunk7 (code : Nat) : Fin 225 :=
  if code = 15588763287300 then (2 : Fin 225) else
  (0 : Fin 225)

private def stateVectorCode
    (vector : Fin 17 -> Fin 6) : Nat :=
  (vector (0 : Fin 17)).val + 6 * ((vector (1 : Fin 17)).val + 6 * ((vector (2 : Fin 17)).val + 6 * ((vector (3 : Fin 17)).val + 6 * ((vector (4 : Fin 17)).val + 6 * ((vector (5 : Fin 17)).val + 6 * ((vector (6 : Fin 17)).val + 6 * ((vector (7 : Fin 17)).val + 6 * ((vector (8 : Fin 17)).val + 6 * ((vector (9 : Fin 17)).val + 6 * ((vector (10 : Fin 17)).val + 6 * ((vector (11 : Fin 17)).val + 6 * ((vector (12 : Fin 17)).val + 6 * ((vector (13 : Fin 17)).val + 6 * ((vector (14 : Fin 17)).val + 6 * ((vector (15 : Fin 17)).val + 6 * ((vector (16 : Fin 17)).val))))))))))))))))

private def decodeStateCode (code : Nat) : Fin 225 :=
  if code < 10037899178496 then decodeStateCodeChunk0 code else
  if code < 10103202648576 then decodeStateCodeChunk1 code else
  if code < 10510563276288 then decodeStateCodeChunk2 code else
  if code < 12715410417120 then decodeStateCodeChunk3 code else
  if code < 13173927101568 then decodeStateCodeChunk4 code else
  if code < 13330655336448 then decodeStateCodeChunk5 code else
  if code < 15588763287300 then decodeStateCodeChunk6 code else
  decodeStateCodeChunk7 code

private def decodeState
    (vector : Fin 17 -> Fin 6) : Fin 225 :=
  decodeStateCode (stateVectorCode vector)

set_option maxHeartbeats 2000000 in
private theorem decodeState_stateVector (state : Fin 225) :
    decodeState (stateVector state) = state := by
  decide +revert

set_option maxHeartbeats 2000000 in
private theorem transitionMap :
    forall (state : Fin 225)
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
    forall (state : Fin 225)
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
    (U := Fin 225)
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
        (Fin 17) targetValid
    have subValid :=
      powerCertificate.embedding.pullback_identity identity powerValid
    exact quotient.pushforwardIdentity identity subValid

/-- First-layer generic-CAS basis wrapper for `S6_8852`. -/
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

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_8852
