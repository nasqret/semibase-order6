import SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6494Representative
import SemigroupBasis.FiniteNilpotentCounterexample
import SemigroupBasis.Nonfinite
import SemigroupBasis.Opposite
import SemigroupBasis.RightGeneratedPowerCertificate

set_option maxRecDepth 2048

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11780

open SemigroupBasis

def routeManifestRowSHA256 : String := "fbc88725e2552660062ab94e309a397023dfe276cf04524e6b2ccc92059b4a97"
def witnessRecordSHA256 : String := "9b4b8a5b7e57a724433334de4c4026e829a816536e83b5e00060681b284a0022"
def transferComponentSHA256 : String := "9b4b8a5b7e57a724433334de4c4026e829a816536e83b5e00060681b284a0022"
def powerCertificateSHA256 : String := "fc5e93a62daf0f66f98c1d5dae4c43915151c2d02c62eea266fddd65d5f96068"

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
      if left = 2 then row6 2 2 2 3 2 2 right else
        if left = 3 then row6 3 3 3 2 3 3 right else
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
  "6b2e18f03b3cb7ac422131daeab1f400000785dda79dd76a6d36da27c2af31c8"

private def packedStateVectorCodeChunk0 (index : Nat) : Nat :=
  match index with
  | 0 => 4010798377
  | 1 => 51752313942
  | 2 => 11114337924
  | 3 => 1823883912
  | 4 => 43004749392
  | 5 => 2367006624
  | 6 => 43004780496
  | 7 => 38629472832
  | 8 => 51680415744
  | 9 => 2407317408
  | 10 => 50229227520
  | 11 => 11053591776
  | 12 => 1823930568
  | 13 => 40817842704
  | 14 => 190169856
  | 15 => 29881908288
  | 16 => 42933084480
  | 17 => 41481896256
  | 18 => 2306260512
  | 19 => 40817873808
  | 20 => 29881939392
  | 21 => 42933115584
  | 22 => 51750633024
  | 23 => 38678508288
  | 24 => 42973426368
  | 25 => 51740601984
  | 26 => 230480640
  | 27 => 41522207040
  | 28 => 2346571296
  | 29 => 41522238144
  | 30 => 37227320064
  | _ => 50289413760

private def packedStateVectorCodeChunk1 (index : Nat) : Nat :=
  match index with
  | 0 => 11114057952
  | 1 => 40817889360
  | 2 => 190216512
  | 3 => 27695001600
  | 4 => 40756255488
  | 5 => 39305067264
  | 6 => 129423744
  | 7 => 43003068480
  | 8 => 29931177024
  | 9 => 42993270720
  | 10 => 28479988800
  | 11 => 41542082496
  | 12 => 2366726688
  | 13 => 40817920464
  | 14 => 27695032704
  | 15 => 40756286592
  | 16 => 43003099584
  | 17 => 29931208128
  | 18 => 42993301824
  | 19 => 51678736128
  | 20 => 29971518912
  | 21 => 38617762176
  | 22 => 40796597376
  | 23 => 43033612608
  | 24 => 51680135808
  | 25 => 230527296
  | 26 => 39345378048
  | 27 => 169734528
  | 28 => 28520299584
  | 29 => 41582393280
  | 30 => 2407037472
  | _ => 39345409152

private def packedStateVectorCodeChunk2 (index : Nat) : Nat :=
  match index with
  | 0 => 28520330688
  | 1 => 41582424384
  | 2 => 50227547904
  | 3 => 37166573952
  | 4 => 50228947584
  | 5 => 27695048256
  | 6 => 40756302144
  | 7 => 39305113920
  | 8 => 129470400
  | 9 => 40816161792
  | 10 => 27754348032
  | 11 => 40816441728
  | 12 => 26303159808
  | 13 => 39365253504
  | 14 => 189889920
  | 15 => 42931404864
  | 16 => 29870430912
  | 17 => 42932804544
  | 18 => 41480216640
  | 19 => 28419242688
  | 20 => 41481616320
  | 21 => 27695079360
  | 22 => 40756333248
  | 23 => 40816192896
  | 24 => 27754379136
  | 25 => 40816472832
  | 26 => 42931435968
  | 27 => 29870462016
  | 28 => 42932835648
  | 29 => 42971746752
  | 30 => 51738922368
  | _ => 27794689920

private def packedStateVectorCodeChunk3 (index : Nat) : Nat :=
  match index with
  | 0 => 29910772800
  | 1 => 38678228352
  | 2 => 40796644032
  | 3 => 40856783616
  | 4 => 42973146432
  | 5 => 39345424704
  | 6 => 169781184
  | 7 => 26343470592
  | 8 => 39405564288
  | 9 => 230200704
  | 10 => 41520527424
  | 11 => 28459553472
  | 12 => 41521927104
  | 13 => 39345455808
  | 14 => 26343501696
  | 15 => 39405595392
  | 16 => 41520558528
  | 17 => 28459584576
  | 18 => 41521958208
  | 19 => 50287734144
  | 20 => 37227040128
  | 21 => 40816208448
  | 22 => 27754394688
  | 23 => 40816488384
  | 24 => 26303206464
  | 25 => 39365300160
  | 26 => 189936576
  | 27 => 40754575872
  | 28 => 27693601920
  | 29 => 40755975552
  | 30 => 39303387648
  | _ => 26242413696

private def packedStateVectorCodeChunk4 (index : Nat) : Nat :=
  match index with
  | 0 => 39304787328
  | 1 => 42991591104
  | 2 => 29930897088
  | 3 => 41540402880
  | 4 => 28479708864
  | 5 => 40816239552
  | 6 => 27754425792
  | 7 => 40816519488
  | 8 => 40754606976
  | 9 => 27693633024
  | 10 => 40756006656
  | 11 => 42991622208
  | 12 => 29930928192
  | 13 => 40794917760
  | 14 => 43031932992
  | 15 => 51678456192
  | 16 => 27794736576
  | 17 => 27733943808
  | 18 => 29971238976
  | 19 => 40856830272
  | 20 => 40796317440
  | 21 => 26343517248
  | 22 => 39405610944
  | 23 => 230247360
  | 24 => 39343698432
  | 25 => 26282724480
  | 26 => 39345098112
  | 27 => 41580713664
  | 28 => 28520019648
  | 29 => 26343548352
  | 30 => 39405642048
  | _ => 39343729536

private def packedStateVectorCodeChunk5 (index : Nat) : Nat :=
  match index with
  | 0 => 26282755584
  | 1 => 39345129216
  | 2 => 41580744768
  | 3 => 28520050752
  | 4 => 50227267968
  | 5 => 40754622528
  | 6 => 27693648576
  | 7 => 40756022208
  | 8 => 39303434304
  | 9 => 26242460352
  | 10 => 39304833984
  | 11 => 40814762112
  | 12 => 27754068096
  | 13 => 39363573888
  | 14 => 26302879872
  | 15 => 42931124928
  | 16 => 41479936704
  | 17 => 40754653632
  | 18 => 27693679680
  | 19 => 40756053312
  | 20 => 40814793216
  | 21 => 27754099200
  | 22 => 42931156032
  | 23 => 40794964416
  | 24 => 40855104000
  | 25 => 42971466816
  | 26 => 27733990464
  | 27 => 27794409984
  | 28 => 40796364096
  | 29 => 39343745088
  | 30 => 26282771136
  | _ => 39345144768

private def packedStateVectorCodeChunk6 (index : Nat) : Nat :=
  match index with
  | 0 => 39403884672
  | 1 => 26343190656
  | 2 => 41520247488
  | 3 => 39343776192
  | 4 => 26282802240
  | 5 => 39345175872
  | 6 => 39403915776
  | 7 => 26343221760
  | 8 => 41520278592
  | 9 => 40814808768
  | 10 => 27754114752
  | 11 => 39363620544
  | 12 => 26302926528
  | 13 => 40754295936
  | 14 => 39303107712
  | 15 => 40814839872
  | 16 => 27754145856
  | 17 => 40754327040
  | 18 => 40855150656
  | 19 => 40794637824
  | 20 => 27794456640
  | 21 => 39403931328
  | 22 => 26343237312
  | 23 => 39343418496
  | 24 => 39403962432
  | 25 => 26343268416
  | 26 => 39343449600
  | 27 => 40754342592
  | 28 => 39303154368
  | 29 => 40754373696
  | 30 => 40794684480
  | _ => 39343465152

private def packedStateVectorCodeChunk7 (index : Nat) : Nat :=
  match index with
  | _ => 39343496256

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
    (coordinate : Fin 14) : Fin 6 :=
  ⟨(packedStateVectorCode state / 6 ^ coordinate.val) % 6,
    Nat.mod_lt _ (by decide)⟩

def generatorVector (generator : Fin 3)
    (coordinate : Fin 14) : Fin 6 :=
  match generator.val with
  | 0 =>
      match coordinate.val with
      | 0 => (1 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (5 : Fin 6)
      | 4 => (5 : Fin 6)
      | 5 => (1 : Fin 6)
      | 6 => (3 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (1 : Fin 6)
      | 10 => (0 : Fin 6)
      | 11 => (5 : Fin 6)
      | 12 => (1 : Fin 6)
      | _ => (0 : Fin 6)
  | 1 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (1 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (1 : Fin 6)
      | 5 => (4 : Fin 6)
      | 6 => (5 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (1 : Fin 6)
      | 9 => (5 : Fin 6)
      | 10 => (3 : Fin 6)
      | 11 => (4 : Fin 6)
      | 12 => (5 : Fin 6)
      | _ => (3 : Fin 6)
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
      | 9 => (4 : Fin 6)
      | 10 => (3 : Fin 6)
      | 11 => (0 : Fin 6)
      | 12 => (5 : Fin 6)
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
  if code = 129423744 then (38 : Fin 225) else
  if code = 129470400 then (72 : Fin 225) else
  if code = 169734528 then (59 : Fin 225) else
  if code = 169781184 then (102 : Fin 225) else
  if code = 189889920 then (78 : Fin 225) else
  if code = 189936576 then (122 : Fin 225) else
  if code = 190169856 then (14 : Fin 225) else
  if code = 190216512 then (34 : Fin 225) else
  if code = 230200704 then (105 : Fin 225) else
  if code = 230247360 then (151 : Fin 225) else
  if code = 230480640 then (26 : Fin 225) else
  if code = 230527296 then (57 : Fin 225) else
  if code = 1823883912 then (3 : Fin 225) else
  if code = 1823930568 then (12 : Fin 225) else
  if code = 2306260512 then (18 : Fin 225) else
  if code = 2346571296 then (28 : Fin 225) else
  if code = 2366726688 then (44 : Fin 225) else
  if code = 2367006624 then (5 : Fin 225) else
  if code = 2407037472 then (62 : Fin 225) else
  if code = 2407317408 then (9 : Fin 225) else
  if code = 4010798377 then (0 : Fin 225) else
  if code = 11053591776 then (11 : Fin 225) else
  if code = 11114057952 then (32 : Fin 225) else
  if code = 11114337924 then (2 : Fin 225) else
  if code = 26242413696 then (127 : Fin 225) else
  if code = 26242460352 then (169 : Fin 225) else
  if code = 26282724480 then (153 : Fin 225) else
  if code = 26282755584 then (160 : Fin 225) else
  if code = 26282771136 then (190 : Fin 225) else
  if code = 26282802240 then (196 : Fin 225) else
  if code = 26302879872 then (174 : Fin 225) else
  if code = 26302926528 then (204 : Fin 225) else
  (0 : Fin 225)

private def decodeStateCodeChunk1 (code : Nat) : Fin 225 :=
  if code = 26303159808 then (76 : Fin 225) else
  if code = 26303206464 then (120 : Fin 225) else
  if code = 26343190656 then (193 : Fin 225) else
  if code = 26343221760 then (199 : Fin 225) else
  if code = 26343237312 then (214 : Fin 225) else
  if code = 26343268416 then (217 : Fin 225) else
  if code = 26343470592 then (103 : Fin 225) else
  if code = 26343501696 then (110 : Fin 225) else
  if code = 26343517248 then (149 : Fin 225) else
  if code = 26343548352 then (157 : Fin 225) else
  if code = 27693601920 then (124 : Fin 225) else
  if code = 27693633024 then (137 : Fin 225) else
  if code = 27693648576 then (166 : Fin 225) else
  if code = 27693679680 then (178 : Fin 225) else
  if code = 27695001600 then (35 : Fin 225) else
  if code = 27695032704 then (46 : Fin 225) else
  if code = 27695048256 then (69 : Fin 225) else
  if code = 27695079360 then (85 : Fin 225) else
  if code = 27733943808 then (145 : Fin 225) else
  if code = 27733990464 then (186 : Fin 225) else
  if code = 27754068096 then (172 : Fin 225) else
  if code = 27754099200 then (181 : Fin 225) else
  if code = 27754114752 then (202 : Fin 225) else
  if code = 27754145856 then (208 : Fin 225) else
  if code = 27754348032 then (74 : Fin 225) else
  if code = 27754379136 then (88 : Fin 225) else
  if code = 27754394688 then (118 : Fin 225) else
  if code = 27754425792 then (134 : Fin 225) else
  if code = 27794409984 then (187 : Fin 225) else
  if code = 27794456640 then (212 : Fin 225) else
  if code = 27794689920 then (95 : Fin 225) else
  if code = 27794736576 then (144 : Fin 225) else
  (0 : Fin 225)

private def decodeStateCodeChunk2 (code : Nat) : Fin 225 :=
  if code = 28419242688 then (83 : Fin 225) else
  if code = 28459553472 then (107 : Fin 225) else
  if code = 28459584576 then (113 : Fin 225) else
  if code = 28479708864 then (132 : Fin 225) else
  if code = 28479988800 then (42 : Fin 225) else
  if code = 28520019648 then (156 : Fin 225) else
  if code = 28520050752 then (163 : Fin 225) else
  if code = 28520299584 then (60 : Fin 225) else
  if code = 28520330688 then (64 : Fin 225) else
  if code = 29870430912 then (80 : Fin 225) else
  if code = 29870462016 then (91 : Fin 225) else
  if code = 29881908288 then (15 : Fin 225) else
  if code = 29881939392 then (20 : Fin 225) else
  if code = 29910772800 then (96 : Fin 225) else
  if code = 29930897088 then (130 : Fin 225) else
  if code = 29930928192 then (140 : Fin 225) else
  if code = 29931177024 then (40 : Fin 225) else
  if code = 29931208128 then (49 : Fin 225) else
  if code = 29971238976 then (146 : Fin 225) else
  if code = 29971518912 then (52 : Fin 225) else
  if code = 37166573952 then (67 : Fin 225) else
  if code = 37227040128 then (116 : Fin 225) else
  if code = 37227320064 then (30 : Fin 225) else
  if code = 38617762176 then (53 : Fin 225) else
  if code = 38629472832 then (7 : Fin 225) else
  if code = 38678228352 then (97 : Fin 225) else
  if code = 38678508288 then (23 : Fin 225) else
  if code = 39303107712 then (206 : Fin 225) else
  if code = 39303154368 then (220 : Fin 225) else
  if code = 39303387648 then (126 : Fin 225) else
  if code = 39303434304 then (168 : Fin 225) else
  if code = 39304787328 then (128 : Fin 225) else
  (0 : Fin 225)

private def decodeStateCodeChunk3 (code : Nat) : Fin 225 :=
  if code = 39304833984 then (170 : Fin 225) else
  if code = 39305067264 then (37 : Fin 225) else
  if code = 39305113920 then (71 : Fin 225) else
  if code = 39343418496 then (215 : Fin 225) else
  if code = 39343449600 then (218 : Fin 225) else
  if code = 39343465152 then (223 : Fin 225) else
  if code = 39343496256 then (224 : Fin 225) else
  if code = 39343698432 then (152 : Fin 225) else
  if code = 39343729536 then (159 : Fin 225) else
  if code = 39343745088 then (189 : Fin 225) else
  if code = 39343776192 then (195 : Fin 225) else
  if code = 39345098112 then (154 : Fin 225) else
  if code = 39345129216 then (161 : Fin 225) else
  if code = 39345144768 then (191 : Fin 225) else
  if code = 39345175872 then (197 : Fin 225) else
  if code = 39345378048 then (58 : Fin 225) else
  if code = 39345409152 then (63 : Fin 225) else
  if code = 39345424704 then (101 : Fin 225) else
  if code = 39345455808 then (109 : Fin 225) else
  if code = 39363573888 then (173 : Fin 225) else
  if code = 39363620544 then (203 : Fin 225) else
  if code = 39365253504 then (77 : Fin 225) else
  if code = 39365300160 then (121 : Fin 225) else
  if code = 39403884672 then (192 : Fin 225) else
  if code = 39403915776 then (198 : Fin 225) else
  if code = 39403931328 then (213 : Fin 225) else
  if code = 39403962432 then (216 : Fin 225) else
  if code = 39405564288 then (104 : Fin 225) else
  if code = 39405595392 then (111 : Fin 225) else
  if code = 39405610944 then (150 : Fin 225) else
  if code = 39405642048 then (158 : Fin 225) else
  if code = 40754295936 then (205 : Fin 225) else
  (0 : Fin 225)

private def decodeStateCodeChunk4 (code : Nat) : Fin 225 :=
  if code = 40754327040 then (209 : Fin 225) else
  if code = 40754342592 then (219 : Fin 225) else
  if code = 40754373696 then (221 : Fin 225) else
  if code = 40754575872 then (123 : Fin 225) else
  if code = 40754606976 then (136 : Fin 225) else
  if code = 40754622528 then (165 : Fin 225) else
  if code = 40754653632 then (177 : Fin 225) else
  if code = 40755975552 then (125 : Fin 225) else
  if code = 40756006656 then (138 : Fin 225) else
  if code = 40756022208 then (167 : Fin 225) else
  if code = 40756053312 then (179 : Fin 225) else
  if code = 40756255488 then (36 : Fin 225) else
  if code = 40756286592 then (47 : Fin 225) else
  if code = 40756302144 then (70 : Fin 225) else
  if code = 40756333248 then (86 : Fin 225) else
  if code = 40794637824 then (211 : Fin 225) else
  if code = 40794684480 then (222 : Fin 225) else
  if code = 40794917760 then (141 : Fin 225) else
  if code = 40794964416 then (183 : Fin 225) else
  if code = 40796317440 then (148 : Fin 225) else
  if code = 40796364096 then (188 : Fin 225) else
  if code = 40796597376 then (54 : Fin 225) else
  if code = 40796644032 then (98 : Fin 225) else
  if code = 40814762112 then (171 : Fin 225) else
  if code = 40814793216 then (180 : Fin 225) else
  if code = 40814808768 then (201 : Fin 225) else
  if code = 40814839872 then (207 : Fin 225) else
  if code = 40816161792 then (73 : Fin 225) else
  if code = 40816192896 then (87 : Fin 225) else
  if code = 40816208448 then (117 : Fin 225) else
  if code = 40816239552 then (133 : Fin 225) else
  if code = 40816441728 then (75 : Fin 225) else
  (0 : Fin 225)

private def decodeStateCodeChunk5 (code : Nat) : Fin 225 :=
  if code = 40816472832 then (89 : Fin 225) else
  if code = 40816488384 then (119 : Fin 225) else
  if code = 40816519488 then (135 : Fin 225) else
  if code = 40817842704 then (13 : Fin 225) else
  if code = 40817873808 then (19 : Fin 225) else
  if code = 40817889360 then (33 : Fin 225) else
  if code = 40817920464 then (45 : Fin 225) else
  if code = 40855104000 then (184 : Fin 225) else
  if code = 40855150656 then (210 : Fin 225) else
  if code = 40856783616 then (99 : Fin 225) else
  if code = 40856830272 then (147 : Fin 225) else
  if code = 41479936704 then (176 : Fin 225) else
  if code = 41480216640 then (82 : Fin 225) else
  if code = 41481616320 then (84 : Fin 225) else
  if code = 41481896256 then (17 : Fin 225) else
  if code = 41520247488 then (194 : Fin 225) else
  if code = 41520278592 then (200 : Fin 225) else
  if code = 41520527424 then (106 : Fin 225) else
  if code = 41520558528 then (112 : Fin 225) else
  if code = 41521927104 then (108 : Fin 225) else
  if code = 41521958208 then (114 : Fin 225) else
  if code = 41522207040 then (27 : Fin 225) else
  if code = 41522238144 then (29 : Fin 225) else
  if code = 41540402880 then (131 : Fin 225) else
  if code = 41542082496 then (43 : Fin 225) else
  if code = 41580713664 then (155 : Fin 225) else
  if code = 41580744768 then (162 : Fin 225) else
  if code = 41582393280 then (61 : Fin 225) else
  if code = 41582424384 then (65 : Fin 225) else
  if code = 42931124928 then (175 : Fin 225) else
  if code = 42931156032 then (182 : Fin 225) else
  if code = 42931404864 then (79 : Fin 225) else
  (0 : Fin 225)

private def decodeStateCodeChunk6 (code : Nat) : Fin 225 :=
  if code = 42931435968 then (90 : Fin 225) else
  if code = 42932804544 then (81 : Fin 225) else
  if code = 42932835648 then (92 : Fin 225) else
  if code = 42933084480 then (16 : Fin 225) else
  if code = 42933115584 then (21 : Fin 225) else
  if code = 42971466816 then (185 : Fin 225) else
  if code = 42971746752 then (93 : Fin 225) else
  if code = 42973146432 then (100 : Fin 225) else
  if code = 42973426368 then (24 : Fin 225) else
  if code = 42991591104 then (129 : Fin 225) else
  if code = 42991622208 then (139 : Fin 225) else
  if code = 42993270720 then (41 : Fin 225) else
  if code = 42993301824 then (50 : Fin 225) else
  if code = 43003068480 then (39 : Fin 225) else
  if code = 43003099584 then (48 : Fin 225) else
  if code = 43004749392 then (4 : Fin 225) else
  if code = 43004780496 then (6 : Fin 225) else
  if code = 43031932992 then (142 : Fin 225) else
  if code = 43033612608 then (55 : Fin 225) else
  if code = 50227267968 then (164 : Fin 225) else
  if code = 50227547904 then (66 : Fin 225) else
  if code = 50228947584 then (68 : Fin 225) else
  if code = 50229227520 then (10 : Fin 225) else
  if code = 50287734144 then (115 : Fin 225) else
  if code = 50289413760 then (31 : Fin 225) else
  if code = 51678456192 then (143 : Fin 225) else
  if code = 51678736128 then (51 : Fin 225) else
  if code = 51680135808 then (56 : Fin 225) else
  if code = 51680415744 then (8 : Fin 225) else
  if code = 51738922368 then (94 : Fin 225) else
  if code = 51740601984 then (25 : Fin 225) else
  if code = 51750633024 then (22 : Fin 225) else
  (0 : Fin 225)

private def decodeStateCodeChunk7 (code : Nat) : Fin 225 :=
  if code = 51752313942 then (1 : Fin 225) else
  (0 : Fin 225)

private def stateVectorCode
    (vector : Fin 14 -> Fin 6) : Nat :=
  (vector (0 : Fin 14)).val + 6 * ((vector (1 : Fin 14)).val + 6 * ((vector (2 : Fin 14)).val + 6 * ((vector (3 : Fin 14)).val + 6 * ((vector (4 : Fin 14)).val + 6 * ((vector (5 : Fin 14)).val + 6 * ((vector (6 : Fin 14)).val + 6 * ((vector (7 : Fin 14)).val + 6 * ((vector (8 : Fin 14)).val + 6 * ((vector (9 : Fin 14)).val + 6 * ((vector (10 : Fin 14)).val + 6 * ((vector (11 : Fin 14)).val + 6 * ((vector (12 : Fin 14)).val + 6 * ((vector (13 : Fin 14)).val)))))))))))))

private def decodeStateCode (code : Nat) : Fin 225 :=
  if code < 26303159808 then decodeStateCodeChunk0 code else
  if code < 28419242688 then decodeStateCodeChunk1 code else
  if code < 39304833984 then decodeStateCodeChunk2 code else
  if code < 40754327040 then decodeStateCodeChunk3 code else
  if code < 40816472832 then decodeStateCodeChunk4 code else
  if code < 42931435968 then decodeStateCodeChunk5 code else
  if code < 51752313942 then decodeStateCodeChunk6 code else
  decodeStateCodeChunk7 code

private def decodeState
    (vector : Fin 14 -> Fin 6) : Fin 225 :=
  decodeStateCode (stateVectorCode vector)

set_option maxHeartbeats 2000000 in
private theorem decodeState_stateVector (state : Fin 225) :
    decodeState (stateVector state) = state := by
  decide +revert

set_option maxHeartbeats 2000000 in
private theorem transitionMap :
    forall (state : Fin 225)
      (generator : Fin 3)
      (coordinate : Fin 14),
      stateVector (transition state generator) coordinate =
        oppositeTable.semigroup.mul (stateVector state coordinate)
          (generatorVector generator coordinate) := by
  intro state generator coordinate
  apply Fin.ext
  exact by decide +revert

set_option maxHeartbeats 2000000 in
private theorem representativeMap :
    forall (state : Fin 225)
      (coordinate : Fin 14),
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
    (I := Fin 14) oppositeTable.semigroup where
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
        (Fin 14) targetValid
    have subValid :=
      powerCertificate.embedding.pullback_identity identity powerValid
    exact quotient.pushforwardIdentity identity subValid

/-- First-layer generic-CAS basis wrapper for `S6_11780`. -/
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

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11780
