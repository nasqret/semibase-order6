import SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_15879Representative
import SemigroupBasis.FiniteNilpotentCounterexample
import SemigroupBasis.Nonfinite
import SemigroupBasis.Opposite
import SemigroupBasis.RightGeneratedPowerCertificate

set_option maxRecDepth 2048

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_15912

open SemigroupBasis

def routeManifestRowSHA256 : String := "ad3d28a9288f02c701c8bec6f81fe428059d98087ddc12aba8bb4c7a6a14bdff"
def witnessRecordSHA256 : String := "8c6fd2479fbe85ee90ad7a28eb459ae1360f1d3fb2e8d83a02b75e0a7702369d"
def transferComponentSHA256 : String := "8c6fd2479fbe85ee90ad7a28eb459ae1360f1d3fb2e8d83a02b75e0a7702369d"
def powerCertificateSHA256 : String := "00831868b70258bca283043ce0faa985b6f9b723b47087fa1d0b537a9c259193"

private def row6
    (c0 c1 c2 c3 c4 c5 : Fin 6) (column : Fin 6) : Fin 6 :=
  if column = 0 then c0 else
    if column = 1 then c1 else
      if column = 2 then c2 else
        if column = 3 then c3 else
          if column = 4 then c4 else c5

/-- Exact one-based catalogue table committed by the portable witness. -/
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 0 0 4 5 right else
    if left = 1 then row6 0 1 1 3 4 5 right else
      if left = 2 then row6 0 1 2 3 4 5 right else
        if left = 3 then row6 0 1 3 3 4 5 right else
          if left = 4 then row6 4 4 4 4 5 0 right else
            row6 5 5 5 5 0 4 right

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
  "dc48fd816f7ad37d836ad161919edd8b697b1829a63cef5cec74ad401a00b922"

private def packedStateVectorCodeChunk0 (index : Nat) : Nat :=
  match index with
  | 0 => 5898877
  | 1 => 2311674
  | 2 => 3695256
  | 3 => 5898883
  | 4 => 5906868
  | 5 => 5891136
  | 6 => 2544972
  | 7 => 2311890
  | 8 => 2031840
  | 9 => 5328240
  | 10 => 2016288
  | 11 => 3695292
  | 12 => 5898853
  | 13 => 5906874
  | 14 => 5891142
  | 15 => 5907084
  | 16 => 5906904
  | 17 => 5891352
  | 18 => 5891172
  | 19 => 2544978
  | 20 => 2545188
  | 21 => 2545080
  | 22 => 2310810
  | 23 => 2032056
  | 24 => 1985208
  | 25 => 2031876
  | 26 => 5328246
  | 27 => 5328888
  | 28 => 5328276
  | 29 => 1969656
  | 30 => 2016504
  | _ => 2016324

private def packedStateVectorCodeChunk1 (index : Nat) : Nat :=
  match index with
  | 0 => 3695112
  | 1 => 5906844
  | 2 => 5891112
  | 3 => 5907090
  | 4 => 5906910
  | 5 => 5891358
  | 6 => 5891178
  | 7 => 5906004
  | 8 => 5907120
  | 9 => 5906940
  | 10 => 5891568
  | 11 => 5891388
  | 12 => 5890992
  | 13 => 2544948
  | 14 => 2545194
  | 15 => 2545086
  | 16 => 2544108
  | 17 => 2545296
  | 18 => 2545116
  | 19 => 2030976
  | 20 => 1985424
  | 21 => 2032092
  | 22 => 1985214
  | 23 => 1985244
  | 24 => 2031696
  | 25 => 5328216
  | 26 => 5328894
  | 27 => 5328282
  | 28 => 5329104
  | 29 => 5328924
  | 30 => 5328096
  | _ => 1969662

private def packedStateVectorCodeChunk2 (index : Nat) : Nat :=
  match index with
  | 0 => 1969872
  | 1 => 1969692
  | 2 => 2015424
  | 3 => 2016540
  | 4 => 2016144
  | 5 => 5907060
  | 6 => 5906880
  | 7 => 5891328
  | 8 => 5891148
  | 9 => 5906010
  | 10 => 5907126
  | 11 => 5906946
  | 12 => 5891574
  | 13 => 5891394
  | 14 => 5890998
  | 15 => 5906040
  | 16 => 5907156
  | 17 => 5906760
  | 18 => 5890488
  | 19 => 5891604
  | 20 => 5891208
  | 21 => 2545164
  | 22 => 2545056
  | 23 => 2544114
  | 24 => 2545302
  | 25 => 2545122
  | 26 => 2544216
  | 27 => 2545332
  | 28 => 2544936
  | 29 => 1984344
  | 30 => 2031012
  | _ => 1985430

private def packedStateVectorCodeChunk3 (index : Nat) : Nat :=
  match index with
  | 0 => 1985460
  | 1 => 2031912
  | 2 => 1985184
  | 3 => 1985250
  | 4 => 1985064
  | 5 => 5328864
  | 6 => 5328252
  | 7 => 5329110
  | 8 => 5328930
  | 9 => 5328102
  | 10 => 5328024
  | 11 => 5329140
  | 12 => 5328744
  | 13 => 1969632
  | 14 => 1969878
  | 15 => 1969698
  | 16 => 1968792
  | 17 => 1969908
  | 18 => 1969512
  | 19 => 2015460
  | 20 => 2016360
  | 21 => 5905980
  | 22 => 5907096
  | 23 => 5906916
  | 24 => 5891544
  | 25 => 5891364
  | 26 => 5890968
  | 27 => 5906046
  | 28 => 5907162
  | 29 => 5906766
  | 30 => 5890494
  | _ => 5891610

private def packedStateVectorCodeChunk4 (index : Nat) : Nat :=
  match index with
  | 0 => 5891214
  | 1 => 5906076
  | 2 => 5906976
  | 3 => 5890524
  | 4 => 5891424
  | 5 => 2544084
  | 6 => 2545272
  | 7 => 2545092
  | 8 => 2544222
  | 9 => 2545338
  | 10 => 2544942
  | 11 => 2544252
  | 12 => 2545152
  | 13 => 1984350
  | 14 => 1984380
  | 15 => 2030832
  | 16 => 1985400
  | 17 => 1985466
  | 18 => 1985280
  | 19 => 1985220
  | 20 => 1985070
  | 21 => 5329080
  | 22 => 5328900
  | 23 => 5328072
  | 24 => 5328030
  | 25 => 5329146
  | 26 => 5328750
  | 27 => 5328060
  | 28 => 5328960
  | 29 => 1969848
  | 30 => 1969668
  | _ => 1968798

private def packedStateVectorCodeChunk5 (index : Nat) : Nat :=
  match index with
  | 0 => 1969914
  | 1 => 1969518
  | 2 => 1968828
  | 3 => 1969728
  | 4 => 2015280
  | 5 => 5906016
  | 6 => 5907132
  | 7 => 5906736
  | 8 => 5890464
  | 9 => 5891580
  | 10 => 5891184
  | 11 => 5906082
  | 12 => 5906982
  | 13 => 5890530
  | 14 => 5891430
  | 15 => 5905896
  | 16 => 5890344
  | 17 => 2544192
  | 18 => 2545308
  | 19 => 2544912
  | 20 => 2544258
  | 21 => 2545158
  | 22 => 2544072
  | 23 => 1984320
  | 24 => 1984386
  | 25 => 1984200
  | 26 => 1985436
  | 27 => 1985286
  | 28 => 1985040
  | 29 => 5328000
  | 30 => 5329116
  | _ => 5328720

private def packedStateVectorCodeChunk6 (index : Nat) : Nat :=
  match index with
  | 0 => 5328066
  | 1 => 5328966
  | 2 => 5327880
  | 3 => 1968768
  | 4 => 1969884
  | 5 => 1969488
  | 6 => 1968834
  | 7 => 1969734
  | 8 => 1968648
  | 9 => 5906052
  | 10 => 5906952
  | 11 => 5890500
  | 12 => 5891400
  | 13 => 5905902
  | 14 => 5890350
  | 15 => 2544228
  | 16 => 2545128
  | 17 => 2544078
  | 18 => 1984356
  | 19 => 1984206
  | 20 => 1985256
  | 21 => 5328036
  | 22 => 5328936
  | 23 => 5327886
  | 24 => 1968804
  | 25 => 1969704
  | 26 => 1968654
  | 27 => 5905872
  | 28 => 5890320
  | 29 => 2544048
  | 30 => 1984176
  | _ => 5327856

private def packedStateVectorCodeChunk7 (index : Nat) : Nat :=
  match index with
  | _ => 1968624

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
      | 0 => (1 : Fin 6)
      | 1 => (4 : Fin 6)
      | 2 => (3 : Fin 6)
      | 3 => (3 : Fin 6)
      | 4 => (3 : Fin 6)
      | 5 => (2 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (3 : Fin 6)
      | _ => (3 : Fin 6)
  | 1 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (1 : Fin 6)
      | 2 => (1 : Fin 6)
      | 3 => (4 : Fin 6)
      | 4 => (1 : Fin 6)
      | 5 => (3 : Fin 6)
      | 6 => (1 : Fin 6)
      | 7 => (2 : Fin 6)
      | _ => (1 : Fin 6)
  | _ =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (4 : Fin 6)
      | 3 => (1 : Fin 6)
      | 4 => (1 : Fin 6)
      | 5 => (1 : Fin 6)
      | 6 => (1 : Fin 6)
      | 7 => (1 : Fin 6)
      | _ => (2 : Fin 6)

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
  | 12 => 1728675
  | 13 => 1830408
  | 14 => 1932109
  | 15 => 2033810
  | 16 => 2084661
  | 17 => 2186362
  | 18 => 2237213
  | 19 => 2389770
  | 20 => 2491471
  | 21 => 2542322
  | 22 => 2582148
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
  | 0 => 116612
  | 1 => 3559279
  | 2 => 3660980
  | 3 => 3762744
  | 4 => 3813595
  | 5 => 3915296
  | 6 => 3966147
  | 7 => 4000348
  | 8 => 4067849
  | 9 => 4118700
  | 10 => 4220401
  | 11 => 4271252
  | 12 => 272103
  | 13 => 4372881
  | 14 => 4474660
  | 15 => 4525511
  | 16 => 4557687
  | 17 => 4627213
  | 18 => 4678064
  | 19 => 4760643
  | 20 => 4881020
  | 21 => 4931871
  | 22 => 5033348
  | 23 => 5084199
  | 24 => 426925
  | 25 => 5186484
  | 26 => 5288276
  | 27 => 5339127
  | 28 => 5440828
  | 29 => 5491679
  | 30 => 480030
  | _ => 5644234

private def packedTransitionCodeChunk2 (index : Nat) : Nat :=
  match index with
  | 0 => 5745935
  | 1 => 5796786
  | 2 => 5824237
  | 3 => 5898488
  | 4 => 532464
  | 5 => 6000090
  | 6 => 6050941
  | 7 => 6152642
  | 8 => 6203493
  | 9 => 6229917
  | 10 => 6305293
  | 11 => 6356144
  | 12 => 6457845
  | 13 => 6508696
  | 14 => 737672
  | 15 => 6534348
  | 16 => 6610399
  | 17 => 839375
  | 18 => 6635826
  | 19 => 6712102
  | 20 => 890453
  | 21 => 6813695
  | 22 => 6864546
  | 23 => 6889408
  | 24 => 6966359
  | 25 => 7017210
  | 26 => 7041736
  | 27 => 7118912
  | 28 => 1094763
  | 29 => 7194291
  | 30 => 7245142
  | _ => 7372494

private def packedTransitionCodeChunk3 (index : Nat) : Nat :=
  match index with
  | 0 => 7423345
  | 1 => 1196696
  | 2 => 7474299
  | 3 => 7525272
  | 4 => 1247998
  | 5 => 7627302
  | 6 => 7678153
  | 7 => 7779974
  | 8 => 7830825
  | 9 => 1351051
  | 10 => 7853102
  | 11 => 7932528
  | 12 => 1402129
  | 13 => 8034104
  | 14 => 8135932
  | 15 => 8186783
  | 16 => 8207934
  | 17 => 8288485
  | 18 => 1504961
  | 19 => 8309637
  | 20 => 1555813
  | 21 => 8360589
  | 22 => 8440915
  | 23 => 8491766
  | 24 => 8593467
  | 25 => 8644318
  | 26 => 1759544
  | 27 => 8665140
  | 28 => 8746141
  | 29 => 1861367
  | 30 => 8766618
  | _ => 8847844

private def packedTransitionCodeChunk4 (index : Nat) : Nat :=
  match index with
  | 0 => 1912445
  | 1 => 8868771
  | 2 => 2064547
  | 3 => 8919848
  | 4 => 2166024
  | 5 => 8970798
  | 6 => 9051124
  | 7 => 9101975
  | 8 => 9123252
  | 9 => 9203803
  | 10 => 2420279
  | 11 => 9225180
  | 12 => 2521756
  | 13 => 9327333
  | 14 => 9378184
  | 15 => 2594660
  | 16 => 9457477
  | 17 => 9508461
  | 18 => 2674312
  | 19 => 9559405
  | 20 => 2776013
  | 21 => 9661335
  | 22 => 9712186
  | 23 => 2928662
  | 24 => 9733239
  | 25 => 9814015
  | 26 => 2979866
  | 27 => 9835167
  | 28 => 3081343
  | 29 => 9966439
  | 30 => 10017290
  | _ => 10038120

private def packedTransitionCodeChunk5 (index : Nat) : Nat :=
  match index with
  | 0 => 10119121
  | 1 => 3234347
  | 2 => 10139823
  | 3 => 3285199
  | 4 => 3356750
  | 5 => 10191454
  | 6 => 10271555
  | 7 => 3589281
  | 8 => 10292932
  | 9 => 10373258
  | 10 => 3640359
  | 11 => 10395201
  | 12 => 3792577
  | 13 => 10446278
  | 14 => 3894054
  | 15 => 4017805
  | 16 => 4170356
  | 17 => 10498815
  | 18 => 10576666
  | 19 => 4400642
  | 20 => 10600857
  | 21 => 4502233
  | 22 => 4577159
  | 23 => 10653393
  | 24 => 10704360
  | 25 => 4730836
  | 26 => 10779846
  | 27 => 4857062
  | 28 => 5009050
  | 29 => 10805956
  | 30 => 10881782
  | _ => 5161383

private def packedTransitionCodeChunk6 (index : Nat) : Nat :=
  match index with
  | 0 => 10907988
  | 1 => 5262964
  | 2 => 5390765
  | 3 => 10959637
  | 4 => 11034338
  | 5 => 5567064
  | 6 => 11061441
  | 7 => 5618017
  | 8 => 5695868
  | 9 => 11113779
  | 10 => 6023155
  | 11 => 11164856
  | 12 => 6124632
  | 13 => 6255219
  | 14 => 6407770
  | 15 => 11218639
  | 16 => 6833615
  | 17 => 6916271
  | 18 => 11271967
  | 19 => 7171647
  | 20 => 7340096
  | 21 => 11323280
  | 22 => 7593456
  | 23 => 7729873
  | 24 => 11375712
  | 25 => 7998688
  | 26 => 8085824
  | 27 => 8390875
  | 28 => 8543426
  | 29 => 9001082
  | 30 => 9306860
  | _ => 9611294

private def packedTransitionCodeChunk7 (index : Nat) : Nat :=
  match index with
  | _ => 9916400

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
  | 0 => 135760216550945770111976029086127419791016418
  | 1 => 1050806598534334314243356863602533930489984893920
  | 2 => 175945240660939971007355769950737611345444308958
  | _ => 776829203291726827347456

def sourceLabel (state : Fin 225) : Fin 6 :=
  ⟨(packedSourceLabelBlockCode (state.val / 64) /
      6 ^ (state.val % 64)) % 6,
    Nat.mod_lt _ (by decide)⟩

def generatorSourceLabel (generator : Fin 3) : Fin 6 :=
  match generator.val with
  | 0 => (4 : Fin 6)
  | 1 => (3 : Fin 6)
  | _ => (1 : Fin 6)

def sourcePreimage (value : Fin 6) : Fin 225 :=
  match value.val with
  | 0 => (5 : Fin 225)
  | 1 => (2 : Fin 225)
  | 2 => (12 : Fin 225)
  | 3 => (1 : Fin 225)
  | 4 => (0 : Fin 225)
  | _ => (3 : Fin 225)

private def decodeStateCodeChunk0 (code : Nat) : Fin 225 :=
  if code = 1968624 then (224 : Fin 225) else
  if code = 1968648 then (200 : Fin 225) else
  if code = 1968654 then (218 : Fin 225) else
  if code = 1968768 then (195 : Fin 225) else
  if code = 1968792 then (112 : Fin 225) else
  if code = 1968798 then (159 : Fin 225) else
  if code = 1968804 then (216 : Fin 225) else
  if code = 1968828 then (162 : Fin 225) else
  if code = 1968834 then (198 : Fin 225) else
  if code = 1969488 then (197 : Fin 225) else
  if code = 1969512 then (114 : Fin 225) else
  if code = 1969518 then (161 : Fin 225) else
  if code = 1969632 then (109 : Fin 225) else
  if code = 1969656 then (29 : Fin 225) else
  if code = 1969662 then (63 : Fin 225) else
  if code = 1969668 then (158 : Fin 225) else
  if code = 1969692 then (65 : Fin 225) else
  if code = 1969698 then (111 : Fin 225) else
  if code = 1969704 then (217 : Fin 225) else
  if code = 1969728 then (163 : Fin 225) else
  if code = 1969734 then (199 : Fin 225) else
  if code = 1969848 then (157 : Fin 225) else
  if code = 1969872 then (64 : Fin 225) else
  if code = 1969878 then (110 : Fin 225) else
  if code = 1969884 then (196 : Fin 225) else
  if code = 1969908 then (113 : Fin 225) else
  if code = 1969914 then (160 : Fin 225) else
  if code = 1984176 then (222 : Fin 225) else
  if code = 1984200 then (185 : Fin 225) else
  if code = 1984206 then (211 : Fin 225) else
  if code = 1984320 then (183 : Fin 225) else
  if code = 1984344 then (93 : Fin 225) else
  (0 : Fin 225)

private def decodeStateCodeChunk1 (code : Nat) : Fin 225 :=
  if code = 1984350 then (141 : Fin 225) else
  if code = 1984356 then (210 : Fin 225) else
  if code = 1984380 then (142 : Fin 225) else
  if code = 1984386 then (184 : Fin 225) else
  if code = 1985040 then (188 : Fin 225) else
  if code = 1985064 then (100 : Fin 225) else
  if code = 1985070 then (148 : Fin 225) else
  if code = 1985184 then (98 : Fin 225) else
  if code = 1985208 then (24 : Fin 225) else
  if code = 1985214 then (54 : Fin 225) else
  if code = 1985220 then (147 : Fin 225) else
  if code = 1985244 then (55 : Fin 225) else
  if code = 1985250 then (99 : Fin 225) else
  if code = 1985256 then (212 : Fin 225) else
  if code = 1985280 then (146 : Fin 225) else
  if code = 1985286 then (187 : Fin 225) else
  if code = 1985400 then (144 : Fin 225) else
  if code = 1985424 then (52 : Fin 225) else
  if code = 1985430 then (95 : Fin 225) else
  if code = 1985436 then (186 : Fin 225) else
  if code = 1985460 then (96 : Fin 225) else
  if code = 1985466 then (145 : Fin 225) else
  if code = 2015280 then (164 : Fin 225) else
  if code = 2015424 then (66 : Fin 225) else
  if code = 2015460 then (115 : Fin 225) else
  if code = 2016144 then (68 : Fin 225) else
  if code = 2016288 then (10 : Fin 225) else
  if code = 2016324 then (31 : Fin 225) else
  if code = 2016360 then (116 : Fin 225) else
  if code = 2016504 then (30 : Fin 225) else
  if code = 2016540 then (67 : Fin 225) else
  if code = 2030832 then (143 : Fin 225) else
  (0 : Fin 225)

private def decodeStateCodeChunk2 (code : Nat) : Fin 225 :=
  if code = 2030976 then (51 : Fin 225) else
  if code = 2031012 then (94 : Fin 225) else
  if code = 2031696 then (56 : Fin 225) else
  if code = 2031840 then (8 : Fin 225) else
  if code = 2031876 then (25 : Fin 225) else
  if code = 2031912 then (97 : Fin 225) else
  if code = 2032056 then (23 : Fin 225) else
  if code = 2032092 then (53 : Fin 225) else
  if code = 2310810 then (22 : Fin 225) else
  if code = 2311674 then (1 : Fin 225) else
  if code = 2311890 then (7 : Fin 225) else
  if code = 2544048 then (221 : Fin 225) else
  if code = 2544072 then (182 : Fin 225) else
  if code = 2544078 then (209 : Fin 225) else
  if code = 2544084 then (133 : Fin 225) else
  if code = 2544108 then (48 : Fin 225) else
  if code = 2544114 then (87 : Fin 225) else
  if code = 2544192 then (177 : Fin 225) else
  if code = 2544216 then (90 : Fin 225) else
  if code = 2544222 then (136 : Fin 225) else
  if code = 2544228 then (207 : Fin 225) else
  if code = 2544252 then (139 : Fin 225) else
  if code = 2544258 then (180 : Fin 225) else
  if code = 2544912 then (179 : Fin 225) else
  if code = 2544936 then (92 : Fin 225) else
  if code = 2544942 then (138 : Fin 225) else
  if code = 2544948 then (45 : Fin 225) else
  if code = 2544972 then (6 : Fin 225) else
  if code = 2544978 then (19 : Fin 225) else
  if code = 2545056 then (86 : Fin 225) else
  if code = 2545080 then (21 : Fin 225) else
  if code = 2545086 then (47 : Fin 225) else
  (0 : Fin 225)

private def decodeStateCodeChunk3 (code : Nat) : Fin 225 :=
  if code = 2545092 then (135 : Fin 225) else
  if code = 2545116 then (50 : Fin 225) else
  if code = 2545122 then (89 : Fin 225) else
  if code = 2545128 then (208 : Fin 225) else
  if code = 2545152 then (140 : Fin 225) else
  if code = 2545158 then (181 : Fin 225) else
  if code = 2545164 then (85 : Fin 225) else
  if code = 2545188 then (20 : Fin 225) else
  if code = 2545194 then (46 : Fin 225) else
  if code = 2545272 then (134 : Fin 225) else
  if code = 2545296 then (49 : Fin 225) else
  if code = 2545302 then (88 : Fin 225) else
  if code = 2545308 then (178 : Fin 225) else
  if code = 2545332 then (91 : Fin 225) else
  if code = 2545338 then (137 : Fin 225) else
  if code = 3695112 then (32 : Fin 225) else
  if code = 3695256 then (2 : Fin 225) else
  if code = 3695292 then (11 : Fin 225) else
  if code = 5327856 then (223 : Fin 225) else
  if code = 5327880 then (194 : Fin 225) else
  if code = 5327886 then (215 : Fin 225) else
  if code = 5328000 then (189 : Fin 225) else
  if code = 5328024 then (106 : Fin 225) else
  if code = 5328030 then (152 : Fin 225) else
  if code = 5328036 then (213 : Fin 225) else
  if code = 5328060 then (155 : Fin 225) else
  if code = 5328066 then (192 : Fin 225) else
  if code = 5328072 then (151 : Fin 225) else
  if code = 5328096 then (62 : Fin 225) else
  if code = 5328102 then (105 : Fin 225) else
  if code = 5328216 then (57 : Fin 225) else
  if code = 5328240 then (9 : Fin 225) else
  (0 : Fin 225)

private def decodeStateCodeChunk4 (code : Nat) : Fin 225 :=
  if code = 5328246 then (26 : Fin 225) else
  if code = 5328252 then (102 : Fin 225) else
  if code = 5328276 then (28 : Fin 225) else
  if code = 5328282 then (59 : Fin 225) else
  if code = 5328720 then (191 : Fin 225) else
  if code = 5328744 then (108 : Fin 225) else
  if code = 5328750 then (154 : Fin 225) else
  if code = 5328864 then (101 : Fin 225) else
  if code = 5328888 then (27 : Fin 225) else
  if code = 5328894 then (58 : Fin 225) else
  if code = 5328900 then (150 : Fin 225) else
  if code = 5328924 then (61 : Fin 225) else
  if code = 5328930 then (104 : Fin 225) else
  if code = 5328936 then (214 : Fin 225) else
  if code = 5328960 then (156 : Fin 225) else
  if code = 5328966 then (193 : Fin 225) else
  if code = 5329080 then (149 : Fin 225) else
  if code = 5329104 then (60 : Fin 225) else
  if code = 5329110 then (103 : Fin 225) else
  if code = 5329116 then (190 : Fin 225) else
  if code = 5329140 then (107 : Fin 225) else
  if code = 5329146 then (153 : Fin 225) else
  if code = 5890320 then (220 : Fin 225) else
  if code = 5890344 then (176 : Fin 225) else
  if code = 5890350 then (206 : Fin 225) else
  if code = 5890464 then (168 : Fin 225) else
  if code = 5890488 then (82 : Fin 225) else
  if code = 5890494 then (126 : Fin 225) else
  if code = 5890500 then (203 : Fin 225) else
  if code = 5890524 then (131 : Fin 225) else
  if code = 5890530 then (173 : Fin 225) else
  if code = 5890968 then (122 : Fin 225) else
  (0 : Fin 225)

private def decodeStateCodeChunk5 (code : Nat) : Fin 225 :=
  if code = 5890992 then (44 : Fin 225) else
  if code = 5890998 then (78 : Fin 225) else
  if code = 5891112 then (34 : Fin 225) else
  if code = 5891136 then (5 : Fin 225) else
  if code = 5891142 then (14 : Fin 225) else
  if code = 5891148 then (72 : Fin 225) else
  if code = 5891172 then (18 : Fin 225) else
  if code = 5891178 then (38 : Fin 225) else
  if code = 5891184 then (170 : Fin 225) else
  if code = 5891208 then (84 : Fin 225) else
  if code = 5891214 then (128 : Fin 225) else
  if code = 5891328 then (71 : Fin 225) else
  if code = 5891352 then (17 : Fin 225) else
  if code = 5891358 then (37 : Fin 225) else
  if code = 5891364 then (121 : Fin 225) else
  if code = 5891388 then (43 : Fin 225) else
  if code = 5891394 then (77 : Fin 225) else
  if code = 5891400 then (204 : Fin 225) else
  if code = 5891424 then (132 : Fin 225) else
  if code = 5891430 then (174 : Fin 225) else
  if code = 5891544 then (120 : Fin 225) else
  if code = 5891568 then (42 : Fin 225) else
  if code = 5891574 then (76 : Fin 225) else
  if code = 5891580 then (169 : Fin 225) else
  if code = 5891604 then (83 : Fin 225) else
  if code = 5891610 then (127 : Fin 225) else
  if code = 5898853 then (12 : Fin 225) else
  if code = 5898877 then (0 : Fin 225) else
  if code = 5898883 then (3 : Fin 225) else
  if code = 5905872 then (219 : Fin 225) else
  if code = 5905896 then (175 : Fin 225) else
  if code = 5905902 then (205 : Fin 225) else
  (0 : Fin 225)

private def decodeStateCodeChunk6 (code : Nat) : Fin 225 :=
  if code = 5905980 then (117 : Fin 225) else
  if code = 5906004 then (39 : Fin 225) else
  if code = 5906010 then (73 : Fin 225) else
  if code = 5906016 then (165 : Fin 225) else
  if code = 5906040 then (79 : Fin 225) else
  if code = 5906046 then (123 : Fin 225) else
  if code = 5906052 then (201 : Fin 225) else
  if code = 5906076 then (129 : Fin 225) else
  if code = 5906082 then (171 : Fin 225) else
  if code = 5906736 then (167 : Fin 225) else
  if code = 5906760 then (81 : Fin 225) else
  if code = 5906766 then (125 : Fin 225) else
  if code = 5906844 then (33 : Fin 225) else
  if code = 5906868 then (4 : Fin 225) else
  if code = 5906874 then (13 : Fin 225) else
  if code = 5906880 then (70 : Fin 225) else
  if code = 5906904 then (16 : Fin 225) else
  if code = 5906910 then (36 : Fin 225) else
  if code = 5906916 then (119 : Fin 225) else
  if code = 5906940 then (41 : Fin 225) else
  if code = 5906946 then (75 : Fin 225) else
  if code = 5906952 then (202 : Fin 225) else
  if code = 5906976 then (130 : Fin 225) else
  if code = 5906982 then (172 : Fin 225) else
  if code = 5907060 then (69 : Fin 225) else
  if code = 5907084 then (15 : Fin 225) else
  if code = 5907090 then (35 : Fin 225) else
  if code = 5907096 then (118 : Fin 225) else
  if code = 5907120 then (40 : Fin 225) else
  if code = 5907126 then (74 : Fin 225) else
  if code = 5907132 then (166 : Fin 225) else
  if code = 5907156 then (80 : Fin 225) else
  (0 : Fin 225)

private def decodeStateCodeChunk7 (code : Nat) : Fin 225 :=
  if code = 5907162 then (124 : Fin 225) else
  (0 : Fin 225)

private def stateVectorCode
    (vector : Fin 9 -> Fin 6) : Nat :=
  (vector (0 : Fin 9)).val + 6 * ((vector (1 : Fin 9)).val + 6 * ((vector (2 : Fin 9)).val + 6 * ((vector (3 : Fin 9)).val + 6 * ((vector (4 : Fin 9)).val + 6 * ((vector (5 : Fin 9)).val + 6 * ((vector (6 : Fin 9)).val + 6 * ((vector (7 : Fin 9)).val + 6 * ((vector (8 : Fin 9)).val))))))))

private def decodeStateCode (code : Nat) : Fin 225 :=
  if code < 1984350 then decodeStateCodeChunk0 code else
  if code < 2030976 then decodeStateCodeChunk1 code else
  if code < 2545092 then decodeStateCodeChunk2 code else
  if code < 5328246 then decodeStateCodeChunk3 code else
  if code < 5890992 then decodeStateCodeChunk4 code else
  if code < 5905980 then decodeStateCodeChunk5 code else
  if code < 5907162 then decodeStateCodeChunk6 code else
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
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_15879Representative.sourceSemigroup.mul (sourceLabel state)
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
            SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_15879Representative.sourceSemigroup.mul value
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
          SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_15879Representative.sourceSemigroup.mul value
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
              SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_15879Representative.sourceSemigroup.mul value
                (generatorSourceLabel nextGenerator))
            (SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_15879Representative.sourceSemigroup.mul (sourceLabel state)
              (generatorSourceLabel generator))
      rw [inductionHypothesis]
      rw [sourceLabelTransition]

private theorem sourceFoldlGeneratorAssoc
    (left right : Fin 6)
    (word : List (Fin 3)) :
    word.foldl
        (fun value generator =>
          SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_15879Representative.sourceSemigroup.mul value
            (generatorSourceLabel generator))
        (SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_15879Representative.sourceSemigroup.mul left right) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_15879Representative.sourceSemigroup.mul left
        (word.foldl
          (fun value generator =>
            SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_15879Representative.sourceSemigroup.mul value
              (generatorSourceLabel generator))
          right) := by
  induction word generalizing right with
  | nil => rfl
  | cons generator word inductionHypothesis =>
      simp only [List.foldl_cons]
      rw [SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_15879Representative.sourceSemigroup.assoc]
      exact inductionHypothesis
        (SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_15879Representative.sourceSemigroup.mul right (generatorSourceLabel generator))

private theorem sourceLabelMapMul :
    forall (left right : Fin 225),
      sourceLabel (powerCertificate.semigroup.mul left right) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_15879Representative.sourceSemigroup.mul (sourceLabel left) (sourceLabel right) := by
  intro left right
  calc
    sourceLabel (powerCertificate.semigroup.mul left right) =
        sourceLabel
          (powerCertificate.rightMultiplyWord
            (transition left (representativeHead right))
            (representativeTail right)) := rfl
    _ = (representativeTail right).foldl
          (fun value generator =>
            SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_15879Representative.sourceSemigroup.mul value
              (generatorSourceLabel generator))
          (sourceLabel (transition left (representativeHead right))) :=
      sourceLabelRightMultiplyWord _ _
    _ = (representativeTail right).foldl
          (fun value generator =>
            SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_15879Representative.sourceSemigroup.mul value
              (generatorSourceLabel generator))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_15879Representative.sourceSemigroup.mul (sourceLabel left)
            (generatorSourceLabel (representativeHead right))) :=
      congrArg
        (fun initial =>
          (representativeTail right).foldl
            (fun value generator =>
              SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_15879Representative.sourceSemigroup.mul value
                (generatorSourceLabel generator))
            initial)
        (sourceLabelTransition left (representativeHead right))
    _ = SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_15879Representative.sourceSemigroup.mul (sourceLabel left)
          ((representativeTail right).foldl
            (fun value generator =>
              SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_15879Representative.sourceSemigroup.mul value
                (generatorSourceLabel generator))
            (generatorSourceLabel (representativeHead right))) :=
      sourceFoldlGeneratorAssoc _ _ _
    _ = SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_15879Representative.sourceSemigroup.mul (sourceLabel left) (sourceLabel right) :=
      congrArg (SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_15879Representative.sourceSemigroup.mul (sourceLabel left))
        (sourceLabelRepresentative right).symm

set_option maxHeartbeats 1000000 in
private theorem sourceLabelRightInverse :
    forall value : Fin 6, sourceLabel (sourcePreimage value) = value := by
  intro value
  apply Fin.ext
  exact by decide +revert

/-- The generated term-function semigroup maps onto the selected root. -/
def quotient : SplitSurjection powerCertificate.semigroup
    SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_15879Representative.sourceSemigroup where
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
    SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_15879Representative.law0.SatisfiedBy oppositeTable.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    oppositeTable SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_15879Representative.law0
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
    SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_15879Representative.law1.SatisfiedBy oppositeTable.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    oppositeTable SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_15879Representative.law1
    targetLaw1ToFinite targetLaw1FromFinite (by decide) (by decide)

/-- Exact finite checks that the selected target models the root basis. -/
theorem targetModels :
    Models oppositeTable.semigroup SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_15879Representative.basis := by
  unfold SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_15879Representative.basis
  exact
    FiniteNilpotentCounterexample.models_cons targetLaw0Valid <|
      FiniteNilpotentCounterexample.models_cons targetLaw1Valid <|
        FiniteNilpotentCounterexample.models_nil oppositeTable.semigroup

/-- Exact identity-theory transfer authenticated by the finite certificate. -/
theorem sameIdentityTheory :
    SameIdentityTheoryOver SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_15879Representative.sourceSemigroup
      oppositeTable.semigroup Nat := by
  intro identity
  constructor
  · intro sourceValid valuation
    exact Derives.sound targetModels
      (SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_15879Representative.basis_complete.2 identity sourceValid) valuation
  · intro targetValid
    have powerValid :=
      identity.satisfiedByPi oppositeTable.semigroup
        (Fin 9) targetValid
    have subValid :=
      powerCertificate.embedding.pullback_identity identity powerValid
    exact quotient.pushforwardIdentity identity subValid

/-- First-layer generic-CAS basis wrapper for `S6_15912`. -/
theorem representative_basis :
    BasisFor table.semigroup.opposite SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_15879Representative.basis := by
  have transferred :
      BasisFor oppositeTable.semigroup SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_15879Representative.basis :=
    (basisFor_iff_of_sameIdentityTheoryOver sameIdentityTheory).mp
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_15879Representative.basis_complete
  simpa only [oppositeTable_semigroup] using transferred


theorem opposite_basis :
    BasisFor table.semigroup (reversedBasis SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_15879Representative.basis) :=
  representative_basis.oppositeReversed

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_15912
