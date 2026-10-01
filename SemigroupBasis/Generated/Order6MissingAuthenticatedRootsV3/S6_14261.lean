import SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_13134
import SemigroupBasis.FiniteNilpotentCounterexample
import SemigroupBasis.Nonfinite
import SemigroupBasis.Opposite
import SemigroupBasis.RightGeneratedPowerCertificate

set_option maxRecDepth 2048

namespace SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_14261

open SemigroupBasis

def routeManifestRowSHA256 : String := "7a1ca1c08994cc0d59d355aa2725db73e29bfe1409f6c1fdcee5e052275d2de1"
def witnessRecordSHA256 : String := "06c69cca02c226e211a0c772144e5ec0d9187bb0044e9ddf65995a57efa37a88"
def transferComponentSHA256 : String := "06c69cca02c226e211a0c772144e5ec0d9187bb0044e9ddf65995a57efa37a88"
def powerCertificateSHA256 : String := "67fc23045ad15ca2817fadbd2989d0813867f2b8853e776eb70c566fe04c71b9"

private def row6
    (c0 c1 c2 c3 c4 c5 : Fin 6) (column : Fin 6) : Fin 6 :=
  if column = 0 then c0 else
    if column = 1 then c1 else
      if column = 2 then c2 else
        if column = 3 then c3 else
          if column = 4 then c4 else c5

/-- Exact one-based catalogue table committed by the portable witness. -/
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 2 0 4 4 right else
    if left = 1 then row6 0 0 2 1 4 4 right else
      if left = 2 then row6 0 0 2 2 4 4 right else
        if left = 3 then row6 0 1 2 3 4 4 right else
          if left = 4 then row6 4 4 4 4 4 4 right else
            row6 5 5 5 5 5 5 right

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
  "87b0cb40ee672b3b39633ff31b23192668eadc26689de855f142038787795e20"

private def packedStateVectorCodeChunk0 (index : Nat) : Nat :=
  match index with
  | 0 => 31767678361
  | 1 => 7322466102
  | 2 => 39368853828
  | 3 => 31765998744
  | 4 => 31283914608
  | 5 => 30678660576
  | 6 => 5142410064
  | 7 => 7261998624
  | 8 => 791456832
  | 9 => 26304987168
  | 10 => 65870496
  | 11 => 39368519424
  | 12 => 31282234992
  | 13 => 30676980960
  | 14 => 31282273872
  | 15 => 31223447136
  | 16 => 31283345664
  | 17 => 30677027616
  | 18 => 30557759328
  | 19 => 30678372864
  | 20 => 5140730448
  | 21 => 5081903712
  | 22 => 5141802240
  | 23 => 5081942592
  | 24 => 730990656
  | 25 => 788284224
  | 26 => 730998432
  | 27 => 791130240
  | 28 => 26303307552
  | 29 => 26184039264
  | 30 => 26304652800
  | _ => 62690112

private def packedStateVectorCodeChunk1 (index : Nat) : Nat :=
  match index with
  | 0 => 5404320
  | 1 => 65536128
  | 2 => 26304699456
  | 3 => 65543904
  | 4 => 31221767520
  | 5 => 31281666048
  | 6 => 30556079712
  | 7 => 30676693248
  | 8 => 31221806400
  | 9 => 31222879488
  | 10 => 31281712704
  | 11 => 31222887264
  | 12 => 31283065728
  | 13 => 30556118592
  | 14 => 30497293152
  | 15 => 30557471616
  | 16 => 30676739904
  | 17 => 30557479392
  | 18 => 5080224096
  | 19 => 5140122624
  | 20 => 5080262976
  | 21 => 5081336064
  | 22 => 5140169280
  | 23 => 5081343840
  | 24 => 5141522304
  | 25 => 727818048
  | 26 => 730664064
  | 27 => 786604608
  | 28 => 727779168
  | 29 => 787957632
  | 30 => 788004288
  | _ => 730671840

private def packedStateVectorCodeChunk2 (index : Nat) : Nat :=
  match index with
  | 0 => 26182359648
  | 1 => 26302973184
  | 2 => 26182398528
  | 3 => 26123573088
  | 4 => 26183751552
  | 5 => 26303019840
  | 6 => 26183759328
  | 7 => 61010496
  | 8 => 2185056
  | 9 => 62363520
  | 10 => 2223936
  | 11 => 5069952
  | 12 => 62410176
  | 13 => 5077728
  | 14 => 31221199872
  | 15 => 31221207648
  | 16 => 31281386112
  | 17 => 30495613536
  | 18 => 30555792000
  | 19 => 30555799776
  | 20 => 31221246528
  | 21 => 31222599552
  | 22 => 31281432768
  | 23 => 31222607328
  | 24 => 30495652416
  | 25 => 30497005440
  | 26 => 30555838656
  | 27 => 30497013216
  | 28 => 5079656448
  | 29 => 5079664224
  | 30 => 5139842688
  | _ => 5079703104

private def packedStateVectorCodeChunk3 (index : Nat) : Nat :=
  match index with
  | 0 => 5081056128
  | 1 => 5139889344
  | 2 => 5081063904
  | 3 => 726138432
  | 4 => 727491456
  | 5 => 727538112
  | 6 => 726099552
  | 7 => 786278016
  | 8 => 786324672
  | 9 => 727499232
  | 10 => 26121893472
  | 11 => 26182071936
  | 12 => 26182079712
  | 13 => 26121932352
  | 14 => 26123285376
  | 15 => 26182118592
  | 16 => 26123293152
  | 17 => 505440
  | 18 => 60683904
  | 19 => 544320
  | 20 => 1897344
  | 21 => 60730560
  | 22 => 1905120
  | 23 => 1944000
  | 24 => 31220919936
  | 25 => 31220927712
  | 26 => 30495325824
  | 27 => 30495333600
  | 28 => 31220966592
  | 29 => 30495372480
  | 30 => 5079376512
  | _ => 5079384288

private def packedStateVectorCodeChunk4 (index : Nat) : Nat :=
  match index with
  | 0 => 5079423168
  | 1 => 725811840
  | 2 => 725858496
  | 3 => 725819616
  | 4 => 26121605760
  | 5 => 26121613536
  | 6 => 26121652416
  | 7 => 217728
  | 8 => 225504
  | _ => 264384

private def packedStateVectorCode (state : Fin 138) : Nat :=
  if state.val < 32 then packedStateVectorCodeChunk0 state.val else
    if state.val < 64 then packedStateVectorCodeChunk1 (state.val - 32) else
      if state.val < 96 then packedStateVectorCodeChunk2 (state.val - 64) else
        if state.val < 128 then packedStateVectorCodeChunk3 (state.val - 96) else
          packedStateVectorCodeChunk4 (state.val - 128)

def stateVector (state : Fin 138)
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
      | 3 => (3 : Fin 6)
      | 4 => (3 : Fin 6)
      | 5 => (3 : Fin 6)
      | 6 => (5 : Fin 6)
      | 7 => (3 : Fin 6)
      | 8 => (1 : Fin 6)
      | 9 => (2 : Fin 6)
      | 10 => (3 : Fin 6)
      | 11 => (3 : Fin 6)
      | 12 => (2 : Fin 6)
      | _ => (2 : Fin 6)
  | 1 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (1 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (1 : Fin 6)
      | 5 => (5 : Fin 6)
      | 6 => (3 : Fin 6)
      | 7 => (3 : Fin 6)
      | 8 => (3 : Fin 6)
      | 9 => (0 : Fin 6)
      | 10 => (1 : Fin 6)
      | 11 => (2 : Fin 6)
      | 12 => (3 : Fin 6)
      | _ => (0 : Fin 6)
  | _ =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (1 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (1 : Fin 6)
      | 6 => (1 : Fin 6)
      | 7 => (1 : Fin 6)
      | 8 => (3 : Fin 6)
      | 9 => (0 : Fin 6)
      | 10 => (3 : Fin 6)
      | 11 => (0 : Fin 6)
      | 12 => (0 : Fin 6)
      | _ => (3 : Fin 6)

private def packedTransitionCodeChunk0 (index : Nat) : Nat :=
  match index with
  | 0 => 95775
  | 1 => 153324
  | 2 => 210873
  | 3 => 249231
  | 4 => 306788
  | 5 => 364337
  | 6 => 421886
  | 7 => 458045
  | 8 => 517801
  | 9 => 575350
  | 10 => 632899
  | 11 => 214348
  | 12 => 709610
  | 13 => 747977
  | 14 => 709610
  | 15 => 782914
  | 16 => 843912
  | 17 => 747977
  | 18 => 901461
  | 19 => 368646
  | 20 => 978164
  | 21 => 1012282
  | 22 => 1074108
  | 23 => 1012282
  | 24 => 1108197
  | 25 => 1170023
  | 26 => 1108197
  | 27 => 522944
  | 28 => 1246720
  | 29 => 1304304
  | 30 => 581049
  | _ => 1400219

private def packedTransitionCodeChunk1 (index : Nat) : Nat :=
  match index with
  | 0 => 1432790
  | 1 => 639154
  | 2 => 581049
  | 3 => 639154
  | 4 => 1490440
  | 5 => 1534464
  | 6 => 1572831
  | 7 => 754218
  | 8 => 1490440
  | 9 => 1624758
  | 10 => 1534464
  | 11 => 1624758
  | 12 => 850028
  | 13 => 1572831
  | 14 => 1701352
  | 15 => 907716
  | 16 => 754218
  | 17 => 907716
  | 18 => 1759000
  | 19 => 1803024
  | 20 => 1759000
  | 21 => 1835909
  | 22 => 1803024
  | 23 => 1835909
  | 24 => 1080085
  | 25 => 1912779
  | 26 => 1113347
  | 27 => 1975667
  | 28 => 1912779
  | 29 => 1176278
  | 30 => 1176278
  | _ => 1113347

private def packedTransitionCodeChunk2 (index : Nat) : Nat :=
  match index with
  | 0 => 2052402
  | 1 => 1252833
  | 2 => 2052402
  | 3 => 2104195
  | 4 => 1310559
  | 5 => 1252833
  | 6 => 1310559
  | 7 => 2186681
  | 8 => 2219155
  | 9 => 1406613
  | 10 => 2219155
  | 11 => 1439045
  | 12 => 1406613
  | 13 => 1439045
  | 14 => 2296266
  | 15 => 2296266
  | 16 => 1540304
  | 17 => 2334634
  | 18 => 1578672
  | 19 => 1578672
  | 20 => 2296266
  | 21 => 1630870
  | 22 => 1540304
  | 23 => 1630870
  | 24 => 2334634
  | 25 => 1707599
  | 26 => 1578672
  | 27 => 1707599
  | 28 => 2412473
  | 29 => 2412473
  | 30 => 1807759
  | _ => 2412473

private def packedTransitionCodeChunk3 (index : Nat) : Nat :=
  match index with
  | 0 => 1841876
  | 1 => 1807759
  | 2 => 1841876
  | 3 => 2470851
  | 4 => 1919020
  | 5 => 1919020
  | 6 => 2470851
  | 7 => 1979714
  | 8 => 1979714
  | 9 => 1919020
  | 10 => 2528545
  | 11 => 2056173
  | 12 => 2056173
  | 13 => 2528545
  | 14 => 2110430
  | 15 => 2056173
  | 16 => 2110430
  | 17 => 2586649
  | 18 => 2189901
  | 19 => 2586649
  | 20 => 2225525
  | 21 => 2189901
  | 22 => 2225525
  | 23 => 2225525
  | 24 => 2302102
  | 25 => 2302102
  | 26 => 2340467
  | 27 => 2340467
  | 28 => 2302102
  | 29 => 2340467
  | 30 => 2417198
  | _ => 2417198

private def packedTransitionCodeChunk4 (index : Nat) : Nat :=
  match index with
  | 0 => 2417198
  | 1 => 2474884
  | 2 => 2474884
  | 3 => 2474884
  | 4 => 2532296
  | 5 => 2532296
  | 6 => 2532296
  | 7 => 2589845
  | 8 => 2589845
  | _ => 2589845

private def packedTransitionCode (state : Fin 138) : Nat :=
  if state.val < 32 then packedTransitionCodeChunk0 state.val else
    if state.val < 64 then packedTransitionCodeChunk1 (state.val - 32) else
      if state.val < 96 then packedTransitionCodeChunk2 (state.val - 64) else
        if state.val < 128 then packedTransitionCodeChunk3 (state.val - 96) else
          packedTransitionCodeChunk4 (state.val - 128)

def transition (state : Fin 138)
    (generator : Fin 3) : Fin 138 :=
  ⟨(packedTransitionCode state / 138 ^ generator.val) % 138,
    Nat.mod_lt _ (by decide)⟩

private def packedRepresentativeHeadBlockCode (index : Nat) : Nat :=
  match index with
  | 0 => 1716841551197412479597788060212
  | 1 => 1526605045486101181047665482640
  | _ => 59008

def representativeHead (state : Fin 138) : Fin 3 :=
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
  | 12 => [0, 1]
  | 13 => [0, 2]
  | 14 => [1, 0]
  | 15 => [1, 1]
  | 16 => [1, 2]
  | 17 => [2, 0]
  | 18 => [2, 1]
  | 19 => [2, 2]
  | 20 => [0, 0]
  | 21 => [0, 1]
  | 22 => [0, 2]
  | 23 => [1, 0]
  | 24 => [1, 2]
  | 25 => [2, 0]
  | 26 => [2, 1]
  | 27 => [2, 2]
  | 28 => [0, 0]
  | 29 => [0, 1]
  | 30 => [0, 2]
  | _ => [1, 0]

private def representativeTailChunk1 (index : Nat) :
    List (Fin 3) :=
  match index with
  | 0 => [1, 1]
  | 1 => [1, 2]
  | 2 => [2, 0]
  | 3 => [2, 1]
  | 4 => [0, 1, 1]
  | 5 => [0, 1, 2]
  | 6 => [0, 2, 1]
  | 7 => [0, 2, 2]
  | 8 => [1, 1, 0]
  | 9 => [1, 1, 2]
  | 10 => [1, 2, 0]
  | 11 => [1, 2, 1]
  | 12 => [1, 2, 2]
  | 13 => [2, 1, 0]
  | 14 => [2, 1, 1]
  | 15 => [2, 1, 2]
  | 16 => [2, 2, 0]
  | 17 => [2, 2, 1]
  | 18 => [0, 0, 1]
  | 19 => [0, 0, 2]
  | 20 => [0, 1, 0]
  | 21 => [0, 1, 2]
  | 22 => [0, 2, 0]
  | 23 => [0, 2, 1]
  | 24 => [0, 2, 2]
  | 25 => [1, 2, 0]
  | 26 => [1, 2, 2]
  | 27 => [2, 0, 0]
  | 28 => [2, 0, 1]
  | 29 => [2, 0, 2]
  | 30 => [2, 2, 0]
  | _ => [2, 2, 1]

private def representativeTailChunk2 (index : Nat) :
    List (Fin 3) :=
  match index with
  | 0 => [0, 0, 1]
  | 1 => [0, 0, 2]
  | 2 => [0, 1, 0]
  | 3 => [0, 1, 1]
  | 4 => [0, 1, 2]
  | 5 => [0, 2, 0]
  | 6 => [0, 2, 1]
  | 7 => [1, 0, 0]
  | 8 => [1, 0, 1]
  | 9 => [1, 0, 2]
  | 10 => [1, 1, 0]
  | 11 => [1, 1, 2]
  | 12 => [1, 2, 0]
  | 13 => [1, 2, 1]
  | 14 => [0, 1, 1, 2]
  | 15 => [0, 1, 2, 1]
  | 16 => [0, 1, 2, 2]
  | 17 => [0, 2, 1, 1]
  | 18 => [0, 2, 1, 2]
  | 19 => [0, 2, 2, 1]
  | 20 => [1, 1, 2, 0]
  | 21 => [1, 1, 2, 2]
  | 22 => [1, 2, 2, 0]
  | 23 => [1, 2, 2, 1]
  | 24 => [2, 1, 1, 0]
  | 25 => [2, 1, 1, 2]
  | 26 => [2, 1, 2, 0]
  | 27 => [2, 1, 2, 1]
  | 28 => [0, 0, 1, 2]
  | 29 => [0, 0, 2, 1]
  | 30 => [0, 0, 2, 2]
  | _ => [0, 1, 2, 0]

private def representativeTailChunk3 (index : Nat) :
    List (Fin 3) :=
  match index with
  | 0 => [0, 1, 2, 2]
  | 1 => [0, 2, 2, 0]
  | 2 => [0, 2, 2, 1]
  | 3 => [1, 2, 0, 0]
  | 4 => [1, 2, 0, 2]
  | 5 => [1, 2, 2, 0]
  | 6 => [2, 0, 0, 1]
  | 7 => [2, 0, 0, 2]
  | 8 => [2, 0, 2, 0]
  | 9 => [2, 0, 2, 1]
  | 10 => [0, 0, 1, 1]
  | 11 => [0, 0, 1, 2]
  | 12 => [0, 0, 2, 1]
  | 13 => [0, 1, 1, 0]
  | 14 => [0, 1, 1, 2]
  | 15 => [0, 1, 2, 0]
  | 16 => [0, 1, 2, 1]
  | 17 => [1, 0, 0, 1]
  | 18 => [1, 0, 0, 2]
  | 19 => [1, 0, 1, 0]
  | 20 => [1, 0, 1, 2]
  | 21 => [1, 0, 2, 0]
  | 22 => [1, 0, 2, 1]
  | 23 => [1, 1, 2, 0]
  | 24 => [0, 1, 1, 2, 2]
  | 25 => [0, 1, 2, 2, 1]
  | 26 => [0, 2, 1, 1, 2]
  | 27 => [0, 2, 1, 2, 1]
  | 28 => [1, 1, 2, 2, 0]
  | 29 => [2, 1, 1, 2, 0]
  | 30 => [0, 0, 1, 2, 2]
  | _ => [0, 0, 2, 2, 1]

private def representativeTailChunk4 (index : Nat) :
    List (Fin 3) :=
  match index with
  | 0 => [0, 1, 2, 2, 0]
  | 1 => [1, 2, 0, 0, 2]
  | 2 => [1, 2, 0, 2, 0]
  | 3 => [2, 0, 0, 2, 1]
  | 4 => [0, 0, 1, 1, 2]
  | 5 => [0, 0, 1, 2, 1]
  | 6 => [0, 1, 1, 2, 0]
  | 7 => [1, 0, 0, 1, 2]
  | 8 => [1, 0, 0, 2, 1]
  | _ => [1, 0, 1, 2, 0]

def representativeTail (state : Fin 138) :
    List (Fin 3) :=
  if state.val < 32 then representativeTailChunk0 state.val else
    if state.val < 64 then representativeTailChunk1 (state.val - 32) else
      if state.val < 96 then representativeTailChunk2 (state.val - 64) else
        if state.val < 128 then representativeTailChunk3 (state.val - 96) else
          representativeTailChunk4 (state.val - 128)

private def packedSourceLabelBlockCode (index : Nat) : Nat :=
  match index with
  | 0 => 25336114695580728701580584607137492159289567991769
  | 1 => 24730609014626704026537421135922021746131369295872
  | _ => 518

def sourceLabel (state : Fin 138) : Fin 6 :=
  ⟨(packedSourceLabelBlockCode (state.val / 64) /
      6 ^ (state.val % 64)) % 6,
    Nat.mod_lt _ (by decide)⟩

def generatorSourceLabel (generator : Fin 3) : Fin 6 :=
  match generator.val with
  | 0 => (5 : Fin 6)
  | 1 => (4 : Fin 6)
  | _ => (1 : Fin 6)

def sourcePreimage (value : Fin 6) : Fin 138 :=
  match value.val with
  | 0 => (10 : Fin 138)
  | 1 => (2 : Fin 138)
  | 2 => (8 : Fin 138)
  | 3 => (6 : Fin 138)
  | 4 => (1 : Fin 138)
  | _ => (0 : Fin 138)

private def decodeStateCodeChunk0 (code : Nat) : Fin 138 :=
  if code = 217728 then (135 : Fin 138) else
  if code = 225504 then (136 : Fin 138) else
  if code = 264384 then (137 : Fin 138) else
  if code = 505440 then (113 : Fin 138) else
  if code = 544320 then (115 : Fin 138) else
  if code = 1897344 then (116 : Fin 138) else
  if code = 1905120 then (118 : Fin 138) else
  if code = 1944000 then (119 : Fin 138) else
  if code = 2185056 then (72 : Fin 138) else
  if code = 2223936 then (74 : Fin 138) else
  if code = 5069952 then (75 : Fin 138) else
  if code = 5077728 then (77 : Fin 138) else
  if code = 5404320 then (32 : Fin 138) else
  if code = 60683904 then (114 : Fin 138) else
  if code = 60730560 then (117 : Fin 138) else
  if code = 61010496 then (71 : Fin 138) else
  if code = 62363520 then (73 : Fin 138) else
  if code = 62410176 then (76 : Fin 138) else
  if code = 62690112 then (31 : Fin 138) else
  if code = 65536128 then (33 : Fin 138) else
  if code = 65543904 then (35 : Fin 138) else
  if code = 65870496 then (10 : Fin 138) else
  if code = 725811840 then (129 : Fin 138) else
  if code = 725819616 then (131 : Fin 138) else
  if code = 725858496 then (130 : Fin 138) else
  if code = 726099552 then (102 : Fin 138) else
  if code = 726138432 then (99 : Fin 138) else
  if code = 727491456 then (100 : Fin 138) else
  if code = 727499232 then (105 : Fin 138) else
  if code = 727538112 then (101 : Fin 138) else
  if code = 727779168 then (60 : Fin 138) else
  if code = 727818048 then (57 : Fin 138) else
  (0 : Fin 138)

private def decodeStateCodeChunk1 (code : Nat) : Fin 138 :=
  if code = 730664064 then (58 : Fin 138) else
  if code = 730671840 then (63 : Fin 138) else
  if code = 730990656 then (24 : Fin 138) else
  if code = 730998432 then (26 : Fin 138) else
  if code = 786278016 then (103 : Fin 138) else
  if code = 786324672 then (104 : Fin 138) else
  if code = 786604608 then (59 : Fin 138) else
  if code = 787957632 then (61 : Fin 138) else
  if code = 788004288 then (62 : Fin 138) else
  if code = 788284224 then (25 : Fin 138) else
  if code = 791130240 then (27 : Fin 138) else
  if code = 791456832 then (8 : Fin 138) else
  if code = 5079376512 then (126 : Fin 138) else
  if code = 5079384288 then (127 : Fin 138) else
  if code = 5079423168 then (128 : Fin 138) else
  if code = 5079656448 then (92 : Fin 138) else
  if code = 5079664224 then (93 : Fin 138) else
  if code = 5079703104 then (95 : Fin 138) else
  if code = 5080224096 then (50 : Fin 138) else
  if code = 5080262976 then (52 : Fin 138) else
  if code = 5081056128 then (96 : Fin 138) else
  if code = 5081063904 then (98 : Fin 138) else
  if code = 5081336064 then (53 : Fin 138) else
  if code = 5081343840 then (55 : Fin 138) else
  if code = 5081903712 then (21 : Fin 138) else
  if code = 5081942592 then (23 : Fin 138) else
  if code = 5139842688 then (94 : Fin 138) else
  if code = 5139889344 then (97 : Fin 138) else
  if code = 5140122624 then (51 : Fin 138) else
  if code = 5140169280 then (54 : Fin 138) else
  if code = 5140730448 then (20 : Fin 138) else
  if code = 5141522304 then (56 : Fin 138) else
  (0 : Fin 138)

private def decodeStateCodeChunk2 (code : Nat) : Fin 138 :=
  if code = 5141802240 then (22 : Fin 138) else
  if code = 5142410064 then (6 : Fin 138) else
  if code = 7261998624 then (7 : Fin 138) else
  if code = 7322466102 then (1 : Fin 138) else
  if code = 26121605760 then (132 : Fin 138) else
  if code = 26121613536 then (133 : Fin 138) else
  if code = 26121652416 then (134 : Fin 138) else
  if code = 26121893472 then (106 : Fin 138) else
  if code = 26121932352 then (109 : Fin 138) else
  if code = 26123285376 then (110 : Fin 138) else
  if code = 26123293152 then (112 : Fin 138) else
  if code = 26123573088 then (67 : Fin 138) else
  if code = 26182071936 then (107 : Fin 138) else
  if code = 26182079712 then (108 : Fin 138) else
  if code = 26182118592 then (111 : Fin 138) else
  if code = 26182359648 then (64 : Fin 138) else
  if code = 26182398528 then (66 : Fin 138) else
  if code = 26183751552 then (68 : Fin 138) else
  if code = 26183759328 then (70 : Fin 138) else
  if code = 26184039264 then (29 : Fin 138) else
  if code = 26302973184 then (65 : Fin 138) else
  if code = 26303019840 then (69 : Fin 138) else
  if code = 26303307552 then (28 : Fin 138) else
  if code = 26304652800 then (30 : Fin 138) else
  if code = 26304699456 then (34 : Fin 138) else
  if code = 26304987168 then (9 : Fin 138) else
  if code = 30495325824 then (122 : Fin 138) else
  if code = 30495333600 then (123 : Fin 138) else
  if code = 30495372480 then (125 : Fin 138) else
  if code = 30495613536 then (81 : Fin 138) else
  if code = 30495652416 then (88 : Fin 138) else
  if code = 30497005440 then (89 : Fin 138) else
  (0 : Fin 138)

private def decodeStateCodeChunk3 (code : Nat) : Fin 138 :=
  if code = 30497013216 then (91 : Fin 138) else
  if code = 30497293152 then (46 : Fin 138) else
  if code = 30555792000 then (82 : Fin 138) else
  if code = 30555799776 then (83 : Fin 138) else
  if code = 30555838656 then (90 : Fin 138) else
  if code = 30556079712 then (38 : Fin 138) else
  if code = 30556118592 then (45 : Fin 138) else
  if code = 30557471616 then (47 : Fin 138) else
  if code = 30557479392 then (49 : Fin 138) else
  if code = 30557759328 then (18 : Fin 138) else
  if code = 30676693248 then (39 : Fin 138) else
  if code = 30676739904 then (48 : Fin 138) else
  if code = 30676980960 then (13 : Fin 138) else
  if code = 30677027616 then (17 : Fin 138) else
  if code = 30678372864 then (19 : Fin 138) else
  if code = 30678660576 then (5 : Fin 138) else
  if code = 31220919936 then (120 : Fin 138) else
  if code = 31220927712 then (121 : Fin 138) else
  if code = 31220966592 then (124 : Fin 138) else
  if code = 31221199872 then (78 : Fin 138) else
  if code = 31221207648 then (79 : Fin 138) else
  if code = 31221246528 then (84 : Fin 138) else
  if code = 31221767520 then (36 : Fin 138) else
  if code = 31221806400 then (40 : Fin 138) else
  if code = 31222599552 then (85 : Fin 138) else
  if code = 31222607328 then (87 : Fin 138) else
  if code = 31222879488 then (41 : Fin 138) else
  if code = 31222887264 then (43 : Fin 138) else
  if code = 31223447136 then (15 : Fin 138) else
  if code = 31281386112 then (80 : Fin 138) else
  if code = 31281432768 then (86 : Fin 138) else
  if code = 31281666048 then (37 : Fin 138) else
  (0 : Fin 138)

private def decodeStateCodeChunk4 (code : Nat) : Fin 138 :=
  if code = 31281712704 then (42 : Fin 138) else
  if code = 31282234992 then (12 : Fin 138) else
  if code = 31282273872 then (14 : Fin 138) else
  if code = 31283065728 then (44 : Fin 138) else
  if code = 31283345664 then (16 : Fin 138) else
  if code = 31283914608 then (4 : Fin 138) else
  if code = 31765998744 then (3 : Fin 138) else
  if code = 31767678361 then (0 : Fin 138) else
  if code = 39368519424 then (11 : Fin 138) else
  if code = 39368853828 then (2 : Fin 138) else
  (0 : Fin 138)

private def stateVectorCode
    (vector : Fin 14 -> Fin 6) : Nat :=
  (vector (0 : Fin 14)).val + 6 * ((vector (1 : Fin 14)).val + 6 * ((vector (2 : Fin 14)).val + 6 * ((vector (3 : Fin 14)).val + 6 * ((vector (4 : Fin 14)).val + 6 * ((vector (5 : Fin 14)).val + 6 * ((vector (6 : Fin 14)).val + 6 * ((vector (7 : Fin 14)).val + 6 * ((vector (8 : Fin 14)).val + 6 * ((vector (9 : Fin 14)).val + 6 * ((vector (10 : Fin 14)).val + 6 * ((vector (11 : Fin 14)).val + 6 * ((vector (12 : Fin 14)).val + 6 * ((vector (13 : Fin 14)).val)))))))))))))

private def decodeStateCode (code : Nat) : Fin 138 :=
  if code < 730664064 then decodeStateCodeChunk0 code else
  if code < 5141802240 then decodeStateCodeChunk1 code else
  if code < 30497013216 then decodeStateCodeChunk2 code else
  if code < 31281712704 then decodeStateCodeChunk3 code else
  decodeStateCodeChunk4 code

private def decodeState
    (vector : Fin 14 -> Fin 6) : Fin 138 :=
  decodeStateCode (stateVectorCode vector)

set_option maxHeartbeats 2000000 in
private theorem decodeState_stateVector (state : Fin 138) :
    decodeState (stateVector state) = state := by
  decide +revert

set_option maxHeartbeats 2000000 in
private theorem transitionMap :
    forall (state : Fin 138)
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
    forall (state : Fin 138)
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
    (U := Fin 138)
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
    forall (state : Fin 138)
      (generator : Fin 3),
      sourceLabel (transition state generator) =
        SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_13134.sourceSemigroup.mul (sourceLabel state)
          (generatorSourceLabel generator) := by
  intro state generator
  apply Fin.ext
  exact by decide +revert

set_option maxHeartbeats 2000000 in
private theorem sourceLabelRepresentative :
    forall state : Fin 138,
      sourceLabel state =
        (representativeTail state).foldl
          (fun value generator =>
            SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_13134.sourceSemigroup.mul value
              (generatorSourceLabel generator))
          (generatorSourceLabel (representativeHead state)) := by
  intro state
  apply Fin.ext
  exact by decide +revert

private theorem sourceLabelRightMultiplyWord
    (state : Fin 138)
    (word : List (Fin 3)) :
    sourceLabel (powerCertificate.rightMultiplyWord state word) =
      word.foldl
        (fun value generator =>
          SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_13134.sourceSemigroup.mul value
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
              SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_13134.sourceSemigroup.mul value
                (generatorSourceLabel nextGenerator))
            (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_13134.sourceSemigroup.mul (sourceLabel state)
              (generatorSourceLabel generator))
      rw [inductionHypothesis]
      rw [sourceLabelTransition]

private theorem sourceFoldlGeneratorAssoc
    (left right : Fin 6)
    (word : List (Fin 3)) :
    word.foldl
        (fun value generator =>
          SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_13134.sourceSemigroup.mul value
            (generatorSourceLabel generator))
        (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_13134.sourceSemigroup.mul left right) =
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_13134.sourceSemigroup.mul left
        (word.foldl
          (fun value generator =>
            SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_13134.sourceSemigroup.mul value
              (generatorSourceLabel generator))
          right) := by
  induction word generalizing right with
  | nil => rfl
  | cons generator word inductionHypothesis =>
      simp only [List.foldl_cons]
      rw [SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_13134.sourceSemigroup.assoc]
      exact inductionHypothesis
        (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_13134.sourceSemigroup.mul right (generatorSourceLabel generator))

private theorem sourceLabelMapMul :
    forall (left right : Fin 138),
      sourceLabel (powerCertificate.semigroup.mul left right) =
        SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_13134.sourceSemigroup.mul (sourceLabel left) (sourceLabel right) := by
  intro left right
  calc
    sourceLabel (powerCertificate.semigroup.mul left right) =
        sourceLabel
          (powerCertificate.rightMultiplyWord
            (transition left (representativeHead right))
            (representativeTail right)) := rfl
    _ = (representativeTail right).foldl
          (fun value generator =>
            SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_13134.sourceSemigroup.mul value
              (generatorSourceLabel generator))
          (sourceLabel (transition left (representativeHead right))) :=
      sourceLabelRightMultiplyWord _ _
    _ = (representativeTail right).foldl
          (fun value generator =>
            SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_13134.sourceSemigroup.mul value
              (generatorSourceLabel generator))
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_13134.sourceSemigroup.mul (sourceLabel left)
            (generatorSourceLabel (representativeHead right))) :=
      congrArg
        (fun initial =>
          (representativeTail right).foldl
            (fun value generator =>
              SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_13134.sourceSemigroup.mul value
                (generatorSourceLabel generator))
            initial)
        (sourceLabelTransition left (representativeHead right))
    _ = SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_13134.sourceSemigroup.mul (sourceLabel left)
          ((representativeTail right).foldl
            (fun value generator =>
              SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_13134.sourceSemigroup.mul value
                (generatorSourceLabel generator))
            (generatorSourceLabel (representativeHead right))) :=
      sourceFoldlGeneratorAssoc _ _ _
    _ = SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_13134.sourceSemigroup.mul (sourceLabel left) (sourceLabel right) :=
      congrArg (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_13134.sourceSemigroup.mul (sourceLabel left))
        (sourceLabelRepresentative right).symm

set_option maxHeartbeats 1000000 in
private theorem sourceLabelRightInverse :
    forall value : Fin 6, sourceLabel (sourcePreimage value) = value := by
  intro value
  apply Fin.ext
  exact by decide +revert

/-- The generated term-function semigroup maps onto the selected root. -/
def quotient : SplitSurjection powerCertificate.semigroup
    SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_13134.sourceSemigroup where
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
    SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_13134.law0.SatisfiedBy oppositeTable.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    oppositeTable SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_13134.law0
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
    SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_13134.law1.SatisfiedBy oppositeTable.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    oppositeTable SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_13134.law1
    targetLaw1ToFinite targetLaw1FromFinite (by decide) (by decide)

private def targetLaw2ToFinite : Nat -> Fin 2
  | 0 => (0 : Fin 2)
  | 1 => (1 : Fin 2)
  | _ => (0 : Fin 2)

private def targetLaw2FromFinite (index : Fin 2) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
private theorem targetLaw2Valid :
    SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_13134.law2.SatisfiedBy oppositeTable.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    oppositeTable SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_13134.law2
    targetLaw2ToFinite targetLaw2FromFinite (by decide) (by decide)

private def targetLaw3ToFinite : Nat -> Fin 2
  | 0 => (0 : Fin 2)
  | 1 => (1 : Fin 2)
  | _ => (0 : Fin 2)

private def targetLaw3FromFinite (index : Fin 2) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
private theorem targetLaw3Valid :
    SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_13134.law3.SatisfiedBy oppositeTable.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    oppositeTable SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_13134.law3
    targetLaw3ToFinite targetLaw3FromFinite (by decide) (by decide)

private def targetLaw4ToFinite : Nat -> Fin 3
  | 0 => (0 : Fin 3)
  | 1 => (1 : Fin 3)
  | 2 => (2 : Fin 3)
  | _ => (0 : Fin 3)

private def targetLaw4FromFinite (index : Fin 3) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
private theorem targetLaw4Valid :
    SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_13134.law4.SatisfiedBy oppositeTable.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    oppositeTable SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_13134.law4
    targetLaw4ToFinite targetLaw4FromFinite (by decide) (by decide)

/-- Exact finite checks that the selected target models the root basis. -/
theorem targetModels :
    Models oppositeTable.semigroup SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_13134.basis := by
  unfold SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_13134.basis
  exact
    FiniteNilpotentCounterexample.models_cons targetLaw0Valid <|
      FiniteNilpotentCounterexample.models_cons targetLaw1Valid <|
        FiniteNilpotentCounterexample.models_cons targetLaw2Valid <|
          FiniteNilpotentCounterexample.models_cons targetLaw3Valid <|
            FiniteNilpotentCounterexample.models_cons targetLaw4Valid <|
              FiniteNilpotentCounterexample.models_nil oppositeTable.semigroup

/-- Exact identity-theory transfer authenticated by the finite certificate. -/
theorem sameIdentityTheory :
    SameIdentityTheoryOver SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_13134.sourceSemigroup
      oppositeTable.semigroup Nat := by
  intro identity
  constructor
  · intro sourceValid valuation
    exact Derives.sound targetModels
      (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_13134.basis_complete.2 identity sourceValid) valuation
  · intro targetValid
    have powerValid :=
      identity.satisfiedByPi oppositeTable.semigroup
        (Fin 14) targetValid
    have subValid :=
      powerCertificate.embedding.pullback_identity identity powerValid
    exact quotient.pushforwardIdentity identity subValid

/-- First-layer generic-CAS basis wrapper for `S6_14261`. -/
theorem representative_basis :
    BasisFor table.semigroup.opposite SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_13134.basis := by
  have transferred :
      BasisFor oppositeTable.semigroup SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_13134.basis :=
    (basisFor_iff_of_sameIdentityTheoryOver sameIdentityTheory).mp
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_13134.basis_complete
  simpa only [oppositeTable_semigroup] using transferred


theorem opposite_basis :
    BasisFor table.semigroup (reversedBasis SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_13134.basis) :=
  representative_basis.oppositeReversed

end SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_14261
