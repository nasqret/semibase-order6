import SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_3750Representative
import SemigroupBasis.FiniteNilpotentCounterexample
import SemigroupBasis.Nonfinite
import SemigroupBasis.Opposite
import SemigroupBasis.RightGeneratedPowerCertificate

set_option maxRecDepth 2048

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_8539

open SemigroupBasis

def routeManifestRowSHA256 : String := "dea805789490abb1c0481fe11ea7d6fb20c170d460904771315bbdf1dab1715d"
def witnessRecordSHA256 : String := "15ffba84b49a3369c3e35d1b9e37933c73f1bdeaf67670cf0fe99b5d4effa6a3"
def transferComponentSHA256 : String := "15ffba84b49a3369c3e35d1b9e37933c73f1bdeaf67670cf0fe99b5d4effa6a3"
def powerCertificateSHA256 : String := "83493ac1297d8432d4c4be3f01324fdc5af893cc37c7450a8e99997ec6fcae10"

private def row6
    (c0 c1 c2 c3 c4 c5 : Fin 6) (column : Fin 6) : Fin 6 :=
  if column = 0 then c0 else
    if column = 1 then c1 else
      if column = 2 then c2 else
        if column = 3 then c3 else
          if column = 4 then c4 else c5

/-- Exact one-based catalogue table committed by the portable witness. -/
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 0 0 0 0 right else
    if left = 1 then row6 0 0 0 1 1 1 right else
      if left = 2 then row6 0 0 0 1 2 1 right else
        if left = 3 then row6 0 1 1 3 3 3 right else
          if left = 4 then row6 0 1 1 3 4 3 right else
            row6 0 1 2 3 3 5 right

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
  "0fc40f8d6b087d74e6afc486aa633ff7105af778121f3b407f00bb1eec6985ae"

private def packedStateVectorCodeChunk0 (index : Nat) : Nat :=
  match index with
  | 0 => 253415525336713
  | 1 => 499218357838470
  | 2 => 587946368480004
  | 3 => 16441547345352
  | 4 => 139917486259008
  | 5 => 229583747279808
  | 6 => 227359244200752
  | 7 => 493549892341344
  | 8 => 358924735627488
  | 9 => 144561158449632
  | 10 => 362152841406048
  | 11 => 586844916058080
  | 12 => 4503827740896
  | 13 => 9536791530240
  | 14 => 4490765365968
  | 15 => 137070191135520
  | 16 => 121871960131104
  | 17 => 9066606265728
  | 18 => 122355203850144
  | 19 => 228562835804352
  | 20 => 7311935739600
  | 21 => 120143521613088
  | 22 => 223431965508384
  | 23 => 221703841078560
  | 24 => 356090440734432
  | 25 => 121950735521184
  | 26 => 356012076290400
  | 27 => 358295644972512
  | 28 => 9147147212160
  | 29 => 138813845014944
  | 30 => 127002869050464
  | _ => 124695597580704

private def packedStateVectorCodeChunk1 (index : Nat) : Nat :=
  match index with
  | 0 => 356484438057312
  | 1 => 358295582826720
  | 2 => 143929891292256
  | 3 => 361129753428192
  | 4 => 1656532617408
  | 5 => 3384961057728
  | 6 => 3868204776768
  | 7 => 8515880054784
  | 8 => 3384959378112
  | 9 => 119037725704224
  | 10 => 3384959098176
  | 11 => 119037725424288
  | 12 => 121321233640224
  | 13 => 3398019792192
  | 14 => 119507910408864
  | 15 => 121321231960608
  | 16 => 121334292654624
  | 17 => 3385019844288
  | 18 => 119037715626528
  | 19 => 3385019564352
  | 20 => 119037715346592
  | 21 => 222881239017504
  | 22 => 220597672294944
  | 23 => 119116442307744
  | 24 => 355461350079456
  | 25 => 3463383728448
  | 26 => 121321282349088
  | 27 => 119038078143648
  | 28 => 121321645146144
  | 29 => 3400196574528
  | 30 => 3387135880512
  | _ => 135966551573664

private def packedStateVectorCodeChunk2 (index : Nat) : Nat :=
  match index with
  | 0 => 121321221882912
  | 1 => 121334282576928
  | 2 => 6208245787968
  | 3 => 119039892128928
  | 4 => 119040254925984
  | 5 => 121321584679968
  | 6 => 138260942021664
  | 7 => 124142694587424
  | 8 => 550726630848
  | 9 => 550726350912
  | 10 => 2834234566848
  | 11 => 1020911335488
  | 12 => 2834232887232
  | 13 => 2847293581248
  | 14 => 118486999213344
  | 15 => 2834293353408
  | 16 => 118486989135648
  | 17 => 220046945804064
  | 18 => 629090515008
  | 19 => 118487351932704
  | 20 => 552903133248
  | 21 => 135413648580384
  | 22 => 5655342794688
  | _ => 139968

private def packedStateVectorCode (state : Fin 88) : Nat :=
  if state.val < 32 then packedStateVectorCodeChunk0 state.val else
    if state.val < 64 then packedStateVectorCodeChunk1 (state.val - 32) else
      packedStateVectorCodeChunk2 (state.val - 64)

def stateVector (state : Fin 88)
    (coordinate : Fin 19) : Fin 6 :=
  ⟨(packedStateVectorCode state / 6 ^ coordinate.val) % 6,
    Nat.mod_lt _ (by decide)⟩

def generatorVector (generator : Fin 3)
    (coordinate : Fin 19) : Fin 6 :=
  match generator.val with
  | 0 =>
      match coordinate.val with
      | 0 => (1 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (3 : Fin 6)
      | 4 => (4 : Fin 6)
      | 5 => (2 : Fin 6)
      | 6 => (4 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (2 : Fin 6)
      | 10 => (5 : Fin 6)
      | 11 => (2 : Fin 6)
      | 12 => (5 : Fin 6)
      | 13 => (4 : Fin 6)
      | 14 => (5 : Fin 6)
      | 15 => (4 : Fin 6)
      | 16 => (5 : Fin 6)
      | 17 => (2 : Fin 6)
      | _ => (2 : Fin 6)
  | 1 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (1 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (2 : Fin 6)
      | 5 => (3 : Fin 6)
      | 6 => (5 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (2 : Fin 6)
      | 9 => (5 : Fin 6)
      | 10 => (2 : Fin 6)
      | 11 => (4 : Fin 6)
      | 12 => (5 : Fin 6)
      | 13 => (2 : Fin 6)
      | 14 => (4 : Fin 6)
      | 15 => (5 : Fin 6)
      | 16 => (2 : Fin 6)
      | 17 => (5 : Fin 6)
      | _ => (4 : Fin 6)
  | _ =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (1 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (5 : Fin 6)
      | 6 => (4 : Fin 6)
      | 7 => (2 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (5 : Fin 6)
      | 10 => (5 : Fin 6)
      | 11 => (4 : Fin 6)
      | 12 => (2 : Fin 6)
      | 13 => (4 : Fin 6)
      | 14 => (2 : Fin 6)
      | 15 => (2 : Fin 6)
      | 16 => (4 : Fin 6)
      | 17 => (4 : Fin 6)
      | _ => (5 : Fin 6)

private def packedTransitionCodeChunk0 (index : Nat) : Nat :=
  match index with
  | 0 => 39075
  | 1 => 62574
  | 2 => 86073
  | 3 => 101731
  | 4 => 125238
  | 5 => 148737
  | 6 => 172236
  | 7 => 186495
  | 8 => 211401
  | 9 => 234900
  | 10 => 258399
  | 11 => 88298
  | 12 => 289710
  | 13 => 305377
  | 14 => 312942
  | 15 => 318860
  | 16 => 344562
  | 17 => 305993
  | 18 => 368058
  | 19 => 151399
  | 20 => 382644
  | 21 => 389084
  | 22 => 415059
  | 23 => 420060
  | 24 => 436007
  | 25 => 453785
  | 26 => 436011
  | 27 => 214076
  | 28 => 307412
  | 29 => 501222
  | 30 => 238079
  | _ => 501578

private def packedTransitionCodeChunk1 (index : Nat) : Nat :=
  match index with
  | 0 => 436548
  | 1 => 260549
  | 2 => 238519
  | 3 => 260551
  | 4 => 560772
  | 5 => 579522
  | 6 => 595186
  | 7 => 308831
  | 8 => 595010
  | 9 => 607889
  | 10 => 595010
  | 11 => 607889
  | 12 => 347676
  | 13 => 595010
  | 14 => 608153
  | 15 => 370908
  | 16 => 370908
  | 17 => 618251
  | 18 => 624169
  | 19 => 618251
  | 20 => 624169
  | 21 => 417551
  | 22 => 631913
  | 23 => 624178
  | 24 => 438675
  | 25 => 618257
  | 26 => 456271
  | 27 => 624169
  | 28 => 456271
  | 29 => 595998
  | 30 => 595998
  | _ => 625148

private def packedTransitionCodeChunk2 (index : Nat) : Nat :=
  match index with
  | 0 => 502732
  | 1 => 502732
  | 2 => 596002
  | 3 => 625500
  | 4 => 625500
  | 5 => 502732
  | 6 => 503172
  | 7 => 502742
  | 8 => 680225
  | 9 => 680225
  | 10 => 580788
  | 11 => 680401
  | 12 => 596276
  | 13 => 596276
  | 14 => 610983
  | 15 => 619511
  | 16 => 626647
  | 17 => 634391
  | 18 => 680234
  | 19 => 626647
  | 20 => 681204
  | 21 => 627087
  | 22 => 596286
  | _ => 681471

private def packedTransitionCode (state : Fin 88) : Nat :=
  if state.val < 32 then packedTransitionCodeChunk0 state.val else
    if state.val < 64 then packedTransitionCodeChunk1 (state.val - 32) else
      packedTransitionCodeChunk2 (state.val - 64)

def transition (state : Fin 88)
    (generator : Fin 3) : Fin 88 :=
  ⟨(packedTransitionCode state / 88 ^ generator.val) % 88,
    Nat.mod_lt _ (by decide)⟩

private def packedRepresentativeHeadBlockCode (index : Nat) : Nat :=
  match index with
  | 0 => 3370096963230173647272800545134
  | _ => 92392618733

def representativeHead (state : Fin 88) : Fin 3 :=
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
  | 8 => [1, 0, 2]
  | 9 => [1, 1, 2]
  | 10 => [1, 2, 0]
  | 11 => [1, 2, 1]
  | 12 => [1, 2, 2]
  | 13 => [2, 0, 1]
  | 14 => [2, 1, 1]
  | 15 => [2, 1, 2]
  | 16 => [2, 2, 1]
  | 17 => [0, 0, 2]
  | 18 => [0, 1, 2]
  | 19 => [0, 2, 0]
  | 20 => [0, 2, 1]
  | 21 => [0, 2, 2]
  | 22 => [1, 0, 2]
  | 23 => [1, 2, 0]
  | 24 => [1, 2, 2]
  | 25 => [2, 0, 0]
  | 26 => [2, 0, 2]
  | 27 => [2, 1, 0]
  | 28 => [2, 2, 0]
  | 29 => [0, 0, 1]
  | 30 => [0, 1, 0]
  | _ => [0, 1, 1]

private def representativeTailChunk2 (index : Nat) :
    List (Fin 3) :=
  match index with
  | 0 => [0, 1, 2]
  | 1 => [0, 2, 1]
  | 2 => [1, 0, 0]
  | 3 => [1, 0, 1]
  | 4 => [1, 1, 0]
  | 5 => [1, 2, 0]
  | 6 => [2, 0, 1]
  | 7 => [2, 1, 0]
  | 8 => [0, 1, 1, 2]
  | 9 => [0, 1, 2, 1]
  | 10 => [0, 1, 2, 2]
  | 11 => [0, 2, 1, 1]
  | 12 => [0, 2, 1, 2]
  | 13 => [0, 2, 2, 1]
  | 14 => [1, 1, 2, 2]
  | 15 => [0, 0, 2, 2]
  | 16 => [0, 1, 2, 2]
  | 17 => [1, 0, 2, 2]
  | 18 => [1, 2, 0, 0]
  | 19 => [1, 2, 2, 0]
  | 20 => [0, 0, 1, 1]
  | 21 => [2, 0, 1, 1]
  | 22 => [2, 1, 0, 0]
  | _ => [0, 1, 1, 2, 2]

def representativeTail (state : Fin 88) :
    List (Fin 3) :=
  if state.val < 32 then representativeTailChunk0 state.val else
    if state.val < 64 then representativeTailChunk1 (state.val - 32) else
      representativeTailChunk2 (state.val - 64)

private def packedSourceLabelBlockCode (index : Nat) : Nat :=
  match index with
  | 0 => 465104445803884394831536450617101010783579425
  | _ => 203119913336832

def sourceLabel (state : Fin 88) : Fin 6 :=
  ⟨(packedSourceLabelBlockCode (state.val / 64) /
      6 ^ (state.val % 64)) % 6,
    Nat.mod_lt _ (by decide)⟩

def generatorSourceLabel (generator : Fin 3) : Fin 6 :=
  match generator.val with
  | 0 => (5 : Fin 6)
  | 1 => (4 : Fin 6)
  | _ => (3 : Fin 6)

def sourcePreimage (value : Fin 6) : Fin 88 :=
  match value.val with
  | 0 => (4 : Fin 88)
  | 1 => (5 : Fin 88)
  | 2 => (8 : Fin 88)
  | 3 => (2 : Fin 88)
  | 4 => (1 : Fin 88)
  | _ => (0 : Fin 88)

private def decodeStateCodeChunk0 (code : Nat) : Fin 88 :=
  if code = 139968 then (87 : Fin 88) else
  if code = 550726350912 then (73 : Fin 88) else
  if code = 550726630848 then (72 : Fin 88) else
  if code = 552903133248 then (84 : Fin 88) else
  if code = 629090515008 then (82 : Fin 88) else
  if code = 1020911335488 then (75 : Fin 88) else
  if code = 1656532617408 then (36 : Fin 88) else
  if code = 2834232887232 then (76 : Fin 88) else
  if code = 2834234566848 then (74 : Fin 88) else
  if code = 2834293353408 then (79 : Fin 88) else
  if code = 2847293581248 then (77 : Fin 88) else
  if code = 3384959098176 then (42 : Fin 88) else
  if code = 3384959378112 then (40 : Fin 88) else
  if code = 3384961057728 then (37 : Fin 88) else
  if code = 3385019564352 then (51 : Fin 88) else
  if code = 3385019844288 then (49 : Fin 88) else
  if code = 3387135880512 then (62 : Fin 88) else
  if code = 3398019792192 then (45 : Fin 88) else
  if code = 3400196574528 then (61 : Fin 88) else
  if code = 3463383728448 then (57 : Fin 88) else
  if code = 3868204776768 then (38 : Fin 88) else
  if code = 4490765365968 then (14 : Fin 88) else
  if code = 4503827740896 then (12 : Fin 88) else
  if code = 5655342794688 then (86 : Fin 88) else
  if code = 6208245787968 then (66 : Fin 88) else
  if code = 7311935739600 then (20 : Fin 88) else
  if code = 8515880054784 then (39 : Fin 88) else
  if code = 9066606265728 then (17 : Fin 88) else
  if code = 9147147212160 then (28 : Fin 88) else
  if code = 9536791530240 then (13 : Fin 88) else
  if code = 16441547345352 then (3 : Fin 88) else
  if code = 118486989135648 then (80 : Fin 88) else
  (0 : Fin 88)

private def decodeStateCodeChunk1 (code : Nat) : Fin 88 :=
  if code = 118486999213344 then (78 : Fin 88) else
  if code = 118487351932704 then (83 : Fin 88) else
  if code = 119037715346592 then (52 : Fin 88) else
  if code = 119037715626528 then (50 : Fin 88) else
  if code = 119037725424288 then (43 : Fin 88) else
  if code = 119037725704224 then (41 : Fin 88) else
  if code = 119038078143648 then (59 : Fin 88) else
  if code = 119039892128928 then (67 : Fin 88) else
  if code = 119040254925984 then (68 : Fin 88) else
  if code = 119116442307744 then (55 : Fin 88) else
  if code = 119507910408864 then (46 : Fin 88) else
  if code = 120143521613088 then (21 : Fin 88) else
  if code = 121321221882912 then (64 : Fin 88) else
  if code = 121321231960608 then (47 : Fin 88) else
  if code = 121321233640224 then (44 : Fin 88) else
  if code = 121321282349088 then (58 : Fin 88) else
  if code = 121321584679968 then (69 : Fin 88) else
  if code = 121321645146144 then (60 : Fin 88) else
  if code = 121334282576928 then (65 : Fin 88) else
  if code = 121334292654624 then (48 : Fin 88) else
  if code = 121871960131104 then (16 : Fin 88) else
  if code = 121950735521184 then (25 : Fin 88) else
  if code = 122355203850144 then (18 : Fin 88) else
  if code = 124142694587424 then (71 : Fin 88) else
  if code = 124695597580704 then (31 : Fin 88) else
  if code = 127002869050464 then (30 : Fin 88) else
  if code = 135413648580384 then (85 : Fin 88) else
  if code = 135966551573664 then (63 : Fin 88) else
  if code = 137070191135520 then (15 : Fin 88) else
  if code = 138260942021664 then (70 : Fin 88) else
  if code = 138813845014944 then (29 : Fin 88) else
  if code = 139917486259008 then (4 : Fin 88) else
  (0 : Fin 88)

private def decodeStateCodeChunk2 (code : Nat) : Fin 88 :=
  if code = 143929891292256 then (34 : Fin 88) else
  if code = 144561158449632 then (9 : Fin 88) else
  if code = 220046945804064 then (81 : Fin 88) else
  if code = 220597672294944 then (54 : Fin 88) else
  if code = 221703841078560 then (23 : Fin 88) else
  if code = 222881239017504 then (53 : Fin 88) else
  if code = 223431965508384 then (22 : Fin 88) else
  if code = 227359244200752 then (6 : Fin 88) else
  if code = 228562835804352 then (19 : Fin 88) else
  if code = 229583747279808 then (5 : Fin 88) else
  if code = 253415525336713 then (0 : Fin 88) else
  if code = 355461350079456 then (56 : Fin 88) else
  if code = 356012076290400 then (26 : Fin 88) else
  if code = 356090440734432 then (24 : Fin 88) else
  if code = 356484438057312 then (32 : Fin 88) else
  if code = 358295582826720 then (33 : Fin 88) else
  if code = 358295644972512 then (27 : Fin 88) else
  if code = 358924735627488 then (8 : Fin 88) else
  if code = 361129753428192 then (35 : Fin 88) else
  if code = 362152841406048 then (10 : Fin 88) else
  if code = 493549892341344 then (7 : Fin 88) else
  if code = 499218357838470 then (1 : Fin 88) else
  if code = 586844916058080 then (11 : Fin 88) else
  if code = 587946368480004 then (2 : Fin 88) else
  (0 : Fin 88)

private def stateVectorCode
    (vector : Fin 19 -> Fin 6) : Nat :=
  (vector (0 : Fin 19)).val + 6 * ((vector (1 : Fin 19)).val + 6 * ((vector (2 : Fin 19)).val + 6 * ((vector (3 : Fin 19)).val + 6 * ((vector (4 : Fin 19)).val + 6 * ((vector (5 : Fin 19)).val + 6 * ((vector (6 : Fin 19)).val + 6 * ((vector (7 : Fin 19)).val + 6 * ((vector (8 : Fin 19)).val + 6 * ((vector (9 : Fin 19)).val + 6 * ((vector (10 : Fin 19)).val + 6 * ((vector (11 : Fin 19)).val + 6 * ((vector (12 : Fin 19)).val + 6 * ((vector (13 : Fin 19)).val + 6 * ((vector (14 : Fin 19)).val + 6 * ((vector (15 : Fin 19)).val + 6 * ((vector (16 : Fin 19)).val + 6 * ((vector (17 : Fin 19)).val + 6 * ((vector (18 : Fin 19)).val))))))))))))))))))

private def decodeStateCode (code : Nat) : Fin 88 :=
  if code < 118486999213344 then decodeStateCodeChunk0 code else
  if code < 143929891292256 then decodeStateCodeChunk1 code else
  decodeStateCodeChunk2 code

private def decodeState
    (vector : Fin 19 -> Fin 6) : Fin 88 :=
  decodeStateCode (stateVectorCode vector)

set_option maxHeartbeats 2000000 in
private theorem decodeState_stateVector (state : Fin 88) :
    decodeState (stateVector state) = state := by
  decide +revert

set_option maxHeartbeats 2000000 in
private theorem transitionMap :
    forall (state : Fin 88)
      (generator : Fin 3)
      (coordinate : Fin 19),
      stateVector (transition state generator) coordinate =
        oppositeTable.semigroup.mul (stateVector state coordinate)
          (generatorVector generator coordinate) := by
  intro state generator coordinate
  apply Fin.ext
  exact by decide +revert

set_option maxHeartbeats 2000000 in
private theorem representativeMap :
    forall (state : Fin 88)
      (coordinate : Fin 19),
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
    (U := Fin 88)
    (G := Fin 3)
    (I := Fin 19) oppositeTable.semigroup where
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
    forall (state : Fin 88)
      (generator : Fin 3),
      sourceLabel (transition state generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_3750Representative.sourceSemigroup.mul (sourceLabel state)
          (generatorSourceLabel generator) := by
  intro state generator
  apply Fin.ext
  exact by decide +revert

set_option maxHeartbeats 2000000 in
private theorem sourceLabelRepresentative :
    forall state : Fin 88,
      sourceLabel state =
        (representativeTail state).foldl
          (fun value generator =>
            SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_3750Representative.sourceSemigroup.mul value
              (generatorSourceLabel generator))
          (generatorSourceLabel (representativeHead state)) := by
  intro state
  apply Fin.ext
  exact by decide +revert

private theorem sourceLabelRightMultiplyWord
    (state : Fin 88)
    (word : List (Fin 3)) :
    sourceLabel (powerCertificate.rightMultiplyWord state word) =
      word.foldl
        (fun value generator =>
          SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_3750Representative.sourceSemigroup.mul value
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
              SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_3750Representative.sourceSemigroup.mul value
                (generatorSourceLabel nextGenerator))
            (SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_3750Representative.sourceSemigroup.mul (sourceLabel state)
              (generatorSourceLabel generator))
      rw [inductionHypothesis]
      rw [sourceLabelTransition]

private theorem sourceFoldlGeneratorAssoc
    (left right : Fin 6)
    (word : List (Fin 3)) :
    word.foldl
        (fun value generator =>
          SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_3750Representative.sourceSemigroup.mul value
            (generatorSourceLabel generator))
        (SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_3750Representative.sourceSemigroup.mul left right) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_3750Representative.sourceSemigroup.mul left
        (word.foldl
          (fun value generator =>
            SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_3750Representative.sourceSemigroup.mul value
              (generatorSourceLabel generator))
          right) := by
  induction word generalizing right with
  | nil => rfl
  | cons generator word inductionHypothesis =>
      simp only [List.foldl_cons]
      rw [SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_3750Representative.sourceSemigroup.assoc]
      exact inductionHypothesis
        (SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_3750Representative.sourceSemigroup.mul right (generatorSourceLabel generator))

private theorem sourceLabelMapMul :
    forall (left right : Fin 88),
      sourceLabel (powerCertificate.semigroup.mul left right) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_3750Representative.sourceSemigroup.mul (sourceLabel left) (sourceLabel right) := by
  intro left right
  calc
    sourceLabel (powerCertificate.semigroup.mul left right) =
        sourceLabel
          (powerCertificate.rightMultiplyWord
            (transition left (representativeHead right))
            (representativeTail right)) := rfl
    _ = (representativeTail right).foldl
          (fun value generator =>
            SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_3750Representative.sourceSemigroup.mul value
              (generatorSourceLabel generator))
          (sourceLabel (transition left (representativeHead right))) :=
      sourceLabelRightMultiplyWord _ _
    _ = (representativeTail right).foldl
          (fun value generator =>
            SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_3750Representative.sourceSemigroup.mul value
              (generatorSourceLabel generator))
          (SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_3750Representative.sourceSemigroup.mul (sourceLabel left)
            (generatorSourceLabel (representativeHead right))) :=
      congrArg
        (fun initial =>
          (representativeTail right).foldl
            (fun value generator =>
              SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_3750Representative.sourceSemigroup.mul value
                (generatorSourceLabel generator))
            initial)
        (sourceLabelTransition left (representativeHead right))
    _ = SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_3750Representative.sourceSemigroup.mul (sourceLabel left)
          ((representativeTail right).foldl
            (fun value generator =>
              SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_3750Representative.sourceSemigroup.mul value
                (generatorSourceLabel generator))
            (generatorSourceLabel (representativeHead right))) :=
      sourceFoldlGeneratorAssoc _ _ _
    _ = SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_3750Representative.sourceSemigroup.mul (sourceLabel left) (sourceLabel right) :=
      congrArg (SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_3750Representative.sourceSemigroup.mul (sourceLabel left))
        (sourceLabelRepresentative right).symm

set_option maxHeartbeats 1000000 in
private theorem sourceLabelRightInverse :
    forall value : Fin 6, sourceLabel (sourcePreimage value) = value := by
  intro value
  apply Fin.ext
  exact by decide +revert

/-- The generated term-function semigroup maps onto the selected root. -/
def quotient : SplitSurjection powerCertificate.semigroup
    SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_3750Representative.sourceSemigroup where
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
    SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_3750Representative.law0.SatisfiedBy oppositeTable.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    oppositeTable SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_3750Representative.law0
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
    SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_3750Representative.law1.SatisfiedBy oppositeTable.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    oppositeTable SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_3750Representative.law1
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
    SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_3750Representative.law2.SatisfiedBy oppositeTable.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    oppositeTable SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_3750Representative.law2
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
    SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_3750Representative.law3.SatisfiedBy oppositeTable.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    oppositeTable SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_3750Representative.law3
    targetLaw3ToFinite targetLaw3FromFinite (by decide) (by decide)

private def targetLaw4ToFinite : Nat -> Fin 2
  | 0 => (0 : Fin 2)
  | 1 => (1 : Fin 2)
  | _ => (0 : Fin 2)

private def targetLaw4FromFinite (index : Fin 2) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
private theorem targetLaw4Valid :
    SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_3750Representative.law4.SatisfiedBy oppositeTable.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    oppositeTable SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_3750Representative.law4
    targetLaw4ToFinite targetLaw4FromFinite (by decide) (by decide)

private def targetLaw5ToFinite : Nat -> Fin 2
  | 0 => (0 : Fin 2)
  | 1 => (1 : Fin 2)
  | _ => (0 : Fin 2)

private def targetLaw5FromFinite (index : Fin 2) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
private theorem targetLaw5Valid :
    SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_3750Representative.law5.SatisfiedBy oppositeTable.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    oppositeTable SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_3750Representative.law5
    targetLaw5ToFinite targetLaw5FromFinite (by decide) (by decide)

private def targetLaw6ToFinite : Nat -> Fin 3
  | 0 => (0 : Fin 3)
  | 1 => (1 : Fin 3)
  | 2 => (2 : Fin 3)
  | _ => (0 : Fin 3)

private def targetLaw6FromFinite (index : Fin 3) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
private theorem targetLaw6Valid :
    SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_3750Representative.law6.SatisfiedBy oppositeTable.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    oppositeTable SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_3750Representative.law6
    targetLaw6ToFinite targetLaw6FromFinite (by decide) (by decide)

/-- Exact finite checks that the selected target models the root basis. -/
theorem targetModels :
    Models oppositeTable.semigroup SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_3750Representative.basis := by
  unfold SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_3750Representative.basis
  exact
    FiniteNilpotentCounterexample.models_cons targetLaw0Valid <|
      FiniteNilpotentCounterexample.models_cons targetLaw1Valid <|
        FiniteNilpotentCounterexample.models_cons targetLaw2Valid <|
          FiniteNilpotentCounterexample.models_cons targetLaw3Valid <|
            FiniteNilpotentCounterexample.models_cons targetLaw4Valid <|
              FiniteNilpotentCounterexample.models_cons targetLaw5Valid <|
                FiniteNilpotentCounterexample.models_cons targetLaw6Valid <|
                  FiniteNilpotentCounterexample.models_nil oppositeTable.semigroup

/-- Exact identity-theory transfer authenticated by the finite certificate. -/
theorem sameIdentityTheory :
    SameIdentityTheoryOver SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_3750Representative.sourceSemigroup
      oppositeTable.semigroup Nat := by
  intro identity
  constructor
  · intro sourceValid valuation
    exact Derives.sound targetModels
      (SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_3750Representative.basis_complete.2 identity sourceValid) valuation
  · intro targetValid
    have powerValid :=
      identity.satisfiedByPi oppositeTable.semigroup
        (Fin 19) targetValid
    have subValid :=
      powerCertificate.embedding.pullback_identity identity powerValid
    exact quotient.pushforwardIdentity identity subValid

/-- First-layer generic-CAS basis wrapper for `S6_8539`. -/
theorem representative_basis :
    BasisFor table.semigroup.opposite SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_3750Representative.basis := by
  have transferred :
      BasisFor oppositeTable.semigroup SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_3750Representative.basis :=
    (basisFor_iff_of_sameIdentityTheoryOver sameIdentityTheory).mp
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_3750Representative.basis_complete
  simpa only [oppositeTable_semigroup] using transferred


theorem opposite_basis :
    BasisFor table.semigroup (reversedBasis SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_3750Representative.basis) :=
  representative_basis.oppositeReversed

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_8539
