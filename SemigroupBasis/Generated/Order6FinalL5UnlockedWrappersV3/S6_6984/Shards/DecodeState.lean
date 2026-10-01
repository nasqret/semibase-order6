import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6984.Shards.DecodeStatePart00
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6984.Shards.DecodeStatePart01
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6984.Shards.DecodeStatePart02
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6984.Shards.DecodeStatePart03
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6984.Shards.DecodeStatePart04

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6984.Shards

def stateVectorCode
    (vector : Fin 18 -> Fin 6) : Nat :=
  (vector (0 : Fin 18)).val + 6 * ((vector (1 : Fin 18)).val + 6 * ((vector (2 : Fin 18)).val + 6 * ((vector (3 : Fin 18)).val + 6 * ((vector (4 : Fin 18)).val + 6 * ((vector (5 : Fin 18)).val + 6 * ((vector (6 : Fin 18)).val + 6 * ((vector (7 : Fin 18)).val + 6 * ((vector (8 : Fin 18)).val + 6 * ((vector (9 : Fin 18)).val + 6 * ((vector (10 : Fin 18)).val + 6 * ((vector (11 : Fin 18)).val + 6 * ((vector (12 : Fin 18)).val + 6 * ((vector (13 : Fin 18)).val + 6 * ((vector (14 : Fin 18)).val + 6 * ((vector (15 : Fin 18)).val + 6 * ((vector (16 : Fin 18)).val + 6 * ((vector (17 : Fin 18)).val)))))))))))))))))

def decodeStateCode (code : Nat) : Fin 4374 :=
  if code < 248111514720 then
    if code < 41791085568 then
      if code < 11188202112 then
        if code < 2188819584 then
          if code < 475051392 then
            if code < 312688512 then
              if code < 63545472 then
                decodeStateCodeChunk0 code
              else
                decodeStateCodeChunk1 code
            else
              if code < 381272832 then
                decodeStateCodeChunk2 code
              else
                decodeStateCodeChunk3 code
          else
            if code < 787739904 then
              if code < 724194432 then
                decodeStateCodeChunk4 code
              else
                decodeStateCodeChunk5 code
            else
              if code < 1037722752 then
                decodeStateCodeChunk6 code
              else
                decodeStateCodeChunk7 code
        else
          if code < 2850308352 then
            if code < 2532580992 then
              if code < 2287636992 then
                decodeStateCodeChunk8 code
              else
                decodeStateCodeChunk9 code
            else
              if code < 2600325504 then
                decodeStateCodeChunk10 code
              else
                decodeStateCodeChunk11 code
          else
            if code < 2981598336 then
              if code < 2913853824 then
                decodeStateCodeChunk12 code
              else
                decodeStateCodeChunk13 code
            else
              if code < 3256775424 then
                decodeStateCodeChunk14 code
              else
                if code < 10944331380 then
                  decodeStateCodeChunk15 code
                else
                  decodeStateCodeChunk16 code
      else
        if code < 39503448576 then
          if code < 11668525632 then
            if code < 11320331904 then
              if code < 11256786432 then
                decodeStateCodeChunk17 code
              else
                decodeStateCodeChunk18 code
            else
              if code < 11599708032 then
                decodeStateCodeChunk19 code
              else
                decodeStateCodeChunk20 code
          else
            if code < 39190760064 then
              if code < 11913236352 then
                decodeStateCodeChunk21 code
              else
                decodeStateCodeChunk22 code
            else
              if code < 39254305536 then
                decodeStateCodeChunk23 code
              else
                decodeStateCodeChunk24 code
        else
          if code < 41066891136 then
            if code < 39847209984 then
              if code < 39597227136 then
                decodeStateCodeChunk25 code
              else
                decodeStateCodeChunk26 code
            else
              if code < 40998306816 then
                decodeStateCodeChunk27 code
              else
                decodeStateCodeChunk28 code
          else
            if code < 41409812736 then
              if code < 41316873984 then
                decodeStateCodeChunk29 code
              else
                decodeStateCodeChunk30 code
            else
              if code < 41478397056 then
                decodeStateCodeChunk31 code
              else
                if code < 41723341056 then
                  decodeStateCodeChunk32 code
                else
                  decodeStateCodeChunk33 code
    else
      if code < 236918234880 then
        if code < 50541325056 then
          if code < 50066273664 then
            if code < 43223238144 then
              if code < 42036029568 then
                decodeStateCodeChunk34 code
              else
                decodeStateCodeChunk35 code
            else
              if code < 43285943808 then
                decodeStateCodeChunk36 code
              else
                decodeStateCodeChunk37 code
          else
            if code < 50378962176 then
              if code < 50134857984 then
                decodeStateCodeChunk38 code
              else
                decodeStateCodeChunk39 code
            else
              if code < 50447546496 then
                decodeStateCodeChunk40 code
              else
                decodeStateCodeChunk41 code
        else
          if code < 235105649280 then
            if code < 51942404736 then
              if code < 50790740261 then
                decodeStateCodeChunk42 code
              else
                decodeStateCodeChunk43 code
            else
              if code < 52192387584 then
                decodeStateCodeChunk44 code
              else
                decodeStateCodeChunk45 code
          else
            if code < 235423376640 then
              if code < 235173393792 then
                decodeStateCodeChunk46 code
              else
                decodeStateCodeChunk47 code
            else
              if code < 235517155200 then
                decodeStateCodeChunk48 code
              else
                if code < 235766298240 then
                  decodeStateCodeChunk49 code
                else
                  decodeStateCodeChunk50 code
      else
        if code < 239112093312 then
          if code < 237574684800 then
            if code < 237230923392 then
              if code < 236986819200 then
                decodeStateCodeChunk51 code
              else
                decodeStateCodeChunk52 code
            else
              if code < 237329740800 then
                decodeStateCodeChunk53 code
              else
                decodeStateCodeChunk54 code
          else
            if code < 237711013632 then
              if code < 237642429312 then
                decodeStateCodeChunk55 code
              else
                decodeStateCodeChunk56 code
            else
              if code < 237955957632 then
                decodeStateCodeChunk57 code
              else
                decodeStateCodeChunk58 code
        else
          if code < 246298890240 then
            if code < 245986201728 then
              if code < 239387270400 then
                decodeStateCodeChunk59 code
              else
                decodeStateCodeChunk60 code
            else
              if code < 246048907392 then
                decodeStateCodeChunk61 code
              else
                decodeStateCodeChunk62 code
          else
            if code < 246641811840 then
              if code < 246362435712 then
                decodeStateCodeChunk63 code
              else
                decodeStateCodeChunk64 code
            else
              if code < 247798787328 then
                decodeStateCodeChunk65 code
              else
                if code < 247862332800 then
                  decodeStateCodeChunk66 code
                else
                  decodeStateCodeChunk67 code
  else
    if code < 8465923049472 then
      if code < 1421551119744 then
        if code < 1412733135744 then
          if code < 1410988294656 then
            if code < 1410675606144 then
              if code < 1410607021824 then
                decodeStateCodeChunk68 code
              else
                decodeStateCodeChunk69 code
            else
              if code < 1410919710336 then
                decodeStateCodeChunk70 code
              else
                decodeStateCodeChunk71 code
          else
            if code < 1412419607424 then
              if code < 1411051840128 then
                decodeStateCodeChunk72 code
              else
                decodeStateCodeChunk73 code
            else
              if code < 1412488191744 then
                decodeStateCodeChunk74 code
              else
                decodeStateCodeChunk75 code
        else
          if code < 1413207347328 then
            if code < 1412864425728 then
              if code < 1412800880256 then
                decodeStateCodeChunk76 code
              else
                decodeStateCodeChunk77 code
            else
              if code < 1413114408576 then
                decodeStateCodeChunk78 code
              else
                decodeStateCodeChunk79 code
          else
            if code < 1414609266816 then
              if code < 1414545721344 then
                decodeStateCodeChunk80 code
              else
                decodeStateCodeChunk81 code
            else
              if code < 1414677011328 then
                decodeStateCodeChunk82 code
              else
                if code < 1421457341184 then
                  decodeStateCodeChunk83 code
                else
                  decodeStateCodeChunk84 code
      else
        if code < 8463635412480 then
          if code < 1423264887936 then
            if code < 1421863808256 then
              if code < 1421619097536 then
                decodeStateCodeChunk85 code
              else
                decodeStateCodeChunk86 code
            else
              if code < 1421932392576 then
                decodeStateCodeChunk87 code
              else
                decodeStateCodeChunk88 code
          else
            if code < 1423427250816 then
              if code < 1423363705344 then
                decodeStateCodeChunk89 code
              else
                decodeStateCodeChunk90 code
            else
              if code < 8463390468480 then
                decodeStateCodeChunk91 code
              else
                decodeStateCodeChunk92 code
        else
          if code < 8465198855040 then
            if code < 8463766702464 then
              if code < 8463703996800 then
                decodeStateCodeChunk93 code
              else
                decodeStateCodeChunk94 code
            else
              if code < 8464046918400 then
                decodeStateCodeChunk95 code
              else
                decodeStateCodeChunk96 code
          else
            if code < 8465516582400 then
              if code < 8465447998080 then
                decodeStateCodeChunk97 code
              else
                decodeStateCodeChunk98 code
            else
              if code < 8465580127872 then
                decodeStateCodeChunk99 code
              else
                if code < 8465859504000 then
                  decodeStateCodeChunk100 code
                else
                  decodeStateCodeChunk101 code
    else
      if code < 50781792599424 then
        if code < 8474647254912 then
          if code < 8467637657472 then
            if code < 8467324129152 then
              if code < 8466173032320 then
                decodeStateCodeChunk102 code
              else
                decodeStateCodeChunk103 code
            else
              if code < 8467392713472 then
                decodeStateCodeChunk104 code
              else
                decodeStateCodeChunk105 code
          else
            if code < 8474515964928 then
              if code < 8474265982080 then
                decodeStateCodeChunk106 code
              else
                decodeStateCodeChunk107 code
            else
              if code < 8474579510400 then
                decodeStateCodeChunk108 code
              else
                decodeStateCodeChunk109 code
        else
          if code < 50779980013824 then
            if code < 8476079407488 then
              if code < 8474892198912 then
                decodeStateCodeChunk110 code
              else
                decodeStateCodeChunk111 code
            else
              if code < 8476142113152 then
                decodeStateCodeChunk112 code
              else
                decodeStateCodeChunk113 code
          else
            if code < 50780292702336 then
              if code < 50780048598144 then
                decodeStateCodeChunk114 code
              else
                decodeStateCodeChunk115 code
            else
              if code < 50780391519744 then
                decodeStateCodeChunk116 code
              else
                if code < 50780455065216 then
                  decodeStateCodeChunk117 code
                else
                  decodeStateCodeChunk118 code
      else
        if code < 50784080236416 then
          if code < 50782267650816 then
            if code < 50782106127744 then
              if code < 50781861183744 then
                decodeStateCodeChunk119 code
              else
                decodeStateCodeChunk120 code
            else
              if code < 50782173872256 then
                decodeStateCodeChunk121 code
              else
                decodeStateCodeChunk122 code
          else
            if code < 50782580339328 then
              if code < 50782517640144 then
                decodeStateCodeChunk123 code
              else
                decodeStateCodeChunk124 code
            else
              if code < 50782830322176 then
                decodeStateCodeChunk125 code
              else
                if code < 50783982258816 then
                  decodeStateCodeChunk126 code
                else
                  decodeStateCodeChunk127 code
        else
          if code < 50784706453248 then
            if code < 50784393764736 then
              if code < 50784330219264 then
                decodeStateCodeChunk128 code
              else
                decodeStateCodeChunk129 code
            else
              if code < 50784642907776 then
                decodeStateCodeChunk130 code
              else
                decodeStateCodeChunk131 code
          else
            if code < 50785049374848 then
              if code < 50784775037568 then
                decodeStateCodeChunk132 code
              else
                decodeStateCodeChunk133 code
            else
              if code < 50786206350336 then
                decodeStateCodeChunk134 code
              else
                if code < 50786451294336 then
                  decodeStateCodeChunk135 code
                else
                  decodeStateCodeChunk136 code

def decodeState
    (vector : Fin 18 -> Fin 6) : Fin 4374 :=
  decodeStateCode (stateVectorCode vector)

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6984.Shards
