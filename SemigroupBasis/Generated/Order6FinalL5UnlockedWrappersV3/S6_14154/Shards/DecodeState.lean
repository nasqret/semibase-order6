import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.Shards.DecodeStatePart00
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.Shards.DecodeStatePart01

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.Shards

def stateVectorCode
    (vector : Fin 21 -> Fin 6) : Nat :=
  (vector (0 : Fin 21)).val + 6 * ((vector (1 : Fin 21)).val + 6 * ((vector (2 : Fin 21)).val + 6 * ((vector (3 : Fin 21)).val + 6 * ((vector (4 : Fin 21)).val + 6 * ((vector (5 : Fin 21)).val + 6 * ((vector (6 : Fin 21)).val + 6 * ((vector (7 : Fin 21)).val + 6 * ((vector (8 : Fin 21)).val + 6 * ((vector (9 : Fin 21)).val + 6 * ((vector (10 : Fin 21)).val + 6 * ((vector (11 : Fin 21)).val + 6 * ((vector (12 : Fin 21)).val + 6 * ((vector (13 : Fin 21)).val + 6 * ((vector (14 : Fin 21)).val + 6 * ((vector (15 : Fin 21)).val + 6 * ((vector (16 : Fin 21)).val + 6 * ((vector (17 : Fin 21)).val + 6 * ((vector (18 : Fin 21)).val + 6 * ((vector (19 : Fin 21)).val + 6 * ((vector (20 : Fin 21)).val))))))))))))))))))))

def decodeStateCode (code : Nat) : Fin 1158 :=
  if code < 69385757265792 then
    if code < 12424190095872 then
      if code < 1572503528448 then
        if code < 1129895132544 then
          if code < 971691448320 then
            decodeStateCodeChunk0 code
          else
            decodeStateCodeChunk1 code
        else
          if code < 1208259296640 then
            decodeStateCodeChunk2 code
          else
            decodeStateCodeChunk3 code
      else
        if code < 1692544991904 then
          if code < 1650877770240 then
            decodeStateCodeChunk4 code
          else
            decodeStateCodeChunk5 code
        else
          if code < 11958339080448 then
            decodeStateCodeChunk6 code
          else
            if code < 12402418913280 then
              decodeStateCodeChunk7 code
            else
              decodeStateCodeChunk8 code
    else
      if code < 68445780233472 then
        if code < 12883310423424 then
          if code < 12741976802304 then
            decodeStateCodeChunk9 code
          else
            decodeStateCodeChunk10 code
        else
          if code < 12898547899776 then
            decodeStateCodeChunk11 code
          else
            decodeStateCodeChunk12 code
      else
        if code < 68911631248896 then
          if code < 68833267084800 then
            decodeStateCodeChunk13 code
          else
            decodeStateCodeChunk14 code
        else
          if code < 69229417955328 then
            decodeStateCodeChunk15 code
          else
            if code < 69307685354880 then
              decodeStateCodeChunk16 code
            else
              decodeStateCodeChunk17 code
  else
    if code < 2438645042556288 then
      if code < 407773188430848 then
        if code < 407367605490048 then
          if code < 406989552388608 then
            decodeStateCodeChunk18 code
          else
            decodeStateCodeChunk19 code
        else
          if code < 407445969654144 then
            decodeStateCodeChunk20 code
          else
            decodeStateCodeChunk21 code
      else
        if code < 407929771285632 then
          if code < 407851455830400 then
            decodeStateCodeChunk22 code
          else
            decodeStateCodeChunk23 code
        else
          if code < 2438188625290752 then
            decodeStateCodeChunk24 code
          else
            if code < 2438566678392192 then
              decodeStateCodeChunk25 code
            else
              decodeStateCodeChunk26 code
    else
      if code < 14625697239355392 then
        if code < 2439052100853120 then
          if code < 2438972261332992 then
            decodeStateCodeChunk27 code
          else
            decodeStateCodeChunk28 code
        else
          if code < 2439130477101120 then
            decodeStateCodeChunk29 code
          else
            if code < 14624913663779328 then
              decodeStateCodeChunk30 code
            else
              decodeStateCodeChunk31 code
      else
        if code < 14625777078875520 then
          if code < 14625761841399168 then
            decodeStateCodeChunk32 code
          else
            decodeStateCodeChunk33 code
        else
          if code < 14625840205563264 then
            decodeStateCodeChunk34 code
          else
            if code < 14625855444999168 then
              decodeStateCodeChunk35 code
            else
              decodeStateCodeChunk36 code

def decodeState
    (vector : Fin 21 -> Fin 6) : Fin 1158 :=
  decodeStateCode (stateVectorCode vector)

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.Shards
