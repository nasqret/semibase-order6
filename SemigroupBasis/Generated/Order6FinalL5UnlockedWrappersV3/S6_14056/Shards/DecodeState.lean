import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14056.Shards.DecodeStatePart00
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14056.Shards.DecodeStatePart01

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14056.Shards

def stateVectorCode
    (vector : Fin 32 -> Fin 6) : Nat :=
  (vector (0 : Fin 32)).val + 6 * ((vector (1 : Fin 32)).val + 6 * ((vector (2 : Fin 32)).val + 6 * ((vector (3 : Fin 32)).val + 6 * ((vector (4 : Fin 32)).val + 6 * ((vector (5 : Fin 32)).val + 6 * ((vector (6 : Fin 32)).val + 6 * ((vector (7 : Fin 32)).val + 6 * ((vector (8 : Fin 32)).val + 6 * ((vector (9 : Fin 32)).val + 6 * ((vector (10 : Fin 32)).val + 6 * ((vector (11 : Fin 32)).val + 6 * ((vector (12 : Fin 32)).val + 6 * ((vector (13 : Fin 32)).val + 6 * ((vector (14 : Fin 32)).val + 6 * ((vector (15 : Fin 32)).val + 6 * ((vector (16 : Fin 32)).val + 6 * ((vector (17 : Fin 32)).val + 6 * ((vector (18 : Fin 32)).val + 6 * ((vector (19 : Fin 32)).val + 6 * ((vector (20 : Fin 32)).val + 6 * ((vector (21 : Fin 32)).val + 6 * ((vector (22 : Fin 32)).val + 6 * ((vector (23 : Fin 32)).val + 6 * ((vector (24 : Fin 32)).val + 6 * ((vector (25 : Fin 32)).val + 6 * ((vector (26 : Fin 32)).val + 6 * ((vector (27 : Fin 32)).val + 6 * ((vector (28 : Fin 32)).val + 6 * ((vector (29 : Fin 32)).val + 6 * ((vector (30 : Fin 32)).val + 6 * ((vector (31 : Fin 32)).val)))))))))))))))))))))))))))))))

def decodeStateCode (code : Nat) : Fin 1158 :=
  if code < 18441810636734733484032 then
    if code < 682375695376953950208 then
      if code < 18984032835970703616 then
        if code < 403537203527328000 then
          if code < 52547121580134240 then
            decodeStateCodeChunk0 code
          else
            decodeStateCodeChunk1 code
        else
          if code < 2414424376618064640 then
            decodeStateCodeChunk2 code
          else
            decodeStateCodeChunk3 code
      else
        if code < 21346108665799901184 then
          if code < 19357164116770557312 then
            decodeStateCodeChunk4 code
          else
            decodeStateCodeChunk5 code
        else
          if code < 85342186661595512832 then
            decodeStateCodeChunk6 code
          else
            if code < 104273875683828301824 then
              decodeStateCodeChunk7 code
            else
              decodeStateCodeChunk8 code
    else
      if code < 4094013277686726033408 then
        if code < 684741433007588032512 then
          if code < 682726889680991944704 then
            decodeStateCodeChunk9 code
          else
            decodeStateCodeChunk10 code
        else
          if code < 767665515629955907584 then
            decodeStateCodeChunk11 code
          else
            decodeStateCodeChunk12 code
      else
        if code < 4096375359002191724544 then
          if code < 4094364471860157087744 then
            decodeStateCodeChunk13 code
          else
            decodeStateCodeChunk14 code
        else
          if code < 4179303735536688463872 then
            decodeStateCodeChunk15 code
          else
            if code < 18422879048332087394304 then
              decodeStateCodeChunk16 code
            else
              decodeStateCodeChunk17 code
  else
    if code < 663240742173794112897024 then
      if code < 147383016746423372218368 then
        if code < 22516839915282224381952 then
          if code < 19105202304891960164352 then
            decodeStateCodeChunk18 code
          else
            decodeStateCodeChunk19 code
        else
          if code < 147382665552093212835840 then
            decodeStateCodeChunk20 code
          else
            decodeStateCodeChunk21 code
      else
        if code < 147467955400583435255808 then
          if code < 147385027633565406855168 then
            decodeStateCodeChunk22 code
          else
            decodeStateCodeChunk23 code
        else
          if code < 165805492195487659327488 then
            decodeStateCodeChunk24 code
          else
            if code < 663221810484771880108032 then
              decodeStateCodeChunk25 code
            else
              decodeStateCodeChunk26 code
    else
      if code < 5305774476730423026272256 then
        if code < 667315772062641713774592 then
          if code < 663904133841951339577344 then
            decodeStateCodeChunk27 code
          else
            decodeStateCodeChunk28 code
        else
          if code < 810604423715620379295744 then
            decodeStateCodeChunk29 code
          else
            if code < 5305774124521433549242368 then
              decodeStateCodeChunk30 code
            else
              decodeStateCodeChunk31 code
      else
        if code < 5305859415385523338346496 then
          if code < 5305776487617591061364736 then
            decodeStateCodeChunk32 code
          else
            decodeStateCodeChunk33 code
        else
          if code < 5324196951333154220212224 then
            decodeStateCodeChunk34 code
          else
            if code < 5968995883883932426371072 then
              decodeStateCodeChunk35 code
            else
              decodeStateCodeChunk36 code

def decodeState
    (vector : Fin 32 -> Fin 6) : Fin 1158 :=
  decodeStateCode (stateVectorCode vector)

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14056.Shards
