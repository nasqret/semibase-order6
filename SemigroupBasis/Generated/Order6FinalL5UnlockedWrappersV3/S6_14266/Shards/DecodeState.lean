import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14266.Shards.DecodeStatePart00
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14266.Shards.DecodeStatePart01

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14266.Shards

def stateVectorCode
    (vector : Fin 24 -> Fin 6) : Nat :=
  (vector (0 : Fin 24)).val + 6 * ((vector (1 : Fin 24)).val + 6 * ((vector (2 : Fin 24)).val + 6 * ((vector (3 : Fin 24)).val + 6 * ((vector (4 : Fin 24)).val + 6 * ((vector (5 : Fin 24)).val + 6 * ((vector (6 : Fin 24)).val + 6 * ((vector (7 : Fin 24)).val + 6 * ((vector (8 : Fin 24)).val + 6 * ((vector (9 : Fin 24)).val + 6 * ((vector (10 : Fin 24)).val + 6 * ((vector (11 : Fin 24)).val + 6 * ((vector (12 : Fin 24)).val + 6 * ((vector (13 : Fin 24)).val + 6 * ((vector (14 : Fin 24)).val + 6 * ((vector (15 : Fin 24)).val + 6 * ((vector (16 : Fin 24)).val + 6 * ((vector (17 : Fin 24)).val + 6 * ((vector (18 : Fin 24)).val + 6 * ((vector (19 : Fin 24)).val + 6 * ((vector (20 : Fin 24)).val + 6 * ((vector (21 : Fin 24)).val + 6 * ((vector (22 : Fin 24)).val + 6 * ((vector (23 : Fin 24)).val)))))))))))))))))))))))

def decodeStateCode (code : Nat) : Fin 1158 :=
  if code < 1983868436591383680 then
    if code < 1785714038747366400 then
      if code < 1109317203653727744 then
        if code < 447554093285611008 then
          if code < 320213214756804096 then
            decodeStateCodeChunk0 code
          else
            decodeStateCodeChunk1 code
        else
          if code < 469581332503721472 then
            decodeStateCodeChunk2 code
          else
            decodeStateCodeChunk3 code
      else
        if code < 1263592054788454692 then
          if code < 1237284316339213824 then
            decodeStateCodeChunk4 code
          else
            decodeStateCodeChunk5 code
        else
          if code < 1636416148352173056 then
            decodeStateCodeChunk6 code
          else
            if code < 1658457480129670656 then
              decodeStateCodeChunk7 code
            else
              decodeStateCodeChunk8 code
    else
      if code < 1894783794322839552 then
        if code < 1874065980403264896 then
          if code < 1852145486237347200 then
            decodeStateCodeChunk9 code
          else
            decodeStateCodeChunk10 code
        else
          if code < 1888707071242545408 then
            decodeStateCodeChunk11 code
          else
            decodeStateCodeChunk12 code
      else
        if code < 1910006973471598848 then
          if code < 1897831533392861184 then
            decodeStateCodeChunk13 code
          else
            decodeStateCodeChunk14 code
        else
          if code < 1916202130925230080 then
            decodeStateCodeChunk15 code
          else
            if code < 1920363738223712256 then
              decodeStateCodeChunk16 code
            else
              decodeStateCodeChunk17 code
  else
    if code < 2663118797501033856 then
      if code < 2042355687797329920 then
        if code < 2025798646078347264 then
          if code < 2009459664992352384 then
            decodeStateCodeChunk18 code
          else
            decodeStateCodeChunk19 code
        else
          if code < 2029467029328009216 then
            decodeStateCodeChunk20 code
          else
            decodeStateCodeChunk21 code
      else
        if code < 2422525947034618368 then
          if code < 2049464884740044544 then
            decodeStateCodeChunk22 code
          else
            decodeStateCodeChunk23 code
        else
          if code < 2448103148613010944 then
            decodeStateCodeChunk24 code
          else
            if code < 2579623216240684032 then
              decodeStateCodeChunk25 code
            else
              decodeStateCodeChunk26 code
    else
      if code < 2711041880569473024 then
        if code < 2684852628808568832 then
          if code < 2678454691150655232 then
            decodeStateCodeChunk27 code
          else
            decodeStateCodeChunk28 code
        else
          if code < 2688611209271571456 then
            decodeStateCodeChunk29 code
          else
            if code < 2705864647703851008 then
              decodeStateCodeChunk30 code
            else
              decodeStateCodeChunk31 code
      else
        if code < 2816070524410963968 then
          if code < 2798495962477216128 then
            decodeStateCodeChunk32 code
          else
            decodeStateCodeChunk33 code
        else
          if code < 2831290425688322304 then
            decodeStateCodeChunk34 code
          else
            if code < 2841749220642556176 then
              decodeStateCodeChunk35 code
            else
              decodeStateCodeChunk36 code

def decodeState
    (vector : Fin 24 -> Fin 6) : Fin 1158 :=
  decodeStateCode (stateVectorCode vector)

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14266.Shards
