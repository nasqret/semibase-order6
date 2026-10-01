import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6988.Shards.DecodeStatePart00
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6988.Shards.DecodeStatePart01
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6988.Shards.DecodeStatePart02
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6988.Shards.DecodeStatePart03
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6988.Shards.DecodeStatePart04

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6988.Shards

def stateVectorCode
    (vector : Fin 10 -> Fin 6) : Nat :=
  (vector (0 : Fin 10)).val + 6 * ((vector (1 : Fin 10)).val + 6 * ((vector (2 : Fin 10)).val + 6 * ((vector (3 : Fin 10)).val + 6 * ((vector (4 : Fin 10)).val + 6 * ((vector (5 : Fin 10)).val + 6 * ((vector (6 : Fin 10)).val + 6 * ((vector (7 : Fin 10)).val + 6 * ((vector (8 : Fin 10)).val + 6 * ((vector (9 : Fin 10)).val)))))))))

def decodeStateCode (code : Nat) : Fin 4374 :=
  if code < 45301032 then
    if code < 36274518 then
      if code < 26770176 then
        if code < 16179264 then
          if code < 8101296 then
            if code < 6653664 then
              if code < 6336144 then
                decodeStateCodeChunk0 code
              else
                decodeStateCodeChunk1 code
            else
              if code < 7787664 then
                decodeStateCodeChunk2 code
              else
                decodeStateCodeChunk3 code
          else
            if code < 9692784 then
              if code < 8395488 then
                decodeStateCodeChunk4 code
              else
                decodeStateCodeChunk5 code
            else
              if code < 9983088 then
                decodeStateCodeChunk6 code
              else
                decodeStateCodeChunk7 code
        else
          if code < 18378576 then
            if code < 16787088 then
              if code < 16496784 then
                decodeStateCodeChunk8 code
              else
                decodeStateCodeChunk9 code
            else
              if code < 18084384 then
                decodeStateCodeChunk10 code
              else
                decodeStateCodeChunk11 code
          else
            if code < 19826208 then
              if code < 19532016 then
                decodeStateCodeChunk12 code
              else
                decodeStateCodeChunk13 code
            else
              if code < 20143728 then
                decodeStateCodeChunk14 code
              else
                if code < 26312688 then
                  decodeStateCodeChunk15 code
                else
                  decodeStateCodeChunk16 code
      else
        if code < 31865400 then
          if code < 29669328 then
            if code < 28217808 then
              if code < 27927504 then
                decodeStateCodeChunk17 code
              else
                decodeStateCodeChunk18 code
            else
              if code < 28535328 then
                decodeStateCodeChunk19 code
              else
                decodeStateCodeChunk20 code
          else
            if code < 31257576 then
              if code < 30122928 then
                decodeStateCodeChunk21 code
              else
                decodeStateCodeChunk22 code
            else
              if code < 31575096 then
                decodeStateCodeChunk23 code
              else
                decodeStateCodeChunk24 code
        else
          if code < 34927848 then
            if code < 33480216 then
              if code < 33022728 then
                decodeStateCodeChunk25 code
              else
                decodeStateCodeChunk26 code
            else
              if code < 34610328 then
                decodeStateCodeChunk27 code
              else
                decodeStateCodeChunk28 code
          else
            if code < 35535780 then
              if code < 35222040 then
                decodeStateCodeChunk29 code
              else
                decodeStateCodeChunk30 code
            else
              if code < 35829972 then
                decodeStateCodeChunk31 code
              else
                if code < 36146865 then
                  decodeStateCodeChunk32 code
                else
                  decodeStateCodeChunk33 code
    else
      if code < 38853540 then
        if code < 37500516 then
          if code < 36700257 then
            if code < 36512337 then
              if code < 36358758 then
                decodeStateCodeChunk34 code
              else
                decodeStateCodeChunk35 code
            else
              if code < 36593334 then
                decodeStateCodeChunk36 code
              else
                decodeStateCodeChunk37 code
          else
            if code < 36912150 then
              if code < 36831798 then
                decodeStateCodeChunk38 code
              else
                decodeStateCodeChunk39 code
            else
              if code < 37182996 then
                decodeStateCodeChunk40 code
              else
                decodeStateCodeChunk41 code
        else
          if code < 38155665 then
            if code < 37945062 then
              if code < 37790820 then
                decodeStateCodeChunk42 code
              else
                decodeStateCodeChunk43 code
            else
              if code < 38029302 then
                decodeStateCodeChunk44 code
              else
                decodeStateCodeChunk45 code
          else
            if code < 38344233 then
              if code < 38263878 then
                decodeStateCodeChunk46 code
              else
                decodeStateCodeChunk47 code
            else
              if code < 38498454 then
                decodeStateCodeChunk48 code
              else
                if code < 38578809 then
                  decodeStateCodeChunk49 code
                else
                  decodeStateCodeChunk50 code
      else
        if code < 40168353 then
          if code < 39692073 then
            if code < 39461364 then
              if code < 39143844 then
                decodeStateCodeChunk51 code
              else
                decodeStateCodeChunk52 code
            else
              if code < 39615606 then
                decodeStateCodeChunk53 code
              else
                decodeStateCodeChunk54 code
          else
            if code < 39930537 then
              if code < 39826209 then
                decodeStateCodeChunk55 code
              else
                decodeStateCodeChunk56 code
            else
              if code < 40010889 then
                decodeStateCodeChunk57 code
              else
                decodeStateCodeChunk58 code
        else
          if code < 41971608 then
            if code < 41336568 then
              if code < 40249353 then
                decodeStateCodeChunk59 code
              else
                decodeStateCodeChunk60 code
            else
              if code < 41654088 then
                decodeStateCodeChunk61 code
              else
                decodeStateCodeChunk62 code
          else
            if code < 43559208 then
              if code < 43101720 then
                decodeStateCodeChunk63 code
              else
                decodeStateCodeChunk64 code
            else
              if code < 44693208 then
                decodeStateCodeChunk65 code
              else
                if code < 45006840 then
                  decodeStateCodeChunk66 code
                else
                  decodeStateCodeChunk67 code
  else
    if code < 53185032 then
      if code < 48342870 then
        if code < 46779249 then
          if code < 46353513 then
            if code < 45908964 then
              if code < 45618660 then
                decodeStateCodeChunk68 code
              else
                decodeStateCodeChunk69 code
            else
              if code < 46225857 then
                decodeStateCodeChunk70 code
              else
                decodeStateCodeChunk71 code
          else
            if code < 46591329 then
              if code < 46437750 then
                decodeStateCodeChunk72 code
              else
                decodeStateCodeChunk73 code
            else
              if code < 46676214 then
                decodeStateCodeChunk74 code
              else
                decodeStateCodeChunk75 code
        else
          if code < 47579508 then
            if code < 46995030 then
              if code < 46910790 then
                decodeStateCodeChunk76 code
              else
                decodeStateCodeChunk77 code
            else
              if code < 47261988 then
                decodeStateCodeChunk78 code
              else
                decodeStateCodeChunk79 code
          else
            if code < 48024054 then
              if code < 47896401 then
                decodeStateCodeChunk80 code
              else
                decodeStateCodeChunk81 code
            else
              if code < 48108294 then
                decodeStateCodeChunk82 code
              else
                if code < 48238545 then
                  decodeStateCodeChunk83 code
                else
                  decodeStateCodeChunk84 code
      else
        if code < 49774953 then
          if code < 48932532 then
            if code < 48581334 then
              if code < 48423225 then
                decodeStateCodeChunk85 code
              else
                decodeStateCodeChunk86 code
            else
              if code < 48657801 then
                decodeStateCodeChunk87 code
              else
                decodeStateCodeChunk88 code
          else
            if code < 49540356 then
              if code < 49250052 then
                decodeStateCodeChunk89 code
              else
                decodeStateCodeChunk90 code
            else
              if code < 49694598 then
                decodeStateCodeChunk91 code
              else
                decodeStateCodeChunk92 code
        else
          if code < 50247345 then
            if code < 50009529 then
              if code < 49905201 then
                decodeStateCodeChunk93 code
              else
                decodeStateCodeChunk94 code
            else
              if code < 50093769 then
                decodeStateCodeChunk95 code
              else
                decodeStateCodeChunk96 code
          else
            if code < 51442776 then
              if code < 50328345 then
                decodeStateCodeChunk97 code
              else
                decodeStateCodeChunk98 code
            else
              if code < 51733080 then
                decodeStateCodeChunk99 code
              else
                if code < 52051032 then
                  decodeStateCodeChunk100 code
                else
                  decodeStateCodeChunk101 code
    else
      if code < 57975393 then
        if code < 56432505 then
          if code < 55380024 then
            if code < 54772200 then
              if code < 53638200 then
                decodeStateCodeChunk102 code
              else
                decodeStateCodeChunk103 code
            else
              if code < 55089720 then
                decodeStateCodeChunk104 code
              else
                decodeStateCodeChunk105 code
          else
            if code < 56155140 then
              if code < 55698084 then
                decodeStateCodeChunk106 code
              else
                decodeStateCodeChunk107 code
            else
              if code < 56304849 then
                decodeStateCodeChunk108 code
              else
                decodeStateCodeChunk109 code
        else
          if code < 56862129 then
            if code < 56670321 then
              if code < 56521062 then
                decodeStateCodeChunk110 code
              else
                decodeStateCodeChunk111 code
            else
              if code < 56755206 then
                decodeStateCodeChunk112 code
              else
                decodeStateCodeChunk113 code
          else
            if code < 57074454 then
              if code < 56989782 then
                decodeStateCodeChunk114 code
              else
                decodeStateCodeChunk115 code
            else
              if code < 57368628 then
                decodeStateCodeChunk116 code
              else
                if code < 57658932 then
                  decodeStateCodeChunk117 code
                else
                  decodeStateCodeChunk118 code
      else
        if code < 59329548 then
          if code < 58425750 then
            if code < 58187718 then
              if code < 58106934 then
                decodeStateCodeChunk119 code
              else
                decodeStateCodeChunk120 code
            else
              if code < 58317537 then
                decodeStateCodeChunk121 code
              else
                decodeStateCodeChunk122 code
          else
            if code < 58660326 then
              if code < 58502649 then
                decodeStateCodeChunk123 code
              else
                decodeStateCodeChunk124 code
            else
              if code < 58744998 then
                decodeStateCodeChunk125 code
              else
                if code < 59011596 then
                  decodeStateCodeChunk126 code
                else
                  decodeStateCodeChunk127 code
        else
          if code < 59988153 then
            if code < 59773662 then
              if code < 59623740 then
                decodeStateCodeChunk128 code
              else
                decodeStateCodeChunk129 code
            else
              if code < 59854017 then
                decodeStateCodeChunk130 code
              else
                decodeStateCodeChunk131 code
          else
            if code < 60173265 then
              if code < 60088593 then
                decodeStateCodeChunk132 code
              else
                decodeStateCodeChunk133 code
            else
              if code < 60330954 then
                decodeStateCodeChunk134 code
              else
                if code < 60407421 then
                  decodeStateCodeChunk135 code
                else
                  decodeStateCodeChunk136 code

def decodeState
    (vector : Fin 10 -> Fin 6) : Fin 4374 :=
  decodeStateCode (stateVectorCode vector)

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6988.Shards
