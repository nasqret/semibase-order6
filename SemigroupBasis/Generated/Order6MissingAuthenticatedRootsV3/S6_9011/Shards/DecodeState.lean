import SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.Shards.DecodeStatePart00
import SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.Shards.DecodeStatePart01
import SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.Shards.DecodeStatePart02

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.Shards

def stateVectorCode
    (vector : Fin 17 -> Fin 6) : Nat :=
  (vector (0 : Fin 17)).val + 6 * ((vector (1 : Fin 17)).val + 6 * ((vector (2 : Fin 17)).val + 6 * ((vector (3 : Fin 17)).val + 6 * ((vector (4 : Fin 17)).val + 6 * ((vector (5 : Fin 17)).val + 6 * ((vector (6 : Fin 17)).val + 6 * ((vector (7 : Fin 17)).val + 6 * ((vector (8 : Fin 17)).val + 6 * ((vector (9 : Fin 17)).val + 6 * ((vector (10 : Fin 17)).val + 6 * ((vector (11 : Fin 17)).val + 6 * ((vector (12 : Fin 17)).val + 6 * ((vector (13 : Fin 17)).val + 6 * ((vector (14 : Fin 17)).val + 6 * ((vector (15 : Fin 17)).val + 6 * ((vector (16 : Fin 17)).val))))))))))))))))

def decodeStateCode (code : Nat) : Fin 2712 :=
  if code < 12734394175872 then
    if code < 10400954351046 then
      if code < 10072191115627 then
        if code < 9992071790605 then
          if code < 9915825535422 then
            if code < 9914009956273 then
              decodeStateCodeChunk0 code
            else
              decodeStateCodeChunk1 code
          else
            if code < 9917639621575 then
              decodeStateCodeChunk2 code
            else
              if code < 9918423909366 then
                decodeStateCodeChunk3 code
              else
                decodeStateCodeChunk4 code
        else
          if code < 9994621455691 then
            if code < 9993895767834 then
              decodeStateCodeChunk5 code
            else
              decodeStateCodeChunk6 code
          else
            if code < 9996727655275 then
              decodeStateCodeChunk7 code
            else
              if code < 10070375629788 then
                decodeStateCodeChunk8 code
              else
                decodeStateCodeChunk9 code
      else
        if code < 10384257319705 then
          if code < 10074789488275 then
            if code < 10072916896578 then
              decodeStateCodeChunk10 code
            else
              decodeStateCodeChunk11 code
          else
            if code < 10305911542176 then
              decodeStateCodeChunk12 code
            else
              if code < 10383530232384 then
                decodeStateCodeChunk13 code
              else
                decodeStateCodeChunk14 code
        else
          if code < 10396531906560 then
            if code < 10386071499390 then
              decodeStateCodeChunk15 code
            else
              if code < 10387893703687 then
                decodeStateCodeChunk16 code
              else
                decodeStateCodeChunk17 code
          else
            if code < 10397326458457 then
              decodeStateCodeChunk18 code
            else
              if code < 10399140404863 then
                decodeStateCodeChunk19 code
              else
                decodeStateCodeChunk20 code
    else
      if code < 10494185031834 then
        if code < 10466612314963 then
          if code < 10462256961804 then
            if code < 10402699566031 then
              decodeStateCodeChunk21 code
            else
              decodeStateCodeChunk22 code
          else
            if code < 10464071047963 then
              decodeStateCodeChunk23 code
            else
              if code < 10464798228594 then
                decodeStateCodeChunk24 code
              else
                decodeStateCodeChunk25 code
        else
          if code < 10476780695317 then
            if code < 10475258869260 then
              decodeStateCodeChunk26 code
            else
              decodeStateCodeChunk27 code
          else
            if code < 10477867367347 then
              decodeStateCodeChunk28 code
            else
              if code < 10479681313746 then
                decodeStateCodeChunk29 code
              else
                decodeStateCodeChunk30 code
      else
        if code < 10553985831708 then
          if code < 10542739364034 then
            if code < 10540925184349 then
              decodeStateCodeChunk31 code
            else
              decodeStateCodeChunk32 code
          else
            if code < 10544611955515 then
              decodeStateCodeChunk33 code
            else
              if code < 10545337736466 then
                decodeStateCodeChunk34 code
              else
                decodeStateCodeChunk35 code
        else
          if code < 10558408274898 then
            if code < 10555507663387 then
              decodeStateCodeChunk36 code
            else
              if code < 10557321602875 then
                decodeStateCodeChunk37 code
              else
                decodeStateCodeChunk38 code
          else
            if code < 10776096806472 then
              decodeStateCodeChunk39 code
            else
              if code < 10789147236169 then
                decodeStateCodeChunk40 code
              else
                decodeStateCodeChunk41 code
  else
    if code < 12902742112644 then
      if code < 12815298022003 then
        if code < 12748182470425 then
          if code < 12737298286591 then
            if code < 12735129941425 then
              decodeStateCodeChunk42 code
            else
              decodeStateCodeChunk43 code
          else
            if code < 12739473342870 then
              decodeStateCodeChunk44 code
            else
              if code < 12746003798737 then
                decodeStateCodeChunk45 code
              else
                decodeStateCodeChunk46 code
        else
          if code < 12752181690559 then
            if code < 12750065281086 then
              decodeStateCodeChunk47 code
            else
              decodeStateCodeChunk48 code
          else
            if code < 12758712006457 then
              decodeStateCodeChunk49 code
            else
              if code < 12813131216268 then
                decodeStateCodeChunk50 code
              else
                decodeStateCodeChunk51 code
      else
        if code < 12830182965402 then
          if code < 12823652354004 then
            if code < 12817182504283 then
              decodeStateCodeChunk52 code
            else
              decodeStateCodeChunk53 code
          else
            if code < 12825889952437 then
              decodeStateCodeChunk54 code
            else
              if code < 12828007909339 then
                decodeStateCodeChunk55 code
              else
                decodeStateCodeChunk56 code
        else
          if code < 12893299296810 then
            if code < 12830969119219 then
              decodeStateCodeChunk57 code
            else
              if code < 12891124232965 then
                decodeStateCodeChunk58 code
              else
                decodeStateCodeChunk59 code
          else
            if code < 12894035061067 then
              decodeStateCodeChunk60 code
            else
              if code < 12896203399747 then
                decodeStateCodeChunk61 code
              else
                decodeStateCodeChunk62 code
    else
      if code < 13296074890357 then
        if code < 13131001961791 then
          if code < 12907087591363 then
            if code < 12904919244685 then
              decodeStateCodeChunk63 code
            else
              decodeStateCodeChunk64 code
          else
            if code < 12908970392946 then
              decodeStateCodeChunk65 code
            else
              if code < 12915442062253 then
                decodeStateCodeChunk66 code
              else
                decodeStateCodeChunk67 code
        else
          if code < 13219818650791 then
            if code < 13143700091814 then
              decodeStateCodeChunk68 code
            else
              if code < 13218004704601 then
                decodeStateCodeChunk69 code
              else
                decodeStateCodeChunk70 code
          else
            if code < 13220614742334 then
              decodeStateCodeChunk71 code
            else
              if code < 13222427141311 then
                decodeStateCodeChunk72 code
              else
                decodeStateCodeChunk73 code
      else
        if code < 13375164695437 then
          if code < 13298908457203 then
            if code < 13297830043068 then
              decodeStateCodeChunk74 code
            else
              decodeStateCodeChunk75 code
          else
            if code < 13300722395827 then
              decodeStateCodeChunk76 code
            else
              if code < 13374370144836 then
                decodeStateCodeChunk77 code
              else
                decodeStateCodeChunk78 code
        else
          if code < 13380537796567 then
            if code < 13376978641843 then
              decodeStateCodeChunk79 code
            else
              if code < 13378792580250 then
                decodeStateCodeChunk80 code
              else
                decodeStateCodeChunk81 code
          else
            if code < 13613885123047 then
              decodeStateCodeChunk82 code
            else
              if code < 15566388267168 then
                decodeStateCodeChunk83 code
              else
                decodeStateCodeChunk84 code

def decodeState
    (vector : Fin 17 -> Fin 6) : Fin 2712 :=
  decodeStateCode (stateVectorCode vector)

end SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.Shards
