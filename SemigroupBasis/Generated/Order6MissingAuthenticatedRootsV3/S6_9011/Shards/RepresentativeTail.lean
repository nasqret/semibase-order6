import SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.Shards.RepresentativeTailPart00
import SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.Shards.RepresentativeTailPart01
import SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.Shards.RepresentativeTailPart02

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.Shards

def representativeTail (state : Fin 2712) :
    List (Fin 4) :=
  if state.val < 1344 then
    if state.val < 672 then
      if state.val < 320 then
        if state.val < 160 then
          if state.val < 64 then
            if state.val < 32 then
              representativeTailChunk0 state.val
            else
              representativeTailChunk1 (state.val - 32)
          else
            if state.val < 96 then
              representativeTailChunk2 (state.val - 64)
            else
              if state.val < 128 then
                representativeTailChunk3 (state.val - 96)
              else
                representativeTailChunk4 (state.val - 128)
        else
          if state.val < 224 then
            if state.val < 192 then
              representativeTailChunk5 (state.val - 160)
            else
              representativeTailChunk6 (state.val - 192)
          else
            if state.val < 256 then
              representativeTailChunk7 (state.val - 224)
            else
              if state.val < 288 then
                representativeTailChunk8 (state.val - 256)
              else
                representativeTailChunk9 (state.val - 288)
      else
        if state.val < 480 then
          if state.val < 384 then
            if state.val < 352 then
              representativeTailChunk10 (state.val - 320)
            else
              representativeTailChunk11 (state.val - 352)
          else
            if state.val < 416 then
              representativeTailChunk12 (state.val - 384)
            else
              if state.val < 448 then
                representativeTailChunk13 (state.val - 416)
              else
                representativeTailChunk14 (state.val - 448)
        else
          if state.val < 576 then
            if state.val < 512 then
              representativeTailChunk15 (state.val - 480)
            else
              if state.val < 544 then
                representativeTailChunk16 (state.val - 512)
              else
                representativeTailChunk17 (state.val - 544)
          else
            if state.val < 608 then
              representativeTailChunk18 (state.val - 576)
            else
              if state.val < 640 then
                representativeTailChunk19 (state.val - 608)
              else
                representativeTailChunk20 (state.val - 640)
    else
      if state.val < 992 then
        if state.val < 832 then
          if state.val < 736 then
            if state.val < 704 then
              representativeTailChunk21 (state.val - 672)
            else
              representativeTailChunk22 (state.val - 704)
          else
            if state.val < 768 then
              representativeTailChunk23 (state.val - 736)
            else
              if state.val < 800 then
                representativeTailChunk24 (state.val - 768)
              else
                representativeTailChunk25 (state.val - 800)
        else
          if state.val < 896 then
            if state.val < 864 then
              representativeTailChunk26 (state.val - 832)
            else
              representativeTailChunk27 (state.val - 864)
          else
            if state.val < 928 then
              representativeTailChunk28 (state.val - 896)
            else
              if state.val < 960 then
                representativeTailChunk29 (state.val - 928)
              else
                representativeTailChunk30 (state.val - 960)
      else
        if state.val < 1152 then
          if state.val < 1056 then
            if state.val < 1024 then
              representativeTailChunk31 (state.val - 992)
            else
              representativeTailChunk32 (state.val - 1024)
          else
            if state.val < 1088 then
              representativeTailChunk33 (state.val - 1056)
            else
              if state.val < 1120 then
                representativeTailChunk34 (state.val - 1088)
              else
                representativeTailChunk35 (state.val - 1120)
        else
          if state.val < 1248 then
            if state.val < 1184 then
              representativeTailChunk36 (state.val - 1152)
            else
              if state.val < 1216 then
                representativeTailChunk37 (state.val - 1184)
              else
                representativeTailChunk38 (state.val - 1216)
          else
            if state.val < 1280 then
              representativeTailChunk39 (state.val - 1248)
            else
              if state.val < 1312 then
                representativeTailChunk40 (state.val - 1280)
              else
                representativeTailChunk41 (state.val - 1312)
  else
    if state.val < 2016 then
      if state.val < 1664 then
        if state.val < 1504 then
          if state.val < 1408 then
            if state.val < 1376 then
              representativeTailChunk42 (state.val - 1344)
            else
              representativeTailChunk43 (state.val - 1376)
          else
            if state.val < 1440 then
              representativeTailChunk44 (state.val - 1408)
            else
              if state.val < 1472 then
                representativeTailChunk45 (state.val - 1440)
              else
                representativeTailChunk46 (state.val - 1472)
        else
          if state.val < 1568 then
            if state.val < 1536 then
              representativeTailChunk47 (state.val - 1504)
            else
              representativeTailChunk48 (state.val - 1536)
          else
            if state.val < 1600 then
              representativeTailChunk49 (state.val - 1568)
            else
              if state.val < 1632 then
                representativeTailChunk50 (state.val - 1600)
              else
                representativeTailChunk51 (state.val - 1632)
      else
        if state.val < 1824 then
          if state.val < 1728 then
            if state.val < 1696 then
              representativeTailChunk52 (state.val - 1664)
            else
              representativeTailChunk53 (state.val - 1696)
          else
            if state.val < 1760 then
              representativeTailChunk54 (state.val - 1728)
            else
              if state.val < 1792 then
                representativeTailChunk55 (state.val - 1760)
              else
                representativeTailChunk56 (state.val - 1792)
        else
          if state.val < 1920 then
            if state.val < 1856 then
              representativeTailChunk57 (state.val - 1824)
            else
              if state.val < 1888 then
                representativeTailChunk58 (state.val - 1856)
              else
                representativeTailChunk59 (state.val - 1888)
          else
            if state.val < 1952 then
              representativeTailChunk60 (state.val - 1920)
            else
              if state.val < 1984 then
                representativeTailChunk61 (state.val - 1952)
              else
                representativeTailChunk62 (state.val - 1984)
    else
      if state.val < 2368 then
        if state.val < 2176 then
          if state.val < 2080 then
            if state.val < 2048 then
              representativeTailChunk63 (state.val - 2016)
            else
              representativeTailChunk64 (state.val - 2048)
          else
            if state.val < 2112 then
              representativeTailChunk65 (state.val - 2080)
            else
              if state.val < 2144 then
                representativeTailChunk66 (state.val - 2112)
              else
                representativeTailChunk67 (state.val - 2144)
        else
          if state.val < 2272 then
            if state.val < 2208 then
              representativeTailChunk68 (state.val - 2176)
            else
              if state.val < 2240 then
                representativeTailChunk69 (state.val - 2208)
              else
                representativeTailChunk70 (state.val - 2240)
          else
            if state.val < 2304 then
              representativeTailChunk71 (state.val - 2272)
            else
              if state.val < 2336 then
                representativeTailChunk72 (state.val - 2304)
              else
                representativeTailChunk73 (state.val - 2336)
      else
        if state.val < 2528 then
          if state.val < 2432 then
            if state.val < 2400 then
              representativeTailChunk74 (state.val - 2368)
            else
              representativeTailChunk75 (state.val - 2400)
          else
            if state.val < 2464 then
              representativeTailChunk76 (state.val - 2432)
            else
              if state.val < 2496 then
                representativeTailChunk77 (state.val - 2464)
              else
                representativeTailChunk78 (state.val - 2496)
        else
          if state.val < 2624 then
            if state.val < 2560 then
              representativeTailChunk79 (state.val - 2528)
            else
              if state.val < 2592 then
                representativeTailChunk80 (state.val - 2560)
              else
                representativeTailChunk81 (state.val - 2592)
          else
            if state.val < 2656 then
              representativeTailChunk82 (state.val - 2624)
            else
              if state.val < 2688 then
                representativeTailChunk83 (state.val - 2656)
              else
                representativeTailChunk84 (state.val - 2688)

end SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.Shards
