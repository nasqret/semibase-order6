import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6984.Shards.RepresentativeTailPart00
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6984.Shards.RepresentativeTailPart01
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6984.Shards.RepresentativeTailPart02
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6984.Shards.RepresentativeTailPart03
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6984.Shards.RepresentativeTailPart04

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6984.Shards

def representativeTail (state : Fin 4374) :
    List (Fin 6) :=
  if state.val < 2176 then
    if state.val < 1088 then
      if state.val < 544 then
        if state.val < 256 then
          if state.val < 128 then
            if state.val < 64 then
              if state.val < 32 then
                representativeTailChunk0 state.val
              else
                representativeTailChunk1 (state.val - 32)
            else
              if state.val < 96 then
                representativeTailChunk2 (state.val - 64)
              else
                representativeTailChunk3 (state.val - 96)
          else
            if state.val < 192 then
              if state.val < 160 then
                representativeTailChunk4 (state.val - 128)
              else
                representativeTailChunk5 (state.val - 160)
            else
              if state.val < 224 then
                representativeTailChunk6 (state.val - 192)
              else
                representativeTailChunk7 (state.val - 224)
        else
          if state.val < 384 then
            if state.val < 320 then
              if state.val < 288 then
                representativeTailChunk8 (state.val - 256)
              else
                representativeTailChunk9 (state.val - 288)
            else
              if state.val < 352 then
                representativeTailChunk10 (state.val - 320)
              else
                representativeTailChunk11 (state.val - 352)
          else
            if state.val < 448 then
              if state.val < 416 then
                representativeTailChunk12 (state.val - 384)
              else
                representativeTailChunk13 (state.val - 416)
            else
              if state.val < 480 then
                representativeTailChunk14 (state.val - 448)
              else
                if state.val < 512 then
                  representativeTailChunk15 (state.val - 480)
                else
                  representativeTailChunk16 (state.val - 512)
      else
        if state.val < 800 then
          if state.val < 672 then
            if state.val < 608 then
              if state.val < 576 then
                representativeTailChunk17 (state.val - 544)
              else
                representativeTailChunk18 (state.val - 576)
            else
              if state.val < 640 then
                representativeTailChunk19 (state.val - 608)
              else
                representativeTailChunk20 (state.val - 640)
          else
            if state.val < 736 then
              if state.val < 704 then
                representativeTailChunk21 (state.val - 672)
              else
                representativeTailChunk22 (state.val - 704)
            else
              if state.val < 768 then
                representativeTailChunk23 (state.val - 736)
              else
                representativeTailChunk24 (state.val - 768)
        else
          if state.val < 928 then
            if state.val < 864 then
              if state.val < 832 then
                representativeTailChunk25 (state.val - 800)
              else
                representativeTailChunk26 (state.val - 832)
            else
              if state.val < 896 then
                representativeTailChunk27 (state.val - 864)
              else
                representativeTailChunk28 (state.val - 896)
          else
            if state.val < 992 then
              if state.val < 960 then
                representativeTailChunk29 (state.val - 928)
              else
                representativeTailChunk30 (state.val - 960)
            else
              if state.val < 1024 then
                representativeTailChunk31 (state.val - 992)
              else
                if state.val < 1056 then
                  representativeTailChunk32 (state.val - 1024)
                else
                  representativeTailChunk33 (state.val - 1056)
    else
      if state.val < 1632 then
        if state.val < 1344 then
          if state.val < 1216 then
            if state.val < 1152 then
              if state.val < 1120 then
                representativeTailChunk34 (state.val - 1088)
              else
                representativeTailChunk35 (state.val - 1120)
            else
              if state.val < 1184 then
                representativeTailChunk36 (state.val - 1152)
              else
                representativeTailChunk37 (state.val - 1184)
          else
            if state.val < 1280 then
              if state.val < 1248 then
                representativeTailChunk38 (state.val - 1216)
              else
                representativeTailChunk39 (state.val - 1248)
            else
              if state.val < 1312 then
                representativeTailChunk40 (state.val - 1280)
              else
                representativeTailChunk41 (state.val - 1312)
        else
          if state.val < 1472 then
            if state.val < 1408 then
              if state.val < 1376 then
                representativeTailChunk42 (state.val - 1344)
              else
                representativeTailChunk43 (state.val - 1376)
            else
              if state.val < 1440 then
                representativeTailChunk44 (state.val - 1408)
              else
                representativeTailChunk45 (state.val - 1440)
          else
            if state.val < 1536 then
              if state.val < 1504 then
                representativeTailChunk46 (state.val - 1472)
              else
                representativeTailChunk47 (state.val - 1504)
            else
              if state.val < 1568 then
                representativeTailChunk48 (state.val - 1536)
              else
                if state.val < 1600 then
                  representativeTailChunk49 (state.val - 1568)
                else
                  representativeTailChunk50 (state.val - 1600)
      else
        if state.val < 1888 then
          if state.val < 1760 then
            if state.val < 1696 then
              if state.val < 1664 then
                representativeTailChunk51 (state.val - 1632)
              else
                representativeTailChunk52 (state.val - 1664)
            else
              if state.val < 1728 then
                representativeTailChunk53 (state.val - 1696)
              else
                representativeTailChunk54 (state.val - 1728)
          else
            if state.val < 1824 then
              if state.val < 1792 then
                representativeTailChunk55 (state.val - 1760)
              else
                representativeTailChunk56 (state.val - 1792)
            else
              if state.val < 1856 then
                representativeTailChunk57 (state.val - 1824)
              else
                representativeTailChunk58 (state.val - 1856)
        else
          if state.val < 2016 then
            if state.val < 1952 then
              if state.val < 1920 then
                representativeTailChunk59 (state.val - 1888)
              else
                representativeTailChunk60 (state.val - 1920)
            else
              if state.val < 1984 then
                representativeTailChunk61 (state.val - 1952)
              else
                representativeTailChunk62 (state.val - 1984)
          else
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
    if state.val < 3264 then
      if state.val < 2720 then
        if state.val < 2432 then
          if state.val < 2304 then
            if state.val < 2240 then
              if state.val < 2208 then
                representativeTailChunk68 (state.val - 2176)
              else
                representativeTailChunk69 (state.val - 2208)
            else
              if state.val < 2272 then
                representativeTailChunk70 (state.val - 2240)
              else
                representativeTailChunk71 (state.val - 2272)
          else
            if state.val < 2368 then
              if state.val < 2336 then
                representativeTailChunk72 (state.val - 2304)
              else
                representativeTailChunk73 (state.val - 2336)
            else
              if state.val < 2400 then
                representativeTailChunk74 (state.val - 2368)
              else
                representativeTailChunk75 (state.val - 2400)
        else
          if state.val < 2560 then
            if state.val < 2496 then
              if state.val < 2464 then
                representativeTailChunk76 (state.val - 2432)
              else
                representativeTailChunk77 (state.val - 2464)
            else
              if state.val < 2528 then
                representativeTailChunk78 (state.val - 2496)
              else
                representativeTailChunk79 (state.val - 2528)
          else
            if state.val < 2624 then
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
      else
        if state.val < 2976 then
          if state.val < 2848 then
            if state.val < 2784 then
              if state.val < 2752 then
                representativeTailChunk85 (state.val - 2720)
              else
                representativeTailChunk86 (state.val - 2752)
            else
              if state.val < 2816 then
                representativeTailChunk87 (state.val - 2784)
              else
                representativeTailChunk88 (state.val - 2816)
          else
            if state.val < 2912 then
              if state.val < 2880 then
                representativeTailChunk89 (state.val - 2848)
              else
                representativeTailChunk90 (state.val - 2880)
            else
              if state.val < 2944 then
                representativeTailChunk91 (state.val - 2912)
              else
                representativeTailChunk92 (state.val - 2944)
        else
          if state.val < 3104 then
            if state.val < 3040 then
              if state.val < 3008 then
                representativeTailChunk93 (state.val - 2976)
              else
                representativeTailChunk94 (state.val - 3008)
            else
              if state.val < 3072 then
                representativeTailChunk95 (state.val - 3040)
              else
                representativeTailChunk96 (state.val - 3072)
          else
            if state.val < 3168 then
              if state.val < 3136 then
                representativeTailChunk97 (state.val - 3104)
              else
                representativeTailChunk98 (state.val - 3136)
            else
              if state.val < 3200 then
                representativeTailChunk99 (state.val - 3168)
              else
                if state.val < 3232 then
                  representativeTailChunk100 (state.val - 3200)
                else
                  representativeTailChunk101 (state.val - 3232)
    else
      if state.val < 3808 then
        if state.val < 3520 then
          if state.val < 3392 then
            if state.val < 3328 then
              if state.val < 3296 then
                representativeTailChunk102 (state.val - 3264)
              else
                representativeTailChunk103 (state.val - 3296)
            else
              if state.val < 3360 then
                representativeTailChunk104 (state.val - 3328)
              else
                representativeTailChunk105 (state.val - 3360)
          else
            if state.val < 3456 then
              if state.val < 3424 then
                representativeTailChunk106 (state.val - 3392)
              else
                representativeTailChunk107 (state.val - 3424)
            else
              if state.val < 3488 then
                representativeTailChunk108 (state.val - 3456)
              else
                representativeTailChunk109 (state.val - 3488)
        else
          if state.val < 3648 then
            if state.val < 3584 then
              if state.val < 3552 then
                representativeTailChunk110 (state.val - 3520)
              else
                representativeTailChunk111 (state.val - 3552)
            else
              if state.val < 3616 then
                representativeTailChunk112 (state.val - 3584)
              else
                representativeTailChunk113 (state.val - 3616)
          else
            if state.val < 3712 then
              if state.val < 3680 then
                representativeTailChunk114 (state.val - 3648)
              else
                representativeTailChunk115 (state.val - 3680)
            else
              if state.val < 3744 then
                representativeTailChunk116 (state.val - 3712)
              else
                if state.val < 3776 then
                  representativeTailChunk117 (state.val - 3744)
                else
                  representativeTailChunk118 (state.val - 3776)
      else
        if state.val < 4096 then
          if state.val < 3936 then
            if state.val < 3872 then
              if state.val < 3840 then
                representativeTailChunk119 (state.val - 3808)
              else
                representativeTailChunk120 (state.val - 3840)
            else
              if state.val < 3904 then
                representativeTailChunk121 (state.val - 3872)
              else
                representativeTailChunk122 (state.val - 3904)
          else
            if state.val < 4000 then
              if state.val < 3968 then
                representativeTailChunk123 (state.val - 3936)
              else
                representativeTailChunk124 (state.val - 3968)
            else
              if state.val < 4032 then
                representativeTailChunk125 (state.val - 4000)
              else
                if state.val < 4064 then
                  representativeTailChunk126 (state.val - 4032)
                else
                  representativeTailChunk127 (state.val - 4064)
        else
          if state.val < 4224 then
            if state.val < 4160 then
              if state.val < 4128 then
                representativeTailChunk128 (state.val - 4096)
              else
                representativeTailChunk129 (state.val - 4128)
            else
              if state.val < 4192 then
                representativeTailChunk130 (state.val - 4160)
              else
                representativeTailChunk131 (state.val - 4192)
          else
            if state.val < 4288 then
              if state.val < 4256 then
                representativeTailChunk132 (state.val - 4224)
              else
                representativeTailChunk133 (state.val - 4256)
            else
              if state.val < 4320 then
                representativeTailChunk134 (state.val - 4288)
              else
                if state.val < 4352 then
                  representativeTailChunk135 (state.val - 4320)
                else
                  representativeTailChunk136 (state.val - 4352)

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6984.Shards
