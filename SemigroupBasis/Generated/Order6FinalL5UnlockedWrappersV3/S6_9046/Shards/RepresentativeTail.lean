import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9046.Shards.RepresentativeTailPart00
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9046.Shards.RepresentativeTailPart01
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9046.Shards.RepresentativeTailPart02
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9046.Shards.RepresentativeTailPart03
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9046.Shards.RepresentativeTailPart04
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9046.Shards.RepresentativeTailPart05
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9046.Shards.RepresentativeTailPart06
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9046.Shards.RepresentativeTailPart07

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9046.Shards

def representativeTail (state : Fin 7782) :
    List (Fin 6) :=
  if state.val < 3904 then
    if state.val < 1952 then
      if state.val < 960 then
        if state.val < 480 then
          if state.val < 224 then
            if state.val < 96 then
              if state.val < 32 then
                representativeTailChunk0 state.val
              else
                if state.val < 64 then
                  representativeTailChunk1 (state.val - 32)
                else
                  representativeTailChunk2 (state.val - 64)
            else
              if state.val < 160 then
                if state.val < 128 then
                  representativeTailChunk3 (state.val - 96)
                else
                  representativeTailChunk4 (state.val - 128)
              else
                if state.val < 192 then
                  representativeTailChunk5 (state.val - 160)
                else
                  representativeTailChunk6 (state.val - 192)
          else
            if state.val < 352 then
              if state.val < 288 then
                if state.val < 256 then
                  representativeTailChunk7 (state.val - 224)
                else
                  representativeTailChunk8 (state.val - 256)
              else
                if state.val < 320 then
                  representativeTailChunk9 (state.val - 288)
                else
                  representativeTailChunk10 (state.val - 320)
            else
              if state.val < 416 then
                if state.val < 384 then
                  representativeTailChunk11 (state.val - 352)
                else
                  representativeTailChunk12 (state.val - 384)
              else
                if state.val < 448 then
                  representativeTailChunk13 (state.val - 416)
                else
                  representativeTailChunk14 (state.val - 448)
        else
          if state.val < 704 then
            if state.val < 576 then
              if state.val < 512 then
                representativeTailChunk15 (state.val - 480)
              else
                if state.val < 544 then
                  representativeTailChunk16 (state.val - 512)
                else
                  representativeTailChunk17 (state.val - 544)
            else
              if state.val < 640 then
                if state.val < 608 then
                  representativeTailChunk18 (state.val - 576)
                else
                  representativeTailChunk19 (state.val - 608)
              else
                if state.val < 672 then
                  representativeTailChunk20 (state.val - 640)
                else
                  representativeTailChunk21 (state.val - 672)
          else
            if state.val < 832 then
              if state.val < 768 then
                if state.val < 736 then
                  representativeTailChunk22 (state.val - 704)
                else
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
                  representativeTailChunk29 (state.val - 928)
      else
        if state.val < 1440 then
          if state.val < 1184 then
            if state.val < 1056 then
              if state.val < 992 then
                representativeTailChunk30 (state.val - 960)
              else
                if state.val < 1024 then
                  representativeTailChunk31 (state.val - 992)
                else
                  representativeTailChunk32 (state.val - 1024)
            else
              if state.val < 1120 then
                if state.val < 1088 then
                  representativeTailChunk33 (state.val - 1056)
                else
                  representativeTailChunk34 (state.val - 1088)
              else
                if state.val < 1152 then
                  representativeTailChunk35 (state.val - 1120)
                else
                  representativeTailChunk36 (state.val - 1152)
          else
            if state.val < 1312 then
              if state.val < 1248 then
                if state.val < 1216 then
                  representativeTailChunk37 (state.val - 1184)
                else
                  representativeTailChunk38 (state.val - 1216)
              else
                if state.val < 1280 then
                  representativeTailChunk39 (state.val - 1248)
                else
                  representativeTailChunk40 (state.val - 1280)
            else
              if state.val < 1376 then
                if state.val < 1344 then
                  representativeTailChunk41 (state.val - 1312)
                else
                  representativeTailChunk42 (state.val - 1344)
              else
                if state.val < 1408 then
                  representativeTailChunk43 (state.val - 1376)
                else
                  representativeTailChunk44 (state.val - 1408)
        else
          if state.val < 1696 then
            if state.val < 1568 then
              if state.val < 1504 then
                if state.val < 1472 then
                  representativeTailChunk45 (state.val - 1440)
                else
                  representativeTailChunk46 (state.val - 1472)
              else
                if state.val < 1536 then
                  representativeTailChunk47 (state.val - 1504)
                else
                  representativeTailChunk48 (state.val - 1536)
            else
              if state.val < 1632 then
                if state.val < 1600 then
                  representativeTailChunk49 (state.val - 1568)
                else
                  representativeTailChunk50 (state.val - 1600)
              else
                if state.val < 1664 then
                  representativeTailChunk51 (state.val - 1632)
                else
                  representativeTailChunk52 (state.val - 1664)
          else
            if state.val < 1824 then
              if state.val < 1760 then
                if state.val < 1728 then
                  representativeTailChunk53 (state.val - 1696)
                else
                  representativeTailChunk54 (state.val - 1728)
              else
                if state.val < 1792 then
                  representativeTailChunk55 (state.val - 1760)
                else
                  representativeTailChunk56 (state.val - 1792)
            else
              if state.val < 1888 then
                if state.val < 1856 then
                  representativeTailChunk57 (state.val - 1824)
                else
                  representativeTailChunk58 (state.val - 1856)
              else
                if state.val < 1920 then
                  representativeTailChunk59 (state.val - 1888)
                else
                  representativeTailChunk60 (state.val - 1920)
    else
      if state.val < 2912 then
        if state.val < 2432 then
          if state.val < 2176 then
            if state.val < 2048 then
              if state.val < 1984 then
                representativeTailChunk61 (state.val - 1952)
              else
                if state.val < 2016 then
                  representativeTailChunk62 (state.val - 1984)
                else
                  representativeTailChunk63 (state.val - 2016)
            else
              if state.val < 2112 then
                if state.val < 2080 then
                  representativeTailChunk64 (state.val - 2048)
                else
                  representativeTailChunk65 (state.val - 2080)
              else
                if state.val < 2144 then
                  representativeTailChunk66 (state.val - 2112)
                else
                  representativeTailChunk67 (state.val - 2144)
          else
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
          if state.val < 2656 then
            if state.val < 2528 then
              if state.val < 2464 then
                representativeTailChunk76 (state.val - 2432)
              else
                if state.val < 2496 then
                  representativeTailChunk77 (state.val - 2464)
                else
                  representativeTailChunk78 (state.val - 2496)
            else
              if state.val < 2592 then
                if state.val < 2560 then
                  representativeTailChunk79 (state.val - 2528)
                else
                  representativeTailChunk80 (state.val - 2560)
              else
                if state.val < 2624 then
                  representativeTailChunk81 (state.val - 2592)
                else
                  representativeTailChunk82 (state.val - 2624)
          else
            if state.val < 2784 then
              if state.val < 2720 then
                if state.val < 2688 then
                  representativeTailChunk83 (state.val - 2656)
                else
                  representativeTailChunk84 (state.val - 2688)
              else
                if state.val < 2752 then
                  representativeTailChunk85 (state.val - 2720)
                else
                  representativeTailChunk86 (state.val - 2752)
            else
              if state.val < 2848 then
                if state.val < 2816 then
                  representativeTailChunk87 (state.val - 2784)
                else
                  representativeTailChunk88 (state.val - 2816)
              else
                if state.val < 2880 then
                  representativeTailChunk89 (state.val - 2848)
                else
                  representativeTailChunk90 (state.val - 2880)
      else
        if state.val < 3392 then
          if state.val < 3136 then
            if state.val < 3008 then
              if state.val < 2944 then
                representativeTailChunk91 (state.val - 2912)
              else
                if state.val < 2976 then
                  representativeTailChunk92 (state.val - 2944)
                else
                  representativeTailChunk93 (state.val - 2976)
            else
              if state.val < 3072 then
                if state.val < 3040 then
                  representativeTailChunk94 (state.val - 3008)
                else
                  representativeTailChunk95 (state.val - 3040)
              else
                if state.val < 3104 then
                  representativeTailChunk96 (state.val - 3072)
                else
                  representativeTailChunk97 (state.val - 3104)
          else
            if state.val < 3264 then
              if state.val < 3200 then
                if state.val < 3168 then
                  representativeTailChunk98 (state.val - 3136)
                else
                  representativeTailChunk99 (state.val - 3168)
              else
                if state.val < 3232 then
                  representativeTailChunk100 (state.val - 3200)
                else
                  representativeTailChunk101 (state.val - 3232)
            else
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
          if state.val < 3648 then
            if state.val < 3520 then
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
            if state.val < 3776 then
              if state.val < 3712 then
                if state.val < 3680 then
                  representativeTailChunk114 (state.val - 3648)
                else
                  representativeTailChunk115 (state.val - 3680)
              else
                if state.val < 3744 then
                  representativeTailChunk116 (state.val - 3712)
                else
                  representativeTailChunk117 (state.val - 3744)
            else
              if state.val < 3840 then
                if state.val < 3808 then
                  representativeTailChunk118 (state.val - 3776)
                else
                  representativeTailChunk119 (state.val - 3808)
              else
                if state.val < 3872 then
                  representativeTailChunk120 (state.val - 3840)
                else
                  representativeTailChunk121 (state.val - 3872)
  else
    if state.val < 5856 then
      if state.val < 4864 then
        if state.val < 4384 then
          if state.val < 4128 then
            if state.val < 4000 then
              if state.val < 3936 then
                representativeTailChunk122 (state.val - 3904)
              else
                if state.val < 3968 then
                  representativeTailChunk123 (state.val - 3936)
                else
                  representativeTailChunk124 (state.val - 3968)
            else
              if state.val < 4064 then
                if state.val < 4032 then
                  representativeTailChunk125 (state.val - 4000)
                else
                  representativeTailChunk126 (state.val - 4032)
              else
                if state.val < 4096 then
                  representativeTailChunk127 (state.val - 4064)
                else
                  representativeTailChunk128 (state.val - 4096)
          else
            if state.val < 4256 then
              if state.val < 4192 then
                if state.val < 4160 then
                  representativeTailChunk129 (state.val - 4128)
                else
                  representativeTailChunk130 (state.val - 4160)
              else
                if state.val < 4224 then
                  representativeTailChunk131 (state.val - 4192)
                else
                  representativeTailChunk132 (state.val - 4224)
            else
              if state.val < 4320 then
                if state.val < 4288 then
                  representativeTailChunk133 (state.val - 4256)
                else
                  representativeTailChunk134 (state.val - 4288)
              else
                if state.val < 4352 then
                  representativeTailChunk135 (state.val - 4320)
                else
                  representativeTailChunk136 (state.val - 4352)
        else
          if state.val < 4608 then
            if state.val < 4480 then
              if state.val < 4416 then
                representativeTailChunk137 (state.val - 4384)
              else
                if state.val < 4448 then
                  representativeTailChunk138 (state.val - 4416)
                else
                  representativeTailChunk139 (state.val - 4448)
            else
              if state.val < 4544 then
                if state.val < 4512 then
                  representativeTailChunk140 (state.val - 4480)
                else
                  representativeTailChunk141 (state.val - 4512)
              else
                if state.val < 4576 then
                  representativeTailChunk142 (state.val - 4544)
                else
                  representativeTailChunk143 (state.val - 4576)
          else
            if state.val < 4736 then
              if state.val < 4672 then
                if state.val < 4640 then
                  representativeTailChunk144 (state.val - 4608)
                else
                  representativeTailChunk145 (state.val - 4640)
              else
                if state.val < 4704 then
                  representativeTailChunk146 (state.val - 4672)
                else
                  representativeTailChunk147 (state.val - 4704)
            else
              if state.val < 4800 then
                if state.val < 4768 then
                  representativeTailChunk148 (state.val - 4736)
                else
                  representativeTailChunk149 (state.val - 4768)
              else
                if state.val < 4832 then
                  representativeTailChunk150 (state.val - 4800)
                else
                  representativeTailChunk151 (state.val - 4832)
      else
        if state.val < 5344 then
          if state.val < 5088 then
            if state.val < 4960 then
              if state.val < 4896 then
                representativeTailChunk152 (state.val - 4864)
              else
                if state.val < 4928 then
                  representativeTailChunk153 (state.val - 4896)
                else
                  representativeTailChunk154 (state.val - 4928)
            else
              if state.val < 5024 then
                if state.val < 4992 then
                  representativeTailChunk155 (state.val - 4960)
                else
                  representativeTailChunk156 (state.val - 4992)
              else
                if state.val < 5056 then
                  representativeTailChunk157 (state.val - 5024)
                else
                  representativeTailChunk158 (state.val - 5056)
          else
            if state.val < 5216 then
              if state.val < 5152 then
                if state.val < 5120 then
                  representativeTailChunk159 (state.val - 5088)
                else
                  representativeTailChunk160 (state.val - 5120)
              else
                if state.val < 5184 then
                  representativeTailChunk161 (state.val - 5152)
                else
                  representativeTailChunk162 (state.val - 5184)
            else
              if state.val < 5280 then
                if state.val < 5248 then
                  representativeTailChunk163 (state.val - 5216)
                else
                  representativeTailChunk164 (state.val - 5248)
              else
                if state.val < 5312 then
                  representativeTailChunk165 (state.val - 5280)
                else
                  representativeTailChunk166 (state.val - 5312)
        else
          if state.val < 5600 then
            if state.val < 5472 then
              if state.val < 5408 then
                if state.val < 5376 then
                  representativeTailChunk167 (state.val - 5344)
                else
                  representativeTailChunk168 (state.val - 5376)
              else
                if state.val < 5440 then
                  representativeTailChunk169 (state.val - 5408)
                else
                  representativeTailChunk170 (state.val - 5440)
            else
              if state.val < 5536 then
                if state.val < 5504 then
                  representativeTailChunk171 (state.val - 5472)
                else
                  representativeTailChunk172 (state.val - 5504)
              else
                if state.val < 5568 then
                  representativeTailChunk173 (state.val - 5536)
                else
                  representativeTailChunk174 (state.val - 5568)
          else
            if state.val < 5728 then
              if state.val < 5664 then
                if state.val < 5632 then
                  representativeTailChunk175 (state.val - 5600)
                else
                  representativeTailChunk176 (state.val - 5632)
              else
                if state.val < 5696 then
                  representativeTailChunk177 (state.val - 5664)
                else
                  representativeTailChunk178 (state.val - 5696)
            else
              if state.val < 5792 then
                if state.val < 5760 then
                  representativeTailChunk179 (state.val - 5728)
                else
                  representativeTailChunk180 (state.val - 5760)
              else
                if state.val < 5824 then
                  representativeTailChunk181 (state.val - 5792)
                else
                  representativeTailChunk182 (state.val - 5824)
    else
      if state.val < 6816 then
        if state.val < 6336 then
          if state.val < 6080 then
            if state.val < 5952 then
              if state.val < 5888 then
                representativeTailChunk183 (state.val - 5856)
              else
                if state.val < 5920 then
                  representativeTailChunk184 (state.val - 5888)
                else
                  representativeTailChunk185 (state.val - 5920)
            else
              if state.val < 6016 then
                if state.val < 5984 then
                  representativeTailChunk186 (state.val - 5952)
                else
                  representativeTailChunk187 (state.val - 5984)
              else
                if state.val < 6048 then
                  representativeTailChunk188 (state.val - 6016)
                else
                  representativeTailChunk189 (state.val - 6048)
          else
            if state.val < 6208 then
              if state.val < 6144 then
                if state.val < 6112 then
                  representativeTailChunk190 (state.val - 6080)
                else
                  representativeTailChunk191 (state.val - 6112)
              else
                if state.val < 6176 then
                  representativeTailChunk192 (state.val - 6144)
                else
                  representativeTailChunk193 (state.val - 6176)
            else
              if state.val < 6272 then
                if state.val < 6240 then
                  representativeTailChunk194 (state.val - 6208)
                else
                  representativeTailChunk195 (state.val - 6240)
              else
                if state.val < 6304 then
                  representativeTailChunk196 (state.val - 6272)
                else
                  representativeTailChunk197 (state.val - 6304)
        else
          if state.val < 6560 then
            if state.val < 6432 then
              if state.val < 6368 then
                representativeTailChunk198 (state.val - 6336)
              else
                if state.val < 6400 then
                  representativeTailChunk199 (state.val - 6368)
                else
                  representativeTailChunk200 (state.val - 6400)
            else
              if state.val < 6496 then
                if state.val < 6464 then
                  representativeTailChunk201 (state.val - 6432)
                else
                  representativeTailChunk202 (state.val - 6464)
              else
                if state.val < 6528 then
                  representativeTailChunk203 (state.val - 6496)
                else
                  representativeTailChunk204 (state.val - 6528)
          else
            if state.val < 6688 then
              if state.val < 6624 then
                if state.val < 6592 then
                  representativeTailChunk205 (state.val - 6560)
                else
                  representativeTailChunk206 (state.val - 6592)
              else
                if state.val < 6656 then
                  representativeTailChunk207 (state.val - 6624)
                else
                  representativeTailChunk208 (state.val - 6656)
            else
              if state.val < 6752 then
                if state.val < 6720 then
                  representativeTailChunk209 (state.val - 6688)
                else
                  representativeTailChunk210 (state.val - 6720)
              else
                if state.val < 6784 then
                  representativeTailChunk211 (state.val - 6752)
                else
                  representativeTailChunk212 (state.val - 6784)
      else
        if state.val < 7296 then
          if state.val < 7040 then
            if state.val < 6912 then
              if state.val < 6848 then
                representativeTailChunk213 (state.val - 6816)
              else
                if state.val < 6880 then
                  representativeTailChunk214 (state.val - 6848)
                else
                  representativeTailChunk215 (state.val - 6880)
            else
              if state.val < 6976 then
                if state.val < 6944 then
                  representativeTailChunk216 (state.val - 6912)
                else
                  representativeTailChunk217 (state.val - 6944)
              else
                if state.val < 7008 then
                  representativeTailChunk218 (state.val - 6976)
                else
                  representativeTailChunk219 (state.val - 7008)
          else
            if state.val < 7168 then
              if state.val < 7104 then
                if state.val < 7072 then
                  representativeTailChunk220 (state.val - 7040)
                else
                  representativeTailChunk221 (state.val - 7072)
              else
                if state.val < 7136 then
                  representativeTailChunk222 (state.val - 7104)
                else
                  representativeTailChunk223 (state.val - 7136)
            else
              if state.val < 7232 then
                if state.val < 7200 then
                  representativeTailChunk224 (state.val - 7168)
                else
                  representativeTailChunk225 (state.val - 7200)
              else
                if state.val < 7264 then
                  representativeTailChunk226 (state.val - 7232)
                else
                  representativeTailChunk227 (state.val - 7264)
        else
          if state.val < 7552 then
            if state.val < 7424 then
              if state.val < 7360 then
                if state.val < 7328 then
                  representativeTailChunk228 (state.val - 7296)
                else
                  representativeTailChunk229 (state.val - 7328)
              else
                if state.val < 7392 then
                  representativeTailChunk230 (state.val - 7360)
                else
                  representativeTailChunk231 (state.val - 7392)
            else
              if state.val < 7488 then
                if state.val < 7456 then
                  representativeTailChunk232 (state.val - 7424)
                else
                  representativeTailChunk233 (state.val - 7456)
              else
                if state.val < 7520 then
                  representativeTailChunk234 (state.val - 7488)
                else
                  representativeTailChunk235 (state.val - 7520)
          else
            if state.val < 7680 then
              if state.val < 7616 then
                if state.val < 7584 then
                  representativeTailChunk236 (state.val - 7552)
                else
                  representativeTailChunk237 (state.val - 7584)
              else
                if state.val < 7648 then
                  representativeTailChunk238 (state.val - 7616)
                else
                  representativeTailChunk239 (state.val - 7648)
            else
              if state.val < 7744 then
                if state.val < 7712 then
                  representativeTailChunk240 (state.val - 7680)
                else
                  representativeTailChunk241 (state.val - 7712)
              else
                if state.val < 7776 then
                  representativeTailChunk242 (state.val - 7744)
                else
                  representativeTailChunk243 (state.val - 7776)

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9046.Shards
