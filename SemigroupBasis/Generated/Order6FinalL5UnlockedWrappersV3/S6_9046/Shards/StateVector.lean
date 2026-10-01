import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9046.Shards.StateVectorPart00
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9046.Shards.StateVectorPart01
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9046.Shards.StateVectorPart02
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9046.Shards.StateVectorPart03
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9046.Shards.StateVectorPart04
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9046.Shards.StateVectorPart05
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9046.Shards.StateVectorPart06
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9046.Shards.StateVectorPart07

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9046.Shards

def packedStateVectorCode (state : Fin 7782) : Nat :=
  if state.val < 3904 then
    if state.val < 1952 then
      if state.val < 960 then
        if state.val < 480 then
          if state.val < 224 then
            if state.val < 96 then
              if state.val < 32 then
                packedStateVectorCodeChunk0 state.val
              else
                if state.val < 64 then
                  packedStateVectorCodeChunk1 (state.val - 32)
                else
                  packedStateVectorCodeChunk2 (state.val - 64)
            else
              if state.val < 160 then
                if state.val < 128 then
                  packedStateVectorCodeChunk3 (state.val - 96)
                else
                  packedStateVectorCodeChunk4 (state.val - 128)
              else
                if state.val < 192 then
                  packedStateVectorCodeChunk5 (state.val - 160)
                else
                  packedStateVectorCodeChunk6 (state.val - 192)
          else
            if state.val < 352 then
              if state.val < 288 then
                if state.val < 256 then
                  packedStateVectorCodeChunk7 (state.val - 224)
                else
                  packedStateVectorCodeChunk8 (state.val - 256)
              else
                if state.val < 320 then
                  packedStateVectorCodeChunk9 (state.val - 288)
                else
                  packedStateVectorCodeChunk10 (state.val - 320)
            else
              if state.val < 416 then
                if state.val < 384 then
                  packedStateVectorCodeChunk11 (state.val - 352)
                else
                  packedStateVectorCodeChunk12 (state.val - 384)
              else
                if state.val < 448 then
                  packedStateVectorCodeChunk13 (state.val - 416)
                else
                  packedStateVectorCodeChunk14 (state.val - 448)
        else
          if state.val < 704 then
            if state.val < 576 then
              if state.val < 512 then
                packedStateVectorCodeChunk15 (state.val - 480)
              else
                if state.val < 544 then
                  packedStateVectorCodeChunk16 (state.val - 512)
                else
                  packedStateVectorCodeChunk17 (state.val - 544)
            else
              if state.val < 640 then
                if state.val < 608 then
                  packedStateVectorCodeChunk18 (state.val - 576)
                else
                  packedStateVectorCodeChunk19 (state.val - 608)
              else
                if state.val < 672 then
                  packedStateVectorCodeChunk20 (state.val - 640)
                else
                  packedStateVectorCodeChunk21 (state.val - 672)
          else
            if state.val < 832 then
              if state.val < 768 then
                if state.val < 736 then
                  packedStateVectorCodeChunk22 (state.val - 704)
                else
                  packedStateVectorCodeChunk23 (state.val - 736)
              else
                if state.val < 800 then
                  packedStateVectorCodeChunk24 (state.val - 768)
                else
                  packedStateVectorCodeChunk25 (state.val - 800)
            else
              if state.val < 896 then
                if state.val < 864 then
                  packedStateVectorCodeChunk26 (state.val - 832)
                else
                  packedStateVectorCodeChunk27 (state.val - 864)
              else
                if state.val < 928 then
                  packedStateVectorCodeChunk28 (state.val - 896)
                else
                  packedStateVectorCodeChunk29 (state.val - 928)
      else
        if state.val < 1440 then
          if state.val < 1184 then
            if state.val < 1056 then
              if state.val < 992 then
                packedStateVectorCodeChunk30 (state.val - 960)
              else
                if state.val < 1024 then
                  packedStateVectorCodeChunk31 (state.val - 992)
                else
                  packedStateVectorCodeChunk32 (state.val - 1024)
            else
              if state.val < 1120 then
                if state.val < 1088 then
                  packedStateVectorCodeChunk33 (state.val - 1056)
                else
                  packedStateVectorCodeChunk34 (state.val - 1088)
              else
                if state.val < 1152 then
                  packedStateVectorCodeChunk35 (state.val - 1120)
                else
                  packedStateVectorCodeChunk36 (state.val - 1152)
          else
            if state.val < 1312 then
              if state.val < 1248 then
                if state.val < 1216 then
                  packedStateVectorCodeChunk37 (state.val - 1184)
                else
                  packedStateVectorCodeChunk38 (state.val - 1216)
              else
                if state.val < 1280 then
                  packedStateVectorCodeChunk39 (state.val - 1248)
                else
                  packedStateVectorCodeChunk40 (state.val - 1280)
            else
              if state.val < 1376 then
                if state.val < 1344 then
                  packedStateVectorCodeChunk41 (state.val - 1312)
                else
                  packedStateVectorCodeChunk42 (state.val - 1344)
              else
                if state.val < 1408 then
                  packedStateVectorCodeChunk43 (state.val - 1376)
                else
                  packedStateVectorCodeChunk44 (state.val - 1408)
        else
          if state.val < 1696 then
            if state.val < 1568 then
              if state.val < 1504 then
                if state.val < 1472 then
                  packedStateVectorCodeChunk45 (state.val - 1440)
                else
                  packedStateVectorCodeChunk46 (state.val - 1472)
              else
                if state.val < 1536 then
                  packedStateVectorCodeChunk47 (state.val - 1504)
                else
                  packedStateVectorCodeChunk48 (state.val - 1536)
            else
              if state.val < 1632 then
                if state.val < 1600 then
                  packedStateVectorCodeChunk49 (state.val - 1568)
                else
                  packedStateVectorCodeChunk50 (state.val - 1600)
              else
                if state.val < 1664 then
                  packedStateVectorCodeChunk51 (state.val - 1632)
                else
                  packedStateVectorCodeChunk52 (state.val - 1664)
          else
            if state.val < 1824 then
              if state.val < 1760 then
                if state.val < 1728 then
                  packedStateVectorCodeChunk53 (state.val - 1696)
                else
                  packedStateVectorCodeChunk54 (state.val - 1728)
              else
                if state.val < 1792 then
                  packedStateVectorCodeChunk55 (state.val - 1760)
                else
                  packedStateVectorCodeChunk56 (state.val - 1792)
            else
              if state.val < 1888 then
                if state.val < 1856 then
                  packedStateVectorCodeChunk57 (state.val - 1824)
                else
                  packedStateVectorCodeChunk58 (state.val - 1856)
              else
                if state.val < 1920 then
                  packedStateVectorCodeChunk59 (state.val - 1888)
                else
                  packedStateVectorCodeChunk60 (state.val - 1920)
    else
      if state.val < 2912 then
        if state.val < 2432 then
          if state.val < 2176 then
            if state.val < 2048 then
              if state.val < 1984 then
                packedStateVectorCodeChunk61 (state.val - 1952)
              else
                if state.val < 2016 then
                  packedStateVectorCodeChunk62 (state.val - 1984)
                else
                  packedStateVectorCodeChunk63 (state.val - 2016)
            else
              if state.val < 2112 then
                if state.val < 2080 then
                  packedStateVectorCodeChunk64 (state.val - 2048)
                else
                  packedStateVectorCodeChunk65 (state.val - 2080)
              else
                if state.val < 2144 then
                  packedStateVectorCodeChunk66 (state.val - 2112)
                else
                  packedStateVectorCodeChunk67 (state.val - 2144)
          else
            if state.val < 2304 then
              if state.val < 2240 then
                if state.val < 2208 then
                  packedStateVectorCodeChunk68 (state.val - 2176)
                else
                  packedStateVectorCodeChunk69 (state.val - 2208)
              else
                if state.val < 2272 then
                  packedStateVectorCodeChunk70 (state.val - 2240)
                else
                  packedStateVectorCodeChunk71 (state.val - 2272)
            else
              if state.val < 2368 then
                if state.val < 2336 then
                  packedStateVectorCodeChunk72 (state.val - 2304)
                else
                  packedStateVectorCodeChunk73 (state.val - 2336)
              else
                if state.val < 2400 then
                  packedStateVectorCodeChunk74 (state.val - 2368)
                else
                  packedStateVectorCodeChunk75 (state.val - 2400)
        else
          if state.val < 2656 then
            if state.val < 2528 then
              if state.val < 2464 then
                packedStateVectorCodeChunk76 (state.val - 2432)
              else
                if state.val < 2496 then
                  packedStateVectorCodeChunk77 (state.val - 2464)
                else
                  packedStateVectorCodeChunk78 (state.val - 2496)
            else
              if state.val < 2592 then
                if state.val < 2560 then
                  packedStateVectorCodeChunk79 (state.val - 2528)
                else
                  packedStateVectorCodeChunk80 (state.val - 2560)
              else
                if state.val < 2624 then
                  packedStateVectorCodeChunk81 (state.val - 2592)
                else
                  packedStateVectorCodeChunk82 (state.val - 2624)
          else
            if state.val < 2784 then
              if state.val < 2720 then
                if state.val < 2688 then
                  packedStateVectorCodeChunk83 (state.val - 2656)
                else
                  packedStateVectorCodeChunk84 (state.val - 2688)
              else
                if state.val < 2752 then
                  packedStateVectorCodeChunk85 (state.val - 2720)
                else
                  packedStateVectorCodeChunk86 (state.val - 2752)
            else
              if state.val < 2848 then
                if state.val < 2816 then
                  packedStateVectorCodeChunk87 (state.val - 2784)
                else
                  packedStateVectorCodeChunk88 (state.val - 2816)
              else
                if state.val < 2880 then
                  packedStateVectorCodeChunk89 (state.val - 2848)
                else
                  packedStateVectorCodeChunk90 (state.val - 2880)
      else
        if state.val < 3392 then
          if state.val < 3136 then
            if state.val < 3008 then
              if state.val < 2944 then
                packedStateVectorCodeChunk91 (state.val - 2912)
              else
                if state.val < 2976 then
                  packedStateVectorCodeChunk92 (state.val - 2944)
                else
                  packedStateVectorCodeChunk93 (state.val - 2976)
            else
              if state.val < 3072 then
                if state.val < 3040 then
                  packedStateVectorCodeChunk94 (state.val - 3008)
                else
                  packedStateVectorCodeChunk95 (state.val - 3040)
              else
                if state.val < 3104 then
                  packedStateVectorCodeChunk96 (state.val - 3072)
                else
                  packedStateVectorCodeChunk97 (state.val - 3104)
          else
            if state.val < 3264 then
              if state.val < 3200 then
                if state.val < 3168 then
                  packedStateVectorCodeChunk98 (state.val - 3136)
                else
                  packedStateVectorCodeChunk99 (state.val - 3168)
              else
                if state.val < 3232 then
                  packedStateVectorCodeChunk100 (state.val - 3200)
                else
                  packedStateVectorCodeChunk101 (state.val - 3232)
            else
              if state.val < 3328 then
                if state.val < 3296 then
                  packedStateVectorCodeChunk102 (state.val - 3264)
                else
                  packedStateVectorCodeChunk103 (state.val - 3296)
              else
                if state.val < 3360 then
                  packedStateVectorCodeChunk104 (state.val - 3328)
                else
                  packedStateVectorCodeChunk105 (state.val - 3360)
        else
          if state.val < 3648 then
            if state.val < 3520 then
              if state.val < 3456 then
                if state.val < 3424 then
                  packedStateVectorCodeChunk106 (state.val - 3392)
                else
                  packedStateVectorCodeChunk107 (state.val - 3424)
              else
                if state.val < 3488 then
                  packedStateVectorCodeChunk108 (state.val - 3456)
                else
                  packedStateVectorCodeChunk109 (state.val - 3488)
            else
              if state.val < 3584 then
                if state.val < 3552 then
                  packedStateVectorCodeChunk110 (state.val - 3520)
                else
                  packedStateVectorCodeChunk111 (state.val - 3552)
              else
                if state.val < 3616 then
                  packedStateVectorCodeChunk112 (state.val - 3584)
                else
                  packedStateVectorCodeChunk113 (state.val - 3616)
          else
            if state.val < 3776 then
              if state.val < 3712 then
                if state.val < 3680 then
                  packedStateVectorCodeChunk114 (state.val - 3648)
                else
                  packedStateVectorCodeChunk115 (state.val - 3680)
              else
                if state.val < 3744 then
                  packedStateVectorCodeChunk116 (state.val - 3712)
                else
                  packedStateVectorCodeChunk117 (state.val - 3744)
            else
              if state.val < 3840 then
                if state.val < 3808 then
                  packedStateVectorCodeChunk118 (state.val - 3776)
                else
                  packedStateVectorCodeChunk119 (state.val - 3808)
              else
                if state.val < 3872 then
                  packedStateVectorCodeChunk120 (state.val - 3840)
                else
                  packedStateVectorCodeChunk121 (state.val - 3872)
  else
    if state.val < 5856 then
      if state.val < 4864 then
        if state.val < 4384 then
          if state.val < 4128 then
            if state.val < 4000 then
              if state.val < 3936 then
                packedStateVectorCodeChunk122 (state.val - 3904)
              else
                if state.val < 3968 then
                  packedStateVectorCodeChunk123 (state.val - 3936)
                else
                  packedStateVectorCodeChunk124 (state.val - 3968)
            else
              if state.val < 4064 then
                if state.val < 4032 then
                  packedStateVectorCodeChunk125 (state.val - 4000)
                else
                  packedStateVectorCodeChunk126 (state.val - 4032)
              else
                if state.val < 4096 then
                  packedStateVectorCodeChunk127 (state.val - 4064)
                else
                  packedStateVectorCodeChunk128 (state.val - 4096)
          else
            if state.val < 4256 then
              if state.val < 4192 then
                if state.val < 4160 then
                  packedStateVectorCodeChunk129 (state.val - 4128)
                else
                  packedStateVectorCodeChunk130 (state.val - 4160)
              else
                if state.val < 4224 then
                  packedStateVectorCodeChunk131 (state.val - 4192)
                else
                  packedStateVectorCodeChunk132 (state.val - 4224)
            else
              if state.val < 4320 then
                if state.val < 4288 then
                  packedStateVectorCodeChunk133 (state.val - 4256)
                else
                  packedStateVectorCodeChunk134 (state.val - 4288)
              else
                if state.val < 4352 then
                  packedStateVectorCodeChunk135 (state.val - 4320)
                else
                  packedStateVectorCodeChunk136 (state.val - 4352)
        else
          if state.val < 4608 then
            if state.val < 4480 then
              if state.val < 4416 then
                packedStateVectorCodeChunk137 (state.val - 4384)
              else
                if state.val < 4448 then
                  packedStateVectorCodeChunk138 (state.val - 4416)
                else
                  packedStateVectorCodeChunk139 (state.val - 4448)
            else
              if state.val < 4544 then
                if state.val < 4512 then
                  packedStateVectorCodeChunk140 (state.val - 4480)
                else
                  packedStateVectorCodeChunk141 (state.val - 4512)
              else
                if state.val < 4576 then
                  packedStateVectorCodeChunk142 (state.val - 4544)
                else
                  packedStateVectorCodeChunk143 (state.val - 4576)
          else
            if state.val < 4736 then
              if state.val < 4672 then
                if state.val < 4640 then
                  packedStateVectorCodeChunk144 (state.val - 4608)
                else
                  packedStateVectorCodeChunk145 (state.val - 4640)
              else
                if state.val < 4704 then
                  packedStateVectorCodeChunk146 (state.val - 4672)
                else
                  packedStateVectorCodeChunk147 (state.val - 4704)
            else
              if state.val < 4800 then
                if state.val < 4768 then
                  packedStateVectorCodeChunk148 (state.val - 4736)
                else
                  packedStateVectorCodeChunk149 (state.val - 4768)
              else
                if state.val < 4832 then
                  packedStateVectorCodeChunk150 (state.val - 4800)
                else
                  packedStateVectorCodeChunk151 (state.val - 4832)
      else
        if state.val < 5344 then
          if state.val < 5088 then
            if state.val < 4960 then
              if state.val < 4896 then
                packedStateVectorCodeChunk152 (state.val - 4864)
              else
                if state.val < 4928 then
                  packedStateVectorCodeChunk153 (state.val - 4896)
                else
                  packedStateVectorCodeChunk154 (state.val - 4928)
            else
              if state.val < 5024 then
                if state.val < 4992 then
                  packedStateVectorCodeChunk155 (state.val - 4960)
                else
                  packedStateVectorCodeChunk156 (state.val - 4992)
              else
                if state.val < 5056 then
                  packedStateVectorCodeChunk157 (state.val - 5024)
                else
                  packedStateVectorCodeChunk158 (state.val - 5056)
          else
            if state.val < 5216 then
              if state.val < 5152 then
                if state.val < 5120 then
                  packedStateVectorCodeChunk159 (state.val - 5088)
                else
                  packedStateVectorCodeChunk160 (state.val - 5120)
              else
                if state.val < 5184 then
                  packedStateVectorCodeChunk161 (state.val - 5152)
                else
                  packedStateVectorCodeChunk162 (state.val - 5184)
            else
              if state.val < 5280 then
                if state.val < 5248 then
                  packedStateVectorCodeChunk163 (state.val - 5216)
                else
                  packedStateVectorCodeChunk164 (state.val - 5248)
              else
                if state.val < 5312 then
                  packedStateVectorCodeChunk165 (state.val - 5280)
                else
                  packedStateVectorCodeChunk166 (state.val - 5312)
        else
          if state.val < 5600 then
            if state.val < 5472 then
              if state.val < 5408 then
                if state.val < 5376 then
                  packedStateVectorCodeChunk167 (state.val - 5344)
                else
                  packedStateVectorCodeChunk168 (state.val - 5376)
              else
                if state.val < 5440 then
                  packedStateVectorCodeChunk169 (state.val - 5408)
                else
                  packedStateVectorCodeChunk170 (state.val - 5440)
            else
              if state.val < 5536 then
                if state.val < 5504 then
                  packedStateVectorCodeChunk171 (state.val - 5472)
                else
                  packedStateVectorCodeChunk172 (state.val - 5504)
              else
                if state.val < 5568 then
                  packedStateVectorCodeChunk173 (state.val - 5536)
                else
                  packedStateVectorCodeChunk174 (state.val - 5568)
          else
            if state.val < 5728 then
              if state.val < 5664 then
                if state.val < 5632 then
                  packedStateVectorCodeChunk175 (state.val - 5600)
                else
                  packedStateVectorCodeChunk176 (state.val - 5632)
              else
                if state.val < 5696 then
                  packedStateVectorCodeChunk177 (state.val - 5664)
                else
                  packedStateVectorCodeChunk178 (state.val - 5696)
            else
              if state.val < 5792 then
                if state.val < 5760 then
                  packedStateVectorCodeChunk179 (state.val - 5728)
                else
                  packedStateVectorCodeChunk180 (state.val - 5760)
              else
                if state.val < 5824 then
                  packedStateVectorCodeChunk181 (state.val - 5792)
                else
                  packedStateVectorCodeChunk182 (state.val - 5824)
    else
      if state.val < 6816 then
        if state.val < 6336 then
          if state.val < 6080 then
            if state.val < 5952 then
              if state.val < 5888 then
                packedStateVectorCodeChunk183 (state.val - 5856)
              else
                if state.val < 5920 then
                  packedStateVectorCodeChunk184 (state.val - 5888)
                else
                  packedStateVectorCodeChunk185 (state.val - 5920)
            else
              if state.val < 6016 then
                if state.val < 5984 then
                  packedStateVectorCodeChunk186 (state.val - 5952)
                else
                  packedStateVectorCodeChunk187 (state.val - 5984)
              else
                if state.val < 6048 then
                  packedStateVectorCodeChunk188 (state.val - 6016)
                else
                  packedStateVectorCodeChunk189 (state.val - 6048)
          else
            if state.val < 6208 then
              if state.val < 6144 then
                if state.val < 6112 then
                  packedStateVectorCodeChunk190 (state.val - 6080)
                else
                  packedStateVectorCodeChunk191 (state.val - 6112)
              else
                if state.val < 6176 then
                  packedStateVectorCodeChunk192 (state.val - 6144)
                else
                  packedStateVectorCodeChunk193 (state.val - 6176)
            else
              if state.val < 6272 then
                if state.val < 6240 then
                  packedStateVectorCodeChunk194 (state.val - 6208)
                else
                  packedStateVectorCodeChunk195 (state.val - 6240)
              else
                if state.val < 6304 then
                  packedStateVectorCodeChunk196 (state.val - 6272)
                else
                  packedStateVectorCodeChunk197 (state.val - 6304)
        else
          if state.val < 6560 then
            if state.val < 6432 then
              if state.val < 6368 then
                packedStateVectorCodeChunk198 (state.val - 6336)
              else
                if state.val < 6400 then
                  packedStateVectorCodeChunk199 (state.val - 6368)
                else
                  packedStateVectorCodeChunk200 (state.val - 6400)
            else
              if state.val < 6496 then
                if state.val < 6464 then
                  packedStateVectorCodeChunk201 (state.val - 6432)
                else
                  packedStateVectorCodeChunk202 (state.val - 6464)
              else
                if state.val < 6528 then
                  packedStateVectorCodeChunk203 (state.val - 6496)
                else
                  packedStateVectorCodeChunk204 (state.val - 6528)
          else
            if state.val < 6688 then
              if state.val < 6624 then
                if state.val < 6592 then
                  packedStateVectorCodeChunk205 (state.val - 6560)
                else
                  packedStateVectorCodeChunk206 (state.val - 6592)
              else
                if state.val < 6656 then
                  packedStateVectorCodeChunk207 (state.val - 6624)
                else
                  packedStateVectorCodeChunk208 (state.val - 6656)
            else
              if state.val < 6752 then
                if state.val < 6720 then
                  packedStateVectorCodeChunk209 (state.val - 6688)
                else
                  packedStateVectorCodeChunk210 (state.val - 6720)
              else
                if state.val < 6784 then
                  packedStateVectorCodeChunk211 (state.val - 6752)
                else
                  packedStateVectorCodeChunk212 (state.val - 6784)
      else
        if state.val < 7296 then
          if state.val < 7040 then
            if state.val < 6912 then
              if state.val < 6848 then
                packedStateVectorCodeChunk213 (state.val - 6816)
              else
                if state.val < 6880 then
                  packedStateVectorCodeChunk214 (state.val - 6848)
                else
                  packedStateVectorCodeChunk215 (state.val - 6880)
            else
              if state.val < 6976 then
                if state.val < 6944 then
                  packedStateVectorCodeChunk216 (state.val - 6912)
                else
                  packedStateVectorCodeChunk217 (state.val - 6944)
              else
                if state.val < 7008 then
                  packedStateVectorCodeChunk218 (state.val - 6976)
                else
                  packedStateVectorCodeChunk219 (state.val - 7008)
          else
            if state.val < 7168 then
              if state.val < 7104 then
                if state.val < 7072 then
                  packedStateVectorCodeChunk220 (state.val - 7040)
                else
                  packedStateVectorCodeChunk221 (state.val - 7072)
              else
                if state.val < 7136 then
                  packedStateVectorCodeChunk222 (state.val - 7104)
                else
                  packedStateVectorCodeChunk223 (state.val - 7136)
            else
              if state.val < 7232 then
                if state.val < 7200 then
                  packedStateVectorCodeChunk224 (state.val - 7168)
                else
                  packedStateVectorCodeChunk225 (state.val - 7200)
              else
                if state.val < 7264 then
                  packedStateVectorCodeChunk226 (state.val - 7232)
                else
                  packedStateVectorCodeChunk227 (state.val - 7264)
        else
          if state.val < 7552 then
            if state.val < 7424 then
              if state.val < 7360 then
                if state.val < 7328 then
                  packedStateVectorCodeChunk228 (state.val - 7296)
                else
                  packedStateVectorCodeChunk229 (state.val - 7328)
              else
                if state.val < 7392 then
                  packedStateVectorCodeChunk230 (state.val - 7360)
                else
                  packedStateVectorCodeChunk231 (state.val - 7392)
            else
              if state.val < 7488 then
                if state.val < 7456 then
                  packedStateVectorCodeChunk232 (state.val - 7424)
                else
                  packedStateVectorCodeChunk233 (state.val - 7456)
              else
                if state.val < 7520 then
                  packedStateVectorCodeChunk234 (state.val - 7488)
                else
                  packedStateVectorCodeChunk235 (state.val - 7520)
          else
            if state.val < 7680 then
              if state.val < 7616 then
                if state.val < 7584 then
                  packedStateVectorCodeChunk236 (state.val - 7552)
                else
                  packedStateVectorCodeChunk237 (state.val - 7584)
              else
                if state.val < 7648 then
                  packedStateVectorCodeChunk238 (state.val - 7616)
                else
                  packedStateVectorCodeChunk239 (state.val - 7648)
            else
              if state.val < 7744 then
                if state.val < 7712 then
                  packedStateVectorCodeChunk240 (state.val - 7680)
                else
                  packedStateVectorCodeChunk241 (state.val - 7712)
              else
                if state.val < 7776 then
                  packedStateVectorCodeChunk242 (state.val - 7744)
                else
                  packedStateVectorCodeChunk243 (state.val - 7776)

def stateVector (state : Fin 7782)
    (coordinate : Fin 23) : Fin 6 :=
  ⟨(packedStateVectorCode state / 6 ^ coordinate.val) % 6,
    Nat.mod_lt _ (by decide)⟩

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9046.Shards
