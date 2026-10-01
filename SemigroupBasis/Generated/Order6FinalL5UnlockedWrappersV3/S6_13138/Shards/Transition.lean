import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.Shards.TransitionPart00
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.Shards.TransitionPart01
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.Shards.TransitionPart02
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.Shards.TransitionPart03
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.Shards.TransitionPart04
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.Shards.TransitionPart05
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.Shards.TransitionPart06
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.Shards.TransitionPart07
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.Shards.TransitionPart08
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.Shards.TransitionPart09
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.Shards.TransitionPart10
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.Shards.TransitionPart11

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.Shards

def packedTransitionCode (state : Fin 11742) : Nat :=
  if state.val < 5856 then
    if state.val < 2912 then
      if state.val < 1440 then
        if state.val < 704 then
          if state.val < 352 then
            if state.val < 160 then
              if state.val < 64 then
                if state.val < 32 then
                  packedTransitionCodeChunk0 state.val
                else
                  packedTransitionCodeChunk1 (state.val - 32)
              else
                if state.val < 96 then
                  packedTransitionCodeChunk2 (state.val - 64)
                else
                  if state.val < 128 then
                    packedTransitionCodeChunk3 (state.val - 96)
                  else
                    packedTransitionCodeChunk4 (state.val - 128)
            else
              if state.val < 256 then
                if state.val < 192 then
                  packedTransitionCodeChunk5 (state.val - 160)
                else
                  if state.val < 224 then
                    packedTransitionCodeChunk6 (state.val - 192)
                  else
                    packedTransitionCodeChunk7 (state.val - 224)
              else
                if state.val < 288 then
                  packedTransitionCodeChunk8 (state.val - 256)
                else
                  if state.val < 320 then
                    packedTransitionCodeChunk9 (state.val - 288)
                  else
                    packedTransitionCodeChunk10 (state.val - 320)
          else
            if state.val < 512 then
              if state.val < 416 then
                if state.val < 384 then
                  packedTransitionCodeChunk11 (state.val - 352)
                else
                  packedTransitionCodeChunk12 (state.val - 384)
              else
                if state.val < 448 then
                  packedTransitionCodeChunk13 (state.val - 416)
                else
                  if state.val < 480 then
                    packedTransitionCodeChunk14 (state.val - 448)
                  else
                    packedTransitionCodeChunk15 (state.val - 480)
            else
              if state.val < 608 then
                if state.val < 544 then
                  packedTransitionCodeChunk16 (state.val - 512)
                else
                  if state.val < 576 then
                    packedTransitionCodeChunk17 (state.val - 544)
                  else
                    packedTransitionCodeChunk18 (state.val - 576)
              else
                if state.val < 640 then
                  packedTransitionCodeChunk19 (state.val - 608)
                else
                  if state.val < 672 then
                    packedTransitionCodeChunk20 (state.val - 640)
                  else
                    packedTransitionCodeChunk21 (state.val - 672)
        else
          if state.val < 1056 then
            if state.val < 864 then
              if state.val < 768 then
                if state.val < 736 then
                  packedTransitionCodeChunk22 (state.val - 704)
                else
                  packedTransitionCodeChunk23 (state.val - 736)
              else
                if state.val < 800 then
                  packedTransitionCodeChunk24 (state.val - 768)
                else
                  if state.val < 832 then
                    packedTransitionCodeChunk25 (state.val - 800)
                  else
                    packedTransitionCodeChunk26 (state.val - 832)
            else
              if state.val < 960 then
                if state.val < 896 then
                  packedTransitionCodeChunk27 (state.val - 864)
                else
                  if state.val < 928 then
                    packedTransitionCodeChunk28 (state.val - 896)
                  else
                    packedTransitionCodeChunk29 (state.val - 928)
              else
                if state.val < 992 then
                  packedTransitionCodeChunk30 (state.val - 960)
                else
                  if state.val < 1024 then
                    packedTransitionCodeChunk31 (state.val - 992)
                  else
                    packedTransitionCodeChunk32 (state.val - 1024)
          else
            if state.val < 1248 then
              if state.val < 1152 then
                if state.val < 1088 then
                  packedTransitionCodeChunk33 (state.val - 1056)
                else
                  if state.val < 1120 then
                    packedTransitionCodeChunk34 (state.val - 1088)
                  else
                    packedTransitionCodeChunk35 (state.val - 1120)
              else
                if state.val < 1184 then
                  packedTransitionCodeChunk36 (state.val - 1152)
                else
                  if state.val < 1216 then
                    packedTransitionCodeChunk37 (state.val - 1184)
                  else
                    packedTransitionCodeChunk38 (state.val - 1216)
            else
              if state.val < 1344 then
                if state.val < 1280 then
                  packedTransitionCodeChunk39 (state.val - 1248)
                else
                  if state.val < 1312 then
                    packedTransitionCodeChunk40 (state.val - 1280)
                  else
                    packedTransitionCodeChunk41 (state.val - 1312)
              else
                if state.val < 1376 then
                  packedTransitionCodeChunk42 (state.val - 1344)
                else
                  if state.val < 1408 then
                    packedTransitionCodeChunk43 (state.val - 1376)
                  else
                    packedTransitionCodeChunk44 (state.val - 1408)
      else
        if state.val < 2176 then
          if state.val < 1792 then
            if state.val < 1600 then
              if state.val < 1504 then
                if state.val < 1472 then
                  packedTransitionCodeChunk45 (state.val - 1440)
                else
                  packedTransitionCodeChunk46 (state.val - 1472)
              else
                if state.val < 1536 then
                  packedTransitionCodeChunk47 (state.val - 1504)
                else
                  if state.val < 1568 then
                    packedTransitionCodeChunk48 (state.val - 1536)
                  else
                    packedTransitionCodeChunk49 (state.val - 1568)
            else
              if state.val < 1696 then
                if state.val < 1632 then
                  packedTransitionCodeChunk50 (state.val - 1600)
                else
                  if state.val < 1664 then
                    packedTransitionCodeChunk51 (state.val - 1632)
                  else
                    packedTransitionCodeChunk52 (state.val - 1664)
              else
                if state.val < 1728 then
                  packedTransitionCodeChunk53 (state.val - 1696)
                else
                  if state.val < 1760 then
                    packedTransitionCodeChunk54 (state.val - 1728)
                  else
                    packedTransitionCodeChunk55 (state.val - 1760)
          else
            if state.val < 1984 then
              if state.val < 1888 then
                if state.val < 1824 then
                  packedTransitionCodeChunk56 (state.val - 1792)
                else
                  if state.val < 1856 then
                    packedTransitionCodeChunk57 (state.val - 1824)
                  else
                    packedTransitionCodeChunk58 (state.val - 1856)
              else
                if state.val < 1920 then
                  packedTransitionCodeChunk59 (state.val - 1888)
                else
                  if state.val < 1952 then
                    packedTransitionCodeChunk60 (state.val - 1920)
                  else
                    packedTransitionCodeChunk61 (state.val - 1952)
            else
              if state.val < 2080 then
                if state.val < 2016 then
                  packedTransitionCodeChunk62 (state.val - 1984)
                else
                  if state.val < 2048 then
                    packedTransitionCodeChunk63 (state.val - 2016)
                  else
                    packedTransitionCodeChunk64 (state.val - 2048)
              else
                if state.val < 2112 then
                  packedTransitionCodeChunk65 (state.val - 2080)
                else
                  if state.val < 2144 then
                    packedTransitionCodeChunk66 (state.val - 2112)
                  else
                    packedTransitionCodeChunk67 (state.val - 2144)
        else
          if state.val < 2528 then
            if state.val < 2336 then
              if state.val < 2240 then
                if state.val < 2208 then
                  packedTransitionCodeChunk68 (state.val - 2176)
                else
                  packedTransitionCodeChunk69 (state.val - 2208)
              else
                if state.val < 2272 then
                  packedTransitionCodeChunk70 (state.val - 2240)
                else
                  if state.val < 2304 then
                    packedTransitionCodeChunk71 (state.val - 2272)
                  else
                    packedTransitionCodeChunk72 (state.val - 2304)
            else
              if state.val < 2432 then
                if state.val < 2368 then
                  packedTransitionCodeChunk73 (state.val - 2336)
                else
                  if state.val < 2400 then
                    packedTransitionCodeChunk74 (state.val - 2368)
                  else
                    packedTransitionCodeChunk75 (state.val - 2400)
              else
                if state.val < 2464 then
                  packedTransitionCodeChunk76 (state.val - 2432)
                else
                  if state.val < 2496 then
                    packedTransitionCodeChunk77 (state.val - 2464)
                  else
                    packedTransitionCodeChunk78 (state.val - 2496)
          else
            if state.val < 2720 then
              if state.val < 2624 then
                if state.val < 2560 then
                  packedTransitionCodeChunk79 (state.val - 2528)
                else
                  if state.val < 2592 then
                    packedTransitionCodeChunk80 (state.val - 2560)
                  else
                    packedTransitionCodeChunk81 (state.val - 2592)
              else
                if state.val < 2656 then
                  packedTransitionCodeChunk82 (state.val - 2624)
                else
                  if state.val < 2688 then
                    packedTransitionCodeChunk83 (state.val - 2656)
                  else
                    packedTransitionCodeChunk84 (state.val - 2688)
            else
              if state.val < 2816 then
                if state.val < 2752 then
                  packedTransitionCodeChunk85 (state.val - 2720)
                else
                  if state.val < 2784 then
                    packedTransitionCodeChunk86 (state.val - 2752)
                  else
                    packedTransitionCodeChunk87 (state.val - 2784)
              else
                if state.val < 2848 then
                  packedTransitionCodeChunk88 (state.val - 2816)
                else
                  if state.val < 2880 then
                    packedTransitionCodeChunk89 (state.val - 2848)
                  else
                    packedTransitionCodeChunk90 (state.val - 2880)
    else
      if state.val < 4384 then
        if state.val < 3648 then
          if state.val < 3264 then
            if state.val < 3072 then
              if state.val < 2976 then
                if state.val < 2944 then
                  packedTransitionCodeChunk91 (state.val - 2912)
                else
                  packedTransitionCodeChunk92 (state.val - 2944)
              else
                if state.val < 3008 then
                  packedTransitionCodeChunk93 (state.val - 2976)
                else
                  if state.val < 3040 then
                    packedTransitionCodeChunk94 (state.val - 3008)
                  else
                    packedTransitionCodeChunk95 (state.val - 3040)
            else
              if state.val < 3168 then
                if state.val < 3104 then
                  packedTransitionCodeChunk96 (state.val - 3072)
                else
                  if state.val < 3136 then
                    packedTransitionCodeChunk97 (state.val - 3104)
                  else
                    packedTransitionCodeChunk98 (state.val - 3136)
              else
                if state.val < 3200 then
                  packedTransitionCodeChunk99 (state.val - 3168)
                else
                  if state.val < 3232 then
                    packedTransitionCodeChunk100 (state.val - 3200)
                  else
                    packedTransitionCodeChunk101 (state.val - 3232)
          else
            if state.val < 3456 then
              if state.val < 3360 then
                if state.val < 3296 then
                  packedTransitionCodeChunk102 (state.val - 3264)
                else
                  if state.val < 3328 then
                    packedTransitionCodeChunk103 (state.val - 3296)
                  else
                    packedTransitionCodeChunk104 (state.val - 3328)
              else
                if state.val < 3392 then
                  packedTransitionCodeChunk105 (state.val - 3360)
                else
                  if state.val < 3424 then
                    packedTransitionCodeChunk106 (state.val - 3392)
                  else
                    packedTransitionCodeChunk107 (state.val - 3424)
            else
              if state.val < 3552 then
                if state.val < 3488 then
                  packedTransitionCodeChunk108 (state.val - 3456)
                else
                  if state.val < 3520 then
                    packedTransitionCodeChunk109 (state.val - 3488)
                  else
                    packedTransitionCodeChunk110 (state.val - 3520)
              else
                if state.val < 3584 then
                  packedTransitionCodeChunk111 (state.val - 3552)
                else
                  if state.val < 3616 then
                    packedTransitionCodeChunk112 (state.val - 3584)
                  else
                    packedTransitionCodeChunk113 (state.val - 3616)
        else
          if state.val < 4000 then
            if state.val < 3808 then
              if state.val < 3712 then
                if state.val < 3680 then
                  packedTransitionCodeChunk114 (state.val - 3648)
                else
                  packedTransitionCodeChunk115 (state.val - 3680)
              else
                if state.val < 3744 then
                  packedTransitionCodeChunk116 (state.val - 3712)
                else
                  if state.val < 3776 then
                    packedTransitionCodeChunk117 (state.val - 3744)
                  else
                    packedTransitionCodeChunk118 (state.val - 3776)
            else
              if state.val < 3904 then
                if state.val < 3840 then
                  packedTransitionCodeChunk119 (state.val - 3808)
                else
                  if state.val < 3872 then
                    packedTransitionCodeChunk120 (state.val - 3840)
                  else
                    packedTransitionCodeChunk121 (state.val - 3872)
              else
                if state.val < 3936 then
                  packedTransitionCodeChunk122 (state.val - 3904)
                else
                  if state.val < 3968 then
                    packedTransitionCodeChunk123 (state.val - 3936)
                  else
                    packedTransitionCodeChunk124 (state.val - 3968)
          else
            if state.val < 4192 then
              if state.val < 4096 then
                if state.val < 4032 then
                  packedTransitionCodeChunk125 (state.val - 4000)
                else
                  if state.val < 4064 then
                    packedTransitionCodeChunk126 (state.val - 4032)
                  else
                    packedTransitionCodeChunk127 (state.val - 4064)
              else
                if state.val < 4128 then
                  packedTransitionCodeChunk128 (state.val - 4096)
                else
                  if state.val < 4160 then
                    packedTransitionCodeChunk129 (state.val - 4128)
                  else
                    packedTransitionCodeChunk130 (state.val - 4160)
            else
              if state.val < 4288 then
                if state.val < 4224 then
                  packedTransitionCodeChunk131 (state.val - 4192)
                else
                  if state.val < 4256 then
                    packedTransitionCodeChunk132 (state.val - 4224)
                  else
                    packedTransitionCodeChunk133 (state.val - 4256)
              else
                if state.val < 4320 then
                  packedTransitionCodeChunk134 (state.val - 4288)
                else
                  if state.val < 4352 then
                    packedTransitionCodeChunk135 (state.val - 4320)
                  else
                    packedTransitionCodeChunk136 (state.val - 4352)
      else
        if state.val < 5120 then
          if state.val < 4736 then
            if state.val < 4544 then
              if state.val < 4448 then
                if state.val < 4416 then
                  packedTransitionCodeChunk137 (state.val - 4384)
                else
                  packedTransitionCodeChunk138 (state.val - 4416)
              else
                if state.val < 4480 then
                  packedTransitionCodeChunk139 (state.val - 4448)
                else
                  if state.val < 4512 then
                    packedTransitionCodeChunk140 (state.val - 4480)
                  else
                    packedTransitionCodeChunk141 (state.val - 4512)
            else
              if state.val < 4640 then
                if state.val < 4576 then
                  packedTransitionCodeChunk142 (state.val - 4544)
                else
                  if state.val < 4608 then
                    packedTransitionCodeChunk143 (state.val - 4576)
                  else
                    packedTransitionCodeChunk144 (state.val - 4608)
              else
                if state.val < 4672 then
                  packedTransitionCodeChunk145 (state.val - 4640)
                else
                  if state.val < 4704 then
                    packedTransitionCodeChunk146 (state.val - 4672)
                  else
                    packedTransitionCodeChunk147 (state.val - 4704)
          else
            if state.val < 4928 then
              if state.val < 4832 then
                if state.val < 4768 then
                  packedTransitionCodeChunk148 (state.val - 4736)
                else
                  if state.val < 4800 then
                    packedTransitionCodeChunk149 (state.val - 4768)
                  else
                    packedTransitionCodeChunk150 (state.val - 4800)
              else
                if state.val < 4864 then
                  packedTransitionCodeChunk151 (state.val - 4832)
                else
                  if state.val < 4896 then
                    packedTransitionCodeChunk152 (state.val - 4864)
                  else
                    packedTransitionCodeChunk153 (state.val - 4896)
            else
              if state.val < 5024 then
                if state.val < 4960 then
                  packedTransitionCodeChunk154 (state.val - 4928)
                else
                  if state.val < 4992 then
                    packedTransitionCodeChunk155 (state.val - 4960)
                  else
                    packedTransitionCodeChunk156 (state.val - 4992)
              else
                if state.val < 5056 then
                  packedTransitionCodeChunk157 (state.val - 5024)
                else
                  if state.val < 5088 then
                    packedTransitionCodeChunk158 (state.val - 5056)
                  else
                    packedTransitionCodeChunk159 (state.val - 5088)
        else
          if state.val < 5472 then
            if state.val < 5280 then
              if state.val < 5184 then
                if state.val < 5152 then
                  packedTransitionCodeChunk160 (state.val - 5120)
                else
                  packedTransitionCodeChunk161 (state.val - 5152)
              else
                if state.val < 5216 then
                  packedTransitionCodeChunk162 (state.val - 5184)
                else
                  if state.val < 5248 then
                    packedTransitionCodeChunk163 (state.val - 5216)
                  else
                    packedTransitionCodeChunk164 (state.val - 5248)
            else
              if state.val < 5376 then
                if state.val < 5312 then
                  packedTransitionCodeChunk165 (state.val - 5280)
                else
                  if state.val < 5344 then
                    packedTransitionCodeChunk166 (state.val - 5312)
                  else
                    packedTransitionCodeChunk167 (state.val - 5344)
              else
                if state.val < 5408 then
                  packedTransitionCodeChunk168 (state.val - 5376)
                else
                  if state.val < 5440 then
                    packedTransitionCodeChunk169 (state.val - 5408)
                  else
                    packedTransitionCodeChunk170 (state.val - 5440)
          else
            if state.val < 5664 then
              if state.val < 5568 then
                if state.val < 5504 then
                  packedTransitionCodeChunk171 (state.val - 5472)
                else
                  if state.val < 5536 then
                    packedTransitionCodeChunk172 (state.val - 5504)
                  else
                    packedTransitionCodeChunk173 (state.val - 5536)
              else
                if state.val < 5600 then
                  packedTransitionCodeChunk174 (state.val - 5568)
                else
                  if state.val < 5632 then
                    packedTransitionCodeChunk175 (state.val - 5600)
                  else
                    packedTransitionCodeChunk176 (state.val - 5632)
            else
              if state.val < 5760 then
                if state.val < 5696 then
                  packedTransitionCodeChunk177 (state.val - 5664)
                else
                  if state.val < 5728 then
                    packedTransitionCodeChunk178 (state.val - 5696)
                  else
                    packedTransitionCodeChunk179 (state.val - 5728)
              else
                if state.val < 5792 then
                  packedTransitionCodeChunk180 (state.val - 5760)
                else
                  if state.val < 5824 then
                    packedTransitionCodeChunk181 (state.val - 5792)
                  else
                    packedTransitionCodeChunk182 (state.val - 5824)
  else
    if state.val < 8800 then
      if state.val < 7328 then
        if state.val < 6592 then
          if state.val < 6208 then
            if state.val < 6016 then
              if state.val < 5920 then
                if state.val < 5888 then
                  packedTransitionCodeChunk183 (state.val - 5856)
                else
                  packedTransitionCodeChunk184 (state.val - 5888)
              else
                if state.val < 5952 then
                  packedTransitionCodeChunk185 (state.val - 5920)
                else
                  if state.val < 5984 then
                    packedTransitionCodeChunk186 (state.val - 5952)
                  else
                    packedTransitionCodeChunk187 (state.val - 5984)
            else
              if state.val < 6112 then
                if state.val < 6048 then
                  packedTransitionCodeChunk188 (state.val - 6016)
                else
                  if state.val < 6080 then
                    packedTransitionCodeChunk189 (state.val - 6048)
                  else
                    packedTransitionCodeChunk190 (state.val - 6080)
              else
                if state.val < 6144 then
                  packedTransitionCodeChunk191 (state.val - 6112)
                else
                  if state.val < 6176 then
                    packedTransitionCodeChunk192 (state.val - 6144)
                  else
                    packedTransitionCodeChunk193 (state.val - 6176)
          else
            if state.val < 6400 then
              if state.val < 6304 then
                if state.val < 6240 then
                  packedTransitionCodeChunk194 (state.val - 6208)
                else
                  if state.val < 6272 then
                    packedTransitionCodeChunk195 (state.val - 6240)
                  else
                    packedTransitionCodeChunk196 (state.val - 6272)
              else
                if state.val < 6336 then
                  packedTransitionCodeChunk197 (state.val - 6304)
                else
                  if state.val < 6368 then
                    packedTransitionCodeChunk198 (state.val - 6336)
                  else
                    packedTransitionCodeChunk199 (state.val - 6368)
            else
              if state.val < 6496 then
                if state.val < 6432 then
                  packedTransitionCodeChunk200 (state.val - 6400)
                else
                  if state.val < 6464 then
                    packedTransitionCodeChunk201 (state.val - 6432)
                  else
                    packedTransitionCodeChunk202 (state.val - 6464)
              else
                if state.val < 6528 then
                  packedTransitionCodeChunk203 (state.val - 6496)
                else
                  if state.val < 6560 then
                    packedTransitionCodeChunk204 (state.val - 6528)
                  else
                    packedTransitionCodeChunk205 (state.val - 6560)
        else
          if state.val < 6944 then
            if state.val < 6752 then
              if state.val < 6656 then
                if state.val < 6624 then
                  packedTransitionCodeChunk206 (state.val - 6592)
                else
                  packedTransitionCodeChunk207 (state.val - 6624)
              else
                if state.val < 6688 then
                  packedTransitionCodeChunk208 (state.val - 6656)
                else
                  if state.val < 6720 then
                    packedTransitionCodeChunk209 (state.val - 6688)
                  else
                    packedTransitionCodeChunk210 (state.val - 6720)
            else
              if state.val < 6848 then
                if state.val < 6784 then
                  packedTransitionCodeChunk211 (state.val - 6752)
                else
                  if state.val < 6816 then
                    packedTransitionCodeChunk212 (state.val - 6784)
                  else
                    packedTransitionCodeChunk213 (state.val - 6816)
              else
                if state.val < 6880 then
                  packedTransitionCodeChunk214 (state.val - 6848)
                else
                  if state.val < 6912 then
                    packedTransitionCodeChunk215 (state.val - 6880)
                  else
                    packedTransitionCodeChunk216 (state.val - 6912)
          else
            if state.val < 7136 then
              if state.val < 7040 then
                if state.val < 6976 then
                  packedTransitionCodeChunk217 (state.val - 6944)
                else
                  if state.val < 7008 then
                    packedTransitionCodeChunk218 (state.val - 6976)
                  else
                    packedTransitionCodeChunk219 (state.val - 7008)
              else
                if state.val < 7072 then
                  packedTransitionCodeChunk220 (state.val - 7040)
                else
                  if state.val < 7104 then
                    packedTransitionCodeChunk221 (state.val - 7072)
                  else
                    packedTransitionCodeChunk222 (state.val - 7104)
            else
              if state.val < 7232 then
                if state.val < 7168 then
                  packedTransitionCodeChunk223 (state.val - 7136)
                else
                  if state.val < 7200 then
                    packedTransitionCodeChunk224 (state.val - 7168)
                  else
                    packedTransitionCodeChunk225 (state.val - 7200)
              else
                if state.val < 7264 then
                  packedTransitionCodeChunk226 (state.val - 7232)
                else
                  if state.val < 7296 then
                    packedTransitionCodeChunk227 (state.val - 7264)
                  else
                    packedTransitionCodeChunk228 (state.val - 7296)
      else
        if state.val < 8064 then
          if state.val < 7680 then
            if state.val < 7488 then
              if state.val < 7392 then
                if state.val < 7360 then
                  packedTransitionCodeChunk229 (state.val - 7328)
                else
                  packedTransitionCodeChunk230 (state.val - 7360)
              else
                if state.val < 7424 then
                  packedTransitionCodeChunk231 (state.val - 7392)
                else
                  if state.val < 7456 then
                    packedTransitionCodeChunk232 (state.val - 7424)
                  else
                    packedTransitionCodeChunk233 (state.val - 7456)
            else
              if state.val < 7584 then
                if state.val < 7520 then
                  packedTransitionCodeChunk234 (state.val - 7488)
                else
                  if state.val < 7552 then
                    packedTransitionCodeChunk235 (state.val - 7520)
                  else
                    packedTransitionCodeChunk236 (state.val - 7552)
              else
                if state.val < 7616 then
                  packedTransitionCodeChunk237 (state.val - 7584)
                else
                  if state.val < 7648 then
                    packedTransitionCodeChunk238 (state.val - 7616)
                  else
                    packedTransitionCodeChunk239 (state.val - 7648)
          else
            if state.val < 7872 then
              if state.val < 7776 then
                if state.val < 7712 then
                  packedTransitionCodeChunk240 (state.val - 7680)
                else
                  if state.val < 7744 then
                    packedTransitionCodeChunk241 (state.val - 7712)
                  else
                    packedTransitionCodeChunk242 (state.val - 7744)
              else
                if state.val < 7808 then
                  packedTransitionCodeChunk243 (state.val - 7776)
                else
                  if state.val < 7840 then
                    packedTransitionCodeChunk244 (state.val - 7808)
                  else
                    packedTransitionCodeChunk245 (state.val - 7840)
            else
              if state.val < 7968 then
                if state.val < 7904 then
                  packedTransitionCodeChunk246 (state.val - 7872)
                else
                  if state.val < 7936 then
                    packedTransitionCodeChunk247 (state.val - 7904)
                  else
                    packedTransitionCodeChunk248 (state.val - 7936)
              else
                if state.val < 8000 then
                  packedTransitionCodeChunk249 (state.val - 7968)
                else
                  if state.val < 8032 then
                    packedTransitionCodeChunk250 (state.val - 8000)
                  else
                    packedTransitionCodeChunk251 (state.val - 8032)
        else
          if state.val < 8416 then
            if state.val < 8224 then
              if state.val < 8128 then
                if state.val < 8096 then
                  packedTransitionCodeChunk252 (state.val - 8064)
                else
                  packedTransitionCodeChunk253 (state.val - 8096)
              else
                if state.val < 8160 then
                  packedTransitionCodeChunk254 (state.val - 8128)
                else
                  if state.val < 8192 then
                    packedTransitionCodeChunk255 (state.val - 8160)
                  else
                    packedTransitionCodeChunk256 (state.val - 8192)
            else
              if state.val < 8320 then
                if state.val < 8256 then
                  packedTransitionCodeChunk257 (state.val - 8224)
                else
                  if state.val < 8288 then
                    packedTransitionCodeChunk258 (state.val - 8256)
                  else
                    packedTransitionCodeChunk259 (state.val - 8288)
              else
                if state.val < 8352 then
                  packedTransitionCodeChunk260 (state.val - 8320)
                else
                  if state.val < 8384 then
                    packedTransitionCodeChunk261 (state.val - 8352)
                  else
                    packedTransitionCodeChunk262 (state.val - 8384)
          else
            if state.val < 8608 then
              if state.val < 8512 then
                if state.val < 8448 then
                  packedTransitionCodeChunk263 (state.val - 8416)
                else
                  if state.val < 8480 then
                    packedTransitionCodeChunk264 (state.val - 8448)
                  else
                    packedTransitionCodeChunk265 (state.val - 8480)
              else
                if state.val < 8544 then
                  packedTransitionCodeChunk266 (state.val - 8512)
                else
                  if state.val < 8576 then
                    packedTransitionCodeChunk267 (state.val - 8544)
                  else
                    packedTransitionCodeChunk268 (state.val - 8576)
            else
              if state.val < 8704 then
                if state.val < 8640 then
                  packedTransitionCodeChunk269 (state.val - 8608)
                else
                  if state.val < 8672 then
                    packedTransitionCodeChunk270 (state.val - 8640)
                  else
                    packedTransitionCodeChunk271 (state.val - 8672)
              else
                if state.val < 8736 then
                  packedTransitionCodeChunk272 (state.val - 8704)
                else
                  if state.val < 8768 then
                    packedTransitionCodeChunk273 (state.val - 8736)
                  else
                    packedTransitionCodeChunk274 (state.val - 8768)
    else
      if state.val < 10272 then
        if state.val < 9536 then
          if state.val < 9152 then
            if state.val < 8960 then
              if state.val < 8864 then
                if state.val < 8832 then
                  packedTransitionCodeChunk275 (state.val - 8800)
                else
                  packedTransitionCodeChunk276 (state.val - 8832)
              else
                if state.val < 8896 then
                  packedTransitionCodeChunk277 (state.val - 8864)
                else
                  if state.val < 8928 then
                    packedTransitionCodeChunk278 (state.val - 8896)
                  else
                    packedTransitionCodeChunk279 (state.val - 8928)
            else
              if state.val < 9056 then
                if state.val < 8992 then
                  packedTransitionCodeChunk280 (state.val - 8960)
                else
                  if state.val < 9024 then
                    packedTransitionCodeChunk281 (state.val - 8992)
                  else
                    packedTransitionCodeChunk282 (state.val - 9024)
              else
                if state.val < 9088 then
                  packedTransitionCodeChunk283 (state.val - 9056)
                else
                  if state.val < 9120 then
                    packedTransitionCodeChunk284 (state.val - 9088)
                  else
                    packedTransitionCodeChunk285 (state.val - 9120)
          else
            if state.val < 9344 then
              if state.val < 9248 then
                if state.val < 9184 then
                  packedTransitionCodeChunk286 (state.val - 9152)
                else
                  if state.val < 9216 then
                    packedTransitionCodeChunk287 (state.val - 9184)
                  else
                    packedTransitionCodeChunk288 (state.val - 9216)
              else
                if state.val < 9280 then
                  packedTransitionCodeChunk289 (state.val - 9248)
                else
                  if state.val < 9312 then
                    packedTransitionCodeChunk290 (state.val - 9280)
                  else
                    packedTransitionCodeChunk291 (state.val - 9312)
            else
              if state.val < 9440 then
                if state.val < 9376 then
                  packedTransitionCodeChunk292 (state.val - 9344)
                else
                  if state.val < 9408 then
                    packedTransitionCodeChunk293 (state.val - 9376)
                  else
                    packedTransitionCodeChunk294 (state.val - 9408)
              else
                if state.val < 9472 then
                  packedTransitionCodeChunk295 (state.val - 9440)
                else
                  if state.val < 9504 then
                    packedTransitionCodeChunk296 (state.val - 9472)
                  else
                    packedTransitionCodeChunk297 (state.val - 9504)
        else
          if state.val < 9888 then
            if state.val < 9696 then
              if state.val < 9600 then
                if state.val < 9568 then
                  packedTransitionCodeChunk298 (state.val - 9536)
                else
                  packedTransitionCodeChunk299 (state.val - 9568)
              else
                if state.val < 9632 then
                  packedTransitionCodeChunk300 (state.val - 9600)
                else
                  if state.val < 9664 then
                    packedTransitionCodeChunk301 (state.val - 9632)
                  else
                    packedTransitionCodeChunk302 (state.val - 9664)
            else
              if state.val < 9792 then
                if state.val < 9728 then
                  packedTransitionCodeChunk303 (state.val - 9696)
                else
                  if state.val < 9760 then
                    packedTransitionCodeChunk304 (state.val - 9728)
                  else
                    packedTransitionCodeChunk305 (state.val - 9760)
              else
                if state.val < 9824 then
                  packedTransitionCodeChunk306 (state.val - 9792)
                else
                  if state.val < 9856 then
                    packedTransitionCodeChunk307 (state.val - 9824)
                  else
                    packedTransitionCodeChunk308 (state.val - 9856)
          else
            if state.val < 10080 then
              if state.val < 9984 then
                if state.val < 9920 then
                  packedTransitionCodeChunk309 (state.val - 9888)
                else
                  if state.val < 9952 then
                    packedTransitionCodeChunk310 (state.val - 9920)
                  else
                    packedTransitionCodeChunk311 (state.val - 9952)
              else
                if state.val < 10016 then
                  packedTransitionCodeChunk312 (state.val - 9984)
                else
                  if state.val < 10048 then
                    packedTransitionCodeChunk313 (state.val - 10016)
                  else
                    packedTransitionCodeChunk314 (state.val - 10048)
            else
              if state.val < 10176 then
                if state.val < 10112 then
                  packedTransitionCodeChunk315 (state.val - 10080)
                else
                  if state.val < 10144 then
                    packedTransitionCodeChunk316 (state.val - 10112)
                  else
                    packedTransitionCodeChunk317 (state.val - 10144)
              else
                if state.val < 10208 then
                  packedTransitionCodeChunk318 (state.val - 10176)
                else
                  if state.val < 10240 then
                    packedTransitionCodeChunk319 (state.val - 10208)
                  else
                    packedTransitionCodeChunk320 (state.val - 10240)
      else
        if state.val < 11008 then
          if state.val < 10624 then
            if state.val < 10432 then
              if state.val < 10336 then
                if state.val < 10304 then
                  packedTransitionCodeChunk321 (state.val - 10272)
                else
                  packedTransitionCodeChunk322 (state.val - 10304)
              else
                if state.val < 10368 then
                  packedTransitionCodeChunk323 (state.val - 10336)
                else
                  if state.val < 10400 then
                    packedTransitionCodeChunk324 (state.val - 10368)
                  else
                    packedTransitionCodeChunk325 (state.val - 10400)
            else
              if state.val < 10528 then
                if state.val < 10464 then
                  packedTransitionCodeChunk326 (state.val - 10432)
                else
                  if state.val < 10496 then
                    packedTransitionCodeChunk327 (state.val - 10464)
                  else
                    packedTransitionCodeChunk328 (state.val - 10496)
              else
                if state.val < 10560 then
                  packedTransitionCodeChunk329 (state.val - 10528)
                else
                  if state.val < 10592 then
                    packedTransitionCodeChunk330 (state.val - 10560)
                  else
                    packedTransitionCodeChunk331 (state.val - 10592)
          else
            if state.val < 10816 then
              if state.val < 10720 then
                if state.val < 10656 then
                  packedTransitionCodeChunk332 (state.val - 10624)
                else
                  if state.val < 10688 then
                    packedTransitionCodeChunk333 (state.val - 10656)
                  else
                    packedTransitionCodeChunk334 (state.val - 10688)
              else
                if state.val < 10752 then
                  packedTransitionCodeChunk335 (state.val - 10720)
                else
                  if state.val < 10784 then
                    packedTransitionCodeChunk336 (state.val - 10752)
                  else
                    packedTransitionCodeChunk337 (state.val - 10784)
            else
              if state.val < 10912 then
                if state.val < 10848 then
                  packedTransitionCodeChunk338 (state.val - 10816)
                else
                  if state.val < 10880 then
                    packedTransitionCodeChunk339 (state.val - 10848)
                  else
                    packedTransitionCodeChunk340 (state.val - 10880)
              else
                if state.val < 10944 then
                  packedTransitionCodeChunk341 (state.val - 10912)
                else
                  if state.val < 10976 then
                    packedTransitionCodeChunk342 (state.val - 10944)
                  else
                    packedTransitionCodeChunk343 (state.val - 10976)
        else
          if state.val < 11360 then
            if state.val < 11168 then
              if state.val < 11072 then
                if state.val < 11040 then
                  packedTransitionCodeChunk344 (state.val - 11008)
                else
                  packedTransitionCodeChunk345 (state.val - 11040)
              else
                if state.val < 11104 then
                  packedTransitionCodeChunk346 (state.val - 11072)
                else
                  if state.val < 11136 then
                    packedTransitionCodeChunk347 (state.val - 11104)
                  else
                    packedTransitionCodeChunk348 (state.val - 11136)
            else
              if state.val < 11264 then
                if state.val < 11200 then
                  packedTransitionCodeChunk349 (state.val - 11168)
                else
                  if state.val < 11232 then
                    packedTransitionCodeChunk350 (state.val - 11200)
                  else
                    packedTransitionCodeChunk351 (state.val - 11232)
              else
                if state.val < 11296 then
                  packedTransitionCodeChunk352 (state.val - 11264)
                else
                  if state.val < 11328 then
                    packedTransitionCodeChunk353 (state.val - 11296)
                  else
                    packedTransitionCodeChunk354 (state.val - 11328)
          else
            if state.val < 11552 then
              if state.val < 11456 then
                if state.val < 11392 then
                  packedTransitionCodeChunk355 (state.val - 11360)
                else
                  if state.val < 11424 then
                    packedTransitionCodeChunk356 (state.val - 11392)
                  else
                    packedTransitionCodeChunk357 (state.val - 11424)
              else
                if state.val < 11488 then
                  packedTransitionCodeChunk358 (state.val - 11456)
                else
                  if state.val < 11520 then
                    packedTransitionCodeChunk359 (state.val - 11488)
                  else
                    packedTransitionCodeChunk360 (state.val - 11520)
            else
              if state.val < 11648 then
                if state.val < 11584 then
                  packedTransitionCodeChunk361 (state.val - 11552)
                else
                  if state.val < 11616 then
                    packedTransitionCodeChunk362 (state.val - 11584)
                  else
                    packedTransitionCodeChunk363 (state.val - 11616)
              else
                if state.val < 11680 then
                  packedTransitionCodeChunk364 (state.val - 11648)
                else
                  if state.val < 11712 then
                    packedTransitionCodeChunk365 (state.val - 11680)
                  else
                    packedTransitionCodeChunk366 (state.val - 11712)

def transition (state : Fin 11742)
    (generator : Fin 6) : Fin 11742 :=
  ⟨(packedTransitionCode state / 11742 ^ generator.val) % 11742,
    Nat.mod_lt _ (by decide)⟩

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.Shards
