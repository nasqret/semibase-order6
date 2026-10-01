import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.Shards.StateVectorPart00
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.Shards.StateVectorPart01
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.Shards.StateVectorPart02
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.Shards.StateVectorPart03
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.Shards.StateVectorPart04
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.Shards.StateVectorPart05
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.Shards.StateVectorPart06
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.Shards.StateVectorPart07
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.Shards.StateVectorPart08
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.Shards.StateVectorPart09
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.Shards.StateVectorPart10
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.Shards.StateVectorPart11

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.Shards

def packedStateVectorCode (state : Fin 11742) : Nat :=
  if state.val < 5856 then
    if state.val < 2912 then
      if state.val < 1440 then
        if state.val < 704 then
          if state.val < 352 then
            if state.val < 160 then
              if state.val < 64 then
                if state.val < 32 then
                  packedStateVectorCodeChunk0 state.val
                else
                  packedStateVectorCodeChunk1 (state.val - 32)
              else
                if state.val < 96 then
                  packedStateVectorCodeChunk2 (state.val - 64)
                else
                  if state.val < 128 then
                    packedStateVectorCodeChunk3 (state.val - 96)
                  else
                    packedStateVectorCodeChunk4 (state.val - 128)
            else
              if state.val < 256 then
                if state.val < 192 then
                  packedStateVectorCodeChunk5 (state.val - 160)
                else
                  if state.val < 224 then
                    packedStateVectorCodeChunk6 (state.val - 192)
                  else
                    packedStateVectorCodeChunk7 (state.val - 224)
              else
                if state.val < 288 then
                  packedStateVectorCodeChunk8 (state.val - 256)
                else
                  if state.val < 320 then
                    packedStateVectorCodeChunk9 (state.val - 288)
                  else
                    packedStateVectorCodeChunk10 (state.val - 320)
          else
            if state.val < 512 then
              if state.val < 416 then
                if state.val < 384 then
                  packedStateVectorCodeChunk11 (state.val - 352)
                else
                  packedStateVectorCodeChunk12 (state.val - 384)
              else
                if state.val < 448 then
                  packedStateVectorCodeChunk13 (state.val - 416)
                else
                  if state.val < 480 then
                    packedStateVectorCodeChunk14 (state.val - 448)
                  else
                    packedStateVectorCodeChunk15 (state.val - 480)
            else
              if state.val < 608 then
                if state.val < 544 then
                  packedStateVectorCodeChunk16 (state.val - 512)
                else
                  if state.val < 576 then
                    packedStateVectorCodeChunk17 (state.val - 544)
                  else
                    packedStateVectorCodeChunk18 (state.val - 576)
              else
                if state.val < 640 then
                  packedStateVectorCodeChunk19 (state.val - 608)
                else
                  if state.val < 672 then
                    packedStateVectorCodeChunk20 (state.val - 640)
                  else
                    packedStateVectorCodeChunk21 (state.val - 672)
        else
          if state.val < 1056 then
            if state.val < 864 then
              if state.val < 768 then
                if state.val < 736 then
                  packedStateVectorCodeChunk22 (state.val - 704)
                else
                  packedStateVectorCodeChunk23 (state.val - 736)
              else
                if state.val < 800 then
                  packedStateVectorCodeChunk24 (state.val - 768)
                else
                  if state.val < 832 then
                    packedStateVectorCodeChunk25 (state.val - 800)
                  else
                    packedStateVectorCodeChunk26 (state.val - 832)
            else
              if state.val < 960 then
                if state.val < 896 then
                  packedStateVectorCodeChunk27 (state.val - 864)
                else
                  if state.val < 928 then
                    packedStateVectorCodeChunk28 (state.val - 896)
                  else
                    packedStateVectorCodeChunk29 (state.val - 928)
              else
                if state.val < 992 then
                  packedStateVectorCodeChunk30 (state.val - 960)
                else
                  if state.val < 1024 then
                    packedStateVectorCodeChunk31 (state.val - 992)
                  else
                    packedStateVectorCodeChunk32 (state.val - 1024)
          else
            if state.val < 1248 then
              if state.val < 1152 then
                if state.val < 1088 then
                  packedStateVectorCodeChunk33 (state.val - 1056)
                else
                  if state.val < 1120 then
                    packedStateVectorCodeChunk34 (state.val - 1088)
                  else
                    packedStateVectorCodeChunk35 (state.val - 1120)
              else
                if state.val < 1184 then
                  packedStateVectorCodeChunk36 (state.val - 1152)
                else
                  if state.val < 1216 then
                    packedStateVectorCodeChunk37 (state.val - 1184)
                  else
                    packedStateVectorCodeChunk38 (state.val - 1216)
            else
              if state.val < 1344 then
                if state.val < 1280 then
                  packedStateVectorCodeChunk39 (state.val - 1248)
                else
                  if state.val < 1312 then
                    packedStateVectorCodeChunk40 (state.val - 1280)
                  else
                    packedStateVectorCodeChunk41 (state.val - 1312)
              else
                if state.val < 1376 then
                  packedStateVectorCodeChunk42 (state.val - 1344)
                else
                  if state.val < 1408 then
                    packedStateVectorCodeChunk43 (state.val - 1376)
                  else
                    packedStateVectorCodeChunk44 (state.val - 1408)
      else
        if state.val < 2176 then
          if state.val < 1792 then
            if state.val < 1600 then
              if state.val < 1504 then
                if state.val < 1472 then
                  packedStateVectorCodeChunk45 (state.val - 1440)
                else
                  packedStateVectorCodeChunk46 (state.val - 1472)
              else
                if state.val < 1536 then
                  packedStateVectorCodeChunk47 (state.val - 1504)
                else
                  if state.val < 1568 then
                    packedStateVectorCodeChunk48 (state.val - 1536)
                  else
                    packedStateVectorCodeChunk49 (state.val - 1568)
            else
              if state.val < 1696 then
                if state.val < 1632 then
                  packedStateVectorCodeChunk50 (state.val - 1600)
                else
                  if state.val < 1664 then
                    packedStateVectorCodeChunk51 (state.val - 1632)
                  else
                    packedStateVectorCodeChunk52 (state.val - 1664)
              else
                if state.val < 1728 then
                  packedStateVectorCodeChunk53 (state.val - 1696)
                else
                  if state.val < 1760 then
                    packedStateVectorCodeChunk54 (state.val - 1728)
                  else
                    packedStateVectorCodeChunk55 (state.val - 1760)
          else
            if state.val < 1984 then
              if state.val < 1888 then
                if state.val < 1824 then
                  packedStateVectorCodeChunk56 (state.val - 1792)
                else
                  if state.val < 1856 then
                    packedStateVectorCodeChunk57 (state.val - 1824)
                  else
                    packedStateVectorCodeChunk58 (state.val - 1856)
              else
                if state.val < 1920 then
                  packedStateVectorCodeChunk59 (state.val - 1888)
                else
                  if state.val < 1952 then
                    packedStateVectorCodeChunk60 (state.val - 1920)
                  else
                    packedStateVectorCodeChunk61 (state.val - 1952)
            else
              if state.val < 2080 then
                if state.val < 2016 then
                  packedStateVectorCodeChunk62 (state.val - 1984)
                else
                  if state.val < 2048 then
                    packedStateVectorCodeChunk63 (state.val - 2016)
                  else
                    packedStateVectorCodeChunk64 (state.val - 2048)
              else
                if state.val < 2112 then
                  packedStateVectorCodeChunk65 (state.val - 2080)
                else
                  if state.val < 2144 then
                    packedStateVectorCodeChunk66 (state.val - 2112)
                  else
                    packedStateVectorCodeChunk67 (state.val - 2144)
        else
          if state.val < 2528 then
            if state.val < 2336 then
              if state.val < 2240 then
                if state.val < 2208 then
                  packedStateVectorCodeChunk68 (state.val - 2176)
                else
                  packedStateVectorCodeChunk69 (state.val - 2208)
              else
                if state.val < 2272 then
                  packedStateVectorCodeChunk70 (state.val - 2240)
                else
                  if state.val < 2304 then
                    packedStateVectorCodeChunk71 (state.val - 2272)
                  else
                    packedStateVectorCodeChunk72 (state.val - 2304)
            else
              if state.val < 2432 then
                if state.val < 2368 then
                  packedStateVectorCodeChunk73 (state.val - 2336)
                else
                  if state.val < 2400 then
                    packedStateVectorCodeChunk74 (state.val - 2368)
                  else
                    packedStateVectorCodeChunk75 (state.val - 2400)
              else
                if state.val < 2464 then
                  packedStateVectorCodeChunk76 (state.val - 2432)
                else
                  if state.val < 2496 then
                    packedStateVectorCodeChunk77 (state.val - 2464)
                  else
                    packedStateVectorCodeChunk78 (state.val - 2496)
          else
            if state.val < 2720 then
              if state.val < 2624 then
                if state.val < 2560 then
                  packedStateVectorCodeChunk79 (state.val - 2528)
                else
                  if state.val < 2592 then
                    packedStateVectorCodeChunk80 (state.val - 2560)
                  else
                    packedStateVectorCodeChunk81 (state.val - 2592)
              else
                if state.val < 2656 then
                  packedStateVectorCodeChunk82 (state.val - 2624)
                else
                  if state.val < 2688 then
                    packedStateVectorCodeChunk83 (state.val - 2656)
                  else
                    packedStateVectorCodeChunk84 (state.val - 2688)
            else
              if state.val < 2816 then
                if state.val < 2752 then
                  packedStateVectorCodeChunk85 (state.val - 2720)
                else
                  if state.val < 2784 then
                    packedStateVectorCodeChunk86 (state.val - 2752)
                  else
                    packedStateVectorCodeChunk87 (state.val - 2784)
              else
                if state.val < 2848 then
                  packedStateVectorCodeChunk88 (state.val - 2816)
                else
                  if state.val < 2880 then
                    packedStateVectorCodeChunk89 (state.val - 2848)
                  else
                    packedStateVectorCodeChunk90 (state.val - 2880)
    else
      if state.val < 4384 then
        if state.val < 3648 then
          if state.val < 3264 then
            if state.val < 3072 then
              if state.val < 2976 then
                if state.val < 2944 then
                  packedStateVectorCodeChunk91 (state.val - 2912)
                else
                  packedStateVectorCodeChunk92 (state.val - 2944)
              else
                if state.val < 3008 then
                  packedStateVectorCodeChunk93 (state.val - 2976)
                else
                  if state.val < 3040 then
                    packedStateVectorCodeChunk94 (state.val - 3008)
                  else
                    packedStateVectorCodeChunk95 (state.val - 3040)
            else
              if state.val < 3168 then
                if state.val < 3104 then
                  packedStateVectorCodeChunk96 (state.val - 3072)
                else
                  if state.val < 3136 then
                    packedStateVectorCodeChunk97 (state.val - 3104)
                  else
                    packedStateVectorCodeChunk98 (state.val - 3136)
              else
                if state.val < 3200 then
                  packedStateVectorCodeChunk99 (state.val - 3168)
                else
                  if state.val < 3232 then
                    packedStateVectorCodeChunk100 (state.val - 3200)
                  else
                    packedStateVectorCodeChunk101 (state.val - 3232)
          else
            if state.val < 3456 then
              if state.val < 3360 then
                if state.val < 3296 then
                  packedStateVectorCodeChunk102 (state.val - 3264)
                else
                  if state.val < 3328 then
                    packedStateVectorCodeChunk103 (state.val - 3296)
                  else
                    packedStateVectorCodeChunk104 (state.val - 3328)
              else
                if state.val < 3392 then
                  packedStateVectorCodeChunk105 (state.val - 3360)
                else
                  if state.val < 3424 then
                    packedStateVectorCodeChunk106 (state.val - 3392)
                  else
                    packedStateVectorCodeChunk107 (state.val - 3424)
            else
              if state.val < 3552 then
                if state.val < 3488 then
                  packedStateVectorCodeChunk108 (state.val - 3456)
                else
                  if state.val < 3520 then
                    packedStateVectorCodeChunk109 (state.val - 3488)
                  else
                    packedStateVectorCodeChunk110 (state.val - 3520)
              else
                if state.val < 3584 then
                  packedStateVectorCodeChunk111 (state.val - 3552)
                else
                  if state.val < 3616 then
                    packedStateVectorCodeChunk112 (state.val - 3584)
                  else
                    packedStateVectorCodeChunk113 (state.val - 3616)
        else
          if state.val < 4000 then
            if state.val < 3808 then
              if state.val < 3712 then
                if state.val < 3680 then
                  packedStateVectorCodeChunk114 (state.val - 3648)
                else
                  packedStateVectorCodeChunk115 (state.val - 3680)
              else
                if state.val < 3744 then
                  packedStateVectorCodeChunk116 (state.val - 3712)
                else
                  if state.val < 3776 then
                    packedStateVectorCodeChunk117 (state.val - 3744)
                  else
                    packedStateVectorCodeChunk118 (state.val - 3776)
            else
              if state.val < 3904 then
                if state.val < 3840 then
                  packedStateVectorCodeChunk119 (state.val - 3808)
                else
                  if state.val < 3872 then
                    packedStateVectorCodeChunk120 (state.val - 3840)
                  else
                    packedStateVectorCodeChunk121 (state.val - 3872)
              else
                if state.val < 3936 then
                  packedStateVectorCodeChunk122 (state.val - 3904)
                else
                  if state.val < 3968 then
                    packedStateVectorCodeChunk123 (state.val - 3936)
                  else
                    packedStateVectorCodeChunk124 (state.val - 3968)
          else
            if state.val < 4192 then
              if state.val < 4096 then
                if state.val < 4032 then
                  packedStateVectorCodeChunk125 (state.val - 4000)
                else
                  if state.val < 4064 then
                    packedStateVectorCodeChunk126 (state.val - 4032)
                  else
                    packedStateVectorCodeChunk127 (state.val - 4064)
              else
                if state.val < 4128 then
                  packedStateVectorCodeChunk128 (state.val - 4096)
                else
                  if state.val < 4160 then
                    packedStateVectorCodeChunk129 (state.val - 4128)
                  else
                    packedStateVectorCodeChunk130 (state.val - 4160)
            else
              if state.val < 4288 then
                if state.val < 4224 then
                  packedStateVectorCodeChunk131 (state.val - 4192)
                else
                  if state.val < 4256 then
                    packedStateVectorCodeChunk132 (state.val - 4224)
                  else
                    packedStateVectorCodeChunk133 (state.val - 4256)
              else
                if state.val < 4320 then
                  packedStateVectorCodeChunk134 (state.val - 4288)
                else
                  if state.val < 4352 then
                    packedStateVectorCodeChunk135 (state.val - 4320)
                  else
                    packedStateVectorCodeChunk136 (state.val - 4352)
      else
        if state.val < 5120 then
          if state.val < 4736 then
            if state.val < 4544 then
              if state.val < 4448 then
                if state.val < 4416 then
                  packedStateVectorCodeChunk137 (state.val - 4384)
                else
                  packedStateVectorCodeChunk138 (state.val - 4416)
              else
                if state.val < 4480 then
                  packedStateVectorCodeChunk139 (state.val - 4448)
                else
                  if state.val < 4512 then
                    packedStateVectorCodeChunk140 (state.val - 4480)
                  else
                    packedStateVectorCodeChunk141 (state.val - 4512)
            else
              if state.val < 4640 then
                if state.val < 4576 then
                  packedStateVectorCodeChunk142 (state.val - 4544)
                else
                  if state.val < 4608 then
                    packedStateVectorCodeChunk143 (state.val - 4576)
                  else
                    packedStateVectorCodeChunk144 (state.val - 4608)
              else
                if state.val < 4672 then
                  packedStateVectorCodeChunk145 (state.val - 4640)
                else
                  if state.val < 4704 then
                    packedStateVectorCodeChunk146 (state.val - 4672)
                  else
                    packedStateVectorCodeChunk147 (state.val - 4704)
          else
            if state.val < 4928 then
              if state.val < 4832 then
                if state.val < 4768 then
                  packedStateVectorCodeChunk148 (state.val - 4736)
                else
                  if state.val < 4800 then
                    packedStateVectorCodeChunk149 (state.val - 4768)
                  else
                    packedStateVectorCodeChunk150 (state.val - 4800)
              else
                if state.val < 4864 then
                  packedStateVectorCodeChunk151 (state.val - 4832)
                else
                  if state.val < 4896 then
                    packedStateVectorCodeChunk152 (state.val - 4864)
                  else
                    packedStateVectorCodeChunk153 (state.val - 4896)
            else
              if state.val < 5024 then
                if state.val < 4960 then
                  packedStateVectorCodeChunk154 (state.val - 4928)
                else
                  if state.val < 4992 then
                    packedStateVectorCodeChunk155 (state.val - 4960)
                  else
                    packedStateVectorCodeChunk156 (state.val - 4992)
              else
                if state.val < 5056 then
                  packedStateVectorCodeChunk157 (state.val - 5024)
                else
                  if state.val < 5088 then
                    packedStateVectorCodeChunk158 (state.val - 5056)
                  else
                    packedStateVectorCodeChunk159 (state.val - 5088)
        else
          if state.val < 5472 then
            if state.val < 5280 then
              if state.val < 5184 then
                if state.val < 5152 then
                  packedStateVectorCodeChunk160 (state.val - 5120)
                else
                  packedStateVectorCodeChunk161 (state.val - 5152)
              else
                if state.val < 5216 then
                  packedStateVectorCodeChunk162 (state.val - 5184)
                else
                  if state.val < 5248 then
                    packedStateVectorCodeChunk163 (state.val - 5216)
                  else
                    packedStateVectorCodeChunk164 (state.val - 5248)
            else
              if state.val < 5376 then
                if state.val < 5312 then
                  packedStateVectorCodeChunk165 (state.val - 5280)
                else
                  if state.val < 5344 then
                    packedStateVectorCodeChunk166 (state.val - 5312)
                  else
                    packedStateVectorCodeChunk167 (state.val - 5344)
              else
                if state.val < 5408 then
                  packedStateVectorCodeChunk168 (state.val - 5376)
                else
                  if state.val < 5440 then
                    packedStateVectorCodeChunk169 (state.val - 5408)
                  else
                    packedStateVectorCodeChunk170 (state.val - 5440)
          else
            if state.val < 5664 then
              if state.val < 5568 then
                if state.val < 5504 then
                  packedStateVectorCodeChunk171 (state.val - 5472)
                else
                  if state.val < 5536 then
                    packedStateVectorCodeChunk172 (state.val - 5504)
                  else
                    packedStateVectorCodeChunk173 (state.val - 5536)
              else
                if state.val < 5600 then
                  packedStateVectorCodeChunk174 (state.val - 5568)
                else
                  if state.val < 5632 then
                    packedStateVectorCodeChunk175 (state.val - 5600)
                  else
                    packedStateVectorCodeChunk176 (state.val - 5632)
            else
              if state.val < 5760 then
                if state.val < 5696 then
                  packedStateVectorCodeChunk177 (state.val - 5664)
                else
                  if state.val < 5728 then
                    packedStateVectorCodeChunk178 (state.val - 5696)
                  else
                    packedStateVectorCodeChunk179 (state.val - 5728)
              else
                if state.val < 5792 then
                  packedStateVectorCodeChunk180 (state.val - 5760)
                else
                  if state.val < 5824 then
                    packedStateVectorCodeChunk181 (state.val - 5792)
                  else
                    packedStateVectorCodeChunk182 (state.val - 5824)
  else
    if state.val < 8800 then
      if state.val < 7328 then
        if state.val < 6592 then
          if state.val < 6208 then
            if state.val < 6016 then
              if state.val < 5920 then
                if state.val < 5888 then
                  packedStateVectorCodeChunk183 (state.val - 5856)
                else
                  packedStateVectorCodeChunk184 (state.val - 5888)
              else
                if state.val < 5952 then
                  packedStateVectorCodeChunk185 (state.val - 5920)
                else
                  if state.val < 5984 then
                    packedStateVectorCodeChunk186 (state.val - 5952)
                  else
                    packedStateVectorCodeChunk187 (state.val - 5984)
            else
              if state.val < 6112 then
                if state.val < 6048 then
                  packedStateVectorCodeChunk188 (state.val - 6016)
                else
                  if state.val < 6080 then
                    packedStateVectorCodeChunk189 (state.val - 6048)
                  else
                    packedStateVectorCodeChunk190 (state.val - 6080)
              else
                if state.val < 6144 then
                  packedStateVectorCodeChunk191 (state.val - 6112)
                else
                  if state.val < 6176 then
                    packedStateVectorCodeChunk192 (state.val - 6144)
                  else
                    packedStateVectorCodeChunk193 (state.val - 6176)
          else
            if state.val < 6400 then
              if state.val < 6304 then
                if state.val < 6240 then
                  packedStateVectorCodeChunk194 (state.val - 6208)
                else
                  if state.val < 6272 then
                    packedStateVectorCodeChunk195 (state.val - 6240)
                  else
                    packedStateVectorCodeChunk196 (state.val - 6272)
              else
                if state.val < 6336 then
                  packedStateVectorCodeChunk197 (state.val - 6304)
                else
                  if state.val < 6368 then
                    packedStateVectorCodeChunk198 (state.val - 6336)
                  else
                    packedStateVectorCodeChunk199 (state.val - 6368)
            else
              if state.val < 6496 then
                if state.val < 6432 then
                  packedStateVectorCodeChunk200 (state.val - 6400)
                else
                  if state.val < 6464 then
                    packedStateVectorCodeChunk201 (state.val - 6432)
                  else
                    packedStateVectorCodeChunk202 (state.val - 6464)
              else
                if state.val < 6528 then
                  packedStateVectorCodeChunk203 (state.val - 6496)
                else
                  if state.val < 6560 then
                    packedStateVectorCodeChunk204 (state.val - 6528)
                  else
                    packedStateVectorCodeChunk205 (state.val - 6560)
        else
          if state.val < 6944 then
            if state.val < 6752 then
              if state.val < 6656 then
                if state.val < 6624 then
                  packedStateVectorCodeChunk206 (state.val - 6592)
                else
                  packedStateVectorCodeChunk207 (state.val - 6624)
              else
                if state.val < 6688 then
                  packedStateVectorCodeChunk208 (state.val - 6656)
                else
                  if state.val < 6720 then
                    packedStateVectorCodeChunk209 (state.val - 6688)
                  else
                    packedStateVectorCodeChunk210 (state.val - 6720)
            else
              if state.val < 6848 then
                if state.val < 6784 then
                  packedStateVectorCodeChunk211 (state.val - 6752)
                else
                  if state.val < 6816 then
                    packedStateVectorCodeChunk212 (state.val - 6784)
                  else
                    packedStateVectorCodeChunk213 (state.val - 6816)
              else
                if state.val < 6880 then
                  packedStateVectorCodeChunk214 (state.val - 6848)
                else
                  if state.val < 6912 then
                    packedStateVectorCodeChunk215 (state.val - 6880)
                  else
                    packedStateVectorCodeChunk216 (state.val - 6912)
          else
            if state.val < 7136 then
              if state.val < 7040 then
                if state.val < 6976 then
                  packedStateVectorCodeChunk217 (state.val - 6944)
                else
                  if state.val < 7008 then
                    packedStateVectorCodeChunk218 (state.val - 6976)
                  else
                    packedStateVectorCodeChunk219 (state.val - 7008)
              else
                if state.val < 7072 then
                  packedStateVectorCodeChunk220 (state.val - 7040)
                else
                  if state.val < 7104 then
                    packedStateVectorCodeChunk221 (state.val - 7072)
                  else
                    packedStateVectorCodeChunk222 (state.val - 7104)
            else
              if state.val < 7232 then
                if state.val < 7168 then
                  packedStateVectorCodeChunk223 (state.val - 7136)
                else
                  if state.val < 7200 then
                    packedStateVectorCodeChunk224 (state.val - 7168)
                  else
                    packedStateVectorCodeChunk225 (state.val - 7200)
              else
                if state.val < 7264 then
                  packedStateVectorCodeChunk226 (state.val - 7232)
                else
                  if state.val < 7296 then
                    packedStateVectorCodeChunk227 (state.val - 7264)
                  else
                    packedStateVectorCodeChunk228 (state.val - 7296)
      else
        if state.val < 8064 then
          if state.val < 7680 then
            if state.val < 7488 then
              if state.val < 7392 then
                if state.val < 7360 then
                  packedStateVectorCodeChunk229 (state.val - 7328)
                else
                  packedStateVectorCodeChunk230 (state.val - 7360)
              else
                if state.val < 7424 then
                  packedStateVectorCodeChunk231 (state.val - 7392)
                else
                  if state.val < 7456 then
                    packedStateVectorCodeChunk232 (state.val - 7424)
                  else
                    packedStateVectorCodeChunk233 (state.val - 7456)
            else
              if state.val < 7584 then
                if state.val < 7520 then
                  packedStateVectorCodeChunk234 (state.val - 7488)
                else
                  if state.val < 7552 then
                    packedStateVectorCodeChunk235 (state.val - 7520)
                  else
                    packedStateVectorCodeChunk236 (state.val - 7552)
              else
                if state.val < 7616 then
                  packedStateVectorCodeChunk237 (state.val - 7584)
                else
                  if state.val < 7648 then
                    packedStateVectorCodeChunk238 (state.val - 7616)
                  else
                    packedStateVectorCodeChunk239 (state.val - 7648)
          else
            if state.val < 7872 then
              if state.val < 7776 then
                if state.val < 7712 then
                  packedStateVectorCodeChunk240 (state.val - 7680)
                else
                  if state.val < 7744 then
                    packedStateVectorCodeChunk241 (state.val - 7712)
                  else
                    packedStateVectorCodeChunk242 (state.val - 7744)
              else
                if state.val < 7808 then
                  packedStateVectorCodeChunk243 (state.val - 7776)
                else
                  if state.val < 7840 then
                    packedStateVectorCodeChunk244 (state.val - 7808)
                  else
                    packedStateVectorCodeChunk245 (state.val - 7840)
            else
              if state.val < 7968 then
                if state.val < 7904 then
                  packedStateVectorCodeChunk246 (state.val - 7872)
                else
                  if state.val < 7936 then
                    packedStateVectorCodeChunk247 (state.val - 7904)
                  else
                    packedStateVectorCodeChunk248 (state.val - 7936)
              else
                if state.val < 8000 then
                  packedStateVectorCodeChunk249 (state.val - 7968)
                else
                  if state.val < 8032 then
                    packedStateVectorCodeChunk250 (state.val - 8000)
                  else
                    packedStateVectorCodeChunk251 (state.val - 8032)
        else
          if state.val < 8416 then
            if state.val < 8224 then
              if state.val < 8128 then
                if state.val < 8096 then
                  packedStateVectorCodeChunk252 (state.val - 8064)
                else
                  packedStateVectorCodeChunk253 (state.val - 8096)
              else
                if state.val < 8160 then
                  packedStateVectorCodeChunk254 (state.val - 8128)
                else
                  if state.val < 8192 then
                    packedStateVectorCodeChunk255 (state.val - 8160)
                  else
                    packedStateVectorCodeChunk256 (state.val - 8192)
            else
              if state.val < 8320 then
                if state.val < 8256 then
                  packedStateVectorCodeChunk257 (state.val - 8224)
                else
                  if state.val < 8288 then
                    packedStateVectorCodeChunk258 (state.val - 8256)
                  else
                    packedStateVectorCodeChunk259 (state.val - 8288)
              else
                if state.val < 8352 then
                  packedStateVectorCodeChunk260 (state.val - 8320)
                else
                  if state.val < 8384 then
                    packedStateVectorCodeChunk261 (state.val - 8352)
                  else
                    packedStateVectorCodeChunk262 (state.val - 8384)
          else
            if state.val < 8608 then
              if state.val < 8512 then
                if state.val < 8448 then
                  packedStateVectorCodeChunk263 (state.val - 8416)
                else
                  if state.val < 8480 then
                    packedStateVectorCodeChunk264 (state.val - 8448)
                  else
                    packedStateVectorCodeChunk265 (state.val - 8480)
              else
                if state.val < 8544 then
                  packedStateVectorCodeChunk266 (state.val - 8512)
                else
                  if state.val < 8576 then
                    packedStateVectorCodeChunk267 (state.val - 8544)
                  else
                    packedStateVectorCodeChunk268 (state.val - 8576)
            else
              if state.val < 8704 then
                if state.val < 8640 then
                  packedStateVectorCodeChunk269 (state.val - 8608)
                else
                  if state.val < 8672 then
                    packedStateVectorCodeChunk270 (state.val - 8640)
                  else
                    packedStateVectorCodeChunk271 (state.val - 8672)
              else
                if state.val < 8736 then
                  packedStateVectorCodeChunk272 (state.val - 8704)
                else
                  if state.val < 8768 then
                    packedStateVectorCodeChunk273 (state.val - 8736)
                  else
                    packedStateVectorCodeChunk274 (state.val - 8768)
    else
      if state.val < 10272 then
        if state.val < 9536 then
          if state.val < 9152 then
            if state.val < 8960 then
              if state.val < 8864 then
                if state.val < 8832 then
                  packedStateVectorCodeChunk275 (state.val - 8800)
                else
                  packedStateVectorCodeChunk276 (state.val - 8832)
              else
                if state.val < 8896 then
                  packedStateVectorCodeChunk277 (state.val - 8864)
                else
                  if state.val < 8928 then
                    packedStateVectorCodeChunk278 (state.val - 8896)
                  else
                    packedStateVectorCodeChunk279 (state.val - 8928)
            else
              if state.val < 9056 then
                if state.val < 8992 then
                  packedStateVectorCodeChunk280 (state.val - 8960)
                else
                  if state.val < 9024 then
                    packedStateVectorCodeChunk281 (state.val - 8992)
                  else
                    packedStateVectorCodeChunk282 (state.val - 9024)
              else
                if state.val < 9088 then
                  packedStateVectorCodeChunk283 (state.val - 9056)
                else
                  if state.val < 9120 then
                    packedStateVectorCodeChunk284 (state.val - 9088)
                  else
                    packedStateVectorCodeChunk285 (state.val - 9120)
          else
            if state.val < 9344 then
              if state.val < 9248 then
                if state.val < 9184 then
                  packedStateVectorCodeChunk286 (state.val - 9152)
                else
                  if state.val < 9216 then
                    packedStateVectorCodeChunk287 (state.val - 9184)
                  else
                    packedStateVectorCodeChunk288 (state.val - 9216)
              else
                if state.val < 9280 then
                  packedStateVectorCodeChunk289 (state.val - 9248)
                else
                  if state.val < 9312 then
                    packedStateVectorCodeChunk290 (state.val - 9280)
                  else
                    packedStateVectorCodeChunk291 (state.val - 9312)
            else
              if state.val < 9440 then
                if state.val < 9376 then
                  packedStateVectorCodeChunk292 (state.val - 9344)
                else
                  if state.val < 9408 then
                    packedStateVectorCodeChunk293 (state.val - 9376)
                  else
                    packedStateVectorCodeChunk294 (state.val - 9408)
              else
                if state.val < 9472 then
                  packedStateVectorCodeChunk295 (state.val - 9440)
                else
                  if state.val < 9504 then
                    packedStateVectorCodeChunk296 (state.val - 9472)
                  else
                    packedStateVectorCodeChunk297 (state.val - 9504)
        else
          if state.val < 9888 then
            if state.val < 9696 then
              if state.val < 9600 then
                if state.val < 9568 then
                  packedStateVectorCodeChunk298 (state.val - 9536)
                else
                  packedStateVectorCodeChunk299 (state.val - 9568)
              else
                if state.val < 9632 then
                  packedStateVectorCodeChunk300 (state.val - 9600)
                else
                  if state.val < 9664 then
                    packedStateVectorCodeChunk301 (state.val - 9632)
                  else
                    packedStateVectorCodeChunk302 (state.val - 9664)
            else
              if state.val < 9792 then
                if state.val < 9728 then
                  packedStateVectorCodeChunk303 (state.val - 9696)
                else
                  if state.val < 9760 then
                    packedStateVectorCodeChunk304 (state.val - 9728)
                  else
                    packedStateVectorCodeChunk305 (state.val - 9760)
              else
                if state.val < 9824 then
                  packedStateVectorCodeChunk306 (state.val - 9792)
                else
                  if state.val < 9856 then
                    packedStateVectorCodeChunk307 (state.val - 9824)
                  else
                    packedStateVectorCodeChunk308 (state.val - 9856)
          else
            if state.val < 10080 then
              if state.val < 9984 then
                if state.val < 9920 then
                  packedStateVectorCodeChunk309 (state.val - 9888)
                else
                  if state.val < 9952 then
                    packedStateVectorCodeChunk310 (state.val - 9920)
                  else
                    packedStateVectorCodeChunk311 (state.val - 9952)
              else
                if state.val < 10016 then
                  packedStateVectorCodeChunk312 (state.val - 9984)
                else
                  if state.val < 10048 then
                    packedStateVectorCodeChunk313 (state.val - 10016)
                  else
                    packedStateVectorCodeChunk314 (state.val - 10048)
            else
              if state.val < 10176 then
                if state.val < 10112 then
                  packedStateVectorCodeChunk315 (state.val - 10080)
                else
                  if state.val < 10144 then
                    packedStateVectorCodeChunk316 (state.val - 10112)
                  else
                    packedStateVectorCodeChunk317 (state.val - 10144)
              else
                if state.val < 10208 then
                  packedStateVectorCodeChunk318 (state.val - 10176)
                else
                  if state.val < 10240 then
                    packedStateVectorCodeChunk319 (state.val - 10208)
                  else
                    packedStateVectorCodeChunk320 (state.val - 10240)
      else
        if state.val < 11008 then
          if state.val < 10624 then
            if state.val < 10432 then
              if state.val < 10336 then
                if state.val < 10304 then
                  packedStateVectorCodeChunk321 (state.val - 10272)
                else
                  packedStateVectorCodeChunk322 (state.val - 10304)
              else
                if state.val < 10368 then
                  packedStateVectorCodeChunk323 (state.val - 10336)
                else
                  if state.val < 10400 then
                    packedStateVectorCodeChunk324 (state.val - 10368)
                  else
                    packedStateVectorCodeChunk325 (state.val - 10400)
            else
              if state.val < 10528 then
                if state.val < 10464 then
                  packedStateVectorCodeChunk326 (state.val - 10432)
                else
                  if state.val < 10496 then
                    packedStateVectorCodeChunk327 (state.val - 10464)
                  else
                    packedStateVectorCodeChunk328 (state.val - 10496)
              else
                if state.val < 10560 then
                  packedStateVectorCodeChunk329 (state.val - 10528)
                else
                  if state.val < 10592 then
                    packedStateVectorCodeChunk330 (state.val - 10560)
                  else
                    packedStateVectorCodeChunk331 (state.val - 10592)
          else
            if state.val < 10816 then
              if state.val < 10720 then
                if state.val < 10656 then
                  packedStateVectorCodeChunk332 (state.val - 10624)
                else
                  if state.val < 10688 then
                    packedStateVectorCodeChunk333 (state.val - 10656)
                  else
                    packedStateVectorCodeChunk334 (state.val - 10688)
              else
                if state.val < 10752 then
                  packedStateVectorCodeChunk335 (state.val - 10720)
                else
                  if state.val < 10784 then
                    packedStateVectorCodeChunk336 (state.val - 10752)
                  else
                    packedStateVectorCodeChunk337 (state.val - 10784)
            else
              if state.val < 10912 then
                if state.val < 10848 then
                  packedStateVectorCodeChunk338 (state.val - 10816)
                else
                  if state.val < 10880 then
                    packedStateVectorCodeChunk339 (state.val - 10848)
                  else
                    packedStateVectorCodeChunk340 (state.val - 10880)
              else
                if state.val < 10944 then
                  packedStateVectorCodeChunk341 (state.val - 10912)
                else
                  if state.val < 10976 then
                    packedStateVectorCodeChunk342 (state.val - 10944)
                  else
                    packedStateVectorCodeChunk343 (state.val - 10976)
        else
          if state.val < 11360 then
            if state.val < 11168 then
              if state.val < 11072 then
                if state.val < 11040 then
                  packedStateVectorCodeChunk344 (state.val - 11008)
                else
                  packedStateVectorCodeChunk345 (state.val - 11040)
              else
                if state.val < 11104 then
                  packedStateVectorCodeChunk346 (state.val - 11072)
                else
                  if state.val < 11136 then
                    packedStateVectorCodeChunk347 (state.val - 11104)
                  else
                    packedStateVectorCodeChunk348 (state.val - 11136)
            else
              if state.val < 11264 then
                if state.val < 11200 then
                  packedStateVectorCodeChunk349 (state.val - 11168)
                else
                  if state.val < 11232 then
                    packedStateVectorCodeChunk350 (state.val - 11200)
                  else
                    packedStateVectorCodeChunk351 (state.val - 11232)
              else
                if state.val < 11296 then
                  packedStateVectorCodeChunk352 (state.val - 11264)
                else
                  if state.val < 11328 then
                    packedStateVectorCodeChunk353 (state.val - 11296)
                  else
                    packedStateVectorCodeChunk354 (state.val - 11328)
          else
            if state.val < 11552 then
              if state.val < 11456 then
                if state.val < 11392 then
                  packedStateVectorCodeChunk355 (state.val - 11360)
                else
                  if state.val < 11424 then
                    packedStateVectorCodeChunk356 (state.val - 11392)
                  else
                    packedStateVectorCodeChunk357 (state.val - 11424)
              else
                if state.val < 11488 then
                  packedStateVectorCodeChunk358 (state.val - 11456)
                else
                  if state.val < 11520 then
                    packedStateVectorCodeChunk359 (state.val - 11488)
                  else
                    packedStateVectorCodeChunk360 (state.val - 11520)
            else
              if state.val < 11648 then
                if state.val < 11584 then
                  packedStateVectorCodeChunk361 (state.val - 11552)
                else
                  if state.val < 11616 then
                    packedStateVectorCodeChunk362 (state.val - 11584)
                  else
                    packedStateVectorCodeChunk363 (state.val - 11616)
              else
                if state.val < 11680 then
                  packedStateVectorCodeChunk364 (state.val - 11648)
                else
                  if state.val < 11712 then
                    packedStateVectorCodeChunk365 (state.val - 11680)
                  else
                    packedStateVectorCodeChunk366 (state.val - 11712)

def stateVector (state : Fin 11742)
    (coordinate : Fin 44) : Fin 6 :=
  ⟨(packedStateVectorCode state / 6 ^ coordinate.val) % 6,
    Nat.mod_lt _ (by decide)⟩

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.Shards
