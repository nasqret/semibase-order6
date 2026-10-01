import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.Shards.StateVectorPart00
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.Shards.StateVectorPart01
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.Shards.StateVectorPart02
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.Shards.StateVectorPart03
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.Shards.StateVectorPart04
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.Shards.StateVectorPart05
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.Shards.StateVectorPart06
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.Shards.StateVectorPart07
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.Shards.StateVectorPart08
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.Shards.StateVectorPart09
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.Shards.StateVectorPart10

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.Shards

def packedStateVectorCode (state : Fin 11184) : Nat :=
  if state.val < 5600 then
    if state.val < 2784 then
      if state.val < 1376 then
        if state.val < 672 then
          if state.val < 320 then
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
              if state.val < 224 then
                if state.val < 192 then
                  packedStateVectorCodeChunk5 (state.val - 160)
                else
                  packedStateVectorCodeChunk6 (state.val - 192)
              else
                if state.val < 256 then
                  packedStateVectorCodeChunk7 (state.val - 224)
                else
                  if state.val < 288 then
                    packedStateVectorCodeChunk8 (state.val - 256)
                  else
                    packedStateVectorCodeChunk9 (state.val - 288)
          else
            if state.val < 480 then
              if state.val < 384 then
                if state.val < 352 then
                  packedStateVectorCodeChunk10 (state.val - 320)
                else
                  packedStateVectorCodeChunk11 (state.val - 352)
              else
                if state.val < 416 then
                  packedStateVectorCodeChunk12 (state.val - 384)
                else
                  if state.val < 448 then
                    packedStateVectorCodeChunk13 (state.val - 416)
                  else
                    packedStateVectorCodeChunk14 (state.val - 448)
            else
              if state.val < 576 then
                if state.val < 512 then
                  packedStateVectorCodeChunk15 (state.val - 480)
                else
                  if state.val < 544 then
                    packedStateVectorCodeChunk16 (state.val - 512)
                  else
                    packedStateVectorCodeChunk17 (state.val - 544)
              else
                if state.val < 608 then
                  packedStateVectorCodeChunk18 (state.val - 576)
                else
                  if state.val < 640 then
                    packedStateVectorCodeChunk19 (state.val - 608)
                  else
                    packedStateVectorCodeChunk20 (state.val - 640)
        else
          if state.val < 1024 then
            if state.val < 832 then
              if state.val < 736 then
                if state.val < 704 then
                  packedStateVectorCodeChunk21 (state.val - 672)
                else
                  packedStateVectorCodeChunk22 (state.val - 704)
              else
                if state.val < 768 then
                  packedStateVectorCodeChunk23 (state.val - 736)
                else
                  if state.val < 800 then
                    packedStateVectorCodeChunk24 (state.val - 768)
                  else
                    packedStateVectorCodeChunk25 (state.val - 800)
            else
              if state.val < 928 then
                if state.val < 864 then
                  packedStateVectorCodeChunk26 (state.val - 832)
                else
                  if state.val < 896 then
                    packedStateVectorCodeChunk27 (state.val - 864)
                  else
                    packedStateVectorCodeChunk28 (state.val - 896)
              else
                if state.val < 960 then
                  packedStateVectorCodeChunk29 (state.val - 928)
                else
                  if state.val < 992 then
                    packedStateVectorCodeChunk30 (state.val - 960)
                  else
                    packedStateVectorCodeChunk31 (state.val - 992)
          else
            if state.val < 1184 then
              if state.val < 1088 then
                if state.val < 1056 then
                  packedStateVectorCodeChunk32 (state.val - 1024)
                else
                  packedStateVectorCodeChunk33 (state.val - 1056)
              else
                if state.val < 1120 then
                  packedStateVectorCodeChunk34 (state.val - 1088)
                else
                  if state.val < 1152 then
                    packedStateVectorCodeChunk35 (state.val - 1120)
                  else
                    packedStateVectorCodeChunk36 (state.val - 1152)
            else
              if state.val < 1280 then
                if state.val < 1216 then
                  packedStateVectorCodeChunk37 (state.val - 1184)
                else
                  if state.val < 1248 then
                    packedStateVectorCodeChunk38 (state.val - 1216)
                  else
                    packedStateVectorCodeChunk39 (state.val - 1248)
              else
                if state.val < 1312 then
                  packedStateVectorCodeChunk40 (state.val - 1280)
                else
                  if state.val < 1344 then
                    packedStateVectorCodeChunk41 (state.val - 1312)
                  else
                    packedStateVectorCodeChunk42 (state.val - 1344)
      else
        if state.val < 2080 then
          if state.val < 1728 then
            if state.val < 1536 then
              if state.val < 1440 then
                if state.val < 1408 then
                  packedStateVectorCodeChunk43 (state.val - 1376)
                else
                  packedStateVectorCodeChunk44 (state.val - 1408)
              else
                if state.val < 1472 then
                  packedStateVectorCodeChunk45 (state.val - 1440)
                else
                  if state.val < 1504 then
                    packedStateVectorCodeChunk46 (state.val - 1472)
                  else
                    packedStateVectorCodeChunk47 (state.val - 1504)
            else
              if state.val < 1632 then
                if state.val < 1568 then
                  packedStateVectorCodeChunk48 (state.val - 1536)
                else
                  if state.val < 1600 then
                    packedStateVectorCodeChunk49 (state.val - 1568)
                  else
                    packedStateVectorCodeChunk50 (state.val - 1600)
              else
                if state.val < 1664 then
                  packedStateVectorCodeChunk51 (state.val - 1632)
                else
                  if state.val < 1696 then
                    packedStateVectorCodeChunk52 (state.val - 1664)
                  else
                    packedStateVectorCodeChunk53 (state.val - 1696)
          else
            if state.val < 1888 then
              if state.val < 1792 then
                if state.val < 1760 then
                  packedStateVectorCodeChunk54 (state.val - 1728)
                else
                  packedStateVectorCodeChunk55 (state.val - 1760)
              else
                if state.val < 1824 then
                  packedStateVectorCodeChunk56 (state.val - 1792)
                else
                  if state.val < 1856 then
                    packedStateVectorCodeChunk57 (state.val - 1824)
                  else
                    packedStateVectorCodeChunk58 (state.val - 1856)
            else
              if state.val < 1984 then
                if state.val < 1920 then
                  packedStateVectorCodeChunk59 (state.val - 1888)
                else
                  if state.val < 1952 then
                    packedStateVectorCodeChunk60 (state.val - 1920)
                  else
                    packedStateVectorCodeChunk61 (state.val - 1952)
              else
                if state.val < 2016 then
                  packedStateVectorCodeChunk62 (state.val - 1984)
                else
                  if state.val < 2048 then
                    packedStateVectorCodeChunk63 (state.val - 2016)
                  else
                    packedStateVectorCodeChunk64 (state.val - 2048)
        else
          if state.val < 2432 then
            if state.val < 2240 then
              if state.val < 2144 then
                if state.val < 2112 then
                  packedStateVectorCodeChunk65 (state.val - 2080)
                else
                  packedStateVectorCodeChunk66 (state.val - 2112)
              else
                if state.val < 2176 then
                  packedStateVectorCodeChunk67 (state.val - 2144)
                else
                  if state.val < 2208 then
                    packedStateVectorCodeChunk68 (state.val - 2176)
                  else
                    packedStateVectorCodeChunk69 (state.val - 2208)
            else
              if state.val < 2336 then
                if state.val < 2272 then
                  packedStateVectorCodeChunk70 (state.val - 2240)
                else
                  if state.val < 2304 then
                    packedStateVectorCodeChunk71 (state.val - 2272)
                  else
                    packedStateVectorCodeChunk72 (state.val - 2304)
              else
                if state.val < 2368 then
                  packedStateVectorCodeChunk73 (state.val - 2336)
                else
                  if state.val < 2400 then
                    packedStateVectorCodeChunk74 (state.val - 2368)
                  else
                    packedStateVectorCodeChunk75 (state.val - 2400)
          else
            if state.val < 2592 then
              if state.val < 2496 then
                if state.val < 2464 then
                  packedStateVectorCodeChunk76 (state.val - 2432)
                else
                  packedStateVectorCodeChunk77 (state.val - 2464)
              else
                if state.val < 2528 then
                  packedStateVectorCodeChunk78 (state.val - 2496)
                else
                  if state.val < 2560 then
                    packedStateVectorCodeChunk79 (state.val - 2528)
                  else
                    packedStateVectorCodeChunk80 (state.val - 2560)
            else
              if state.val < 2688 then
                if state.val < 2624 then
                  packedStateVectorCodeChunk81 (state.val - 2592)
                else
                  if state.val < 2656 then
                    packedStateVectorCodeChunk82 (state.val - 2624)
                  else
                    packedStateVectorCodeChunk83 (state.val - 2656)
              else
                if state.val < 2720 then
                  packedStateVectorCodeChunk84 (state.val - 2688)
                else
                  if state.val < 2752 then
                    packedStateVectorCodeChunk85 (state.val - 2720)
                  else
                    packedStateVectorCodeChunk86 (state.val - 2752)
    else
      if state.val < 4192 then
        if state.val < 3488 then
          if state.val < 3136 then
            if state.val < 2944 then
              if state.val < 2848 then
                if state.val < 2816 then
                  packedStateVectorCodeChunk87 (state.val - 2784)
                else
                  packedStateVectorCodeChunk88 (state.val - 2816)
              else
                if state.val < 2880 then
                  packedStateVectorCodeChunk89 (state.val - 2848)
                else
                  if state.val < 2912 then
                    packedStateVectorCodeChunk90 (state.val - 2880)
                  else
                    packedStateVectorCodeChunk91 (state.val - 2912)
            else
              if state.val < 3040 then
                if state.val < 2976 then
                  packedStateVectorCodeChunk92 (state.val - 2944)
                else
                  if state.val < 3008 then
                    packedStateVectorCodeChunk93 (state.val - 2976)
                  else
                    packedStateVectorCodeChunk94 (state.val - 3008)
              else
                if state.val < 3072 then
                  packedStateVectorCodeChunk95 (state.val - 3040)
                else
                  if state.val < 3104 then
                    packedStateVectorCodeChunk96 (state.val - 3072)
                  else
                    packedStateVectorCodeChunk97 (state.val - 3104)
          else
            if state.val < 3296 then
              if state.val < 3200 then
                if state.val < 3168 then
                  packedStateVectorCodeChunk98 (state.val - 3136)
                else
                  packedStateVectorCodeChunk99 (state.val - 3168)
              else
                if state.val < 3232 then
                  packedStateVectorCodeChunk100 (state.val - 3200)
                else
                  if state.val < 3264 then
                    packedStateVectorCodeChunk101 (state.val - 3232)
                  else
                    packedStateVectorCodeChunk102 (state.val - 3264)
            else
              if state.val < 3392 then
                if state.val < 3328 then
                  packedStateVectorCodeChunk103 (state.val - 3296)
                else
                  if state.val < 3360 then
                    packedStateVectorCodeChunk104 (state.val - 3328)
                  else
                    packedStateVectorCodeChunk105 (state.val - 3360)
              else
                if state.val < 3424 then
                  packedStateVectorCodeChunk106 (state.val - 3392)
                else
                  if state.val < 3456 then
                    packedStateVectorCodeChunk107 (state.val - 3424)
                  else
                    packedStateVectorCodeChunk108 (state.val - 3456)
        else
          if state.val < 3840 then
            if state.val < 3648 then
              if state.val < 3552 then
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
              if state.val < 3744 then
                if state.val < 3680 then
                  packedStateVectorCodeChunk114 (state.val - 3648)
                else
                  if state.val < 3712 then
                    packedStateVectorCodeChunk115 (state.val - 3680)
                  else
                    packedStateVectorCodeChunk116 (state.val - 3712)
              else
                if state.val < 3776 then
                  packedStateVectorCodeChunk117 (state.val - 3744)
                else
                  if state.val < 3808 then
                    packedStateVectorCodeChunk118 (state.val - 3776)
                  else
                    packedStateVectorCodeChunk119 (state.val - 3808)
          else
            if state.val < 4000 then
              if state.val < 3904 then
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
        if state.val < 4896 then
          if state.val < 4544 then
            if state.val < 4352 then
              if state.val < 4256 then
                if state.val < 4224 then
                  packedStateVectorCodeChunk131 (state.val - 4192)
                else
                  packedStateVectorCodeChunk132 (state.val - 4224)
              else
                if state.val < 4288 then
                  packedStateVectorCodeChunk133 (state.val - 4256)
                else
                  if state.val < 4320 then
                    packedStateVectorCodeChunk134 (state.val - 4288)
                  else
                    packedStateVectorCodeChunk135 (state.val - 4320)
            else
              if state.val < 4448 then
                if state.val < 4384 then
                  packedStateVectorCodeChunk136 (state.val - 4352)
                else
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
            if state.val < 4704 then
              if state.val < 4608 then
                if state.val < 4576 then
                  packedStateVectorCodeChunk142 (state.val - 4544)
                else
                  packedStateVectorCodeChunk143 (state.val - 4576)
              else
                if state.val < 4640 then
                  packedStateVectorCodeChunk144 (state.val - 4608)
                else
                  if state.val < 4672 then
                    packedStateVectorCodeChunk145 (state.val - 4640)
                  else
                    packedStateVectorCodeChunk146 (state.val - 4672)
            else
              if state.val < 4800 then
                if state.val < 4736 then
                  packedStateVectorCodeChunk147 (state.val - 4704)
                else
                  if state.val < 4768 then
                    packedStateVectorCodeChunk148 (state.val - 4736)
                  else
                    packedStateVectorCodeChunk149 (state.val - 4768)
              else
                if state.val < 4832 then
                  packedStateVectorCodeChunk150 (state.val - 4800)
                else
                  if state.val < 4864 then
                    packedStateVectorCodeChunk151 (state.val - 4832)
                  else
                    packedStateVectorCodeChunk152 (state.val - 4864)
        else
          if state.val < 5248 then
            if state.val < 5056 then
              if state.val < 4960 then
                if state.val < 4928 then
                  packedStateVectorCodeChunk153 (state.val - 4896)
                else
                  packedStateVectorCodeChunk154 (state.val - 4928)
              else
                if state.val < 4992 then
                  packedStateVectorCodeChunk155 (state.val - 4960)
                else
                  if state.val < 5024 then
                    packedStateVectorCodeChunk156 (state.val - 4992)
                  else
                    packedStateVectorCodeChunk157 (state.val - 5024)
            else
              if state.val < 5152 then
                if state.val < 5088 then
                  packedStateVectorCodeChunk158 (state.val - 5056)
                else
                  if state.val < 5120 then
                    packedStateVectorCodeChunk159 (state.val - 5088)
                  else
                    packedStateVectorCodeChunk160 (state.val - 5120)
              else
                if state.val < 5184 then
                  packedStateVectorCodeChunk161 (state.val - 5152)
                else
                  if state.val < 5216 then
                    packedStateVectorCodeChunk162 (state.val - 5184)
                  else
                    packedStateVectorCodeChunk163 (state.val - 5216)
          else
            if state.val < 5408 then
              if state.val < 5312 then
                if state.val < 5280 then
                  packedStateVectorCodeChunk164 (state.val - 5248)
                else
                  packedStateVectorCodeChunk165 (state.val - 5280)
              else
                if state.val < 5344 then
                  packedStateVectorCodeChunk166 (state.val - 5312)
                else
                  if state.val < 5376 then
                    packedStateVectorCodeChunk167 (state.val - 5344)
                  else
                    packedStateVectorCodeChunk168 (state.val - 5376)
            else
              if state.val < 5504 then
                if state.val < 5440 then
                  packedStateVectorCodeChunk169 (state.val - 5408)
                else
                  if state.val < 5472 then
                    packedStateVectorCodeChunk170 (state.val - 5440)
                  else
                    packedStateVectorCodeChunk171 (state.val - 5472)
              else
                if state.val < 5536 then
                  packedStateVectorCodeChunk172 (state.val - 5504)
                else
                  if state.val < 5568 then
                    packedStateVectorCodeChunk173 (state.val - 5536)
                  else
                    packedStateVectorCodeChunk174 (state.val - 5568)
  else
    if state.val < 8384 then
      if state.val < 6976 then
        if state.val < 6272 then
          if state.val < 5920 then
            if state.val < 5760 then
              if state.val < 5664 then
                if state.val < 5632 then
                  packedStateVectorCodeChunk175 (state.val - 5600)
                else
                  packedStateVectorCodeChunk176 (state.val - 5632)
              else
                if state.val < 5696 then
                  packedStateVectorCodeChunk177 (state.val - 5664)
                else
                  if state.val < 5728 then
                    packedStateVectorCodeChunk178 (state.val - 5696)
                  else
                    packedStateVectorCodeChunk179 (state.val - 5728)
            else
              if state.val < 5824 then
                if state.val < 5792 then
                  packedStateVectorCodeChunk180 (state.val - 5760)
                else
                  packedStateVectorCodeChunk181 (state.val - 5792)
              else
                if state.val < 5856 then
                  packedStateVectorCodeChunk182 (state.val - 5824)
                else
                  if state.val < 5888 then
                    packedStateVectorCodeChunk183 (state.val - 5856)
                  else
                    packedStateVectorCodeChunk184 (state.val - 5888)
          else
            if state.val < 6080 then
              if state.val < 5984 then
                if state.val < 5952 then
                  packedStateVectorCodeChunk185 (state.val - 5920)
                else
                  packedStateVectorCodeChunk186 (state.val - 5952)
              else
                if state.val < 6016 then
                  packedStateVectorCodeChunk187 (state.val - 5984)
                else
                  if state.val < 6048 then
                    packedStateVectorCodeChunk188 (state.val - 6016)
                  else
                    packedStateVectorCodeChunk189 (state.val - 6048)
            else
              if state.val < 6176 then
                if state.val < 6112 then
                  packedStateVectorCodeChunk190 (state.val - 6080)
                else
                  if state.val < 6144 then
                    packedStateVectorCodeChunk191 (state.val - 6112)
                  else
                    packedStateVectorCodeChunk192 (state.val - 6144)
              else
                if state.val < 6208 then
                  packedStateVectorCodeChunk193 (state.val - 6176)
                else
                  if state.val < 6240 then
                    packedStateVectorCodeChunk194 (state.val - 6208)
                  else
                    packedStateVectorCodeChunk195 (state.val - 6240)
        else
          if state.val < 6624 then
            if state.val < 6432 then
              if state.val < 6336 then
                if state.val < 6304 then
                  packedStateVectorCodeChunk196 (state.val - 6272)
                else
                  packedStateVectorCodeChunk197 (state.val - 6304)
              else
                if state.val < 6368 then
                  packedStateVectorCodeChunk198 (state.val - 6336)
                else
                  if state.val < 6400 then
                    packedStateVectorCodeChunk199 (state.val - 6368)
                  else
                    packedStateVectorCodeChunk200 (state.val - 6400)
            else
              if state.val < 6528 then
                if state.val < 6464 then
                  packedStateVectorCodeChunk201 (state.val - 6432)
                else
                  if state.val < 6496 then
                    packedStateVectorCodeChunk202 (state.val - 6464)
                  else
                    packedStateVectorCodeChunk203 (state.val - 6496)
              else
                if state.val < 6560 then
                  packedStateVectorCodeChunk204 (state.val - 6528)
                else
                  if state.val < 6592 then
                    packedStateVectorCodeChunk205 (state.val - 6560)
                  else
                    packedStateVectorCodeChunk206 (state.val - 6592)
          else
            if state.val < 6784 then
              if state.val < 6688 then
                if state.val < 6656 then
                  packedStateVectorCodeChunk207 (state.val - 6624)
                else
                  packedStateVectorCodeChunk208 (state.val - 6656)
              else
                if state.val < 6720 then
                  packedStateVectorCodeChunk209 (state.val - 6688)
                else
                  if state.val < 6752 then
                    packedStateVectorCodeChunk210 (state.val - 6720)
                  else
                    packedStateVectorCodeChunk211 (state.val - 6752)
            else
              if state.val < 6880 then
                if state.val < 6816 then
                  packedStateVectorCodeChunk212 (state.val - 6784)
                else
                  if state.val < 6848 then
                    packedStateVectorCodeChunk213 (state.val - 6816)
                  else
                    packedStateVectorCodeChunk214 (state.val - 6848)
              else
                if state.val < 6912 then
                  packedStateVectorCodeChunk215 (state.val - 6880)
                else
                  if state.val < 6944 then
                    packedStateVectorCodeChunk216 (state.val - 6912)
                  else
                    packedStateVectorCodeChunk217 (state.val - 6944)
      else
        if state.val < 7680 then
          if state.val < 7328 then
            if state.val < 7136 then
              if state.val < 7040 then
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
          if state.val < 8032 then
            if state.val < 7840 then
              if state.val < 7744 then
                if state.val < 7712 then
                  packedStateVectorCodeChunk240 (state.val - 7680)
                else
                  packedStateVectorCodeChunk241 (state.val - 7712)
              else
                if state.val < 7776 then
                  packedStateVectorCodeChunk242 (state.val - 7744)
                else
                  if state.val < 7808 then
                    packedStateVectorCodeChunk243 (state.val - 7776)
                  else
                    packedStateVectorCodeChunk244 (state.val - 7808)
            else
              if state.val < 7936 then
                if state.val < 7872 then
                  packedStateVectorCodeChunk245 (state.val - 7840)
                else
                  if state.val < 7904 then
                    packedStateVectorCodeChunk246 (state.val - 7872)
                  else
                    packedStateVectorCodeChunk247 (state.val - 7904)
              else
                if state.val < 7968 then
                  packedStateVectorCodeChunk248 (state.val - 7936)
                else
                  if state.val < 8000 then
                    packedStateVectorCodeChunk249 (state.val - 7968)
                  else
                    packedStateVectorCodeChunk250 (state.val - 8000)
          else
            if state.val < 8192 then
              if state.val < 8096 then
                if state.val < 8064 then
                  packedStateVectorCodeChunk251 (state.val - 8032)
                else
                  packedStateVectorCodeChunk252 (state.val - 8064)
              else
                if state.val < 8128 then
                  packedStateVectorCodeChunk253 (state.val - 8096)
                else
                  if state.val < 8160 then
                    packedStateVectorCodeChunk254 (state.val - 8128)
                  else
                    packedStateVectorCodeChunk255 (state.val - 8160)
            else
              if state.val < 8288 then
                if state.val < 8224 then
                  packedStateVectorCodeChunk256 (state.val - 8192)
                else
                  if state.val < 8256 then
                    packedStateVectorCodeChunk257 (state.val - 8224)
                  else
                    packedStateVectorCodeChunk258 (state.val - 8256)
              else
                if state.val < 8320 then
                  packedStateVectorCodeChunk259 (state.val - 8288)
                else
                  if state.val < 8352 then
                    packedStateVectorCodeChunk260 (state.val - 8320)
                  else
                    packedStateVectorCodeChunk261 (state.val - 8352)
    else
      if state.val < 9792 then
        if state.val < 9088 then
          if state.val < 8736 then
            if state.val < 8544 then
              if state.val < 8448 then
                if state.val < 8416 then
                  packedStateVectorCodeChunk262 (state.val - 8384)
                else
                  packedStateVectorCodeChunk263 (state.val - 8416)
              else
                if state.val < 8480 then
                  packedStateVectorCodeChunk264 (state.val - 8448)
                else
                  if state.val < 8512 then
                    packedStateVectorCodeChunk265 (state.val - 8480)
                  else
                    packedStateVectorCodeChunk266 (state.val - 8512)
            else
              if state.val < 8640 then
                if state.val < 8576 then
                  packedStateVectorCodeChunk267 (state.val - 8544)
                else
                  if state.val < 8608 then
                    packedStateVectorCodeChunk268 (state.val - 8576)
                  else
                    packedStateVectorCodeChunk269 (state.val - 8608)
              else
                if state.val < 8672 then
                  packedStateVectorCodeChunk270 (state.val - 8640)
                else
                  if state.val < 8704 then
                    packedStateVectorCodeChunk271 (state.val - 8672)
                  else
                    packedStateVectorCodeChunk272 (state.val - 8704)
          else
            if state.val < 8896 then
              if state.val < 8800 then
                if state.val < 8768 then
                  packedStateVectorCodeChunk273 (state.val - 8736)
                else
                  packedStateVectorCodeChunk274 (state.val - 8768)
              else
                if state.val < 8832 then
                  packedStateVectorCodeChunk275 (state.val - 8800)
                else
                  if state.val < 8864 then
                    packedStateVectorCodeChunk276 (state.val - 8832)
                  else
                    packedStateVectorCodeChunk277 (state.val - 8864)
            else
              if state.val < 8992 then
                if state.val < 8928 then
                  packedStateVectorCodeChunk278 (state.val - 8896)
                else
                  if state.val < 8960 then
                    packedStateVectorCodeChunk279 (state.val - 8928)
                  else
                    packedStateVectorCodeChunk280 (state.val - 8960)
              else
                if state.val < 9024 then
                  packedStateVectorCodeChunk281 (state.val - 8992)
                else
                  if state.val < 9056 then
                    packedStateVectorCodeChunk282 (state.val - 9024)
                  else
                    packedStateVectorCodeChunk283 (state.val - 9056)
        else
          if state.val < 9440 then
            if state.val < 9248 then
              if state.val < 9152 then
                if state.val < 9120 then
                  packedStateVectorCodeChunk284 (state.val - 9088)
                else
                  packedStateVectorCodeChunk285 (state.val - 9120)
              else
                if state.val < 9184 then
                  packedStateVectorCodeChunk286 (state.val - 9152)
                else
                  if state.val < 9216 then
                    packedStateVectorCodeChunk287 (state.val - 9184)
                  else
                    packedStateVectorCodeChunk288 (state.val - 9216)
            else
              if state.val < 9344 then
                if state.val < 9280 then
                  packedStateVectorCodeChunk289 (state.val - 9248)
                else
                  if state.val < 9312 then
                    packedStateVectorCodeChunk290 (state.val - 9280)
                  else
                    packedStateVectorCodeChunk291 (state.val - 9312)
              else
                if state.val < 9376 then
                  packedStateVectorCodeChunk292 (state.val - 9344)
                else
                  if state.val < 9408 then
                    packedStateVectorCodeChunk293 (state.val - 9376)
                  else
                    packedStateVectorCodeChunk294 (state.val - 9408)
          else
            if state.val < 9600 then
              if state.val < 9504 then
                if state.val < 9472 then
                  packedStateVectorCodeChunk295 (state.val - 9440)
                else
                  packedStateVectorCodeChunk296 (state.val - 9472)
              else
                if state.val < 9536 then
                  packedStateVectorCodeChunk297 (state.val - 9504)
                else
                  if state.val < 9568 then
                    packedStateVectorCodeChunk298 (state.val - 9536)
                  else
                    packedStateVectorCodeChunk299 (state.val - 9568)
            else
              if state.val < 9696 then
                if state.val < 9632 then
                  packedStateVectorCodeChunk300 (state.val - 9600)
                else
                  if state.val < 9664 then
                    packedStateVectorCodeChunk301 (state.val - 9632)
                  else
                    packedStateVectorCodeChunk302 (state.val - 9664)
              else
                if state.val < 9728 then
                  packedStateVectorCodeChunk303 (state.val - 9696)
                else
                  if state.val < 9760 then
                    packedStateVectorCodeChunk304 (state.val - 9728)
                  else
                    packedStateVectorCodeChunk305 (state.val - 9760)
      else
        if state.val < 10496 then
          if state.val < 10144 then
            if state.val < 9952 then
              if state.val < 9856 then
                if state.val < 9824 then
                  packedStateVectorCodeChunk306 (state.val - 9792)
                else
                  packedStateVectorCodeChunk307 (state.val - 9824)
              else
                if state.val < 9888 then
                  packedStateVectorCodeChunk308 (state.val - 9856)
                else
                  if state.val < 9920 then
                    packedStateVectorCodeChunk309 (state.val - 9888)
                  else
                    packedStateVectorCodeChunk310 (state.val - 9920)
            else
              if state.val < 10048 then
                if state.val < 9984 then
                  packedStateVectorCodeChunk311 (state.val - 9952)
                else
                  if state.val < 10016 then
                    packedStateVectorCodeChunk312 (state.val - 9984)
                  else
                    packedStateVectorCodeChunk313 (state.val - 10016)
              else
                if state.val < 10080 then
                  packedStateVectorCodeChunk314 (state.val - 10048)
                else
                  if state.val < 10112 then
                    packedStateVectorCodeChunk315 (state.val - 10080)
                  else
                    packedStateVectorCodeChunk316 (state.val - 10112)
          else
            if state.val < 10304 then
              if state.val < 10208 then
                if state.val < 10176 then
                  packedStateVectorCodeChunk317 (state.val - 10144)
                else
                  packedStateVectorCodeChunk318 (state.val - 10176)
              else
                if state.val < 10240 then
                  packedStateVectorCodeChunk319 (state.val - 10208)
                else
                  if state.val < 10272 then
                    packedStateVectorCodeChunk320 (state.val - 10240)
                  else
                    packedStateVectorCodeChunk321 (state.val - 10272)
            else
              if state.val < 10400 then
                if state.val < 10336 then
                  packedStateVectorCodeChunk322 (state.val - 10304)
                else
                  if state.val < 10368 then
                    packedStateVectorCodeChunk323 (state.val - 10336)
                  else
                    packedStateVectorCodeChunk324 (state.val - 10368)
              else
                if state.val < 10432 then
                  packedStateVectorCodeChunk325 (state.val - 10400)
                else
                  if state.val < 10464 then
                    packedStateVectorCodeChunk326 (state.val - 10432)
                  else
                    packedStateVectorCodeChunk327 (state.val - 10464)
        else
          if state.val < 10848 then
            if state.val < 10656 then
              if state.val < 10560 then
                if state.val < 10528 then
                  packedStateVectorCodeChunk328 (state.val - 10496)
                else
                  packedStateVectorCodeChunk329 (state.val - 10528)
              else
                if state.val < 10592 then
                  packedStateVectorCodeChunk330 (state.val - 10560)
                else
                  if state.val < 10624 then
                    packedStateVectorCodeChunk331 (state.val - 10592)
                  else
                    packedStateVectorCodeChunk332 (state.val - 10624)
            else
              if state.val < 10752 then
                if state.val < 10688 then
                  packedStateVectorCodeChunk333 (state.val - 10656)
                else
                  if state.val < 10720 then
                    packedStateVectorCodeChunk334 (state.val - 10688)
                  else
                    packedStateVectorCodeChunk335 (state.val - 10720)
              else
                if state.val < 10784 then
                  packedStateVectorCodeChunk336 (state.val - 10752)
                else
                  if state.val < 10816 then
                    packedStateVectorCodeChunk337 (state.val - 10784)
                  else
                    packedStateVectorCodeChunk338 (state.val - 10816)
          else
            if state.val < 11008 then
              if state.val < 10912 then
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
              if state.val < 11104 then
                if state.val < 11040 then
                  packedStateVectorCodeChunk344 (state.val - 11008)
                else
                  if state.val < 11072 then
                    packedStateVectorCodeChunk345 (state.val - 11040)
                  else
                    packedStateVectorCodeChunk346 (state.val - 11072)
              else
                if state.val < 11136 then
                  packedStateVectorCodeChunk347 (state.val - 11104)
                else
                  if state.val < 11168 then
                    packedStateVectorCodeChunk348 (state.val - 11136)
                  else
                    packedStateVectorCodeChunk349 (state.val - 11168)

def stateVector (state : Fin 11184)
    (coordinate : Fin 37) : Fin 6 :=
  ⟨(packedStateVectorCode state / 6 ^ coordinate.val) % 6,
    Nat.mod_lt _ (by decide)⟩

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.Shards
