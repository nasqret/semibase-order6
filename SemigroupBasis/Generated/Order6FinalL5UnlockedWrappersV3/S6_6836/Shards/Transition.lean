import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6836.Shards.TransitionPart00
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6836.Shards.TransitionPart01
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6836.Shards.TransitionPart02
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6836.Shards.TransitionPart03
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6836.Shards.TransitionPart04
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6836.Shards.TransitionPart05
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6836.Shards.TransitionPart06
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6836.Shards.TransitionPart07

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6836.Shards

def packedTransitionCode (state : Fin 7782) : Nat :=
  if state.val < 3904 then
    if state.val < 1952 then
      if state.val < 960 then
        if state.val < 480 then
          if state.val < 224 then
            if state.val < 96 then
              if state.val < 32 then
                packedTransitionCodeChunk0 state.val
              else
                if state.val < 64 then
                  packedTransitionCodeChunk1 (state.val - 32)
                else
                  packedTransitionCodeChunk2 (state.val - 64)
            else
              if state.val < 160 then
                if state.val < 128 then
                  packedTransitionCodeChunk3 (state.val - 96)
                else
                  packedTransitionCodeChunk4 (state.val - 128)
              else
                if state.val < 192 then
                  packedTransitionCodeChunk5 (state.val - 160)
                else
                  packedTransitionCodeChunk6 (state.val - 192)
          else
            if state.val < 352 then
              if state.val < 288 then
                if state.val < 256 then
                  packedTransitionCodeChunk7 (state.val - 224)
                else
                  packedTransitionCodeChunk8 (state.val - 256)
              else
                if state.val < 320 then
                  packedTransitionCodeChunk9 (state.val - 288)
                else
                  packedTransitionCodeChunk10 (state.val - 320)
            else
              if state.val < 416 then
                if state.val < 384 then
                  packedTransitionCodeChunk11 (state.val - 352)
                else
                  packedTransitionCodeChunk12 (state.val - 384)
              else
                if state.val < 448 then
                  packedTransitionCodeChunk13 (state.val - 416)
                else
                  packedTransitionCodeChunk14 (state.val - 448)
        else
          if state.val < 704 then
            if state.val < 576 then
              if state.val < 512 then
                packedTransitionCodeChunk15 (state.val - 480)
              else
                if state.val < 544 then
                  packedTransitionCodeChunk16 (state.val - 512)
                else
                  packedTransitionCodeChunk17 (state.val - 544)
            else
              if state.val < 640 then
                if state.val < 608 then
                  packedTransitionCodeChunk18 (state.val - 576)
                else
                  packedTransitionCodeChunk19 (state.val - 608)
              else
                if state.val < 672 then
                  packedTransitionCodeChunk20 (state.val - 640)
                else
                  packedTransitionCodeChunk21 (state.val - 672)
          else
            if state.val < 832 then
              if state.val < 768 then
                if state.val < 736 then
                  packedTransitionCodeChunk22 (state.val - 704)
                else
                  packedTransitionCodeChunk23 (state.val - 736)
              else
                if state.val < 800 then
                  packedTransitionCodeChunk24 (state.val - 768)
                else
                  packedTransitionCodeChunk25 (state.val - 800)
            else
              if state.val < 896 then
                if state.val < 864 then
                  packedTransitionCodeChunk26 (state.val - 832)
                else
                  packedTransitionCodeChunk27 (state.val - 864)
              else
                if state.val < 928 then
                  packedTransitionCodeChunk28 (state.val - 896)
                else
                  packedTransitionCodeChunk29 (state.val - 928)
      else
        if state.val < 1440 then
          if state.val < 1184 then
            if state.val < 1056 then
              if state.val < 992 then
                packedTransitionCodeChunk30 (state.val - 960)
              else
                if state.val < 1024 then
                  packedTransitionCodeChunk31 (state.val - 992)
                else
                  packedTransitionCodeChunk32 (state.val - 1024)
            else
              if state.val < 1120 then
                if state.val < 1088 then
                  packedTransitionCodeChunk33 (state.val - 1056)
                else
                  packedTransitionCodeChunk34 (state.val - 1088)
              else
                if state.val < 1152 then
                  packedTransitionCodeChunk35 (state.val - 1120)
                else
                  packedTransitionCodeChunk36 (state.val - 1152)
          else
            if state.val < 1312 then
              if state.val < 1248 then
                if state.val < 1216 then
                  packedTransitionCodeChunk37 (state.val - 1184)
                else
                  packedTransitionCodeChunk38 (state.val - 1216)
              else
                if state.val < 1280 then
                  packedTransitionCodeChunk39 (state.val - 1248)
                else
                  packedTransitionCodeChunk40 (state.val - 1280)
            else
              if state.val < 1376 then
                if state.val < 1344 then
                  packedTransitionCodeChunk41 (state.val - 1312)
                else
                  packedTransitionCodeChunk42 (state.val - 1344)
              else
                if state.val < 1408 then
                  packedTransitionCodeChunk43 (state.val - 1376)
                else
                  packedTransitionCodeChunk44 (state.val - 1408)
        else
          if state.val < 1696 then
            if state.val < 1568 then
              if state.val < 1504 then
                if state.val < 1472 then
                  packedTransitionCodeChunk45 (state.val - 1440)
                else
                  packedTransitionCodeChunk46 (state.val - 1472)
              else
                if state.val < 1536 then
                  packedTransitionCodeChunk47 (state.val - 1504)
                else
                  packedTransitionCodeChunk48 (state.val - 1536)
            else
              if state.val < 1632 then
                if state.val < 1600 then
                  packedTransitionCodeChunk49 (state.val - 1568)
                else
                  packedTransitionCodeChunk50 (state.val - 1600)
              else
                if state.val < 1664 then
                  packedTransitionCodeChunk51 (state.val - 1632)
                else
                  packedTransitionCodeChunk52 (state.val - 1664)
          else
            if state.val < 1824 then
              if state.val < 1760 then
                if state.val < 1728 then
                  packedTransitionCodeChunk53 (state.val - 1696)
                else
                  packedTransitionCodeChunk54 (state.val - 1728)
              else
                if state.val < 1792 then
                  packedTransitionCodeChunk55 (state.val - 1760)
                else
                  packedTransitionCodeChunk56 (state.val - 1792)
            else
              if state.val < 1888 then
                if state.val < 1856 then
                  packedTransitionCodeChunk57 (state.val - 1824)
                else
                  packedTransitionCodeChunk58 (state.val - 1856)
              else
                if state.val < 1920 then
                  packedTransitionCodeChunk59 (state.val - 1888)
                else
                  packedTransitionCodeChunk60 (state.val - 1920)
    else
      if state.val < 2912 then
        if state.val < 2432 then
          if state.val < 2176 then
            if state.val < 2048 then
              if state.val < 1984 then
                packedTransitionCodeChunk61 (state.val - 1952)
              else
                if state.val < 2016 then
                  packedTransitionCodeChunk62 (state.val - 1984)
                else
                  packedTransitionCodeChunk63 (state.val - 2016)
            else
              if state.val < 2112 then
                if state.val < 2080 then
                  packedTransitionCodeChunk64 (state.val - 2048)
                else
                  packedTransitionCodeChunk65 (state.val - 2080)
              else
                if state.val < 2144 then
                  packedTransitionCodeChunk66 (state.val - 2112)
                else
                  packedTransitionCodeChunk67 (state.val - 2144)
          else
            if state.val < 2304 then
              if state.val < 2240 then
                if state.val < 2208 then
                  packedTransitionCodeChunk68 (state.val - 2176)
                else
                  packedTransitionCodeChunk69 (state.val - 2208)
              else
                if state.val < 2272 then
                  packedTransitionCodeChunk70 (state.val - 2240)
                else
                  packedTransitionCodeChunk71 (state.val - 2272)
            else
              if state.val < 2368 then
                if state.val < 2336 then
                  packedTransitionCodeChunk72 (state.val - 2304)
                else
                  packedTransitionCodeChunk73 (state.val - 2336)
              else
                if state.val < 2400 then
                  packedTransitionCodeChunk74 (state.val - 2368)
                else
                  packedTransitionCodeChunk75 (state.val - 2400)
        else
          if state.val < 2656 then
            if state.val < 2528 then
              if state.val < 2464 then
                packedTransitionCodeChunk76 (state.val - 2432)
              else
                if state.val < 2496 then
                  packedTransitionCodeChunk77 (state.val - 2464)
                else
                  packedTransitionCodeChunk78 (state.val - 2496)
            else
              if state.val < 2592 then
                if state.val < 2560 then
                  packedTransitionCodeChunk79 (state.val - 2528)
                else
                  packedTransitionCodeChunk80 (state.val - 2560)
              else
                if state.val < 2624 then
                  packedTransitionCodeChunk81 (state.val - 2592)
                else
                  packedTransitionCodeChunk82 (state.val - 2624)
          else
            if state.val < 2784 then
              if state.val < 2720 then
                if state.val < 2688 then
                  packedTransitionCodeChunk83 (state.val - 2656)
                else
                  packedTransitionCodeChunk84 (state.val - 2688)
              else
                if state.val < 2752 then
                  packedTransitionCodeChunk85 (state.val - 2720)
                else
                  packedTransitionCodeChunk86 (state.val - 2752)
            else
              if state.val < 2848 then
                if state.val < 2816 then
                  packedTransitionCodeChunk87 (state.val - 2784)
                else
                  packedTransitionCodeChunk88 (state.val - 2816)
              else
                if state.val < 2880 then
                  packedTransitionCodeChunk89 (state.val - 2848)
                else
                  packedTransitionCodeChunk90 (state.val - 2880)
      else
        if state.val < 3392 then
          if state.val < 3136 then
            if state.val < 3008 then
              if state.val < 2944 then
                packedTransitionCodeChunk91 (state.val - 2912)
              else
                if state.val < 2976 then
                  packedTransitionCodeChunk92 (state.val - 2944)
                else
                  packedTransitionCodeChunk93 (state.val - 2976)
            else
              if state.val < 3072 then
                if state.val < 3040 then
                  packedTransitionCodeChunk94 (state.val - 3008)
                else
                  packedTransitionCodeChunk95 (state.val - 3040)
              else
                if state.val < 3104 then
                  packedTransitionCodeChunk96 (state.val - 3072)
                else
                  packedTransitionCodeChunk97 (state.val - 3104)
          else
            if state.val < 3264 then
              if state.val < 3200 then
                if state.val < 3168 then
                  packedTransitionCodeChunk98 (state.val - 3136)
                else
                  packedTransitionCodeChunk99 (state.val - 3168)
              else
                if state.val < 3232 then
                  packedTransitionCodeChunk100 (state.val - 3200)
                else
                  packedTransitionCodeChunk101 (state.val - 3232)
            else
              if state.val < 3328 then
                if state.val < 3296 then
                  packedTransitionCodeChunk102 (state.val - 3264)
                else
                  packedTransitionCodeChunk103 (state.val - 3296)
              else
                if state.val < 3360 then
                  packedTransitionCodeChunk104 (state.val - 3328)
                else
                  packedTransitionCodeChunk105 (state.val - 3360)
        else
          if state.val < 3648 then
            if state.val < 3520 then
              if state.val < 3456 then
                if state.val < 3424 then
                  packedTransitionCodeChunk106 (state.val - 3392)
                else
                  packedTransitionCodeChunk107 (state.val - 3424)
              else
                if state.val < 3488 then
                  packedTransitionCodeChunk108 (state.val - 3456)
                else
                  packedTransitionCodeChunk109 (state.val - 3488)
            else
              if state.val < 3584 then
                if state.val < 3552 then
                  packedTransitionCodeChunk110 (state.val - 3520)
                else
                  packedTransitionCodeChunk111 (state.val - 3552)
              else
                if state.val < 3616 then
                  packedTransitionCodeChunk112 (state.val - 3584)
                else
                  packedTransitionCodeChunk113 (state.val - 3616)
          else
            if state.val < 3776 then
              if state.val < 3712 then
                if state.val < 3680 then
                  packedTransitionCodeChunk114 (state.val - 3648)
                else
                  packedTransitionCodeChunk115 (state.val - 3680)
              else
                if state.val < 3744 then
                  packedTransitionCodeChunk116 (state.val - 3712)
                else
                  packedTransitionCodeChunk117 (state.val - 3744)
            else
              if state.val < 3840 then
                if state.val < 3808 then
                  packedTransitionCodeChunk118 (state.val - 3776)
                else
                  packedTransitionCodeChunk119 (state.val - 3808)
              else
                if state.val < 3872 then
                  packedTransitionCodeChunk120 (state.val - 3840)
                else
                  packedTransitionCodeChunk121 (state.val - 3872)
  else
    if state.val < 5856 then
      if state.val < 4864 then
        if state.val < 4384 then
          if state.val < 4128 then
            if state.val < 4000 then
              if state.val < 3936 then
                packedTransitionCodeChunk122 (state.val - 3904)
              else
                if state.val < 3968 then
                  packedTransitionCodeChunk123 (state.val - 3936)
                else
                  packedTransitionCodeChunk124 (state.val - 3968)
            else
              if state.val < 4064 then
                if state.val < 4032 then
                  packedTransitionCodeChunk125 (state.val - 4000)
                else
                  packedTransitionCodeChunk126 (state.val - 4032)
              else
                if state.val < 4096 then
                  packedTransitionCodeChunk127 (state.val - 4064)
                else
                  packedTransitionCodeChunk128 (state.val - 4096)
          else
            if state.val < 4256 then
              if state.val < 4192 then
                if state.val < 4160 then
                  packedTransitionCodeChunk129 (state.val - 4128)
                else
                  packedTransitionCodeChunk130 (state.val - 4160)
              else
                if state.val < 4224 then
                  packedTransitionCodeChunk131 (state.val - 4192)
                else
                  packedTransitionCodeChunk132 (state.val - 4224)
            else
              if state.val < 4320 then
                if state.val < 4288 then
                  packedTransitionCodeChunk133 (state.val - 4256)
                else
                  packedTransitionCodeChunk134 (state.val - 4288)
              else
                if state.val < 4352 then
                  packedTransitionCodeChunk135 (state.val - 4320)
                else
                  packedTransitionCodeChunk136 (state.val - 4352)
        else
          if state.val < 4608 then
            if state.val < 4480 then
              if state.val < 4416 then
                packedTransitionCodeChunk137 (state.val - 4384)
              else
                if state.val < 4448 then
                  packedTransitionCodeChunk138 (state.val - 4416)
                else
                  packedTransitionCodeChunk139 (state.val - 4448)
            else
              if state.val < 4544 then
                if state.val < 4512 then
                  packedTransitionCodeChunk140 (state.val - 4480)
                else
                  packedTransitionCodeChunk141 (state.val - 4512)
              else
                if state.val < 4576 then
                  packedTransitionCodeChunk142 (state.val - 4544)
                else
                  packedTransitionCodeChunk143 (state.val - 4576)
          else
            if state.val < 4736 then
              if state.val < 4672 then
                if state.val < 4640 then
                  packedTransitionCodeChunk144 (state.val - 4608)
                else
                  packedTransitionCodeChunk145 (state.val - 4640)
              else
                if state.val < 4704 then
                  packedTransitionCodeChunk146 (state.val - 4672)
                else
                  packedTransitionCodeChunk147 (state.val - 4704)
            else
              if state.val < 4800 then
                if state.val < 4768 then
                  packedTransitionCodeChunk148 (state.val - 4736)
                else
                  packedTransitionCodeChunk149 (state.val - 4768)
              else
                if state.val < 4832 then
                  packedTransitionCodeChunk150 (state.val - 4800)
                else
                  packedTransitionCodeChunk151 (state.val - 4832)
      else
        if state.val < 5344 then
          if state.val < 5088 then
            if state.val < 4960 then
              if state.val < 4896 then
                packedTransitionCodeChunk152 (state.val - 4864)
              else
                if state.val < 4928 then
                  packedTransitionCodeChunk153 (state.val - 4896)
                else
                  packedTransitionCodeChunk154 (state.val - 4928)
            else
              if state.val < 5024 then
                if state.val < 4992 then
                  packedTransitionCodeChunk155 (state.val - 4960)
                else
                  packedTransitionCodeChunk156 (state.val - 4992)
              else
                if state.val < 5056 then
                  packedTransitionCodeChunk157 (state.val - 5024)
                else
                  packedTransitionCodeChunk158 (state.val - 5056)
          else
            if state.val < 5216 then
              if state.val < 5152 then
                if state.val < 5120 then
                  packedTransitionCodeChunk159 (state.val - 5088)
                else
                  packedTransitionCodeChunk160 (state.val - 5120)
              else
                if state.val < 5184 then
                  packedTransitionCodeChunk161 (state.val - 5152)
                else
                  packedTransitionCodeChunk162 (state.val - 5184)
            else
              if state.val < 5280 then
                if state.val < 5248 then
                  packedTransitionCodeChunk163 (state.val - 5216)
                else
                  packedTransitionCodeChunk164 (state.val - 5248)
              else
                if state.val < 5312 then
                  packedTransitionCodeChunk165 (state.val - 5280)
                else
                  packedTransitionCodeChunk166 (state.val - 5312)
        else
          if state.val < 5600 then
            if state.val < 5472 then
              if state.val < 5408 then
                if state.val < 5376 then
                  packedTransitionCodeChunk167 (state.val - 5344)
                else
                  packedTransitionCodeChunk168 (state.val - 5376)
              else
                if state.val < 5440 then
                  packedTransitionCodeChunk169 (state.val - 5408)
                else
                  packedTransitionCodeChunk170 (state.val - 5440)
            else
              if state.val < 5536 then
                if state.val < 5504 then
                  packedTransitionCodeChunk171 (state.val - 5472)
                else
                  packedTransitionCodeChunk172 (state.val - 5504)
              else
                if state.val < 5568 then
                  packedTransitionCodeChunk173 (state.val - 5536)
                else
                  packedTransitionCodeChunk174 (state.val - 5568)
          else
            if state.val < 5728 then
              if state.val < 5664 then
                if state.val < 5632 then
                  packedTransitionCodeChunk175 (state.val - 5600)
                else
                  packedTransitionCodeChunk176 (state.val - 5632)
              else
                if state.val < 5696 then
                  packedTransitionCodeChunk177 (state.val - 5664)
                else
                  packedTransitionCodeChunk178 (state.val - 5696)
            else
              if state.val < 5792 then
                if state.val < 5760 then
                  packedTransitionCodeChunk179 (state.val - 5728)
                else
                  packedTransitionCodeChunk180 (state.val - 5760)
              else
                if state.val < 5824 then
                  packedTransitionCodeChunk181 (state.val - 5792)
                else
                  packedTransitionCodeChunk182 (state.val - 5824)
    else
      if state.val < 6816 then
        if state.val < 6336 then
          if state.val < 6080 then
            if state.val < 5952 then
              if state.val < 5888 then
                packedTransitionCodeChunk183 (state.val - 5856)
              else
                if state.val < 5920 then
                  packedTransitionCodeChunk184 (state.val - 5888)
                else
                  packedTransitionCodeChunk185 (state.val - 5920)
            else
              if state.val < 6016 then
                if state.val < 5984 then
                  packedTransitionCodeChunk186 (state.val - 5952)
                else
                  packedTransitionCodeChunk187 (state.val - 5984)
              else
                if state.val < 6048 then
                  packedTransitionCodeChunk188 (state.val - 6016)
                else
                  packedTransitionCodeChunk189 (state.val - 6048)
          else
            if state.val < 6208 then
              if state.val < 6144 then
                if state.val < 6112 then
                  packedTransitionCodeChunk190 (state.val - 6080)
                else
                  packedTransitionCodeChunk191 (state.val - 6112)
              else
                if state.val < 6176 then
                  packedTransitionCodeChunk192 (state.val - 6144)
                else
                  packedTransitionCodeChunk193 (state.val - 6176)
            else
              if state.val < 6272 then
                if state.val < 6240 then
                  packedTransitionCodeChunk194 (state.val - 6208)
                else
                  packedTransitionCodeChunk195 (state.val - 6240)
              else
                if state.val < 6304 then
                  packedTransitionCodeChunk196 (state.val - 6272)
                else
                  packedTransitionCodeChunk197 (state.val - 6304)
        else
          if state.val < 6560 then
            if state.val < 6432 then
              if state.val < 6368 then
                packedTransitionCodeChunk198 (state.val - 6336)
              else
                if state.val < 6400 then
                  packedTransitionCodeChunk199 (state.val - 6368)
                else
                  packedTransitionCodeChunk200 (state.val - 6400)
            else
              if state.val < 6496 then
                if state.val < 6464 then
                  packedTransitionCodeChunk201 (state.val - 6432)
                else
                  packedTransitionCodeChunk202 (state.val - 6464)
              else
                if state.val < 6528 then
                  packedTransitionCodeChunk203 (state.val - 6496)
                else
                  packedTransitionCodeChunk204 (state.val - 6528)
          else
            if state.val < 6688 then
              if state.val < 6624 then
                if state.val < 6592 then
                  packedTransitionCodeChunk205 (state.val - 6560)
                else
                  packedTransitionCodeChunk206 (state.val - 6592)
              else
                if state.val < 6656 then
                  packedTransitionCodeChunk207 (state.val - 6624)
                else
                  packedTransitionCodeChunk208 (state.val - 6656)
            else
              if state.val < 6752 then
                if state.val < 6720 then
                  packedTransitionCodeChunk209 (state.val - 6688)
                else
                  packedTransitionCodeChunk210 (state.val - 6720)
              else
                if state.val < 6784 then
                  packedTransitionCodeChunk211 (state.val - 6752)
                else
                  packedTransitionCodeChunk212 (state.val - 6784)
      else
        if state.val < 7296 then
          if state.val < 7040 then
            if state.val < 6912 then
              if state.val < 6848 then
                packedTransitionCodeChunk213 (state.val - 6816)
              else
                if state.val < 6880 then
                  packedTransitionCodeChunk214 (state.val - 6848)
                else
                  packedTransitionCodeChunk215 (state.val - 6880)
            else
              if state.val < 6976 then
                if state.val < 6944 then
                  packedTransitionCodeChunk216 (state.val - 6912)
                else
                  packedTransitionCodeChunk217 (state.val - 6944)
              else
                if state.val < 7008 then
                  packedTransitionCodeChunk218 (state.val - 6976)
                else
                  packedTransitionCodeChunk219 (state.val - 7008)
          else
            if state.val < 7168 then
              if state.val < 7104 then
                if state.val < 7072 then
                  packedTransitionCodeChunk220 (state.val - 7040)
                else
                  packedTransitionCodeChunk221 (state.val - 7072)
              else
                if state.val < 7136 then
                  packedTransitionCodeChunk222 (state.val - 7104)
                else
                  packedTransitionCodeChunk223 (state.val - 7136)
            else
              if state.val < 7232 then
                if state.val < 7200 then
                  packedTransitionCodeChunk224 (state.val - 7168)
                else
                  packedTransitionCodeChunk225 (state.val - 7200)
              else
                if state.val < 7264 then
                  packedTransitionCodeChunk226 (state.val - 7232)
                else
                  packedTransitionCodeChunk227 (state.val - 7264)
        else
          if state.val < 7552 then
            if state.val < 7424 then
              if state.val < 7360 then
                if state.val < 7328 then
                  packedTransitionCodeChunk228 (state.val - 7296)
                else
                  packedTransitionCodeChunk229 (state.val - 7328)
              else
                if state.val < 7392 then
                  packedTransitionCodeChunk230 (state.val - 7360)
                else
                  packedTransitionCodeChunk231 (state.val - 7392)
            else
              if state.val < 7488 then
                if state.val < 7456 then
                  packedTransitionCodeChunk232 (state.val - 7424)
                else
                  packedTransitionCodeChunk233 (state.val - 7456)
              else
                if state.val < 7520 then
                  packedTransitionCodeChunk234 (state.val - 7488)
                else
                  packedTransitionCodeChunk235 (state.val - 7520)
          else
            if state.val < 7680 then
              if state.val < 7616 then
                if state.val < 7584 then
                  packedTransitionCodeChunk236 (state.val - 7552)
                else
                  packedTransitionCodeChunk237 (state.val - 7584)
              else
                if state.val < 7648 then
                  packedTransitionCodeChunk238 (state.val - 7616)
                else
                  packedTransitionCodeChunk239 (state.val - 7648)
            else
              if state.val < 7744 then
                if state.val < 7712 then
                  packedTransitionCodeChunk240 (state.val - 7680)
                else
                  packedTransitionCodeChunk241 (state.val - 7712)
              else
                if state.val < 7776 then
                  packedTransitionCodeChunk242 (state.val - 7744)
                else
                  packedTransitionCodeChunk243 (state.val - 7776)

def transition (state : Fin 7782)
    (generator : Fin 6) : Fin 7782 :=
  ⟨(packedTransitionCode state / 7782 ^ generator.val) % 7782,
    Nat.mod_lt _ (by decide)⟩

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6836.Shards
