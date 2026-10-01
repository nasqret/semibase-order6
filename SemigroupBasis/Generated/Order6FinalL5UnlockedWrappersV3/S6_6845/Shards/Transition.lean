import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6845.Shards.TransitionPart00
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6845.Shards.TransitionPart01
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6845.Shards.TransitionPart02
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6845.Shards.TransitionPart03
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6845.Shards.TransitionPart04

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6845.Shards

def packedTransitionCode (state : Fin 4374) : Nat :=
  if state.val < 2176 then
    if state.val < 1088 then
      if state.val < 544 then
        if state.val < 256 then
          if state.val < 128 then
            if state.val < 64 then
              if state.val < 32 then
                packedTransitionCodeChunk0 state.val
              else
                packedTransitionCodeChunk1 (state.val - 32)
            else
              if state.val < 96 then
                packedTransitionCodeChunk2 (state.val - 64)
              else
                packedTransitionCodeChunk3 (state.val - 96)
          else
            if state.val < 192 then
              if state.val < 160 then
                packedTransitionCodeChunk4 (state.val - 128)
              else
                packedTransitionCodeChunk5 (state.val - 160)
            else
              if state.val < 224 then
                packedTransitionCodeChunk6 (state.val - 192)
              else
                packedTransitionCodeChunk7 (state.val - 224)
        else
          if state.val < 384 then
            if state.val < 320 then
              if state.val < 288 then
                packedTransitionCodeChunk8 (state.val - 256)
              else
                packedTransitionCodeChunk9 (state.val - 288)
            else
              if state.val < 352 then
                packedTransitionCodeChunk10 (state.val - 320)
              else
                packedTransitionCodeChunk11 (state.val - 352)
          else
            if state.val < 448 then
              if state.val < 416 then
                packedTransitionCodeChunk12 (state.val - 384)
              else
                packedTransitionCodeChunk13 (state.val - 416)
            else
              if state.val < 480 then
                packedTransitionCodeChunk14 (state.val - 448)
              else
                if state.val < 512 then
                  packedTransitionCodeChunk15 (state.val - 480)
                else
                  packedTransitionCodeChunk16 (state.val - 512)
      else
        if state.val < 800 then
          if state.val < 672 then
            if state.val < 608 then
              if state.val < 576 then
                packedTransitionCodeChunk17 (state.val - 544)
              else
                packedTransitionCodeChunk18 (state.val - 576)
            else
              if state.val < 640 then
                packedTransitionCodeChunk19 (state.val - 608)
              else
                packedTransitionCodeChunk20 (state.val - 640)
          else
            if state.val < 736 then
              if state.val < 704 then
                packedTransitionCodeChunk21 (state.val - 672)
              else
                packedTransitionCodeChunk22 (state.val - 704)
            else
              if state.val < 768 then
                packedTransitionCodeChunk23 (state.val - 736)
              else
                packedTransitionCodeChunk24 (state.val - 768)
        else
          if state.val < 928 then
            if state.val < 864 then
              if state.val < 832 then
                packedTransitionCodeChunk25 (state.val - 800)
              else
                packedTransitionCodeChunk26 (state.val - 832)
            else
              if state.val < 896 then
                packedTransitionCodeChunk27 (state.val - 864)
              else
                packedTransitionCodeChunk28 (state.val - 896)
          else
            if state.val < 992 then
              if state.val < 960 then
                packedTransitionCodeChunk29 (state.val - 928)
              else
                packedTransitionCodeChunk30 (state.val - 960)
            else
              if state.val < 1024 then
                packedTransitionCodeChunk31 (state.val - 992)
              else
                if state.val < 1056 then
                  packedTransitionCodeChunk32 (state.val - 1024)
                else
                  packedTransitionCodeChunk33 (state.val - 1056)
    else
      if state.val < 1632 then
        if state.val < 1344 then
          if state.val < 1216 then
            if state.val < 1152 then
              if state.val < 1120 then
                packedTransitionCodeChunk34 (state.val - 1088)
              else
                packedTransitionCodeChunk35 (state.val - 1120)
            else
              if state.val < 1184 then
                packedTransitionCodeChunk36 (state.val - 1152)
              else
                packedTransitionCodeChunk37 (state.val - 1184)
          else
            if state.val < 1280 then
              if state.val < 1248 then
                packedTransitionCodeChunk38 (state.val - 1216)
              else
                packedTransitionCodeChunk39 (state.val - 1248)
            else
              if state.val < 1312 then
                packedTransitionCodeChunk40 (state.val - 1280)
              else
                packedTransitionCodeChunk41 (state.val - 1312)
        else
          if state.val < 1472 then
            if state.val < 1408 then
              if state.val < 1376 then
                packedTransitionCodeChunk42 (state.val - 1344)
              else
                packedTransitionCodeChunk43 (state.val - 1376)
            else
              if state.val < 1440 then
                packedTransitionCodeChunk44 (state.val - 1408)
              else
                packedTransitionCodeChunk45 (state.val - 1440)
          else
            if state.val < 1536 then
              if state.val < 1504 then
                packedTransitionCodeChunk46 (state.val - 1472)
              else
                packedTransitionCodeChunk47 (state.val - 1504)
            else
              if state.val < 1568 then
                packedTransitionCodeChunk48 (state.val - 1536)
              else
                if state.val < 1600 then
                  packedTransitionCodeChunk49 (state.val - 1568)
                else
                  packedTransitionCodeChunk50 (state.val - 1600)
      else
        if state.val < 1888 then
          if state.val < 1760 then
            if state.val < 1696 then
              if state.val < 1664 then
                packedTransitionCodeChunk51 (state.val - 1632)
              else
                packedTransitionCodeChunk52 (state.val - 1664)
            else
              if state.val < 1728 then
                packedTransitionCodeChunk53 (state.val - 1696)
              else
                packedTransitionCodeChunk54 (state.val - 1728)
          else
            if state.val < 1824 then
              if state.val < 1792 then
                packedTransitionCodeChunk55 (state.val - 1760)
              else
                packedTransitionCodeChunk56 (state.val - 1792)
            else
              if state.val < 1856 then
                packedTransitionCodeChunk57 (state.val - 1824)
              else
                packedTransitionCodeChunk58 (state.val - 1856)
        else
          if state.val < 2016 then
            if state.val < 1952 then
              if state.val < 1920 then
                packedTransitionCodeChunk59 (state.val - 1888)
              else
                packedTransitionCodeChunk60 (state.val - 1920)
            else
              if state.val < 1984 then
                packedTransitionCodeChunk61 (state.val - 1952)
              else
                packedTransitionCodeChunk62 (state.val - 1984)
          else
            if state.val < 2080 then
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
    if state.val < 3264 then
      if state.val < 2720 then
        if state.val < 2432 then
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
          if state.val < 2560 then
            if state.val < 2496 then
              if state.val < 2464 then
                packedTransitionCodeChunk76 (state.val - 2432)
              else
                packedTransitionCodeChunk77 (state.val - 2464)
            else
              if state.val < 2528 then
                packedTransitionCodeChunk78 (state.val - 2496)
              else
                packedTransitionCodeChunk79 (state.val - 2528)
          else
            if state.val < 2624 then
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
        if state.val < 2976 then
          if state.val < 2848 then
            if state.val < 2784 then
              if state.val < 2752 then
                packedTransitionCodeChunk85 (state.val - 2720)
              else
                packedTransitionCodeChunk86 (state.val - 2752)
            else
              if state.val < 2816 then
                packedTransitionCodeChunk87 (state.val - 2784)
              else
                packedTransitionCodeChunk88 (state.val - 2816)
          else
            if state.val < 2912 then
              if state.val < 2880 then
                packedTransitionCodeChunk89 (state.val - 2848)
              else
                packedTransitionCodeChunk90 (state.val - 2880)
            else
              if state.val < 2944 then
                packedTransitionCodeChunk91 (state.val - 2912)
              else
                packedTransitionCodeChunk92 (state.val - 2944)
        else
          if state.val < 3104 then
            if state.val < 3040 then
              if state.val < 3008 then
                packedTransitionCodeChunk93 (state.val - 2976)
              else
                packedTransitionCodeChunk94 (state.val - 3008)
            else
              if state.val < 3072 then
                packedTransitionCodeChunk95 (state.val - 3040)
              else
                packedTransitionCodeChunk96 (state.val - 3072)
          else
            if state.val < 3168 then
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
      if state.val < 3808 then
        if state.val < 3520 then
          if state.val < 3392 then
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
          if state.val < 3648 then
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
        if state.val < 4096 then
          if state.val < 3936 then
            if state.val < 3872 then
              if state.val < 3840 then
                packedTransitionCodeChunk119 (state.val - 3808)
              else
                packedTransitionCodeChunk120 (state.val - 3840)
            else
              if state.val < 3904 then
                packedTransitionCodeChunk121 (state.val - 3872)
              else
                packedTransitionCodeChunk122 (state.val - 3904)
          else
            if state.val < 4000 then
              if state.val < 3968 then
                packedTransitionCodeChunk123 (state.val - 3936)
              else
                packedTransitionCodeChunk124 (state.val - 3968)
            else
              if state.val < 4032 then
                packedTransitionCodeChunk125 (state.val - 4000)
              else
                if state.val < 4064 then
                  packedTransitionCodeChunk126 (state.val - 4032)
                else
                  packedTransitionCodeChunk127 (state.val - 4064)
        else
          if state.val < 4224 then
            if state.val < 4160 then
              if state.val < 4128 then
                packedTransitionCodeChunk128 (state.val - 4096)
              else
                packedTransitionCodeChunk129 (state.val - 4128)
            else
              if state.val < 4192 then
                packedTransitionCodeChunk130 (state.val - 4160)
              else
                packedTransitionCodeChunk131 (state.val - 4192)
          else
            if state.val < 4288 then
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

def transition (state : Fin 4374)
    (generator : Fin 6) : Fin 4374 :=
  ⟨(packedTransitionCode state / 4374 ^ generator.val) % 4374,
    Nat.mod_lt _ (by decide)⟩

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6845.Shards
