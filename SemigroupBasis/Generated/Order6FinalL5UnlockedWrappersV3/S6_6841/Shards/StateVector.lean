import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.Shards.StateVectorPart00
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.Shards.StateVectorPart01
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.Shards.StateVectorPart02
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.Shards.StateVectorPart03
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.Shards.StateVectorPart04

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.Shards

def packedStateVectorCode (state : Fin 4374) : Nat :=
  if state.val < 2176 then
    if state.val < 1088 then
      if state.val < 544 then
        if state.val < 256 then
          if state.val < 128 then
            if state.val < 64 then
              if state.val < 32 then
                packedStateVectorCodeChunk0 state.val
              else
                packedStateVectorCodeChunk1 (state.val - 32)
            else
              if state.val < 96 then
                packedStateVectorCodeChunk2 (state.val - 64)
              else
                packedStateVectorCodeChunk3 (state.val - 96)
          else
            if state.val < 192 then
              if state.val < 160 then
                packedStateVectorCodeChunk4 (state.val - 128)
              else
                packedStateVectorCodeChunk5 (state.val - 160)
            else
              if state.val < 224 then
                packedStateVectorCodeChunk6 (state.val - 192)
              else
                packedStateVectorCodeChunk7 (state.val - 224)
        else
          if state.val < 384 then
            if state.val < 320 then
              if state.val < 288 then
                packedStateVectorCodeChunk8 (state.val - 256)
              else
                packedStateVectorCodeChunk9 (state.val - 288)
            else
              if state.val < 352 then
                packedStateVectorCodeChunk10 (state.val - 320)
              else
                packedStateVectorCodeChunk11 (state.val - 352)
          else
            if state.val < 448 then
              if state.val < 416 then
                packedStateVectorCodeChunk12 (state.val - 384)
              else
                packedStateVectorCodeChunk13 (state.val - 416)
            else
              if state.val < 480 then
                packedStateVectorCodeChunk14 (state.val - 448)
              else
                if state.val < 512 then
                  packedStateVectorCodeChunk15 (state.val - 480)
                else
                  packedStateVectorCodeChunk16 (state.val - 512)
      else
        if state.val < 800 then
          if state.val < 672 then
            if state.val < 608 then
              if state.val < 576 then
                packedStateVectorCodeChunk17 (state.val - 544)
              else
                packedStateVectorCodeChunk18 (state.val - 576)
            else
              if state.val < 640 then
                packedStateVectorCodeChunk19 (state.val - 608)
              else
                packedStateVectorCodeChunk20 (state.val - 640)
          else
            if state.val < 736 then
              if state.val < 704 then
                packedStateVectorCodeChunk21 (state.val - 672)
              else
                packedStateVectorCodeChunk22 (state.val - 704)
            else
              if state.val < 768 then
                packedStateVectorCodeChunk23 (state.val - 736)
              else
                packedStateVectorCodeChunk24 (state.val - 768)
        else
          if state.val < 928 then
            if state.val < 864 then
              if state.val < 832 then
                packedStateVectorCodeChunk25 (state.val - 800)
              else
                packedStateVectorCodeChunk26 (state.val - 832)
            else
              if state.val < 896 then
                packedStateVectorCodeChunk27 (state.val - 864)
              else
                packedStateVectorCodeChunk28 (state.val - 896)
          else
            if state.val < 992 then
              if state.val < 960 then
                packedStateVectorCodeChunk29 (state.val - 928)
              else
                packedStateVectorCodeChunk30 (state.val - 960)
            else
              if state.val < 1024 then
                packedStateVectorCodeChunk31 (state.val - 992)
              else
                if state.val < 1056 then
                  packedStateVectorCodeChunk32 (state.val - 1024)
                else
                  packedStateVectorCodeChunk33 (state.val - 1056)
    else
      if state.val < 1632 then
        if state.val < 1344 then
          if state.val < 1216 then
            if state.val < 1152 then
              if state.val < 1120 then
                packedStateVectorCodeChunk34 (state.val - 1088)
              else
                packedStateVectorCodeChunk35 (state.val - 1120)
            else
              if state.val < 1184 then
                packedStateVectorCodeChunk36 (state.val - 1152)
              else
                packedStateVectorCodeChunk37 (state.val - 1184)
          else
            if state.val < 1280 then
              if state.val < 1248 then
                packedStateVectorCodeChunk38 (state.val - 1216)
              else
                packedStateVectorCodeChunk39 (state.val - 1248)
            else
              if state.val < 1312 then
                packedStateVectorCodeChunk40 (state.val - 1280)
              else
                packedStateVectorCodeChunk41 (state.val - 1312)
        else
          if state.val < 1472 then
            if state.val < 1408 then
              if state.val < 1376 then
                packedStateVectorCodeChunk42 (state.val - 1344)
              else
                packedStateVectorCodeChunk43 (state.val - 1376)
            else
              if state.val < 1440 then
                packedStateVectorCodeChunk44 (state.val - 1408)
              else
                packedStateVectorCodeChunk45 (state.val - 1440)
          else
            if state.val < 1536 then
              if state.val < 1504 then
                packedStateVectorCodeChunk46 (state.val - 1472)
              else
                packedStateVectorCodeChunk47 (state.val - 1504)
            else
              if state.val < 1568 then
                packedStateVectorCodeChunk48 (state.val - 1536)
              else
                if state.val < 1600 then
                  packedStateVectorCodeChunk49 (state.val - 1568)
                else
                  packedStateVectorCodeChunk50 (state.val - 1600)
      else
        if state.val < 1888 then
          if state.val < 1760 then
            if state.val < 1696 then
              if state.val < 1664 then
                packedStateVectorCodeChunk51 (state.val - 1632)
              else
                packedStateVectorCodeChunk52 (state.val - 1664)
            else
              if state.val < 1728 then
                packedStateVectorCodeChunk53 (state.val - 1696)
              else
                packedStateVectorCodeChunk54 (state.val - 1728)
          else
            if state.val < 1824 then
              if state.val < 1792 then
                packedStateVectorCodeChunk55 (state.val - 1760)
              else
                packedStateVectorCodeChunk56 (state.val - 1792)
            else
              if state.val < 1856 then
                packedStateVectorCodeChunk57 (state.val - 1824)
              else
                packedStateVectorCodeChunk58 (state.val - 1856)
        else
          if state.val < 2016 then
            if state.val < 1952 then
              if state.val < 1920 then
                packedStateVectorCodeChunk59 (state.val - 1888)
              else
                packedStateVectorCodeChunk60 (state.val - 1920)
            else
              if state.val < 1984 then
                packedStateVectorCodeChunk61 (state.val - 1952)
              else
                packedStateVectorCodeChunk62 (state.val - 1984)
          else
            if state.val < 2080 then
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
    if state.val < 3264 then
      if state.val < 2720 then
        if state.val < 2432 then
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
          if state.val < 2560 then
            if state.val < 2496 then
              if state.val < 2464 then
                packedStateVectorCodeChunk76 (state.val - 2432)
              else
                packedStateVectorCodeChunk77 (state.val - 2464)
            else
              if state.val < 2528 then
                packedStateVectorCodeChunk78 (state.val - 2496)
              else
                packedStateVectorCodeChunk79 (state.val - 2528)
          else
            if state.val < 2624 then
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
        if state.val < 2976 then
          if state.val < 2848 then
            if state.val < 2784 then
              if state.val < 2752 then
                packedStateVectorCodeChunk85 (state.val - 2720)
              else
                packedStateVectorCodeChunk86 (state.val - 2752)
            else
              if state.val < 2816 then
                packedStateVectorCodeChunk87 (state.val - 2784)
              else
                packedStateVectorCodeChunk88 (state.val - 2816)
          else
            if state.val < 2912 then
              if state.val < 2880 then
                packedStateVectorCodeChunk89 (state.val - 2848)
              else
                packedStateVectorCodeChunk90 (state.val - 2880)
            else
              if state.val < 2944 then
                packedStateVectorCodeChunk91 (state.val - 2912)
              else
                packedStateVectorCodeChunk92 (state.val - 2944)
        else
          if state.val < 3104 then
            if state.val < 3040 then
              if state.val < 3008 then
                packedStateVectorCodeChunk93 (state.val - 2976)
              else
                packedStateVectorCodeChunk94 (state.val - 3008)
            else
              if state.val < 3072 then
                packedStateVectorCodeChunk95 (state.val - 3040)
              else
                packedStateVectorCodeChunk96 (state.val - 3072)
          else
            if state.val < 3168 then
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
      if state.val < 3808 then
        if state.val < 3520 then
          if state.val < 3392 then
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
          if state.val < 3648 then
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
        if state.val < 4096 then
          if state.val < 3936 then
            if state.val < 3872 then
              if state.val < 3840 then
                packedStateVectorCodeChunk119 (state.val - 3808)
              else
                packedStateVectorCodeChunk120 (state.val - 3840)
            else
              if state.val < 3904 then
                packedStateVectorCodeChunk121 (state.val - 3872)
              else
                packedStateVectorCodeChunk122 (state.val - 3904)
          else
            if state.val < 4000 then
              if state.val < 3968 then
                packedStateVectorCodeChunk123 (state.val - 3936)
              else
                packedStateVectorCodeChunk124 (state.val - 3968)
            else
              if state.val < 4032 then
                packedStateVectorCodeChunk125 (state.val - 4000)
              else
                if state.val < 4064 then
                  packedStateVectorCodeChunk126 (state.val - 4032)
                else
                  packedStateVectorCodeChunk127 (state.val - 4064)
        else
          if state.val < 4224 then
            if state.val < 4160 then
              if state.val < 4128 then
                packedStateVectorCodeChunk128 (state.val - 4096)
              else
                packedStateVectorCodeChunk129 (state.val - 4128)
            else
              if state.val < 4192 then
                packedStateVectorCodeChunk130 (state.val - 4160)
              else
                packedStateVectorCodeChunk131 (state.val - 4192)
          else
            if state.val < 4288 then
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

def stateVector (state : Fin 4374)
    (coordinate : Fin 28) : Fin 6 :=
  ⟨(packedStateVectorCode state / 6 ^ coordinate.val) % 6,
    Nat.mod_lt _ (by decide)⟩

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.Shards
