import SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.Shards.TransitionPart00
import SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.Shards.TransitionPart01
import SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.Shards.TransitionPart02

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.Shards

def packedTransitionCode (state : Fin 2712) : Nat :=
  if state.val < 1344 then
    if state.val < 672 then
      if state.val < 320 then
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
          if state.val < 224 then
            if state.val < 192 then
              packedTransitionCodeChunk5 (state.val - 160)
            else
              packedTransitionCodeChunk6 (state.val - 192)
          else
            if state.val < 256 then
              packedTransitionCodeChunk7 (state.val - 224)
            else
              if state.val < 288 then
                packedTransitionCodeChunk8 (state.val - 256)
              else
                packedTransitionCodeChunk9 (state.val - 288)
      else
        if state.val < 480 then
          if state.val < 384 then
            if state.val < 352 then
              packedTransitionCodeChunk10 (state.val - 320)
            else
              packedTransitionCodeChunk11 (state.val - 352)
          else
            if state.val < 416 then
              packedTransitionCodeChunk12 (state.val - 384)
            else
              if state.val < 448 then
                packedTransitionCodeChunk13 (state.val - 416)
              else
                packedTransitionCodeChunk14 (state.val - 448)
        else
          if state.val < 576 then
            if state.val < 512 then
              packedTransitionCodeChunk15 (state.val - 480)
            else
              if state.val < 544 then
                packedTransitionCodeChunk16 (state.val - 512)
              else
                packedTransitionCodeChunk17 (state.val - 544)
          else
            if state.val < 608 then
              packedTransitionCodeChunk18 (state.val - 576)
            else
              if state.val < 640 then
                packedTransitionCodeChunk19 (state.val - 608)
              else
                packedTransitionCodeChunk20 (state.val - 640)
    else
      if state.val < 992 then
        if state.val < 832 then
          if state.val < 736 then
            if state.val < 704 then
              packedTransitionCodeChunk21 (state.val - 672)
            else
              packedTransitionCodeChunk22 (state.val - 704)
          else
            if state.val < 768 then
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
              if state.val < 960 then
                packedTransitionCodeChunk29 (state.val - 928)
              else
                packedTransitionCodeChunk30 (state.val - 960)
      else
        if state.val < 1152 then
          if state.val < 1056 then
            if state.val < 1024 then
              packedTransitionCodeChunk31 (state.val - 992)
            else
              packedTransitionCodeChunk32 (state.val - 1024)
          else
            if state.val < 1088 then
              packedTransitionCodeChunk33 (state.val - 1056)
            else
              if state.val < 1120 then
                packedTransitionCodeChunk34 (state.val - 1088)
              else
                packedTransitionCodeChunk35 (state.val - 1120)
        else
          if state.val < 1248 then
            if state.val < 1184 then
              packedTransitionCodeChunk36 (state.val - 1152)
            else
              if state.val < 1216 then
                packedTransitionCodeChunk37 (state.val - 1184)
              else
                packedTransitionCodeChunk38 (state.val - 1216)
          else
            if state.val < 1280 then
              packedTransitionCodeChunk39 (state.val - 1248)
            else
              if state.val < 1312 then
                packedTransitionCodeChunk40 (state.val - 1280)
              else
                packedTransitionCodeChunk41 (state.val - 1312)
  else
    if state.val < 2016 then
      if state.val < 1664 then
        if state.val < 1504 then
          if state.val < 1408 then
            if state.val < 1376 then
              packedTransitionCodeChunk42 (state.val - 1344)
            else
              packedTransitionCodeChunk43 (state.val - 1376)
          else
            if state.val < 1440 then
              packedTransitionCodeChunk44 (state.val - 1408)
            else
              if state.val < 1472 then
                packedTransitionCodeChunk45 (state.val - 1440)
              else
                packedTransitionCodeChunk46 (state.val - 1472)
        else
          if state.val < 1568 then
            if state.val < 1536 then
              packedTransitionCodeChunk47 (state.val - 1504)
            else
              packedTransitionCodeChunk48 (state.val - 1536)
          else
            if state.val < 1600 then
              packedTransitionCodeChunk49 (state.val - 1568)
            else
              if state.val < 1632 then
                packedTransitionCodeChunk50 (state.val - 1600)
              else
                packedTransitionCodeChunk51 (state.val - 1632)
      else
        if state.val < 1824 then
          if state.val < 1728 then
            if state.val < 1696 then
              packedTransitionCodeChunk52 (state.val - 1664)
            else
              packedTransitionCodeChunk53 (state.val - 1696)
          else
            if state.val < 1760 then
              packedTransitionCodeChunk54 (state.val - 1728)
            else
              if state.val < 1792 then
                packedTransitionCodeChunk55 (state.val - 1760)
              else
                packedTransitionCodeChunk56 (state.val - 1792)
        else
          if state.val < 1920 then
            if state.val < 1856 then
              packedTransitionCodeChunk57 (state.val - 1824)
            else
              if state.val < 1888 then
                packedTransitionCodeChunk58 (state.val - 1856)
              else
                packedTransitionCodeChunk59 (state.val - 1888)
          else
            if state.val < 1952 then
              packedTransitionCodeChunk60 (state.val - 1920)
            else
              if state.val < 1984 then
                packedTransitionCodeChunk61 (state.val - 1952)
              else
                packedTransitionCodeChunk62 (state.val - 1984)
    else
      if state.val < 2368 then
        if state.val < 2176 then
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
          if state.val < 2272 then
            if state.val < 2208 then
              packedTransitionCodeChunk68 (state.val - 2176)
            else
              if state.val < 2240 then
                packedTransitionCodeChunk69 (state.val - 2208)
              else
                packedTransitionCodeChunk70 (state.val - 2240)
          else
            if state.val < 2304 then
              packedTransitionCodeChunk71 (state.val - 2272)
            else
              if state.val < 2336 then
                packedTransitionCodeChunk72 (state.val - 2304)
              else
                packedTransitionCodeChunk73 (state.val - 2336)
      else
        if state.val < 2528 then
          if state.val < 2432 then
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

def transition (state : Fin 2712)
    (generator : Fin 4) : Fin 2712 :=
  ⟨(packedTransitionCode state / 2712 ^ generator.val) % 2712,
    Nat.mod_lt _ (by decide)⟩

end SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.Shards
