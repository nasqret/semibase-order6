import SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.Shards.StateVectorPart00
import SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.Shards.StateVectorPart01
import SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.Shards.StateVectorPart02

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.Shards

def packedStateVectorCode (state : Fin 2712) : Nat :=
  if state.val < 1344 then
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
      if state.val < 992 then
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
          if state.val < 896 then
            if state.val < 864 then
              packedStateVectorCodeChunk26 (state.val - 832)
            else
              packedStateVectorCodeChunk27 (state.val - 864)
          else
            if state.val < 928 then
              packedStateVectorCodeChunk28 (state.val - 896)
            else
              if state.val < 960 then
                packedStateVectorCodeChunk29 (state.val - 928)
              else
                packedStateVectorCodeChunk30 (state.val - 960)
      else
        if state.val < 1152 then
          if state.val < 1056 then
            if state.val < 1024 then
              packedStateVectorCodeChunk31 (state.val - 992)
            else
              packedStateVectorCodeChunk32 (state.val - 1024)
          else
            if state.val < 1088 then
              packedStateVectorCodeChunk33 (state.val - 1056)
            else
              if state.val < 1120 then
                packedStateVectorCodeChunk34 (state.val - 1088)
              else
                packedStateVectorCodeChunk35 (state.val - 1120)
        else
          if state.val < 1248 then
            if state.val < 1184 then
              packedStateVectorCodeChunk36 (state.val - 1152)
            else
              if state.val < 1216 then
                packedStateVectorCodeChunk37 (state.val - 1184)
              else
                packedStateVectorCodeChunk38 (state.val - 1216)
          else
            if state.val < 1280 then
              packedStateVectorCodeChunk39 (state.val - 1248)
            else
              if state.val < 1312 then
                packedStateVectorCodeChunk40 (state.val - 1280)
              else
                packedStateVectorCodeChunk41 (state.val - 1312)
  else
    if state.val < 2016 then
      if state.val < 1664 then
        if state.val < 1504 then
          if state.val < 1408 then
            if state.val < 1376 then
              packedStateVectorCodeChunk42 (state.val - 1344)
            else
              packedStateVectorCodeChunk43 (state.val - 1376)
          else
            if state.val < 1440 then
              packedStateVectorCodeChunk44 (state.val - 1408)
            else
              if state.val < 1472 then
                packedStateVectorCodeChunk45 (state.val - 1440)
              else
                packedStateVectorCodeChunk46 (state.val - 1472)
        else
          if state.val < 1568 then
            if state.val < 1536 then
              packedStateVectorCodeChunk47 (state.val - 1504)
            else
              packedStateVectorCodeChunk48 (state.val - 1536)
          else
            if state.val < 1600 then
              packedStateVectorCodeChunk49 (state.val - 1568)
            else
              if state.val < 1632 then
                packedStateVectorCodeChunk50 (state.val - 1600)
              else
                packedStateVectorCodeChunk51 (state.val - 1632)
      else
        if state.val < 1824 then
          if state.val < 1728 then
            if state.val < 1696 then
              packedStateVectorCodeChunk52 (state.val - 1664)
            else
              packedStateVectorCodeChunk53 (state.val - 1696)
          else
            if state.val < 1760 then
              packedStateVectorCodeChunk54 (state.val - 1728)
            else
              if state.val < 1792 then
                packedStateVectorCodeChunk55 (state.val - 1760)
              else
                packedStateVectorCodeChunk56 (state.val - 1792)
        else
          if state.val < 1920 then
            if state.val < 1856 then
              packedStateVectorCodeChunk57 (state.val - 1824)
            else
              if state.val < 1888 then
                packedStateVectorCodeChunk58 (state.val - 1856)
              else
                packedStateVectorCodeChunk59 (state.val - 1888)
          else
            if state.val < 1952 then
              packedStateVectorCodeChunk60 (state.val - 1920)
            else
              if state.val < 1984 then
                packedStateVectorCodeChunk61 (state.val - 1952)
              else
                packedStateVectorCodeChunk62 (state.val - 1984)
    else
      if state.val < 2368 then
        if state.val < 2176 then
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
          if state.val < 2272 then
            if state.val < 2208 then
              packedStateVectorCodeChunk68 (state.val - 2176)
            else
              if state.val < 2240 then
                packedStateVectorCodeChunk69 (state.val - 2208)
              else
                packedStateVectorCodeChunk70 (state.val - 2240)
          else
            if state.val < 2304 then
              packedStateVectorCodeChunk71 (state.val - 2272)
            else
              if state.val < 2336 then
                packedStateVectorCodeChunk72 (state.val - 2304)
              else
                packedStateVectorCodeChunk73 (state.val - 2336)
      else
        if state.val < 2528 then
          if state.val < 2432 then
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

def stateVector (state : Fin 2712)
    (coordinate : Fin 17) : Fin 6 :=
  ⟨(packedStateVectorCode state / 6 ^ coordinate.val) % 6,
    Nat.mod_lt _ (by decide)⟩

end SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.Shards
