import SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3945.Shards.StateVectorPart00
import SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3945.Shards.StateVectorPart01

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3945.Shards

def packedStateVectorCode (state : Fin 1447) : Nat :=
  if state.val < 736 then
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
      if state.val < 544 then
        if state.val < 448 then
          if state.val < 384 then
            packedStateVectorCodeChunk11 (state.val - 352)
          else
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
        if state.val < 640 then
          if state.val < 576 then
            packedStateVectorCodeChunk17 (state.val - 544)
          else
            if state.val < 608 then
              packedStateVectorCodeChunk18 (state.val - 576)
            else
              packedStateVectorCodeChunk19 (state.val - 608)
        else
          if state.val < 672 then
            packedStateVectorCodeChunk20 (state.val - 640)
          else
            if state.val < 704 then
              packedStateVectorCodeChunk21 (state.val - 672)
            else
              packedStateVectorCodeChunk22 (state.val - 704)
  else
    if state.val < 1088 then
      if state.val < 896 then
        if state.val < 800 then
          if state.val < 768 then
            packedStateVectorCodeChunk23 (state.val - 736)
          else
            packedStateVectorCodeChunk24 (state.val - 768)
        else
          if state.val < 832 then
            packedStateVectorCodeChunk25 (state.val - 800)
          else
            if state.val < 864 then
              packedStateVectorCodeChunk26 (state.val - 832)
            else
              packedStateVectorCodeChunk27 (state.val - 864)
      else
        if state.val < 992 then
          if state.val < 928 then
            packedStateVectorCodeChunk28 (state.val - 896)
          else
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
      if state.val < 1280 then
        if state.val < 1184 then
          if state.val < 1120 then
            packedStateVectorCodeChunk34 (state.val - 1088)
          else
            if state.val < 1152 then
              packedStateVectorCodeChunk35 (state.val - 1120)
            else
              packedStateVectorCodeChunk36 (state.val - 1152)
        else
          if state.val < 1216 then
            packedStateVectorCodeChunk37 (state.val - 1184)
          else
            if state.val < 1248 then
              packedStateVectorCodeChunk38 (state.val - 1216)
            else
              packedStateVectorCodeChunk39 (state.val - 1248)
      else
        if state.val < 1376 then
          if state.val < 1312 then
            packedStateVectorCodeChunk40 (state.val - 1280)
          else
            if state.val < 1344 then
              packedStateVectorCodeChunk41 (state.val - 1312)
            else
              packedStateVectorCodeChunk42 (state.val - 1344)
        else
          if state.val < 1408 then
            packedStateVectorCodeChunk43 (state.val - 1376)
          else
            if state.val < 1440 then
              packedStateVectorCodeChunk44 (state.val - 1408)
            else
              packedStateVectorCodeChunk45 (state.val - 1440)

def stateVector (state : Fin 1447)
    (coordinate : Fin 93) : Fin 6 :=
  ⟨(packedStateVectorCode state / 6 ^ coordinate.val) % 6,
    Nat.mod_lt _ (by decide)⟩

end SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3945.Shards
