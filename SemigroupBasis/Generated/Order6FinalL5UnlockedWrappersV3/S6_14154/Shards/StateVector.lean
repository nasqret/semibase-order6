import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.Shards.StateVectorPart00
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.Shards.StateVectorPart01

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.Shards

def packedStateVectorCode (state : Fin 1158) : Nat :=
  if state.val < 576 then
    if state.val < 288 then
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
            if state.val < 256 then
              packedStateVectorCodeChunk7 (state.val - 224)
            else
              packedStateVectorCodeChunk8 (state.val - 256)
    else
      if state.val < 416 then
        if state.val < 352 then
          if state.val < 320 then
            packedStateVectorCodeChunk9 (state.val - 288)
          else
            packedStateVectorCodeChunk10 (state.val - 320)
        else
          if state.val < 384 then
            packedStateVectorCodeChunk11 (state.val - 352)
          else
            packedStateVectorCodeChunk12 (state.val - 384)
      else
        if state.val < 480 then
          if state.val < 448 then
            packedStateVectorCodeChunk13 (state.val - 416)
          else
            packedStateVectorCodeChunk14 (state.val - 448)
        else
          if state.val < 512 then
            packedStateVectorCodeChunk15 (state.val - 480)
          else
            if state.val < 544 then
              packedStateVectorCodeChunk16 (state.val - 512)
            else
              packedStateVectorCodeChunk17 (state.val - 544)
  else
    if state.val < 864 then
      if state.val < 704 then
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
      if state.val < 1024 then
        if state.val < 928 then
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

def stateVector (state : Fin 1158)
    (coordinate : Fin 21) : Fin 6 :=
  ⟨(packedStateVectorCode state / 6 ^ coordinate.val) % 6,
    Nat.mod_lt _ (by decide)⟩

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14154.Shards
