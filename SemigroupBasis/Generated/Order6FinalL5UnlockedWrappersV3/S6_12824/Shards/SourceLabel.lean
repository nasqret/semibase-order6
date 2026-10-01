import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards.SourceLabelPart00

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards

def packedSourceLabelBlockCode (index : Nat) : Nat :=
  if index < 384 then
    if index < 192 then
      if index < 96 then
        if index < 32 then
          packedSourceLabelBlockCodeChunk0 index
        else
          if index < 64 then
            packedSourceLabelBlockCodeChunk1 (index - 32)
          else
            packedSourceLabelBlockCodeChunk2 (index - 64)
      else
        if index < 128 then
          packedSourceLabelBlockCodeChunk3 (index - 96)
        else
          if index < 160 then
            packedSourceLabelBlockCodeChunk4 (index - 128)
          else
            packedSourceLabelBlockCodeChunk5 (index - 160)
    else
      if index < 288 then
        if index < 224 then
          packedSourceLabelBlockCodeChunk6 (index - 192)
        else
          if index < 256 then
            packedSourceLabelBlockCodeChunk7 (index - 224)
          else
            packedSourceLabelBlockCodeChunk8 (index - 256)
      else
        if index < 320 then
          packedSourceLabelBlockCodeChunk9 (index - 288)
        else
          if index < 352 then
            packedSourceLabelBlockCodeChunk10 (index - 320)
          else
            packedSourceLabelBlockCodeChunk11 (index - 352)
  else
    if index < 576 then
      if index < 480 then
        if index < 416 then
          packedSourceLabelBlockCodeChunk12 (index - 384)
        else
          if index < 448 then
            packedSourceLabelBlockCodeChunk13 (index - 416)
          else
            packedSourceLabelBlockCodeChunk14 (index - 448)
      else
        if index < 512 then
          packedSourceLabelBlockCodeChunk15 (index - 480)
        else
          if index < 544 then
            packedSourceLabelBlockCodeChunk16 (index - 512)
          else
            packedSourceLabelBlockCodeChunk17 (index - 544)
    else
      if index < 672 then
        if index < 608 then
          packedSourceLabelBlockCodeChunk18 (index - 576)
        else
          if index < 640 then
            packedSourceLabelBlockCodeChunk19 (index - 608)
          else
            packedSourceLabelBlockCodeChunk20 (index - 640)
      else
        if index < 704 then
          packedSourceLabelBlockCodeChunk21 (index - 672)
        else
          if index < 736 then
            packedSourceLabelBlockCodeChunk22 (index - 704)
          else
            packedSourceLabelBlockCodeChunk23 (index - 736)

def sourceLabel (state : Fin 48684) : Fin 6 :=
  ⟨(packedSourceLabelBlockCode (state.val / 64) /
      6 ^ (state.val % 64)) % 6,
    Nat.mod_lt _ (by decide)⟩

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards
