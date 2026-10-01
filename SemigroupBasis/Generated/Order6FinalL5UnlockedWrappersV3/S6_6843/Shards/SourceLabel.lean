import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.Shards.SourceLabelPart00

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.Shards

def packedSourceLabelBlockCode (index : Nat) : Nat :=
  if index < 128 then
    if index < 64 then
      if index < 32 then
        packedSourceLabelBlockCodeChunk0 index
      else
        packedSourceLabelBlockCodeChunk1 (index - 32)
    else
      if index < 96 then
        packedSourceLabelBlockCodeChunk2 (index - 64)
      else
        packedSourceLabelBlockCodeChunk3 (index - 96)
  else
    if index < 192 then
      if index < 160 then
        packedSourceLabelBlockCodeChunk4 (index - 128)
      else
        packedSourceLabelBlockCodeChunk5 (index - 160)
    else
      if index < 224 then
        packedSourceLabelBlockCodeChunk6 (index - 192)
      else
        if index < 256 then
          packedSourceLabelBlockCodeChunk7 (index - 224)
        else
          packedSourceLabelBlockCodeChunk8 (index - 256)

def sourceLabel (state : Fin 18432) : Fin 6 :=
  ⟨(packedSourceLabelBlockCode (state.val / 64) /
      6 ^ (state.val % 64)) % 6,
    Nat.mod_lt _ (by decide)⟩

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6843.Shards
