import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14268.Shards.SourceLabelPart00

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14268.Shards

def packedSourceLabelBlockCode (index : Nat) : Nat :=
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

def sourceLabel (state : Fin 11742) : Fin 6 :=
  ⟨(packedSourceLabelBlockCode (state.val / 64) /
      6 ^ (state.val % 64)) % 6,
    Nat.mod_lt _ (by decide)⟩

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14268.Shards
