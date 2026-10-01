import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9046.Shards.SourceLabelPart00

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9046.Shards

def packedSourceLabelBlockCode (index : Nat) : Nat :=
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

def sourceLabel (state : Fin 7782) : Fin 6 :=
  ⟨(packedSourceLabelBlockCode (state.val / 64) /
      6 ^ (state.val % 64)) % 6,
    Nat.mod_lt _ (by decide)⟩

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9046.Shards
