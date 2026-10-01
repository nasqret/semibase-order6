import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6845.Shards.SourceLabelPart00

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6845.Shards

def packedSourceLabelBlockCode (index : Nat) : Nat :=
  if index < 32 then
    packedSourceLabelBlockCodeChunk0 index
  else
    if index < 64 then
      packedSourceLabelBlockCodeChunk1 (index - 32)
    else
      packedSourceLabelBlockCodeChunk2 (index - 64)

def sourceLabel (state : Fin 4374) : Fin 6 :=
  ⟨(packedSourceLabelBlockCode (state.val / 64) /
      6 ^ (state.val % 64)) % 6,
    Nat.mod_lt _ (by decide)⟩

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6845.Shards
