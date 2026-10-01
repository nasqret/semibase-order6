import SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.Shards.SourceLabelPart00

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.Shards

def packedSourceLabelBlockCode (index : Nat) : Nat :=
  if index < 32 then
    packedSourceLabelBlockCodeChunk0 index
  else
    packedSourceLabelBlockCodeChunk1 (index - 32)

def sourceLabel (state : Fin 2712) : Fin 6 :=
  ⟨(packedSourceLabelBlockCode (state.val / 64) /
      6 ^ (state.val % 64)) % 6,
    Nat.mod_lt _ (by decide)⟩

end SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.Shards
