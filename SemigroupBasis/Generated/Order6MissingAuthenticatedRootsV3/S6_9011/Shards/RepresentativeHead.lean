import SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.Shards.RepresentativeHeadPart00

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.Shards

def packedRepresentativeHeadBlockCode (index : Nat) : Nat :=
  if index < 32 then
    packedRepresentativeHeadBlockCodeChunk0 index
  else
    packedRepresentativeHeadBlockCodeChunk1 (index - 32)

def representativeHead (state : Fin 2712) : Fin 4 :=
  ⟨(packedRepresentativeHeadBlockCode (state.val / 64) /
      4 ^ (state.val % 64)) % 4,
    Nat.mod_lt _ (by decide)⟩

end SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.Shards
