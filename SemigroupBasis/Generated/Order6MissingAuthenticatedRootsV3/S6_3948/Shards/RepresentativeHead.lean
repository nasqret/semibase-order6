import SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.Shards.RepresentativeHeadPart00

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.Shards

def packedRepresentativeHeadBlockCode (index : Nat) : Nat :=
  packedRepresentativeHeadBlockCodeChunk0 index

def representativeHead (state : Fin 1447) : Fin 4 :=
  ⟨(packedRepresentativeHeadBlockCode (state.val / 64) /
      4 ^ (state.val % 64)) % 4,
    Nat.mod_lt _ (by decide)⟩

end SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.Shards
