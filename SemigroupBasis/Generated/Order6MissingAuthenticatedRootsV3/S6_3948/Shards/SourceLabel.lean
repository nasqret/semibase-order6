import SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.Shards.SourceLabelPart00

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.Shards

def packedSourceLabelBlockCode (index : Nat) : Nat :=
  packedSourceLabelBlockCodeChunk0 index

def sourceLabel (state : Fin 1447) : Fin 6 :=
  ⟨(packedSourceLabelBlockCode (state.val / 64) /
      6 ^ (state.val % 64)) % 6,
    Nat.mod_lt _ (by decide)⟩

end SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.Shards
