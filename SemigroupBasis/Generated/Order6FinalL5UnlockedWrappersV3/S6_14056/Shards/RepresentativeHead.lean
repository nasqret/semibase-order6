import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14056.Shards.RepresentativeHeadPart00

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14056.Shards

def packedRepresentativeHeadBlockCode (index : Nat) : Nat :=
  packedRepresentativeHeadBlockCodeChunk0 index

def representativeHead (state : Fin 1158) : Fin 6 :=
  ⟨(packedRepresentativeHeadBlockCode (state.val / 64) /
      6 ^ (state.val % 64)) % 6,
    Nat.mod_lt _ (by decide)⟩

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14056.Shards
