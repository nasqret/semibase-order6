import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6984.Shards.RepresentativeHeadPart00

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6984.Shards

def packedRepresentativeHeadBlockCode (index : Nat) : Nat :=
  if index < 32 then
    packedRepresentativeHeadBlockCodeChunk0 index
  else
    if index < 64 then
      packedRepresentativeHeadBlockCodeChunk1 (index - 32)
    else
      packedRepresentativeHeadBlockCodeChunk2 (index - 64)

def representativeHead (state : Fin 4374) : Fin 6 :=
  ⟨(packedRepresentativeHeadBlockCode (state.val / 64) /
      6 ^ (state.val % 64)) % 6,
    Nat.mod_lt _ (by decide)⟩

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6984.Shards
