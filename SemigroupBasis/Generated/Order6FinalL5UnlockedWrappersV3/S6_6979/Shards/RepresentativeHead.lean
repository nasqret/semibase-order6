import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.Shards.RepresentativeHeadPart00

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.Shards

def packedRepresentativeHeadBlockCode (index : Nat) : Nat :=
  if index < 64 then
    if index < 32 then
      packedRepresentativeHeadBlockCodeChunk0 index
    else
      packedRepresentativeHeadBlockCodeChunk1 (index - 32)
  else
    if index < 96 then
      packedRepresentativeHeadBlockCodeChunk2 (index - 64)
    else
      packedRepresentativeHeadBlockCodeChunk3 (index - 96)

def representativeHead (state : Fin 7782) : Fin 6 :=
  ⟨(packedRepresentativeHeadBlockCode (state.val / 64) /
      6 ^ (state.val % 64)) % 6,
    Nat.mod_lt _ (by decide)⟩

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.Shards
