import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14221.Shards.RepresentativeHeadPart00

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14221.Shards

def packedRepresentativeHeadBlockCode (index : Nat) : Nat :=
  if index < 96 then
    if index < 32 then
      packedRepresentativeHeadBlockCodeChunk0 index
    else
      if index < 64 then
        packedRepresentativeHeadBlockCodeChunk1 (index - 32)
      else
        packedRepresentativeHeadBlockCodeChunk2 (index - 64)
  else
    if index < 128 then
      packedRepresentativeHeadBlockCodeChunk3 (index - 96)
    else
      if index < 160 then
        packedRepresentativeHeadBlockCodeChunk4 (index - 128)
      else
        packedRepresentativeHeadBlockCodeChunk5 (index - 160)

def representativeHead (state : Fin 11742) : Fin 6 :=
  ⟨(packedRepresentativeHeadBlockCode (state.val / 64) /
      6 ^ (state.val % 64)) % 6,
    Nat.mod_lt _ (by decide)⟩

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14221.Shards
