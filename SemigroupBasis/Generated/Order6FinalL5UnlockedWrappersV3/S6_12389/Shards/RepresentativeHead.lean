import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.Shards.RepresentativeHeadPart00

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.Shards

def packedRepresentativeHeadBlockCode (index : Nat) : Nat :=
  if index < 128 then
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
  else
    if index < 192 then
      if index < 160 then
        packedRepresentativeHeadBlockCodeChunk4 (index - 128)
      else
        packedRepresentativeHeadBlockCodeChunk5 (index - 160)
    else
      if index < 224 then
        packedRepresentativeHeadBlockCodeChunk6 (index - 192)
      else
        if index < 256 then
          packedRepresentativeHeadBlockCodeChunk7 (index - 224)
        else
          packedRepresentativeHeadBlockCodeChunk8 (index - 256)

def representativeHead (state : Fin 17622) : Fin 6 :=
  ⟨(packedRepresentativeHeadBlockCode (state.val / 64) /
      6 ^ (state.val % 64)) % 6,
    Nat.mod_lt _ (by decide)⟩

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12389.Shards
