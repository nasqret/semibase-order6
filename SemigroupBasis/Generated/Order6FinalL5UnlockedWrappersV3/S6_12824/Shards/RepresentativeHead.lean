import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards.RepresentativeHeadPart00

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards

def packedRepresentativeHeadBlockCode (index : Nat) : Nat :=
  if index < 384 then
    if index < 192 then
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
    else
      if index < 288 then
        if index < 224 then
          packedRepresentativeHeadBlockCodeChunk6 (index - 192)
        else
          if index < 256 then
            packedRepresentativeHeadBlockCodeChunk7 (index - 224)
          else
            packedRepresentativeHeadBlockCodeChunk8 (index - 256)
      else
        if index < 320 then
          packedRepresentativeHeadBlockCodeChunk9 (index - 288)
        else
          if index < 352 then
            packedRepresentativeHeadBlockCodeChunk10 (index - 320)
          else
            packedRepresentativeHeadBlockCodeChunk11 (index - 352)
  else
    if index < 576 then
      if index < 480 then
        if index < 416 then
          packedRepresentativeHeadBlockCodeChunk12 (index - 384)
        else
          if index < 448 then
            packedRepresentativeHeadBlockCodeChunk13 (index - 416)
          else
            packedRepresentativeHeadBlockCodeChunk14 (index - 448)
      else
        if index < 512 then
          packedRepresentativeHeadBlockCodeChunk15 (index - 480)
        else
          if index < 544 then
            packedRepresentativeHeadBlockCodeChunk16 (index - 512)
          else
            packedRepresentativeHeadBlockCodeChunk17 (index - 544)
    else
      if index < 672 then
        if index < 608 then
          packedRepresentativeHeadBlockCodeChunk18 (index - 576)
        else
          if index < 640 then
            packedRepresentativeHeadBlockCodeChunk19 (index - 608)
          else
            packedRepresentativeHeadBlockCodeChunk20 (index - 640)
      else
        if index < 704 then
          packedRepresentativeHeadBlockCodeChunk21 (index - 672)
        else
          if index < 736 then
            packedRepresentativeHeadBlockCodeChunk22 (index - 704)
          else
            packedRepresentativeHeadBlockCodeChunk23 (index - 736)

def representativeHead (state : Fin 48684) : Fin 6 :=
  ⟨(packedRepresentativeHeadBlockCode (state.val / 64) /
      6 ^ (state.val % 64)) % 6,
    Nat.mod_lt _ (by decide)⟩

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12824.Shards
