import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14266.Shards.TransitionPart00
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14266.Shards.TransitionPart01

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14266.Shards

def packedTransitionCode (state : Fin 1158) : Nat :=
  if state.val < 576 then
    if state.val < 288 then
      if state.val < 128 then
        if state.val < 64 then
          if state.val < 32 then
            packedTransitionCodeChunk0 state.val
          else
            packedTransitionCodeChunk1 (state.val - 32)
        else
          if state.val < 96 then
            packedTransitionCodeChunk2 (state.val - 64)
          else
            packedTransitionCodeChunk3 (state.val - 96)
      else
        if state.val < 192 then
          if state.val < 160 then
            packedTransitionCodeChunk4 (state.val - 128)
          else
            packedTransitionCodeChunk5 (state.val - 160)
        else
          if state.val < 224 then
            packedTransitionCodeChunk6 (state.val - 192)
          else
            if state.val < 256 then
              packedTransitionCodeChunk7 (state.val - 224)
            else
              packedTransitionCodeChunk8 (state.val - 256)
    else
      if state.val < 416 then
        if state.val < 352 then
          if state.val < 320 then
            packedTransitionCodeChunk9 (state.val - 288)
          else
            packedTransitionCodeChunk10 (state.val - 320)
        else
          if state.val < 384 then
            packedTransitionCodeChunk11 (state.val - 352)
          else
            packedTransitionCodeChunk12 (state.val - 384)
      else
        if state.val < 480 then
          if state.val < 448 then
            packedTransitionCodeChunk13 (state.val - 416)
          else
            packedTransitionCodeChunk14 (state.val - 448)
        else
          if state.val < 512 then
            packedTransitionCodeChunk15 (state.val - 480)
          else
            if state.val < 544 then
              packedTransitionCodeChunk16 (state.val - 512)
            else
              packedTransitionCodeChunk17 (state.val - 544)
  else
    if state.val < 864 then
      if state.val < 704 then
        if state.val < 640 then
          if state.val < 608 then
            packedTransitionCodeChunk18 (state.val - 576)
          else
            packedTransitionCodeChunk19 (state.val - 608)
        else
          if state.val < 672 then
            packedTransitionCodeChunk20 (state.val - 640)
          else
            packedTransitionCodeChunk21 (state.val - 672)
      else
        if state.val < 768 then
          if state.val < 736 then
            packedTransitionCodeChunk22 (state.val - 704)
          else
            packedTransitionCodeChunk23 (state.val - 736)
        else
          if state.val < 800 then
            packedTransitionCodeChunk24 (state.val - 768)
          else
            if state.val < 832 then
              packedTransitionCodeChunk25 (state.val - 800)
            else
              packedTransitionCodeChunk26 (state.val - 832)
    else
      if state.val < 1024 then
        if state.val < 928 then
          if state.val < 896 then
            packedTransitionCodeChunk27 (state.val - 864)
          else
            packedTransitionCodeChunk28 (state.val - 896)
        else
          if state.val < 960 then
            packedTransitionCodeChunk29 (state.val - 928)
          else
            if state.val < 992 then
              packedTransitionCodeChunk30 (state.val - 960)
            else
              packedTransitionCodeChunk31 (state.val - 992)
      else
        if state.val < 1088 then
          if state.val < 1056 then
            packedTransitionCodeChunk32 (state.val - 1024)
          else
            packedTransitionCodeChunk33 (state.val - 1056)
        else
          if state.val < 1120 then
            packedTransitionCodeChunk34 (state.val - 1088)
          else
            if state.val < 1152 then
              packedTransitionCodeChunk35 (state.val - 1120)
            else
              packedTransitionCodeChunk36 (state.val - 1152)

def transition (state : Fin 1158)
    (generator : Fin 6) : Fin 1158 :=
  ⟨(packedTransitionCode state / 1158 ^ generator.val) % 1158,
    Nat.mod_lt _ (by decide)⟩

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14266.Shards
