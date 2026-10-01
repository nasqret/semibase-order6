import SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3945.Shards.TransitionPart00
import SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3945.Shards.TransitionPart01

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3945.Shards

def packedTransitionCode (state : Fin 1447) : Nat :=
  if state.val < 736 then
    if state.val < 352 then
      if state.val < 160 then
        if state.val < 64 then
          if state.val < 32 then
            packedTransitionCodeChunk0 state.val
          else
            packedTransitionCodeChunk1 (state.val - 32)
        else
          if state.val < 96 then
            packedTransitionCodeChunk2 (state.val - 64)
          else
            if state.val < 128 then
              packedTransitionCodeChunk3 (state.val - 96)
            else
              packedTransitionCodeChunk4 (state.val - 128)
      else
        if state.val < 256 then
          if state.val < 192 then
            packedTransitionCodeChunk5 (state.val - 160)
          else
            if state.val < 224 then
              packedTransitionCodeChunk6 (state.val - 192)
            else
              packedTransitionCodeChunk7 (state.val - 224)
        else
          if state.val < 288 then
            packedTransitionCodeChunk8 (state.val - 256)
          else
            if state.val < 320 then
              packedTransitionCodeChunk9 (state.val - 288)
            else
              packedTransitionCodeChunk10 (state.val - 320)
    else
      if state.val < 544 then
        if state.val < 448 then
          if state.val < 384 then
            packedTransitionCodeChunk11 (state.val - 352)
          else
            if state.val < 416 then
              packedTransitionCodeChunk12 (state.val - 384)
            else
              packedTransitionCodeChunk13 (state.val - 416)
        else
          if state.val < 480 then
            packedTransitionCodeChunk14 (state.val - 448)
          else
            if state.val < 512 then
              packedTransitionCodeChunk15 (state.val - 480)
            else
              packedTransitionCodeChunk16 (state.val - 512)
      else
        if state.val < 640 then
          if state.val < 576 then
            packedTransitionCodeChunk17 (state.val - 544)
          else
            if state.val < 608 then
              packedTransitionCodeChunk18 (state.val - 576)
            else
              packedTransitionCodeChunk19 (state.val - 608)
        else
          if state.val < 672 then
            packedTransitionCodeChunk20 (state.val - 640)
          else
            if state.val < 704 then
              packedTransitionCodeChunk21 (state.val - 672)
            else
              packedTransitionCodeChunk22 (state.val - 704)
  else
    if state.val < 1088 then
      if state.val < 896 then
        if state.val < 800 then
          if state.val < 768 then
            packedTransitionCodeChunk23 (state.val - 736)
          else
            packedTransitionCodeChunk24 (state.val - 768)
        else
          if state.val < 832 then
            packedTransitionCodeChunk25 (state.val - 800)
          else
            if state.val < 864 then
              packedTransitionCodeChunk26 (state.val - 832)
            else
              packedTransitionCodeChunk27 (state.val - 864)
      else
        if state.val < 992 then
          if state.val < 928 then
            packedTransitionCodeChunk28 (state.val - 896)
          else
            if state.val < 960 then
              packedTransitionCodeChunk29 (state.val - 928)
            else
              packedTransitionCodeChunk30 (state.val - 960)
        else
          if state.val < 1024 then
            packedTransitionCodeChunk31 (state.val - 992)
          else
            if state.val < 1056 then
              packedTransitionCodeChunk32 (state.val - 1024)
            else
              packedTransitionCodeChunk33 (state.val - 1056)
    else
      if state.val < 1280 then
        if state.val < 1184 then
          if state.val < 1120 then
            packedTransitionCodeChunk34 (state.val - 1088)
          else
            if state.val < 1152 then
              packedTransitionCodeChunk35 (state.val - 1120)
            else
              packedTransitionCodeChunk36 (state.val - 1152)
        else
          if state.val < 1216 then
            packedTransitionCodeChunk37 (state.val - 1184)
          else
            if state.val < 1248 then
              packedTransitionCodeChunk38 (state.val - 1216)
            else
              packedTransitionCodeChunk39 (state.val - 1248)
      else
        if state.val < 1376 then
          if state.val < 1312 then
            packedTransitionCodeChunk40 (state.val - 1280)
          else
            if state.val < 1344 then
              packedTransitionCodeChunk41 (state.val - 1312)
            else
              packedTransitionCodeChunk42 (state.val - 1344)
        else
          if state.val < 1408 then
            packedTransitionCodeChunk43 (state.val - 1376)
          else
            if state.val < 1440 then
              packedTransitionCodeChunk44 (state.val - 1408)
            else
              packedTransitionCodeChunk45 (state.val - 1440)

def transition (state : Fin 1447)
    (generator : Fin 4) : Fin 1447 :=
  ⟨(packedTransitionCode state / 1447 ^ generator.val) % 1447,
    Nat.mod_lt _ (by decide)⟩

end SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3945.Shards
