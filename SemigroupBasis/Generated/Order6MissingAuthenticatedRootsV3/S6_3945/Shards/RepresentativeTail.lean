import SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3945.Shards.RepresentativeTailPart00
import SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3945.Shards.RepresentativeTailPart01

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3945.Shards

def representativeTail (state : Fin 1447) :
    List (Fin 4) :=
  if state.val < 736 then
    if state.val < 352 then
      if state.val < 160 then
        if state.val < 64 then
          if state.val < 32 then
            representativeTailChunk0 state.val
          else
            representativeTailChunk1 (state.val - 32)
        else
          if state.val < 96 then
            representativeTailChunk2 (state.val - 64)
          else
            if state.val < 128 then
              representativeTailChunk3 (state.val - 96)
            else
              representativeTailChunk4 (state.val - 128)
      else
        if state.val < 256 then
          if state.val < 192 then
            representativeTailChunk5 (state.val - 160)
          else
            if state.val < 224 then
              representativeTailChunk6 (state.val - 192)
            else
              representativeTailChunk7 (state.val - 224)
        else
          if state.val < 288 then
            representativeTailChunk8 (state.val - 256)
          else
            if state.val < 320 then
              representativeTailChunk9 (state.val - 288)
            else
              representativeTailChunk10 (state.val - 320)
    else
      if state.val < 544 then
        if state.val < 448 then
          if state.val < 384 then
            representativeTailChunk11 (state.val - 352)
          else
            if state.val < 416 then
              representativeTailChunk12 (state.val - 384)
            else
              representativeTailChunk13 (state.val - 416)
        else
          if state.val < 480 then
            representativeTailChunk14 (state.val - 448)
          else
            if state.val < 512 then
              representativeTailChunk15 (state.val - 480)
            else
              representativeTailChunk16 (state.val - 512)
      else
        if state.val < 640 then
          if state.val < 576 then
            representativeTailChunk17 (state.val - 544)
          else
            if state.val < 608 then
              representativeTailChunk18 (state.val - 576)
            else
              representativeTailChunk19 (state.val - 608)
        else
          if state.val < 672 then
            representativeTailChunk20 (state.val - 640)
          else
            if state.val < 704 then
              representativeTailChunk21 (state.val - 672)
            else
              representativeTailChunk22 (state.val - 704)
  else
    if state.val < 1088 then
      if state.val < 896 then
        if state.val < 800 then
          if state.val < 768 then
            representativeTailChunk23 (state.val - 736)
          else
            representativeTailChunk24 (state.val - 768)
        else
          if state.val < 832 then
            representativeTailChunk25 (state.val - 800)
          else
            if state.val < 864 then
              representativeTailChunk26 (state.val - 832)
            else
              representativeTailChunk27 (state.val - 864)
      else
        if state.val < 992 then
          if state.val < 928 then
            representativeTailChunk28 (state.val - 896)
          else
            if state.val < 960 then
              representativeTailChunk29 (state.val - 928)
            else
              representativeTailChunk30 (state.val - 960)
        else
          if state.val < 1024 then
            representativeTailChunk31 (state.val - 992)
          else
            if state.val < 1056 then
              representativeTailChunk32 (state.val - 1024)
            else
              representativeTailChunk33 (state.val - 1056)
    else
      if state.val < 1280 then
        if state.val < 1184 then
          if state.val < 1120 then
            representativeTailChunk34 (state.val - 1088)
          else
            if state.val < 1152 then
              representativeTailChunk35 (state.val - 1120)
            else
              representativeTailChunk36 (state.val - 1152)
        else
          if state.val < 1216 then
            representativeTailChunk37 (state.val - 1184)
          else
            if state.val < 1248 then
              representativeTailChunk38 (state.val - 1216)
            else
              representativeTailChunk39 (state.val - 1248)
      else
        if state.val < 1376 then
          if state.val < 1312 then
            representativeTailChunk40 (state.val - 1280)
          else
            if state.val < 1344 then
              representativeTailChunk41 (state.val - 1312)
            else
              representativeTailChunk42 (state.val - 1344)
        else
          if state.val < 1408 then
            representativeTailChunk43 (state.val - 1376)
          else
            if state.val < 1440 then
              representativeTailChunk44 (state.val - 1408)
            else
              representativeTailChunk45 (state.val - 1440)

end SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3945.Shards
