import SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.Shards.DecodeStateProofPart00
import SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.Shards.DecodeStateProofPart01

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.Shards

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVector (state : Fin 2712) :
    decodeState (stateVector state) = state := by
  if hAt1344 : state.val < 1344 then
    if hAt640 : state.val < 640 then
      if hAt320 : state.val < 320 then
        if hAt128 : state.val < 128 then
          if hAt64 : state.val < 64 then
            exact decodeState_stateVectorProof0000 state (by omega) (by omega)
          else
            exact decodeState_stateVectorProof0001 state (by omega) (by omega)
        else
          if hAt192 : state.val < 192 then
            exact decodeState_stateVectorProof0002 state (by omega) (by omega)
          else
            if hAt256 : state.val < 256 then
              exact decodeState_stateVectorProof0003 state (by omega) (by omega)
            else
              exact decodeState_stateVectorProof0004 state (by omega) (by omega)
      else
        if hAt448 : state.val < 448 then
          if hAt384 : state.val < 384 then
            exact decodeState_stateVectorProof0005 state (by omega) (by omega)
          else
            exact decodeState_stateVectorProof0006 state (by omega) (by omega)
        else
          if hAt512 : state.val < 512 then
            exact decodeState_stateVectorProof0007 state (by omega) (by omega)
          else
            if hAt576 : state.val < 576 then
              exact decodeState_stateVectorProof0008 state (by omega) (by omega)
            else
              exact decodeState_stateVectorProof0009 state (by omega) (by omega)
    else
      if hAt960 : state.val < 960 then
        if hAt768 : state.val < 768 then
          if hAt704 : state.val < 704 then
            exact decodeState_stateVectorProof0010 state (by omega) (by omega)
          else
            exact decodeState_stateVectorProof0011 state (by omega) (by omega)
        else
          if hAt832 : state.val < 832 then
            exact decodeState_stateVectorProof0012 state (by omega) (by omega)
          else
            if hAt896 : state.val < 896 then
              exact decodeState_stateVectorProof0013 state (by omega) (by omega)
            else
              exact decodeState_stateVectorProof0014 state (by omega) (by omega)
      else
        if hAt1152 : state.val < 1152 then
          if hAt1024 : state.val < 1024 then
            exact decodeState_stateVectorProof0015 state (by omega) (by omega)
          else
            if hAt1088 : state.val < 1088 then
              exact decodeState_stateVectorProof0016 state (by omega) (by omega)
            else
              exact decodeState_stateVectorProof0017 state (by omega) (by omega)
        else
          if hAt1216 : state.val < 1216 then
            exact decodeState_stateVectorProof0018 state (by omega) (by omega)
          else
            if hAt1280 : state.val < 1280 then
              exact decodeState_stateVectorProof0019 state (by omega) (by omega)
            else
              exact decodeState_stateVectorProof0020 state (by omega) (by omega)
  else
    if hAt2048 : state.val < 2048 then
      if hAt1664 : state.val < 1664 then
        if hAt1472 : state.val < 1472 then
          if hAt1408 : state.val < 1408 then
            exact decodeState_stateVectorProof0021 state (by omega) (by omega)
          else
            exact decodeState_stateVectorProof0022 state (by omega) (by omega)
        else
          if hAt1536 : state.val < 1536 then
            exact decodeState_stateVectorProof0023 state (by omega) (by omega)
          else
            if hAt1600 : state.val < 1600 then
              exact decodeState_stateVectorProof0024 state (by omega) (by omega)
            else
              exact decodeState_stateVectorProof0025 state (by omega) (by omega)
      else
        if hAt1856 : state.val < 1856 then
          if hAt1728 : state.val < 1728 then
            exact decodeState_stateVectorProof0026 state (by omega) (by omega)
          else
            if hAt1792 : state.val < 1792 then
              exact decodeState_stateVectorProof0027 state (by omega) (by omega)
            else
              exact decodeState_stateVectorProof0028 state (by omega) (by omega)
        else
          if hAt1920 : state.val < 1920 then
            exact decodeState_stateVectorProof0029 state (by omega) (by omega)
          else
            if hAt1984 : state.val < 1984 then
              exact decodeState_stateVectorProof0030 state (by omega) (by omega)
            else
              exact decodeState_stateVectorProof0031 state (by omega) (by omega)
    else
      if hAt2368 : state.val < 2368 then
        if hAt2176 : state.val < 2176 then
          if hAt2112 : state.val < 2112 then
            exact decodeState_stateVectorProof0032 state (by omega) (by omega)
          else
            exact decodeState_stateVectorProof0033 state (by omega) (by omega)
        else
          if hAt2240 : state.val < 2240 then
            exact decodeState_stateVectorProof0034 state (by omega) (by omega)
          else
            if hAt2304 : state.val < 2304 then
              exact decodeState_stateVectorProof0035 state (by omega) (by omega)
            else
              exact decodeState_stateVectorProof0036 state (by omega) (by omega)
      else
        if hAt2560 : state.val < 2560 then
          if hAt2432 : state.val < 2432 then
            exact decodeState_stateVectorProof0037 state (by omega) (by omega)
          else
            if hAt2496 : state.val < 2496 then
              exact decodeState_stateVectorProof0038 state (by omega) (by omega)
            else
              exact decodeState_stateVectorProof0039 state (by omega) (by omega)
        else
          if hAt2624 : state.val < 2624 then
            exact decodeState_stateVectorProof0040 state (by omega) (by omega)
          else
            if hAt2688 : state.val < 2688 then
              exact decodeState_stateVectorProof0041 state (by omega) (by omega)
            else
              exact decodeState_stateVectorProof0042 state (by omega) (by omega)

end SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.Shards
