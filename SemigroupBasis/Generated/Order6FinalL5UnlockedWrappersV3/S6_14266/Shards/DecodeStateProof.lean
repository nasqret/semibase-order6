import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14266.Shards.DecodeStateProofPart00

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14266.Shards

set_option maxHeartbeats 2000000 in
theorem decodeState_stateVector (state : Fin 1158) :
    decodeState (stateVector state) = state := by
  if hAt576 : state.val < 576 then
    if hAt256 : state.val < 256 then
      if hAt128 : state.val < 128 then
        if hAt64 : state.val < 64 then
          exact decodeState_stateVectorProof0000 state (by omega) (by omega)
        else
          exact decodeState_stateVectorProof0001 state (by omega) (by omega)
      else
        if hAt192 : state.val < 192 then
          exact decodeState_stateVectorProof0002 state (by omega) (by omega)
        else
          exact decodeState_stateVectorProof0003 state (by omega) (by omega)
    else
      if hAt384 : state.val < 384 then
        if hAt320 : state.val < 320 then
          exact decodeState_stateVectorProof0004 state (by omega) (by omega)
        else
          exact decodeState_stateVectorProof0005 state (by omega) (by omega)
      else
        if hAt448 : state.val < 448 then
          exact decodeState_stateVectorProof0006 state (by omega) (by omega)
        else
          if hAt512 : state.val < 512 then
            exact decodeState_stateVectorProof0007 state (by omega) (by omega)
          else
            exact decodeState_stateVectorProof0008 state (by omega) (by omega)
  else
    if hAt896 : state.val < 896 then
      if hAt704 : state.val < 704 then
        if hAt640 : state.val < 640 then
          exact decodeState_stateVectorProof0009 state (by omega) (by omega)
        else
          exact decodeState_stateVectorProof0010 state (by omega) (by omega)
      else
        if hAt768 : state.val < 768 then
          exact decodeState_stateVectorProof0011 state (by omega) (by omega)
        else
          if hAt832 : state.val < 832 then
            exact decodeState_stateVectorProof0012 state (by omega) (by omega)
          else
            exact decodeState_stateVectorProof0013 state (by omega) (by omega)
    else
      if hAt1024 : state.val < 1024 then
        if hAt960 : state.val < 960 then
          exact decodeState_stateVectorProof0014 state (by omega) (by omega)
        else
          exact decodeState_stateVectorProof0015 state (by omega) (by omega)
      else
        if hAt1088 : state.val < 1088 then
          exact decodeState_stateVectorProof0016 state (by omega) (by omega)
        else
          if hAt1152 : state.val < 1152 then
            exact decodeState_stateVectorProof0017 state (by omega) (by omega)
          else
            exact decodeState_stateVectorProof0018 state (by omega) (by omega)

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14266.Shards
