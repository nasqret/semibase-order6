import SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.Shards.TransitionMapProofPart00
import SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.Shards.TransitionMapProofPart01
import SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.Support.Core
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.Shards

set_option maxHeartbeats 2000000 in
theorem transitionMap
    (state : Fin 2712)
    (generator : Fin 4)
    (coordinate : Fin 17) :
    SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.stateVector
        (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.generatorVector generator coordinate) := by
  if hAt1344 : state.val < 1344 then
    if hAt640 : state.val < 640 then
      if hAt320 : state.val < 320 then
        if hAt128 : state.val < 128 then
          if hAt64 : state.val < 64 then
            exact transitionMapProof0000 state (by omega) (by omega) generator coordinate
          else
            exact transitionMapProof0001 state (by omega) (by omega) generator coordinate
        else
          if hAt192 : state.val < 192 then
            exact transitionMapProof0002 state (by omega) (by omega) generator coordinate
          else
            if hAt256 : state.val < 256 then
              exact transitionMapProof0003 state (by omega) (by omega) generator coordinate
            else
              exact transitionMapProof0004 state (by omega) (by omega) generator coordinate
      else
        if hAt448 : state.val < 448 then
          if hAt384 : state.val < 384 then
            exact transitionMapProof0005 state (by omega) (by omega) generator coordinate
          else
            exact transitionMapProof0006 state (by omega) (by omega) generator coordinate
        else
          if hAt512 : state.val < 512 then
            exact transitionMapProof0007 state (by omega) (by omega) generator coordinate
          else
            if hAt576 : state.val < 576 then
              exact transitionMapProof0008 state (by omega) (by omega) generator coordinate
            else
              exact transitionMapProof0009 state (by omega) (by omega) generator coordinate
    else
      if hAt960 : state.val < 960 then
        if hAt768 : state.val < 768 then
          if hAt704 : state.val < 704 then
            exact transitionMapProof0010 state (by omega) (by omega) generator coordinate
          else
            exact transitionMapProof0011 state (by omega) (by omega) generator coordinate
        else
          if hAt832 : state.val < 832 then
            exact transitionMapProof0012 state (by omega) (by omega) generator coordinate
          else
            if hAt896 : state.val < 896 then
              exact transitionMapProof0013 state (by omega) (by omega) generator coordinate
            else
              exact transitionMapProof0014 state (by omega) (by omega) generator coordinate
      else
        if hAt1152 : state.val < 1152 then
          if hAt1024 : state.val < 1024 then
            exact transitionMapProof0015 state (by omega) (by omega) generator coordinate
          else
            if hAt1088 : state.val < 1088 then
              exact transitionMapProof0016 state (by omega) (by omega) generator coordinate
            else
              exact transitionMapProof0017 state (by omega) (by omega) generator coordinate
        else
          if hAt1216 : state.val < 1216 then
            exact transitionMapProof0018 state (by omega) (by omega) generator coordinate
          else
            if hAt1280 : state.val < 1280 then
              exact transitionMapProof0019 state (by omega) (by omega) generator coordinate
            else
              exact transitionMapProof0020 state (by omega) (by omega) generator coordinate
  else
    if hAt2048 : state.val < 2048 then
      if hAt1664 : state.val < 1664 then
        if hAt1472 : state.val < 1472 then
          if hAt1408 : state.val < 1408 then
            exact transitionMapProof0021 state (by omega) (by omega) generator coordinate
          else
            exact transitionMapProof0022 state (by omega) (by omega) generator coordinate
        else
          if hAt1536 : state.val < 1536 then
            exact transitionMapProof0023 state (by omega) (by omega) generator coordinate
          else
            if hAt1600 : state.val < 1600 then
              exact transitionMapProof0024 state (by omega) (by omega) generator coordinate
            else
              exact transitionMapProof0025 state (by omega) (by omega) generator coordinate
      else
        if hAt1856 : state.val < 1856 then
          if hAt1728 : state.val < 1728 then
            exact transitionMapProof0026 state (by omega) (by omega) generator coordinate
          else
            if hAt1792 : state.val < 1792 then
              exact transitionMapProof0027 state (by omega) (by omega) generator coordinate
            else
              exact transitionMapProof0028 state (by omega) (by omega) generator coordinate
        else
          if hAt1920 : state.val < 1920 then
            exact transitionMapProof0029 state (by omega) (by omega) generator coordinate
          else
            if hAt1984 : state.val < 1984 then
              exact transitionMapProof0030 state (by omega) (by omega) generator coordinate
            else
              exact transitionMapProof0031 state (by omega) (by omega) generator coordinate
    else
      if hAt2368 : state.val < 2368 then
        if hAt2176 : state.val < 2176 then
          if hAt2112 : state.val < 2112 then
            exact transitionMapProof0032 state (by omega) (by omega) generator coordinate
          else
            exact transitionMapProof0033 state (by omega) (by omega) generator coordinate
        else
          if hAt2240 : state.val < 2240 then
            exact transitionMapProof0034 state (by omega) (by omega) generator coordinate
          else
            if hAt2304 : state.val < 2304 then
              exact transitionMapProof0035 state (by omega) (by omega) generator coordinate
            else
              exact transitionMapProof0036 state (by omega) (by omega) generator coordinate
      else
        if hAt2560 : state.val < 2560 then
          if hAt2432 : state.val < 2432 then
            exact transitionMapProof0037 state (by omega) (by omega) generator coordinate
          else
            if hAt2496 : state.val < 2496 then
              exact transitionMapProof0038 state (by omega) (by omega) generator coordinate
            else
              exact transitionMapProof0039 state (by omega) (by omega) generator coordinate
        else
          if hAt2624 : state.val < 2624 then
            exact transitionMapProof0040 state (by omega) (by omega) generator coordinate
          else
            if hAt2688 : state.val < 2688 then
              exact transitionMapProof0041 state (by omega) (by omega) generator coordinate
            else
              exact transitionMapProof0042 state (by omega) (by omega) generator coordinate

end SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.Shards
