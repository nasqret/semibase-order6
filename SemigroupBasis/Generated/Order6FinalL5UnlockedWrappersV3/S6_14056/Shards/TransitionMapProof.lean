import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14056.Shards.TransitionMapProofPart00
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14056.Support.Core
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14056.Shards

set_option maxHeartbeats 2000000 in
theorem transitionMap
    (state : Fin 1158)
    (generator : Fin 6)
    (coordinate : Fin 32) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14056.stateVector
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14056.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14056.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14056.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14056.generatorVector generator coordinate) := by
  if hAt576 : state.val < 576 then
    if hAt256 : state.val < 256 then
      if hAt128 : state.val < 128 then
        if hAt64 : state.val < 64 then
          exact transitionMapProof0000 state (by omega) (by omega) generator coordinate
        else
          exact transitionMapProof0001 state (by omega) (by omega) generator coordinate
      else
        if hAt192 : state.val < 192 then
          exact transitionMapProof0002 state (by omega) (by omega) generator coordinate
        else
          exact transitionMapProof0003 state (by omega) (by omega) generator coordinate
    else
      if hAt384 : state.val < 384 then
        if hAt320 : state.val < 320 then
          exact transitionMapProof0004 state (by omega) (by omega) generator coordinate
        else
          exact transitionMapProof0005 state (by omega) (by omega) generator coordinate
      else
        if hAt448 : state.val < 448 then
          exact transitionMapProof0006 state (by omega) (by omega) generator coordinate
        else
          if hAt512 : state.val < 512 then
            exact transitionMapProof0007 state (by omega) (by omega) generator coordinate
          else
            exact transitionMapProof0008 state (by omega) (by omega) generator coordinate
  else
    if hAt896 : state.val < 896 then
      if hAt704 : state.val < 704 then
        if hAt640 : state.val < 640 then
          exact transitionMapProof0009 state (by omega) (by omega) generator coordinate
        else
          exact transitionMapProof0010 state (by omega) (by omega) generator coordinate
      else
        if hAt768 : state.val < 768 then
          exact transitionMapProof0011 state (by omega) (by omega) generator coordinate
        else
          if hAt832 : state.val < 832 then
            exact transitionMapProof0012 state (by omega) (by omega) generator coordinate
          else
            exact transitionMapProof0013 state (by omega) (by omega) generator coordinate
    else
      if hAt1024 : state.val < 1024 then
        if hAt960 : state.val < 960 then
          exact transitionMapProof0014 state (by omega) (by omega) generator coordinate
        else
          exact transitionMapProof0015 state (by omega) (by omega) generator coordinate
      else
        if hAt1088 : state.val < 1088 then
          exact transitionMapProof0016 state (by omega) (by omega) generator coordinate
        else
          if hAt1152 : state.val < 1152 then
            exact transitionMapProof0017 state (by omega) (by omega) generator coordinate
          else
            exact transitionMapProof0018 state (by omega) (by omega) generator coordinate

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14056.Shards
