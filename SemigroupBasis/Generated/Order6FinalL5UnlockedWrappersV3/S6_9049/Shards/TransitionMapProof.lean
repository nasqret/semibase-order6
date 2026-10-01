import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9049.Shards.TransitionMapProofPart00
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9049.Shards.TransitionMapProofPart01
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9049.Shards.TransitionMapProofPart02
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9049.Support.Core
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9049.Shards

set_option maxHeartbeats 2000000 in
theorem transitionMap
    (state : Fin 4374)
    (generator : Fin 6)
    (coordinate : Fin 22) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9049.stateVector
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9049.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9049.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9049.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9049.generatorVector generator coordinate) := by
  if hAt2176 : state.val < 2176 then
    if hAt1088 : state.val < 1088 then
      if hAt512 : state.val < 512 then
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
              exact transitionMapProof0007 state (by omega) (by omega) generator coordinate
      else
        if hAt768 : state.val < 768 then
          if hAt640 : state.val < 640 then
            if hAt576 : state.val < 576 then
              exact transitionMapProof0008 state (by omega) (by omega) generator coordinate
            else
              exact transitionMapProof0009 state (by omega) (by omega) generator coordinate
          else
            if hAt704 : state.val < 704 then
              exact transitionMapProof0010 state (by omega) (by omega) generator coordinate
            else
              exact transitionMapProof0011 state (by omega) (by omega) generator coordinate
        else
          if hAt896 : state.val < 896 then
            if hAt832 : state.val < 832 then
              exact transitionMapProof0012 state (by omega) (by omega) generator coordinate
            else
              exact transitionMapProof0013 state (by omega) (by omega) generator coordinate
          else
            if hAt960 : state.val < 960 then
              exact transitionMapProof0014 state (by omega) (by omega) generator coordinate
            else
              if hAt1024 : state.val < 1024 then
                exact transitionMapProof0015 state (by omega) (by omega) generator coordinate
              else
                exact transitionMapProof0016 state (by omega) (by omega) generator coordinate
    else
      if hAt1600 : state.val < 1600 then
        if hAt1344 : state.val < 1344 then
          if hAt1216 : state.val < 1216 then
            if hAt1152 : state.val < 1152 then
              exact transitionMapProof0017 state (by omega) (by omega) generator coordinate
            else
              exact transitionMapProof0018 state (by omega) (by omega) generator coordinate
          else
            if hAt1280 : state.val < 1280 then
              exact transitionMapProof0019 state (by omega) (by omega) generator coordinate
            else
              exact transitionMapProof0020 state (by omega) (by omega) generator coordinate
        else
          if hAt1472 : state.val < 1472 then
            if hAt1408 : state.val < 1408 then
              exact transitionMapProof0021 state (by omega) (by omega) generator coordinate
            else
              exact transitionMapProof0022 state (by omega) (by omega) generator coordinate
          else
            if hAt1536 : state.val < 1536 then
              exact transitionMapProof0023 state (by omega) (by omega) generator coordinate
            else
              exact transitionMapProof0024 state (by omega) (by omega) generator coordinate
      else
        if hAt1856 : state.val < 1856 then
          if hAt1728 : state.val < 1728 then
            if hAt1664 : state.val < 1664 then
              exact transitionMapProof0025 state (by omega) (by omega) generator coordinate
            else
              exact transitionMapProof0026 state (by omega) (by omega) generator coordinate
          else
            if hAt1792 : state.val < 1792 then
              exact transitionMapProof0027 state (by omega) (by omega) generator coordinate
            else
              exact transitionMapProof0028 state (by omega) (by omega) generator coordinate
        else
          if hAt1984 : state.val < 1984 then
            if hAt1920 : state.val < 1920 then
              exact transitionMapProof0029 state (by omega) (by omega) generator coordinate
            else
              exact transitionMapProof0030 state (by omega) (by omega) generator coordinate
          else
            if hAt2048 : state.val < 2048 then
              exact transitionMapProof0031 state (by omega) (by omega) generator coordinate
            else
              if hAt2112 : state.val < 2112 then
                exact transitionMapProof0032 state (by omega) (by omega) generator coordinate
              else
                exact transitionMapProof0033 state (by omega) (by omega) generator coordinate
  else
    if hAt3264 : state.val < 3264 then
      if hAt2688 : state.val < 2688 then
        if hAt2432 : state.val < 2432 then
          if hAt2304 : state.val < 2304 then
            if hAt2240 : state.val < 2240 then
              exact transitionMapProof0034 state (by omega) (by omega) generator coordinate
            else
              exact transitionMapProof0035 state (by omega) (by omega) generator coordinate
          else
            if hAt2368 : state.val < 2368 then
              exact transitionMapProof0036 state (by omega) (by omega) generator coordinate
            else
              exact transitionMapProof0037 state (by omega) (by omega) generator coordinate
        else
          if hAt2560 : state.val < 2560 then
            if hAt2496 : state.val < 2496 then
              exact transitionMapProof0038 state (by omega) (by omega) generator coordinate
            else
              exact transitionMapProof0039 state (by omega) (by omega) generator coordinate
          else
            if hAt2624 : state.val < 2624 then
              exact transitionMapProof0040 state (by omega) (by omega) generator coordinate
            else
              exact transitionMapProof0041 state (by omega) (by omega) generator coordinate
      else
        if hAt2944 : state.val < 2944 then
          if hAt2816 : state.val < 2816 then
            if hAt2752 : state.val < 2752 then
              exact transitionMapProof0042 state (by omega) (by omega) generator coordinate
            else
              exact transitionMapProof0043 state (by omega) (by omega) generator coordinate
          else
            if hAt2880 : state.val < 2880 then
              exact transitionMapProof0044 state (by omega) (by omega) generator coordinate
            else
              exact transitionMapProof0045 state (by omega) (by omega) generator coordinate
        else
          if hAt3072 : state.val < 3072 then
            if hAt3008 : state.val < 3008 then
              exact transitionMapProof0046 state (by omega) (by omega) generator coordinate
            else
              exact transitionMapProof0047 state (by omega) (by omega) generator coordinate
          else
            if hAt3136 : state.val < 3136 then
              exact transitionMapProof0048 state (by omega) (by omega) generator coordinate
            else
              if hAt3200 : state.val < 3200 then
                exact transitionMapProof0049 state (by omega) (by omega) generator coordinate
              else
                exact transitionMapProof0050 state (by omega) (by omega) generator coordinate
    else
      if hAt3840 : state.val < 3840 then
        if hAt3520 : state.val < 3520 then
          if hAt3392 : state.val < 3392 then
            if hAt3328 : state.val < 3328 then
              exact transitionMapProof0051 state (by omega) (by omega) generator coordinate
            else
              exact transitionMapProof0052 state (by omega) (by omega) generator coordinate
          else
            if hAt3456 : state.val < 3456 then
              exact transitionMapProof0053 state (by omega) (by omega) generator coordinate
            else
              exact transitionMapProof0054 state (by omega) (by omega) generator coordinate
        else
          if hAt3648 : state.val < 3648 then
            if hAt3584 : state.val < 3584 then
              exact transitionMapProof0055 state (by omega) (by omega) generator coordinate
            else
              exact transitionMapProof0056 state (by omega) (by omega) generator coordinate
          else
            if hAt3712 : state.val < 3712 then
              exact transitionMapProof0057 state (by omega) (by omega) generator coordinate
            else
              if hAt3776 : state.val < 3776 then
                exact transitionMapProof0058 state (by omega) (by omega) generator coordinate
              else
                exact transitionMapProof0059 state (by omega) (by omega) generator coordinate
      else
        if hAt4096 : state.val < 4096 then
          if hAt3968 : state.val < 3968 then
            if hAt3904 : state.val < 3904 then
              exact transitionMapProof0060 state (by omega) (by omega) generator coordinate
            else
              exact transitionMapProof0061 state (by omega) (by omega) generator coordinate
          else
            if hAt4032 : state.val < 4032 then
              exact transitionMapProof0062 state (by omega) (by omega) generator coordinate
            else
              exact transitionMapProof0063 state (by omega) (by omega) generator coordinate
        else
          if hAt4224 : state.val < 4224 then
            if hAt4160 : state.val < 4160 then
              exact transitionMapProof0064 state (by omega) (by omega) generator coordinate
            else
              exact transitionMapProof0065 state (by omega) (by omega) generator coordinate
          else
            if hAt4288 : state.val < 4288 then
              exact transitionMapProof0066 state (by omega) (by omega) generator coordinate
            else
              if hAt4352 : state.val < 4352 then
                exact transitionMapProof0067 state (by omega) (by omega) generator coordinate
              else
                exact transitionMapProof0068 state (by omega) (by omega) generator coordinate

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9049.Shards
