import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.Shards.TransitionMapProofPart00
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.Shards.TransitionMapProofPart01
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.Shards.TransitionMapProofPart02
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.Shards.TransitionMapProofPart03
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.Support.Core
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.Shards

set_option maxHeartbeats 2000000 in
theorem transitionMap
    (state : Fin 7782)
    (generator : Fin 6)
    (coordinate : Fin 22) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.stateVector
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.generatorVector generator coordinate) := by
  if hAt3904 : state.val < 3904 then
    if hAt1920 : state.val < 1920 then
      if hAt960 : state.val < 960 then
        if hAt448 : state.val < 448 then
          if hAt192 : state.val < 192 then
            if hAt64 : state.val < 64 then
              exact transitionMapProof0000 state (by omega) (by omega) generator coordinate
            else
              if hAt128 : state.val < 128 then
                exact transitionMapProof0001 state (by omega) (by omega) generator coordinate
              else
                exact transitionMapProof0002 state (by omega) (by omega) generator coordinate
          else
            if hAt320 : state.val < 320 then
              if hAt256 : state.val < 256 then
                exact transitionMapProof0003 state (by omega) (by omega) generator coordinate
              else
                exact transitionMapProof0004 state (by omega) (by omega) generator coordinate
            else
              if hAt384 : state.val < 384 then
                exact transitionMapProof0005 state (by omega) (by omega) generator coordinate
              else
                exact transitionMapProof0006 state (by omega) (by omega) generator coordinate
        else
          if hAt704 : state.val < 704 then
            if hAt576 : state.val < 576 then
              if hAt512 : state.val < 512 then
                exact transitionMapProof0007 state (by omega) (by omega) generator coordinate
              else
                exact transitionMapProof0008 state (by omega) (by omega) generator coordinate
            else
              if hAt640 : state.val < 640 then
                exact transitionMapProof0009 state (by omega) (by omega) generator coordinate
              else
                exact transitionMapProof0010 state (by omega) (by omega) generator coordinate
          else
            if hAt832 : state.val < 832 then
              if hAt768 : state.val < 768 then
                exact transitionMapProof0011 state (by omega) (by omega) generator coordinate
              else
                exact transitionMapProof0012 state (by omega) (by omega) generator coordinate
            else
              if hAt896 : state.val < 896 then
                exact transitionMapProof0013 state (by omega) (by omega) generator coordinate
              else
                exact transitionMapProof0014 state (by omega) (by omega) generator coordinate
      else
        if hAt1408 : state.val < 1408 then
          if hAt1152 : state.val < 1152 then
            if hAt1024 : state.val < 1024 then
              exact transitionMapProof0015 state (by omega) (by omega) generator coordinate
            else
              if hAt1088 : state.val < 1088 then
                exact transitionMapProof0016 state (by omega) (by omega) generator coordinate
              else
                exact transitionMapProof0017 state (by omega) (by omega) generator coordinate
          else
            if hAt1280 : state.val < 1280 then
              if hAt1216 : state.val < 1216 then
                exact transitionMapProof0018 state (by omega) (by omega) generator coordinate
              else
                exact transitionMapProof0019 state (by omega) (by omega) generator coordinate
            else
              if hAt1344 : state.val < 1344 then
                exact transitionMapProof0020 state (by omega) (by omega) generator coordinate
              else
                exact transitionMapProof0021 state (by omega) (by omega) generator coordinate
        else
          if hAt1664 : state.val < 1664 then
            if hAt1536 : state.val < 1536 then
              if hAt1472 : state.val < 1472 then
                exact transitionMapProof0022 state (by omega) (by omega) generator coordinate
              else
                exact transitionMapProof0023 state (by omega) (by omega) generator coordinate
            else
              if hAt1600 : state.val < 1600 then
                exact transitionMapProof0024 state (by omega) (by omega) generator coordinate
              else
                exact transitionMapProof0025 state (by omega) (by omega) generator coordinate
          else
            if hAt1792 : state.val < 1792 then
              if hAt1728 : state.val < 1728 then
                exact transitionMapProof0026 state (by omega) (by omega) generator coordinate
              else
                exact transitionMapProof0027 state (by omega) (by omega) generator coordinate
            else
              if hAt1856 : state.val < 1856 then
                exact transitionMapProof0028 state (by omega) (by omega) generator coordinate
              else
                exact transitionMapProof0029 state (by omega) (by omega) generator coordinate
    else
      if hAt2880 : state.val < 2880 then
        if hAt2368 : state.val < 2368 then
          if hAt2112 : state.val < 2112 then
            if hAt1984 : state.val < 1984 then
              exact transitionMapProof0030 state (by omega) (by omega) generator coordinate
            else
              if hAt2048 : state.val < 2048 then
                exact transitionMapProof0031 state (by omega) (by omega) generator coordinate
              else
                exact transitionMapProof0032 state (by omega) (by omega) generator coordinate
          else
            if hAt2240 : state.val < 2240 then
              if hAt2176 : state.val < 2176 then
                exact transitionMapProof0033 state (by omega) (by omega) generator coordinate
              else
                exact transitionMapProof0034 state (by omega) (by omega) generator coordinate
            else
              if hAt2304 : state.val < 2304 then
                exact transitionMapProof0035 state (by omega) (by omega) generator coordinate
              else
                exact transitionMapProof0036 state (by omega) (by omega) generator coordinate
        else
          if hAt2624 : state.val < 2624 then
            if hAt2496 : state.val < 2496 then
              if hAt2432 : state.val < 2432 then
                exact transitionMapProof0037 state (by omega) (by omega) generator coordinate
              else
                exact transitionMapProof0038 state (by omega) (by omega) generator coordinate
            else
              if hAt2560 : state.val < 2560 then
                exact transitionMapProof0039 state (by omega) (by omega) generator coordinate
              else
                exact transitionMapProof0040 state (by omega) (by omega) generator coordinate
          else
            if hAt2752 : state.val < 2752 then
              if hAt2688 : state.val < 2688 then
                exact transitionMapProof0041 state (by omega) (by omega) generator coordinate
              else
                exact transitionMapProof0042 state (by omega) (by omega) generator coordinate
            else
              if hAt2816 : state.val < 2816 then
                exact transitionMapProof0043 state (by omega) (by omega) generator coordinate
              else
                exact transitionMapProof0044 state (by omega) (by omega) generator coordinate
      else
        if hAt3392 : state.val < 3392 then
          if hAt3136 : state.val < 3136 then
            if hAt3008 : state.val < 3008 then
              if hAt2944 : state.val < 2944 then
                exact transitionMapProof0045 state (by omega) (by omega) generator coordinate
              else
                exact transitionMapProof0046 state (by omega) (by omega) generator coordinate
            else
              if hAt3072 : state.val < 3072 then
                exact transitionMapProof0047 state (by omega) (by omega) generator coordinate
              else
                exact transitionMapProof0048 state (by omega) (by omega) generator coordinate
          else
            if hAt3264 : state.val < 3264 then
              if hAt3200 : state.val < 3200 then
                exact transitionMapProof0049 state (by omega) (by omega) generator coordinate
              else
                exact transitionMapProof0050 state (by omega) (by omega) generator coordinate
            else
              if hAt3328 : state.val < 3328 then
                exact transitionMapProof0051 state (by omega) (by omega) generator coordinate
              else
                exact transitionMapProof0052 state (by omega) (by omega) generator coordinate
        else
          if hAt3648 : state.val < 3648 then
            if hAt3520 : state.val < 3520 then
              if hAt3456 : state.val < 3456 then
                exact transitionMapProof0053 state (by omega) (by omega) generator coordinate
              else
                exact transitionMapProof0054 state (by omega) (by omega) generator coordinate
            else
              if hAt3584 : state.val < 3584 then
                exact transitionMapProof0055 state (by omega) (by omega) generator coordinate
              else
                exact transitionMapProof0056 state (by omega) (by omega) generator coordinate
          else
            if hAt3776 : state.val < 3776 then
              if hAt3712 : state.val < 3712 then
                exact transitionMapProof0057 state (by omega) (by omega) generator coordinate
              else
                exact transitionMapProof0058 state (by omega) (by omega) generator coordinate
            else
              if hAt3840 : state.val < 3840 then
                exact transitionMapProof0059 state (by omega) (by omega) generator coordinate
              else
                exact transitionMapProof0060 state (by omega) (by omega) generator coordinate
  else
    if hAt5824 : state.val < 5824 then
      if hAt4864 : state.val < 4864 then
        if hAt4352 : state.val < 4352 then
          if hAt4096 : state.val < 4096 then
            if hAt3968 : state.val < 3968 then
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
                exact transitionMapProof0067 state (by omega) (by omega) generator coordinate
        else
          if hAt4608 : state.val < 4608 then
            if hAt4480 : state.val < 4480 then
              if hAt4416 : state.val < 4416 then
                exact transitionMapProof0068 state (by omega) (by omega) generator coordinate
              else
                exact transitionMapProof0069 state (by omega) (by omega) generator coordinate
            else
              if hAt4544 : state.val < 4544 then
                exact transitionMapProof0070 state (by omega) (by omega) generator coordinate
              else
                exact transitionMapProof0071 state (by omega) (by omega) generator coordinate
          else
            if hAt4736 : state.val < 4736 then
              if hAt4672 : state.val < 4672 then
                exact transitionMapProof0072 state (by omega) (by omega) generator coordinate
              else
                exact transitionMapProof0073 state (by omega) (by omega) generator coordinate
            else
              if hAt4800 : state.val < 4800 then
                exact transitionMapProof0074 state (by omega) (by omega) generator coordinate
              else
                exact transitionMapProof0075 state (by omega) (by omega) generator coordinate
      else
        if hAt5312 : state.val < 5312 then
          if hAt5056 : state.val < 5056 then
            if hAt4928 : state.val < 4928 then
              exact transitionMapProof0076 state (by omega) (by omega) generator coordinate
            else
              if hAt4992 : state.val < 4992 then
                exact transitionMapProof0077 state (by omega) (by omega) generator coordinate
              else
                exact transitionMapProof0078 state (by omega) (by omega) generator coordinate
          else
            if hAt5184 : state.val < 5184 then
              if hAt5120 : state.val < 5120 then
                exact transitionMapProof0079 state (by omega) (by omega) generator coordinate
              else
                exact transitionMapProof0080 state (by omega) (by omega) generator coordinate
            else
              if hAt5248 : state.val < 5248 then
                exact transitionMapProof0081 state (by omega) (by omega) generator coordinate
              else
                exact transitionMapProof0082 state (by omega) (by omega) generator coordinate
        else
          if hAt5568 : state.val < 5568 then
            if hAt5440 : state.val < 5440 then
              if hAt5376 : state.val < 5376 then
                exact transitionMapProof0083 state (by omega) (by omega) generator coordinate
              else
                exact transitionMapProof0084 state (by omega) (by omega) generator coordinate
            else
              if hAt5504 : state.val < 5504 then
                exact transitionMapProof0085 state (by omega) (by omega) generator coordinate
              else
                exact transitionMapProof0086 state (by omega) (by omega) generator coordinate
          else
            if hAt5696 : state.val < 5696 then
              if hAt5632 : state.val < 5632 then
                exact transitionMapProof0087 state (by omega) (by omega) generator coordinate
              else
                exact transitionMapProof0088 state (by omega) (by omega) generator coordinate
            else
              if hAt5760 : state.val < 5760 then
                exact transitionMapProof0089 state (by omega) (by omega) generator coordinate
              else
                exact transitionMapProof0090 state (by omega) (by omega) generator coordinate
    else
      if hAt6784 : state.val < 6784 then
        if hAt6272 : state.val < 6272 then
          if hAt6016 : state.val < 6016 then
            if hAt5888 : state.val < 5888 then
              exact transitionMapProof0091 state (by omega) (by omega) generator coordinate
            else
              if hAt5952 : state.val < 5952 then
                exact transitionMapProof0092 state (by omega) (by omega) generator coordinate
              else
                exact transitionMapProof0093 state (by omega) (by omega) generator coordinate
          else
            if hAt6144 : state.val < 6144 then
              if hAt6080 : state.val < 6080 then
                exact transitionMapProof0094 state (by omega) (by omega) generator coordinate
              else
                exact transitionMapProof0095 state (by omega) (by omega) generator coordinate
            else
              if hAt6208 : state.val < 6208 then
                exact transitionMapProof0096 state (by omega) (by omega) generator coordinate
              else
                exact transitionMapProof0097 state (by omega) (by omega) generator coordinate
        else
          if hAt6528 : state.val < 6528 then
            if hAt6400 : state.val < 6400 then
              if hAt6336 : state.val < 6336 then
                exact transitionMapProof0098 state (by omega) (by omega) generator coordinate
              else
                exact transitionMapProof0099 state (by omega) (by omega) generator coordinate
            else
              if hAt6464 : state.val < 6464 then
                exact transitionMapProof0100 state (by omega) (by omega) generator coordinate
              else
                exact transitionMapProof0101 state (by omega) (by omega) generator coordinate
          else
            if hAt6656 : state.val < 6656 then
              if hAt6592 : state.val < 6592 then
                exact transitionMapProof0102 state (by omega) (by omega) generator coordinate
              else
                exact transitionMapProof0103 state (by omega) (by omega) generator coordinate
            else
              if hAt6720 : state.val < 6720 then
                exact transitionMapProof0104 state (by omega) (by omega) generator coordinate
              else
                exact transitionMapProof0105 state (by omega) (by omega) generator coordinate
      else
        if hAt7296 : state.val < 7296 then
          if hAt7040 : state.val < 7040 then
            if hAt6912 : state.val < 6912 then
              if hAt6848 : state.val < 6848 then
                exact transitionMapProof0106 state (by omega) (by omega) generator coordinate
              else
                exact transitionMapProof0107 state (by omega) (by omega) generator coordinate
            else
              if hAt6976 : state.val < 6976 then
                exact transitionMapProof0108 state (by omega) (by omega) generator coordinate
              else
                exact transitionMapProof0109 state (by omega) (by omega) generator coordinate
          else
            if hAt7168 : state.val < 7168 then
              if hAt7104 : state.val < 7104 then
                exact transitionMapProof0110 state (by omega) (by omega) generator coordinate
              else
                exact transitionMapProof0111 state (by omega) (by omega) generator coordinate
            else
              if hAt7232 : state.val < 7232 then
                exact transitionMapProof0112 state (by omega) (by omega) generator coordinate
              else
                exact transitionMapProof0113 state (by omega) (by omega) generator coordinate
        else
          if hAt7552 : state.val < 7552 then
            if hAt7424 : state.val < 7424 then
              if hAt7360 : state.val < 7360 then
                exact transitionMapProof0114 state (by omega) (by omega) generator coordinate
              else
                exact transitionMapProof0115 state (by omega) (by omega) generator coordinate
            else
              if hAt7488 : state.val < 7488 then
                exact transitionMapProof0116 state (by omega) (by omega) generator coordinate
              else
                exact transitionMapProof0117 state (by omega) (by omega) generator coordinate
          else
            if hAt7680 : state.val < 7680 then
              if hAt7616 : state.val < 7616 then
                exact transitionMapProof0118 state (by omega) (by omega) generator coordinate
              else
                exact transitionMapProof0119 state (by omega) (by omega) generator coordinate
            else
              if hAt7744 : state.val < 7744 then
                exact transitionMapProof0120 state (by omega) (by omega) generator coordinate
              else
                exact transitionMapProof0121 state (by omega) (by omega) generator coordinate

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.Shards
