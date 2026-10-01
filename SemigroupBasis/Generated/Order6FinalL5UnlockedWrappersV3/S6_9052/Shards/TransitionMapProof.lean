import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9052.Shards.TransitionMapProofPart00
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9052.Shards.TransitionMapProofPart01
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9052.Shards.TransitionMapProofPart02
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9052.Shards.TransitionMapProofPart03
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9052.Shards.TransitionMapProofPart04
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9052.Shards.TransitionMapProofPart05
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9052.Shards.TransitionMapProofPart06
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9052.Shards.TransitionMapProofPart07
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9052.Shards.TransitionMapProofPart08
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9052.Support.Core
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9052.Shards

set_option maxHeartbeats 2000000 in
theorem transitionMap
    (state : Fin 18432)
    (generator : Fin 6)
    (coordinate : Fin 22) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9052.stateVector
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9052.transition state generator) coordinate =
      SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9052.oppositeTable.semigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9052.stateVector state coordinate)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9052.generatorVector generator coordinate) := by
  if hAt9216 : state.val < 9216 then
    if hAt4608 : state.val < 4608 then
      if hAt2304 : state.val < 2304 then
        if hAt1152 : state.val < 1152 then
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
            if hAt832 : state.val < 832 then
              if hAt704 : state.val < 704 then
                if hAt640 : state.val < 640 then
                  exact transitionMapProof0009 state (by omega) (by omega) generator coordinate
                else
                  exact transitionMapProof0010 state (by omega) (by omega) generator coordinate
              else
                if hAt768 : state.val < 768 then
                  exact transitionMapProof0011 state (by omega) (by omega) generator coordinate
                else
                  exact transitionMapProof0012 state (by omega) (by omega) generator coordinate
            else
              if hAt960 : state.val < 960 then
                if hAt896 : state.val < 896 then
                  exact transitionMapProof0013 state (by omega) (by omega) generator coordinate
                else
                  exact transitionMapProof0014 state (by omega) (by omega) generator coordinate
              else
                if hAt1024 : state.val < 1024 then
                  exact transitionMapProof0015 state (by omega) (by omega) generator coordinate
                else
                  if hAt1088 : state.val < 1088 then
                    exact transitionMapProof0016 state (by omega) (by omega) generator coordinate
                  else
                    exact transitionMapProof0017 state (by omega) (by omega) generator coordinate
        else
          if hAt1728 : state.val < 1728 then
            if hAt1408 : state.val < 1408 then
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
              if hAt1536 : state.val < 1536 then
                if hAt1472 : state.val < 1472 then
                  exact transitionMapProof0022 state (by omega) (by omega) generator coordinate
                else
                  exact transitionMapProof0023 state (by omega) (by omega) generator coordinate
              else
                if hAt1600 : state.val < 1600 then
                  exact transitionMapProof0024 state (by omega) (by omega) generator coordinate
                else
                  if hAt1664 : state.val < 1664 then
                    exact transitionMapProof0025 state (by omega) (by omega) generator coordinate
                  else
                    exact transitionMapProof0026 state (by omega) (by omega) generator coordinate
          else
            if hAt1984 : state.val < 1984 then
              if hAt1856 : state.val < 1856 then
                if hAt1792 : state.val < 1792 then
                  exact transitionMapProof0027 state (by omega) (by omega) generator coordinate
                else
                  exact transitionMapProof0028 state (by omega) (by omega) generator coordinate
              else
                if hAt1920 : state.val < 1920 then
                  exact transitionMapProof0029 state (by omega) (by omega) generator coordinate
                else
                  exact transitionMapProof0030 state (by omega) (by omega) generator coordinate
            else
              if hAt2112 : state.val < 2112 then
                if hAt2048 : state.val < 2048 then
                  exact transitionMapProof0031 state (by omega) (by omega) generator coordinate
                else
                  exact transitionMapProof0032 state (by omega) (by omega) generator coordinate
              else
                if hAt2176 : state.val < 2176 then
                  exact transitionMapProof0033 state (by omega) (by omega) generator coordinate
                else
                  if hAt2240 : state.val < 2240 then
                    exact transitionMapProof0034 state (by omega) (by omega) generator coordinate
                  else
                    exact transitionMapProof0035 state (by omega) (by omega) generator coordinate
      else
        if hAt3456 : state.val < 3456 then
          if hAt2880 : state.val < 2880 then
            if hAt2560 : state.val < 2560 then
              if hAt2432 : state.val < 2432 then
                if hAt2368 : state.val < 2368 then
                  exact transitionMapProof0036 state (by omega) (by omega) generator coordinate
                else
                  exact transitionMapProof0037 state (by omega) (by omega) generator coordinate
              else
                if hAt2496 : state.val < 2496 then
                  exact transitionMapProof0038 state (by omega) (by omega) generator coordinate
                else
                  exact transitionMapProof0039 state (by omega) (by omega) generator coordinate
            else
              if hAt2688 : state.val < 2688 then
                if hAt2624 : state.val < 2624 then
                  exact transitionMapProof0040 state (by omega) (by omega) generator coordinate
                else
                  exact transitionMapProof0041 state (by omega) (by omega) generator coordinate
              else
                if hAt2752 : state.val < 2752 then
                  exact transitionMapProof0042 state (by omega) (by omega) generator coordinate
                else
                  if hAt2816 : state.val < 2816 then
                    exact transitionMapProof0043 state (by omega) (by omega) generator coordinate
                  else
                    exact transitionMapProof0044 state (by omega) (by omega) generator coordinate
          else
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
                  if hAt3392 : state.val < 3392 then
                    exact transitionMapProof0052 state (by omega) (by omega) generator coordinate
                  else
                    exact transitionMapProof0053 state (by omega) (by omega) generator coordinate
        else
          if hAt4032 : state.val < 4032 then
            if hAt3712 : state.val < 3712 then
              if hAt3584 : state.val < 3584 then
                if hAt3520 : state.val < 3520 then
                  exact transitionMapProof0054 state (by omega) (by omega) generator coordinate
                else
                  exact transitionMapProof0055 state (by omega) (by omega) generator coordinate
              else
                if hAt3648 : state.val < 3648 then
                  exact transitionMapProof0056 state (by omega) (by omega) generator coordinate
                else
                  exact transitionMapProof0057 state (by omega) (by omega) generator coordinate
            else
              if hAt3840 : state.val < 3840 then
                if hAt3776 : state.val < 3776 then
                  exact transitionMapProof0058 state (by omega) (by omega) generator coordinate
                else
                  exact transitionMapProof0059 state (by omega) (by omega) generator coordinate
              else
                if hAt3904 : state.val < 3904 then
                  exact transitionMapProof0060 state (by omega) (by omega) generator coordinate
                else
                  if hAt3968 : state.val < 3968 then
                    exact transitionMapProof0061 state (by omega) (by omega) generator coordinate
                  else
                    exact transitionMapProof0062 state (by omega) (by omega) generator coordinate
          else
            if hAt4288 : state.val < 4288 then
              if hAt4160 : state.val < 4160 then
                if hAt4096 : state.val < 4096 then
                  exact transitionMapProof0063 state (by omega) (by omega) generator coordinate
                else
                  exact transitionMapProof0064 state (by omega) (by omega) generator coordinate
              else
                if hAt4224 : state.val < 4224 then
                  exact transitionMapProof0065 state (by omega) (by omega) generator coordinate
                else
                  exact transitionMapProof0066 state (by omega) (by omega) generator coordinate
            else
              if hAt4416 : state.val < 4416 then
                if hAt4352 : state.val < 4352 then
                  exact transitionMapProof0067 state (by omega) (by omega) generator coordinate
                else
                  exact transitionMapProof0068 state (by omega) (by omega) generator coordinate
              else
                if hAt4480 : state.val < 4480 then
                  exact transitionMapProof0069 state (by omega) (by omega) generator coordinate
                else
                  if hAt4544 : state.val < 4544 then
                    exact transitionMapProof0070 state (by omega) (by omega) generator coordinate
                  else
                    exact transitionMapProof0071 state (by omega) (by omega) generator coordinate
    else
      if hAt6912 : state.val < 6912 then
        if hAt5760 : state.val < 5760 then
          if hAt5184 : state.val < 5184 then
            if hAt4864 : state.val < 4864 then
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
              if hAt4992 : state.val < 4992 then
                if hAt4928 : state.val < 4928 then
                  exact transitionMapProof0076 state (by omega) (by omega) generator coordinate
                else
                  exact transitionMapProof0077 state (by omega) (by omega) generator coordinate
              else
                if hAt5056 : state.val < 5056 then
                  exact transitionMapProof0078 state (by omega) (by omega) generator coordinate
                else
                  if hAt5120 : state.val < 5120 then
                    exact transitionMapProof0079 state (by omega) (by omega) generator coordinate
                  else
                    exact transitionMapProof0080 state (by omega) (by omega) generator coordinate
          else
            if hAt5440 : state.val < 5440 then
              if hAt5312 : state.val < 5312 then
                if hAt5248 : state.val < 5248 then
                  exact transitionMapProof0081 state (by omega) (by omega) generator coordinate
                else
                  exact transitionMapProof0082 state (by omega) (by omega) generator coordinate
              else
                if hAt5376 : state.val < 5376 then
                  exact transitionMapProof0083 state (by omega) (by omega) generator coordinate
                else
                  exact transitionMapProof0084 state (by omega) (by omega) generator coordinate
            else
              if hAt5568 : state.val < 5568 then
                if hAt5504 : state.val < 5504 then
                  exact transitionMapProof0085 state (by omega) (by omega) generator coordinate
                else
                  exact transitionMapProof0086 state (by omega) (by omega) generator coordinate
              else
                if hAt5632 : state.val < 5632 then
                  exact transitionMapProof0087 state (by omega) (by omega) generator coordinate
                else
                  if hAt5696 : state.val < 5696 then
                    exact transitionMapProof0088 state (by omega) (by omega) generator coordinate
                  else
                    exact transitionMapProof0089 state (by omega) (by omega) generator coordinate
        else
          if hAt6336 : state.val < 6336 then
            if hAt6016 : state.val < 6016 then
              if hAt5888 : state.val < 5888 then
                if hAt5824 : state.val < 5824 then
                  exact transitionMapProof0090 state (by omega) (by omega) generator coordinate
                else
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
                  if hAt6272 : state.val < 6272 then
                    exact transitionMapProof0097 state (by omega) (by omega) generator coordinate
                  else
                    exact transitionMapProof0098 state (by omega) (by omega) generator coordinate
          else
            if hAt6592 : state.val < 6592 then
              if hAt6464 : state.val < 6464 then
                if hAt6400 : state.val < 6400 then
                  exact transitionMapProof0099 state (by omega) (by omega) generator coordinate
                else
                  exact transitionMapProof0100 state (by omega) (by omega) generator coordinate
              else
                if hAt6528 : state.val < 6528 then
                  exact transitionMapProof0101 state (by omega) (by omega) generator coordinate
                else
                  exact transitionMapProof0102 state (by omega) (by omega) generator coordinate
            else
              if hAt6720 : state.val < 6720 then
                if hAt6656 : state.val < 6656 then
                  exact transitionMapProof0103 state (by omega) (by omega) generator coordinate
                else
                  exact transitionMapProof0104 state (by omega) (by omega) generator coordinate
              else
                if hAt6784 : state.val < 6784 then
                  exact transitionMapProof0105 state (by omega) (by omega) generator coordinate
                else
                  if hAt6848 : state.val < 6848 then
                    exact transitionMapProof0106 state (by omega) (by omega) generator coordinate
                  else
                    exact transitionMapProof0107 state (by omega) (by omega) generator coordinate
      else
        if hAt8064 : state.val < 8064 then
          if hAt7488 : state.val < 7488 then
            if hAt7168 : state.val < 7168 then
              if hAt7040 : state.val < 7040 then
                if hAt6976 : state.val < 6976 then
                  exact transitionMapProof0108 state (by omega) (by omega) generator coordinate
                else
                  exact transitionMapProof0109 state (by omega) (by omega) generator coordinate
              else
                if hAt7104 : state.val < 7104 then
                  exact transitionMapProof0110 state (by omega) (by omega) generator coordinate
                else
                  exact transitionMapProof0111 state (by omega) (by omega) generator coordinate
            else
              if hAt7296 : state.val < 7296 then
                if hAt7232 : state.val < 7232 then
                  exact transitionMapProof0112 state (by omega) (by omega) generator coordinate
                else
                  exact transitionMapProof0113 state (by omega) (by omega) generator coordinate
              else
                if hAt7360 : state.val < 7360 then
                  exact transitionMapProof0114 state (by omega) (by omega) generator coordinate
                else
                  if hAt7424 : state.val < 7424 then
                    exact transitionMapProof0115 state (by omega) (by omega) generator coordinate
                  else
                    exact transitionMapProof0116 state (by omega) (by omega) generator coordinate
          else
            if hAt7744 : state.val < 7744 then
              if hAt7616 : state.val < 7616 then
                if hAt7552 : state.val < 7552 then
                  exact transitionMapProof0117 state (by omega) (by omega) generator coordinate
                else
                  exact transitionMapProof0118 state (by omega) (by omega) generator coordinate
              else
                if hAt7680 : state.val < 7680 then
                  exact transitionMapProof0119 state (by omega) (by omega) generator coordinate
                else
                  exact transitionMapProof0120 state (by omega) (by omega) generator coordinate
            else
              if hAt7872 : state.val < 7872 then
                if hAt7808 : state.val < 7808 then
                  exact transitionMapProof0121 state (by omega) (by omega) generator coordinate
                else
                  exact transitionMapProof0122 state (by omega) (by omega) generator coordinate
              else
                if hAt7936 : state.val < 7936 then
                  exact transitionMapProof0123 state (by omega) (by omega) generator coordinate
                else
                  if hAt8000 : state.val < 8000 then
                    exact transitionMapProof0124 state (by omega) (by omega) generator coordinate
                  else
                    exact transitionMapProof0125 state (by omega) (by omega) generator coordinate
        else
          if hAt8640 : state.val < 8640 then
            if hAt8320 : state.val < 8320 then
              if hAt8192 : state.val < 8192 then
                if hAt8128 : state.val < 8128 then
                  exact transitionMapProof0126 state (by omega) (by omega) generator coordinate
                else
                  exact transitionMapProof0127 state (by omega) (by omega) generator coordinate
              else
                if hAt8256 : state.val < 8256 then
                  exact transitionMapProof0128 state (by omega) (by omega) generator coordinate
                else
                  exact transitionMapProof0129 state (by omega) (by omega) generator coordinate
            else
              if hAt8448 : state.val < 8448 then
                if hAt8384 : state.val < 8384 then
                  exact transitionMapProof0130 state (by omega) (by omega) generator coordinate
                else
                  exact transitionMapProof0131 state (by omega) (by omega) generator coordinate
              else
                if hAt8512 : state.val < 8512 then
                  exact transitionMapProof0132 state (by omega) (by omega) generator coordinate
                else
                  if hAt8576 : state.val < 8576 then
                    exact transitionMapProof0133 state (by omega) (by omega) generator coordinate
                  else
                    exact transitionMapProof0134 state (by omega) (by omega) generator coordinate
          else
            if hAt8896 : state.val < 8896 then
              if hAt8768 : state.val < 8768 then
                if hAt8704 : state.val < 8704 then
                  exact transitionMapProof0135 state (by omega) (by omega) generator coordinate
                else
                  exact transitionMapProof0136 state (by omega) (by omega) generator coordinate
              else
                if hAt8832 : state.val < 8832 then
                  exact transitionMapProof0137 state (by omega) (by omega) generator coordinate
                else
                  exact transitionMapProof0138 state (by omega) (by omega) generator coordinate
            else
              if hAt9024 : state.val < 9024 then
                if hAt8960 : state.val < 8960 then
                  exact transitionMapProof0139 state (by omega) (by omega) generator coordinate
                else
                  exact transitionMapProof0140 state (by omega) (by omega) generator coordinate
              else
                if hAt9088 : state.val < 9088 then
                  exact transitionMapProof0141 state (by omega) (by omega) generator coordinate
                else
                  if hAt9152 : state.val < 9152 then
                    exact transitionMapProof0142 state (by omega) (by omega) generator coordinate
                  else
                    exact transitionMapProof0143 state (by omega) (by omega) generator coordinate
  else
    if hAt13824 : state.val < 13824 then
      if hAt11520 : state.val < 11520 then
        if hAt10368 : state.val < 10368 then
          if hAt9792 : state.val < 9792 then
            if hAt9472 : state.val < 9472 then
              if hAt9344 : state.val < 9344 then
                if hAt9280 : state.val < 9280 then
                  exact transitionMapProof0144 state (by omega) (by omega) generator coordinate
                else
                  exact transitionMapProof0145 state (by omega) (by omega) generator coordinate
              else
                if hAt9408 : state.val < 9408 then
                  exact transitionMapProof0146 state (by omega) (by omega) generator coordinate
                else
                  exact transitionMapProof0147 state (by omega) (by omega) generator coordinate
            else
              if hAt9600 : state.val < 9600 then
                if hAt9536 : state.val < 9536 then
                  exact transitionMapProof0148 state (by omega) (by omega) generator coordinate
                else
                  exact transitionMapProof0149 state (by omega) (by omega) generator coordinate
              else
                if hAt9664 : state.val < 9664 then
                  exact transitionMapProof0150 state (by omega) (by omega) generator coordinate
                else
                  if hAt9728 : state.val < 9728 then
                    exact transitionMapProof0151 state (by omega) (by omega) generator coordinate
                  else
                    exact transitionMapProof0152 state (by omega) (by omega) generator coordinate
          else
            if hAt10048 : state.val < 10048 then
              if hAt9920 : state.val < 9920 then
                if hAt9856 : state.val < 9856 then
                  exact transitionMapProof0153 state (by omega) (by omega) generator coordinate
                else
                  exact transitionMapProof0154 state (by omega) (by omega) generator coordinate
              else
                if hAt9984 : state.val < 9984 then
                  exact transitionMapProof0155 state (by omega) (by omega) generator coordinate
                else
                  exact transitionMapProof0156 state (by omega) (by omega) generator coordinate
            else
              if hAt10176 : state.val < 10176 then
                if hAt10112 : state.val < 10112 then
                  exact transitionMapProof0157 state (by omega) (by omega) generator coordinate
                else
                  exact transitionMapProof0158 state (by omega) (by omega) generator coordinate
              else
                if hAt10240 : state.val < 10240 then
                  exact transitionMapProof0159 state (by omega) (by omega) generator coordinate
                else
                  if hAt10304 : state.val < 10304 then
                    exact transitionMapProof0160 state (by omega) (by omega) generator coordinate
                  else
                    exact transitionMapProof0161 state (by omega) (by omega) generator coordinate
        else
          if hAt10944 : state.val < 10944 then
            if hAt10624 : state.val < 10624 then
              if hAt10496 : state.val < 10496 then
                if hAt10432 : state.val < 10432 then
                  exact transitionMapProof0162 state (by omega) (by omega) generator coordinate
                else
                  exact transitionMapProof0163 state (by omega) (by omega) generator coordinate
              else
                if hAt10560 : state.val < 10560 then
                  exact transitionMapProof0164 state (by omega) (by omega) generator coordinate
                else
                  exact transitionMapProof0165 state (by omega) (by omega) generator coordinate
            else
              if hAt10752 : state.val < 10752 then
                if hAt10688 : state.val < 10688 then
                  exact transitionMapProof0166 state (by omega) (by omega) generator coordinate
                else
                  exact transitionMapProof0167 state (by omega) (by omega) generator coordinate
              else
                if hAt10816 : state.val < 10816 then
                  exact transitionMapProof0168 state (by omega) (by omega) generator coordinate
                else
                  if hAt10880 : state.val < 10880 then
                    exact transitionMapProof0169 state (by omega) (by omega) generator coordinate
                  else
                    exact transitionMapProof0170 state (by omega) (by omega) generator coordinate
          else
            if hAt11200 : state.val < 11200 then
              if hAt11072 : state.val < 11072 then
                if hAt11008 : state.val < 11008 then
                  exact transitionMapProof0171 state (by omega) (by omega) generator coordinate
                else
                  exact transitionMapProof0172 state (by omega) (by omega) generator coordinate
              else
                if hAt11136 : state.val < 11136 then
                  exact transitionMapProof0173 state (by omega) (by omega) generator coordinate
                else
                  exact transitionMapProof0174 state (by omega) (by omega) generator coordinate
            else
              if hAt11328 : state.val < 11328 then
                if hAt11264 : state.val < 11264 then
                  exact transitionMapProof0175 state (by omega) (by omega) generator coordinate
                else
                  exact transitionMapProof0176 state (by omega) (by omega) generator coordinate
              else
                if hAt11392 : state.val < 11392 then
                  exact transitionMapProof0177 state (by omega) (by omega) generator coordinate
                else
                  if hAt11456 : state.val < 11456 then
                    exact transitionMapProof0178 state (by omega) (by omega) generator coordinate
                  else
                    exact transitionMapProof0179 state (by omega) (by omega) generator coordinate
      else
        if hAt12672 : state.val < 12672 then
          if hAt12096 : state.val < 12096 then
            if hAt11776 : state.val < 11776 then
              if hAt11648 : state.val < 11648 then
                if hAt11584 : state.val < 11584 then
                  exact transitionMapProof0180 state (by omega) (by omega) generator coordinate
                else
                  exact transitionMapProof0181 state (by omega) (by omega) generator coordinate
              else
                if hAt11712 : state.val < 11712 then
                  exact transitionMapProof0182 state (by omega) (by omega) generator coordinate
                else
                  exact transitionMapProof0183 state (by omega) (by omega) generator coordinate
            else
              if hAt11904 : state.val < 11904 then
                if hAt11840 : state.val < 11840 then
                  exact transitionMapProof0184 state (by omega) (by omega) generator coordinate
                else
                  exact transitionMapProof0185 state (by omega) (by omega) generator coordinate
              else
                if hAt11968 : state.val < 11968 then
                  exact transitionMapProof0186 state (by omega) (by omega) generator coordinate
                else
                  if hAt12032 : state.val < 12032 then
                    exact transitionMapProof0187 state (by omega) (by omega) generator coordinate
                  else
                    exact transitionMapProof0188 state (by omega) (by omega) generator coordinate
          else
            if hAt12352 : state.val < 12352 then
              if hAt12224 : state.val < 12224 then
                if hAt12160 : state.val < 12160 then
                  exact transitionMapProof0189 state (by omega) (by omega) generator coordinate
                else
                  exact transitionMapProof0190 state (by omega) (by omega) generator coordinate
              else
                if hAt12288 : state.val < 12288 then
                  exact transitionMapProof0191 state (by omega) (by omega) generator coordinate
                else
                  exact transitionMapProof0192 state (by omega) (by omega) generator coordinate
            else
              if hAt12480 : state.val < 12480 then
                if hAt12416 : state.val < 12416 then
                  exact transitionMapProof0193 state (by omega) (by omega) generator coordinate
                else
                  exact transitionMapProof0194 state (by omega) (by omega) generator coordinate
              else
                if hAt12544 : state.val < 12544 then
                  exact transitionMapProof0195 state (by omega) (by omega) generator coordinate
                else
                  if hAt12608 : state.val < 12608 then
                    exact transitionMapProof0196 state (by omega) (by omega) generator coordinate
                  else
                    exact transitionMapProof0197 state (by omega) (by omega) generator coordinate
        else
          if hAt13248 : state.val < 13248 then
            if hAt12928 : state.val < 12928 then
              if hAt12800 : state.val < 12800 then
                if hAt12736 : state.val < 12736 then
                  exact transitionMapProof0198 state (by omega) (by omega) generator coordinate
                else
                  exact transitionMapProof0199 state (by omega) (by omega) generator coordinate
              else
                if hAt12864 : state.val < 12864 then
                  exact transitionMapProof0200 state (by omega) (by omega) generator coordinate
                else
                  exact transitionMapProof0201 state (by omega) (by omega) generator coordinate
            else
              if hAt13056 : state.val < 13056 then
                if hAt12992 : state.val < 12992 then
                  exact transitionMapProof0202 state (by omega) (by omega) generator coordinate
                else
                  exact transitionMapProof0203 state (by omega) (by omega) generator coordinate
              else
                if hAt13120 : state.val < 13120 then
                  exact transitionMapProof0204 state (by omega) (by omega) generator coordinate
                else
                  if hAt13184 : state.val < 13184 then
                    exact transitionMapProof0205 state (by omega) (by omega) generator coordinate
                  else
                    exact transitionMapProof0206 state (by omega) (by omega) generator coordinate
          else
            if hAt13504 : state.val < 13504 then
              if hAt13376 : state.val < 13376 then
                if hAt13312 : state.val < 13312 then
                  exact transitionMapProof0207 state (by omega) (by omega) generator coordinate
                else
                  exact transitionMapProof0208 state (by omega) (by omega) generator coordinate
              else
                if hAt13440 : state.val < 13440 then
                  exact transitionMapProof0209 state (by omega) (by omega) generator coordinate
                else
                  exact transitionMapProof0210 state (by omega) (by omega) generator coordinate
            else
              if hAt13632 : state.val < 13632 then
                if hAt13568 : state.val < 13568 then
                  exact transitionMapProof0211 state (by omega) (by omega) generator coordinate
                else
                  exact transitionMapProof0212 state (by omega) (by omega) generator coordinate
              else
                if hAt13696 : state.val < 13696 then
                  exact transitionMapProof0213 state (by omega) (by omega) generator coordinate
                else
                  if hAt13760 : state.val < 13760 then
                    exact transitionMapProof0214 state (by omega) (by omega) generator coordinate
                  else
                    exact transitionMapProof0215 state (by omega) (by omega) generator coordinate
    else
      if hAt16128 : state.val < 16128 then
        if hAt14976 : state.val < 14976 then
          if hAt14400 : state.val < 14400 then
            if hAt14080 : state.val < 14080 then
              if hAt13952 : state.val < 13952 then
                if hAt13888 : state.val < 13888 then
                  exact transitionMapProof0216 state (by omega) (by omega) generator coordinate
                else
                  exact transitionMapProof0217 state (by omega) (by omega) generator coordinate
              else
                if hAt14016 : state.val < 14016 then
                  exact transitionMapProof0218 state (by omega) (by omega) generator coordinate
                else
                  exact transitionMapProof0219 state (by omega) (by omega) generator coordinate
            else
              if hAt14208 : state.val < 14208 then
                if hAt14144 : state.val < 14144 then
                  exact transitionMapProof0220 state (by omega) (by omega) generator coordinate
                else
                  exact transitionMapProof0221 state (by omega) (by omega) generator coordinate
              else
                if hAt14272 : state.val < 14272 then
                  exact transitionMapProof0222 state (by omega) (by omega) generator coordinate
                else
                  if hAt14336 : state.val < 14336 then
                    exact transitionMapProof0223 state (by omega) (by omega) generator coordinate
                  else
                    exact transitionMapProof0224 state (by omega) (by omega) generator coordinate
          else
            if hAt14656 : state.val < 14656 then
              if hAt14528 : state.val < 14528 then
                if hAt14464 : state.val < 14464 then
                  exact transitionMapProof0225 state (by omega) (by omega) generator coordinate
                else
                  exact transitionMapProof0226 state (by omega) (by omega) generator coordinate
              else
                if hAt14592 : state.val < 14592 then
                  exact transitionMapProof0227 state (by omega) (by omega) generator coordinate
                else
                  exact transitionMapProof0228 state (by omega) (by omega) generator coordinate
            else
              if hAt14784 : state.val < 14784 then
                if hAt14720 : state.val < 14720 then
                  exact transitionMapProof0229 state (by omega) (by omega) generator coordinate
                else
                  exact transitionMapProof0230 state (by omega) (by omega) generator coordinate
              else
                if hAt14848 : state.val < 14848 then
                  exact transitionMapProof0231 state (by omega) (by omega) generator coordinate
                else
                  if hAt14912 : state.val < 14912 then
                    exact transitionMapProof0232 state (by omega) (by omega) generator coordinate
                  else
                    exact transitionMapProof0233 state (by omega) (by omega) generator coordinate
        else
          if hAt15552 : state.val < 15552 then
            if hAt15232 : state.val < 15232 then
              if hAt15104 : state.val < 15104 then
                if hAt15040 : state.val < 15040 then
                  exact transitionMapProof0234 state (by omega) (by omega) generator coordinate
                else
                  exact transitionMapProof0235 state (by omega) (by omega) generator coordinate
              else
                if hAt15168 : state.val < 15168 then
                  exact transitionMapProof0236 state (by omega) (by omega) generator coordinate
                else
                  exact transitionMapProof0237 state (by omega) (by omega) generator coordinate
            else
              if hAt15360 : state.val < 15360 then
                if hAt15296 : state.val < 15296 then
                  exact transitionMapProof0238 state (by omega) (by omega) generator coordinate
                else
                  exact transitionMapProof0239 state (by omega) (by omega) generator coordinate
              else
                if hAt15424 : state.val < 15424 then
                  exact transitionMapProof0240 state (by omega) (by omega) generator coordinate
                else
                  if hAt15488 : state.val < 15488 then
                    exact transitionMapProof0241 state (by omega) (by omega) generator coordinate
                  else
                    exact transitionMapProof0242 state (by omega) (by omega) generator coordinate
          else
            if hAt15808 : state.val < 15808 then
              if hAt15680 : state.val < 15680 then
                if hAt15616 : state.val < 15616 then
                  exact transitionMapProof0243 state (by omega) (by omega) generator coordinate
                else
                  exact transitionMapProof0244 state (by omega) (by omega) generator coordinate
              else
                if hAt15744 : state.val < 15744 then
                  exact transitionMapProof0245 state (by omega) (by omega) generator coordinate
                else
                  exact transitionMapProof0246 state (by omega) (by omega) generator coordinate
            else
              if hAt15936 : state.val < 15936 then
                if hAt15872 : state.val < 15872 then
                  exact transitionMapProof0247 state (by omega) (by omega) generator coordinate
                else
                  exact transitionMapProof0248 state (by omega) (by omega) generator coordinate
              else
                if hAt16000 : state.val < 16000 then
                  exact transitionMapProof0249 state (by omega) (by omega) generator coordinate
                else
                  if hAt16064 : state.val < 16064 then
                    exact transitionMapProof0250 state (by omega) (by omega) generator coordinate
                  else
                    exact transitionMapProof0251 state (by omega) (by omega) generator coordinate
      else
        if hAt17280 : state.val < 17280 then
          if hAt16704 : state.val < 16704 then
            if hAt16384 : state.val < 16384 then
              if hAt16256 : state.val < 16256 then
                if hAt16192 : state.val < 16192 then
                  exact transitionMapProof0252 state (by omega) (by omega) generator coordinate
                else
                  exact transitionMapProof0253 state (by omega) (by omega) generator coordinate
              else
                if hAt16320 : state.val < 16320 then
                  exact transitionMapProof0254 state (by omega) (by omega) generator coordinate
                else
                  exact transitionMapProof0255 state (by omega) (by omega) generator coordinate
            else
              if hAt16512 : state.val < 16512 then
                if hAt16448 : state.val < 16448 then
                  exact transitionMapProof0256 state (by omega) (by omega) generator coordinate
                else
                  exact transitionMapProof0257 state (by omega) (by omega) generator coordinate
              else
                if hAt16576 : state.val < 16576 then
                  exact transitionMapProof0258 state (by omega) (by omega) generator coordinate
                else
                  if hAt16640 : state.val < 16640 then
                    exact transitionMapProof0259 state (by omega) (by omega) generator coordinate
                  else
                    exact transitionMapProof0260 state (by omega) (by omega) generator coordinate
          else
            if hAt16960 : state.val < 16960 then
              if hAt16832 : state.val < 16832 then
                if hAt16768 : state.val < 16768 then
                  exact transitionMapProof0261 state (by omega) (by omega) generator coordinate
                else
                  exact transitionMapProof0262 state (by omega) (by omega) generator coordinate
              else
                if hAt16896 : state.val < 16896 then
                  exact transitionMapProof0263 state (by omega) (by omega) generator coordinate
                else
                  exact transitionMapProof0264 state (by omega) (by omega) generator coordinate
            else
              if hAt17088 : state.val < 17088 then
                if hAt17024 : state.val < 17024 then
                  exact transitionMapProof0265 state (by omega) (by omega) generator coordinate
                else
                  exact transitionMapProof0266 state (by omega) (by omega) generator coordinate
              else
                if hAt17152 : state.val < 17152 then
                  exact transitionMapProof0267 state (by omega) (by omega) generator coordinate
                else
                  if hAt17216 : state.val < 17216 then
                    exact transitionMapProof0268 state (by omega) (by omega) generator coordinate
                  else
                    exact transitionMapProof0269 state (by omega) (by omega) generator coordinate
        else
          if hAt17856 : state.val < 17856 then
            if hAt17536 : state.val < 17536 then
              if hAt17408 : state.val < 17408 then
                if hAt17344 : state.val < 17344 then
                  exact transitionMapProof0270 state (by omega) (by omega) generator coordinate
                else
                  exact transitionMapProof0271 state (by omega) (by omega) generator coordinate
              else
                if hAt17472 : state.val < 17472 then
                  exact transitionMapProof0272 state (by omega) (by omega) generator coordinate
                else
                  exact transitionMapProof0273 state (by omega) (by omega) generator coordinate
            else
              if hAt17664 : state.val < 17664 then
                if hAt17600 : state.val < 17600 then
                  exact transitionMapProof0274 state (by omega) (by omega) generator coordinate
                else
                  exact transitionMapProof0275 state (by omega) (by omega) generator coordinate
              else
                if hAt17728 : state.val < 17728 then
                  exact transitionMapProof0276 state (by omega) (by omega) generator coordinate
                else
                  if hAt17792 : state.val < 17792 then
                    exact transitionMapProof0277 state (by omega) (by omega) generator coordinate
                  else
                    exact transitionMapProof0278 state (by omega) (by omega) generator coordinate
          else
            if hAt18112 : state.val < 18112 then
              if hAt17984 : state.val < 17984 then
                if hAt17920 : state.val < 17920 then
                  exact transitionMapProof0279 state (by omega) (by omega) generator coordinate
                else
                  exact transitionMapProof0280 state (by omega) (by omega) generator coordinate
              else
                if hAt18048 : state.val < 18048 then
                  exact transitionMapProof0281 state (by omega) (by omega) generator coordinate
                else
                  exact transitionMapProof0282 state (by omega) (by omega) generator coordinate
            else
              if hAt18240 : state.val < 18240 then
                if hAt18176 : state.val < 18176 then
                  exact transitionMapProof0283 state (by omega) (by omega) generator coordinate
                else
                  exact transitionMapProof0284 state (by omega) (by omega) generator coordinate
              else
                if hAt18304 : state.val < 18304 then
                  exact transitionMapProof0285 state (by omega) (by omega) generator coordinate
                else
                  if hAt18368 : state.val < 18368 then
                    exact transitionMapProof0286 state (by omega) (by omega) generator coordinate
                  else
                    exact transitionMapProof0287 state (by omega) (by omega) generator coordinate

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9052.Shards
