import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9052.Shards.SourceLabelTransitionProofPart00
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9052.Shards.SourceLabelTransitionProofPart01
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9052.Shards.SourceLabelTransitionProofPart02
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9052.Shards.SourceLabelTransitionProofPart03
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9052.Shards.SourceLabelTransitionProofPart04
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9052.Shards.SourceLabelTransitionProofPart05
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9052.Shards.SourceLabelTransitionProofPart06
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9052.Shards.SourceLabelTransitionProofPart07
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9052.Shards.SourceLabelTransitionProofPart08
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9052.Support.Core
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9052.Shards

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransition
    (state : Fin 18432)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9052.sourceLabel
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9052.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative.sourceSemigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9052.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9052.generatorSourceLabel generator) := by
  if hAt9216 : state.val < 9216 then
    if hAt4608 : state.val < 4608 then
      if hAt2304 : state.val < 2304 then
        if hAt1152 : state.val < 1152 then
          if hAt576 : state.val < 576 then
            if hAt256 : state.val < 256 then
              if hAt128 : state.val < 128 then
                if hAt64 : state.val < 64 then
                  exact sourceLabelTransitionProof0000 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0001 state (by omega) (by omega) generator
              else
                if hAt192 : state.val < 192 then
                  exact sourceLabelTransitionProof0002 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0003 state (by omega) (by omega) generator
            else
              if hAt384 : state.val < 384 then
                if hAt320 : state.val < 320 then
                  exact sourceLabelTransitionProof0004 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0005 state (by omega) (by omega) generator
              else
                if hAt448 : state.val < 448 then
                  exact sourceLabelTransitionProof0006 state (by omega) (by omega) generator
                else
                  if hAt512 : state.val < 512 then
                    exact sourceLabelTransitionProof0007 state (by omega) (by omega) generator
                  else
                    exact sourceLabelTransitionProof0008 state (by omega) (by omega) generator
          else
            if hAt832 : state.val < 832 then
              if hAt704 : state.val < 704 then
                if hAt640 : state.val < 640 then
                  exact sourceLabelTransitionProof0009 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0010 state (by omega) (by omega) generator
              else
                if hAt768 : state.val < 768 then
                  exact sourceLabelTransitionProof0011 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0012 state (by omega) (by omega) generator
            else
              if hAt960 : state.val < 960 then
                if hAt896 : state.val < 896 then
                  exact sourceLabelTransitionProof0013 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0014 state (by omega) (by omega) generator
              else
                if hAt1024 : state.val < 1024 then
                  exact sourceLabelTransitionProof0015 state (by omega) (by omega) generator
                else
                  if hAt1088 : state.val < 1088 then
                    exact sourceLabelTransitionProof0016 state (by omega) (by omega) generator
                  else
                    exact sourceLabelTransitionProof0017 state (by omega) (by omega) generator
        else
          if hAt1728 : state.val < 1728 then
            if hAt1408 : state.val < 1408 then
              if hAt1280 : state.val < 1280 then
                if hAt1216 : state.val < 1216 then
                  exact sourceLabelTransitionProof0018 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0019 state (by omega) (by omega) generator
              else
                if hAt1344 : state.val < 1344 then
                  exact sourceLabelTransitionProof0020 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0021 state (by omega) (by omega) generator
            else
              if hAt1536 : state.val < 1536 then
                if hAt1472 : state.val < 1472 then
                  exact sourceLabelTransitionProof0022 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0023 state (by omega) (by omega) generator
              else
                if hAt1600 : state.val < 1600 then
                  exact sourceLabelTransitionProof0024 state (by omega) (by omega) generator
                else
                  if hAt1664 : state.val < 1664 then
                    exact sourceLabelTransitionProof0025 state (by omega) (by omega) generator
                  else
                    exact sourceLabelTransitionProof0026 state (by omega) (by omega) generator
          else
            if hAt1984 : state.val < 1984 then
              if hAt1856 : state.val < 1856 then
                if hAt1792 : state.val < 1792 then
                  exact sourceLabelTransitionProof0027 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0028 state (by omega) (by omega) generator
              else
                if hAt1920 : state.val < 1920 then
                  exact sourceLabelTransitionProof0029 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0030 state (by omega) (by omega) generator
            else
              if hAt2112 : state.val < 2112 then
                if hAt2048 : state.val < 2048 then
                  exact sourceLabelTransitionProof0031 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0032 state (by omega) (by omega) generator
              else
                if hAt2176 : state.val < 2176 then
                  exact sourceLabelTransitionProof0033 state (by omega) (by omega) generator
                else
                  if hAt2240 : state.val < 2240 then
                    exact sourceLabelTransitionProof0034 state (by omega) (by omega) generator
                  else
                    exact sourceLabelTransitionProof0035 state (by omega) (by omega) generator
      else
        if hAt3456 : state.val < 3456 then
          if hAt2880 : state.val < 2880 then
            if hAt2560 : state.val < 2560 then
              if hAt2432 : state.val < 2432 then
                if hAt2368 : state.val < 2368 then
                  exact sourceLabelTransitionProof0036 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0037 state (by omega) (by omega) generator
              else
                if hAt2496 : state.val < 2496 then
                  exact sourceLabelTransitionProof0038 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0039 state (by omega) (by omega) generator
            else
              if hAt2688 : state.val < 2688 then
                if hAt2624 : state.val < 2624 then
                  exact sourceLabelTransitionProof0040 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0041 state (by omega) (by omega) generator
              else
                if hAt2752 : state.val < 2752 then
                  exact sourceLabelTransitionProof0042 state (by omega) (by omega) generator
                else
                  if hAt2816 : state.val < 2816 then
                    exact sourceLabelTransitionProof0043 state (by omega) (by omega) generator
                  else
                    exact sourceLabelTransitionProof0044 state (by omega) (by omega) generator
          else
            if hAt3136 : state.val < 3136 then
              if hAt3008 : state.val < 3008 then
                if hAt2944 : state.val < 2944 then
                  exact sourceLabelTransitionProof0045 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0046 state (by omega) (by omega) generator
              else
                if hAt3072 : state.val < 3072 then
                  exact sourceLabelTransitionProof0047 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0048 state (by omega) (by omega) generator
            else
              if hAt3264 : state.val < 3264 then
                if hAt3200 : state.val < 3200 then
                  exact sourceLabelTransitionProof0049 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0050 state (by omega) (by omega) generator
              else
                if hAt3328 : state.val < 3328 then
                  exact sourceLabelTransitionProof0051 state (by omega) (by omega) generator
                else
                  if hAt3392 : state.val < 3392 then
                    exact sourceLabelTransitionProof0052 state (by omega) (by omega) generator
                  else
                    exact sourceLabelTransitionProof0053 state (by omega) (by omega) generator
        else
          if hAt4032 : state.val < 4032 then
            if hAt3712 : state.val < 3712 then
              if hAt3584 : state.val < 3584 then
                if hAt3520 : state.val < 3520 then
                  exact sourceLabelTransitionProof0054 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0055 state (by omega) (by omega) generator
              else
                if hAt3648 : state.val < 3648 then
                  exact sourceLabelTransitionProof0056 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0057 state (by omega) (by omega) generator
            else
              if hAt3840 : state.val < 3840 then
                if hAt3776 : state.val < 3776 then
                  exact sourceLabelTransitionProof0058 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0059 state (by omega) (by omega) generator
              else
                if hAt3904 : state.val < 3904 then
                  exact sourceLabelTransitionProof0060 state (by omega) (by omega) generator
                else
                  if hAt3968 : state.val < 3968 then
                    exact sourceLabelTransitionProof0061 state (by omega) (by omega) generator
                  else
                    exact sourceLabelTransitionProof0062 state (by omega) (by omega) generator
          else
            if hAt4288 : state.val < 4288 then
              if hAt4160 : state.val < 4160 then
                if hAt4096 : state.val < 4096 then
                  exact sourceLabelTransitionProof0063 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0064 state (by omega) (by omega) generator
              else
                if hAt4224 : state.val < 4224 then
                  exact sourceLabelTransitionProof0065 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0066 state (by omega) (by omega) generator
            else
              if hAt4416 : state.val < 4416 then
                if hAt4352 : state.val < 4352 then
                  exact sourceLabelTransitionProof0067 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0068 state (by omega) (by omega) generator
              else
                if hAt4480 : state.val < 4480 then
                  exact sourceLabelTransitionProof0069 state (by omega) (by omega) generator
                else
                  if hAt4544 : state.val < 4544 then
                    exact sourceLabelTransitionProof0070 state (by omega) (by omega) generator
                  else
                    exact sourceLabelTransitionProof0071 state (by omega) (by omega) generator
    else
      if hAt6912 : state.val < 6912 then
        if hAt5760 : state.val < 5760 then
          if hAt5184 : state.val < 5184 then
            if hAt4864 : state.val < 4864 then
              if hAt4736 : state.val < 4736 then
                if hAt4672 : state.val < 4672 then
                  exact sourceLabelTransitionProof0072 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0073 state (by omega) (by omega) generator
              else
                if hAt4800 : state.val < 4800 then
                  exact sourceLabelTransitionProof0074 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0075 state (by omega) (by omega) generator
            else
              if hAt4992 : state.val < 4992 then
                if hAt4928 : state.val < 4928 then
                  exact sourceLabelTransitionProof0076 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0077 state (by omega) (by omega) generator
              else
                if hAt5056 : state.val < 5056 then
                  exact sourceLabelTransitionProof0078 state (by omega) (by omega) generator
                else
                  if hAt5120 : state.val < 5120 then
                    exact sourceLabelTransitionProof0079 state (by omega) (by omega) generator
                  else
                    exact sourceLabelTransitionProof0080 state (by omega) (by omega) generator
          else
            if hAt5440 : state.val < 5440 then
              if hAt5312 : state.val < 5312 then
                if hAt5248 : state.val < 5248 then
                  exact sourceLabelTransitionProof0081 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0082 state (by omega) (by omega) generator
              else
                if hAt5376 : state.val < 5376 then
                  exact sourceLabelTransitionProof0083 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0084 state (by omega) (by omega) generator
            else
              if hAt5568 : state.val < 5568 then
                if hAt5504 : state.val < 5504 then
                  exact sourceLabelTransitionProof0085 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0086 state (by omega) (by omega) generator
              else
                if hAt5632 : state.val < 5632 then
                  exact sourceLabelTransitionProof0087 state (by omega) (by omega) generator
                else
                  if hAt5696 : state.val < 5696 then
                    exact sourceLabelTransitionProof0088 state (by omega) (by omega) generator
                  else
                    exact sourceLabelTransitionProof0089 state (by omega) (by omega) generator
        else
          if hAt6336 : state.val < 6336 then
            if hAt6016 : state.val < 6016 then
              if hAt5888 : state.val < 5888 then
                if hAt5824 : state.val < 5824 then
                  exact sourceLabelTransitionProof0090 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0091 state (by omega) (by omega) generator
              else
                if hAt5952 : state.val < 5952 then
                  exact sourceLabelTransitionProof0092 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0093 state (by omega) (by omega) generator
            else
              if hAt6144 : state.val < 6144 then
                if hAt6080 : state.val < 6080 then
                  exact sourceLabelTransitionProof0094 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0095 state (by omega) (by omega) generator
              else
                if hAt6208 : state.val < 6208 then
                  exact sourceLabelTransitionProof0096 state (by omega) (by omega) generator
                else
                  if hAt6272 : state.val < 6272 then
                    exact sourceLabelTransitionProof0097 state (by omega) (by omega) generator
                  else
                    exact sourceLabelTransitionProof0098 state (by omega) (by omega) generator
          else
            if hAt6592 : state.val < 6592 then
              if hAt6464 : state.val < 6464 then
                if hAt6400 : state.val < 6400 then
                  exact sourceLabelTransitionProof0099 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0100 state (by omega) (by omega) generator
              else
                if hAt6528 : state.val < 6528 then
                  exact sourceLabelTransitionProof0101 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0102 state (by omega) (by omega) generator
            else
              if hAt6720 : state.val < 6720 then
                if hAt6656 : state.val < 6656 then
                  exact sourceLabelTransitionProof0103 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0104 state (by omega) (by omega) generator
              else
                if hAt6784 : state.val < 6784 then
                  exact sourceLabelTransitionProof0105 state (by omega) (by omega) generator
                else
                  if hAt6848 : state.val < 6848 then
                    exact sourceLabelTransitionProof0106 state (by omega) (by omega) generator
                  else
                    exact sourceLabelTransitionProof0107 state (by omega) (by omega) generator
      else
        if hAt8064 : state.val < 8064 then
          if hAt7488 : state.val < 7488 then
            if hAt7168 : state.val < 7168 then
              if hAt7040 : state.val < 7040 then
                if hAt6976 : state.val < 6976 then
                  exact sourceLabelTransitionProof0108 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0109 state (by omega) (by omega) generator
              else
                if hAt7104 : state.val < 7104 then
                  exact sourceLabelTransitionProof0110 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0111 state (by omega) (by omega) generator
            else
              if hAt7296 : state.val < 7296 then
                if hAt7232 : state.val < 7232 then
                  exact sourceLabelTransitionProof0112 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0113 state (by omega) (by omega) generator
              else
                if hAt7360 : state.val < 7360 then
                  exact sourceLabelTransitionProof0114 state (by omega) (by omega) generator
                else
                  if hAt7424 : state.val < 7424 then
                    exact sourceLabelTransitionProof0115 state (by omega) (by omega) generator
                  else
                    exact sourceLabelTransitionProof0116 state (by omega) (by omega) generator
          else
            if hAt7744 : state.val < 7744 then
              if hAt7616 : state.val < 7616 then
                if hAt7552 : state.val < 7552 then
                  exact sourceLabelTransitionProof0117 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0118 state (by omega) (by omega) generator
              else
                if hAt7680 : state.val < 7680 then
                  exact sourceLabelTransitionProof0119 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0120 state (by omega) (by omega) generator
            else
              if hAt7872 : state.val < 7872 then
                if hAt7808 : state.val < 7808 then
                  exact sourceLabelTransitionProof0121 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0122 state (by omega) (by omega) generator
              else
                if hAt7936 : state.val < 7936 then
                  exact sourceLabelTransitionProof0123 state (by omega) (by omega) generator
                else
                  if hAt8000 : state.val < 8000 then
                    exact sourceLabelTransitionProof0124 state (by omega) (by omega) generator
                  else
                    exact sourceLabelTransitionProof0125 state (by omega) (by omega) generator
        else
          if hAt8640 : state.val < 8640 then
            if hAt8320 : state.val < 8320 then
              if hAt8192 : state.val < 8192 then
                if hAt8128 : state.val < 8128 then
                  exact sourceLabelTransitionProof0126 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0127 state (by omega) (by omega) generator
              else
                if hAt8256 : state.val < 8256 then
                  exact sourceLabelTransitionProof0128 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0129 state (by omega) (by omega) generator
            else
              if hAt8448 : state.val < 8448 then
                if hAt8384 : state.val < 8384 then
                  exact sourceLabelTransitionProof0130 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0131 state (by omega) (by omega) generator
              else
                if hAt8512 : state.val < 8512 then
                  exact sourceLabelTransitionProof0132 state (by omega) (by omega) generator
                else
                  if hAt8576 : state.val < 8576 then
                    exact sourceLabelTransitionProof0133 state (by omega) (by omega) generator
                  else
                    exact sourceLabelTransitionProof0134 state (by omega) (by omega) generator
          else
            if hAt8896 : state.val < 8896 then
              if hAt8768 : state.val < 8768 then
                if hAt8704 : state.val < 8704 then
                  exact sourceLabelTransitionProof0135 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0136 state (by omega) (by omega) generator
              else
                if hAt8832 : state.val < 8832 then
                  exact sourceLabelTransitionProof0137 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0138 state (by omega) (by omega) generator
            else
              if hAt9024 : state.val < 9024 then
                if hAt8960 : state.val < 8960 then
                  exact sourceLabelTransitionProof0139 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0140 state (by omega) (by omega) generator
              else
                if hAt9088 : state.val < 9088 then
                  exact sourceLabelTransitionProof0141 state (by omega) (by omega) generator
                else
                  if hAt9152 : state.val < 9152 then
                    exact sourceLabelTransitionProof0142 state (by omega) (by omega) generator
                  else
                    exact sourceLabelTransitionProof0143 state (by omega) (by omega) generator
  else
    if hAt13824 : state.val < 13824 then
      if hAt11520 : state.val < 11520 then
        if hAt10368 : state.val < 10368 then
          if hAt9792 : state.val < 9792 then
            if hAt9472 : state.val < 9472 then
              if hAt9344 : state.val < 9344 then
                if hAt9280 : state.val < 9280 then
                  exact sourceLabelTransitionProof0144 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0145 state (by omega) (by omega) generator
              else
                if hAt9408 : state.val < 9408 then
                  exact sourceLabelTransitionProof0146 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0147 state (by omega) (by omega) generator
            else
              if hAt9600 : state.val < 9600 then
                if hAt9536 : state.val < 9536 then
                  exact sourceLabelTransitionProof0148 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0149 state (by omega) (by omega) generator
              else
                if hAt9664 : state.val < 9664 then
                  exact sourceLabelTransitionProof0150 state (by omega) (by omega) generator
                else
                  if hAt9728 : state.val < 9728 then
                    exact sourceLabelTransitionProof0151 state (by omega) (by omega) generator
                  else
                    exact sourceLabelTransitionProof0152 state (by omega) (by omega) generator
          else
            if hAt10048 : state.val < 10048 then
              if hAt9920 : state.val < 9920 then
                if hAt9856 : state.val < 9856 then
                  exact sourceLabelTransitionProof0153 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0154 state (by omega) (by omega) generator
              else
                if hAt9984 : state.val < 9984 then
                  exact sourceLabelTransitionProof0155 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0156 state (by omega) (by omega) generator
            else
              if hAt10176 : state.val < 10176 then
                if hAt10112 : state.val < 10112 then
                  exact sourceLabelTransitionProof0157 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0158 state (by omega) (by omega) generator
              else
                if hAt10240 : state.val < 10240 then
                  exact sourceLabelTransitionProof0159 state (by omega) (by omega) generator
                else
                  if hAt10304 : state.val < 10304 then
                    exact sourceLabelTransitionProof0160 state (by omega) (by omega) generator
                  else
                    exact sourceLabelTransitionProof0161 state (by omega) (by omega) generator
        else
          if hAt10944 : state.val < 10944 then
            if hAt10624 : state.val < 10624 then
              if hAt10496 : state.val < 10496 then
                if hAt10432 : state.val < 10432 then
                  exact sourceLabelTransitionProof0162 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0163 state (by omega) (by omega) generator
              else
                if hAt10560 : state.val < 10560 then
                  exact sourceLabelTransitionProof0164 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0165 state (by omega) (by omega) generator
            else
              if hAt10752 : state.val < 10752 then
                if hAt10688 : state.val < 10688 then
                  exact sourceLabelTransitionProof0166 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0167 state (by omega) (by omega) generator
              else
                if hAt10816 : state.val < 10816 then
                  exact sourceLabelTransitionProof0168 state (by omega) (by omega) generator
                else
                  if hAt10880 : state.val < 10880 then
                    exact sourceLabelTransitionProof0169 state (by omega) (by omega) generator
                  else
                    exact sourceLabelTransitionProof0170 state (by omega) (by omega) generator
          else
            if hAt11200 : state.val < 11200 then
              if hAt11072 : state.val < 11072 then
                if hAt11008 : state.val < 11008 then
                  exact sourceLabelTransitionProof0171 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0172 state (by omega) (by omega) generator
              else
                if hAt11136 : state.val < 11136 then
                  exact sourceLabelTransitionProof0173 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0174 state (by omega) (by omega) generator
            else
              if hAt11328 : state.val < 11328 then
                if hAt11264 : state.val < 11264 then
                  exact sourceLabelTransitionProof0175 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0176 state (by omega) (by omega) generator
              else
                if hAt11392 : state.val < 11392 then
                  exact sourceLabelTransitionProof0177 state (by omega) (by omega) generator
                else
                  if hAt11456 : state.val < 11456 then
                    exact sourceLabelTransitionProof0178 state (by omega) (by omega) generator
                  else
                    exact sourceLabelTransitionProof0179 state (by omega) (by omega) generator
      else
        if hAt12672 : state.val < 12672 then
          if hAt12096 : state.val < 12096 then
            if hAt11776 : state.val < 11776 then
              if hAt11648 : state.val < 11648 then
                if hAt11584 : state.val < 11584 then
                  exact sourceLabelTransitionProof0180 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0181 state (by omega) (by omega) generator
              else
                if hAt11712 : state.val < 11712 then
                  exact sourceLabelTransitionProof0182 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0183 state (by omega) (by omega) generator
            else
              if hAt11904 : state.val < 11904 then
                if hAt11840 : state.val < 11840 then
                  exact sourceLabelTransitionProof0184 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0185 state (by omega) (by omega) generator
              else
                if hAt11968 : state.val < 11968 then
                  exact sourceLabelTransitionProof0186 state (by omega) (by omega) generator
                else
                  if hAt12032 : state.val < 12032 then
                    exact sourceLabelTransitionProof0187 state (by omega) (by omega) generator
                  else
                    exact sourceLabelTransitionProof0188 state (by omega) (by omega) generator
          else
            if hAt12352 : state.val < 12352 then
              if hAt12224 : state.val < 12224 then
                if hAt12160 : state.val < 12160 then
                  exact sourceLabelTransitionProof0189 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0190 state (by omega) (by omega) generator
              else
                if hAt12288 : state.val < 12288 then
                  exact sourceLabelTransitionProof0191 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0192 state (by omega) (by omega) generator
            else
              if hAt12480 : state.val < 12480 then
                if hAt12416 : state.val < 12416 then
                  exact sourceLabelTransitionProof0193 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0194 state (by omega) (by omega) generator
              else
                if hAt12544 : state.val < 12544 then
                  exact sourceLabelTransitionProof0195 state (by omega) (by omega) generator
                else
                  if hAt12608 : state.val < 12608 then
                    exact sourceLabelTransitionProof0196 state (by omega) (by omega) generator
                  else
                    exact sourceLabelTransitionProof0197 state (by omega) (by omega) generator
        else
          if hAt13248 : state.val < 13248 then
            if hAt12928 : state.val < 12928 then
              if hAt12800 : state.val < 12800 then
                if hAt12736 : state.val < 12736 then
                  exact sourceLabelTransitionProof0198 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0199 state (by omega) (by omega) generator
              else
                if hAt12864 : state.val < 12864 then
                  exact sourceLabelTransitionProof0200 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0201 state (by omega) (by omega) generator
            else
              if hAt13056 : state.val < 13056 then
                if hAt12992 : state.val < 12992 then
                  exact sourceLabelTransitionProof0202 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0203 state (by omega) (by omega) generator
              else
                if hAt13120 : state.val < 13120 then
                  exact sourceLabelTransitionProof0204 state (by omega) (by omega) generator
                else
                  if hAt13184 : state.val < 13184 then
                    exact sourceLabelTransitionProof0205 state (by omega) (by omega) generator
                  else
                    exact sourceLabelTransitionProof0206 state (by omega) (by omega) generator
          else
            if hAt13504 : state.val < 13504 then
              if hAt13376 : state.val < 13376 then
                if hAt13312 : state.val < 13312 then
                  exact sourceLabelTransitionProof0207 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0208 state (by omega) (by omega) generator
              else
                if hAt13440 : state.val < 13440 then
                  exact sourceLabelTransitionProof0209 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0210 state (by omega) (by omega) generator
            else
              if hAt13632 : state.val < 13632 then
                if hAt13568 : state.val < 13568 then
                  exact sourceLabelTransitionProof0211 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0212 state (by omega) (by omega) generator
              else
                if hAt13696 : state.val < 13696 then
                  exact sourceLabelTransitionProof0213 state (by omega) (by omega) generator
                else
                  if hAt13760 : state.val < 13760 then
                    exact sourceLabelTransitionProof0214 state (by omega) (by omega) generator
                  else
                    exact sourceLabelTransitionProof0215 state (by omega) (by omega) generator
    else
      if hAt16128 : state.val < 16128 then
        if hAt14976 : state.val < 14976 then
          if hAt14400 : state.val < 14400 then
            if hAt14080 : state.val < 14080 then
              if hAt13952 : state.val < 13952 then
                if hAt13888 : state.val < 13888 then
                  exact sourceLabelTransitionProof0216 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0217 state (by omega) (by omega) generator
              else
                if hAt14016 : state.val < 14016 then
                  exact sourceLabelTransitionProof0218 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0219 state (by omega) (by omega) generator
            else
              if hAt14208 : state.val < 14208 then
                if hAt14144 : state.val < 14144 then
                  exact sourceLabelTransitionProof0220 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0221 state (by omega) (by omega) generator
              else
                if hAt14272 : state.val < 14272 then
                  exact sourceLabelTransitionProof0222 state (by omega) (by omega) generator
                else
                  if hAt14336 : state.val < 14336 then
                    exact sourceLabelTransitionProof0223 state (by omega) (by omega) generator
                  else
                    exact sourceLabelTransitionProof0224 state (by omega) (by omega) generator
          else
            if hAt14656 : state.val < 14656 then
              if hAt14528 : state.val < 14528 then
                if hAt14464 : state.val < 14464 then
                  exact sourceLabelTransitionProof0225 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0226 state (by omega) (by omega) generator
              else
                if hAt14592 : state.val < 14592 then
                  exact sourceLabelTransitionProof0227 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0228 state (by omega) (by omega) generator
            else
              if hAt14784 : state.val < 14784 then
                if hAt14720 : state.val < 14720 then
                  exact sourceLabelTransitionProof0229 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0230 state (by omega) (by omega) generator
              else
                if hAt14848 : state.val < 14848 then
                  exact sourceLabelTransitionProof0231 state (by omega) (by omega) generator
                else
                  if hAt14912 : state.val < 14912 then
                    exact sourceLabelTransitionProof0232 state (by omega) (by omega) generator
                  else
                    exact sourceLabelTransitionProof0233 state (by omega) (by omega) generator
        else
          if hAt15552 : state.val < 15552 then
            if hAt15232 : state.val < 15232 then
              if hAt15104 : state.val < 15104 then
                if hAt15040 : state.val < 15040 then
                  exact sourceLabelTransitionProof0234 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0235 state (by omega) (by omega) generator
              else
                if hAt15168 : state.val < 15168 then
                  exact sourceLabelTransitionProof0236 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0237 state (by omega) (by omega) generator
            else
              if hAt15360 : state.val < 15360 then
                if hAt15296 : state.val < 15296 then
                  exact sourceLabelTransitionProof0238 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0239 state (by omega) (by omega) generator
              else
                if hAt15424 : state.val < 15424 then
                  exact sourceLabelTransitionProof0240 state (by omega) (by omega) generator
                else
                  if hAt15488 : state.val < 15488 then
                    exact sourceLabelTransitionProof0241 state (by omega) (by omega) generator
                  else
                    exact sourceLabelTransitionProof0242 state (by omega) (by omega) generator
          else
            if hAt15808 : state.val < 15808 then
              if hAt15680 : state.val < 15680 then
                if hAt15616 : state.val < 15616 then
                  exact sourceLabelTransitionProof0243 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0244 state (by omega) (by omega) generator
              else
                if hAt15744 : state.val < 15744 then
                  exact sourceLabelTransitionProof0245 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0246 state (by omega) (by omega) generator
            else
              if hAt15936 : state.val < 15936 then
                if hAt15872 : state.val < 15872 then
                  exact sourceLabelTransitionProof0247 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0248 state (by omega) (by omega) generator
              else
                if hAt16000 : state.val < 16000 then
                  exact sourceLabelTransitionProof0249 state (by omega) (by omega) generator
                else
                  if hAt16064 : state.val < 16064 then
                    exact sourceLabelTransitionProof0250 state (by omega) (by omega) generator
                  else
                    exact sourceLabelTransitionProof0251 state (by omega) (by omega) generator
      else
        if hAt17280 : state.val < 17280 then
          if hAt16704 : state.val < 16704 then
            if hAt16384 : state.val < 16384 then
              if hAt16256 : state.val < 16256 then
                if hAt16192 : state.val < 16192 then
                  exact sourceLabelTransitionProof0252 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0253 state (by omega) (by omega) generator
              else
                if hAt16320 : state.val < 16320 then
                  exact sourceLabelTransitionProof0254 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0255 state (by omega) (by omega) generator
            else
              if hAt16512 : state.val < 16512 then
                if hAt16448 : state.val < 16448 then
                  exact sourceLabelTransitionProof0256 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0257 state (by omega) (by omega) generator
              else
                if hAt16576 : state.val < 16576 then
                  exact sourceLabelTransitionProof0258 state (by omega) (by omega) generator
                else
                  if hAt16640 : state.val < 16640 then
                    exact sourceLabelTransitionProof0259 state (by omega) (by omega) generator
                  else
                    exact sourceLabelTransitionProof0260 state (by omega) (by omega) generator
          else
            if hAt16960 : state.val < 16960 then
              if hAt16832 : state.val < 16832 then
                if hAt16768 : state.val < 16768 then
                  exact sourceLabelTransitionProof0261 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0262 state (by omega) (by omega) generator
              else
                if hAt16896 : state.val < 16896 then
                  exact sourceLabelTransitionProof0263 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0264 state (by omega) (by omega) generator
            else
              if hAt17088 : state.val < 17088 then
                if hAt17024 : state.val < 17024 then
                  exact sourceLabelTransitionProof0265 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0266 state (by omega) (by omega) generator
              else
                if hAt17152 : state.val < 17152 then
                  exact sourceLabelTransitionProof0267 state (by omega) (by omega) generator
                else
                  if hAt17216 : state.val < 17216 then
                    exact sourceLabelTransitionProof0268 state (by omega) (by omega) generator
                  else
                    exact sourceLabelTransitionProof0269 state (by omega) (by omega) generator
        else
          if hAt17856 : state.val < 17856 then
            if hAt17536 : state.val < 17536 then
              if hAt17408 : state.val < 17408 then
                if hAt17344 : state.val < 17344 then
                  exact sourceLabelTransitionProof0270 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0271 state (by omega) (by omega) generator
              else
                if hAt17472 : state.val < 17472 then
                  exact sourceLabelTransitionProof0272 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0273 state (by omega) (by omega) generator
            else
              if hAt17664 : state.val < 17664 then
                if hAt17600 : state.val < 17600 then
                  exact sourceLabelTransitionProof0274 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0275 state (by omega) (by omega) generator
              else
                if hAt17728 : state.val < 17728 then
                  exact sourceLabelTransitionProof0276 state (by omega) (by omega) generator
                else
                  if hAt17792 : state.val < 17792 then
                    exact sourceLabelTransitionProof0277 state (by omega) (by omega) generator
                  else
                    exact sourceLabelTransitionProof0278 state (by omega) (by omega) generator
          else
            if hAt18112 : state.val < 18112 then
              if hAt17984 : state.val < 17984 then
                if hAt17920 : state.val < 17920 then
                  exact sourceLabelTransitionProof0279 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0280 state (by omega) (by omega) generator
              else
                if hAt18048 : state.val < 18048 then
                  exact sourceLabelTransitionProof0281 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0282 state (by omega) (by omega) generator
            else
              if hAt18240 : state.val < 18240 then
                if hAt18176 : state.val < 18176 then
                  exact sourceLabelTransitionProof0283 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0284 state (by omega) (by omega) generator
              else
                if hAt18304 : state.val < 18304 then
                  exact sourceLabelTransitionProof0285 state (by omega) (by omega) generator
                else
                  if hAt18368 : state.val < 18368 then
                    exact sourceLabelTransitionProof0286 state (by omega) (by omega) generator
                  else
                    exact sourceLabelTransitionProof0287 state (by omega) (by omega) generator

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9052.Shards
