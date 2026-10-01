import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13662.Shards.SourceLabelTransitionProofPart00
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13662.Shards.SourceLabelTransitionProofPart01
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13662.Shards.SourceLabelTransitionProofPart02
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13662.Shards.SourceLabelTransitionProofPart03
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13662.Shards.SourceLabelTransitionProofPart04
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13662.Shards.SourceLabelTransitionProofPart05
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13662.Support.Core
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13662.Shards

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransition
    (state : Fin 11742)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13662.sourceLabel
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13662.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Opposite.sourceSemigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13662.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13662.generatorSourceLabel generator) := by
  if hAt5888 : state.val < 5888 then
    if hAt2944 : state.val < 2944 then
      if hAt1472 : state.val < 1472 then
        if hAt704 : state.val < 704 then
          if hAt320 : state.val < 320 then
            if hAt128 : state.val < 128 then
              if hAt64 : state.val < 64 then
                exact sourceLabelTransitionProof0000 state (by omega) (by omega) generator
              else
                exact sourceLabelTransitionProof0001 state (by omega) (by omega) generator
            else
              if hAt192 : state.val < 192 then
                exact sourceLabelTransitionProof0002 state (by omega) (by omega) generator
              else
                if hAt256 : state.val < 256 then
                  exact sourceLabelTransitionProof0003 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0004 state (by omega) (by omega) generator
          else
            if hAt512 : state.val < 512 then
              if hAt384 : state.val < 384 then
                exact sourceLabelTransitionProof0005 state (by omega) (by omega) generator
              else
                if hAt448 : state.val < 448 then
                  exact sourceLabelTransitionProof0006 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0007 state (by omega) (by omega) generator
            else
              if hAt576 : state.val < 576 then
                exact sourceLabelTransitionProof0008 state (by omega) (by omega) generator
              else
                if hAt640 : state.val < 640 then
                  exact sourceLabelTransitionProof0009 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0010 state (by omega) (by omega) generator
        else
          if hAt1088 : state.val < 1088 then
            if hAt896 : state.val < 896 then
              if hAt768 : state.val < 768 then
                exact sourceLabelTransitionProof0011 state (by omega) (by omega) generator
              else
                if hAt832 : state.val < 832 then
                  exact sourceLabelTransitionProof0012 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0013 state (by omega) (by omega) generator
            else
              if hAt960 : state.val < 960 then
                exact sourceLabelTransitionProof0014 state (by omega) (by omega) generator
              else
                if hAt1024 : state.val < 1024 then
                  exact sourceLabelTransitionProof0015 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0016 state (by omega) (by omega) generator
          else
            if hAt1280 : state.val < 1280 then
              if hAt1152 : state.val < 1152 then
                exact sourceLabelTransitionProof0017 state (by omega) (by omega) generator
              else
                if hAt1216 : state.val < 1216 then
                  exact sourceLabelTransitionProof0018 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0019 state (by omega) (by omega) generator
            else
              if hAt1344 : state.val < 1344 then
                exact sourceLabelTransitionProof0020 state (by omega) (by omega) generator
              else
                if hAt1408 : state.val < 1408 then
                  exact sourceLabelTransitionProof0021 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0022 state (by omega) (by omega) generator
      else
        if hAt2176 : state.val < 2176 then
          if hAt1792 : state.val < 1792 then
            if hAt1600 : state.val < 1600 then
              if hAt1536 : state.val < 1536 then
                exact sourceLabelTransitionProof0023 state (by omega) (by omega) generator
              else
                exact sourceLabelTransitionProof0024 state (by omega) (by omega) generator
            else
              if hAt1664 : state.val < 1664 then
                exact sourceLabelTransitionProof0025 state (by omega) (by omega) generator
              else
                if hAt1728 : state.val < 1728 then
                  exact sourceLabelTransitionProof0026 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0027 state (by omega) (by omega) generator
          else
            if hAt1984 : state.val < 1984 then
              if hAt1856 : state.val < 1856 then
                exact sourceLabelTransitionProof0028 state (by omega) (by omega) generator
              else
                if hAt1920 : state.val < 1920 then
                  exact sourceLabelTransitionProof0029 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0030 state (by omega) (by omega) generator
            else
              if hAt2048 : state.val < 2048 then
                exact sourceLabelTransitionProof0031 state (by omega) (by omega) generator
              else
                if hAt2112 : state.val < 2112 then
                  exact sourceLabelTransitionProof0032 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0033 state (by omega) (by omega) generator
        else
          if hAt2560 : state.val < 2560 then
            if hAt2368 : state.val < 2368 then
              if hAt2240 : state.val < 2240 then
                exact sourceLabelTransitionProof0034 state (by omega) (by omega) generator
              else
                if hAt2304 : state.val < 2304 then
                  exact sourceLabelTransitionProof0035 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0036 state (by omega) (by omega) generator
            else
              if hAt2432 : state.val < 2432 then
                exact sourceLabelTransitionProof0037 state (by omega) (by omega) generator
              else
                if hAt2496 : state.val < 2496 then
                  exact sourceLabelTransitionProof0038 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0039 state (by omega) (by omega) generator
          else
            if hAt2752 : state.val < 2752 then
              if hAt2624 : state.val < 2624 then
                exact sourceLabelTransitionProof0040 state (by omega) (by omega) generator
              else
                if hAt2688 : state.val < 2688 then
                  exact sourceLabelTransitionProof0041 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0042 state (by omega) (by omega) generator
            else
              if hAt2816 : state.val < 2816 then
                exact sourceLabelTransitionProof0043 state (by omega) (by omega) generator
              else
                if hAt2880 : state.val < 2880 then
                  exact sourceLabelTransitionProof0044 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0045 state (by omega) (by omega) generator
    else
      if hAt4416 : state.val < 4416 then
        if hAt3648 : state.val < 3648 then
          if hAt3264 : state.val < 3264 then
            if hAt3072 : state.val < 3072 then
              if hAt3008 : state.val < 3008 then
                exact sourceLabelTransitionProof0046 state (by omega) (by omega) generator
              else
                exact sourceLabelTransitionProof0047 state (by omega) (by omega) generator
            else
              if hAt3136 : state.val < 3136 then
                exact sourceLabelTransitionProof0048 state (by omega) (by omega) generator
              else
                if hAt3200 : state.val < 3200 then
                  exact sourceLabelTransitionProof0049 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0050 state (by omega) (by omega) generator
          else
            if hAt3456 : state.val < 3456 then
              if hAt3328 : state.val < 3328 then
                exact sourceLabelTransitionProof0051 state (by omega) (by omega) generator
              else
                if hAt3392 : state.val < 3392 then
                  exact sourceLabelTransitionProof0052 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0053 state (by omega) (by omega) generator
            else
              if hAt3520 : state.val < 3520 then
                exact sourceLabelTransitionProof0054 state (by omega) (by omega) generator
              else
                if hAt3584 : state.val < 3584 then
                  exact sourceLabelTransitionProof0055 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0056 state (by omega) (by omega) generator
        else
          if hAt4032 : state.val < 4032 then
            if hAt3840 : state.val < 3840 then
              if hAt3712 : state.val < 3712 then
                exact sourceLabelTransitionProof0057 state (by omega) (by omega) generator
              else
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
            if hAt4224 : state.val < 4224 then
              if hAt4096 : state.val < 4096 then
                exact sourceLabelTransitionProof0063 state (by omega) (by omega) generator
              else
                if hAt4160 : state.val < 4160 then
                  exact sourceLabelTransitionProof0064 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0065 state (by omega) (by omega) generator
            else
              if hAt4288 : state.val < 4288 then
                exact sourceLabelTransitionProof0066 state (by omega) (by omega) generator
              else
                if hAt4352 : state.val < 4352 then
                  exact sourceLabelTransitionProof0067 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0068 state (by omega) (by omega) generator
      else
        if hAt5120 : state.val < 5120 then
          if hAt4736 : state.val < 4736 then
            if hAt4544 : state.val < 4544 then
              if hAt4480 : state.val < 4480 then
                exact sourceLabelTransitionProof0069 state (by omega) (by omega) generator
              else
                exact sourceLabelTransitionProof0070 state (by omega) (by omega) generator
            else
              if hAt4608 : state.val < 4608 then
                exact sourceLabelTransitionProof0071 state (by omega) (by omega) generator
              else
                if hAt4672 : state.val < 4672 then
                  exact sourceLabelTransitionProof0072 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0073 state (by omega) (by omega) generator
          else
            if hAt4928 : state.val < 4928 then
              if hAt4800 : state.val < 4800 then
                exact sourceLabelTransitionProof0074 state (by omega) (by omega) generator
              else
                if hAt4864 : state.val < 4864 then
                  exact sourceLabelTransitionProof0075 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0076 state (by omega) (by omega) generator
            else
              if hAt4992 : state.val < 4992 then
                exact sourceLabelTransitionProof0077 state (by omega) (by omega) generator
              else
                if hAt5056 : state.val < 5056 then
                  exact sourceLabelTransitionProof0078 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0079 state (by omega) (by omega) generator
        else
          if hAt5504 : state.val < 5504 then
            if hAt5312 : state.val < 5312 then
              if hAt5184 : state.val < 5184 then
                exact sourceLabelTransitionProof0080 state (by omega) (by omega) generator
              else
                if hAt5248 : state.val < 5248 then
                  exact sourceLabelTransitionProof0081 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0082 state (by omega) (by omega) generator
            else
              if hAt5376 : state.val < 5376 then
                exact sourceLabelTransitionProof0083 state (by omega) (by omega) generator
              else
                if hAt5440 : state.val < 5440 then
                  exact sourceLabelTransitionProof0084 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0085 state (by omega) (by omega) generator
          else
            if hAt5696 : state.val < 5696 then
              if hAt5568 : state.val < 5568 then
                exact sourceLabelTransitionProof0086 state (by omega) (by omega) generator
              else
                if hAt5632 : state.val < 5632 then
                  exact sourceLabelTransitionProof0087 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0088 state (by omega) (by omega) generator
            else
              if hAt5760 : state.val < 5760 then
                exact sourceLabelTransitionProof0089 state (by omega) (by omega) generator
              else
                if hAt5824 : state.val < 5824 then
                  exact sourceLabelTransitionProof0090 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0091 state (by omega) (by omega) generator
  else
    if hAt8832 : state.val < 8832 then
      if hAt7360 : state.val < 7360 then
        if hAt6592 : state.val < 6592 then
          if hAt6208 : state.val < 6208 then
            if hAt6016 : state.val < 6016 then
              if hAt5952 : state.val < 5952 then
                exact sourceLabelTransitionProof0092 state (by omega) (by omega) generator
              else
                exact sourceLabelTransitionProof0093 state (by omega) (by omega) generator
            else
              if hAt6080 : state.val < 6080 then
                exact sourceLabelTransitionProof0094 state (by omega) (by omega) generator
              else
                if hAt6144 : state.val < 6144 then
                  exact sourceLabelTransitionProof0095 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0096 state (by omega) (by omega) generator
          else
            if hAt6400 : state.val < 6400 then
              if hAt6272 : state.val < 6272 then
                exact sourceLabelTransitionProof0097 state (by omega) (by omega) generator
              else
                if hAt6336 : state.val < 6336 then
                  exact sourceLabelTransitionProof0098 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0099 state (by omega) (by omega) generator
            else
              if hAt6464 : state.val < 6464 then
                exact sourceLabelTransitionProof0100 state (by omega) (by omega) generator
              else
                if hAt6528 : state.val < 6528 then
                  exact sourceLabelTransitionProof0101 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0102 state (by omega) (by omega) generator
        else
          if hAt6976 : state.val < 6976 then
            if hAt6784 : state.val < 6784 then
              if hAt6656 : state.val < 6656 then
                exact sourceLabelTransitionProof0103 state (by omega) (by omega) generator
              else
                if hAt6720 : state.val < 6720 then
                  exact sourceLabelTransitionProof0104 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0105 state (by omega) (by omega) generator
            else
              if hAt6848 : state.val < 6848 then
                exact sourceLabelTransitionProof0106 state (by omega) (by omega) generator
              else
                if hAt6912 : state.val < 6912 then
                  exact sourceLabelTransitionProof0107 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0108 state (by omega) (by omega) generator
          else
            if hAt7168 : state.val < 7168 then
              if hAt7040 : state.val < 7040 then
                exact sourceLabelTransitionProof0109 state (by omega) (by omega) generator
              else
                if hAt7104 : state.val < 7104 then
                  exact sourceLabelTransitionProof0110 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0111 state (by omega) (by omega) generator
            else
              if hAt7232 : state.val < 7232 then
                exact sourceLabelTransitionProof0112 state (by omega) (by omega) generator
              else
                if hAt7296 : state.val < 7296 then
                  exact sourceLabelTransitionProof0113 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0114 state (by omega) (by omega) generator
      else
        if hAt8064 : state.val < 8064 then
          if hAt7680 : state.val < 7680 then
            if hAt7488 : state.val < 7488 then
              if hAt7424 : state.val < 7424 then
                exact sourceLabelTransitionProof0115 state (by omega) (by omega) generator
              else
                exact sourceLabelTransitionProof0116 state (by omega) (by omega) generator
            else
              if hAt7552 : state.val < 7552 then
                exact sourceLabelTransitionProof0117 state (by omega) (by omega) generator
              else
                if hAt7616 : state.val < 7616 then
                  exact sourceLabelTransitionProof0118 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0119 state (by omega) (by omega) generator
          else
            if hAt7872 : state.val < 7872 then
              if hAt7744 : state.val < 7744 then
                exact sourceLabelTransitionProof0120 state (by omega) (by omega) generator
              else
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
          if hAt8448 : state.val < 8448 then
            if hAt8256 : state.val < 8256 then
              if hAt8128 : state.val < 8128 then
                exact sourceLabelTransitionProof0126 state (by omega) (by omega) generator
              else
                if hAt8192 : state.val < 8192 then
                  exact sourceLabelTransitionProof0127 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0128 state (by omega) (by omega) generator
            else
              if hAt8320 : state.val < 8320 then
                exact sourceLabelTransitionProof0129 state (by omega) (by omega) generator
              else
                if hAt8384 : state.val < 8384 then
                  exact sourceLabelTransitionProof0130 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0131 state (by omega) (by omega) generator
          else
            if hAt8640 : state.val < 8640 then
              if hAt8512 : state.val < 8512 then
                exact sourceLabelTransitionProof0132 state (by omega) (by omega) generator
              else
                if hAt8576 : state.val < 8576 then
                  exact sourceLabelTransitionProof0133 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0134 state (by omega) (by omega) generator
            else
              if hAt8704 : state.val < 8704 then
                exact sourceLabelTransitionProof0135 state (by omega) (by omega) generator
              else
                if hAt8768 : state.val < 8768 then
                  exact sourceLabelTransitionProof0136 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0137 state (by omega) (by omega) generator
    else
      if hAt10304 : state.val < 10304 then
        if hAt9536 : state.val < 9536 then
          if hAt9152 : state.val < 9152 then
            if hAt8960 : state.val < 8960 then
              if hAt8896 : state.val < 8896 then
                exact sourceLabelTransitionProof0138 state (by omega) (by omega) generator
              else
                exact sourceLabelTransitionProof0139 state (by omega) (by omega) generator
            else
              if hAt9024 : state.val < 9024 then
                exact sourceLabelTransitionProof0140 state (by omega) (by omega) generator
              else
                if hAt9088 : state.val < 9088 then
                  exact sourceLabelTransitionProof0141 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0142 state (by omega) (by omega) generator
          else
            if hAt9344 : state.val < 9344 then
              if hAt9216 : state.val < 9216 then
                exact sourceLabelTransitionProof0143 state (by omega) (by omega) generator
              else
                if hAt9280 : state.val < 9280 then
                  exact sourceLabelTransitionProof0144 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0145 state (by omega) (by omega) generator
            else
              if hAt9408 : state.val < 9408 then
                exact sourceLabelTransitionProof0146 state (by omega) (by omega) generator
              else
                if hAt9472 : state.val < 9472 then
                  exact sourceLabelTransitionProof0147 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0148 state (by omega) (by omega) generator
        else
          if hAt9920 : state.val < 9920 then
            if hAt9728 : state.val < 9728 then
              if hAt9600 : state.val < 9600 then
                exact sourceLabelTransitionProof0149 state (by omega) (by omega) generator
              else
                if hAt9664 : state.val < 9664 then
                  exact sourceLabelTransitionProof0150 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0151 state (by omega) (by omega) generator
            else
              if hAt9792 : state.val < 9792 then
                exact sourceLabelTransitionProof0152 state (by omega) (by omega) generator
              else
                if hAt9856 : state.val < 9856 then
                  exact sourceLabelTransitionProof0153 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0154 state (by omega) (by omega) generator
          else
            if hAt10112 : state.val < 10112 then
              if hAt9984 : state.val < 9984 then
                exact sourceLabelTransitionProof0155 state (by omega) (by omega) generator
              else
                if hAt10048 : state.val < 10048 then
                  exact sourceLabelTransitionProof0156 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0157 state (by omega) (by omega) generator
            else
              if hAt10176 : state.val < 10176 then
                exact sourceLabelTransitionProof0158 state (by omega) (by omega) generator
              else
                if hAt10240 : state.val < 10240 then
                  exact sourceLabelTransitionProof0159 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0160 state (by omega) (by omega) generator
      else
        if hAt11008 : state.val < 11008 then
          if hAt10624 : state.val < 10624 then
            if hAt10432 : state.val < 10432 then
              if hAt10368 : state.val < 10368 then
                exact sourceLabelTransitionProof0161 state (by omega) (by omega) generator
              else
                exact sourceLabelTransitionProof0162 state (by omega) (by omega) generator
            else
              if hAt10496 : state.val < 10496 then
                exact sourceLabelTransitionProof0163 state (by omega) (by omega) generator
              else
                if hAt10560 : state.val < 10560 then
                  exact sourceLabelTransitionProof0164 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0165 state (by omega) (by omega) generator
          else
            if hAt10816 : state.val < 10816 then
              if hAt10688 : state.val < 10688 then
                exact sourceLabelTransitionProof0166 state (by omega) (by omega) generator
              else
                if hAt10752 : state.val < 10752 then
                  exact sourceLabelTransitionProof0167 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0168 state (by omega) (by omega) generator
            else
              if hAt10880 : state.val < 10880 then
                exact sourceLabelTransitionProof0169 state (by omega) (by omega) generator
              else
                if hAt10944 : state.val < 10944 then
                  exact sourceLabelTransitionProof0170 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0171 state (by omega) (by omega) generator
        else
          if hAt11392 : state.val < 11392 then
            if hAt11200 : state.val < 11200 then
              if hAt11072 : state.val < 11072 then
                exact sourceLabelTransitionProof0172 state (by omega) (by omega) generator
              else
                if hAt11136 : state.val < 11136 then
                  exact sourceLabelTransitionProof0173 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0174 state (by omega) (by omega) generator
            else
              if hAt11264 : state.val < 11264 then
                exact sourceLabelTransitionProof0175 state (by omega) (by omega) generator
              else
                if hAt11328 : state.val < 11328 then
                  exact sourceLabelTransitionProof0176 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0177 state (by omega) (by omega) generator
          else
            if hAt11584 : state.val < 11584 then
              if hAt11456 : state.val < 11456 then
                exact sourceLabelTransitionProof0178 state (by omega) (by omega) generator
              else
                if hAt11520 : state.val < 11520 then
                  exact sourceLabelTransitionProof0179 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0180 state (by omega) (by omega) generator
            else
              if hAt11648 : state.val < 11648 then
                exact sourceLabelTransitionProof0181 state (by omega) (by omega) generator
              else
                if hAt11712 : state.val < 11712 then
                  exact sourceLabelTransitionProof0182 state (by omega) (by omega) generator
                else
                  exact sourceLabelTransitionProof0183 state (by omega) (by omega) generator

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13662.Shards
