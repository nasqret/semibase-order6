import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.Shards.RepresentativeStateProofPart00
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.Shards.RepresentativeStateProofPart01
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.Shards.RepresentativeStateProofPart02
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.Shards.RepresentativeStateProofPart03
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.Shards.RepresentativeStateProofPart04
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.Shards.RepresentativeStateProofPart05
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.Shards.RepresentativeStateProofPart06
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.Shards.RepresentativeStateProofPart07
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.Shards.RepresentativeStateProofPart08
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.Support.Core
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.Shards

set_option maxHeartbeats 2000000 in
theorem representativeState
    (state : Fin 17622)
    : (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeTail state).foldl
        SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.transition
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.generatorState
          (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.representativeHead state)) =
      state := by
  if hAt8832 : state.val < 8832 then
    if hAt4416 : state.val < 4416 then
      if hAt2176 : state.val < 2176 then
        if hAt1088 : state.val < 1088 then
          if hAt512 : state.val < 512 then
            if hAt256 : state.val < 256 then
              if hAt128 : state.val < 128 then
                if hAt64 : state.val < 64 then
                  exact representativeStateProof0000 state (by omega) (by omega)
                else
                  exact representativeStateProof0001 state (by omega) (by omega)
              else
                if hAt192 : state.val < 192 then
                  exact representativeStateProof0002 state (by omega) (by omega)
                else
                  exact representativeStateProof0003 state (by omega) (by omega)
            else
              if hAt384 : state.val < 384 then
                if hAt320 : state.val < 320 then
                  exact representativeStateProof0004 state (by omega) (by omega)
                else
                  exact representativeStateProof0005 state (by omega) (by omega)
              else
                if hAt448 : state.val < 448 then
                  exact representativeStateProof0006 state (by omega) (by omega)
                else
                  exact representativeStateProof0007 state (by omega) (by omega)
          else
            if hAt768 : state.val < 768 then
              if hAt640 : state.val < 640 then
                if hAt576 : state.val < 576 then
                  exact representativeStateProof0008 state (by omega) (by omega)
                else
                  exact representativeStateProof0009 state (by omega) (by omega)
              else
                if hAt704 : state.val < 704 then
                  exact representativeStateProof0010 state (by omega) (by omega)
                else
                  exact representativeStateProof0011 state (by omega) (by omega)
            else
              if hAt896 : state.val < 896 then
                if hAt832 : state.val < 832 then
                  exact representativeStateProof0012 state (by omega) (by omega)
                else
                  exact representativeStateProof0013 state (by omega) (by omega)
              else
                if hAt960 : state.val < 960 then
                  exact representativeStateProof0014 state (by omega) (by omega)
                else
                  if hAt1024 : state.val < 1024 then
                    exact representativeStateProof0015 state (by omega) (by omega)
                  else
                    exact representativeStateProof0016 state (by omega) (by omega)
        else
          if hAt1600 : state.val < 1600 then
            if hAt1344 : state.val < 1344 then
              if hAt1216 : state.val < 1216 then
                if hAt1152 : state.val < 1152 then
                  exact representativeStateProof0017 state (by omega) (by omega)
                else
                  exact representativeStateProof0018 state (by omega) (by omega)
              else
                if hAt1280 : state.val < 1280 then
                  exact representativeStateProof0019 state (by omega) (by omega)
                else
                  exact representativeStateProof0020 state (by omega) (by omega)
            else
              if hAt1472 : state.val < 1472 then
                if hAt1408 : state.val < 1408 then
                  exact representativeStateProof0021 state (by omega) (by omega)
                else
                  exact representativeStateProof0022 state (by omega) (by omega)
              else
                if hAt1536 : state.val < 1536 then
                  exact representativeStateProof0023 state (by omega) (by omega)
                else
                  exact representativeStateProof0024 state (by omega) (by omega)
          else
            if hAt1856 : state.val < 1856 then
              if hAt1728 : state.val < 1728 then
                if hAt1664 : state.val < 1664 then
                  exact representativeStateProof0025 state (by omega) (by omega)
                else
                  exact representativeStateProof0026 state (by omega) (by omega)
              else
                if hAt1792 : state.val < 1792 then
                  exact representativeStateProof0027 state (by omega) (by omega)
                else
                  exact representativeStateProof0028 state (by omega) (by omega)
            else
              if hAt1984 : state.val < 1984 then
                if hAt1920 : state.val < 1920 then
                  exact representativeStateProof0029 state (by omega) (by omega)
                else
                  exact representativeStateProof0030 state (by omega) (by omega)
              else
                if hAt2048 : state.val < 2048 then
                  exact representativeStateProof0031 state (by omega) (by omega)
                else
                  if hAt2112 : state.val < 2112 then
                    exact representativeStateProof0032 state (by omega) (by omega)
                  else
                    exact representativeStateProof0033 state (by omega) (by omega)
      else
        if hAt3264 : state.val < 3264 then
          if hAt2688 : state.val < 2688 then
            if hAt2432 : state.val < 2432 then
              if hAt2304 : state.val < 2304 then
                if hAt2240 : state.val < 2240 then
                  exact representativeStateProof0034 state (by omega) (by omega)
                else
                  exact representativeStateProof0035 state (by omega) (by omega)
              else
                if hAt2368 : state.val < 2368 then
                  exact representativeStateProof0036 state (by omega) (by omega)
                else
                  exact representativeStateProof0037 state (by omega) (by omega)
            else
              if hAt2560 : state.val < 2560 then
                if hAt2496 : state.val < 2496 then
                  exact representativeStateProof0038 state (by omega) (by omega)
                else
                  exact representativeStateProof0039 state (by omega) (by omega)
              else
                if hAt2624 : state.val < 2624 then
                  exact representativeStateProof0040 state (by omega) (by omega)
                else
                  exact representativeStateProof0041 state (by omega) (by omega)
          else
            if hAt2944 : state.val < 2944 then
              if hAt2816 : state.val < 2816 then
                if hAt2752 : state.val < 2752 then
                  exact representativeStateProof0042 state (by omega) (by omega)
                else
                  exact representativeStateProof0043 state (by omega) (by omega)
              else
                if hAt2880 : state.val < 2880 then
                  exact representativeStateProof0044 state (by omega) (by omega)
                else
                  exact representativeStateProof0045 state (by omega) (by omega)
            else
              if hAt3072 : state.val < 3072 then
                if hAt3008 : state.val < 3008 then
                  exact representativeStateProof0046 state (by omega) (by omega)
                else
                  exact representativeStateProof0047 state (by omega) (by omega)
              else
                if hAt3136 : state.val < 3136 then
                  exact representativeStateProof0048 state (by omega) (by omega)
                else
                  if hAt3200 : state.val < 3200 then
                    exact representativeStateProof0049 state (by omega) (by omega)
                  else
                    exact representativeStateProof0050 state (by omega) (by omega)
        else
          if hAt3840 : state.val < 3840 then
            if hAt3520 : state.val < 3520 then
              if hAt3392 : state.val < 3392 then
                if hAt3328 : state.val < 3328 then
                  exact representativeStateProof0051 state (by omega) (by omega)
                else
                  exact representativeStateProof0052 state (by omega) (by omega)
              else
                if hAt3456 : state.val < 3456 then
                  exact representativeStateProof0053 state (by omega) (by omega)
                else
                  exact representativeStateProof0054 state (by omega) (by omega)
            else
              if hAt3648 : state.val < 3648 then
                if hAt3584 : state.val < 3584 then
                  exact representativeStateProof0055 state (by omega) (by omega)
                else
                  exact representativeStateProof0056 state (by omega) (by omega)
              else
                if hAt3712 : state.val < 3712 then
                  exact representativeStateProof0057 state (by omega) (by omega)
                else
                  if hAt3776 : state.val < 3776 then
                    exact representativeStateProof0058 state (by omega) (by omega)
                  else
                    exact representativeStateProof0059 state (by omega) (by omega)
          else
            if hAt4096 : state.val < 4096 then
              if hAt3968 : state.val < 3968 then
                if hAt3904 : state.val < 3904 then
                  exact representativeStateProof0060 state (by omega) (by omega)
                else
                  exact representativeStateProof0061 state (by omega) (by omega)
              else
                if hAt4032 : state.val < 4032 then
                  exact representativeStateProof0062 state (by omega) (by omega)
                else
                  exact representativeStateProof0063 state (by omega) (by omega)
            else
              if hAt4224 : state.val < 4224 then
                if hAt4160 : state.val < 4160 then
                  exact representativeStateProof0064 state (by omega) (by omega)
                else
                  exact representativeStateProof0065 state (by omega) (by omega)
              else
                if hAt4288 : state.val < 4288 then
                  exact representativeStateProof0066 state (by omega) (by omega)
                else
                  if hAt4352 : state.val < 4352 then
                    exact representativeStateProof0067 state (by omega) (by omega)
                  else
                    exact representativeStateProof0068 state (by omega) (by omega)
    else
      if hAt6592 : state.val < 6592 then
        if hAt5504 : state.val < 5504 then
          if hAt4928 : state.val < 4928 then
            if hAt4672 : state.val < 4672 then
              if hAt4544 : state.val < 4544 then
                if hAt4480 : state.val < 4480 then
                  exact representativeStateProof0069 state (by omega) (by omega)
                else
                  exact representativeStateProof0070 state (by omega) (by omega)
              else
                if hAt4608 : state.val < 4608 then
                  exact representativeStateProof0071 state (by omega) (by omega)
                else
                  exact representativeStateProof0072 state (by omega) (by omega)
            else
              if hAt4800 : state.val < 4800 then
                if hAt4736 : state.val < 4736 then
                  exact representativeStateProof0073 state (by omega) (by omega)
                else
                  exact representativeStateProof0074 state (by omega) (by omega)
              else
                if hAt4864 : state.val < 4864 then
                  exact representativeStateProof0075 state (by omega) (by omega)
                else
                  exact representativeStateProof0076 state (by omega) (by omega)
          else
            if hAt5184 : state.val < 5184 then
              if hAt5056 : state.val < 5056 then
                if hAt4992 : state.val < 4992 then
                  exact representativeStateProof0077 state (by omega) (by omega)
                else
                  exact representativeStateProof0078 state (by omega) (by omega)
              else
                if hAt5120 : state.val < 5120 then
                  exact representativeStateProof0079 state (by omega) (by omega)
                else
                  exact representativeStateProof0080 state (by omega) (by omega)
            else
              if hAt5312 : state.val < 5312 then
                if hAt5248 : state.val < 5248 then
                  exact representativeStateProof0081 state (by omega) (by omega)
                else
                  exact representativeStateProof0082 state (by omega) (by omega)
              else
                if hAt5376 : state.val < 5376 then
                  exact representativeStateProof0083 state (by omega) (by omega)
                else
                  if hAt5440 : state.val < 5440 then
                    exact representativeStateProof0084 state (by omega) (by omega)
                  else
                    exact representativeStateProof0085 state (by omega) (by omega)
        else
          if hAt6016 : state.val < 6016 then
            if hAt5760 : state.val < 5760 then
              if hAt5632 : state.val < 5632 then
                if hAt5568 : state.val < 5568 then
                  exact representativeStateProof0086 state (by omega) (by omega)
                else
                  exact representativeStateProof0087 state (by omega) (by omega)
              else
                if hAt5696 : state.val < 5696 then
                  exact representativeStateProof0088 state (by omega) (by omega)
                else
                  exact representativeStateProof0089 state (by omega) (by omega)
            else
              if hAt5888 : state.val < 5888 then
                if hAt5824 : state.val < 5824 then
                  exact representativeStateProof0090 state (by omega) (by omega)
                else
                  exact representativeStateProof0091 state (by omega) (by omega)
              else
                if hAt5952 : state.val < 5952 then
                  exact representativeStateProof0092 state (by omega) (by omega)
                else
                  exact representativeStateProof0093 state (by omega) (by omega)
          else
            if hAt6272 : state.val < 6272 then
              if hAt6144 : state.val < 6144 then
                if hAt6080 : state.val < 6080 then
                  exact representativeStateProof0094 state (by omega) (by omega)
                else
                  exact representativeStateProof0095 state (by omega) (by omega)
              else
                if hAt6208 : state.val < 6208 then
                  exact representativeStateProof0096 state (by omega) (by omega)
                else
                  exact representativeStateProof0097 state (by omega) (by omega)
            else
              if hAt6400 : state.val < 6400 then
                if hAt6336 : state.val < 6336 then
                  exact representativeStateProof0098 state (by omega) (by omega)
                else
                  exact representativeStateProof0099 state (by omega) (by omega)
              else
                if hAt6464 : state.val < 6464 then
                  exact representativeStateProof0100 state (by omega) (by omega)
                else
                  if hAt6528 : state.val < 6528 then
                    exact representativeStateProof0101 state (by omega) (by omega)
                  else
                    exact representativeStateProof0102 state (by omega) (by omega)
      else
        if hAt7680 : state.val < 7680 then
          if hAt7104 : state.val < 7104 then
            if hAt6848 : state.val < 6848 then
              if hAt6720 : state.val < 6720 then
                if hAt6656 : state.val < 6656 then
                  exact representativeStateProof0103 state (by omega) (by omega)
                else
                  exact representativeStateProof0104 state (by omega) (by omega)
              else
                if hAt6784 : state.val < 6784 then
                  exact representativeStateProof0105 state (by omega) (by omega)
                else
                  exact representativeStateProof0106 state (by omega) (by omega)
            else
              if hAt6976 : state.val < 6976 then
                if hAt6912 : state.val < 6912 then
                  exact representativeStateProof0107 state (by omega) (by omega)
                else
                  exact representativeStateProof0108 state (by omega) (by omega)
              else
                if hAt7040 : state.val < 7040 then
                  exact representativeStateProof0109 state (by omega) (by omega)
                else
                  exact representativeStateProof0110 state (by omega) (by omega)
          else
            if hAt7360 : state.val < 7360 then
              if hAt7232 : state.val < 7232 then
                if hAt7168 : state.val < 7168 then
                  exact representativeStateProof0111 state (by omega) (by omega)
                else
                  exact representativeStateProof0112 state (by omega) (by omega)
              else
                if hAt7296 : state.val < 7296 then
                  exact representativeStateProof0113 state (by omega) (by omega)
                else
                  exact representativeStateProof0114 state (by omega) (by omega)
            else
              if hAt7488 : state.val < 7488 then
                if hAt7424 : state.val < 7424 then
                  exact representativeStateProof0115 state (by omega) (by omega)
                else
                  exact representativeStateProof0116 state (by omega) (by omega)
              else
                if hAt7552 : state.val < 7552 then
                  exact representativeStateProof0117 state (by omega) (by omega)
                else
                  if hAt7616 : state.val < 7616 then
                    exact representativeStateProof0118 state (by omega) (by omega)
                  else
                    exact representativeStateProof0119 state (by omega) (by omega)
        else
          if hAt8256 : state.val < 8256 then
            if hAt7936 : state.val < 7936 then
              if hAt7808 : state.val < 7808 then
                if hAt7744 : state.val < 7744 then
                  exact representativeStateProof0120 state (by omega) (by omega)
                else
                  exact representativeStateProof0121 state (by omega) (by omega)
              else
                if hAt7872 : state.val < 7872 then
                  exact representativeStateProof0122 state (by omega) (by omega)
                else
                  exact representativeStateProof0123 state (by omega) (by omega)
            else
              if hAt8064 : state.val < 8064 then
                if hAt8000 : state.val < 8000 then
                  exact representativeStateProof0124 state (by omega) (by omega)
                else
                  exact representativeStateProof0125 state (by omega) (by omega)
              else
                if hAt8128 : state.val < 8128 then
                  exact representativeStateProof0126 state (by omega) (by omega)
                else
                  if hAt8192 : state.val < 8192 then
                    exact representativeStateProof0127 state (by omega) (by omega)
                  else
                    exact representativeStateProof0128 state (by omega) (by omega)
          else
            if hAt8512 : state.val < 8512 then
              if hAt8384 : state.val < 8384 then
                if hAt8320 : state.val < 8320 then
                  exact representativeStateProof0129 state (by omega) (by omega)
                else
                  exact representativeStateProof0130 state (by omega) (by omega)
              else
                if hAt8448 : state.val < 8448 then
                  exact representativeStateProof0131 state (by omega) (by omega)
                else
                  exact representativeStateProof0132 state (by omega) (by omega)
            else
              if hAt8640 : state.val < 8640 then
                if hAt8576 : state.val < 8576 then
                  exact representativeStateProof0133 state (by omega) (by omega)
                else
                  exact representativeStateProof0134 state (by omega) (by omega)
              else
                if hAt8704 : state.val < 8704 then
                  exact representativeStateProof0135 state (by omega) (by omega)
                else
                  if hAt8768 : state.val < 8768 then
                    exact representativeStateProof0136 state (by omega) (by omega)
                  else
                    exact representativeStateProof0137 state (by omega) (by omega)
  else
    if hAt13248 : state.val < 13248 then
      if hAt11008 : state.val < 11008 then
        if hAt9920 : state.val < 9920 then
          if hAt9344 : state.val < 9344 then
            if hAt9088 : state.val < 9088 then
              if hAt8960 : state.val < 8960 then
                if hAt8896 : state.val < 8896 then
                  exact representativeStateProof0138 state (by omega) (by omega)
                else
                  exact representativeStateProof0139 state (by omega) (by omega)
              else
                if hAt9024 : state.val < 9024 then
                  exact representativeStateProof0140 state (by omega) (by omega)
                else
                  exact representativeStateProof0141 state (by omega) (by omega)
            else
              if hAt9216 : state.val < 9216 then
                if hAt9152 : state.val < 9152 then
                  exact representativeStateProof0142 state (by omega) (by omega)
                else
                  exact representativeStateProof0143 state (by omega) (by omega)
              else
                if hAt9280 : state.val < 9280 then
                  exact representativeStateProof0144 state (by omega) (by omega)
                else
                  exact representativeStateProof0145 state (by omega) (by omega)
          else
            if hAt9600 : state.val < 9600 then
              if hAt9472 : state.val < 9472 then
                if hAt9408 : state.val < 9408 then
                  exact representativeStateProof0146 state (by omega) (by omega)
                else
                  exact representativeStateProof0147 state (by omega) (by omega)
              else
                if hAt9536 : state.val < 9536 then
                  exact representativeStateProof0148 state (by omega) (by omega)
                else
                  exact representativeStateProof0149 state (by omega) (by omega)
            else
              if hAt9728 : state.val < 9728 then
                if hAt9664 : state.val < 9664 then
                  exact representativeStateProof0150 state (by omega) (by omega)
                else
                  exact representativeStateProof0151 state (by omega) (by omega)
              else
                if hAt9792 : state.val < 9792 then
                  exact representativeStateProof0152 state (by omega) (by omega)
                else
                  if hAt9856 : state.val < 9856 then
                    exact representativeStateProof0153 state (by omega) (by omega)
                  else
                    exact representativeStateProof0154 state (by omega) (by omega)
        else
          if hAt10432 : state.val < 10432 then
            if hAt10176 : state.val < 10176 then
              if hAt10048 : state.val < 10048 then
                if hAt9984 : state.val < 9984 then
                  exact representativeStateProof0155 state (by omega) (by omega)
                else
                  exact representativeStateProof0156 state (by omega) (by omega)
              else
                if hAt10112 : state.val < 10112 then
                  exact representativeStateProof0157 state (by omega) (by omega)
                else
                  exact representativeStateProof0158 state (by omega) (by omega)
            else
              if hAt10304 : state.val < 10304 then
                if hAt10240 : state.val < 10240 then
                  exact representativeStateProof0159 state (by omega) (by omega)
                else
                  exact representativeStateProof0160 state (by omega) (by omega)
              else
                if hAt10368 : state.val < 10368 then
                  exact representativeStateProof0161 state (by omega) (by omega)
                else
                  exact representativeStateProof0162 state (by omega) (by omega)
          else
            if hAt10688 : state.val < 10688 then
              if hAt10560 : state.val < 10560 then
                if hAt10496 : state.val < 10496 then
                  exact representativeStateProof0163 state (by omega) (by omega)
                else
                  exact representativeStateProof0164 state (by omega) (by omega)
              else
                if hAt10624 : state.val < 10624 then
                  exact representativeStateProof0165 state (by omega) (by omega)
                else
                  exact representativeStateProof0166 state (by omega) (by omega)
            else
              if hAt10816 : state.val < 10816 then
                if hAt10752 : state.val < 10752 then
                  exact representativeStateProof0167 state (by omega) (by omega)
                else
                  exact representativeStateProof0168 state (by omega) (by omega)
              else
                if hAt10880 : state.val < 10880 then
                  exact representativeStateProof0169 state (by omega) (by omega)
                else
                  if hAt10944 : state.val < 10944 then
                    exact representativeStateProof0170 state (by omega) (by omega)
                  else
                    exact representativeStateProof0171 state (by omega) (by omega)
      else
        if hAt12096 : state.val < 12096 then
          if hAt11520 : state.val < 11520 then
            if hAt11264 : state.val < 11264 then
              if hAt11136 : state.val < 11136 then
                if hAt11072 : state.val < 11072 then
                  exact representativeStateProof0172 state (by omega) (by omega)
                else
                  exact representativeStateProof0173 state (by omega) (by omega)
              else
                if hAt11200 : state.val < 11200 then
                  exact representativeStateProof0174 state (by omega) (by omega)
                else
                  exact representativeStateProof0175 state (by omega) (by omega)
            else
              if hAt11392 : state.val < 11392 then
                if hAt11328 : state.val < 11328 then
                  exact representativeStateProof0176 state (by omega) (by omega)
                else
                  exact representativeStateProof0177 state (by omega) (by omega)
              else
                if hAt11456 : state.val < 11456 then
                  exact representativeStateProof0178 state (by omega) (by omega)
                else
                  exact representativeStateProof0179 state (by omega) (by omega)
          else
            if hAt11776 : state.val < 11776 then
              if hAt11648 : state.val < 11648 then
                if hAt11584 : state.val < 11584 then
                  exact representativeStateProof0180 state (by omega) (by omega)
                else
                  exact representativeStateProof0181 state (by omega) (by omega)
              else
                if hAt11712 : state.val < 11712 then
                  exact representativeStateProof0182 state (by omega) (by omega)
                else
                  exact representativeStateProof0183 state (by omega) (by omega)
            else
              if hAt11904 : state.val < 11904 then
                if hAt11840 : state.val < 11840 then
                  exact representativeStateProof0184 state (by omega) (by omega)
                else
                  exact representativeStateProof0185 state (by omega) (by omega)
              else
                if hAt11968 : state.val < 11968 then
                  exact representativeStateProof0186 state (by omega) (by omega)
                else
                  if hAt12032 : state.val < 12032 then
                    exact representativeStateProof0187 state (by omega) (by omega)
                  else
                    exact representativeStateProof0188 state (by omega) (by omega)
        else
          if hAt12672 : state.val < 12672 then
            if hAt12352 : state.val < 12352 then
              if hAt12224 : state.val < 12224 then
                if hAt12160 : state.val < 12160 then
                  exact representativeStateProof0189 state (by omega) (by omega)
                else
                  exact representativeStateProof0190 state (by omega) (by omega)
              else
                if hAt12288 : state.val < 12288 then
                  exact representativeStateProof0191 state (by omega) (by omega)
                else
                  exact representativeStateProof0192 state (by omega) (by omega)
            else
              if hAt12480 : state.val < 12480 then
                if hAt12416 : state.val < 12416 then
                  exact representativeStateProof0193 state (by omega) (by omega)
                else
                  exact representativeStateProof0194 state (by omega) (by omega)
              else
                if hAt12544 : state.val < 12544 then
                  exact representativeStateProof0195 state (by omega) (by omega)
                else
                  if hAt12608 : state.val < 12608 then
                    exact representativeStateProof0196 state (by omega) (by omega)
                  else
                    exact representativeStateProof0197 state (by omega) (by omega)
          else
            if hAt12928 : state.val < 12928 then
              if hAt12800 : state.val < 12800 then
                if hAt12736 : state.val < 12736 then
                  exact representativeStateProof0198 state (by omega) (by omega)
                else
                  exact representativeStateProof0199 state (by omega) (by omega)
              else
                if hAt12864 : state.val < 12864 then
                  exact representativeStateProof0200 state (by omega) (by omega)
                else
                  exact representativeStateProof0201 state (by omega) (by omega)
            else
              if hAt13056 : state.val < 13056 then
                if hAt12992 : state.val < 12992 then
                  exact representativeStateProof0202 state (by omega) (by omega)
                else
                  exact representativeStateProof0203 state (by omega) (by omega)
              else
                if hAt13120 : state.val < 13120 then
                  exact representativeStateProof0204 state (by omega) (by omega)
                else
                  if hAt13184 : state.val < 13184 then
                    exact representativeStateProof0205 state (by omega) (by omega)
                  else
                    exact representativeStateProof0206 state (by omega) (by omega)
    else
      if hAt15424 : state.val < 15424 then
        if hAt14336 : state.val < 14336 then
          if hAt13760 : state.val < 13760 then
            if hAt13504 : state.val < 13504 then
              if hAt13376 : state.val < 13376 then
                if hAt13312 : state.val < 13312 then
                  exact representativeStateProof0207 state (by omega) (by omega)
                else
                  exact representativeStateProof0208 state (by omega) (by omega)
              else
                if hAt13440 : state.val < 13440 then
                  exact representativeStateProof0209 state (by omega) (by omega)
                else
                  exact representativeStateProof0210 state (by omega) (by omega)
            else
              if hAt13632 : state.val < 13632 then
                if hAt13568 : state.val < 13568 then
                  exact representativeStateProof0211 state (by omega) (by omega)
                else
                  exact representativeStateProof0212 state (by omega) (by omega)
              else
                if hAt13696 : state.val < 13696 then
                  exact representativeStateProof0213 state (by omega) (by omega)
                else
                  exact representativeStateProof0214 state (by omega) (by omega)
          else
            if hAt14016 : state.val < 14016 then
              if hAt13888 : state.val < 13888 then
                if hAt13824 : state.val < 13824 then
                  exact representativeStateProof0215 state (by omega) (by omega)
                else
                  exact representativeStateProof0216 state (by omega) (by omega)
              else
                if hAt13952 : state.val < 13952 then
                  exact representativeStateProof0217 state (by omega) (by omega)
                else
                  exact representativeStateProof0218 state (by omega) (by omega)
            else
              if hAt14144 : state.val < 14144 then
                if hAt14080 : state.val < 14080 then
                  exact representativeStateProof0219 state (by omega) (by omega)
                else
                  exact representativeStateProof0220 state (by omega) (by omega)
              else
                if hAt14208 : state.val < 14208 then
                  exact representativeStateProof0221 state (by omega) (by omega)
                else
                  if hAt14272 : state.val < 14272 then
                    exact representativeStateProof0222 state (by omega) (by omega)
                  else
                    exact representativeStateProof0223 state (by omega) (by omega)
        else
          if hAt14848 : state.val < 14848 then
            if hAt14592 : state.val < 14592 then
              if hAt14464 : state.val < 14464 then
                if hAt14400 : state.val < 14400 then
                  exact representativeStateProof0224 state (by omega) (by omega)
                else
                  exact representativeStateProof0225 state (by omega) (by omega)
              else
                if hAt14528 : state.val < 14528 then
                  exact representativeStateProof0226 state (by omega) (by omega)
                else
                  exact representativeStateProof0227 state (by omega) (by omega)
            else
              if hAt14720 : state.val < 14720 then
                if hAt14656 : state.val < 14656 then
                  exact representativeStateProof0228 state (by omega) (by omega)
                else
                  exact representativeStateProof0229 state (by omega) (by omega)
              else
                if hAt14784 : state.val < 14784 then
                  exact representativeStateProof0230 state (by omega) (by omega)
                else
                  exact representativeStateProof0231 state (by omega) (by omega)
          else
            if hAt15104 : state.val < 15104 then
              if hAt14976 : state.val < 14976 then
                if hAt14912 : state.val < 14912 then
                  exact representativeStateProof0232 state (by omega) (by omega)
                else
                  exact representativeStateProof0233 state (by omega) (by omega)
              else
                if hAt15040 : state.val < 15040 then
                  exact representativeStateProof0234 state (by omega) (by omega)
                else
                  exact representativeStateProof0235 state (by omega) (by omega)
            else
              if hAt15232 : state.val < 15232 then
                if hAt15168 : state.val < 15168 then
                  exact representativeStateProof0236 state (by omega) (by omega)
                else
                  exact representativeStateProof0237 state (by omega) (by omega)
              else
                if hAt15296 : state.val < 15296 then
                  exact representativeStateProof0238 state (by omega) (by omega)
                else
                  if hAt15360 : state.val < 15360 then
                    exact representativeStateProof0239 state (by omega) (by omega)
                  else
                    exact representativeStateProof0240 state (by omega) (by omega)
      else
        if hAt16512 : state.val < 16512 then
          if hAt15936 : state.val < 15936 then
            if hAt15680 : state.val < 15680 then
              if hAt15552 : state.val < 15552 then
                if hAt15488 : state.val < 15488 then
                  exact representativeStateProof0241 state (by omega) (by omega)
                else
                  exact representativeStateProof0242 state (by omega) (by omega)
              else
                if hAt15616 : state.val < 15616 then
                  exact representativeStateProof0243 state (by omega) (by omega)
                else
                  exact representativeStateProof0244 state (by omega) (by omega)
            else
              if hAt15808 : state.val < 15808 then
                if hAt15744 : state.val < 15744 then
                  exact representativeStateProof0245 state (by omega) (by omega)
                else
                  exact representativeStateProof0246 state (by omega) (by omega)
              else
                if hAt15872 : state.val < 15872 then
                  exact representativeStateProof0247 state (by omega) (by omega)
                else
                  exact representativeStateProof0248 state (by omega) (by omega)
          else
            if hAt16192 : state.val < 16192 then
              if hAt16064 : state.val < 16064 then
                if hAt16000 : state.val < 16000 then
                  exact representativeStateProof0249 state (by omega) (by omega)
                else
                  exact representativeStateProof0250 state (by omega) (by omega)
              else
                if hAt16128 : state.val < 16128 then
                  exact representativeStateProof0251 state (by omega) (by omega)
                else
                  exact representativeStateProof0252 state (by omega) (by omega)
            else
              if hAt16320 : state.val < 16320 then
                if hAt16256 : state.val < 16256 then
                  exact representativeStateProof0253 state (by omega) (by omega)
                else
                  exact representativeStateProof0254 state (by omega) (by omega)
              else
                if hAt16384 : state.val < 16384 then
                  exact representativeStateProof0255 state (by omega) (by omega)
                else
                  if hAt16448 : state.val < 16448 then
                    exact representativeStateProof0256 state (by omega) (by omega)
                  else
                    exact representativeStateProof0257 state (by omega) (by omega)
        else
          if hAt17088 : state.val < 17088 then
            if hAt16768 : state.val < 16768 then
              if hAt16640 : state.val < 16640 then
                if hAt16576 : state.val < 16576 then
                  exact representativeStateProof0258 state (by omega) (by omega)
                else
                  exact representativeStateProof0259 state (by omega) (by omega)
              else
                if hAt16704 : state.val < 16704 then
                  exact representativeStateProof0260 state (by omega) (by omega)
                else
                  exact representativeStateProof0261 state (by omega) (by omega)
            else
              if hAt16896 : state.val < 16896 then
                if hAt16832 : state.val < 16832 then
                  exact representativeStateProof0262 state (by omega) (by omega)
                else
                  exact representativeStateProof0263 state (by omega) (by omega)
              else
                if hAt16960 : state.val < 16960 then
                  exact representativeStateProof0264 state (by omega) (by omega)
                else
                  if hAt17024 : state.val < 17024 then
                    exact representativeStateProof0265 state (by omega) (by omega)
                  else
                    exact representativeStateProof0266 state (by omega) (by omega)
          else
            if hAt17344 : state.val < 17344 then
              if hAt17216 : state.val < 17216 then
                if hAt17152 : state.val < 17152 then
                  exact representativeStateProof0267 state (by omega) (by omega)
                else
                  exact representativeStateProof0268 state (by omega) (by omega)
              else
                if hAt17280 : state.val < 17280 then
                  exact representativeStateProof0269 state (by omega) (by omega)
                else
                  exact representativeStateProof0270 state (by omega) (by omega)
            else
              if hAt17472 : state.val < 17472 then
                if hAt17408 : state.val < 17408 then
                  exact representativeStateProof0271 state (by omega) (by omega)
                else
                  exact representativeStateProof0272 state (by omega) (by omega)
              else
                if hAt17536 : state.val < 17536 then
                  exact representativeStateProof0273 state (by omega) (by omega)
                else
                  if hAt17600 : state.val < 17600 then
                    exact representativeStateProof0274 state (by omega) (by omega)
                  else
                    exact representativeStateProof0275 state (by omega) (by omega)

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.Shards
