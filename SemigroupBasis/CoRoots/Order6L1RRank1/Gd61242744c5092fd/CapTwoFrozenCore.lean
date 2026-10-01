import SemigroupBasis.CoRoots.Order6L1RRank1.Gd61242744c5092fd.CapTwoRouteGeneratedAppend

/-!
# Indexed core relation for the 198 frozen Gd paths

This off-tree generated source names exactly the existing 198 frozen path
schemes.  It adds no coverage theorem.  The relation is closed under word
substitution because every constructor binding is a nonempty `Word`.
-/

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6L1RRank1.Gd61242744c5092fd
namespace CapTwoRTCRoute

open SemigroupBasis

/-- Exact contiguous index type for frozen paths 00000 through 00197. -/
inductive FrozenPathIndex where
  | Path00000 | Path00001 | Path00002 | Path00003
  | Path00004 | Path00005 | Path00006 | Path00007
  | Path00008 | Path00009 | Path00010 | Path00011
  | Path00012 | Path00013 | Path00014 | Path00015
  | Path00016 | Path00017 | Path00018 | Path00019
  | Path00020 | Path00021 | Path00022 | Path00023
  | Path00024 | Path00025 | Path00026 | Path00027
  | Path00028 | Path00029 | Path00030 | Path00031
  | Path00032 | Path00033 | Path00034 | Path00035
  | Path00036 | Path00037 | Path00038 | Path00039
  | Path00040 | Path00041 | Path00042 | Path00043
  | Path00044 | Path00045 | Path00046 | Path00047
  | Path00048 | Path00049 | Path00050 | Path00051
  | Path00052 | Path00053 | Path00054 | Path00055
  | Path00056 | Path00057 | Path00058 | Path00059
  | Path00060 | Path00061 | Path00062 | Path00063
  | Path00064 | Path00065 | Path00066 | Path00067
  | Path00068 | Path00069 | Path00070 | Path00071
  | Path00072 | Path00073 | Path00074 | Path00075
  | Path00076 | Path00077 | Path00078 | Path00079
  | Path00080 | Path00081 | Path00082 | Path00083
  | Path00084 | Path00085 | Path00086 | Path00087
  | Path00088 | Path00089 | Path00090 | Path00091
  | Path00092 | Path00093 | Path00094 | Path00095
  | Path00096 | Path00097 | Path00098 | Path00099
  | Path00100 | Path00101 | Path00102 | Path00103
  | Path00104 | Path00105 | Path00106 | Path00107
  | Path00108 | Path00109 | Path00110 | Path00111
  | Path00112 | Path00113 | Path00114 | Path00115
  | Path00116 | Path00117 | Path00118 | Path00119
  | Path00120 | Path00121 | Path00122 | Path00123
  | Path00124 | Path00125 | Path00126 | Path00127
  | Path00128 | Path00129 | Path00130 | Path00131
  | Path00132 | Path00133 | Path00134 | Path00135
  | Path00136 | Path00137 | Path00138 | Path00139
  | Path00140 | Path00141 | Path00142 | Path00143
  | Path00144 | Path00145 | Path00146 | Path00147
  | Path00148 | Path00149 | Path00150 | Path00151
  | Path00152 | Path00153 | Path00154 | Path00155
  | Path00156 | Path00157 | Path00158 | Path00159
  | Path00160 | Path00161 | Path00162 | Path00163
  | Path00164 | Path00165 | Path00166 | Path00167
  | Path00168 | Path00169 | Path00170 | Path00171
  | Path00172 | Path00173 | Path00174 | Path00175
  | Path00176 | Path00177 | Path00178 | Path00179
  | Path00180 | Path00181 | Path00182 | Path00183
  | Path00184 | Path00185 | Path00186 | Path00187
  | Path00188 | Path00189 | Path00190 | Path00191
  | Path00192 | Path00193 | Path00194 | Path00195
  | Path00196 | Path00197
deriving DecidableEq, Repr

/-- Exact count of the indexed frozen relation. -/
theorem frozenPathIndexCount : 198 = 198 := by
  decide

/-- One forward instance of exactly one frozen path. -/
inductive FrozenCoreStep : FrozenPathIndex → Word Nat → Word Nat → Prop where
  | Path00000
      (V0 : Word Nat) :
      FrozenCoreStep .Path00000
        (V0 ++ (V0 ++ (V0)))
        (V0 ++ (V0))
  | Path00001
      (V0 V1 : Word Nat) :
      FrozenCoreStep .Path00001
        (V0 ++ (V0 ++ (V1 ++ (V0))))
        (V0 ++ (V1 ++ (V0)))
  | Path00002
      (V0 V1 : Word Nat) :
      FrozenCoreStep .Path00002
        (V0 ++ (V1 ++ (V0 ++ (V0))))
        (V0 ++ (V1 ++ (V0)))
  | Path00003
      (V0 V1 : Word Nat) :
      FrozenCoreStep .Path00003
        (V0 ++ (V1 ++ (V0 ++ (V1))))
        (V1 ++ (V0 ++ (V1 ++ (V0))))
  | Path00004
      (V0 V1 : Word Nat) :
      FrozenCoreStep .Path00004
        (V0 ++ (V1 ++ (V1 ++ (V0))))
        (V0 ++ (V1 ++ (V0 ++ (V1))))
  | Path00005
      (V0 V1 : Word Nat) :
      FrozenCoreStep .Path00005
        (V0 ++ (V1 ++ (V1 ++ (V0))))
        (V1 ++ (V0 ++ (V1 ++ (V0))))
  | Path00006
      (V0 V1 : Word Nat) :
      FrozenCoreStep .Path00006
        (V0 ++ (V1 ++ (V1 ++ (V1))))
        (V0 ++ (V1 ++ (V1)))
  | Path00007
      (V0 V1 : Word Nat) :
      FrozenCoreStep .Path00007
        (V0 ++ (V0 ++ (V1 ++ (V1 ++ (V0)))))
        (V0 ++ (V1 ++ (V0 ++ (V1))))
  | Path00008
      (V0 V1 : Word Nat) :
      FrozenCoreStep .Path00008
        (V0 ++ (V0 ++ (V1 ++ (V1 ++ (V0)))))
        (V1 ++ (V0 ++ (V1 ++ (V0))))
  | Path00009
      (V0 V1 : Word Nat) :
      FrozenCoreStep .Path00009
        (V0 ++ (V0 ++ (V1 ++ (V1 ++ (V1)))))
        (V0 ++ (V0 ++ (V1 ++ (V1))))
  | Path00010
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00010
        (V0 ++ (V0 ++ (V1 ++ (V2 ++ (V0)))))
        (V0 ++ (V1 ++ (V2 ++ (V0))))
  | Path00011
      (V0 V1 : Word Nat) :
      FrozenCoreStep .Path00011
        (V0 ++ (V1 ++ (V0 ++ (V1 ++ (V0)))))
        (V0 ++ (V1 ++ (V0 ++ (V1))))
  | Path00012
      (V0 V1 : Word Nat) :
      FrozenCoreStep .Path00012
        (V0 ++ (V1 ++ (V0 ++ (V1 ++ (V1)))))
        (V0 ++ (V1 ++ (V0 ++ (V1))))
  | Path00013
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00013
        (V0 ++ (V1 ++ (V0 ++ (V2 ++ (V0)))))
        (V0 ++ (V1 ++ (V2 ++ (V0))))
  | Path00014
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00014
        (V0 ++ (V1 ++ (V0 ++ (V2 ++ (V1)))))
        (V1 ++ (V0 ++ (V0 ++ (V2 ++ (V1)))))
  | Path00015
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00015
        (V0 ++ (V1 ++ (V1 ++ (V2 ++ (V0)))))
        (V1 ++ (V0 ++ (V1 ++ (V2 ++ (V0)))))
  | Path00016
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00016
        (V0 ++ (V1 ++ (V1 ++ (V2 ++ (V1)))))
        (V0 ++ (V1 ++ (V2 ++ (V1))))
  | Path00017
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00017
        (V0 ++ (V1 ++ (V2 ++ (V0 ++ (V0)))))
        (V0 ++ (V1 ++ (V2 ++ (V0))))
  | Path00018
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00018
        (V0 ++ (V1 ++ (V2 ++ (V0 ++ (V1)))))
        (V0 ++ (V2 ++ (V1 ++ (V0 ++ (V1)))))
  | Path00019
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00019
        (V0 ++ (V1 ++ (V2 ++ (V0 ++ (V1)))))
        (V1 ++ (V0 ++ (V2 ++ (V1 ++ (V0)))))
  | Path00020
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00020
        (V0 ++ (V1 ++ (V2 ++ (V0 ++ (V1)))))
        (V1 ++ (V2 ++ (V0 ++ (V1 ++ (V0)))))
  | Path00021
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00021
        (V0 ++ (V1 ++ (V2 ++ (V0 ++ (V2)))))
        (V0 ++ (V2 ++ (V1 ++ (V0 ++ (V2)))))
  | Path00022
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00022
        (V0 ++ (V1 ++ (V2 ++ (V0 ++ (V2)))))
        (V2 ++ (V0 ++ (V1 ++ (V2 ++ (V0)))))
  | Path00023
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00023
        (V0 ++ (V1 ++ (V2 ++ (V0 ++ (V2)))))
        (V2 ++ (V1 ++ (V0 ++ (V2 ++ (V0)))))
  | Path00024
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00024
        (V0 ++ (V1 ++ (V2 ++ (V1 ++ (V0)))))
        (V0 ++ (V1 ++ (V2 ++ (V0 ++ (V1)))))
  | Path00025
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00025
        (V0 ++ (V1 ++ (V2 ++ (V1 ++ (V0)))))
        (V0 ++ (V2 ++ (V1 ++ (V0 ++ (V1)))))
  | Path00026
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00026
        (V0 ++ (V1 ++ (V2 ++ (V1 ++ (V0)))))
        (V1 ++ (V0 ++ (V2 ++ (V1 ++ (V0)))))
  | Path00027
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00027
        (V0 ++ (V1 ++ (V2 ++ (V1 ++ (V0)))))
        (V1 ++ (V2 ++ (V0 ++ (V1 ++ (V0)))))
  | Path00028
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00028
        (V0 ++ (V1 ++ (V2 ++ (V1 ++ (V1)))))
        (V0 ++ (V1 ++ (V2 ++ (V1))))
  | Path00029
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00029
        (V0 ++ (V1 ++ (V2 ++ (V1 ++ (V2)))))
        (V0 ++ (V2 ++ (V1 ++ (V2 ++ (V1)))))
  | Path00030
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00030
        (V0 ++ (V1 ++ (V2 ++ (V2 ++ (V0)))))
        (V0 ++ (V1 ++ (V2 ++ (V0 ++ (V2)))))
  | Path00031
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00031
        (V0 ++ (V1 ++ (V2 ++ (V2 ++ (V0)))))
        (V0 ++ (V2 ++ (V1 ++ (V0 ++ (V2)))))
  | Path00032
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00032
        (V0 ++ (V1 ++ (V2 ++ (V2 ++ (V0)))))
        (V2 ++ (V0 ++ (V1 ++ (V2 ++ (V0)))))
  | Path00033
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00033
        (V0 ++ (V1 ++ (V2 ++ (V2 ++ (V0)))))
        (V2 ++ (V1 ++ (V0 ++ (V2 ++ (V0)))))
  | Path00034
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00034
        (V0 ++ (V1 ++ (V2 ++ (V2 ++ (V1)))))
        (V0 ++ (V1 ++ (V2 ++ (V1 ++ (V2)))))
  | Path00035
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00035
        (V0 ++ (V1 ++ (V2 ++ (V2 ++ (V1)))))
        (V0 ++ (V2 ++ (V1 ++ (V2 ++ (V1)))))
  | Path00036
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00036
        (V0 ++ (V1 ++ (V2 ++ (V2 ++ (V2)))))
        (V0 ++ (V1 ++ (V2 ++ (V2))))
  | Path00037
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00037
        (V0 ++ (V0 ++ (V1 ++ (V1 ++ (V2 ++ (V0))))))
        (V0 ++ (V1 ++ (V1 ++ (V2 ++ (V0)))))
  | Path00038
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00038
        (V0 ++ (V0 ++ (V1 ++ (V1 ++ (V2 ++ (V0))))))
        (V1 ++ (V0 ++ (V1 ++ (V2 ++ (V0)))))
  | Path00039
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00039
        (V0 ++ (V0 ++ (V1 ++ (V1 ++ (V2 ++ (V1))))))
        (V0 ++ (V0 ++ (V1 ++ (V2 ++ (V1)))))
  | Path00040
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00040
        (V0 ++ (V0 ++ (V1 ++ (V2 ++ (V1 ++ (V0))))))
        (V0 ++ (V1 ++ (V2 ++ (V0 ++ (V1)))))
  | Path00041
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00041
        (V0 ++ (V0 ++ (V1 ++ (V2 ++ (V1 ++ (V0))))))
        (V0 ++ (V2 ++ (V1 ++ (V0 ++ (V1)))))
  | Path00042
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00042
        (V0 ++ (V0 ++ (V1 ++ (V2 ++ (V1 ++ (V0))))))
        (V1 ++ (V0 ++ (V2 ++ (V1 ++ (V0)))))
  | Path00043
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00043
        (V0 ++ (V0 ++ (V1 ++ (V2 ++ (V1 ++ (V0))))))
        (V1 ++ (V2 ++ (V0 ++ (V1 ++ (V0)))))
  | Path00044
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00044
        (V0 ++ (V0 ++ (V1 ++ (V2 ++ (V1 ++ (V1))))))
        (V0 ++ (V0 ++ (V1 ++ (V2 ++ (V1)))))
  | Path00045
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00045
        (V0 ++ (V0 ++ (V1 ++ (V2 ++ (V1 ++ (V2))))))
        (V0 ++ (V0 ++ (V2 ++ (V1 ++ (V2 ++ (V1))))))
  | Path00046
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00046
        (V0 ++ (V0 ++ (V1 ++ (V2 ++ (V2 ++ (V0))))))
        (V0 ++ (V1 ++ (V2 ++ (V0 ++ (V2)))))
  | Path00047
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00047
        (V0 ++ (V0 ++ (V1 ++ (V2 ++ (V2 ++ (V0))))))
        (V0 ++ (V2 ++ (V1 ++ (V0 ++ (V2)))))
  | Path00048
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00048
        (V0 ++ (V0 ++ (V1 ++ (V2 ++ (V2 ++ (V0))))))
        (V2 ++ (V0 ++ (V1 ++ (V2 ++ (V0)))))
  | Path00049
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00049
        (V0 ++ (V0 ++ (V1 ++ (V2 ++ (V2 ++ (V0))))))
        (V2 ++ (V1 ++ (V0 ++ (V2 ++ (V0)))))
  | Path00050
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00050
        (V0 ++ (V0 ++ (V1 ++ (V2 ++ (V2 ++ (V1))))))
        (V0 ++ (V0 ++ (V1 ++ (V2 ++ (V1 ++ (V2))))))
  | Path00051
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00051
        (V0 ++ (V0 ++ (V1 ++ (V2 ++ (V2 ++ (V1))))))
        (V0 ++ (V0 ++ (V2 ++ (V1 ++ (V2 ++ (V1))))))
  | Path00052
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00052
        (V0 ++ (V0 ++ (V1 ++ (V2 ++ (V2 ++ (V2))))))
        (V0 ++ (V0 ++ (V1 ++ (V2 ++ (V2)))))
  | Path00053
      (V0 V1 V2 V3 : Word Nat) :
      FrozenCoreStep .Path00053
        (V0 ++ (V0 ++ (V1 ++ (V2 ++ (V3 ++ (V0))))))
        (V0 ++ (V1 ++ (V2 ++ (V3 ++ (V0)))))
  | Path00054
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00054
        (V0 ++ (V1 ++ (V0 ++ (V1 ++ (V2 ++ (V0))))))
        (V0 ++ (V1 ++ (V1 ++ (V2 ++ (V0)))))
  | Path00055
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00055
        (V0 ++ (V1 ++ (V0 ++ (V1 ++ (V2 ++ (V1))))))
        (V0 ++ (V1 ++ (V0 ++ (V2 ++ (V1)))))
  | Path00056
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00056
        (V0 ++ (V1 ++ (V0 ++ (V2 ++ (V1 ++ (V0))))))
        (V0 ++ (V1 ++ (V2 ++ (V0 ++ (V1)))))
  | Path00057
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00057
        (V0 ++ (V1 ++ (V0 ++ (V2 ++ (V1 ++ (V0))))))
        (V0 ++ (V2 ++ (V1 ++ (V0 ++ (V1)))))
  | Path00058
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00058
        (V0 ++ (V1 ++ (V0 ++ (V2 ++ (V1 ++ (V1))))))
        (V0 ++ (V1 ++ (V0 ++ (V2 ++ (V1)))))
  | Path00059
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00059
        (V0 ++ (V1 ++ (V0 ++ (V2 ++ (V1 ++ (V2))))))
        (V0 ++ (V2 ++ (V0 ++ (V1 ++ (V2 ++ (V1))))))
  | Path00060
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00060
        (V0 ++ (V1 ++ (V0 ++ (V2 ++ (V1 ++ (V2))))))
        (V2 ++ (V0 ++ (V2 ++ (V1 ++ (V0 ++ (V1))))))
  | Path00061
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00061
        (V0 ++ (V1 ++ (V0 ++ (V2 ++ (V2 ++ (V0))))))
        (V0 ++ (V1 ++ (V2 ++ (V0 ++ (V2)))))
  | Path00062
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00062
        (V0 ++ (V1 ++ (V0 ++ (V2 ++ (V2 ++ (V0))))))
        (V0 ++ (V2 ++ (V1 ++ (V0 ++ (V2)))))
  | Path00063
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00063
        (V0 ++ (V1 ++ (V0 ++ (V2 ++ (V2 ++ (V0))))))
        (V2 ++ (V0 ++ (V1 ++ (V2 ++ (V0)))))
  | Path00064
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00064
        (V0 ++ (V1 ++ (V0 ++ (V2 ++ (V2 ++ (V0))))))
        (V2 ++ (V1 ++ (V0 ++ (V2 ++ (V0)))))
  | Path00065
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00065
        (V0 ++ (V1 ++ (V0 ++ (V2 ++ (V2 ++ (V1))))))
        (V0 ++ (V1 ++ (V0 ++ (V2 ++ (V1 ++ (V2))))))
  | Path00066
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00066
        (V0 ++ (V1 ++ (V0 ++ (V2 ++ (V2 ++ (V1))))))
        (V0 ++ (V2 ++ (V0 ++ (V1 ++ (V2 ++ (V1))))))
  | Path00067
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00067
        (V0 ++ (V1 ++ (V0 ++ (V2 ++ (V2 ++ (V1))))))
        (V1 ++ (V0 ++ (V1 ++ (V2 ++ (V0 ++ (V2))))))
  | Path00068
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00068
        (V0 ++ (V1 ++ (V0 ++ (V2 ++ (V2 ++ (V1))))))
        (V1 ++ (V2 ++ (V1 ++ (V0 ++ (V2 ++ (V0))))))
  | Path00069
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00069
        (V0 ++ (V1 ++ (V0 ++ (V2 ++ (V2 ++ (V1))))))
        (V2 ++ (V0 ++ (V2 ++ (V1 ++ (V0 ++ (V1))))))
  | Path00070
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00070
        (V0 ++ (V1 ++ (V0 ++ (V2 ++ (V2 ++ (V1))))))
        (V2 ++ (V1 ++ (V2 ++ (V0 ++ (V1 ++ (V0))))))
  | Path00071
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00071
        (V0 ++ (V1 ++ (V0 ++ (V2 ++ (V2 ++ (V2))))))
        (V0 ++ (V1 ++ (V0 ++ (V2 ++ (V2)))))
  | Path00072
      (V0 V1 V2 V3 : Word Nat) :
      FrozenCoreStep .Path00072
        (V0 ++ (V1 ++ (V0 ++ (V2 ++ (V3 ++ (V0))))))
        (V0 ++ (V1 ++ (V2 ++ (V3 ++ (V0)))))
  | Path00073
      (V0 V1 V2 V3 : Word Nat) :
      FrozenCoreStep .Path00073
        (V0 ++ (V1 ++ (V0 ++ (V2 ++ (V3 ++ (V1))))))
        (V1 ++ (V0 ++ (V0 ++ (V2 ++ (V3 ++ (V1))))))
  | Path00074
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00074
        (V0 ++ (V1 ++ (V1 ++ (V2 ++ (V0 ++ (V0))))))
        (V0 ++ (V1 ++ (V1 ++ (V2 ++ (V0)))))
  | Path00075
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00075
        (V0 ++ (V1 ++ (V1 ++ (V2 ++ (V0 ++ (V1))))))
        (V0 ++ (V1 ++ (V2 ++ (V0 ++ (V1)))))
  | Path00076
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00076
        (V0 ++ (V1 ++ (V1 ++ (V2 ++ (V0 ++ (V1))))))
        (V0 ++ (V2 ++ (V1 ++ (V0 ++ (V1)))))
  | Path00077
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00077
        (V0 ++ (V1 ++ (V1 ++ (V2 ++ (V0 ++ (V2))))))
        (V0 ++ (V1 ++ (V0 ++ (V2 ++ (V1 ++ (V2))))))
  | Path00078
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00078
        (V0 ++ (V1 ++ (V1 ++ (V2 ++ (V0 ++ (V2))))))
        (V0 ++ (V2 ++ (V0 ++ (V1 ++ (V2 ++ (V1))))))
  | Path00079
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00079
        (V0 ++ (V1 ++ (V1 ++ (V2 ++ (V0 ++ (V2))))))
        (V2 ++ (V0 ++ (V2 ++ (V1 ++ (V0 ++ (V1))))))
  | Path00080
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00080
        (V0 ++ (V1 ++ (V1 ++ (V2 ++ (V2 ++ (V0))))))
        (V0 ++ (V1 ++ (V0 ++ (V2 ++ (V1 ++ (V2))))))
  | Path00081
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00081
        (V0 ++ (V1 ++ (V1 ++ (V2 ++ (V2 ++ (V0))))))
        (V0 ++ (V2 ++ (V0 ++ (V1 ++ (V2 ++ (V1))))))
  | Path00082
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00082
        (V0 ++ (V1 ++ (V1 ++ (V2 ++ (V2 ++ (V0))))))
        (V1 ++ (V0 ++ (V1 ++ (V2 ++ (V0 ++ (V2))))))
  | Path00083
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00083
        (V0 ++ (V1 ++ (V1 ++ (V2 ++ (V2 ++ (V0))))))
        (V1 ++ (V2 ++ (V1 ++ (V0 ++ (V2 ++ (V0))))))
  | Path00084
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00084
        (V0 ++ (V1 ++ (V1 ++ (V2 ++ (V2 ++ (V0))))))
        (V2 ++ (V0 ++ (V2 ++ (V1 ++ (V0 ++ (V1))))))
  | Path00085
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00085
        (V0 ++ (V1 ++ (V1 ++ (V2 ++ (V2 ++ (V0))))))
        (V2 ++ (V1 ++ (V2 ++ (V0 ++ (V1 ++ (V0))))))
  | Path00086
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00086
        (V0 ++ (V1 ++ (V1 ++ (V2 ++ (V2 ++ (V1))))))
        (V0 ++ (V1 ++ (V2 ++ (V1 ++ (V2)))))
  | Path00087
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00087
        (V0 ++ (V1 ++ (V1 ++ (V2 ++ (V2 ++ (V1))))))
        (V0 ++ (V2 ++ (V1 ++ (V2 ++ (V1)))))
  | Path00088
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00088
        (V0 ++ (V1 ++ (V1 ++ (V2 ++ (V2 ++ (V2))))))
        (V0 ++ (V1 ++ (V1 ++ (V2 ++ (V2)))))
  | Path00089
      (V0 V1 V2 V3 : Word Nat) :
      FrozenCoreStep .Path00089
        (V0 ++ (V1 ++ (V1 ++ (V2 ++ (V3 ++ (V0))))))
        (V1 ++ (V0 ++ (V1 ++ (V2 ++ (V3 ++ (V0))))))
  | Path00090
      (V0 V1 V2 V3 : Word Nat) :
      FrozenCoreStep .Path00090
        (V0 ++ (V1 ++ (V1 ++ (V2 ++ (V3 ++ (V1))))))
        (V0 ++ (V1 ++ (V2 ++ (V3 ++ (V1)))))
  | Path00091
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00091
        (V0 ++ (V1 ++ (V2 ++ (V0 ++ (V1 ++ (V0))))))
        (V0 ++ (V1 ++ (V2 ++ (V0 ++ (V1)))))
  | Path00092
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00092
        (V0 ++ (V1 ++ (V2 ++ (V0 ++ (V1 ++ (V1))))))
        (V0 ++ (V1 ++ (V2 ++ (V0 ++ (V1)))))
  | Path00093
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00093
        (V0 ++ (V1 ++ (V2 ++ (V0 ++ (V1 ++ (V2))))))
        (V0 ++ (V1 ++ (V0 ++ (V2 ++ (V1 ++ (V2))))))
  | Path00094
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00094
        (V0 ++ (V1 ++ (V2 ++ (V0 ++ (V2 ++ (V0))))))
        (V0 ++ (V1 ++ (V2 ++ (V0 ++ (V2)))))
  | Path00095
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00095
        (V0 ++ (V1 ++ (V2 ++ (V0 ++ (V2 ++ (V1))))))
        (V0 ++ (V1 ++ (V0 ++ (V2 ++ (V1 ++ (V2))))))
  | Path00096
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00096
        (V0 ++ (V1 ++ (V2 ++ (V0 ++ (V2 ++ (V1))))))
        (V1 ++ (V0 ++ (V1 ++ (V2 ++ (V0 ++ (V2))))))
  | Path00097
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00097
        (V0 ++ (V1 ++ (V2 ++ (V0 ++ (V2 ++ (V2))))))
        (V0 ++ (V1 ++ (V2 ++ (V0 ++ (V2)))))
  | Path00098
      (V0 V1 V2 V3 : Word Nat) :
      FrozenCoreStep .Path00098
        (V0 ++ (V1 ++ (V2 ++ (V0 ++ (V3 ++ (V0))))))
        (V0 ++ (V1 ++ (V2 ++ (V3 ++ (V0)))))
  | Path00099
      (V0 V1 V2 V3 : Word Nat) :
      FrozenCoreStep .Path00099
        (V0 ++ (V1 ++ (V2 ++ (V0 ++ (V3 ++ (V1))))))
        (V0 ++ (V2 ++ (V1 ++ (V0 ++ (V3 ++ (V1))))))
  | Path00100
      (V0 V1 V2 V3 : Word Nat) :
      FrozenCoreStep .Path00100
        (V0 ++ (V1 ++ (V2 ++ (V0 ++ (V3 ++ (V1))))))
        (V1 ++ (V0 ++ (V2 ++ (V0 ++ (V3 ++ (V1))))))
  | Path00101
      (V0 V1 V2 V3 : Word Nat) :
      FrozenCoreStep .Path00101
        (V0 ++ (V1 ++ (V2 ++ (V0 ++ (V3 ++ (V1))))))
        (V1 ++ (V2 ++ (V0 ++ (V0 ++ (V3 ++ (V1))))))
  | Path00102
      (V0 V1 V2 V3 : Word Nat) :
      FrozenCoreStep .Path00102
        (V0 ++ (V1 ++ (V2 ++ (V0 ++ (V3 ++ (V2))))))
        (V0 ++ (V2 ++ (V1 ++ (V0 ++ (V3 ++ (V2))))))
  | Path00103
      (V0 V1 V2 V3 : Word Nat) :
      FrozenCoreStep .Path00103
        (V0 ++ (V1 ++ (V2 ++ (V0 ++ (V3 ++ (V2))))))
        (V2 ++ (V0 ++ (V1 ++ (V0 ++ (V3 ++ (V2))))))
  | Path00104
      (V0 V1 V2 V3 : Word Nat) :
      FrozenCoreStep .Path00104
        (V0 ++ (V1 ++ (V2 ++ (V0 ++ (V3 ++ (V2))))))
        (V2 ++ (V1 ++ (V0 ++ (V0 ++ (V3 ++ (V2))))))
  | Path00105
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00105
        (V0 ++ (V1 ++ (V2 ++ (V1 ++ (V2 ++ (V0))))))
        (V0 ++ (V1 ++ (V0 ++ (V2 ++ (V1 ++ (V2))))))
  | Path00106
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00106
        (V0 ++ (V1 ++ (V2 ++ (V1 ++ (V2 ++ (V0))))))
        (V1 ++ (V0 ++ (V1 ++ (V2 ++ (V0 ++ (V2))))))
  | Path00107
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00107
        (V0 ++ (V1 ++ (V2 ++ (V1 ++ (V2 ++ (V0))))))
        (V1 ++ (V2 ++ (V1 ++ (V0 ++ (V2 ++ (V0))))))
  | Path00108
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00108
        (V0 ++ (V1 ++ (V2 ++ (V1 ++ (V2 ++ (V1))))))
        (V0 ++ (V1 ++ (V2 ++ (V1 ++ (V2)))))
  | Path00109
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00109
        (V0 ++ (V1 ++ (V2 ++ (V1 ++ (V2 ++ (V2))))))
        (V0 ++ (V1 ++ (V2 ++ (V1 ++ (V2)))))
  | Path00110
      (V0 V1 V2 V3 : Word Nat) :
      FrozenCoreStep .Path00110
        (V0 ++ (V1 ++ (V2 ++ (V1 ++ (V3 ++ (V0))))))
        (V0 ++ (V2 ++ (V1 ++ (V1 ++ (V3 ++ (V0))))))
  | Path00111
      (V0 V1 V2 V3 : Word Nat) :
      FrozenCoreStep .Path00111
        (V0 ++ (V1 ++ (V2 ++ (V1 ++ (V3 ++ (V0))))))
        (V1 ++ (V0 ++ (V2 ++ (V1 ++ (V3 ++ (V0))))))
  | Path00112
      (V0 V1 V2 V3 : Word Nat) :
      FrozenCoreStep .Path00112
        (V0 ++ (V1 ++ (V2 ++ (V1 ++ (V3 ++ (V0))))))
        (V1 ++ (V2 ++ (V0 ++ (V1 ++ (V3 ++ (V0))))))
  | Path00113
      (V0 V1 V2 V3 : Word Nat) :
      FrozenCoreStep .Path00113
        (V0 ++ (V1 ++ (V2 ++ (V1 ++ (V3 ++ (V1))))))
        (V0 ++ (V1 ++ (V2 ++ (V3 ++ (V1)))))
  | Path00114
      (V0 V1 V2 V3 : Word Nat) :
      FrozenCoreStep .Path00114
        (V0 ++ (V1 ++ (V2 ++ (V1 ++ (V3 ++ (V2))))))
        (V0 ++ (V2 ++ (V1 ++ (V1 ++ (V3 ++ (V2))))))
  | Path00115
      (V0 V1 V2 V3 : Word Nat) :
      FrozenCoreStep .Path00115
        (V0 ++ (V1 ++ (V2 ++ (V2 ++ (V3 ++ (V0))))))
        (V0 ++ (V2 ++ (V1 ++ (V2 ++ (V3 ++ (V0))))))
  | Path00116
      (V0 V1 V2 V3 : Word Nat) :
      FrozenCoreStep .Path00116
        (V0 ++ (V1 ++ (V2 ++ (V2 ++ (V3 ++ (V0))))))
        (V2 ++ (V0 ++ (V1 ++ (V2 ++ (V3 ++ (V0))))))
  | Path00117
      (V0 V1 V2 V3 : Word Nat) :
      FrozenCoreStep .Path00117
        (V0 ++ (V1 ++ (V2 ++ (V2 ++ (V3 ++ (V0))))))
        (V2 ++ (V1 ++ (V0 ++ (V2 ++ (V3 ++ (V0))))))
  | Path00118
      (V0 V1 V2 V3 : Word Nat) :
      FrozenCoreStep .Path00118
        (V0 ++ (V1 ++ (V2 ++ (V2 ++ (V3 ++ (V1))))))
        (V0 ++ (V2 ++ (V1 ++ (V2 ++ (V3 ++ (V1))))))
  | Path00119
      (V0 V1 V2 V3 : Word Nat) :
      FrozenCoreStep .Path00119
        (V0 ++ (V1 ++ (V2 ++ (V2 ++ (V3 ++ (V2))))))
        (V0 ++ (V1 ++ (V2 ++ (V3 ++ (V2)))))
  | Path00120
      (V0 V1 V2 V3 : Word Nat) :
      FrozenCoreStep .Path00120
        (V0 ++ (V1 ++ (V2 ++ (V3 ++ (V0 ++ (V0))))))
        (V0 ++ (V1 ++ (V2 ++ (V3 ++ (V0)))))
  | Path00121
      (V0 V1 V2 V3 : Word Nat) :
      FrozenCoreStep .Path00121
        (V0 ++ (V1 ++ (V2 ++ (V3 ++ (V0 ++ (V1))))))
        (V0 ++ (V2 ++ (V1 ++ (V3 ++ (V0 ++ (V1))))))
  | Path00122
      (V0 V1 V2 V3 : Word Nat) :
      FrozenCoreStep .Path00122
        (V0 ++ (V1 ++ (V2 ++ (V3 ++ (V0 ++ (V1))))))
        (V0 ++ (V2 ++ (V3 ++ (V1 ++ (V0 ++ (V1))))))
  | Path00123
      (V0 V1 V2 V3 : Word Nat) :
      FrozenCoreStep .Path00123
        (V0 ++ (V1 ++ (V2 ++ (V3 ++ (V0 ++ (V1))))))
        (V1 ++ (V0 ++ (V2 ++ (V3 ++ (V1 ++ (V0))))))
  | Path00124
      (V0 V1 V2 V3 : Word Nat) :
      FrozenCoreStep .Path00124
        (V0 ++ (V1 ++ (V2 ++ (V3 ++ (V0 ++ (V1))))))
        (V1 ++ (V2 ++ (V0 ++ (V3 ++ (V1 ++ (V0))))))
  | Path00125
      (V0 V1 V2 V3 : Word Nat) :
      FrozenCoreStep .Path00125
        (V0 ++ (V1 ++ (V2 ++ (V3 ++ (V0 ++ (V1))))))
        (V1 ++ (V2 ++ (V3 ++ (V0 ++ (V1 ++ (V0))))))
  | Path00126
      (V0 V1 V2 V3 : Word Nat) :
      FrozenCoreStep .Path00126
        (V0 ++ (V1 ++ (V2 ++ (V3 ++ (V0 ++ (V2))))))
        (V0 ++ (V1 ++ (V3 ++ (V2 ++ (V0 ++ (V2))))))
  | Path00127
      (V0 V1 V2 V3 : Word Nat) :
      FrozenCoreStep .Path00127
        (V0 ++ (V1 ++ (V2 ++ (V3 ++ (V0 ++ (V2))))))
        (V0 ++ (V2 ++ (V1 ++ (V3 ++ (V0 ++ (V2))))))
  | Path00128
      (V0 V1 V2 V3 : Word Nat) :
      FrozenCoreStep .Path00128
        (V0 ++ (V1 ++ (V2 ++ (V3 ++ (V0 ++ (V2))))))
        (V2 ++ (V0 ++ (V1 ++ (V3 ++ (V2 ++ (V0))))))
  | Path00129
      (V0 V1 V2 V3 : Word Nat) :
      FrozenCoreStep .Path00129
        (V0 ++ (V1 ++ (V2 ++ (V3 ++ (V0 ++ (V2))))))
        (V2 ++ (V1 ++ (V0 ++ (V3 ++ (V2 ++ (V0))))))
  | Path00130
      (V0 V1 V2 V3 : Word Nat) :
      FrozenCoreStep .Path00130
        (V0 ++ (V1 ++ (V2 ++ (V3 ++ (V0 ++ (V2))))))
        (V2 ++ (V1 ++ (V3 ++ (V0 ++ (V2 ++ (V0))))))
  | Path00131
      (V0 V1 V2 V3 : Word Nat) :
      FrozenCoreStep .Path00131
        (V0 ++ (V1 ++ (V2 ++ (V3 ++ (V0 ++ (V3))))))
        (V0 ++ (V1 ++ (V3 ++ (V2 ++ (V0 ++ (V3))))))
  | Path00132
      (V0 V1 V2 V3 : Word Nat) :
      FrozenCoreStep .Path00132
        (V0 ++ (V1 ++ (V2 ++ (V3 ++ (V0 ++ (V3))))))
        (V0 ++ (V3 ++ (V1 ++ (V2 ++ (V0 ++ (V3))))))
  | Path00133
      (V0 V1 V2 V3 : Word Nat) :
      FrozenCoreStep .Path00133
        (V0 ++ (V1 ++ (V2 ++ (V3 ++ (V0 ++ (V3))))))
        (V3 ++ (V0 ++ (V1 ++ (V2 ++ (V3 ++ (V0))))))
  | Path00134
      (V0 V1 V2 V3 : Word Nat) :
      FrozenCoreStep .Path00134
        (V0 ++ (V1 ++ (V2 ++ (V3 ++ (V0 ++ (V3))))))
        (V3 ++ (V1 ++ (V0 ++ (V2 ++ (V3 ++ (V0))))))
  | Path00135
      (V0 V1 V2 V3 : Word Nat) :
      FrozenCoreStep .Path00135
        (V0 ++ (V1 ++ (V2 ++ (V3 ++ (V0 ++ (V3))))))
        (V3 ++ (V1 ++ (V2 ++ (V0 ++ (V3 ++ (V0))))))
  | Path00136
      (V0 V1 V2 V3 : Word Nat) :
      FrozenCoreStep .Path00136
        (V0 ++ (V1 ++ (V2 ++ (V3 ++ (V1 ++ (V0))))))
        (V0 ++ (V1 ++ (V2 ++ (V3 ++ (V0 ++ (V1))))))
  | Path00137
      (V0 V1 V2 V3 : Word Nat) :
      FrozenCoreStep .Path00137
        (V0 ++ (V1 ++ (V2 ++ (V3 ++ (V1 ++ (V0))))))
        (V0 ++ (V2 ++ (V1 ++ (V3 ++ (V0 ++ (V1))))))
  | Path00138
      (V0 V1 V2 V3 : Word Nat) :
      FrozenCoreStep .Path00138
        (V0 ++ (V1 ++ (V2 ++ (V3 ++ (V1 ++ (V0))))))
        (V0 ++ (V2 ++ (V3 ++ (V1 ++ (V0 ++ (V1))))))
  | Path00139
      (V0 V1 V2 V3 : Word Nat) :
      FrozenCoreStep .Path00139
        (V0 ++ (V1 ++ (V2 ++ (V3 ++ (V1 ++ (V0))))))
        (V1 ++ (V0 ++ (V2 ++ (V3 ++ (V1 ++ (V0))))))
  | Path00140
      (V0 V1 V2 V3 : Word Nat) :
      FrozenCoreStep .Path00140
        (V0 ++ (V1 ++ (V2 ++ (V3 ++ (V1 ++ (V0))))))
        (V1 ++ (V2 ++ (V0 ++ (V3 ++ (V1 ++ (V0))))))
  | Path00141
      (V0 V1 V2 V3 : Word Nat) :
      FrozenCoreStep .Path00141
        (V0 ++ (V1 ++ (V2 ++ (V3 ++ (V1 ++ (V0))))))
        (V1 ++ (V2 ++ (V3 ++ (V0 ++ (V1 ++ (V0))))))
  | Path00142
      (V0 V1 V2 V3 : Word Nat) :
      FrozenCoreStep .Path00142
        (V0 ++ (V1 ++ (V2 ++ (V3 ++ (V1 ++ (V1))))))
        (V0 ++ (V1 ++ (V2 ++ (V3 ++ (V1)))))
  | Path00143
      (V0 V1 V2 V3 : Word Nat) :
      FrozenCoreStep .Path00143
        (V0 ++ (V1 ++ (V2 ++ (V3 ++ (V1 ++ (V2))))))
        (V0 ++ (V1 ++ (V3 ++ (V2 ++ (V1 ++ (V2))))))
  | Path00144
      (V0 V1 V2 V3 : Word Nat) :
      FrozenCoreStep .Path00144
        (V0 ++ (V1 ++ (V2 ++ (V3 ++ (V1 ++ (V2))))))
        (V0 ++ (V2 ++ (V1 ++ (V3 ++ (V2 ++ (V1))))))
  | Path00145
      (V0 V1 V2 V3 : Word Nat) :
      FrozenCoreStep .Path00145
        (V0 ++ (V1 ++ (V2 ++ (V3 ++ (V1 ++ (V2))))))
        (V0 ++ (V2 ++ (V3 ++ (V1 ++ (V2 ++ (V1))))))
  | Path00146
      (V0 V1 V2 V3 : Word Nat) :
      FrozenCoreStep .Path00146
        (V0 ++ (V1 ++ (V2 ++ (V3 ++ (V1 ++ (V3))))))
        (V0 ++ (V1 ++ (V3 ++ (V2 ++ (V1 ++ (V3))))))
  | Path00147
      (V0 V1 V2 V3 : Word Nat) :
      FrozenCoreStep .Path00147
        (V0 ++ (V1 ++ (V2 ++ (V3 ++ (V1 ++ (V3))))))
        (V0 ++ (V3 ++ (V1 ++ (V2 ++ (V3 ++ (V1))))))
  | Path00148
      (V0 V1 V2 V3 : Word Nat) :
      FrozenCoreStep .Path00148
        (V0 ++ (V1 ++ (V2 ++ (V3 ++ (V1 ++ (V3))))))
        (V0 ++ (V3 ++ (V2 ++ (V1 ++ (V3 ++ (V1))))))
  | Path00149
      (V0 V1 V2 V3 : Word Nat) :
      FrozenCoreStep .Path00149
        (V0 ++ (V1 ++ (V2 ++ (V3 ++ (V2 ++ (V0))))))
        (V0 ++ (V1 ++ (V2 ++ (V3 ++ (V0 ++ (V2))))))
  | Path00150
      (V0 V1 V2 V3 : Word Nat) :
      FrozenCoreStep .Path00150
        (V0 ++ (V1 ++ (V2 ++ (V3 ++ (V2 ++ (V0))))))
        (V0 ++ (V1 ++ (V3 ++ (V2 ++ (V0 ++ (V2))))))
  | Path00151
      (V0 V1 V2 V3 : Word Nat) :
      FrozenCoreStep .Path00151
        (V0 ++ (V1 ++ (V2 ++ (V3 ++ (V2 ++ (V0))))))
        (V0 ++ (V2 ++ (V1 ++ (V3 ++ (V0 ++ (V2))))))
  | Path00152
      (V0 V1 V2 V3 : Word Nat) :
      FrozenCoreStep .Path00152
        (V0 ++ (V1 ++ (V2 ++ (V3 ++ (V2 ++ (V0))))))
        (V2 ++ (V0 ++ (V1 ++ (V3 ++ (V2 ++ (V0))))))
  | Path00153
      (V0 V1 V2 V3 : Word Nat) :
      FrozenCoreStep .Path00153
        (V0 ++ (V1 ++ (V2 ++ (V3 ++ (V2 ++ (V0))))))
        (V2 ++ (V1 ++ (V0 ++ (V3 ++ (V2 ++ (V0))))))
  | Path00154
      (V0 V1 V2 V3 : Word Nat) :
      FrozenCoreStep .Path00154
        (V0 ++ (V1 ++ (V2 ++ (V3 ++ (V2 ++ (V0))))))
        (V2 ++ (V1 ++ (V3 ++ (V0 ++ (V2 ++ (V0))))))
  | Path00155
      (V0 V1 V2 V3 : Word Nat) :
      FrozenCoreStep .Path00155
        (V0 ++ (V1 ++ (V2 ++ (V3 ++ (V2 ++ (V1))))))
        (V0 ++ (V1 ++ (V2 ++ (V3 ++ (V1 ++ (V2))))))
  | Path00156
      (V0 V1 V2 V3 : Word Nat) :
      FrozenCoreStep .Path00156
        (V0 ++ (V1 ++ (V2 ++ (V3 ++ (V2 ++ (V1))))))
        (V0 ++ (V1 ++ (V3 ++ (V2 ++ (V1 ++ (V2))))))
  | Path00157
      (V0 V1 V2 V3 : Word Nat) :
      FrozenCoreStep .Path00157
        (V0 ++ (V1 ++ (V2 ++ (V3 ++ (V2 ++ (V1))))))
        (V0 ++ (V2 ++ (V1 ++ (V3 ++ (V2 ++ (V1))))))
  | Path00158
      (V0 V1 V2 V3 : Word Nat) :
      FrozenCoreStep .Path00158
        (V0 ++ (V1 ++ (V2 ++ (V3 ++ (V2 ++ (V1))))))
        (V0 ++ (V2 ++ (V3 ++ (V1 ++ (V2 ++ (V1))))))
  | Path00159
      (V0 V1 V2 V3 : Word Nat) :
      FrozenCoreStep .Path00159
        (V0 ++ (V1 ++ (V2 ++ (V3 ++ (V2 ++ (V2))))))
        (V0 ++ (V1 ++ (V2 ++ (V3 ++ (V2)))))
  | Path00160
      (V0 V1 V2 V3 : Word Nat) :
      FrozenCoreStep .Path00160
        (V0 ++ (V1 ++ (V2 ++ (V3 ++ (V2 ++ (V3))))))
        (V0 ++ (V1 ++ (V3 ++ (V2 ++ (V3 ++ (V2))))))
  | Path00161
      (V0 V1 V2 V3 : Word Nat) :
      FrozenCoreStep .Path00161
        (V0 ++ (V1 ++ (V2 ++ (V3 ++ (V3 ++ (V0))))))
        (V0 ++ (V1 ++ (V2 ++ (V3 ++ (V0 ++ (V3))))))
  | Path00162
      (V0 V1 V2 V3 : Word Nat) :
      FrozenCoreStep .Path00162
        (V0 ++ (V1 ++ (V2 ++ (V3 ++ (V3 ++ (V0))))))
        (V0 ++ (V1 ++ (V3 ++ (V2 ++ (V0 ++ (V3))))))
  | Path00163
      (V0 V1 V2 V3 : Word Nat) :
      FrozenCoreStep .Path00163
        (V0 ++ (V1 ++ (V2 ++ (V3 ++ (V3 ++ (V0))))))
        (V0 ++ (V3 ++ (V1 ++ (V2 ++ (V0 ++ (V3))))))
  | Path00164
      (V0 V1 V2 V3 : Word Nat) :
      FrozenCoreStep .Path00164
        (V0 ++ (V1 ++ (V2 ++ (V3 ++ (V3 ++ (V0))))))
        (V3 ++ (V0 ++ (V1 ++ (V2 ++ (V3 ++ (V0))))))
  | Path00165
      (V0 V1 V2 V3 : Word Nat) :
      FrozenCoreStep .Path00165
        (V0 ++ (V1 ++ (V2 ++ (V3 ++ (V3 ++ (V0))))))
        (V3 ++ (V1 ++ (V0 ++ (V2 ++ (V3 ++ (V0))))))
  | Path00166
      (V0 V1 V2 V3 : Word Nat) :
      FrozenCoreStep .Path00166
        (V0 ++ (V1 ++ (V2 ++ (V3 ++ (V3 ++ (V0))))))
        (V3 ++ (V1 ++ (V2 ++ (V0 ++ (V3 ++ (V0))))))
  | Path00167
      (V0 V1 V2 V3 : Word Nat) :
      FrozenCoreStep .Path00167
        (V0 ++ (V1 ++ (V2 ++ (V3 ++ (V3 ++ (V1))))))
        (V0 ++ (V1 ++ (V2 ++ (V3 ++ (V1 ++ (V3))))))
  | Path00168
      (V0 V1 V2 V3 : Word Nat) :
      FrozenCoreStep .Path00168
        (V0 ++ (V1 ++ (V2 ++ (V3 ++ (V3 ++ (V1))))))
        (V0 ++ (V1 ++ (V3 ++ (V2 ++ (V1 ++ (V3))))))
  | Path00169
      (V0 V1 V2 V3 : Word Nat) :
      FrozenCoreStep .Path00169
        (V0 ++ (V1 ++ (V2 ++ (V3 ++ (V3 ++ (V1))))))
        (V0 ++ (V3 ++ (V1 ++ (V2 ++ (V3 ++ (V1))))))
  | Path00170
      (V0 V1 V2 V3 : Word Nat) :
      FrozenCoreStep .Path00170
        (V0 ++ (V1 ++ (V2 ++ (V3 ++ (V3 ++ (V1))))))
        (V0 ++ (V3 ++ (V2 ++ (V1 ++ (V3 ++ (V1))))))
  | Path00171
      (V0 V1 V2 V3 : Word Nat) :
      FrozenCoreStep .Path00171
        (V0 ++ (V1 ++ (V2 ++ (V3 ++ (V3 ++ (V2))))))
        (V0 ++ (V1 ++ (V2 ++ (V3 ++ (V2 ++ (V3))))))
  | Path00172
      (V0 V1 V2 V3 : Word Nat) :
      FrozenCoreStep .Path00172
        (V0 ++ (V1 ++ (V2 ++ (V3 ++ (V3 ++ (V2))))))
        (V0 ++ (V1 ++ (V3 ++ (V2 ++ (V3 ++ (V2))))))
  | Path00173
      (V0 V1 V2 V3 : Word Nat) :
      FrozenCoreStep .Path00173
        (V0 ++ (V1 ++ (V2 ++ (V3 ++ (V3 ++ (V3))))))
        (V0 ++ (V1 ++ (V2 ++ (V3 ++ (V3)))))
  | Path00174
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00174
        (V0 ++ (V0 ++ (V1 ++ (V1 ++ (V2 ++ (V2 ++ (V0)))))))
        (V0 ++ (V1 ++ (V0 ++ (V2 ++ (V1 ++ (V2))))))
  | Path00175
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00175
        (V0 ++ (V0 ++ (V1 ++ (V1 ++ (V2 ++ (V2 ++ (V0)))))))
        (V0 ++ (V2 ++ (V0 ++ (V1 ++ (V2 ++ (V1))))))
  | Path00176
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00176
        (V0 ++ (V0 ++ (V1 ++ (V1 ++ (V2 ++ (V2 ++ (V0)))))))
        (V1 ++ (V0 ++ (V1 ++ (V2 ++ (V0 ++ (V2))))))
  | Path00177
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00177
        (V0 ++ (V0 ++ (V1 ++ (V1 ++ (V2 ++ (V2 ++ (V0)))))))
        (V1 ++ (V2 ++ (V1 ++ (V0 ++ (V2 ++ (V0))))))
  | Path00178
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00178
        (V0 ++ (V0 ++ (V1 ++ (V1 ++ (V2 ++ (V2 ++ (V0)))))))
        (V2 ++ (V0 ++ (V2 ++ (V1 ++ (V0 ++ (V1))))))
  | Path00179
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00179
        (V0 ++ (V0 ++ (V1 ++ (V1 ++ (V2 ++ (V2 ++ (V0)))))))
        (V2 ++ (V1 ++ (V2 ++ (V0 ++ (V1 ++ (V0))))))
  | Path00180
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00180
        (V0 ++ (V0 ++ (V1 ++ (V1 ++ (V2 ++ (V2 ++ (V1)))))))
        (V0 ++ (V0 ++ (V1 ++ (V2 ++ (V1 ++ (V2))))))
  | Path00181
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00181
        (V0 ++ (V0 ++ (V1 ++ (V1 ++ (V2 ++ (V2 ++ (V1)))))))
        (V0 ++ (V0 ++ (V2 ++ (V1 ++ (V2 ++ (V1))))))
  | Path00182
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00182
        (V0 ++ (V0 ++ (V1 ++ (V1 ++ (V2 ++ (V2 ++ (V2)))))))
        (V0 ++ (V0 ++ (V1 ++ (V1 ++ (V2 ++ (V2))))))
  | Path00183
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00183
        (V0 ++ (V0 ++ (V1 ++ (V2 ++ (V1 ++ (V2 ++ (V0)))))))
        (V0 ++ (V1 ++ (V0 ++ (V2 ++ (V1 ++ (V2))))))
  | Path00184
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00184
        (V0 ++ (V0 ++ (V1 ++ (V2 ++ (V1 ++ (V2 ++ (V0)))))))
        (V1 ++ (V0 ++ (V1 ++ (V2 ++ (V0 ++ (V2))))))
  | Path00185
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00185
        (V0 ++ (V0 ++ (V1 ++ (V2 ++ (V1 ++ (V2 ++ (V0)))))))
        (V1 ++ (V2 ++ (V1 ++ (V0 ++ (V2 ++ (V0))))))
  | Path00186
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00186
        (V0 ++ (V0 ++ (V1 ++ (V2 ++ (V1 ++ (V2 ++ (V1)))))))
        (V0 ++ (V0 ++ (V1 ++ (V2 ++ (V1 ++ (V2))))))
  | Path00187
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00187
        (V0 ++ (V0 ++ (V1 ++ (V2 ++ (V1 ++ (V2 ++ (V2)))))))
        (V0 ++ (V0 ++ (V1 ++ (V2 ++ (V1 ++ (V2))))))
  | Path00188
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00188
        (V0 ++ (V1 ++ (V0 ++ (V1 ++ (V2 ++ (V2 ++ (V0)))))))
        (V0 ++ (V1 ++ (V0 ++ (V2 ++ (V1 ++ (V2))))))
  | Path00189
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00189
        (V0 ++ (V1 ++ (V0 ++ (V1 ++ (V2 ++ (V2 ++ (V0)))))))
        (V0 ++ (V2 ++ (V0 ++ (V1 ++ (V2 ++ (V1))))))
  | Path00190
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00190
        (V0 ++ (V1 ++ (V0 ++ (V1 ++ (V2 ++ (V2 ++ (V0)))))))
        (V2 ++ (V0 ++ (V2 ++ (V1 ++ (V0 ++ (V1))))))
  | Path00191
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00191
        (V0 ++ (V1 ++ (V0 ++ (V1 ++ (V2 ++ (V2 ++ (V1)))))))
        (V0 ++ (V1 ++ (V0 ++ (V2 ++ (V1 ++ (V2))))))
  | Path00192
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00192
        (V0 ++ (V1 ++ (V0 ++ (V1 ++ (V2 ++ (V2 ++ (V1)))))))
        (V0 ++ (V2 ++ (V0 ++ (V1 ++ (V2 ++ (V1))))))
  | Path00193
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00193
        (V0 ++ (V1 ++ (V0 ++ (V1 ++ (V2 ++ (V2 ++ (V1)))))))
        (V2 ++ (V0 ++ (V2 ++ (V1 ++ (V0 ++ (V1))))))
  | Path00194
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00194
        (V0 ++ (V1 ++ (V0 ++ (V1 ++ (V2 ++ (V2 ++ (V2)))))))
        (V0 ++ (V1 ++ (V0 ++ (V1 ++ (V2 ++ (V2))))))
  | Path00195
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00195
        (V0 ++ (V1 ++ (V0 ++ (V2 ++ (V1 ++ (V2 ++ (V0)))))))
        (V0 ++ (V1 ++ (V0 ++ (V2 ++ (V1 ++ (V2))))))
  | Path00196
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00196
        (V0 ++ (V1 ++ (V0 ++ (V2 ++ (V1 ++ (V2 ++ (V1)))))))
        (V0 ++ (V1 ++ (V0 ++ (V2 ++ (V1 ++ (V2))))))
  | Path00197
      (V0 V1 V2 : Word Nat) :
      FrozenCoreStep .Path00197
        (V0 ++ (V1 ++ (V0 ++ (V2 ++ (V1 ++ (V2 ++ (V2)))))))
        (V0 ++ (V1 ++ (V0 ++ (V2 ++ (V1 ++ (V2))))))

/-! The path tag stays outside the proof; no proof is eliminated into data. -/
def FrozenCoreAny (left right : Word Nat) : Prop :=
  ∃ index : FrozenPathIndex, FrozenCoreStep index left right

namespace FrozenCoreStep

/-- Every indexed core step is sound in the displayed Gd basis. -/
theorem derives {index : FrozenPathIndex} {left right : Word Nat}
    (step : FrozenCoreStep index left right) :
    Derives basis left right := by
  cases step with
  | Path00000 V0 =>
      exact derivesFrozenPath00000 V0
  | Path00001 V0 V1 =>
      exact derivesFrozenPath00001 V0 V1
  | Path00002 V0 V1 =>
      exact derivesFrozenPath00002 V0 V1
  | Path00003 V0 V1 =>
      exact derivesFrozenPath00003 V0 V1
  | Path00004 V0 V1 =>
      exact derivesFrozenPath00004 V0 V1
  | Path00005 V0 V1 =>
      exact derivesFrozenPath00005 V0 V1
  | Path00006 V0 V1 =>
      exact derivesFrozenPath00006 V0 V1
  | Path00007 V0 V1 =>
      exact derivesFrozenPath00007 V0 V1
  | Path00008 V0 V1 =>
      exact derivesFrozenPath00008 V0 V1
  | Path00009 V0 V1 =>
      exact derivesFrozenPath00009 V0 V1
  | Path00010 V0 V1 V2 =>
      exact derivesFrozenPath00010 V0 V1 V2
  | Path00011 V0 V1 =>
      exact derivesFrozenPath00011 V0 V1
  | Path00012 V0 V1 =>
      exact derivesFrozenPath00012 V0 V1
  | Path00013 V0 V1 V2 =>
      exact derivesFrozenPath00013 V0 V1 V2
  | Path00014 V0 V1 V2 =>
      exact derivesFrozenPath00014 V0 V1 V2
  | Path00015 V0 V1 V2 =>
      exact derivesFrozenPath00015 V0 V1 V2
  | Path00016 V0 V1 V2 =>
      exact derivesFrozenPath00016 V0 V1 V2
  | Path00017 V0 V1 V2 =>
      exact derivesFrozenPath00017 V0 V1 V2
  | Path00018 V0 V1 V2 =>
      exact derivesFrozenPath00018 V0 V1 V2
  | Path00019 V0 V1 V2 =>
      exact derivesFrozenPath00019 V0 V1 V2
  | Path00020 V0 V1 V2 =>
      exact derivesFrozenPath00020 V0 V1 V2
  | Path00021 V0 V1 V2 =>
      exact derivesFrozenPath00021 V0 V1 V2
  | Path00022 V0 V1 V2 =>
      exact derivesFrozenPath00022 V0 V1 V2
  | Path00023 V0 V1 V2 =>
      exact derivesFrozenPath00023 V0 V1 V2
  | Path00024 V0 V1 V2 =>
      exact derivesFrozenPath00024 V0 V1 V2
  | Path00025 V0 V1 V2 =>
      exact derivesFrozenPath00025 V0 V1 V2
  | Path00026 V0 V1 V2 =>
      exact derivesFrozenPath00026 V0 V1 V2
  | Path00027 V0 V1 V2 =>
      exact derivesFrozenPath00027 V0 V1 V2
  | Path00028 V0 V1 V2 =>
      exact derivesFrozenPath00028 V0 V1 V2
  | Path00029 V0 V1 V2 =>
      exact derivesFrozenPath00029 V0 V1 V2
  | Path00030 V0 V1 V2 =>
      exact derivesFrozenPath00030 V0 V1 V2
  | Path00031 V0 V1 V2 =>
      exact derivesFrozenPath00031 V0 V1 V2
  | Path00032 V0 V1 V2 =>
      exact derivesFrozenPath00032 V0 V1 V2
  | Path00033 V0 V1 V2 =>
      exact derivesFrozenPath00033 V0 V1 V2
  | Path00034 V0 V1 V2 =>
      exact derivesFrozenPath00034 V0 V1 V2
  | Path00035 V0 V1 V2 =>
      exact derivesFrozenPath00035 V0 V1 V2
  | Path00036 V0 V1 V2 =>
      exact derivesFrozenPath00036 V0 V1 V2
  | Path00037 V0 V1 V2 =>
      exact derivesFrozenPath00037 V0 V1 V2
  | Path00038 V0 V1 V2 =>
      exact derivesFrozenPath00038 V0 V1 V2
  | Path00039 V0 V1 V2 =>
      exact derivesFrozenPath00039 V0 V1 V2
  | Path00040 V0 V1 V2 =>
      exact derivesFrozenPath00040 V0 V1 V2
  | Path00041 V0 V1 V2 =>
      exact derivesFrozenPath00041 V0 V1 V2
  | Path00042 V0 V1 V2 =>
      exact derivesFrozenPath00042 V0 V1 V2
  | Path00043 V0 V1 V2 =>
      exact derivesFrozenPath00043 V0 V1 V2
  | Path00044 V0 V1 V2 =>
      exact derivesFrozenPath00044 V0 V1 V2
  | Path00045 V0 V1 V2 =>
      exact derivesFrozenPath00045 V0 V1 V2
  | Path00046 V0 V1 V2 =>
      exact derivesFrozenPath00046 V0 V1 V2
  | Path00047 V0 V1 V2 =>
      exact derivesFrozenPath00047 V0 V1 V2
  | Path00048 V0 V1 V2 =>
      exact derivesFrozenPath00048 V0 V1 V2
  | Path00049 V0 V1 V2 =>
      exact derivesFrozenPath00049 V0 V1 V2
  | Path00050 V0 V1 V2 =>
      exact derivesFrozenPath00050 V0 V1 V2
  | Path00051 V0 V1 V2 =>
      exact derivesFrozenPath00051 V0 V1 V2
  | Path00052 V0 V1 V2 =>
      exact derivesFrozenPath00052 V0 V1 V2
  | Path00053 V0 V1 V2 V3 =>
      exact derivesFrozenPath00053 V0 V1 V2 V3
  | Path00054 V0 V1 V2 =>
      exact derivesFrozenPath00054 V0 V1 V2
  | Path00055 V0 V1 V2 =>
      exact derivesFrozenPath00055 V0 V1 V2
  | Path00056 V0 V1 V2 =>
      exact derivesFrozenPath00056 V0 V1 V2
  | Path00057 V0 V1 V2 =>
      exact derivesFrozenPath00057 V0 V1 V2
  | Path00058 V0 V1 V2 =>
      exact derivesFrozenPath00058 V0 V1 V2
  | Path00059 V0 V1 V2 =>
      exact derivesFrozenPath00059 V0 V1 V2
  | Path00060 V0 V1 V2 =>
      exact derivesFrozenPath00060 V0 V1 V2
  | Path00061 V0 V1 V2 =>
      exact derivesFrozenPath00061 V0 V1 V2
  | Path00062 V0 V1 V2 =>
      exact derivesFrozenPath00062 V0 V1 V2
  | Path00063 V0 V1 V2 =>
      exact derivesFrozenPath00063 V0 V1 V2
  | Path00064 V0 V1 V2 =>
      exact derivesFrozenPath00064 V0 V1 V2
  | Path00065 V0 V1 V2 =>
      exact derivesFrozenPath00065 V0 V1 V2
  | Path00066 V0 V1 V2 =>
      exact derivesFrozenPath00066 V0 V1 V2
  | Path00067 V0 V1 V2 =>
      exact derivesFrozenPath00067 V0 V1 V2
  | Path00068 V0 V1 V2 =>
      exact derivesFrozenPath00068 V0 V1 V2
  | Path00069 V0 V1 V2 =>
      exact derivesFrozenPath00069 V0 V1 V2
  | Path00070 V0 V1 V2 =>
      exact derivesFrozenPath00070 V0 V1 V2
  | Path00071 V0 V1 V2 =>
      exact derivesFrozenPath00071 V0 V1 V2
  | Path00072 V0 V1 V2 V3 =>
      exact derivesFrozenPath00072 V0 V1 V2 V3
  | Path00073 V0 V1 V2 V3 =>
      exact derivesFrozenPath00073 V0 V1 V2 V3
  | Path00074 V0 V1 V2 =>
      exact derivesFrozenPath00074 V0 V1 V2
  | Path00075 V0 V1 V2 =>
      exact derivesFrozenPath00075 V0 V1 V2
  | Path00076 V0 V1 V2 =>
      exact derivesFrozenPath00076 V0 V1 V2
  | Path00077 V0 V1 V2 =>
      exact derivesFrozenPath00077 V0 V1 V2
  | Path00078 V0 V1 V2 =>
      exact derivesFrozenPath00078 V0 V1 V2
  | Path00079 V0 V1 V2 =>
      exact derivesFrozenPath00079 V0 V1 V2
  | Path00080 V0 V1 V2 =>
      exact derivesFrozenPath00080 V0 V1 V2
  | Path00081 V0 V1 V2 =>
      exact derivesFrozenPath00081 V0 V1 V2
  | Path00082 V0 V1 V2 =>
      exact derivesFrozenPath00082 V0 V1 V2
  | Path00083 V0 V1 V2 =>
      exact derivesFrozenPath00083 V0 V1 V2
  | Path00084 V0 V1 V2 =>
      exact derivesFrozenPath00084 V0 V1 V2
  | Path00085 V0 V1 V2 =>
      exact derivesFrozenPath00085 V0 V1 V2
  | Path00086 V0 V1 V2 =>
      exact derivesFrozenPath00086 V0 V1 V2
  | Path00087 V0 V1 V2 =>
      exact derivesFrozenPath00087 V0 V1 V2
  | Path00088 V0 V1 V2 =>
      exact derivesFrozenPath00088 V0 V1 V2
  | Path00089 V0 V1 V2 V3 =>
      exact derivesFrozenPath00089 V0 V1 V2 V3
  | Path00090 V0 V1 V2 V3 =>
      exact derivesFrozenPath00090 V0 V1 V2 V3
  | Path00091 V0 V1 V2 =>
      exact derivesFrozenPath00091 V0 V1 V2
  | Path00092 V0 V1 V2 =>
      exact derivesFrozenPath00092 V0 V1 V2
  | Path00093 V0 V1 V2 =>
      exact derivesFrozenPath00093 V0 V1 V2
  | Path00094 V0 V1 V2 =>
      exact derivesFrozenPath00094 V0 V1 V2
  | Path00095 V0 V1 V2 =>
      exact derivesFrozenPath00095 V0 V1 V2
  | Path00096 V0 V1 V2 =>
      exact derivesFrozenPath00096 V0 V1 V2
  | Path00097 V0 V1 V2 =>
      exact derivesFrozenPath00097 V0 V1 V2
  | Path00098 V0 V1 V2 V3 =>
      exact derivesFrozenPath00098 V0 V1 V2 V3
  | Path00099 V0 V1 V2 V3 =>
      exact derivesFrozenPath00099 V0 V1 V2 V3
  | Path00100 V0 V1 V2 V3 =>
      exact derivesFrozenPath00100 V0 V1 V2 V3
  | Path00101 V0 V1 V2 V3 =>
      exact derivesFrozenPath00101 V0 V1 V2 V3
  | Path00102 V0 V1 V2 V3 =>
      exact derivesFrozenPath00102 V0 V1 V2 V3
  | Path00103 V0 V1 V2 V3 =>
      exact derivesFrozenPath00103 V0 V1 V2 V3
  | Path00104 V0 V1 V2 V3 =>
      exact derivesFrozenPath00104 V0 V1 V2 V3
  | Path00105 V0 V1 V2 =>
      exact derivesFrozenPath00105 V0 V1 V2
  | Path00106 V0 V1 V2 =>
      exact derivesFrozenPath00106 V0 V1 V2
  | Path00107 V0 V1 V2 =>
      exact derivesFrozenPath00107 V0 V1 V2
  | Path00108 V0 V1 V2 =>
      exact derivesFrozenPath00108 V0 V1 V2
  | Path00109 V0 V1 V2 =>
      exact derivesFrozenPath00109 V0 V1 V2
  | Path00110 V0 V1 V2 V3 =>
      exact derivesFrozenPath00110 V0 V1 V2 V3
  | Path00111 V0 V1 V2 V3 =>
      exact derivesFrozenPath00111 V0 V1 V2 V3
  | Path00112 V0 V1 V2 V3 =>
      exact derivesFrozenPath00112 V0 V1 V2 V3
  | Path00113 V0 V1 V2 V3 =>
      exact derivesFrozenPath00113 V0 V1 V2 V3
  | Path00114 V0 V1 V2 V3 =>
      exact derivesFrozenPath00114 V0 V1 V2 V3
  | Path00115 V0 V1 V2 V3 =>
      exact derivesFrozenPath00115 V0 V1 V2 V3
  | Path00116 V0 V1 V2 V3 =>
      exact derivesFrozenPath00116 V0 V1 V2 V3
  | Path00117 V0 V1 V2 V3 =>
      exact derivesFrozenPath00117 V0 V1 V2 V3
  | Path00118 V0 V1 V2 V3 =>
      exact derivesFrozenPath00118 V0 V1 V2 V3
  | Path00119 V0 V1 V2 V3 =>
      exact derivesFrozenPath00119 V0 V1 V2 V3
  | Path00120 V0 V1 V2 V3 =>
      exact derivesFrozenPath00120 V0 V1 V2 V3
  | Path00121 V0 V1 V2 V3 =>
      exact derivesFrozenPath00121 V0 V1 V2 V3
  | Path00122 V0 V1 V2 V3 =>
      exact derivesFrozenPath00122 V0 V1 V2 V3
  | Path00123 V0 V1 V2 V3 =>
      exact derivesFrozenPath00123 V0 V1 V2 V3
  | Path00124 V0 V1 V2 V3 =>
      exact derivesFrozenPath00124 V0 V1 V2 V3
  | Path00125 V0 V1 V2 V3 =>
      exact derivesFrozenPath00125 V0 V1 V2 V3
  | Path00126 V0 V1 V2 V3 =>
      exact derivesFrozenPath00126 V0 V1 V2 V3
  | Path00127 V0 V1 V2 V3 =>
      exact derivesFrozenPath00127 V0 V1 V2 V3
  | Path00128 V0 V1 V2 V3 =>
      exact derivesFrozenPath00128 V0 V1 V2 V3
  | Path00129 V0 V1 V2 V3 =>
      exact derivesFrozenPath00129 V0 V1 V2 V3
  | Path00130 V0 V1 V2 V3 =>
      exact derivesFrozenPath00130 V0 V1 V2 V3
  | Path00131 V0 V1 V2 V3 =>
      exact derivesFrozenPath00131 V0 V1 V2 V3
  | Path00132 V0 V1 V2 V3 =>
      exact derivesFrozenPath00132 V0 V1 V2 V3
  | Path00133 V0 V1 V2 V3 =>
      exact derivesFrozenPath00133 V0 V1 V2 V3
  | Path00134 V0 V1 V2 V3 =>
      exact derivesFrozenPath00134 V0 V1 V2 V3
  | Path00135 V0 V1 V2 V3 =>
      exact derivesFrozenPath00135 V0 V1 V2 V3
  | Path00136 V0 V1 V2 V3 =>
      exact derivesFrozenPath00136 V0 V1 V2 V3
  | Path00137 V0 V1 V2 V3 =>
      exact derivesFrozenPath00137 V0 V1 V2 V3
  | Path00138 V0 V1 V2 V3 =>
      exact derivesFrozenPath00138 V0 V1 V2 V3
  | Path00139 V0 V1 V2 V3 =>
      exact derivesFrozenPath00139 V0 V1 V2 V3
  | Path00140 V0 V1 V2 V3 =>
      exact derivesFrozenPath00140 V0 V1 V2 V3
  | Path00141 V0 V1 V2 V3 =>
      exact derivesFrozenPath00141 V0 V1 V2 V3
  | Path00142 V0 V1 V2 V3 =>
      exact derivesFrozenPath00142 V0 V1 V2 V3
  | Path00143 V0 V1 V2 V3 =>
      exact derivesFrozenPath00143 V0 V1 V2 V3
  | Path00144 V0 V1 V2 V3 =>
      exact derivesFrozenPath00144 V0 V1 V2 V3
  | Path00145 V0 V1 V2 V3 =>
      exact derivesFrozenPath00145 V0 V1 V2 V3
  | Path00146 V0 V1 V2 V3 =>
      exact derivesFrozenPath00146 V0 V1 V2 V3
  | Path00147 V0 V1 V2 V3 =>
      exact derivesFrozenPath00147 V0 V1 V2 V3
  | Path00148 V0 V1 V2 V3 =>
      exact derivesFrozenPath00148 V0 V1 V2 V3
  | Path00149 V0 V1 V2 V3 =>
      exact derivesFrozenPath00149 V0 V1 V2 V3
  | Path00150 V0 V1 V2 V3 =>
      exact derivesFrozenPath00150 V0 V1 V2 V3
  | Path00151 V0 V1 V2 V3 =>
      exact derivesFrozenPath00151 V0 V1 V2 V3
  | Path00152 V0 V1 V2 V3 =>
      exact derivesFrozenPath00152 V0 V1 V2 V3
  | Path00153 V0 V1 V2 V3 =>
      exact derivesFrozenPath00153 V0 V1 V2 V3
  | Path00154 V0 V1 V2 V3 =>
      exact derivesFrozenPath00154 V0 V1 V2 V3
  | Path00155 V0 V1 V2 V3 =>
      exact derivesFrozenPath00155 V0 V1 V2 V3
  | Path00156 V0 V1 V2 V3 =>
      exact derivesFrozenPath00156 V0 V1 V2 V3
  | Path00157 V0 V1 V2 V3 =>
      exact derivesFrozenPath00157 V0 V1 V2 V3
  | Path00158 V0 V1 V2 V3 =>
      exact derivesFrozenPath00158 V0 V1 V2 V3
  | Path00159 V0 V1 V2 V3 =>
      exact derivesFrozenPath00159 V0 V1 V2 V3
  | Path00160 V0 V1 V2 V3 =>
      exact derivesFrozenPath00160 V0 V1 V2 V3
  | Path00161 V0 V1 V2 V3 =>
      exact derivesFrozenPath00161 V0 V1 V2 V3
  | Path00162 V0 V1 V2 V3 =>
      exact derivesFrozenPath00162 V0 V1 V2 V3
  | Path00163 V0 V1 V2 V3 =>
      exact derivesFrozenPath00163 V0 V1 V2 V3
  | Path00164 V0 V1 V2 V3 =>
      exact derivesFrozenPath00164 V0 V1 V2 V3
  | Path00165 V0 V1 V2 V3 =>
      exact derivesFrozenPath00165 V0 V1 V2 V3
  | Path00166 V0 V1 V2 V3 =>
      exact derivesFrozenPath00166 V0 V1 V2 V3
  | Path00167 V0 V1 V2 V3 =>
      exact derivesFrozenPath00167 V0 V1 V2 V3
  | Path00168 V0 V1 V2 V3 =>
      exact derivesFrozenPath00168 V0 V1 V2 V3
  | Path00169 V0 V1 V2 V3 =>
      exact derivesFrozenPath00169 V0 V1 V2 V3
  | Path00170 V0 V1 V2 V3 =>
      exact derivesFrozenPath00170 V0 V1 V2 V3
  | Path00171 V0 V1 V2 V3 =>
      exact derivesFrozenPath00171 V0 V1 V2 V3
  | Path00172 V0 V1 V2 V3 =>
      exact derivesFrozenPath00172 V0 V1 V2 V3
  | Path00173 V0 V1 V2 V3 =>
      exact derivesFrozenPath00173 V0 V1 V2 V3
  | Path00174 V0 V1 V2 =>
      exact derivesFrozenPath00174 V0 V1 V2
  | Path00175 V0 V1 V2 =>
      exact derivesFrozenPath00175 V0 V1 V2
  | Path00176 V0 V1 V2 =>
      exact derivesFrozenPath00176 V0 V1 V2
  | Path00177 V0 V1 V2 =>
      exact derivesFrozenPath00177 V0 V1 V2
  | Path00178 V0 V1 V2 =>
      exact derivesFrozenPath00178 V0 V1 V2
  | Path00179 V0 V1 V2 =>
      exact derivesFrozenPath00179 V0 V1 V2
  | Path00180 V0 V1 V2 =>
      exact derivesFrozenPath00180 V0 V1 V2
  | Path00181 V0 V1 V2 =>
      exact derivesFrozenPath00181 V0 V1 V2
  | Path00182 V0 V1 V2 =>
      exact derivesFrozenPath00182 V0 V1 V2
  | Path00183 V0 V1 V2 =>
      exact derivesFrozenPath00183 V0 V1 V2
  | Path00184 V0 V1 V2 =>
      exact derivesFrozenPath00184 V0 V1 V2
  | Path00185 V0 V1 V2 =>
      exact derivesFrozenPath00185 V0 V1 V2
  | Path00186 V0 V1 V2 =>
      exact derivesFrozenPath00186 V0 V1 V2
  | Path00187 V0 V1 V2 =>
      exact derivesFrozenPath00187 V0 V1 V2
  | Path00188 V0 V1 V2 =>
      exact derivesFrozenPath00188 V0 V1 V2
  | Path00189 V0 V1 V2 =>
      exact derivesFrozenPath00189 V0 V1 V2
  | Path00190 V0 V1 V2 =>
      exact derivesFrozenPath00190 V0 V1 V2
  | Path00191 V0 V1 V2 =>
      exact derivesFrozenPath00191 V0 V1 V2
  | Path00192 V0 V1 V2 =>
      exact derivesFrozenPath00192 V0 V1 V2
  | Path00193 V0 V1 V2 =>
      exact derivesFrozenPath00193 V0 V1 V2
  | Path00194 V0 V1 V2 =>
      exact derivesFrozenPath00194 V0 V1 V2
  | Path00195 V0 V1 V2 =>
      exact derivesFrozenPath00195 V0 V1 V2
  | Path00196 V0 V1 V2 =>
      exact derivesFrozenPath00196 V0 V1 V2
  | Path00197 V0 V1 V2 =>
      exact derivesFrozenPath00197 V0 V1 V2

private theorem bind_append
    (left right : Word Nat) (substitution : Nat → Word Nat) :
    (left ++ right).bind substitution =
      left.bind substitution ++ right.bind substitution := by
  apply Word.toList_injective
  simp [Word.toList_bind]

/-- A core step remains the same indexed step after word substitution. -/
theorem subst {index : FrozenPathIndex} {left right : Word Nat}
    (step : FrozenCoreStep index left right)
    (substitution : Nat → Word Nat) :
    FrozenCoreStep index
      (left.bind substitution) (right.bind substitution) := by
  cases step with
  | Path00000 V0 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00000 (V0.bind substitution))
  | Path00001 V0 V1 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00001 (V0.bind substitution) (V1.bind substitution))
  | Path00002 V0 V1 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00002 (V0.bind substitution) (V1.bind substitution))
  | Path00003 V0 V1 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00003 (V0.bind substitution) (V1.bind substitution))
  | Path00004 V0 V1 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00004 (V0.bind substitution) (V1.bind substitution))
  | Path00005 V0 V1 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00005 (V0.bind substitution) (V1.bind substitution))
  | Path00006 V0 V1 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00006 (V0.bind substitution) (V1.bind substitution))
  | Path00007 V0 V1 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00007 (V0.bind substitution) (V1.bind substitution))
  | Path00008 V0 V1 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00008 (V0.bind substitution) (V1.bind substitution))
  | Path00009 V0 V1 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00009 (V0.bind substitution) (V1.bind substitution))
  | Path00010 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00010 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00011 V0 V1 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00011 (V0.bind substitution) (V1.bind substitution))
  | Path00012 V0 V1 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00012 (V0.bind substitution) (V1.bind substitution))
  | Path00013 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00013 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00014 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00014 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00015 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00015 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00016 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00016 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00017 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00017 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00018 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00018 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00019 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00019 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00020 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00020 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00021 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00021 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00022 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00022 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00023 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00023 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00024 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00024 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00025 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00025 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00026 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00026 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00027 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00027 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00028 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00028 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00029 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00029 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00030 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00030 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00031 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00031 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00032 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00032 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00033 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00033 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00034 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00034 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00035 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00035 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00036 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00036 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00037 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00037 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00038 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00038 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00039 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00039 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00040 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00040 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00041 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00041 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00042 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00042 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00043 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00043 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00044 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00044 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00045 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00045 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00046 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00046 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00047 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00047 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00048 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00048 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00049 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00049 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00050 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00050 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00051 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00051 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00052 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00052 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00053 V0 V1 V2 V3 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00053 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution) (V3.bind substitution))
  | Path00054 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00054 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00055 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00055 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00056 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00056 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00057 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00057 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00058 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00058 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00059 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00059 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00060 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00060 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00061 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00061 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00062 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00062 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00063 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00063 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00064 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00064 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00065 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00065 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00066 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00066 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00067 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00067 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00068 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00068 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00069 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00069 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00070 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00070 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00071 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00071 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00072 V0 V1 V2 V3 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00072 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution) (V3.bind substitution))
  | Path00073 V0 V1 V2 V3 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00073 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution) (V3.bind substitution))
  | Path00074 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00074 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00075 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00075 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00076 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00076 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00077 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00077 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00078 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00078 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00079 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00079 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00080 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00080 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00081 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00081 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00082 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00082 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00083 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00083 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00084 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00084 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00085 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00085 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00086 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00086 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00087 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00087 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00088 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00088 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00089 V0 V1 V2 V3 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00089 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution) (V3.bind substitution))
  | Path00090 V0 V1 V2 V3 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00090 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution) (V3.bind substitution))
  | Path00091 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00091 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00092 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00092 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00093 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00093 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00094 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00094 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00095 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00095 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00096 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00096 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00097 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00097 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00098 V0 V1 V2 V3 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00098 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution) (V3.bind substitution))
  | Path00099 V0 V1 V2 V3 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00099 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution) (V3.bind substitution))
  | Path00100 V0 V1 V2 V3 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00100 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution) (V3.bind substitution))
  | Path00101 V0 V1 V2 V3 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00101 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution) (V3.bind substitution))
  | Path00102 V0 V1 V2 V3 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00102 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution) (V3.bind substitution))
  | Path00103 V0 V1 V2 V3 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00103 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution) (V3.bind substitution))
  | Path00104 V0 V1 V2 V3 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00104 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution) (V3.bind substitution))
  | Path00105 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00105 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00106 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00106 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00107 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00107 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00108 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00108 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00109 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00109 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00110 V0 V1 V2 V3 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00110 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution) (V3.bind substitution))
  | Path00111 V0 V1 V2 V3 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00111 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution) (V3.bind substitution))
  | Path00112 V0 V1 V2 V3 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00112 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution) (V3.bind substitution))
  | Path00113 V0 V1 V2 V3 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00113 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution) (V3.bind substitution))
  | Path00114 V0 V1 V2 V3 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00114 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution) (V3.bind substitution))
  | Path00115 V0 V1 V2 V3 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00115 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution) (V3.bind substitution))
  | Path00116 V0 V1 V2 V3 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00116 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution) (V3.bind substitution))
  | Path00117 V0 V1 V2 V3 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00117 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution) (V3.bind substitution))
  | Path00118 V0 V1 V2 V3 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00118 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution) (V3.bind substitution))
  | Path00119 V0 V1 V2 V3 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00119 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution) (V3.bind substitution))
  | Path00120 V0 V1 V2 V3 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00120 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution) (V3.bind substitution))
  | Path00121 V0 V1 V2 V3 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00121 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution) (V3.bind substitution))
  | Path00122 V0 V1 V2 V3 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00122 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution) (V3.bind substitution))
  | Path00123 V0 V1 V2 V3 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00123 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution) (V3.bind substitution))
  | Path00124 V0 V1 V2 V3 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00124 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution) (V3.bind substitution))
  | Path00125 V0 V1 V2 V3 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00125 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution) (V3.bind substitution))
  | Path00126 V0 V1 V2 V3 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00126 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution) (V3.bind substitution))
  | Path00127 V0 V1 V2 V3 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00127 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution) (V3.bind substitution))
  | Path00128 V0 V1 V2 V3 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00128 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution) (V3.bind substitution))
  | Path00129 V0 V1 V2 V3 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00129 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution) (V3.bind substitution))
  | Path00130 V0 V1 V2 V3 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00130 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution) (V3.bind substitution))
  | Path00131 V0 V1 V2 V3 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00131 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution) (V3.bind substitution))
  | Path00132 V0 V1 V2 V3 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00132 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution) (V3.bind substitution))
  | Path00133 V0 V1 V2 V3 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00133 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution) (V3.bind substitution))
  | Path00134 V0 V1 V2 V3 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00134 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution) (V3.bind substitution))
  | Path00135 V0 V1 V2 V3 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00135 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution) (V3.bind substitution))
  | Path00136 V0 V1 V2 V3 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00136 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution) (V3.bind substitution))
  | Path00137 V0 V1 V2 V3 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00137 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution) (V3.bind substitution))
  | Path00138 V0 V1 V2 V3 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00138 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution) (V3.bind substitution))
  | Path00139 V0 V1 V2 V3 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00139 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution) (V3.bind substitution))
  | Path00140 V0 V1 V2 V3 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00140 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution) (V3.bind substitution))
  | Path00141 V0 V1 V2 V3 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00141 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution) (V3.bind substitution))
  | Path00142 V0 V1 V2 V3 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00142 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution) (V3.bind substitution))
  | Path00143 V0 V1 V2 V3 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00143 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution) (V3.bind substitution))
  | Path00144 V0 V1 V2 V3 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00144 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution) (V3.bind substitution))
  | Path00145 V0 V1 V2 V3 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00145 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution) (V3.bind substitution))
  | Path00146 V0 V1 V2 V3 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00146 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution) (V3.bind substitution))
  | Path00147 V0 V1 V2 V3 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00147 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution) (V3.bind substitution))
  | Path00148 V0 V1 V2 V3 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00148 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution) (V3.bind substitution))
  | Path00149 V0 V1 V2 V3 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00149 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution) (V3.bind substitution))
  | Path00150 V0 V1 V2 V3 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00150 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution) (V3.bind substitution))
  | Path00151 V0 V1 V2 V3 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00151 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution) (V3.bind substitution))
  | Path00152 V0 V1 V2 V3 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00152 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution) (V3.bind substitution))
  | Path00153 V0 V1 V2 V3 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00153 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution) (V3.bind substitution))
  | Path00154 V0 V1 V2 V3 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00154 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution) (V3.bind substitution))
  | Path00155 V0 V1 V2 V3 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00155 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution) (V3.bind substitution))
  | Path00156 V0 V1 V2 V3 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00156 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution) (V3.bind substitution))
  | Path00157 V0 V1 V2 V3 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00157 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution) (V3.bind substitution))
  | Path00158 V0 V1 V2 V3 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00158 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution) (V3.bind substitution))
  | Path00159 V0 V1 V2 V3 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00159 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution) (V3.bind substitution))
  | Path00160 V0 V1 V2 V3 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00160 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution) (V3.bind substitution))
  | Path00161 V0 V1 V2 V3 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00161 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution) (V3.bind substitution))
  | Path00162 V0 V1 V2 V3 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00162 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution) (V3.bind substitution))
  | Path00163 V0 V1 V2 V3 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00163 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution) (V3.bind substitution))
  | Path00164 V0 V1 V2 V3 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00164 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution) (V3.bind substitution))
  | Path00165 V0 V1 V2 V3 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00165 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution) (V3.bind substitution))
  | Path00166 V0 V1 V2 V3 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00166 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution) (V3.bind substitution))
  | Path00167 V0 V1 V2 V3 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00167 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution) (V3.bind substitution))
  | Path00168 V0 V1 V2 V3 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00168 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution) (V3.bind substitution))
  | Path00169 V0 V1 V2 V3 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00169 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution) (V3.bind substitution))
  | Path00170 V0 V1 V2 V3 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00170 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution) (V3.bind substitution))
  | Path00171 V0 V1 V2 V3 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00171 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution) (V3.bind substitution))
  | Path00172 V0 V1 V2 V3 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00172 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution) (V3.bind substitution))
  | Path00173 V0 V1 V2 V3 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00173 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution) (V3.bind substitution))
  | Path00174 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00174 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00175 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00175 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00176 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00176 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00177 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00177 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00178 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00178 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00179 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00179 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00180 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00180 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00181 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00181 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00182 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00182 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00183 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00183 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00184 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00184 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00185 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00185 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00186 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00186 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00187 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00187 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00188 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00188 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00189 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00189 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00190 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00190 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00191 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00191 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00192 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00192 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00193 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00193 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00194 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00194 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00195 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00195 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00196 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00196 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))
  | Path00197 V0 V1 V2 =>
      simpa only [bind_append] using
        (FrozenCoreStep.Path00197 (V0.bind substitution) (V1.bind substitution) (V2.bind substitution))

end FrozenCoreStep

namespace FrozenCoreAny

/-- Existentially indexed core steps preserve displayed-basis soundness. -/
theorem derives {left right : Word Nat}
    (step : FrozenCoreAny left right) :
    Derives basis left right := by
  obtain ⟨index, indexedStep⟩ := step
  exact FrozenCoreStep.derives indexedStep

/-- Word substitution preserves the selected index of an existential step. -/
theorem subst {left right : Word Nat}
    (step : FrozenCoreAny left right)
    (substitution : Nat → Word Nat) :
    FrozenCoreAny (left.bind substitution) (right.bind substitution) := by
  obtain ⟨index, indexedStep⟩ := step
  exact ⟨index, FrozenCoreStep.subst indexedStep substitution⟩

end FrozenCoreAny
end CapTwoRTCRoute
end SemigroupBasis.CoRoots.Order6L1RRank1.Gd61242744c5092fd
