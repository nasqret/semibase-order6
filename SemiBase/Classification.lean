import SemiBase.Catalogue.Order6
import SemiBase.Census.Shard001
import SemiBase.Census.Shard002
import SemiBase.Census.Shard003
import SemiBase.Census.Shard004
import SemiBase.Census.Shard005
import SemiBase.Census.Shard006
import SemiBase.Census.Shard007
import SemiBase.Census.Shard008
import SemiBase.Census.Shard009
import SemiBase.Census.Shard010
import SemiBase.Census.Shard011
import SemiBase.Census.Shard012
import SemiBase.Census.Shard013
import SemiBase.Census.Shard014
import SemiBase.Census.Shard015
import SemiBase.Census.Shard016
import SemiBase.Census.Shard017
import SemiBase.Census.Shard018
import SemiBase.Census.Shard019
import SemiBase.Census.Shard020
import SemiBase.Census.Shard021
import SemiBase.Census.Shard022
import SemiBase.Census.Shard023
import SemiBase.Census.Shard024
import SemiBase.Census.Shard025
import SemiBase.Census.Shard026
import SemiBase.Census.Shard027
import SemiBase.Census.Shard028
import SemiBase.Census.Shard029
import SemiBase.Census.Shard030
import SemiBase.Census.Shard031
import SemiBase.Census.Shard032
import SemiBase.Census.Shard033
import SemiBase.Census.Shard034
import SemiBase.Census.Shard035
import SemiBase.Census.Shard036
import SemiBase.Census.Shard037
import SemiBase.Census.Shard038
import SemiBase.Census.Shard039
import SemiBase.Census.Shard040
import SemiBase.Census.Shard041
import SemiBase.Census.Shard042
import SemiBase.Census.Shard043
import SemiBase.Census.Shard044
import SemiBase.Census.Shard045
import SemiBase.Census.Shard046
import SemiBase.Census.Shard047
import SemiBase.Census.Shard048
import SemiBase.Census.Shard049
import SemiBase.Census.Shard050
import SemiBase.Census.Shard051
import SemiBase.Census.Shard052
import SemiBase.Census.Shard053
import SemiBase.Census.Shard054
import SemiBase.Census.Shard055
import SemiBase.Census.Shard056
import SemiBase.Census.Shard057
import SemiBase.Census.Shard058
import SemiBase.Census.Shard059
import SemiBase.Census.Shard060
import SemiBase.Census.Shard061
import SemiBase.Census.Shard062
import SemiBase.Census.Shard063
import SemiBase.Census.Shard064
import SemiBase.Census.Shard065
import SemiBase.Census.Shard066
import SemiBase.Census.Shard067
import SemiBase.Census.Shard068
import SemiBase.Census.Shard069
import SemiBase.Census.Shard070
import SemiBase.Census.Shard071
import SemiBase.Census.Shard072
import SemiBase.Census.Shard073
import SemiBase.Census.Shard074
import SemiBase.Census.Shard075
import SemiBase.Census.Shard076
import SemiBase.Census.Shard077
import SemiBase.Census.Shard078
import SemiBase.Census.Shard079
import SemiBase.Census.Shard080
import SemiBase.Census.Shard081
import SemiBase.Census.Shard082
import SemiBase.Census.Shard083
import SemiBase.Census.Shard084
import SemiBase.Census.Shard085
import SemiBase.Census.Shard086
import SemiBase.Census.Shard087
import SemiBase.Census.Shard088
import SemiBase.Census.Shard089
import SemiBase.Census.Shard090
import SemiBase.Census.Shard091
import SemiBase.Census.Shard092
import SemiBase.Census.Shard093
import SemiBase.Census.Shard094
import SemiBase.Census.Shard095
import SemiBase.Census.Shard096
import SemiBase.Census.Shard097
import SemiBase.Census.Shard098
import SemiBase.Census.Shard099
import SemiBase.Census.Shard100
import SemiBase.Census.Shard101
import SemiBase.Census.Shard102
import SemiBase.Census.Shard103
import SemiBase.Census.Shard104
import SemiBase.Census.Shard105
import SemiBase.Census.Shard106
import SemiBase.Census.Shard107

/-!
# The classification of the semigroups of order six by finite basability
-/

set_option maxRecDepth 8192

namespace SemiBase

theorem allClassified_order6 : AllClassified Catalogue.order6 :=
  AllClassified.append Census.shard001 <|
  AllClassified.append Census.shard002 <|
  AllClassified.append Census.shard003 <|
  AllClassified.append Census.shard004 <|
  AllClassified.append Census.shard005 <|
  AllClassified.append Census.shard006 <|
  AllClassified.append Census.shard007 <|
  AllClassified.append Census.shard008 <|
  AllClassified.append Census.shard009 <|
  AllClassified.append Census.shard010 <|
  AllClassified.append Census.shard011 <|
  AllClassified.append Census.shard012 <|
  AllClassified.append Census.shard013 <|
  AllClassified.append Census.shard014 <|
  AllClassified.append Census.shard015 <|
  AllClassified.append Census.shard016 <|
  AllClassified.append Census.shard017 <|
  AllClassified.append Census.shard018 <|
  AllClassified.append Census.shard019 <|
  AllClassified.append Census.shard020 <|
  AllClassified.append Census.shard021 <|
  AllClassified.append Census.shard022 <|
  AllClassified.append Census.shard023 <|
  AllClassified.append Census.shard024 <|
  AllClassified.append Census.shard025 <|
  AllClassified.append Census.shard026 <|
  AllClassified.append Census.shard027 <|
  AllClassified.append Census.shard028 <|
  AllClassified.append Census.shard029 <|
  AllClassified.append Census.shard030 <|
  AllClassified.append Census.shard031 <|
  AllClassified.append Census.shard032 <|
  AllClassified.append Census.shard033 <|
  AllClassified.append Census.shard034 <|
  AllClassified.append Census.shard035 <|
  AllClassified.append Census.shard036 <|
  AllClassified.append Census.shard037 <|
  AllClassified.append Census.shard038 <|
  AllClassified.append Census.shard039 <|
  AllClassified.append Census.shard040 <|
  AllClassified.append Census.shard041 <|
  AllClassified.append Census.shard042 <|
  AllClassified.append Census.shard043 <|
  AllClassified.append Census.shard044 <|
  AllClassified.append Census.shard045 <|
  AllClassified.append Census.shard046 <|
  AllClassified.append Census.shard047 <|
  AllClassified.append Census.shard048 <|
  AllClassified.append Census.shard049 <|
  AllClassified.append Census.shard050 <|
  AllClassified.append Census.shard051 <|
  AllClassified.append Census.shard052 <|
  AllClassified.append Census.shard053 <|
  AllClassified.append Census.shard054 <|
  AllClassified.append Census.shard055 <|
  AllClassified.append Census.shard056 <|
  AllClassified.append Census.shard057 <|
  AllClassified.append Census.shard058 <|
  AllClassified.append Census.shard059 <|
  AllClassified.append Census.shard060 <|
  AllClassified.append Census.shard061 <|
  AllClassified.append Census.shard062 <|
  AllClassified.append Census.shard063 <|
  AllClassified.append Census.shard064 <|
  AllClassified.append Census.shard065 <|
  AllClassified.append Census.shard066 <|
  AllClassified.append Census.shard067 <|
  AllClassified.append Census.shard068 <|
  AllClassified.append Census.shard069 <|
  AllClassified.append Census.shard070 <|
  AllClassified.append Census.shard071 <|
  AllClassified.append Census.shard072 <|
  AllClassified.append Census.shard073 <|
  AllClassified.append Census.shard074 <|
  AllClassified.append Census.shard075 <|
  AllClassified.append Census.shard076 <|
  AllClassified.append Census.shard077 <|
  AllClassified.append Census.shard078 <|
  AllClassified.append Census.shard079 <|
  AllClassified.append Census.shard080 <|
  AllClassified.append Census.shard081 <|
  AllClassified.append Census.shard082 <|
  AllClassified.append Census.shard083 <|
  AllClassified.append Census.shard084 <|
  AllClassified.append Census.shard085 <|
  AllClassified.append Census.shard086 <|
  AllClassified.append Census.shard087 <|
  AllClassified.append Census.shard088 <|
  AllClassified.append Census.shard089 <|
  AllClassified.append Census.shard090 <|
  AllClassified.append Census.shard091 <|
  AllClassified.append Census.shard092 <|
  AllClassified.append Census.shard093 <|
  AllClassified.append Census.shard094 <|
  AllClassified.append Census.shard095 <|
  AllClassified.append Census.shard096 <|
  AllClassified.append Census.shard097 <|
  AllClassified.append Census.shard098 <|
  AllClassified.append Census.shard099 <|
  AllClassified.append Census.shard100 <|
  AllClassified.append Census.shard101 <|
  AllClassified.append Census.shard102 <|
  AllClassified.append Census.shard103 <|
  AllClassified.append Census.shard104 <|
  AllClassified.append Census.shard105 <|
  AllClassified.append Census.shard106 <|
  Census.shard107

/-- **Classification of the semigroups of order six by finite basability.**
For every class `e` of the catalogue (the 15,973 semigroups of order six of
GAP Smallsemi, up to isomorphism and anti-isomorphism), the table of `e` is the
table of a semigroup, and every semigroup on `Fin 6` with this table is
nonfinitely based if `e` is `[6, 3843]`, `[6, 8564]`, `[6, 8878]` or
`[6, 13747]`, and finitely based otherwise. -/
theorem order6_classification : ∀ e ∈ Catalogue.order6, Classified e :=
  AllClassified.mem allClassified_order6

/-- Every semigroup with the table of a class of order six other than the four
exceptional classes has a finite identity basis. -/
theorem order6_finitelyBased : ∀ e ∈ Catalogue.order6, e.id ∉ nonfinitelyBasedIds →
    ∀ G : SemigroupBasis.Semigroup (Fin 6), HasTable G e.rows →
      SemigroupBasis.FinitelyBased G :=
  fun e he hid G hG => ((order6_classification e he).2 G hG).2 hid

/-- The four exceptional classes of order six have no finite identity basis. -/
theorem order6_nonfinitelyBased : ∀ e ∈ Catalogue.order6, e.id ∈ nonfinitelyBasedIds →
    ∀ G : SemigroupBasis.Semigroup (Fin 6), HasTable G e.rows →
      SemigroupBasis.NonfinitelyBased G :=
  fun e he hid G hG => ((order6_classification e he).2 G hG).1 hid

end SemiBase
