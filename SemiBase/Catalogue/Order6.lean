import SemiBase.Statement
import SemiBase.Catalogue.Order6.Part001
import SemiBase.Catalogue.Order6.Part002
import SemiBase.Catalogue.Order6.Part003
import SemiBase.Catalogue.Order6.Part004
import SemiBase.Catalogue.Order6.Part005
import SemiBase.Catalogue.Order6.Part006
import SemiBase.Catalogue.Order6.Part007
import SemiBase.Catalogue.Order6.Part008
import SemiBase.Catalogue.Order6.Part009
import SemiBase.Catalogue.Order6.Part010
import SemiBase.Catalogue.Order6.Part011
import SemiBase.Catalogue.Order6.Part012
import SemiBase.Catalogue.Order6.Part013
import SemiBase.Catalogue.Order6.Part014
import SemiBase.Catalogue.Order6.Part015
import SemiBase.Catalogue.Order6.Part016
import SemiBase.Catalogue.Order6.Part017
import SemiBase.Catalogue.Order6.Part018
import SemiBase.Catalogue.Order6.Part019
import SemiBase.Catalogue.Order6.Part020
import SemiBase.Catalogue.Order6.Part021
import SemiBase.Catalogue.Order6.Part022
import SemiBase.Catalogue.Order6.Part023
import SemiBase.Catalogue.Order6.Part024
import SemiBase.Catalogue.Order6.Part025
import SemiBase.Catalogue.Order6.Part026
import SemiBase.Catalogue.Order6.Part027
import SemiBase.Catalogue.Order6.Part028
import SemiBase.Catalogue.Order6.Part029
import SemiBase.Catalogue.Order6.Part030
import SemiBase.Catalogue.Order6.Part031
import SemiBase.Catalogue.Order6.Part032
import SemiBase.Catalogue.Order6.Part033
import SemiBase.Catalogue.Order6.Part034
import SemiBase.Catalogue.Order6.Part035
import SemiBase.Catalogue.Order6.Part036
import SemiBase.Catalogue.Order6.Part037
import SemiBase.Catalogue.Order6.Part038
import SemiBase.Catalogue.Order6.Part039
import SemiBase.Catalogue.Order6.Part040
import SemiBase.Catalogue.Order6.Part041
import SemiBase.Catalogue.Order6.Part042
import SemiBase.Catalogue.Order6.Part043
import SemiBase.Catalogue.Order6.Part044
import SemiBase.Catalogue.Order6.Part045
import SemiBase.Catalogue.Order6.Part046
import SemiBase.Catalogue.Order6.Part047
import SemiBase.Catalogue.Order6.Part048
import SemiBase.Catalogue.Order6.Part049
import SemiBase.Catalogue.Order6.Part050
import SemiBase.Catalogue.Order6.Part051
import SemiBase.Catalogue.Order6.Part052
import SemiBase.Catalogue.Order6.Part053
import SemiBase.Catalogue.Order6.Part054
import SemiBase.Catalogue.Order6.Part055
import SemiBase.Catalogue.Order6.Part056
import SemiBase.Catalogue.Order6.Part057
import SemiBase.Catalogue.Order6.Part058
import SemiBase.Catalogue.Order6.Part059
import SemiBase.Catalogue.Order6.Part060
import SemiBase.Catalogue.Order6.Part061
import SemiBase.Catalogue.Order6.Part062
import SemiBase.Catalogue.Order6.Part063
import SemiBase.Catalogue.Order6.Part064
import SemiBase.Catalogue.Order6.Part065
import SemiBase.Catalogue.Order6.Part066
import SemiBase.Catalogue.Order6.Part067
import SemiBase.Catalogue.Order6.Part068
import SemiBase.Catalogue.Order6.Part069
import SemiBase.Catalogue.Order6.Part070
import SemiBase.Catalogue.Order6.Part071
import SemiBase.Catalogue.Order6.Part072
import SemiBase.Catalogue.Order6.Part073
import SemiBase.Catalogue.Order6.Part074
import SemiBase.Catalogue.Order6.Part075
import SemiBase.Catalogue.Order6.Part076
import SemiBase.Catalogue.Order6.Part077
import SemiBase.Catalogue.Order6.Part078
import SemiBase.Catalogue.Order6.Part079
import SemiBase.Catalogue.Order6.Part080
import SemiBase.Catalogue.Order6.Part081
import SemiBase.Catalogue.Order6.Part082
import SemiBase.Catalogue.Order6.Part083
import SemiBase.Catalogue.Order6.Part084
import SemiBase.Catalogue.Order6.Part085
import SemiBase.Catalogue.Order6.Part086
import SemiBase.Catalogue.Order6.Part087
import SemiBase.Catalogue.Order6.Part088
import SemiBase.Catalogue.Order6.Part089
import SemiBase.Catalogue.Order6.Part090
import SemiBase.Catalogue.Order6.Part091
import SemiBase.Catalogue.Order6.Part092
import SemiBase.Catalogue.Order6.Part093
import SemiBase.Catalogue.Order6.Part094
import SemiBase.Catalogue.Order6.Part095
import SemiBase.Catalogue.Order6.Part096
import SemiBase.Catalogue.Order6.Part097
import SemiBase.Catalogue.Order6.Part098
import SemiBase.Catalogue.Order6.Part099
import SemiBase.Catalogue.Order6.Part100
import SemiBase.Catalogue.Order6.Part101
import SemiBase.Catalogue.Order6.Part102
import SemiBase.Catalogue.Order6.Part103
import SemiBase.Catalogue.Order6.Part104
import SemiBase.Catalogue.Order6.Part105
import SemiBase.Catalogue.Order6.Part106
import SemiBase.Catalogue.Order6.Part107

/-!
# The catalogue of semigroups of order six

The 15,973 classes of semigroups of order six up to isomorphism and
anti-isomorphism, as listed by GAP Smallsemi 0.7.2 (OEIS A001423), in Smallsemi
order. The catalogue is data: this repository does not prove that it lists
every class.
-/

namespace SemiBase.Catalogue

/-- The 15,973 classes `[6, 1]`, …, `[6, 15973]` with their tables. -/
def order6 : List Entry :=
  Order6.part001 ++ (Order6.part002 ++ (Order6.part003 ++ (Order6.part004 ++ (Order6.part005 ++ (Order6.part006 ++ (Order6.part007 ++ (Order6.part008 ++ (Order6.part009 ++ (Order6.part010 ++ (Order6.part011 ++ (Order6.part012 ++ (Order6.part013 ++ (Order6.part014 ++ (Order6.part015 ++ (Order6.part016 ++ (Order6.part017 ++ (Order6.part018 ++ (Order6.part019 ++ (Order6.part020 ++ (Order6.part021 ++ (Order6.part022 ++ (Order6.part023 ++ (Order6.part024 ++ (Order6.part025 ++ (Order6.part026 ++ (Order6.part027 ++ (Order6.part028 ++ (Order6.part029 ++ (Order6.part030 ++ (Order6.part031 ++ (Order6.part032 ++ (Order6.part033 ++ (Order6.part034 ++ (Order6.part035 ++ (Order6.part036 ++ (Order6.part037 ++ (Order6.part038 ++ (Order6.part039 ++ (Order6.part040 ++ (Order6.part041 ++ (Order6.part042 ++ (Order6.part043 ++ (Order6.part044 ++ (Order6.part045 ++ (Order6.part046 ++ (Order6.part047 ++ (Order6.part048 ++ (Order6.part049 ++ (Order6.part050 ++ (Order6.part051 ++ (Order6.part052 ++ (Order6.part053 ++ (Order6.part054 ++ (Order6.part055 ++ (Order6.part056 ++ (Order6.part057 ++ (Order6.part058 ++ (Order6.part059 ++ (Order6.part060 ++ (Order6.part061 ++ (Order6.part062 ++ (Order6.part063 ++ (Order6.part064 ++ (Order6.part065 ++ (Order6.part066 ++ (Order6.part067 ++ (Order6.part068 ++ (Order6.part069 ++ (Order6.part070 ++ (Order6.part071 ++ (Order6.part072 ++ (Order6.part073 ++ (Order6.part074 ++ (Order6.part075 ++ (Order6.part076 ++ (Order6.part077 ++ (Order6.part078 ++ (Order6.part079 ++ (Order6.part080 ++ (Order6.part081 ++ (Order6.part082 ++ (Order6.part083 ++ (Order6.part084 ++ (Order6.part085 ++ (Order6.part086 ++ (Order6.part087 ++ (Order6.part088 ++ (Order6.part089 ++ (Order6.part090 ++ (Order6.part091 ++ (Order6.part092 ++ (Order6.part093 ++ (Order6.part094 ++ (Order6.part095 ++ (Order6.part096 ++ (Order6.part097 ++ (Order6.part098 ++ (Order6.part099 ++ (Order6.part100 ++ (Order6.part101 ++ (Order6.part102 ++ (Order6.part103 ++ (Order6.part104 ++ (Order6.part105 ++ (Order6.part106 ++ (Order6.part107))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem order6_length : order6.length = 15973 := by decide +kernel

/-- The entries are the classes `[6, 1]`, …, `[6, 15973]`, in this order. -/
theorem order6_ids : order6.map Entry.id = List.range' 1 15973 := by decide +kernel

end SemiBase.Catalogue
