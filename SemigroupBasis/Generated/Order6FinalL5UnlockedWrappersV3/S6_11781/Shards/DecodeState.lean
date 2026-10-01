import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.Shards.DecodeStatePart00
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.Shards.DecodeStatePart01
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.Shards.DecodeStatePart02
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.Shards.DecodeStatePart03
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.Shards.DecodeStatePart04

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.Shards

def stateVectorCode
    (vector : Fin 26 -> Fin 6) : Nat :=
  (vector (0 : Fin 26)).val + 6 * ((vector (1 : Fin 26)).val + 6 * ((vector (2 : Fin 26)).val + 6 * ((vector (3 : Fin 26)).val + 6 * ((vector (4 : Fin 26)).val + 6 * ((vector (5 : Fin 26)).val + 6 * ((vector (6 : Fin 26)).val + 6 * ((vector (7 : Fin 26)).val + 6 * ((vector (8 : Fin 26)).val + 6 * ((vector (9 : Fin 26)).val + 6 * ((vector (10 : Fin 26)).val + 6 * ((vector (11 : Fin 26)).val + 6 * ((vector (12 : Fin 26)).val + 6 * ((vector (13 : Fin 26)).val + 6 * ((vector (14 : Fin 26)).val + 6 * ((vector (15 : Fin 26)).val + 6 * ((vector (16 : Fin 26)).val + 6 * ((vector (17 : Fin 26)).val + 6 * ((vector (18 : Fin 26)).val + 6 * ((vector (19 : Fin 26)).val + 6 * ((vector (20 : Fin 26)).val + 6 * ((vector (21 : Fin 26)).val + 6 * ((vector (22 : Fin 26)).val + 6 * ((vector (23 : Fin 26)).val + 6 * ((vector (24 : Fin 26)).val + 6 * ((vector (25 : Fin 26)).val)))))))))))))))))))))))))

def decodeStateCode (code : Nat) : Fin 4374 :=
  if code < 136603559669586094080 then
    if code < 122251230840756731904 then
      if code < 51195698843973115392 then
        if code < 23535036395527546368 then
          if code < 22767136860945010176 then
            if code < 22745205552524447232 then
              if code < 22743377473304415744 then
                decodeStateCodeChunk0 code
              else
                decodeStateCodeChunk1 code
            else
              if code < 22764699421984968192 then
                decodeStateCodeChunk2 code
              else
                decodeStateCodeChunk3 code
          else
            if code < 22896321099705847296 then
              if code < 22874999151025294848 then
                decodeStateCodeChunk4 code
              else
                decodeStateCodeChunk5 code
            else
              if code < 23532598956204707328 then
                decodeStateCodeChunk6 code
              else
                decodeStateCodeChunk7 code
        else
          if code < 27503757826684374528 then
            if code < 23688487821712320000 then
              if code < 23664119073968918016 then
                decodeStateCodeChunk8 code
              else
                decodeStateCodeChunk9 code
            else
              if code < 27481829339373719040 then
                decodeStateCodeChunk10 code
              else
                decodeStateCodeChunk11 code
          else
            if code < 28273282398937769472 then
              if code < 27615276353568886272 then
                decodeStateCodeChunk12 code
              else
                decodeStateCodeChunk13 code
            else
              if code < 28424397867402286080 then
                decodeStateCodeChunk14 code
              else
                if code < 51173784460035214848 then
                  decodeStateCodeChunk15 code
                else
                  decodeStateCodeChunk16 code
      else
        if code < 117512835318521413632 then
          if code < 55933436499111313920 then
            if code < 51963516093643771392 then
              if code < 51307219641241603584 then
                decodeStateCodeChunk17 code
              else
                decodeStateCodeChunk18 code
            else
              if code < 52096963029837571584 then
                decodeStateCodeChunk19 code
              else
                decodeStateCodeChunk20 code
          else
            if code < 117510397879561371648 then
              if code < 56701237292307509760 then
                decodeStateCodeChunk21 code
              else
                decodeStateCodeChunk22 code
            else
              if code < 117511007239301382144 then
                decodeStateCodeChunk23 code
              else
                decodeStateCodeChunk24 code
        else
          if code < 117664066518148325376 then
            if code < 117534780732491513856 then
              if code < 117532343293531471872 then
                decodeStateCodeChunk25 code
              else
                decodeStateCodeChunk26 code
            else
              if code < 117642645830621011968 then
                decodeStateCodeChunk27 code
              else
                decodeStateCodeChunk28 code
          else
            if code < 118302682617998972928 then
              if code < 118300245178676133888 then
                decodeStateCodeChunk29 code
              else
                decodeStateCodeChunk30 code
            else
              if code < 118431866843336318976 then
                decodeStateCodeChunk31 code
              else
                if code < 122248793323432525824 then
                  decodeStateCodeChunk32 code
                else
                  decodeStateCodeChunk33 code
    else
      if code < 135939992186575180800 then
        if code < 133329368109014809344 then
          if code < 133304999361634204416 then
            if code < 122402447856469942272 then
              if code < 122273162149177294848 then
                decodeStateCodeChunk34 code
              else
                decodeStateCodeChunk35 code
            else
              if code < 123041064034684753920 then
                decodeStateCodeChunk36 code
              else
                decodeStateCodeChunk37 code
          else
            if code < 133307436800594246400 then
              if code < 133305608721374214912 then
                decodeStateCodeChunk38 code
              else
                decodeStateCodeChunk39 code
            else
              if code < 133326930670054767360 then
                decodeStateCodeChunk40 code
              else
                decodeStateCodeChunk41 code
        else
          if code < 134097269054152299264 then
            if code < 133458552804899937024 then
              if code < 133437230856219384576 then
                decodeStateCodeChunk42 code
              else
                decodeStateCodeChunk43 code
            else
              if code < 134094831614829460224 then
                decodeStateCodeChunk44 code
              else
                decodeStateCodeChunk45 code
          else
            if code < 134250737393935823616 then
              if code < 134226354540642884352 then
                decodeStateCodeChunk46 code
              else
                decodeStateCodeChunk47 code
            else
              if code < 135937554747615138816 then
                decodeStateCodeChunk48 code
              else
                if code < 135938164107355149312 then
                  decodeStateCodeChunk49 code
                else
                  decodeStateCodeChunk50 code
      else
        if code < 136400566581352599552 then
          if code < 136376175265092734976 then
            if code < 136069174100532483072 then
              if code < 135960092594665804800 then
                decodeStateCodeChunk51 code
              else
                decodeStateCodeChunk52 code
            else
              if code < 136071611539492525056 then
                decodeStateCodeChunk53 code
              else
                decodeStateCodeChunk54 code
          else
            if code < 136378612704052776960 then
              if code < 136376784624832745472 then
                decodeStateCodeChunk55 code
              else
                decodeStateCodeChunk56 code
            else
              if code < 136398129142392557568 then
                decodeStateCodeChunk57 code
              else
                decodeStateCodeChunk58 code
        else
          if code < 136471852901443700736 then
            if code < 136450009047430268928 then
              if code < 136449399687690258432 then
                decodeStateCodeChunk59 code
              else
                decodeStateCodeChunk60 code
            else
              if code < 136453665205870331904 then
                decodeStateCodeChunk61 code
              else
                decodeStateCodeChunk62 code
          else
            if code < 136510248944447483904 then
              if code < 136507811505487441920 then
                decodeStateCodeChunk63 code
              else
                decodeStateCodeChunk64 code
            else
              if code < 136532273349494992896 then
                decodeStateCodeChunk65 code
              else
                if code < 136581645287824975872 then
                  decodeStateCodeChunk66 code
                else
                  decodeStateCodeChunk67 code
  else
    if code < 146096470382685401088 then
      if code < 140678323293467612160 then
        if code < 137265221415907952640 then
          if code < 137166003286623129600 then
            if code < 136749195590949983232 then
              if code < 136727789008972207104 then
                decodeStateCodeChunk68 code
              else
                decodeStateCodeChunk69 code
            else
              if code < 136859498167221605376 then
                decodeStateCodeChunk70 code
              else
                decodeStateCodeChunk71 code
          else
            if code < 137239024589307316224 then
              if code < 137168440725945968640 then
                decodeStateCodeChunk72 code
              else
                decodeStateCodeChunk73 code
            else
              if code < 137243290107487389696 then
                decodeStateCodeChunk74 code
              else
                decodeStateCodeChunk75 code
        else
          if code < 138065278155057494784 then
            if code < 137375016153214150656 then
              if code < 137319480089736376320 then
                decodeStateCodeChunk76 code
              else
                decodeStateCodeChunk77 code
            else
              if code < 138043956206376942336 then
                decodeStateCodeChunk78 code
              else
                decodeStateCodeChunk79 code
          else
            if code < 138833179099832187648 then
              if code < 138175578341222112000 then
                decodeStateCodeChunk80 code
              else
                decodeStateCodeChunk81 code
            else
              if code < 138964702025645611776 then
                decodeStateCodeChunk82 code
              else
                if code < 140675885776143406080 then
                  decodeStateCodeChunk83 code
                else
                  decodeStateCodeChunk84 code
      else
        if code < 141319978667278166016 then
          if code < 141138897688245030912 then
            if code < 141114520399170539520 then
              if code < 140807507479985673216 then
                decodeStateCodeChunk85 code
              else
                decodeStateCodeChunk86 code
            else
              if code < 141116957916494745600 then
                decodeStateCodeChunk87 code
              else
                decodeStateCodeChunk88 code
          else
            if code < 141210183929971968000 then
              if code < 141188354181508073472 then
                decodeStateCodeChunk89 code
              else
                decodeStateCodeChunk90 code
            else
              if code < 141248582402264838144 then
                decodeStateCodeChunk91 code
              else
                decodeStateCodeChunk92 code
        else
          if code < 141981637592490117120 then
            if code < 141597845652224332800 then
              if code < 141466122388425397248 then
                decodeStateCodeChunk93 code
              else
                decodeStateCodeChunk94 code
            else
              if code < 141906788289312860160 then
                decodeStateCodeChunk95 code
              else
                decodeStateCodeChunk96 code
          else
            if code < 145940496424942288896 then
              if code < 142057912208036327424 then
                decodeStateCodeChunk97 code
              else
                decodeStateCodeChunk98 code
            else
              if code < 145942933863902330880 then
                decodeStateCodeChunk99 code
              else
                if code < 146072101633128013824 then
                  decodeStateCodeChunk100 code
                else
                  decodeStateCodeChunk101 code
    else
      if code < 164905577032356771840 then
        if code < 162525427132678380288 then
          if code < 151492975874231887872 then
            if code < 150678881054558797824 then
              if code < 146752749451303833600 then
                decodeStateCodeChunk102 code
              else
                decodeStateCodeChunk103 code
            else
              if code < 150810502719218982912 then
                decodeStateCodeChunk104 code
              else
                decodeStateCodeChunk105 code
          else
            if code < 161757032966031649536 then
              if code < 161735696909624777472 then
                decodeStateCodeChunk106 code
              else
                decodeStateCodeChunk107 code
            else
              if code < 161867335043820116736 then
                decodeStateCodeChunk108 code
              else
                decodeStateCodeChunk109 code
        else
          if code < 164499766340147205120 then
            if code < 164368130517694706688 then
              if code < 162657062915948796672 then
                decodeStateCodeChunk110 code
              else
                decodeStateCodeChunk111 code
            else
              if code < 164389466574101578752 then
                decodeStateCodeChunk112 code
              else
                decodeStateCodeChunk113 code
          else
            if code < 164808711706557984768 then
              if code < 164806274267597942784 then
                decodeStateCodeChunk114 code
              else
                decodeStateCodeChunk115 code
            else
              if code < 164879380203579353088 then
                decodeStateCodeChunk116 code
              else
                if code < 164883645721759426560 then
                  decodeStateCodeChunk117 code
                else
                  decodeStateCodeChunk118 code
      else
        if code < 166607493759808061184 then
          if code < 165310800647028728832 then
            if code < 165015284326139750400 then
              if code < 164959818790409662464 then
                decodeStateCodeChunk119 code
              else
                decodeStateCodeChunk120 code
            else
              if code < 165159685058851261440 then
                decodeStateCodeChunk121 code
              else
                decodeStateCodeChunk122 code
          else
            if code < 165673394752212412416 then
              if code < 165617943322031861760 then
                decodeStateCodeChunk123 code
              else
                decodeStateCodeChunk124 code
            else
              if code < 165800731163983865856 then
                decodeStateCodeChunk125 code
              else
                if code < 166474044394687971072 then
                  decodeStateCodeChunk126 code
                else
                  decodeStateCodeChunk127 code
        else
          if code < 169617728171888225280 then
            if code < 169128406505306032128 then
              if code < 167416715425219958016 then
                decodeStateCodeChunk128 code
              else
                decodeStateCodeChunk129 code
            else
              if code < 169544608130357277696 then
                decodeStateCodeChunk130 code
              else
                decodeStateCodeChunk131 code
          else
            if code < 169771281147155833344 then
              if code < 169643925000665644032 then
                decodeStateCodeChunk132 code
              else
                decodeStateCodeChunk133 code
            else
              if code < 170334334108685325312 then
                decodeStateCodeChunk134 code
              else
                if code < 170429997641663536128 then
                  decodeStateCodeChunk135 code
                else
                  decodeStateCodeChunk136 code

def decodeState
    (vector : Fin 26 -> Fin 6) : Fin 4374 :=
  decodeStateCode (stateVectorCode vector)

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_11781.Shards
