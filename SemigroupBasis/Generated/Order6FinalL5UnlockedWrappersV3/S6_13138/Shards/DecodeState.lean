import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.Shards.DecodeStatePart00
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.Shards.DecodeStatePart01
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.Shards.DecodeStatePart02
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.Shards.DecodeStatePart03
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.Shards.DecodeStatePart04
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.Shards.DecodeStatePart05
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.Shards.DecodeStatePart06
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.Shards.DecodeStatePart07
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.Shards.DecodeStatePart08
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.Shards.DecodeStatePart09
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.Shards.DecodeStatePart10
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.Shards.DecodeStatePart11

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.Shards

def stateVectorCode
    (vector : Fin 36 -> Fin 6) : Nat :=
  (vector (0 : Fin 36)).val + 6 * ((vector (1 : Fin 36)).val + 6 * ((vector (2 : Fin 36)).val + 6 * ((vector (3 : Fin 36)).val + 6 * ((vector (4 : Fin 36)).val + 6 * ((vector (5 : Fin 36)).val + 6 * ((vector (6 : Fin 36)).val + 6 * ((vector (7 : Fin 36)).val + 6 * ((vector (8 : Fin 36)).val + 6 * ((vector (9 : Fin 36)).val + 6 * ((vector (10 : Fin 36)).val + 6 * ((vector (11 : Fin 36)).val + 6 * ((vector (12 : Fin 36)).val + 6 * ((vector (13 : Fin 36)).val + 6 * ((vector (14 : Fin 36)).val + 6 * ((vector (15 : Fin 36)).val + 6 * ((vector (16 : Fin 36)).val + 6 * ((vector (17 : Fin 36)).val + 6 * ((vector (18 : Fin 36)).val + 6 * ((vector (19 : Fin 36)).val + 6 * ((vector (20 : Fin 36)).val + 6 * ((vector (21 : Fin 36)).val + 6 * ((vector (22 : Fin 36)).val + 6 * ((vector (23 : Fin 36)).val + 6 * ((vector (24 : Fin 36)).val + 6 * ((vector (25 : Fin 36)).val + 6 * ((vector (26 : Fin 36)).val + 6 * ((vector (27 : Fin 36)).val + 6 * ((vector (28 : Fin 36)).val + 6 * ((vector (29 : Fin 36)).val + 6 * ((vector (30 : Fin 36)).val + 6 * ((vector (31 : Fin 36)).val + 6 * ((vector (32 : Fin 36)).val + 6 * ((vector (33 : Fin 36)).val + 6 * ((vector (34 : Fin 36)).val + 6 * ((vector (35 : Fin 36)).val)))))))))))))))))))))))))))))))))))

def decodeStateCode (code : Nat) : Fin 11742 :=
  if code < 7907952802999146357465902592 then
    if code < 6236634025911679397236023552 then
      if code < 6190018132837878686464420608 then
        if code < 6188875909692339572311919616 then
          if code < 6188667072507028938540201984 then
            if code < 6188654845117641168767276928 then
              if code < 6188654843534524720585446144 then
                if code < 6188654835637222487868716544 then
                  decodeStateCodeChunk0 code
                else
                  decodeStateCodeChunk1 code
              else
                if code < 6188654844327911337171604224 then
                  decodeStateCodeChunk2 code
                else
                  if code < 6188654845113984615966814080 then
                    decodeStateCodeChunk3 code
                  else
                    decodeStateCodeChunk4 code
            else
              if code < 6188660985266469406277763840 then
                if code < 6188654845249279877270355840 then
                  decodeStateCodeChunk5 code
                else
                  if code < 6188660976579453881520440832 then
                    decodeStateCodeChunk6 code
                  else
                    decodeStateCodeChunk7 code
              else
                if code < 6188660986059855763822904832 then
                  decodeStateCodeChunk8 code
                else
                  if code < 6188660988425406598238400384 then
                    decodeStateCodeChunk9 code
                  else
                    decodeStateCodeChunk10 code
          else
            if code < 6188691689323208093832162048 then
              if code < 6188691633906712822747914240 then
                if code < 6188667129323730626930505216 then
                  decodeStateCodeChunk11 code
                else
                  decodeStateCodeChunk12 code
              else
                if code < 6188691681290526441053216256 then
                  decodeStateCodeChunk13 code
                else
                  if code < 6188691686164286731066050048 then
                    decodeStateCodeChunk14 code
                  else
                    decodeStateCodeChunk15 code
            else
              if code < 6188875862173129838023884288 then
                if code < 6188691690767288803881009024 then
                  decodeStateCodeChunk16 code
                else
                  if code < 6188691690858793933014418944 then
                    decodeStateCodeChunk17 code
                  else
                    decodeStateCodeChunk18 code
              else
                if code < 6188875862308508790077898240 then
                  decodeStateCodeChunk19 code
                else
                  if code < 6188875909560701175088714752 then
                    decodeStateCodeChunk20 code
                  else
                    decodeStateCodeChunk21 code
        else
          if code < 6188882062432875290892205056 then
            if code < 6188875919165343979836503424 then
              if code < 6188875918989831526414187520 then
                if code < 6188875917589540005625923840 then
                  decodeStateCodeChunk22 code
                else
                  decodeStateCodeChunk23 code
              else
                if code < 6188875919033705872121336832 then
                  decodeStateCodeChunk24 code
                else
                  if code < 6188875919125109623789009920 then
                    decodeStateCodeChunk25 code
                  else
                    decodeStateCodeChunk26 code
            else
              if code < 6188882050630795846368918528 then
                if code < 6188875919169085163394610560 then
                  decodeStateCodeChunk27 code
                else
                  if code < 6188875919169102222833765376 then
                    decodeStateCodeChunk28 code
                  else
                    decodeStateCodeChunk29 code
              else
                if code < 6188882059186190139645741312 then
                  decodeStateCodeChunk30 code
                else
                  if code < 6188882060107541570231319552 then
                    decodeStateCodeChunk31 code
                  else
                    decodeStateCodeChunk32 code
          else
            if code < 6189981288588438249396008448 then
              if code < 6188912707961812742889523200 then
                if code < 6188888146426749671908179456 then
                  decodeStateCodeChunk33 code
                else
                  if code < 6188888203269044941740690432 then
                    decodeStateCodeChunk34 code
                  else
                    decodeStateCodeChunk35 code
              else
                if code < 6188912764778498210260655616 then
                  decodeStateCodeChunk36 code
                else
                  if code < 6189981231771736326276009984 then
                    decodeStateCodeChunk37 code
                  else
                    decodeStateCodeChunk38 code
            else
              if code < 6190018124808852957033045504 then
                if code < 6190018077425023117345775616 then
                  decodeStateCodeChunk39 code
                else
                  if code < 6190018077556661512392198144 then
                    decodeStateCodeChunk40 code
                  else
                    decodeStateCodeChunk41 code
              else
                if code < 6190018124940576453747691008 then
                  decodeStateCodeChunk42 code
                else
                  if code < 6190018132706155420488702720 then
                    decodeStateCodeChunk43 code
                  else
                    decodeStateCodeChunk44 code
      else
        if code < 6197976767096997266256482304 then
          if code < 6190202362687428841126376832 then
            if code < 6190018134420995499978874368 then
              if code < 6190018134285615605015311872 then
                if code < 6190018134241843527444684288 then
                  decodeStateCodeChunk45 code
                else
                  decodeStateCodeChunk46 code
              else
                if code < 6190018134285717507093616512 then
                  decodeStateCodeChunk47 code
                else
                  if code < 6190018134417237256618815360 then
                    decodeStateCodeChunk48 code
                  else
                    decodeStateCodeChunk49 code
            else
              if code < 6190202361107952095635742976 then
                if code < 6190202334121744854118399488 then
                  decodeStateCodeChunk50 code
                else
                  if code < 6190202353210649629640506368 then
                    decodeStateCodeChunk51 code
                  else
                    decodeStateCodeChunk52 code
              else
                if code < 6190202362552134130911563136 then
                  decodeStateCodeChunk53 code
                else
                  if code < 6190202362683654561765620736 then
                    decodeStateCodeChunk54 code
                  else
                    decodeStateCodeChunk55 code
          else
            if code < 6190239208340716009128193536 then
              if code < 6190239206761255578262383360 then
                if code < 6190239151480139964509626368 then
                  decodeStateCodeChunk56 code
                else
                  if code < 6190239198863953345545653760 then
                    decodeStateCodeChunk57 code
                  else
                    decodeStateCodeChunk58 code
              else
                if code < 6190239208293185727012779520 then
                  decodeStateCodeChunk59 code
                else
                  if code < 6190239208340698703712634752 then
                    decodeStateCodeChunk60 code
                  else
                    decodeStateCodeChunk61 code
            else
              if code < 6197939940265512566484874752 then
                if code < 6196619647166145533905466880 then
                  decodeStateCodeChunk62 code
                else
                  if code < 6196840719638044477793257728 then
                    decodeStateCodeChunk63 code
                  else
                    decodeStateCodeChunk64 code
              else
                if code < 6197940035033122328260413312 then
                  decodeStateCodeChunk65 code
                else
                  if code < 6197946166498588299979568640 then
                    decodeStateCodeChunk66 code
                  else
                    decodeStateCodeChunk67 code
        else
          if code < 6205935540217013872003259136 then
            if code < 6198161107505122883980839168 then
              if code < 6197976880686409169392160256 then
                if code < 6197976795483309834582603264 then
                  decodeStateCodeChunk68 code
                else
                  decodeStateCodeChunk69 code
              else
                if code < 6198160966933143180438978048 then
                  decodeStateCodeChunk70 code
                else
                  if code < 6198161023662080453431790976 then
                    decodeStateCodeChunk71 code
                  else
                    decodeStateCodeChunk72 code
            else
              if code < 6198197869447005872453611392 then
                if code < 6198161109084583303962737664 then
                  decodeStateCodeChunk73 code
                else
                  if code < 6198167249895054626607019392 then
                    decodeStateCodeChunk74 code
                  else
                    decodeStateCodeChunk75 code
              else
                if code < 6199272621818992144650253824 then
                  decodeStateCodeChunk76 code
                else
                  if code < 6205898694563625522790810368 then
                    decodeStateCodeChunk77 code
                  else
                    decodeStateCodeChunk78 code
          else
            if code < 6236412952672004135529825792 then
              if code < 6207458488489612549510216704 then
                if code < 6206119768483430889818808576 then
                  decodeStateCodeChunk79 code
                else
                  if code < 6206156606371054078300681728 then
                    decodeStateCodeChunk80 code
                  else
                    decodeStateCodeChunk81 code
              else
                if code < 6236406811751726621717503488 then
                  decodeStateCodeChunk82 code
                else
                  if code < 6236412943239115357990565376 then
                    decodeStateCodeChunk83 code
                  else
                    decodeStateCodeChunk84 code
            else
              if code < 6236627876220277785345905664 then
                if code < 6236412955085068549247074176 then
                  decodeStateCodeChunk85 code
                else
                  if code < 6236443657383076459970108928 then
                    decodeStateCodeChunk86 code
                  else
                    decodeStateCodeChunk87 code
              else
                if code < 6236627885697040307441606016 then
                  decodeStateCodeChunk88 code
                else
                  if code < 6236633972147869535746604544 then
                    decodeStateCodeChunk89 code
                  else
                    decodeStateCodeChunk90 code
    else
      if code < 6484488595485254141580080640 then
        if code < 6285743140011128919862647552 then
          if code < 6245699079255057467394349824 then
            if code < 6237954329167837623525626880 then
              if code < 6237733198431414731582361600 then
                if code < 6236634028964571696498674688 then
                  decodeStateCodeChunk91 code
                else
                  decodeStateCodeChunk92 code
              else
                if code < 6237770091538083476182801920 then
                  decodeStateCodeChunk93 code
                else
                  if code < 6237770101011088277704988544 then
                    decodeStateCodeChunk94 code
                  else
                    decodeStateCodeChunk95 code
            else
              if code < 6244372639641510280867493376 then
                if code < 6237991165457804209540701696 then
                  decodeStateCodeChunk96 code
                else
                  if code < 6244372582824807652107220992 then
                    decodeStateCodeChunk97 code
                  else
                    decodeStateCodeChunk98 code
              else
                if code < 6244593711192040345074662400 then
                  decodeStateCodeChunk99 code
                else
                  if code < 6245692939848432368511290880 then
                    decodeStateCodeChunk100 code
                  else
                    decodeStateCodeChunk101 code
          else
            if code < 6245920240023165315829355520 then
              if code < 6245913956951552503260648960 then
                if code < 6245729728685016998828986368 then
                  decodeStateCodeChunk102 code
                else
                  if code < 6245729785545694122335325696 then
                    decodeStateCodeChunk103 code
                  else
                    decodeStateCodeChunk104 code
              else
                if code < 6245914013812128536995304448 then
                  decodeStateCodeChunk105 code
                else
                  if code < 6245920126323950146754287104 then
                    decodeStateCodeChunk106 code
                  else
                    decodeStateCodeChunk107 code
            else
              if code < 6284195624156095985889517056 then
                if code < 6245950944734342020963339776 then
                  decodeStateCodeChunk108 code
                else
                  if code < 6284158776923348777014635264 then
                    decodeStateCodeChunk109 code
                  else
                    decodeStateCodeChunk110 code
              else
                if code < 6284392127199386876820483072 then
                  decodeStateCodeChunk111 code
                else
                  if code < 6285522066091306626548079360 then
                    decodeStateCodeChunk112 code
                  else
                    decodeStateCodeChunk113 code
        else
          if code < 6475246437048275350497429504 then
            if code < 6475203486122255838039983616 then
              if code < 6475172783648752479281038848 then
                if code < 6302743394804159944208426496 then
                  decodeStateCodeChunk114 code
                else
                  decodeStateCodeChunk115 code
              else
                if code < 6475172786149564695559798656 then
                  decodeStateCodeChunk116 code
                else
                  if code < 6475203448079926799003092992 then
                    decodeStateCodeChunk117 code
                  else
                    decodeStateCodeChunk118 code
            else
              if code < 6475203505072124536580015616 then
                if code < 6475203490729116876114483072 then
                  decodeStateCodeChunk119 code
                else
                  if code < 6475203504896628957578380800 then
                    decodeStateCodeChunk120 code
                  else
                    decodeStateCodeChunk121 code
              else
                if code < 6475209622326088494348879360 then
                  decodeStateCodeChunk122 code
                else
                  if code < 6475209644303256877571347200 then
                    decodeStateCodeChunk123 code
                  else
                    decodeStateCodeChunk124 code
          else
            if code < 6483131421063135557758875648 then
              if code < 6476529934243686039030203904 then
                if code < 6476529877383212035799998464 then
                  decodeStateCodeChunk125 code
                else
                  if code < 6476529929505304726829975040 then
                    decodeStateCodeChunk126 code
                  else
                    decodeStateCodeChunk127 code
              else
                if code < 6476529946879471664517606144 then
                  decodeStateCodeChunk128 code
                else
                  if code < 6476529948546577882677954048 then
                    decodeStateCodeChunk129 code
                  else
                    decodeStateCodeChunk130 code
            else
              if code < 6484457974353960962357625600 then
                if code < 6483131449449549686404462080 then
                  decodeStateCodeChunk131 code
                else
                  if code < 6483168306948789823278269952 then
                    decodeStateCodeChunk132 code
                  else
                    decodeStateCodeChunk133 code
              else
                if code < 6484488567055067697731794944 then
                  decodeStateCodeChunk134 code
                else
                  if code < 6484488593905793721598182144 then
                    decodeStateCodeChunk135 code
                  else
                    decodeStateCodeChunk136 code
      else
        if code < 6530958145121924123847673344 then
          if code < 6522955471666618716309542784 then
            if code < 6484494835933473763790262144 then
              if code < 6484488680776118100766257024 then
                if code < 6484488609700499718678382080 then
                  decodeStateCodeChunk137 code
                else
                  decodeStateCodeChunk138 code
              else
                if code < 6484488694991363758405504896 then
                  decodeStateCodeChunk139 code
                else
                  if code < 6484494736427465654682742656 then
                    decodeStateCodeChunk140 code
                  else
                    decodeStateCodeChunk141 code
            else
              if code < 6522924755043748340825194368 then
                if code < 6522924698248983290340194304 then
                  decodeStateCodeChunk142 code
                else
                  if code < 6522924751950638457622948608 then
                    decodeStateCodeChunk143 code
                  else
                    decodeStateCodeChunk144 code
              else
                if code < 6522955447912642121241927168 then
                  decodeStateCodeChunk145 code
                else
                  if code < 6522955457389286154544732032 then
                    decodeStateCodeChunk146 code
                  else
                    decodeStateCodeChunk147 code
          else
            if code < 6524281915100939083466939904 then
              if code < 6522961612612489470168030720 then
                if code < 6522961593589480205982309888 then
                  decodeStateCodeChunk148 code
                else
                  if code < 6522961598331517676622601728 then
                    decodeStateCodeChunk149 code
                  else
                    decodeStateCodeChunk150 code
              else
                if code < 6524281858324471594391789568 then
                  decodeStateCodeChunk151 code
                else
                  if code < 6524281900882020423445913088 then
                    decodeStateCodeChunk152 code
                  else
                    decodeStateCodeChunk153 code
            else
              if code < 6530884437274889604315705216 then
                if code < 6530884382849298766517053440 then
                  decodeStateCodeChunk154 code
                else
                  if code < 6530884435695429317113516800 then
                    decodeStateCodeChunk155 code
                  else
                    decodeStateCodeChunk156 code
              else
                if code < 6530884439709874800251708928 then
                  decodeStateCodeChunk157 code
                else
                  if code < 6530921282928176395385470848 then
                    decodeStateCodeChunk158 code
                  else
                    decodeStateCodeChunk159 code
        else
          if code < 6532247802260602363226273280 then
            if code < 6532241585504289280616222208 then
              if code < 6532210966149872960246663040 then
                if code < 6532210880771260754435378688 then
                  decodeStateCodeChunk160 code
                else
                  decodeStateCodeChunk161 code
              else
                if code < 6532241571354973542718464000 then
                  decodeStateCodeChunk162 code
                else
                  if code < 6532241583924913966293314304 then
                    decodeStateCodeChunk163 code
                  else
                    decodeStateCodeChunk164 code
            else
              if code < 6532241685076126108674289152 then
                if code < 6532241599675660982555155968 then
                  decodeStateCodeChunk165 code
                else
                  if code < 6532241670751262568586513920 then
                    decodeStateCodeChunk166 code
                  else
                    decodeStateCodeChunk167 code
              else
                if code < 6532247716969738746161733120 then
                  decodeStateCodeChunk168 code
                else
                  if code < 6532247726446484470024134144 then
                    decodeStateCodeChunk169 code
                  else
                    decodeStateCodeChunk170 code
          else
            if code < 6763041748548522424767923712 then
              if code < 6761715304898573499668350464 then
                if code < 6532247825952509033066534400 then
                  decodeStateCodeChunk171 code
                else
                  if code < 6761715248173275328216025088 then
                    decodeStateCodeChunk172 code
                  else
                    decodeStateCodeChunk173 code
              else
                if code < 6761764434783543433019131392 then
                  decodeStateCodeChunk174 code
                else
                  if code < 6763041746837440301306555136 then
                    decodeStateCodeChunk175 code
                  else
                    decodeStateCodeChunk176 code
            else
              if code < 7907946709440745234867147776 then
                if code < 6778959156059380891882753536 then
                  decodeStateCodeChunk177 code
                else
                  if code < 6858545680227601798561573632 then
                    decodeStateCodeChunk178 code
                  else
                    decodeStateCodeChunk179 code
              else
                if code < 7907946718873634010229625856 then
                  decodeStateCodeChunk180 code
                else
                  if code < 7907946718917507887202978816 then
                    decodeStateCodeChunk181 code
                  else
                    decodeStateCodeChunk182 code
  else
    if code < 8242216787451322814523171840 then
      if code < 7964990945161278022732584960 then
        if code < 7917268754486292684297564672 then
          if code < 7909310008089121882472523648 then
            if code < 7907952862228828257279133056 then
              if code < 7907952858280278427693119744 then
                if code < 7907952850382976157971090432 then
                  decodeStateCodeChunk183 code
                else
                  decodeStateCodeChunk184 code
              else
                if code < 7907952859815865442700635136 then
                  decodeStateCodeChunk185 code
                else
                  if code < 7907952859859738821553630208 then
                    decodeStateCodeChunk186 code
                  else
                    decodeStateCodeChunk187 code
            else
              if code < 7909273162391961270669014016 then
                if code < 7907983562991334295648865024 then
                  decodeStateCodeChunk188 code
                else
                  if code < 7907983564570811603108126208 then
                    decodeStateCodeChunk189 code
                  else
                    decodeStateCodeChunk190 code
              else
                if code < 7909309951228562320445792256 then
                  decodeStateCodeChunk191 code
                else
                  if code < 7909310006509677934198549248 then
                    decodeStateCodeChunk192 code
                  else
                    decodeStateCodeChunk193 code
          else
            if code < 7917231908789115093595846656 then
              if code < 7915911520969668293662261248 then
                if code < 7915911464105351455129625088 then
                  decodeStateCodeChunk194 code
                else
                  if code < 7915911519386467068882382080 then
                    decodeStateCodeChunk195 code
                  else
                    decodeStateCodeChunk196 code
              else
                if code < 7917231795111836874798359040 then
                  decodeStateCodeChunk197 code
                else
                  if code < 7917231823501924127725535232 then
                    decodeStateCodeChunk198 code
                  else
                    decodeStateCodeChunk199 code
            else
              if code < 7917238049775098921538410880 then
                if code < 7917237936057704716126093824 then
                  decodeStateCodeChunk200 code
                else
                  if code < 7917237964484353318365419904 then
                    decodeStateCodeChunk201 code
                  else
                    decodeStateCodeChunk202 code
              else
                if code < 7917268659722322102063880704 then
                  decodeStateCodeChunk203 code
                else
                  if code < 7917268669199084621982798720 then
                    decodeStateCodeChunk204 code
                  else
                    decodeStateCodeChunk205 code
        else
          if code < 7957061917888224308459765760 then
            if code < 7955704824874027925827924224 then
              if code < 7955698685445564589029860352 then
                if code < 7955698628716610259137472000 then
                  decodeStateCodeChunk206 code
                else
                  decodeStateCodeChunk207 code
              else
                if code < 7955704769592912312075167232 then
                  decodeStateCodeChunk208 code
                else
                  if code < 7955704816976725695287976960 then
                    decodeStateCodeChunk209 code
                  else
                    decodeStateCodeChunk210 code
            else
              if code < 7955704828756868032083772800 then
                if code < 7955704826365740569369699328 then
                  decodeStateCodeChunk211 code
                else
                  if code < 7955704826475526919533556736 then
                    decodeStateCodeChunk212 code
                  else
                    decodeStateCodeChunk213 code
              else
                if code < 7955735521622088727390920192 then
                  decodeStateCodeChunk214 code
                else
                  if code < 7957025119552940009509671936 then
                    decodeStateCodeChunk215 code
                  else
                    decodeStateCodeChunk216 code
          else
            if code < 7963664511119614543002556800 then
              if code < 7963664501573385013085239296 then
                if code < 7957061974682989320488277888 then
                  decodeStateCodeChunk217 code
                else
                  if code < 7963664454255382011245781504 then
                    decodeStateCodeChunk218 code
                  else
                    decodeStateCodeChunk219 code
              else
                if code < 7963664509474444962021917952 then
                  decodeStateCodeChunk220 code
                else
                  if code < 7963664510984336341138169856 then
                    decodeStateCodeChunk221 code
                  else
                    decodeStateCodeChunk222 code
            else
              if code < 7964984813564207286524491776 then
                if code < 7963664513444930997421940736 then
                  decodeStateCodeChunk223 code
                else
                  if code < 7964984804083788007377598464 then
                    decodeStateCodeChunk224 code
                  else
                    decodeStateCodeChunk225 code
              else
                if code < 7964984897608321883744494848 then
                  decodeStateCodeChunk226 code
                else
                  if code < 7964990897777464169334790656 then
                    decodeStateCodeChunk227 code
                  else
                    decodeStateCodeChunk228 code
      else
        if code < 8202423465444628765636452864 then
          if code < 8194280602133103945619244544 then
            if code < 7965021649872352658542834176 then
              if code < 7964990954634384005447301120 then
                if code < 7964990954502660741285568512 then
                  decodeStateCodeChunk229 code
                else
                  decodeStateCodeChunk230 code
              else
                if code < 7964991038345787675254506752 then
                  decodeStateCodeChunk231 code
                else
                  if code < 7964991039925146534916939776 then
                    decodeStateCodeChunk232 code
                  else
                    decodeStateCodeChunk233 code
            else
              if code < 8194243699619139092849952768 then
                if code < 7965021659301585275465249280 then
                  decodeStateCodeChunk234 code
                else
                  if code < 7965021744570513328862556672 then
                    decodeStateCodeChunk235 code
                  else
                    decodeStateCodeChunk236 code
              else
                if code < 8194274451714126360096916992 then
                  decodeStateCodeChunk237 code
                else
                  if code < 8194274475406033509192089088 then
                    decodeStateCodeChunk238 code
                  else
                    decodeStateCodeChunk239 code
          else
            if code < 8195600847848640198504210432 then
              if code < 8194495478250034180789788672 then
                if code < 8194464773538860296402914816 then
                  decodeStateCodeChunk240 code
                else
                  if code < 8194464830355562454978202624 then
                    decodeStateCodeChunk241 code
                  else
                    decodeStateCodeChunk242 code
              else
                if code < 8194495535110610214161647104 then
                  decodeStateCodeChunk243 code
                else
                  if code < 8194716566384898968294621184 then
                    decodeStateCodeChunk244 code
                  else
                    decodeStateCodeChunk245 code
            else
              if code < 8202202363094620004515556352 then
                if code < 8195600918924360247203716608 then
                  decodeStateCodeChunk246 code
                else
                  if code < 8195821978585063599804464640 then
                    decodeStateCodeChunk247 code
                  else
                    decodeStateCodeChunk248 code
              else
                if code < 8202202419955196038250211840 then
                  decodeStateCodeChunk249 code
                else
                  if code < 8202239277410562297787869696 then
                    decodeStateCodeChunk250 code
                  else
                    decodeStateCodeChunk251 code
        else
          if code < 8203780639735227075321850752 then
            if code < 8203559580034306647785777664 then
              if code < 8202460280302194615184444416 then
                if code < 8202423491465609982700044288 then
                  decodeStateCodeChunk252 code
                else
                  decodeStateCodeChunk253 code
              else
                if code < 8203528946395193726246196096 then
                  decodeStateCodeChunk254 code
                else
                  if code < 8203559565771632597044713984 then
                    decodeStateCodeChunk255 code
                  else
                    decodeStateCodeChunk256 code
            else
              if code < 8203565806263624534457594752 then
                if code < 8203565664112286099316648960 then
                  decodeStateCodeChunk257 code
                else
                  if code < 8203565706761374145923588992 then
                    decodeStateCodeChunk258 code
                  else
                    decodeStateCodeChunk259 code
              else
                if code < 8203750010838151939695255552 then
                  decodeStateCodeChunk260 code
                else
                  if code < 8203780630258464555402932736 then
                    decodeStateCodeChunk261 code
                  else
                    decodeStateCodeChunk262 code
          else
            if code < 8242026370924773433897672704 then
              if code < 8204001811588807984470507264 then
                if code < 8203780724989529776616722944 then
                  decodeStateCodeChunk263 code
                else
                  if code < 8203786780677438718664643456 then
                    decodeStateCodeChunk264 code
                  else
                    decodeStateCodeChunk265 code
              else
                if code < 8205076466202429672586002432 then
                  decodeStateCodeChunk266 code
                else
                  if code < 8241995722218651461045392128 then
                    decodeStateCodeChunk267 code
                  else
                    decodeStateCodeChunk268 code
            else
              if code < 8242032568661651520570023424 then
                if code < 8242026441912762632816500224 then
                  decodeStateCodeChunk269 code
                else
                  if code < 8242032559185007356664290816 then
                    decodeStateCodeChunk270 code
                  else
                    decodeStateCodeChunk271 code
              else
                if code < 8242032582218703968745493248 then
                  decodeStateCodeChunk272 code
                else
                  if code < 8242069430877352995366323712 then
                    decodeStateCodeChunk273 code
                  else
                    decodeStateCodeChunk274 code
    else
      if code < 8251312570005812223407473152 then
        if code < 8249992267564976858700212736 then
          if code < 8249955353113638214352673792 then
            if code < 8242253633170522015283879424 then
              if code < 8242216797015934892866667520 then
                if code < 8242216795480348348044136704 then
                  decodeStateCodeChunk275 code
                else
                  decodeStateCodeChunk276 code
              else
                if code < 8242216799407164072261725184 then
                  decodeStateCodeChunk277 code
                else
                  if code < 8242247500388853227874945792 then
                    decodeStateCodeChunk278 code
                  else
                    decodeStateCodeChunk279 code
            else
              if code < 8243352871194008888468577792 then
                if code < 8242253642669238608409017856 then
                  decodeStateCodeChunk280 code
                else
                  if code < 8242474730804103356368971264 then
                    decodeStateCodeChunk281 code
                  else
                    decodeStateCodeChunk282 code
              else
                if code < 8243573935680823919804554752 then
                  decodeStateCodeChunk283 code
                else
                  if code < 8243573945289225070225184640 then
                    decodeStateCodeChunk284 code
                  else
                    decodeStateCodeChunk285 code
          else
            if code < 8249992196397734806809412608 then
              if code < 8249955407561150176128920064 then
                if code < 8249955398197728411490435584 then
                  decodeStateCodeChunk286 code
                else
                  if code < 8249955406025563631669186304 then
                    decodeStateCodeChunk287 code
                  else
                    decodeStateCodeChunk288 code
              else
                if code < 8249955407608697136387795456 then
                  decodeStateCodeChunk289 code
                else
                  if code < 8249955409974214587669386112 then
                    decodeStateCodeChunk290 code
                  else
                    decodeStateCodeChunk291 code
            else
              if code < 8249992253258310709941140352 then
                if code < 8249992210748275170672706560 then
                  decodeStateCodeChunk292 code
                else
                  if code < 8249992248655325876879485440 then
                    decodeStateCodeChunk293 code
                  else
                    decodeStateCodeChunk294 code
              else
                if code < 8249992253393605028335133568 then
                  decodeStateCodeChunk295 code
                else
                  if code < 8249992266819019447159600896 then
                    decodeStateCodeChunk296 code
                  else
                    decodeStateCodeChunk297 code
        else
          if code < 8250176481660124115837215104 then
            if code < 8250176472183378049853177856 then
              if code < 8250176424667926469681138176 then
                if code < 8250029115474012315340368384 then
                  decodeStateCodeChunk298 code
                else
                  decodeStateCodeChunk299 code
              else
                if code < 8250176427033358947720651264 then
                  decodeStateCodeChunk300 code
                else
                  if code < 8250176472047982132320434176 then
                    decodeStateCodeChunk301 code
                  else
                    decodeStateCodeChunk302 code
            else
              if code < 8250176481480870907320115200 then
                if code < 8250176479945283892312599808 then
                  decodeStateCodeChunk303 code
                else
                  if code < 8250176480080680241211043072 then
                    decodeStateCodeChunk304 code
                  else
                    decodeStateCodeChunk305 code
              else
                if code < 8250176481590555634763413504 then
                  decodeStateCodeChunk306 code
                else
                  if code < 8250176481616266827392438272 then
                    decodeStateCodeChunk307 code
                  else
                    decodeStateCodeChunk308 code
          else
            if code < 8251281794262771945339264000 then
              if code < 8250213270452851418517974016 then
                if code < 8250176483893935321037363584 then
                  decodeStateCodeChunk309 code
                else
                  if code < 8250176484025573481354090880 then
                    decodeStateCodeChunk310 code
                  else
                    decodeStateCodeChunk311 code
              else
                if code < 8250213325931383171104550656 then
                  decodeStateCodeChunk312 code
                else
                  if code < 8250213327313427935861105152 then
                    decodeStateCodeChunk313 code
                  else
                    decodeStateCodeChunk314 code
            else
              if code < 8251312527535875311277536256 then
                if code < 8251281851123348319018773376 then
                  decodeStateCodeChunk315 code
                else
                  if code < 8251281936414228995522468352 then
                    decodeStateCodeChunk316 code
                  else
                    decodeStateCodeChunk317 code
              else
                if code < 8251312554255081663620091648 then
                  decodeStateCodeChunk318 code
                else
                  if code < 8251312555834542083601990144 then
                    decodeStateCodeChunk319 code
                  else
                    decodeStateCodeChunk320 code
      else
        if code < 8251533628174784997956779776 then
          if code < 8251318711127175473951832960 then
            if code < 8251318692038372415107351040 then
              if code < 8251318639916059204780028928 then
                if code < 8251312636518646092671365632 then
                  decodeStateCodeChunk321 code
                else
                  decodeStateCodeChunk322 code
              else
                if code < 8251318654131321238352790528 then
                  decodeStateCodeChunk323 code
                else
                  if code < 8251318687299872590169620992 then
                    decodeStateCodeChunk324 code
                  else
                    decodeStateCodeChunk325 code
            else
              if code < 8251318696842446090435817984 then
                if code < 8251318695328812978486716160 then
                  decodeStateCodeChunk326 code
                else
                  if code < 8251318696776635107911756672 then
                    decodeStateCodeChunk327 code
                  else
                    decodeStateCodeChunk328 code
              else
                if code < 8251318696912031119404925440 then
                  decodeStateCodeChunk329 code
                else
                  if code < 8251318710991796182315762176 then
                    decodeStateCodeChunk330 code
                  else
                    decodeStateCodeChunk331 code
          else
            if code < 8251502925043068582201766272 then
              if code < 8251318796414383067895599616 then
                if code < 8251318782023641909256083968 then
                  decodeStateCodeChunk332 code
                else
                  if code < 8251318794769028103065313024 then
                    decodeStateCodeChunk333 code
                  else
                    decodeStateCodeChunk334 code
              else
                if code < 8251502896744419339138654720 then
                  decodeStateCodeChunk335 code
                else
                  if code < 8251502923463608292822795520 then
                    decodeStateCodeChunk336 code
                  else
                    decodeStateCodeChunk337 code
            else
              if code < 8251503010290160487391098880 then
                if code < 8251502925174690285681236352 then
                  decodeStateCodeChunk338 code
                else
                  if code < 8251503000988791855551422464 then
                    decodeStateCodeChunk339 code
                  else
                    decodeStateCodeChunk340 code
              else
                if code < 8251503010465656079453427712 then
                  decodeStateCodeChunk341 code
                else
                  if code < 8251533601389768736239842304 then
                    decodeStateCodeChunk342 code
                  else
                    decodeStateCodeChunk343 code
        else
          if code < 8251539856118959794632980992 then
            if code < 8251539742397807687978228736 then
              if code < 8251533629885883917837462400 then
                if code < 8251533629754245757520735104 then
                  decodeStateCodeChunk344 code
                else
                  decodeStateCodeChunk345 code
              else
                if code < 8251533705707280917110411776 then
                  decodeStateCodeChunk346 code
                else
                  if code < 8251533715381476933162699648 then
                    decodeStateCodeChunk347 code
                  else
                    decodeStateCodeChunk348 code
            else
              if code < 8251539770787861558134297088 then
                if code < 8251539761552405338535219712 then
                  decodeStateCodeChunk349 code
                else
                  if code < 8251539769449707569075166976 then
                    decodeStateCodeChunk350 code
                  else
                    decodeStateCodeChunk351 code
              else
                if code < 8251539770831751719620318080 then
                  decodeStateCodeChunk352 code
                else
                  if code < 8251539851387890825797063168 then
                    decodeStateCodeChunk353 code
                  else
                    decodeStateCodeChunk354 code
          else
            if code < 9627054354842471817526715904 then
              if code < 8252829456177573996379840512 then
                if code < 8251760830536328636462703616 then
                  decodeStateCodeChunk355 code
                else
                  if code < 8252608382257853263011863040 then
                    decodeStateCodeChunk356 code
                  else
                    decodeStateCodeChunk357 code
              else
                if code < 9627017461805371175246016000 then
                  decodeStateCodeChunk358 code
                else
                  if code < 9627017518643993826173236224 then
                    decodeStateCodeChunk359 code
                  else
                    decodeStateCodeChunk360 code
            else
              if code < 9644298215308100392266413568 then
                if code < 9628343962140400552901827584 then
                  decodeStateCodeChunk361 code
                else
                  if code < 9628380807793670415488085504 then
                    decodeStateCodeChunk362 code
                  else
                    decodeStateCodeChunk363 code
              else
                if code < 9723884712924046123403587584 then
                  decodeStateCodeChunk364 code
                else
                  if code < 10201625780191447156541614080 then
                    decodeStateCodeChunk365 code
                  else
                    decodeStateCodeChunk366 code

def decodeState
    (vector : Fin 36 -> Fin 6) : Fin 11742 :=
  decodeStateCode (stateVectorCode vector)

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13138.Shards
