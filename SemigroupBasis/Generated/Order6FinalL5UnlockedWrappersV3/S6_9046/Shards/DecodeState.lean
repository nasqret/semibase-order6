import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9046.Shards.DecodeStatePart00
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9046.Shards.DecodeStatePart01
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9046.Shards.DecodeStatePart02
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9046.Shards.DecodeStatePart03
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9046.Shards.DecodeStatePart04
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9046.Shards.DecodeStatePart05
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9046.Shards.DecodeStatePart06
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9046.Shards.DecodeStatePart07

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9046.Shards

def stateVectorCode
    (vector : Fin 23 -> Fin 6) : Nat :=
  (vector (0 : Fin 23)).val + 6 * ((vector (1 : Fin 23)).val + 6 * ((vector (2 : Fin 23)).val + 6 * ((vector (3 : Fin 23)).val + 6 * ((vector (4 : Fin 23)).val + 6 * ((vector (5 : Fin 23)).val + 6 * ((vector (6 : Fin 23)).val + 6 * ((vector (7 : Fin 23)).val + 6 * ((vector (8 : Fin 23)).val + 6 * ((vector (9 : Fin 23)).val + 6 * ((vector (10 : Fin 23)).val + 6 * ((vector (11 : Fin 23)).val + 6 * ((vector (12 : Fin 23)).val + 6 * ((vector (13 : Fin 23)).val + 6 * ((vector (14 : Fin 23)).val + 6 * ((vector (15 : Fin 23)).val + 6 * ((vector (16 : Fin 23)).val + 6 * ((vector (17 : Fin 23)).val + 6 * ((vector (18 : Fin 23)).val + 6 * ((vector (19 : Fin 23)).val + 6 * ((vector (20 : Fin 23)).val + 6 * ((vector (21 : Fin 23)).val + 6 * ((vector (22 : Fin 23)).val))))))))))))))))))))))

def decodeStateCode (code : Nat) : Fin 7782 :=
  if code < 223814960021915712 then
    if code < 99429400492227648 then
      if code < 89053371313251840 then
        if code < 10971187772378112 then
          if code < 3833311579393824 then
            if code < 806258419555392 then
              if code < 188435339744832 then
                decodeStateCodeChunk0 code
              else
                if code < 679778658657792 then
                  decodeStateCodeChunk1 code
                else
                  decodeStateCodeChunk2 code
            else
              if code < 1906560930373632 then
                if code < 1297209907570176 then
                  decodeStateCodeChunk3 code
                else
                  decodeStateCodeChunk4 code
              else
                if code < 2208498056602848 then
                  decodeStateCodeChunk5 code
                else
                  decodeStateCodeChunk6 code
          else
            if code < 5554647922000896 then
              if code < 4445492437422144 then
                if code < 4050221408782560 then
                  decodeStateCodeChunk7 code
                else
                  decodeStateCodeChunk8 code
              else
                if code < 4944826714212864 then
                  decodeStateCodeChunk9 code
                else
                  decodeStateCodeChunk10 code
            else
              if code < 7492367375244864 then
                if code < 5777045421719328 then
                  decodeStateCodeChunk11 code
                else
                  decodeStateCodeChunk12 code
              else
                if code < 8295991888080384 then
                  decodeStateCodeChunk13 code
                else
                  decodeStateCodeChunk14 code
        else
          if code < 87927813753615936 then
            if code < 12198370593038976 then
              if code < 11182771016323776 then
                decodeStateCodeChunk15 code
              else
                if code < 11684928591056160 then
                  decodeStateCodeChunk16 code
                else
                  decodeStateCodeChunk17 code
            else
              if code < 87820624639747296 then
                if code < 12908889751737024 then
                  decodeStateCodeChunk18 code
                else
                  decodeStateCodeChunk19 code
              else
                if code < 87919274236511808 then
                  decodeStateCodeChunk20 code
                else
                  decodeStateCodeChunk21 code
          else
            if code < 88528631809817664 then
              if code < 88131012031070208 then
                if code < 88029778591798848 then
                  decodeStateCodeChunk22 code
                else
                  decodeStateCodeChunk23 code
              else
                if code < 88429971329141472 then
                  decodeStateCodeChunk24 code
                else
                  decodeStateCodeChunk25 code
            else
              if code < 88639125281193024 then
                if code < 88537123437710400 then
                  decodeStateCodeChunk26 code
                else
                  decodeStateCodeChunk27 code
              else
                if code < 88739929894344192 then
                  decodeStateCodeChunk28 code
                else
                  decodeStateCodeChunk29 code
      else
        if code < 92407357598994144 then
          if code < 91575900745243200 then
            if code < 89750268170058528 then
              if code < 89343632179030752 then
                decodeStateCodeChunk30 code
              else
                if code < 89651908083377376 then
                  decodeStateCodeChunk31 code
                else
                  decodeStateCodeChunk32 code
            else
              if code < 89972717910492384 then
                if code < 89852206886853408 then
                  decodeStateCodeChunk33 code
                else
                  decodeStateCodeChunk34 code
              else
                if code < 91479604250183904 then
                  decodeStateCodeChunk35 code
                else
                  decodeStateCodeChunk36 code
          else
            if code < 92088950939578080 then
              if code < 91778239193674752 then
                if code < 91592383341091392 then
                  decodeStateCodeChunk37 code
                else
                  decodeStateCodeChunk38 code
              else
                if code < 91798010909599968 then
                  decodeStateCodeChunk39 code
                else
                  decodeStateCodeChunk40 code
            else
              if code < 92201730030485568 then
                if code < 92184894795898944 then
                  decodeStateCodeChunk41 code
                else
                  decodeStateCodeChunk42 code
              else
                if code < 92387596766980608 then
                  decodeStateCodeChunk43 code
                else
                  decodeStateCodeChunk44 code
        else
          if code < 95739872039373312 then
            if code < 93412042767047232 then
              if code < 93016717339004640 then
                if code < 92794241475215424 then
                  decodeStateCodeChunk45 code
                else
                  decodeStateCodeChunk46 code
              else
                if code < 93318880836584448 then
                  decodeStateCodeChunk47 code
                else
                  decodeStateCodeChunk48 code
            else
              if code < 95130044281082880 then
                if code < 93530464079690304 then
                  decodeStateCodeChunk49 code
                else
                  decodeStateCodeChunk50 code
              else
                if code < 95234501537054496 then
                  decodeStateCodeChunk51 code
                else
                  decodeStateCodeChunk52 code
          else
            if code < 98727022479310848 then
              if code < 96961403914062048 then
                if code < 95849427317608512 then
                  decodeStateCodeChunk53 code
                else
                  decodeStateCodeChunk54 code
              else
                if code < 98718482962206720 then
                  decodeStateCodeChunk55 code
                else
                  decodeStateCodeChunk56 code
            else
              if code < 99022862436249600 then
                if code < 98825761328085792 then
                  decodeStateCodeChunk57 code
                else
                  decodeStateCodeChunk58 code
              else
                if code < 99327931960370688 then
                  decodeStateCodeChunk59 code
                else
                  decodeStateCodeChunk60 code
    else
      if code < 137294368558240320 then
        if code < 120658252537677024 then
          if code < 109957782656775744 then
            if code < 99945755030103552 then
              if code < 99437892120120384 then
                decodeStateCodeChunk61 code
              else
                if code < 99635028060736224 then
                  decodeStateCodeChunk62 code
                else
                  decodeStateCodeChunk63 code
            else
              if code < 100648594500720192 then
                if code < 100546629662490624 then
                  decodeStateCodeChunk64 code
                else
                  decodeStateCodeChunk65 code
              else
                if code < 100850930772369408 then
                  decodeStateCodeChunk66 code
                else
                  decodeStateCodeChunk67 code
          else
            if code < 114028644323731968 then
              if code < 111585554368169184 then
                if code < 110569963518738720 then
                  decodeStateCodeChunk68 code
                else
                  decodeStateCodeChunk69 code
              else
                if code < 113416463465703648 then
                  decodeStateCodeChunk70 code
                else
                  decodeStateCodeChunk71 code
            else
              if code < 115543258170172416 then
                if code < 114733921802609952 then
                  decodeStateCodeChunk72 code
                else
                  decodeStateCodeChunk73 code
              else
                if code < 117777899390787648 then
                  decodeStateCodeChunk74 code
                else
                  decodeStateCodeChunk75 code
        else
          if code < 132622305751531008 then
            if code < 122695085181810240 then
              if code < 121270433397672672 then
                decodeStateCodeChunk76 code
              else
                if code < 121975710872616000 then
                  decodeStateCodeChunk77 code
                else
                  decodeStateCodeChunk78 code
            else
              if code < 132002131748764896 then
                if code < 131796033997239072 then
                  decodeStateCodeChunk79 code
                else
                  decodeStateCodeChunk80 code
              else
                if code < 132405863932311840 then
                  decodeStateCodeChunk81 code
                else
                  decodeStateCodeChunk82 code
          else
            if code < 135652180019309568 then
              if code < 133725664466809632 then
                if code < 133234486603416288 then
                  decodeStateCodeChunk83 code
                else
                  decodeStateCodeChunk84 code
              else
                if code < 135370380310405344 then
                  decodeStateCodeChunk85 code
                else
                  decodeStateCodeChunk86 code
            else
              if code < 136264360881272544 then
                if code < 136058733312763968 then
                  decodeStateCodeChunk87 code
                else
                  decodeStateCodeChunk88 code
              else
                if code < 136870897332625920 then
                  decodeStateCodeChunk89 code
                else
                  decodeStateCodeChunk90 code
      else
        if code < 220153640372435232 then
          if code < 144429034000086144 then
            if code < 140942142093211200 then
              if code < 139012903444414464 then
                decodeStateCodeChunk91 code
              else
                if code < 139714891813293120 then
                  decodeStateCodeChunk92 code
                else
                  decodeStateCodeChunk93 code
            else
              if code < 143210247049890432 then
                if code < 142702447256517312 then
                  decodeStateCodeChunk94 code
                else
                  decodeStateCodeChunk95 code
              else
                if code < 143512260362941536 then
                  decodeStateCodeChunk96 code
                else
                  decodeStateCodeChunk97 code
          else
            if code < 219643019467140672 then
              if code < 219456369088911360 then
                if code < 219439886493063168 then
                  decodeStateCodeChunk98 code
                else
                  decodeStateCodeChunk99 code
              else
                if code < 219544293683041056 then
                  decodeStateCodeChunk100 code
                else
                  decodeStateCodeChunk101 code
            else
              if code < 220048880543718912 then
                if code < 219747074018286816 then
                  decodeStateCodeChunk102 code
                else
                  decodeStateCodeChunk103 code
              else
                if code < 220065715778305536 then
                  decodeStateCodeChunk104 code
                else
                  decodeStateCodeChunk105 code
        else
          if code < 221577978701790432 then
            if code < 220776635475031104 then
              if code < 220355991881560800 then
                if code < 220252366156534848 then
                  decodeStateCodeChunk106 code
                else
                  decodeStateCodeChunk107 code
              else
                if code < 220660969970746080 then
                  decodeStateCodeChunk108 code
                else
                  decodeStateCodeChunk109 code
            else
              if code < 221369138202553920 then
                if code < 221270334054243552 then
                  decodeStateCodeChunk110 code
                else
                  decodeStateCodeChunk111 code
              else
                if code < 221394436766862912 then
                  decodeStateCodeChunk112 code
                else
                  decodeStateCodeChunk113 code
          else
            if code < 223307173289189952 then
              if code < 223120990919162880 then
                if code < 223098424218652896 then
                  decodeStateCodeChunk114 code
                else
                  decodeStateCodeChunk115 code
              else
                if code < 223205613332521536 then
                  decodeStateCodeChunk116 code
                else
                  decodeStateCodeChunk117 code
            else
              if code < 223707781791958752 then
                if code < 223408419789155328 then
                  decodeStateCodeChunk118 code
                else
                  decodeStateCodeChunk119 code
              else
                if code < 223730337608557056 then
                  decodeStateCodeChunk120 code
                else
                  decodeStateCodeChunk121 code
  else
    if code < 384516675613638144 then
      if code < 245954714942145024 then
        if code < 230444592180466464 then
          if code < 225129599407462176 then
            if code < 224323240874107392 then
              if code < 223916519978584128 then
                decodeStateCodeChunk122 code
              else
                if code < 224017766478549504 then
                  decodeStateCodeChunk123 code
                else
                  decodeStateCodeChunk124 code
            else
              if code < 224929378968150240 then
                if code < 224619143957733888 then
                  decodeStateCodeChunk125 code
                else
                  decodeStateCodeChunk126 code
              else
                if code < 225028104754263840 then
                  decodeStateCodeChunk127 code
                else
                  decodeStateCodeChunk128 code
          else
            if code < 227463136201152576 then
              if code < 226853308442862144 then
                if code < 225247772566872288 then
                  decodeStateCodeChunk129 code
                else
                  decodeStateCodeChunk130 code
              else
                if code < 227064578229218304 then
                  decodeStateCodeChunk131 code
                else
                  decodeStateCodeChunk132 code
            else
              if code < 228884183235615744 then
                if code < 228579816822266880 then
                  decodeStateCodeChunk133 code
                else
                  decodeStateCodeChunk134 code
              else
                if code < 230343502408735968 then
                  decodeStateCodeChunk135 code
                else
                  decodeStateCodeChunk136 code
        else
          if code < 231863754139614720 then
            if code < 230955670208037600 then
              if code < 230546141253223200 then
                decodeStateCodeChunk137 code
              else
                if code < 230653484918544384 then
                  decodeStateCodeChunk138 code
                else
                  decodeStateCodeChunk139 code
            else
              if code < 231161611229361216 then
                if code < 231054409054845216 then
                  decodeStateCodeChunk140 code
                else
                  decodeStateCodeChunk141 code
              else
                if code < 231558995905445376 then
                  decodeStateCodeChunk142 code
                else
                  decodeStateCodeChunk143 code
          else
            if code < 242087286655259712 then
              if code < 232371388477468224 then
                if code < 232177189018097664 then
                  decodeStateCodeChunk144 code
                else
                  decodeStateCodeChunk145 code
              else
                if code < 241384830278178816 then
                  decodeStateCodeChunk146 code
                else
                  decodeStateCodeChunk147 code
            else
              if code < 243511624986582240 then
                if code < 242705109724992576 then
                  decodeStateCodeChunk148 code
                else
                  decodeStateCodeChunk149 code
              else
                if code < 245342534084116704 then
                  decodeStateCodeChunk150 code
                else
                  decodeStateCodeChunk151 code
      else
        if code < 351368322913045728 then
          if code < 263414919267210816 then
            if code < 250626777688388160 then
              if code < 246967798140385056 then
                decodeStateCodeChunk152 code
              else
                if code < 248995871414272224 then
                  decodeStateCodeChunk153 code
                else
                  decodeStateCodeChunk154 code
            else
              if code < 253196504016085728 then
                if code < 252584323156090080 then
                  decodeStateCodeChunk155 code
                else
                  decodeStateCodeChunk156 code
              else
                if code < 254209587212358432 then
                  decodeStateCodeChunk157 code
                else
                  decodeStateCodeChunk158 code
          else
            if code < 267908631786846720 then
              if code < 265445794059964416 then
                if code < 264027097952391456 then
                  decodeStateCodeChunk159 code
                else
                  decodeStateCodeChunk160 code
              else
                if code < 267290808707036160 then
                  decodeStateCodeChunk161 code
                else
                  decodeStateCodeChunk162 code
            else
              if code < 276042196510424064 then
                if code < 274315764318401088 then
                  decodeStateCodeChunk163 code
                else
                  decodeStateCodeChunk164 code
              else
                if code < 351080880982359264 then
                  decodeStateCodeChunk165 code
                else
                  decodeStateCodeChunk166 code
        else
          if code < 356655463875072576 then
            if code < 354734218371013632 then
              if code < 351991786033921536 then
                if code < 351772042033931328 then
                  decodeStateCodeChunk167 code
                else
                  decodeStateCodeChunk168 code
              else
                if code < 353007690340101696 then
                  decodeStateCodeChunk169 code
                else
                  decodeStateCodeChunk170 code
            else
              if code < 355352041450824192 then
                if code < 355024468352880864 then
                  decodeStateCodeChunk171 code
                else
                  decodeStateCodeChunk172 code
              else
                if code < 355639483381510656 then
                  decodeStateCodeChunk173 code
                else
                  decodeStateCodeChunk174 code
          else
            if code < 373000904963292384 then
              if code < 362571340007702016 then
                if code < 361970443587336192 then
                  decodeStateCodeChunk175 code
                else
                  decodeStateCodeChunk176 code
              else
                if code < 362878438284849888 then
                  decodeStateCodeChunk177 code
                else
                  decodeStateCodeChunk178 code
            else
              if code < 376958608765295616 then
                if code < 373920273344577024 then
                  decodeStateCodeChunk179 code
                else
                  decodeStateCodeChunk180 code
              else
                if code < 378586693933438752 then
                  decodeStateCodeChunk181 code
                else
                  decodeStateCodeChunk182 code
    else
      if code < 486946474201188864 then
        if code < 482683790123140320 then
          if code < 399201519961331424 then
            if code < 395646999781681440 then
              if code < 394933182775621632 then
                decodeStateCodeChunk183 code
              else
                if code < 395153227171667520 then
                  decodeStateCodeChunk184 code
                else
                  decodeStateCodeChunk185 code
            else
              if code < 396879737727901248 then
                if code < 396168826748382720 then
                  decodeStateCodeChunk186 code
                else
                  decodeStateCodeChunk187 code
              else
                if code < 398693720167958304 then
                  decodeStateCodeChunk188 code
                else
                  decodeStateCodeChunk189 code
          else
            if code < 402959240595357984 then
              if code < 400417409612270592 then
                if code < 399427208757046080 then
                  decodeStateCodeChunk190 code
                else
                  decodeStateCodeChunk191 code
              else
                if code < 402245499776679936 then
                  decodeStateCodeChunk192 code
                else
                  decodeStateCodeChunk193 code
            else
              if code < 406544871346233408 then
                if code < 405935509419362880 then
                  decodeStateCodeChunk194 code
                else
                  decodeStateCodeChunk195 code
              else
                if code < 407365500888696387 then
                  decodeStateCodeChunk196 code
                else
                  decodeStateCodeChunk197 code
        else
          if code < 483614429885328096 then
            if code < 482993787870425088 then
              if code < 482782581210756672 then
                decodeStateCodeChunk198 code
              else
                if code < 482807918957147712 then
                  decodeStateCodeChunk199 code
                else
                  decodeStateCodeChunk200 code
            else
              if code < 483394698946031904 then
                if code < 483295960099224288 then
                  decodeStateCodeChunk201 code
                else
                  decodeStateCodeChunk202 code
              else
                if code < 483496245842006304 then
                  decodeStateCodeChunk203 code
                else
                  decodeStateCodeChunk204 code
          else
            if code < 484835961758049504 then
              if code < 484517568157360128 then
                if code < 484009777091271744 then
                  decodeStateCodeChunk205 code
                else
                  decodeStateCodeChunk206 code
              else
                if code < 484627526140327488 then
                  decodeStateCodeChunk207 code
                else
                  decodeStateCodeChunk208 code
            else
              if code < 486444394993762080 then
                if code < 486354028049851392 then
                  decodeStateCodeChunk209 code
                else
                  decodeStateCodeChunk210 code
              else
                if code < 486565611292957248 then
                  decodeStateCodeChunk211 code
                else
                  decodeStateCodeChunk212 code
      else
        if code < 494295543815823648 then
          if code < 488388039588011808 then
            if code < 487250853675231744 then
              if code < 486969030021721824 then
                decodeStateCodeChunk213 code
              else
                if code < 487056588912484416 then
                  decodeStateCodeChunk214 code
                else
                  decodeStateCodeChunk215 code
            else
              if code < 487885577283021312 then
                if code < 487564362574391808 then
                  decodeStateCodeChunk216 code
                else
                  decodeStateCodeChunk217 code
              else
                if code < 488266757981411904 then
                  decodeStateCodeChunk218 code
                else
                  decodeStateCodeChunk219 code
          else
            if code < 492128530929289440 then
              if code < 490602621757340160 then
                if code < 489996172367202528 then
                  decodeStateCodeChunk220 code
                else
                  decodeStateCodeChunk221 code
              else
                if code < 490906988170689024 then
                  decodeStateCodeChunk222 code
                else
                  decodeStateCodeChunk223 code
            else
              if code < 493787667835022112 then
                if code < 493683286766478912 then
                  decodeStateCodeChunk224 code
                else
                  decodeStateCodeChunk225 code
              else
                if code < 494193907671726816 then
                  decodeStateCodeChunk226 code
                else
                  decodeStateCodeChunk227 code
        else
          if code < 508987805910156576 then
            if code < 504829489834055232 then
              if code < 495409795176116736 then
                if code < 494498284968987360 then
                  decodeStateCodeChunk228 code
                else
                  decodeStateCodeChunk229 code
              else
                if code < 495519909887412288 then
                  decodeStateCodeChunk230 code
                else
                  decodeStateCodeChunk231 code
            else
              if code < 506454440433573888 then
                if code < 505531632754386432 then
                  decodeStateCodeChunk232 code
                else
                  decodeStateCodeChunk233 code
              else
                if code < 508375625048193600 then
                  decodeStateCodeChunk234 code
                else
                  decodeStateCodeChunk235 code
          else
            if code < 515527138603081728 then
              if code < 510412144239511776 then
                if code < 509797150994926080 then
                  decodeStateCodeChunk236 code
                else
                  decodeStateCodeChunk237 code
              else
                if code < 512649606568067136 then
                  decodeStateCodeChunk238 code
                else
                  decodeStateCodeChunk239 code
            else
              if code < 516847418059973184 then
                if code < 516229594980162624 then
                  decodeStateCodeChunk240 code
                else
                  decodeStateCodeChunk241 code
              else
                if code < 517653933341718240 then
                  decodeStateCodeChunk242 code
                else
                  decodeStateCodeChunk243 code

def decodeState
    (vector : Fin 23 -> Fin 6) : Fin 7782 :=
  decodeStateCode (stateVectorCode vector)

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9046.Shards
