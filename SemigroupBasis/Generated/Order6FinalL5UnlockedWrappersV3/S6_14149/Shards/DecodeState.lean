import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.Shards.DecodeStatePart00
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.Shards.DecodeStatePart01
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.Shards.DecodeStatePart02
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.Shards.DecodeStatePart03
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.Shards.DecodeStatePart04
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.Shards.DecodeStatePart05
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.Shards.DecodeStatePart06
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.Shards.DecodeStatePart07
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.Shards.DecodeStatePart08
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.Shards.DecodeStatePart09
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.Shards.DecodeStatePart10

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.Shards

def stateVectorCode
    (vector : Fin 37 -> Fin 6) : Nat :=
  (vector (0 : Fin 37)).val + 6 * ((vector (1 : Fin 37)).val + 6 * ((vector (2 : Fin 37)).val + 6 * ((vector (3 : Fin 37)).val + 6 * ((vector (4 : Fin 37)).val + 6 * ((vector (5 : Fin 37)).val + 6 * ((vector (6 : Fin 37)).val + 6 * ((vector (7 : Fin 37)).val + 6 * ((vector (8 : Fin 37)).val + 6 * ((vector (9 : Fin 37)).val + 6 * ((vector (10 : Fin 37)).val + 6 * ((vector (11 : Fin 37)).val + 6 * ((vector (12 : Fin 37)).val + 6 * ((vector (13 : Fin 37)).val + 6 * ((vector (14 : Fin 37)).val + 6 * ((vector (15 : Fin 37)).val + 6 * ((vector (16 : Fin 37)).val + 6 * ((vector (17 : Fin 37)).val + 6 * ((vector (18 : Fin 37)).val + 6 * ((vector (19 : Fin 37)).val + 6 * ((vector (20 : Fin 37)).val + 6 * ((vector (21 : Fin 37)).val + 6 * ((vector (22 : Fin 37)).val + 6 * ((vector (23 : Fin 37)).val + 6 * ((vector (24 : Fin 37)).val + 6 * ((vector (25 : Fin 37)).val + 6 * ((vector (26 : Fin 37)).val + 6 * ((vector (27 : Fin 37)).val + 6 * ((vector (28 : Fin 37)).val + 6 * ((vector (29 : Fin 37)).val + 6 * ((vector (30 : Fin 37)).val + 6 * ((vector (31 : Fin 37)).val + 6 * ((vector (32 : Fin 37)).val + 6 * ((vector (33 : Fin 37)).val + 6 * ((vector (34 : Fin 37)).val + 6 * ((vector (35 : Fin 37)).val + 6 * ((vector (36 : Fin 37)).val))))))))))))))))))))))))))))))))))))

def decodeStateCode (code : Nat) : Fin 11184 :=
  if code < 144606951644668620812845056 then
    if code < 47754188975150711904927744 then
      if code < 2210769206955809615904768 then
        if code < 886356874765103334948864 then
          if code < 26615553788204443238400 then
            if code < 2217577090968276959232 then
              if code < 172241624111366799360 then
                if code < 34770066764998901760 then
                  decodeStateCodeChunk0 code
                else
                  decodeStateCodeChunk1 code
              else
                if code < 255887216903127564288 then
                  decodeStateCodeChunk2 code
                else
                  if code < 597036048628523728896 then
                    decodeStateCodeChunk3 code
                  else
                    decodeStateCodeChunk4 code
            else
              if code < 24593778606335298895872 then
                if code < 2563544739517676126208 then
                  decodeStateCodeChunk5 code
                else
                  decodeStateCodeChunk6 code
              else
                if code < 24735995857336868536320 then
                  decodeStateCodeChunk7 code
                else
                  if code < 24824401768417591296000 then
                    decodeStateCodeChunk8 code
                  else
                    decodeStateCodeChunk9 code
          else
            if code < 98259813812775369572352 then
              if code < 73719773423192116297728 then
                if code < 27122516717503575490560 then
                  decodeStateCodeChunk10 code
                else
                  decodeStateCodeChunk11 code
              else
                if code < 73876125382722969403392 then
                  decodeStateCodeChunk12 code
                else
                  if code < 74207812076405482586112 then
                    decodeStateCodeChunk13 code
                  else
                    decodeStateCodeChunk14 code
            else
              if code < 884325710568360108883968 then
                if code < 98439938114483512147968 then
                  decodeStateCodeChunk15 code
                else
                  if code < 98800011222294674276352 then
                    decodeStateCodeChunk16 code
                  else
                    decodeStateCodeChunk17 code
              else
                if code < 884470998992451331424256 then
                  decodeStateCodeChunk18 code
                else
                  if code < 884557869316987227734016 then
                    decodeStateCodeChunk19 code
                  else
                    decodeStateCodeChunk20 code
        else
          if code < 1351035739407239979466752 then
            if code < 1326478281078848266174464 then
              if code < 958029652825506752495616 then
                if code < 886854470616479025856512 then
                  decodeStateCodeChunk21 code
                else
                  decodeStateCodeChunk22 code
              else
                if code < 958247596430118906494976 then
                  decodeStateCodeChunk23 code
                else
                  if code < 958598302460006627278848 then
                    decodeStateCodeChunk24 code
                  else
                    decodeStateCodeChunk25 code
            else
              if code < 1326997908940983776575488 then
                if code < 1326615716074610233442304 then
                  decodeStateCodeChunk26 code
                else
                  if code < 1326699390916669514711040 then
                    decodeStateCodeChunk27 code
                  else
                    decodeStateCodeChunk28 code
              else
                if code < 1328661080790734664105984 then
                  decodeStateCodeChunk29 code
                else
                  if code < 1329007019190016542769152 then
                    decodeStateCodeChunk30 code
                  else
                    decodeStateCodeChunk31 code
          else
            if code < 1400163277122958503444480 then
              if code < 1351267898155867098316800 then
                if code < 1351179470307835735179264 then
                  decodeStateCodeChunk32 code
                else
                  decodeStateCodeChunk33 code
              else
                if code < 1353059028238703309881344 then
                  decodeStateCodeChunk34 code
                else
                  if code < 1353566013104953082511360 then
                    decodeStateCodeChunk35 code
                  else
                    decodeStateCodeChunk36 code
            else
              if code < 1424698659566689116487680 then
                if code < 1400319621770172476424192 then
                  decodeStateCodeChunk37 code
                else
                  if code < 1400651323088488749858816 then
                    decodeStateCodeChunk38 code
                  else
                    decodeStateCodeChunk39 code
              else
                if code < 1424883412564982378790912 then
                  decodeStateCodeChunk40 code
                else
                  if code < 1425243507609744181297152 then
                    decodeStateCodeChunk41 code
                  else
                    decodeStateCodeChunk42 code
      else
        if code < 4937317562366662300139520 then
          if code < 3979875505389162013753344 then
            if code < 2284473149212956259516416 then
              if code < 2210999830117891908304896 then
                if code < 2210911424206811185545216 then
                  decodeStateCodeChunk43 code
                else
                  decodeStateCodeChunk44 code
              else
                if code < 2212790982137678760247296 then
                  decodeStateCodeChunk45 code
                else
                  if code < 2213297945066977892499456 then
                    decodeStateCodeChunk46 code
                  else
                    decodeStateCodeChunk47 code
            else
              if code < 3979365303103014800719872 then
                if code < 2284686442184032653410304 then
                  decodeStateCodeChunk48 code
                else
                  if code < 2285041776910583858085888 then
                    decodeStateCodeChunk49 code
                  else
                    decodeStateCodeChunk50 code
              else
                if code < 3979502738098776767987712 then
                  decodeStateCodeChunk51 code
                else
                  if code < 3979545383632381619208192 then
                    decodeStateCodeChunk52 code
                  else
                    decodeStateCodeChunk53 code
          else
            if code < 4053538367049605924782080 then
              if code < 3981894041214183077314560 then
                if code < 3981420203181910872293376 then
                  decodeStateCodeChunk54 code
                else
                  decodeStateCodeChunk55 code
              else
                if code < 4053050328396392558493696 then
                  decodeStateCodeChunk56 code
                else
                  if code < 4053206680355923411599360 then
                    decodeStateCodeChunk57 code
                  else
                    decodeStateCodeChunk58 code
            else
              if code < 4863831563714127810527232 then
                if code < 4863627835253530621378560 then
                  decodeStateCodeChunk59 code
                else
                  if code < 4863716263101561984516096 then
                    decodeStateCodeChunk60 code
                  else
                    decodeStateCodeChunk61 code
              else
                if code < 4864171169647461685100544 then
                  decodeStateCodeChunk62 code
                else
                  if code < 4865848600514658633252864 then
                    decodeStateCodeChunk63 code
                  else
                    decodeStateCodeChunk64 code
        else
          if code < 33234949912222612970274816 then
            if code < 31836705701478625362051072 then
              if code < 4937857781713602430205952 then
                if code < 4937502337301906202820608 then
                  decodeStateCodeChunk65 code
                else
                  decodeStateCodeChunk66 code
              else
                if code < 31834672892010584107646976 then
                  decodeStateCodeChunk67 code
                else
                  if code < 31834845053199209793060864 then
                    decodeStateCodeChunk68 code
                  else
                    decodeStateCodeChunk69 code
            else
              if code < 33161122728176768683868160 then
                if code < 31908368936965500215230464 then
                  decodeStateCodeChunk70 code
                else
                  if code < 31908875921831749987860480 then
                    decodeStateCodeChunk71 code
                  else
                    decodeStateCodeChunk72 code
              else
                if code < 33161301185270228157726720 then
                  decodeStateCodeChunk73 code
                else
                  if code < 33163319735720353166524416 then
                    decodeStateCodeChunk74 code
                  else
                    decodeStateCodeChunk75 code
          else
            if code < 35887865313348591273639936 then
              if code < 35814145576486983557971968 then
                if code < 33235333677237115740487680 then
                  decodeStateCodeChunk76 code
                else
                  decodeStateCodeChunk77 code
              else
                if code < 35814491478324681036005376 then
                  decodeStateCodeChunk78 code
                else
                  if code < 35816538480999786614882304 then
                    decodeStateCodeChunk79 code
                  else
                    decodeStateCodeChunk80 code
            else
              if code < 47752143573873003073634304 then
                if code < 47751968261075802053935104 then
                  decodeStateCodeChunk81 code
                else
                  if code < 47752010906507846948487168 then
                    decodeStateCodeChunk82 code
                  else
                    decodeStateCodeChunk83 code
              else
                if code < 47752224148292705181499392 then
                  decodeStateCodeChunk84 code
                else
                  if code < 47752568470672777662234624 then
                    decodeStateCodeChunk85 code
                  else
                    decodeStateCodeChunk86 code
    else
      if code < 51731899025647388659384320 then
        if code < 49080485610965940962328576 then
          if code < 47850425507444340824211456 then
            if code < 47778605861499400076918784 then
              if code < 47776565176666078926864384 then
                if code < 47754553837826079549554688 then
                  decodeStateCodeChunk87 code
                else
                  decodeStateCodeChunk88 code
              else
                if code < 47776707393917080496504832 then
                  decodeStateCodeChunk89 code
                else
                  if code < 47776800538818859280891904 then
                    decodeStateCodeChunk90 code
                  else
                    decodeStateCodeChunk91 code
            else
              if code < 47825857058703678281613312 then
                if code < 47779103369602973206315008 then
                  decodeStateCodeChunk92 code
                else
                  if code < 47825691171482935744266240 then
                    decodeStateCodeChunk93 code
                  else
                    decodeStateCodeChunk94 code
              else
                if code < 47826198141724551756644352 then
                  decodeStateCodeChunk95 code
                else
                  if code < 47850236016064709240291328 then
                    decodeStateCodeChunk96 code
                  else
                    decodeStateCodeChunk97 code
          else
            if code < 48638337815398375527284736 then
              if code < 48636297108628103736852480 then
                if code < 47850818771161291987943424 then
                  decodeStateCodeChunk98 code
                else
                  decodeStateCodeChunk99 code
              else
                if code < 48636447135433533281009664 then
                  decodeStateCodeChunk100 code
                else
                  if code < 48636534006367428917329920 then
                    decodeStateCodeChunk101 code
                  else
                    decodeStateCodeChunk102 code
            else
              if code < 49078501867144165353062400 then
                if code < 48638835301564998016303104 then
                  decodeStateCodeChunk103 code
                else
                  if code < 49078438644852419784081408 then
                    decodeStateCodeChunk104 code
                  else
                    decodeStateCodeChunk105 code
              else
                if code < 49078613943024987043528704 then
                  decodeStateCodeChunk106 code
                else
                  if code < 49078926661568682509991936 then
                    decodeStateCodeChunk107 code
                  else
                    decodeStateCodeChunk108 code
        else
          if code < 49176764760051706995671040 then
            if code < 49103570982912114349375488 then
              if code < 49102978707178953677733888 then
                if code < 49080670385901184865009664 then
                  decodeStateCodeChunk109 code
                else
                  decodeStateCodeChunk110 code
              else
                if code < 49103065577503489574043648 then
                  decodeStateCodeChunk111 code
                else
                  if code < 49103187174020889188499456 then
                    decodeStateCodeChunk112 code
                  else
                    decodeStateCodeChunk113 code
            else
              if code < 49152272066304562817925120 then
                if code < 49105205790281866118430720 then
                  decodeStateCodeChunk114 code
                else
                  if code < 49152101565011868921102336 then
                    decodeStateCodeChunk115 code
                  else
                    decodeStateCodeChunk116 code
              else
                if code < 49152362132111575329275904 then
                  decodeStateCodeChunk117 code
                else
                  if code < 49152698601063318554738688 then
                    decodeStateCodeChunk118 code
                  else
                    decodeStateCodeChunk119 code
          else
            if code < 49963302914874139159363584 then
              if code < 49962712174727523314171904 then
                if code < 49177177064429633157464064 then
                  decodeStateCodeChunk120 code
                else
                  decodeStateCodeChunk121 code
              else
                if code < 49962797531402465024409600 then
                  decodeStateCodeChunk122 code
                else
                  if code < 49962919105982913998487552 then
                    decodeStateCodeChunk123 code
                  else
                    decodeStateCodeChunk124 code
            else
              if code < 51731341461582607347351552 then
                if code < 49964951849640103331758080 then
                  decodeStateCodeChunk125 code
                else
                  if code < 51731298816049002496131072 then
                    decodeStateCodeChunk126 code
                  else
                    decodeStateCodeChunk127 code
              else
                if code < 51731474128846203515830272 then
                  decodeStateCodeChunk128 code
                else
                  if code < 51731554703265905623695360 then
                    decodeStateCodeChunk129 code
                  else
                    decodeStateCodeChunk130 code
      else
        if code < 83566147006232153863225344 then
          if code < 79586617417305793272741888 then
            if code < 51805528718635173024202752 then
              if code < 51733884392799750176735232 then
                if code < 51733519530123912347123712 then
                  decodeStateCodeChunk131 code
                else
                  decodeStateCodeChunk132 code
              else
                if code < 51805031166758788385734656 then
                  decodeStateCodeChunk133 code
                else
                  if code < 51805192286247365124292608 then
                    decodeStateCodeChunk134 code
                  else
                    decodeStateCodeChunk135 code
            else
              if code < 52615807766067621637914624 then
                if code < 52615607108678554144997376 then
                  decodeStateCodeChunk136 code
                else
                  if code < 52615693979917129651322880 then
                    decodeStateCodeChunk137 code
                  else
                    decodeStateCodeChunk138 code
              else
                if code < 52616204145645689403931392 then
                  decodeStateCodeChunk139 code
                else
                  if code < 52617843624670241948172288 then
                    decodeStateCodeChunk140 code
                  else
                    decodeStateCodeChunk141 code
          else
            if code < 80913070478203721984507904 then
              if code < 79587165512017543113474048 then
                if code < 79586788064844824772083712 then
                  decodeStateCodeChunk142 code
                else
                  decodeStateCodeChunk143 code
              else
                if code < 79660307166355875591880704 then
                  decodeStateCodeChunk144 code
                else
                  if code < 79660814151222125364510720 then
                    decodeStateCodeChunk145 code
                  else
                    decodeStateCodeChunk146 code
            else
              if code < 80986774420460868628119552 then
                if code < 80913253651741569139605504 then
                  decodeStateCodeChunk147 code
                else
                  if code < 80915115813670578894667776 then
                    decodeStateCodeChunk148 code
                  else
                    decodeStateCodeChunk149 code
              else
                if code < 80987271906627491117137920 then
                  decodeStateCodeChunk150 code
                else
                  if code < 83565974845043528177811456 then
                    decodeStateCodeChunk151 code
                  else
                    decodeStateCodeChunk152 code
        else
          if code < 143280634329621254759251968 then
            if code < 143256072140223841604468736 then
              if code < 83639803542738966650290176 then
                if code < 83568163977221832764817408 then
                  decodeStateCodeChunk153 code
                else
                  decodeStateCodeChunk154 code
              else
                if code < 83640177940676016164143104 then
                  decodeStateCodeChunk155 code
                else
                  if code < 143255933162329217930625024 then
                    decodeStateCodeChunk156 code
                  else
                    decodeStateCodeChunk157 code
            else
              if code < 143257980208878224790257664 then
                if code < 143256113206195440391815168 then
                  decodeStateCodeChunk158 code
                else
                  if code < 143256444892889122904997888 then
                    decodeStateCodeChunk159 code
                  else
                    decodeStateCodeChunk160 code
              else
                if code < 143258463443339247913795584 then
                  decodeStateCodeChunk161 code
                else
                  if code < 143280479564434486893477888 then
                    decodeStateCodeChunk162 code
                  else
                    decodeStateCodeChunk163 code
          else
            if code < 144582430521242806445408256 then
              if code < 143282510750568180759920640 then
                if code < 143280721199945790655561728 then
                  decodeStateCodeChunk164 code
                else
                  decodeStateCodeChunk165 code
              else
                if code < 143282723955791454592303104 then
                  decodeStateCodeChunk166 code
                else
                  if code < 144582349946823104337543168 then
                    decodeStateCodeChunk167 code
                  else
                    decodeStateCodeChunk168 code
            else
              if code < 144584390690154960528605184 then
                if code < 144582530027250911199363072 then
                  decodeStateCodeChunk169 code
                else
                  if code < 144582605834040007465107456 then
                    decodeStateCodeChunk170 code
                  else
                    decodeStateCodeChunk171 code
              else
                if code < 144584589621735684355129344 then
                  decodeStateCodeChunk172 code
                else
                  if code < 144584935560134966233792512 then
                    decodeStateCodeChunk173 code
                  else
                    decodeStateCodeChunk174 code
  else
    if code < 6924109112854471567214641152 then
      if code < 620800656326942632584413184 then
        if code < 573023689981947876187570176 then
          if code < 147237789676733172201553920 then
            if code < 147235261019057489606344704 then
              if code < 144607423881405056226951168 then
                if code < 144607106409855388678619136 then
                  decodeStateCodeChunk175 code
                else
                  decodeStateCodeChunk176 code
              else
                if code < 144608997045946329644138496 then
                  decodeStateCodeChunk177 code
                else
                  if code < 144609499292431241095151616 then
                    decodeStateCodeChunk178 code
                  else
                    decodeStateCodeChunk179 code
            else
              if code < 147235436295293106225414144 then
                if code < 147235401525226341226512384 then
                  decodeStateCodeChunk180 code
                else
                  decodeStateCodeChunk181 code
              else
                if code < 147235771118971200497614848 then
                  decodeStateCodeChunk182 code
                else
                  if code < 147237311092905684838121472 then
                    decodeStateCodeChunk183 code
                  else
                    decodeStateCodeChunk184 code
          else
            if code < 176417165034147739374452736 then
              if code < 175090730795153460106887168 then
                if code < 175090558633964834421473280 then
                  decodeStateCodeChunk185 code
                else
                  decodeStateCodeChunk186 code
              else
                if code < 175092591465369826316255232 then
                  decodeStateCodeChunk187 code
                else
                  if code < 176416994386608707875110912 then
                    decodeStateCodeChunk188 code
                  else
                    decodeStateCodeChunk189 code
            else
              if code < 179070050710705599965822976 then
                if code < 176417542481320459892625408 then
                  decodeStateCodeChunk190 code
                else
                  if code < 179069877013930429453959168 then
                    decodeStateCodeChunk191 code
                  else
                    decodeStateCodeChunk192 code
              else
                if code < 179070420282513521657241600 then
                  decodeStateCodeChunk193 code
                else
                  if code < 573023599916140863676219392 then
                    decodeStateCodeChunk194 code
                  else
                    decodeStateCodeChunk195 code
        else
          if code < 575234353328492212220067840 then
            if code < 573907900333405135429435392 then
              if code < 573024196952189492199948288 then
                if code < 573023855869168618724917248 then
                  decodeStateCodeChunk196 code
                else
                  decodeStateCodeChunk197 code
              else
                if code < 573048249041673664648445952 then
                  decodeStateCodeChunk198 code
                else
                  if code < 573048433794671957910749184 then
                    decodeStateCodeChunk199 code
                  else
                    decodeStateCodeChunk200 code
            else
              if code < 574350076617759265835188224 then
                if code < 573908080457706843572011008 then
                  decodeStateCodeChunk201 code
                else
                  if code < 573908440530814654734139392 then
                    decodeStateCodeChunk202 code
                  else
                    decodeStateCodeChunk203 code
              else
                if code < 574350242468418423971905536 then
                  decodeStateCodeChunk204 code
                else
                  if code < 574350569394793817523093504 then
                    decodeStateCodeChunk205 code
                  else
                    decodeStateCodeChunk206 code
          else
            if code < 606184891646585365831090176 then
              if code < 575234893525901731524771840 then
                if code < 575234538191175258684260352 then
                  decodeStateCodeChunk207 code
                else
                  decodeStateCodeChunk208 code
              else
                if code < 604858419676035985113612288 then
                  decodeStateCodeChunk209 code
                else
                  if code < 604858798812353902764097536 then
                    decodeStateCodeChunk210 code
                  else
                    decodeStateCodeChunk211 code
            else
              if code < 620776078335628441477447680 then
                if code < 620775571394636092985573376 then
                  decodeStateCodeChunk212 code
                else
                  if code < 620775741895928786882396160 then
                    decodeStateCodeChunk213 code
                  else
                    decodeStateCodeChunk214 code
              else
                if code < 620776168430687542619209728 then
                  decodeStateCodeChunk215 code
                else
                  if code < 620800300992216159743901696 then
                    decodeStateCodeChunk216 code
                  else
                    decodeStateCodeChunk217 code
      else
        if code < 748114158615916550018826240 then
          if code < 653936668814884139553521664 then
            if code < 622102223343240844243107840 then
              if code < 621660075547673278808064000 then
                if code < 621659895423371570665488384 then
                  decodeStateCodeChunk218 code
                else
                  decodeStateCodeChunk219 code
              else
                if code < 621660464051071941009801216 then
                  decodeStateCodeChunk220 code
                else
                  if code < 622102095421569343319703552 then
                    decodeStateCodeChunk221 code
                  else
                    decodeStateCodeChunk222 code
            else
              if code < 622986561711429723850014720 then
                if code < 622102555029934526756290560 then
                  decodeStateCodeChunk223 code
                else
                  if code < 622986348418458647456120832 then
                    decodeStateCodeChunk224 code
                  else
                    decodeStateCodeChunk225 code
              else
                if code < 622986917046768455904608256 then
                  decodeStateCodeChunk226 code
                else
                  if code < 652610414766002420349665280 then
                    decodeStateCodeChunk227 code
                  else
                    decodeStateCodeChunk228 code
          else
            if code < 716304077879177953822113792 then
              if code < 716279533078470081606844416 then
                if code < 653937171039432100364156928 then
                  decodeStateCodeChunk229 code
                else
                  decodeStateCodeChunk230 code
              else
                if code < 716279698929129239743561728 then
                  decodeStateCodeChunk231 code
                else
                  if code < 716280025855504633294749696 then
                    decodeStateCodeChunk232 code
                  else
                    decodeStateCodeChunk233 code
            else
              if code < 717605976794227037517643776 then
                if code < 716304262741861000286306304 then
                  decodeStateCodeChunk234 code
                else
                  if code < 716304618076587473126817792 then
                    decodeStateCodeChunk235 code
                  else
                    decodeStateCodeChunk236 code
              else
                if code < 717606147295519731414466560 then
                  decodeStateCodeChunk237 code
                else
                  if code < 717606483735219386009518080 then
                    decodeStateCodeChunk238 code
                  else
                    decodeStateCodeChunk239 code
        else
          if code < 6877683333818588342047997952 then
            if code < 6876283459626600922443939840 then
              if code < 749440758566635966700716032 then
                if code < 748114660840464510829461504 then
                  decodeStateCodeChunk240 code
                else
                  decodeStateCodeChunk241 code
              else
                if code < 749441132964572546029584384 then
                  decodeStateCodeChunk242 code
                else
                  if code < 6876283243240519805756768256 then
                    decodeStateCodeChunk243 code
                  else
                    decodeStateCodeChunk244 code
            else
              if code < 6877609644113412161009614848 then
                if code < 6876285445052255580482174976 then
                  decodeStateCodeChunk245 code
                else
                  if code < 6876356989828208997294931968 then
                    decodeStateCodeChunk246 code
                  else
                    decodeStateCodeChunk247 code
              else
                if code < 6877609732541260192372752384 then
                  decodeStateCodeChunk248 code
                else
                  if code < 6877611694253071208162525184 then
                    decodeStateCodeChunk249 code
                  else
                    decodeStateCodeChunk250 code
          else
            if code < 6880336235092318107948023808 then
              if code < 6880262543763807579521679360 then
                if code < 6877683509204508711868956672 then
                  decodeStateCodeChunk251 code
                else
                  decodeStateCodeChunk252 code
              else
                if code < 6880262630634436795287994368 then
                  decodeStateCodeChunk253 code
                else
                  if code < 6880264605025500601346162688 then
                    decodeStateCodeChunk254 code
                  else
                    decodeStateCodeChunk255 code
            else
              if code < 6924035350450240963964043264 then
                if code < 6880336424605634690172321792 then
                  decodeStateCodeChunk256 code
                else
                  if code < 6924035195663117245457891328 then
                    decodeStateCodeChunk257 code
                  else
                    decodeStateCodeChunk258 code
              else
                if code < 6924037383215835103937691648 then
                  decodeStateCodeChunk259 code
                else
                  if code < 6924108890194422567379402752 then
                    decodeStateCodeChunk260 code
                  else
                    decodeStateCodeChunk261 code
    else
      if code < 20660684412024521826100051968 then
        if code < 7450633441505982689367293952 then
          if code < 7019539190603368404891992064 then
            if code < 6925435570632423243347656704 then
              if code < 6925361822420790344681521152 then
                if code < 6925361643985633835848040448 then
                  decodeStateCodeChunk262 code
                else
                  decodeStateCodeChunk263 code
              else
                if code < 6925363840971240469690318848 then
                  decodeStateCodeChunk264 code
                else
                  if code < 6925435390507512175465070592 then
                    decodeStateCodeChunk265 code
                  else
                    decodeStateCodeChunk266 code
            else
              if code < 6928016747005288524552339456 then
                if code < 6928014581521143010292662272 then
                  decodeStateCodeChunk267 code
                else
                  if code < 6928016543189080124801679360 then
                    decodeStateCodeChunk268 code
                  else
                    decodeStateCodeChunk269 code
              else
                if code < 6928088358118580677867732992 then
                  decodeStateCodeChunk270 code
                else
                  if code < 7019539103733043868995682304 then
                    decodeStateCodeChunk271 code
                  else
                    decodeStateCodeChunk272 code
          else
            if code < 7023518429922563892002684928 then
              if code < 7020865544224069080770936832 then
                if code < 7019541160190544700577415168 then
                  decodeStateCodeChunk273 code
                else
                  decodeStateCodeChunk274 code
              else
                if code < 7020865632651917112134074368 then
                  decodeStateCodeChunk275 code
                else
                  if code < 7020867594363728127923847168 then
                    decodeStateCodeChunk276 code
                  else
                    decodeStateCodeChunk277 code
            else
              if code < 7023520680719510446691844096 then
                if code < 7023518516792888427898994688 then
                  decodeStateCodeChunk278 code
                else
                  if code < 7023520476903302046941184000 then
                    decodeStateCodeChunk279 code
                  else
                    decodeStateCodeChunk280 code
              else
                if code < 7449306969513496358009438208 then
                  decodeStateCodeChunk281 code
                else
                  if code < 7450633256643299642903101440 then
                    decodeStateCodeChunk282 code
                  else
                    decodeStateCodeChunk283 code
        else
          if code < 20629733897398335364097114112 then
            if code < 7592562897900882653217816576 then
              if code < 7497059026180483240786132992 then
                if code < 7497058808236878628632133632 then
                  decodeStateCodeChunk284 code
                else
                  decodeStateCodeChunk285 code
              else
                if code < 7498385308660262349659701248 then
                  decodeStateCodeChunk286 code
                else
                  if code < 7592562703649184732671901696 then
                    decodeStateCodeChunk287 code
                  else
                    decodeStateCodeChunk288 code
            else
              if code < 20628849767599360856322736128 then
                if code < 7593889175773292767872024576 then
                  decodeStateCodeChunk289 code
                else
                  if code < 7593889398433341767707262976 then
                    decodeStateCodeChunk290 code
                  else
                    decodeStateCodeChunk291 code
              else
                if code < 20628850194017119720867627008 then
                  decodeStateCodeChunk292 code
                else
                  if code < 20628874359783882111754174464 then
                    decodeStateCodeChunk293 code
                  else
                    decodeStateCodeChunk294 code
          else
            if code < 20630201149204044209379606528 then
              if code < 20630176073690001811382992896 then
                if code < 20629734153336738485385560064 then
                  decodeStateCodeChunk295 code
                else
                  decodeStateCodeChunk296 code
              else
                if code < 20630176552281141615626551296 then
                  decodeStateCodeChunk297 code
                else
                  if code < 20630200689624928293463523328 then
                    decodeStateCodeChunk298 code
                  else
                    decodeStateCodeChunk299 code
            else
              if code < 20632829131308378791255998464 then
                if code < 20631060535190294635430805504 then
                  decodeStateCodeChunk300 code
                else
                  if code < 20632828927557981243426471936 then
                    decodeStateCodeChunk301 code
                  else
                    decodeStateCodeChunk302 code
              else
                if code < 20633713227953308564539310080 then
                  decodeStateCodeChunk303 code
                else
                  if code < 20633713483891711685827756032 then
                    decodeStateCodeChunk304 code
                  else
                    decodeStateCodeChunk305 code
      else
        if code < 20772106008705290846997577728 then
          if code < 20677952746313852126880595968 then
            if code < 20676626127475418208833372160 then
              if code < 20664663576780022086566412288 then
                if code < 20662010718107850464280182784 then
                  decodeStateCodeChunk306 code
                else
                  decodeStateCodeChunk307 code
              else
                if code < 20676601563655374131410501632 then
                  decodeStateCodeChunk308 code
                else
                  if code < 20676601767391147045479776256 then
                    decodeStateCodeChunk309 code
                  else
                    decodeStateCodeChunk310 code
            else
              if code < 20677486399560915851667308544 then
                if code < 20676626388042517915241545728 then
                  decodeStateCodeChunk311 code
                else
                  if code < 20677485944610496520870952960 then
                    decodeStateCodeChunk312 code
                  else
                    decodeStateCodeChunk313 code
              else
                if code < 20677928177755426711136108544 then
                  decodeStateCodeChunk314 code
                else
                  if code < 20677928552072927804783591424 then
                    decodeStateCodeChunk315 code
                  else
                    decodeStateCodeChunk316 code
          else
            if code < 20681465275165469721313148928 then
              if code < 20678812563448930438918176768 then
                if code < 20678812302859893781869625344 then
                  decodeStateCodeChunk317 code
                else
                  decodeStateCodeChunk318 code
              else
                if code < 20680580922706446213703532544 then
                  decodeStateCodeChunk319 code
                else
                  if code < 20680581405955531870587322368 then
                    decodeStateCodeChunk320 code
                  else
                    decodeStateCodeChunk321 code
            else
              if code < 20709762850610875710843125760 then
                if code < 20681465730115889522294489088 then
                  decodeStateCodeChunk322 code
                else
                  if code < 20708436411852869599657721856 then
                    decodeStateCodeChunk323 code
                  else
                    decodeStateCodeChunk324 code
              else
                if code < 20712415709283047333129355264 then
                  decodeStateCodeChunk325 code
                else
                  if code < 20772105525426955922593284096 then
                    decodeStateCodeChunk326 code
                  else
                    decodeStateCodeChunk327 code
        else
          if code < 20807919984094914762504142848 then
            if code < 20773456679720956740054810624 then
              if code < 20772130600926373686829645824 then
                if code < 20772130093963444387697393664 then
                  decodeStateCodeChunk328 code
                else
                  decodeStateCodeChunk329 code
              else
                if code < 20773432111191780591830827008 then
                  decodeStateCodeChunk330 code
                else
                  if code < 20773432480865960466598330368 then
                    decodeStateCodeChunk331 code
                  else
                    decodeStateCodeChunk332 code
            else
              if code < 20803940141399891911800520704 then
                if code < 20776084827909944620231950336 then
                  decodeStateCodeChunk333 code
                else
                  if code < 20776085027002396315421245440 then
                    decodeStateCodeChunk334 code
                  else
                    decodeStateCodeChunk335 code
              else
                if code < 20803940681641175332385980416 then
                  decodeStateCodeChunk336 code
                else
                  if code < 20805267101555340843486806016 then
                    decodeStateCodeChunk337 code
                  else
                    decodeStateCodeChunk338 code
          else
            if code < 27554211210913082550874275840 then
              if code < 27506459329544268235357028352 then
                if code < 27505132966622300487957872640 then
                  decodeStateCodeChunk339 code
                else
                  decodeStateCodeChunk340 code
              else
                if code < 27509112211820598746689830912 then
                  decodeStateCodeChunk341 code
                else
                  if code < 27552884791130538743615717376 then
                    decodeStateCodeChunk342 code
                  else
                    decodeStateCodeChunk343 code
            else
              if code < 27648388899726131170847490048 then
                if code < 27556864093189413062207078400 then
                  decodeStateCodeChunk344 code
                else
                  if code < 27556864349127816183495524352 then
                    decodeStateCodeChunk345 code
                  else
                    decodeStateCodeChunk346 code
              else
                if code < 27649715338615758985875161088 then
                  decodeStateCodeChunk347 code
                else
                  if code < 27652368197551174015845924864 then
                    decodeStateCodeChunk348 code
                  else
                    decodeStateCodeChunk349 code

def decodeState
    (vector : Fin 37 -> Fin 6) : Fin 11184 :=
  decodeStateCode (stateVectorCode vector)

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.Shards
