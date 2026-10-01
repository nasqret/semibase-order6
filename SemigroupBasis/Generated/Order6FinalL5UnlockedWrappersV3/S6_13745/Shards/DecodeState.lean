import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.Shards.DecodeStatePart00
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.Shards.DecodeStatePart01
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.Shards.DecodeStatePart02
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.Shards.DecodeStatePart03
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.Shards.DecodeStatePart04
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.Shards.DecodeStatePart05
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.Shards.DecodeStatePart06
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.Shards.DecodeStatePart07
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.Shards.DecodeStatePart08
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.Shards.DecodeStatePart09
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.Shards.DecodeStatePart10
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.Shards.DecodeStatePart11

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.Shards

def stateVectorCode
    (vector : Fin 36 -> Fin 6) : Nat :=
  (vector (0 : Fin 36)).val + 6 * ((vector (1 : Fin 36)).val + 6 * ((vector (2 : Fin 36)).val + 6 * ((vector (3 : Fin 36)).val + 6 * ((vector (4 : Fin 36)).val + 6 * ((vector (5 : Fin 36)).val + 6 * ((vector (6 : Fin 36)).val + 6 * ((vector (7 : Fin 36)).val + 6 * ((vector (8 : Fin 36)).val + 6 * ((vector (9 : Fin 36)).val + 6 * ((vector (10 : Fin 36)).val + 6 * ((vector (11 : Fin 36)).val + 6 * ((vector (12 : Fin 36)).val + 6 * ((vector (13 : Fin 36)).val + 6 * ((vector (14 : Fin 36)).val + 6 * ((vector (15 : Fin 36)).val + 6 * ((vector (16 : Fin 36)).val + 6 * ((vector (17 : Fin 36)).val + 6 * ((vector (18 : Fin 36)).val + 6 * ((vector (19 : Fin 36)).val + 6 * ((vector (20 : Fin 36)).val + 6 * ((vector (21 : Fin 36)).val + 6 * ((vector (22 : Fin 36)).val + 6 * ((vector (23 : Fin 36)).val + 6 * ((vector (24 : Fin 36)).val + 6 * ((vector (25 : Fin 36)).val + 6 * ((vector (26 : Fin 36)).val + 6 * ((vector (27 : Fin 36)).val + 6 * ((vector (28 : Fin 36)).val + 6 * ((vector (29 : Fin 36)).val + 6 * ((vector (30 : Fin 36)).val + 6 * ((vector (31 : Fin 36)).val + 6 * ((vector (32 : Fin 36)).val + 6 * ((vector (33 : Fin 36)).val + 6 * ((vector (34 : Fin 36)).val + 6 * ((vector (35 : Fin 36)).val)))))))))))))))))))))))))))))))))))

def decodeStateCode (code : Nat) : Fin 11742 :=
  if code < 7910894361839073032357217792 then
    if code < 6284171060325083670778529280 then
      if code < 6191381422141232732884341504 then
        if code < 6189096983747457126940107264 then
          if code < 6188667127217816988034192896 then
            if code < 6188654845121297799931903872 then
              if code < 6188654843534525192947213056 then
                if code < 6188654835637222958053701120 then
                  decodeStateCodeChunk0 code
                else
                  decodeStateCodeChunk1 code
              else
                if code < 6188654844331567811245105920 then
                  decodeStateCodeChunk2 code
                else
                  if code < 6188654845113984615966814080 then
                    decodeStateCodeChunk3 code
                  else
                    decodeStateCodeChunk4 code
            else
              if code < 6188667070137838504471885824 then
                if code < 6188654845384575138573897600 then
                  decodeStateCodeChunk5 code
                else
                  if code < 6188660982114895237161162240 then
                    decodeStateCodeChunk6 code
                  else
                    decodeStateCodeChunk7 code
              else
                if code < 6188667117784928212671714816 then
                  decodeStateCodeChunk8 code
                else
                  if code < 6188667126208718198950699776 then
                    decodeStateCodeChunk9 code
                  else
                    decodeStateCodeChunk10 code
          else
            if code < 6188728535111891547619824384 then
              if code < 6188728479560017011024906240 then
                if code < 6188667127788177674209064448 then
                  decodeStateCodeChunk11 code
                else
                  decodeStateCodeChunk12 code
              else
                if code < 6188728526943830472601880064 then
                  decodeStateCodeChunk13 code
                else
                  if code < 6188728531952969714305930752 then
                    decodeStateCodeChunk14 code
                  else
                    decodeStateCodeChunk15 code
            else
              if code < 6189096936092851041576846336 then
                if code < 6188728536420592991795203968 then
                  decodeStateCodeChunk16 code
                else
                  if code < 6188728536647477072982627840 then
                    decodeStateCodeChunk17 code
                  else
                    decodeStateCodeChunk18 code
              else
                if code < 6189096936363608945684874240 then
                  decodeStateCodeChunk19 code
                else
                  if code < 6189096983484179940672877056 then
                    decodeStateCodeChunk20 code
                  else
                    decodeStateCodeChunk21 code
        else
          if code < 6189109274311402128647655168 then
            if code < 6189096993216703343706192768 then
              if code < 6189096992909552259782164992 then
                if code < 6189096991644555371207347968 then
                  decodeStateCodeChunk22 code
                else
                  decodeStateCodeChunk23 code
              else
                if code < 6189096992953427076037095936 then
                  decodeStateCodeChunk24 code
                else
                  if code < 6189096993180108062710989312 then
                    decodeStateCodeChunk25 code
                  else
                    decodeStateCodeChunk26 code
            else
              if code < 6189103134648810283265524224 then
                if code < 6189096993224185789186571136 then
                  decodeStateCodeChunk27 code
                else
                  if code < 6189096993224219777461953024 then
                    decodeStateCodeChunk28 code
                  else
                    decodeStateCodeChunk29 code
              else
                if code < 6189109217977279971207840768 then
                  decodeStateCodeChunk30 code
                else
                  if code < 6189109265631681991934231040 then
                    decodeStateCodeChunk31 code
                  else
                    decodeStateCodeChunk32 code
          else
            if code < 6191307732106765313924986368 then
              if code < 6189170627670216459487303680 then
                if code < 6189109275108410789137187328 then
                  decodeStateCodeChunk33 code
                else
                  if code < 6189109275854300990350311936 then
                    decodeStateCodeChunk34 code
                  else
                    decodeStateCodeChunk35 code
              else
                if code < 6189170684486885627475101184 then
                  decodeStateCodeChunk36 code
                else
                  if code < 6191307675290064018081097728 then
                    decodeStateCodeChunk37 code
                  else
                    decodeStateCodeChunk38 code
            else
              if code < 6191381413980483896382359040 then
                if code < 6191381366596637600220628992 then
                  decodeStateCodeChunk39 code
                else
                  if code < 6191381366859913998492653568 then
                    decodeStateCodeChunk40 code
                  else
                    decodeStateCodeChunk41 code
              else
                if code < 6191381414243930497990829568 then
                  decodeStateCodeChunk42 code
                else
                  if code < 6191381421877786200932905728 then
                    decodeStateCodeChunk43 code
                  else
                    decodeStateCodeChunk44 code
      else
        if code < 6205026540460415240291189760 then
          if code < 6191749880260873144650103680 then
            if code < 6191381423728006331752171008 then
              if code < 6191381423457246541825046016 then
                if code < 6191381423413575870022338048 then
                  decodeStateCodeChunk45 code
                else
                  decodeStateCodeChunk46 code
              else
                if code < 6191381423457450476584583040 then
                  decodeStateCodeChunk47 code
                else
                  if code < 6191381423720489897270816640 then
                    decodeStateCodeChunk48 code
                  else
                    decodeStateCodeChunk49 code
            else
              if code < 6191749878681379943047806720 then
                if code < 6191749851559792652015354880 then
                  decodeStateCodeChunk50 code
                else
                  if code < 6191749870784076849776460288 then
                    decodeStateCodeChunk51 code
                  else
                    decodeStateCodeChunk52 code
              else
                if code < 6191749879990283645856312192 then
                  decodeStateCodeChunk53 code
                else
                  if code < 6191749880253324063504843264 then
                    decodeStateCodeChunk54 code
                  else
                    decodeStateCodeChunk55 code
          else
            if code < 6191823571567446945169294848 then
              if code < 6191823569987986516480267008 then
                if code < 6191823514706870902727510016 then
                  decodeStateCodeChunk56 code
                else
                  if code < 6191823562090684281586755072 then
                    decodeStateCodeChunk57 code
                  else
                    decodeStateCodeChunk58 code
              else
                if code < 6191823571516260660979348992 then
                  decodeStateCodeChunk59 code
                else
                  if code < 6191823571567412869822619520 then
                    decodeStateCodeChunk60 code
                  else
                    decodeStateCodeChunk61 code
            else
              if code < 6199708560316829697115980288 then
                if code < 6199266412214110969376601600 then
                  decodeStateCodeChunk62 code
                else
                  if code < 6199340108522546266400945664 then
                    decodeStateCodeChunk63 code
                  else
                    decodeStateCodeChunk64 code
              else
                if code < 6199708569793761627292967424 then
                  decodeStateCodeChunk65 code
                else
                  if code < 6204584421841025879857428480 then
                    decodeStateCodeChunk66 code
                  else
                    decodeStateCodeChunk67 code
        else
          if code < 6207667230903504686236236672 then
            if code < 6207298688816563309859174400 then
              if code < 6206353070059333927156548096 then
                if code < 6205026598066847621920080384 then
                  decodeStateCodeChunk68 code
                else
                  decodeStateCodeChunk69 code
              else
                if code < 6207225073324057291896829440 then
                  decodeStateCodeChunk70 code
                else
                  if code < 6207237327041469810381731328 then
                    decodeStateCodeChunk71 code
                  else
                    decodeStateCodeChunk72 code
            else
              if code < 6207298774370670781208065536 then
                if code < 6207298745633265468434462208 then
                  decodeStateCodeChunk73 code
                else
                  if code < 6207298772527966953541632768 then
                    decodeStateCodeChunk74 code
                  else
                    decodeStateCodeChunk75 code
              else
                if code < 6207667200630512959968624384 then
                  decodeStateCodeChunk76 code
                else
                  if code < 6207667221163498759358378496 then
                    decodeStateCodeChunk77 code
                  else
                    decodeStateCodeChunk78 code
          else
            if code < 6239059689355492835604801024 then
              if code < 6207740922166441493403428352 then
                if code < 6207679484357639943717714816 then
                  decodeStateCodeChunk79 code
                else
                  if code < 6207740884303264687385654784 then
                    decodeStateCodeChunk80 code
                  else
                    decodeStateCodeChunk81 code
              else
                if code < 6236412948789164423271673344 then
                  decodeStateCodeChunk82 code
                else
                  if code < 6236848958062894411599781632 then
                    decodeStateCodeChunk83 code
                  else
                    decodeStateCodeChunk84 code
            else
              if code < 6284158768963892090625689088 then
                if code < 6239501818241612068970984448 then
                  decodeStateCodeChunk85 code
                else
                  if code < 6247019402386095873703159296 then
                    decodeStateCodeChunk86 code
                  else
                    decodeStateCodeChunk87 code
              else
                if code < 6284171003457195315810183168 then
                  decodeStateCodeChunk88 code
                else
                  if code < 6284171058738310933916504832 then
                    decodeStateCodeChunk89 code
                  else
                    decodeStateCodeChunk90 code
    else
      if code < 6764405028375215224261148544 then
        if code < 6303185492802842738323616256 then
          if code < 6287253813338890585995324288 then
            if code < 6284613199499429655970257408 then
              if code < 6284232469769368258884288384 then
                if code < 6284232412908589235839223808 then
                  decodeStateCodeChunk91 code
                else
                  decodeStateCodeChunk92 code
              else
                if code < 6284600924722775858455305984 then
                  decodeStateCodeChunk93 code
                else
                  if code < 6284600926302236221844876160 then
                    decodeStateCodeChunk94 code
                  else
                    decodeStateCodeChunk95 code
            else
              if code < 6286885299937931357120145408 then
                if code < 6284613208164525006185962368 then
                  decodeStateCodeChunk96 code
                else
                  if code < 6284613208976192310845667840 then
                    decodeStateCodeChunk97 code
                  else
                    decodeStateCodeChunk98 code
              else
                if code < 6286885356754836635608770048 then
                  decodeStateCodeChunk99 code
                else
                  if code < 6287253756471002365983470592 then
                    decodeStateCodeChunk100 code
                  else
                    decodeStateCodeChunk101 code
          else
            if code < 6302743314975590686565020416 then
              if code < 6300532567881081121740636672 then
                if code < 6287327504623527348077250048 then
                  decodeStateCodeChunk102 code
                else
                  if code < 6300090428750609059964203776 then
                    decodeStateCodeChunk103 code
                  else
                    decodeStateCodeChunk104 code
              else
                if code < 6300532578169510815716332416 then
                  decodeStateCodeChunk105 code
                else
                  if code < 6302731034626753943976371712 then
                    decodeStateCodeChunk106 code
                  else
                    decodeStateCodeChunk107 code
            else
              if code < 6303173125649696372050375680 then
                if code < 6302804669116625363187050496 then
                  decodeStateCodeChunk108 code
                else
                  if code < 6302804725977403576465073664 then
                    decodeStateCodeChunk109 code
                  else
                    decodeStateCodeChunk110 code
              else
                if code < 6303173182510272405785031168 then
                  decodeStateCodeChunk111 code
                else
                  if code < 6303185435964203629107950592 then
                    decodeStateCodeChunk112 code
                  else
                    decodeStateCodeChunk113 code
        else
          if code < 6761727578366542263415181184 then
            if code < 6477893228139277848072537600 then
              if code < 6475240284256468859548796928 then
                if code < 6303246902225196148591584768 then
                  decodeStateCodeChunk114 code
                else
                  decodeStateCodeChunk115 code
              else
                if code < 6475240341080483335004210688 then
                  decodeStateCodeChunk116 code
                else
                  if code < 6477893171556365768652380160 then
                    decodeStateCodeChunk117 code
                  else
                    decodeStateCodeChunk118 code
            else
              if code < 6761690670843742508504193024 then
                if code < 6485851916377918930955784960 then
                  decodeStateCodeChunk119 code
                else
                  if code < 6522992307009522485382451968 then
                    decodeStateCodeChunk120 code
                  else
                    decodeStateCodeChunk121 code
              else
                if code < 6761690726132171379507045120 then
                  decodeStateCodeChunk122 code
                else
                  if code < 6761690727931000391644141056 then
                    decodeStateCodeChunk123 code
                  else
                    decodeStateCodeChunk124 code
          else
            if code < 6761764418177288021811844608 then
              if code < 6761752136607491681215287168 then
                if code < 6761752126859971257913935360 then
                  decodeStateCodeChunk125 code
                else
                  if code < 6761752135028032332206285568 then
                    decodeStateCodeChunk126 code
                  else
                    decodeStateCodeChunk127 code
              else
                if code < 6761752141075115246757398016 then
                  decodeStateCodeChunk128 code
                else
                  if code < 6761752141345874090509800960 then
                    decodeStateCodeChunk129 code
                  else
                    decodeStateCodeChunk130 code
            else
              if code < 6764405021793926989872931584 then
                if code < 6761764422922982617383556608 then
                  decodeStateCodeChunk131 code
                else
                  if code < 6764404971251396775450691584 then
                    decodeStateCodeChunk132 code
                  else
                    decodeStateCodeChunk133 code
              else
                if code < 6764405023592960063018927616 then
                  decodeStateCodeChunk134 code
                else
                  if code < 6764405028068098934025979392 then
                    decodeStateCodeChunk135 code
                  else
                    decodeStateCodeChunk136 code
      else
        if code < 6859908956701445464517690880 then
          if code < 6780334627477703364078301056 then
            if code < 6780322293734532043808446464 then
              if code < 6777644843455303437487577088 then
                if code < 6777608047555020696618566400 then
                  decodeStateCodeChunk137 code
                else
                  decodeStateCodeChunk138 code
              else
                if code < 6777681745179436037061613056 then
                  decodeStateCodeChunk139 code
                else
                  if code < 6780260936171129916895262208 then
                    decodeStateCodeChunk140 code
                  else
                    decodeStateCodeChunk141 code
            else
              if code < 6780322350551234202383734272 then
                if code < 6780322344013819787288150784 then
                  decodeStateCodeChunk142 code
                else
                  if code < 6780322345812852859708552704 then
                    decodeStateCodeChunk143 code
                  else
                    decodeStateCodeChunk144 code
              else
                if code < 6780322374023568237925344768 then
                  decodeStateCodeChunk145 code
                else
                  if code < 6780322378981522230862247424 then
                    decodeStateCodeChunk146 code
                  else
                    decodeStateCodeChunk147 code
          else
            if code < 6857256069642650977570752000 then
              if code < 6857194660235130936329049600 then
                if code < 6780334659856642668181033728 then
                  decodeStateCodeChunk148 code
                else
                  if code < 6857194651555410825740932608 then
                    decodeStateCodeChunk149 code
                  else
                    decodeStateCodeChunk150 code
              else
                if code < 6857231454555987106181486592 then
                  decodeStateCodeChunk151 code
                else
                  if code < 6857256017564550203889862656 then
                    decodeStateCodeChunk152 code
                  else
                    decodeStateCodeChunk153 code
            else
              if code < 6857268351541738368159499776 then
                if code < 6857256074395690646247194496 then
                  decodeStateCodeChunk154 code
                else
                  if code < 6857268342072254181198890496 then
                    decodeStateCodeChunk155 code
                  else
                    decodeStateCodeChunk156 code
              else
                if code < 6857268356287431892758314880 then
                  decodeStateCodeChunk157 code
                else
                  if code < 6859908951955785688756225536 then
                    decodeStateCodeChunk158 code
                  else
                    decodeStateCodeChunk159 code
        else
          if code < 6875828321178319742784996864 then
            if code < 6873150880617193966020497280 then
              if code < 6873114019959033095833376256 then
                if code < 6859908961454468363259004416 then
                  decodeStateCodeChunk160 code
                else
                  decodeStateCodeChunk161 code
              else
                if code < 6873114029391887073153431040 then
                  decodeStateCodeChunk162 code
                else
                  if code < 6873114030181618240930567680 then
                    decodeStateCodeChunk163 code
                  else
                    decodeStateCodeChunk164 code
            else
              if code < 6875766914892949328625697536 then
                if code < 6873187720742335340944965504 then
                  decodeStateCodeChunk165 code
                else
                  if code < 6874440497435756142562162176 then
                    decodeStateCodeChunk166 code
                  else
                    decodeStateCodeChunk167 code
              else
                if code < 6875766944858823904103523840 then
                  decodeStateCodeChunk168 code
                else
                  if code < 6875828273794523286231631872 then
                    decodeStateCodeChunk169 code
                  else
                    decodeStateCodeChunk170 code
          else
            if code < 6875840607735143309632243200 then
              if code < 6875828349586703730669676032 then
                if code < 6875828325872827179825858048 then
                  decodeStateCodeChunk171 code
                else
                  if code < 6875828325916701054985225728 then
                    decodeStateCodeChunk172 code
                  else
                    decodeStateCodeChunk173 code
              else
                if code < 6875828359019592508208936448 then
                  decodeStateCodeChunk174 code
                else
                  if code < 6875840584087110519308273664 then
                    decodeStateCodeChunk175 code
                  else
                    decodeStateCodeChunk176 code
            else
              if code < 7908167791393148186614681344 then
                if code < 6875840612517398391784705920 then
                  decodeStateCodeChunk177 code
                else
                  if code < 6875840639368226130884248320 then
                    decodeStateCodeChunk178 code
                  else
                    decodeStateCodeChunk179 code
              else
                if code < 7908173925227721992582521344 then
                  decodeStateCodeChunk180 code
                else
                  if code < 7908241484257245260568995328 then
                    decodeStateCodeChunk181 code
                  else
                    decodeStateCodeChunk182 code
  else
    if code < 10218918739936455919559794176 then
      if code < 9738674175282540852064552704 then
        if code < 9644494669512339087494318592 then
          if code < 9627250874561619073620926976 then
            if code < 9627238535860488938845307904 then
              if code < 7955919757943141839444737792 then
                if code < 7917459067715482408317912576 then
                  decodeStateCodeChunk183 code
                else
                  decodeStateCodeChunk184 code
              else
                if code < 7966606049313316735090358016 then
                  decodeStateCodeChunk185 code
                else
                  if code < 8203786814749199219716903128 then
                    decodeStateCodeChunk186 code
                  else
                    decodeStateCodeChunk187 code
            else
              if code < 9627250817744883070433879040 then
                if code < 9627238591141604552598064896 then
                  decodeStateCodeChunk188 code
                else
                  if code < 9627238592721031067022310272 then
                    decodeStateCodeChunk189 code
                  else
                    decodeStateCodeChunk190 code
              else
                if code < 9627250865128697385309528576 then
                  decodeStateCodeChunk191 code
                else
                  if code < 9627250873025999628910169856 then
                    decodeStateCodeChunk192 code
                  else
                    decodeStateCodeChunk193 code
          else
            if code < 9629965114203683106532435968 then
              if code < 9627312274550875887488828928 then
                if code < 9627250874605492831238060928 then
                  decodeStateCodeChunk194 code
                else
                  if code < 9627250875395020047566995968 then
                    decodeStateCodeChunk195 code
                  else
                    decodeStateCodeChunk196 code
              else
                if code < 9627312284027638420468440960 then
                  decodeStateCodeChunk197 code
                else
                  if code < 9629891479713810729557684736 then
                    decodeStateCodeChunk198 code
                  else
                    decodeStateCodeChunk199 code
            else
              if code < 9629965171064292941347217280 then
                if code < 9629965169484798720285192960 then
                  decodeStateCodeChunk200 code
                else
                  if code < 9629965171064258992249905024 then
                    decodeStateCodeChunk201 code
                  else
                    decodeStateCodeChunk202 code
              else
                if code < 9643168188138150198934866432 then
                  decodeStateCodeChunk203 code
                else
                  if code < 9643168196825182626403109376 then
                    decodeStateCodeChunk204 code
                  else
                    decodeStateCodeChunk205 code
        else
          if code < 9722754750800794285837145088 then
            if code < 9645821102808010635906746880 then
              if code < 9645808801977577289064534912 then
                if code < 9645808792500814756084922880 then
                  decodeStateCodeChunk206 code
                else
                  decodeStateCodeChunk207 code
              else
                if code < 9645808830400553132717038080 then
                  decodeStateCodeChunk208 code
                else
                  if code < 9645821082275024836516992768 then
                    decodeStateCodeChunk209 code
                  else
                    decodeStateCodeChunk210 code
            else
              if code < 9645882512230397900219198976 then
                if code < 9645821112288632447239758720 then
                  decodeStateCodeChunk211 code
                else
                  if code < 9645882491704724417709570816 then
                    decodeStateCodeChunk212 code
                  else
                    decodeStateCodeChunk213 code
              else
                if code < 9722742468916568476119487488 then
                  decodeStateCodeChunk214 code
                else
                  if code < 9722742525755207585335153152 then
                    decodeStateCodeChunk215 code
                  else
                    decodeStateCodeChunk216 code
          else
            if code < 9722816160245079004525676544 then
              if code < 9722754807617496444412432896 then
                if code < 9722754798184607669049954816 then
                  decodeStateCodeChunk217 code
                else
                  if code < 9722754806081909899589902080 then
                    decodeStateCodeChunk218 code
                  else
                    decodeStateCodeChunk219 code
              else
                if code < 9722754807880739851371373056 then
                  decodeStateCodeChunk220 code
                else
                  if code < 9722754808407226666740441600 then
                    decodeStateCodeChunk221 code
                  else
                    decodeStateCodeChunk222 code
            else
              if code < 9725469104120372399531638656 then
                if code < 9725395356106781581823874048 then
                  decodeStateCodeChunk223 code
                else
                  if code < 9725469047281733447040288768 then
                    decodeStateCodeChunk224 code
                  else
                    decodeStateCodeChunk225 code
              else
                if code < 9738674120001628358225132544 then
                  decodeStateCodeChunk226 code
                else
                  if code < 9738674167377926304644479488 then
                    decodeStateCodeChunk227 code
                  else
                    decodeStateCodeChunk228 code
      else
        if code < 10200274816474718717167631232 then
          if code < 9741327064162095659569150464 then
            if code < 9741314772800909721636125184 then
              if code < 9738674177103510888186026496 then
                if code < 9738674176832752030647335424 then
                  decodeStateCodeChunk229 code
                else
                  decodeStateCodeChunk230 code
              else
                if code < 9738674177673668314774707072 then
                  decodeStateCodeChunk231 code
                else
                  if code < 9740000649750347393086389120 then
                    decodeStateCodeChunk232 code
                  else
                    decodeStateCodeChunk233 code
            else
              if code < 9741327035482986702296546304 then
                if code < 9741314782226486180118477312 then
                  decodeStateCodeChunk234 code
                else
                  if code < 9741314810459342111409068544 then
                    decodeStateCodeChunk235 code
                  else
                    decodeStateCodeChunk236 code
              else
                if code < 9741327062319392772272686848 then
                  decodeStateCodeChunk237 code
                else
                  if code < 9741327063891540875374459392 then
                    decodeStateCodeChunk238 code
                  else
                    decodeStateCodeChunk239 code
          else
            if code < 10199869518982970060072474112 then
              if code < 9741388471741543062627318528 then
                if code < 9741327091795138055051499264 then
                  decodeStateCodeChunk240 code
                else
                  if code < 9741327092585071385679419904 then
                    decodeStateCodeChunk241 code
                  else
                    decodeStateCodeChunk242 code
              else
                if code < 9741388473576933502440728448 then
                  decodeStateCodeChunk243 code
                else
                  if code < 9741388502007221532370429824 then
                    decodeStateCodeChunk244 code
                  else
                    decodeStateCodeChunk245 code
            else
              if code < 10199906363890604430751600512 then
                if code < 10199894080426714271371666176 then
                  decodeStateCodeChunk246 code
                else
                  if code < 10199906357572559683137676032 then
                    decodeStateCodeChunk247 code
                  else
                    decodeStateCodeChunk248 code
              else
                if code < 10200127437766450492243785216 then
                  decodeStateCodeChunk249 code
                else
                  if code < 10200274814895156854771298048 then
                    decodeStateCodeChunk250 code
                  else
                    decodeStateCodeChunk251 code
        else
          if code < 10217113313188036848141749760 then
            if code < 10215749933197450031885008896 then
              if code < 10200348506991664572206477184 then
                if code < 10200336225107234832808441344 then
                  decodeStateCodeChunk252 code
                else
                  decodeStateCodeChunk253 code
              else
                if code < 10202546968998956199804372480 then
                  decodeStateCodeChunk254 code
                else
                  if code < 10202989102667126612466107904 then
                    decodeStateCodeChunk255 code
                  else
                    decodeStateCodeChunk256 code
            else
              if code < 10216044760030217038689941376 then
                if code < 10215749990811194734747590144 then
                  decodeStateCodeChunk257 code
                else
                  if code < 10215823681320725772599827968 then
                    decodeStateCodeChunk258 code
                  else
                    decodeStateCodeChunk259 code
              else
                if code < 10216192136325522553520748288 then
                  decodeStateCodeChunk260 code
                else
                  if code < 10216192138650737770147342848 then
                    decodeStateCodeChunk261 code
                  else
                    decodeStateCodeChunk262 code
          else
            if code < 10218685336752154678371532800 then
              if code < 10218464310208934994657652224 then
                if code < 10218464229663764564427214848 then
                  decodeStateCodeChunk263 code
                else
                  if code < 10218464286517028146325251968 then
                    decodeStateCodeChunk264 code
                  else
                    decodeStateCodeChunk265 code
              else
                if code < 10218476558924485797532147200 then
                  decodeStateCodeChunk266 code
                else
                  if code < 10218476573103271348009704960 then
                    decodeStateCodeChunk267 code
                  else
                    decodeStateCodeChunk268 code
            else
              if code < 10218906432777009323662080768 then
                if code < 10218845015457353682128570880 then
                  decodeStateCodeChunk269 code
                else
                  if code < 10218845053364404362580118016 then
                    decodeStateCodeChunk270 code
                  else
                    decodeStateCodeChunk271 code
              else
                if code < 10218906434363782060524105216 then
                  decodeStateCodeChunk272 code
                else
                  if code < 10218918659387629326535729152 then
                    decodeStateCodeChunk273 code
                  else
                    decodeStateCodeChunk274 code
    else
      if code < 10311771752542576550200504320 then
        if code < 10311255970103375621373790080 then
          if code < 10295778748961758913597366784 then
            if code < 10295410290629857952952570624 then
              if code < 10295336601955752147877007232 then
                if code < 10295336599323318227759899392 then
                  decodeStateCodeChunk275 code
                else
                  decodeStateCodeChunk276 code
              else
                if code < 10295398008767569093875290880 then
                  decodeStateCodeChunk277 code
                else
                  if code < 10295410235348979312432039936 then
                    decodeStateCodeChunk278 code
                  else
                    decodeStateCodeChunk279 code
            else
              if code < 10295631314270324804856784896 then
                if code < 10295410292428924877966267904 then
                  decodeStateCodeChunk280 code
                else
                  if code < 10295410296969856577866317696 then
                    decodeStateCodeChunk281 code
                  else
                    decodeStateCodeChunk282 code
              else
                if code < 10295778692934719284498596864 then
                  decodeStateCodeChunk283 code
                else
                  if code < 10295778747426172368774835968 then
                    decodeStateCodeChunk284 code
                  else
                    decodeStateCodeChunk285 code
          else
            if code < 10298271974703665931493159680 then
              if code < 10295852383451664199893067776 then
                if code < 10295778749751319870056522240 then
                  decodeStateCodeChunk286 code
                else
                  if code < 10295840156848317030695940864 then
                    decodeStateCodeChunk287 code
                  else
                    decodeStateCodeChunk288 code
              else
                if code < 10295852440268366344682067456 then
                  decodeStateCodeChunk289 code
                else
                  if code < 10298050895782320439068414720 then
                    decodeStateCodeChunk290 code
                  else
                    decodeStateCodeChunk291 code
            else
              if code < 10311255960626613101454872064 then
                if code < 10298493045201188472447223296 then
                  decodeStateCodeChunk292 code
                else
                  if code < 10311255913498763716916232192 then
                    decodeStateCodeChunk293 code
                  else
                    decodeStateCodeChunk294 code
              else
                if code < 10311255968516602069665565440 then
                  decodeStateCodeChunk295 code
                else
                  if code < 10311255969576922815326251776 then
                    decodeStateCodeChunk296 code
                  else
                    decodeStateCodeChunk297 code
        else
          if code < 10311698061082241184978017280 then
            if code < 10311329656671601870155750912 then
              if code < 10311255971156382164335253376 then
                if code < 10311255970863856732905610752 then
                  decodeStateCodeChunk298 code
                else
                  decodeStateCodeChunk299 code
              else
                if code < 10311292821504176546993413632 then
                  decodeStateCodeChunk300 code
                else
                  if code < 10311329609287788487668535296 then
                    decodeStateCodeChunk301 code
                  else
                    decodeStateCodeChunk302 code
            else
              if code < 10311329664832349687923600128 then
                if code < 10311329661358796990316486144 then
                  decodeStateCodeChunk303 code
                else
                  if code < 10311329661432089269713471360 then
                    decodeStateCodeChunk304 code
                  else
                    decodeStateCodeChunk305 code
              else
                if code < 10311329666162972097901070208 then
                  decodeStateCodeChunk306 code
                else
                  if code < 10311513867037584724733167104 then
                    decodeStateCodeChunk307 code
                  else
                    decodeStateCodeChunk308 code
          else
            if code < 10311698117416567415036237568 then
              if code < 10311698108729501108123798016 then
                if code < 10311698061345721565169183744 then
                  decodeStateCodeChunk309 code
                else
                  if code < 10311698108458741305861573120 then
                    decodeStateCodeChunk310 code
                  else
                    decodeStateCodeChunk311 code
              else
                if code < 10311698114257544022491269632 then
                  decodeStateCodeChunk312 code
                else
                  if code < 10311698116626803334310180608 then
                    decodeStateCodeChunk313 code
                  else
                    decodeStateCodeChunk314 code
            else
              if code < 10311698118206263615707616128 then
                if code < 10311698117943020338626009600 then
                  decodeStateCodeChunk315 code
                else
                  if code < 10311698118162389884211870208 then
                    decodeStateCodeChunk316 code
                  else
                    decodeStateCodeChunk317 code
              else
                if code < 10311698118725234048834093952 then
                  decodeStateCodeChunk318 code
                else
                  if code < 10311698118973955492870023680 then
                    decodeStateCodeChunk319 code
                  else
                    decodeStateCodeChunk320 code
      else
        if code < 10313982577133053278574689792 then
          if code < 10313970285508623933682724352 then
            if code < 10313908857110775306518834688 then
              if code < 10311771809512871176669650432 then
                if code < 10311771807933410757413346048 then
                  decodeStateCodeChunk321 code
                else
                  decodeStateCodeChunk322 code
              else
                if code < 10312619293489350533172973056 then
                  decodeStateCodeChunk323 code
                else
                  if code < 10313024590937123739914617728 then
                    decodeStateCodeChunk324 code
                  else
                    decodeStateCodeChunk325 code
            else
              if code < 10313970264975604280974080768 then
                if code < 10313908885562999189269034880 then
                  decodeStateCodeChunk326 code
                else
                  if code < 10313970214703459587780055040 then
                    decodeStateCodeChunk327 code
                  else
                    decodeStateCodeChunk328 code
              else
                if code < 10313970266555098423671940992 then
                  decodeStateCodeChunk329 code
                else
                  if code < 10313970269743252758199180032 then
                    decodeStateCodeChunk330 code
                  else
                    decodeStateCodeChunk331 code
          else
            if code < 10313982548417552004218138112 then
              if code < 10313982525010655467601879040 then
                if code < 10313970299943137457228135936 then
                  decodeStateCodeChunk332 code
                else
                  if code < 10313982491849501536869617664 then
                    decodeStateCodeChunk333 code
                  else
                    decodeStateCodeChunk334 code
              else
                if code < 10313982539233315860452396544 then
                  decodeStateCodeChunk335 code
                else
                  if code < 10313982546881762339482270464 then
                    decodeStateCodeChunk336 code
                  else
                    decodeStateCodeChunk337 code
            else
              if code < 10313982553177699933119371136 then
                if code < 10313982548446801249970818560 then
                  decodeStateCodeChunk338 code
                else
                  if code < 10313982548702765252998553088 then
                    decodeStateCodeChunk339 code
                  else
                    decodeStateCodeChunk340 code
              else
                if code < 10313982553448458778322962304 then
                  decodeStateCodeChunk341 code
                else
                  if code < 10313982575312253019140324096 then
                    decodeStateCodeChunk342 code
                  else
                    decodeStateCodeChunk343 code
        else
          if code < 10314412404925056774400028160 then
            if code < 10314351003553767382128682752 then
              if code < 10314203570507604561979797504 then
                if code < 10313982581871231368556824448 then
                  decodeStateCodeChunk344 code
                else
                  decodeStateCodeChunk345 code
              else
                if code < 10314350948119093100832586752 then
                  decodeStateCodeChunk346 code
                else
                  if code < 10314350995495390106156370432 then
                    decodeStateCodeChunk347 code
                  else
                    decodeStateCodeChunk348 code
            else
              if code < 10314351024192814688503589376 then
                if code < 10314351004972356817687116288 then
                  decodeStateCodeChunk349 code
                else
                  if code < 10314351005235599285001681408 then
                    decodeStateCodeChunk350 code
                  else
                    decodeStateCodeChunk351 code
              else
                if code < 10314351033402643907246848512 then
                  decodeStateCodeChunk352 code
                else
                  if code < 10314412357533930133937123328 then
                    decodeStateCodeChunk353 code
                  else
                    decodeStateCodeChunk354 code
          else
            if code < 10314424686809480061811207680 then
              if code < 10314412414665062702003480448 then
                if code < 10314412412975917676836879104 then
                  decodeStateCodeChunk355 code
                else
                  if code < 10314412414423756244959324032 then
                    decodeStateCodeChunk356 code
                  else
                    decodeStateCodeChunk357 code
              else
                if code < 10314412441508577185304115968 then
                  decodeStateCodeChunk358 code
                else
                  if code < 10314424639579225346141736960 then
                    decodeStateCodeChunk359 code
                  else
                    decodeStateCodeChunk360 code
            else
              if code < 10314424696505645170142240256 then
                if code < 10314424694706782292351154944 then
                  decodeStateCodeChunk361 code
                else
                  if code < 10314424696264305792167628288 then
                    decodeStateCodeChunk362 code
                  else
                    decodeStateCodeChunk363 code
              else
                if code < 10314424696549518919052244864 then
                  decodeStateCodeChunk364 code
                else
                  if code < 10314424723396656644216052480 then
                    decodeStateCodeChunk365 code
                  else
                    decodeStateCodeChunk366 code

def decodeState
    (vector : Fin 36 -> Fin 6) : Fin 11742 :=
  decodeStateCode (stateVectorCode vector)

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.Shards
