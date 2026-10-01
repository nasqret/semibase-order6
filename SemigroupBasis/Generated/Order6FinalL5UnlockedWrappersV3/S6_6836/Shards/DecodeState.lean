import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6836.Shards.DecodeStatePart00
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6836.Shards.DecodeStatePart01
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6836.Shards.DecodeStatePart02
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6836.Shards.DecodeStatePart03
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6836.Shards.DecodeStatePart04
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6836.Shards.DecodeStatePart05
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6836.Shards.DecodeStatePart06
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6836.Shards.DecodeStatePart07

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6836.Shards

def stateVectorCode
    (vector : Fin 33 -> Fin 6) : Nat :=
  (vector (0 : Fin 33)).val + 6 * ((vector (1 : Fin 33)).val + 6 * ((vector (2 : Fin 33)).val + 6 * ((vector (3 : Fin 33)).val + 6 * ((vector (4 : Fin 33)).val + 6 * ((vector (5 : Fin 33)).val + 6 * ((vector (6 : Fin 33)).val + 6 * ((vector (7 : Fin 33)).val + 6 * ((vector (8 : Fin 33)).val + 6 * ((vector (9 : Fin 33)).val + 6 * ((vector (10 : Fin 33)).val + 6 * ((vector (11 : Fin 33)).val + 6 * ((vector (12 : Fin 33)).val + 6 * ((vector (13 : Fin 33)).val + 6 * ((vector (14 : Fin 33)).val + 6 * ((vector (15 : Fin 33)).val + 6 * ((vector (16 : Fin 33)).val + 6 * ((vector (17 : Fin 33)).val + 6 * ((vector (18 : Fin 33)).val + 6 * ((vector (19 : Fin 33)).val + 6 * ((vector (20 : Fin 33)).val + 6 * ((vector (21 : Fin 33)).val + 6 * ((vector (22 : Fin 33)).val + 6 * ((vector (23 : Fin 33)).val + 6 * ((vector (24 : Fin 33)).val + 6 * ((vector (25 : Fin 33)).val + 6 * ((vector (26 : Fin 33)).val + 6 * ((vector (27 : Fin 33)).val + 6 * ((vector (28 : Fin 33)).val + 6 * ((vector (29 : Fin 33)).val + 6 * ((vector (30 : Fin 33)).val + 6 * ((vector (31 : Fin 33)).val + 6 * ((vector (32 : Fin 33)).val))))))))))))))))))))))))))))))))

def decodeStateCode (code : Nat) : Fin 7782 :=
  if code < 294777079644607125258240 then
    if code < 33264095134569170927616 then
      if code < 2058826691500742541312 then
        if code < 66337338736502636544 then
          if code < 10136713380624138240 then
            if code < 2369190669160808448 then
              if code < 43873901280755712 then
                decodeStateCodeChunk0 code
              else
                if code < 659950703980904448 then
                  decodeStateCodeChunk1 code
                else
                  decodeStateCodeChunk2 code
            else
              if code < 9476762676643233792 then
                if code < 3027313293921681408 then
                  decodeStateCodeChunk3 code
                else
                  decodeStateCodeChunk4 code
              else
                if code < 9520636577923989504 then
                  decodeStateCodeChunk5 code
                else
                  decodeStateCodeChunk6 code
          else
            if code < 56904449961140158464 then
              if code < 12504075970564915200 then
                if code < 11845953345804042240 then
                  decodeStateCodeChunk7 code
                else
                  decodeStateCodeChunk8 code
              else
                if code < 56860576059859402752 then
                  decodeStateCodeChunk9 code
                else
                  decodeStateCodeChunk10 code
            else
              if code < 59229766729020211200 then
                if code < 57520526763840307200 then
                  decodeStateCodeChunk11 code
                else
                  decodeStateCodeChunk12 code
              else
                if code < 59887889353781084160 then
                  decodeStateCodeChunk13 code
                else
                  decodeStateCodeChunk14 code
        else
          if code < 578126397176518017024 then
            if code < 69364652030424317952 then
              if code < 66383125350300647424 then
                decodeStateCodeChunk15 code
              else
                if code < 67041264901720965120 then
                  decodeStateCodeChunk16 code
                else
                  decodeStateCodeChunk17 code
            else
              if code < 521265821116658614272 then
                if code < 511789058440015380480 then
                  decodeStateCodeChunk18 code
                else
                  decodeStateCodeChunk19 code
              else
                if code < 568649634499874783232 then
                  decodeStateCodeChunk20 code
                else
                  decodeStateCodeChunk21 code
          else
            if code < 2049357241140979433472 then
              if code < 2047026440135439286272 then
                if code < 2046982566234158530560 then
                  decodeStateCodeChunk22 code
                else
                  decodeStateCodeChunk23 code
              else
                if code < 2047648001175799529472 then
                  decodeStateCodeChunk24 code
                else
                  decodeStateCodeChunk25 code
            else
              if code < 2056459345837461209088 then
                if code < 2050015363765740306432 then
                  decodeStateCodeChunk26 code
                else
                  decodeStateCodeChunk27 code
              else
                if code < 2056508788609699282944 then
                  decodeStateCodeChunk28 code
                else
                  decodeStateCodeChunk29 code
      else
        if code < 6653396707846471876608 then
          if code < 2115731141461882699776 then
            if code < 2104501264918778806272 then
              if code < 2059492143369042984960 then
                decodeStateCodeChunk30 code
              else
                if code < 2103849134409825533952 then
                  decodeStateCodeChunk31 code
                else
                  decodeStateCodeChunk32 code
            else
              if code < 2106913009288147845120 then
                if code < 2106217834127498280960 then
                  decodeStateCodeChunk33 code
                else
                  decodeStateCodeChunk34 code
              else
                if code < 2113369263109602017280 then
                  decodeStateCodeChunk35 code
                else
                  decodeStateCodeChunk36 code
          else
            if code < 2625728696450180923392 then
              if code < 2568246559271597113344 then
                if code < 2558769796594953879552 then
                  decodeStateCodeChunk37 code
                else
                  decodeStateCodeChunk38 code
              else
                if code < 2615630389581472727040 then
                  decodeStateCodeChunk39 code
                else
                  decodeStateCodeChunk40 code
            else
              if code < 6150470163359619612672 then
                if code < 6140995228762196410368 then
                  decodeStateCodeChunk41 code
                else
                  decodeStateCodeChunk42 code
              else
                if code < 6198506615129936560128 then
                  decodeStateCodeChunk43 code
                else
                  decodeStateCodeChunk44 code
        else
          if code < 30762239503837928873472 then
            if code < 30704713492836428471808 then
              if code < 8197450901514558111744 then
                if code < 6719726734266094387200 then
                  decodeStateCodeChunk45 code
                else
                  decodeStateCodeChunk46 code
              else
                if code < 8700377446001410375680 then
                  decodeStateCodeChunk47 code
                else
                  decodeStateCodeChunk48 code
            else
              if code < 30714197161590074769408 then
                if code < 30705378927778069470720 then
                  decodeStateCodeChunk49 code
                else
                  decodeStateCodeChunk50 code
              else
                if code < 30761574068896287874560 then
                  decodeStateCodeChunk51 code
                else
                  decodeStateCodeChunk52 code
          else
            if code < 32751700967801775587328 then
              if code < 31226591226797513441280 then
                if code < 30771715674081441153024 then
                  decodeStateCodeChunk53 code
                else
                  decodeStateCodeChunk54 code
              else
                if code < 31283451802857372844032 then
                  decodeStateCodeChunk55 code
                else
                  decodeStateCodeChunk56 code
            else
              if code < 32808554214618095419392 then
                if code < 32761170502794835918848 then
                  decodeStateCodeChunk57 code
                else
                  decodeStateCodeChunk58 code
              else
                if code < 32818029166142178066432 then
                  decodeStateCodeChunk59 code
                else
                  decodeStateCodeChunk60 code
    else
      if code < 75797656012482467069952 then
        if code < 73757653052710388760576 then
          if code < 73700790733204606550016 then
            if code < 73691357844429244071936 then
              if code < 33320963006097615175680 then
                decodeStateCodeChunk61 code
              else
                if code < 73691313970527963316224 then
                  decodeStateCodeChunk62 code
                else
                  decodeStateCodeChunk63 code
            else
              if code < 73693719722781524754432 then
                if code < 73691483981895426244608 then
                  decodeStateCodeChunk64 code
                else
                  decodeStateCodeChunk65 code
              else
                if code < 73693851344485367021568 then
                  decodeStateCodeChunk66 code
                else
                  decodeStateCodeChunk67 code
          else
            if code < 73748174546587822718976 then
              if code < 73703152611556887232512 then
                if code < 73700834607105887305728 then
                  decodeStateCodeChunk68 code
                else
                  decodeStateCodeChunk69 code
              else
                if code < 73703284233260729499648 then
                  decodeStateCodeChunk70 code
                else
                  decodeStateCodeChunk71 code
            else
              if code < 73750536424940103401472 then
                if code < 73748218420489103474688 then
                  decodeStateCodeChunk72 code
                else
                  decodeStateCodeChunk73 code
              else
                if code < 73750668469810431787008 then
                  decodeStateCodeChunk74 code
                else
                  decodeStateCodeChunk75 code
        else
          if code < 75738333030639884697600 then
            if code < 74203227338354940837888 then
              if code < 73757784674414231027712 then
                decodeStateCodeChunk76 code
              else
                if code < 73760152037004171804672 then
                  decodeStateCodeChunk77 code
                else
                  decodeStateCodeChunk78 code
            else
              if code < 74269389181486320451584 then
                if code < 74212704101031584071680 then
                  decodeStateCodeChunk79 code
                else
                  decodeStateCodeChunk80 code
              else
                if code < 75738289156738603941888 then
                  decodeStateCodeChunk81 code
                else
                  decodeStateCodeChunk82 code
          else
            if code < 75747817088706748612608 then
              if code < 75740707705546705600512 then
                if code < 75738465143216850862080 then
                  decodeStateCodeChunk83 code
                else
                  decodeStateCodeChunk84 code
              else
                if code < 75747766004048544399360 then
                  decodeStateCodeChunk85 code
                else
                  decodeStateCodeChunk86 code
            else
              if code < 75795157028188684025856 then
                if code < 75750184451296689389568 then
                  decodeStateCodeChunk87 code
                else
                  decodeStateCodeChunk88 code
              else
                if code < 75795288649892526292992 then
                  decodeStateCodeChunk89 code
                else
                  decodeStateCodeChunk90 code
      else
        if code < 104964630803450634829824 then
          if code < 80353514693792557301760 then
            if code < 76259553149776042524672 then
              if code < 75804675853614047428608 then
                decodeStateCodeChunk91 code
              else
                if code < 76250032513198118535168 then
                  decodeStateCodeChunk92 code
                else
                  decodeStateCodeChunk93 code
            else
              if code < 79832300058894059569152 then
                if code < 76316369851934621171712 then
                  decodeStateCodeChunk94 code
                else
                  decodeStateCodeChunk95 code
              else
                if code < 79889153745803524964352 then
                  decodeStateCodeChunk96 code
                else
                  decodeStateCodeChunk97 code
          else
            if code < 104405501805528684036096 then
              if code < 104396017730535160676352 then
                if code < 81888751990854683983872 then
                  decodeStateCodeChunk98 code
                else
                  decodeStateCodeChunk99 code
              else
                if code < 104396151180318222974976 then
                  decodeStateCodeChunk100 code
                else
                  decodeStateCodeChunk101 code
            else
              if code < 104462355069271663312896 then
                if code < 104452880134674240110592 then
                  decodeStateCodeChunk102 code
                else
                  decodeStateCodeChunk103 code
              else
                if code < 104907770227390775427072 then
                  decodeStateCodeChunk104 code
                else
                  decodeStateCodeChunk105 code
        else
          if code < 221133200673680538992640 then
            if code < 106509344880116064190464 then
              if code < 106452476974812665217024 then
                if code < 106443000736862464770048 then
                  decodeStateCodeChunk106 code
                else
                  decodeStateCodeChunk107 code
              else
                if code < 106499861296074028892160 then
                  decodeStateCodeChunk108 code
                else
                  decodeStateCodeChunk109 code
            else
              if code < 221076296731519182176256 then
                if code < 107011611457050640269312 then
                  decodeStateCodeChunk110 code
                else
                  decodeStateCodeChunk111 code
              else
                if code < 221083447669628162015232 then
                  decodeStateCodeChunk112 code
                else
                  decodeStateCodeChunk113 code
          else
            if code < 223632696829645191905280 then
              if code < 221652009556325475287040 then
                if code < 221586330340213733523456 then
                  decodeStateCodeChunk114 code
                else
                  decodeStateCodeChunk115 code
              else
                if code < 223130384533881819758592 then
                  decodeStateCodeChunk116 code
                else
                  decodeStateCodeChunk117 code
            else
              if code < 252357378835907610869760 then
                if code < 251788114868442779566080 then
                  decodeStateCodeChunk118 code
                else
                  decodeStateCodeChunk119 code
              else
                if code < 294765277565162601971712 then
                  decodeStateCodeChunk120 code
                else
                  decodeStateCodeChunk121 code
  else
    if code < 4083726704240806147915776 then
      if code < 1179629511022476466716672 then
        if code < 1107473440442608030187520 then
          if code < 1105381488532865651785728 then
            if code < 297333480165899621105664 then
              if code < 295276978875800055840768 then
                decodeStateCodeChunk122 code
              else
                if code < 296814584043251906641920 then
                  decodeStateCodeChunk123 code
                else
                  decodeStateCodeChunk124 code
            else
              if code < 1105369642985824977887232 then
                if code < 326038550439550695505920 then
                  decodeStateCodeChunk125 code
                else
                  decodeStateCodeChunk126 code
              else
                if code < 1105372670299118899568640 then
                  decodeStateCodeChunk127 code
                else
                  decodeStateCodeChunk128 code
          else
            if code < 1105891478673898749050880 then
              if code < 1105429530874799998844928 then
                if code < 1105426503561506077163520 then
                  decodeStateCodeChunk129 code
                else
                  decodeStateCodeChunk130 code
              else
                if code < 1105438963441890467708928 then
                  decodeStateCodeChunk131 code
                else
                  decodeStateCodeChunk132 code
            else
              if code < 1107418992406783990382592 then
                if code < 1105948339249645151797248 then
                  decodeStateCodeChunk133 code
                else
                  decodeStateCodeChunk134 code
              else
                if code < 1107426099995718132252672 then
                  decodeStateCodeChunk135 code
                else
                  decodeStateCodeChunk136 code
        else
          if code < 1136642915523573683159040 then
            if code < 1107985887098946363654144 then
              if code < 1107482916680636594798592 then
                decodeStateCodeChunk137 code
              else
                if code < 1107928982649377044316160 then
                  decodeStateCodeChunk138 code
                else
                  decodeStateCodeChunk139 code
            else
              if code < 1113614426006247683653632 then
                if code < 1111576922030769388388352 then
                  decodeStateCodeChunk140 code
                else
                  decodeStateCodeChunk141 code
              else
                if code < 1136131170254480015474688 then
                  decodeStateCodeChunk142 code
                else
                  decodeStateCodeChunk143 code
          else
            if code < 1179070426000015753347072 then
              if code < 1138700031062475092705280 then
                if code < 1138178151500434737315840 then
                  decodeStateCodeChunk144 code
                else
                  decodeStateCodeChunk145 code
              else
                if code < 1179063318834258981507072 then
                  decodeStateCodeChunk146 code
                else
                  decodeStateCodeChunk147 code
            else
              if code < 1179120310947378502041600 then
                if code < 1179117766345748399345664 then
                  decodeStateCodeChunk148 code
                else
                  decodeStateCodeChunk149 code
              else
                if code < 1179572650446416607313920 then
                  decodeStateCodeChunk150 code
                else
                  decodeStateCodeChunk151 code
      else
        if code < 3981378245020198302449664 then
          if code < 1209765616336946518301952 then
            if code < 1181164790365360654123008 then
              if code < 1181107929806227454164992 then
                decodeStateCodeChunk152 code
              else
                if code < 1181117362695002816643072 then
                  decodeStateCodeChunk153 code
                else
                  decodeStateCodeChunk154 code
            else
              if code < 1181676491675998107992064 then
                if code < 1181176592461731836854272 then
                  decodeStateCodeChunk155 code
                else
                  decodeStateCodeChunk156 code
              else
                if code < 1185268228604347174354944 then
                  decodeStateCodeChunk157 code
                else
                  decodeStateCodeChunk158 code
          else
            if code < 3979331264282043363950592 then
              if code < 1211822073752751159607296 then
                if code < 1210277493058162154766336 then
                  decodeStateCodeChunk159 code
                else
                  decodeStateCodeChunk160 code
              else
                if code < 1212390679513349753634816 then
                  decodeStateCodeChunk161 code
                else
                  decodeStateCodeChunk162 code
            else
              if code < 3979388124858103223353344 then
                if code < 3979340741044720007184384 then
                  decodeStateCodeChunk163 code
                else
                  decodeStateCodeChunk164 code
              else
                if code < 3979397601620779866587136 then
                  decodeStateCodeChunk165 code
                else
                  decodeStateCodeChunk166 code
        else
          if code < 4012139765482364078456832 then
            if code < 3985538536522927801958400 then
              if code < 3981443880379335422902272 then
                if code < 3981434403599732120223744 then
                  decodeStateCodeChunk167 code
                else
                  decodeStateCodeChunk168 code
              else
                if code < 3985472206496508179447808 then
                  decodeStateCodeChunk169 code
                else
                  decodeStateCodeChunk170 code
            else
              if code < 4010092133933901259210752 then
                if code < 4010035273357841399808000 then
                  decodeStateCodeChunk171 code
                else
                  decodeStateCodeChunk172 code
              else
                if code < 4012082254095996338307072 then
                  decodeStateCodeChunk173 code
                else
                  decodeStateCodeChunk174 code
          else
            if code < 4053088374381119853821952 then
              if code < 4053031389495673032278016 then
                if code < 4053021912732996389044224 then
                  decodeStateCodeChunk175 code
                else
                  decodeStateCodeChunk176 code
              else
                if code < 4053078861056858809958400 then
                  decodeStateCodeChunk177 code
                else
                  decodeStateCodeChunk178 code
            else
              if code < 4055125878356598149087232 then
                if code < 4055078326376853349466112 then
                  decodeStateCodeChunk179 code
                else
                  decodeStateCodeChunk180 code
              else
                if code < 4059219708211204183818240 then
                  decodeStateCodeChunk181 code
                else
                  decodeStateCodeChunk182 code
    else
      if code < 23906697517776155151384576 then
        if code < 5158391635730683437907968 then
          if code < 4276152246080660047921152 then
            if code < 4200405140128875441094656 then
              if code < 4083783572129182887444480 then
                decodeStateCodeChunk183 code
              else
                if code < 4085783037449177426952192 then
                  decodeStateCodeChunk184 code
                else
                  decodeStateCodeChunk185 code
            else
              if code < 4231109193078574757707776 then
                if code < 4200470819344987182858240 then
                  decodeStateCodeChunk186 code
                else
                  decodeStateCodeChunk187 code
              else
                if code < 4233213692515414316482560 then
                  decodeStateCodeChunk188 code
                else
                  decodeStateCodeChunk189 code
          else
            if code < 5086804653521506573811712 then
              if code < 5084757058534628155195392 then
                if code < 5084700197958568295792640 then
                  decodeStateCodeChunk190 code
                else
                  decodeStateCodeChunk191 code
              else
                if code < 5086747178696723234291712 then
                  decodeStateCodeChunk192 code
                else
                  decodeStateCodeChunk193 code
            else
              if code < 5115414341515778834006016 then
                if code < 5090898000749092970692608 then
                  decodeStateCodeChunk194 code
                else
                  decodeStateCodeChunk195 code
              else
                if code < 5117461322169300475281408 then
                  decodeStateCodeChunk196 code
                else
                  decodeStateCodeChunk197 code
        else
          if code < 23876040234797041940840448 then
            if code < 5166579427484765835755520 then
              if code < 5158457797573814817521664 then
                decodeStateCodeChunk198 code
              else
                if code < 5160495301481586475008000 then
                  decodeStateCodeChunk199 code
                else
                  decodeStateCodeChunk200 code
            else
              if code < 23875983374221295538094080 then
                if code < 5189162640270193662197760 then
                  decodeStateCodeChunk201 code
                else
                  decodeStateCodeChunk202 code
              else
                if code < 23875992850577732354654208 then
                  decodeStateCodeChunk203 code
                else
                  decodeStateCodeChunk204 code
          else
            if code < 23878087829783920359456768 then
              if code < 23878030969208173956710400 then
                if code < 23876049718465717273362432 then
                  decodeStateCodeChunk205 code
                else
                  decodeStateCodeChunk206 code
              else
                if code < 23878040445564610773270528 then
                  decodeStateCodeChunk207 code
                else
                  decodeStateCodeChunk208 code
            else
              if code < 23882181184323745272299520 then
                if code < 23878097349912698500104192 then
                  decodeStateCodeChunk209 code
                else
                  decodeStateCodeChunk210 code
              else
                if code < 23884181438863733792980992 then
                  decodeStateCodeChunk211 code
                else
                  decodeStateCodeChunk212 code
      else
        if code < 24099113758247377574510592 then
          if code < 23951721793154732104826880 then
            if code < 23908802017111121296834560 then
              if code < 23906754385562580113424384 then
                decodeStateCodeChunk213 code
              else
                if code < 23908744505826626970009600 then
                  decodeStateCodeChunk214 code
                else
                  decodeStateCodeChunk215 code
            else
              if code < 23949731497496718446051328 then
                if code < 23949674812416577166327808 then
                  decodeStateCodeChunk216 code
                else
                  decodeStateCodeChunk217 code
              else
                if code < 23949741025039295059329024 then
                  decodeStateCodeChunk218 code
                else
                  decodeStateCodeChunk219 code
          else
            if code < 23980388831662049817477120 then
              if code < 23951788005777449997828096 then
                if code < 23951778478234873384550400 then
                  decodeStateCodeChunk220 code
                else
                  decodeStateCodeChunk221 code
              else
                if code < 23957872080002369937948672 then
                  decodeStateCodeChunk222 code
                else
                  decodeStateCodeChunk223 code
            else
              if code < 23982483328241139820265472 then
                if code < 23982426336043768241746944 then
                  decodeStateCodeChunk224 code
                else
                  decodeStateCodeChunk225 code
              else
                if code < 24097067435631847396884480 then
                  decodeStateCodeChunk226 code
                else
                  decodeStateCodeChunk227 code
        else
          if code < 24989551030155083702353920 then
            if code < 24981362449079839187484672 then
              if code < 24170758084082800421978112 then
                if code < 24127819487151061372305408 then
                  decodeStateCodeChunk228 code
                else
                  decodeStateCodeChunk229 code
              else
                if code < 24201510135602014397399040 then
                  decodeStateCodeChunk230 code
                else
                  decodeStateCodeChunk231 code
            else
              if code < 24983410044066717606100992 then
                if code < 24981419309757067182735360 then
                  decodeStateCodeChunk232 code
                else
                  decodeStateCodeChunk233 code
              else
                if code < 24983466948516286925438976 then
                  decodeStateCodeChunk234 code
                else
                  decodeStateCodeChunk235 code
          else
            if code < 25057091391250207290163200 then
              if code < 25014170957695995842887680 then
                if code < 25012123976856359311884288 then
                  decodeStateCodeChunk236 code
                else
                  decodeStateCodeChunk237 code
              else
                if code < 25055101095592507088044032 then
                  decodeStateCodeChunk238 code
                else
                  decodeStateCodeChunk239 code
            else
              if code < 25085758422955358830952448 then
                if code < 25057157596967318314696704 then
                  decodeStateCodeChunk240 code
                else
                  decodeStateCodeChunk241 code
              else
                if code < 25087852919027040871219200 then
                  decodeStateCodeChunk242 code
                else
                  decodeStateCodeChunk243 code

def decodeState
    (vector : Fin 33 -> Fin 6) : Fin 7782 :=
  decodeStateCode (stateVectorCode vector)

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6836.Shards
