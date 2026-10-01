import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.Shards.DecodeStatePart00
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.Shards.DecodeStatePart01
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.Shards.DecodeStatePart02
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.Shards.DecodeStatePart03
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.Shards.DecodeStatePart04
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.Shards.DecodeStatePart05
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.Shards.DecodeStatePart06
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.Shards.DecodeStatePart07
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.Shards.DecodeStatePart08
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.Shards.DecodeStatePart09
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.Shards.DecodeStatePart10
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.Shards.DecodeStatePart11

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.Shards

def stateVectorCode
    (vector : Fin 42 -> Fin 6) : Nat :=
  (vector (0 : Fin 42)).val + 6 * ((vector (1 : Fin 42)).val + 6 * ((vector (2 : Fin 42)).val + 6 * ((vector (3 : Fin 42)).val + 6 * ((vector (4 : Fin 42)).val + 6 * ((vector (5 : Fin 42)).val + 6 * ((vector (6 : Fin 42)).val + 6 * ((vector (7 : Fin 42)).val + 6 * ((vector (8 : Fin 42)).val + 6 * ((vector (9 : Fin 42)).val + 6 * ((vector (10 : Fin 42)).val + 6 * ((vector (11 : Fin 42)).val + 6 * ((vector (12 : Fin 42)).val + 6 * ((vector (13 : Fin 42)).val + 6 * ((vector (14 : Fin 42)).val + 6 * ((vector (15 : Fin 42)).val + 6 * ((vector (16 : Fin 42)).val + 6 * ((vector (17 : Fin 42)).val + 6 * ((vector (18 : Fin 42)).val + 6 * ((vector (19 : Fin 42)).val + 6 * ((vector (20 : Fin 42)).val + 6 * ((vector (21 : Fin 42)).val + 6 * ((vector (22 : Fin 42)).val + 6 * ((vector (23 : Fin 42)).val + 6 * ((vector (24 : Fin 42)).val + 6 * ((vector (25 : Fin 42)).val + 6 * ((vector (26 : Fin 42)).val + 6 * ((vector (27 : Fin 42)).val + 6 * ((vector (28 : Fin 42)).val + 6 * ((vector (29 : Fin 42)).val + 6 * ((vector (30 : Fin 42)).val + 6 * ((vector (31 : Fin 42)).val + 6 * ((vector (32 : Fin 42)).val + 6 * ((vector (33 : Fin 42)).val + 6 * ((vector (34 : Fin 42)).val + 6 * ((vector (35 : Fin 42)).val + 6 * ((vector (36 : Fin 42)).val + 6 * ((vector (37 : Fin 42)).val + 6 * ((vector (38 : Fin 42)).val + 6 * ((vector (39 : Fin 42)).val + 6 * ((vector (40 : Fin 42)).val + 6 * ((vector (41 : Fin 42)).val)))))))))))))))))))))))))))))))))))))))))

def decodeStateCode (code : Nat) : Fin 11742 :=
  if code < 161529073543281848352687341807616 then
    if code < 6683918408355261710719896256512 then
      if code < 1119282333501899916014858864640 then
        if code < 36128452646351489033385234432 then
          if code < 5328437306423447868179742720 then
            if code < 27858384882609570785525760 then
              if code < 27719530829181458841600 then
                if code < 3070485731905350082560 then
                  decodeStateCodeChunk0 code
                else
                  decodeStateCodeChunk1 code
              else
                if code < 4007050085802381901037568 then
                  decodeStateCodeChunk2 code
                else
                  if code < 23900547098705564426969088 then
                    decodeStateCodeChunk3 code
                  else
                    decodeStateCodeChunk4 code
            else
              if code < 1317161484167236578774614016 then
                if code < 171111214390537554296832000 then
                  decodeStateCodeChunk5 code
                else
                  if code < 1146047199832484886447857664 then
                    decodeStateCodeChunk6 code
                  else
                    decodeStateCodeChunk7 code
              else
                if code < 5185178269043694445231349760 then
                  decodeStateCodeChunk8 code
                else
                  if code < 5328434150661476585164972032 then
                    decodeStateCodeChunk9 code
                  else
                    decodeStateCodeChunk10 code
          else
            if code < 32093303996329968844430659584 then
              if code < 30943277484896450853165551616 then
                if code < 6474484420438175570460672000 then
                  decodeStateCodeChunk11 code
                else
                  decodeStateCodeChunk12 code
              else
                if code < 30943302029711774895811350528 then
                  decodeStateCodeChunk13 code
                else
                  if code < 30947281360266544976340209664 then
                    decodeStateCodeChunk14 code
                  else
                    decodeStateCodeChunk15 code
            else
              if code < 36104579733229505192125550592 then
                if code < 36100600488228647952486715392 then
                  decodeStateCodeChunk16 code
                else
                  if code < 36101263624433499535173439488 then
                    decodeStateCodeChunk17 code
                  else
                    decodeStateCodeChunk18 code
              else
                if code < 36104604381762748789137297408 then
                  decodeStateCodeChunk19 code
                else
                  if code < 36124473315006582489976098816 then
                    decodeStateCodeChunk20 code
                  else
                    decodeStateCodeChunk21 code
        else
          if code < 1113957902886037560936709982208 then
            if code < 36271736179846561506511835136 then
              if code < 36247835717987339196311556096 then
                if code < 36128919358749518582416625664 then
                  decodeStateCodeChunk22 code
                else
                  decodeStateCodeChunk23 code
              else
                if code < 36248498940258372041323794432 then
                  decodeStateCodeChunk24 code
                else
                  if code < 36271711635031034343952699392 then
                    decodeStateCodeChunk25 code
                  else
                    decodeStateCodeChunk26 code
            else
              if code < 37274941994812942450507075584 then
                if code < 36272374837836671190739931136 then
                  decodeStateCodeChunk27 code
                else
                  if code < 37247089836690101369608556544 then
                    decodeStateCodeChunk28 code
                  else
                    decodeStateCodeChunk29 code
              else
                if code < 37418422037668952918092369920 then
                  decodeStateCodeChunk30 code
                else
                  if code < 1113957878322268711540777715712 then
                    decodeStateCodeChunk31 code
                  else
                    decodeStateCodeChunk32 code
          else
            if code < 1114125010717337395288573151232 then
              if code < 1114101137804478654854998001664 then
                if code < 1113981754239261432092683118592 then
                  decodeStateCodeChunk33 code
                else
                  if code < 1114101134733992922988830001152 then
                    decodeStateCodeChunk34 code
                  else
                    decodeStateCodeChunk35 code
              else
                if code < 1114105117135019003264951617536 then
                  decodeStateCodeChunk36 code
                else
                  if code < 1114125010139240467269420091392 then
                    decodeStateCodeChunk37 code
                  else
                    decodeStateCodeChunk38 code
            else
              if code < 1115103925522101187924713768960 then
                if code < 1114128989469795415079873120256 then
                  decodeStateCodeChunk39 code
                else
                  if code < 1114128992948293804380037318656 then
                    decodeStateCodeChunk40 code
                  else
                    decodeStateCodeChunk41 code
              else
                if code < 1115271057320119198253496895488 then
                  decodeStateCodeChunk42 code
                else
                  if code < 1119139077175466560232448043008 then
                    decodeStateCodeChunk43 code
                  else
                    decodeStateCodeChunk44 code
      else
        if code < 1150206402253803227201385068544 then
          if code < 1146190458888022937096450930688 then
            if code < 1120432363254452063186643290112 then
              if code < 1119286312814093636139315628032 then
                if code < 1119286312387639120877058164736 then
                  decodeStateCodeChunk45 code
                else
                  decodeStateCodeChunk46 code
              else
                if code < 1119286315884038256556354308096 then
                  decodeStateCodeChunk47 code
                else
                  if code < 1119286340618388639318552840192 then
                    decodeStateCodeChunk48 code
                  else
                    decodeStateCodeChunk49 code
            else
              if code < 1145044411688205186827867633664 then
                if code < 1144901155788211620074815272960 then
                  decodeStateCodeChunk50 code
                else
                  if code < 1144901180351980283316675729408 then
                    decodeStateCodeChunk51 code
                  else
                    decodeStateCodeChunk52 code
              else
                if code < 1145044412218889162219570411520 then
                  decodeStateCodeChunk53 code
                else
                  if code < 1145048391530505234700486391808 then
                    decodeStateCodeChunk54 code
                  else
                    decodeStateCodeChunk55 code
          else
            if code < 1150202174045033529931619432448 then
              if code < 1150082351552774354820601927680 then
                if code < 1150058478724431178230938916864 then
                  decodeStateCodeChunk56 code
                else
                  if code < 1150059138809367269828341979136 then
                    decodeStateCodeChunk57 code
                  else
                    decodeStateCodeChunk58 code
              else
                if code < 1150201731554714414923656910848 then
                  decodeStateCodeChunk59 code
                else
                  if code < 1150201734643349114166384187392 then
                    decodeStateCodeChunk60 code
                  else
                    decodeStateCodeChunk61 code
            else
              if code < 1150205713954965288168074754048 then
                if code < 1150202395289022913399365752832 then
                  decodeStateCodeChunk62 code
                else
                  if code < 1150202398359494122335397804032 then
                    decodeStateCodeChunk63 code
                  else
                    decodeStateCodeChunk64 code
              else
                if code < 1150205714467222224865131804672 then
                  decodeStateCodeChunk65 code
                else
                  if code < 1150206377178303809293481072640 then
                    decodeStateCodeChunk66 code
                  else
                    decodeStateCodeChunk67 code
        else
          if code < 1151347781824228073660363495424 then
            if code < 1150229589938872698844301211648 then
              if code < 1150226270675316703973495199744 then
                if code < 1150225608048999505439624017920 then
                  decodeStateCodeChunk68 code
                else
                  decodeStateCodeChunk69 code
              else
                if code < 1150226271289712192992984184832 then
                  decodeStateCodeChunk70 code
                else
                  if code < 1150229586868401794770988881920 then
                    decodeStateCodeChunk71 code
                  else
                    decodeStateCodeChunk72 code
            else
              if code < 1150230250601379451574514800640 then
                if code < 1150229590450617883539764164608 then
                  decodeStateCodeChunk73 code
                else
                  if code < 1150230029358984153186635937792 then
                    decodeStateCodeChunk74 code
                  else
                    decodeStateCodeChunk75 code
              else
                if code < 1150230253671865183401500719104 then
                  decodeStateCodeChunk76 code
                else
                  if code < 1150230278237198877112291743744 then
                    decodeStateCodeChunk77 code
                  else
                    decodeStateCodeChunk78 code
          else
            if code < 4491936092766696187355361202176 then
              if code < 1151376297801211733341049321472 then
                if code < 1151351761666528028240444897280 then
                  decodeStateCodeChunk79 code
                else
                  if code < 1151375633982416522473269811200 then
                    decodeStateCodeChunk80 code
                  else
                    decodeStateCodeChunk81 code
              else
                if code < 4455978751353162282877519921152 then
                  decodeStateCodeChunk82 code
                else
                  if code < 4461159950272763061071859154944 then
                    decodeStateCodeChunk83 code
                  else
                    decodeStateCodeChunk84 code
            else
              if code < 6683751251822909059265469874176 then
                if code < 4492103224650070872625854566400 then
                  decodeStateCodeChunk85 code
                else
                  if code < 5198641213168974137921163767808 then
                    decodeStateCodeChunk86 code
                  else
                    decodeStateCodeChunk87 code
              else
                if code < 6683775127806238796947348463616 then
                  decodeStateCodeChunk88 code
                else
                  if code < 6683894532371931871517243080704 then
                    decodeStateCodeChunk89 code
                  else
                    decodeStateCodeChunk90 code
    else
      if code < 41247384772831173429643934742528 then
        if code < 7833977523095311677805124603904 then
          if code < 6719995792926947846810486919168 then
            if code < 6719851849154585794089463074816 then
              if code < 6689075707239508976391054950400 then
                if code < 6688932450742955787268722204672 then
                  decodeStateCodeChunk91 code
                else
                  decodeStateCodeChunk92 code
              else
                if code < 6714694526218891207851870277632 then
                  decodeStateCodeChunk93 code
                else
                  if code < 6714837782203650565216224227328 then
                    decodeStateCodeChunk94 code
                  else
                    decodeStateCodeChunk95 code
            else
              if code < 6719876388361766022202169118720 then
                if code < 6719852512378434967101145829376 then
                  decodeStateCodeChunk96 code
                else
                  if code < 6719852536941677947504778760192 then
                    decodeStateCodeChunk97 code
                  else
                    decodeStateCodeChunk98 code
              else
                if code < 6719995105651600776334767108096 then
                  decodeStateCodeChunk99 code
                else
                  if code < 6719995768873344095181600534528 then
                    decodeStateCodeChunk100 code
                  else
                    decodeStateCodeChunk101 code
          else
            if code < 6721165691461115447283622563840 then
              if code < 6720019644856740963955654864896 then
                if code < 6720018981142188923889835069440 then
                  decodeStateCodeChunk102 code
                else
                  if code < 6720019644261299107648357158912 then
                    decodeStateCodeChunk103 code
                  else
                    decodeStateCodeChunk104 code
              else
                if code < 6720019668908764027955624300544 then
                  decodeStateCodeChunk105 code
                else
                  if code < 6721141152339672030209326731264 then
                    decodeStateCodeChunk106 code
                  else
                    decodeStateCodeChunk107 code
            else
              if code < 7803033585495440340730911916032 then
                if code < 7457476368206714207676110843904 then
                  decodeStateCodeChunk108 code
                else
                  if code < 7797852386556886037183286214656 then
                    decodeStateCodeChunk109 code
                  else
                    decodeStateCodeChunk110 code
              else
                if code < 7833953647110321934324899360768 then
                  decodeStateCodeChunk111 code
                else
                  if code < 7833953671674091401543901360128 then
                    decodeStateCodeChunk112 code
                  else
                    decodeStateCodeChunk113 code
        else
          if code < 40133426894016098443726830391296 then
            if code < 27879890233475679756692877195264 then
              if code < 26736135124887300629967839502336 then
                if code < 7835123570293549866028461944832 then
                  decodeStateCodeChunk114 code
                else
                  decodeStateCodeChunk115 code
              else
                if code < 26767078402438534199471752826880 then
                  decodeStateCodeChunk116 code
                else
                  if code < 27848946980573505900674685241344 then
                    decodeStateCodeChunk117 code
                  else
                    decodeStateCodeChunk118 code
            else
              if code < 40102483616531216828150298181632 then
                if code < 27881036280675512046922741438464 then
                  decodeStateCodeChunk119 code
                else
                  if code < 31221766520988360277120668094464 then
                    decodeStateCodeChunk120 code
                  else
                    decodeStateCodeChunk121 code
              else
                if code < 40102483619602199797603496828928 then
                  decodeStateCodeChunk122 code
                else
                  if code < 40103629663731034493746402172928 then
                    decodeStateCodeChunk123 code
                  else
                    decodeStateCodeChunk124 code
          else
            if code < 41216441495365216091132720547840 then
              if code < 40136865698819995019298872119296 then
                if code < 40133426918560913775292435943424 then
                  decodeStateCodeChunk125 code
                else
                  if code < 40133427557304721439001735548928 then
                    decodeStateCodeChunk126 code
                  else
                    decodeStateCodeChunk127 code
              else
                if code < 40138584769703966706774821523456 then
                  decodeStateCodeChunk128 code
                else
                  if code < 41216441494768194778101613430784 then
                    decodeStateCodeChunk129 code
                  else
                    decodeStateCodeChunk130 code
            else
              if code < 41216584775828963992827959642112 then
                if code < 41216441498454640724658784733184 then
                  decodeStateCodeChunk131 code
                else
                  if code < 41216537023862304315363023259648 then
                    decodeStateCodeChunk132 code
                  else
                    decodeStateCodeChunk133 code
              else
                if code < 41247384769163666282285515069440 then
                  decodeStateCodeChunk134 code
                else
                  if code < 41247384769779641232534752901120 then
                    decodeStateCodeChunk135 code
                  else
                    decodeStateCodeChunk136 code
      else
        if code < 46817178806056632794196142215168 then
          if code < 41252685904353736363781632481280 then
            if code < 41247528053294906698242083862528 then
              if code < 41247385433001400394774008682496 then
                if code < 41247385432385425444485588768768 then
                  decodeStateCodeChunk137 code
                else
                  decodeStateCodeChunk138 code
              else
                if code < 41247385457546215726339614234624 then
                  decodeStateCodeChunk139 code
                else
                  if code < 41247480961479535084208143153152 then
                    decodeStateCodeChunk140 code
                  else
                    decodeStateCodeChunk141 code
            else
              if code < 41250919103080611389862429063168 then
                if code < 41248530816960519988908818872320 then
                  decodeStateCodeChunk142 code
                else
                  if code < 41248674075930970121953445984256 then
                    decodeStateCodeChunk143 code
                  else
                    decodeStateCodeChunk144 code
              else
                if code < 41252542645383798083514914494464 then
                  decodeStateCodeChunk145 code
                else
                  if code < 41252685901281671171430175193088 then
                    decodeStateCodeChunk146 code
                  else
                    decodeStateCodeChunk147 code
          else
            if code < 46817174163504317441016516268032 then
              if code < 46786233542507614261757037182976 then
                if code < 41253831948481503453235891795968 then
                  decodeStateCodeChunk148 code
                else
                  if code < 46786230889620576393296892395520 then
                    decodeStateCodeChunk149 code
                  else
                    decodeStateCodeChunk150 code
              else
                if code < 46786234868951145991131094843392 then
                  decodeStateCodeChunk151 code
                else
                  if code < 46787376936820408675964614803456 then
                    decodeStateCodeChunk152 code
                  else
                    decodeStateCodeChunk153 code
            else
              if code < 46817174851289830844905421426688 then
                if code < 46817174826640771122956370333696 then
                  decodeStateCodeChunk154 code
                else
                  if code < 46817174827237807162181194371072 then
                    decodeStateCodeChunk155 code
                  else
                    decodeStateCodeChunk156 code
              else
                if code < 46817177479632053371455891001344 then
                  decodeStateCodeChunk157 code
                else
                  if code < 46817178142853811313996114710528 then
                    decodeStateCodeChunk158 code
                  else
                    decodeStateCodeChunk159 code
        else
          if code < 47900188767858080719098831962112 then
            if code < 46822332063603785247648348327936 then
              if code < 46818320873925894259369812185088 then
                if code < 46817321399246582008358299840512 then
                  decodeStateCodeChunk160 code
                else
                  decodeStateCodeChunk161 code
              else
                if code < 46818324853768194417069806923776 then
                  decodeStateCodeChunk162 code
                else
                  if code < 46821759016038715758940411023360 then
                    decodeStateCodeChunk163 code
                  else
                    decodeStateCodeChunk164 code
            else
              if code < 46822479274868112933649340387328 then
                if code < 46822336018455878061969228189696 then
                  decodeStateCodeChunk165 code
                else
                  if code < 46822336018986560928508009009152 then
                    decodeStateCodeChunk166 code
                  else
                    decodeStateCodeChunk167 code
              else
                if code < 46823482065571983105162988179456 then
                  decodeStateCodeChunk168 code
                else
                  if code < 47559910906327738510887525020160 then
                    decodeStateCodeChunk169 code
                  else
                    decodeStateCodeChunk170 code
          else
            if code < 47936433173774009312580917538816 then
              if code < 47931275298153004874144428142592 then
                if code < 47900336027651857708075554471936 then
                  decodeStateCodeChunk171 code
                else
                  if code < 47931132705475311496407281577984 then
                    decodeStateCodeChunk172 code
                  else
                    decodeStateCodeChunk173 code
              else
                if code < 47931275985938532902823821881344 then
                  decodeStateCodeChunk174 code
                else
                  if code < 47932278752674617292298816999424 then
                    decodeStateCodeChunk175 code
                  else
                    decodeStateCodeChunk176 code
            else
              if code < 160409962346002463330700663398400 then
                if code < 47936437153104578902108518592512 then
                  decodeStateCodeChunk177 code
                else
                  if code < 47937435965075442019577640210432 then
                    decodeStateCodeChunk178 code
                  else
                    decodeStateCodeChunk179 code
              else
                if code < 160415262924838712704011858223104 then
                  decodeStateCodeChunk180 code
                else
                  if code < 161523916244908885595591469803520 then
                    decodeStateCodeChunk181 code
                  else
                    decodeStateCodeChunk182 code
  else
    if code < 282054393294043125774566609233920 then
      if code < 247305124116848314860215552851968 then
        if code < 241734188012171361903789440403456 then
          if code < 240641858458126900206263353614336 then
            if code < 240614925575171069547117249822720 then
              if code < 164865793836434113663587915964416 then
                if code < 161530219590481154147599325177856 then
                  decodeStateCodeChunk183 code
                else
                  decodeStateCodeChunk184 code
              else
                if code < 165634362292906106208335051299590 then
                  decodeStateCodeChunk185 code
                else
                  if code < 188383816484153193636230801172480 then
                    decodeStateCodeChunk186 code
                  else
                    decodeStateCodeChunk187 code
            else
              if code < 240620086877437829656959968747520 then
                if code < 240614929554520051558855609417728 then
                  decodeStateCodeChunk188 code
                else
                  if code < 240620082898106748230797476372480 then
                    decodeStateCodeChunk189 code
                  else
                    decodeStateCodeChunk190 code
              else
                if code < 240620230133337362666236189286400 then
                  decodeStateCodeChunk191 code
                else
                  if code < 240620230821122876036271775555584 then
                    decodeStateCodeChunk192 code
                  else
                    decodeStateCodeChunk193 code
          else
            if code < 241730172756507332216232811137024 then
              if code < 241729026709819245161360841934848 then
                if code < 240651174070975111770850423087104 then
                  decodeStateCodeChunk194 code
                else
                  if code < 241728883453426474433106155833344 then
                    decodeStateCodeChunk195 code
                  else
                    decodeStateCodeChunk196 code
              else
                if code < 241729026709905062478569409546240 then
                  decodeStateCodeChunk197 code
                else
                  if code < 241729030689149814716878395770880 then
                    decodeStateCodeChunk198 code
                  else
                    decodeStateCodeChunk199 code
            else
              if code < 241734184695465990754016497084416 then
                if code < 241734041439565485198131890071552 then
                  decodeStateCodeChunk200 code
                else
                  if code < 241734184032755464914134367111168 then
                    decodeStateCodeChunk201 code
                  else
                    decodeStateCodeChunk202 code
              else
                if code < 241734184696081453807447165569024 then
                  decodeStateCodeChunk203 code
                else
                  if code < 241734188011593279372050873419776 then
                    decodeStateCodeChunk204 code
                  else
                    decodeStateCodeChunk205 code
        else
          if code < 247298820080335215807845087576064 then
            if code < 241764984713960956804770405918720 then
              if code < 241734188675393135690623274354688 then
                if code < 241734188674796085017400172455936 then
                  decodeStateCodeChunk206 code
                else
                  decodeStateCodeChunk207 code
              else
                if code < 241735330743177041699613896189952 then
                  decodeStateCodeChunk208 code
                else
                  if code < 241754670289164060489717376985088 then
                    decodeStateCodeChunk209 code
                  else
                    decodeStateCodeChunk210 code
            else
              if code < 241765131949809125658610273339392 then
                if code < 241765127970457986513209426872320 then
                  decodeStateCodeChunk211 code
                else
                  if code < 241765131949193662571300164577280 then
                    decodeStateCodeChunk212 code
                  else
                    decodeStateCodeChunk213 code
              else
                if code < 247298676823922965067460928020480 then
                  decodeStateCodeChunk214 code
                else
                  if code < 247298676826993962661508704837632 then
                    decodeStateCodeChunk215 code
                  else
                    decodeStateCodeChunk216 code
          else
            if code < 247303977406341957820215862493184 then
              if code < 247303834174493410160692362682368 then
                if code < 247298820083490977745313965539328 then
                  decodeStateCodeChunk217 code
                else
                  if code < 247299966129581503559709853630464 then
                    decodeStateCodeChunk218 code
                  else
                    decodeStateCodeChunk219 code
              else
                if code < 247303834834644698215660028633088 then
                  decodeStateCodeChunk220 code
                else
                  if code < 247303977404806197032396270542848 then
                    decodeStateCodeChunk221 code
                  else
                    decodeStateCodeChunk222 code
            else
              if code < 247303978069563205120234327375872 then
                if code < 247303978065980974237721925722112 then
                  decodeStateCodeChunk223 code
                else
                  if code < 247303978066493245917539359137792 then
                    decodeStateCodeChunk224 code
                  else
                    decodeStateCodeChunk225 code
              else
                if code < 247303978091056488288583252058112 then
                  decodeStateCodeChunk226 code
                else
                  if code < 247305123452517774498701539688448 then
                    decodeStateCodeChunk227 code
                  else
                    decodeStateCodeChunk228 code
      else
        if code < 282017002840839968097376953796608 then
          if code < 248417935944786572470521726468096 then
            if code < 247334921368012265244508229345280 then
              if code < 247334778112112221007800129167360 then
                if code < 247334778084477995057982479671296 then
                  decodeStateCodeChunk229 code
                else
                  decodeStateCodeChunk230 code
              else
                if code < 247334921343449022873464336424960 then
                  decodeStateCodeChunk231 code
                else
                  if code < 247334921344043954185048352096256 then
                    decodeStateCodeChunk232 code
                  else
                    decodeStateCodeChunk233 code
            else
              if code < 248412777958656972614886519472128 then
                if code < 247336067391158495602725097512960 then
                  decodeStateCodeChunk234 code
                else
                  if code < 248046616654088407001452234476288 then
                    decodeStateCodeChunk235 code
                  else
                    decodeStateCodeChunk236 code
              else
                if code < 248417935281507938099007975063552 then
                  decodeStateCodeChunk237 code
                else
                  if code < 248417935306156997787260435595264 then
                    decodeStateCodeChunk238 code
                  else
                    decodeStateCodeChunk239 code
          else
            if code < 280903044986655013922345304662016 then
              if code < 248448879219212053791665414086656 then
                if code < 248417935969293466093716503666688 then
                  decodeStateCodeChunk240 code
                else
                  if code < 248419081992014820381713565302784 then
                    decodeStateCodeChunk241 code
                  else
                    decodeStateCodeChunk242 code
              else
                if code < 248448879222299884330825457369088 then
                  decodeStateCodeChunk243 code
                else
                  if code < 248450025269480763095545306816512 then
                    decodeStateCodeChunk244 code
                  else
                    decodeStateCodeChunk245 code
            else
              if code < 280908226713695579342125185245184 then
                if code < 280903068838074574903649513766912 then
                  decodeStateCodeChunk246 code
                else
                  if code < 280903068862638343803864606449664 then
                    decodeStateCodeChunk247 code
                  else
                    decodeStateCodeChunk248 code
              else
                if code < 280933988924272244700587593900032 then
                  decodeStateCodeChunk249 code
                else
                  if code < 280940316035290883230491053531136 then
                    decodeStateCodeChunk250 code
                  else
                    decodeStateCodeChunk251 code
        else
          if code < 282018148888039800379104306235392 then
            if code < 282017026716842251469455853193216 then
              if code < 282017003504062253745922211579904 then
                if code < 282017002864891991762234151438336 then
                  decodeStateCodeChunk252 code
                else
                  decodeStateCodeChunk253 code
              else
                if code < 282017018757650457565726205847552 then
                  decodeStateCodeChunk254 code
                else
                  if code < 282017026716311567409626763601920 then
                    decodeStateCodeChunk255 code
                  else
                    decodeStateCodeChunk256 code
            else
              if code < 282017146760047011782576125937664 then
                if code < 282017027380045583618547180742656 then
                  decodeStateCodeChunk257 code
                else
                  if code < 282017114262152382674789649257472 then
                    decodeStateCodeChunk258 code
                  else
                    decodeStateCodeChunk259 code
              else
                if code < 282017169972780664068210616731648 then
                  decodeStateCodeChunk260 code
                else
                  if code < 282017170635945050791542308898816 then
                    decodeStateCodeChunk261 code
                  else
                    decodeStateCodeChunk262 code
          else
            if code < 282047946778543016216650516531200 then
              if code < 282022327848344807921497003689984 then
                if code < 282018172763511385066720355788800 then
                  decodeStateCodeChunk263 code
                else
                  if code < 282022184591932557181112844134400 then
                    decodeStateCodeChunk264 code
                  else
                    decodeStateCodeChunk265 code
              else
                if code < 282023473895544113682594850252800 then
                  decodeStateCodeChunk266 code
                else
                  if code < 282043959488730950028231966566400 then
                    decodeStateCodeChunk267 code
                  else
                    decodeStateCodeChunk268 code
            else
              if code < 282053127866328555274566729050112 then
                if code < 282049092825145285963443343239168 then
                  decodeStateCodeChunk269 code
                else
                  if code < 282053103990345488678771760408576 then
                    decodeStateCodeChunk270 code
                  else
                    decodeStateCodeChunk271 code
              else
                if code < 282053247246843308117616684681216 then
                  decodeStateCodeChunk272 code
                else
                  if code < 282053271122825833601818856368128 then
                    decodeStateCodeChunk273 code
                  else
                    decodeStateCodeChunk274 code
    else
      if code < 287622917282076686840542386069504 then
        if code < 287587942924335730841485221765120 then
          if code < 287586816107496441937608118837248 then
            if code < 287586792898402904903712842809344 then
              if code < 287586792235181145741042584125440 then
                if code < 287586792232025383770190572257280 then
                  decodeStateCodeChunk275 code
                else
                  decodeStateCodeChunk276 code
              else
                if code < 287586792894735397755884238151680 then
                  decodeStateCodeChunk277 code
                else
                  if code < 287586792895265569988325407784960 then
                    decodeStateCodeChunk278 code
                  else
                    decodeStateCodeChunk279 code
            else
              if code < 287586796238989652830556870148096 then
                if code < 287586794887489574616377964109824 then
                  decodeStateCodeChunk280 code
                else
                  if code < 287586796213914664665653684674560 then
                    decodeStateCodeChunk281 code
                  else
                    decodeStateCodeChunk282 code
              else
                if code < 287586796877732948014261491204096 then
                  decodeStateCodeChunk283 code
                else
                  if code < 287586808812568836372700549545984 then
                    decodeStateCodeChunk284 code
                  else
                    decodeStateCodeChunk285 code
          else
            if code < 287586820752096264551021926195200 then
              if code < 287586820086827523397623930101760 then
                if code < 287586816770718201099808192536576 then
                  decodeStateCodeChunk286 code
                else
                  if code < 287586816771230472779625625952256 then
                    decodeStateCodeChunk287 code
                  else
                    decodeStateCodeChunk288 code
              else
                if code < 287586820089897482642674729033728 then
                  decodeStateCodeChunk289 code
                else
                  if code < 287586820114461236875900230770688 then
                    decodeStateCodeChunk290 code
                  else
                    decodeStateCodeChunk291 code
            else
              if code < 287586963346395010807381078573056 then
                if code < 287586820753649927108813361512448 then
                  decodeStateCodeChunk292 code
                else
                  if code < 287586940133632928268196890279936 then
                    decodeStateCodeChunk293 code
                  else
                    decodeStateCodeChunk294 code
              else
                if code < 287586964009616256888680063434752 then
                  decodeStateCodeChunk295 code
                else
                  if code < 287587938942446448726871626424320 then
                    decodeStateCodeChunk296 code
                  else
                    decodeStateCodeChunk297 code
        else
          if code < 287617736169131132606870808502272 then
            if code < 287591977965518488291367368728576 then
              if code < 287587966800319060680687874940928 then
                if code < 287587962817918033423852193587200 then
                  decodeStateCodeChunk298 code
                else
                  decodeStateCodeChunk299 code
              else
                if code < 287591973983117461034531687374848 then
                  decodeStateCodeChunk300 code
                else
                  if code < 287591977962466954866135007174656 then
                    decodeStateCodeChunk301 code
                  else
                    decodeStateCodeChunk302 code
            else
              if code < 287592121246493965525628044124160 then
                if code < 287592121218859725594350511194112 then
                  decodeStateCodeChunk303 code
                else
                  if code < 287592121221930197886488262156288 then
                    decodeStateCodeChunk304 code
                  else
                    decodeStateCodeChunk305 code
              else
                if code < 287593267269130028949456952492032 then
                  decodeStateCodeChunk306 code
                else
                  if code < 287612606812558833585990924115968 then
                    decodeStateCodeChunk307 code
                  else
                    decodeStateCodeChunk308 code
          else
            if code < 287618886199328238496752261341184 then
              if code < 287617738825106805368289894211584 then
                if code < 287617736172712559168418897272832 then
                  decodeStateCodeChunk309 code
                else
                  if code < 287617736172798639762731739979776 then
                    decodeStateCodeChunk310 code
                  else
                    decodeStateCodeChunk311 code
              else
                if code < 287617740152128406214985726820352 then
                  decodeStateCodeChunk312 code
                else
                  if code < 287617883432592152889341427843072 then
                    decodeStateCodeChunk313 code
                  else
                    decodeStateCodeChunk314 code
            else
              if code < 287622897363930614215449991127040 then
                if code < 287622320357931251464003271860224 then
                  decodeStateCodeChunk315 code
                else
                  if code < 287622893384602165197974354927616 then
                    decodeStateCodeChunk316 code
                  else
                    decodeStateCodeChunk317 code
              else
                if code < 287622897364443953493531922931712 then
                  decodeStateCodeChunk318 code
                else
                  if code < 287622897388494383081772582838272 then
                    decodeStateCodeChunk319 code
                  else
                    decodeStateCodeChunk320 code
      else
        if code < 288700921884801702521153752399872 then
          if code < 288700750110347652472796746874880 then
            if code < 287623064496412553232040284266496 then
              if code < 287622921261407241813742828265472 then
                if code < 287622921239914735003595177926656 then
                  decodeStateCodeChunk321 code
                else
                  decodeStateCodeChunk322 code
              else
                if code < 287623040620429224608736001204224 then
                  decodeStateCodeChunk323 code
                else
                  if code < 287623064496326194761222667051008 then
                    decodeStateCodeChunk324 code
                  else
                    decodeStateCodeChunk325 code
            else
              if code < 288329528977511248581259030479360 then
                if code < 287624039432313216177425072922624 then
                  decodeStateCodeChunk326 code
                else
                  if code < 287624067287625521529382061088768 then
                    decodeStateCodeChunk327 code
                  else
                    decodeStateCodeChunk328 code
              else
                if code < 288329602594056167905808181431040 then
                  decodeStateCodeChunk329 code
                else
                  if code < 288363911056729555661394125750784 then
                    decodeStateCodeChunk330 code
                  else
                    decodeStateCodeChunk331 code
          else
            if code < 288700893369336529653939719405568 then
              if code < 288700773986245179585728002129920 then
                if code < 288700750773484120779370361192448 then
                  decodeStateCodeChunk332 code
                else
                  if code < 288700750776639370880987989475328 then
                    decodeStateCodeChunk333 code
                  else
                    decodeStateCodeChunk334 code
              else
                if code < 288700774649485877657150113849344 then
                  decodeStateCodeChunk335 code
                else
                  if code < 288700846302065973372411754217472 then
                    decodeStateCodeChunk336 code
                  else
                    decodeStateCodeChunk337 code
            else
              if code < 288700917905367429679178922590208 then
                if code < 288700894054032633041256632549376 then
                  decodeStateCodeChunk338 code
                else
                  if code < 288700917242145670483125530001408 then
                    decodeStateCodeChunk339 code
                  else
                    decodeStateCodeChunk340 code
              else
                if code < 288700917929930672016369496621056 then
                  decodeStateCodeChunk341 code
                else
                  if code < 288700921224631475565466560233472 then
                    decodeStateCodeChunk342 code
                  else
                    decodeStateCodeChunk343 code
        else
          if code < 288731789579531916086282677813248 then
            if code < 288706079097096718066473353748480 then
              if code < 288702040076668696473588052721664 then
                if code < 288701896820683426575222714531840 then
                  decodeStateCodeChunk344 code
                else
                  decodeStateCodeChunk345 code
              else
                if code < 288702067931897290447369712320512 then
                  decodeStateCodeChunk346 code
                else
                  if code < 288706075117785101977065778323456 then
                    decodeStateCodeChunk347 code
                  else
                    decodeStateCodeChunk348 code
            else
              if code < 288726560736028498822820945338368 then
                if code < 288706079097182520759008979025920 then
                  decodeStateCodeChunk349 code
                else
                  if code < 288707077909066001715150584684544 then
                    decodeStateCodeChunk350 code
                  else
                    decodeStateCodeChunk351 code
              else
                if code < 288731694047964356764262849126400 then
                  decodeStateCodeChunk352 code
                else
                  if code < 288731694051035617601718310477824 then
                    decodeStateCodeChunk353 code
                  else
                    decodeStateCodeChunk354 code
          else
            if code < 288736998498664607146861880377344 then
              if code < 288736851260279905252085643485184 then
                if code < 288731837331498575755284284473344 then
                  decodeStateCodeChunk355 code
                else
                  if code < 288732983354134639179074010759168 then
                    decodeStateCodeChunk356 code
                  else
                    decodeStateCodeChunk357 code
              else
                if code < 288736875136262430736431482806272 then
                  decodeStateCodeChunk358 code
                else
                  if code < 288736994519334066798138470105088 then
                    decodeStateCodeChunk359 code
                  else
                    decodeStateCodeChunk360 code
            else
              if code < 288737022371596419404185412272128 then
                if code < 288736998523229956074553110970368 then
                  decodeStateCodeChunk361 code
                else
                  if code < 288737018416726968359729717452800 then
                    decodeStateCodeChunk362 code
                  else
                    decodeStateCodeChunk363 code
              else
                if code < 288737022396055943872484052443136 then
                  decodeStateCodeChunk364 code
                else
                  if code < 288738140566535463915717351579648 then
                    decodeStateCodeChunk365 code
                  else
                    decodeStateCodeChunk366 code

def decodeState
    (vector : Fin 42 -> Fin 6) : Fin 11742 :=
  decodeStateCode (stateVectorCode vector)

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14079.Shards
