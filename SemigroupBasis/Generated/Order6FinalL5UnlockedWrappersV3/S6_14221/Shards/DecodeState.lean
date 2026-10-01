import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14221.Shards.DecodeStatePart00
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14221.Shards.DecodeStatePart01
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14221.Shards.DecodeStatePart02
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14221.Shards.DecodeStatePart03
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14221.Shards.DecodeStatePart04
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14221.Shards.DecodeStatePart05
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14221.Shards.DecodeStatePart06
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14221.Shards.DecodeStatePart07
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14221.Shards.DecodeStatePart08
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14221.Shards.DecodeStatePart09
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14221.Shards.DecodeStatePart10
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14221.Shards.DecodeStatePart11

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14221.Shards

def stateVectorCode
    (vector : Fin 53 -> Fin 6) : Nat :=
  (vector (0 : Fin 53)).val + 6 * ((vector (1 : Fin 53)).val + 6 * ((vector (2 : Fin 53)).val + 6 * ((vector (3 : Fin 53)).val + 6 * ((vector (4 : Fin 53)).val + 6 * ((vector (5 : Fin 53)).val + 6 * ((vector (6 : Fin 53)).val + 6 * ((vector (7 : Fin 53)).val + 6 * ((vector (8 : Fin 53)).val + 6 * ((vector (9 : Fin 53)).val + 6 * ((vector (10 : Fin 53)).val + 6 * ((vector (11 : Fin 53)).val + 6 * ((vector (12 : Fin 53)).val + 6 * ((vector (13 : Fin 53)).val + 6 * ((vector (14 : Fin 53)).val + 6 * ((vector (15 : Fin 53)).val + 6 * ((vector (16 : Fin 53)).val + 6 * ((vector (17 : Fin 53)).val + 6 * ((vector (18 : Fin 53)).val + 6 * ((vector (19 : Fin 53)).val + 6 * ((vector (20 : Fin 53)).val + 6 * ((vector (21 : Fin 53)).val + 6 * ((vector (22 : Fin 53)).val + 6 * ((vector (23 : Fin 53)).val + 6 * ((vector (24 : Fin 53)).val + 6 * ((vector (25 : Fin 53)).val + 6 * ((vector (26 : Fin 53)).val + 6 * ((vector (27 : Fin 53)).val + 6 * ((vector (28 : Fin 53)).val + 6 * ((vector (29 : Fin 53)).val + 6 * ((vector (30 : Fin 53)).val + 6 * ((vector (31 : Fin 53)).val + 6 * ((vector (32 : Fin 53)).val + 6 * ((vector (33 : Fin 53)).val + 6 * ((vector (34 : Fin 53)).val + 6 * ((vector (35 : Fin 53)).val + 6 * ((vector (36 : Fin 53)).val + 6 * ((vector (37 : Fin 53)).val + 6 * ((vector (38 : Fin 53)).val + 6 * ((vector (39 : Fin 53)).val + 6 * ((vector (40 : Fin 53)).val + 6 * ((vector (41 : Fin 53)).val + 6 * ((vector (42 : Fin 53)).val + 6 * ((vector (43 : Fin 53)).val + 6 * ((vector (44 : Fin 53)).val + 6 * ((vector (45 : Fin 53)).val + 6 * ((vector (46 : Fin 53)).val + 6 * ((vector (47 : Fin 53)).val + 6 * ((vector (48 : Fin 53)).val + 6 * ((vector (49 : Fin 53)).val + 6 * ((vector (50 : Fin 53)).val + 6 * ((vector (51 : Fin 53)).val + 6 * ((vector (52 : Fin 53)).val))))))))))))))))))))))))))))))))))))))))))))))))))))

def decodeStateCode (code : Nat) : Fin 11742 :=
  if code < 58678984184766891283266726813417770876928 then
    if code < 2424878483910692109586223779052601679872 then
      if code < 415418740404827236965403285789074235392 then
        if code < 404140643189073966732159536561343430656 then
          if code < 78582902718380549942469388994767429632 then
            if code < 1879723839191188241721761668408541184 then
              if code < 743499009124568918134911664128 then
                if code < 860442056079439683119947776 then
                  decodeStateCodeChunk0 code
                else
                  decodeStateCodeChunk1 code
              else
                if code < 8662879960179693666805685966340096 then
                  decodeStateCodeChunk2 code
                else
                  if code < 1879684417459608240420423333882888192 then
                    decodeStateCodeChunk3 code
                  else
                    decodeStateCodeChunk4 code
            else
              if code < 67356773122064575121202538490472898560 then
                if code < 11234790990998983359350493570681274368 then
                  decodeStateCodeChunk5 code
                else
                  if code < 13105812837931155875017650186260840448 then
                    decodeStateCodeChunk6 code
                  else
                    decodeStateCodeChunk7 code
              else
                if code < 67365435630728434637383245223102513152 then
                  decodeStateCodeChunk8 code
                else
                  if code < 69236496837505638192933436671099666432 then
                    decodeStateCodeChunk9 code
                  else
                    decodeStateCodeChunk10 code
          else
            if code < 269427097686725909809331500392431689728 then
              if code < 78591564855725116542415790842768785408 then
                if code < 78591564113086531221677740978486640640 then
                  decodeStateCodeChunk11 code
                else
                  decodeStateCodeChunk12 code
              else
                if code < 80462585960018703566763169414487998464 then
                  decodeStateCodeChunk13 code
                else
                  if code < 80462625691183027522887212088673959936 then
                    decodeStateCodeChunk14 code
                  else
                    decodeStateCodeChunk15 code
            else
              if code < 348018661798951796323858661299527352320 then
                if code < 270683134333220015251952632669208051712 then
                  decodeStateCodeChunk16 code
                else
                  if code < 336783870808789563092551346315216289792 then
                    decodeStateCodeChunk17 code
                  else
                    decodeStateCodeChunk18 code
              else
                if code < 349266036308984952129131905855940198400 then
                  decodeStateCodeChunk19 code
                else
                  if code < 404140638733242472207071167890249949184 then
                    decodeStateCodeChunk20 code
                  else
                    decodeStateCodeChunk21 code
        else
          if code < 404194099798879464744983983658203348992 then
            if code < 404192616007841009593020609837228564480 then
              if code < 404149345428022954393275312618269048832 then
                if code < 404149305325535137457620352118571401216 then
                  decodeStateCodeChunk22 code
                else
                  decodeStateCodeChunk23 code
              else
                if code < 404192611552009478222296625731338240000 then
                  decodeStateCodeChunk24 code
                else
                  if code < 404192616006981452856214724240507928576 then
                    decodeStateCodeChunk25 code
                  else
                    decodeStateCodeChunk26 code
            else
              if code < 404194059696391647979888915947400200192 then
                if code < 404192651654497295143758379166711414784 then
                  decodeStateCodeChunk27 code
                else
                  if code < 404194055240560134861410354895343583232 then
                    decodeStateCodeChunk28 code
                  else
                    decodeStateCodeChunk29 code
              else
                if code < 404194095343047749145997832575765217280 then
                  decodeStateCodeChunk30 code
                else
                  if code < 404194095343907487196961463641195937792 then
                    decodeStateCodeChunk31 code
                  else
                    decodeStateCodeChunk32 code
          else
            if code < 406072335328457673384702181252387602432 then
              if code < 404202761936199949824851516168712781824 then
                if code < 404201313790958244823729762020511186944 then
                  decodeStateCodeChunk33 code
                else
                  if code < 404201318308676306548376499545740148736 then
                    decodeStateCodeChunk34 code
                  else
                    decodeStateCodeChunk35 code
              else
                if code < 405448666020971662926467927198694113280 then
                  decodeStateCodeChunk36 code
                else
                  if code < 406020362571577197723264806917540675584 then
                    decodeStateCodeChunk37 code
                  else
                    decodeStateCodeChunk38 code
            else
              if code < 415366772042751374311967708972906913792 then
                if code < 406073778955981316803306699663813410816 then
                  decodeStateCodeChunk39 code
                else
                  if code < 415366767586060322893747596083103473664 then
                    decodeStateCodeChunk40 code
                  else
                    decodeStateCodeChunk41 code
              else
                if code < 415375431951296770154879627930530480128 then
                  decodeStateCodeChunk42 code
                else
                  if code < 415375469825868627965504724680671002624 then
                    decodeStateCodeChunk43 code
                  else
                    decodeStateCodeChunk44 code
      else
        if code < 482732245175871913708382323875737763840 then
          if code < 471550832818455319700150447758821556224 then
            if code < 417246491425254586894483416861080813568 then
              if code < 415420228652556540728171594257348460544 then
                if code < 415418784964005884245402512307316097024 then
                  decodeStateCodeChunk45 code
                else
                  decodeStateCodeChunk46 code
              else
                if code < 415427447100467257465589821038842118144 then
                  decodeStateCodeChunk47 code
                else
                  if code < 416622822055881806585711668335459434496 then
                    decodeStateCodeChunk48 code
                  else
                    decodeStateCodeChunk49 code
            else
              if code < 471506073991791172213293156429440483328 then
                if code < 417299907933431692848782399812598267904 then
                  decodeStateCodeChunk50 code
                else
                  if code < 471498855543856782143221365722037878784 then
                    decodeStateCodeChunk51 code
                  else
                    decodeStateCodeChunk52 code
              else
                if code < 471506118611996829813912214686614421504 then
                  decodeStateCodeChunk53 code
                else
                  if code < 471507562238661158749800793259743641600 then
                    decodeStateCodeChunk54 code
                  else
                    decodeStateCodeChunk55 code
          else
            if code < 482723540708123994786938212763135090688 then
              if code < 471559535058287497514206515726323810304 then
                if code < 471550868465111641940175530522061078528 then
                  decodeStateCodeChunk56 code
                else
                  if code < 471559530601596670240354684491905630208 then
                    decodeStateCodeChunk57 code
                  else
                    decodeStateCodeChunk58 code
              else
                if code < 473377135569891647845061256898510061568 then
                  decodeStateCodeChunk59 code
                else
                  if code < 473430552078068864506898170827289657344 then
                    decodeStateCodeChunk60 code
                  else
                    decodeStateCodeChunk61 code
            else
              if code < 482732202845468561543247541206754787328 then
                if code < 482724984397534189725442604114597879808 then
                  decodeStateCodeChunk62 code
                else
                  if code < 482732202844609022902320494499254501376 then
                    decodeStateCodeChunk63 code
                  else
                    decodeStateCodeChunk64 code
              else
                if code < 482732207300440554287259014631742537728 then
                  decodeStateCodeChunk65 code
                else
                  if code < 482732207302159625087007437222771195904 then
                    decodeStateCodeChunk66 code
                  else
                    decodeStateCodeChunk67 code
        else
          if code < 484033011686146681319890425903786786816 then
            if code < 482733691093197862235127941830191120384 then
              if code < 482733650989850749396345132752228581376 then
                if code < 482733646534019218196181549274198179840 then
                  decodeStateCodeChunk68 code
                else
                  decodeStateCodeChunk69 code
              else
                if code < 482733686636506832324402442790006456320 then
                  decodeStateCodeChunk70 code
                else
                  if code < 482733688864422570361316331943181156352 then
                    decodeStateCodeChunk71 code
                  else
                    decodeStateCodeChunk72 code
            else
              if code < 482785659456133263188725628854114222080 then
                if code < 482776957216301103797493157521540489216 then
                  decodeStateCodeChunk73 code
                else
                  if code < 482777001774620212436565337332282064896 then
                    decodeStateCodeChunk74 code
                  else
                    decodeStateCodeChunk75 code
              else
                if code < 482785663911105259330152864286706270208 then
                  decodeStateCodeChunk76 code
                else
                  if code < 483979595177969354448038306383524790272 then
                    decodeStateCodeChunk77 code
                  else
                    decodeStateCodeChunk78 code
          else
            if code < 2020755211041575796858478095292653207552 then
              if code < 484656681055519240540531575199265488896 then
                if code < 484603264547342134756810664268886179840 then
                  decodeStateCodeChunk79 code
                else
                  if code < 484604708236752326639037764812005703680 then
                    decodeStateCodeChunk80 code
                  else
                    decodeStateCodeChunk81 code
              else
                if code < 1886024301224844561122336790569518891008 then
                  decodeStateCodeChunk82 code
                else
                  if code < 2020755170937369130196973101151901655040 then
                    decodeStateCodeChunk83 code
                  else
                    decodeStateCodeChunk84 code
            else
              if code < 2424843832394293085330377987280904069120 then
                if code < 2020756654728407382697865335995160363008 then
                  decodeStateCodeChunk85 code
                else
                  if code < 2022008333571774676143261401399891066880 then
                    decodeStateCodeChunk86 code
                  else
                    decodeStateCodeChunk87 code
              else
                if code < 2424843832766471898137749758461452222464 then
                  decodeStateCodeChunk88 code
                else
                  if code < 2424843833137791209306254571709211287552 then
                    decodeStateCodeChunk89 code
                  else
                    decodeStateCodeChunk90 code
    else
      if code < 15020613862830864494019941973201355014144 then
        if code < 2830917611350416754462122808069763137536 then
          if code < 2829036443946301678574542070534575693824 then
            if code < 2426723556233626625900541526232798330880 then
              if code < 2424895805213919648252972270306307547136 then
                if code < 2424895805213060109953208679957963677696 then
                  decodeStateCodeChunk91 code
                else
                  decodeStateCodeChunk92 code
              else
                if code < 2426714854613547326539177150119545929728 then
                  decodeStateCodeChunk93 code
                else
                  if code < 2426723516750008497449434837871316959232 then
                    decodeStateCodeChunk94 code
                  else
                    decodeStateCodeChunk95 code
            else
              if code < 2426775528928620552771013748929418231808 then
                if code < 2426766826689675764817805220083847921664 then
                  decodeStateCodeChunk96 code
                else
                  if code < 2426766866792159382017122645342260559872 then
                    decodeStateCodeChunk97 code
                  else
                    decodeStateCodeChunk98 code
              else
                if code < 2829036443945442139407658554551729332224 then
                  decodeStateCodeChunk99 code
                else
                  if code < 2829036443945442360495789764552166973440 then
                    decodeStateCodeChunk100 code
                  else
                    decodeStateCodeChunk101 code
          else
            if code < 2829037927738199448052460544277446918144 then
              if code < 2829037887634852334531351027050821918720 then
                if code < 2829036484048789255331145894219527749632 then
                  decodeStateCodeChunk102 code
                else
                  if code < 2829036484048789274436302904781368754176 then
                    decodeStateCodeChunk103 code
                  else
                    decodeStateCodeChunk104 code
              else
                if code < 2829037889862768072582461780798134026240 then
                  decodeStateCodeChunk105 code
                else
                  if code < 2829037927737339931075412977786934034432 then
                    decodeStateCodeChunk106 code
                  else
                    decodeStateCodeChunk107 code
            else
              if code < 2830908949213955583722446848497570316288 then
                if code < 2829037927738199669126380266421359771648 then
                  decodeStateCodeChunk108 code
                else
                  if code < 2830907505524545391683462562785935753216 then
                    decodeStateCodeChunk109 code
                  else
                    decodeStateCodeChunk110 code
              else
                if code < 2830913280405959269076048792932354916352 then
                  decodeStateCodeChunk111 code
                else
                  if code < 2830916167661006562423138522358128574464 then
                    decodeStateCodeChunk112 code
                  else
                    decodeStateCodeChunk113 code
        else
          if code < 14618299451100775113238265369198207877120 then
            if code < 10182108980567018592988901280379489222656 then
              if code < 10047394953897612966862824471977345679360 then
                if code < 2830917611474189852214503316560799891456 then
                  decodeStateCodeChunk114 code
                else
                  decodeStateCodeChunk115 code
              else
                if code < 10170926162395623181374392330181489696768 then
                  decodeStateCodeChunk116 code
                else
                  if code < 10172130239590583488792930427092381237248 then
                    decodeStateCodeChunk117 code
                  else
                    decodeStateCodeChunk118 code
            else
              if code < 14616419767487817666697712299909426126848 then
                if code < 10182160993488273084158762786061644759040 then
                  decodeStateCodeChunk119 code
                else
                  if code < 11765244350892864842490480030745257811968 then
                    decodeStateCodeChunk120 code
                  else
                    decodeStateCodeChunk121 code
              else
                if code < 14616421211177226959102489180789750366208 then
                  decodeStateCodeChunk122 code
                else
                  if code < 14616428430366941280489210623934763892736 then
                    decodeStateCodeChunk123 code
                  else
                    decodeStateCodeChunk124 code
          else
            if code < 14629525579954452723471535809578661494784 then
              if code < 14627645897084133641348404125191282565120 then
                if code < 14618299491327031827521826042695185514496 then
                  decodeStateCodeChunk125 code
                else
                  if code < 14618300934891809386422383299989988884480 then
                    decodeStateCodeChunk126 code
                  else
                    decodeStateCodeChunk127 code
              else
                if code < 14627654558477980102750671874062664335360 then
                  decodeStateCodeChunk128 code
                else
                  if code < 14627656002167389413407690623398338887680 then
                    decodeStateCodeChunk129 code
                  else
                    decodeStateCodeChunk130 code
            else
              if code < 15020561849909609873719734173939691159552 then
                if code < 14629525620552028509256276860135273578496 then
                  decodeStateCodeChunk131 code
                else
                  if code < 14629527063745486775752334028608863125504 then
                    decodeStateCodeChunk132 code
                  else
                    decodeStateCodeChunk133 code
              else
                if code < 15020570552148581632008840237302044950528 then
                  decodeStateCodeChunk134 code
                else
                  if code < 15020613822728376916581012049277743472640 then
                    decodeStateCodeChunk135 code
                  else
                    decodeStateCodeChunk136 code
      else
        if code < 17041576399996956493199958849878894518272 then
          if code < 15033667702602505418215553621474006482944 then
            if code < 15031787978763287281301955412332251160576 then
              if code < 15022441573625054931474382284714213556224 then
                if code < 15020622524967348656617850651075666509824 then
                  decodeStateCodeChunk137 code
                else
                  decodeStateCodeChunk138 code
              else
                if code < 15022493546442962420512958697373937909760 then
                  decodeStateCodeChunk139 code
                else
                  if code < 15022493546567307657569572739930141442048 then
                    decodeStateCodeChunk140 code
                  else
                    decodeStateCodeChunk141 code
            else
              if code < 15031839951582054195374005965739193769984 then
                if code < 15031796640899772328024939883477014708224 then
                  decodeStateCodeChunk142 code
                else
                  if code < 15031796681002259905463869807439808331776 then
                    decodeStateCodeChunk143 code
                  else
                    decodeStateCodeChunk144 code
              else
                if code < 15031848653821026837788187213012259602432 then
                  decodeStateCodeChunk145 code
                else
                  if code < 15033667702477873006307796796001908113408 then
                    decodeStateCodeChunk146 code
                  else
                    decodeStateCodeChunk147 code
          else
            if code < 16976124334437747247020423568812245434368 then
              if code < 16974270636491415549942025528281345294336 then
                if code < 15033719675420984936191985536161198587904 then
                  decodeStateCodeChunk148 code
                else
                  if code < 16974218664415287111677612602332008153088 then
                    decodeStateCodeChunk149 code
                  else
                    decodeStateCodeChunk150 code
              else
                if code < 16976089685148404440782363062757890899968 then
                  decodeStateCodeChunk151 code
                else
                  if code < 16976098347657044442738044229879935975424 then
                    decodeStateCodeChunk152 code
                  else
                    decodeStateCodeChunk153 code
            else
              if code < 16976150360206975790961642911167440666624 then
                if code < 16976141658339350295754097318142500585472 then
                  decodeStateCodeChunk154 code
                else
                  if code < 16976143141759065276874900959662691237888 then
                    decodeStateCodeChunk155 code
                  else
                    decodeStateCodeChunk156 code
              else
                if code < 17019158793063362374710204445418614628352 then
                  decodeStateCodeChunk157 code
                else
                  if code < 17041575436794711976832638393084607987712 then
                    decodeStateCodeChunk158 code
                  else
                    decodeStateCodeChunk159 code
        else
          if code < 17380283780492310821244989428901498535936 then
            if code < 17043456604198846970880115681174458384384 then
              if code < 17043446459013106697993944474173129277440 then
                if code < 17041628853302888312098298284191457738752 then
                  decodeStateCodeChunk160 code
                else
                  decodeStateCodeChunk161 code
              else
                if code < 17043455120407812697695997750382677377024 then
                  decodeStateCodeChunk162 code
                else
                  if code < 17043455160634069411979558423879655014400 then
                    decodeStateCodeChunk163 code
                  else
                    decodeStateCodeChunk164 code
            else
              if code < 17378412718913207572736180100485771403264 then
                if code < 17043499874778645332063963436316231385088 then
                  decodeStateCodeChunk165 code
                else
                  if code < 17043508577018473530718045649903129640960 then
                    decodeStateCodeChunk166 code
                  else
                    decodeStateCodeChunk167 code
              else
                if code < 17378412759015695150857433685798527434752 then
                  decodeStateCodeChunk168 code
                else
                  if code < 17380283780491451285845093280655343828992 then
                    decodeStateCodeChunk169 code
                  else
                    decodeStateCodeChunk170 code
          else
            if code < 17447640553613514074122584604284543516672 then
              if code < 17425194070788162335026640872621225230336 then
                if code < 17380292442628771992666970770481190486016 then
                  decodeStateCodeChunk171 code
                else
                  if code < 17423317234327915802920675673653244043264 then
                    decodeStateCodeChunk172 code
                  else
                    decodeStateCodeChunk173 code
              else
                if code < 17445769492035271245138765395246293917696 then
                  decodeStateCodeChunk174 code
                else
                  if code < 17445769532137758822577695319169905459200 then
                    decodeStateCodeChunk175 code
                  else
                    decodeStateCodeChunk176 code
            else
              if code < 58544270799675336770368430698373684330496 then
                if code < 17447649215750000004970709359350607724544 then
                  decodeStateCodeChunk177 code
                else
                  if code < 17447649215874345242027305222674567610368 then
                    decodeStateCodeChunk178 code
                  else
                    decodeStateCodeChunk179 code
              else
                if code < 58611670722327109257648288303925328584704 then
                  decodeStateCodeChunk180 code
                else
                  if code < 58611679424566917783793964542485959049216 then
                    decodeStateCodeChunk181 code
                  else
                    decodeStateCodeChunk182 code
  else
    if code < 102328097641649884913766810910074127466496 then
      if code < 89732327851672186638912911599640825069568 then
        if code < 87711676430438540271328575885377391329280 then
          if code < 87372961108788600575614493320675851214848 then
            if code < 87305604335663958079688791858607559254016 then
              if code < 60089760525003681146417931696731767185408 then
                if code < 58679028979241070720356329168759657365504 then
                  decodeStateCodeChunk183 code
                else
                  decodeStateCodeChunk184 code
              else
                if code < 60225745840630087128608921528018901026304 then
                  decodeStateCodeChunk185 code
                else
                  if code < 68378412971037239008884538554554780516352 then
                    decodeStateCodeChunk186 code
                  else
                    decodeStateCodeChunk187 code
            else
              if code < 87307484019277751200998222898965508030464 then
                if code < 87305604336406596665180129306673324957696 then
                  decodeStateCodeChunk188 code
                else
                  if code < 87305612997803857613101883774696245198848 then
                    decodeStateCodeChunk189 code
                  else
                    decodeStateCodeChunk190 code
              else
                if code < 87307484046880871026588193771115728535552 then
                  decodeStateCodeChunk191 code
                else
                  if code < 87307484059502288825888649323197257744384 then
                    decodeStateCodeChunk192 code
                  else
                    decodeStateCodeChunk193 code
          else
            if code < 87709744733784876552422645282918657138688 then
              if code < 87374840792401557819503935640958168760320 then
                if code < 87372969770922506798134449807564107415552 then
                  decodeStateCodeChunk194 code
                else
                  if code < 87372969771666004915955147096561993908224 then
                    decodeStateCodeChunk195 code
                  else
                    decodeStateCodeChunk196 code
              else
                if code < 87374840822230874330597532040310923395072 then
                  decodeStateCodeChunk197 code
                else
                  if code < 87374840832624376373594613033239149805568 then
                    decodeStateCodeChunk198 code
                  else
                    decodeStateCodeChunk199 code
            else
              if code < 87709798190392103333713123707328978255872 then
                if code < 87709753438251741075498037143940489052160 then
                  decodeStateCodeChunk200 code
                else
                  if code < 87709796746702693141659920622854493732864 then
                    decodeStateCodeChunk201 code
                  else
                    decodeStateCodeChunk202 code
              else
                if code < 87709806852528564283549461674347391385600 then
                  decodeStateCodeChunk203 code
                else
                  if code < 87711624457619773136524141995757133660160 then
                    decodeStateCodeChunk204 code
                  else
                    decodeStateCodeChunk205 code
        else
          if code < 89719274012023339896302230152771839434752 then
            if code < 87777154963513307470035880320074002759680 then
              if code < 87777110169039127590798439132625140482048 then
                if code < 87711677874129669313107607671709546610688 then
                  decodeStateCodeChunk206 code
                else
                  decodeStateCodeChunk207 code
              else
                if code < 87777110209144193795930290050461071343616 then
                  decodeStateCodeChunk208 code
                else
                  if code < 87777111652832744452583224058528514736128 then
                    decodeStateCodeChunk209 code
                  else
                    decodeStateCodeChunk210 code
            else
              if code < 87779034647126264692432021233610208083968 then
                if code < 87777163627881146193758422577429129232384 then
                  decodeStateCodeChunk211 code
                else
                  if code < 87778981232973214594414861539064016830464 then
                    decodeStateCodeChunk212 code
                  else
                    decodeStateCodeChunk213 code
              else
                if code < 89719222039203713334076152738199904919552 then
                  decodeStateCodeChunk214 code
                else
                  if code < 89719256688493056361388110418677236965376 then
                    decodeStateCodeChunk215 code
                  else
                    decodeStateCodeChunk216 code
          else
            if code < 89721153735738041022576510747999272435712 then
              if code < 89721145033499096013549389810737224351744 then
                if code < 89721093060680329008387065478357233639424 then
                  decodeStateCodeChunk217 code
                else
                  if code < 89721101750418190921464497730810412007424 then
                    decodeStateCodeChunk218 code
                  else
                    decodeStateCodeChunk219 code
              else
                if code < 89721145033499096253728459228344170258432 then
                  decodeStateCodeChunk220 code
                else
                  if code < 89721145073601579649185763649449363537920 then
                    decodeStateCodeChunk221 code
                  else
                    decodeStateCodeChunk222 code
            else
              if code < 89730448168800029308724475372812600549376 then
                if code < 89726758098299689311257066988306282160128 then
                  decodeStateCodeChunk223 code
                else
                  if code < 89730448168057390723403737324358873358336 then
                    decodeStateCodeChunk224 code
                  else
                    decodeStateCodeChunk225 code
              else
                if code < 89730500140877017396678516532507053105152 then
                  decodeStateCodeChunk226 code
                else
                  if code < 89732319189537444760046903783432200888320 then
                    decodeStateCodeChunk227 code
                  else
                    decodeStateCodeChunk228 code
      else
        if code < 101923903786794816025439381422047406768128 then
          if code < 90134640538993637968268611728533253758976 then
            if code < 90123414410141679759765986182626656428032 then
              if code < 89732327891896724263803338023872574783488 then
                if code < 89732327879275306464502882471791045574656 then
                  decodeStateCodeChunk229 code
                else
                  decodeStateCodeChunk230 code
              else
                if code < 89732371202455256927976367046240197705728 then
                  decodeStateCodeChunk231 code
                else
                  if code < 89732379864715491177875015041169445912576 then
                    decodeStateCodeChunk232 code
                  else
                    decodeStateCodeChunk233 code
            else
              if code < 90125286915408474151703860005461130510336 then
                if code < 90123415893931858480633995835197607673856 then
                  decodeStateCodeChunk234 code
                else
                  if code < 90125285471719063958968326555229806428160 then
                    decodeStateCodeChunk235 code
                  else
                    decodeStateCodeChunk236 code
              else
                if code < 90125294133979298430623220980490812030976 then
                  decodeStateCodeChunk237 code
                else
                  if code < 90130899939735260765843357590853642723328 then
                    decodeStateCodeChunk238 code
                  else
                    decodeStateCodeChunk239 code
          else
            if code < 101922024103924497164390165802234945675264 then
              if code < 90136513044265589571923397409406384111616 then
                if code < 90134640579100423244200211068921031196672 then
                  decodeStateCodeChunk240 code
                else
                  if code < 90134642022788973900853536895301301338112 then
                    decodeStateCodeChunk241 code
                  else
                    decodeStateCodeChunk242 code
              else
                if code < 90136520262836413642050726748790778789888 then
                  decodeStateCodeChunk243 code
                else
                  if code < 90136521706525823834103932880063963365376 then
                    decodeStateCodeChunk244 code
                  else
                    decodeStateCodeChunk245 code
            else
              if code < 101922032766060982211113167944812169527296 then
                if code < 101922025546871267889726468440067533414400 then
                  decodeStateCodeChunk246 code
                else
                  if code < 101922025546874706915806419069573606121472 then
                    decodeStateCodeChunk247 code
                  else
                    decodeStateCodeChunk248 code
              else
                if code < 101922034209007752936449474237392642375680 then
                  decodeStateCodeChunk249 code
                else
                  if code < 101922034209011191962358865077080332206080 then
                    decodeStateCodeChunk250 code
                  else
                    decodeStateCodeChunk251 code
        else
          if code < 101923905270710483152693321733678841937920 then
            if code < 101923904749996200984913526260721702584320 then
              if code < 101923903787537454610944930968739992223744 then
                if code < 101923903786798254185646498128070568525824 then
                  decodeStateCodeChunk252 code
                else
                  decodeStateCodeChunk253 code
              else
                if code < 101923903814396217007288095566951903576064 then
                  decodeStateCodeChunk254 code
                else
                  if code < 101923903826900737802007122259565968310272 then
                    decodeStateCodeChunk255 code
                  else
                    decodeStateCodeChunk256 code
            else
              if code < 101923905270585850298623517633631388090368 then
                if code < 101923905230483365816219481506631939211264 then
                  decodeStateCodeChunk257 code
                else
                  if code < 101923905230486803957828433786899739394048 then
                    decodeStateCodeChunk258 code
                  else
                    decodeStateCodeChunk259 code
              else
                if code < 101923905270586709834037603943553722171392 then
                  decodeStateCodeChunk260 code
                else
                  if code < 101923905270590148215133846543503843868672 then
                    decodeStateCodeChunk261 code
                  else
                    decodeStateCodeChunk262 code
          else
            if code < 102326226620049926803256448267513457311744 then
              if code < 102326174647231159005054543321715718258688 then
                if code < 102326165944990468175970445497932039823360 then
                  decodeStateCodeChunk263 code
                else
                  if code < 102326174607128671409192783098200038080512 then
                    decodeStateCodeChunk264 code
                  else
                    decodeStateCodeChunk265 code
              else
                if code < 102326217917810953276371289389233279311872 then
                  decodeStateCodeChunk266 code
                else
                  if code < 102326217957913440872403606357140015185920 then
                    decodeStateCodeChunk267 code
                  else
                    decodeStateCodeChunk268 code
            else
              if code < 102328045668831117999865323194694822739968 then
                if code < 102328045668703334830162345251946343645184 then
                  decodeStateCodeChunk269 code
                else
                  if code < 102328045668706772769124986100755094781952 then
                    decodeStateCodeChunk270 code
                  else
                    decodeStateCodeChunk271 code
              else
                if code < 102328097641522101541597539808979980075008 then
                  decodeStateCodeChunk272 code
                else
                  if code < 102328097641525539683026458582140899246080 then
                    decodeStateCodeChunk273 code
                  else
                    decodeStateCodeChunk274 code
    else
      if code < 104337878081619008873613860903086067441664 then
        if code < 104277986627183140984485005074583399620608 then
          if code < 104270519864808394526135511907204663001088 then
            if code < 104270467892360087275077902136346901864448 then
              if code < 104268648843331778871114527456498727493632 then
                if code < 104268596871255650432338369039920230768640 then
                  decodeStateCodeChunk275 code
                else
                  decodeStateCodeChunk276 code
              else
                if code < 104268650287021189066223591028308833148928 then
                  decodeStateCodeChunk277 code
                else
                  if code < 104270467891988767982332242247324971687936 then
                    decodeStateCodeChunk278 code
                  else
                    decodeStateCodeChunk279 code
            else
              if code < 104270476594352345387246656564432902733824 then
                if code < 104270467892732266088055874018059185209344 then
                  decodeStateCodeChunk280 code
                else
                  if code < 104270476554868727479698887868625201053696 then
                    decodeStateCodeChunk281 code
                  else
                    decodeStateCodeChunk282 code
              else
                if code < 104270502541278111009658415681177008594944 then
                  decodeStateCodeChunk283 code
                else
                  if code < 104270519864807535006102190096743688986624 then
                    decodeStateCodeChunk284 code
                  else
                    decodeStateCodeChunk285 code
          else
            if code < 104270521348599428818439016617207010115584 then
              if code < 104270519904910878364422938604102317948928 then
                if code < 104270519864808394545254880405662210875392 then
                  decodeStateCodeChunk286 code
                else
                  if code < 104270519904910878142680929256146720735232 then
                    decodeStateCodeChunk287 code
                  else
                    decodeStateCodeChunk288 code
              else
                if code < 104270521308496945201893577332764049039360 then
                  decodeStateCodeChunk289 code
                else
                  if code < 104270521348599428799319626792608298909696 then
                    decodeStateCodeChunk290 code
                  else
                    decodeStateCodeChunk291 code
            else
              if code < 104270527123481702433868336117337054330880 then
                if code < 104270521348600288335401830758890357833728 then
                  decodeStateCodeChunk292 code
                else
                  if code < 104270521348601147888556416396070108807168 then
                    decodeStateCodeChunk293 code
                  else
                    decodeStateCodeChunk294 code
              else
                if code < 104270528567171112411684712323276614615040 then
                  decodeStateCodeChunk295 code
                else
                  if code < 104270530010860522603723301742466167422976 then
                    decodeStateCodeChunk296 code
                  else
                    decodeStateCodeChunk297 code
        else
          if code < 104281754695901016813796873314661926912000 then
            if code < 104281694021588522098764855655015894278144 then
              if code < 104279822999370127377603553128996041367552 then
                if code < 104278005434505318478436215828807485308928 then
                  decodeStateCodeChunk298 code
                else
                  decodeStateCodeChunk299 code
              else
                if code < 104279876415874866345028431507475827499008 then
                  decodeStateCodeChunk300 code
                else
                  if code < 104281694020843305131047725897940346757120 then
                    decodeStateCodeChunk301 code
                  else
                    decodeStateCodeChunk302 code
            else
              if code < 104281702723206022997477576096346950811648 then
                if code < 104281702683351085373459142024351374819328 then
                  decodeStateCodeChunk303 code
                else
                  if code < 104281702723082249678821861351609976143872 then
                    decodeStateCodeChunk304 code
                  else
                    decodeStateCodeChunk305 code
              else
                if code < 104281745993665509965644980749195059027968 then
                  decodeStateCodeChunk306 code
                else
                  if code < 104281747477453106097229620013997844283392 then
                    decodeStateCodeChunk307 code
                  else
                    decodeStateCodeChunk308 code
          else
            if code < 104336007060143252959017772383824124026880 then
              if code < 104315425864014137029504125411163916648448 then
                if code < 104281756139590427024272508177419331125248 then
                  decodeStateCodeChunk309 code
                else
                  if code < 104313554802437616366525508318700599812096 then
                    decodeStateCodeChunk310 code
                  else
                    decodeStateCodeChunk311 code
              else
                if code < 104322909909817543092086331996813187375104 then
                  decodeStateCodeChunk312 code
                else
                  if code < 104335955087324484829380699783346519744512 then
                    decodeStateCodeChunk313 code
                  else
                    decodeStateCodeChunk314 code
            else
              if code < 104337833367350659837354230558082027143168 then
                if code < 104337825628313076133744749122644517240832 then
                  decodeStateCodeChunk315 code
                else
                  if code < 104337826109171560257625764247233532649472 then
                    decodeStateCodeChunk316 code
                  else
                    decodeStateCodeChunk317 code
              else
                if code < 104337834770936727098549882083366290505728 then
                  decodeStateCodeChunk318 code
                else
                  if code < 104337834811163843348062757193856504086528 then
                    decodeStateCodeChunk319 code
                  else
                    decodeStateCodeChunk320 code
      else
        if code < 104349104210472686152250467515741189070848 then
          if code < 104349059456100994090105464064209327931392 then
            if code < 104347180735694435547095375937201353662464 then
              if code < 104337886783857977518445242260533267841024 then
                if code < 104337878121721492471722218182376776482816 then
                  decodeStateCodeChunk321 code
                else
                  decodeStateCodeChunk322 code
              else
                if code < 104337886783982322755501838123857227726848 then
                  decodeStateCodeChunk323 code
                else
                  if code < 104347179772490471978355853802265973334016 then
                    decodeStateCodeChunk324 code
                  else
                    decodeStateCodeChunk325 code
            else
              if code < 104349050793966228114025840105310634270720 then
                if code < 104347181216178163323753304427003668045824 then
                  decodeStateCodeChunk326 code
                else
                  if code < 104347233188996930237654400324070146023424 then
                    decodeStateCodeChunk327 code
                  else
                    decodeStateCodeChunk328 code
              else
                if code < 104349051757170191682765362240246014599168 then
                  decodeStateCodeChunk329 code
                else
                  if code < 104349052237653919459423290730048328982528 then
                    decodeStateCodeChunk330 code
                  else
                    decodeStateCodeChunk331 code
          else
            if code < 104349060899790403382339678107101196369920 then
              if code < 104349059456909816904301220916808156299264 then
                if code < 104349059456103572699219191222574220263424 then
                  decodeStateCodeChunk332 code
                else
                  if code < 104349059456843632878077291552180740866048 then
                    decodeStateCodeChunk333 code
                  else
                    decodeStateCodeChunk334 code
              else
                if code < 104349059496204337244950648659658169597952 then
                  decodeStateCodeChunk335 code
                else
                  if code < 104349059496329829394909365461447813578752 then
                    decodeStateCodeChunk336 code
                  else
                    decodeStateCodeChunk337 code
            else
              if code < 104349060939893747418566411434042720960512 then
                if code < 104349060899790404487709254739964026601472 then
                  decodeStateCodeChunk338 code
                else
                  if code < 104349060939892887017293685018472095367168 then
                    decodeStateCodeChunk339 code
                  else
                    decodeStateCodeChunk340 code
              else
                if code < 104349060939896326043203079512907670306816 then
                  decodeStateCodeChunk341 code
                else
                  if code < 104349060940017520516162425867579482652672 then
                    decodeStateCodeChunk342 code
                  else
                    decodeStateCodeChunk343 code
        else
          if code < 104684016854094834271854358400214614704128 then
            if code < 104672790685138669397358364410910595850240 then
              if code < 104349112912711654797067636777382679625728 then
                if code < 104349104250575169768781672766017244971008 then
                  decodeStateCodeChunk344 code
                else
                  decodeStateCodeChunk345 code
              else
                if code < 104349112912712514351075130848108743442432 then
                  decodeStateCodeChunk346 code
                else
                  if code < 104349112912836287430049306620630995779584 then
                    decodeStateCodeChunk347 code
                  else
                    decodeStateCodeChunk348 code
            else
              if code < 104674661746717772646037715351323017166848 then
                if code < 104672790725241156993390681480377288392704 then
                  decodeStateCodeChunk349 code
                else
                  if code < 104674661746716913128904301707057119313920 then
                    decodeStateCodeChunk350 code
                  else
                    decodeStateCodeChunk351 code
              else
                if code < 104674667521600905594073686366545149968384 then
                  decodeStateCodeChunk352 code
                else
                  if code < 104680274811147046653231514615612933570560 then
                    decodeStateCodeChunk353 code
                  else
                    decodeStateCodeChunk354 code
          else
            if code < 104751373587114409463405338054482277933056 then
              if code < 104725179286459267287551115418801294123008 then
                if code < 104685887875574028770197761269174690856960 then
                  decodeStateCodeChunk355 code
                else
                  if code < 104685896537833403263622615332075066834944 then
                    decodeStateCodeChunk356 code
                  else
                    decodeStateCodeChunk357 code
              else
                if code < 104740147498363220664940361284009131540480 then
                  decodeStateCodeChunk358 code
                else
                  if code < 104742018519838977021684267324713809821696 then
                    decodeStateCodeChunk359 code
                  else
                    decodeStateCodeChunk360 code
            else
              if code < 104753253310829138223237282626535776796672 then
                if code < 104751373627216897059267095840519815987200 then
                  decodeStateCodeChunk361 code
                else
                  if code < 104753244648692653194937085190363176976384 then
                    decodeStateCodeChunk362 code
                  else
                    decodeStateCodeChunk363 code
              else
                if code < 104753253310829998642947029503335468318720 then
                  decodeStateCodeChunk364 code
                else
                  if code < 104753253310891885191723778900188435529728 then
                    decodeStateCodeChunk365 code
                  else
                    decodeStateCodeChunk366 code

def decodeState
    (vector : Fin 53 -> Fin 6) : Fin 11742 :=
  decodeStateCode (stateVectorCode vector)

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14221.Shards
