import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.Shards.DecodeStatePart00
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.Shards.DecodeStatePart01
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.Shards.DecodeStatePart02
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.Shards.DecodeStatePart03
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.Shards.DecodeStatePart04
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.Shards.DecodeStatePart05
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.Shards.DecodeStatePart06
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.Shards.DecodeStatePart07
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.Shards.DecodeStatePart08
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.Shards.DecodeStatePart09
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.Shards.DecodeStatePart10
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.Shards.DecodeStatePart11

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.Shards

def stateVectorCode
    (vector : Fin 45 -> Fin 6) : Nat :=
  (vector (0 : Fin 45)).val + 6 * ((vector (1 : Fin 45)).val + 6 * ((vector (2 : Fin 45)).val + 6 * ((vector (3 : Fin 45)).val + 6 * ((vector (4 : Fin 45)).val + 6 * ((vector (5 : Fin 45)).val + 6 * ((vector (6 : Fin 45)).val + 6 * ((vector (7 : Fin 45)).val + 6 * ((vector (8 : Fin 45)).val + 6 * ((vector (9 : Fin 45)).val + 6 * ((vector (10 : Fin 45)).val + 6 * ((vector (11 : Fin 45)).val + 6 * ((vector (12 : Fin 45)).val + 6 * ((vector (13 : Fin 45)).val + 6 * ((vector (14 : Fin 45)).val + 6 * ((vector (15 : Fin 45)).val + 6 * ((vector (16 : Fin 45)).val + 6 * ((vector (17 : Fin 45)).val + 6 * ((vector (18 : Fin 45)).val + 6 * ((vector (19 : Fin 45)).val + 6 * ((vector (20 : Fin 45)).val + 6 * ((vector (21 : Fin 45)).val + 6 * ((vector (22 : Fin 45)).val + 6 * ((vector (23 : Fin 45)).val + 6 * ((vector (24 : Fin 45)).val + 6 * ((vector (25 : Fin 45)).val + 6 * ((vector (26 : Fin 45)).val + 6 * ((vector (27 : Fin 45)).val + 6 * ((vector (28 : Fin 45)).val + 6 * ((vector (29 : Fin 45)).val + 6 * ((vector (30 : Fin 45)).val + 6 * ((vector (31 : Fin 45)).val + 6 * ((vector (32 : Fin 45)).val + 6 * ((vector (33 : Fin 45)).val + 6 * ((vector (34 : Fin 45)).val + 6 * ((vector (35 : Fin 45)).val + 6 * ((vector (36 : Fin 45)).val + 6 * ((vector (37 : Fin 45)).val + 6 * ((vector (38 : Fin 45)).val + 6 * ((vector (39 : Fin 45)).val + 6 * ((vector (40 : Fin 45)).val + 6 * ((vector (41 : Fin 45)).val + 6 * ((vector (42 : Fin 45)).val + 6 * ((vector (43 : Fin 45)).val + 6 * ((vector (44 : Fin 45)).val))))))))))))))))))))))))))))))))))))))))))))

def decodeStateCode (code : Nat) : Fin 11742 :=
  if code < 86621353959008620207431117982969344 then
    if code < 83637739828193380268933660679088128 then
      if code < 65925878136750808681012763718821760 then
        if code < 49004858061133786395153898252289280 then
          if code < 37455589179712263431585808884408832 then
            if code < 14436888412815341247986915846003712 then
              if code < 11549366337782301408310106377221120 then
                if code < 8659778503301172336468801970003968 then
                  decodeStateCodeChunk0 code
                else
                  decodeStateCodeChunk1 code
              else
                if code < 13873225718469793499988096683722752 then
                  decodeStateCodeChunk2 code
                else
                  if code < 14356683437623617602011788927396864 then
                    decodeStateCodeChunk3 code
                  else
                    decodeStateCodeChunk4 code
            else
              if code < 16842666396768490129452466233010176 then
                if code < 15447227825920814996826084272580096 then
                  decodeStateCodeChunk5 code
                else
                  if code < 16762440792881715100297255672008192 then
                    decodeStateCodeChunk6 code
                  else
                    decodeStateCodeChunk7 code
              else
                if code < 17244063977085687403129263070768128 then
                  decodeStateCodeChunk8 code
                else
                  if code < 17324267234275305827709929786073600 then
                    decodeStateCodeChunk9 code
                  else
                    decodeStateCodeChunk10 code
          else
            if code < 47365851248674328049342275284604928 then
              if code < 43230343955415687113467071811912704 then
                if code < 43227744720108520284943626224406528 then
                  decodeStateCodeChunk11 code
                else
                  decodeStateCodeChunk12 code
              else
                if code < 43310551700223533434450646871275904 then
                  decodeStateCodeChunk13 code
                else
                  if code < 46404137718641752319782644030123264 then
                    decodeStateCodeChunk14 code
                  else
                    decodeStateCodeChunk15 code
            else
              if code < 48521773380368099900605263242992128 then
                if code < 48521400246290777173706448010961280 then
                  decodeStateCodeChunk16 code
                else
                  if code < 48521400342003502572228973788989952 then
                    decodeStateCodeChunk17 code
                  else
                    decodeStateCodeChunk18 code
              else
                if code < 49002626707235704256173795881547776 then
                  decodeStateCodeChunk19 code
                else
                  if code < 49002998026566347489414753384859648 then
                    decodeStateCodeChunk20 code
                  else
                    decodeStateCodeChunk21 code
        else
          if code < 51411007364405296757645756446470144 then
            if code < 49291516825544822330531032333579008 then
              if code < 49083206431941018997849543126185216 then
                if code < 49082835112389472426632960679408896 then
                  decodeStateCodeChunk22 code
                else
                  decodeStateCodeChunk23 code
              else
                if code < 49085430917514544301320699438316544 then
                  decodeStateCodeChunk24 code
                else
                  if code < 49085434355435249935751140388822784 then
                    decodeStateCodeChunk25 code
                  else
                    decodeStateCodeChunk26 code
            else
              if code < 51408779353378246054553921881831296 then
                if code < 50249520585083247698639632176562176 then
                  decodeStateCodeChunk27 code
                else
                  if code < 50255437642564105704040663504177152 then
                    decodeStateCodeChunk28 code
                  else
                    decodeStateCodeChunk29 code
              else
                if code < 51409147330070019583349042467141632 then
                  decodeStateCodeChunk30 code
                else
                  if code < 51410986639995300702394675600404864 then
                    decodeStateCodeChunk31 code
                  else
                    decodeStateCodeChunk32 code
          else
            if code < 51892608200842394306867392077049344 then
              if code < 51491212339595996781630112927394304 then
                if code < 51411375245826492749279865955556352 then
                  decodeStateCodeChunk33 code
                else
                  if code < 51488984415880862505735964132391424 then
                    decodeStateCodeChunk34 code
                  else
                    decodeStateCodeChunk35 code
              else
                if code < 51491583563656062455772625478503296 then
                  decodeStateCodeChunk36 code
                else
                  if code < 51892236785799025675121305579671936 then
                    decodeStateCodeChunk37 code
                  else
                    decodeStateCodeChunk38 code
            else
              if code < 51972813175996248809186650456641024 then
                if code < 51972789108877104978893601889754112 then
                  decodeStateCodeChunk39 code
                else
                  if code < 51972809737904790863646505083780096 then
                    decodeStateCodeChunk40 code
                  else
                    decodeStateCodeChunk41 code
              else
                if code < 54857467834931655115981384829529600 then
                  decodeStateCodeChunk42 code
                else
                  if code < 62366263404561760747611791191947264 then
                    decodeStateCodeChunk43 code
                  else
                    decodeStateCodeChunk44 code
      else
        if code < 80766182189326905071798952344181120 then
          if code < 77862735787299380705964181155240960 then
            if code < 69297062031438805341875605379613696 then
              if code < 66409708997952903373704141193986048 then
                if code < 66407479354932585317079909424298496 then
                  decodeStateCodeChunk45 code
                else
                  decodeStateCodeChunk46 code
              else
                if code < 68813257243652855223329025183328128 then
                  decodeStateCodeChunk47 code
                else
                  if code < 68815485262834053695642220948829440 then
                    decodeStateCodeChunk48 code
                  else
                    decodeStateCodeChunk49 code
            else
              if code < 72104066357061034052324077172654592 then
                if code < 70928840763686292460228631294332416 then
                  decodeStateCodeChunk50 code
                else
                  if code < 72088482980298132614263113958731264 then
                    decodeStateCodeChunk51 code
                  else
                    decodeStateCodeChunk52 code
              else
                if code < 72184281646493327922401275983278592 then
                  decodeStateCodeChunk53 code
                else
                  if code < 76681206376998182307940344502256640 then
                    decodeStateCodeChunk54 code
                  else
                    decodeStateCodeChunk55 code
          else
            if code < 77878712831312270975816052604403712 then
              if code < 77865335022311754667634557468901376 then
                if code < 77862867582690516540384198454269312 then
                  decodeStateCodeChunk56 code
                else
                  if code < 77863230306667131789557073377990016 then
                    decodeStateCodeChunk57 code
                  else
                    decodeStateCodeChunk58 code
              else
                if code < 77876235647415503745994028087525376 then
                  decodeStateCodeChunk59 code
                else
                  if code < 77876608686001174994091137970720768 then
                    decodeStateCodeChunk60 code
                  else
                    decodeStateCodeChunk61 code
            else
              if code < 77959029543415904423382534088971264 then
                if code < 77956440044278194522113159524058496 then
                  decodeStateCodeChunk62 code
                else
                  if code < 77958667967956483144720049241093504 then
                    decodeStateCodeChunk63 code
                  else
                    decodeStateCodeChunk64 code
              else
                if code < 77959041006579000046104407378811264 then
                  decodeStateCodeChunk65 code
                else
                  if code < 80752443945644586667809901024604160 then
                    decodeStateCodeChunk66 code
                  else
                    decodeStateCodeChunk67 code
        else
          if code < 83156582222931651344650255919634432 then
            if code < 81975045939443140947632419438817280 then
              if code < 81039319602431409582416517494267136 then
                if code < 80846389456537291718342357764961280 then
                  decodeStateCodeChunk68 code
                else
                  decodeStateCodeChunk69 code
              else
                if code < 81841309088934736514371567086710784 then
                  decodeStateCodeChunk70 code
                else
                  if code < 81974982333785681112340212654465024 then
                    decodeStateCodeChunk71 code
                  else
                    decodeStateCodeChunk72 code
            else
              if code < 83156510024795005842491462223931392 then
                if code < 81997323361969664368796311571323392 then
                  decodeStateCodeChunk73 code
                else
                  if code < 82000976403386546154187409435682816 then
                    decodeStateCodeChunk74 code
                  else
                    decodeStateCodeChunk75 code
              else
                if code < 83156520338998731181133387713413504 then
                  decodeStateCodeChunk76 code
                else
                  if code < 83156522055674563487852212944365568 then
                    decodeStateCodeChunk77 code
                  else
                    decodeStateCodeChunk78 code
          else
            if code < 83169949720074083995922526776596992 then
              if code < 83156583944877435495937569864267648 then
                if code < 83156582225584367799367756722886656 then
                  decodeStateCodeChunk79 code
                else
                  if code < 83156582225805441719257769735927808 then
                    decodeStateCodeChunk80 code
                  else
                    decodeStateCodeChunk81 code
              else
                if code < 83156893377621219672931033422476544 then
                  decodeStateCodeChunk82 code
                else
                  if code < 83156955264170010616161158749451520 then
                    decodeStateCodeChunk83 code
                  else
                    decodeStateCodeChunk84 code
            else
              if code < 83170322756056166326798201812057600 then
                if code < 83169949720124405605532852626398720 then
                  decodeStateCodeChunk85 code
                else
                  if code < 83169949720345308943694683874371584 then
                    decodeStateCodeChunk86 code
                  else
                    decodeStateCodeChunk87 code
              else
                if code < 83170322758709053363362368809631232 then
                  decodeStateCodeChunk88 code
                else
                  if code < 83250526006859034135002501465726976 then
                    decodeStateCodeChunk89 code
                  else
                    decodeStateCodeChunk90 code
    else
      if code < 86044324056647428437985953276869376 then
        if code < 83733913252081864585136177140398336 then
          if code < 83651552562094975323751839115442688 then
            if code < 83640340782313399632144698869091328 then
              if code < 83637751861725824949724494395000064 then
                if code < 83637750142397105629478685662828544 then
                  decodeStateCodeChunk91 code
                else
                  decodeStateCodeChunk92 code
              else
                if code < 83638123178366707063960079895164928 then
                  decodeStateCodeChunk93 code
                else
                  if code < 83638123181019594100558100211628032 then
                    decodeStateCodeChunk94 code
                  else
                    decodeStateCodeChunk95 code
            else
              if code < 83651179523742659878585761989756160 then
                if code < 83651117636935949362973839201510656 then
                  decodeStateCodeChunk96 code
                else
                  if code < 83651179521052927189868419916310528 then
                    decodeStateCodeChunk97 code
                  else
                    decodeStateCodeChunk98 code
              else
                if code < 83651490675546184380538640447912448 then
                  decodeStateCodeChunk99 code
                else
                  if code < 83651550840383570423092450760177664 then
                    decodeStateCodeChunk100 code
                  else
                    decodeStateCodeChunk101 code
          else
            if code < 83731384490717973424519539146741760 then
              if code < 83653716869590229155457844230310912 then
                if code < 83653335238488697958682293775968256 then
                  decodeStateCodeChunk102 code
                else
                  if code < 83653706557781472047065119799089408 then
                    decodeStateCodeChunk103 code
                  else
                    decodeStateCodeChunk104 code
              else
                if code < 83653718591314939430881464727735296 then
                  decodeStateCodeChunk105 code
                else
                  if code < 83653780477863730374026956757486592 then
                    decodeStateCodeChunk106 code
                  else
                    decodeStateCodeChunk107 code
            else
              if code < 83731757529328208441508742561161216 then
                if code < 83731695642779246916567364305345024 then
                  decodeStateCodeChunk108 code
                else
                  if code < 83731755810047593167306783706798080 then
                    decodeStateCodeChunk109 code
                  else
                    decodeStateCodeChunk110 code
              else
                if code < 83733550527884146174287365174629632 then
                  decodeStateCodeChunk111 code
                else
                  if code < 83733911532752121730664329382372736 then
                    decodeStateCodeChunk112 code
                  else
                    decodeStateCodeChunk113 code
        else
          if code < 84862423327274558301317316645791232 then
            if code < 83733983733984654270445406468557056 then
              if code < 83733923566505639585895078923663616 then
                if code < 83733921847397994183575790712862976 then
                  decodeStateCodeChunk114 code
                else
                  decodeStateCodeChunk115 code
              else
                if code < 83733983731330743744646248180612096 then
                  decodeStateCodeChunk116 code
                else
                  if code < 83733983733762727443099374782381056 then
                    decodeStateCodeChunk117 code
                  else
                    decodeStateCodeChunk118 code
            else
              if code < 83928895681712159690397782128325376 then
                if code < 83733985453055454019883594883197952 then
                  decodeStateCodeChunk119 code
                else
                  if code < 83926690114201383399314292254354688 then
                    decodeStateCodeChunk120 code
                  else
                    decodeStateCodeChunk121 code
              else
                if code < 84728748363278952066623771949195264 then
                  decodeStateCodeChunk122 code
                else
                  if code < 84862352845334751587589812860035072 then
                    decodeStateCodeChunk123 code
                  else
                    decodeStateCodeChunk124 code
          else
            if code < 86043951018024939966907087267140864 then
              if code < 84888405363082841525698017056077824 then
                if code < 84864601389873269004714008512413696 then
                  decodeStateCodeChunk125 code
                else
                  if code < 84884693873555580500988780745775616 then
                    decodeStateCodeChunk126 code
                  else
                    decodeStateCodeChunk127 code
              else
                if code < 84890552482591557971183856235689984 then
                  decodeStateCodeChunk128 code
                else
                  if code < 86043890850767852063797706227949952 then
                    decodeStateCodeChunk129 code
                  else
                    decodeStateCodeChunk130 code
            else
              if code < 86043961332475326507618514890252288 then
                if code < 86043952737317666501036140804792704 then
                  decodeStateCodeChunk131 code
                else
                  if code < 86043961330055795275119388464901632 then
                    decodeStateCodeChunk132 code
                  else
                    decodeStateCodeChunk133 code
              else
                if code < 86043961332708682267894287482955648 then
                  decodeStateCodeChunk134 code
                else
                  if code < 86044262167445579873975262421739520 then
                    decodeStateCodeChunk135 code
                  else
                    decodeStateCodeChunk136 code
      else
        if code < 86137906830191275251601459310796288 then
          if code < 86057328827210509810617939211069440 then
            if code < 86046178933781243342041746987141120 then
              if code < 86046098137607175537060587757011328 then
                if code < 86044334371072227697550420178384768 then
                  decodeStateCodeChunk137 code
                else
                  decodeStateCodeChunk138 code
              else
                if code < 86046118766525349553684804796049408 then
                  decodeStateCodeChunk139 code
                else
                  if code < 86046158305085168335685090733446400 then
                    decodeStateCodeChunk140 code
                  else
                    decodeStateCodeChunk141 code
            else
              if code < 86046551969750844776505666071350272 then
                if code < 86046180653068170140101729998680064 then
                  decodeStateCodeChunk142 code
                else
                  if code < 86046490085854940822411207981811072 then
                    decodeStateCodeChunk143 code
                  else
                    decodeStateCodeChunk144 code
              else
                if code < 86046551972403902393663926478331648 then
                  decodeStateCodeChunk145 code
                else
                  if code < 86057328826988582982256294901434368 then
                    decodeStateCodeChunk146 code
                  else
                    decodeStateCodeChunk147 code
          else
            if code < 86059556742965959485181012266448128 then
              if code < 86059505170775607582335188118588928 then
                if code < 86057700146540129509801638860513664 then
                  decodeStateCodeChunk148 code
                else
                  if code < 86057701865610929301911937912023040 then
                    decodeStateCodeChunk149 code
                  else
                    decodeStateCodeChunk150 code
              else
                if code < 86059546428307805191714509524371968 then
                  decodeStateCodeChunk151 code
                else
                  if code < 86059546428542355024087541351393152 then
                    decodeStateCodeChunk152 code
                  else
                    decodeStateCodeChunk153 code
            else
              if code < 86059919466942774558019795254009600 then
                if code < 86059898835335722362683145455373312 then
                  decodeStateCodeChunk154 code
                else
                  if code < 86059919464289716940861534847028224 then
                    decodeStateCodeChunk155 code
                  else
                    decodeStateCodeChunk156 code
              else
                if code < 86059928062296773301249909916733952 then
                  decodeStateCodeChunk157 code
                else
                  if code < 86137533794210386992806597919105024 then
                    decodeStateCodeChunk158 code
                  else
                    decodeStateCodeChunk159 code
        else
          if code < 86541066468251678123859731779021824 then
            if code < 86140133037488496815501773036405248 then
              if code < 86139761717937803153095823022853632 then
                if code < 86139751403511981172021932777129984 then
                  decodeStateCodeChunk160 code
                else
                  decodeStateCodeChunk161 code
              else
                if code < 86140122722805778752127969031238144 then
                  decodeStateCodeChunk162 code
                else
                  if code < 86140133034835609779056092654944768 then
                    decodeStateCodeChunk163 code
                  else
                    decodeStateCodeChunk164 code
            else
              if code < 86527719602703646189782290037266688 then
                if code < 86527305306573353297672423360366592 then
                  decodeStateCodeChunk165 code
                else
                  if code < 86527348283398618647292417635101184 then
                    decodeStateCodeChunk166 code
                  else
                    decodeStateCodeChunk167 code
              else
                if code < 86540714058645588713219661779569152 then
                  decodeStateCodeChunk168 code
                else
                  if code < 86540775945415453579809843669920256 then
                    decodeStateCodeChunk169 code
                  else
                    decodeStateCodeChunk170 code
          else
            if code < 86620991234823354262655330474969088 then
              if code < 86541148983829178444666203392678144 then
                if code < 86541087097243541845525656954866688 then
                  decodeStateCodeChunk171 code
                else
                  if code < 86541128354875182244372190446740864 then
                    decodeStateCodeChunk172 code
                  else
                    decodeStateCodeChunk173 code
              else
                if code < 86541159298253976892563494423430528 then
                  decodeStateCodeChunk174 code
                else
                  if code < 86620960291481406846110088268510464 then
                    decodeStateCodeChunk175 code
                  else
                    decodeStateCodeChunk176 code
            else
              if code < 86621331608343220728610266895494144 then
                if code < 86621271443554962219505720911288576 then
                  decodeStateCodeChunk177 code
                else
                  if code < 86621292072459829260578687534820864 then
                    decodeStateCodeChunk178 code
                  else
                    decodeStateCodeChunk179 code
              else
                if code < 86621333330103751543651030740993408 then
                  decodeStateCodeChunk180 code
                else
                  if code < 86621352239907115747936202876825088 then
                    decodeStateCodeChunk181 code
                  else
                    decodeStateCodeChunk182 code
  else
    if code < 101058196486195430712270306965979648 then
      if code < 100481166347702388539716640120781312 then
        if code < 95283190728624404792370928872370176 then
          if code < 94031597189971237788729993019871232 then
            if code < 88253486772181157761583114460390912 then
              if code < 86621362554141715611551521533428736 then
                if code < 86621362551722184379052382047384064 then
                  decodeStateCodeChunk183 code
                else
                  decodeStateCodeChunk184 code
              else
                if code < 86621362554375071371827281065438080 then
                  decodeStateCodeChunk185 code
                else
                  if code < 86621364273445871120249874270878592 then
                    decodeStateCodeChunk186 code
                  else
                    decodeStateCodeChunk187 code
            else
              if code < 89506326645119672998426269336669696 then
                if code < 89412755950392606854628006101036544 then
                  decodeStateCodeChunk188 code
                else
                  if code < 89492960918288038241161079360294400 then
                    decodeStateCodeChunk189 code
                  else
                    decodeStateCodeChunk190 code
              else
                if code < 89508545974365279531199969162627584 then
                  decodeStateCodeChunk191 code
                else
                  if code < 93872290881717570844289321525735424 then
                    decodeStateCodeChunk192 code
                  else
                    decodeStateCodeChunk193 code
          else
            if code < 95267595358344462421903230747479040 then
              if code < 95187503849781112028392714301122560 then
                if code < 95187130238138089330058282224536960 then
                  decodeStateCodeChunk194 code
                else
                  if code < 95187140552562888610324053264074112 then
                    decodeStateCodeChunk195 code
                  else
                    decodeStateCodeChunk196 code
              else
                if code < 95189731765500740330783428424616960 then
                  decodeStateCodeChunk197 code
                else
                  if code < 95267337497463509332133785709303808 then
                    decodeStateCodeChunk198 code
                  else
                    decodeStateCodeChunk199 code
            else
              if code < 95269936740729309630045812244409344 then
                if code < 95267719131438973844704135857537024 then
                  decodeStateCodeChunk200 code
                else
                  if code < 95269812967633774716875831841884160 then
                    decodeStateCodeChunk201 code
                  else
                    decodeStateCodeChunk202 code
              else
                if code < 95280962806015834187194602225209856 then
                  decodeStateCodeChunk203 code
                else
                  if code < 95282931146243535766013253299177472 then
                    decodeStateCodeChunk204 code
                  else
                    decodeStateCodeChunk205 code
        else
          if code < 99299317190244883872814811271845376 then
            if code < 98157294932313114805411419125898240 then
              if code < 95283313929804950397015953039961984 then
                if code < 95283304184866057405778949758512128 then
                  decodeStateCodeChunk206 code
                else
                  decodeStateCodeChunk207 code
              else
                if code < 97001378244590241243519505263863808 then
                  decodeStateCodeChunk208 code
                else
                  if code < 98156921321443849268560555230870912 then
                    decodeStateCodeChunk209 code
                  else
                    decodeStateCodeChunk210 code
            else
              if code < 98443727058739427941238329132332288 then
                if code < 98170662376339155039540539990780928 then
                  decodeStateCodeChunk211 code
                else
                  if code < 98363530685939048416394711238401280 then
                    decodeStateCodeChunk212 code
                  else
                    decodeStateCodeChunk213 code
              else
                if code < 99165571744604411474453763706816512 then
                  decodeStateCodeChunk214 code
                else
                  if code < 99165953378321956414016121419182080 then
                    decodeStateCodeChunk215 code
                  else
                    decodeStateCodeChunk216 code
          else
            if code < 100480784713775198656018447813079040 then
              if code < 99379822995973275798447048746110464 then
                if code < 99321536164622993067640930670062080 then
                  decodeStateCodeChunk217 code
                else
                  if code < 99325247654150419935696459687806976 then
                    decodeStateCodeChunk218 code
                  else
                    decodeStateCodeChunk219 code
              else
                if code < 99405516227483094753218450175954432 then
                  decodeStateCodeChunk220 code
                else
                  if code < 100480784711344238447934409564471296 then
                    decodeStateCodeChunk221 code
                  else
                    decodeStateCodeChunk222 code
            else
              if code < 100480795028409642880420051271170560 then
                if code < 100480784713997125483364490383166720 then
                  decodeStateCodeChunk223 code
                else
                  if code < 100480793309129022867752029383186432 then
                    decodeStateCodeChunk224 code
                  else
                    decodeStateCodeChunk225 code
              else
                if code < 100480855195677984392862752587536384 then
                  decodeStateCodeChunk226 code
                else
                  if code < 100481156033289871099988970772691328 then
                    decodeStateCodeChunk227 code
                  else
                    decodeStateCodeChunk228 code
      else
        if code < 101042590804572418562795220451768320 then
          if code < 100574800648283599857968311575387648 then
            if code < 100561060163353194636711200136419328 then
              if code < 100560989681009284507123777004859264 then
                if code < 100481228234263631949036168025898496 then
                  decodeStateCodeChunk229 code
                else
                  decodeStateCodeChunk230 code
              else
                if code < 100560998276362255810216460673847680 then
                  decodeStateCodeChunk231 code
                else
                  if code < 100560999996305074135348347347606016 then
                    decodeStateCodeChunk232 code
                  else
                    decodeStateCodeChunk233 code
            else
              if code < 100561433200170250835169567871999488 then
                if code < 100561360997870217093366200194315776 then
                  decodeStateCodeChunk234 code
                else
                  if code < 100561371313400385972218709187124736 then
                    decodeStateCodeChunk235 code
                  else
                    decodeStateCodeChunk236 code
              else
                if code < 100574427608372503843737749853838848 then
                  decodeStateCodeChunk237 code
                else
                  if code < 100574427610583243040741937398111744 then
                    decodeStateCodeChunk238 code
                  else
                    decodeStateCodeChunk239 code
          else
            if code < 100964613752443695991740064960060800 then
              if code < 100962024831819275700718981971376128 then
                if code < 100962014514741589384007530550378496 then
                  decodeStateCodeChunk240 code
                else
                  if code < 100962014517394476420046971109084416 then
                    decodeStateCodeChunk241 code
                  else
                    decodeStateCodeChunk242 code
              else
                if code < 100962385836688245569712637427944704 then
                  decodeStateCodeChunk243 code
                else
                  if code < 100964240713822226272648389498427776 then
                    decodeStateCodeChunk244 code
                  else
                    decodeStateCodeChunk245 code
            else
              if code < 101042228079760459830222964756469760 then
                if code < 101042217766183281156874783881411840 then
                  decodeStateCodeChunk246 code
                else
                  if code < 101042219485241803759859221704307200 then
                    decodeStateCodeChunk247 code
                  else
                    decodeStateCodeChunk248 code
              else
                if code < 101042229799273582738365833116588032 then
                  decodeStateCodeChunk249 code
                else
                  if code < 101042590803700404768307389450302976 then
                    decodeStateCodeChunk250 code
                  else
                    decodeStateCodeChunk251 code
        else
          if code < 101055968562479102364261972216748032 then
            if code < 101044818727377500064707197266017664 then
              if code < 101042601118346277968141551735954944 then
                if code < 101042601118124180514364032875876736 then
                  decodeStateCodeChunk252 code
                else
                  decodeStateCodeChunk253 code
              else
                if code < 101044445689013949961888071018380544 then
                  decodeStateCodeChunk254 code
                else
                  if code < 101044447408084924987155716770376064 then
                    decodeStateCodeChunk255 code
                  else
                    decodeStateCodeChunk256 code
            else
              if code < 101044818728299835511629804689155840 then
                if code < 101044818727598574027083112424558848 then
                  decodeStateCodeChunk257 code
                else
                  if code < 101044818727636443171755048534541312 then
                    decodeStateCodeChunk258 code
                  else
                    decodeStateCodeChunk259 code
              else
                if code < 101055595526547507485327799421445376 then
                  decodeStateCodeChunk260 code
                else
                  if code < 101055657413943748411481516763353472 then
                    decodeStateCodeChunk261 code
                  else
                    decodeStateCodeChunk262 code
          else
            if code < 101058184455093601082583474130812288 then
              if code < 101056030449029087379589354601258496 then
                if code < 101055968565131989400707652598208512 then
                  decodeStateCodeChunk263 code
                else
                  if code < 101055968566017479108033936140605312 then
                    decodeStateCodeChunk264 code
                  else
                    decodeStateCodeChunk265 code
              else
                if code < 101057813134474554100293464834813952 then
                  decodeStateCodeChunk266 code
                else
                  if code < 101057823450225625527222111299819520 then
                    decodeStateCodeChunk267 code
                  else
                    decodeStateCodeChunk268 code
            else
              if code < 101058186174423348632764551750368640 then
                if code < 101058186171770461640006581568541696 then
                  decodeStateCodeChunk269 code
                else
                  if code < 101058186174201421804402922678209920 then
                    decodeStateCodeChunk270 code
                  else
                    decodeStateCodeChunk271 code
              else
                if code < 101058186175048871872653752711094528 then
                  decodeStateCodeChunk272 code
                else
                  if code < 101058194769518570198517983058361344 then
                    decodeStateCodeChunk273 code
                  else
                    decodeStateCodeChunk274 code
    else
      if code < 103450658596811967908603372758267392 then
        if code < 103368535140179806357885274394150912 then
          if code < 102208904956848632255033421106796544 then
            if code < 101250971679391079951475666596733696 then
              if code < 101058256653414474105285579708595200 then
                if code < 101058196488848147165955281536944384 then
                  decodeStateCodeChunk275 code
                else
                  decodeStateCodeChunk276 code
              else
                if code < 101058256656988502472885826915469568 then
                  decodeStateCodeChunk277 code
                else
                  if code < 101058258376060330451074433307836928 then
                    decodeStateCodeChunk278 code
                  else
                    decodeStateCodeChunk279 code
            else
              if code < 102053023053585588398643875378320896 then
                if code < 101331106165642497947721199255714560 then
                  decodeStateCodeChunk280 code
                else
                  if code < 102052950851285554653184349260574208 then
                    decodeStateCodeChunk281 code
                  else
                    decodeStateCodeChunk282 code
              else
                if code < 102055591345513933728181812309778944 then
                  decodeStateCodeChunk283 code
                else
                  if code < 102186997134757964231880258567323136 then
                    decodeStateCodeChunk284 code
                  else
                    decodeStateCodeChunk285 code
          else
            if code < 103368163818025381626664997295011328 then
              if code < 102266892669873448029735434076581376 then
                if code < 102209276276393156545123082629269504 then
                  decodeStateCodeChunk286 code
                else
                  if code < 102212680052469360015917499937273344 then
                    decodeStateCodeChunk287 code
                  else
                    decodeStateCodeChunk288 code
              else
                if code < 102289170092437835856174326611470336 then
                  decodeStateCodeChunk289 code
                else
                  if code < 102295030428099000227334105861096960 then
                    decodeStateCodeChunk290 code
                  else
                    decodeStateCodeChunk291 code
            else
              if code < 103368223988118385979689505655926784 then
                if code < 103368163820641423008808289220723456 then
                  decodeStateCodeChunk292 code
                else
                  if code < 103368163820899171957432460966590848 then
                    decodeStateCodeChunk293 code
                  else
                    decodeStateCodeChunk294 code
              else
                if code < 103368225707227059608964435221299968 then
                  decodeStateCodeChunk295 code
                else
                  if code < 103368234302544208728421254680532864 then
                    decodeStateCodeChunk296 code
                  else
                    decodeStateCodeChunk297 code
        else
          if code < 103448368787911331067686977346778624 then
            if code < 103370391736612659361483081679208960 then
              if code < 103368607341165678468230612692814592 then
                if code < 103368597024087992152534763011364352 then
                  decodeStateCodeChunk298 code
                else
                  decodeStateCodeChunk299 code
              else
                if code < 103370371107407056734205012041106944 then
                  decodeStateCodeChunk300 code
                else
                  if code < 103370390017326068944657993190529408 then
                    decodeStateCodeChunk301 code
                  else
                    decodeStateCodeChunk302 code
            else
              if code < 103370763055905405020762743929841152 then
                if code < 103370432994029537386285343879954304 then
                  decodeStateCodeChunk303 code
                else
                  if code < 103370453623167761832091963273889280 then
                    decodeStateCodeChunk304 code
                  else
                    decodeStateCodeChunk305 code
              else
                if code < 103370783684693760005948490928310784 then
                  decodeStateCodeChunk306 code
                else
                  if code < 103448367067476213918936556431519744 then
                    decodeStateCodeChunk307 code
                  else
                    decodeStateCodeChunk308 code
          else
            if code < 103448812308177666952916899350080256 then
              if code < 103448439270649284949219216075333632 then
                if code < 103448428955352471874465616211113472 then
                  decodeStateCodeChunk309 code
                else
                  if code < 103448430675307572038967586714387200 then
                    decodeStateCodeChunk310 code
                  else
                    decodeStateCodeChunk311 code
              else
                if code < 103448740107191794842571563228198912 then
                  decodeStateCodeChunk312 code
                else
                  if code < 103448801993752867629995948686684032 then
                    decodeStateCodeChunk313 code
                  else
                    decodeStateCodeChunk314 code
            else
              if code < 103450596711588596989655484999856128 then
                if code < 103450574363526952271385360807591936 then
                  decodeStateCodeChunk315 code
                else
                  if code < 103450594992517792459011429327563136 then
                    decodeStateCodeChunk316 code
                  else
                    decodeStateCodeChunk317 code
              else
                if code < 103450636250076766708623873758676480 then
                  decodeStateCodeChunk318 code
                else
                  if code < 103450656879060442507540299087143424 then
                    decodeStateCodeChunk319 code
                  else
                    decodeStateCodeChunk320 code
      else
        if code < 103931826229359467224691788690139520 then
          if code < 103464024326737756201808387449797888 then
            if code < 103451029917431157086004315242961408 then
              if code < 103450968030882366139304222553033216 then
                if code < 103450947402112599827575768269335040 then
                  decodeStateCodeChunk321 code
                else
                  decodeStateCodeChunk322 code
              else
                if code < 103450968031140285712328671463361024 then
                  decodeStateCodeChunk323 code
                else
                  if code < 103451009288661390774428198717483520 then
                    decodeStateCodeChunk324 code
                  else
                    decodeStateCodeChunk325 code
            else
              if code < 103462178035893767971806033031896576 then
                if code < 103451029917689076659181104088291840 then
                  decodeStateCodeChunk326 code
                else
                  if code < 103461806716564148185280770655639424 then
                    decodeStateCodeChunk327 code
                  else
                    decodeStateCodeChunk328 code
              else
                if code < 103462179755848868136477270129617664 then
                  decodeStateCodeChunk329 code
                else
                  if code < 103464024323201596977864476800218624 then
                    decodeStateCodeChunk330 code
                  else
                    decodeStateCodeChunk331 code
          else
            if code < 103464407678679706733488513851657984 then
              if code < 103464397362891619072560498478225920 then
                if code < 103464354388264806297337622076013056 then
                  decodeStateCodeChunk332 code
                else
                  if code < 103464376736185207721541836285391744 then
                    decodeStateCodeChunk333 code
                  else
                    decodeStateCodeChunk334 code
              else
                if code < 103464397364475982120035444082426752 then
                  decodeStateCodeChunk335 code
                else
                  if code < 103464405956956015211254503682687488 then
                    decodeStateCodeChunk336 code
                  else
                    decodeStateCodeChunk337 code
            else
              if code < 103851992572822684200206834624374272 then
                if code < 103851600621713241400439088427081728 then
                  decodeStateCodeChunk338 code
                else
                  if code < 103851951315031372945722720849478656 then
                    decodeStateCodeChunk339 code
                  else
                    decodeStateCodeChunk340 code
              else
                if code < 103931805596905135628142405807808512 then
                  decodeStateCodeChunk341 code
                else
                  if code < 103931824509404367102844945567948800 then
                    decodeStateCodeChunk342 code
                  else
                    decodeStateCodeChunk343 code
        else
          if code < 103945544366780912570417293056624384 then
            if code < 103932197548026860312152877505010176 then
              if code < 103932197545115030212313668557112320 then
                if code < 103932176918850768322851212860731648 then
                  decodeStateCodeChunk344 code
                else
                  decodeStateCodeChunk345 code
              else
                if code < 103932197547767917247743749375807744 then
                  decodeStateCodeChunk346 code
                else
                  if code < 103932197547989844077290246781961216 then
                    decodeStateCodeChunk347 code
                  else
                    decodeStateCodeChunk348 code
            else
              if code < 103945253842740035124106637866020864 then
                if code < 103945171324621208215730652742901760 then
                  decodeStateCodeChunk349 code
                else
                  if code < 103945191956191244177237200217481216 then
                    decodeStateCodeChunk350 code
                  else
                    decodeStateCodeChunk351 code
              else
                if code < 103945523737673394437268485887916544 then
                  decodeStateCodeChunk352 code
                else
                  if code < 103945544365637503246412677601767680 then
                    decodeStateCodeChunk353 code
                  else
                    decodeStateCodeChunk354 code
          else
            if code < 103945606252408562184490665384785664 then
              if code < 103945564994776920163529444355033600 then
                if code < 103945564991902959207363032792455680 then
                  decodeStateCodeChunk355 code
                else
                  if code < 103945564994554822753439635694588928 then
                    decodeStateCodeChunk356 code
                  else
                    decodeStateCodeChunk357 code
              else
                if code < 103945564994813765817002426501908992 then
                  decodeStateCodeChunk358 code
                else
                  if code < 103945585623558963624975666866416128 then
                    decodeStateCodeChunk359 code
                  else
                    decodeStateCodeChunk360 code
            else
              if code < 103945626881362556763685592532392448 then
                if code < 103945625162033832702858541368469248 then
                  decodeStateCodeChunk361 code
                else
                  if code < 103945626881104637147007288918102912 then
                    decodeStateCodeChunk362 code
                  else
                    decodeStateCodeChunk363 code
              else
                if code < 103945635476457607660369827897652608 then
                  decodeStateCodeChunk364 code
                else
                  if code < 103945637193134468217775457960083968 then
                    decodeStateCodeChunk365 code
                  else
                    decodeStateCodeChunk366 code

def decodeState
    (vector : Fin 45 -> Fin 6) : Fin 11742 :=
  decodeStateCode (stateVectorCode vector)

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14267.Shards
