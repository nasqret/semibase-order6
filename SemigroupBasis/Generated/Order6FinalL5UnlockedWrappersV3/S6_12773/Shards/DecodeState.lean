import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.Shards.DecodeStatePart00
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.Shards.DecodeStatePart01
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.Shards.DecodeStatePart02
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.Shards.DecodeStatePart03
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.Shards.DecodeStatePart04
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.Shards.DecodeStatePart05
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.Shards.DecodeStatePart06
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.Shards.DecodeStatePart07
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.Shards.DecodeStatePart08
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.Shards.DecodeStatePart09
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.Shards.DecodeStatePart10
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.Shards.DecodeStatePart11

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.Shards

def stateVectorCode
    (vector : Fin 44 -> Fin 6) : Nat :=
  (vector (0 : Fin 44)).val + 6 * ((vector (1 : Fin 44)).val + 6 * ((vector (2 : Fin 44)).val + 6 * ((vector (3 : Fin 44)).val + 6 * ((vector (4 : Fin 44)).val + 6 * ((vector (5 : Fin 44)).val + 6 * ((vector (6 : Fin 44)).val + 6 * ((vector (7 : Fin 44)).val + 6 * ((vector (8 : Fin 44)).val + 6 * ((vector (9 : Fin 44)).val + 6 * ((vector (10 : Fin 44)).val + 6 * ((vector (11 : Fin 44)).val + 6 * ((vector (12 : Fin 44)).val + 6 * ((vector (13 : Fin 44)).val + 6 * ((vector (14 : Fin 44)).val + 6 * ((vector (15 : Fin 44)).val + 6 * ((vector (16 : Fin 44)).val + 6 * ((vector (17 : Fin 44)).val + 6 * ((vector (18 : Fin 44)).val + 6 * ((vector (19 : Fin 44)).val + 6 * ((vector (20 : Fin 44)).val + 6 * ((vector (21 : Fin 44)).val + 6 * ((vector (22 : Fin 44)).val + 6 * ((vector (23 : Fin 44)).val + 6 * ((vector (24 : Fin 44)).val + 6 * ((vector (25 : Fin 44)).val + 6 * ((vector (26 : Fin 44)).val + 6 * ((vector (27 : Fin 44)).val + 6 * ((vector (28 : Fin 44)).val + 6 * ((vector (29 : Fin 44)).val + 6 * ((vector (30 : Fin 44)).val + 6 * ((vector (31 : Fin 44)).val + 6 * ((vector (32 : Fin 44)).val + 6 * ((vector (33 : Fin 44)).val + 6 * ((vector (34 : Fin 44)).val + 6 * ((vector (35 : Fin 44)).val + 6 * ((vector (36 : Fin 44)).val + 6 * ((vector (37 : Fin 44)).val + 6 * ((vector (38 : Fin 44)).val + 6 * ((vector (39 : Fin 44)).val + 6 * ((vector (40 : Fin 44)).val + 6 * ((vector (41 : Fin 44)).val + 6 * ((vector (42 : Fin 44)).val + 6 * ((vector (43 : Fin 44)).val)))))))))))))))))))))))))))))))))))))))))))

def decodeStateCode (code : Nat) : Fin 11742 :=
  if code < 12731201875666746584381272158167040 then
    if code < 7892172338486596757858090113818624 then
      if code < 7094578927989315098425839119622144 then
        if code < 6961027779021805558524757197840384 then
          if code < 6956444143349366449071681733976064 then
            if code < 6934168419947407842590937988325376 then
              if code < 6929712588986632722109819051892736 then
                if code < 6929709723316460134208043985674240 then
                  decodeStateCodeChunk0 code
                else
                  decodeStateCodeChunk1 code
              else
                if code < 6930451792857170299494388052385792 then
                  decodeStateCodeChunk2 code
                else
                  if code < 6930452385777479894951215079743488 then
                    decodeStateCodeChunk3 code
                  else
                    decodeStateCodeChunk4 code
            else
              if code < 6934289331905865862551796518346752 then
                if code < 6934168444265027266688008992645120 then
                  decodeStateCodeChunk5 code
                else
                  if code < 6934168993413212461796126939799552 then
                    decodeStateCodeChunk6 code
                  else
                    decodeStateCodeChunk7 code
              else
                if code < 6934351214475837999531088690028544 then
                  decodeStateCodeChunk8 code
                else
                  if code < 6935031966512538108586851289915392 then
                    decodeStateCodeChunk9 code
                  else
                    decodeStateCodeChunk10 code
          else
            if code < 6960903433342714734823686684598272 then
              if code < 6956447673015571079491143122608128 then
                if code < 6956447577512147136128280447885312 then
                  decodeStateCodeChunk11 code
                else
                  decodeStateCodeChunk12 code
              else
                if code < 6956447697333699879581535151595520 then
                  decodeStateCodeChunk13 code
                else
                  if code < 6960903409025095310726615680278528 then
                    decodeStateCodeChunk14 code
                  else
                    decodeStateCodeChunk15 code
            else
              if code < 6961024317114702874998580587651072 then
                if code < 6960903508949995279314886907142144 then
                  decodeStateCodeChunk16 code
                else
                  if code < 6960904005924166811522535095869440 then
                    decodeStateCodeChunk17 code
                  else
                    decodeStateCodeChunk18 code
              else
                if code < 6961027281605429326299033884762112 then
                  decodeStateCodeChunk19 code
                else
                  if code < 6961027755587915576741630561869824 then
                    decodeStateCodeChunk20 code
                  else
                    decodeStateCodeChunk21 code
        else
          if code < 7090143176069857339474645103468544 then
            if code < 6974268062321411095767451822006272 then
              if code < 6961027874967829856746974666940416 then
                if code < 6961027851091903387991631656509440 then
                  decodeStateCodeChunk22 code
                else
                  decodeStateCodeChunk23 code
              else
                if code < 6961048479941443507979260532047872 then
                  decodeStateCodeChunk24 code
                else
                  if code < 6969811634019416591072936967610368 then
                    decodeStateCodeChunk25 code
                  else
                    decodeStateCodeChunk26 code
            else
              if code < 7090119658224230514042576767606784 then
                if code < 6974457136675633179251157372051456 then
                  decodeStateCodeChunk27 code
                else
                  if code < 7090119085313214494626333428080640 then
                    decodeStateCodeChunk28 code
                  else
                    decodeStateCodeChunk29 code
              else
                if code < 7090119682102260824619934359281664 then
                  decodeStateCodeChunk30 code
                else
                  if code < 7090139714052786257974799127601152 then
                    decodeStateCodeChunk31 code
                  else
                    decodeStateCodeChunk32 code
          else
            if code < 7090882929640696364618342372794368 then
              if code < 7090862296478110953022681851027456 then
                if code < 7090861723456557970697392392560640 then
                  decodeStateCodeChunk33 code
                else
                  if code < 7090862296367630850688755221520384 then
                    decodeStateCodeChunk34 code
                  else
                    decodeStateCodeChunk35 code
              else
                if code < 7090862300346904545085895804313600 then
                  decodeStateCodeChunk36 code
                else
                  if code < 7090882352637765831349584773308416 then
                    decodeStateCodeChunk37 code
                  else
                    decodeStateCodeChunk38 code
            else
              if code < 7094575493716509240568332476276736 then
                if code < 7094575489295542594384140747153408 then
                  decodeStateCodeChunk39 code
                else
                  if code < 7094575489739282526908406462013440 then
                    decodeStateCodeChunk40 code
                  else
                    decodeStateCodeChunk41 code
              else
                if code < 7094578354855180591616218295230464 then
                  decodeStateCodeChunk42 code
                else
                  if code < 7094578927878834999141532300075008 then
                    decodeStateCodeChunk43 code
                  else
                    decodeStateCodeChunk44 code
      else
        if code < 7121331107666512484730726169239552 then
          if code < 7095338781050353911416350725169152 then
            if code < 7094699266816194968815960750940160 then
              if code < 7094598983706822184234796416819200 then
                if code < 7094578951756808452190569102368768 then
                  decodeStateCodeChunk45 code
                else
                  decodeStateCodeChunk46 code
              else
                if code < 7094599560709752673629652735549440 then
                  decodeStateCodeChunk47 code
                else
                  if code < 7094699262392669593155338871103488 then
                    decodeStateCodeChunk48 code
                  else
                    decodeStateCodeChunk49 code
            else
              if code < 7094761148941972285107753120817152 then
                if code < 7094702724854447196247003911806976 then
                  decodeStateCodeChunk50 code
                else
                  if code < 7094723329828060847377333645860864 then
                    decodeStateCodeChunk51 code
                  else
                    decodeStateCodeChunk52 code
              else
                if code < 7095318127880578762044701503512576 then
                  decodeStateCodeChunk53 code
                else
                  if code < 7095318128435310545132428906782720 then
                    decodeStateCodeChunk54 code
                  else
                    decodeStateCodeChunk55 code
          else
            if code < 7116874703240498959067096964194304 then
              if code < 7116854073836170179675615907553280 then
                if code < 7095441901532892429019043683491840 then
                  decodeStateCodeChunk56 code
                else
                  if code < 7095462530382489427864068814331904 then
                    decodeStateCodeChunk57 code
                  else
                    decodeStateCodeChunk58 code
              else
                if code < 7116854646859772508881050025336832 then
                  decodeStateCodeChunk59 code
                else
                  if code < 7116857512419917515961872859848704 then
                    decodeStateCodeChunk60 code
                  else
                    decodeStateCodeChunk61 code
            else
              if code < 7116878240754825352101131197145088 then
                if code < 7116875276265122409451331211239424 then
                  decodeStateCodeChunk62 code
                else
                  if code < 7116878145248845052006165645942784 then
                    decodeStateCodeChunk63 code
                  else
                    decodeStateCodeChunk64 code
              else
                if code < 7121310478925403113590236035014656 then
                  decodeStateCodeChunk65 code
                else
                  if code < 7121313916956465606702482323415040 then
                    decodeStateCodeChunk66 code
                  else
                    decodeStateCodeChunk67 code
        else
          if code < 7121458318904156219383335274536960 then
            if code < 7121434255449687616772016788594688 then
              if code < 7121334068288954716911823456100352 then
                if code < 7121333972784512039841935469895680 then
                  decodeStateCodeChunk68 code
                else
                  decodeStateCodeChunk69 code
              else
                if code < 7121334545808621331976668719931392 then
                  decodeStateCodeChunk70 code
                else
                  if code < 7121434251470868806475555297681408 then
                    decodeStateCodeChunk71 code
                  else
                    decodeStateCodeChunk72 code
            else
              if code < 7121454880765203171789261220454400 then
                if code < 7121437690054616099396180937547776 then
                  decodeStateCodeChunk73 code
                else
                  if code < 7121454880762556766412054497976320 then
                    decodeStateCodeChunk74 code
                  else
                    decodeStateCodeChunk75 code
              else
                if code < 7121454884744531356962432761831424 then
                  decodeStateCodeChunk76 code
                else
                  if code < 7121457841494514837276054878879744 then
                    decodeStateCodeChunk77 code
                  else
                    decodeStateCodeChunk78 code
          else
            if code < 7130222141509150836667265829445632 then
              if code < 7121458414407665454118562060255232 then
                if code < 7121458318906802624760541997015040 then
                  decodeStateCodeChunk79 code
                else
                  if code < 7121458322886130809933713538392064 then
                    decodeStateCodeChunk80 code
                  else
                    decodeStateCodeChunk81 code
              else
                if code < 7121458414410735943507997223272448 then
                  decodeStateCodeChunk82 code
                else
                  if code < 7121458418390064129290528504659968 then
                    decodeStateCodeChunk83 code
                  else
                    decodeStateCodeChunk84 code
            else
              if code < 7892172195231208520875980932112384 then
                if code < 7134677973353709894501997532946432 then
                  decodeStateCodeChunk85 code
                else
                  if code < 7134711785728505943661046418776064 then
                    decodeStateCodeChunk86 code
                  else
                    decodeStateCodeChunk87 code
              else
                if code < 7892172199652175173170775084949504 then
                  decodeStateCodeChunk88 code
                else
                  if code < 7892172291176780303681329056768000 then
                    decodeStateCodeChunk89 code
                  else
                    decodeStateCodeChunk90 code
    else
      if code < 7923383740617010558296783898337280 then
        if code < 7896751895787876601276226149933056 then
          if code < 7892914977074191917731629292052480 then
            if code < 7892914833818291935565921745690624 then
              if code < 7892911395677147326376017263648768 then
                if code < 7892192943904405226223743128756224 then
                  decodeStateCodeChunk91 code
                else
                  decodeStateCodeChunk92 code
              else
                if code < 7892911399656022993693940130570240 then
                  decodeStateCodeChunk93 code
                else
                  if code < 7892911968810829317770649483534336 then
                    decodeStateCodeChunk94 code
                  else
                    decodeStateCodeChunk95 code
            else
              if code < 7892914929320633158792115925147648 then
                if code < 7892914834260442144807417362309120 then
                  decodeStateCodeChunk96 code
                else
                  if code < 7892914838239770333044314263183360 then
                    decodeStateCodeChunk97 code
                  else
                    decodeStateCodeChunk98 code
              else
                if code < 7892914929430715234128637026099200 then
                  decodeStateCodeChunk99 code
                else
                  if code < 7892914933301498949336799600631808 then
                    decodeStateCodeChunk100 code
                  else
                    decodeStateCodeChunk101 code
          else
            if code < 7896628122689782969749766649143296 then
              if code < 7896628027187842140271387089100800 then
                if code < 7892915001392323087013239030996992 then
                  decodeStateCodeChunk102 code
                else
                  if code < 7896628026743701813913654723469312 then
                    decodeStateCodeChunk103 code
                  else
                    decodeStateCodeChunk104 code
              else
                if code < 7896628030723032368903781825110016 then
                  decodeStateCodeChunk105 code
                else
                  if code < 7896628051063879960886620700860416 then
                    decodeStateCodeChunk106 code
                  else
                    decodeStateCodeChunk107 code
            else
              if code < 7896628170444308358397664328671232 then
                if code < 7896628122800263068950380541435904 then
                  decodeStateCodeChunk108 code
                else
                  if code < 7896628146565709438929216515661824 then
                    decodeStateCodeChunk109 code
                  else
                    decodeStateCodeChunk110 code
              else
                if code < 7896628600209961314680523850113024 then
                  decodeStateCodeChunk111 code
                else
                  if code < 7896648751541426931559954301509632 then
                    decodeStateCodeChunk112 code
                  else
                    decodeStateCodeChunk113 code
        else
          if code < 7897371238355351511293128768610304 then
            if code < 7896773384174408696360826086227968 then
              if code < 7896752397185061763453098070499328 then
                if code < 7896752372865395358618812497649664 then
                  decodeStateCodeChunk114 code
                else
                  decodeStateCodeChunk115 code
              else
                if code < 7896752472792342307943906472222720 then
                  decodeStateCodeChunk116 code
                else
                  if code < 7896772524639011187177181879271424 then
                    decodeStateCodeChunk117 code
                  else
                    decodeStateCodeChunk118 code
            else
              if code < 7897370669752718241336535185678336 then
                if code < 7897367800211193288525253038170112 then
                  decodeStateCodeChunk119 code
                else
                  if code < 7897370665331239849967726357766144 then
                    decodeStateCodeChunk120 code
                  else
                    decodeStateCodeChunk121 code
              else
                if code < 7897370761277321005720145356185600 then
                  decodeStateCodeChunk122 code
                else
                  if code < 7897370785153304335643981306585088 then
                    decodeStateCodeChunk123 code
                  else
                    decodeStateCodeChunk124 code
          else
            if code < 7897495393576644906630232669151232 then
              if code < 7897494538354233447135886151245824 then
                if code < 7897391390126920356066540158115840 then
                  decodeStateCodeChunk125 code
                else
                  if code < 7897491597184758501845771011350528 then
                    decodeStateCodeChunk126 code
                  else
                    decodeStateCodeChunk127 code
              else
                if code < 7897495011894571859237640797282304 then
                  decodeStateCodeChunk128 code
                else
                  if code < 7897495107066891929213322472316928 then
                    decodeStateCodeChunk129 code
                  else
                    decodeStateCodeChunk130 code
            else
              if code < 7918907279812829308368469236768768 then
                if code < 7897515187100483203242251654135808 then
                  decodeStateCodeChunk131 code
                else
                  if code < 7897556898001724341440759647035392 then
                    decodeStateCodeChunk132 code
                  else
                    decodeStateCodeChunk133 code
              else
                if code < 7918927909104062383782063229034496 then
                  decodeStateCodeChunk134 code
                else
                  if code < 7923363111435802697643651147620352 then
                    decodeStateCodeChunk135 code
                  else
                    decodeStateCodeChunk136 code
      else
        if code < 8057777734679367444221344589144064 then
          if code < 8053321907145747718648869958508544 then
            if code < 7923507513827176385321863932739584 then
              if code < 7923486888844326018624505690054656 then
                if code < 7923486884422906853976567552270336 then
                  decodeStateCodeChunk137 code
                else
                  decodeStateCodeChunk138 code
              else
                if code < 7923487461425834956424688952664064 then
                  decodeStateCodeChunk139 code
                else
                  if code < 7923507513715104189991573977169920 then
                    decodeStateCodeChunk140 code
                  else
                    decodeStateCodeChunk141 code
            else
              if code < 8052602854494549074304642490884096 then
                if code < 7923508086738249221439325480943616 then
                  decodeStateCodeChunk142 code
                else
                  if code < 7923508373252098530031014498926592 then
                    decodeStateCodeChunk143 code
                  else
                    decodeStateCodeChunk144 code
              else
                if code < 8053321330253354210441971219095552 then
                  decodeStateCodeChunk145 code
                else
                  if code < 8053321354460891556239415349665792 then
                    decodeStateCodeChunk146 code
                  else
                    decodeStateCodeChunk147 code
          else
            if code < 8057038534788158315861774184603648 then
              if code < 8053345401555492119865747399303168 then
                if code < 8053324772705895141841453755457536 then
                  decodeStateCodeChunk148 code
                else
                  if code < 8053342532458161987844387016073216 then
                    decodeStateCodeChunk149 code
                  else
                    decodeStateCodeChunk150 code
              else
                if code < 8053352273859815464518980847329280 then
                  decodeStateCodeChunk151 code
                else
                  if code < 8057037961654021446564441339518976 then
                    decodeStateCodeChunk152 code
                  else
                    decodeStateCodeChunk153 code
            else
              if code < 8057162307775205612126430513192960 then
                if code < 8057058594482892133610509326409728 then
                  decodeStateCodeChunk154 code
                else
                  if code < 8057058709883535088409382009495552 then
                    decodeStateCodeChunk155 code
                  else
                    decodeStateCodeChunk156 code
              else
                if code < 8057182936624802611479725612359680 then
                  decodeStateCodeChunk157 code
                else
                  if code < 8057183032129245288040407613833216 then
                    decodeStateCodeChunk158 code
                  else
                    decodeStateCodeChunk159 code
        else
          if code < 8083917448293358072992782144176128 then
            if code < 8057901508329631761266862669815808 then
              if code < 8057781173373649371178631250370560 then
                if code < 8057777758997496244311344797310976 then
                  decodeStateCodeChunk160 code
                else
                  decodeStateCodeChunk161 code
              else
                if code < 8057801229199646436108859918049280 then
                  decodeStateCodeChunk162 code
                else
                  if code < 8057808678396420152591850664943616 then
                    decodeStateCodeChunk163 code
                  else
                    decodeStateCodeChunk164 code
            else
              if code < 8057925599086274627037465788866560 then
                if code < 8057922137068694170559819990851584 then
                  decodeStateCodeChunk165 code
                else
                  if code < 8057925121566608011871064921931776 then
                    decodeStateCodeChunk166 code
                  else
                    decodeStateCodeChunk167 code
              else
                if code < 8057963394325737908225105006813184 then
                  decodeStateCodeChunk168 code
                else
                  if code < 8079337847551564746503643664539648 then
                    decodeStateCodeChunk169 code
                  else
                    decodeStateCodeChunk170 code
          else
            if code < 8404716712139353220017731474235392 then
              if code < 8137460534599663765866537750466560 then
                if code < 8083918025185751565965687383326720 then
                  decodeStateCodeChunk171 code
                else
                  if code < 8133560822600402559569694251016192 then
                    decodeStateCodeChunk172 code
                  else
                    decodeStateCodeChunk173 code
              else
                if code < 8163998642428781730481830240903168 then
                  decodeStateCodeChunk174 code
                else
                  if code < 8400157712502436813880811945074688 then
                    decodeStateCodeChunk175 code
                  else
                    decodeStateCodeChunk176 code
            else
              if code < 12705209433637663416801709884235776 then
                if code < 8413504626054187185806970692444160 then
                  decodeStateCodeChunk177 code
                else
                  if code < 8645352242691222118842907342159872 then
                    decodeStateCodeChunk178 code
                  else
                    decodeStateCodeChunk179 code
              else
                if code < 12705210026557973012271702091161600 then
                  decodeStateCodeChunk180 code
                else
                  if code < 12731201780162810895832852014686208 then
                    decodeStateCodeChunk181 code
                  else
                    decodeStateCodeChunk182 code
  else
    if code < 13667672593976597860838734972772352 then
      if code < 12891756785214194288139605761327104 then
        if code < 12736524691886424521312981330288640 then
          if code < 12732068860373476609971140597833728 then
            if code < 12731346277614434827872818614222848 then
              if code < 12731222504516852941446312440045568 then
                if code < 12731202377062394185687211445657600 then
                  decodeStateCodeChunk183 code
                else
                  decodeStateCodeChunk184 code
              else
                if code < 12731225966976071862387546767548416 then
                  decodeStateCodeChunk185 code
                else
                  if code < 12731326221788437806815520382377984 then
                    decodeStateCodeChunk186 code
                  else
                    decodeStateCodeChunk187 code
            else
              if code < 12731944514252235533763092557258752 then
                if code < 12731349715755522579533853757734912 then
                  decodeStateCodeChunk188 code
                else
                  if code < 12731349739631505909372664590090240 then
                    decodeStateCodeChunk189 code
                  else
                    decodeStateCodeChunk190 code
              else
                if code < 12731944991882439134270129140850688 then
                  decodeStateCodeChunk191 code
                else
                  if code < 12732068764869484060847600964919296 then
                    decodeStateCodeChunk192 code
                  else
                    decodeStateCodeChunk193 code
          else
            if code < 12735782077176914426747158083526656 then
              if code < 12732336462394578174115179282112512 then
                if code < 12732088916199926146446326908256256 then
                  decodeStateCodeChunk194 code
                else
                  if code < 12732089493202401776810689148534784 then
                    decodeStateCodeChunk195 code
                  else
                    decodeStateCodeChunk196 code
              else
                if code < 12732460812495090575528788849655808 then
                  decodeStateCodeChunk197 code
                else
                  if code < 12735781981672981107288787514155008 then
                    decodeStateCodeChunk198 code
                  else
                    decodeStateCodeChunk199 code
            else
              if code < 12735805547821155553433708928221184 then
                if code < 12735785491553067510145842712535040 then
                  decodeStateCodeChunk200 code
                else
                  if code < 12735802682261093468534106505347072 then
                    decodeStateCodeChunk201 code
                  else
                    decodeStateCodeChunk202 code
              else
                if code < 12735806120292639276541137587060736 then
                  decodeStateCodeChunk203 code
                else
                  if code < 12735806124271486516635147704598528 then
                    decodeStateCodeChunk204 code
                  else
                    decodeStateCodeChunk205 code
        else
          if code < 12870220170720834687957898004766720 then
            if code < 12865639992976622854399038254014464 then
              if code < 12865619364127025873342051459653632 then
                if code < 12738752607643407853506807742144512 then
                  decodeStateCodeChunk206 code
                else
                  decodeStateCodeChunk207 code
              else
                if code < 12865619937148635713179675418025984 then
                  decodeStateCodeChunk208 code
                else
                  if code < 12865619937260707908594598670819328 then
                    decodeStateCodeChunk209 code
                  else
                    decodeStateCodeChunk210 code
            else
              if code < 12865743710247755204350514846097408 then
                if code < 12865640565999767929819429885304832 then
                  decodeStateCodeChunk211 code
                else
                  if code < 12865640566662992076453091320127488 then
                    decodeStateCodeChunk212 code
                  else
                    decodeStateCodeChunk213 code
              else
                if code < 12865764339207886776092271199494144 then
                  decodeStateCodeChunk214 code
                else
                  if code < 12870199541758656134968306189590528 then
                    decodeStateCodeChunk215 code
                  else
                    decodeStateCodeChunk216 code
          else
            if code < 12891632916944289961938251017101312 then
              if code < 12891632343478544531672296684314624 then
                if code < 12870220194928428896868520171511808 then
                  decodeStateCodeChunk217 code
                else
                  if code < 12891611718608275736383735621804032 then
                    decodeStateCodeChunk218 code
                  else
                    decodeStateCodeChunk219 code
              else
                if code < 12891632347902067537634449620000768 then
                  decodeStateCodeChunk220 code
                else
                  if code < 12891632439427182065483469089611776 then
                    decodeStateCodeChunk221 code
                  else
                    decodeStateCodeChunk222 code
            else
              if code < 12891756212524254557635313489657856 then
                if code < 12891632940822320290796008988270592 then
                  decodeStateCodeChunk223 code
                else
                  if code < 12891635901445276637352705991385088 then
                    decodeStateCodeChunk224 code
                  else
                    decodeStateCodeChunk225 code
              else
                if code < 12891756689599726378113641826066432 then
                  decodeStateCodeChunk226 code
                else
                  if code < 12891756690155479297616043598798848 then
                    decodeStateCodeChunk227 code
                  else
                    decodeStateCodeChunk228 code
      else
        if code < 12896212521667403981843107165347840 then
          if code < 12892499328187830913980110208147456 then
            if code < 12892375077567969169588431677349888 then
              if code < 12891759654643135259524871889862656 then
                if code < 12891756789527182703432609728020480 then
                  decodeStateCodeChunk229 code
                else
                  decodeStateCodeChunk230 code
              else
                if code < 12892354926238548205168222881570816 then
                  decodeStateCodeChunk231 code
                else
                  if code < 12892374982174570440901318582788096 then
                    decodeStateCodeChunk232 code
                  else
                    decodeStateCodeChunk233 code
            else
              if code < 12892478699336130091608960858660864 then
                if code < 12892375081991492175550584613036032 then
                  decodeStateCodeChunk234 code
                else
                  if code < 12892375555532340006419877249736704 then
                    decodeStateCodeChunk235 code
                  else
                    decodeStateCodeChunk236 code
              else
                if code < 12892498850778132627422868672331776 then
                  decodeStateCodeChunk237 code
                else
                  if code < 12892499328185217696672025836429312 then
                    decodeStateCodeChunk238 code
                  else
                    decodeStateCodeChunk239 code
          else
            if code < 12892725672507182159264019120463872 then
              if code < 12892499423689717252598770235916288 then
                if code < 12892499328740003986379137438556160 then
                  decodeStateCodeChunk240 code
                else
                  if code < 12892499352063245638059654637264896 then
                    decodeStateCodeChunk241 code
                  else
                    decodeStateCodeChunk242 code
              else
                if code < 12892499423801789448015574228647936 then
                  decodeStateCodeChunk243 code
                else
                  if code < 12892499427670526182564572942090240 then
                    decodeStateCodeChunk244 code
                  else
                    decodeStateCodeChunk245 code
            else
              if code < 12896191892263643808210866390556672 then
                if code < 12892746421402988038081349412003840 then
                  decodeStateCodeChunk246 code
                else
                  if code < 12892870652123583790299881730072576 then
                    decodeStateCodeChunk247 code
                  else
                    decodeStateCodeChunk248 code
              else
                if code < 12896212521113240789789784639184896 then
                  decodeStateCodeChunk249 code
                else
                  if code < 12896212521556867007358106726146048 then
                    decodeStateCodeChunk250 code
                  else
                    decodeStateCodeChunk251 code
        else
          if code < 12896955160142926683567525744549888 then
            if code < 12896212640492588832819355658747904 then
              if code < 12896212616617174109146599605452800 then
                if code < 12896212544988655513462540692480000 then
                  decodeStateCodeChunk252 code
                else
                  decodeStateCodeChunk253 code
              else
                if code < 12896212617060800326714921692413952 then
                  decodeStateCodeChunk254 code
                else
                  if code < 12896212617171337301199922131615744 then
                    decodeStateCodeChunk255 code
                  else
                    decodeStateCodeChunk256 code
            else
              if code < 12896216055203425653870974680104960 then
                if code < 12896215482179311623354589651795968 then
                  decodeStateCodeChunk257 code
                else
                  if code < 12896216055200438090319388553773056 then
                    decodeStateCodeChunk258 code
                  else
                    decodeStateCodeChunk259 code
              else
                if code < 12896216059182753839653505961492480 then
                  decodeStateCodeChunk260 code
                else
                  if code < 12896955159698220099413362817015808 then
                    decodeStateCodeChunk261 code
                  else
                    decodeStateCodeChunk262 code
          else
            if code < 13667669040434469130275331833520128 then
              if code < 12899183076120474558980337792983040 then
                if code < 12896955255204200400016132505124864 then
                  decodeStateCodeChunk263 code
                else
                  if code < 12896955259181483973743378225479680 then
                    decodeStateCodeChunk264 code
                  else
                    decodeStateCodeChunk265 code
              else
                if code < 12899554490251404228593920885456896 then
                  decodeStateCodeChunk266 code
                else
                  if code < 13667669036457185556027121150255104 then
                    decodeStateCodeChunk267 code
                  else
                    decodeStateCodeChunk268 code
            else
              if code < 13667669155837102205237239965671424 then
                if code < 13667669131959526779254255699681280 then
                  decodeStateCodeChunk269 code
                else
                  if code < 13667669132071655835244298441908224 then
                    decodeStateCodeChunk270 code
                  else
                    decodeStateCodeChunk271 code
              else
                if code < 13667672570100616900105568183181312 then
                  decodeStateCodeChunk272 code
                else
                  if code < 13667672570211151490775265701322752 then
                    decodeStateCodeChunk273 code
                  else
                    decodeStateCodeChunk274 code
    else
      if code < 13699008365674367439049112675205120 then
        if code < 13694407559301120843338932654301184 then
          if code < 13672249237965251619152152473231360 then
            if code < 13667793382578367358607704069431296 then
              if code < 13667689784686699186308332309569536 then
                if code < 13667674289174029865934982430318592 then
                  decodeStateCodeChunk275 code
                else
                  decodeStateCodeChunk276 code
              else
                if code < 13667693199394974938010844911820800 then
                  decodeStateCodeChunk277 code
                else
                  if code < 13667792905056653781085496067416064 then
                    decodeStateCodeChunk278 code
                  else
                    decodeStateCodeChunk279 code
            else
              if code < 13667813534018834702744796434055168 then
                if code < 13667793478190790657075441982955520 then
                  decodeStateCodeChunk280 code
                else
                  if code < 13667796347177583832906699676835840 then
                    decodeStateCodeChunk281 code
                  else
                    decodeStateCodeChunk282 code
              else
                if code < 13667816972050408984910389067169792 then
                  decodeStateCodeChunk283 code
                else
                  if code < 13667818691120696988248120577933312 then
                    decodeStateCodeChunk284 code
                  else
                    decodeStateCodeChunk285 code
          else
            if code < 13674477225351722545506233888464896 then
              if code < 13672269938445357316069816751407104 then
                if code < 13672252174711203558547821315219456 then
                  decodeStateCodeChunk286 code
                else
                  if code < 13672252747736850455850006416056320 then
                    decodeStateCodeChunk287 code
                  else
                    decodeStateCodeChunk288 code
              else
                if code < 13672272804115529950469203676479488 then
                  decodeStateCodeChunk289 code
                else
                  if code < 13672273380565775622703660516294656 then
                    decodeStateCodeChunk290 code
                  else
                    decodeStateCodeChunk291 code
            else
              if code < 13693788693813211411206162337357824 then
                if code < 13693664920605604310103780329644032 then
                  decodeStateCodeChunk292 code
                else
                  if code < 13693685549897349130701913056534528 then
                    decodeStateCodeChunk293 code
                  else
                    decodeStateCodeChunk294 code
              else
                if code < 13693809322996466252682113798750208 then
                  decodeStateCodeChunk295 code
                else
                  if code < 13694404121048986755838158628380672 then
                    decodeStateCodeChunk296 code
                  else
                    decodeStateCodeChunk297 code
        else
          if code < 13694551965117093305966369959231488 then
            if code < 13694531356164149099744322691915776 then
              if code < 13694428188150717824498419775299584 then
                if code < 13694424749900630717634240731209728 then
                  decodeStateCodeChunk298 code
                else
                  decodeStateCodeChunk299 code
              else
                if code < 13694429907113539338994622237761536 then
                  decodeStateCodeChunk300 code
                else
                  if code < 13694528467170225418981636227391488 then
                    decodeStateCodeChunk301 code
                  else
                    decodeStateCodeChunk302 code
            else
              if code < 13694549096020331776032523070521344 then
                if code < 13694548522998210234870156108742656 then
                  decodeStateCodeChunk303 code
                else
                  if code < 13694548526975493809118366792007680 then
                    decodeStateCodeChunk304 code
                  else
                    decodeStateCodeChunk305 code
              else
                if code < 13694551961137821980742971877801984 then
                  decodeStateCodeChunk306 code
                else
                  if code < 13694551961248356571412669395943424 then
                    decodeStateCodeChunk307 code
                  else
                    decodeStateCodeChunk308 code
          else
            if code < 13698265177941259797516168253587456 then
              if code < 13698245102218609958160000045539328 then
                if code < 13694553680208564868688241893818368 then
                  decodeStateCodeChunk309 code
                else
                  if code < 13698244525215679486521209484337152 then
                    decodeStateCodeChunk310 code
                  else
                    decodeStateCodeChunk311 code
              else
                if code < 13698265154507369815733981987586048 then
                  decodeStateCodeChunk312 code
                else
                  if code < 13698265154509983033042066359304192 then
                    decodeStateCodeChunk313 code
                  else
                    decodeStateCodeChunk314 code
            else
              if code < 13698987736824770457977989856354304 then
                if code < 13698265727533073573103486794514432 then
                  decodeStateCodeChunk315 code
                else
                  if code < 13698266014044871162575682552381440 then
                    decodeStateCodeChunk316 code
                  else
                    decodeStateCodeChunk317 code
              else
                if code < 13699004927643304902574918190088192 then
                  decodeStateCodeChunk318 code
                else
                  if code < 13699007793094962346829602760540160 then
                    decodeStateCodeChunk319 code
                  else
                    decodeStateCodeChunk320 code
      else
        if code < 13854958458128125426901918678040576 then
          if code < 13828223473016974884142899722108928 then
            if code < 13828099600215510088243017437208576 then
              if code < 13701232843289244267594478252572672 then
                if code < 13699008370097892814726661214486528 then
                  decodeStateCodeChunk321 code
                else
                  decodeStateCodeChunk322 code
              else
                if code < 13828078971033790464128315231428608 then
                  decodeStateCodeChunk323 code
                else
                  if code < 13828079547926240835969356969926656 then
                    decodeStateCodeChunk324 code
                  else
                    decodeStateCodeChunk325 code
            else
              if code < 13828099719816045772565390735302656 then
                if code < 13828099624091038533473741215162368 then
                  decodeStateCodeChunk326 code
                else
                  if code < 13828099695719500268175887909314560 then
                    decodeStateCodeChunk327 code
                  else
                    decodeStateCodeChunk328 code
              else
                if code < 13828103133860531140979679172288512 then
                  decodeStateCodeChunk329 code
                else
                  if code < 13828203317155029127268031350562816 then
                    decodeStateCodeChunk330 code
                  else
                    decodeStateCodeChunk331 code
          else
            if code < 13832679873463655197283380318519296 then
              if code < 13828226906958172257172992730841088 then
                if code < 13828223946557313295127490491228160 then
                  decodeStateCodeChunk332 code
                else
                  if code < 13828224041508559427696905152086016 then
                    decodeStateCodeChunk333 code
                  else
                    decodeStateCodeChunk334 code
              else
                if code < 13832679777517574020205716991090688 then
                  decodeStateCodeChunk335 code
                else
                  if code < 13832679801725168229116339157835776 then
                    decodeStateCodeChunk336 code
                  else
                    decodeStateCodeChunk337 code
            else
              if code < 13854219257462591061411546653245440 then
                if code < 13832683311494717719135291968307200 then
                  decodeStateCodeChunk338 code
                else
                  if code < 13834887068293244589936689869676544 then
                    decodeStateCodeChunk339 code
                  else
                    decodeStateCodeChunk340 code
              else
                if code < 13854834685030486679899274280296448 then
                  decodeStateCodeChunk341 code
                else
                  if code < 13854958457464391907930546109464576 then
                    decodeStateCodeChunk342 code
                  else
                    decodeStateCodeChunk343 code
        else
          if code < 14174894724003469360638074698997760 then
            if code < 13859414862443087571198558793875456 then
              if code < 13854959054806123007962607365373952 then
                if code < 13854959030488503565584744160739328 then
                  decodeStateCodeChunk344 code
                else
                  decodeStateCodeChunk345 code
              else
                if code < 13858675088975541623482361980895232 then
                  decodeStateCodeChunk346 code
                else
                  if code < 13858675661999198400707555484844032 then
                    decodeStateCodeChunk347 code
                  else
                    decodeStateCodeChunk348 code
            else
              if code < 13908308124969633754167400258265088 then
                if code < 13859414886319070919318553647366144 then
                  decodeStateCodeChunk349 code
                else
                  if code < 13859418300695224028410966943514624 then
                    decodeStateCodeChunk350 code
                  else
                    decodeStateCodeChunk351 code
              else
                if code < 13934300451598583342942037787090944 then
                  decodeStateCodeChunk352 code
                else
                  if code < 13935168606449001800739962196246528 then
                    decodeStateCodeChunk353 code
                  else
                    decodeStateCodeChunk354 code
          else
            if code < 15752998761519748065421527414595584 then
              if code < 14182839409704590078512893882445824 then
                if code < 14175039126392796067577218297036800 then
                  decodeStateCodeChunk355 code
                else
                  if code < 14179474352489980382311575851311104 then
                    decodeStateCodeChunk356 code
                  else
                    decodeStateCodeChunk357 code
              else
                if code < 15592588254027909978514864494796800 then
                  decodeStateCodeChunk358 code
                else
                  if code < 15639932036895090009584272723943424 then
                    decodeStateCodeChunk359 code
                  else
                    decodeStateCodeChunk360 code
            else
              if code < 16555053157313627500814623635136512 then
                if code < 15793471987442413397246312212930560 then
                  decodeStateCodeChunk361 code
                else
                  if code < 16555047856847887002349695006007296 then
                    decodeStateCodeChunk362 code
                  else
                    decodeStateCodeChunk363 code
              else
                if code < 16561923423765390677967127674937344 then
                  decodeStateCodeChunk364 code
                else
                  if code < 16715488759127157505444115725541376 then
                    decodeStateCodeChunk365 code
                  else
                    decodeStateCodeChunk366 code

def decodeState
    (vector : Fin 44 -> Fin 6) : Fin 11742 :=
  decodeStateCode (stateVectorCode vector)

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.Shards
