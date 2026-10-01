import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14155.Shards.DecodeStatePart00
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14155.Shards.DecodeStatePart01
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14155.Shards.DecodeStatePart02
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14155.Shards.DecodeStatePart03
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14155.Shards.DecodeStatePart04
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14155.Shards.DecodeStatePart05
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14155.Shards.DecodeStatePart06
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14155.Shards.DecodeStatePart07
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14155.Shards.DecodeStatePart08
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14155.Shards.DecodeStatePart09
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14155.Shards.DecodeStatePart10
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14155.Shards.DecodeStatePart11

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14155.Shards

def stateVectorCode
    (vector : Fin 33 -> Fin 6) : Nat :=
  (vector (0 : Fin 33)).val + 6 * ((vector (1 : Fin 33)).val + 6 * ((vector (2 : Fin 33)).val + 6 * ((vector (3 : Fin 33)).val + 6 * ((vector (4 : Fin 33)).val + 6 * ((vector (5 : Fin 33)).val + 6 * ((vector (6 : Fin 33)).val + 6 * ((vector (7 : Fin 33)).val + 6 * ((vector (8 : Fin 33)).val + 6 * ((vector (9 : Fin 33)).val + 6 * ((vector (10 : Fin 33)).val + 6 * ((vector (11 : Fin 33)).val + 6 * ((vector (12 : Fin 33)).val + 6 * ((vector (13 : Fin 33)).val + 6 * ((vector (14 : Fin 33)).val + 6 * ((vector (15 : Fin 33)).val + 6 * ((vector (16 : Fin 33)).val + 6 * ((vector (17 : Fin 33)).val + 6 * ((vector (18 : Fin 33)).val + 6 * ((vector (19 : Fin 33)).val + 6 * ((vector (20 : Fin 33)).val + 6 * ((vector (21 : Fin 33)).val + 6 * ((vector (22 : Fin 33)).val + 6 * ((vector (23 : Fin 33)).val + 6 * ((vector (24 : Fin 33)).val + 6 * ((vector (25 : Fin 33)).val + 6 * ((vector (26 : Fin 33)).val + 6 * ((vector (27 : Fin 33)).val + 6 * ((vector (28 : Fin 33)).val + 6 * ((vector (29 : Fin 33)).val + 6 * ((vector (30 : Fin 33)).val + 6 * ((vector (31 : Fin 33)).val + 6 * ((vector (32 : Fin 33)).val))))))))))))))))))))))))))))))))

def decodeStateCode (code : Nat) : Fin 11742 :=
  if code < 19164252598637547832351488 then
    if code < 17132629727252808381943296 then
      if code < 4608106252998052639996800 then
        if code < 3834347456884425819852672 then
          if code < 3281662657581240864981888 then
            if code < 3195817471503950043643776 then
              if code < 3171253765943333634157440 then
                if code < 3171239419177928283696000 then
                  decodeStateCodeChunk0 code
                else
                  decodeStateCodeChunk1 code
              else
                if code < 3174210450087594536336256 then
                  decodeStateCodeChunk2 code
                else
                  if code < 3195803264882821384475520 then
                    decodeStateCodeChunk3 code
                  else
                    decodeStateCodeChunk4 code
            else
              if code < 3198887942611182484984704 then
                if code < 3195988053223666332440448 then
                  decodeStateCodeChunk5 code
                else
                  if code < 3198774350330184226967424 then
                    decodeStateCodeChunk6 code
                  else
                    decodeStateCodeChunk7 code
              else
                if code < 3198944737063305996649344 then
                  decodeStateCodeChunk8 code
                else
                  if code < 3199058587399683946400640 then
                    decodeStateCodeChunk9 code
                  else
                    decodeStateCodeChunk10 code
          else
            if code < 3281837977690752597257088 then
              if code < 3281776379037982009874304 then
                if code < 3281662734673659022945152 then
                  decodeStateCodeChunk11 code
                else
                  decodeStateCodeChunk12 code
              else
                if code < 3281776381483890829985664 then
                  decodeStateCodeChunk13 code
                else
                  if code < 3281776392452679244033920 then
                    decodeStateCodeChunk14 code
                  else
                    decodeStateCodeChunk15 code
            else
              if code < 3306354365181084864333696 then
                if code < 3281951701584938910052224 then
                  decodeStateCodeChunk16 code
                else
                  if code < 3284917925560615532702592 then
                    decodeStateCodeChunk17 code
                  else
                    decodeStateCodeChunk18 code
              else
                if code < 3309311180947049427381120 then
                  decodeStateCodeChunk19 code
                else
                  if code < 3395455872583756554158976 then
                    decodeStateCodeChunk20 code
                  else
                    decodeStateCodeChunk21 code
        else
          if code < 3944884416744851675033472 then
            if code < 3861981905318568707925888 then
              if code < 3837418136393002767847296 then
                if code < 3834461386742569955627904 then
                  decodeStateCodeChunk22 code
                else
                  decodeStateCodeChunk23 code
              else
                if code < 3837432219913596409167744 then
                  decodeStateCodeChunk24 code
                else
                  if code < 3859025024046432013128576 then
                    decodeStateCodeChunk25 code
                  else
                    decodeStateCodeChunk26 code
            else
              if code < 3861996778577848873659264 then
                if code < 3861995977879150499867520 then
                  decodeStateCodeChunk27 code
                else
                  if code < 3861996043681584662620032 then
                    decodeStateCodeChunk28 code
                  else
                    decodeStateCodeChunk29 code
              else
                if code < 3862095497599573234270080 then
                  decodeStateCodeChunk30 code
                else
                  if code < 3862109830644817516439424 then
                    decodeStateCodeChunk31 code
                  else
                    decodeStateCodeChunk32 code
          else
            if code < 3947955680028157001974656 then
              if code < 3944998151303140001524608 then
                if code < 3944884427721737679060864 then
                  decodeStateCodeChunk33 code
                else
                  if code < 3944884430463856690506624 then
                    decodeStateCodeChunk34 code
                  else
                    decodeStateCodeChunk35 code
              else
                if code < 3945908699281591339326336 then
                  decodeStateCodeChunk36 code
                else
                  if code < 3947954898820820254054272 then
                    decodeStateCodeChunk37 code
                  else
                    decodeStateCodeChunk38 code
            else
              if code < 3972533664028620673860480 then
                if code < 3947969892724859081796480 then
                  decodeStateCodeChunk39 code
                else
                  if code < 3972518670124581805807488 then
                    decodeStateCodeChunk40 code
                  else
                    decodeStateCodeChunk41 code
              else
                if code < 4497683014290118961828736 then
                  decodeStateCodeChunk42 code
                else
                  if code < 4525217748314499233414016 then
                    decodeStateCodeChunk43 code
                  else
                    decodeStateCodeChunk44 code
      else
        if code < 16469407191562937776986624 then
          if code < 11820658009169323912411008 then
            if code < 5272352250621701907252096 then
              if code < 4832436225350444699513088 then
                if code < 4608395245510911427303296 then
                  decodeStateCodeChunk45 code
                else
                  decodeStateCodeChunk46 code
              else
                if code < 5188426081861517843087232 then
                  decodeStateCodeChunk47 code
                else
                  if code < 5197750514482679187958656 then
                    decodeStateCodeChunk48 code
                  else
                    decodeStateCodeChunk49 code
            else
              if code < 11240437491117507542647680 then
                if code < 11154464300487334027897728 then
                  decodeStateCodeChunk50 code
                else
                  if code < 11157549052244753444906880 then
                    decodeStateCodeChunk51 code
                  else
                    decodeStateCodeChunk52 code
              else
                if code < 11265001337067791351859072 then
                  decodeStateCodeChunk53 code
                else
                  if code < 11378680751455723378629504 then
                    decodeStateCodeChunk54 code
                  else
                    decodeStateCodeChunk55 code
          else
            if code < 16447914025371950347049472 then
              if code < 11931307705397231680111488 then
                if code < 11820770940591218400831360 then
                  decodeStateCodeChunk56 code
                else
                  if code < 11928223030115870007974784 then
                    decodeStateCodeChunk57 code
                  else
                    decodeStateCodeChunk58 code
              else
                if code < 12594529541643438824827776 then
                  decodeStateCodeChunk59 code
                else
                  if code < 13257624154038017910090624 then
                    decodeStateCodeChunk60 code
                  else
                    decodeStateCodeChunk61 code
            else
              if code < 16466407693792294569940224 then
                if code < 16447999184614336298925312 then
                  decodeStateCodeChunk62 code
                else
                  if code < 16450984349826605325605376 then
                    decodeStateCodeChunk63 code
                  else
                    decodeStateCodeChunk64 code
              else
                if code < 16466421996684112096302336 then
                  decodeStateCodeChunk65 code
                else
                  if code < 16466592492086145838039296 then
                    decodeStateCodeChunk66 code
                  else
                    decodeStateCodeChunk67 code
        else
          if code < 16561521310104502982604288 then
            if code < 16558436550730087171542528 then
              if code < 16469492614037446968728064 then
                if code < 16469492469224475043745280 then
                  decodeStateCodeChunk68 code
                else
                  decodeStateCodeChunk69 code
              else
                if code < 16469663051347368386158080 then
                  decodeStateCodeChunk70 code
                else
                  if code < 16558436535687929144987136 then
                    decodeStateCodeChunk71 code
                  else
                    decodeStateCodeChunk72 code
            else
              if code < 16558521843422484425376000 then
                if code < 16558521826958251731571968 then
                  decodeStateCodeChunk73 code
                else
                  if code < 16558521828797615572631808 then
                    decodeStateCodeChunk74 code
                  else
                    decodeStateCodeChunk75 code
              else
                if code < 16558536144485987598903552 then
                  decodeStateCodeChunk76 code
                else
                  if code < 16558697147067770175592704 then
                    decodeStateCodeChunk77 code
                  else
                    decodeStateCodeChunk78 code
          else
            if code < 17114191937720389645742592 then
              if code < 16672229553257997748637184 then
                if code < 16576944757813687963726080 then
                  decodeStateCodeChunk79 code
                else
                  if code < 16577129540061007123693824 then
                    decodeStateCodeChunk80 code
                  else
                    decodeStateCodeChunk81 code
              else
                if code < 16782766602705478365672960 then
                  decodeStateCodeChunk82 code
                else
                  if code < 17111206728645451494849792 then
                    decodeStateCodeChunk83 code
                  else
                    decodeStateCodeChunk84 code
            else
              if code < 17132614737004614497296896 then
                if code < 17114206108988805399304704 then
                  decodeStateCodeChunk85 code
                else
                  if code < 17129629454377796834727168 then
                    decodeStateCodeChunk86 code
                  else
                    decodeStateCodeChunk87 code
              else
                if code < 17132628935682986394788352 then
                  decodeStateCodeChunk88 code
                else
                  if code < 17132628952147219048281600 then
                    decodeStateCodeChunk89 code
                  else
                    decodeStateCodeChunk90 code
    else
      if code < 18767184086300416704824832 then
        if code < 18656661416941308827437056 then
          if code < 17240166516977298592379136 then
            if code < 17221658311315771963559424 then
              if code < 17132714243417548482660864 then
                if code < 17132700027857419846771200 then
                  decodeStateCodeChunk91 code
                else
                  decodeStateCodeChunk92 code
              else
                if code < 17221658294851539773640192 then
                  decodeStateCodeChunk93 code
                else
                  if code < 17221658309476401954949632 then
                    decodeStateCodeChunk94 code
                  else
                    decodeStateCodeChunk95 code
            else
              if code < 17224728767798135478253056 then
                if code < 17221743600746731212969216 then
                  decodeStateCodeChunk96 code
                else
                  if code < 17222682574950840296492544 then
                    decodeStateCodeChunk97 code
                  else
                    decodeStateCodeChunk98 code
              else
                if code < 17224729555700279311824384 then
                  decodeStateCodeChunk99 code
                else
                  if code < 17224743070688542449661440 then
                    decodeStateCodeChunk100 code
                  else
                    decodeStateCodeChunk101 code
          else
            if code < 18017096117646021967056384 then
              if code < 17792865661254849805909248 then
                if code < 17243165911956805789208064 then
                  decodeStateCodeChunk102 code
                else
                  if code < 17774343328552335529597440 then
                    decodeStateCodeChunk103 code
                  else
                    decodeStateCodeChunk104 code
              else
                if code < 17884880069054480607195648 then
                  decodeStateCodeChunk105 code
                else
                  if code < 17885055376367450678545920 then
                    decodeStateCodeChunk106 code
                  else
                    decodeStateCodeChunk107 code
            else
              if code < 18549126107911158462374400 then
                if code < 18456073205274445469711616 then
                  decodeStateCodeChunk108 code
                else
                  if code < 18459157761741948630059520 then
                    decodeStateCodeChunk109 code
                  else
                    decodeStateCodeChunk110 code
              else
                if code < 18569610220011428949898752 then
                  decodeStateCodeChunk111 code
                else
                  if code < 18656647124603315737876992 then
                    decodeStateCodeChunk112 code
                  else
                    decodeStateCodeChunk113 code
        else
          if code < 18679064472576495138783744 then
            if code < 18661377667340857001025024 then
              if code < 18658373548510451517587712 then
                if code < 18658288308519175500951552 then
                  decodeStateCodeChunk114 code
                else
                  decodeStateCodeChunk115 code
              else
                if code < 18658477778274947613076992 then
                  decodeStateCodeChunk116 code
                else
                  if code < 18660641711693172423459840 then
                    decodeStateCodeChunk117 code
                  else
                    decodeStateCodeChunk118 code
            else
              if code < 18675254749997764107191808 then
                if code < 18675069951703912839092736 then
                  decodeStateCodeChunk119 code
                else
                  if code < 18675084232658779725076992 then
                    decodeStateCodeChunk120 code
                  else
                    decodeStateCodeChunk121 code
              else
                if code < 18676815248285716791350016 then
                  decodeStateCodeChunk122 code
                else
                  if code < 18676815330558058721010432 then
                    decodeStateCodeChunk123 code
                  else
                    decodeStateCodeChunk124 code
          else
            if code < 18679885799828748301868544 then
              if code < 18679235185926378408093696 then
                if code < 18679178193728849768683008 then
                  decodeStateCodeChunk125 code
                else
                  if code < 18679178206940107435066368 then
                    decodeStateCodeChunk126 code
                  else
                    decodeStateCodeChunk127 code
              else
                if code < 18679348907484737983805952 then
                  decodeStateCodeChunk128 code
                else
                  if code < 18679885719088635023486976 then
                    decodeStateCodeChunk129 code
                  else
                    decodeStateCodeChunk130 code
            else
              if code < 18695304543838771931936256 then
                if code < 18679971076067891115929088 then
                  decodeStateCodeChunk131 code
                else
                  if code < 18693379188765876664065024 then
                    decodeStateCodeChunk132 code
                  else
                    decodeStateCodeChunk133 code
              else
                if code < 18767070365554301683249152 then
                  decodeStateCodeChunk134 code
                else
                  if code < 18767084655649564669390848 then
                    decodeStateCodeChunk135 code
                  else
                    decodeStateCodeChunk136 code
      else
        if code < 19027109385035437795083648 then
          if code < 18769099965016631415300864 then
            if code < 18768825138594335386590720 then
              if code < 18767198301444196577183232 then
                if code < 18767184097666659633437184 then
                  decodeStateCodeChunk137 code
                else
                  decodeStateCodeChunk138 code
              else
                if code < 18767255160183757415760384 then
                  decodeStateCodeChunk139 code
                else
                  if code < 18767368883570143945213440 then
                    decodeStateCodeChunk140 code
                  else
                    decodeStateCodeChunk141 code
            else
              if code < 18768910442559653181544704 then
                if code < 18768844156407134713818624 then
                  decodeStateCodeChunk142 code
                else
                  if code < 18768910429450327580676864 then
                    decodeStateCodeChunk143 code
                  else
                    decodeStateCodeChunk144 code
              else
                if code < 18768929381451909287338752 then
                  decodeStateCodeChunk145 code
                else
                  if code < 18769014672019789031235072 then
                    decodeStateCodeChunk146 code
                  else
                    decodeStateCodeChunk147 code
          else
            if code < 18789885737509172189736960 then
              if code < 18785621205273384446800896 then
                if code < 18771349913226789330235392 then
                  decodeStateCodeChunk148 code
                else
                  if code < 18785606913350042270860800 then
                    decodeStateCodeChunk149 code
                  else
                    decodeStateCodeChunk150 code
              else
                if code < 18787352209618755326632704 then
                  decodeStateCodeChunk151 code
                else
                  if code < 18787522857470884283040000 then
                    decodeStateCodeChunk152 code
                  else
                    decodeStateCodeChunk153 code
            else
              if code < 19012861216153424437473024 then
                if code < 19012756971763981173784320 then
                  decodeStateCodeChunk154 code
                else
                  if code < 19012842262628070969606912 then
                    decodeStateCodeChunk155 code
                  else
                    decodeStateCodeChunk156 code
              else
                if code < 19013031929503307737016064 then
                  decodeStateCodeChunk157 code
                else
                  if code < 19017040555936946788363008 then
                    decodeStateCodeChunk158 code
                  else
                    decodeStateCodeChunk159 code
        else
          if code < 19045617505048302514399872 then
            if code < 19037425215416971879809792 then
              if code < 19030179779047378651874688 then
                if code < 19027194599108915908274304 then
                  decodeStateCodeChunk160 code
                else
                  decodeStateCodeChunk161 code
              else
                if code < 19030350492397262072350080 then
                  decodeStateCodeChunk162 code
                else
                  if code < 19037424986907304679997696 then
                    decodeStateCodeChunk163 code
                  else
                    decodeStateCodeChunk164 code
            else
              if code < 19041519165620126590128384 then
                if code < 19041433744962418890534144 then
                  decodeStateCodeChunk165 code
                else
                  if code < 19041519035826508679638272 then
                    decodeStateCodeChunk166 code
                  else
                    decodeStateCodeChunk167 code
              else
                if code < 19041689616031282377473280 then
                  decodeStateCodeChunk168 code
                else
                  if code < 19045617425515389395548800 then
                    decodeStateCodeChunk169 code
                  else
                    decodeStateCodeChunk170 code
          else
            if code < 19160139683635877957140224 then
              if code < 19048687976155300036248960 then
                if code < 19048602671569331445647232 then
                  decodeStateCodeChunk171 code
                else
                  if code < 19048687962433421234751360 then
                    decodeStateCodeChunk172 code
                  else
                    decodeStateCodeChunk173 code
              else
                if code < 19048773256050923212293504 then
                  decodeStateCodeChunk174 code
                else
                  if code < 19160139584606509511518464 then
                    decodeStateCodeChunk175 code
                  else
                    decodeStateCodeChunk176 code
            else
              if code < 19160224888580480048170752 then
                if code < 19160224875775226904337152 then
                  decodeStateCodeChunk177 code
                else
                  if code < 19160224877611775803039488 then
                    decodeStateCodeChunk178 code
                  else
                    decodeStateCodeChunk179 code
              else
                if code < 19160329119859989921786624 then
                  decodeStateCodeChunk180 code
                else
                  if code < 19160414411028759980644608 then
                    decodeStateCodeChunk181 code
                  else
                    decodeStateCodeChunk182 code
  else
    if code < 19838723747654930502545280 then
      if code < 19653206121436317480016128 then
        if code < 19545673412034694626766848 then
          if code < 19189072230947280361495296 then
            if code < 19174563073902903046936704 then
              if code < 19174491921098594962818432 then
                if code < 19174477706259259867972992 then
                  decodeStateCodeChunk183 code
                else
                  decodeStateCodeChunk184 code
              else
                if code < 19174562999244867878402688 then
                  decodeStateCodeChunk185 code
                else
                  if code < 19174563008080531593681024 then
                    decodeStateCodeChunk186 code
                  else
                    decodeStateCodeChunk187 code
            else
              if code < 19177562394643266330609024 then
                if code < 19174653026052805113830784 then
                  decodeStateCodeChunk188 code
                else
                  if code < 19174738317221574808212096 then
                    decodeStateCodeChunk189 code
                  else
                    decodeStateCodeChunk190 code
              else
                if code < 19184788745186141508873984 then
                  decodeStateCodeChunk191 code
                else
                  if code < 19184978181723161429590272 then
                    decodeStateCodeChunk192 code
                  else
                    decodeStateCodeChunk193 code
          else
            if code < 19542583855782285830221824 then
              if code < 19251425201848279463991168 then
                if code < 19193000107159041247504512 then
                  decodeStateCodeChunk194 code
                else
                  if code < 19196070577961602517571456 then
                    decodeStateCodeChunk195 code
                  else
                    decodeStateCodeChunk196 code
              else
                if code < 19385497792623805290388224 then
                  decodeStateCodeChunk197 code
                else
                  if code < 19540829082336245276382720 then
                    decodeStateCodeChunk198 code
                  else
                    decodeStateCodeChunk199 code
            else
              if code < 19544937335742201290966016 then
                if code < 19544923043812267787879424 then
                  decodeStateCodeChunk200 code
                else
                  if code < 19544923252619538698142720 then
                    decodeStateCodeChunk201 code
                  else
                    decodeStateCodeChunk202 code
              else
                if code < 19545654341514106255560192 then
                  decodeStateCodeChunk203 code
                else
                  if code < 19545655131244642796052480 then
                    decodeStateCodeChunk204 code
                  else
                    decodeStateCodeChunk205 code
        else
          if code < 19564096964476587148320768 then
            if code < 19563360941189660119483392 then
              if code < 19563345883303240582780416 then
                if code < 19559365707368054251952640 then
                  decodeStateCodeChunk206 code
                else
                  decodeStateCodeChunk207 code
              else
                if code < 19563360085648628710626816 then
                  decodeStateCodeChunk208 code
                else
                  if code < 19563360162834143505613824 then
                    decodeStateCodeChunk209 code
                  else
                    decodeStateCodeChunk210 code
            else
              if code < 19564077234332582727556608 then
                if code < 19563459591658849297012224 then
                  decodeStateCodeChunk211 code
                else
                  if code < 19563473883580258520471040 then
                    decodeStateCodeChunk212 code
                  else
                    decodeStateCodeChunk213 code
              else
                if code < 19564096108935564658225152 then
                  decodeStateCodeChunk214 code
                else
                  if code < 19564096189370997854969856 then
                    decodeStateCodeChunk215 code
                  else
                    decodeStateCodeChunk216 code
          else
            if code < 19651366055001586259395584 then
              if code < 19577675656974674062531584 then
                if code < 19564162525188209186938368 then
                  decodeStateCodeChunk217 code
                else
                  if code < 19564181480243551215661056 then
                    decodeStateCodeChunk218 code
                  else
                    decodeStateCodeChunk219 code
              else
                if code < 19651366042196333296960512 then
                  decodeStateCodeChunk220 code
                else
                  if code < 19651366053165035002512384 then
                    decodeStateCodeChunk221 code
                  else
                    decodeStateCodeChunk222 code
            else
              if code < 19653120815642652509171712 then
                if code < 19651366833763099474745856 then
                  decodeStateCodeChunk223 code
                else
                  if code < 19651479776145233978300928 then
                    decodeStateCodeChunk224 code
                  else
                    decodeStateCodeChunk225 code
              else
                if code < 19653120830267553983417856 then
                  decodeStateCodeChunk226 code
                else
                  if code < 19653120832104096895968768 then
                    decodeStateCodeChunk227 code
                  else
                    decodeStateCodeChunk228 code
      else
        if code < 19704655502296539713968896 then
          if code < 19674614195970255178550784 then
            if code < 19656191301374472934510080 then
              if code < 19655460003672930539460096 then
                if code < 19654145095741959925168128 then
                  decodeStateCodeChunk229 code
                else
                  decodeStateCodeChunk230 code
              else
                if code < 19655460793402866227561472 then
                  decodeStateCodeChunk231 code
                else
                  if code < 19655474218823240909991936 then
                    decodeStateCodeChunk232 code
                  else
                    decodeStateCodeChunk233 code
            else
              if code < 19669902669014183472089088 then
                if code < 19656192078308507419422720 then
                  decodeStateCodeChunk234 code
                else
                  if code < 19656210322545340193791488 then
                    decodeStateCodeChunk235 code
                  else
                    decodeStateCodeChunk236 code
              else
                if code < 19673882908932142685417472 then
                  decodeStateCodeChunk237 code
                else
                  if code < 19673897902836024673976832 then
                    decodeStateCodeChunk238 code
                  else
                    decodeStateCodeChunk239 code
          else
            if code < 19680092566975093613596416 then
              if code < 19676064164382566038192896 then
                if code < 19674633938919271150542336 then
                  decodeStateCodeChunk240 code
                else
                  if code < 19675978829644339869122304 then
                    decodeStateCodeChunk241 code
                  else
                    decodeStateCodeChunk242 code
              else
                if code < 19680072834689871156870912 then
                  decodeStateCodeChunk243 code
                else
                  if code < 19680091645623171071291136 then
                    decodeStateCodeChunk244 code
                  else
                    decodeStateCodeChunk245 code
            else
              if code < 19693401604020439111972224 then
                if code < 19690402274445822667975296 then
                  decodeStateCodeChunk246 code
                else
                  if code < 19693387465657153236268416 then
                    decodeStateCodeChunk247 code
                  else
                    decodeStateCodeChunk248 code
              else
                if code < 19700627801381748255921408 then
                  decodeStateCodeChunk249 code
                else
                  if code < 19704636561882999818481408 then
                    decodeStateCodeChunk250 code
                  else
                    decodeStateCodeChunk251 code
        else
          if code < 19823361343770831585198336 then
            if code < 19711810226557637522130816 then
              if code < 19704656302995237906362112 then
                if code < 19704655515101792706637056 then
                  decodeStateCodeChunk252 code
                else
                  decodeStateCodeChunk253 code
              else
                if code < 19704721852442409767813376 then
                  decodeStateCodeChunk254 code
                else
                  if code < 19704740806270562184347904 then
                    decodeStateCodeChunk255 code
                  else
                    decodeStateCodeChunk256 code
            else
              if code < 19711825220461763491710336 then
                if code < 19711824364920740789983104 then
                  decodeStateCodeChunk257 code
                else
                  if code < 19711824442015971118937472 then
                    decodeStateCodeChunk258 code
                  else
                    decodeStateCodeChunk259 code
              else
                if code < 19711895443079899979859840 then
                  decodeStateCodeChunk260 code
                else
                  if code < 19711909732869011591137152 then
                    decodeStateCodeChunk261 code
                  else
                    decodeStateCodeChunk262 code
          else
            if code < 19827456107782095201639168 then
              if code < 19823446647439887008187648 then
                if code < 19823361354747717962100480 then
                  decodeStateCodeChunk263 code
                else
                  if code < 19823361356880477414934272 then
                    decodeStateCodeChunk264 code
                  else
                    decodeStateCodeChunk265 code
              else
                if code < 19827455307083396858080512 then
                  decodeStateCodeChunk266 code
                else
                  if code < 19827456094977129786104064 then
                    decodeStateCodeChunk267 code
                  else
                    decodeStateCodeChunk268 code
            else
              if code < 19837699476391571960313216 then
                if code < 19827475050337092427979520 then
                  decodeStateCodeChunk269 code
                else
                  if code < 19837699467555629949459840 then
                    decodeStateCodeChunk270 code
                  else
                    decodeStateCodeChunk271 code
              else
                if code < 19837699596728888808562560 then
                  decodeStateCodeChunk272 code
                else
                  if code < 19837784769681816305101440 then
                    decodeStateCodeChunk273 code
                  else
                    decodeStateCodeChunk274 code
    else
      if code < 25091319310131184264954368 then
        if code < 20501096701907982493572480 then
          if code < 20005621725264272671371264 then
            if code < 19852038819186540633255168 then
              if code < 19840770728382087973885824 then
                if code < 19840769947182613673063808 then
                  decodeStateCodeChunk275 code
                else
                  decodeStateCodeChunk276 code
              else
                if code < 19840784230584793645630848 then
                  decodeStateCodeChunk277 code
                else
                  if code < 19852019075941491212561664 then
                    decodeStateCodeChunk278 code
                  else
                    decodeStateCodeChunk279 code
            else
              if code < 19859278132949908352190336 then
                if code < 19856207596020530881587840 then
                  decodeStateCodeChunk280 code
                else
                  if code < 19859193631816041586455936 then
                    decodeStateCodeChunk281 code
                  else
                    decodeStateCodeChunk282 code
              else
                if code < 19984750861111863323106816 then
                  decodeStateCodeChunk283 code
                else
                  if code < 20001527761959883581060096 then
                    decodeStateCodeChunk284 code
                  else
                    decodeStateCodeChunk285 code
          else
            if code < 20339390116754338698554112 then
              if code < 20095268691956914175178240 then
                if code < 20006329449777673401441792 then
                  decodeStateCodeChunk286 code
                else
                  if code < 20093627636108159952374784 then
                    decodeStateCodeChunk287 code
                  else
                    decodeStateCodeChunk288 code
              else
                if code < 20095439275513179745629696 then
                  decodeStateCodeChunk289 code
                else
                  if code < 20113795808691732082135296 then
                    decodeStateCodeChunk290 code
                  else
                    decodeStateCodeChunk291 code
            else
              if code < 20375131494479708890776960 then
                if code < 20356623506088773950633344 then
                  decodeStateCodeChunk292 code
                else
                  if code < 20367962695220738099887872 then
                    decodeStateCodeChunk293 code
                  else
                    decodeStateCodeChunk294 code
              else
                if code < 20486668494652447664588544 then
                  decodeStateCodeChunk295 code
                else
                  if code < 20500921301362978307700096 then
                    decodeStateCodeChunk296 code
                  else
                    decodeStateCodeChunk297 code
        else
          if code < 21006536052504095621782272 then
            if code < 20890539706180141964828160 then
              if code < 20743674100358767232355072 then
                if code < 20519443636451916715092096 then
                  decodeStateCodeChunk298 code
                else
                  decodeStateCodeChunk299 code
              else
                if code < 20872097925962808450129408 then
                  decodeStateCodeChunk300 code
                else
                  if code < 20889803681167015871262720 then
                    decodeStateCodeChunk301 code
                  else
                    decodeStateCodeChunk302 code
            else
              if code < 20980588650737915728442880 then
                if code < 20904119208613561107078144 then
                  decodeStateCodeChunk303 code
                else
                  if code < 20977923316821288255037440 then
                    decodeStateCodeChunk304 code
                  else
                    decodeStateCodeChunk305 code
              else
                if code < 20982635677178050804932096 then
                  decodeStateCodeChunk306 code
                else
                  if code < 21001077457344917797953024 then
                    decodeStateCodeChunk307 code
                  else
                    decodeStateCodeChunk308 code
          else
            if code < 21167227746776434702992768 then
              if code < 21038353253642143815103872 then
                if code < 21031080867906423886114560 then
                  decodeStateCodeChunk309 code
                else
                  if code < 21035268696576563177592960 then
                    decodeStateCodeChunk310 code
                  else
                    decodeStateCodeChunk311 code
              else
                if code < 21153898924428989819443968 then
                  decodeStateCodeChunk312 code
                else
                  if code < 21164143062964271937881472 then
                    decodeStateCodeChunk313 code
                  else
                    decodeStateCodeChunk314 code
            else
              if code < 24449808024903126574469376 then
                if code < 24425068805160587090466048 then
                  decodeStateCodeChunk315 code
                else
                  if code < 24428153491411841169772032 then
                    decodeStateCodeChunk316 code
                  else
                    decodeStateCodeChunk317 code
              else
                if code < 24535605867760082317771008 then
                  decodeStateCodeChunk318 code
                else
                  if code < 24649342052417740459501056 then
                    decodeStateCodeChunk319 code
                  else
                    decodeStateCodeChunk320 code
      else
        if code < 27522121634534959894697472 then
          if code < 26744268100075770215176704 then
            if code < 26528285545103255213007360 then
              if code < 25198827538758372467557632 then
                if code < 25091375380977018893971968 then
                  decodeStateCodeChunk321 code
                else
                  decodeStateCodeChunk322 code
              else
                if code < 25201912210383627944087040 then
                  decodeStateCodeChunk323 code
                else
                  if code < 25862234168331893049995520 then
                    decodeStateCodeChunk324 code
                  else
                    decodeStateCodeChunk325 code
            else
              if code < 26638010611150784986759680 then
                if code < 26633915926169746190501376 then
                  decodeStateCodeChunk326 code
                else
                  if code < 26635647072191674292884224 then
                    decodeStateCodeChunk327 code
                  else
                    decodeStateCodeChunk328 code
              else
                if code < 26638717542994279068364800 then
                  decodeStateCodeChunk329 code
                else
                  if code < 26732162248292455905664512 then
                    decodeStateCodeChunk330 code
                  else
                    decodeStateCodeChunk331 code
          else
            if code < 27007519656545527970551680 then
              if code < 26996086195578446775812352 then
                if code < 26745994380977847628763904 then
                  decodeStateCodeChunk332 code
                else
                  if code < 26748547570968782774321664 then
                    decodeStateCodeChunk333 code
                  else
                    decodeStateCodeChunk334 code
              else
                if code < 27000180287449277497217280 then
                  decodeStateCodeChunk335 code
                else
                  if code < 27004278669825795560106624 then
                    decodeStateCodeChunk336 code
                  else
                    decodeStateCodeChunk337 code
            else
              if code < 27151646936139525929007744 then
                if code < 27143449756103173584847104 then
                  decodeStateCodeChunk338 code
                else
                  if code < 27143468797689420389777664 then
                    decodeStateCodeChunk339 code
                  else
                    decodeStateCodeChunk340 code
              else
                if code < 27154731699181393684649856 then
                  decodeStateCodeChunk341 code
                else
                  if code < 27518026872360003893402112 then
                    decodeStateCodeChunk342 code
                  else
                    decodeStateCodeChunk343 code
        else
          if code < 27802586810580820566217344 then
            if code < 27630290059854191698367232 then
              if code < 27522842509746048559509504 then
                if code < 27522767485376745737527296 then
                  decodeStateCodeChunk344 code
                else
                  decodeStateCodeChunk345 code
              else
                if code < 27545284403865577115285760 then
                  decodeStateCodeChunk346 code
                else
                  if code < 27618008175433732532103936 then
                    decodeStateCodeChunk347 code
                  else
                    decodeStateCodeChunk348 code
            else
              if code < 27663382863664115153211648 then
                if code < 27632672733934545277174272 then
                  decodeStateCodeChunk349 code
                else
                  if code < 27659288902187805282931968 then
                    decodeStateCodeChunk350 code
                  else
                    decodeStateCodeChunk351 code
              else
                if code < 27663402046611477570916608 then
                  decodeStateCodeChunk352 code
                else
                  if code < 27670556629805567155668864 then
                    decodeStateCodeChunk353 code
                  else
                    decodeStateCodeChunk354 code
          else
            if code < 28322529844300188864088320 then
              if code < 27817883095259913234470784 then
                if code < 27806671526244147154568448 then
                  decodeStateCodeChunk355 code
                else
                  if code < 27810728458145895508487424 then
                    decodeStateCodeChunk356 code
                  else
                    decodeStateCodeChunk357 code
              else
                if code < 27960359578547646779306496 then
                  decodeStateCodeChunk358 code
                else
                  if code < 28058605002894384266236416 then
                    decodeStateCodeChunk359 code
                  else
                    decodeStateCodeChunk360 code
            else
              if code < 28869034982553068034516480 then
                if code < 28469893373456942369343744 then
                  decodeStateCodeChunk361 code
                else
                  if code < 28702363640593276420690176 then
                    decodeStateCodeChunk362 code
                  else
                    decodeStateCodeChunk363 code
              else
                if code < 28959823068628618797917184 then
                  decodeStateCodeChunk364 code
                else
                  if code < 29129030362115317575038592 then
                    decodeStateCodeChunk365 code
                  else
                    decodeStateCodeChunk366 code

def decodeState
    (vector : Fin 33 -> Fin 6) : Fin 11742 :=
  decodeStateCode (stateVectorCode vector)

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14155.Shards
