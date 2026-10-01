import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13662.Shards.DecodeStatePart00
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13662.Shards.DecodeStatePart01
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13662.Shards.DecodeStatePart02
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13662.Shards.DecodeStatePart03
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13662.Shards.DecodeStatePart04
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13662.Shards.DecodeStatePart05
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13662.Shards.DecodeStatePart06
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13662.Shards.DecodeStatePart07
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13662.Shards.DecodeStatePart08
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13662.Shards.DecodeStatePart09
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13662.Shards.DecodeStatePart10
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13662.Shards.DecodeStatePart11

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13662.Shards

def stateVectorCode
    (vector : Fin 44 -> Fin 6) : Nat :=
  (vector (0 : Fin 44)).val + 6 * ((vector (1 : Fin 44)).val + 6 * ((vector (2 : Fin 44)).val + 6 * ((vector (3 : Fin 44)).val + 6 * ((vector (4 : Fin 44)).val + 6 * ((vector (5 : Fin 44)).val + 6 * ((vector (6 : Fin 44)).val + 6 * ((vector (7 : Fin 44)).val + 6 * ((vector (8 : Fin 44)).val + 6 * ((vector (9 : Fin 44)).val + 6 * ((vector (10 : Fin 44)).val + 6 * ((vector (11 : Fin 44)).val + 6 * ((vector (12 : Fin 44)).val + 6 * ((vector (13 : Fin 44)).val + 6 * ((vector (14 : Fin 44)).val + 6 * ((vector (15 : Fin 44)).val + 6 * ((vector (16 : Fin 44)).val + 6 * ((vector (17 : Fin 44)).val + 6 * ((vector (18 : Fin 44)).val + 6 * ((vector (19 : Fin 44)).val + 6 * ((vector (20 : Fin 44)).val + 6 * ((vector (21 : Fin 44)).val + 6 * ((vector (22 : Fin 44)).val + 6 * ((vector (23 : Fin 44)).val + 6 * ((vector (24 : Fin 44)).val + 6 * ((vector (25 : Fin 44)).val + 6 * ((vector (26 : Fin 44)).val + 6 * ((vector (27 : Fin 44)).val + 6 * ((vector (28 : Fin 44)).val + 6 * ((vector (29 : Fin 44)).val + 6 * ((vector (30 : Fin 44)).val + 6 * ((vector (31 : Fin 44)).val + 6 * ((vector (32 : Fin 44)).val + 6 * ((vector (33 : Fin 44)).val + 6 * ((vector (34 : Fin 44)).val + 6 * ((vector (35 : Fin 44)).val + 6 * ((vector (36 : Fin 44)).val + 6 * ((vector (37 : Fin 44)).val + 6 * ((vector (38 : Fin 44)).val + 6 * ((vector (39 : Fin 44)).val + 6 * ((vector (40 : Fin 44)).val + 6 * ((vector (41 : Fin 44)).val + 6 * ((vector (42 : Fin 44)).val + 6 * ((vector (43 : Fin 44)).val)))))))))))))))))))))))))))))))))))))))))))

def decodeStateCode (code : Nat) : Fin 11742 :=
  if code < 13456101611432416768831971508064256 then
    if code < 10969379807287666151852193013862400 then
      if code < 10559433503098643658119981841567744 then
        if code < 10425881853214420823748075044966400 then
          if code < 10407934658634805017700114932338688 then
            if code < 10399022995093411473843690025046016 then
              if code < 10394567164095961281803961773838336 then
                if code < 10394564298462463764242076542373888 then
                  decodeStateCodeChunk0 code
                else
                  decodeStateCodeChunk1 code
              else
                if code < 10395306366676900994150919519916032 then
                  decodeStateCodeChunk2 code
                else
                  if code < 10395306952964992997985745810280448 then
                    decodeStateCodeChunk3 code
                  else
                    decodeStateCodeChunk4 code
            else
              if code < 10399085455107665871891757241782272 then
                if code < 10399023011452540369722539723182080 then
                  decodeStateCodeChunk5 code
                else
                  if code < 10399023568559216091830159496499200 then
                    decodeStateCodeChunk6 code
                  else
                    decodeStateCodeChunk7 code
              else
                if code < 10399147341656458393346760900661248 then
                  decodeStateCodeChunk8 code
                else
                  if code < 10399886541658200576180124256882688 then
                    decodeStateCodeChunk9 code
                  else
                    decodeStateCodeChunk10 code
          else
            if code < 10421302251256777799371672587325440 then
              if code < 10421298714516551270535772063125504 then
                if code < 10412391063097661801865814419148800 then
                  decodeStateCodeChunk11 code
                else
                  decodeStateCodeChunk12 code
              else
                if code < 10421302152657811183384335793754112 then
                  decodeStateCodeChunk13 code
                else
                  if code < 10421302169017279663258863448608768 then
                    decodeStateCodeChunk14 code
                  else
                    decodeStateCodeChunk15 code
            else
              if code < 10425758080190530243895804045021184 then
                if code < 10425755121705645278341626847531008 then
                  decodeStateCodeChunk16 code
                else
                  if code < 10425757987265792654613275571179520 then
                    decodeStateCodeChunk17 code
                  else
                    decodeStateCodeChunk18 code
              else
                if code < 10425758557636846697561776473182208 then
                  decodeStateCodeChunk19 code
                else
                  if code < 10425878892150396988999885253038080 then
                    decodeStateCodeChunk20 code
                  else
                    decodeStateCodeChunk21 code
        else
          if code < 10554994864874935722434757259677696 then
            if code < 10425902484716904841468912407195648 then
              if code < 10425882333386974457180693310787584 then
                if code < 10425882330292337605427603550179328 then
                  decodeStateCodeChunk22 code
                else
                  decodeStateCodeChunk23 code
              else
                if code < 10425882425869592637613759591059456 then
                  decodeStateCodeChunk24 code
                else
                  if code < 10425882428890936207147375475134464 then
                    decodeStateCodeChunk25 code
                  else
                    decodeStateCodeChunk26 code
            else
              if code < 10554974233370404725804788902514688 then
                if code < 10425903057740561618489340350361600 then
                  decodeStateCodeChunk27 code
                else
                  if code < 10554973660422543053101756670005248 then
                    decodeStateCodeChunk28 code
                  else
                    decodeStateCodeChunk29 code
              else
                if code < 10554974249289773926435745609797632 then
                  decodeStateCodeChunk30 code
                else
                  if code < 10554984547797591371503324489568256 then
                    decodeStateCodeChunk31 code
                  else
                    decodeStateCodeChunk32 code
          else
            if code < 10555737500807541595383562512617472 then
              if code < 10555716871587439511498105092952064 then
                if code < 10555716298565886530391535114506240 then
                  decodeStateCodeChunk33 code
                else
                  if code < 10555716871513805063669686836449280 then
                    decodeStateCodeChunk34 code
                  else
                    decodeStateCodeChunk35 code
              else
                if code < 10555716874166635239742427271843840 then
                  decodeStateCodeChunk36 code
                else
                  if code < 10555726613359482730047883912925184 then
                    decodeStateCodeChunk37 code
                  else
                    decodeStateCodeChunk38 code
            else
              if code < 10559430067536239935224863943806976 then
                if code < 10559430064441546224418173303853056 then
                  decodeStateCodeChunk39 code
                else
                  if code < 10559430064885456739889338076942336 then
                    decodeStateCodeChunk40 code
                  else
                    decodeStateCodeChunk41 code
              else
                if code < 10559432930001354014866926856556544 then
                  decodeStateCodeChunk42 code
                else
                  if code < 10559433503025009212122463915003904 then
                    decodeStateCodeChunk43 code
                  else
                    decodeStateCodeChunk44 code
      else
        if code < 10581732811993313335944520309837824 then
          if code < 10560193332394236082850865272573952 then
            if code < 10559505706653532676359946947153920 then
              if code < 10559450693734996864041469371469824 then
                if code < 10559433518944321554006380352884736 then
                  decodeStateCodeChunk45 code
                else
                  decodeStateCodeChunk46 code
              else
                if code < 10559453558926687703789305817714688 then
                  decodeStateCodeChunk47 code
                else
                  if code < 10559491950990052865055752544374784 then
                    decodeStateCodeChunk48 code
                  else
                    decodeStateCodeChunk49 code
            else
              if code < 10559574482749957838350761899839488 then
                if code < 10559553840635925662964692435128320 then
                  decodeStateCodeChunk50 code
                else
                  if code < 10559557292041960299179974685675520 then
                    decodeStateCodeChunk51 code
                  else
                    decodeStateCodeChunk52 code
              else
                if code < 10560172703026752975025633118441472 then
                  decodeStateCodeChunk53 code
                else
                  if code < 10560172703544639103607852148707328 then
                    decodeStateCodeChunk54 code
                  else
                    decodeStateCodeChunk55 code
          else
            if code < 10572869760470529306727231311187968 then
              if code < 10568341154517191966990208954175488 then
                if code < 10560296476126381842190342120329216 then
                  decodeStateCodeChunk56 code
                else
                  if code < 10560317105418126662702901180026880 then
                    decodeStateCodeChunk57 code
                  else
                    decodeStateCodeChunk58 code
              else
                if code < 10568351485228792711623998614179840 then
                  decodeStateCodeChunk59 code
                else
                  if code < 10572800997637487394016135000068096 then
                    decodeStateCodeChunk60 code
                  else
                    decodeStateCodeChunk61 code
            else
              if code < 10581729278276477357363228856274944 then
                if code < 10581709222005944352670215381159936 then
                  decodeStateCodeChunk62 code
                else
                  if code < 10581709237923266572562782057451520 then
                    decodeStateCodeChunk63 code
                  else
                    decodeStateCodeChunk64 code
              else
                if code < 10581729851300077328346469133438976 then
                  decodeStateCodeChunk65 code
                else
                  if code < 10581732716418076865176964597944320 then
                    decodeStateCodeChunk66 code
                  else
                    decodeStateCodeChunk67 code
        else
          if code < 10586309455910607389372455527518208 then
            if code < 10586188643432911367426420554321920 then
              if code < 10586167921731926940191193828593664 then
                if code < 10586165053961041946780841910702080 then
                  decodeStateCodeChunk68 code
                else
                  decodeStateCodeChunk69 code
              else
                if code < 10586185682810638927243279792066560 then
                  decodeStateCodeChunk70 code
                else
                  if code < 10586188547928638464073931984900096 then
                    decodeStateCodeChunk71 code
                  else
                    decodeStateCodeChunk72 code
            else
              if code < 10586288827132341990303877712547840 then
                if code < 10586189120952577964210551982002176 then
                  decodeStateCodeChunk73 code
                else
                  if code < 10586288826616531274271948177985536 then
                    decodeStateCodeChunk74 code
                  else
                    decodeStateCodeChunk75 code
              else
                if code < 10586292265200280146145141777551360 then
                  decodeStateCodeChunk76 code
                else
                  if code < 10586309455908247668457550710542336 then
                    decodeStateCodeChunk77 code
                  else
                    decodeStateCodeChunk78 code
          else
            if code < 10586312989553780437129488013307904 then
              if code < 10586312894049847121428831487102976 then
                if code < 10586309458563153251596342981545984 then
                  decodeStateCodeChunk79 code
                else
                  if code < 10586312416532199074790933193420800 then
                    decodeStateCodeChunk80 code
                  else
                    decodeStateCodeChunk81 code
              else
                if code < 10586312894052206842343736304078848 then
                  decodeStateCodeChunk82 code
                else
                  if code < 10586312896704752704567623758106624 then
                    decodeStateCodeChunk83 code
                  else
                    decodeStateCodeChunk84 code
            else
              if code < 10889164509785146103871498672181248 then
                if code < 10586312989556140161700551270346752 then
                  decodeStateCodeChunk85 code
                else
                  if code < 10586312992207690975133237941972992 then
                    decodeStateCodeChunk86 code
                  else
                    decodeStateCodeChunk87 code
              else
                if code < 10902532052002266769285891665727488 then
                  decodeStateCodeChunk88 code
                else
                  if code < 10907111656244338717373164548624384 then
                    decodeStateCodeChunk89 code
                  else
                    decodeStateCodeChunk90 code
    else
      if code < 11362369754287996306141369109114880 then
        if code < 11361482697838345326840579061764096 then
          if code < 11357769424879684528952579181563904 then
            if code < 11357765970820762812214595355463680 then
              if code < 11357026773473952847346742010957824 then
                if code < 11357026770377212153957752558833664 then
                  decodeStateCodeChunk91 code
                else
                  decodeStateCodeChunk92 code
              else
                if code < 11357026865880804308080904773423104 then
                  decodeStateCodeChunk93 code
                else
                  if code < 11357026866398690434834104213688320 then
                    decodeStateCodeChunk94 code
                  else
                    decodeStateCodeChunk95 code
            else
              if code < 11357766546499353604490394904350720 then
                if code < 11357765970823207816985169309782016 then
                  decodeStateCodeChunk96 code
                else
                  if code < 11357765986738085030279317904216064 then
                    decodeStateCodeChunk97 code
                  else
                    decodeStateCodeChunk98 code
              else
                if code < 11357769408964467728006359097856000 then
                  decodeStateCodeChunk99 code
                else
                  if code < 11357769409406955151444679232835584 then
                    decodeStateCodeChunk100 code
                  else
                    decodeStateCodeChunk101 code
          else
            if code < 11361482601890160326728086935359488 then
              if code < 11357769504539986933162086591418368 then
                if code < 11357769456790067256101635791900672 then
                  decodeStateCodeChunk102 code
                else
                  if code < 11357769504466352487164568664854528 then
                    decodeStateCodeChunk103 code
                  else
                    decodeStateCodeChunk104 code
              else
                if code < 11357769507119182663254235759693824 then
                  decodeStateCodeChunk105 code
                else
                  if code < 11357790133760087431547101592014848 then
                    decodeStateCodeChunk106 code
                  else
                    decodeStateCodeChunk107 code
            else
              if code < 11361482649641785824828992283660288 then
                if code < 11361482602334070845855488512675840 then
                  decodeStateCodeChunk108 code
                else
                  if code < 11361482604984854041190074009571328 then
                    decodeStateCodeChunk109 code
                  else
                    decodeStateCodeChunk110 code
              else
                if code < 11361482666001255884163260768243712 then
                  decodeStateCodeChunk111 code
                else
                  if code < 11361482697835901901581231192985600 then
                    decodeStateCodeChunk112 code
                  else
                    decodeStateCodeChunk113 code
        else
          if code < 11362225240477755223358218429059072 then
            if code < 11361606471007230375646196816203776 then
              if code < 11361483175357672339628719076069376 then
                if code < 11361482713311074702521340160430080 then
                  decodeStateCodeChunk114 code
                else
                  decodeStateCodeChunk115 code
              else
                if code < 11361503326687602723967478704754688 then
                  decodeStateCodeChunk116 code
                else
                  if code < 11361545061904414724776154152095744 then
                    decodeStateCodeChunk117 code
                  else
                    decodeStateCodeChunk118 code
            else
              if code < 11361607044032877272829895300927488 then
                if code < 11361606757519030334072088502652928 then
                  decodeStateCodeChunk119 code
                else
                  if code < 11361606951106092702810152258555904 then
                    decodeStateCodeChunk120 code
                  else
                    decodeStateCodeChunk121 code
              else
                if code < 11361627099858874337507168800468992 then
                  decodeStateCodeChunk122 code
                else
                  if code < 11362222375357708661915745109463040 then
                    decodeStateCodeChunk123 code
                  else
                    decodeStateCodeChunk124 code
          else
            if code < 11362287700121449247224181918060544 then
              if code < 11362225336497186525324494365446144 then
                if code < 11362225243572448937837132162715648 then
                  decodeStateCodeChunk125 code
                else
                  if code < 11362225335979301977980961054052352 then
                    decodeStateCodeChunk126 code
                  else
                    decodeStateCodeChunk127 code
              else
                if code < 11362225813574705282616300734828544 then
                  decodeStateCodeChunk128 code
                else
                  if code < 11362245965346783506345747100979200 then
                    decodeStateCodeChunk129 code
                  else
                    decodeStateCodeChunk130 code
            else
              if code < 11362349586596890045187481230168064 then
                if code < 11362346151109883402577575119736832 then
                  decodeStateCodeChunk131 code
                else
                  if code < 11362349111731816302350950902976512 then
                    decodeStateCodeChunk132 code
                  else
                    decodeStateCodeChunk133 code
              else
                if code < 11362349602958065921803545496834048 then
                  decodeStateCodeChunk134 code
                else
                  if code < 11362349685197564057916354635550720 then
                    decodeStateCodeChunk135 code
                  else
                    decodeStateCodeChunk136 code
      else
        if code < 11521892536800140372336161802145792 then
          if code < 11388362677803792635152773759823872 then
            if code < 11388341459569363000697909281738752 then
              if code < 11383782484250577760134720703156224 then
                if code < 11383761854958832939672079615987712 then
                  decodeStateCodeChunk137 code
                else
                  decodeStateCodeChunk138 code
              else
                if code < 11388217686913587790206623169368064 then
                  decodeStateCodeChunk139 code
                else
                  if code < 11388238315763186350788941598806016 then
                    decodeStateCodeChunk140 code
                  else
                    decodeStateCodeChunk141 code
            else
              if code < 11388362088861107821211491429134336 then
                if code < 11388341462664113573874023676432384 then
                  decodeStateCodeChunk142 code
                else
                  if code < 11388342033034828033114286375620608 then
                    decodeStateCodeChunk143 code
                  else
                    decodeStateCodeChunk144 code
              else
                if code < 11388362088936561805592066514087936 then
                  decodeStateCodeChunk145 code
                else
                  if code < 11388362375372964640161722626682880 then
                    decodeStateCodeChunk146 code
                  else
                    decodeStateCodeChunk147 code
          else
            if code < 11518175921206256821660558584434688 then
              if code < 11468567072013198273761519011885056 then
                if code < 11441697931817589718070246521294848 then
                  decodeStateCodeChunk148 code
                else
                  if code < 11442450932506495778654816845811712 then
                    decodeStateCodeChunk149 code
                  else
                    decodeStateCodeChunk150 code
              else
                if code < 11517457334210478905311672118267904 then
                  decodeStateCodeChunk151 code
                else
                  if code < 11518175905362625908341334601617408 then
                    decodeStateCodeChunk152 code
                  else
                    decodeStateCodeChunk153 code
            else
              if code < 11518189674214859520027288709091328 then
                if code < 11518176478828430522671645633007616 then
                  decodeStateCodeChunk154 code
                else
                  if code < 11518179346525568972875126663532544 then
                    decodeStateCodeChunk155 code
                  else
                    decodeStateCodeChunk156 code
              else
                if code < 11518197107604677360625519347355648 then
                  decodeStateCodeChunk157 code
                else
                  if code < 11518199988639657997766280340819968 then
                    decodeStateCodeChunk158 code
                  else
                    decodeStateCodeChunk159 code
        else
          if code < 11522655902392104045235035761528832 then
            if code < 11522037036904194887331079462318080 then
              if code < 11521913165649735776993606738890752 then
                if code < 11521893109824136732439638646968320 then
                  decodeStateCodeChunk160 code
                else
                  decodeStateCodeChunk161 code
              else
                if code < 11521913261153727543699240198328320 then
                  decodeStateCodeChunk162 code
                else
                  if code < 11521954996372586514328375242313728 then
                    decodeStateCodeChunk163 code
                  else
                    decodeStateCodeChunk164 code
            else
              if code < 11522632325742861507904408812048384 then
                if code < 11522037527688296667342202986811392 then
                  decodeStateCodeChunk165 code
                else
                  if code < 11522037623192229986800577909747712 then
                    decodeStateCodeChunk166 code
                  else
                    decodeStateCodeChunk167 code
              else
                if code < 11522635748409627789582694192828416 then
                  decodeStateCodeChunk168 code
                else
                  if code < 11522652939117285687985552580136960 then
                    decodeStateCodeChunk169 code
                  else
                    decodeStateCodeChunk170 code
          else
            if code < 11544192418792099692804160422924288 then
              if code < 11522776712288557301524297952317440 then
                if code < 11522697637610964606293092232908800 then
                  decodeStateCodeChunk171 code
                else
                  if code < 11522756098840443394432522832105472 then
                    decodeStateCodeChunk172 code
                  else
                    decodeStateCodeChunk173 code
              else
                if code < 11522780150356465495756740533735424 then
                  decodeStateCodeChunk174 code
                else
                  if code < 11522780245860400390613163297140736 then
                    decodeStateCodeChunk175 code
                  else
                    decodeStateCodeChunk176 code
            else
              if code < 13282685773355239558577039047643136 then
                if code < 11548772023402629753830072806404096 then
                  decodeStateCodeChunk177 code
                else
                  if code < 11548772596426286541515471662215168 then
                    decodeStateCodeChunk178 code
                  else
                    decodeStateCodeChunk179 code
              else
                if code < 13443095691904051624159420117143552 then
                  decodeStateCodeChunk180 code
                else
                  if code < 13443106006552255329003569572663296 then
                    decodeStateCodeChunk181 code
                  else
                    decodeStateCodeChunk182 code
  else
    if code < 16361809846265649851643911166996480 then
      if code < 16356486921277603412111359433232384 then
        if code < 16196944067022132471467220616065024 then
          if code < 16196080520899149782178311116591104 then
            if code < 16170064004878198381383018842935296 then
              if code < 14245146558034116942484463250051072 then
                if code < 14245144793863896407525049710923776 then
                  decodeStateCodeChunk183 code
                else
                  decodeStateCodeChunk184 code
              else
                if code < 14247436646852944481264760848520576 then
                  decodeStateCodeChunk185 code
                else
                  if code < 14405565042977940618302966021148672 then
                    decodeStateCodeChunk186 code
                  else
                    decodeStateCodeChunk187 code
            else
              if code < 16196056450812918428171534612287488 then
                if code < 16170064580481050932056589127897088 then
                  decodeStateCodeChunk188 code
                else
                  if code < 16174644185091580729830626143555584 then
                    decodeStateCodeChunk189 code
                  else
                    decodeStateCodeChunk190 code
              else
                if code < 16196056928406276375405182574956544 then
                  decodeStateCodeChunk191 code
                else
                  if code < 16196077079662515409242862048677888 then
                    decodeStateCodeChunk192 code
                  else
                    decodeStateCodeChunk193 code
          else
            if code < 16196572745076444494431842801119232 then
              if code < 16196201441701019475576072942809088 then
                if code < 16196180796934100274611913262682112 then
                  decodeStateCodeChunk194 code
                else
                  if code < 16196200852760098875129657601732608 then
                    decodeStateCodeChunk195 code
                  else
                    decodeStateCodeChunk196 code
              else
                if code < 16196204293996731668604895654932480 then
                  decodeStateCodeChunk197 code
                else
                  if code < 16196428263542652948009710967754752 then
                    decodeStateCodeChunk198 code
                  else
                    decodeStateCodeChunk199 code
            else
              if code < 16196923340015658273822890360033280 then
                if code < 16196799089398409746738381952372736 then
                  decodeStateCodeChunk200 code
                else
                  if code < 16196799566991767693964271862796288 then
                    decodeStateCodeChunk201 code
                  else
                    decodeStateCodeChunk202 code
              else
                if code < 16196923435519650033216206939344896 then
                  decodeStateCodeChunk203 code
                else
                  if code < 16196943491345929777693436725161984 then
                    decodeStateCodeChunk204 code
                  else
                    decodeStateCodeChunk205 code
        else
          if code < 16330474512294582483856367595343872 then
            if code < 16200657257370393597736707563433984 then
              if code < 16200636548860494210424878201360384 then
                if code < 16199171980126060554265974182572032 then
                  decodeStateCodeChunk206 code
                else
                  decodeStateCodeChunk207 code
              else
                if code < 16200639493565047986041684329549824 then
                  decodeStateCodeChunk208 code
                else
                  if code < 16200640066662396069636865521143808 then
                    decodeStateCodeChunk209 code
                  else
                    decodeStateCodeChunk210 code
            else
              if code < 16200660698533279759343937835216896 then
                if code < 16200660122930484113128086742659072 then
                  decodeStateCodeChunk211 code
                else
                  if code < 16200660695438642907590848074608640 then
                    decodeStateCodeChunk212 code
                  else
                    decodeStateCodeChunk213 code
              else
                if code < 16201379267032597944868369761619968 then
                  decodeStateCodeChunk214 code
                else
                  if code < 16330473939272689920584784897626112 then
                    decodeStateCodeChunk215 code
                  else
                    decodeStateCodeChunk216 code
          else
            if code < 16330618914243865192669195291889664 then
              if code < 16330495141145885285874817861079040 then
                if code < 16330474512367989487552467194204160 then
                  decodeStateCodeChunk217 code
                else
                  if code < 16330494568122285322203894464040960 then
                    decodeStateCodeChunk218 code
                  else
                    decodeStateCodeChunk219 code
              else
                if code < 16330495141588431145684081822912512 then
                  decodeStateCodeChunk220 code
                else
                  if code < 16330598285392221230858981518135296 then
                    decodeStateCodeChunk221 code
                  else
                    decodeStateCodeChunk222 code
            else
              if code < 16335074746198621370439170560659456 then
                if code < 16330618930602994088547104620056576 then
                  decodeStateCodeChunk223 code
                else
                  if code < 16335054116907216123257762608631808 then
                    decodeStateCodeChunk224 code
                  else
                    decodeStateCodeChunk225 code
              else
                if code < 16356466289775460557847904315117568 then
                  decodeStateCodeChunk226 code
                else
                  if code < 16356466878716041574299033520295936 then
                    decodeStateCodeChunk227 code
                  else
                    decodeStateCodeChunk228 code
      else
        if code < 16357353905984276577112028955316224 then
          if code < 16356858237917463614211365858021376 then
            if code < 16356610787668720584143780161695744 then
              if code < 16356487491722007642050901881376768 then
                if code < 16356487014572844518655149845499904 then
                  decodeStateCodeChunk229 code
                else
                  decodeStateCodeChunk230 code
              else
                if code < 16356487507565638555370360956686336 then
                  decodeStateCodeChunk231 code
                else
                  if code < 16356490468629719250998820293038080 then
                    decodeStateCodeChunk232 code
                  else
                    decodeStateCodeChunk233 code
            else
              if code < 16356611360250172704716216397066240 then
                if code < 16356611264745898221903904280186880 then
                  decodeStateCodeChunk234 code
                else
                  if code < 16356611265261737367919183874445312 then
                    decodeStateCodeChunk235 code
                  else
                    decodeStateCodeChunk236 code
              else
                if code < 16356611362902718577909519541252096 then
                  decodeStateCodeChunk237 code
                else
                  if code < 16356614225883670224106415941054464 then
                    decodeStateCodeChunk238 code
                  else
                    decodeStateCodeChunk239 code
          else
            if code < 16357229669075658053451117554552832 then
              if code < 16357209501457901979541014657748992 then
                if code < 16356982106518978819994761009065984 then
                  decodeStateCodeChunk240 code
                else
                  if code < 16356982695459899420542501214318592 then
                    decodeStateCodeChunk241 code
                  else
                    decodeStateCodeChunk242 code
              else
                if code < 16357229557654402517857663613128704 then
                  decodeStateCodeChunk243 code
                else
                  if code < 16357229652716189573577295177175040 then
                    decodeStateCodeChunk244 code
                  else
                    decodeStateCodeChunk245 code
            else
              if code < 16357353426255919310413821751504896 then
                if code < 16357230132886694690685448770539520 then
                  decodeStateCodeChunk246 code
                else
                  if code < 16357333277134679596048433449783296 then
                    decodeStateCodeChunk247 code
                  else
                    decodeStateCodeChunk248 code
              else
                if code < 16357353903331730703918647446966272 then
                  decodeStateCodeChunk249 code
                else
                  if code < 16357353903405137707611925935919104 then
                    decodeStateCodeChunk250 code
                  else
                    decodeStateCodeChunk251 code
        else
          if code < 16361067112618373316514206177398784 then
            if code < 16359210500017245400212273515340288 then
              if code < 16357353998837426701134258424688640 then
                if code < 16357353919471889532367917235015680 then
                  decodeStateCodeChunk252 code
                else
                  decodeStateCodeChunk253 code
              else
                if code < 16357353999279517683655823721148416 then
                  decodeStateCodeChunk254 code
                else
                  if code < 16357354001932404727616940896071680 then
                    decodeStateCodeChunk255 code
                  else
                    decodeStateCodeChunk256 code
            else
              if code < 16361067096700994235944019685036032 then
                if code < 16359581914592194839842716977524736 then
                  decodeStateCodeChunk257 code
                else
                  if code < 16361046470062136452079999706255360 then
                    decodeStateCodeChunk258 code
                  else
                    decodeStateCodeChunk259 code
              else
                if code < 16361067096703098081218837700513792 then
                  decodeStateCodeChunk260 code
                else
                  if code < 16361067098911733433151118171541504 then
                    decodeStateCodeChunk261 code
                  else
                    decodeStateCodeChunk262 code
          else
            if code < 16361070630347552089071054694477824 then
              if code < 16361067194415666752507933137809408 then
                if code < 16361067192204927555300834651303936 then
                  decodeStateCodeChunk263 code
                else
                  if code < 16361067192207031400575652666781696 then
                    decodeStateCodeChunk264 code
                  else
                    decodeStateCodeChunk265 code
              else
                if code < 16361067208122306635871021143666688 then
                  decodeStateCodeChunk266 code
                else
                  if code < 16361070059976837630118545205850112 then
                    decodeStateCodeChunk267 code
                  else
                    decodeStateCodeChunk268 code
            else
              if code < 16361809734846442872897575347654656 then
                if code < 16361070630421241816184186373238784 then
                  decodeStateCodeChunk269 code
                else
                  if code < 16361070646263906088842301920227328 then
                    decodeStateCodeChunk270 code
                  else
                    decodeStateCodeChunk271 code
              else
                if code < 16361809737499328329781249665241088 then
                  decodeStateCodeChunk272 code
                else
                  if code < 16361809830424065919367521992683520 then
                    decodeStateCodeChunk273 code
                  else
                    decodeStateCodeChunk274 code
    else
      if code < 17159406536357685131157592096223232 then
        if code < 17134877401541903236657047165849600 then
          if code < 17132527145246790323406116352872448 then
            if code < 17132523611603359769007112395214848 then
              if code < 16677783081589742368795440105689088 then
                if code < 16677413465524165544511942784880640 then
                  decodeStateCodeChunk275 code
                else
                  decodeStateCodeChunk276 code
              else
                if code < 16681889926328858539621065176150016 then
                  decodeStateCodeChunk277 code
                else
                  if code < 16762094893562949183747929733033984 then
                    decodeStateCodeChunk278 code
                  else
                    decodeStateCodeChunk279 code
            else
              if code < 17132523707180984394937500793884672 then
                if code < 17132523614254199824917757751513088 then
                  decodeStateCodeChunk280 code
                else
                  if code < 17132523707105530410506067366432768 then
                    decodeStateCodeChunk281 code
                  else
                    decodeStateCodeChunk282 code
              else
                if code < 17132523723024615308265188106424320 then
                  decodeStateCodeChunk283 code
                else
                  if code < 17132525426175990575601348393947136 then
                    decodeStateCodeChunk284 code
                  else
                    decodeStateCodeChunk285 code
          else
            if code < 17132647957724541571574530134822912 then
              if code < 17132544351874212289328757490569216 then
                if code < 17132527145320480050519248031633408 then
                  decodeStateCodeChunk286 code
                else
                  if code < 17132527161164167824363751895519232 then
                    decodeStateCodeChunk287 code
                  else
                    decodeStateCodeChunk288 code
              else
                if code < 17132547774540580548853483053895680 then
                  decodeStateCodeChunk289 code
                else
                  if code < 17132647480202827994052322132807680 then
                    decodeStateCodeChunk290 code
                  else
                    decodeStateCodeChunk291 code
            else
              if code < 17132668109128163262437998786031616 then
                if code < 17132648053300119216766763594993664 then
                  decodeStateCodeChunk292 code
                else
                  if code < 17132650918346476051096105235828736 then
                    decodeStateCodeChunk293 code
                  else
                    decodeStateCodeChunk294 code
              else
                if code < 17132669844042593924236235995656192 then
                  decodeStateCodeChunk295 code
                else
                  if code < 17132671549848958489372508901715968 then
                    decodeStateCodeChunk296 code
                  else
                    decodeStateCodeChunk297 code
        else
          if code < 17159258696195160179075702010138624 then
            if code < 17137127379151508366961494471651328 then
              if code < 17137103900656698041543493816471552 then
                if code < 17137103789311180789811555182694400 then
                  decodeStateCodeChunk298 code
                else
                  decodeStateCodeChunk299 code
              else
                if code < 17137107036371222341417497097064448 then
                  decodeStateCodeChunk300 code
                else
                  if code < 17137107338800344519126830812286976 then
                    decodeStateCodeChunk301 code
                  else
                    decodeStateCodeChunk302 code
            else
              if code < 17158540125043352761870031796031488 then
                if code < 17137127951732619280508271775690752 then
                  decodeStateCodeChunk303 code
                else
                  if code < 17158519495751268357412339665457152 then
                    decodeStateCodeChunk304 code
                  else
                    decodeStateCodeChunk305 code
              else
                if code < 17158643268849189827833944772251648 then
                  decodeStateCodeChunk306 code
                else
                  if code < 17158663898142640465578412116455424 then
                    decodeStateCodeChunk307 code
                  else
                    decodeStateCodeChunk308 code
          else
            if code < 17159385907434738006969250647822336 then
              if code < 17159282763186356657042756389687296 then
                if code < 17159262134336758096460437960249344 then
                  decodeStateCodeChunk309 code
                else
                  if code < 17159279325046802561432966515052544 then
                    decodeStateCodeChunk310 code
                  else
                    decodeStateCodeChunk311 code
              else
                if code < 17159282779105724278162487011430400 then
                  decodeStateCodeChunk312 code
                else
                  if code < 17159383042316398842218239239180288 then
                    decodeStateCodeChunk313 code
                  else
                    decodeStateCodeChunk314 code
            else
              if code < 17159403671165995823297825387753472 then
                if code < 17159403098142735491152874760744960 then
                  decodeStateCodeChunk315 code
                else
                  if code < 17159403100795224503761733079969792 then
                    decodeStateCodeChunk316 code
                  else
                    decodeStateCodeChunk317 code
              else
                if code < 17159404817213478379051204642467840 then
                  decodeStateCodeChunk318 code
                else
                  if code < 17159406536283995404044460417462272 then
                    decodeStateCodeChunk319 code
                  else
                    decodeStateCodeChunk320 code
      else
        if code < 17292954286340337098142823642288128 then
          if code < 17163859505331829191833662527614976 then
            if code < 17163119729653600099525956719456256 then
              if code < 17161610960725758255397709767495680 then
                if code < 17159406538936824000623841796730880 then
                  decodeStateCodeChunk321 code
                else
                  decodeStateCodeChunk322 code
              else
                if code < 17163099100362138002382440396279808 then
                  decodeStateCodeChunk323 code
                else
                  if code < 17163099676038340652596484940288000 then
                    decodeStateCodeChunk324 code
                  else
                    decodeStateCodeChunk325 code
            else
              if code < 17163120302235391760475166620758016 then
                if code < 17163119729727232966063968908783616 then
                  decodeStateCodeChunk326 code
                else
                  if code < 17163119745570863879382252521631744 then
                    decodeStateCodeChunk327 code
                  else
                    decodeStateCodeChunk328 code
              else
                if code < 17163120318596567636786551017418752 then
                  decodeStateCodeChunk329 code
                else
                  if code < 17163842025532836019820348377387008 then
                    decodeStateCodeChunk330 code
                  else
                    decodeStateCodeChunk331 code
          else
            if code < 17241837986937992469514275859330752 then
              if code < 17163862941265077635970704970854400 then
                if code < 17163862368241138135580968723722240 then
                  decodeStateCodeChunk332 code
                else
                  if code < 17163862654310790254513673346068480 then
                    decodeStateCodeChunk333 code
                  else
                    decodeStateCodeChunk334 code
              else
                if code < 17212752741847391127722470655250432 then
                  decodeStateCodeChunk335 code
                else
                  if code < 17238868865376044044461138011418624 then
                    decodeStateCodeChunk336 code
                  else
                    decodeStateCodeChunk337 code
            else
              if code < 17292954175140157069051329375817728 then
                if code < 17292933546069486157291028353830912 then
                  decodeStateCodeChunk338 code
                else
                  if code < 17292934119166775800535620009119744 then
                    decodeStateCodeChunk339 code
                  else
                    decodeStateCodeChunk340 code
              else
                if code < 17292954190836346918209953170182144 then
                  decodeStateCodeChunk341 code
                else
                  if code < 17292954270865105857115428729901056 then
                    decodeStateCodeChunk342 code
                  else
                    decodeStateCodeChunk343 code
        else
          if code < 17297537886640893507919570880409600 then
            if code < 17293078616544198260285439155023872 then
              if code < 17292957724924084445397947735592960 then
                if code < 17292954751037716351124341947617280 then
                  decodeStateCodeChunk344 code
                else
                  decodeStateCodeChunk345 code
              else
                if code < 17293078044036435921660126233800704 then
                  decodeStateCodeChunk346 code
                else
                  if code < 17293078521482411200902121837596672 then
                    decodeStateCodeChunk347 code
                  else
                    decodeStateCodeChunk348 code
            else
              if code < 17297534352995359112258068119588864 then
                if code < 17293078632461518900819354773270528 then
                  decodeStateCodeChunk349 code
                else
                  if code < 17295306532300670636807646058819584 then
                    decodeStateCodeChunk350 code
                  else
                    decodeStateCodeChunk351 code
              else
                if code < 17297534368912681343119345208561664 then
                  decodeStateCodeChunk352 code
                else
                  if code < 17297534450710031628821276294885376 then
                    decodeStateCodeChunk353 code
                  else
                    decodeStateCodeChunk354 code
          else
            if code < 17319813608729200920440819741798400 then
              if code < 17319813032610509256665153875390464 then
                if code < 17318950059584874694539471515799552 then
                  decodeStateCodeChunk355 code
                else
                  if code < 17319689259955075213336194492911616 then
                    decodeStateCodeChunk356 code
                  else
                    decodeStateCodeChunk357 code
              else
                if code < 17319813033053055120139039607009280 then
                  decodeStateCodeChunk358 code
                else
                  if code < 17319813605634166033389600370765824 then
                    decodeStateCodeChunk359 code
                  else
                    decodeStateCodeChunk360 code
            else
              if code < 17323530239798257273647167729774592 then
                if code < 17319816487111578812844604417290240 then
                  decodeStateCodeChunk361 code
                else
                  if code < 17323529666774657346216692388900864 then
                    decodeStateCodeChunk362 code
                  else
                    decodeStateCodeChunk363 code
              else
                if code < 17324269437662953091056807694807040 then
                  decodeStateCodeChunk364 code
                else
                  if code < 17324272875730861281024672466120704 then
                    decodeStateCodeChunk365 code
                  else
                    decodeStateCodeChunk366 code

def decodeState
    (vector : Fin 44 -> Fin 6) : Fin 11742 :=
  decodeStateCode (stateVectorCode vector)

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13662.Shards
