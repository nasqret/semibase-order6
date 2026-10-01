import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14268.Shards.DecodeStatePart00
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14268.Shards.DecodeStatePart01
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14268.Shards.DecodeStatePart02
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14268.Shards.DecodeStatePart03
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14268.Shards.DecodeStatePart04
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14268.Shards.DecodeStatePart05
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14268.Shards.DecodeStatePart06
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14268.Shards.DecodeStatePart07
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14268.Shards.DecodeStatePart08
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14268.Shards.DecodeStatePart09
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14268.Shards.DecodeStatePart10
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14268.Shards.DecodeStatePart11

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14268.Shards

def stateVectorCode
    (vector : Fin 32 -> Fin 6) : Nat :=
  (vector (0 : Fin 32)).val + 6 * ((vector (1 : Fin 32)).val + 6 * ((vector (2 : Fin 32)).val + 6 * ((vector (3 : Fin 32)).val + 6 * ((vector (4 : Fin 32)).val + 6 * ((vector (5 : Fin 32)).val + 6 * ((vector (6 : Fin 32)).val + 6 * ((vector (7 : Fin 32)).val + 6 * ((vector (8 : Fin 32)).val + 6 * ((vector (9 : Fin 32)).val + 6 * ((vector (10 : Fin 32)).val + 6 * ((vector (11 : Fin 32)).val + 6 * ((vector (12 : Fin 32)).val + 6 * ((vector (13 : Fin 32)).val + 6 * ((vector (14 : Fin 32)).val + 6 * ((vector (15 : Fin 32)).val + 6 * ((vector (16 : Fin 32)).val + 6 * ((vector (17 : Fin 32)).val + 6 * ((vector (18 : Fin 32)).val + 6 * ((vector (19 : Fin 32)).val + 6 * ((vector (20 : Fin 32)).val + 6 * ((vector (21 : Fin 32)).val + 6 * ((vector (22 : Fin 32)).val + 6 * ((vector (23 : Fin 32)).val + 6 * ((vector (24 : Fin 32)).val + 6 * ((vector (25 : Fin 32)).val + 6 * ((vector (26 : Fin 32)).val + 6 * ((vector (27 : Fin 32)).val + 6 * ((vector (28 : Fin 32)).val + 6 * ((vector (29 : Fin 32)).val + 6 * ((vector (30 : Fin 32)).val + 6 * ((vector (31 : Fin 32)).val)))))))))))))))))))))))))))))))

def decodeStateCode (code : Nat) : Fin 11742 :=
  if code < 3172648640954942146816512 then
    if code < 2742953263997495183788032 then
      if code < 752094049812825398307840 then
        if code < 531186762438475823877120 then
          if code < 531020108053568322201600 then
            if code < 530987724832056649132032 then
              if code < 530986935101767929262080 then
                if code < 530986825515740513439744 then
                  decodeStateCodeChunk0 code
                else
                  decodeStateCodeChunk1 code
              else
                if code < 530986957038797296601088 then
                  decodeStateCodeChunk2 code
                else
                  if code < 530987593210744264888320 then
                    decodeStateCodeChunk3 code
                  else
                    decodeStateCodeChunk4 code
            else
              if code < 531015369672242758947840 then
                if code < 530991542589235704041472 then
                  decodeStateCodeChunk5 code
                else
                  if code < 530992331606188136042496 then
                    decodeStateCodeChunk6 code
                  else
                    decodeStateCodeChunk7 code
              else
                if code < 531016155136947632477184 then
                  decodeStateCodeChunk8 code
                else
                  if code < 531019994083549170886656 then
                    decodeStateCodeChunk9 code
                  else
                    decodeStateCodeChunk10 code
          else
            if code < 531158196873053736364032 then
              if code < 531020897783804496964608 then
                if code < 531020765549906320822272 then
                  decodeStateCodeChunk11 code
                else
                  decodeStateCodeChunk12 code
              else
                if code < 531157411512742687773696 then
                  decodeStateCodeChunk13 code
                else
                  if code < 531158174935632911001600 then
                    decodeStateCodeChunk14 code
                  else
                    decodeStateCodeChunk15 code
            else
              if code < 531162146235101398953984 then
                if code < 531158306557806998719488 then
                  decodeStateCodeChunk16 code
                else
                  if code < 531158328494757639097344 then
                    decodeStateCodeChunk17 code
                  else
                    decodeStateCodeChunk18 code
              else
                if code < 531162935253921872996352 then
                  decodeStateCodeChunk19 code
                else
                  if code < 531185973337373340331008 then
                    decodeStateCodeChunk20 code
                  else
                    decodeStateCodeChunk21 code
        else
          if code < 537132488460342205280256 then
            if code < 532015054266156667103232 then
              if code < 531191347278556507278336 then
                if code < 531190580196216488629248 then
                  decodeStateCodeChunk22 code
                else
                  decodeStateCodeChunk23 code
              else
                if code < 531191475226705004587008 then
                  decodeStateCodeChunk24 code
                else
                  if code < 531191501446570729933824 then
                    decodeStateCodeChunk25 code
                  else
                    decodeStateCodeChunk26 code
            else
              if code < 532214070548354540070912 then
                if code < 532043485180472633462784 then
                  decodeStateCodeChunk27 code
                else
                  if code < 532185636603695985321984 then
                    decodeStateCodeChunk28 code
                  else
                    decodeStateCodeChunk29 code
              else
                if code < 537127745813015518605312 then
                  decodeStateCodeChunk30 code
                else
                  if code < 537128535459153884599296 then
                    decodeStateCodeChunk31 code
                  else
                    decodeStateCodeChunk32 code
          else
            if code < 568031622951077133806592 then
              if code < 538185194466005725876224 then
                if code < 537160914380810752561152 then
                  decodeStateCodeChunk33 code
                else
                  if code < 537161839388896148960256 then
                    decodeStateCodeChunk34 code
                  else
                    decodeStateCodeChunk35 code
              else
                if code < 567861041220076385224704 then
                  decodeStateCodeChunk36 code
                else
                  if code < 567865783274486745655296 then
                    decodeStateCodeChunk37 code
                  else
                    decodeStateCodeChunk38 code
            else
              if code < 574002750638186768609280 then
                if code < 568036365002679445023744 then
                  decodeStateCodeChunk39 code
                else
                  if code < 568888615535045003569152 then
                    decodeStateCodeChunk40 code
                  else
                    decodeStateCodeChunk41 code
              else
                if code < 752060745845846672044032 then
                  decodeStateCodeChunk42 code
                else
                  if code < 752065484247402947997696 then
                    decodeStateCodeChunk43 code
                  else
                    decodeStateCodeChunk44 code
      else
        if code < 2741730765390157316060160 then
          if code < 1858629948331874108018688 then
            if code < 789105542262749494659072 then
              if code < 752264627865098706634752 then
                if code < 752231462855180250737664 then
                  decodeStateCodeChunk45 code
                else
                  decodeStateCodeChunk46 code
              else
                if code < 753259559981005725493248 then
                  decodeStateCodeChunk47 code
                else
                  if code < 758234750721302931369984 then
                    decodeStateCodeChunk48 code
                  else
                    decodeStateCodeChunk49 code
            else
              if code < 1857606435298000065530880 then
                if code < 1857601693260581668015104 then
                  decodeStateCodeChunk50 code
                else
                  if code < 1857601824885106257392640 then
                    decodeStateCodeChunk51 code
                  else
                    decodeStateCodeChunk52 code
              else
                if code < 1857630281372718956964864 then
                  decodeStateCodeChunk53 code
                else
                  if code < 1857634997836840984065024 then
                    decodeStateCodeChunk54 code
                  else
                    decodeStateCodeChunk55 code
          else
            if code < 2741726001415709853536256 then
              if code < 1900451011609456538858496 then
                if code < 1863600619332441220420608 then
                  decodeStateCodeChunk56 code
                else
                  if code < 1894475934049677924953088 then
                    decodeStateCodeChunk57 code
                  else
                    decodeStateCodeChunk58 code
              else
                if code < 2078708149865874946102272 then
                  decodeStateCodeChunk59 code
                else
                  if code < 2121377156836926588733824 then
                    decodeStateCodeChunk60 code
                  else
                    decodeStateCodeChunk61 code
            else
              if code < 2741726790414860922390528 then
                if code < 2741726027008818994443264 then
                  decodeStateCodeChunk62 code
                else
                  if code < 2741726154243227047962624 then
                    decodeStateCodeChunk63 code
                  else
                    decodeStateCodeChunk64 code
              else
                if code < 2741726922039307570867200 then
                  decodeStateCodeChunk65 code
                else
                  if code < 2741730739184854264541184 then
                    decodeStateCodeChunk66 code
                  else
                    decodeStateCodeChunk67 code
        else
          if code < 2741897525701616679545856 then
            if code < 2741759327299891088028672 then
              if code < 2741755352327350561262592 then
                if code < 2741754563223413544317952 then
                  decodeStateCodeChunk68 code
                else
                  decodeStateCodeChunk69 code
              else
                if code < 2741759173740753299238912 then
                  decodeStateCodeChunk70 code
                else
                  if code < 2741759301604751805468672 then
                    decodeStateCodeChunk71 code
                  else
                    decodeStateCodeChunk72 code
            else
              if code < 2741896736685617678208000 then
                if code < 2741760094991120238440448 then
                  decodeStateCodeChunk73 code
                else
                  if code < 2741896605061092665567232 then
                    decodeStateCodeChunk74 code
                  else
                    decodeStateCodeChunk75 code
              else
                if code < 2741897375920898185171968 then
                  decodeStateCodeChunk76 code
                else
                  if code < 2741897398467221626254336 then
                    decodeStateCodeChunk77 code
                  else
                    decodeStateCodeChunk78 code
          else
            if code < 2741930544468959073266688 then
              if code < 2741925166970356252551168 then
                if code < 2741901342833058186479616 then
                  decodeStateCodeChunk79 code
                else
                  if code < 2741902114302236506788864 then
                    decodeStateCodeChunk80 code
                  else
                    decodeStateCodeChunk81 code
              else
                if code < 2741925938440004757844992 then
                  decodeStateCodeChunk82 code
                else
                  if code < 2741929777403062770714624 then
                    decodeStateCodeChunk83 code
                  else
                    decodeStateCodeChunk84 code
            else
              if code < 2742754230162821288816640 then
                if code < 2741930567133756009302016 then
                  decodeStateCodeChunk85 code
                else
                  if code < 2741930698636973295922176 then
                    decodeStateCodeChunk86 code
                  else
                    decodeStateCodeChunk87 code
              else
                if code < 2742782664107479843565568 then
                  decodeStateCodeChunk88 code
                else
                  if code < 2742901931025745465411584 then
                    decodeStateCodeChunk89 code
                  else
                    decodeStateCodeChunk90 code
    else
      if code < 3110387100001649373321216 then
        if code < 3110182665174156650443776 then
          if code < 2779627787149265148561408 then
            if code < 2747900905685911353323520 then
              if code < 2747867732648994780278784 then
                if code < 2747866942935789810978816 then
                  decodeStateCodeChunk91 code
                else
                  decodeStateCodeChunk92 code
              else
                if code < 2747871682011029744971776 then
                  decodeStateCodeChunk93 code
                else
                  if code < 2747896298215357237761024 then
                    decodeStateCodeChunk94 code
                  else
                    decodeStateCodeChunk95 code
            else
              if code < 2778604976808730871580672 then
                if code < 2748923602552471637716992 then
                  decodeStateCodeChunk96 code
                else
                  if code < 2778600220166361240161280 then
                    decodeStateCodeChunk97 code
                  else
                    decodeStateCodeChunk98 code
              else
                if code < 2778770819546225448855552 then
                  decodeStateCodeChunk99 code
                else
                  if code < 2778775562193068889851904 then
                    decodeStateCodeChunk100 code
                  else
                    decodeStateCodeChunk101 code
          else
            if code < 2963003697124279011495936 then
              if code < 2962804681434514581891072 then
                if code < 2784741158115306001133568 then
                  decodeStateCodeChunk102 code
                else
                  if code < 2962799942443894884427776 then
                    decodeStateCodeChunk103 code
                  else
                    decodeStateCodeChunk104 code
              else
                if code < 2962833243363996123211776 then
                  decodeStateCodeChunk105 code
                else
                  if code < 2962970656405880851123200 then
                    decodeStateCodeChunk106 code
                  else
                    decodeStateCodeChunk107 code
            else
              if code < 2999678900205383499589632 then
                if code < 2963975061016255769708544 then
                  decodeStateCodeChunk108 code
                else
                  if code < 2968969425260171674383360 then
                    decodeStateCodeChunk109 code
                  else
                    decodeStateCodeChunk110 code
              else
                if code < 3005819820482895921189888 then
                  decodeStateCodeChunk111 code
                else
                  if code < 3110182534283603217555456 then
                    decodeStateCodeChunk112 code
                  else
                    decodeStateCodeChunk113 code
        else
          if code < 3110216627859013602459648 then
            if code < 3110188061664013820599296 then
              if code < 3110183323283145683966976 then
                if code < 3110182687111185654985728 then
                  decodeStateCodeChunk114 code
                else
                  decodeStateCodeChunk115 code
              else
                if code < 3110183454907213572317184 then
                  decodeStateCodeChunk116 code
                else
                  if code < 3110187272055098493017088 then
                    decodeStateCodeChunk117 code
                  else
                    decodeStateCodeChunk118 code
            else
              if code < 3110215706608659663485952 then
                if code < 3110211096091307150201856 then
                  decodeStateCodeChunk119 code
                else
                  if code < 3110211885212157040303104 then
                    decodeStateCodeChunk120 code
                  else
                    decodeStateCodeChunk121 code
              else
                if code < 3110215834472645471818752 then
                  decodeStateCodeChunk122 code
                else
                  if code < 3110216491952044113097728 then
                    decodeStateCodeChunk123 code
                  else
                    decodeStateCodeChunk124 code
          else
            if code < 3110357876309841045058560 then
              if code < 3110353908788804549419008 then
                if code < 3110353137928986029586432 then
                  decodeStateCodeChunk125 code
                else
                  if code < 3110353273206848311916544 then
                    decodeStateCodeChunk126 code
                  else
                    decodeStateCodeChunk127 code
              else
                if code < 3110354036632559282254848 then
                  decodeStateCodeChunk128 code
                else
                  if code < 3110354058569523043792896 then
                    decodeStateCodeChunk129 code
                  else
                    decodeStateCodeChunk130 code
            else
              if code < 3110382488857539852334080 then
                if code < 3110358647776668379978752 then
                  decodeStateCodeChunk131 code
                else
                  if code < 3110381699838249616570368 then
                    decodeStateCodeChunk132 code
                  else
                    decodeStateCodeChunk133 code
              else
                if code < 3110386310270969134961664 then
                  decodeStateCodeChunk134 code
                else
                  if code < 3110387077353308790813696 then
                    decodeStateCodeChunk135 code
                  else
                    decodeStateCodeChunk136 code
      else
        if code < 3171592877051940074657280 then
          if code < 3117380135521924897938432 then
            if code < 3111409796966948444009472 then
              if code < 3111210763031184777354240 then
                if code < 3110387231504879660169216 then
                  decodeStateCodeChunk137 code
                else
                  decodeStateCodeChunk138 code
              else
                if code < 3111239214527849169122304 then
                  decodeStateCodeChunk139 code
                else
                  if code < 3111381365967998817629184 then
                    decodeStateCodeChunk140 code
                  else
                    decodeStateCodeChunk141 code
            else
              if code < 3116328214878936109218816 then
                if code < 3116323475804140238822400 then
                  decodeStateCodeChunk142 code
                else
                  if code < 3116324265517358268816384 then
                    decodeStateCodeChunk143 code
                  else
                    decodeStateCodeChunk144 code
              else
                if code < 3116352831083263602008064 then
                  decodeStateCodeChunk145 code
                else
                  if code < 3116357438553804717342720 then
                    decodeStateCodeChunk146 code
                  else
                    decodeStateCodeChunk147 code
          else
            if code < 3153197690983200816340992 then
              if code < 3147227352414118812874752 then
                if code < 3147056770685926113506304 then
                  decodeStateCodeChunk148 code
                else
                  if code < 3147061509676637235827712 then
                    decodeStateCodeChunk149 code
                  else
                    decodeStateCodeChunk150 code
              else
                if code < 3147232095060975254098944 then
                  decodeStateCodeChunk151 code
                else
                  if code < 3148084850160132261245952 then
                    decodeStateCodeChunk152 code
                  else
                    decodeStateCodeChunk153 code
            else
              if code < 3171592087321638959221248 then
                if code < 3171591955697178947719680 then
                  decodeStateCodeChunk154 code
                else
                  if code < 3171591977735624241295872 then
                    decodeStateCodeChunk155 code
                  else
                    decodeStateCodeChunk156 code
              else
                if code < 3171592109357328446360064 then
                  decodeStateCodeChunk157 code
                else
                  if code < 3171592745430693296214528 then
                    decodeStateCodeChunk158 code
                  else
                    decodeStateCodeChunk159 code
        else
          if code < 3171763349093002767690240 then
            if code < 3171625146929706237504000 then
              if code < 3171597483828879913112064 then
                if code < 3171596694809576556188160 then
                  decodeStateCodeChunk160 code
                else
                  decodeStateCodeChunk161 code
              else
                if code < 3171620521993673382778368 then
                  decodeStateCodeChunk162 code
                else
                  if code < 3171621311012963679008256 then
                    decodeStateCodeChunk163 code
                  else
                    decodeStateCodeChunk164 code
            else
              if code < 3171626050004144986314240 then
                if code < 3171625260273451747726848 then
                  decodeStateCodeChunk165 code
                else
                  if code < 3171625917770247172968960 then
                    decodeStateCodeChunk166 code
                  else
                    decodeStateCodeChunk167 code
              else
                if code < 3171762690983935007205888 then
                  decodeStateCodeChunk168 code
                else
                  if code < 3171763327155973400351232 then
                    decodeStateCodeChunk169 code
                  else
                    decodeStateCodeChunk170 code
          else
            if code < 3171791914658816676023808 then
              if code < 3171767302111117445485056 then
                if code < 3171763458780028590804480 then
                  decodeStateCodeChunk171 code
                else
                  if code < 3171763480714706670423552 then
                    decodeStateCodeChunk172 code
                  else
                    decodeStateCodeChunk173 code
              else
                if code < 3171768087575822319014400 then
                  decodeStateCodeChunk174 code
                else
                  if code < 3171791125639526379793920 then
                    decodeStateCodeChunk175 code
                  else
                    decodeStateCodeChunk176 code
            else
              if code < 3171796631102734172278272 then
                if code < 3171795732416087518588416 then
                  decodeStateCodeChunk177 code
                else
                  if code < 3171796500107316669000192 then
                    decodeStateCodeChunk178 code
                  else
                    decodeStateCodeChunk179 code
              else
                if code < 3171796653668805382712832 then
                  decodeStateCodeChunk180 code
                else
                  if code < 3172620207095386711478784 then
                    decodeStateCodeChunk181 code
                  else
                    decodeStateCodeChunk182 code
  else
    if code < 3219730093081963825069824 then
      if code < 3183879368356387329783168 then
        if code < 3181997599042271159943936 then
          if code < 3181827012946608503013120 then
            if code < 3177738426042874543624704 then
              if code < 3172819222785151503880704 then
                if code < 3172790788824036837468672 then
                  decodeStateCodeChunk183 code
                else
                  decodeStateCodeChunk184 code
              else
                if code < 3177732898033356370752000 then
                  decodeStateCodeChunk185 code
                else
                  if code < 3177733687763566424126976 then
                    decodeStateCodeChunk186 code
                  else
                    decodeStateCodeChunk187 code
            else
              if code < 3178790350353789457715712 then
                if code < 3177766067311601116402176 then
                  decodeStateCodeChunk188 code
                else
                  if code < 3177766992218126495666688 then
                    decodeStateCodeChunk189 code
                  else
                    decodeStateCodeChunk190 code
              else
                if code < 3181826860119026065582848 then
                  decodeStateCodeChunk191 code
                else
                  if code < 3181826991009579498471168 then
                    decodeStateCodeChunk192 code
                  else
                    decodeStateCodeChunk193 code
          else
            if code < 3181856211047579888330496 then
              if code < 3181831597890521341044480 then
                if code < 3181827649118568531994368 then
                  decodeStateCodeChunk194 code
                else
                  if code < 3181827780742636420344576 then
                    decodeStateCodeChunk195 code
                  else
                    decodeStateCodeChunk196 code
              else
                if code < 3181832387499436668626688 then
                  decodeStateCodeChunk197 code
                else
                  if code < 3181855421926729998229248 then
                    decodeStateCodeChunk198 code
                  else
                    decodeStateCodeChunk199 code
            else
              if code < 3181860817787466961125120 then
                if code < 3181860032444082511513344 then
                  decodeStateCodeChunk200 code
                else
                  if code < 3181860160308068319846144 then
                    decodeStateCodeChunk201 code
                  else
                    decodeStateCodeChunk202 code
              else
                if code < 3181860953694436450487040 then
                  decodeStateCodeChunk203 code
                else
                  if code < 3181997463764408877613824 then
                    decodeStateCodeChunk204 code
                  else
                    decodeStateCodeChunk205 code
        else
          if code < 3182031557340302508196608 then
            if code < 3182002973612091228006144 then
              if code < 3181998362467982130282240 then
                if code < 3181998234624227397446400 then
                  decodeStateCodeChunk206 code
                else
                  decodeStateCodeChunk207 code
              else
                if code < 3181998384404945891820288 then
                  decodeStateCodeChunk208 code
                else
                  if code < 3182002202145263893085952 then
                    decodeStateCodeChunk209 code
                  else
                    decodeStateCodeChunk210 code
            else
              if code < 3182030636106391982989056 then
                if code < 3182026025673672464597760 then
                  decodeStateCodeChunk211 code
                else
                  if code < 3182026814692962700361472 then
                    decodeStateCodeChunk212 code
                  else
                    decodeStateCodeChunk213 code
              else
                if code < 3182031403188731638841088 then
                  decodeStateCodeChunk214 code
                else
                  if code < 3182031425837072221348608 then
                    decodeStateCodeChunk215 code
                  else
                    decodeStateCodeChunk216 code
          else
            if code < 3183873862164458114676096 then
              if code < 3183025691803421665656576 then
                if code < 3182855088866607625381632 then
                  decodeStateCodeChunk217 code
                else
                  if code < 3182883540363272017149696 then
                    decodeStateCodeChunk218 code
                  else
                    decodeStateCodeChunk219 code
              else
                if code < 3183054122802371292036864 then
                  decodeStateCodeChunk220 code
                else
                  if code < 3183873840128690263373184 then
                    decodeStateCodeChunk221 code
                  else
                    decodeStateCodeChunk222 code
            else
              if code < 3183874629875839976420736 then
                if code < 3183873971750472469804416 then
                  decodeStateCodeChunk223 code
                else
                  if code < 3183873993788917763380608 then
                    decodeStateCodeChunk224 code
                  else
                    decodeStateCodeChunk225 code
              else
                if code < 3183874761481087404693888 then
                  decodeStateCodeChunk226 code
                else
                  if code < 3183878582891682456253824 then
                    decodeStateCodeChunk227 code
                  else
                    decodeStateCodeChunk228 code
      else
        if code < 3185101870622717868641664 then
          if code < 3184045365145760861786496 then
            if code < 3183907802201836852786560 then
              if code < 3183903195441745309612416 then
                if code < 3183902423972553928609152 then
                  decodeStateCodeChunk229 code
                else
                  decodeStateCodeChunk230 code
              else
                if code < 3183907031443121165331840 then
                  decodeStateCodeChunk231 code
                else
                  if code < 3183907144702220680434048 then
                    decodeStateCodeChunk232 code
                  else
                    decodeStateCodeChunk233 code
            else
              if code < 3184045211584742333058432 then
                if code < 3184044443790999734848896 then
                  decodeStateCodeChunk234 code
                else
                  if code < 3184044575412716698276224 then
                    decodeStateCodeChunk235 code
                  else
                    decodeStateCodeChunk236 code
              else
                if code < 3184045233623252567307648 then
                  decodeStateCodeChunk237 code
                else
                  if code < 3184045343208875524878720 then
                    decodeStateCodeChunk238 code
                  else
                    decodeStateCodeChunk239 code
          else
            if code < 3184078384536555121564032 then
              if code < 3184073010071116059611520 then
                if code < 3184049186539899076089216 then
                  decodeStateCodeChunk240 code
                else
                  if code < 3184049975559189735116160 then
                    decodeStateCodeChunk241 code
                  else
                    decodeStateCodeChunk242 code
              else
                if code < 3184073799089949231550848 then
                  decodeStateCodeChunk243 code
                else
                  if code < 3184077744082071828434304 then
                    decodeStateCodeChunk244 code
                  else
                    decodeStateCodeChunk245 code
            else
              if code < 3184902858606507997934976 then
                if code < 3184078515548429341166976 then
                  decodeStateCodeChunk246 code
                else
                  if code < 3184078538179856324923776 then
                    decodeStateCodeChunk247 code
                  else
                    decodeStateCodeChunk248 code
              else
                if code < 3184930525485270673395072 then
                  decodeStateCodeChunk249 code
                else
                  if code < 3185073440436717717796224 then
                    decodeStateCodeChunk250 code
                  else
                    decodeStateCodeChunk251 code
        else
          if code < 3191043800928723539064192 then
            if code < 3188001895908914326678272 then
              if code < 3187968595008939617372928 then
                if code < 3187967802333020635629312 then
                  decodeStateCodeChunk252 code
                else
                  decodeStateCodeChunk253 code
              else
                if code < 3187973329835679395129088 then
                  decodeStateCodeChunk254 code
                else
                  if code < 3188000974556974309648128 then
                    decodeStateCodeChunk255 code
                  else
                    decodeStateCodeChunk256 code
            else
              if code < 3190015707470210337061248 then
                if code < 3189025254656745017485056 then
                  decodeStateCodeChunk257 code
                else
                  if code < 3190014914693188583405952 then
                    decodeStateCodeChunk258 code
                  else
                    decodeStateCodeChunk259 code
              else
                if code < 3190044134000038563886464 then
                  decodeStateCodeChunk260 code
                else
                  if code < 3190048744416301668283776 then
                    decodeStateCodeChunk261 code
                  else
                    decodeStateCodeChunk262 code
          else
            if code < 3214464961670851373526528 then
              if code < 3208495412848905599150592 then
                if code < 3208466170913371380656640 then
                  decodeStateCodeChunk263 code
                else
                  if code < 3208470913557406772439552 then
                    decodeStateCodeChunk264 code
                  else
                    decodeStateCodeChunk265 code
              else
                if code < 3208637568557329294634496 then
                  decodeStateCodeChunk266 code
                else
                  if code < 3209327898188757298407936 then
                    decodeStateCodeChunk267 code
                  else
                    decodeStateCodeChunk268 code
            else
              if code < 3218705839187966293270272 then
                if code < 3215634688032429845850624 then
                  decodeStateCodeChunk269 code
                else
                  if code < 3218701097133542932611840 then
                    decodeStateCodeChunk270 code
                  else
                    decodeStateCodeChunk271 code
              else
                if code < 3218871682517880950883072 then
                  decodeStateCodeChunk272 code
                else
                  if code < 3218877184424139274583808 then
                    decodeStateCodeChunk273 code
                  else
                    decodeStateCodeChunk274 code
    else
      if code < 4069369145522276794939392 then
        if code < 3399835069047929486529024 then
          if code < 3331427061305877464752128 then
            if code < 3220924191381541735698816 then
              if code < 3220752794332838012194176 then
                if code < 3220748077259342821592448 then
                  decodeStateCodeChunk275 code
                else
                  decodeStateCodeChunk276 code
              else
                if code < 3220918658990356630868352 then
                  decodeStateCodeChunk277 code
                else
                  if code < 3220919452376738124534144 then
                    decodeStateCodeChunk278 code
                  else
                    decodeStateCodeChunk279 code
            else
              if code < 3226894529324322827827584 then
                if code < 3224699865293904510453504 then
                  decodeStateCodeChunk280 code
                else
                  if code < 3225870245569024882886400 then
                    decodeStateCodeChunk281 code
                  else
                    decodeStateCodeChunk282 code
              else
                if code < 3331256604498876417361920 then
                  decodeStateCodeChunk283 code
                else
                  if code < 3331289644590437815145472 then
                    decodeStateCodeChunk284 code
                  else
                    decodeStateCodeChunk285 code
          else
            if code < 3392665901742093794072064 then
              if code < 3337397312127157269504000 then
                if code < 3331455619561804084377600 then
                  decodeStateCodeChunk286 code
                else
                  if code < 3332284704671420051223552 then
                    decodeStateCodeChunk287 code
                  else
                    decodeStateCodeChunk288 code
              else
                if code < 3368102257782844139971584 then
                  decodeStateCodeChunk289 code
                else
                  if code < 3369158788263165533352960 then
                    decodeStateCodeChunk290 code
                  else
                    decodeStateCodeChunk291 code
            else
              if code < 3392841221848790523523584 then
                if code < 3392694459995199243323904 then
                  decodeStateCodeChunk292 code
                else
                  if code < 3392836479794367102398976 then
                    decodeStateCodeChunk293 code
                  else
                    decodeStateCodeChunk294 code
              else
                if code < 3392869783761345828662784 then
                  decodeStateCodeChunk295 code
                else
                  if code < 3398806837236755290489344 then
                    decodeStateCodeChunk296 code
                  else
                    decodeStateCodeChunk297 code
        else
          if code < 3406175026934601551711616 then
            if code < 3403957460811864791867136 then
              if code < 3402933974101766509790976 then
                if code < 3402900933381487246682880 then
                  decodeStateCodeChunk298 code
                else
                  decodeStateCodeChunk299 code
              else
                if code < 3403071512062478843597568 then
                  decodeStateCodeChunk300 code
                else
                  if code < 3403099949070782216897280 then
                    decodeStateCodeChunk301 code
                  else
                    decodeStateCodeChunk302 code
            else
              if code < 3405118364223136095572352 then
                if code < 3404947782514703863453056 then
                  decodeStateCodeChunk303 code
                else
                  if code < 3404976344423967450436992 then
                    decodeStateCodeChunk304 code
                  else
                    decodeStateCodeChunk305 code
              else
                if code < 3405123106260632796786048 then
                  decodeStateCodeChunk306 code
                else
                  if code < 3405151668189644213588352 then
                    decodeStateCodeChunk307 code
                  else
                    decodeStateCodeChunk308 code
          else
            if code < 3441997320965812213322112 then
              if code < 3429710694482620222287360 then
                if code < 3410065121544147629922048 then
                  decodeStateCodeChunk309 code
                else
                  if code < 3411121787369942228908416 then
                    decodeStateCodeChunk310 code
                  else
                    decodeStateCodeChunk311 code
              else
                if code < 3439632861961168656225024 then
                  decodeStateCodeChunk312 code
                else
                  if code < 3440826934055604533309184 then
                    decodeStateCodeChunk313 code
                  else
                    decodeStateCodeChunk314 code
            else
              if code < 4068345632505328928166912 then
                if code < 4068340875843276770399232 then
                  decodeStateCodeChunk315 code
                else
                  if code < 4068341007464980975463424 then
                    decodeStateCodeChunk316 code
                  else
                    decodeStateCodeChunk317 code
              else
                if code < 4068369477973509552294912 then
                  decodeStateCodeChunk318 code
                else
                  if code < 4068374195041349462387712 then
                    decodeStateCodeChunk319 code
                  else
                    decodeStateCodeChunk320 code
      else
        if code < 4508470337283364333978368 then
          if code < 4442085592308475463540736 then
            if code < 4327316622244029384308736 then
              if code < 4105215131255113349753856 then
                if code < 4073657489627039072326656 then
                  decodeStateCodeChunk321 code
                else
                  decodeStateCodeChunk322 code
              else
                if code < 4110507881902173650826240 then
                  decodeStateCodeChunk323 code
                else
                  if code < 4289448136800606478027776 then
                    decodeStateCodeChunk324 code
                  else
                    decodeStateCodeChunk325 code
            else
              if code < 4436825988921378874914816 then
                if code < 4436797449030407930640384 then
                  decodeStateCodeChunk326 code
                else
                  if code < 4436797580654932520017920 then
                    decodeStateCodeChunk327 code
                  else
                    decodeStateCodeChunk328 code
              else
                if code < 4436830618326062581413888 then
                  decodeStateCodeChunk329 code
                else
                  if code < 4437825655860786014751744 then
                    decodeStateCodeChunk330 code
                  else
                    decodeStateCodeChunk331 code
          else
            if code < 4498240040453770999451136 then
              if code < 4498206852897162979776000 then
                if code < 4473671642188406937851904 then
                  decodeStateCodeChunk332 code
                else
                  if code < 4478931227128344205787136 then
                    decodeStateCodeChunk333 code
                  else
                    decodeStateCodeChunk334 code
              else
                if code < 4498206984518867184840192 then
                  decodeStateCodeChunk335 code
                else
                  if code < 4498235411049087292952064 then
                    decodeStateCodeChunk336 code
                  else
                    decodeStateCodeChunk337 code
            else
              if code < 4508441734546593284776704 then
                if code < 4499211389738053052422656 then
                  decodeStateCodeChunk338 code
                else
                  if code < 4504347904694807979800064 then
                    decodeStateCodeChunk339 code
                  else
                    decodeStateCodeChunk340 code
              else
                if code < 4508441866171117874154240 then
                  decodeStateCodeChunk341 code
                else
                  if code < 4508446491208645442544384 then
                    decodeStateCodeChunk342 code
                  else
                    decodeStateCodeChunk343 code
        else
          if code < 4535085825258352853110272 then
            if code < 4510493494614270106909056 then
              if code < 4509470004242519545498368 then
                if code < 4508475053747486361078528 then
                  decodeStateCodeChunk344 code
                else
                  decodeStateCodeChunk345 code
              else
                if code < 4510488755603811578032512 then
                  decodeStateCodeChunk346 code
                else
                  if code < 4510488887124046888489344 then
                    decodeStateCodeChunk347 code
                  else
                    decodeStateCodeChunk348 code
            else
              if code < 4513729786522194469300992 then
                if code < 4510521924780979612692864 then
                  decodeStateCodeChunk349 code
                else
                  if code < 4511516962315794833685888 then
                    decodeStateCodeChunk350 code
                  else
                    decodeStateCodeChunk351 code
              else
                if code < 4514786446169986869185280 then
                  decodeStateCodeChunk352 code
                else
                  if code < 4516804995895003615159680 then
                    decodeStateCodeChunk353 code
                  else
                    decodeStateCodeChunk354 code
          else
            if code < 4719276842856854645822976 then
              if code < 4548390541338319638592896 then
                if code < 4545315968024313031557888 then
                  decodeStateCodeChunk355 code
                else
                  if code < 4547362948762293830922624 then
                    decodeStateCodeChunk356 code
                  else
                    decodeStateCodeChunk357 code
              else
                if code < 4657867420729133167091712 then
                  decodeStateCodeChunk358 code
                else
                  if code < 4663155323205803243091456 then
                    decodeStateCodeChunk359 code
                  else
                    decodeStateCodeChunk360 code
            else
              if code < 4731563465664140427442560 then
                if code < 4720333501909340672924160 then
                  decodeStateCodeChunk361 code
                else
                  if code < 4729540308474289787087616 then
                    decodeStateCodeChunk362 code
                  else
                    decodeStateCodeChunk363 code
              else
                if code < 4735823139410303560368384 then
                  decodeStateCodeChunk364 code
                else
                  if code < 4766385961231180565250816 then
                    decodeStateCodeChunk365 code
                  else
                    decodeStateCodeChunk366 code

def decodeState
    (vector : Fin 32 -> Fin 6) : Fin 11742 :=
  decodeStateCode (stateVectorCode vector)

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14268.Shards
