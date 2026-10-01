import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.Shards.DecodeStatePart00
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.Shards.DecodeStatePart01
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.Shards.DecodeStatePart02
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.Shards.DecodeStatePart03
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.Shards.DecodeStatePart04
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.Shards.DecodeStatePart05
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.Shards.DecodeStatePart06
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.Shards.DecodeStatePart07

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.Shards

def stateVectorCode
    (vector : Fin 22 -> Fin 6) : Nat :=
  (vector (0 : Fin 22)).val + 6 * ((vector (1 : Fin 22)).val + 6 * ((vector (2 : Fin 22)).val + 6 * ((vector (3 : Fin 22)).val + 6 * ((vector (4 : Fin 22)).val + 6 * ((vector (5 : Fin 22)).val + 6 * ((vector (6 : Fin 22)).val + 6 * ((vector (7 : Fin 22)).val + 6 * ((vector (8 : Fin 22)).val + 6 * ((vector (9 : Fin 22)).val + 6 * ((vector (10 : Fin 22)).val + 6 * ((vector (11 : Fin 22)).val + 6 * ((vector (12 : Fin 22)).val + 6 * ((vector (13 : Fin 22)).val + 6 * ((vector (14 : Fin 22)).val + 6 * ((vector (15 : Fin 22)).val + 6 * ((vector (16 : Fin 22)).val + 6 * ((vector (17 : Fin 22)).val + 6 * ((vector (18 : Fin 22)).val + 6 * ((vector (19 : Fin 22)).val + 6 * ((vector (20 : Fin 22)).val + 6 * ((vector (21 : Fin 22)).val)))))))))))))))))))))

def decodeStateCode (code : Nat) : Fin 7782 :=
  if code < 1828172821671936 then
    if code < 31910540654592 then
      if code < 15190675531776 then
        if code < 3516591863808 then
          if code < 1017645742080 then
            if code < 420118990848 then
              if code < 80540946432 then
                decodeStateCodeChunk0 code
              else
                if code < 167612239872 then
                  decodeStateCodeChunk1 code
                else
                  decodeStateCodeChunk2 code
            else
              if code < 613852618752 then
                if code < 507190284288 then
                  decodeStateCodeChunk3 code
                else
                  decodeStateCodeChunk4 code
              else
                if code < 872889716736 then
                  decodeStateCodeChunk5 code
                else
                  decodeStateCodeChunk6 code
          else
            if code < 2968042715136 then
              if code < 2761248393216 then
                if code < 2421670348800 then
                  decodeStateCodeChunk7 code
                else
                  decodeStateCodeChunk8 code
              else
                if code < 2887501768704 then
                  decodeStateCodeChunk9 code
                else
                  decodeStateCodeChunk10 code
            else
              if code < 3307620759552 then
                if code < 3227079813120 then
                  decodeStateCodeChunk11 code
                else
                  decodeStateCodeChunk12 code
              else
                if code < 3388161705984 then
                  decodeStateCodeChunk13 code
                else
                  decodeStateCodeChunk14 code
        else
          if code < 8005117040640 then
            if code < 5395155019776 then
              if code < 3760391485440 then
                decodeStateCodeChunk15 code
              else
                if code < 5186183915520 then
                  decodeStateCodeChunk16 code
                else
                  decodeStateCodeChunk17 code
            else
              if code < 6057985241088 then
                if code < 5709700067328 then
                  decodeStateCodeChunk18 code
                else
                  decodeStateCodeChunk19 code
              else
                if code < 6203829657600 then
                  decodeStateCodeChunk20 code
                else
                  decodeStateCodeChunk21 code
          else
            if code < 14566241332224 then
              if code < 14198062786560 then
                if code < 14117521840128 then
                  decodeStateCodeChunk22 code
                else
                  decodeStateCodeChunk23 code
              else
                if code < 14287310862336 then
                  decodeStateCodeChunk24 code
                else
                  decodeStateCodeChunk25 code
            else
              if code < 14731374497760 then
                if code < 14646479947776 then
                  decodeStateCodeChunk26 code
                else
                  decodeStateCodeChunk27 code
              else
                if code < 14986057992192 then
                  decodeStateCodeChunk28 code
                else
                  decodeStateCodeChunk29 code
      else
        if code < 20232103421952 then
          if code < 17512213893120 then
            if code < 17005023608832 then
              if code < 16551164491776 then
                decodeStateCodeChunk30 code
              else
                if code < 16919343037440 then
                  decodeStateCodeChunk31 code
                else
                  decodeStateCodeChunk32 code
            else
              if code < 17344601653248 then
                if code < 17085564555264 then
                  decodeStateCodeChunk33 code
                else
                  decodeStateCodeChunk34 code
              else
                if code < 17425142599680 then
                  decodeStateCodeChunk35 code
                else
                  decodeStateCodeChunk36 code
          else
            if code < 19683554273280 then
              if code < 17933421275136 then
                if code < 17793018814464 then
                  decodeStateCodeChunk37 code
                else
                  decodeStateCodeChunk38 code
              else
                if code < 19343976228864 then
                  decodeStateCodeChunk39 code
                else
                  decodeStateCodeChunk40 code
            else
              if code < 19892525377536 then
                if code < 19785863043072 then
                  decodeStateCodeChunk41 code
                else
                  decodeStateCodeChunk42 code
              else
                if code < 20151562475520 then
                  decodeStateCodeChunk43 code
                else
                  decodeStateCodeChunk44 code
        else
          if code < 23128312320000 then
            if code < 22104136230912 then
              if code < 20441074526208 then
                if code < 20312644368384 then
                  decodeStateCodeChunk45 code
                else
                  decodeStateCodeChunk46 code
              else
                if code < 20680520583168 then
                  decodeStateCodeChunk47 code
                else
                  decodeStateCodeChunk48 code
            else
              if code < 22634182729728 then
                if code < 22271748470784 then
                  decodeStateCodeChunk49 code
                else
                  decodeStateCodeChunk50 code
              else
                if code < 22975937556480 then
                  decodeStateCodeChunk51 code
                else
                  decodeStateCodeChunk52 code
          else
            if code < 31205263177728 then
              if code < 31037650937856 then
                if code < 24920892573696 then
                  decodeStateCodeChunk53 code
                else
                  decodeStateCodeChunk54 code
              else
                if code < 31122545448960 then
                  decodeStateCodeChunk55 code
                else
                  decodeStateCodeChunk56 code
            else
              if code < 31570962610176 then
                if code < 31490723994624 then
                  decodeStateCodeChunk57 code
                else
                  decodeStateCodeChunk58 code
              else
                if code < 31651503556608 then
                  decodeStateCodeChunk59 code
                else
                  decodeStateCodeChunk60 code
    else
      if code < 319344852602880 then
        if code < 90277693820928 then
          if code < 48104712843264 then
            if code < 33841648917504 then
              if code < 32067268982784 then
                decodeStateCodeChunk61 code
              else
                if code < 33473470371840 then
                  decodeStateCodeChunk62 code
                else
                  decodeStateCodeChunk63 code
            else
              if code < 36739732267008 then
                if code < 34325680656384 then
                  decodeStateCodeChunk64 code
                else
                  decodeStateCodeChunk65 code
              else
                if code < 37233861857280 then
                  decodeStateCodeChunk66 code
                else
                  decodeStateCodeChunk67 code
          else
            if code < 85284155142144 then
              if code < 84748666687488 then
                if code < 48833934925824 then
                  decodeStateCodeChunk68 code
                else
                  decodeStateCodeChunk69 code
              else
                if code < 85114366119936 then
                  decodeStateCodeChunk70 code
                else
                  decodeStateCodeChunk71 code
            else
              if code < 87863642210304 then
                if code < 87524064165888 then
                  decodeStateCodeChunk72 code
                else
                  decodeStateCodeChunk73 code
              else
                if code < 88029077667840 then
                  decodeStateCodeChunk74 code
                else
                  decodeStateCodeChunk75 code
        else
          if code < 305631123886080 then
            if code < 99143728275456 then
              if code < 90811005493248 then
                decodeStateCodeChunk76 code
              else
                if code < 98804151630720 then
                  decodeStateCodeChunk77 code
                else
                  decodeStateCodeChunk78 code
            else
              if code < 99677402744831 then
                if code < 99304810168320 then
                  decodeStateCodeChunk79 code
                else
                  decodeStateCodeChunk80 code
              else
                if code < 305150054989824 then
                  decodeStateCodeChunk81 code
                else
                  decodeStateCodeChunk82 code
          else
            if code < 309864965529600 then
              if code < 307590227988480 then
                if code < 307111335874560 then
                  decodeStateCodeChunk83 code
                else
                  decodeStateCodeChunk84 code
              else
                if code < 308064766537728 then
                  decodeStateCodeChunk85 code
                else
                  decodeStateCodeChunk86 code
            else
              if code < 312683898654720 then
                if code < 310387393290240 then
                  decodeStateCodeChunk87 code
                else
                  decodeStateCodeChunk88 code
              else
                if code < 318865960488960 then
                  decodeStateCodeChunk89 code
                else
                  decodeStateCodeChunk90 code
      else
        if code < 340949417287680 then
          if code < 325041491976192 then
            if code < 322094128693248 then
              if code < 321140698030080 then
                decodeStateCodeChunk91 code
              else
                if code < 321619590144000 then
                  decodeStateCodeChunk92 code
                else
                  decodeStateCodeChunk93 code
            else
              if code < 324059763142656 then
                if code < 322623086800896 then
                  decodeStateCodeChunk94 code
                else
                  decodeStateCodeChunk95 code
              else
                if code < 324534301691904 then
                  decodeStateCodeChunk96 code
                else
                  decodeStateCodeChunk97 code
          else
            if code < 335814387757056 then
              if code < 327340174123008 then
                if code < 326815569580032 then
                  decodeStateCodeChunk98 code
                else
                  decodeStateCodeChunk99 code
              else
                if code < 329675861569536 then
                  decodeStateCodeChunk100 code
                else
                  decodeStateCodeChunk101 code
            else
              if code < 338089125298176 then
                if code < 336288926306304 then
                  decodeStateCodeChunk102 code
                else
                  decodeStateCodeChunk103 code
              else
                if code < 338613729841152 then
                  decodeStateCodeChunk104 code
                else
                  decodeStateCodeChunk105 code
        else
          if code < 392282298335232 then
            if code < 389339288616960 then
              if code < 343851068141568 then
                if code < 341835367698432 then
                  decodeStateCodeChunk106 code
                else
                  decodeStateCodeChunk107 code
              else
                if code < 353200348274688 then
                  decodeStateCodeChunk108 code
                else
                  decodeStateCodeChunk109 code
            else
              if code < 390344962056192 then
                if code < 389820357513216 then
                  decodeStateCodeChunk110 code
                else
                  decodeStateCodeChunk111 code
              else
                if code < 391807759785984 then
                  decodeStateCodeChunk112 code
                else
                  decodeStateCodeChunk113 code
          else
            if code < 397397736824832 then
              if code < 394561397839104 then
                if code < 393074647105536 then
                  decodeStateCodeChunk114 code
                else
                  decodeStateCodeChunk115 code
              else
                if code < 395101231460352 then
                  decodeStateCodeChunk116 code
                else
                  decodeStateCodeChunk117 code
            else
              if code < 404036924349312 then
                if code < 403562385800064 then
                  decodeStateCodeChunk118 code
                else
                  decodeStateCodeChunk119 code
              else
                if code < 405837123341184 then
                  decodeStateCodeChunk120 code
                else
                  decodeStateCodeChunk121 code
  else
    if code < 10999729560969216 then
      if code < 1913585406971904 then
        if code < 1847850933989376 then
          if code < 1834204685524992 then
            if code < 1830902506721280 then
              if code < 1828651713785856 then
                decodeStateCodeChunk122 code
              else
                if code < 1829435355426816 then
                  decodeStateCodeChunk123 code
                else
                  decodeStateCodeChunk124 code
            else
              if code < 1831864644513792 then
                if code < 1831381398835200 then
                  decodeStateCodeChunk125 code
                else
                  decodeStateCodeChunk126 code
              else
                if code < 1833421043884032 then
                  decodeStateCodeChunk127 code
                else
                  decodeStateCodeChunk128 code
          else
            if code < 1844694599602176 then
              if code < 1842657131335680 then
                if code < 1836488130195456 then
                  decodeStateCodeChunk129 code
                else
                  decodeStateCodeChunk130 code
              else
                if code < 1843138200231936 then
                  decodeStateCodeChunk131 code
                else
                  decodeStateCodeChunk132 code
            else
              if code < 1845656737394688 then
                if code < 1845175668498432 then
                  decodeStateCodeChunk133 code
                else
                  decodeStateCodeChunk134 code
              else
                if code < 1847372041875456 then
                  decodeStateCodeChunk135 code
                else
                  decodeStateCodeChunk136 code
        else
          if code < 1860143223840768 then
            if code < 1850580619038720 then
              if code < 1848377715314688 then
                decodeStateCodeChunk137 code
              else
                if code < 1848869668122624 then
                  decodeStateCodeChunk138 code
                else
                  decodeStateCodeChunk139 code
            else
              if code < 1859126666489856 then
                if code < 1851209709133824 then
                  decodeStateCodeChunk140 code
                else
                  decodeStateCodeChunk141 code
              else
                if code < 1859605558603776 then
                  decodeStateCodeChunk142 code
                else
                  decodeStateCodeChunk143 code
          else
            if code < 1865639599239168 then
              if code < 1862483264851968 then
                if code < 1861856351539200 then
                  decodeStateCodeChunk144 code
                else
                  decodeStateCodeChunk145 code
              else
                if code < 1864766709522432 then
                  decodeStateCodeChunk146 code
                else
                  decodeStateCodeChunk147 code
            else
              if code < 1878480438239232 then
                if code < 1876432086061056 then
                  decodeStateCodeChunk148 code
                else
                  decodeStateCodeChunk149 code
              else
                if code < 1913106514857984 then
                  decodeStateCodeChunk150 code
                else
                  decodeStateCodeChunk151 code
      else
        if code < 10971936404103168 then
          if code < 1926898607738880 then
            if code < 1916097413787648 then
              if code < 1915143983124480 then
                decodeStateCodeChunk152 code
              else
                if code < 1915622875238400 then
                  decodeStateCodeChunk153 code
                else
                  decodeStateCodeChunk154 code
            else
              if code < 1918300317511680 then
                if code < 1916878878646272 then
                  decodeStateCodeChunk155 code
                else
                  decodeStateCodeChunk156 code
              else
                if code < 1919218919657472 then
                  decodeStateCodeChunk157 code
                else
                  decodeStateCodeChunk158 code
          else
            if code < 10968932444479488 then
              if code < 1928152434364416 then
                if code < 1927377500086080 then
                  decodeStateCodeChunk159 code
                else
                  decodeStateCodeChunk160 code
              else
                if code < 1929576050012160 then
                  decodeStateCodeChunk161 code
                else
                  decodeStateCodeChunk162 code
            else
              if code < 10970969912745984 then
                if code < 10969415690158080 then
                  decodeStateCodeChunk163 code
                else
                  decodeStateCodeChunk164 code
              else
                if code < 10971453158424576 then
                  decodeStateCodeChunk165 code
                else
                  decodeStateCodeChunk166 code
        else
          if code < 10985898286006272 then
            if code < 10982724537360384 then
              if code < 10974182843473920 then
                if code < 10973660415713280 then
                  decodeStateCodeChunk167 code
                else
                  decodeStateCodeChunk168 code
              else
                if code < 10976468464926720 then
                  decodeStateCodeChunk169 code
                else
                  decodeStateCodeChunk170 code
            else
              if code < 10984931794649088 then
                if code < 10983207783038976 then
                  decodeStateCodeChunk171 code
                else
                  decodeStateCodeChunk172 code
              else
                if code < 10985415040327680 then
                  decodeStateCodeChunk173 code
                else
                  decodeStateCodeChunk174 code
          else
            if code < 10989098156040192 then
              if code < 10987974936354816 then
                if code < 10986420713766912 then
                  decodeStateCodeChunk175 code
                else
                  decodeStateCodeChunk176 code
              else
                if code < 10988614910361600 then
                  decodeStateCodeChunk177 code
                else
                  decodeStateCodeChunk178 code
            else
              if code < 10991187867082752 then
                if code < 10990652378628096 then
                  decodeStateCodeChunk179 code
                else
                  decodeStateCodeChunk180 code
              else
                if code < 10993473488535552 then
                  decodeStateCodeChunk181 code
                else
                  decodeStateCodeChunk182 code
    else
      if code < 65816047900569600 then
        if code < 11059155718742016 then
          if code < 11017048041234432 then
            if code < 11002420063936512 then
              if code < 11000369534976000 then
                decodeStateCodeChunk183 code
              else
                if code < 11001923757563904 then
                  decodeStateCodeChunk184 code
                else
                  decodeStateCodeChunk185 code
            else
              if code < 11005619933970432 then
                if code < 11004744867471360 then
                  decodeStateCodeChunk186 code
                else
                  decodeStateCodeChunk187 code
              else
                if code < 11007905555423232 then
                  decodeStateCodeChunk188 code
                else
                  decodeStateCodeChunk189 code
          else
            if code < 11055864423849984 then
              if code < 11053657166561280 then
                if code < 11053173920882688 then
                  decodeStateCodeChunk190 code
                else
                  decodeStateCodeChunk191 code
              else
                if code < 11054192655015936 then
                  decodeStateCodeChunk192 code
                else
                  decodeStateCodeChunk193 code
            else
              if code < 11056857036595200 then
                if code < 11056347669528576 then
                  decodeStateCodeChunk194 code
                else
                  decodeStateCodeChunk195 code
              else
                if code < 11058385137795072 then
                  decodeStateCodeChunk196 code
                else
                  decodeStateCodeChunk197 code
        else
          if code < 65811417884540928 then
            if code < 11068102294142976 then
              if code < 11061245429784576 then
                decodeStateCodeChunk198 code
              else
                if code < 11067619048464384 then
                  decodeStateCodeChunk199 code
                else
                  decodeStateCodeChunk200 code
            else
              if code < 65810917224603648 then
                if code < 11069656516730880 then
                  decodeStateCodeChunk201 code
                else
                  decodeStateCodeChunk202 code
              else
                if code < 65811256802648064 then
                  decodeStateCodeChunk203 code
                else
                  decodeStateCodeChunk204 code
          else
            if code < 65813749218422784 then
              if code < 65813215906750464 then
                if code < 65811790114320384 then
                  decodeStateCodeChunk205 code
                else
                  decodeStateCodeChunk206 code
              else
                if code < 65813424877854720 then
                  decodeStateCodeChunk207 code
                else
                  decodeStateCodeChunk208 code
            else
              if code < 65814249878360064 then
                if code < 65814088796467200 then
                  decodeStateCodeChunk209 code
                else
                  decodeStateCodeChunk210 code
              else
                if code < 65814624284921856 then
                  decodeStateCodeChunk211 code
                else
                  decodeStateCodeChunk212 code
      else
        if code < 65847058341728256 then
          if code < 65830532210233344 then
            if code < 65828207406698496 then
              if code < 65816415776784384 then
                decodeStateCodeChunk213 code
              else
                if code < 65827861298307072 then
                  decodeStateCodeChunk214 code
                else
                  decodeStateCodeChunk215 code
            else
              if code < 65828742895153152 then
                if code < 65828394609979392 then
                  decodeStateCodeChunk216 code
                else
                  decodeStateCodeChunk217 code
              else
                if code < 65830166510800896 then
                  decodeStateCodeChunk218 code
                else
                  decodeStateCodeChunk219 code
          else
            if code < 65831616247836672 then
              if code < 65831061168340992 then
                if code < 65830693292126208 then
                  decodeStateCodeChunk220 code
                else
                  decodeStateCodeChunk221 code
              else
                if code < 65831226603798528 then
                  decodeStateCodeChunk222 code
                else
                  decodeStateCodeChunk223 code
            else
              if code < 65833359850487808 then
                if code < 65833020272443392 then
                  decodeStateCodeChunk224 code
                else
                  decodeStateCodeChunk225 code
              else
                if code < 65845121005449216 then
                  decodeStateCodeChunk226 code
                else
                  decodeStateCodeChunk227 code
        else
          if code < 65897912339059968 then
            if code < 65895580996780032 then
              if code < 65848085782990848 then
                if code < 65847591653400576 then
                  decodeStateCodeChunk228 code
                else
                  decodeStateCodeChunk229 code
              else
                if code < 65850023119269888 then
                  decodeStateCodeChunk230 code
                else
                  decodeStateCodeChunk231 code
            else
              if code < 65896114308452352 then
                if code < 65895953234964048 then
                  decodeStateCodeChunk232 code
                else
                  decodeStateCodeChunk233 code
              else
                if code < 65896503952490496 then
                  decodeStateCodeChunk234 code
                else
                  decodeStateCodeChunk235 code
          else
            if code < 65898948479053824 then
              if code < 65898412990599168 then
                if code < 65898251908706304 then
                  decodeStateCodeChunk236 code
                else
                  decodeStateCodeChunk237 code
              else
                if code < 65898780866813952 then
                  decodeStateCodeChunk238 code
                else
                  decodeStateCodeChunk239 code
            else
              if code < 65900739970916352 then
                if code < 65899338123091968 then
                  decodeStateCodeChunk240 code
                else
                  decodeStateCodeChunk241 code
              else
                if code < 65901086079307776 then
                  decodeStateCodeChunk242 code
                else
                  decodeStateCodeChunk243 code

def decodeState
    (vector : Fin 22 -> Fin 6) : Fin 7782 :=
  decodeStateCode (stateVectorCode vector)

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.Shards
