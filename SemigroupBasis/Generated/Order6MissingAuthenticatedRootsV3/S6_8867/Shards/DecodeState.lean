import SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.Shards.DecodeStatePart00
import SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.Shards.DecodeStatePart01
import SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.Shards.DecodeStatePart02

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.Shards

def stateVectorCode
    (vector : Fin 29 -> Fin 6) : Nat :=
  (vector (0 : Fin 29)).val + 6 * ((vector (1 : Fin 29)).val + 6 * ((vector (2 : Fin 29)).val + 6 * ((vector (3 : Fin 29)).val + 6 * ((vector (4 : Fin 29)).val + 6 * ((vector (5 : Fin 29)).val + 6 * ((vector (6 : Fin 29)).val + 6 * ((vector (7 : Fin 29)).val + 6 * ((vector (8 : Fin 29)).val + 6 * ((vector (9 : Fin 29)).val + 6 * ((vector (10 : Fin 29)).val + 6 * ((vector (11 : Fin 29)).val + 6 * ((vector (12 : Fin 29)).val + 6 * ((vector (13 : Fin 29)).val + 6 * ((vector (14 : Fin 29)).val + 6 * ((vector (15 : Fin 29)).val + 6 * ((vector (16 : Fin 29)).val + 6 * ((vector (17 : Fin 29)).val + 6 * ((vector (18 : Fin 29)).val + 6 * ((vector (19 : Fin 29)).val + 6 * ((vector (20 : Fin 29)).val + 6 * ((vector (21 : Fin 29)).val + 6 * ((vector (22 : Fin 29)).val + 6 * ((vector (23 : Fin 29)).val + 6 * ((vector (24 : Fin 29)).val + 6 * ((vector (25 : Fin 29)).val + 6 * ((vector (26 : Fin 29)).val + 6 * ((vector (27 : Fin 29)).val + 6 * ((vector (28 : Fin 29)).val))))))))))))))))))))))))))))

def decodeStateCode (code : Nat) : Fin 2712 :=
  if code < 27634648642357303443456 then
    if code < 21863431083066445246464 then
      if code < 21834891110296374349824 then
        if code < 21517420327969995251712 then
          if code < 21493841000477293412352 then
            if code < 21493728370498408833024 then
              decodeStateCodeChunk0 code
            else
              decodeStateCodeChunk1 code
          else
            if code < 21498444098311133039616 then
              decodeStateCodeChunk2 code
            else
              if code < 21498579381815635184640 then
                decodeStateCodeChunk3 code
              else
                decodeStateCodeChunk4 code
        else
          if code < 21522293225471649779712 then
            if code < 21522157947687731613696 then
              decodeStateCodeChunk5 code
            else
              decodeStateCodeChunk6 code
          else
            if code < 21545828673473093824512 then
              decodeStateCodeChunk7 code
            else
              if code < 21659688048849841078272 then
                decodeStateCodeChunk8 code
              else
                decodeStateCodeChunk9 code
      else
        if code < 21835816118854072049664 then
          if code < 21835026388158656679936 then
            if code < 21835001511598432038912 then
              decodeStateCodeChunk10 code
            else
              decodeStateCodeChunk11 code
          else
            if code < 21835680840991789719552 then
              decodeStateCodeChunk12 code
            else
              if code < 21835791242291670626304 then
                decodeStateCodeChunk13 code
              else
                decodeStateCodeChunk14 code
        else
          if code < 21840551554950768061440 then
            if code < 21839739887293828402176 then
              decodeStateCodeChunk15 code
            else
              if code < 21840398001925444537344 then
                decodeStateCodeChunk16 code
              else
                decodeStateCodeChunk17 code
          else
            if code < 21858693463427073048576 then
              decodeStateCodeChunk18 code
            else
              if code < 21859482584760571625472 then
                decodeStateCodeChunk19 code
              else
                decodeStateCodeChunk20 code
    else
      if code < 22545736668311403958272 then
        if code < 21887934809754927992832 then
          if code < 21864224571478080565248 then
            if code < 21864089197778602328064 then
              decodeStateCodeChunk21 code
            else
              decodeStateCodeChunk22 code
          else
            if code < 21868173227765403565056 then
              decodeStateCodeChunk23 code
            else
              if code < 21886992028272293572608 then
                decodeStateCodeChunk24 code
              else
                decodeStateCodeChunk25 code
        else
          if code < 22517196701052945936384 then
            if code < 21982684003612728155136 then
              decodeStateCodeChunk26 code
            else
              decodeStateCodeChunk27 code
          else
            if code < 22517309427001810145280 then
              decodeStateCodeChunk28 code
            else
              if code < 22522044152180986260480 then
                decodeStateCodeChunk29 code
              else
                decodeStateCodeChunk30 code
      else
        if code < 22863097929390704114688 then
          if code < 22858381479360803060736 then
            if code < 22659724110871894404096 then
              decodeStateCodeChunk31 code
            else
              decodeStateCodeChunk32 code
          else
            if code < 22858516757223085390848 then
              decodeStateCodeChunk33 code
            else
              if code < 22859171819413781658624 then
                decodeStateCodeChunk34 code
              else
                decodeStateCodeChunk35 code
        else
          if code < 22887583217293947816960 then
            if code < 22863888263801462897664 then
              decodeStateCodeChunk36 code
            else
              if code < 22886790445520416373760 then
                decodeStateCodeChunk37 code
              else
                decodeStateCodeChunk38 code
          else
            if code < 22891641558371457850368 then
              decodeStateCodeChunk39 code
            else
              if code < 23001457928380880329728 then
                decodeStateCodeChunk40 code
              else
                decodeStateCodeChunk41 code
  else
    if code < 28691417281041220672512 then
      if code < 28009137999838099774464 then
        if code < 27975968704183449000960 then
          if code < 27639522324126806805504 then
            if code < 27634783925861805588480 then
              decodeStateCodeChunk42 code
            else
              decodeStateCodeChunk43 code
          else
            if code < 27667817328731324120064 then
              decodeStateCodeChunk44 code
            else
              if code < 27975834035680906681344 then
                decodeStateCodeChunk45 code
              else
                decodeStateCodeChunk46 code
        else
          if code < 27980685165484728990720 then
            if code < 27976736503085021346816 then
              decodeStateCodeChunk47 code
            else
              decodeStateCodeChunk48 code
          else
            if code < 27981493785872783612928 then
              decodeStateCodeChunk49 code
            else
              if code < 28005032122690772892672 then
                decodeStateCodeChunk50 code
              else
                decodeStateCodeChunk51 code
      else
        if code < 28658142673236178320384 then
          if code < 28150499699898791537664 then
            if code < 28150342479428411538432 then
              decodeStateCodeChunk52 code
            else
              decodeStateCodeChunk53 code
          else
            if code < 28178908045323525946368 then
              decodeStateCodeChunk54 code
            else
              if code < 28658138915517781588992 then
                decodeStateCodeChunk55 code
              else
                decodeStateCodeChunk56 code
        else
          if code < 28662902906891843091456 then
            if code < 28658252250826385808384 then
              decodeStateCodeChunk57 code
            else
              if code < 28658295622530920954880 then
                decodeStateCodeChunk58 code
              else
                decodeStateCodeChunk59 code
          else
            if code < 28686569299543812307968 then
              decodeStateCodeChunk60 code
            else
              if code < 28686703866408033795072 then
                decodeStateCodeChunk61 code
              else
                decodeStateCodeChunk62 code
    else
      if code < 29004987100178112334848 then
        if code < 29000095143258648628224 then
          if code < 28999306028035378068480 then
            if code < 28805404723602053760000 then
              decodeStateCodeChunk63 code
            else
              decodeStateCodeChunk64 code
          else
            if code < 28999412056669321976832 then
              decodeStateCodeChunk65 code
            else
              if code < 28999437751299177004032 then
                decodeStateCodeChunk66 code
              else
                decodeStateCodeChunk67 code
        else
          if code < 29004040871701875735552 then
            if code < 29000117080209289006080 then
              decodeStateCodeChunk68 code
            else
              if code < 29000226866520270781440 then
                decodeStateCodeChunk69 code
              else
                decodeStateCodeChunk70 code
          else
            if code < 29004175438644461386752 then
              decodeStateCodeChunk71 code
            else
              if code < 29004834252441149586432 then
                decodeStateCodeChunk72 code
              else
                decodeStateCodeChunk73 code
      else
        if code < 29033395552815181544448 then
          if code < 29028522486126022327296 then
            if code < 29027758247373728332800 then
              decodeStateCodeChunk74 code
            else
              decodeStateCodeChunk75 code
          else
            if code < 29028657052992420596736 then
              decodeStateCodeChunk76 code
            else
              if code < 29032580743042596903936 then
                decodeStateCodeChunk77 code
              else
                decodeStateCodeChunk78 code
        else
          if code < 29349152980593385466880 then
            if code < 29142400243933290728448 then
              decodeStateCodeChunk79 code
            else
              if code < 29344418238486844468224 then
                decodeStateCodeChunk80 code
              else
                decodeStateCodeChunk81 code
          else
            if code < 29372954653967929049664 then
              decodeStateCodeChunk82 code
            else
              if code < 34314976686158482157568 then
                decodeStateCodeChunk83 code
              else
                decodeStateCodeChunk84 code

def decodeState
    (vector : Fin 29 -> Fin 6) : Fin 2712 :=
  decodeStateCode (stateVectorCode vector)

end SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.Shards
