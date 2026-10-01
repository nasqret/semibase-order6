import SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.Shards.DecodeStatePart00
import SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.Shards.DecodeStatePart01

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.Shards

def stateVectorCode
    (vector : Fin 85 -> Fin 6) : Nat :=
  (vector (0 : Fin 85)).val + 6 * ((vector (1 : Fin 85)).val + 6 * ((vector (2 : Fin 85)).val + 6 * ((vector (3 : Fin 85)).val + 6 * ((vector (4 : Fin 85)).val + 6 * ((vector (5 : Fin 85)).val + 6 * ((vector (6 : Fin 85)).val + 6 * ((vector (7 : Fin 85)).val + 6 * ((vector (8 : Fin 85)).val + 6 * ((vector (9 : Fin 85)).val + 6 * ((vector (10 : Fin 85)).val + 6 * ((vector (11 : Fin 85)).val + 6 * ((vector (12 : Fin 85)).val + 6 * ((vector (13 : Fin 85)).val + 6 * ((vector (14 : Fin 85)).val + 6 * ((vector (15 : Fin 85)).val + 6 * ((vector (16 : Fin 85)).val + 6 * ((vector (17 : Fin 85)).val + 6 * ((vector (18 : Fin 85)).val + 6 * ((vector (19 : Fin 85)).val + 6 * ((vector (20 : Fin 85)).val + 6 * ((vector (21 : Fin 85)).val + 6 * ((vector (22 : Fin 85)).val + 6 * ((vector (23 : Fin 85)).val + 6 * ((vector (24 : Fin 85)).val + 6 * ((vector (25 : Fin 85)).val + 6 * ((vector (26 : Fin 85)).val + 6 * ((vector (27 : Fin 85)).val + 6 * ((vector (28 : Fin 85)).val + 6 * ((vector (29 : Fin 85)).val + 6 * ((vector (30 : Fin 85)).val + 6 * ((vector (31 : Fin 85)).val + 6 * ((vector (32 : Fin 85)).val + 6 * ((vector (33 : Fin 85)).val + 6 * ((vector (34 : Fin 85)).val + 6 * ((vector (35 : Fin 85)).val + 6 * ((vector (36 : Fin 85)).val + 6 * ((vector (37 : Fin 85)).val + 6 * ((vector (38 : Fin 85)).val + 6 * ((vector (39 : Fin 85)).val + 6 * ((vector (40 : Fin 85)).val + 6 * ((vector (41 : Fin 85)).val + 6 * ((vector (42 : Fin 85)).val + 6 * ((vector (43 : Fin 85)).val + 6 * ((vector (44 : Fin 85)).val + 6 * ((vector (45 : Fin 85)).val + 6 * ((vector (46 : Fin 85)).val + 6 * ((vector (47 : Fin 85)).val + 6 * ((vector (48 : Fin 85)).val + 6 * ((vector (49 : Fin 85)).val + 6 * ((vector (50 : Fin 85)).val + 6 * ((vector (51 : Fin 85)).val + 6 * ((vector (52 : Fin 85)).val + 6 * ((vector (53 : Fin 85)).val + 6 * ((vector (54 : Fin 85)).val + 6 * ((vector (55 : Fin 85)).val + 6 * ((vector (56 : Fin 85)).val + 6 * ((vector (57 : Fin 85)).val + 6 * ((vector (58 : Fin 85)).val + 6 * ((vector (59 : Fin 85)).val + 6 * ((vector (60 : Fin 85)).val + 6 * ((vector (61 : Fin 85)).val + 6 * ((vector (62 : Fin 85)).val + 6 * ((vector (63 : Fin 85)).val + 6 * ((vector (64 : Fin 85)).val + 6 * ((vector (65 : Fin 85)).val + 6 * ((vector (66 : Fin 85)).val + 6 * ((vector (67 : Fin 85)).val + 6 * ((vector (68 : Fin 85)).val + 6 * ((vector (69 : Fin 85)).val + 6 * ((vector (70 : Fin 85)).val + 6 * ((vector (71 : Fin 85)).val + 6 * ((vector (72 : Fin 85)).val + 6 * ((vector (73 : Fin 85)).val + 6 * ((vector (74 : Fin 85)).val + 6 * ((vector (75 : Fin 85)).val + 6 * ((vector (76 : Fin 85)).val + 6 * ((vector (77 : Fin 85)).val + 6 * ((vector (78 : Fin 85)).val + 6 * ((vector (79 : Fin 85)).val + 6 * ((vector (80 : Fin 85)).val + 6 * ((vector (81 : Fin 85)).val + 6 * ((vector (82 : Fin 85)).val + 6 * ((vector (83 : Fin 85)).val + 6 * ((vector (84 : Fin 85)).val))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

def decodeStateCode (code : Nat) : Fin 1447 :=
  if code < 4963609603078156103820788913346401375641521514904252328181760 then
    if code < 63340287225548293643744642662139344935400494858240 then
      if code < 525387317837847550830149507801562514194432 then
        if code < 39606513145327320186514925758933131853824 then
          if code < 33947816541270232238092185282022113017856 then
            decodeStateCodeChunk0 code
          else
            decodeStateCodeChunk1 code
        else
          if code < 174592516262072800067931423582262935945216 then
            decodeStateCodeChunk2 code
          else
            if code < 176210429646894680925740451221716296794112 then
              decodeStateCodeChunk3 code
            else
              decodeStateCodeChunk4 code
      else
        if code < 6353225557387803498230200973339181749108736 then
          if code < 698370063123371986379368800789636902289408 then
            decodeStateCodeChunk5 code
          else
            if code < 6286139559781228585795307573837191213744128 then
              decodeStateCodeChunk6 code
            else
              decodeStateCodeChunk7 code
        else
          if code < 6809122407577200180859007330033485033242624 then
            decodeStateCodeChunk8 code
          else
            if code < 12604607670846039497280380393106020744822784 then
              decodeStateCodeChunk9 code
            else
              decodeStateCodeChunk10 code
    else
      if code < 638816687611396952022115731932072120000996460513284063232 then
        if code < 492534069091517845907684775477150778999898014859919360 then
          if code < 380041726437784579353749849315068892838452910882816 then
            decodeStateCodeChunk11 code
          else
            if code < 13681501925662292625136561639477872502698267679653888 then
              decodeStateCodeChunk12 code
            else
              decodeStateCodeChunk13 code
        else
          if code < 17731226487298691940915320510034378980127275066591281152 then
            decodeStateCodeChunk14 code
          else
            if code < 106387358923716560373443883074374203200931483851773968384 then
              decodeStateCodeChunk15 code
            else
              decodeStateCodeChunk16 code
      else
        if code < 275756048391816934508774440014454550580660172634438951239680 then
          if code < 22979669907564495797037454662402286387916906828694005219328 then
            decodeStateCodeChunk17 code
          else
            if code < 137878030846638579525878484973828918966287551257178630258688 then
              decodeStateCodeChunk18 code
            else
              decodeStateCodeChunk19 code
        else
          if code < 827268185079831438561392873072609437991691186119427445751808 then
            decodeStateCodeChunk20 code
          else
            if code < 4963608617944918181642069967792537882218912815502022244564992 then
              decodeStateCodeChunk21 code
            else
              decodeStateCodeChunk22 code
  else
    if code < 38597020613139683778789454701031709765258775362137235473494441984 then
      if code < 178689927977243549975912029972145276226683091647449740670402560 then
        if code < 29781654662873924994418867103210941691108999463367942613237760 then
          if code < 14890826346497263661959059880211631811808942720670201884442624 then
            decodeStateCodeChunk23 code
          else
            decodeStateCodeChunk24 code
        else
          if code < 30608928758362585528130161318253409819338314220423783122993152 then
            decodeStateCodeChunk25 code
          else
            if code < 122435691391815025729664269900917893175823499036485653708668928 then
              decodeStateCodeChunk26 code
            else
              decodeStateCodeChunk27 code
      else
        if code < 6432837407194459564071236373659764409913198967607572401160716288 then
          if code < 1072139461476102327188630428843360286081904228004096903150043136 then
            decodeStateCodeChunk28 code
          else
            if code < 1077930338771662905352335487879167454538051267943184670568480768 then
              decodeStateCodeChunk29 code
            else
              decodeStateCodeChunk30 code
        else
          if code < 6616630098961717625669331936037213621931065990920382284545654784 then
            decodeStateCodeChunk31 code
          else
            if code < 7504976975044239361930309503503179442992510444293335950188085248 then
              decodeStateCodeChunk32 code
            else
              decodeStateCodeChunk33 code
    else
      if code < 231582973926706391528877230846469732006313223752400396392593358848 then
        if code < 39759336349509127155742215973855611167424830863060237292817874944 then
          if code < 38597024443166694337342181899536878869896061976132418614159474688 then
            decodeStateCodeChunk34 code
          else
            if code < 38775710541116927328765158302909321411349636302580919630978613248 then
              decodeStateCodeChunk35 code
            else
              decodeStateCodeChunk36 code
        else
          if code < 85235096248009161465234433472312807245290550727574074519413850112 then
            decodeStateCodeChunk37 code
          else
            if code < 231582146658507630195513182704901819920923327668606661344530268160 then
              decodeStateCodeChunk38 code
            else
              decodeStateCodeChunk39 code
      else
        if code < 348624041930104227353022904982399255952282129965281211151959457792 then
          if code < 232654263140314204999937691521101358068393943394328997176572641280 then
            decodeStateCodeChunk40 code
          else
            if code < 238014987895633329511453305535589510699360344599283562436177690624 then
              decodeStateCodeChunk41 code
            else
              decodeStateCodeChunk42 code
        else
          if code < 570103321966423511495832717779577783499051891862623296515622487201 then
            decodeStateCodeChunk43 code
          else
            if code < 1063919822239979030354629634523140323351951631550736551263701303296 then
              decodeStateCodeChunk44 code
            else
              decodeStateCodeChunk45 code

def decodeState
    (vector : Fin 85 -> Fin 6) : Fin 1447 :=
  decodeStateCode (stateVectorCode vector)

end SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3948.Shards
