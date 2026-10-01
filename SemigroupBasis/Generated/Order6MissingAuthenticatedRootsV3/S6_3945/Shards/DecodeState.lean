import SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3945.Shards.DecodeStatePart00
import SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3945.Shards.DecodeStatePart01

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3945.Shards

def stateVectorCode
    (vector : Fin 93 -> Fin 6) : Nat :=
  (vector (0 : Fin 93)).val + 6 * ((vector (1 : Fin 93)).val + 6 * ((vector (2 : Fin 93)).val + 6 * ((vector (3 : Fin 93)).val + 6 * ((vector (4 : Fin 93)).val + 6 * ((vector (5 : Fin 93)).val + 6 * ((vector (6 : Fin 93)).val + 6 * ((vector (7 : Fin 93)).val + 6 * ((vector (8 : Fin 93)).val + 6 * ((vector (9 : Fin 93)).val + 6 * ((vector (10 : Fin 93)).val + 6 * ((vector (11 : Fin 93)).val + 6 * ((vector (12 : Fin 93)).val + 6 * ((vector (13 : Fin 93)).val + 6 * ((vector (14 : Fin 93)).val + 6 * ((vector (15 : Fin 93)).val + 6 * ((vector (16 : Fin 93)).val + 6 * ((vector (17 : Fin 93)).val + 6 * ((vector (18 : Fin 93)).val + 6 * ((vector (19 : Fin 93)).val + 6 * ((vector (20 : Fin 93)).val + 6 * ((vector (21 : Fin 93)).val + 6 * ((vector (22 : Fin 93)).val + 6 * ((vector (23 : Fin 93)).val + 6 * ((vector (24 : Fin 93)).val + 6 * ((vector (25 : Fin 93)).val + 6 * ((vector (26 : Fin 93)).val + 6 * ((vector (27 : Fin 93)).val + 6 * ((vector (28 : Fin 93)).val + 6 * ((vector (29 : Fin 93)).val + 6 * ((vector (30 : Fin 93)).val + 6 * ((vector (31 : Fin 93)).val + 6 * ((vector (32 : Fin 93)).val + 6 * ((vector (33 : Fin 93)).val + 6 * ((vector (34 : Fin 93)).val + 6 * ((vector (35 : Fin 93)).val + 6 * ((vector (36 : Fin 93)).val + 6 * ((vector (37 : Fin 93)).val + 6 * ((vector (38 : Fin 93)).val + 6 * ((vector (39 : Fin 93)).val + 6 * ((vector (40 : Fin 93)).val + 6 * ((vector (41 : Fin 93)).val + 6 * ((vector (42 : Fin 93)).val + 6 * ((vector (43 : Fin 93)).val + 6 * ((vector (44 : Fin 93)).val + 6 * ((vector (45 : Fin 93)).val + 6 * ((vector (46 : Fin 93)).val + 6 * ((vector (47 : Fin 93)).val + 6 * ((vector (48 : Fin 93)).val + 6 * ((vector (49 : Fin 93)).val + 6 * ((vector (50 : Fin 93)).val + 6 * ((vector (51 : Fin 93)).val + 6 * ((vector (52 : Fin 93)).val + 6 * ((vector (53 : Fin 93)).val + 6 * ((vector (54 : Fin 93)).val + 6 * ((vector (55 : Fin 93)).val + 6 * ((vector (56 : Fin 93)).val + 6 * ((vector (57 : Fin 93)).val + 6 * ((vector (58 : Fin 93)).val + 6 * ((vector (59 : Fin 93)).val + 6 * ((vector (60 : Fin 93)).val + 6 * ((vector (61 : Fin 93)).val + 6 * ((vector (62 : Fin 93)).val + 6 * ((vector (63 : Fin 93)).val + 6 * ((vector (64 : Fin 93)).val + 6 * ((vector (65 : Fin 93)).val + 6 * ((vector (66 : Fin 93)).val + 6 * ((vector (67 : Fin 93)).val + 6 * ((vector (68 : Fin 93)).val + 6 * ((vector (69 : Fin 93)).val + 6 * ((vector (70 : Fin 93)).val + 6 * ((vector (71 : Fin 93)).val + 6 * ((vector (72 : Fin 93)).val + 6 * ((vector (73 : Fin 93)).val + 6 * ((vector (74 : Fin 93)).val + 6 * ((vector (75 : Fin 93)).val + 6 * ((vector (76 : Fin 93)).val + 6 * ((vector (77 : Fin 93)).val + 6 * ((vector (78 : Fin 93)).val + 6 * ((vector (79 : Fin 93)).val + 6 * ((vector (80 : Fin 93)).val + 6 * ((vector (81 : Fin 93)).val + 6 * ((vector (82 : Fin 93)).val + 6 * ((vector (83 : Fin 93)).val + 6 * ((vector (84 : Fin 93)).val + 6 * ((vector (85 : Fin 93)).val + 6 * ((vector (86 : Fin 93)).val + 6 * ((vector (87 : Fin 93)).val + 6 * ((vector (88 : Fin 93)).val + 6 * ((vector (89 : Fin 93)).val + 6 * ((vector (90 : Fin 93)).val + 6 * ((vector (91 : Fin 93)).val + 6 * ((vector (92 : Fin 93)).val))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

def decodeStateCode (code : Nat) : Fin 1447 :=
  if code < 1871960468505680670190499499171380820809157317851587677076534067200 then
    if code < 17731226487286359054212667121086722194195127454325014528 then
      if code < 879726203989190513795936863171475639823803351040 then
        if code < 174592497982210242797852781048413332439040 then
          if code < 92144066112213001815625660251054205304832 then
            decodeStateCodeChunk0 code
          else
            decodeStateCodeChunk1 code
        else
          if code < 174861933763590290070957994677809235099648 then
            decodeStateCodeChunk2 code
          else
            if code < 356455785886142314165305622527555403776000 then
              decodeStateCodeChunk3 code
            else
              decodeStateCodeChunk4 code
      else
        if code < 2955204465460905343777435776917397571400475333604933632 then
          if code < 1172993412946060033902120688325681046019299606528 then
            decodeStateCodeChunk5 code
          else
            if code < 2955204464782103989102329578903588024473255600170467328 then
              decodeStateCodeChunk6 code
            else
              decodeStateCodeChunk7 code
        else
          if code < 2955204515010241538315061218039747334641690115657695232 then
            decodeStateCodeChunk8 code
          else
            if code < 5910408928200412760909625053980027848879448002272428032 then
              decodeStateCodeChunk9 code
            else
              decodeStateCodeChunk10 code
    else
      if code < 6432836786588220492137813932224371711462606835982037968830332928 then
        if code < 827271058195285852324057967512467585667510569730643154960384 then
          if code < 3829944921253795249533471013230744339951665330230338256896 then
            decodeStateCodeChunk11 code
          else
            if code < 22983117266057318576015661376763763228060651525648804741120 then
              decodeStateCodeChunk12 code
            else
              decodeStateCodeChunk13 code
        else
          if code < 4963608617944918181523450904983967066990461391679778919022592 then
            decodeStateCodeChunk14 code
          else
            if code < 178689913201221569541678865292646148661425544544854188348145664 then
              decodeStateCodeChunk15 code
            else
              decodeStateCodeChunk16 code
      else
        if code < 231582124317162258854233280750821399027176506038514824725531721728 then
          if code < 38597020619050092658116232323179456316006177218355890062765326336 then
            decodeStateCodeChunk17 code
          else
            if code < 39669160186915834159344371329601400286987278433256408470391881728 then
              decodeStateCodeChunk18 code
            else
              decodeStateCodeChunk19 code
        else
          if code < 694746371037006843260294339447343949019951103230696873036913573888 then
            decodeStateCodeChunk20 code
          else
            if code < 1389492883780990713863270991416160973912994719110312701884020817920 then
              decodeStateCodeChunk21 code
            else
              decodeStateCodeChunk22 code
  else
    if code < 10813264130718280515128241019173193674639769001838514851666068370358272 then
      if code < 300130433115045239259161168513181527866081213964249687407806331748352 then
        if code < 8452747560242840211481787509485076176641622204200707865874737922048 then
          if code < 8336956475421288962275832236431671290912980004465391313566866341888 then
            decodeStateCodeChunk23 code
          else
            decodeStateCodeChunk24 code
        else
          if code < 50021738714629030178190827026718509246256257172146216983246007173120 then
            decodeStateCodeChunk25 code
          else
            if code < 50259753675732780656657434031989110069944921460664048628233169534976 then
              decodeStateCodeChunk26 code
            else
              decodeStateCodeChunk27 code
      else
        if code < 1804024748426917306776422829669583527450703618572614187865883956740096 then
          if code < 308467389591101404637324480201756494917579225804463423764069693259776 then
            decodeStateCodeChunk28 code
          else
            if code < 1800782598690253786417128666239770393717907180201564215401814010363904 then
              decodeStateCodeChunk29 code
            else
              decodeStateCodeChunk30 code
        else
          if code < 3601565197382440769056613563082558505557604832727574278631913804529664 then
            decodeStateCodeChunk31 code
          else
            if code < 10804695592141525181173216482822043161291098329539712565376288861192192 then
              decodeStateCodeChunk32 code
            else
              decodeStateCodeChunk33 code
    else
      if code < 388969041317094803090077767347483585120368006942718217993325198071300096 then
        if code < 64836510509328384097225066451286514500804468690028713569456489018425344 then
          if code < 11714465997326133414100646129038433793905930296165789440277371395506176 then
            decodeStateCodeChunk34 code
          else
            if code < 64828173374159229020204091781322525772065609040071202437273969888329728 then
              decodeStateCodeChunk35 code
            else
              decodeStateCodeChunk36 code
        else
          if code < 75632868936519096583298869580028254333958616348453827360064952718065664 then
            decodeStateCodeChunk37 code
          else
            if code < 129681403004913081433594545606626163402805847910081709924782809680969728 then
              decodeStateCodeChunk38 code
            else
              decodeStateCodeChunk39 code
      else
        if code < 594358301015569209767205820117538420140920501237928971560423625181888512 then
          if code < 388980273050146848922180476173046450053120038974831671437245423871328256 then
            decodeStateCodeChunk40 code
          else
            if code < 390769823910821448176460964940618842807177173789071981132708549278826496 then
              decodeStateCodeChunk41 code
            else
              decodeStateCodeChunk42 code
        else
          if code < 1002358902866483216713718680182595802184413075617360022192167702627533985 then
            decodeStateCodeChunk43 code
          else
            if code < 1853705598291970391288018684793714536997646142489538653159228297265020928 then
              decodeStateCodeChunk44 code
            else
              decodeStateCodeChunk45 code

def decodeState
    (vector : Fin 93 -> Fin 6) : Fin 1447 :=
  decodeStateCode (stateVectorCode vector)

end SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3945.Shards
