import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9049.Shards.DecodeStatePart00
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9049.Shards.DecodeStatePart01
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9049.Shards.DecodeStatePart02
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9049.Shards.DecodeStatePart03
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9049.Shards.DecodeStatePart04

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9049.Shards

def stateVectorCode
    (vector : Fin 22 -> Fin 6) : Nat :=
  (vector (0 : Fin 22)).val + 6 * ((vector (1 : Fin 22)).val + 6 * ((vector (2 : Fin 22)).val + 6 * ((vector (3 : Fin 22)).val + 6 * ((vector (4 : Fin 22)).val + 6 * ((vector (5 : Fin 22)).val + 6 * ((vector (6 : Fin 22)).val + 6 * ((vector (7 : Fin 22)).val + 6 * ((vector (8 : Fin 22)).val + 6 * ((vector (9 : Fin 22)).val + 6 * ((vector (10 : Fin 22)).val + 6 * ((vector (11 : Fin 22)).val + 6 * ((vector (12 : Fin 22)).val + 6 * ((vector (13 : Fin 22)).val + 6 * ((vector (14 : Fin 22)).val + 6 * ((vector (15 : Fin 22)).val + 6 * ((vector (16 : Fin 22)).val + 6 * ((vector (17 : Fin 22)).val + 6 * ((vector (18 : Fin 22)).val + 6 * ((vector (19 : Fin 22)).val + 6 * ((vector (20 : Fin 22)).val + 6 * ((vector (21 : Fin 22)).val)))))))))))))))))))))

def decodeStateCode (code : Nat) : Fin 4374 :=
  if code < 26320155904364256 then
    if code < 11030613748752384 then
      if code < 3771024351922656 then
        if code < 774928042015104 then
          if code < 318604021014528 then
            if code < 115024806884736 then
              if code < 30859517630016 then
                decodeStateCodeChunk0 code
              else
                decodeStateCodeChunk1 code
            else
              if code < 165644428927968 then
                decodeStateCodeChunk2 code
              else
                decodeStateCodeChunk3 code
          else
            if code < 639984225614400 then
              if code < 371576744762976 then
                decodeStateCodeChunk4 code
              else
                decodeStateCodeChunk5 code
            else
              if code < 724304066422752 then
                decodeStateCodeChunk6 code
              else
                decodeStateCodeChunk7 code
        else
          if code < 1880801069607936 then
            if code < 978742348637184 then
              if code < 927728728998912 then
                decodeStateCodeChunk8 code
              else
                decodeStateCodeChunk9 code
            else
              if code < 1830022723860480 then
                decodeStateCodeChunk10 code
              else
                decodeStateCodeChunk11 code
          else
            if code < 2084001524178912 then
              if code < 1948587704472096 then
                decodeStateCodeChunk12 code
              else
                decodeStateCodeChunk13 code
            else
              if code < 2185563657349728 then
                decodeStateCodeChunk14 code
              else
                if code < 3686469418629792 then
                  decodeStateCodeChunk15 code
                else
                  decodeStateCodeChunk16 code
      else
        if code < 4634273885472864 then
          if code < 4295753031724704 then
            if code < 3974148618544224 then
              if code < 3804799669483968 then
                decodeStateCodeChunk17 code
              else
                decodeStateCodeChunk18 code
            else
              if code < 4024992449160288 then
                decodeStateCodeChunk19 code
              else
                decodeStateCodeChunk20 code
          else
            if code < 4400131921798176 then
              if code < 4380307965009792 then
                decodeStateCodeChunk21 code
              else
                decodeStateCodeChunk22 code
            else
              if code < 4583495358326880 then
                decodeStateCodeChunk23 code
              else
                decodeStateCodeChunk24 code
        else
          if code < 5689381265775072 then
            if code < 5503577655680064 then
              if code < 5212602867736224 then
                decodeStateCodeChunk25 code
              else
                decodeStateCodeChunk26 code
            else
              if code < 5588446045629312 then
                decodeStateCodeChunk27 code
              else
                decodeStateCodeChunk28 code
          else
            if code < 7630920911218176 then
              if code < 5824705655813184 then
                decodeStateCodeChunk29 code
              else
                decodeStateCodeChunk30 code
            else
              if code < 8290902510520416 then
                decodeStateCodeChunk31 code
              else
                if code < 10979835221606400 then
                  decodeStateCodeChunk32 code
                else
                  decodeStateCodeChunk33 code
    else
      if code < 22560008208180480 then
        if code < 12522960633674304 then
          if code < 11609008094959776 then
            if code < 11284493323788288 then
              if code < 11098400202218016 then
                decodeStateCodeChunk34 code
              else
                decodeStateCodeChunk35 code
            else
              if code < 11335520004120576 then
                decodeStateCodeChunk36 code
              else
                decodeStateCodeChunk37 code
          else
            if code < 11792539144280448 then
              if code < 11707668577828800 then
                decodeStateCodeChunk38 code
              else
                decodeStateCodeChunk39 code
            else
              if code < 11927785170170016 then
                decodeStateCodeChunk40 code
              else
                decodeStateCodeChunk41 code
        else
          if code < 21950883500196096 then
            if code < 12915340827028416 then
              if code < 12830705715539520 then
                decodeStateCodeChunk42 code
              else
                decodeStateCodeChunk43 code
            else
              if code < 13118214764521152 then
                decodeStateCodeChunk44 code
              else
                decodeStateCodeChunk45 code
          else
            if code < 22068745380113184 then
              if code < 22001194019139840 then
                decodeStateCodeChunk46 code
              else
                decodeStateCodeChunk47 code
            else
              if code < 22153535405610624 then
                decodeStateCodeChunk48 code
              else
                if code < 22272324594242976 then
                  decodeStateCodeChunk49 code
                else
                  decodeStateCodeChunk50 code
      else
        if code < 23919313845396096 then
          if code < 22881383998749504 then
            if code < 22678103003807520 then
              if code < 22610407975207776 then
                decodeStateCodeChunk51 code
              else
                decodeStateCodeChunk52 code
            else
              if code < 22762660113595008 then
                decodeStateCodeChunk53 code
              else
                decodeStateCodeChunk54 code
          else
            if code < 23783899662612288 then
              if code < 23273357194234080 then
                decodeStateCodeChunk55 code
              else
                decodeStateCodeChunk56 code
            else
              if code < 23868535136851584 then
                decodeStateCodeChunk57 code
              else
                decodeStateCodeChunk58 code
        else
          if code < 25724823289299648 then
            if code < 25606493401195872 then
              if code < 24088570825488192 then
                decodeStateCodeChunk59 code
              else
                decodeStateCodeChunk60 code
            else
              if code < 25657117376788224 then
                decodeStateCodeChunk61 code
              else
                decodeStateCodeChunk62 code
          else
            if code < 25928013222196128 then
              if code < 25759380434431104 then
                decodeStateCodeChunk63 code
              else
                decodeStateCodeChunk64 code
            else
              if code < 26215777014290784 then
                decodeStateCodeChunk65 code
              else
                if code < 26249785247562048 then
                  decodeStateCodeChunk66 code
                else
                  decodeStateCodeChunk67 code
  else
    if code < 66129168606879744 then
      if code < 33647675422286016 then
        if code < 29263200390399744 then
          if code < 27423366908550912 then
            if code < 26537307356397888 then
              if code < 26368505142415488 then
                decodeStateCodeChunk68 code
              else
                decodeStateCodeChunk69 code
            else
              if code < 26844882346917792 then
                decodeStateCodeChunk70 code
              else
                decodeStateCodeChunk71 code
          else
            if code < 27542166618857760 then
              if code < 27474158314992384 then
                decodeStateCodeChunk72 code
              else
                decodeStateCodeChunk73 code
            else
              if code < 27727959344473440 then
                decodeStateCodeChunk74 code
              else
                decodeStateCodeChunk75 code
        else
          if code < 33018411124090080 then
            if code < 31198246694748864 then
              if code < 29923181989701984 then
                decodeStateCodeChunk76 code
              else
                decodeStateCodeChunk77 code
            else
              if code < 32933701639243584 then
                decodeStateCodeChunk78 code
              else
                decodeStateCodeChunk79 code
          else
            if code < 33238383686031168 then
              if code < 33069189651236064 then
                decodeStateCodeChunk80 code
              else
                decodeStateCodeChunk81 code
            else
              if code < 33526369872721152 then
                decodeStateCodeChunk82 code
              else
                if code < 33579732240499968 then
                  decodeStateCodeChunk83 code
                else
                  decodeStateCodeChunk84 code
      else
        if code < 45754715414416896 then
          if code < 34835205904491744 then
            if code < 34155240112855872 then
              if code < 33831039221611776 then
                decodeStateCodeChunk85 code
              else
                decodeStateCodeChunk86 code
            else
              if code < 34733724311707488 then
                decodeStateCodeChunk87 code
              else
                decodeStateCodeChunk88 code
          else
            if code < 35089095819803616 then
              if code < 34936689674050560 then
                decodeStateCodeChunk89 code
              else
                decodeStateCodeChunk90 code
            else
              if code < 44496580088439648 then
                decodeStateCodeChunk91 code
              else
                decodeStateCodeChunk92 code
        else
          if code < 55209421286555904 then
            if code < 48305077022674656 then
              if code < 47645095423372416 then
                decodeStateCodeChunk93 code
              else
                decodeStateCodeChunk94 code
            else
              if code < 49681692978380352 then
                decodeStateCodeChunk95 code
              else
                decodeStateCodeChunk96 code
          else
            if code < 65824497444003840 then
              if code < 56687536309786272 then
                decodeStateCodeChunk97 code
              else
                decodeStateCodeChunk98 code
            else
              if code < 65875511063642112 then
                decodeStateCodeChunk99 code
              else
                if code < 65945413349538336 then
                  decodeStateCodeChunk100 code
                else
                  decodeStateCodeChunk101 code
    else
      if code < 70397116146591840 then
        if code < 67793162886734976 then
          if code < 66687522769533312 then
            if code < 66484167763424256 then
              if code < 66433389236278272 then
                decodeStateCodeChunk102 code
              else
                decodeStateCodeChunk103 code
            else
              if code < 66552030404271648 then
                decodeStateCodeChunk104 code
              else
                decodeStateCodeChunk105 code
          else
            if code < 67640822044459776 then
              if code < 66789385298674272 then
                decodeStateCodeChunk106 code
              else
                decodeStateCodeChunk107 code
            else
              if code < 67691838022278912 then
                decodeStateCodeChunk108 code
              else
                decodeStateCodeChunk109 code
        else
          if code < 69632994378238848 then
            if code < 69497192909605536 then
              if code < 67962890051811648 then
                decodeStateCodeChunk110 code
              else
                decodeStateCodeChunk111 code
            else
              if code < 69581981121397632 then
                decodeStateCodeChunk112 code
              else
                decodeStateCodeChunk113 code
          else
            if code < 70092444983715936 then
              if code < 69802018986816576 then
                decodeStateCodeChunk114 code
              else
                decodeStateCodeChunk115 code
            else
              if code < 70191105466584960 then
                decodeStateCodeChunk116 code
              else
                if code < 70225194240810432 then
                  decodeStateCodeChunk117 code
                else
                  decodeStateCodeChunk118 code
      else
        if code < 76895081300530656 then
          if code < 71517029244490944 then
            if code < 71297685772077312 then
              if code < 70752504947166720 then
                decodeStateCodeChunk119 code
              else
                decodeStateCodeChunk120 code
            else
              if code < 71398775906838144 then
                decodeStateCodeChunk121 code
              else
                decodeStateCodeChunk122 code
          else
            if code < 73763179168425120 then
              if code < 71653135643498376 then
                decodeStateCodeChunk123 code
              else
                decodeStateCodeChunk124 code
            else
              if code < 75055169086674048 then
                decodeStateCodeChunk125 code
              else
                if code < 76807550705776704 then
                  decodeStateCodeChunk126 code
                else
                  decodeStateCodeChunk127 code
        else
          if code < 77552400695028192 then
            if code < 77399983846761984 then
              if code < 77044522487048064 then
                decodeStateCodeChunk128 code
              else
                decodeStateCodeChunk129 code
            else
              if code < 77453659671204960 then
                decodeStateCodeChunk130 code
              else
                decodeStateCodeChunk131 code
          else
            if code < 78333838706436768 then
              if code < 77724635694746688 then
                decodeStateCodeChunk132 code
              else
                decodeStateCodeChunk133 code
            else
              if code < 78708976611891840 then
                decodeStateCodeChunk134 code
              else
                if code < 78827700497606208 then
                  decodeStateCodeChunk135 code
                else
                  decodeStateCodeChunk136 code

def decodeState
    (vector : Fin 22 -> Fin 6) : Fin 4374 :=
  decodeStateCode (stateVectorCode vector)

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9049.Shards
