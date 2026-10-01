import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.Shards.DecodeStatePart00
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.Shards.DecodeStatePart01
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.Shards.DecodeStatePart02
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.Shards.DecodeStatePart03
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.Shards.DecodeStatePart04

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.Shards

def stateVectorCode
    (vector : Fin 28 -> Fin 6) : Nat :=
  (vector (0 : Fin 28)).val + 6 * ((vector (1 : Fin 28)).val + 6 * ((vector (2 : Fin 28)).val + 6 * ((vector (3 : Fin 28)).val + 6 * ((vector (4 : Fin 28)).val + 6 * ((vector (5 : Fin 28)).val + 6 * ((vector (6 : Fin 28)).val + 6 * ((vector (7 : Fin 28)).val + 6 * ((vector (8 : Fin 28)).val + 6 * ((vector (9 : Fin 28)).val + 6 * ((vector (10 : Fin 28)).val + 6 * ((vector (11 : Fin 28)).val + 6 * ((vector (12 : Fin 28)).val + 6 * ((vector (13 : Fin 28)).val + 6 * ((vector (14 : Fin 28)).val + 6 * ((vector (15 : Fin 28)).val + 6 * ((vector (16 : Fin 28)).val + 6 * ((vector (17 : Fin 28)).val + 6 * ((vector (18 : Fin 28)).val + 6 * ((vector (19 : Fin 28)).val + 6 * ((vector (20 : Fin 28)).val + 6 * ((vector (21 : Fin 28)).val + 6 * ((vector (22 : Fin 28)).val + 6 * ((vector (23 : Fin 28)).val + 6 * ((vector (24 : Fin 28)).val + 6 * ((vector (25 : Fin 28)).val + 6 * ((vector (26 : Fin 28)).val + 6 * ((vector (27 : Fin 28)).val)))))))))))))))))))))))))))

def decodeStateCode (code : Nat) : Fin 4374 :=
  if code < 14529812964967415808 then
    if code < 2413112531125655808 then
      if code < 271774838050682112 then
        if code < 263243801690535168 then
          if code < 7348521123938304 then
            if code < 236973232226304 then
              if code < 33853318889472 then
                decodeStateCodeChunk0 code
              else
                decodeStateCodeChunk1 code
            else
              if code < 1421839393357824 then
                decodeStateCodeChunk2 code
              else
                decodeStateCodeChunk3 code
          else
            if code < 44093542972022784 then
              if code < 8768009592373248 then
                decodeStateCodeChunk4 code
              else
                decodeStateCodeChunk5 code
            else
              if code < 51220071479771136 then
                decodeStateCodeChunk6 code
              else
                decodeStateCodeChunk7 code
        else
          if code < 263496904871473152 then
            if code < 263280005865483264 then
              if code < 263257907290460928 then
                decodeStateCodeChunk8 code
              else
                decodeStateCodeChunk9 code
            else
              if code < 263449270654343424 then
                decodeStateCodeChunk10 code
              else
                decodeStateCodeChunk11 code
          else
            if code < 264679744507036416 then
              if code < 264476626770481920 then
                decodeStateCodeChunk12 code
              else
                decodeStateCodeChunk13 code
            else
              if code < 270558077674763520 then
                decodeStateCodeChunk14 code
              else
                if code < 270759236307215616 then
                  decodeStateCodeChunk15 code
                else
                  decodeStateCodeChunk16 code
      else
        if code < 2369238640728811776 then
          if code < 308573003854319616 then
            if code < 307165269647702016 then
              if code < 307119659898610944 then
                decodeStateCodeChunk17 code
              else
                decodeStateCodeChunk18 code
            else
              if code < 308336028453709056 then
                decodeStateCodeChunk19 code
              else
                decodeStateCodeChunk20 code
          else
            if code < 2369191073679525888 then
              if code < 314635096692073728 then
                decodeStateCodeChunk21 code
              else
                decodeStateCodeChunk22 code
            else
              if code < 2369224535179274496 then
                decodeStateCodeChunk23 code
              else
                decodeStateCodeChunk24 code
        else
          if code < 2370627016858824192 then
            if code < 2369442150699372288 then
              if code < 2369396543006131200 then
                decodeStateCodeChunk25 code
              else
                decodeStateCodeChunk26 code
            else
              if code < 2370443254659295488 then
                decodeStateCodeChunk27 code
              else
                decodeStateCodeChunk28 code
          else
            if code < 2376539595107474688 then
              if code < 2376505741786905600 then
                decodeStateCodeChunk29 code
              else
                decodeStateCodeChunk30 code
            else
              if code < 2377722110039672832 then
                decodeStateCodeChunk31 code
              else
                if code < 2413064583139461120 then
                  decodeStateCodeChunk32 code
                else
                  decodeStateCodeChunk33 code
    else
      if code < 14216565865604917248 then
        if code < 2639782990094112000 then
          if code < 2632434078659328000 then
            if code < 2414500526268370944 then
              if code < 2413315660108919040 then
                decodeStateCodeChunk34 code
              else
                decodeStateCodeChunk35 code
            else
              if code < 2420413104265079040 then
                decodeStateCodeChunk36 code
              else
                decodeStateCodeChunk37 code
          else
            if code < 2632685155628785920 then
              if code < 2632482035715449088 then
                decodeStateCodeChunk38 code
              else
                decodeStateCodeChunk39 code
            else
              if code < 2633856308059521024 then
                decodeStateCodeChunk40 code
              else
                decodeStateCodeChunk41 code
        else
          if code < 14215146768896836608 then
            if code < 2676547302284927232 then
              if code < 2641202478260216064 then
                decodeStateCodeChunk42 code
              else
                decodeStateCodeChunk43 code
            else
              if code < 2683656499251716352 then
                decodeStateCodeChunk44 code
              else
                decodeStateCodeChunk45 code
          else
            if code < 14215349889172970496 then
              if code < 14215194782236609920 then
                decodeStateCodeChunk46 code
              else
                decodeStateCodeChunk47 code
            else
              if code < 14215364060077766016 then
                decodeStateCodeChunk48 code
              else
                if code < 14215397913033858432 then
                  decodeStateCodeChunk49 code
                else
                  decodeStateCodeChunk50 code
      else
        if code < 14260487725391302656 then
          if code < 14223878171601131520 then
            if code < 14222492928211940352 then
              if code < 14216600110381830144 then
                decodeStateCodeChunk51 code
              else
                decodeStateCodeChunk52 code
            else
              if code < 14222662206053096448 then
                decodeStateCodeChunk53 code
              else
                decodeStateCodeChunk54 code
          else
            if code < 14259235142071277568 then
              if code < 14259032032679055360 then
                decodeStateCodeChunk55 code
              else
                decodeStateCodeChunk56 code
            else
              if code < 14260236646609539072 then
                decodeStateCodeChunk57 code
              else
                decodeStateCodeChunk58 code
        else
          if code < 14479606142129405952 then
            if code < 14478401528198922240 then
              if code < 14266567217241870336 then
                decodeStateCodeChunk59 code
              else
                decodeStateCodeChunk60 code
            else
              if code < 14478604648112259072 then
                decodeStateCodeChunk61 code
              else
                decodeStateCodeChunk62 code
          else
            if code < 14485936712761737216 then
              if code < 14479857220911169536 then
                decodeStateCodeChunk63 code
              else
                decodeStateCodeChunk64 code
            else
              if code < 14522277845708070912 then
                decodeStateCodeChunk65 code
              else
                if code < 14523494148959698944 then
                  decodeStateCodeChunk66 code
                else
                  decodeStateCodeChunk67 code
  else
    if code < 511789261559928717312 then
      if code < 85555326688961027328 then
        if code < 85298379918411785472 then
          if code < 85292097317582181120 then
            if code < 85291067601531659520 then
              if code < 85290878206230951168 then
                decodeStateCodeChunk68 code
              else
                decodeStateCodeChunk69 code
            else
              if code < 85292083211982255360 then
                decodeStateCodeChunk70 code
              else
                decodeStateCodeChunk71 code
          else
            if code < 85292286791196665088 then
              if code < 85292117526407804928 then
                decodeStateCodeChunk72 code
              else
                decodeStateCodeChunk73 code
            else
              if code < 85292334369119784960 then
                decodeStateCodeChunk74 code
              else
                decodeStateCodeChunk75 code
        else
          if code < 85335957191627175168 then
            if code < 85299598716255970560 then
              if code < 85299395988163454208 then
                decodeStateCodeChunk76 code
              else
                decodeStateCodeChunk77 code
            else
              if code < 85334771846202734592 then
                decodeStateCodeChunk78 code
              else
                decodeStateCodeChunk79 code
          else
            if code < 85342050318842295552 then
              if code < 85336005141417277440 then
                decodeStateCodeChunk80 code
              else
                decodeStateCodeChunk81 code
            else
              if code < 85343302893446793216 then
                decodeStateCodeChunk82 code
              else
                if code < 85554121996716768000 then
                  decodeStateCodeChunk83 code
                else
                  decodeStateCodeChunk84 code
      else
        if code < 511745390401696035840 then
          if code < 85598184518676129024 then
            if code < 85561419816176147712 then
              if code < 85555374569507280384 then
                decodeStateCodeChunk85 code
              else
                decodeStateCodeChunk86 code
            else
              if code < 85562672388966660096 then
                decodeStateCodeChunk87 code
              else
                decodeStateCodeChunk88 code
          else
            if code < 85606716025212862464 then
              if code < 85599403708341134592 then
                decodeStateCodeChunk89 code
              else
                decodeStateCodeChunk90 code
            else
              if code < 511745187292666610688 then
                decodeStateCodeChunk91 code
              else
                decodeStateCodeChunk92 code
        else
          if code < 511752533530043547648 then
            if code < 511752499206539673600 then
              if code < 511746437503354355712 then
                decodeStateCodeChunk93 code
              else
                decodeStateCodeChunk94 code
            else
              if code < 511752502027649581056 then
                decodeStateCodeChunk95 code
              else
                decodeStateCodeChunk96 code
          else
            if code < 511753715575094771712 then
              if code < 511752702796637995008 then
                decodeStateCodeChunk97 code
              else
                decodeStateCodeChunk98 code
            else
              if code < 511753749428413661184 then
                decodeStateCodeChunk99 code
              else
                if code < 511753952548326998016 then
                  decodeStateCodeChunk100 code
                else
                  decodeStateCodeChunk101 code
    else
      if code < 3070514981133696902400 then
        if code < 512015977236531511296 then
          if code < 511797792607172775936 then
            if code < 511796404621098307584 then
              if code < 511796370758709491712 then
                decodeStateCodeChunk102 code
              else
                decodeStateCodeChunk103 code
            else
              if code < 511796610081052655616 then
                decodeStateCodeChunk104 code
              else
                decodeStateCodeChunk105 code
          else
            if code < 512015740263299284992 then
              if code < 512008464542786122752 then
                decodeStateCodeChunk106 code
              else
                decodeStateCodeChunk107 code
            else
              if code < 512015774116618174464 then
                decodeStateCodeChunk108 code
              else
                decodeStateCodeChunk109 code
        else
          if code < 3070471107234230131968 then
            if code < 512053520568993921024 then
              if code < 512017162102692642816 then
                decodeStateCodeChunk110 code
              else
                decodeStateCodeChunk111 code
            else
              if code < 512059817284501775616 then
                decodeStateCodeChunk112 code
              else
                decodeStateCodeChunk113 code
          else
            if code < 3070471346567448809472 then
              if code < 3070471141098424535040 then
                decodeStateCodeChunk114 code
              else
                decodeStateCodeChunk115 code
            else
              if code < 3070472529082693416192 then
                decodeStateCodeChunk116 code
              else
                if code < 3070478455766229583872 then
                  decodeStateCodeChunk117 code
                else
                  decodeStateCodeChunk118 code
      else
        if code < 3070523512170057049344 then
          if code < 3070515218117804642304 then
            if code < 3070515014988821379072 then
              if code < 3070514995239246439680 then
                decodeStateCodeChunk119 code
              else
                decodeStateCodeChunk120 code
            else
              if code < 3070515184253610239232 then
                decodeStateCodeChunk121 code
              else
                decodeStateCodeChunk122 code
          else
            if code < 3070516402973090260224 then
              if code < 3070516213958726460672 then
                decodeStateCodeChunk123 code
              else
                decodeStateCodeChunk124 code
            else
              if code < 3070522293528941192448 then
                decodeStateCodeChunk125 code
              else
                if code < 3070522329656626427904 then
                  decodeStateCodeChunk126 code
                else
                  decodeStateCodeChunk127 code
        else
          if code < 3070778226970662125568 then
            if code < 3070734567865563555072 then
              if code < 3070523749154164789248 then
                decodeStateCodeChunk128 code
              else
                decodeStateCodeChunk129 code
            else
              if code < 3070741665309719715072 then
                decodeStateCodeChunk130 code
              else
                decodeStateCodeChunk131 code
          else
            if code < 3070779443339217223680 then
              if code < 3070778274916469858304 then
                decodeStateCodeChunk132 code
              else
                decodeStateCodeChunk133 code
            else
              if code < 3070785536858253164544 then
                decodeStateCodeChunk134 code
              else
                if code < 3070785773831485390848 then
                  decodeStateCodeChunk135 code
                else
                  decodeStateCodeChunk136 code

def decodeState
    (vector : Fin 28 -> Fin 6) : Fin 4374 :=
  decodeStateCode (stateVectorCode vector)

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.Shards
