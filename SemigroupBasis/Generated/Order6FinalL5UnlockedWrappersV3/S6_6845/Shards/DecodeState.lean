import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6845.Shards.DecodeStatePart00
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6845.Shards.DecodeStatePart01
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6845.Shards.DecodeStatePart02
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6845.Shards.DecodeStatePart03
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6845.Shards.DecodeStatePart04

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6845.Shards

def stateVectorCode
    (vector : Fin 22 -> Fin 6) : Nat :=
  (vector (0 : Fin 22)).val + 6 * ((vector (1 : Fin 22)).val + 6 * ((vector (2 : Fin 22)).val + 6 * ((vector (3 : Fin 22)).val + 6 * ((vector (4 : Fin 22)).val + 6 * ((vector (5 : Fin 22)).val + 6 * ((vector (6 : Fin 22)).val + 6 * ((vector (7 : Fin 22)).val + 6 * ((vector (8 : Fin 22)).val + 6 * ((vector (9 : Fin 22)).val + 6 * ((vector (10 : Fin 22)).val + 6 * ((vector (11 : Fin 22)).val + 6 * ((vector (12 : Fin 22)).val + 6 * ((vector (13 : Fin 22)).val + 6 * ((vector (14 : Fin 22)).val + 6 * ((vector (15 : Fin 22)).val + 6 * ((vector (16 : Fin 22)).val + 6 * ((vector (17 : Fin 22)).val + 6 * ((vector (18 : Fin 22)).val + 6 * ((vector (19 : Fin 22)).val + 6 * ((vector (20 : Fin 22)).val + 6 * ((vector (21 : Fin 22)).val)))))))))))))))))))))

def decodeStateCode (code : Nat) : Fin 4374 :=
  if code < 78031968825547008 then
    if code < 69472861376595840 then
      if code < 32940424085566464 then
        if code < 12193824372212736 then
          if code < 11008017841112064 then
            if code < 10974164522222592 then
              if code < 10969462672376832 then
                decodeStateCodeChunk0 code
              else
                decodeStateCodeChunk1 code
            else
              if code < 11002375621297152 then
                decodeStateCodeChunk2 code
              else
                decodeStateCodeChunk3 code
          else
            if code < 11205495534633984 then
              if code < 11172582585713664 then
                decodeStateCodeChunk4 code
              else
                decodeStateCodeChunk5 code
            else
              if code < 12187398510756864 then
                decodeStateCodeChunk6 code
              else
                decodeStateCodeChunk7 code
        else
          if code < 18315658992780288 then
            if code < 12429857234469888 then
              if code < 12390361695765504 then
                decodeStateCodeChunk8 code
              else
                decodeStateCodeChunk9 code
            else
              if code < 18281810027455488 then
                decodeStateCodeChunk10 code
              else
                decodeStateCodeChunk11 code
          else
            if code < 19505200882369536 then
              if code < 18490541685654528 then
                decodeStateCodeChunk12 code
              else
                decodeStateCodeChunk13 code
            else
              if code < 19736531894780928 then
                decodeStateCodeChunk14 code
              else
                if code < 32906596888065024 then
                  decodeStateCodeChunk15 code
                else
                  decodeStateCodeChunk16 code
      else
        if code < 65816572329592704 then
          if code < 40252583511770112 then
            if code < 34125319996056576 then
              if code < 33115179799471104 then
                decodeStateCodeChunk17 code
              else
                decodeStateCodeChunk18 code
            else
              if code < 34334051654255616 then
                decodeStateCodeChunk19 code
              else
                decodeStateCodeChunk20 code
          else
            if code < 65810904109322112 then
              if code < 41437454026466304 then
                decodeStateCodeChunk21 code
              else
                decodeStateCodeChunk22 code
            else
              if code < 65811844479291264 then
                decodeStateCodeChunk23 code
              else
                decodeStateCodeChunk24 code
        else
          if code < 66048029716311936 then
            if code < 65850578023245696 then
              if code < 65844779196034944 then
                decodeStateCodeChunk25 code
              else
                decodeStateCodeChunk26 code
            else
              if code < 66014964392628096 then
                decodeStateCodeChunk27 code
              else
                decodeStateCodeChunk28 code
          else
            if code < 67036388182316928 then
              if code < 67029805713465216 then
                decodeStateCodeChunk29 code
              else
                decodeStateCodeChunk30 code
            else
              if code < 67232899505414016 then
                decodeStateCodeChunk31 code
              else
                if code < 69467214924148608 then
                  decodeStateCodeChunk32 code
                else
                  decodeStateCodeChunk33 code
    else
      if code < 76819963267844352 then
        if code < 76784978017101312 then
          if code < 76779335192624640 then
            if code < 69704188156374912 then
              if code < 69506736463308672 then
                decodeStateCodeChunk34 code
              else
                decodeStateCodeChunk35 code
            else
              if code < 70692546622379904 then
                decodeStateCodeChunk36 code
              else
                decodeStateCodeChunk37 code
          else
            if code < 76780275562593792 then
              if code < 76779491920952832 then
                decodeStateCodeChunk38 code
              else
                decodeStateCodeChunk39 code
            else
              if code < 76780432290921984 then
                decodeStateCodeChunk40 code
              else
                decodeStateCodeChunk41 code
        else
          if code < 76813247289676032 then
            if code < 76785957393772608 then
              if code < 76785167402203392 then
                decodeStateCodeChunk42 code
              else
                decodeStateCodeChunk43 code
            else
              if code < 76786117810537536 then
                decodeStateCodeChunk44 code
              else
                decodeStateCodeChunk45 code
          else
            if code < 76814193102440832 then
              if code < 76813406194786560 then
                decodeStateCodeChunk46 code
              else
                decodeStateCodeChunk47 code
            else
              if code < 76818831335990784 then
                decodeStateCodeChunk48 code
              else
                if code < 76819048293669120 then
                  decodeStateCodeChunk49 code
                else
                  decodeStateCodeChunk50 code
      else
        if code < 77017281451593984 then
          if code < 76988097930438144 then
            if code < 76982649933859200 then
              if code < 76982487762735360 then
                decodeStateCodeChunk51 code
              else
                decodeStateCodeChunk52 code
            else
              if code < 76983437929064832 then
                decodeStateCodeChunk53 code
              else
                decodeStateCodeChunk54 code
          else
            if code < 76989208089429504 then
              if code < 76988293665468480 then
                decodeStateCodeChunk55 code
              else
                decodeStateCodeChunk56 code
            else
              if code < 77016346524420480 then
                decodeStateCodeChunk57 code
              else
                decodeStateCodeChunk58 code
        else
          if code < 77998270179135744 then
            if code < 77022926452852992 then
              if code < 77021951249327616 then
                decodeStateCodeChunk59 code
              else
                decodeStateCodeChunk60 code
            else
              if code < 77998097367644544 then
                decodeStateCodeChunk61 code
              else
                decodeStateCodeChunk62 code
          else
            if code < 77999220587329920 then
              if code < 77999059626369408 then
                decodeStateCodeChunk63 code
              else
                decodeStateCodeChunk64 code
            else
              if code < 78003896860123200 then
                decodeStateCodeChunk65 code
              else
                if code < 78004798223390208 then
                  decodeStateCodeChunk66 code
                else
                  decodeStateCodeChunk67 code
  else
    if code < 109927416367622016 then
      if code < 84132148815436032 then
        if code < 78235060561645824 then
          if code < 78201207242756352 then
            if code < 78033069552654720 then
              if code < 78032883195060480 then
                decodeStateCodeChunk68 code
              else
                decodeStateCodeChunk69 code
            else
              if code < 78038528559956352 then
                decodeStateCodeChunk70 code
              else
                decodeStateCodeChunk71 code
          else
            if code < 78202310146646400 then
              if code < 78202114955951616 then
                decodeStateCodeChunk72 code
              else
                decodeStateCodeChunk73 code
            else
              if code < 78207016833926208 then
                decodeStateCodeChunk74 code
              else
                decodeStateCodeChunk75 code
        else
          if code < 84092634895853952 then
            if code < 78241623434417664 then
              if code < 78236006737207680 then
                decodeStateCodeChunk76 code
              else
                decodeStateCodeChunk77 code
            else
              if code < 84091694525884800 then
                decodeStateCodeChunk78 code
              else
                decodeStateCodeChunk79 code
          else
            if code < 84098300395286592 then
              if code < 84097353675389184 then
                decodeStateCodeChunk80 code
              else
                decodeStateCodeChunk81 code
            else
              if code < 84125569612597632 then
                decodeStateCodeChunk82 code
              else
                if code < 84131148216116736 then
                  decodeStateCodeChunk83 code
                else
                  decodeStateCodeChunk84 code
      else
        if code < 85317012799785216 then
          if code < 84329578735640064 then
            if code < 84300414810564096 then
              if code < 84294814439221632 then
                decodeStateCodeChunk85 code
              else
                decodeStateCodeChunk86 code
            else
              if code < 84301394187235392 then
                decodeStateCodeChunk87 code
              else
                decodeStateCodeChunk88 code
          else
            if code < 85310440006361472 then
              if code < 84335240430602496 then
                decodeStateCodeChunk89 code
              else
                decodeStateCodeChunk90 code
            else
              if code < 85311381283463232 then
                decodeStateCodeChunk91 code
              else
                decodeStateCodeChunk92 code
        else
          if code < 85520073934960128 then
            if code < 85350842174068992 then
              if code < 85345197898404096 then
                decodeStateCodeChunk93 code
              else
                decodeStateCodeChunk94 code
            else
              if code < 85514431836077568 then
                decodeStateCodeChunk95 code
              else
                decodeStateCodeChunk96 code
          else
            if code < 109684826435666304 then
              if code < 85548319867590912 then
                decodeStateCodeChunk97 code
              else
                decodeStateCodeChunk98 code
            else
              if code < 109690599863723904 then
                decodeStateCodeChunk99 code
              else
                if code < 109887920224255872 then
                  decodeStateCodeChunk100 code
                else
                  decodeStateCodeChunk101 code
    else
      if code < 121872112560797184 then
        if code < 120659105511759168 then
          if code < 114599356501850496 then
            if code < 113341120558468992 then
              if code < 110937529838157696 then
                decodeStateCodeChunk102 code
              else
                decodeStateCodeChunk103 code
            else
              if code < 113544236118241152 then
                decodeStateCodeChunk104 code
              else
                decodeStateCodeChunk105 code
          else
            if code < 120653452587891456 then
              if code < 120653295859563264 then
                decodeStateCodeChunk106 code
              else
                decodeStateCodeChunk107 code
            else
              if code < 120658944489772608 then
                decodeStateCodeChunk108 code
              else
                decodeStateCodeChunk109 code
        else
          if code < 120856513719707136 then
            if code < 120692769990721920 then
              if code < 120687247125259776 then
                decodeStateCodeChunk110 code
              else
                decodeStateCodeChunk111 code
            else
              if code < 120692954476524096 then
                decodeStateCodeChunk112 code
              else
                decodeStateCodeChunk113 code
          else
            if code < 120862199299788864 then
              if code < 120862015899858432 then
                decodeStateCodeChunk114 code
              else
                decodeStateCodeChunk115 code
            else
              if code < 120890399695370496 then
                decodeStateCodeChunk116 code
              else
                if code < 120896047539519552 then
                  decodeStateCodeChunk117 code
                else
                  decodeStateCodeChunk118 code
      else
        if code < 127971239558405184 then
          if code < 121911666881022720 then
            if code < 121877823359053440 then
              if code < 121877636514650496 then
                decodeStateCodeChunk119 code
              else
                decodeStateCodeChunk120 code
            else
              if code < 121906004342053248 then
                decodeStateCodeChunk121 code
              else
                decodeStateCodeChunk122 code
          else
            if code < 122080912793518464 then
              if code < 122075249888392704 then
                decodeStateCodeChunk123 code
              else
                decodeStateCodeChunk124 code
            else
              if code < 122109124376322432 then
                decodeStateCodeChunk125 code
              else
                if code < 127965592259431488 then
                  decodeStateCodeChunk126 code
                else
                  decodeStateCodeChunk127 code
        else
          if code < 128202565491657792 then
            if code < 128168673891660288 then
              if code < 127999466078734080 then
                decodeStateCodeChunk128 code
              else
                decodeStateCodeChunk129 code
            else
              if code < 128174332800139776 then
                decodeStateCodeChunk130 code
              else
                decodeStateCodeChunk131 code
          else
            if code < 129218126172572160 then
              if code < 129184331635203840 then
                decodeStateCodeChunk132 code
              else
                decodeStateCodeChunk133 code
            else
              if code < 129387392646087168 then
                decodeStateCodeChunk134 code
              else
                if code < 129393078286635072 then
                  decodeStateCodeChunk135 code
                else
                  decodeStateCodeChunk136 code

def decodeState
    (vector : Fin 22 -> Fin 6) : Fin 4374 :=
  decodeStateCode (stateVectorCode vector)

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6845.Shards
