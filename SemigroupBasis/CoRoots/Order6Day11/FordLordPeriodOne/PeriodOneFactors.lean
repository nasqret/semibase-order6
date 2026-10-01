import SemigroupBasis.CoRoots.Order6Day11.FordLordPeriodOne.PeriodOnePresentation
import SemigroupBasis.Generated.S2_4
import SemigroupBasis.Generated.S5_400PublishedRoots

/-! Six literal B11 Models, twelve embeddings, and exact M6-to-M19 validity. No sibling subdirect claim. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day11.FordLordPeriodOne

open SemigroupBasis

abbrev initialTable : FiniteTable := Generated.S2_4.table
abbrev core400Table : FiniteTable := Generated.Catalogue.S5_400.table
abbrev core840Table : FiniteTable := Generated.Catalogue.S5_840.table

private def toFin1 : Nat → Fin 1
  | _ => 0
private def toFin2 : Nat → Fin 2
  | 0 => 0
  | _ => 1
private def toFin3 : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2
private def toFin4 : Nat → Fin 4
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 3

private theorem initialLaw00 : law00.SatisfiedBy initialTable.semigroup := by
  have checked : Models initialTable.semigroup [law00] :=
    FiniteCertificate.checkModels_sound initialTable [law00] toFin1 (by decide)
  exact checked law00 (by decide)

private theorem initialLaw01 : law01.SatisfiedBy initialTable.semigroup := by
  have checked : Models initialTable.semigroup [law01] :=
    FiniteCertificate.checkModels_sound initialTable [law01] toFin2 (by decide)
  exact checked law01 (by decide)

private theorem initialLaw02 : law02.SatisfiedBy initialTable.semigroup := by
  have checked : Models initialTable.semigroup [law02] :=
    FiniteCertificate.checkModels_sound initialTable [law02] toFin2 (by decide)
  exact checked law02 (by decide)

private theorem initialLaw03 : law03.SatisfiedBy initialTable.semigroup := by
  have checked : Models initialTable.semigroup [law03] :=
    FiniteCertificate.checkModels_sound initialTable [law03] toFin2 (by decide)
  exact checked law03 (by decide)

private theorem initialLaw04 : law04.SatisfiedBy initialTable.semigroup := by
  have checked : Models initialTable.semigroup [law04] :=
    FiniteCertificate.checkModels_sound initialTable [law04] toFin2 (by decide)
  exact checked law04 (by decide)

private theorem initialLaw05 : law05.SatisfiedBy initialTable.semigroup := by
  have checked : Models initialTable.semigroup [law05] :=
    FiniteCertificate.checkModels_sound initialTable [law05] toFin3 (by decide)
  exact checked law05 (by decide)

private theorem initialLaw06 : law06.SatisfiedBy initialTable.semigroup := by
  have checked : Models initialTable.semigroup [law06] :=
    FiniteCertificate.checkModels_sound initialTable [law06] toFin3 (by decide)
  exact checked law06 (by decide)

private theorem initialLaw07 : law07.SatisfiedBy initialTable.semigroup := by
  have checked : Models initialTable.semigroup [law07] :=
    FiniteCertificate.checkModels_sound initialTable [law07] toFin3 (by decide)
  exact checked law07 (by decide)

private theorem initialLaw08 : law08.SatisfiedBy initialTable.semigroup := by
  have checked : Models initialTable.semigroup [law08] :=
    FiniteCertificate.checkModels_sound initialTable [law08] toFin4 (by decide)
  exact checked law08 (by decide)

private theorem initialLaw09 : law09.SatisfiedBy initialTable.semigroup := by
  have checked : Models initialTable.semigroup [law09] :=
    FiniteCertificate.checkModels_sound initialTable [law09] toFin4 (by decide)
  exact checked law09 (by decide)

private theorem initialLaw10 : law10.SatisfiedBy initialTable.semigroup := by
  have checked : Models initialTable.semigroup [law10] :=
    FiniteCertificate.checkModels_sound initialTable [law10] toFin4 (by decide)
  exact checked law10 (by decide)

theorem initialModels : Models initialTable.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact initialLaw00
  · exact initialLaw01
  · exact initialLaw02
  · exact initialLaw03
  · exact initialLaw04
  · exact initialLaw05
  · exact initialLaw06
  · exact initialLaw07
  · exact initialLaw08
  · exact initialLaw09
  · exact initialLaw10

private theorem core400Law00 : law00.SatisfiedBy core400Table.semigroup := by
  have checked : Models core400Table.semigroup [law00] :=
    FiniteCertificate.checkModels_sound core400Table [law00] toFin1 (by decide)
  exact checked law00 (by decide)

private theorem core400Law01 : law01.SatisfiedBy core400Table.semigroup := by
  have checked : Models core400Table.semigroup [law01] :=
    FiniteCertificate.checkModels_sound core400Table [law01] toFin2 (by decide)
  exact checked law01 (by decide)

private theorem core400Law02 : law02.SatisfiedBy core400Table.semigroup := by
  have checked : Models core400Table.semigroup [law02] :=
    FiniteCertificate.checkModels_sound core400Table [law02] toFin2 (by decide)
  exact checked law02 (by decide)

private theorem core400Law03 : law03.SatisfiedBy core400Table.semigroup := by
  have checked : Models core400Table.semigroup [law03] :=
    FiniteCertificate.checkModels_sound core400Table [law03] toFin2 (by decide)
  exact checked law03 (by decide)

private theorem core400Law04 : law04.SatisfiedBy core400Table.semigroup := by
  have checked : Models core400Table.semigroup [law04] :=
    FiniteCertificate.checkModels_sound core400Table [law04] toFin2 (by decide)
  exact checked law04 (by decide)

private theorem core400Law05 : law05.SatisfiedBy core400Table.semigroup := by
  have checked : Models core400Table.semigroup [law05] :=
    FiniteCertificate.checkModels_sound core400Table [law05] toFin3 (by decide)
  exact checked law05 (by decide)

private theorem core400Law06 : law06.SatisfiedBy core400Table.semigroup := by
  have checked : Models core400Table.semigroup [law06] :=
    FiniteCertificate.checkModels_sound core400Table [law06] toFin3 (by decide)
  exact checked law06 (by decide)

private theorem core400Law07 : law07.SatisfiedBy core400Table.semigroup := by
  have checked : Models core400Table.semigroup [law07] :=
    FiniteCertificate.checkModels_sound core400Table [law07] toFin3 (by decide)
  exact checked law07 (by decide)

private theorem core400Law08 : law08.SatisfiedBy core400Table.semigroup := by
  have checked : Models core400Table.semigroup [law08] :=
    FiniteCertificate.checkModels_sound core400Table [law08] toFin4 (by decide)
  exact checked law08 (by decide)

private theorem core400Law09 : law09.SatisfiedBy core400Table.semigroup := by
  have checked : Models core400Table.semigroup [law09] :=
    FiniteCertificate.checkModels_sound core400Table [law09] toFin4 (by decide)
  exact checked law09 (by decide)

private theorem core400Law10 : law10.SatisfiedBy core400Table.semigroup := by
  have checked : Models core400Table.semigroup [law10] :=
    FiniteCertificate.checkModels_sound core400Table [law10] toFin4 (by decide)
  exact checked law10 (by decide)

theorem core400Models : Models core400Table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact core400Law00
  · exact core400Law01
  · exact core400Law02
  · exact core400Law03
  · exact core400Law04
  · exact core400Law05
  · exact core400Law06
  · exact core400Law07
  · exact core400Law08
  · exact core400Law09
  · exact core400Law10

private theorem core840Law00 : law00.SatisfiedBy core840Table.semigroup := by
  have checked : Models core840Table.semigroup [law00] :=
    FiniteCertificate.checkModels_sound core840Table [law00] toFin1 (by decide)
  exact checked law00 (by decide)

private theorem core840Law01 : law01.SatisfiedBy core840Table.semigroup := by
  have checked : Models core840Table.semigroup [law01] :=
    FiniteCertificate.checkModels_sound core840Table [law01] toFin2 (by decide)
  exact checked law01 (by decide)

private theorem core840Law02 : law02.SatisfiedBy core840Table.semigroup := by
  have checked : Models core840Table.semigroup [law02] :=
    FiniteCertificate.checkModels_sound core840Table [law02] toFin2 (by decide)
  exact checked law02 (by decide)

private theorem core840Law03 : law03.SatisfiedBy core840Table.semigroup := by
  have checked : Models core840Table.semigroup [law03] :=
    FiniteCertificate.checkModels_sound core840Table [law03] toFin2 (by decide)
  exact checked law03 (by decide)

private theorem core840Law04 : law04.SatisfiedBy core840Table.semigroup := by
  have checked : Models core840Table.semigroup [law04] :=
    FiniteCertificate.checkModels_sound core840Table [law04] toFin2 (by decide)
  exact checked law04 (by decide)

private theorem core840Law05 : law05.SatisfiedBy core840Table.semigroup := by
  have checked : Models core840Table.semigroup [law05] :=
    FiniteCertificate.checkModels_sound core840Table [law05] toFin3 (by decide)
  exact checked law05 (by decide)

private theorem core840Law06 : law06.SatisfiedBy core840Table.semigroup := by
  have checked : Models core840Table.semigroup [law06] :=
    FiniteCertificate.checkModels_sound core840Table [law06] toFin3 (by decide)
  exact checked law06 (by decide)

private theorem core840Law07 : law07.SatisfiedBy core840Table.semigroup := by
  have checked : Models core840Table.semigroup [law07] :=
    FiniteCertificate.checkModels_sound core840Table [law07] toFin3 (by decide)
  exact checked law07 (by decide)

private theorem core840Law08 : law08.SatisfiedBy core840Table.semigroup := by
  have checked : Models core840Table.semigroup [law08] :=
    FiniteCertificate.checkModels_sound core840Table [law08] toFin4 (by decide)
  exact checked law08 (by decide)

private theorem core840Law09 : law09.SatisfiedBy core840Table.semigroup := by
  have checked : Models core840Table.semigroup [law09] :=
    FiniteCertificate.checkModels_sound core840Table [law09] toFin4 (by decide)
  exact checked law09 (by decide)

private theorem core840Law10 : law10.SatisfiedBy core840Table.semigroup := by
  have checked : Models core840Table.semigroup [law10] :=
    FiniteCertificate.checkModels_sound core840Table [law10] toFin4 (by decide)
  exact checked law10 (by decide)

theorem core840Models : Models core840Table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact core840Law00
  · exact core840Law01
  · exact core840Law02
  · exact core840Law03
  · exact core840Law04
  · exact core840Law05
  · exact core840Law06
  · exact core840Law07
  · exact core840Law08
  · exact core840Law09
  · exact core840Law10

theorem core400Valid_core840Valid (identity : Identity Nat)
    (valid : identity.SatisfiedBy core400Table.semigroup) :
    identity.SatisfiedBy core840Table.semigroup := by
  have derived := Generated.S5_400PublishedRoots.S5_400.representativeBasisFor.2 identity valid
  exact derived.sound Generated.S5_400PublishedRoots.S5_840.models

namespace S6_8206

def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else if b = 3 then 0 else if b = 4 then 0 else 0) else
  if a = 1 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else if b = 3 then 0 else if b = 4 then 0 else 1) else
  if a = 2 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else if b = 3 then 0 else if b = 4 then 2 else 2) else
  if a = 3 then (if b = 0 then 3 else if b = 1 then 3 else if b = 2 then 3 else if b = 3 then 3 else if b = 4 then 3 else 3) else
  if a = 4 then (if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 0 else if b = 3 then 0 else if b = 4 then 4 else 4) else
  (if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 2 else if b = 3 then 0 else if b = 4 then 4 else 5)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def catalogueRows : List (List Nat) := [[1,1,1,1,1,1],[1,1,1,1,1,2],[1,1,1,1,3,3],[4,4,4,4,4,4],[1,2,1,1,5,5],[1,2,3,1,5,6]]

theorem catalogueRows_exact :
    List.ofFn (fun a : Fin 6 => List.ofFn (fun b : Fin 6 => (mul a b).val + 1)) = catalogueRows := by decide

private theorem literalLaw00 : law00.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law00] :=
    FiniteCertificate.checkModels_sound table [law00] toFin1 (by decide)
  exact checked law00 (by decide)

private theorem literalLaw01 : law01.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law01] :=
    FiniteCertificate.checkModels_sound table [law01] toFin2 (by decide)
  exact checked law01 (by decide)

private theorem literalLaw02 : law02.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law02] :=
    FiniteCertificate.checkModels_sound table [law02] toFin2 (by decide)
  exact checked law02 (by decide)

private theorem literalLaw03 : law03.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law03] :=
    FiniteCertificate.checkModels_sound table [law03] toFin2 (by decide)
  exact checked law03 (by decide)

private theorem literalLaw04 : law04.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law04] :=
    FiniteCertificate.checkModels_sound table [law04] toFin2 (by decide)
  exact checked law04 (by decide)

private theorem literalLaw05 : law05.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law05] :=
    FiniteCertificate.checkModels_sound table [law05] toFin3 (by decide)
  exact checked law05 (by decide)

private theorem literalLaw06 : law06.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law06] :=
    FiniteCertificate.checkModels_sound table [law06] toFin3 (by decide)
  exact checked law06 (by decide)

private theorem literalLaw07 : law07.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law07] :=
    FiniteCertificate.checkModels_sound table [law07] toFin3 (by decide)
  exact checked law07 (by decide)

private theorem literalLaw08 : law08.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law08] :=
    FiniteCertificate.checkModels_sound table [law08] toFin4 (by decide)
  exact checked law08 (by decide)

private theorem literalLaw09 : law09.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law09] :=
    FiniteCertificate.checkModels_sound table [law09] toFin4 (by decide)
  exact checked law09 (by decide)

private theorem literalLaw10 : law10.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law10] :=
    FiniteCertificate.checkModels_sound table [law10] toFin4 (by decide)
  exact checked law10 (by decide)

theorem literalModels : Models table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact literalLaw00
  · exact literalLaw01
  · exact literalLaw02
  · exact literalLaw03
  · exact literalLaw04
  · exact literalLaw05
  · exact literalLaw06
  · exact literalLaw07
  · exact literalLaw08
  · exact literalLaw09
  · exact literalLaw10

theorem models : Models table.semigroup basis := literalModels

def coreMap (a : Fin 5) : Fin 6 := if a = 0 then 0 else if a = 1 then 1 else if a = 2 then 2 else if a = 3 then 4 else 5

def coreEmbedding : Embedding core400Table.semigroup table.semigroup where
  toFun := coreMap
  map_mul := by decide
  injective := by intro a b; exact by decide +revert

theorem validCoreNative (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy core400Table.semigroup := coreEmbedding.pullback_identity identity valid

def initialMap (a : Fin 2) : Fin 6 := if a = 0 then 0 else 3

def initialEmbedding : Embedding initialTable.semigroup table.semigroup where
  toFun := initialMap
  map_mul := by decide
  injective := by intro a b; exact by decide +revert

theorem validInitial (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy initialTable.semigroup := initialEmbedding.pullback_identity identity valid

theorem validCore (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy core840Table.semigroup :=
  core400Valid_core840Valid identity (validCoreNative identity valid)

end S6_8206

namespace S6_8264

def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else if b = 3 then 0 else if b = 4 then 0 else 0) else
  if a = 1 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else if b = 3 then 0 else if b = 4 then 0 else 1) else
  if a = 2 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else if b = 3 then 2 else if b = 4 then 2 else 2) else
  if a = 3 then (if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 0 else if b = 3 then 3 else if b = 4 then 3 else 3) else
  if a = 4 then (if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 0 else if b = 3 then 4 else if b = 4 then 4 else 4) else
  (if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 2 else if b = 3 then 3 else if b = 4 then 3 else 5)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def catalogueRows : List (List Nat) := [[1,1,1,1,1,1],[1,1,1,1,1,2],[1,1,1,3,3,3],[1,2,1,4,4,4],[1,2,1,5,5,5],[1,2,3,4,4,6]]

theorem catalogueRows_exact :
    List.ofFn (fun a : Fin 6 => List.ofFn (fun b : Fin 6 => (mul a b).val + 1)) = catalogueRows := by decide

private theorem literalLaw00 : law00.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law00] :=
    FiniteCertificate.checkModels_sound table [law00] toFin1 (by decide)
  exact checked law00 (by decide)

private theorem literalLaw01 : law01.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law01] :=
    FiniteCertificate.checkModels_sound table [law01] toFin2 (by decide)
  exact checked law01 (by decide)

private theorem literalLaw02 : law02.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law02] :=
    FiniteCertificate.checkModels_sound table [law02] toFin2 (by decide)
  exact checked law02 (by decide)

private theorem literalLaw03 : law03.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law03] :=
    FiniteCertificate.checkModels_sound table [law03] toFin2 (by decide)
  exact checked law03 (by decide)

private theorem literalLaw04 : law04.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law04] :=
    FiniteCertificate.checkModels_sound table [law04] toFin2 (by decide)
  exact checked law04 (by decide)

private theorem literalLaw05 : law05.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law05] :=
    FiniteCertificate.checkModels_sound table [law05] toFin3 (by decide)
  exact checked law05 (by decide)

private theorem literalLaw06 : law06.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law06] :=
    FiniteCertificate.checkModels_sound table [law06] toFin3 (by decide)
  exact checked law06 (by decide)

private theorem literalLaw07 : law07.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law07] :=
    FiniteCertificate.checkModels_sound table [law07] toFin3 (by decide)
  exact checked law07 (by decide)

private theorem literalLaw08 : law08.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law08] :=
    FiniteCertificate.checkModels_sound table [law08] toFin4 (by decide)
  exact checked law08 (by decide)

private theorem literalLaw09 : law09.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law09] :=
    FiniteCertificate.checkModels_sound table [law09] toFin4 (by decide)
  exact checked law09 (by decide)

private theorem literalLaw10 : law10.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law10] :=
    FiniteCertificate.checkModels_sound table [law10] toFin4 (by decide)
  exact checked law10 (by decide)

theorem literalModels : Models table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact literalLaw00
  · exact literalLaw01
  · exact literalLaw02
  · exact literalLaw03
  · exact literalLaw04
  · exact literalLaw05
  · exact literalLaw06
  · exact literalLaw07
  · exact literalLaw08
  · exact literalLaw09
  · exact literalLaw10

theorem models : Models table.semigroup basis := literalModels

def coreMap (a : Fin 5) : Fin 6 := if a = 0 then 0 else if a = 1 then 1 else if a = 2 then 2 else if a = 3 then 3 else 5

def coreEmbedding : Embedding core400Table.semigroup table.semigroup where
  toFun := coreMap
  map_mul := by decide
  injective := by intro a b; exact by decide +revert

theorem validCoreNative (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy core400Table.semigroup := coreEmbedding.pullback_identity identity valid

def initialMap (a : Fin 2) : Fin 6 := if a = 0 then 3 else 4

def initialEmbedding : Embedding initialTable.semigroup table.semigroup where
  toFun := initialMap
  map_mul := by decide
  injective := by intro a b; exact by decide +revert

theorem validInitial (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy initialTable.semigroup := initialEmbedding.pullback_identity identity valid

theorem validCore (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy core840Table.semigroup :=
  core400Valid_core840Valid identity (validCoreNative identity valid)

end S6_8264

namespace S6_8486

def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else if b = 3 then 0 else if b = 4 then 0 else 0) else
  if a = 1 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else if b = 3 then 0 else if b = 4 then 1 else 1) else
  if a = 2 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else if b = 3 then 2 else if b = 4 then 2 else 2) else
  if a = 3 then (if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 0 else if b = 3 then 3 else if b = 4 then 3 else 3) else
  if a = 4 then (if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 2 else if b = 3 then 3 else if b = 4 then 4 else 4) else
  (if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 2 else if b = 3 then 3 else if b = 4 then 5 else 5)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def catalogueRows : List (List Nat) := [[1,1,1,1,1,1],[1,1,1,1,2,2],[1,1,1,3,3,3],[1,2,1,4,4,4],[1,2,3,4,5,5],[1,2,3,4,6,6]]

theorem catalogueRows_exact :
    List.ofFn (fun a : Fin 6 => List.ofFn (fun b : Fin 6 => (mul a b).val + 1)) = catalogueRows := by decide

private theorem literalLaw00 : law00.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law00] :=
    FiniteCertificate.checkModels_sound table [law00] toFin1 (by decide)
  exact checked law00 (by decide)

private theorem literalLaw01 : law01.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law01] :=
    FiniteCertificate.checkModels_sound table [law01] toFin2 (by decide)
  exact checked law01 (by decide)

private theorem literalLaw02 : law02.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law02] :=
    FiniteCertificate.checkModels_sound table [law02] toFin2 (by decide)
  exact checked law02 (by decide)

private theorem literalLaw03 : law03.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law03] :=
    FiniteCertificate.checkModels_sound table [law03] toFin2 (by decide)
  exact checked law03 (by decide)

private theorem literalLaw04 : law04.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law04] :=
    FiniteCertificate.checkModels_sound table [law04] toFin2 (by decide)
  exact checked law04 (by decide)

private theorem literalLaw05 : law05.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law05] :=
    FiniteCertificate.checkModels_sound table [law05] toFin3 (by decide)
  exact checked law05 (by decide)

private theorem literalLaw06 : law06.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law06] :=
    FiniteCertificate.checkModels_sound table [law06] toFin3 (by decide)
  exact checked law06 (by decide)

private theorem literalLaw07 : law07.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law07] :=
    FiniteCertificate.checkModels_sound table [law07] toFin3 (by decide)
  exact checked law07 (by decide)

private theorem literalLaw08 : law08.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law08] :=
    FiniteCertificate.checkModels_sound table [law08] toFin4 (by decide)
  exact checked law08 (by decide)

private theorem literalLaw09 : law09.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law09] :=
    FiniteCertificate.checkModels_sound table [law09] toFin4 (by decide)
  exact checked law09 (by decide)

private theorem literalLaw10 : law10.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law10] :=
    FiniteCertificate.checkModels_sound table [law10] toFin4 (by decide)
  exact checked law10 (by decide)

theorem literalModels : Models table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact literalLaw00
  · exact literalLaw01
  · exact literalLaw02
  · exact literalLaw03
  · exact literalLaw04
  · exact literalLaw05
  · exact literalLaw06
  · exact literalLaw07
  · exact literalLaw08
  · exact literalLaw09
  · exact literalLaw10

theorem models : Models table.semigroup basis := literalModels

def coreMap (a : Fin 5) : Fin 6 := if a = 0 then 0 else if a = 1 then 1 else if a = 2 then 2 else if a = 3 then 3 else 4

def coreEmbedding : Embedding core400Table.semigroup table.semigroup where
  toFun := coreMap
  map_mul := by decide
  injective := by intro a b; exact by decide +revert

theorem validCoreNative (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy core400Table.semigroup := coreEmbedding.pullback_identity identity valid

def initialMap (a : Fin 2) : Fin 6 := if a = 0 then 4 else 5

def initialEmbedding : Embedding initialTable.semigroup table.semigroup where
  toFun := initialMap
  map_mul := by decide
  injective := by intro a b; exact by decide +revert

theorem validInitial (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy initialTable.semigroup := initialEmbedding.pullback_identity identity valid

theorem validCore (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy core840Table.semigroup :=
  core400Valid_core840Valid identity (validCoreNative identity valid)

end S6_8486

namespace S6_13340

def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else if b = 3 then 0 else if b = 4 then 0 else 0) else
  if a = 1 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else if b = 3 then 0 else if b = 4 then 1 else 1) else
  if a = 2 then (if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 2 else if b = 3 then 0 else if b = 4 then 0 else 2) else
  if a = 3 then (if b = 0 then 3 else if b = 1 then 3 else if b = 2 then 3 else if b = 3 then 3 else if b = 4 then 3 else 3) else
  if a = 4 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else if b = 3 then 0 else if b = 4 then 4 else 4) else
  (if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 2 else if b = 3 then 0 else if b = 4 then 4 else 5)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def catalogueRows : List (List Nat) := [[1,1,1,1,1,1],[1,1,1,1,2,2],[1,2,3,1,1,3],[4,4,4,4,4,4],[1,1,1,1,5,5],[1,2,3,1,5,6]]

theorem catalogueRows_exact :
    List.ofFn (fun a : Fin 6 => List.ofFn (fun b : Fin 6 => (mul a b).val + 1)) = catalogueRows := by decide

private theorem literalLaw00 : law00.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law00] :=
    FiniteCertificate.checkModels_sound table [law00] toFin1 (by decide)
  exact checked law00 (by decide)

private theorem literalLaw01 : law01.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law01] :=
    FiniteCertificate.checkModels_sound table [law01] toFin2 (by decide)
  exact checked law01 (by decide)

private theorem literalLaw02 : law02.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law02] :=
    FiniteCertificate.checkModels_sound table [law02] toFin2 (by decide)
  exact checked law02 (by decide)

private theorem literalLaw03 : law03.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law03] :=
    FiniteCertificate.checkModels_sound table [law03] toFin2 (by decide)
  exact checked law03 (by decide)

private theorem literalLaw04 : law04.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law04] :=
    FiniteCertificate.checkModels_sound table [law04] toFin2 (by decide)
  exact checked law04 (by decide)

private theorem literalLaw05 : law05.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law05] :=
    FiniteCertificate.checkModels_sound table [law05] toFin3 (by decide)
  exact checked law05 (by decide)

private theorem literalLaw06 : law06.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law06] :=
    FiniteCertificate.checkModels_sound table [law06] toFin3 (by decide)
  exact checked law06 (by decide)

private theorem literalLaw07 : law07.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law07] :=
    FiniteCertificate.checkModels_sound table [law07] toFin3 (by decide)
  exact checked law07 (by decide)

private theorem literalLaw08 : law08.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law08] :=
    FiniteCertificate.checkModels_sound table [law08] toFin4 (by decide)
  exact checked law08 (by decide)

private theorem literalLaw09 : law09.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law09] :=
    FiniteCertificate.checkModels_sound table [law09] toFin4 (by decide)
  exact checked law09 (by decide)

private theorem literalLaw10 : law10.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law10] :=
    FiniteCertificate.checkModels_sound table [law10] toFin4 (by decide)
  exact checked law10 (by decide)

theorem literalModels : Models table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact literalLaw00
  · exact literalLaw01
  · exact literalLaw02
  · exact literalLaw03
  · exact literalLaw04
  · exact literalLaw05
  · exact literalLaw06
  · exact literalLaw07
  · exact literalLaw08
  · exact literalLaw09
  · exact literalLaw10

theorem models : Models table.semigroup basis := literalModels

def coreMap (a : Fin 5) : Fin 6 := if a = 0 then 0 else if a = 1 then 1 else if a = 2 then 2 else if a = 3 then 4 else 5

def coreEmbedding : Embedding core840Table.semigroup table.semigroup where
  toFun := coreMap
  map_mul := by decide
  injective := by intro a b; exact by decide +revert

theorem validCoreNative (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy core840Table.semigroup := coreEmbedding.pullback_identity identity valid

def initialMap (a : Fin 2) : Fin 6 := if a = 0 then 0 else 3

def initialEmbedding : Embedding initialTable.semigroup table.semigroup where
  toFun := initialMap
  map_mul := by decide
  injective := by intro a b; exact by decide +revert

theorem validInitial (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy initialTable.semigroup := initialEmbedding.pullback_identity identity valid

theorem validCore (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy core840Table.semigroup :=
  validCoreNative identity valid

end S6_13340

namespace S6_13376

def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else if b = 3 then 0 else if b = 4 then 0 else 0) else
  if a = 1 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else if b = 3 then 0 else if b = 4 then 1 else 1) else
  if a = 2 then (if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 2 else if b = 3 then 2 else if b = 4 then 0 else 2) else
  if a = 3 then (if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 3 else if b = 3 then 3 else if b = 4 then 0 else 3) else
  if a = 4 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else if b = 3 then 0 else if b = 4 then 4 else 4) else
  (if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 2 else if b = 3 then 2 else if b = 4 then 4 else 5)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def catalogueRows : List (List Nat) := [[1,1,1,1,1,1],[1,1,1,1,2,2],[1,2,3,3,1,3],[1,2,4,4,1,4],[1,1,1,1,5,5],[1,2,3,3,5,6]]

theorem catalogueRows_exact :
    List.ofFn (fun a : Fin 6 => List.ofFn (fun b : Fin 6 => (mul a b).val + 1)) = catalogueRows := by decide

private theorem literalLaw00 : law00.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law00] :=
    FiniteCertificate.checkModels_sound table [law00] toFin1 (by decide)
  exact checked law00 (by decide)

private theorem literalLaw01 : law01.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law01] :=
    FiniteCertificate.checkModels_sound table [law01] toFin2 (by decide)
  exact checked law01 (by decide)

private theorem literalLaw02 : law02.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law02] :=
    FiniteCertificate.checkModels_sound table [law02] toFin2 (by decide)
  exact checked law02 (by decide)

private theorem literalLaw03 : law03.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law03] :=
    FiniteCertificate.checkModels_sound table [law03] toFin2 (by decide)
  exact checked law03 (by decide)

private theorem literalLaw04 : law04.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law04] :=
    FiniteCertificate.checkModels_sound table [law04] toFin2 (by decide)
  exact checked law04 (by decide)

private theorem literalLaw05 : law05.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law05] :=
    FiniteCertificate.checkModels_sound table [law05] toFin3 (by decide)
  exact checked law05 (by decide)

private theorem literalLaw06 : law06.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law06] :=
    FiniteCertificate.checkModels_sound table [law06] toFin3 (by decide)
  exact checked law06 (by decide)

private theorem literalLaw07 : law07.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law07] :=
    FiniteCertificate.checkModels_sound table [law07] toFin3 (by decide)
  exact checked law07 (by decide)

private theorem literalLaw08 : law08.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law08] :=
    FiniteCertificate.checkModels_sound table [law08] toFin4 (by decide)
  exact checked law08 (by decide)

private theorem literalLaw09 : law09.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law09] :=
    FiniteCertificate.checkModels_sound table [law09] toFin4 (by decide)
  exact checked law09 (by decide)

private theorem literalLaw10 : law10.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law10] :=
    FiniteCertificate.checkModels_sound table [law10] toFin4 (by decide)
  exact checked law10 (by decide)

theorem literalModels : Models table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact literalLaw00
  · exact literalLaw01
  · exact literalLaw02
  · exact literalLaw03
  · exact literalLaw04
  · exact literalLaw05
  · exact literalLaw06
  · exact literalLaw07
  · exact literalLaw08
  · exact literalLaw09
  · exact literalLaw10

theorem models : Models table.semigroup basis := literalModels

def coreMap (a : Fin 5) : Fin 6 := if a = 0 then 0 else if a = 1 then 1 else if a = 2 then 2 else if a = 3 then 4 else 5

def coreEmbedding : Embedding core840Table.semigroup table.semigroup where
  toFun := coreMap
  map_mul := by decide
  injective := by intro a b; exact by decide +revert

theorem validCoreNative (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy core840Table.semigroup := coreEmbedding.pullback_identity identity valid

def initialMap (a : Fin 2) : Fin 6 := if a = 0 then 2 else 3

def initialEmbedding : Embedding initialTable.semigroup table.semigroup where
  toFun := initialMap
  map_mul := by decide
  injective := by intro a b; exact by decide +revert

theorem validInitial (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy initialTable.semigroup := initialEmbedding.pullback_identity identity valid

theorem validCore (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy core840Table.semigroup :=
  validCoreNative identity valid

end S6_13376

namespace S6_13610

def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else if b = 3 then 0 else if b = 4 then 0 else 0) else
  if a = 1 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else if b = 3 then 1 else if b = 4 then 1 else 1) else
  if a = 2 then (if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 2 else if b = 3 then 0 else if b = 4 then 2 else 2) else
  if a = 3 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else if b = 3 then 3 else if b = 4 then 3 else 3) else
  if a = 4 then (if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 2 else if b = 3 then 3 else if b = 4 then 4 else 4) else
  (if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 2 else if b = 3 then 3 else if b = 4 then 5 else 5)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def catalogueRows : List (List Nat) := [[1,1,1,1,1,1],[1,1,1,2,2,2],[1,2,3,1,3,3],[1,1,1,4,4,4],[1,2,3,4,5,5],[1,2,3,4,6,6]]

theorem catalogueRows_exact :
    List.ofFn (fun a : Fin 6 => List.ofFn (fun b : Fin 6 => (mul a b).val + 1)) = catalogueRows := by decide

private theorem literalLaw00 : law00.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law00] :=
    FiniteCertificate.checkModels_sound table [law00] toFin1 (by decide)
  exact checked law00 (by decide)

private theorem literalLaw01 : law01.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law01] :=
    FiniteCertificate.checkModels_sound table [law01] toFin2 (by decide)
  exact checked law01 (by decide)

private theorem literalLaw02 : law02.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law02] :=
    FiniteCertificate.checkModels_sound table [law02] toFin2 (by decide)
  exact checked law02 (by decide)

private theorem literalLaw03 : law03.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law03] :=
    FiniteCertificate.checkModels_sound table [law03] toFin2 (by decide)
  exact checked law03 (by decide)

private theorem literalLaw04 : law04.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law04] :=
    FiniteCertificate.checkModels_sound table [law04] toFin2 (by decide)
  exact checked law04 (by decide)

private theorem literalLaw05 : law05.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law05] :=
    FiniteCertificate.checkModels_sound table [law05] toFin3 (by decide)
  exact checked law05 (by decide)

private theorem literalLaw06 : law06.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law06] :=
    FiniteCertificate.checkModels_sound table [law06] toFin3 (by decide)
  exact checked law06 (by decide)

private theorem literalLaw07 : law07.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law07] :=
    FiniteCertificate.checkModels_sound table [law07] toFin3 (by decide)
  exact checked law07 (by decide)

private theorem literalLaw08 : law08.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law08] :=
    FiniteCertificate.checkModels_sound table [law08] toFin4 (by decide)
  exact checked law08 (by decide)

private theorem literalLaw09 : law09.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law09] :=
    FiniteCertificate.checkModels_sound table [law09] toFin4 (by decide)
  exact checked law09 (by decide)

private theorem literalLaw10 : law10.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law10] :=
    FiniteCertificate.checkModels_sound table [law10] toFin4 (by decide)
  exact checked law10 (by decide)

theorem literalModels : Models table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact literalLaw00
  · exact literalLaw01
  · exact literalLaw02
  · exact literalLaw03
  · exact literalLaw04
  · exact literalLaw05
  · exact literalLaw06
  · exact literalLaw07
  · exact literalLaw08
  · exact literalLaw09
  · exact literalLaw10

theorem models : Models table.semigroup basis := literalModels

def coreMap (a : Fin 5) : Fin 6 := if a = 0 then 0 else if a = 1 then 1 else if a = 2 then 2 else if a = 3 then 3 else 4

def coreEmbedding : Embedding core840Table.semigroup table.semigroup where
  toFun := coreMap
  map_mul := by decide
  injective := by intro a b; exact by decide +revert

theorem validCoreNative (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy core840Table.semigroup := coreEmbedding.pullback_identity identity valid

def initialMap (a : Fin 2) : Fin 6 := if a = 0 then 4 else 5

def initialEmbedding : Embedding initialTable.semigroup table.semigroup where
  toFun := initialMap
  map_mul := by decide
  injective := by intro a b; exact by decide +revert

theorem validInitial (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy initialTable.semigroup := initialEmbedding.pullback_identity identity valid

theorem validCore (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy core840Table.semigroup :=
  validCoreNative identity valid

end S6_13610


end SemigroupBasis.CoRoots.Order6Day11.FordLordPeriodOne
