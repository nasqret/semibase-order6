import SemigroupBasis.CoRoots.Order6Day11.FordLast8.FordLastPrefixLift
import SemigroupBasis.Examples.LeftZeroTwo
import SemigroupBasis.Transfer

/-! Eight literal tables, sixteen embeddings, and exact dual-signature transport for the two opposite cores. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day11.FordLast8

open SemigroupBasis

abbrev initialTable : FiniteTable := Examples.leftZeroTwo
abbrev core354Table : FiniteTable := Generated.Catalogue.S5_354.table

def core381OppositeTable : FiniteTable where
  order := 5
  mul := fun a b => Generated.Catalogue.S5_381.table.mul b a
  assoc := by decide

def core610OppositeTable : FiniteTable where
  order := 5
  mul := fun a b => Generated.Catalogue.S5_610.table.mul b a
  assoc := by decide

private def toFin1 : Nat → Fin 1
  | _ => 0
private def toFin2 : Nat → Fin 2
  | 0 => 0
  | _ => 1
private def toFin3 : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

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
    FiniteCertificate.checkModels_sound initialTable [law04] toFin3 (by decide)
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
    FiniteCertificate.checkModels_sound initialTable [law07] toFin2 (by decide)
  exact checked law07 (by decide)

private theorem initialLaw08 : law08.SatisfiedBy initialTable.semigroup := by
  have checked : Models initialTable.semigroup [law08] :=
    FiniteCertificate.checkModels_sound initialTable [law08] toFin3 (by decide)
  exact checked law08 (by decide)

theorem initialModels : Models initialTable.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact initialLaw00
  · exact initialLaw01
  · exact initialLaw02
  · exact initialLaw03
  · exact initialLaw04
  · exact initialLaw05
  · exact initialLaw06
  · exact initialLaw07
  · exact initialLaw08

private theorem coreLaw00 : law00.SatisfiedBy coreTable.semigroup := by
  have checked : Models coreTable.semigroup [law00] :=
    FiniteCertificate.checkModels_sound coreTable [law00] toFin1 (by decide)
  exact checked law00 (by decide)

private theorem coreLaw01 : law01.SatisfiedBy coreTable.semigroup := by
  have checked : Models coreTable.semigroup [law01] :=
    FiniteCertificate.checkModels_sound coreTable [law01] toFin2 (by decide)
  exact checked law01 (by decide)

private theorem coreLaw02 : law02.SatisfiedBy coreTable.semigroup := by
  have checked : Models coreTable.semigroup [law02] :=
    FiniteCertificate.checkModels_sound coreTable [law02] toFin2 (by decide)
  exact checked law02 (by decide)

private theorem coreLaw03 : law03.SatisfiedBy coreTable.semigroup := by
  have checked : Models coreTable.semigroup [law03] :=
    FiniteCertificate.checkModels_sound coreTable [law03] toFin2 (by decide)
  exact checked law03 (by decide)

private theorem coreLaw04 : law04.SatisfiedBy coreTable.semigroup := by
  have checked : Models coreTable.semigroup [law04] :=
    FiniteCertificate.checkModels_sound coreTable [law04] toFin3 (by decide)
  exact checked law04 (by decide)

private theorem coreLaw05 : law05.SatisfiedBy coreTable.semigroup := by
  have checked : Models coreTable.semigroup [law05] :=
    FiniteCertificate.checkModels_sound coreTable [law05] toFin3 (by decide)
  exact checked law05 (by decide)

private theorem coreLaw06 : law06.SatisfiedBy coreTable.semigroup := by
  have checked : Models coreTable.semigroup [law06] :=
    FiniteCertificate.checkModels_sound coreTable [law06] toFin3 (by decide)
  exact checked law06 (by decide)

private theorem coreLaw07 : law07.SatisfiedBy coreTable.semigroup := by
  have checked : Models coreTable.semigroup [law07] :=
    FiniteCertificate.checkModels_sound coreTable [law07] toFin2 (by decide)
  exact checked law07 (by decide)

private theorem coreLaw08 : law08.SatisfiedBy coreTable.semigroup := by
  have checked : Models coreTable.semigroup [law08] :=
    FiniteCertificate.checkModels_sound coreTable [law08] toFin3 (by decide)
  exact checked law08 (by decide)

theorem coreModels : Models coreTable.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact coreLaw00
  · exact coreLaw01
  · exact coreLaw02
  · exact coreLaw03
  · exact coreLaw04
  · exact coreLaw05
  · exact coreLaw06
  · exact coreLaw07
  · exact coreLaw08

theorem core354Valid_commonCore (identity : Identity Nat)
    (valid : identity.SatisfiedBy core354Table.semigroup) :
    identity.SatisfiedBy coreTable.semigroup := by
  have derived := SemigroupBasis.CoRoots.S5_348Family.S5_354.basis_complete.2 identity valid
  exact derived.sound SemigroupBasis.CoRoots.S5_348Family.S5_348.models

theorem core381OppositeValid_commonCore (identity : Identity Nat)
    (valid : identity.SatisfiedBy core381OppositeTable.semigroup) :
    identity.SatisfiedBy coreTable.semigroup := by
  have oppositeValid : identity.SatisfiedBy Generated.Catalogue.S5_381.table.semigroup.opposite := valid
  have reversedValid := (Identity.satisfiedBy_opposite_iff_reversed identity
    Generated.Catalogue.S5_381.table.semigroup).mp oppositeValid
  have dual := SemigroupBasis.CoRoots.S5_381FamilyInvariant.S5_381.valid_sameSignature
    identity.reversed reversedValid
  have same : LowerSignature identity.lhs identity.rhs :=
    Examples.SimpleSequenceFirstGap.SameSignature.ofDual
      (left := identity.lhs) (right := identity.rhs) dual
  have derived := SemigroupBasis.CoRoots.S5_348.derives_of_sameSimpleSequenceFirstGapFinalSignature same
  exact derived.sound SemigroupBasis.CoRoots.S5_348Family.S5_348.models

theorem core610OppositeValid_commonCore (identity : Identity Nat)
    (valid : identity.SatisfiedBy core610OppositeTable.semigroup) :
    identity.SatisfiedBy coreTable.semigroup := by
  have oppositeValid : identity.SatisfiedBy Generated.Catalogue.S5_610.table.semigroup.opposite := valid
  have reversedValid := (Identity.satisfiedBy_opposite_iff_reversed identity
    Generated.Catalogue.S5_610.table.semigroup).mp oppositeValid
  have dual := SemigroupBasis.CoRoots.S5_381FamilyInvariant.S5_610.valid_sameSignature
    identity.reversed reversedValid
  have same : LowerSignature identity.lhs identity.rhs :=
    Examples.SimpleSequenceFirstGap.SameSignature.ofDual
      (left := identity.lhs) (right := identity.rhs) dual
  have derived := SemigroupBasis.CoRoots.S5_348.derives_of_sameSimpleSequenceFirstGapFinalSignature same
  exact derived.sound SemigroupBasis.CoRoots.S5_348Family.S5_348.models

namespace S6_7628

def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else if b = 3 then 0 else if b = 4 then 0 else 0) else
  if a = 1 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else if b = 3 then 0 else if b = 4 then 0 else 0) else
  if a = 2 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else if b = 3 then 0 else if b = 4 then 2 else 2) else
  if a = 3 then (if b = 0 then 3 else if b = 1 then 3 else if b = 2 then 3 else if b = 3 then 3 else if b = 4 then 3 else 3) else
  if a = 4 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else if b = 3 then 0 else if b = 4 then 4 else 4) else
  (if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 2 else if b = 3 then 0 else if b = 4 then 4 else 5)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def catalogueRows : List (List Nat) := [[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,3,3],[4,4,4,4,4,4],[1,1,1,1,5,5],[1,2,3,1,5,6]]

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
    FiniteCertificate.checkModels_sound table [law04] toFin3 (by decide)
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
    FiniteCertificate.checkModels_sound table [law07] toFin2 (by decide)
  exact checked law07 (by decide)

private theorem literalLaw08 : law08.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law08] :=
    FiniteCertificate.checkModels_sound table [law08] toFin3 (by decide)
  exact checked law08 (by decide)

theorem literalModels : Models table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact literalLaw00
  · exact literalLaw01
  · exact literalLaw02
  · exact literalLaw03
  · exact literalLaw04
  · exact literalLaw05
  · exact literalLaw06
  · exact literalLaw07
  · exact literalLaw08

theorem models : Models table.semigroup basis := literalModels

def coreMap (a : Fin 5) : Fin 6 := if a = 0 then 0 else if a = 1 then 1 else if a = 2 then 2 else if a = 3 then 4 else 5

def coreEmbedding : Embedding coreTable.semigroup table.semigroup where
  toFun := coreMap
  map_mul := by decide
  injective := by intro a b; exact by decide +revert

theorem validCoreNative (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy coreTable.semigroup := coreEmbedding.pullback_identity identity valid

def initialMap (a : Fin 2) : Fin 6 := if a = 0 then 0 else 3

def initialEmbedding : Embedding initialTable.semigroup table.semigroup where
  toFun := initialMap
  map_mul := by decide
  injective := by intro a b; exact by decide +revert

theorem validInitial (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy initialTable.semigroup := initialEmbedding.pullback_identity identity valid

theorem validCore (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy coreTable.semigroup :=
  validCoreNative identity valid

end S6_7628

namespace S6_7653

def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else if b = 3 then 0 else if b = 4 then 0 else 0) else
  if a = 1 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else if b = 3 then 0 else if b = 4 then 0 else 0) else
  if a = 2 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else if b = 3 then 0 else if b = 4 then 2 else 2) else
  if a = 3 then (if b = 0 then 3 else if b = 1 then 3 else if b = 2 then 3 else if b = 3 then 3 else if b = 4 then 3 else 3) else
  if a = 4 then (if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 0 else if b = 3 then 0 else if b = 4 then 4 else 4) else
  (if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 2 else if b = 3 then 0 else if b = 4 then 4 else 5)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def catalogueRows : List (List Nat) := [[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,3,3],[4,4,4,4,4,4],[1,2,1,1,5,5],[1,2,3,1,5,6]]

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
    FiniteCertificate.checkModels_sound table [law04] toFin3 (by decide)
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
    FiniteCertificate.checkModels_sound table [law07] toFin2 (by decide)
  exact checked law07 (by decide)

private theorem literalLaw08 : law08.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law08] :=
    FiniteCertificate.checkModels_sound table [law08] toFin3 (by decide)
  exact checked law08 (by decide)

theorem literalModels : Models table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact literalLaw00
  · exact literalLaw01
  · exact literalLaw02
  · exact literalLaw03
  · exact literalLaw04
  · exact literalLaw05
  · exact literalLaw06
  · exact literalLaw07
  · exact literalLaw08

theorem models : Models table.semigroup basis := literalModels

def coreMap (a : Fin 5) : Fin 6 := if a = 0 then 0 else if a = 1 then 1 else if a = 2 then 2 else if a = 3 then 4 else 5

def coreEmbedding : Embedding core354Table.semigroup table.semigroup where
  toFun := coreMap
  map_mul := by decide
  injective := by intro a b; exact by decide +revert

theorem validCoreNative (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy core354Table.semigroup := coreEmbedding.pullback_identity identity valid

def initialMap (a : Fin 2) : Fin 6 := if a = 0 then 0 else 3

def initialEmbedding : Embedding initialTable.semigroup table.semigroup where
  toFun := initialMap
  map_mul := by decide
  injective := by intro a b; exact by decide +revert

theorem validInitial (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy initialTable.semigroup := initialEmbedding.pullback_identity identity valid

theorem validCore (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy coreTable.semigroup :=
  core354Valid_commonCore identity (validCoreNative identity valid)

end S6_7653

namespace S6_7682

def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else if b = 3 then 0 else if b = 4 then 0 else 0) else
  if a = 1 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else if b = 3 then 0 else if b = 4 then 0 else 0) else
  if a = 2 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else if b = 3 then 2 else if b = 4 then 2 else 2) else
  if a = 3 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else if b = 3 then 3 else if b = 4 then 3 else 3) else
  if a = 4 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else if b = 3 then 4 else if b = 4 then 4 else 4) else
  (if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 2 else if b = 3 then 3 else if b = 4 then 3 else 5)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def catalogueRows : List (List Nat) := [[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,3,3,3],[1,1,1,4,4,4],[1,1,1,5,5,5],[1,2,3,4,4,6]]

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
    FiniteCertificate.checkModels_sound table [law04] toFin3 (by decide)
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
    FiniteCertificate.checkModels_sound table [law07] toFin2 (by decide)
  exact checked law07 (by decide)

private theorem literalLaw08 : law08.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law08] :=
    FiniteCertificate.checkModels_sound table [law08] toFin3 (by decide)
  exact checked law08 (by decide)

theorem literalModels : Models table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact literalLaw00
  · exact literalLaw01
  · exact literalLaw02
  · exact literalLaw03
  · exact literalLaw04
  · exact literalLaw05
  · exact literalLaw06
  · exact literalLaw07
  · exact literalLaw08

theorem models : Models table.semigroup basis := literalModels

def coreMap (a : Fin 5) : Fin 6 := if a = 0 then 0 else if a = 1 then 1 else if a = 2 then 2 else if a = 3 then 3 else 5

def coreEmbedding : Embedding coreTable.semigroup table.semigroup where
  toFun := coreMap
  map_mul := by decide
  injective := by intro a b; exact by decide +revert

theorem validCoreNative (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy coreTable.semigroup := coreEmbedding.pullback_identity identity valid

def initialMap (a : Fin 2) : Fin 6 := if a = 0 then 3 else 4

def initialEmbedding : Embedding initialTable.semigroup table.semigroup where
  toFun := initialMap
  map_mul := by decide
  injective := by intro a b; exact by decide +revert

theorem validInitial (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy initialTable.semigroup := initialEmbedding.pullback_identity identity valid

theorem validCore (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy coreTable.semigroup :=
  validCoreNative identity valid

end S6_7682

namespace S6_7688

def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else if b = 3 then 0 else if b = 4 then 0 else 0) else
  if a = 1 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else if b = 3 then 0 else if b = 4 then 0 else 0) else
  if a = 2 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else if b = 3 then 2 else if b = 4 then 2 else 2) else
  if a = 3 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else if b = 3 then 3 else if b = 4 then 3 else 3) else
  if a = 4 then (if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 2 else if b = 3 then 3 else if b = 4 then 4 else 4) else
  (if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 2 else if b = 3 then 3 else if b = 4 then 5 else 5)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def catalogueRows : List (List Nat) := [[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,3,3,3],[1,1,1,4,4,4],[1,2,3,4,5,5],[1,2,3,4,6,6]]

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
    FiniteCertificate.checkModels_sound table [law04] toFin3 (by decide)
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
    FiniteCertificate.checkModels_sound table [law07] toFin2 (by decide)
  exact checked law07 (by decide)

private theorem literalLaw08 : law08.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law08] :=
    FiniteCertificate.checkModels_sound table [law08] toFin3 (by decide)
  exact checked law08 (by decide)

theorem literalModels : Models table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact literalLaw00
  · exact literalLaw01
  · exact literalLaw02
  · exact literalLaw03
  · exact literalLaw04
  · exact literalLaw05
  · exact literalLaw06
  · exact literalLaw07
  · exact literalLaw08

theorem models : Models table.semigroup basis := literalModels

def coreMap (a : Fin 5) : Fin 6 := if a = 0 then 0 else if a = 1 then 1 else if a = 2 then 2 else if a = 3 then 3 else 4

def coreEmbedding : Embedding coreTable.semigroup table.semigroup where
  toFun := coreMap
  map_mul := by decide
  injective := by intro a b; exact by decide +revert

theorem validCoreNative (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy coreTable.semigroup := coreEmbedding.pullback_identity identity valid

def initialMap (a : Fin 2) : Fin 6 := if a = 0 then 4 else 5

def initialEmbedding : Embedding initialTable.semigroup table.semigroup where
  toFun := initialMap
  map_mul := by decide
  injective := by intro a b; exact by decide +revert

theorem validInitial (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy initialTable.semigroup := initialEmbedding.pullback_identity identity valid

theorem validCore (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy coreTable.semigroup :=
  validCoreNative identity valid

end S6_7688

namespace S6_7715

def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else if b = 3 then 0 else if b = 4 then 0 else 0) else
  if a = 1 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else if b = 3 then 0 else if b = 4 then 0 else 0) else
  if a = 2 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else if b = 3 then 2 else if b = 4 then 2 else 2) else
  if a = 3 then (if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 0 else if b = 3 then 3 else if b = 4 then 3 else 3) else
  if a = 4 then (if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 0 else if b = 3 then 4 else if b = 4 then 4 else 4) else
  (if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 2 else if b = 3 then 3 else if b = 4 then 3 else 5)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def catalogueRows : List (List Nat) := [[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,3,3,3],[1,2,1,4,4,4],[1,2,1,5,5,5],[1,2,3,4,4,6]]

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
    FiniteCertificate.checkModels_sound table [law04] toFin3 (by decide)
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
    FiniteCertificate.checkModels_sound table [law07] toFin2 (by decide)
  exact checked law07 (by decide)

private theorem literalLaw08 : law08.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law08] :=
    FiniteCertificate.checkModels_sound table [law08] toFin3 (by decide)
  exact checked law08 (by decide)

theorem literalModels : Models table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact literalLaw00
  · exact literalLaw01
  · exact literalLaw02
  · exact literalLaw03
  · exact literalLaw04
  · exact literalLaw05
  · exact literalLaw06
  · exact literalLaw07
  · exact literalLaw08

theorem models : Models table.semigroup basis := literalModels

def coreMap (a : Fin 5) : Fin 6 := if a = 0 then 0 else if a = 1 then 1 else if a = 2 then 2 else if a = 3 then 3 else 5

def coreEmbedding : Embedding core354Table.semigroup table.semigroup where
  toFun := coreMap
  map_mul := by decide
  injective := by intro a b; exact by decide +revert

theorem validCoreNative (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy core354Table.semigroup := coreEmbedding.pullback_identity identity valid

def initialMap (a : Fin 2) : Fin 6 := if a = 0 then 3 else 4

def initialEmbedding : Embedding initialTable.semigroup table.semigroup where
  toFun := initialMap
  map_mul := by decide
  injective := by intro a b; exact by decide +revert

theorem validInitial (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy initialTable.semigroup := initialEmbedding.pullback_identity identity valid

theorem validCore (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy coreTable.semigroup :=
  core354Valid_commonCore identity (validCoreNative identity valid)

end S6_7715

namespace S6_7718

def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else if b = 3 then 0 else if b = 4 then 0 else 0) else
  if a = 1 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else if b = 3 then 0 else if b = 4 then 0 else 0) else
  if a = 2 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else if b = 3 then 2 else if b = 4 then 2 else 2) else
  if a = 3 then (if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 0 else if b = 3 then 3 else if b = 4 then 3 else 3) else
  if a = 4 then (if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 2 else if b = 3 then 3 else if b = 4 then 4 else 4) else
  (if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 2 else if b = 3 then 3 else if b = 4 then 5 else 5)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def catalogueRows : List (List Nat) := [[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,3,3,3],[1,2,1,4,4,4],[1,2,3,4,5,5],[1,2,3,4,6,6]]

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
    FiniteCertificate.checkModels_sound table [law04] toFin3 (by decide)
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
    FiniteCertificate.checkModels_sound table [law07] toFin2 (by decide)
  exact checked law07 (by decide)

private theorem literalLaw08 : law08.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law08] :=
    FiniteCertificate.checkModels_sound table [law08] toFin3 (by decide)
  exact checked law08 (by decide)

theorem literalModels : Models table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact literalLaw00
  · exact literalLaw01
  · exact literalLaw02
  · exact literalLaw03
  · exact literalLaw04
  · exact literalLaw05
  · exact literalLaw06
  · exact literalLaw07
  · exact literalLaw08

theorem models : Models table.semigroup basis := literalModels

def coreMap (a : Fin 5) : Fin 6 := if a = 0 then 0 else if a = 1 then 1 else if a = 2 then 2 else if a = 3 then 3 else 4

def coreEmbedding : Embedding core354Table.semigroup table.semigroup where
  toFun := coreMap
  map_mul := by decide
  injective := by intro a b; exact by decide +revert

theorem validCoreNative (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy core354Table.semigroup := coreEmbedding.pullback_identity identity valid

def initialMap (a : Fin 2) : Fin 6 := if a = 0 then 4 else 5

def initialEmbedding : Embedding initialTable.semigroup table.semigroup where
  toFun := initialMap
  map_mul := by decide
  injective := by intro a b; exact by decide +revert

theorem validInitial (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy initialTable.semigroup := initialEmbedding.pullback_identity identity valid

theorem validCore (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy coreTable.semigroup :=
  core354Valid_commonCore identity (validCoreNative identity valid)

end S6_7718

namespace S6_8332

def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else if b = 3 then 0 else if b = 4 then 0 else 0) else
  if a = 1 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else if b = 3 then 0 else if b = 4 then 1 else 1) else
  if a = 2 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else if b = 3 then 0 else if b = 4 then 1 else 1) else
  if a = 3 then (if b = 0 then 3 else if b = 1 then 3 else if b = 2 then 3 else if b = 3 then 3 else if b = 4 then 3 else 3) else
  if a = 4 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else if b = 3 then 0 else if b = 4 then 4 else 4) else
  (if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 2 else if b = 3 then 0 else if b = 4 then 4 else 5)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def catalogueRows : List (List Nat) := [[1,1,1,1,1,1],[1,1,1,1,2,2],[1,1,1,1,2,2],[4,4,4,4,4,4],[1,1,1,1,5,5],[1,2,3,1,5,6]]

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
    FiniteCertificate.checkModels_sound table [law04] toFin3 (by decide)
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
    FiniteCertificate.checkModels_sound table [law07] toFin2 (by decide)
  exact checked law07 (by decide)

private theorem literalLaw08 : law08.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law08] :=
    FiniteCertificate.checkModels_sound table [law08] toFin3 (by decide)
  exact checked law08 (by decide)

theorem literalModels : Models table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact literalLaw00
  · exact literalLaw01
  · exact literalLaw02
  · exact literalLaw03
  · exact literalLaw04
  · exact literalLaw05
  · exact literalLaw06
  · exact literalLaw07
  · exact literalLaw08

theorem models : Models table.semigroup basis := literalModels

def coreMap (a : Fin 5) : Fin 6 := if a = 0 then 0 else if a = 1 then 1 else if a = 2 then 2 else if a = 3 then 4 else 5

def coreEmbedding : Embedding core381OppositeTable.semigroup table.semigroup where
  toFun := coreMap
  map_mul := by decide
  injective := by intro a b; exact by decide +revert

theorem validCoreNative (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy core381OppositeTable.semigroup := coreEmbedding.pullback_identity identity valid

def initialMap (a : Fin 2) : Fin 6 := if a = 0 then 0 else 3

def initialEmbedding : Embedding initialTable.semigroup table.semigroup where
  toFun := initialMap
  map_mul := by decide
  injective := by intro a b; exact by decide +revert

theorem validInitial (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy initialTable.semigroup := initialEmbedding.pullback_identity identity valid

theorem validCore (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy coreTable.semigroup :=
  core381OppositeValid_commonCore identity (validCoreNative identity valid)

end S6_8332

namespace S6_11425

def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else if b = 3 then 0 else if b = 4 then 0 else 0) else
  if a = 1 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 1 else if b = 3 then 1 else if b = 4 then 0 else 1) else
  if a = 2 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 2 else if b = 3 then 2 else if b = 4 then 0 else 2) else
  if a = 3 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 2 else if b = 3 then 2 else if b = 4 then 0 else 2) else
  if a = 4 then (if b = 0 then 4 else if b = 1 then 4 else if b = 2 then 4 else if b = 3 then 4 else if b = 4 then 4 else 4) else
  (if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 2 else if b = 3 then 3 else if b = 4 then 0 else 5)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def catalogueRows : List (List Nat) := [[1,1,1,1,1,1],[1,1,2,2,1,2],[1,1,3,3,1,3],[1,1,3,3,1,3],[5,5,5,5,5,5],[1,2,3,4,1,6]]

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
    FiniteCertificate.checkModels_sound table [law04] toFin3 (by decide)
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
    FiniteCertificate.checkModels_sound table [law07] toFin2 (by decide)
  exact checked law07 (by decide)

private theorem literalLaw08 : law08.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law08] :=
    FiniteCertificate.checkModels_sound table [law08] toFin3 (by decide)
  exact checked law08 (by decide)

theorem literalModels : Models table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact literalLaw00
  · exact literalLaw01
  · exact literalLaw02
  · exact literalLaw03
  · exact literalLaw04
  · exact literalLaw05
  · exact literalLaw06
  · exact literalLaw07
  · exact literalLaw08

theorem models : Models table.semigroup basis := literalModels

def coreMap (a : Fin 5) : Fin 6 := if a = 0 then 0 else if a = 1 then 1 else if a = 2 then 2 else if a = 3 then 3 else 5

def coreEmbedding : Embedding core610OppositeTable.semigroup table.semigroup where
  toFun := coreMap
  map_mul := by decide
  injective := by intro a b; exact by decide +revert

theorem validCoreNative (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy core610OppositeTable.semigroup := coreEmbedding.pullback_identity identity valid

def initialMap (a : Fin 2) : Fin 6 := if a = 0 then 0 else 4

def initialEmbedding : Embedding initialTable.semigroup table.semigroup where
  toFun := initialMap
  map_mul := by decide
  injective := by intro a b; exact by decide +revert

theorem validInitial (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy initialTable.semigroup := initialEmbedding.pullback_identity identity valid

theorem validCore (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy coreTable.semigroup :=
  core610OppositeValid_commonCore identity (validCoreNative identity valid)

end S6_11425


end SemigroupBasis.CoRoots.Order6Day11.FordLast8
