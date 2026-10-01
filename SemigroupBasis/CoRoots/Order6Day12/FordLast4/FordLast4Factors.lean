import SemigroupBasis.CoRoots.Order6Day12.FordLast4.FordLast4PrefixLift
import SemigroupBasis.Examples.LeftZeroTwo
import SemigroupBasis.TransferPower

/-! Four literal tables, four initial embeddings, two direct core embeddings and two separating-pair core embeddings. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day12.FordLast4

open SemigroupBasis

abbrev initialTable : FiniteTable := Examples.leftZeroTwo

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
    FiniteCertificate.checkModels_sound initialTable [law03] toFin3 (by decide)
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

theorem initialModels : Models initialTable.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact initialLaw00
  · exact initialLaw01
  · exact initialLaw02
  · exact initialLaw03
  · exact initialLaw04
  · exact initialLaw05
  · exact initialLaw06

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
    FiniteCertificate.checkModels_sound coreTable [law03] toFin3 (by decide)
  exact checked law03 (by decide)

private theorem coreLaw04 : law04.SatisfiedBy coreTable.semigroup := by
  have checked : Models coreTable.semigroup [law04] :=
    FiniteCertificate.checkModels_sound coreTable [law04] toFin2 (by decide)
  exact checked law04 (by decide)

private theorem coreLaw05 : law05.SatisfiedBy coreTable.semigroup := by
  have checked : Models coreTable.semigroup [law05] :=
    FiniteCertificate.checkModels_sound coreTable [law05] toFin3 (by decide)
  exact checked law05 (by decide)

private theorem coreLaw06 : law06.SatisfiedBy coreTable.semigroup := by
  have checked : Models coreTable.semigroup [law06] :=
    FiniteCertificate.checkModels_sound coreTable [law06] toFin3 (by decide)
  exact checked law06 (by decide)

theorem coreModels : Models coreTable.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact coreLaw00
  · exact coreLaw01
  · exact coreLaw02
  · exact coreLaw03
  · exact coreLaw04
  · exact coreLaw05
  · exact coreLaw06

namespace S6_12964

def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else if b = 3 then 0 else if b = 4 then 0 else 0) else
  if a = 1 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else if b = 3 then 0 else if b = 4 then 0 else 1) else
  if a = 2 then (if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 2 else if b = 3 then 0 else if b = 4 then 4 else 2) else
  if a = 3 then (if b = 0 then 3 else if b = 1 then 3 else if b = 2 then 3 else if b = 3 then 3 else if b = 4 then 3 else 3) else
  if a = 4 then (if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 2 else if b = 3 then 0 else if b = 4 then 4 else 2) else
  (if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 2 else if b = 3 then 0 else if b = 4 then 4 else 5)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def catalogueRows : List (List Nat) := [[1,1,1,1,1,1],[1,1,1,1,1,2],[1,2,3,1,5,3],[4,4,4,4,4,4],[1,2,3,1,5,3],[1,2,3,1,5,6]]

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
    FiniteCertificate.checkModels_sound table [law03] toFin3 (by decide)
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

theorem literalModels : Models table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact literalLaw00
  · exact literalLaw01
  · exact literalLaw02
  · exact literalLaw03
  · exact literalLaw04
  · exact literalLaw05
  · exact literalLaw06

theorem models : Models table.semigroup basis := literalModels

def initialMap (a : Fin 2) : Fin 6 := if a = 0 then 0 else 3

def initialEmbedding : Embedding initialTable.semigroup table.semigroup where
  toFun := initialMap
  map_mul := by decide
  injective := by intro a b; exact by decide +revert

theorem validInitial (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy initialTable.semigroup := initialEmbedding.pullback_identity identity valid

def coreMap (a : Fin 5) : Fin 6 := if a = 0 then 0 else if a = 1 then 1 else if a = 2 then 2 else if a = 3 then 4 else 5

def coreEmbedding : Embedding coreTable.semigroup table.semigroup where
  toFun := coreMap
  map_mul := by decide
  injective := by intro a b; exact by decide +revert

theorem validCore (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy coreTable.semigroup := coreEmbedding.pullback_identity identity valid

end S6_12964

namespace S6_13363

def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else if b = 3 then 0 else if b = 4 then 0 else 0) else
  if a = 1 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else if b = 3 then 0 else if b = 4 then 1 else 1) else
  if a = 2 then (if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 2 else if b = 3 then 0 else if b = 4 then 2 else 2) else
  if a = 3 then (if b = 0 then 3 else if b = 1 then 3 else if b = 2 then 3 else if b = 3 then 3 else if b = 4 then 3 else 3) else
  if a = 4 then (if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 2 else if b = 3 then 0 else if b = 4 then 4 else 5) else
  (if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 2 else if b = 3 then 0 else if b = 4 then 4 else 5)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def catalogueRows : List (List Nat) := [[1,1,1,1,1,1],[1,1,1,1,2,2],[1,2,3,1,3,3],[4,4,4,4,4,4],[1,2,3,1,5,6],[1,2,3,1,5,6]]

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
    FiniteCertificate.checkModels_sound table [law03] toFin3 (by decide)
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

theorem literalModels : Models table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact literalLaw00
  · exact literalLaw01
  · exact literalLaw02
  · exact literalLaw03
  · exact literalLaw04
  · exact literalLaw05
  · exact literalLaw06

theorem models : Models table.semigroup basis := literalModels

def initialMap (a : Fin 2) : Fin 6 := if a = 0 then 0 else 3

def initialEmbedding : Embedding initialTable.semigroup table.semigroup where
  toFun := initialMap
  map_mul := by decide
  injective := by intro a b; exact by decide +revert

theorem validInitial (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy initialTable.semigroup := initialEmbedding.pullback_identity identity valid

def coreMap0 (a : Fin 5) : Fin 6 := if a = 0 then 0 else if a = 1 then 0 else if a = 2 then 4 else if a = 3 then 5 else 4

def coreHom0 : Hom coreTable.semigroup table.semigroup where
  toFun := coreMap0
  map_mul := by decide

def coreMap1 (a : Fin 5) : Fin 6 := if a = 0 then 0 else if a = 1 then 1 else if a = 2 then 2 else if a = 3 then 2 else 4

def coreHom1 : Hom coreTable.semigroup table.semigroup where
  toFun := coreMap1
  map_mul := by decide

theorem corePair_injective : Function.Injective (fun a => (coreMap0 a, coreMap1 a)) := by
  intro a b
  exact by decide +revert

def coreEmbedding : Embedding coreTable.semigroup (table.semigroup.pi (Fin 2)) where
  toFun := fun a coordinate => if coordinate = 0 then coreMap0 a else coreMap1 a
  map_mul := by
    intro a b
    funext coordinate
    exact by decide +revert
  injective := by
    intro a b same
    have first := congrFun same (0 : Fin 2)
    have second := congrFun same (1 : Fin 2)
    clear same
    exact by decide +revert

theorem validCore (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy coreTable.semigroup :=
  coreEmbedding.pullback_identity identity (identity.satisfiedByPi table.semigroup (Fin 2) valid)

end S6_13363

namespace S6_13398

def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else if b = 3 then 0 else if b = 4 then 0 else 0) else
  if a = 1 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else if b = 3 then 0 else if b = 4 then 1 else 1) else
  if a = 2 then (if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 2 else if b = 3 then 2 else if b = 4 then 2 else 2) else
  if a = 3 then (if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 3 else if b = 3 then 3 else if b = 4 then 3 else 3) else
  if a = 4 then (if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 2 else if b = 3 then 2 else if b = 4 then 4 else 5) else
  (if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 2 else if b = 3 then 2 else if b = 4 then 4 else 5)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def catalogueRows : List (List Nat) := [[1,1,1,1,1,1],[1,1,1,1,2,2],[1,2,3,3,3,3],[1,2,4,4,4,4],[1,2,3,3,5,6],[1,2,3,3,5,6]]

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
    FiniteCertificate.checkModels_sound table [law03] toFin3 (by decide)
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

theorem literalModels : Models table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact literalLaw00
  · exact literalLaw01
  · exact literalLaw02
  · exact literalLaw03
  · exact literalLaw04
  · exact literalLaw05
  · exact literalLaw06

theorem models : Models table.semigroup basis := literalModels

def initialMap (a : Fin 2) : Fin 6 := if a = 0 then 2 else 3

def initialEmbedding : Embedding initialTable.semigroup table.semigroup where
  toFun := initialMap
  map_mul := by decide
  injective := by intro a b; exact by decide +revert

theorem validInitial (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy initialTable.semigroup := initialEmbedding.pullback_identity identity valid

def coreMap0 (a : Fin 5) : Fin 6 := if a = 0 then 0 else if a = 1 then 0 else if a = 2 then 4 else if a = 3 then 5 else 4

def coreHom0 : Hom coreTable.semigroup table.semigroup where
  toFun := coreMap0
  map_mul := by decide

def coreMap1 (a : Fin 5) : Fin 6 := if a = 0 then 0 else if a = 1 then 1 else if a = 2 then 2 else if a = 3 then 2 else 4

def coreHom1 : Hom coreTable.semigroup table.semigroup where
  toFun := coreMap1
  map_mul := by decide

theorem corePair_injective : Function.Injective (fun a => (coreMap0 a, coreMap1 a)) := by
  intro a b
  exact by decide +revert

def coreEmbedding : Embedding coreTable.semigroup (table.semigroup.pi (Fin 2)) where
  toFun := fun a coordinate => if coordinate = 0 then coreMap0 a else coreMap1 a
  map_mul := by
    intro a b
    funext coordinate
    exact by decide +revert
  injective := by
    intro a b same
    have first := congrFun same (0 : Fin 2)
    have second := congrFun same (1 : Fin 2)
    clear same
    exact by decide +revert

theorem validCore (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy coreTable.semigroup :=
  coreEmbedding.pullback_identity identity (identity.satisfiedByPi table.semigroup (Fin 2) valid)

end S6_13398

namespace S6_13425

def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else if b = 3 then 0 else if b = 4 then 0 else 0) else
  if a = 1 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else if b = 3 then 0 else if b = 4 then 1 else 1) else
  if a = 2 then (if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 2 else if b = 3 then 3 else if b = 4 then 2 else 2) else
  if a = 3 then (if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 2 else if b = 3 then 3 else if b = 4 then 2 else 2) else
  if a = 4 then (if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 2 else if b = 3 then 3 else if b = 4 then 4 else 4) else
  (if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 2 else if b = 3 then 3 else if b = 4 then 5 else 5)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def catalogueRows : List (List Nat) := [[1,1,1,1,1,1],[1,1,1,1,2,2],[1,2,3,4,3,3],[1,2,3,4,3,3],[1,2,3,4,5,5],[1,2,3,4,6,6]]

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
    FiniteCertificate.checkModels_sound table [law03] toFin3 (by decide)
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

theorem literalModels : Models table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact literalLaw00
  · exact literalLaw01
  · exact literalLaw02
  · exact literalLaw03
  · exact literalLaw04
  · exact literalLaw05
  · exact literalLaw06

theorem models : Models table.semigroup basis := literalModels

def initialMap (a : Fin 2) : Fin 6 := if a = 0 then 4 else 5

def initialEmbedding : Embedding initialTable.semigroup table.semigroup where
  toFun := initialMap
  map_mul := by decide
  injective := by intro a b; exact by decide +revert

theorem validInitial (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy initialTable.semigroup := initialEmbedding.pullback_identity identity valid

def coreMap (a : Fin 5) : Fin 6 := if a = 0 then 0 else if a = 1 then 1 else if a = 2 then 2 else if a = 3 then 3 else 4

def coreEmbedding : Embedding coreTable.semigroup table.semigroup where
  toFun := coreMap
  map_mul := by decide
  injective := by intro a b; exact by decide +revert

theorem validCore (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy coreTable.semigroup := coreEmbedding.pullback_identity identity valid

end S6_13425


end SemigroupBasis.CoRoots.Order6Day12.FordLast4
