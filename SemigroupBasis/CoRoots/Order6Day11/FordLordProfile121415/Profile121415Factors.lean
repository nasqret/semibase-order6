import SemigroupBasis.CoRoots.Order6Day11.FordLordProfile121415.Profile121415Presentation
import SemigroupBasis.Examples.CyclicTwo
import SemigroupBasis.CoRoots.S5_787Invariant
import SemigroupBasis.Subdirect

/-! Literal C/25 Models and exact finite factor maps for all seven classes.
Embeddings pull identities back; split surjections push them forward.
No simultaneous subdirect representation is asserted for the siblings. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day11.FordLordProfile121415

open SemigroupBasis

abbrev cyclicTable : FiniteTable := Examples.cyclicTwo
abbrev separatorTable : FiniteTable := Generated.Catalogue.S4_69.table
abbrev firstTable : FiniteTable := Generated.Catalogue.S2_4.table

private def toFinOne : Nat → Fin 1 := fun _ => 0
private def toFinTwo : Nat → Fin 2
  | 0 => 0
  | _ => 1
private def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

namespace S6_8856

def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 2 else if b = 3 then 0 else if b = 4 then 0 else 0) else
  if a = 1 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 2 else if b = 3 then 0 else if b = 4 then 0 else 1) else
  if a = 2 then (if b = 0 then 2 else if b = 1 then 2 else if b = 2 then 0 else if b = 3 then 2 else if b = 4 then 2 else 2) else
  if a = 3 then (if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 2 else if b = 3 then 3 else if b = 4 then 3 else 0) else
  if a = 4 then (if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 2 else if b = 3 then 4 else if b = 4 then 4 else 0) else
  (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 2 else if b = 3 then 0 else if b = 4 then 0 else 5)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def catalogueRows : List (List Nat) :=
  [[1,1,3,1,1,1],[1,1,3,1,1,2],[3,3,1,3,3,3],[1,2,3,4,4,1],[1,2,3,5,5,1],[1,1,3,1,1,6]]

theorem catalogueRows_exact :
    List.ofFn (fun a : Fin 6 => List.ofFn (fun b : Fin 6 => (mul a b).val + 1)) =
      catalogueRows := by decide

private theorem validLaw00 : law00.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law00] :=
    FiniteCertificate.checkModels_sound table [law00] toFinOne (by decide)
  exact checked law00 (by decide)

private theorem validLaw01 : law01.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law01] :=
    FiniteCertificate.checkModels_sound table [law01] toFinTwo (by decide)
  exact checked law01 (by decide)

private theorem validLaw02 : law02.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law02] :=
    FiniteCertificate.checkModels_sound table [law02] toFinTwo (by decide)
  exact checked law02 (by decide)

private theorem validLaw03 : law03.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law03] :=
    FiniteCertificate.checkModels_sound table [law03] toFinTwo (by decide)
  exact checked law03 (by decide)

private theorem validLaw04 : law04.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law04] :=
    FiniteCertificate.checkModels_sound table [law04] toFinTwo (by decide)
  exact checked law04 (by decide)

private theorem validLaw05 : law05.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law05] :=
    FiniteCertificate.checkModels_sound table [law05] toFinTwo (by decide)
  exact checked law05 (by decide)

private theorem validLaw06 : law06.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law06] :=
    FiniteCertificate.checkModels_sound table [law06] toFinTwo (by decide)
  exact checked law06 (by decide)

private theorem validLaw07 : law07.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law07] :=
    FiniteCertificate.checkModels_sound table [law07] toFinTwo (by decide)
  exact checked law07 (by decide)

private theorem validLaw08 : law08.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law08] :=
    FiniteCertificate.checkModels_sound table [law08] toFinThree (by decide)
  exact checked law08 (by decide)

private theorem validLaw09 : law09.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law09] :=
    FiniteCertificate.checkModels_sound table [law09] toFinTwo (by decide)
  exact checked law09 (by decide)

private theorem validLaw10 : law10.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law10] :=
    FiniteCertificate.checkModels_sound table [law10] toFinTwo (by decide)
  exact checked law10 (by decide)

private theorem validLaw11 : law11.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law11] :=
    FiniteCertificate.checkModels_sound table [law11] toFinThree (by decide)
  exact checked law11 (by decide)

private theorem validLaw12 : law12.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law12] :=
    FiniteCertificate.checkModels_sound table [law12] toFinThree (by decide)
  exact checked law12 (by decide)

private theorem validLaw13 : law13.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law13] :=
    FiniteCertificate.checkModels_sound table [law13] toFinThree (by decide)
  exact checked law13 (by decide)

private theorem validLaw14 : law14.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law14] :=
    FiniteCertificate.checkModels_sound table [law14] toFinThree (by decide)
  exact checked law14 (by decide)

private theorem validLaw15 : law15.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law15] :=
    FiniteCertificate.checkModels_sound table [law15] toFinThree (by decide)
  exact checked law15 (by decide)

private theorem validLaw16 : law16.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law16] :=
    FiniteCertificate.checkModels_sound table [law16] toFinThree (by decide)
  exact checked law16 (by decide)

private theorem validLaw17 : law17.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law17] :=
    FiniteCertificate.checkModels_sound table [law17] toFinThree (by decide)
  exact checked law17 (by decide)

private theorem validLaw18 : law18.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law18] :=
    FiniteCertificate.checkModels_sound table [law18] toFinThree (by decide)
  exact checked law18 (by decide)

private theorem validLaw19 : law19.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law19] :=
    FiniteCertificate.checkModels_sound table [law19] toFinThree (by decide)
  exact checked law19 (by decide)

private theorem validLaw20 : law20.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law20] :=
    FiniteCertificate.checkModels_sound table [law20] toFinFour (by decide)
  exact checked law20 (by decide)

private theorem validLaw21 : law21.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law21] :=
    FiniteCertificate.checkModels_sound table [law21] toFinTwo (by decide)
  exact checked law21 (by decide)

private theorem validLaw22 : law22.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law22] :=
    FiniteCertificate.checkModels_sound table [law22] toFinTwo (by decide)
  exact checked law22 (by decide)

private theorem validLaw23 : law23.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law23] :=
    FiniteCertificate.checkModels_sound table [law23] toFinFour (by decide)
  exact checked law23 (by decide)

private theorem validLaw24 : law24.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law24] :=
    FiniteCertificate.checkModels_sound table [law24] toFinFour (by decide)
  exact checked law24 (by decide)

theorem models : Models table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact validLaw00
  · exact validLaw01
  · exact validLaw02
  · exact validLaw03
  · exact validLaw04
  · exact validLaw05
  · exact validLaw06
  · exact validLaw07
  · exact validLaw08
  · exact validLaw09
  · exact validLaw10
  · exact validLaw11
  · exact validLaw12
  · exact validLaw13
  · exact validLaw14
  · exact validLaw15
  · exact validLaw16
  · exact validLaw17
  · exact validLaw18
  · exact validLaw19
  · exact validLaw20
  · exact validLaw21
  · exact validLaw22
  · exact validLaw23
  · exact validLaw24

def cyclicMap (a : Fin 2) : Fin 6 :=
  if a = 0 then 0 else 2

def cyclicEmbedding : Embedding cyclicTable.semigroup table.semigroup where
  toFun := cyclicMap
  map_mul := by decide
  injective := by intro a b; exact by decide +revert

theorem validCyclic (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy cyclicTable.semigroup :=
  cyclicEmbedding.pullback_identity identity valid

def separatorMap (a : Fin 4) : Fin 6 :=
  if a = 0 then 0 else if a = 1 then 1 else if a = 2 then 3 else 5

def separatorEmbedding : Embedding separatorTable.semigroup table.semigroup where
  toFun := separatorMap
  map_mul := by decide
  injective := by intro a b; exact by decide +revert

theorem validSeparator (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy separatorTable.semigroup :=
  separatorEmbedding.pullback_identity identity valid

def firstMap (a : Fin 2) : Fin 6 :=
  if a = 0 then 3 else 4

def firstEmbedding : Embedding firstTable.semigroup table.semigroup where
  toFun := firstMap
  map_mul := by decide
  injective := by intro a b; exact by decide +revert

theorem validFirst (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy firstTable.semigroup :=
  firstEmbedding.pullback_identity identity valid

end S6_8856

namespace S6_9004

def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 1 else if b = 3 then 0 else if b = 4 then 0 else 0) else
  if a = 1 then (if b = 0 then 1 else if b = 1 then 0 else if b = 2 then 0 else if b = 3 then 1 else if b = 4 then 1 else 1) else
  if a = 2 then (if b = 0 then 1 else if b = 1 then 0 else if b = 2 then 0 else if b = 3 then 1 else if b = 4 then 1 else 2) else
  if a = 3 then (if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 2 else if b = 3 then 3 else if b = 4 then 3 else 0) else
  if a = 4 then (if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 2 else if b = 3 then 4 else if b = 4 then 4 else 0) else
  (if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 1 else if b = 3 then 0 else if b = 4 then 0 else 5)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def catalogueRows : List (List Nat) :=
  [[1,2,2,1,1,1],[2,1,1,2,2,2],[2,1,1,2,2,3],[1,2,3,4,4,1],[1,2,3,5,5,1],[1,2,2,1,1,6]]

theorem catalogueRows_exact :
    List.ofFn (fun a : Fin 6 => List.ofFn (fun b : Fin 6 => (mul a b).val + 1)) =
      catalogueRows := by decide

private theorem validLaw00 : law00.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law00] :=
    FiniteCertificate.checkModels_sound table [law00] toFinOne (by decide)
  exact checked law00 (by decide)

private theorem validLaw01 : law01.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law01] :=
    FiniteCertificate.checkModels_sound table [law01] toFinTwo (by decide)
  exact checked law01 (by decide)

private theorem validLaw02 : law02.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law02] :=
    FiniteCertificate.checkModels_sound table [law02] toFinTwo (by decide)
  exact checked law02 (by decide)

private theorem validLaw03 : law03.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law03] :=
    FiniteCertificate.checkModels_sound table [law03] toFinTwo (by decide)
  exact checked law03 (by decide)

private theorem validLaw04 : law04.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law04] :=
    FiniteCertificate.checkModels_sound table [law04] toFinTwo (by decide)
  exact checked law04 (by decide)

private theorem validLaw05 : law05.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law05] :=
    FiniteCertificate.checkModels_sound table [law05] toFinTwo (by decide)
  exact checked law05 (by decide)

private theorem validLaw06 : law06.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law06] :=
    FiniteCertificate.checkModels_sound table [law06] toFinTwo (by decide)
  exact checked law06 (by decide)

private theorem validLaw07 : law07.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law07] :=
    FiniteCertificate.checkModels_sound table [law07] toFinTwo (by decide)
  exact checked law07 (by decide)

private theorem validLaw08 : law08.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law08] :=
    FiniteCertificate.checkModels_sound table [law08] toFinThree (by decide)
  exact checked law08 (by decide)

private theorem validLaw09 : law09.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law09] :=
    FiniteCertificate.checkModels_sound table [law09] toFinTwo (by decide)
  exact checked law09 (by decide)

private theorem validLaw10 : law10.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law10] :=
    FiniteCertificate.checkModels_sound table [law10] toFinTwo (by decide)
  exact checked law10 (by decide)

private theorem validLaw11 : law11.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law11] :=
    FiniteCertificate.checkModels_sound table [law11] toFinThree (by decide)
  exact checked law11 (by decide)

private theorem validLaw12 : law12.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law12] :=
    FiniteCertificate.checkModels_sound table [law12] toFinThree (by decide)
  exact checked law12 (by decide)

private theorem validLaw13 : law13.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law13] :=
    FiniteCertificate.checkModels_sound table [law13] toFinThree (by decide)
  exact checked law13 (by decide)

private theorem validLaw14 : law14.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law14] :=
    FiniteCertificate.checkModels_sound table [law14] toFinThree (by decide)
  exact checked law14 (by decide)

private theorem validLaw15 : law15.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law15] :=
    FiniteCertificate.checkModels_sound table [law15] toFinThree (by decide)
  exact checked law15 (by decide)

private theorem validLaw16 : law16.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law16] :=
    FiniteCertificate.checkModels_sound table [law16] toFinThree (by decide)
  exact checked law16 (by decide)

private theorem validLaw17 : law17.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law17] :=
    FiniteCertificate.checkModels_sound table [law17] toFinThree (by decide)
  exact checked law17 (by decide)

private theorem validLaw18 : law18.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law18] :=
    FiniteCertificate.checkModels_sound table [law18] toFinThree (by decide)
  exact checked law18 (by decide)

private theorem validLaw19 : law19.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law19] :=
    FiniteCertificate.checkModels_sound table [law19] toFinThree (by decide)
  exact checked law19 (by decide)

private theorem validLaw20 : law20.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law20] :=
    FiniteCertificate.checkModels_sound table [law20] toFinFour (by decide)
  exact checked law20 (by decide)

private theorem validLaw21 : law21.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law21] :=
    FiniteCertificate.checkModels_sound table [law21] toFinTwo (by decide)
  exact checked law21 (by decide)

private theorem validLaw22 : law22.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law22] :=
    FiniteCertificate.checkModels_sound table [law22] toFinTwo (by decide)
  exact checked law22 (by decide)

private theorem validLaw23 : law23.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law23] :=
    FiniteCertificate.checkModels_sound table [law23] toFinFour (by decide)
  exact checked law23 (by decide)

private theorem validLaw24 : law24.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law24] :=
    FiniteCertificate.checkModels_sound table [law24] toFinFour (by decide)
  exact checked law24 (by decide)

theorem models : Models table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact validLaw00
  · exact validLaw01
  · exact validLaw02
  · exact validLaw03
  · exact validLaw04
  · exact validLaw05
  · exact validLaw06
  · exact validLaw07
  · exact validLaw08
  · exact validLaw09
  · exact validLaw10
  · exact validLaw11
  · exact validLaw12
  · exact validLaw13
  · exact validLaw14
  · exact validLaw15
  · exact validLaw16
  · exact validLaw17
  · exact validLaw18
  · exact validLaw19
  · exact validLaw20
  · exact validLaw21
  · exact validLaw22
  · exact validLaw23
  · exact validLaw24

def cyclicMap (a : Fin 2) : Fin 6 :=
  if a = 0 then 0 else 1

def cyclicEmbedding : Embedding cyclicTable.semigroup table.semigroup where
  toFun := cyclicMap
  map_mul := by decide
  injective := by intro a b; exact by decide +revert

theorem validCyclic (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy cyclicTable.semigroup :=
  cyclicEmbedding.pullback_identity identity valid

def separatorMap (a : Fin 6) : Fin 4 :=
  if a = 0 then 0 else if a = 1 then 0 else if a = 2 then 1 else if a = 3 then 2 else if a = 4 then 2 else 3

def separatorSection (a : Fin 4) : Fin 6 :=
  if a = 0 then 0 else if a = 1 then 2 else if a = 2 then 3 else 5

def separatorSurjection : SplitSurjection table.semigroup separatorTable.semigroup where
  toFun := separatorMap
  map_mul := by decide
  preimage := separatorSection
  right_inverse := by intro a; exact by decide +revert

theorem validSeparator (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy separatorTable.semigroup :=
  separatorSurjection.pushforwardIdentity identity valid

def firstMap (a : Fin 2) : Fin 6 :=
  if a = 0 then 3 else 4

def firstEmbedding : Embedding firstTable.semigroup table.semigroup where
  toFun := firstMap
  map_mul := by decide
  injective := by intro a b; exact by decide +revert

theorem validFirst (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy firstTable.semigroup :=
  firstEmbedding.pullback_identity identity valid

end S6_9004

namespace S6_10949

def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else if b = 3 then 0 else if b = 4 then 0 else 0) else
  if a = 1 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else if b = 3 then 0 else if b = 4 then 0 else 1) else
  if a = 2 then (if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 2 else if b = 3 then 3 else if b = 4 then 0 else 0) else
  if a = 3 then (if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 3 else if b = 3 then 2 else if b = 4 then 0 else 0) else
  if a = 4 then (if b = 0 then 4 else if b = 1 then 4 else if b = 2 then 4 else if b = 3 then 4 else if b = 4 then 4 else 4) else
  (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else if b = 3 then 0 else if b = 4 then 0 else 5)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def catalogueRows : List (List Nat) :=
  [[1,1,1,1,1,1],[1,1,1,1,1,2],[1,2,3,4,1,1],[1,2,4,3,1,1],[5,5,5,5,5,5],[1,1,1,1,1,6]]

theorem catalogueRows_exact :
    List.ofFn (fun a : Fin 6 => List.ofFn (fun b : Fin 6 => (mul a b).val + 1)) =
      catalogueRows := by decide

private theorem validLaw00 : law00.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law00] :=
    FiniteCertificate.checkModels_sound table [law00] toFinOne (by decide)
  exact checked law00 (by decide)

private theorem validLaw01 : law01.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law01] :=
    FiniteCertificate.checkModels_sound table [law01] toFinTwo (by decide)
  exact checked law01 (by decide)

private theorem validLaw02 : law02.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law02] :=
    FiniteCertificate.checkModels_sound table [law02] toFinTwo (by decide)
  exact checked law02 (by decide)

private theorem validLaw03 : law03.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law03] :=
    FiniteCertificate.checkModels_sound table [law03] toFinTwo (by decide)
  exact checked law03 (by decide)

private theorem validLaw04 : law04.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law04] :=
    FiniteCertificate.checkModels_sound table [law04] toFinTwo (by decide)
  exact checked law04 (by decide)

private theorem validLaw05 : law05.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law05] :=
    FiniteCertificate.checkModels_sound table [law05] toFinTwo (by decide)
  exact checked law05 (by decide)

private theorem validLaw06 : law06.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law06] :=
    FiniteCertificate.checkModels_sound table [law06] toFinTwo (by decide)
  exact checked law06 (by decide)

private theorem validLaw07 : law07.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law07] :=
    FiniteCertificate.checkModels_sound table [law07] toFinTwo (by decide)
  exact checked law07 (by decide)

private theorem validLaw08 : law08.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law08] :=
    FiniteCertificate.checkModels_sound table [law08] toFinThree (by decide)
  exact checked law08 (by decide)

private theorem validLaw09 : law09.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law09] :=
    FiniteCertificate.checkModels_sound table [law09] toFinTwo (by decide)
  exact checked law09 (by decide)

private theorem validLaw10 : law10.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law10] :=
    FiniteCertificate.checkModels_sound table [law10] toFinTwo (by decide)
  exact checked law10 (by decide)

private theorem validLaw11 : law11.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law11] :=
    FiniteCertificate.checkModels_sound table [law11] toFinThree (by decide)
  exact checked law11 (by decide)

private theorem validLaw12 : law12.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law12] :=
    FiniteCertificate.checkModels_sound table [law12] toFinThree (by decide)
  exact checked law12 (by decide)

private theorem validLaw13 : law13.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law13] :=
    FiniteCertificate.checkModels_sound table [law13] toFinThree (by decide)
  exact checked law13 (by decide)

private theorem validLaw14 : law14.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law14] :=
    FiniteCertificate.checkModels_sound table [law14] toFinThree (by decide)
  exact checked law14 (by decide)

private theorem validLaw15 : law15.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law15] :=
    FiniteCertificate.checkModels_sound table [law15] toFinThree (by decide)
  exact checked law15 (by decide)

private theorem validLaw16 : law16.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law16] :=
    FiniteCertificate.checkModels_sound table [law16] toFinThree (by decide)
  exact checked law16 (by decide)

private theorem validLaw17 : law17.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law17] :=
    FiniteCertificate.checkModels_sound table [law17] toFinThree (by decide)
  exact checked law17 (by decide)

private theorem validLaw18 : law18.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law18] :=
    FiniteCertificate.checkModels_sound table [law18] toFinThree (by decide)
  exact checked law18 (by decide)

private theorem validLaw19 : law19.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law19] :=
    FiniteCertificate.checkModels_sound table [law19] toFinThree (by decide)
  exact checked law19 (by decide)

private theorem validLaw20 : law20.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law20] :=
    FiniteCertificate.checkModels_sound table [law20] toFinFour (by decide)
  exact checked law20 (by decide)

private theorem validLaw21 : law21.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law21] :=
    FiniteCertificate.checkModels_sound table [law21] toFinTwo (by decide)
  exact checked law21 (by decide)

private theorem validLaw22 : law22.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law22] :=
    FiniteCertificate.checkModels_sound table [law22] toFinTwo (by decide)
  exact checked law22 (by decide)

private theorem validLaw23 : law23.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law23] :=
    FiniteCertificate.checkModels_sound table [law23] toFinFour (by decide)
  exact checked law23 (by decide)

private theorem validLaw24 : law24.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law24] :=
    FiniteCertificate.checkModels_sound table [law24] toFinFour (by decide)
  exact checked law24 (by decide)

theorem models : Models table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact validLaw00
  · exact validLaw01
  · exact validLaw02
  · exact validLaw03
  · exact validLaw04
  · exact validLaw05
  · exact validLaw06
  · exact validLaw07
  · exact validLaw08
  · exact validLaw09
  · exact validLaw10
  · exact validLaw11
  · exact validLaw12
  · exact validLaw13
  · exact validLaw14
  · exact validLaw15
  · exact validLaw16
  · exact validLaw17
  · exact validLaw18
  · exact validLaw19
  · exact validLaw20
  · exact validLaw21
  · exact validLaw22
  · exact validLaw23
  · exact validLaw24

def cyclicMap (a : Fin 2) : Fin 6 :=
  if a = 0 then 2 else 3

def cyclicEmbedding : Embedding cyclicTable.semigroup table.semigroup where
  toFun := cyclicMap
  map_mul := by decide
  injective := by intro a b; exact by decide +revert

theorem validCyclic (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy cyclicTable.semigroup :=
  cyclicEmbedding.pullback_identity identity valid

def separatorMap (a : Fin 4) : Fin 6 :=
  if a = 0 then 0 else if a = 1 then 1 else if a = 2 then 2 else 5

def separatorEmbedding : Embedding separatorTable.semigroup table.semigroup where
  toFun := separatorMap
  map_mul := by decide
  injective := by intro a b; exact by decide +revert

theorem validSeparator (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy separatorTable.semigroup :=
  separatorEmbedding.pullback_identity identity valid

def firstMap (a : Fin 2) : Fin 6 :=
  if a = 0 then 0 else 4

def firstEmbedding : Embedding firstTable.semigroup table.semigroup where
  toFun := firstMap
  map_mul := by decide
  injective := by intro a b; exact by decide +revert

theorem validFirst (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy firstTable.semigroup :=
  firstEmbedding.pullback_identity identity valid

end S6_10949

namespace S6_10951

def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else if b = 3 then 0 else if b = 4 then 0 else 0) else
  if a = 1 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else if b = 3 then 0 else if b = 4 then 0 else 1) else
  if a = 2 then (if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 2 else if b = 3 then 3 else if b = 4 then 0 else 0) else
  if a = 3 then (if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 3 else if b = 3 then 2 else if b = 4 then 0 else 0) else
  if a = 4 then (if b = 0 then 4 else if b = 1 then 4 else if b = 2 then 4 else if b = 3 then 4 else if b = 4 then 4 else 4) else
  (if b = 0 then 4 else if b = 1 then 4 else if b = 2 then 4 else if b = 3 then 4 else if b = 4 then 4 else 5)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def catalogueRows : List (List Nat) :=
  [[1,1,1,1,1,1],[1,1,1,1,1,2],[1,2,3,4,1,1],[1,2,4,3,1,1],[5,5,5,5,5,5],[5,5,5,5,5,6]]

theorem catalogueRows_exact :
    List.ofFn (fun a : Fin 6 => List.ofFn (fun b : Fin 6 => (mul a b).val + 1)) =
      catalogueRows := by decide

private theorem validLaw00 : law00.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law00] :=
    FiniteCertificate.checkModels_sound table [law00] toFinOne (by decide)
  exact checked law00 (by decide)

private theorem validLaw01 : law01.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law01] :=
    FiniteCertificate.checkModels_sound table [law01] toFinTwo (by decide)
  exact checked law01 (by decide)

private theorem validLaw02 : law02.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law02] :=
    FiniteCertificate.checkModels_sound table [law02] toFinTwo (by decide)
  exact checked law02 (by decide)

private theorem validLaw03 : law03.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law03] :=
    FiniteCertificate.checkModels_sound table [law03] toFinTwo (by decide)
  exact checked law03 (by decide)

private theorem validLaw04 : law04.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law04] :=
    FiniteCertificate.checkModels_sound table [law04] toFinTwo (by decide)
  exact checked law04 (by decide)

private theorem validLaw05 : law05.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law05] :=
    FiniteCertificate.checkModels_sound table [law05] toFinTwo (by decide)
  exact checked law05 (by decide)

private theorem validLaw06 : law06.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law06] :=
    FiniteCertificate.checkModels_sound table [law06] toFinTwo (by decide)
  exact checked law06 (by decide)

private theorem validLaw07 : law07.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law07] :=
    FiniteCertificate.checkModels_sound table [law07] toFinTwo (by decide)
  exact checked law07 (by decide)

private theorem validLaw08 : law08.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law08] :=
    FiniteCertificate.checkModels_sound table [law08] toFinThree (by decide)
  exact checked law08 (by decide)

private theorem validLaw09 : law09.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law09] :=
    FiniteCertificate.checkModels_sound table [law09] toFinTwo (by decide)
  exact checked law09 (by decide)

private theorem validLaw10 : law10.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law10] :=
    FiniteCertificate.checkModels_sound table [law10] toFinTwo (by decide)
  exact checked law10 (by decide)

private theorem validLaw11 : law11.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law11] :=
    FiniteCertificate.checkModels_sound table [law11] toFinThree (by decide)
  exact checked law11 (by decide)

private theorem validLaw12 : law12.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law12] :=
    FiniteCertificate.checkModels_sound table [law12] toFinThree (by decide)
  exact checked law12 (by decide)

private theorem validLaw13 : law13.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law13] :=
    FiniteCertificate.checkModels_sound table [law13] toFinThree (by decide)
  exact checked law13 (by decide)

private theorem validLaw14 : law14.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law14] :=
    FiniteCertificate.checkModels_sound table [law14] toFinThree (by decide)
  exact checked law14 (by decide)

private theorem validLaw15 : law15.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law15] :=
    FiniteCertificate.checkModels_sound table [law15] toFinThree (by decide)
  exact checked law15 (by decide)

private theorem validLaw16 : law16.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law16] :=
    FiniteCertificate.checkModels_sound table [law16] toFinThree (by decide)
  exact checked law16 (by decide)

private theorem validLaw17 : law17.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law17] :=
    FiniteCertificate.checkModels_sound table [law17] toFinThree (by decide)
  exact checked law17 (by decide)

private theorem validLaw18 : law18.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law18] :=
    FiniteCertificate.checkModels_sound table [law18] toFinThree (by decide)
  exact checked law18 (by decide)

private theorem validLaw19 : law19.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law19] :=
    FiniteCertificate.checkModels_sound table [law19] toFinThree (by decide)
  exact checked law19 (by decide)

private theorem validLaw20 : law20.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law20] :=
    FiniteCertificate.checkModels_sound table [law20] toFinFour (by decide)
  exact checked law20 (by decide)

private theorem validLaw21 : law21.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law21] :=
    FiniteCertificate.checkModels_sound table [law21] toFinTwo (by decide)
  exact checked law21 (by decide)

private theorem validLaw22 : law22.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law22] :=
    FiniteCertificate.checkModels_sound table [law22] toFinTwo (by decide)
  exact checked law22 (by decide)

private theorem validLaw23 : law23.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law23] :=
    FiniteCertificate.checkModels_sound table [law23] toFinFour (by decide)
  exact checked law23 (by decide)

private theorem validLaw24 : law24.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law24] :=
    FiniteCertificate.checkModels_sound table [law24] toFinFour (by decide)
  exact checked law24 (by decide)

theorem models : Models table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact validLaw00
  · exact validLaw01
  · exact validLaw02
  · exact validLaw03
  · exact validLaw04
  · exact validLaw05
  · exact validLaw06
  · exact validLaw07
  · exact validLaw08
  · exact validLaw09
  · exact validLaw10
  · exact validLaw11
  · exact validLaw12
  · exact validLaw13
  · exact validLaw14
  · exact validLaw15
  · exact validLaw16
  · exact validLaw17
  · exact validLaw18
  · exact validLaw19
  · exact validLaw20
  · exact validLaw21
  · exact validLaw22
  · exact validLaw23
  · exact validLaw24

def cyclicMap (a : Fin 2) : Fin 6 :=
  if a = 0 then 2 else 3

def cyclicEmbedding : Embedding cyclicTable.semigroup table.semigroup where
  toFun := cyclicMap
  map_mul := by decide
  injective := by intro a b; exact by decide +revert

theorem validCyclic (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy cyclicTable.semigroup :=
  cyclicEmbedding.pullback_identity identity valid

def separatorMap (a : Fin 6) : Fin 4 :=
  if a = 0 then 0 else if a = 1 then 1 else if a = 2 then 2 else if a = 3 then 2 else if a = 4 then 0 else 3

def separatorSection (a : Fin 4) : Fin 6 :=
  if a = 0 then 0 else if a = 1 then 1 else if a = 2 then 2 else 5

def separatorSurjection : SplitSurjection table.semigroup separatorTable.semigroup where
  toFun := separatorMap
  map_mul := by decide
  preimage := separatorSection
  right_inverse := by intro a; exact by decide +revert

theorem validSeparator (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy separatorTable.semigroup :=
  separatorSurjection.pushforwardIdentity identity valid

def firstMap (a : Fin 2) : Fin 6 :=
  if a = 0 then 0 else 4

def firstEmbedding : Embedding firstTable.semigroup table.semigroup where
  toFun := firstMap
  map_mul := by decide
  injective := by intro a b; exact by decide +revert

theorem validFirst (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy firstTable.semigroup :=
  firstEmbedding.pullback_identity identity valid

end S6_10951

namespace S6_11227

def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else if b = 3 then 0 else if b = 4 then 0 else 0) else
  if a = 1 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else if b = 3 then 0 else if b = 4 then 1 else 1) else
  if a = 2 then (if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 2 else if b = 3 then 3 else if b = 4 then 0 else 0) else
  if a = 3 then (if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 3 else if b = 3 then 2 else if b = 4 then 0 else 0) else
  if a = 4 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else if b = 3 then 0 else if b = 4 then 4 else 4) else
  (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else if b = 3 then 0 else if b = 4 then 5 else 5)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def catalogueRows : List (List Nat) :=
  [[1,1,1,1,1,1],[1,1,1,1,2,2],[1,2,3,4,1,1],[1,2,4,3,1,1],[1,1,1,1,5,5],[1,1,1,1,6,6]]

theorem catalogueRows_exact :
    List.ofFn (fun a : Fin 6 => List.ofFn (fun b : Fin 6 => (mul a b).val + 1)) =
      catalogueRows := by decide

private theorem validLaw00 : law00.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law00] :=
    FiniteCertificate.checkModels_sound table [law00] toFinOne (by decide)
  exact checked law00 (by decide)

private theorem validLaw01 : law01.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law01] :=
    FiniteCertificate.checkModels_sound table [law01] toFinTwo (by decide)
  exact checked law01 (by decide)

private theorem validLaw02 : law02.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law02] :=
    FiniteCertificate.checkModels_sound table [law02] toFinTwo (by decide)
  exact checked law02 (by decide)

private theorem validLaw03 : law03.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law03] :=
    FiniteCertificate.checkModels_sound table [law03] toFinTwo (by decide)
  exact checked law03 (by decide)

private theorem validLaw04 : law04.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law04] :=
    FiniteCertificate.checkModels_sound table [law04] toFinTwo (by decide)
  exact checked law04 (by decide)

private theorem validLaw05 : law05.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law05] :=
    FiniteCertificate.checkModels_sound table [law05] toFinTwo (by decide)
  exact checked law05 (by decide)

private theorem validLaw06 : law06.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law06] :=
    FiniteCertificate.checkModels_sound table [law06] toFinTwo (by decide)
  exact checked law06 (by decide)

private theorem validLaw07 : law07.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law07] :=
    FiniteCertificate.checkModels_sound table [law07] toFinTwo (by decide)
  exact checked law07 (by decide)

private theorem validLaw08 : law08.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law08] :=
    FiniteCertificate.checkModels_sound table [law08] toFinThree (by decide)
  exact checked law08 (by decide)

private theorem validLaw09 : law09.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law09] :=
    FiniteCertificate.checkModels_sound table [law09] toFinTwo (by decide)
  exact checked law09 (by decide)

private theorem validLaw10 : law10.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law10] :=
    FiniteCertificate.checkModels_sound table [law10] toFinTwo (by decide)
  exact checked law10 (by decide)

private theorem validLaw11 : law11.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law11] :=
    FiniteCertificate.checkModels_sound table [law11] toFinThree (by decide)
  exact checked law11 (by decide)

private theorem validLaw12 : law12.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law12] :=
    FiniteCertificate.checkModels_sound table [law12] toFinThree (by decide)
  exact checked law12 (by decide)

private theorem validLaw13 : law13.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law13] :=
    FiniteCertificate.checkModels_sound table [law13] toFinThree (by decide)
  exact checked law13 (by decide)

private theorem validLaw14 : law14.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law14] :=
    FiniteCertificate.checkModels_sound table [law14] toFinThree (by decide)
  exact checked law14 (by decide)

private theorem validLaw15 : law15.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law15] :=
    FiniteCertificate.checkModels_sound table [law15] toFinThree (by decide)
  exact checked law15 (by decide)

private theorem validLaw16 : law16.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law16] :=
    FiniteCertificate.checkModels_sound table [law16] toFinThree (by decide)
  exact checked law16 (by decide)

private theorem validLaw17 : law17.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law17] :=
    FiniteCertificate.checkModels_sound table [law17] toFinThree (by decide)
  exact checked law17 (by decide)

private theorem validLaw18 : law18.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law18] :=
    FiniteCertificate.checkModels_sound table [law18] toFinThree (by decide)
  exact checked law18 (by decide)

private theorem validLaw19 : law19.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law19] :=
    FiniteCertificate.checkModels_sound table [law19] toFinThree (by decide)
  exact checked law19 (by decide)

private theorem validLaw20 : law20.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law20] :=
    FiniteCertificate.checkModels_sound table [law20] toFinFour (by decide)
  exact checked law20 (by decide)

private theorem validLaw21 : law21.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law21] :=
    FiniteCertificate.checkModels_sound table [law21] toFinTwo (by decide)
  exact checked law21 (by decide)

private theorem validLaw22 : law22.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law22] :=
    FiniteCertificate.checkModels_sound table [law22] toFinTwo (by decide)
  exact checked law22 (by decide)

private theorem validLaw23 : law23.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law23] :=
    FiniteCertificate.checkModels_sound table [law23] toFinFour (by decide)
  exact checked law23 (by decide)

private theorem validLaw24 : law24.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law24] :=
    FiniteCertificate.checkModels_sound table [law24] toFinFour (by decide)
  exact checked law24 (by decide)

theorem models : Models table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact validLaw00
  · exact validLaw01
  · exact validLaw02
  · exact validLaw03
  · exact validLaw04
  · exact validLaw05
  · exact validLaw06
  · exact validLaw07
  · exact validLaw08
  · exact validLaw09
  · exact validLaw10
  · exact validLaw11
  · exact validLaw12
  · exact validLaw13
  · exact validLaw14
  · exact validLaw15
  · exact validLaw16
  · exact validLaw17
  · exact validLaw18
  · exact validLaw19
  · exact validLaw20
  · exact validLaw21
  · exact validLaw22
  · exact validLaw23
  · exact validLaw24

def cyclicMap (a : Fin 2) : Fin 6 :=
  if a = 0 then 2 else 3

def cyclicEmbedding : Embedding cyclicTable.semigroup table.semigroup where
  toFun := cyclicMap
  map_mul := by decide
  injective := by intro a b; exact by decide +revert

theorem validCyclic (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy cyclicTable.semigroup :=
  cyclicEmbedding.pullback_identity identity valid

def separatorMap (a : Fin 4) : Fin 6 :=
  if a = 0 then 0 else if a = 1 then 1 else if a = 2 then 2 else 4

def separatorEmbedding : Embedding separatorTable.semigroup table.semigroup where
  toFun := separatorMap
  map_mul := by decide
  injective := by intro a b; exact by decide +revert

theorem validSeparator (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy separatorTable.semigroup :=
  separatorEmbedding.pullback_identity identity valid

def firstMap (a : Fin 2) : Fin 6 :=
  if a = 0 then 4 else 5

def firstEmbedding : Embedding firstTable.semigroup table.semigroup where
  toFun := firstMap
  map_mul := by decide
  injective := by intro a b; exact by decide +revert

theorem validFirst (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy firstTable.semigroup :=
  firstEmbedding.pullback_identity identity valid

end S6_11227

namespace S6_11299

def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else if b = 3 then 0 else if b = 4 then 0 else 0) else
  if a = 1 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 1 else if b = 3 then 1 else if b = 4 then 0 else 0) else
  if a = 2 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 2 else if b = 3 then 3 else if b = 4 then 0 else 0) else
  if a = 3 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 3 else if b = 3 then 2 else if b = 4 then 0 else 0) else
  if a = 4 then (if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 0 else if b = 3 then 0 else if b = 4 then 4 else 0) else
  (if b = 0 then 5 else if b = 1 then 5 else if b = 2 then 5 else if b = 3 then 5 else if b = 4 then 5 else 5)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def catalogueRows : List (List Nat) :=
  [[1,1,1,1,1,1],[1,1,2,2,1,1],[1,1,3,4,1,1],[1,1,4,3,1,1],[1,2,1,1,5,1],[6,6,6,6,6,6]]

theorem catalogueRows_exact :
    List.ofFn (fun a : Fin 6 => List.ofFn (fun b : Fin 6 => (mul a b).val + 1)) =
      catalogueRows := by decide

private theorem validLaw00 : law00.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law00] :=
    FiniteCertificate.checkModels_sound table [law00] toFinOne (by decide)
  exact checked law00 (by decide)

private theorem validLaw01 : law01.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law01] :=
    FiniteCertificate.checkModels_sound table [law01] toFinTwo (by decide)
  exact checked law01 (by decide)

private theorem validLaw02 : law02.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law02] :=
    FiniteCertificate.checkModels_sound table [law02] toFinTwo (by decide)
  exact checked law02 (by decide)

private theorem validLaw03 : law03.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law03] :=
    FiniteCertificate.checkModels_sound table [law03] toFinTwo (by decide)
  exact checked law03 (by decide)

private theorem validLaw04 : law04.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law04] :=
    FiniteCertificate.checkModels_sound table [law04] toFinTwo (by decide)
  exact checked law04 (by decide)

private theorem validLaw05 : law05.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law05] :=
    FiniteCertificate.checkModels_sound table [law05] toFinTwo (by decide)
  exact checked law05 (by decide)

private theorem validLaw06 : law06.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law06] :=
    FiniteCertificate.checkModels_sound table [law06] toFinTwo (by decide)
  exact checked law06 (by decide)

private theorem validLaw07 : law07.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law07] :=
    FiniteCertificate.checkModels_sound table [law07] toFinTwo (by decide)
  exact checked law07 (by decide)

private theorem validLaw08 : law08.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law08] :=
    FiniteCertificate.checkModels_sound table [law08] toFinThree (by decide)
  exact checked law08 (by decide)

private theorem validLaw09 : law09.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law09] :=
    FiniteCertificate.checkModels_sound table [law09] toFinTwo (by decide)
  exact checked law09 (by decide)

private theorem validLaw10 : law10.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law10] :=
    FiniteCertificate.checkModels_sound table [law10] toFinTwo (by decide)
  exact checked law10 (by decide)

private theorem validLaw11 : law11.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law11] :=
    FiniteCertificate.checkModels_sound table [law11] toFinThree (by decide)
  exact checked law11 (by decide)

private theorem validLaw12 : law12.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law12] :=
    FiniteCertificate.checkModels_sound table [law12] toFinThree (by decide)
  exact checked law12 (by decide)

private theorem validLaw13 : law13.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law13] :=
    FiniteCertificate.checkModels_sound table [law13] toFinThree (by decide)
  exact checked law13 (by decide)

private theorem validLaw14 : law14.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law14] :=
    FiniteCertificate.checkModels_sound table [law14] toFinThree (by decide)
  exact checked law14 (by decide)

private theorem validLaw15 : law15.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law15] :=
    FiniteCertificate.checkModels_sound table [law15] toFinThree (by decide)
  exact checked law15 (by decide)

private theorem validLaw16 : law16.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law16] :=
    FiniteCertificate.checkModels_sound table [law16] toFinThree (by decide)
  exact checked law16 (by decide)

private theorem validLaw17 : law17.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law17] :=
    FiniteCertificate.checkModels_sound table [law17] toFinThree (by decide)
  exact checked law17 (by decide)

private theorem validLaw18 : law18.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law18] :=
    FiniteCertificate.checkModels_sound table [law18] toFinThree (by decide)
  exact checked law18 (by decide)

private theorem validLaw19 : law19.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law19] :=
    FiniteCertificate.checkModels_sound table [law19] toFinThree (by decide)
  exact checked law19 (by decide)

private theorem validLaw20 : law20.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law20] :=
    FiniteCertificate.checkModels_sound table [law20] toFinFour (by decide)
  exact checked law20 (by decide)

private theorem validLaw21 : law21.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law21] :=
    FiniteCertificate.checkModels_sound table [law21] toFinTwo (by decide)
  exact checked law21 (by decide)

private theorem validLaw22 : law22.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law22] :=
    FiniteCertificate.checkModels_sound table [law22] toFinTwo (by decide)
  exact checked law22 (by decide)

private theorem validLaw23 : law23.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law23] :=
    FiniteCertificate.checkModels_sound table [law23] toFinFour (by decide)
  exact checked law23 (by decide)

private theorem validLaw24 : law24.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law24] :=
    FiniteCertificate.checkModels_sound table [law24] toFinFour (by decide)
  exact checked law24 (by decide)

theorem models : Models table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact validLaw00
  · exact validLaw01
  · exact validLaw02
  · exact validLaw03
  · exact validLaw04
  · exact validLaw05
  · exact validLaw06
  · exact validLaw07
  · exact validLaw08
  · exact validLaw09
  · exact validLaw10
  · exact validLaw11
  · exact validLaw12
  · exact validLaw13
  · exact validLaw14
  · exact validLaw15
  · exact validLaw16
  · exact validLaw17
  · exact validLaw18
  · exact validLaw19
  · exact validLaw20
  · exact validLaw21
  · exact validLaw22
  · exact validLaw23
  · exact validLaw24

def cyclicMap (a : Fin 2) : Fin 6 :=
  if a = 0 then 2 else 3

def cyclicEmbedding : Embedding cyclicTable.semigroup table.semigroup where
  toFun := cyclicMap
  map_mul := by decide
  injective := by intro a b; exact by decide +revert

theorem validCyclic (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy cyclicTable.semigroup :=
  cyclicEmbedding.pullback_identity identity valid

def separatorMap (a : Fin 4) : Fin 6 :=
  if a = 0 then 0 else if a = 1 then 1 else if a = 2 then 4 else 2

def separatorEmbedding : Embedding separatorTable.semigroup table.semigroup where
  toFun := separatorMap
  map_mul := by decide
  injective := by intro a b; exact by decide +revert

theorem validSeparator (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy separatorTable.semigroup :=
  separatorEmbedding.pullback_identity identity valid

def firstMap (a : Fin 2) : Fin 6 :=
  if a = 0 then 0 else 5

def firstEmbedding : Embedding firstTable.semigroup table.semigroup where
  toFun := firstMap
  map_mul := by decide
  injective := by intro a b; exact by decide +revert

theorem validFirst (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy firstTable.semigroup :=
  firstEmbedding.pullback_identity identity valid

end S6_11299

namespace S6_11410

def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else if b = 3 then 0 else if b = 4 then 0 else 0) else
  if a = 1 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 1 else if b = 3 then 1 else if b = 4 then 0 else 0) else
  if a = 2 then (if b = 0 then 4 else if b = 1 then 4 else if b = 2 then 2 else if b = 3 then 3 else if b = 4 then 4 else 4) else
  if a = 3 then (if b = 0 then 4 else if b = 1 then 4 else if b = 2 then 3 else if b = 3 then 2 else if b = 4 then 4 else 4) else
  if a = 4 then (if b = 0 then 4 else if b = 1 then 4 else if b = 2 then 4 else if b = 3 then 4 else if b = 4 then 4 else 4) else
  (if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 0 else if b = 3 then 0 else if b = 4 then 0 else 5)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def catalogueRows : List (List Nat) :=
  [[1,1,1,1,1,1],[1,1,2,2,1,1],[5,5,3,4,5,5],[5,5,4,3,5,5],[5,5,5,5,5,5],[1,2,1,1,1,6]]

theorem catalogueRows_exact :
    List.ofFn (fun a : Fin 6 => List.ofFn (fun b : Fin 6 => (mul a b).val + 1)) =
      catalogueRows := by decide

private theorem validLaw00 : law00.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law00] :=
    FiniteCertificate.checkModels_sound table [law00] toFinOne (by decide)
  exact checked law00 (by decide)

private theorem validLaw01 : law01.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law01] :=
    FiniteCertificate.checkModels_sound table [law01] toFinTwo (by decide)
  exact checked law01 (by decide)

private theorem validLaw02 : law02.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law02] :=
    FiniteCertificate.checkModels_sound table [law02] toFinTwo (by decide)
  exact checked law02 (by decide)

private theorem validLaw03 : law03.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law03] :=
    FiniteCertificate.checkModels_sound table [law03] toFinTwo (by decide)
  exact checked law03 (by decide)

private theorem validLaw04 : law04.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law04] :=
    FiniteCertificate.checkModels_sound table [law04] toFinTwo (by decide)
  exact checked law04 (by decide)

private theorem validLaw05 : law05.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law05] :=
    FiniteCertificate.checkModels_sound table [law05] toFinTwo (by decide)
  exact checked law05 (by decide)

private theorem validLaw06 : law06.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law06] :=
    FiniteCertificate.checkModels_sound table [law06] toFinTwo (by decide)
  exact checked law06 (by decide)

private theorem validLaw07 : law07.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law07] :=
    FiniteCertificate.checkModels_sound table [law07] toFinTwo (by decide)
  exact checked law07 (by decide)

private theorem validLaw08 : law08.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law08] :=
    FiniteCertificate.checkModels_sound table [law08] toFinThree (by decide)
  exact checked law08 (by decide)

private theorem validLaw09 : law09.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law09] :=
    FiniteCertificate.checkModels_sound table [law09] toFinTwo (by decide)
  exact checked law09 (by decide)

private theorem validLaw10 : law10.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law10] :=
    FiniteCertificate.checkModels_sound table [law10] toFinTwo (by decide)
  exact checked law10 (by decide)

private theorem validLaw11 : law11.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law11] :=
    FiniteCertificate.checkModels_sound table [law11] toFinThree (by decide)
  exact checked law11 (by decide)

private theorem validLaw12 : law12.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law12] :=
    FiniteCertificate.checkModels_sound table [law12] toFinThree (by decide)
  exact checked law12 (by decide)

private theorem validLaw13 : law13.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law13] :=
    FiniteCertificate.checkModels_sound table [law13] toFinThree (by decide)
  exact checked law13 (by decide)

private theorem validLaw14 : law14.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law14] :=
    FiniteCertificate.checkModels_sound table [law14] toFinThree (by decide)
  exact checked law14 (by decide)

private theorem validLaw15 : law15.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law15] :=
    FiniteCertificate.checkModels_sound table [law15] toFinThree (by decide)
  exact checked law15 (by decide)

private theorem validLaw16 : law16.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law16] :=
    FiniteCertificate.checkModels_sound table [law16] toFinThree (by decide)
  exact checked law16 (by decide)

private theorem validLaw17 : law17.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law17] :=
    FiniteCertificate.checkModels_sound table [law17] toFinThree (by decide)
  exact checked law17 (by decide)

private theorem validLaw18 : law18.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law18] :=
    FiniteCertificate.checkModels_sound table [law18] toFinThree (by decide)
  exact checked law18 (by decide)

private theorem validLaw19 : law19.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law19] :=
    FiniteCertificate.checkModels_sound table [law19] toFinThree (by decide)
  exact checked law19 (by decide)

private theorem validLaw20 : law20.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law20] :=
    FiniteCertificate.checkModels_sound table [law20] toFinFour (by decide)
  exact checked law20 (by decide)

private theorem validLaw21 : law21.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law21] :=
    FiniteCertificate.checkModels_sound table [law21] toFinTwo (by decide)
  exact checked law21 (by decide)

private theorem validLaw22 : law22.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law22] :=
    FiniteCertificate.checkModels_sound table [law22] toFinTwo (by decide)
  exact checked law22 (by decide)

private theorem validLaw23 : law23.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law23] :=
    FiniteCertificate.checkModels_sound table [law23] toFinFour (by decide)
  exact checked law23 (by decide)

private theorem validLaw24 : law24.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law24] :=
    FiniteCertificate.checkModels_sound table [law24] toFinFour (by decide)
  exact checked law24 (by decide)

theorem models : Models table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact validLaw00
  · exact validLaw01
  · exact validLaw02
  · exact validLaw03
  · exact validLaw04
  · exact validLaw05
  · exact validLaw06
  · exact validLaw07
  · exact validLaw08
  · exact validLaw09
  · exact validLaw10
  · exact validLaw11
  · exact validLaw12
  · exact validLaw13
  · exact validLaw14
  · exact validLaw15
  · exact validLaw16
  · exact validLaw17
  · exact validLaw18
  · exact validLaw19
  · exact validLaw20
  · exact validLaw21
  · exact validLaw22
  · exact validLaw23
  · exact validLaw24

def cyclicMap (a : Fin 2) : Fin 6 :=
  if a = 0 then 2 else 3

def cyclicEmbedding : Embedding cyclicTable.semigroup table.semigroup where
  toFun := cyclicMap
  map_mul := by decide
  injective := by intro a b; exact by decide +revert

theorem validCyclic (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy cyclicTable.semigroup :=
  cyclicEmbedding.pullback_identity identity valid

def separatorMap (a : Fin 6) : Fin 4 :=
  if a = 0 then 0 else if a = 1 then 1 else if a = 2 then 3 else if a = 3 then 3 else if a = 4 then 0 else 2

def separatorSection (a : Fin 4) : Fin 6 :=
  if a = 0 then 0 else if a = 1 then 1 else if a = 2 then 5 else 2

def separatorSurjection : SplitSurjection table.semigroup separatorTable.semigroup where
  toFun := separatorMap
  map_mul := by decide
  preimage := separatorSection
  right_inverse := by intro a; exact by decide +revert

theorem validSeparator (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy separatorTable.semigroup :=
  separatorSurjection.pushforwardIdentity identity valid

def firstMap (a : Fin 2) : Fin 6 :=
  if a = 0 then 0 else 4

def firstEmbedding : Embedding firstTable.semigroup table.semigroup where
  toFun := firstMap
  map_mul := by decide
  injective := by intro a b; exact by decide +revert

theorem validFirst (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy firstTable.semigroup :=
  firstEmbedding.pullback_identity identity valid

end S6_11410

end SemigroupBasis.CoRoots.Order6Day11.FordLordProfile121415
