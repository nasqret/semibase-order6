import SemigroupBasis.CoRoots.Order6Day12.FordLast2.T16Presentation
import SemigroupBasis.CoRoots.Order6Day12.FordLast2.T16CoreObservations
import SemigroupBasis.Examples.LeftNormalBandFifteen
import SemigroupBasis.Subdirect

/-! Two literal catalogue tables and the same actual S3_15-opposite/S5_610 subdirect pair for each. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day12.FordLast2

open SemigroupBasis

def finalTable : FiniteTable where
  order := 3
  mul := fun a b => Examples.leftNormalBandFifteen.mul b a
  assoc := by decide

theorem finalRows_exact :
    List.ofFn (fun a : Fin 3 => List.ofFn (fun b : Fin 3 => (finalTable.mul a b).val)) = [[0,0,0],[0,1,2],[0,1,2]] := by decide

theorem coreRows_exact :
    List.ofFn (fun a : Fin 5 => List.ofFn (fun b : Fin 5 => (coreTable.mul a b).val)) = [[0,0,0,0,0],[0,0,0,0,1],[0,1,2,2,2],[0,1,2,2,3],[0,1,2,2,4]] := by decide

private def toFin1 : Nat → Fin 1
  | _ => 0
private def toFin2 : Nat → Fin 2
  | 0 => 0
  | _ => 1
private def toFin3 : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

private theorem finalLaw00 : law00.SatisfiedBy finalTable.semigroup := by
  have checked : Models finalTable.semigroup [law00] :=
    FiniteCertificate.checkModels_sound finalTable [law00] toFin1 (by decide)
  exact checked law00 (by decide)

private theorem finalLaw01 : law01.SatisfiedBy finalTable.semigroup := by
  have checked : Models finalTable.semigroup [law01] :=
    FiniteCertificate.checkModels_sound finalTable [law01] toFin2 (by decide)
  exact checked law01 (by decide)

private theorem finalLaw02 : law02.SatisfiedBy finalTable.semigroup := by
  have checked : Models finalTable.semigroup [law02] :=
    FiniteCertificate.checkModels_sound finalTable [law02] toFin2 (by decide)
  exact checked law02 (by decide)

private theorem finalLaw03 : law03.SatisfiedBy finalTable.semigroup := by
  have checked : Models finalTable.semigroup [law03] :=
    FiniteCertificate.checkModels_sound finalTable [law03] toFin2 (by decide)
  exact checked law03 (by decide)

private theorem finalLaw04 : law04.SatisfiedBy finalTable.semigroup := by
  have checked : Models finalTable.semigroup [law04] :=
    FiniteCertificate.checkModels_sound finalTable [law04] toFin2 (by decide)
  exact checked law04 (by decide)

private theorem finalLaw05 : law05.SatisfiedBy finalTable.semigroup := by
  have checked : Models finalTable.semigroup [law05] :=
    FiniteCertificate.checkModels_sound finalTable [law05] toFin3 (by decide)
  exact checked law05 (by decide)

private theorem finalLaw06 : law06.SatisfiedBy finalTable.semigroup := by
  have checked : Models finalTable.semigroup [law06] :=
    FiniteCertificate.checkModels_sound finalTable [law06] toFin3 (by decide)
  exact checked law06 (by decide)

private theorem finalLaw07 : law07.SatisfiedBy finalTable.semigroup := by
  have checked : Models finalTable.semigroup [law07] :=
    FiniteCertificate.checkModels_sound finalTable [law07] toFin3 (by decide)
  exact checked law07 (by decide)

private theorem finalLaw08 : law08.SatisfiedBy finalTable.semigroup := by
  have checked : Models finalTable.semigroup [law08] :=
    FiniteCertificate.checkModels_sound finalTable [law08] toFin3 (by decide)
  exact checked law08 (by decide)

theorem finalModels : Models finalTable.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact finalLaw00
  · exact finalLaw01
  · exact finalLaw02
  · exact finalLaw03
  · exact finalLaw04
  · exact finalLaw05
  · exact finalLaw06
  · exact finalLaw07
  · exact finalLaw08

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

private theorem coreLaw07 : law07.SatisfiedBy coreTable.semigroup := by
  have checked : Models coreTable.semigroup [law07] :=
    FiniteCertificate.checkModels_sound coreTable [law07] toFin3 (by decide)
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

theorem lastOfFinalValid (identity : Identity Nat)
    (valid : identity.SatisfiedBy finalTable.semigroup) :
    identity.lhs.reverse.head = identity.rhs.reverse.head := by
  have native : identity.SatisfiedBy Examples.leftNormalBandFifteen.semigroup.opposite := valid
  have reversed := (Identity.satisfiedBy_opposite_iff_reversed identity
    Examples.leftNormalBandFifteen.semigroup).mp native
  exact Examples.leftNormalBandFifteenValid_head_eq identity.reversed reversed

namespace S6_10934

def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else if b = 3 then 0 else if b = 4 then 0 else 0) else
  if a = 1 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else if b = 3 then 0 else if b = 4 then 0 else 1) else
  if a = 2 then (if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 2 else if b = 3 then 2 else if b = 4 then 4 else 2) else
  if a = 3 then (if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 2 else if b = 3 then 2 else if b = 4 then 4 else 3) else
  if a = 4 then (if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 2 else if b = 3 then 2 else if b = 4 then 4 else 2) else
  (if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 2 else if b = 3 then 2 else if b = 4 then 4 else 5)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def catalogueRows : List (List Nat) := [[1,1,1,1,1,1],[1,1,1,1,1,2],[1,2,3,3,5,3],[1,2,3,3,5,4],[1,2,3,3,5,3],[1,2,3,3,5,6]]

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

def finalMap (a : Fin 6) : Fin 3 := if a = 0 then 0 else if a = 1 then 0 else if a = 2 then 1 else if a = 3 then 1 else if a = 4 then 2 else 1

def finalSection (a : Fin 3) : Fin 6 := if a = 0 then 0 else if a = 1 then 2 else 4

def finalQuotient : SplitSurjection table.semigroup finalTable.semigroup where
  toFun := finalMap
  map_mul := by decide
  preimage := finalSection
  right_inverse := by intro value; exact by decide +revert

def coreMap (a : Fin 6) : Fin 5 := if a = 0 then 0 else if a = 1 then 1 else if a = 2 then 2 else if a = 3 then 3 else if a = 4 then 2 else 4

def coreSection (a : Fin 5) : Fin 6 := if a = 0 then 0 else if a = 1 then 1 else if a = 2 then 2 else if a = 3 then 3 else 5

def coreQuotient : SplitSurjection table.semigroup coreTable.semigroup where
  toFun := coreMap
  map_mul := by decide
  preimage := coreSection
  right_inverse := by intro value; exact by decide +revert

def pair : SubdirectPair table.semigroup finalTable.semigroup coreTable.semigroup where
  left := finalQuotient
  right := coreQuotient
  jointlyInjective := by intro a b; exact by decide +revert

theorem valid_iff_factors (identity : Identity Nat) :
    identity.SatisfiedBy table.semigroup ↔
      identity.SatisfiedBy finalTable.semigroup ∧ identity.SatisfiedBy coreTable.semigroup :=
  pair.satisfiedBy_iff identity

end S6_10934

namespace S6_11222

def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else if b = 3 then 0 else if b = 4 then 0 else 0) else
  if a = 1 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else if b = 3 then 0 else if b = 4 then 1 else 1) else
  if a = 2 then (if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 2 else if b = 3 then 2 else if b = 4 then 2 else 2) else
  if a = 3 then (if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 2 else if b = 3 then 2 else if b = 4 then 3 else 3) else
  if a = 4 then (if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 2 else if b = 3 then 2 else if b = 4 then 4 else 5) else
  (if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 2 else if b = 3 then 2 else if b = 4 then 4 else 5)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def catalogueRows : List (List Nat) := [[1,1,1,1,1,1],[1,1,1,1,2,2],[1,2,3,3,3,3],[1,2,3,3,4,4],[1,2,3,3,5,6],[1,2,3,3,5,6]]

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

def finalMap (a : Fin 6) : Fin 3 := if a = 0 then 0 else if a = 1 then 0 else if a = 2 then 0 else if a = 3 then 0 else if a = 4 then 1 else 2

def finalSection (a : Fin 3) : Fin 6 := if a = 0 then 0 else if a = 1 then 4 else 5

def finalQuotient : SplitSurjection table.semigroup finalTable.semigroup where
  toFun := finalMap
  map_mul := by decide
  preimage := finalSection
  right_inverse := by intro value; exact by decide +revert

def coreMap (a : Fin 6) : Fin 5 := if a = 0 then 0 else if a = 1 then 1 else if a = 2 then 2 else if a = 3 then 3 else if a = 4 then 4 else 4

def coreSection (a : Fin 5) : Fin 6 := if a = 0 then 0 else if a = 1 then 1 else if a = 2 then 2 else if a = 3 then 3 else 4

def coreQuotient : SplitSurjection table.semigroup coreTable.semigroup where
  toFun := coreMap
  map_mul := by decide
  preimage := coreSection
  right_inverse := by intro value; exact by decide +revert

def pair : SubdirectPair table.semigroup finalTable.semigroup coreTable.semigroup where
  left := finalQuotient
  right := coreQuotient
  jointlyInjective := by intro a b; exact by decide +revert

theorem valid_iff_factors (identity : Identity Nat) :
    identity.SatisfiedBy table.semigroup ↔
      identity.SatisfiedBy finalTable.semigroup ∧ identity.SatisfiedBy coreTable.semigroup :=
  pair.satisfiedBy_iff identity

end S6_11222


end SemigroupBasis.CoRoots.Order6Day12.FordLast2
