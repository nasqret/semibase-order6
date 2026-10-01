import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0442CyclicMoves
import SemigroupBasis.CoRoots.Order6Day9.S3_18.Rank006Intersection

/-! Exact msg0443 displayed laws and actual finite table interfaces. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0443Group14914

open SemigroupBasis

def law00 : Identity Nat := (Identity.mk (Word.mk 3 [1, 2, 3]) (Word.mk 3 [2, 1, 3]))
def law01 : Identity Nat := (Identity.mk (Word.mk 2 [2, 3, 3]) (Word.mk 3 [3, 2, 2]))
def law02 : Identity Nat := (Identity.mk (Word.mk 2 [2, 3, 3]) (Word.mk 3 [2, 3, 2]))
def law03 : Identity Nat := (Identity.mk (Word.mk 2 [2, 3, 3]) (Word.mk 3 [2, 2, 3]))
def law04 : Identity Nat := (Identity.mk (Word.mk 0 [0]) (Word.mk 0 [0, 0, 0, 0]))
def law05 : Identity Nat := (Identity.mk (Word.mk 0 [1, 0]) (Word.mk 0 [0, 0, 0, 1, 0]))
def law06 : Identity Nat := (Identity.mk (Word.mk 0 [0, 0, 1, 0]) (Word.mk 1 [0, 1, 1, 1]))
def law07 : Identity Nat := (Identity.mk (Word.mk 0 [0, 0, 1, 1]) (Word.mk 1 [0, 0, 0, 1]))
def law08 : Identity Nat := (Identity.mk (Word.mk 0 [0, 1, 2, 1]) (Word.mk 0 [1, 0, 2, 1]))
def law09 : Identity Nat := (Identity.mk (Word.mk 0 [0, 1, 2, 1]) (Word.mk 0 [1, 1, 2, 0]))
def law10 : Identity Nat := (Identity.mk (Word.mk 0 [0, 1, 2, 1]) (Word.mk 0 [2, 0, 1, 1]))
def law11 : Identity Nat := (Identity.mk (Word.mk 0 [0, 1, 2, 1]) (Word.mk 1 [0, 0, 2, 1]))
def law12 : Identity Nat := (Identity.mk (Word.mk 0 [1, 2, 3, 0]) (Word.mk 0 [1, 3, 2, 0]))
def basis : List (Identity Nat) := [law00, law01, law02, law03, law04, law05, law06, law07, law08, law09, law10, law11, law12]
def basisSHA256 : String := "dc3543fbce9eb1776819b5f117120226a3ce993f38e7c42e4740b717db27ecfb"
theorem basis_length : basis.length = 13 := rfl

abbrev leftTable := Generated.Catalogue.S3_18.table
abbrev expandedTable := Generated.Catalogue.S4_124.table
abbrev rightTable := Generated.Catalogue.S4_69.table
def toFinite : Nat → Fin 4
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 3

theorem leftModels : Models leftTable.semigroup basis :=
  FiniteCertificate.checkModels_sound leftTable basis toFinite (by decide)
theorem rightModels : Models rightTable.semigroup basis :=
  FiniteCertificate.checkModels_sound rightTable basis toFinite (by decide)
theorem expandedModels : Models expandedTable.semigroup basis :=
  FiniteCertificate.checkModels_sound expandedTable basis toFinite (by decide)

def mul14914 (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else if b = 3 then 0 else if b = 4 then 0 else 0) else
  if a = 1 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else if b = 3 then 1 else if b = 4 then 0 else 0) else
  if a = 2 then (if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 2 else if b = 3 then 0 else if b = 4 then 4 else 5) else
  if a = 3 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else if b = 3 then 3 else if b = 4 then 0 else 0) else
  if a = 4 then (if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 4 else if b = 3 then 0 else if b = 4 then 5 else 2) else
  (if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 5 else if b = 3 then 0 else if b = 4 then 2 else 4)
def table14914 : FiniteTable := ⟨6, mul14914, by decide⟩
theorem rows14914 :
    (List.finRange 6).map (fun a => (List.finRange 6).map (fun b => (mul14914 a b).val)) =
      [[0,0,0,0,0,0],[0,0,0,1,0,0],[0,1,2,0,4,5],[0,0,0,3,0,0],[0,1,4,0,5,2],[0,1,5,0,2,4]] := by decide
def map14914Left (value : Fin 6) : Fin 4 := if value = 0 then 0 else if value = 1 then 0 else if value = 2 then 1 else if value = 3 then 0 else if value = 4 then 2 else 3
def section14914Left (value : Fin 4) : Fin 6 := if value = 0 then 0 else if value = 1 then 2 else if value = 2 then 4 else 5
def onto14914Left : SplitSurjection table14914.semigroup expandedTable.semigroup where
  toFun := map14914Left
  map_mul := by decide
  preimage := section14914Left
  right_inverse := by decide
def map14914Right (value : Fin 6) : Fin 4 := if value = 0 then 0 else if value = 1 then 1 else if value = 2 then 2 else if value = 3 then 3 else if value = 4 then 2 else 2
def section14914Right (value : Fin 4) : Fin 6 := if value = 0 then 0 else if value = 1 then 1 else if value = 2 then 2 else 3
def onto14914Right : SplitSurjection table14914.semigroup rightTable.semigroup where
  toFun := map14914Right
  map_mul := by decide
  preimage := section14914Right
  right_inverse := by decide
def subdirect14914 : SubdirectPair table14914.semigroup expandedTable.semigroup rightTable.semigroup where
  left := onto14914Left
  right := onto14914Right
  jointlyInjective := by unfold Function.Injective; decide

def mul14937 (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else if b = 3 then 0 else if b = 4 then 4 else 5) else
  if a = 1 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else if b = 3 then 1 else if b = 4 then 4 else 5) else
  if a = 2 then (if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 2 else if b = 3 then 0 else if b = 4 then 4 else 5) else
  if a = 3 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else if b = 3 then 3 else if b = 4 then 4 else 5) else
  if a = 4 then (if b = 0 then 4 else if b = 1 then 4 else if b = 2 then 4 else if b = 3 then 4 else if b = 4 then 5 else 0) else
  (if b = 0 then 5 else if b = 1 then 5 else if b = 2 then 5 else if b = 3 then 5 else if b = 4 then 0 else 4)
def table14937 : FiniteTable := ⟨6, mul14937, by decide⟩
theorem rows14937 :
    (List.finRange 6).map (fun a => (List.finRange 6).map (fun b => (mul14937 a b).val)) =
      [[0,0,0,0,4,5],[0,0,0,1,4,5],[0,1,2,0,4,5],[0,0,0,3,4,5],[4,4,4,4,5,0],[5,5,5,5,0,4]] := by decide
def map14937Left (value : Fin 6) : Fin 3 := if value = 0 then 0 else if value = 1 then 0 else if value = 2 then 0 else if value = 3 then 0 else if value = 4 then 1 else 2
def section14937Left (value : Fin 3) : Fin 6 := if value = 0 then 0 else if value = 1 then 4 else 5
def onto14937Left : SplitSurjection table14937.semigroup leftTable.semigroup where
  toFun := map14937Left
  map_mul := by decide
  preimage := section14937Left
  right_inverse := by decide
def map14937Right (value : Fin 6) : Fin 4 := if value = 0 then 0 else if value = 1 then 1 else if value = 2 then 2 else if value = 3 then 3 else if value = 4 then 0 else 0
def section14937Right (value : Fin 4) : Fin 6 := if value = 0 then 0 else if value = 1 then 1 else if value = 2 then 2 else 3
def onto14937Right : SplitSurjection table14937.semigroup rightTable.semigroup where
  toFun := map14937Right
  map_mul := by decide
  preimage := section14937Right
  right_inverse := by decide
def subdirect14937 : SubdirectPair table14937.semigroup leftTable.semigroup rightTable.semigroup where
  left := onto14937Left
  right := onto14937Right
  jointlyInjective := by unfold Function.Injective; decide

def mul15924 (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else if b = 3 then 3 else if b = 4 then 4 else 4) else
  if a = 1 then (if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 0 else if b = 3 then 3 else if b = 4 then 4 else 4) else
  if a = 2 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 2 else if b = 3 then 3 else if b = 4 then 4 else 5) else
  if a = 3 then (if b = 0 then 3 else if b = 1 then 3 else if b = 2 then 3 else if b = 3 then 4 else if b = 4 then 0 else 0) else
  if a = 4 then (if b = 0 then 4 else if b = 1 then 4 else if b = 2 then 4 else if b = 3 then 0 else if b = 4 then 3 else 3) else
  (if b = 0 then 4 else if b = 1 then 5 else if b = 2 then 4 else if b = 3 then 0 else if b = 4 then 3 else 3)
def table15924 : FiniteTable := ⟨6, mul15924, by decide⟩
theorem rows15924 :
    (List.finRange 6).map (fun a => (List.finRange 6).map (fun b => (mul15924 a b).val)) =
      [[0,0,0,3,4,4],[0,1,0,3,4,4],[0,0,2,3,4,5],[3,3,3,4,0,0],[4,4,4,0,3,3],[4,5,4,0,3,3]] := by decide
def map15924Left (value : Fin 6) : Fin 3 := if value = 0 then 0 else if value = 1 then 0 else if value = 2 then 0 else if value = 3 then 1 else if value = 4 then 2 else 2
def section15924Left (value : Fin 3) : Fin 6 := if value = 0 then 0 else if value = 1 then 3 else 4
def onto15924Left : SplitSurjection table15924.semigroup leftTable.semigroup where
  toFun := map15924Left
  map_mul := by decide
  preimage := section15924Left
  right_inverse := by decide
def map15924Right (value : Fin 6) : Fin 4 := if value = 0 then 0 else if value = 1 then 3 else if value = 2 then 2 else if value = 3 then 0 else if value = 4 then 0 else 1
def section15924Right (value : Fin 4) : Fin 6 := if value = 0 then 0 else if value = 1 then 5 else if value = 2 then 2 else 1
def onto15924Right : SplitSurjection table15924.semigroup rightTable.semigroup where
  toFun := map15924Right
  map_mul := by decide
  preimage := section15924Right
  right_inverse := by decide
def subdirect15924 : SubdirectPair table15924.semigroup leftTable.semigroup rightTable.semigroup where
  left := onto15924Left
  right := onto15924Right
  jointlyInjective := by unfold Function.Injective; decide

theorem models14914 : Models table14914.semigroup basis := by
  intro identity member
  exact (subdirect14914.satisfiedBy_iff identity).mpr ⟨expandedModels identity member, rightModels identity member⟩
theorem models14937 : Models table14937.semigroup basis := by
  intro identity member
  exact (subdirect14937.satisfiedBy_iff identity).mpr ⟨leftModels identity member, rightModels identity member⟩
theorem models15924 : Models table15924.semigroup basis := by
  intro identity member
  exact (subdirect15924.satisfiedBy_iff identity).mpr ⟨leftModels identity member, rightModels identity member⟩

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0443Group14914
