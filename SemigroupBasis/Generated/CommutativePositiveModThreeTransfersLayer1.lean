import SemigroupBasis.Examples.CommutativePositiveModThreeFour
import SemigroupBasis.Generated.Catalogue
import SemigroupBasis.Generated.S4_124
import SemigroupBasis.FiniteReflection
import SemigroupBasis.TransferPower

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.CommutativePositiveModThreeTransfers

open SemigroupBasis
open SemigroupBasis.Examples

-- BEGIN S4_125
namespace S4_125

/-- This is the supplied embedding `S4_125 ↪ S4_124²`. It is retained as
direction evidence, but it cannot transfer a basis from `S4_124` to
`S4_125`: `inheritAlongPowerEmbedding` requires the reverse embedding. -/
def reversePowerEmbedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_125.table.semigroup
      (SemigroupBasis.Generated.Catalogue.S4_124.table.semigroup.pi (Fin 2)) where
  toFun := fun (a : Fin 4) (i : Fin 2) =>
    if i = 0 then if a = 0 then (0 : Fin 4) else if a = 1 then (1 : Fin 4) else if a = 2 then (0 : Fin 4) else (0 : Fin 4) else if a = 0 then (1 : Fin 4) else if a = 1 then (1 : Fin 4) else if a = 2 then (2 : Fin 4) else (3 : Fin 4)
  map_mul := by
    intro a b
    funext i
    exact by decide +revert
  injective := by
    intro a b h
    have h0 := congrFun h (0 : Fin 2)
    have h1 := congrFun h (1 : Fin 2)
    clear h
    exact by decide +revert

def finitePowerLaw : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteCommutativityLaw : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finitePowerLaw_map :
    finitePowerLaw.map Fin.val = positiveModThreePowerLaw := rfl

theorem finiteCommutativityLaw_map :
    finiteCommutativityLaw.map Fin.val =
      positiveModThreeCommutativityLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S4_125.table.semigroup commutativePositiveModThreeBasis := by
  intro e he
  simp only [commutativePositiveModThreeBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · rw [← finitePowerLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S4_125.table.checkIdentityNat_sound
      finitePowerLaw (by decide)
  · rw [← finiteCommutativityLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S4_125.table.checkIdentityNat_sound
      finiteCommutativityLaw (by decide)

private def modThreeState (n : Nat) : Fin 4 :=
  if n % 3 = 0 then 0 else if n % 3 = 1 then 2 else 3

private def modThreeSeparator (z : Nat) : Nat → Fin 4 :=
  fun x => if x = z then 2 else 0

private theorem modThreeMul_target (n : Nat) :
    SemigroupBasis.Generated.Catalogue.S4_125.mul
        (modThreeState n) 2 =
      modThreeState (n + 1) := by
  by_cases h0 : n % 3 = 0
  · have hnext : (n + 1) % 3 = 1 := by omega
    simp [modThreeState, h0, hnext,
      SemigroupBasis.Generated.Catalogue.S4_125.mul]
  · by_cases h1 : n % 3 = 1
    · have hnext : (n + 1) % 3 = 2 := by omega
      simp [modThreeState, h1, hnext,
        SemigroupBasis.Generated.Catalogue.S4_125.mul]
    · have h2 : n % 3 = 2 := by omega
      have hnext : (n + 1) % 3 = 0 := by omega
      simp [modThreeState, h2, hnext,
        SemigroupBasis.Generated.Catalogue.S4_125.mul]

private theorem modThreeMul_other (n : Nat) :
    SemigroupBasis.Generated.Catalogue.S4_125.mul
        (modThreeState n) 0 =
      modThreeState n := by
  by_cases h0 : n % 3 = 0
  · simp [modThreeState, h0,
      SemigroupBasis.Generated.Catalogue.S4_125.mul]
  · by_cases h1 : n % 3 = 1
    · simp [modThreeState, h1,
        SemigroupBasis.Generated.Catalogue.S4_125.mul]
    · have h2 : n % 3 = 2 := by omega
      simp [modThreeState, h2,
        SemigroupBasis.Generated.Catalogue.S4_125.mul]

private theorem modThreeFold
    (z : Nat) (xs : List Nat) (acc : Nat) :
    xs.foldl
        (fun current x =>
          SemigroupBasis.Generated.Catalogue.S4_125.mul current
            (modThreeSeparator z x))
        (modThreeState acc) =
      modThreeState (acc + xs.count z) := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      by_cases hx : x = z
      · subst x
        rw [List.count_cons_self]
        rw [show modThreeSeparator z z = (2 : Fin 4) by
          simp [modThreeSeparator]]
        rw [modThreeMul_target, ih]
        congr 1
        omega
      · rw [List.count_cons_of_ne hx]
        rw [show modThreeSeparator z x = (0 : Fin 4) by
          simp [modThreeSeparator, hx]]
        rw [modThreeMul_other, ih]

theorem eval_modThreeSeparator (z : Nat) (w : Word Nat) :
    SemigroupBasis.Generated.Catalogue.S4_125.table.semigroup.eval (modThreeSeparator z) w =
      modThreeState (w.toList.count z) := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current x =>
              SemigroupBasis.Generated.Catalogue.S4_125.mul current
                (modThreeSeparator z x))
            (modThreeSeparator z head) =
          modThreeState ((head :: tail).count z)
      by_cases hhead : head = z
      · subst head
        rw [List.count_cons_self]
        rw [show modThreeSeparator z z = modThreeState 1 by
          apply Fin.ext
          simp [modThreeSeparator, modThreeState]]
        rw [modThreeFold]
        congr 1
        omega
      · rw [List.count_cons_of_ne hhead]
        rw [show modThreeSeparator z head = modThreeState 0 by
          apply Fin.ext
          simp [modThreeSeparator, modThreeState, hhead]]
        rw [modThreeFold]
        congr 1
        omega

private theorem modThreeState_eq_iff (m n : Nat) :
    modThreeState m = modThreeState n ↔ m % 3 = n % 3 := by
  have hm : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
  have hn : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases hm with hm | hm | hm <;>
    rcases hn with hn | hn | hn <;>
    simp [modThreeState, hm, hn]

private def supportState (n : Nat) : Fin 4 :=
  if n = 0 then 1 else 0

private def supportSeparator (z : Nat) : Nat → Fin 4 :=
  fun x => if x = z then 0 else 1

private theorem supportMul_target (n : Nat) :
    SemigroupBasis.Generated.Catalogue.S4_125.mul
        (supportState n) 0 =
      supportState (n + 1) := by
  by_cases hn : n = 0
  · subst n
    rfl
  · simp [supportState, hn,
      SemigroupBasis.Generated.Catalogue.S4_125.mul]

private theorem supportMul_other (n : Nat) :
    SemigroupBasis.Generated.Catalogue.S4_125.mul
        (supportState n) 1 =
      supportState n := by
  by_cases hn : n = 0
  · subst n
    rfl
  · simp [supportState, hn,
      SemigroupBasis.Generated.Catalogue.S4_125.mul]

private theorem supportFold
    (z : Nat) (xs : List Nat) (acc : Nat) :
    xs.foldl
        (fun current x =>
          SemigroupBasis.Generated.Catalogue.S4_125.mul current
            (supportSeparator z x))
        (supportState acc) =
      supportState (acc + xs.count z) := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      by_cases hx : x = z
      · subst x
        rw [List.count_cons_self]
        rw [show supportSeparator z z = (0 : Fin 4) by
          simp [supportSeparator]]
        rw [supportMul_target, ih]
        congr 1
        omega
      · rw [List.count_cons_of_ne hx]
        rw [show supportSeparator z x = (1 : Fin 4) by
          simp [supportSeparator, hx]]
        rw [supportMul_other, ih]

theorem eval_supportSeparator (z : Nat) (w : Word Nat) :
    SemigroupBasis.Generated.Catalogue.S4_125.table.semigroup.eval (supportSeparator z) w =
      supportState (w.toList.count z) := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current x =>
              SemigroupBasis.Generated.Catalogue.S4_125.mul current
                (supportSeparator z x))
            (supportSeparator z head) =
          supportState ((head :: tail).count z)
      by_cases hhead : head = z
      · subst head
        rw [List.count_cons_self]
        rw [show supportSeparator z z = supportState 1 by
          apply Fin.ext
          simp [supportSeparator, supportState]]
        rw [supportFold]
        congr 1
        omega
      · rw [List.count_cons_of_ne hhead]
        rw [show supportSeparator z head = supportState 0 by
          apply Fin.ext
          simp [supportSeparator, supportState, hhead]]
        rw [supportFold]
        congr 1
        omega

private theorem supportState_eq_iff (m n : Nat) :
    supportState m = supportState n ↔ (m = 0 ↔ n = 0) := by
  by_cases hm : m = 0 <;> by_cases hn : n = 0 <;>
    simp [supportState, hm, hn]

theorem valid_support (e : Identity Nat)
    (valid : e.SatisfiedBy SemigroupBasis.Generated.Catalogue.S4_125.table.semigroup) :
    ∀ z, z ∈ e.lhs.toList ↔ z ∈ e.rhs.toList := by
  intro z
  have evaluated := valid (supportSeparator z)
  rw [eval_supportSeparator, eval_supportSeparator] at evaluated
  have zeroEq :=
    (supportState_eq_iff _ _).mp evaluated
  rw [← List.count_pos_iff, ← List.count_pos_iff]
  constructor <;> intro hpos
  · have hnzero : e.lhs.toList.count z ≠ 0 := by omega
    have hrzero : e.rhs.toList.count z ≠ 0 :=
      fun hr => hnzero (zeroEq.mpr hr)
    omega
  · have hnzero : e.rhs.toList.count z ≠ 0 := by omega
    have hlzero : e.lhs.toList.count z ≠ 0 :=
      fun hl => hnzero (zeroEq.mp hl)
    omega

theorem valid_count_mod_three (e : Identity Nat)
    (valid : e.SatisfiedBy SemigroupBasis.Generated.Catalogue.S4_125.table.semigroup) :
    ∀ z, e.lhs.toList.count z % 3 =
      e.rhs.toList.count z % 3 := by
  intro z
  have evaluated := valid (modThreeSeparator z)
  rw [eval_modThreeSeparator, eval_modThreeSeparator] at evaluated
  exact (modThreeState_eq_iff _ _).mp evaluated

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_125.table.semigroup commutativePositiveModThreeBasis :=
  commutativePositiveModThreeBasis_complete_of_separates
    SemigroupBasis.Generated.Catalogue.S4_125.table targetModels valid_support valid_count_mod_three

end S4_125
-- END S4_125

-- BEGIN S5_1145
namespace S5_1145

def embedding :
    Embedding SemigroupBasis.Generated.S4_124.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1145.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (2 : Fin 5) else if a = 2 then (3 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finitePowerLaw : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteCommutativityLaw : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finitePowerLaw_map :
    finitePowerLaw.map Fin.val = positiveModThreePowerLaw := rfl

theorem finiteCommutativityLaw_map :
    finiteCommutativityLaw.map Fin.val =
      positiveModThreeCommutativityLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1145.table.semigroup commutativePositiveModThreeBasis := by
  intro e he
  simp only [commutativePositiveModThreeBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · rw [← finitePowerLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1145.table.checkIdentityNat_sound
      finitePowerLaw (by decide)
  · rw [← finiteCommutativityLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1145.table.checkIdentityNat_sound
      finiteCommutativityLaw (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1145.table.semigroup commutativePositiveModThreeBasis :=
  SemigroupBasis.Generated.S4_124.representative_basis.inheritAlongEmbedding
    embedding targetModels

end S5_1145
-- END S5_1145

-- BEGIN S5_1147
namespace S5_1147

def embedding :
    Embedding SemigroupBasis.Generated.S4_124.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1147.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (2 : Fin 5) else if a = 2 then (3 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finitePowerLaw : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteCommutativityLaw : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finitePowerLaw_map :
    finitePowerLaw.map Fin.val = positiveModThreePowerLaw := rfl

theorem finiteCommutativityLaw_map :
    finiteCommutativityLaw.map Fin.val =
      positiveModThreeCommutativityLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1147.table.semigroup commutativePositiveModThreeBasis := by
  intro e he
  simp only [commutativePositiveModThreeBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · rw [← finitePowerLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1147.table.checkIdentityNat_sound
      finitePowerLaw (by decide)
  · rw [← finiteCommutativityLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1147.table.checkIdentityNat_sound
      finiteCommutativityLaw (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1147.table.semigroup commutativePositiveModThreeBasis :=
  SemigroupBasis.Generated.S4_124.representative_basis.inheritAlongEmbedding
    embedding targetModels

end S5_1147
-- END S5_1147

-- BEGIN S5_1148
namespace S5_1148

def embedding :
    Embedding SemigroupBasis.Generated.S4_124.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1148.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (3 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finitePowerLaw : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteCommutativityLaw : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finitePowerLaw_map :
    finitePowerLaw.map Fin.val = positiveModThreePowerLaw := rfl

theorem finiteCommutativityLaw_map :
    finiteCommutativityLaw.map Fin.val =
      positiveModThreeCommutativityLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1148.table.semigroup commutativePositiveModThreeBasis := by
  intro e he
  simp only [commutativePositiveModThreeBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · rw [← finitePowerLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1148.table.checkIdentityNat_sound
      finitePowerLaw (by decide)
  · rw [← finiteCommutativityLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1148.table.checkIdentityNat_sound
      finiteCommutativityLaw (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1148.table.semigroup commutativePositiveModThreeBasis :=
  SemigroupBasis.Generated.S4_124.representative_basis.inheritAlongEmbedding
    embedding targetModels

end S5_1148
-- END S5_1148

-- BEGIN S5_1150
namespace S5_1150

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_125.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1150.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (3 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finitePowerLaw : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteCommutativityLaw : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finitePowerLaw_map :
    finitePowerLaw.map Fin.val = positiveModThreePowerLaw := rfl

theorem finiteCommutativityLaw_map :
    finiteCommutativityLaw.map Fin.val =
      positiveModThreeCommutativityLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1150.table.semigroup commutativePositiveModThreeBasis := by
  intro e he
  simp only [commutativePositiveModThreeBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · rw [← finitePowerLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1150.table.checkIdentityNat_sound
      finitePowerLaw (by decide)
  · rw [← finiteCommutativityLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1150.table.checkIdentityNat_sound
      finiteCommutativityLaw (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1150.table.semigroup commutativePositiveModThreeBasis :=
  SemigroupBasis.Generated.CommutativePositiveModThreeTransfers.S4_125.representative_basis.inheritAlongEmbedding
    embedding targetModels

end S5_1150
-- END S5_1150

-- BEGIN S5_1151
namespace S5_1151

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_125.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1151.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (3 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def finitePowerLaw : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteCommutativityLaw : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem finitePowerLaw_map :
    finitePowerLaw.map Fin.val = positiveModThreePowerLaw := rfl

theorem finiteCommutativityLaw_map :
    finiteCommutativityLaw.map Fin.val =
      positiveModThreeCommutativityLaw := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_1151.table.semigroup commutativePositiveModThreeBasis := by
  intro e he
  simp only [commutativePositiveModThreeBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · rw [← finitePowerLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1151.table.checkIdentityNat_sound
      finitePowerLaw (by decide)
  · rw [← finiteCommutativityLaw_map]
    exact SemigroupBasis.Generated.Catalogue.S5_1151.table.checkIdentityNat_sound
      finiteCommutativityLaw (by decide)

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1151.table.semigroup commutativePositiveModThreeBasis :=
  SemigroupBasis.Generated.CommutativePositiveModThreeTransfers.S4_125.representative_basis.inheritAlongEmbedding
    embedding targetModels

end S5_1151
-- END S5_1151

end SemigroupBasis.Generated.CommutativePositiveModThreeTransfers
