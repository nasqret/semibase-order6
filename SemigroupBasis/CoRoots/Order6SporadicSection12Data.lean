import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6SporadicSection12

open SemigroupBasis

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def word_12_1a_left : Word Nat := w 0 [0, 0, 1]
def word_12_1a_right : Word Nat := w 0 [0, 1]
def law_12_1a : Identity Nat := ⟨word_12_1a_left, word_12_1a_right⟩
def word_12_1b_left : Word Nat := w 0 [1, 0, 2]
def word_12_1b_right : Word Nat := w 0 [0, 1, 2]
def law_12_1b : Identity Nat := ⟨word_12_1b_left, word_12_1b_right⟩
def word_12_1c_empty_left : Word Nat := w 0 [0, 1, 1, 0]
def word_12_1c_empty_right : Word Nat := w 0 [0, 1, 1, 1]
def law_12_1c_empty : Identity Nat := ⟨word_12_1c_empty_left, word_12_1c_empty_right⟩
def word_12_1c_H_left : Word Nat := w 0 [0, 3, 1, 1, 0]
def word_12_1c_H_right : Word Nat := w 0 [0, 3, 1, 1, 1]
def law_12_1c_H : Identity Nat := ⟨word_12_1c_H_left, word_12_1c_H_right⟩
def word_12_1c_K_left : Word Nat := w 0 [0, 1, 1, 4, 0]
def word_12_1c_K_right : Word Nat := w 0 [0, 1, 1, 4, 1]
def law_12_1c_K : Identity Nat := ⟨word_12_1c_K_left, word_12_1c_K_right⟩
def word_12_1c_HK_left : Word Nat := w 0 [0, 3, 1, 1, 4, 0]
def word_12_1c_HK_right : Word Nat := w 0 [0, 3, 1, 1, 4, 1]
def law_12_1c_HK : Identity Nat := ⟨word_12_1c_HK_left, word_12_1c_HK_right⟩
def word_12_3a_empty_left : Word Nat := w 0 [0, 0, 0]
def word_12_3a_empty_right : Word Nat := w 0 [0, 0]
def law_12_3a_empty : Identity Nat := ⟨word_12_3a_empty_left, word_12_3a_empty_right⟩
def word_12_3a_H_left : Word Nat := w 0 [0, 0, 3, 0]
def word_12_3a_H_right : Word Nat := w 0 [0, 3, 0]
def law_12_3a_H : Identity Nat := ⟨word_12_3a_H_left, word_12_3a_H_right⟩
def word_12_3b_empty_left : Word Nat := w 0 [1, 2, 0]
def word_12_3b_empty_right : Word Nat := w 0 [2, 1, 0]
def law_12_3b_empty : Identity Nat := ⟨word_12_3b_empty_left, word_12_3b_empty_right⟩
def word_12_3b_H_left : Word Nat := w 0 [3, 1, 2, 0]
def word_12_3b_H_right : Word Nat := w 0 [3, 2, 1, 0]
def law_12_3b_H : Identity Nat := ⟨word_12_3b_H_left, word_12_3b_H_right⟩
def word_12_3b_K_left : Word Nat := w 0 [1, 2, 4, 0]
def word_12_3b_K_right : Word Nat := w 0 [2, 1, 4, 0]
def law_12_3b_K : Identity Nat := ⟨word_12_3b_K_left, word_12_3b_K_right⟩
def word_12_3b_HK_left : Word Nat := w 0 [3, 1, 2, 4, 0]
def word_12_3b_HK_right : Word Nat := w 0 [3, 2, 1, 4, 0]
def law_12_3b_HK : Identity Nat := ⟨word_12_3b_HK_left, word_12_3b_HK_right⟩
def word_12_3c_left_empty_left : Word Nat := w 0 [1, 0, 1]
def word_12_3c_left_empty_right : Word Nat := w 0 [1, 1, 0]
def law_12_3c_left_empty : Identity Nat := ⟨word_12_3c_left_empty_left, word_12_3c_left_empty_right⟩
def word_12_3c_left_H_left : Word Nat := w 0 [3, 1, 0, 1]
def word_12_3c_left_H_right : Word Nat := w 0 [3, 1, 1, 0]
def law_12_3c_left_H : Identity Nat := ⟨word_12_3c_left_H_left, word_12_3c_left_H_right⟩
def word_12_3c_left_K_left : Word Nat := w 0 [1, 4, 0, 1]
def word_12_3c_left_K_right : Word Nat := w 0 [1, 4, 1, 0]
def law_12_3c_left_K : Identity Nat := ⟨word_12_3c_left_K_left, word_12_3c_left_K_right⟩
def word_12_3c_left_HK_left : Word Nat := w 0 [3, 1, 4, 0, 1]
def word_12_3c_left_HK_right : Word Nat := w 0 [3, 1, 4, 1, 0]
def law_12_3c_left_HK : Identity Nat := ⟨word_12_3c_left_HK_left, word_12_3c_left_HK_right⟩
def word_12_3c_right_empty_left : Word Nat := w 0 [1, 0, 1]
def word_12_3c_right_empty_right : Word Nat := w 1 [0, 0, 1]
def law_12_3c_right_empty : Identity Nat := ⟨word_12_3c_right_empty_left, word_12_3c_right_empty_right⟩
def word_12_3c_right_H_left : Word Nat := w 0 [1, 3, 0, 1]
def word_12_3c_right_H_right : Word Nat := w 1 [0, 3, 0, 1]
def law_12_3c_right_H : Identity Nat := ⟨word_12_3c_right_H_left, word_12_3c_right_H_right⟩
def word_12_3c_right_K_left : Word Nat := w 0 [1, 0, 4, 1]
def word_12_3c_right_K_right : Word Nat := w 1 [0, 0, 4, 1]
def law_12_3c_right_K : Identity Nat := ⟨word_12_3c_right_K_left, word_12_3c_right_K_right⟩
def word_12_3c_right_HK_left : Word Nat := w 0 [1, 3, 0, 4, 1]
def word_12_3c_right_HK_right : Word Nat := w 1 [0, 3, 0, 4, 1]
def law_12_3c_right_HK : Identity Nat := ⟨word_12_3c_right_HK_left, word_12_3c_right_HK_right⟩
def word_12_4_empty_left : Word Nat := w 0 [0, 1, 1]
def word_12_4_empty_right : Word Nat := w 0 [1, 0, 1]
def law_12_4_empty : Identity Nat := ⟨word_12_4_empty_left, word_12_4_empty_right⟩
def word_12_4_H_left : Word Nat := w 0 [3, 0, 1, 1]
def word_12_4_H_right : Word Nat := w 0 [3, 1, 0, 1]
def law_12_4_H : Identity Nat := ⟨word_12_4_H_left, word_12_4_H_right⟩
def word_12_4_K_left : Word Nat := w 0 [0, 1, 4, 1]
def word_12_4_K_right : Word Nat := w 0 [1, 0, 4, 1]
def law_12_4_K : Identity Nat := ⟨word_12_4_K_left, word_12_4_K_right⟩
def word_12_4_HK_left : Word Nat := w 0 [3, 0, 1, 4, 1]
def word_12_4_HK_right : Word Nat := w 0 [3, 1, 0, 4, 1]
def law_12_4_HK : Identity Nat := ⟨word_12_4_HK_left, word_12_4_HK_right⟩

@[simp] theorem word_12_4_empty_left_shape :
    word_12_4_empty_left = ⟨0, [0, 1, 1]⟩ := by
  rfl

@[simp] theorem word_12_4_empty_right_shape :
    word_12_4_empty_right = ⟨0, [1, 0, 1]⟩ := by
  rfl

@[simp] theorem word_12_4_H_left_shape :
    word_12_4_H_left = ⟨0, [3, 0, 1, 1]⟩ := by
  rfl

@[simp] theorem word_12_4_H_right_shape :
    word_12_4_H_right = ⟨0, [3, 1, 0, 1]⟩ := by
  rfl

@[simp] theorem word_12_4_K_left_shape :
    word_12_4_K_left = ⟨0, [0, 1, 4, 1]⟩ := by
  rfl

@[simp] theorem word_12_4_K_right_shape :
    word_12_4_K_right = ⟨0, [1, 0, 4, 1]⟩ := by
  rfl

@[simp] theorem word_12_4_HK_left_shape :
    word_12_4_HK_left = ⟨0, [3, 0, 1, 4, 1]⟩ := by
  rfl

@[simp] theorem word_12_4_HK_right_shape :
    word_12_4_HK_right = ⟨0, [3, 1, 0, 4, 1]⟩ := by
  rfl

/-- The six ordinary identities from Proposition 12.1 -/
def a2Basis : List (Identity Nat) :=
  [law_12_1a, law_12_1b, law_12_1c_empty, law_12_1c_H, law_12_1c_K, law_12_1c_HK]

def a2OppositeBasis : List (Identity Nat) :=
  reversedBasis a2Basis


/-- The fourteen ordinary identities from Proposition 12.4 -/
def b8Basis : List (Identity Nat) :=
  [law_12_3a_empty, law_12_3a_H, law_12_3b_empty, law_12_3b_H, law_12_3b_K, law_12_3b_HK, law_12_3c_left_empty, law_12_3c_left_H, law_12_3c_left_K, law_12_3c_left_HK, law_12_3c_right_empty, law_12_3c_right_H, law_12_3c_right_K, law_12_3c_right_HK]

def b8OppositeBasis : List (Identity Nat) :=
  reversedBasis b8Basis


/-- The eighteen ordinary identities from Proposition 12.8 -/
def b7Basis : List (Identity Nat) :=
  [law_12_3a_empty, law_12_3a_H, law_12_3b_empty, law_12_3b_H, law_12_3b_K, law_12_3b_HK, law_12_3c_left_empty, law_12_3c_left_H, law_12_3c_left_K, law_12_3c_left_HK, law_12_3c_right_empty, law_12_3c_right_H, law_12_3c_right_K, law_12_3c_right_HK, law_12_4_empty, law_12_4_H, law_12_4_K, law_12_4_HK]

def b7OppositeBasis : List (Identity Nat) :=
  reversedBasis b7Basis


def a2Part01Basis : List (Identity Nat) :=
  [law_12_1a, law_12_1b, law_12_1c_empty]

def a2Part02Basis : List (Identity Nat) :=
  [law_12_1c_H, law_12_1c_K, law_12_1c_HK]

theorem a2Basis_eq_parts :
    a2Basis =
    a2Part01Basis ++
    a2Part02Basis := by
  rfl

def b7Part01Basis : List (Identity Nat) :=
  [law_12_3a_empty, law_12_3a_H, law_12_3b_empty]

def b7Part02Basis : List (Identity Nat) :=
  [law_12_3b_H, law_12_3b_K, law_12_3b_HK]

def b7Part03Basis : List (Identity Nat) :=
  [law_12_3c_left_empty, law_12_3c_left_H, law_12_3c_left_K]

def b7Part04Basis : List (Identity Nat) :=
  [law_12_3c_left_HK, law_12_3c_right_empty, law_12_3c_right_H]

def b7Part05Basis : List (Identity Nat) :=
  [law_12_3c_right_K, law_12_3c_right_HK, law_12_4_empty]

def b7Part06Basis : List (Identity Nat) :=
  [law_12_4_H, law_12_4_K, law_12_4_HK]

theorem b7Basis_eq_parts :
    b7Basis =
    b7Part01Basis ++
    b7Part02Basis ++
    b7Part03Basis ++
    b7Part04Basis ++
    b7Part05Basis ++
    b7Part06Basis := by
  rfl

def b8Part01Basis : List (Identity Nat) :=
  [law_12_3a_empty, law_12_3a_H, law_12_3b_empty]

def b8Part02Basis : List (Identity Nat) :=
  [law_12_3b_H, law_12_3b_K, law_12_3b_HK]

def b8Part03Basis : List (Identity Nat) :=
  [law_12_3c_left_empty, law_12_3c_left_H, law_12_3c_left_K]

def b8Part04Basis : List (Identity Nat) :=
  [law_12_3c_left_HK, law_12_3c_right_empty, law_12_3c_right_H]

def b8Part05Basis : List (Identity Nat) :=
  [law_12_3c_right_K, law_12_3c_right_HK]

theorem b8Basis_eq_parts :
    b8Basis =
    b8Part01Basis ++
    b8Part02Basis ++
    b8Part03Basis ++
    b8Part04Basis ++
    b8Part05Basis := by
  rfl

private def toFinFive : Nat → Fin 5
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | _ => 4

def finiteA2Basis : List (Identity (Fin 5)) :=
  a2Basis.map fun identity => identity.map toFinFive

private theorem a2Basis_roundTrip_checked :
    a2Basis.all (fun identity =>
      decide ((identity.map toFinFive).map Fin.val = identity)) = true := by
  decide

private theorem a2Basis_roundTrip
    (identity : Identity Nat) (member : identity ∈ a2Basis) :
    (identity.map toFinFive).map Fin.val = identity := by
  exact of_decide_eq_true <|
    (List.all_eq_true.mp a2Basis_roundTrip_checked) identity member

/-- Finite checks establish soundness of the A2 displayed laws only. -/
theorem modelsA2_of_finite_checks
    (candidate : FiniteTable)
    (checked : finiteA2Basis.all candidate.checkIdentityFused = true) :
    Models candidate.semigroup a2Basis := by
  intro identity member
  have finiteMember : identity.map toFinFive ∈ finiteA2Basis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    candidate.checkIdentityFusedNat_sound (identity.map toFinFive)
      ((List.all_eq_true.mp checked) _ finiteMember)
  rw [a2Basis_roundTrip identity member] at finiteValid
  exact finiteValid


def finiteB8Basis : List (Identity (Fin 5)) :=
  b8Basis.map fun identity => identity.map toFinFive

private theorem b8Basis_roundTrip_checked :
    b8Basis.all (fun identity =>
      decide ((identity.map toFinFive).map Fin.val = identity)) = true := by
  decide

private theorem b8Basis_roundTrip
    (identity : Identity Nat) (member : identity ∈ b8Basis) :
    (identity.map toFinFive).map Fin.val = identity := by
  exact of_decide_eq_true <|
    (List.all_eq_true.mp b8Basis_roundTrip_checked) identity member

/-- Finite checks establish soundness of the B8 displayed laws only. -/
theorem modelsB8_of_finite_checks
    (candidate : FiniteTable)
    (checked : finiteB8Basis.all candidate.checkIdentityFused = true) :
    Models candidate.semigroup b8Basis := by
  intro identity member
  have finiteMember : identity.map toFinFive ∈ finiteB8Basis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    candidate.checkIdentityFusedNat_sound (identity.map toFinFive)
      ((List.all_eq_true.mp checked) _ finiteMember)
  rw [b8Basis_roundTrip identity member] at finiteValid
  exact finiteValid


def finiteB7Basis : List (Identity (Fin 5)) :=
  b7Basis.map fun identity => identity.map toFinFive

private theorem b7Basis_roundTrip_checked :
    b7Basis.all (fun identity =>
      decide ((identity.map toFinFive).map Fin.val = identity)) = true := by
  decide

private theorem b7Basis_roundTrip
    (identity : Identity Nat) (member : identity ∈ b7Basis) :
    (identity.map toFinFive).map Fin.val = identity := by
  exact of_decide_eq_true <|
    (List.all_eq_true.mp b7Basis_roundTrip_checked) identity member

/-- Finite checks establish soundness of the B7 displayed laws only. -/
theorem modelsB7_of_finite_checks
    (candidate : FiniteTable)
    (checked : finiteB7Basis.all candidate.checkIdentityFused = true) :
    Models candidate.semigroup b7Basis := by
  intro identity member
  have finiteMember : identity.map toFinFive ∈ finiteB7Basis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    candidate.checkIdentityFusedNat_sound (identity.map toFinFive)
      ((List.all_eq_true.mp checked) _ finiteMember)
  rw [b7Basis_roundTrip identity member] at finiteValid
  exact finiteValid


def finiteA2Part01Basis : List (Identity (Fin 5)) :=
  a2Part01Basis.map fun identity => identity.map toFinFive

private theorem a2Part01Basis_roundTrip_checked :
    a2Part01Basis.all (fun identity =>
      decide ((identity.map toFinFive).map Fin.val = identity)) = true := by
  decide

private theorem a2Part01Basis_roundTrip
    (identity : Identity Nat) (member : identity ∈ a2Part01Basis) :
    (identity.map toFinFive).map Fin.val = identity := by
  exact of_decide_eq_true <|
    (List.all_eq_true.mp a2Part01Basis_roundTrip_checked) identity member

/-- Finite checks establish soundness of the A2 part 1 displayed laws only. -/
theorem modelsA2Part01_of_finite_checks
    (candidate : FiniteTable)
    (checked : finiteA2Part01Basis.all candidate.checkIdentityFused = true) :
    Models candidate.semigroup a2Part01Basis := by
  intro identity member
  have finiteMember : identity.map toFinFive ∈ finiteA2Part01Basis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    candidate.checkIdentityFusedNat_sound (identity.map toFinFive)
      ((List.all_eq_true.mp checked) _ finiteMember)
  rw [a2Part01Basis_roundTrip identity member] at finiteValid
  exact finiteValid

def finiteA2Part02Basis : List (Identity (Fin 5)) :=
  a2Part02Basis.map fun identity => identity.map toFinFive

private theorem a2Part02Basis_roundTrip_checked :
    a2Part02Basis.all (fun identity =>
      decide ((identity.map toFinFive).map Fin.val = identity)) = true := by
  decide

private theorem a2Part02Basis_roundTrip
    (identity : Identity Nat) (member : identity ∈ a2Part02Basis) :
    (identity.map toFinFive).map Fin.val = identity := by
  exact of_decide_eq_true <|
    (List.all_eq_true.mp a2Part02Basis_roundTrip_checked) identity member

/-- Finite checks establish soundness of the A2 part 2 displayed laws only. -/
theorem modelsA2Part02_of_finite_checks
    (candidate : FiniteTable)
    (checked : finiteA2Part02Basis.all candidate.checkIdentityFused = true) :
    Models candidate.semigroup a2Part02Basis := by
  intro identity member
  have finiteMember : identity.map toFinFive ∈ finiteA2Part02Basis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    candidate.checkIdentityFusedNat_sound (identity.map toFinFive)
      ((List.all_eq_true.mp checked) _ finiteMember)
  rw [a2Part02Basis_roundTrip identity member] at finiteValid
  exact finiteValid

def finiteB7Part01Basis : List (Identity (Fin 5)) :=
  b7Part01Basis.map fun identity => identity.map toFinFive

private theorem b7Part01Basis_roundTrip_checked :
    b7Part01Basis.all (fun identity =>
      decide ((identity.map toFinFive).map Fin.val = identity)) = true := by
  decide

private theorem b7Part01Basis_roundTrip
    (identity : Identity Nat) (member : identity ∈ b7Part01Basis) :
    (identity.map toFinFive).map Fin.val = identity := by
  exact of_decide_eq_true <|
    (List.all_eq_true.mp b7Part01Basis_roundTrip_checked) identity member

/-- Finite checks establish soundness of the B7 part 1 displayed laws only. -/
theorem modelsB7Part01_of_finite_checks
    (candidate : FiniteTable)
    (checked : finiteB7Part01Basis.all candidate.checkIdentityFused = true) :
    Models candidate.semigroup b7Part01Basis := by
  intro identity member
  have finiteMember : identity.map toFinFive ∈ finiteB7Part01Basis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    candidate.checkIdentityFusedNat_sound (identity.map toFinFive)
      ((List.all_eq_true.mp checked) _ finiteMember)
  rw [b7Part01Basis_roundTrip identity member] at finiteValid
  exact finiteValid

def finiteB7Part02Basis : List (Identity (Fin 5)) :=
  b7Part02Basis.map fun identity => identity.map toFinFive

private theorem b7Part02Basis_roundTrip_checked :
    b7Part02Basis.all (fun identity =>
      decide ((identity.map toFinFive).map Fin.val = identity)) = true := by
  decide

private theorem b7Part02Basis_roundTrip
    (identity : Identity Nat) (member : identity ∈ b7Part02Basis) :
    (identity.map toFinFive).map Fin.val = identity := by
  exact of_decide_eq_true <|
    (List.all_eq_true.mp b7Part02Basis_roundTrip_checked) identity member

/-- Finite checks establish soundness of the B7 part 2 displayed laws only. -/
theorem modelsB7Part02_of_finite_checks
    (candidate : FiniteTable)
    (checked : finiteB7Part02Basis.all candidate.checkIdentityFused = true) :
    Models candidate.semigroup b7Part02Basis := by
  intro identity member
  have finiteMember : identity.map toFinFive ∈ finiteB7Part02Basis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    candidate.checkIdentityFusedNat_sound (identity.map toFinFive)
      ((List.all_eq_true.mp checked) _ finiteMember)
  rw [b7Part02Basis_roundTrip identity member] at finiteValid
  exact finiteValid

def finiteB7Part03Basis : List (Identity (Fin 5)) :=
  b7Part03Basis.map fun identity => identity.map toFinFive

private theorem b7Part03Basis_roundTrip_checked :
    b7Part03Basis.all (fun identity =>
      decide ((identity.map toFinFive).map Fin.val = identity)) = true := by
  decide

private theorem b7Part03Basis_roundTrip
    (identity : Identity Nat) (member : identity ∈ b7Part03Basis) :
    (identity.map toFinFive).map Fin.val = identity := by
  exact of_decide_eq_true <|
    (List.all_eq_true.mp b7Part03Basis_roundTrip_checked) identity member

/-- Finite checks establish soundness of the B7 part 3 displayed laws only. -/
theorem modelsB7Part03_of_finite_checks
    (candidate : FiniteTable)
    (checked : finiteB7Part03Basis.all candidate.checkIdentityFused = true) :
    Models candidate.semigroup b7Part03Basis := by
  intro identity member
  have finiteMember : identity.map toFinFive ∈ finiteB7Part03Basis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    candidate.checkIdentityFusedNat_sound (identity.map toFinFive)
      ((List.all_eq_true.mp checked) _ finiteMember)
  rw [b7Part03Basis_roundTrip identity member] at finiteValid
  exact finiteValid

def finiteB7Part04Basis : List (Identity (Fin 5)) :=
  b7Part04Basis.map fun identity => identity.map toFinFive

private theorem b7Part04Basis_roundTrip_checked :
    b7Part04Basis.all (fun identity =>
      decide ((identity.map toFinFive).map Fin.val = identity)) = true := by
  decide

private theorem b7Part04Basis_roundTrip
    (identity : Identity Nat) (member : identity ∈ b7Part04Basis) :
    (identity.map toFinFive).map Fin.val = identity := by
  exact of_decide_eq_true <|
    (List.all_eq_true.mp b7Part04Basis_roundTrip_checked) identity member

/-- Finite checks establish soundness of the B7 part 4 displayed laws only. -/
theorem modelsB7Part04_of_finite_checks
    (candidate : FiniteTable)
    (checked : finiteB7Part04Basis.all candidate.checkIdentityFused = true) :
    Models candidate.semigroup b7Part04Basis := by
  intro identity member
  have finiteMember : identity.map toFinFive ∈ finiteB7Part04Basis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    candidate.checkIdentityFusedNat_sound (identity.map toFinFive)
      ((List.all_eq_true.mp checked) _ finiteMember)
  rw [b7Part04Basis_roundTrip identity member] at finiteValid
  exact finiteValid

def finiteB7Part05Basis : List (Identity (Fin 5)) :=
  b7Part05Basis.map fun identity => identity.map toFinFive

private theorem b7Part05Basis_roundTrip_checked :
    b7Part05Basis.all (fun identity =>
      decide ((identity.map toFinFive).map Fin.val = identity)) = true := by
  decide

private theorem b7Part05Basis_roundTrip
    (identity : Identity Nat) (member : identity ∈ b7Part05Basis) :
    (identity.map toFinFive).map Fin.val = identity := by
  exact of_decide_eq_true <|
    (List.all_eq_true.mp b7Part05Basis_roundTrip_checked) identity member

/-- Finite checks establish soundness of the B7 part 5 displayed laws only. -/
theorem modelsB7Part05_of_finite_checks
    (candidate : FiniteTable)
    (checked : finiteB7Part05Basis.all candidate.checkIdentityFused = true) :
    Models candidate.semigroup b7Part05Basis := by
  intro identity member
  have finiteMember : identity.map toFinFive ∈ finiteB7Part05Basis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    candidate.checkIdentityFusedNat_sound (identity.map toFinFive)
      ((List.all_eq_true.mp checked) _ finiteMember)
  rw [b7Part05Basis_roundTrip identity member] at finiteValid
  exact finiteValid

def finiteB7Part06Basis : List (Identity (Fin 5)) :=
  b7Part06Basis.map fun identity => identity.map toFinFive

private theorem b7Part06Basis_roundTrip_checked :
    b7Part06Basis.all (fun identity =>
      decide ((identity.map toFinFive).map Fin.val = identity)) = true := by
  decide

private theorem b7Part06Basis_roundTrip
    (identity : Identity Nat) (member : identity ∈ b7Part06Basis) :
    (identity.map toFinFive).map Fin.val = identity := by
  exact of_decide_eq_true <|
    (List.all_eq_true.mp b7Part06Basis_roundTrip_checked) identity member

/-- Finite checks establish soundness of the B7 part 6 displayed laws only. -/
theorem modelsB7Part06_of_finite_checks
    (candidate : FiniteTable)
    (checked : finiteB7Part06Basis.all candidate.checkIdentityFused = true) :
    Models candidate.semigroup b7Part06Basis := by
  intro identity member
  have finiteMember : identity.map toFinFive ∈ finiteB7Part06Basis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    candidate.checkIdentityFusedNat_sound (identity.map toFinFive)
      ((List.all_eq_true.mp checked) _ finiteMember)
  rw [b7Part06Basis_roundTrip identity member] at finiteValid
  exact finiteValid

def finiteB8Part01Basis : List (Identity (Fin 5)) :=
  b8Part01Basis.map fun identity => identity.map toFinFive

private theorem b8Part01Basis_roundTrip_checked :
    b8Part01Basis.all (fun identity =>
      decide ((identity.map toFinFive).map Fin.val = identity)) = true := by
  decide

private theorem b8Part01Basis_roundTrip
    (identity : Identity Nat) (member : identity ∈ b8Part01Basis) :
    (identity.map toFinFive).map Fin.val = identity := by
  exact of_decide_eq_true <|
    (List.all_eq_true.mp b8Part01Basis_roundTrip_checked) identity member

/-- Finite checks establish soundness of the B8 part 1 displayed laws only. -/
theorem modelsB8Part01_of_finite_checks
    (candidate : FiniteTable)
    (checked : finiteB8Part01Basis.all candidate.checkIdentityFused = true) :
    Models candidate.semigroup b8Part01Basis := by
  intro identity member
  have finiteMember : identity.map toFinFive ∈ finiteB8Part01Basis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    candidate.checkIdentityFusedNat_sound (identity.map toFinFive)
      ((List.all_eq_true.mp checked) _ finiteMember)
  rw [b8Part01Basis_roundTrip identity member] at finiteValid
  exact finiteValid

def finiteB8Part02Basis : List (Identity (Fin 5)) :=
  b8Part02Basis.map fun identity => identity.map toFinFive

private theorem b8Part02Basis_roundTrip_checked :
    b8Part02Basis.all (fun identity =>
      decide ((identity.map toFinFive).map Fin.val = identity)) = true := by
  decide

private theorem b8Part02Basis_roundTrip
    (identity : Identity Nat) (member : identity ∈ b8Part02Basis) :
    (identity.map toFinFive).map Fin.val = identity := by
  exact of_decide_eq_true <|
    (List.all_eq_true.mp b8Part02Basis_roundTrip_checked) identity member

/-- Finite checks establish soundness of the B8 part 2 displayed laws only. -/
theorem modelsB8Part02_of_finite_checks
    (candidate : FiniteTable)
    (checked : finiteB8Part02Basis.all candidate.checkIdentityFused = true) :
    Models candidate.semigroup b8Part02Basis := by
  intro identity member
  have finiteMember : identity.map toFinFive ∈ finiteB8Part02Basis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    candidate.checkIdentityFusedNat_sound (identity.map toFinFive)
      ((List.all_eq_true.mp checked) _ finiteMember)
  rw [b8Part02Basis_roundTrip identity member] at finiteValid
  exact finiteValid

def finiteB8Part03Basis : List (Identity (Fin 5)) :=
  b8Part03Basis.map fun identity => identity.map toFinFive

private theorem b8Part03Basis_roundTrip_checked :
    b8Part03Basis.all (fun identity =>
      decide ((identity.map toFinFive).map Fin.val = identity)) = true := by
  decide

private theorem b8Part03Basis_roundTrip
    (identity : Identity Nat) (member : identity ∈ b8Part03Basis) :
    (identity.map toFinFive).map Fin.val = identity := by
  exact of_decide_eq_true <|
    (List.all_eq_true.mp b8Part03Basis_roundTrip_checked) identity member

/-- Finite checks establish soundness of the B8 part 3 displayed laws only. -/
theorem modelsB8Part03_of_finite_checks
    (candidate : FiniteTable)
    (checked : finiteB8Part03Basis.all candidate.checkIdentityFused = true) :
    Models candidate.semigroup b8Part03Basis := by
  intro identity member
  have finiteMember : identity.map toFinFive ∈ finiteB8Part03Basis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    candidate.checkIdentityFusedNat_sound (identity.map toFinFive)
      ((List.all_eq_true.mp checked) _ finiteMember)
  rw [b8Part03Basis_roundTrip identity member] at finiteValid
  exact finiteValid

def finiteB8Part04Basis : List (Identity (Fin 5)) :=
  b8Part04Basis.map fun identity => identity.map toFinFive

private theorem b8Part04Basis_roundTrip_checked :
    b8Part04Basis.all (fun identity =>
      decide ((identity.map toFinFive).map Fin.val = identity)) = true := by
  decide

private theorem b8Part04Basis_roundTrip
    (identity : Identity Nat) (member : identity ∈ b8Part04Basis) :
    (identity.map toFinFive).map Fin.val = identity := by
  exact of_decide_eq_true <|
    (List.all_eq_true.mp b8Part04Basis_roundTrip_checked) identity member

/-- Finite checks establish soundness of the B8 part 4 displayed laws only. -/
theorem modelsB8Part04_of_finite_checks
    (candidate : FiniteTable)
    (checked : finiteB8Part04Basis.all candidate.checkIdentityFused = true) :
    Models candidate.semigroup b8Part04Basis := by
  intro identity member
  have finiteMember : identity.map toFinFive ∈ finiteB8Part04Basis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    candidate.checkIdentityFusedNat_sound (identity.map toFinFive)
      ((List.all_eq_true.mp checked) _ finiteMember)
  rw [b8Part04Basis_roundTrip identity member] at finiteValid
  exact finiteValid

def finiteB8Part05Basis : List (Identity (Fin 5)) :=
  b8Part05Basis.map fun identity => identity.map toFinFive

private theorem b8Part05Basis_roundTrip_checked :
    b8Part05Basis.all (fun identity =>
      decide ((identity.map toFinFive).map Fin.val = identity)) = true := by
  decide

private theorem b8Part05Basis_roundTrip
    (identity : Identity Nat) (member : identity ∈ b8Part05Basis) :
    (identity.map toFinFive).map Fin.val = identity := by
  exact of_decide_eq_true <|
    (List.all_eq_true.mp b8Part05Basis_roundTrip_checked) identity member

/-- Finite checks establish soundness of the B8 part 5 displayed laws only. -/
theorem modelsB8Part05_of_finite_checks
    (candidate : FiniteTable)
    (checked : finiteB8Part05Basis.all candidate.checkIdentityFused = true) :
    Models candidate.semigroup b8Part05Basis := by
  intro identity member
  have finiteMember : identity.map toFinFive ∈ finiteB8Part05Basis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    candidate.checkIdentityFusedNat_sound (identity.map toFinFive)
      ((List.all_eq_true.mp checked) _ finiteMember)
  rw [b8Part05Basis_roundTrip identity member] at finiteValid
  exact finiteValid


theorem modelsAppend
    {candidate : Semigroup α} {first second : List (Identity Nat)}
    (firstModels : Models candidate first)
    (secondModels : Models candidate second) :
    Models candidate (first ++ second) := by
  intro identity member
  rcases List.mem_append.mp member with member | member
  · exact firstModels identity member
  · exact secondModels identity member

def WordDisjoint (left right : Word Nat) : Prop :=
  ∀ letter, letter ∈ left.toList → letter ∉ right.toList

def Disconnected (word : Word Nat) : Prop :=
  ∃ left right : Word Nat,
    word = left ++ right ∧ WordDisjoint left right

/-- The non-singleton connected words used in Lemma 2.6 and Lemma 12.7. -/
def Connected (word : Word Nat) : Prop :=
  2 ≤ word.toList.length ∧ ¬Disconnected word

def appendFactors (first : Word Nat) (rest : List (Word Nat)) : Word Nat :=
  rest.foldl (fun current next => current ++ next) first

/-- Products of pairwise disjoint connected factors from Lemma 2.6(ii). -/
def PairwiseDisjointConnectedProduct (word : Word Nat) : Prop :=
  ∃ first rest,
    (∀ factor, factor ∈ first :: rest → Connected factor) ∧
    (first :: rest).Pairwise WordDisjoint ∧
    word = appendFactors first rest

/-- Finite support for the connected/disjoint-connected basis reduction.

Lee--Volkov gives a possibly infinite restricted basis.  Every equational
derivation uses only finitely many of its identities, which is the operational
form needed by `Derives` and by the Section 12 completeness argument. -/
structure RestrictedBasisReduction
    (candidate : FiniteTable) (domain : Word Nat → Prop) where
  reduce :
    ∀ identity : Identity Nat,
      identity.SatisfiedBy candidate.semigroup →
      ∃ source : List (Identity Nat),
        Models candidate.semigroup source ∧
        (∀ sourceIdentity, sourceIdentity ∈ source →
          domain sourceIdentity.lhs ∧ domain sourceIdentity.rhs) ∧
        Derives source identity.lhs identity.rhs

/-- Normalization and uniqueness on the restricted paper domain. -/
structure RestrictedCanonicalProof
    (candidate : FiniteTable) (targetBasis : List (Identity Nat))
    (domain : Word Nat → Prop) where
  canonical : Word Nat → Prop
  normalize :
    ∀ word, domain word →
      ∃ target, canonical target ∧ Derives targetBasis word target
  uniqueOfValid :
    ∀ left right,
      canonical left → canonical right →
      (Identity.mk left right).SatisfiedBy candidate.semigroup → left = right

/-- The unrestricted A2 normalization and canonical-uniqueness package. -/
structure UnrestrictedCanonicalProof
    (candidate : FiniteTable) (targetBasis : List (Identity Nat)) where
  canonical : Word Nat → Prop
  normalize :
    ∀ word, ∃ target, canonical target ∧ Derives targetBasis word target
  uniqueOfValid :
    ∀ left right,
      canonical left → canonical right →
      (Identity.mk left right).SatisfiedBy candidate.semigroup → left = right

private theorem normalizedIdentityValid
    (candidate : FiniteTable) (targetBasis : List (Identity Nat))
    (models : Models candidate.semigroup targetBasis)
    (identity : Identity Nat) (valid : identity.SatisfiedBy candidate.semigroup)
    (leftTarget rightTarget : Word Nat)
    (leftDerives : Derives targetBasis identity.lhs leftTarget)
    (rightDerives : Derives targetBasis identity.rhs rightTarget) :
    (Identity.mk leftTarget rightTarget).SatisfiedBy candidate.semigroup := by
  intro valuation
  exact (leftDerives.sound models valuation).symm.trans <|
    (valid valuation).trans (rightDerives.sound models valuation)

theorem basisFor_of_unrestrictedCanonical
    (candidate : FiniteTable) (targetBasis : List (Identity Nat))
    (models : Models candidate.semigroup targetBasis)
    (proof : UnrestrictedCanonicalProof candidate targetBasis) :
    BasisFor candidate.semigroup targetBasis := by
  refine ⟨models, ?_⟩
  intro identity valid
  rcases proof.normalize identity.lhs with
    ⟨leftTarget, leftCanonical, leftDerives⟩
  rcases proof.normalize identity.rhs with
    ⟨rightTarget, rightCanonical, rightDerives⟩
  have targetValid := normalizedIdentityValid candidate targetBasis models
    identity valid leftTarget rightTarget leftDerives rightDerives
  have same := proof.uniqueOfValid leftTarget rightTarget
    leftCanonical rightCanonical targetValid
  subst rightTarget
  exact Derives.trans leftDerives (Derives.symm rightDerives)

theorem basisFor_of_restrictedCanonical
    (candidate : FiniteTable) (targetBasis : List (Identity Nat))
    (domain : Word Nat → Prop)
    (models : Models candidate.semigroup targetBasis)
    (reduction : RestrictedBasisReduction candidate domain)
    (proof : RestrictedCanonicalProof candidate targetBasis domain) :
    BasisFor candidate.semigroup targetBasis := by
  refine ⟨models, ?_⟩
  intro identity valid
  rcases reduction.reduce identity valid with
    ⟨source, sourceModels, sourceDomain, sourceDerives⟩
  apply sourceDerives.transport
  intro sourceIdentity member
  have sourceValid := sourceModels sourceIdentity member
  have domainProof := sourceDomain sourceIdentity member
  rcases proof.normalize sourceIdentity.lhs domainProof.1 with
    ⟨leftTarget, leftCanonical, leftDerives⟩
  rcases proof.normalize sourceIdentity.rhs domainProof.2 with
    ⟨rightTarget, rightCanonical, rightDerives⟩
  have targetValid := normalizedIdentityValid candidate targetBasis models
    sourceIdentity sourceValid leftTarget rightTarget leftDerives rightDerives
  have same := proof.uniqueOfValid leftTarget rightTarget
    leftCanonical rightCanonical targetValid
  subst rightTarget
  exact Derives.trans leftDerives (Derives.symm rightDerives)

namespace S6_5597

/-- Exact one-based catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,2,1,3],[1,1,1,2,1,3],[5,5,5,5,5,5],[1,2,3,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "4133bda50a7c9c58333f325303623b5f92c817fc30cd7960424bf4775066e276"

end S6_5597

namespace S6_5625

/-- Exact one-based catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,2],[1,1,1,1,1,3],[1,1,1,2,1,4],[1,1,3,1,5,1],[1,2,1,4,1,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (0 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "0c94c89e62dea4ae97d2cab236d687134c43ebd87938f3419d677a6352a3d711"

end S6_5625

namespace S6_5626

/-- Exact one-based catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,2],[1,1,1,1,1,3],[1,1,1,2,1,4],[1,1,3,1,5,3],[1,2,1,4,1,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (2 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "9cfcf60509b00948af18dac7bbaf1ec50e22a939448170fdd02d01bcfc07370e"

end S6_5626


end SemigroupBasis.CoRoots.Order6SporadicSection12
