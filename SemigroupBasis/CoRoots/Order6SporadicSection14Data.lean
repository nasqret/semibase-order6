import SemigroupBasis.FiniteReflection
import SemigroupBasis.Generated.S2_4
import SemigroupBasis.Generated.S3_6
import SemigroupBasis.Generated.S3_16
import SemigroupBasis.Opposite

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6SporadicSection14

open SemigroupBasis

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def word_14_1a_left : Word Nat := w 0 [0, 1]
def word_14_1a_right : Word Nat := w 0 [1]
def law_14_1a : Identity Nat := ⟨word_14_1a_left, word_14_1a_right⟩
def word_14_1b_left : Word Nat := w 0 [1, 0, 0]
def word_14_1b_right : Word Nat := w 0 [1, 0]
def law_14_1b : Identity Nat := ⟨word_14_1b_left, word_14_1b_right⟩
def word_14_1c_empty_left : Word Nat := w 0 [1, 0, 1]
def word_14_1c_empty_right : Word Nat := w 0 [1, 1]
def law_14_1c_empty : Identity Nat := ⟨word_14_1c_empty_left, word_14_1c_empty_right⟩
def word_14_1c_H_left : Word Nat := w 0 [3, 1, 0, 1]
def word_14_1c_H_right : Word Nat := w 0 [3, 1, 1]
def law_14_1c_H : Identity Nat := ⟨word_14_1c_H_left, word_14_1c_H_right⟩
def word_14_1c_K_left : Word Nat := w 0 [1, 4, 0, 1]
def word_14_1c_K_right : Word Nat := w 0 [1, 4, 1]
def law_14_1c_K : Identity Nat := ⟨word_14_1c_K_left, word_14_1c_K_right⟩
def word_14_1c_HK_left : Word Nat := w 0 [3, 1, 4, 0, 1]
def word_14_1c_HK_right : Word Nat := w 0 [3, 1, 4, 1]
def law_14_1c_HK : Identity Nat := ⟨word_14_1c_HK_left, word_14_1c_HK_right⟩
def word_14_1d_empty_left : Word Nat := w 0 [1, 1, 0]
def word_14_1d_empty_right : Word Nat := w 0 [1, 0]
def law_14_1d_empty : Identity Nat := ⟨word_14_1d_empty_left, word_14_1d_empty_right⟩
def word_14_1d_H_left : Word Nat := w 0 [3, 1, 1, 0]
def word_14_1d_H_right : Word Nat := w 0 [3, 1, 0]
def law_14_1d_H : Identity Nat := ⟨word_14_1d_H_left, word_14_1d_H_right⟩
def word_14_1d_K_left : Word Nat := w 0 [1, 4, 1, 0]
def word_14_1d_K_right : Word Nat := w 0 [1, 4, 0]
def law_14_1d_K : Identity Nat := ⟨word_14_1d_K_left, word_14_1d_K_right⟩
def word_14_1d_HK_left : Word Nat := w 0 [3, 1, 4, 1, 0]
def word_14_1d_HK_right : Word Nat := w 0 [3, 1, 4, 0]
def law_14_1d_HK : Identity Nat := ⟨word_14_1d_HK_left, word_14_1d_HK_right⟩
def alphaBasis : List (Identity Nat) :=
  [law_14_1a, law_14_1b, law_14_1c_empty, law_14_1c_H, law_14_1c_K, law_14_1c_HK, law_14_1d_empty, law_14_1d_H, law_14_1d_K, law_14_1d_HK]
def oppositeAlphaBasis : List (Identity Nat) :=
  reversedBasis alphaBasis

def word_14_3a_left : Word Nat := w 0 [0, 1]
def word_14_3a_right : Word Nat := w 0 [1]
def law_14_3a : Identity Nat := ⟨word_14_3a_left, word_14_3a_right⟩
def word_14_3b_left : Word Nat := w 0 [1, 1]
def word_14_3b_right : Word Nat := w 0 [1]
def law_14_3b : Identity Nat := ⟨word_14_3b_left, word_14_3b_right⟩
def word_14_3c_empty_left : Word Nat := w 0 [1, 0, 1]
def word_14_3c_empty_right : Word Nat := w 0 [1, 1]
def law_14_3c_empty : Identity Nat := ⟨word_14_3c_empty_left, word_14_3c_empty_right⟩
def word_14_3c_H_left : Word Nat := w 0 [3, 1, 0, 1]
def word_14_3c_H_right : Word Nat := w 0 [3, 1, 1]
def law_14_3c_H : Identity Nat := ⟨word_14_3c_H_left, word_14_3c_H_right⟩
def word_14_3c_K_left : Word Nat := w 0 [1, 4, 0, 1]
def word_14_3c_K_right : Word Nat := w 0 [1, 4, 1]
def law_14_3c_K : Identity Nat := ⟨word_14_3c_K_left, word_14_3c_K_right⟩
def word_14_3c_HK_left : Word Nat := w 0 [3, 1, 4, 0, 1]
def word_14_3c_HK_right : Word Nat := w 0 [3, 1, 4, 1]
def law_14_3c_HK : Identity Nat := ⟨word_14_3c_HK_left, word_14_3c_HK_right⟩
def word_14_3d_empty_left : Word Nat := w 0 [1, 1, 0]
def word_14_3d_empty_right : Word Nat := w 0 [1, 0]
def law_14_3d_empty : Identity Nat := ⟨word_14_3d_empty_left, word_14_3d_empty_right⟩
def word_14_3d_H_left : Word Nat := w 0 [3, 1, 1, 0]
def word_14_3d_H_right : Word Nat := w 0 [3, 1, 0]
def law_14_3d_H : Identity Nat := ⟨word_14_3d_H_left, word_14_3d_H_right⟩
def word_14_3d_K_left : Word Nat := w 0 [1, 4, 1, 0]
def word_14_3d_K_right : Word Nat := w 0 [1, 4, 0]
def law_14_3d_K : Identity Nat := ⟨word_14_3d_K_left, word_14_3d_K_right⟩
def word_14_3d_HK_left : Word Nat := w 0 [3, 1, 4, 1, 0]
def word_14_3d_HK_right : Word Nat := w 0 [3, 1, 4, 0]
def law_14_3d_HK : Identity Nat := ⟨word_14_3d_HK_left, word_14_3d_HK_right⟩
def betaBasis : List (Identity Nat) :=
  [law_14_3a, law_14_3b, law_14_3c_empty, law_14_3c_H, law_14_3c_K, law_14_3c_HK, law_14_3d_empty, law_14_3d_H, law_14_3d_K, law_14_3d_HK]
def oppositeBetaBasis : List (Identity Nat) :=
  reversedBasis betaBasis

def alphaPart01Basis : List (Identity Nat) :=
  [law_14_1a, law_14_1b, law_14_1c_empty]

def alphaPart02Basis : List (Identity Nat) :=
  [law_14_1c_H, law_14_1c_K, law_14_1c_HK]

def alphaPart03Basis : List (Identity Nat) :=
  [law_14_1d_empty, law_14_1d_H, law_14_1d_K]

def alphaPart04Basis : List (Identity Nat) :=
  [law_14_1d_HK]

theorem alphaBasis_eq_parts :
    alphaBasis =
    alphaPart01Basis ++
    alphaPart02Basis ++
    alphaPart03Basis ++
    alphaPart04Basis := by
  rfl

def oppositeAlphaPart01Basis : List (Identity Nat) :=
  reversedBasis alphaPart01Basis

def oppositeAlphaPart02Basis : List (Identity Nat) :=
  reversedBasis alphaPart02Basis

def oppositeAlphaPart03Basis : List (Identity Nat) :=
  reversedBasis alphaPart03Basis

def oppositeAlphaPart04Basis : List (Identity Nat) :=
  reversedBasis alphaPart04Basis

theorem oppositeAlphaBasis_eq_parts :
    oppositeAlphaBasis =
    oppositeAlphaPart01Basis ++
    oppositeAlphaPart02Basis ++
    oppositeAlphaPart03Basis ++
    oppositeAlphaPart04Basis := by
  rfl

def betaPart01Basis : List (Identity Nat) :=
  [law_14_3a, law_14_3b, law_14_3c_empty]

def betaPart02Basis : List (Identity Nat) :=
  [law_14_3c_H, law_14_3c_K, law_14_3c_HK]

def betaPart03Basis : List (Identity Nat) :=
  [law_14_3d_empty, law_14_3d_H, law_14_3d_K]

def betaPart04Basis : List (Identity Nat) :=
  [law_14_3d_HK]

theorem betaBasis_eq_parts :
    betaBasis =
    betaPart01Basis ++
    betaPart02Basis ++
    betaPart03Basis ++
    betaPart04Basis := by
  rfl

def oppositeBetaPart01Basis : List (Identity Nat) :=
  reversedBasis betaPart01Basis

def oppositeBetaPart02Basis : List (Identity Nat) :=
  reversedBasis betaPart02Basis

def oppositeBetaPart03Basis : List (Identity Nat) :=
  reversedBasis betaPart03Basis

def oppositeBetaPart04Basis : List (Identity Nat) :=
  reversedBasis betaPart04Basis

theorem oppositeBetaBasis_eq_parts :
    oppositeBetaBasis =
    oppositeBetaPart01Basis ++
    oppositeBetaPart02Basis ++
    oppositeBetaPart03Basis ++
    oppositeBetaPart04Basis := by
  rfl

private def toFinFive : Nat → Fin 5
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | _ => 4

def finiteAlphaBasis : List (Identity (Fin 5)) :=
  alphaBasis.map fun identity => identity.map toFinFive

private theorem alphaBasis_roundTrip_checked :
    alphaBasis.all (fun identity =>
      decide ((identity.map toFinFive).map Fin.val = identity)) = true := by
  decide

private theorem alphaBasis_roundTrip
    (identity : Identity Nat) (member : identity ∈ alphaBasis) :
    (identity.map toFinFive).map Fin.val = identity := by
  exact of_decide_eq_true <|
    (List.all_eq_true.mp alphaBasis_roundTrip_checked) identity member

theorem modelsAlpha_of_finite_checks
    (candidate : FiniteTable)
    (checked : finiteAlphaBasis.all candidate.checkIdentityFused = true) :
    Models candidate.semigroup alphaBasis := by
  intro identity member
  have finiteMember : identity.map toFinFive ∈ finiteAlphaBasis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    candidate.checkIdentityFusedNat_sound (identity.map toFinFive)
      ((List.all_eq_true.mp checked) _ finiteMember)
  rw [alphaBasis_roundTrip identity member] at finiteValid
  exact finiteValid

def finiteOppositeAlphaBasis : List (Identity (Fin 5)) :=
  oppositeAlphaBasis.map fun identity => identity.map toFinFive

private theorem oppositeAlphaBasis_roundTrip_checked :
    oppositeAlphaBasis.all (fun identity =>
      decide ((identity.map toFinFive).map Fin.val = identity)) = true := by
  decide

private theorem oppositeAlphaBasis_roundTrip
    (identity : Identity Nat) (member : identity ∈ oppositeAlphaBasis) :
    (identity.map toFinFive).map Fin.val = identity := by
  exact of_decide_eq_true <|
    (List.all_eq_true.mp oppositeAlphaBasis_roundTrip_checked) identity member

theorem modelsOppositeAlpha_of_finite_checks
    (candidate : FiniteTable)
    (checked : finiteOppositeAlphaBasis.all candidate.checkIdentityFused = true) :
    Models candidate.semigroup oppositeAlphaBasis := by
  intro identity member
  have finiteMember : identity.map toFinFive ∈ finiteOppositeAlphaBasis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    candidate.checkIdentityFusedNat_sound (identity.map toFinFive)
      ((List.all_eq_true.mp checked) _ finiteMember)
  rw [oppositeAlphaBasis_roundTrip identity member] at finiteValid
  exact finiteValid

def finiteBetaBasis : List (Identity (Fin 5)) :=
  betaBasis.map fun identity => identity.map toFinFive

private theorem betaBasis_roundTrip_checked :
    betaBasis.all (fun identity =>
      decide ((identity.map toFinFive).map Fin.val = identity)) = true := by
  decide

private theorem betaBasis_roundTrip
    (identity : Identity Nat) (member : identity ∈ betaBasis) :
    (identity.map toFinFive).map Fin.val = identity := by
  exact of_decide_eq_true <|
    (List.all_eq_true.mp betaBasis_roundTrip_checked) identity member

theorem modelsBeta_of_finite_checks
    (candidate : FiniteTable)
    (checked : finiteBetaBasis.all candidate.checkIdentityFused = true) :
    Models candidate.semigroup betaBasis := by
  intro identity member
  have finiteMember : identity.map toFinFive ∈ finiteBetaBasis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    candidate.checkIdentityFusedNat_sound (identity.map toFinFive)
      ((List.all_eq_true.mp checked) _ finiteMember)
  rw [betaBasis_roundTrip identity member] at finiteValid
  exact finiteValid

def finiteOppositeBetaBasis : List (Identity (Fin 5)) :=
  oppositeBetaBasis.map fun identity => identity.map toFinFive

private theorem oppositeBetaBasis_roundTrip_checked :
    oppositeBetaBasis.all (fun identity =>
      decide ((identity.map toFinFive).map Fin.val = identity)) = true := by
  decide

private theorem oppositeBetaBasis_roundTrip
    (identity : Identity Nat) (member : identity ∈ oppositeBetaBasis) :
    (identity.map toFinFive).map Fin.val = identity := by
  exact of_decide_eq_true <|
    (List.all_eq_true.mp oppositeBetaBasis_roundTrip_checked) identity member

theorem modelsOppositeBeta_of_finite_checks
    (candidate : FiniteTable)
    (checked : finiteOppositeBetaBasis.all candidate.checkIdentityFused = true) :
    Models candidate.semigroup oppositeBetaBasis := by
  intro identity member
  have finiteMember : identity.map toFinFive ∈ finiteOppositeBetaBasis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    candidate.checkIdentityFusedNat_sound (identity.map toFinFive)
      ((List.all_eq_true.mp checked) _ finiteMember)
  rw [oppositeBetaBasis_roundTrip identity member] at finiteValid
  exact finiteValid

def finiteAlphaPart01Basis : List (Identity (Fin 5)) :=
  alphaPart01Basis.map fun identity => identity.map toFinFive

private theorem alphaPart01Basis_roundTrip_checked :
    alphaPart01Basis.all (fun identity =>
      decide ((identity.map toFinFive).map Fin.val = identity)) = true := by
  decide

private theorem alphaPart01Basis_roundTrip
    (identity : Identity Nat) (member : identity ∈ alphaPart01Basis) :
    (identity.map toFinFive).map Fin.val = identity := by
  exact of_decide_eq_true <|
    (List.all_eq_true.mp alphaPart01Basis_roundTrip_checked) identity member

theorem modelsAlphaPart01_of_finite_checks
    (candidate : FiniteTable)
    (checked : finiteAlphaPart01Basis.all candidate.checkIdentityFused = true) :
    Models candidate.semigroup alphaPart01Basis := by
  intro identity member
  have finiteMember : identity.map toFinFive ∈ finiteAlphaPart01Basis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    candidate.checkIdentityFusedNat_sound (identity.map toFinFive)
      ((List.all_eq_true.mp checked) _ finiteMember)
  rw [alphaPart01Basis_roundTrip identity member] at finiteValid
  exact finiteValid

def finiteAlphaPart02Basis : List (Identity (Fin 5)) :=
  alphaPart02Basis.map fun identity => identity.map toFinFive

private theorem alphaPart02Basis_roundTrip_checked :
    alphaPart02Basis.all (fun identity =>
      decide ((identity.map toFinFive).map Fin.val = identity)) = true := by
  decide

private theorem alphaPart02Basis_roundTrip
    (identity : Identity Nat) (member : identity ∈ alphaPart02Basis) :
    (identity.map toFinFive).map Fin.val = identity := by
  exact of_decide_eq_true <|
    (List.all_eq_true.mp alphaPart02Basis_roundTrip_checked) identity member

theorem modelsAlphaPart02_of_finite_checks
    (candidate : FiniteTable)
    (checked : finiteAlphaPart02Basis.all candidate.checkIdentityFused = true) :
    Models candidate.semigroup alphaPart02Basis := by
  intro identity member
  have finiteMember : identity.map toFinFive ∈ finiteAlphaPart02Basis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    candidate.checkIdentityFusedNat_sound (identity.map toFinFive)
      ((List.all_eq_true.mp checked) _ finiteMember)
  rw [alphaPart02Basis_roundTrip identity member] at finiteValid
  exact finiteValid

def finiteAlphaPart03Basis : List (Identity (Fin 5)) :=
  alphaPart03Basis.map fun identity => identity.map toFinFive

private theorem alphaPart03Basis_roundTrip_checked :
    alphaPart03Basis.all (fun identity =>
      decide ((identity.map toFinFive).map Fin.val = identity)) = true := by
  decide

private theorem alphaPart03Basis_roundTrip
    (identity : Identity Nat) (member : identity ∈ alphaPart03Basis) :
    (identity.map toFinFive).map Fin.val = identity := by
  exact of_decide_eq_true <|
    (List.all_eq_true.mp alphaPart03Basis_roundTrip_checked) identity member

theorem modelsAlphaPart03_of_finite_checks
    (candidate : FiniteTable)
    (checked : finiteAlphaPart03Basis.all candidate.checkIdentityFused = true) :
    Models candidate.semigroup alphaPart03Basis := by
  intro identity member
  have finiteMember : identity.map toFinFive ∈ finiteAlphaPart03Basis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    candidate.checkIdentityFusedNat_sound (identity.map toFinFive)
      ((List.all_eq_true.mp checked) _ finiteMember)
  rw [alphaPart03Basis_roundTrip identity member] at finiteValid
  exact finiteValid

def finiteAlphaPart04Basis : List (Identity (Fin 5)) :=
  alphaPart04Basis.map fun identity => identity.map toFinFive

private theorem alphaPart04Basis_roundTrip_checked :
    alphaPart04Basis.all (fun identity =>
      decide ((identity.map toFinFive).map Fin.val = identity)) = true := by
  decide

private theorem alphaPart04Basis_roundTrip
    (identity : Identity Nat) (member : identity ∈ alphaPart04Basis) :
    (identity.map toFinFive).map Fin.val = identity := by
  exact of_decide_eq_true <|
    (List.all_eq_true.mp alphaPart04Basis_roundTrip_checked) identity member

theorem modelsAlphaPart04_of_finite_checks
    (candidate : FiniteTable)
    (checked : finiteAlphaPart04Basis.all candidate.checkIdentityFused = true) :
    Models candidate.semigroup alphaPart04Basis := by
  intro identity member
  have finiteMember : identity.map toFinFive ∈ finiteAlphaPart04Basis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    candidate.checkIdentityFusedNat_sound (identity.map toFinFive)
      ((List.all_eq_true.mp checked) _ finiteMember)
  rw [alphaPart04Basis_roundTrip identity member] at finiteValid
  exact finiteValid

def finiteOppositeAlphaPart01Basis : List (Identity (Fin 5)) :=
  oppositeAlphaPart01Basis.map fun identity => identity.map toFinFive

private theorem oppositeAlphaPart01Basis_roundTrip_checked :
    oppositeAlphaPart01Basis.all (fun identity =>
      decide ((identity.map toFinFive).map Fin.val = identity)) = true := by
  decide

private theorem oppositeAlphaPart01Basis_roundTrip
    (identity : Identity Nat) (member : identity ∈ oppositeAlphaPart01Basis) :
    (identity.map toFinFive).map Fin.val = identity := by
  exact of_decide_eq_true <|
    (List.all_eq_true.mp oppositeAlphaPart01Basis_roundTrip_checked) identity member

theorem modelsOppositeAlphaPart01_of_finite_checks
    (candidate : FiniteTable)
    (checked : finiteOppositeAlphaPart01Basis.all candidate.checkIdentityFused = true) :
    Models candidate.semigroup oppositeAlphaPart01Basis := by
  intro identity member
  have finiteMember : identity.map toFinFive ∈ finiteOppositeAlphaPart01Basis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    candidate.checkIdentityFusedNat_sound (identity.map toFinFive)
      ((List.all_eq_true.mp checked) _ finiteMember)
  rw [oppositeAlphaPart01Basis_roundTrip identity member] at finiteValid
  exact finiteValid

def finiteOppositeAlphaPart02Basis : List (Identity (Fin 5)) :=
  oppositeAlphaPart02Basis.map fun identity => identity.map toFinFive

private theorem oppositeAlphaPart02Basis_roundTrip_checked :
    oppositeAlphaPart02Basis.all (fun identity =>
      decide ((identity.map toFinFive).map Fin.val = identity)) = true := by
  decide

private theorem oppositeAlphaPart02Basis_roundTrip
    (identity : Identity Nat) (member : identity ∈ oppositeAlphaPart02Basis) :
    (identity.map toFinFive).map Fin.val = identity := by
  exact of_decide_eq_true <|
    (List.all_eq_true.mp oppositeAlphaPart02Basis_roundTrip_checked) identity member

theorem modelsOppositeAlphaPart02_of_finite_checks
    (candidate : FiniteTable)
    (checked : finiteOppositeAlphaPart02Basis.all candidate.checkIdentityFused = true) :
    Models candidate.semigroup oppositeAlphaPart02Basis := by
  intro identity member
  have finiteMember : identity.map toFinFive ∈ finiteOppositeAlphaPart02Basis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    candidate.checkIdentityFusedNat_sound (identity.map toFinFive)
      ((List.all_eq_true.mp checked) _ finiteMember)
  rw [oppositeAlphaPart02Basis_roundTrip identity member] at finiteValid
  exact finiteValid

def finiteOppositeAlphaPart03Basis : List (Identity (Fin 5)) :=
  oppositeAlphaPart03Basis.map fun identity => identity.map toFinFive

private theorem oppositeAlphaPart03Basis_roundTrip_checked :
    oppositeAlphaPart03Basis.all (fun identity =>
      decide ((identity.map toFinFive).map Fin.val = identity)) = true := by
  decide

private theorem oppositeAlphaPart03Basis_roundTrip
    (identity : Identity Nat) (member : identity ∈ oppositeAlphaPart03Basis) :
    (identity.map toFinFive).map Fin.val = identity := by
  exact of_decide_eq_true <|
    (List.all_eq_true.mp oppositeAlphaPart03Basis_roundTrip_checked) identity member

theorem modelsOppositeAlphaPart03_of_finite_checks
    (candidate : FiniteTable)
    (checked : finiteOppositeAlphaPart03Basis.all candidate.checkIdentityFused = true) :
    Models candidate.semigroup oppositeAlphaPart03Basis := by
  intro identity member
  have finiteMember : identity.map toFinFive ∈ finiteOppositeAlphaPart03Basis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    candidate.checkIdentityFusedNat_sound (identity.map toFinFive)
      ((List.all_eq_true.mp checked) _ finiteMember)
  rw [oppositeAlphaPart03Basis_roundTrip identity member] at finiteValid
  exact finiteValid

def finiteOppositeAlphaPart04Basis : List (Identity (Fin 5)) :=
  oppositeAlphaPart04Basis.map fun identity => identity.map toFinFive

private theorem oppositeAlphaPart04Basis_roundTrip_checked :
    oppositeAlphaPart04Basis.all (fun identity =>
      decide ((identity.map toFinFive).map Fin.val = identity)) = true := by
  decide

private theorem oppositeAlphaPart04Basis_roundTrip
    (identity : Identity Nat) (member : identity ∈ oppositeAlphaPart04Basis) :
    (identity.map toFinFive).map Fin.val = identity := by
  exact of_decide_eq_true <|
    (List.all_eq_true.mp oppositeAlphaPart04Basis_roundTrip_checked) identity member

theorem modelsOppositeAlphaPart04_of_finite_checks
    (candidate : FiniteTable)
    (checked : finiteOppositeAlphaPart04Basis.all candidate.checkIdentityFused = true) :
    Models candidate.semigroup oppositeAlphaPart04Basis := by
  intro identity member
  have finiteMember : identity.map toFinFive ∈ finiteOppositeAlphaPart04Basis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    candidate.checkIdentityFusedNat_sound (identity.map toFinFive)
      ((List.all_eq_true.mp checked) _ finiteMember)
  rw [oppositeAlphaPart04Basis_roundTrip identity member] at finiteValid
  exact finiteValid

def finiteBetaPart01Basis : List (Identity (Fin 5)) :=
  betaPart01Basis.map fun identity => identity.map toFinFive

private theorem betaPart01Basis_roundTrip_checked :
    betaPart01Basis.all (fun identity =>
      decide ((identity.map toFinFive).map Fin.val = identity)) = true := by
  decide

private theorem betaPart01Basis_roundTrip
    (identity : Identity Nat) (member : identity ∈ betaPart01Basis) :
    (identity.map toFinFive).map Fin.val = identity := by
  exact of_decide_eq_true <|
    (List.all_eq_true.mp betaPart01Basis_roundTrip_checked) identity member

theorem modelsBetaPart01_of_finite_checks
    (candidate : FiniteTable)
    (checked : finiteBetaPart01Basis.all candidate.checkIdentityFused = true) :
    Models candidate.semigroup betaPart01Basis := by
  intro identity member
  have finiteMember : identity.map toFinFive ∈ finiteBetaPart01Basis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    candidate.checkIdentityFusedNat_sound (identity.map toFinFive)
      ((List.all_eq_true.mp checked) _ finiteMember)
  rw [betaPart01Basis_roundTrip identity member] at finiteValid
  exact finiteValid

def finiteBetaPart02Basis : List (Identity (Fin 5)) :=
  betaPart02Basis.map fun identity => identity.map toFinFive

private theorem betaPart02Basis_roundTrip_checked :
    betaPart02Basis.all (fun identity =>
      decide ((identity.map toFinFive).map Fin.val = identity)) = true := by
  decide

private theorem betaPart02Basis_roundTrip
    (identity : Identity Nat) (member : identity ∈ betaPart02Basis) :
    (identity.map toFinFive).map Fin.val = identity := by
  exact of_decide_eq_true <|
    (List.all_eq_true.mp betaPart02Basis_roundTrip_checked) identity member

theorem modelsBetaPart02_of_finite_checks
    (candidate : FiniteTable)
    (checked : finiteBetaPart02Basis.all candidate.checkIdentityFused = true) :
    Models candidate.semigroup betaPart02Basis := by
  intro identity member
  have finiteMember : identity.map toFinFive ∈ finiteBetaPart02Basis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    candidate.checkIdentityFusedNat_sound (identity.map toFinFive)
      ((List.all_eq_true.mp checked) _ finiteMember)
  rw [betaPart02Basis_roundTrip identity member] at finiteValid
  exact finiteValid

def finiteBetaPart03Basis : List (Identity (Fin 5)) :=
  betaPart03Basis.map fun identity => identity.map toFinFive

private theorem betaPart03Basis_roundTrip_checked :
    betaPart03Basis.all (fun identity =>
      decide ((identity.map toFinFive).map Fin.val = identity)) = true := by
  decide

private theorem betaPart03Basis_roundTrip
    (identity : Identity Nat) (member : identity ∈ betaPart03Basis) :
    (identity.map toFinFive).map Fin.val = identity := by
  exact of_decide_eq_true <|
    (List.all_eq_true.mp betaPart03Basis_roundTrip_checked) identity member

theorem modelsBetaPart03_of_finite_checks
    (candidate : FiniteTable)
    (checked : finiteBetaPart03Basis.all candidate.checkIdentityFused = true) :
    Models candidate.semigroup betaPart03Basis := by
  intro identity member
  have finiteMember : identity.map toFinFive ∈ finiteBetaPart03Basis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    candidate.checkIdentityFusedNat_sound (identity.map toFinFive)
      ((List.all_eq_true.mp checked) _ finiteMember)
  rw [betaPart03Basis_roundTrip identity member] at finiteValid
  exact finiteValid

def finiteBetaPart04Basis : List (Identity (Fin 5)) :=
  betaPart04Basis.map fun identity => identity.map toFinFive

private theorem betaPart04Basis_roundTrip_checked :
    betaPart04Basis.all (fun identity =>
      decide ((identity.map toFinFive).map Fin.val = identity)) = true := by
  decide

private theorem betaPart04Basis_roundTrip
    (identity : Identity Nat) (member : identity ∈ betaPart04Basis) :
    (identity.map toFinFive).map Fin.val = identity := by
  exact of_decide_eq_true <|
    (List.all_eq_true.mp betaPart04Basis_roundTrip_checked) identity member

theorem modelsBetaPart04_of_finite_checks
    (candidate : FiniteTable)
    (checked : finiteBetaPart04Basis.all candidate.checkIdentityFused = true) :
    Models candidate.semigroup betaPart04Basis := by
  intro identity member
  have finiteMember : identity.map toFinFive ∈ finiteBetaPart04Basis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    candidate.checkIdentityFusedNat_sound (identity.map toFinFive)
      ((List.all_eq_true.mp checked) _ finiteMember)
  rw [betaPart04Basis_roundTrip identity member] at finiteValid
  exact finiteValid

def finiteOppositeBetaPart01Basis : List (Identity (Fin 5)) :=
  oppositeBetaPart01Basis.map fun identity => identity.map toFinFive

private theorem oppositeBetaPart01Basis_roundTrip_checked :
    oppositeBetaPart01Basis.all (fun identity =>
      decide ((identity.map toFinFive).map Fin.val = identity)) = true := by
  decide

private theorem oppositeBetaPart01Basis_roundTrip
    (identity : Identity Nat) (member : identity ∈ oppositeBetaPart01Basis) :
    (identity.map toFinFive).map Fin.val = identity := by
  exact of_decide_eq_true <|
    (List.all_eq_true.mp oppositeBetaPart01Basis_roundTrip_checked) identity member

theorem modelsOppositeBetaPart01_of_finite_checks
    (candidate : FiniteTable)
    (checked : finiteOppositeBetaPart01Basis.all candidate.checkIdentityFused = true) :
    Models candidate.semigroup oppositeBetaPart01Basis := by
  intro identity member
  have finiteMember : identity.map toFinFive ∈ finiteOppositeBetaPart01Basis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    candidate.checkIdentityFusedNat_sound (identity.map toFinFive)
      ((List.all_eq_true.mp checked) _ finiteMember)
  rw [oppositeBetaPart01Basis_roundTrip identity member] at finiteValid
  exact finiteValid

def finiteOppositeBetaPart02Basis : List (Identity (Fin 5)) :=
  oppositeBetaPart02Basis.map fun identity => identity.map toFinFive

private theorem oppositeBetaPart02Basis_roundTrip_checked :
    oppositeBetaPart02Basis.all (fun identity =>
      decide ((identity.map toFinFive).map Fin.val = identity)) = true := by
  decide

private theorem oppositeBetaPart02Basis_roundTrip
    (identity : Identity Nat) (member : identity ∈ oppositeBetaPart02Basis) :
    (identity.map toFinFive).map Fin.val = identity := by
  exact of_decide_eq_true <|
    (List.all_eq_true.mp oppositeBetaPart02Basis_roundTrip_checked) identity member

theorem modelsOppositeBetaPart02_of_finite_checks
    (candidate : FiniteTable)
    (checked : finiteOppositeBetaPart02Basis.all candidate.checkIdentityFused = true) :
    Models candidate.semigroup oppositeBetaPart02Basis := by
  intro identity member
  have finiteMember : identity.map toFinFive ∈ finiteOppositeBetaPart02Basis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    candidate.checkIdentityFusedNat_sound (identity.map toFinFive)
      ((List.all_eq_true.mp checked) _ finiteMember)
  rw [oppositeBetaPart02Basis_roundTrip identity member] at finiteValid
  exact finiteValid

def finiteOppositeBetaPart03Basis : List (Identity (Fin 5)) :=
  oppositeBetaPart03Basis.map fun identity => identity.map toFinFive

private theorem oppositeBetaPart03Basis_roundTrip_checked :
    oppositeBetaPart03Basis.all (fun identity =>
      decide ((identity.map toFinFive).map Fin.val = identity)) = true := by
  decide

private theorem oppositeBetaPart03Basis_roundTrip
    (identity : Identity Nat) (member : identity ∈ oppositeBetaPart03Basis) :
    (identity.map toFinFive).map Fin.val = identity := by
  exact of_decide_eq_true <|
    (List.all_eq_true.mp oppositeBetaPart03Basis_roundTrip_checked) identity member

theorem modelsOppositeBetaPart03_of_finite_checks
    (candidate : FiniteTable)
    (checked : finiteOppositeBetaPart03Basis.all candidate.checkIdentityFused = true) :
    Models candidate.semigroup oppositeBetaPart03Basis := by
  intro identity member
  have finiteMember : identity.map toFinFive ∈ finiteOppositeBetaPart03Basis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    candidate.checkIdentityFusedNat_sound (identity.map toFinFive)
      ((List.all_eq_true.mp checked) _ finiteMember)
  rw [oppositeBetaPart03Basis_roundTrip identity member] at finiteValid
  exact finiteValid

def finiteOppositeBetaPart04Basis : List (Identity (Fin 5)) :=
  oppositeBetaPart04Basis.map fun identity => identity.map toFinFive

private theorem oppositeBetaPart04Basis_roundTrip_checked :
    oppositeBetaPart04Basis.all (fun identity =>
      decide ((identity.map toFinFive).map Fin.val = identity)) = true := by
  decide

private theorem oppositeBetaPart04Basis_roundTrip
    (identity : Identity Nat) (member : identity ∈ oppositeBetaPart04Basis) :
    (identity.map toFinFive).map Fin.val = identity := by
  exact of_decide_eq_true <|
    (List.all_eq_true.mp oppositeBetaPart04Basis_roundTrip_checked) identity member

theorem modelsOppositeBetaPart04_of_finite_checks
    (candidate : FiniteTable)
    (checked : finiteOppositeBetaPart04Basis.all candidate.checkIdentityFused = true) :
    Models candidate.semigroup oppositeBetaPart04Basis := by
  intro identity member
  have finiteMember : identity.map toFinFive ∈ finiteOppositeBetaPart04Basis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    candidate.checkIdentityFusedNat_sound (identity.map toFinFive)
      ((List.all_eq_true.mp checked) _ finiteMember)
  rw [oppositeBetaPart04Basis_roundTrip identity member] at finiteValid
  exact finiteValid

/-- Combine independently elaborated finite checks without rechecking them. -/
theorem modelsAppend
    {candidate : Semigroup α} {first second : List (Identity Nat)}
    (firstModels : Models candidate first)
    (secondModels : Models candidate second) :
    Models candidate (first ++ second) := by
  intro identity member
  rcases List.mem_append.mp member with member | member
  · exact firstModels identity member
  · exact secondModels identity member

/-- The unrestricted canonical-form content of Proposition 14.1. -/
structure AlphaCompleteness {S : Type u} (candidate : Semigroup S) : Prop where
  derives :
    ∀ identity : Identity Nat,
      identity.SatisfiedBy candidate →
      Derives alphaBasis identity.lhs identity.rhs

/-- The unrestricted canonical-form content of Proposition 14.4. -/
structure BetaCompleteness {S : Type u} (candidate : Semigroup S) : Prop where
  derives :
    ∀ identity : Identity Nat,
      identity.SatisfiedBy candidate →
      Derives betaBasis identity.lhs identity.rhs

theorem alphaBasisFor_of_completeness
    {S : Type u} (candidate : Semigroup S)
    (models : Models candidate alphaBasis)
    (completion : AlphaCompleteness candidate) :
    BasisFor candidate alphaBasis := by
  refine ⟨models, ?_⟩
  intro identity valid
  exact completion.derives identity valid

theorem betaBasisFor_of_completeness
    {S : Type u} (candidate : Semigroup S)
    (models : Models candidate betaBasis)
    (completion : BetaCompleteness candidate) :
    BasisFor candidate betaBasis := by
  refine ⟨models, ?_⟩
  intro identity valid
  exact completion.derives identity valid

namespace S6_12198

/-- Exact one-based catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,3,1,5,6],[4,4,4,4,4,4],[1,1,3,6,5,6],[6,6,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "d2fc01fdd4885051cc9ec62c542f32a73591cbb73270bad069f3ee13644c518f"

/-- The orientation in which the published Section 14 table is read. -/
abbrev publishedSemigroup : Semigroup (Fin 6) :=
  table.semigroup

end S6_12198

namespace S6_12399

/-- Exact one-based catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,2,3,1,5,6],[4,4,4,4,4,4],[1,2,3,6,5,6],[6,6,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "bdd94b4e99910af6184e0b93b6493cb1407ff1af8c084d77bcff42fb025054fa"

/-- The orientation in which the published Section 14 table is read. -/
abbrev publishedSemigroup : Semigroup (Fin 6) :=
  table.semigroup

end S6_12399

namespace S6_12526

/-- Exact one-based catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[3,3,3,3,3,3],[3,3,3,4,5,6],[5,5,5,5,5,5],[5,5,3,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "b31ef5406600384bd690991fdeed43da1e0dfd6332d3ea807564a1618418b929"

/-- The orientation in which the published Section 14 table is read. -/
abbrev publishedSemigroup : Semigroup (Fin 6) :=
  table.semigroup

end S6_12526

namespace S6_14467

/-- Exact one-based catalogue table: `[[1,1,1,4,5,6],[1,1,1,4,5,6],[3,3,3,4,5,6],[4,4,4,4,5,6],[4,4,6,4,5,6],[6,6,6,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 2 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 4 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "20877f894bdd63ccd163008643cd0bccf9ce9bc33c4fe81ea03dc0e3cf0f80af"

/-- The orientation in which the published Section 14 table is read. -/
abbrev publishedSemigroup : Semigroup (Fin 6) :=
  table.semigroup.opposite

end S6_14467


end SemigroupBasis.CoRoots.Order6SporadicSection14
