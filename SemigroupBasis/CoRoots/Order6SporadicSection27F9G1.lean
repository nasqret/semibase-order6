import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite
import SemigroupBasis.CoRoots.S5_107ListDerives

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6SporadicSection27

open SemigroupBasis

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

/-!
## Lee--Zhang Proposition 27.3

The capital letters in the published identities denote optional variables.
The definitions below are the exact 22 ordinary identities obtained by
expanding those optional positions.  Variables are encoded as
`x = 0`, `y = 1`, `h = 2`, `k = 3`, and `t = 4`.
-/

def lawA_H : Identity Nat :=
  ⟨w 0 [2, 0, 0], w 0 [2, 0]⟩

def lawA_empty : Identity Nat :=
  ⟨w 0 [0, 0], w 0 [0]⟩

def lawB_HK : Identity Nat :=
  ⟨w 0 [2, 1, 3, 0, 1], w 0 [2, 1, 3, 1, 0]⟩

def lawB_H : Identity Nat :=
  ⟨w 0 [2, 1, 0, 1], w 0 [2, 1, 1, 0]⟩

def lawB_K : Identity Nat :=
  ⟨w 0 [1, 3, 0, 1], w 0 [1, 3, 1, 0]⟩

def lawB_empty : Identity Nat :=
  ⟨w 0 [1, 0, 1], w 0 [1, 1, 0]⟩

def lawC_HK : Identity Nat :=
  ⟨w 0 [2, 1, 3, 1, 0], w 0 [2, 1, 3, 0]⟩

def lawC_H : Identity Nat :=
  ⟨w 0 [2, 1, 1, 0], w 0 [2, 1, 0]⟩

def lawC_K : Identity Nat :=
  ⟨w 0 [1, 3, 1, 0], w 0 [1, 3, 0]⟩

def lawC_empty : Identity Nat :=
  ⟨w 0 [1, 1, 0], w 0 [1, 0]⟩

def lawD_HKT : Identity Nat :=
  ⟨w 0 [2, 1, 3, 0, 4, 1], w 0 [2, 1, 3, 0, 4, 0]⟩

def lawD_HK : Identity Nat :=
  ⟨w 0 [2, 1, 3, 0, 1], w 0 [2, 1, 3, 0, 0]⟩

def lawD_HT : Identity Nat :=
  ⟨w 0 [2, 1, 0, 4, 1], w 0 [2, 1, 0, 4, 0]⟩

def lawD_H : Identity Nat :=
  ⟨w 0 [2, 1, 0, 1], w 0 [2, 1, 0, 0]⟩

def lawD_KT : Identity Nat :=
  ⟨w 0 [1, 3, 0, 4, 1], w 0 [1, 3, 0, 4, 0]⟩

def lawD_K : Identity Nat :=
  ⟨w 0 [1, 3, 0, 1], w 0 [1, 3, 0, 0]⟩

def lawD_T : Identity Nat :=
  ⟨w 0 [1, 0, 4, 1], w 0 [1, 0, 4, 0]⟩

def lawD_empty : Identity Nat :=
  ⟨w 0 [1, 0, 1], w 0 [1, 0, 0]⟩

def lawE_HK : Identity Nat :=
  ⟨w 0 [2, 0, 1, 3, 1], w 0 [2, 0, 1, 3, 0]⟩

def lawE_H : Identity Nat :=
  ⟨w 0 [2, 0, 1, 1], w 0 [2, 0, 1, 0]⟩

def lawE_K : Identity Nat :=
  ⟨w 0 [0, 1, 3, 1], w 0 [0, 1, 3, 0]⟩

def lawE_empty : Identity Nat :=
  ⟨w 0 [0, 1, 1], w 0 [0, 1, 0]⟩

/-- The exact 22-law ordinary expansion of Proposition 27.3, in the pinned
campaign source order. -/
def basis : List (Identity Nat) :=
  [lawA_H,
    lawE_HK, lawE_H,
    lawD_HKT, lawD_HK,
    lawB_HK, lawC_HK,
    lawD_HT, lawD_H,
    lawB_H, lawC_H,
    lawA_empty,
    lawE_K, lawE_empty,
    lawD_KT, lawD_K,
    lawB_K, lawC_K,
    lawD_T, lawD_empty,
    lawB_empty, lawC_empty]

def oppositeBasis : List (Identity Nat) :=
  reversedBasis basis

def toFinFive : Nat → Fin 5
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | _ => 4

def finiteBasis : List (Identity (Fin 5)) :=
  basis.map fun identity => identity.map toFinFive

private theorem basis_roundTrip_checked :
    basis.all (fun identity =>
      decide ((identity.map toFinFive).map Fin.val = identity)) = true := by
  decide

private theorem basis_roundTrip
    (identity : Identity Nat) (member : identity ∈ basis) :
    (identity.map toFinFive).map Fin.val = identity := by
  exact of_decide_eq_true <|
    (List.all_eq_true.mp basis_roundTrip_checked) identity member

/-- Exhaustive checking of the five displayed variables proves soundness of
the literal 22-law system for an exact finite table. -/
theorem models_of_finite_checks
    (candidate : FiniteTable)
    (checked : finiteBasis.all candidate.checkIdentity = true) :
    Models candidate.semigroup basis := by
  intro identity member
  have finiteMember : identity.map toFinFive ∈ finiteBasis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    candidate.checkIdentityNat_sound (identity.map toFinFive)
      ((List.all_eq_true.mp checked) _ finiteMember)
  rw [basis_roundTrip identity member] at finiteValid
  exact finiteValid

private theorem satisfied_of_fused_check
    (candidate : FiniteTable) (identity : Identity Nat)
    (member : identity ∈ basis)
    (checked :
      candidate.checkIdentityFused (identity.map toFinFive) = true) :
    identity.SatisfiedBy candidate.semigroup := by
  have finiteValid :=
    candidate.checkIdentityFusedNat_sound
      (identity.map toFinFive) checked
  rw [basis_roundTrip identity member] at finiteValid
  exact finiteValid

/-- Memory-bounded target soundness interface.  Keeping the 22 fused
certificates separate prevents the kernel from materializing one enormous
cartesian-product decision term. -/
theorem models_of_individual_fused_checks
    (candidate : FiniteTable)
    (checkA_H :
      candidate.checkIdentityFused (lawA_H.map toFinFive) = true)
    (checkE_HK :
      candidate.checkIdentityFused (lawE_HK.map toFinFive) = true)
    (checkE_H :
      candidate.checkIdentityFused (lawE_H.map toFinFive) = true)
    (checkD_HKT :
      candidate.checkIdentityFused (lawD_HKT.map toFinFive) = true)
    (checkD_HK :
      candidate.checkIdentityFused (lawD_HK.map toFinFive) = true)
    (checkB_HK :
      candidate.checkIdentityFused (lawB_HK.map toFinFive) = true)
    (checkC_HK :
      candidate.checkIdentityFused (lawC_HK.map toFinFive) = true)
    (checkD_HT :
      candidate.checkIdentityFused (lawD_HT.map toFinFive) = true)
    (checkD_H :
      candidate.checkIdentityFused (lawD_H.map toFinFive) = true)
    (checkB_H :
      candidate.checkIdentityFused (lawB_H.map toFinFive) = true)
    (checkC_H :
      candidate.checkIdentityFused (lawC_H.map toFinFive) = true)
    (checkA_empty :
      candidate.checkIdentityFused (lawA_empty.map toFinFive) = true)
    (checkE_K :
      candidate.checkIdentityFused (lawE_K.map toFinFive) = true)
    (checkE_empty :
      candidate.checkIdentityFused (lawE_empty.map toFinFive) = true)
    (checkD_KT :
      candidate.checkIdentityFused (lawD_KT.map toFinFive) = true)
    (checkD_K :
      candidate.checkIdentityFused (lawD_K.map toFinFive) = true)
    (checkB_K :
      candidate.checkIdentityFused (lawB_K.map toFinFive) = true)
    (checkC_K :
      candidate.checkIdentityFused (lawC_K.map toFinFive) = true)
    (checkD_T :
      candidate.checkIdentityFused (lawD_T.map toFinFive) = true)
    (checkD_empty :
      candidate.checkIdentityFused (lawD_empty.map toFinFive) = true)
    (checkB_empty :
      candidate.checkIdentityFused (lawB_empty.map toFinFive) = true)
    (checkC_empty :
      candidate.checkIdentityFused (lawC_empty.map toFinFive) = true) :
    Models candidate.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact satisfied_of_fused_check candidate lawA_H (by simp [basis]) checkA_H
  · exact satisfied_of_fused_check candidate lawE_HK (by simp [basis]) checkE_HK
  · exact satisfied_of_fused_check candidate lawE_H (by simp [basis]) checkE_H
  · exact satisfied_of_fused_check candidate lawD_HKT (by simp [basis]) checkD_HKT
  · exact satisfied_of_fused_check candidate lawD_HK (by simp [basis]) checkD_HK
  · exact satisfied_of_fused_check candidate lawB_HK (by simp [basis]) checkB_HK
  · exact satisfied_of_fused_check candidate lawC_HK (by simp [basis]) checkC_HK
  · exact satisfied_of_fused_check candidate lawD_HT (by simp [basis]) checkD_HT
  · exact satisfied_of_fused_check candidate lawD_H (by simp [basis]) checkD_H
  · exact satisfied_of_fused_check candidate lawB_H (by simp [basis]) checkB_H
  · exact satisfied_of_fused_check candidate lawC_H (by simp [basis]) checkC_H
  · exact satisfied_of_fused_check candidate lawA_empty (by simp [basis]) checkA_empty
  · exact satisfied_of_fused_check candidate lawE_K (by simp [basis]) checkE_K
  · exact satisfied_of_fused_check candidate lawE_empty (by simp [basis]) checkE_empty
  · exact satisfied_of_fused_check candidate lawD_KT (by simp [basis]) checkD_KT
  · exact satisfied_of_fused_check candidate lawD_K (by simp [basis]) checkD_K
  · exact satisfied_of_fused_check candidate lawB_K (by simp [basis]) checkB_K
  · exact satisfied_of_fused_check candidate lawC_K (by simp [basis]) checkC_K
  · exact satisfied_of_fused_check candidate lawD_T (by simp [basis]) checkD_T
  · exact satisfied_of_fused_check candidate lawD_empty (by simp [basis]) checkD_empty
  · exact satisfied_of_fused_check candidate lawB_empty (by simp [basis]) checkB_empty
  · exact satisfied_of_fused_check candidate lawC_empty (by simp [basis]) checkC_empty

/-! ## Primitive Proposition 27.3 derivations -/

private def instantiateFiveWords
    (x y h k t : Word Nat) : Nat → Word Nat
  | 0 => x
  | 1 => y
  | 2 => h
  | 3 => k
  | 4 => t
  | n + 5 => Word.singleton (n + 5)

private theorem basisAEmpty :
    Derives basis (w 0 [0, 0]) (w 0 [0]) :=
  Derives.fromBasis (e := lawA_empty) (by simp [basis])

private theorem basisAH :
    Derives basis (w 0 [2, 0, 0]) (w 0 [2, 0]) :=
  Derives.fromBasis (e := lawA_H) (by simp [basis])

private theorem basisBEmpty :
    Derives basis (w 0 [1, 0, 1]) (w 0 [1, 1, 0]) :=
  Derives.fromBasis (e := lawB_empty) (by simp [basis])

private theorem basisBH :
    Derives basis (w 0 [2, 1, 0, 1]) (w 0 [2, 1, 1, 0]) :=
  Derives.fromBasis (e := lawB_H) (by simp [basis])

private theorem basisBK :
    Derives basis (w 0 [1, 3, 0, 1]) (w 0 [1, 3, 1, 0]) :=
  Derives.fromBasis (e := lawB_K) (by simp [basis])

private theorem basisBHK :
    Derives basis (w 0 [2, 1, 3, 0, 1])
      (w 0 [2, 1, 3, 1, 0]) :=
  Derives.fromBasis (e := lawB_HK) (by simp [basis])

private theorem basisCEmpty :
    Derives basis (w 0 [1, 1, 0]) (w 0 [1, 0]) :=
  Derives.fromBasis (e := lawC_empty) (by simp [basis])

private theorem basisCH :
    Derives basis (w 0 [2, 1, 1, 0]) (w 0 [2, 1, 0]) :=
  Derives.fromBasis (e := lawC_H) (by simp [basis])

private theorem basisCK :
    Derives basis (w 0 [1, 3, 1, 0]) (w 0 [1, 3, 0]) :=
  Derives.fromBasis (e := lawC_K) (by simp [basis])

private theorem basisCHK :
    Derives basis (w 0 [2, 1, 3, 1, 0]) (w 0 [2, 1, 3, 0]) :=
  Derives.fromBasis (e := lawC_HK) (by simp [basis])

private theorem basisDEmpty :
    Derives basis (w 0 [1, 0, 1]) (w 0 [1, 0, 0]) :=
  Derives.fromBasis (e := lawD_empty) (by simp [basis])

private theorem basisDH :
    Derives basis (w 0 [2, 1, 0, 1]) (w 0 [2, 1, 0, 0]) :=
  Derives.fromBasis (e := lawD_H) (by simp [basis])

private theorem basisDK :
    Derives basis (w 0 [1, 3, 0, 1]) (w 0 [1, 3, 0, 0]) :=
  Derives.fromBasis (e := lawD_K) (by simp [basis])

private theorem basisDHK :
    Derives basis (w 0 [2, 1, 3, 0, 1]) (w 0 [2, 1, 3, 0, 0]) :=
  Derives.fromBasis (e := lawD_HK) (by simp [basis])

private theorem basisDT :
    Derives basis (w 0 [1, 0, 4, 1]) (w 0 [1, 0, 4, 0]) :=
  Derives.fromBasis (e := lawD_T) (by simp [basis])

private theorem basisDHT :
    Derives basis (w 0 [2, 1, 0, 4, 1]) (w 0 [2, 1, 0, 4, 0]) :=
  Derives.fromBasis (e := lawD_HT) (by simp [basis])

private theorem basisDKT :
    Derives basis (w 0 [1, 3, 0, 4, 1]) (w 0 [1, 3, 0, 4, 0]) :=
  Derives.fromBasis (e := lawD_KT) (by simp [basis])

private theorem basisDHKT :
    Derives basis (w 0 [2, 1, 3, 0, 4, 1])
      (w 0 [2, 1, 3, 0, 4, 0]) :=
  Derives.fromBasis (e := lawD_HKT) (by simp [basis])

private theorem basisEEmpty :
    Derives basis (w 0 [0, 1, 1]) (w 0 [0, 1, 0]) :=
  Derives.fromBasis (e := lawE_empty) (by simp [basis])

private theorem basisEH :
    Derives basis (w 0 [2, 0, 1, 1]) (w 0 [2, 0, 1, 0]) :=
  Derives.fromBasis (e := lawE_H) (by simp [basis])

private theorem basisEK :
    Derives basis (w 0 [0, 1, 3, 1]) (w 0 [0, 1, 3, 0]) :=
  Derives.fromBasis (e := lawE_K) (by simp [basis])

private theorem basisEHK :
    Derives basis (w 0 [2, 0, 1, 3, 1]) (w 0 [2, 0, 1, 3, 0]) :=
  Derives.fromBasis (e := lawE_HK) (by simp [basis])

theorem derivesAEmpty (x : Word Nat) :
    Derives basis ((x ++ x) ++ x) (x ++ x) := by
  have substituted :=
    Derives.subst basisAEmpty (instantiateFiveWords x x x x x)
  simpa [w, instantiateFiveWords, Word.bind, Word.singleton,
    Word.append, Word.append_assoc] using substituted

theorem derivesAH (x h : Word Nat) :
    Derives basis (((x ++ h) ++ x) ++ x) ((x ++ h) ++ x) := by
  have substituted :=
    Derives.subst basisAH (instantiateFiveWords x x h x x)
  simpa [w, instantiateFiveWords, Word.bind, Word.singleton,
    Word.append, Word.append_assoc] using substituted

theorem derivesBEmpty (x y : Word Nat) :
    Derives basis (((x ++ y) ++ x) ++ y)
      (((x ++ y) ++ y) ++ x) := by
  have substituted :=
    Derives.subst basisBEmpty (instantiateFiveWords x y x x x)
  simpa [w, instantiateFiveWords, Word.bind, Word.singleton,
    Word.append, Word.append_assoc] using substituted

theorem derivesBH (x y h : Word Nat) :
    Derives basis ((((x ++ h) ++ y) ++ x) ++ y)
      ((((x ++ h) ++ y) ++ y) ++ x) := by
  have substituted :=
    Derives.subst basisBH (instantiateFiveWords x y h x x)
  simpa [w, instantiateFiveWords, Word.bind, Word.singleton,
    Word.append, Word.append_assoc] using substituted

theorem derivesBK (x y k : Word Nat) :
    Derives basis ((((x ++ y) ++ k) ++ x) ++ y)
      ((((x ++ y) ++ k) ++ y) ++ x) := by
  have substituted :=
    Derives.subst basisBK (instantiateFiveWords x y x k x)
  simpa [w, instantiateFiveWords, Word.bind, Word.singleton,
    Word.append, Word.append_assoc] using substituted

theorem derivesBHK (x y h k : Word Nat) :
    Derives basis (((((x ++ h) ++ y) ++ k) ++ x) ++ y)
      (((((x ++ h) ++ y) ++ k) ++ y) ++ x) := by
  have substituted :=
    Derives.subst basisBHK (instantiateFiveWords x y h k x)
  simpa [w, instantiateFiveWords, Word.bind, Word.singleton,
    Word.append, Word.append_assoc] using substituted

theorem derivesCEmpty (x y : Word Nat) :
    Derives basis (((x ++ y) ++ y) ++ x) ((x ++ y) ++ x) := by
  have substituted :=
    Derives.subst basisCEmpty (instantiateFiveWords x y x x x)
  simpa [w, instantiateFiveWords, Word.bind, Word.singleton,
    Word.append, Word.append_assoc] using substituted

theorem derivesCH (x y h : Word Nat) :
    Derives basis ((((x ++ h) ++ y) ++ y) ++ x)
      (((x ++ h) ++ y) ++ x) := by
  have substituted :=
    Derives.subst basisCH (instantiateFiveWords x y h x x)
  simpa [w, instantiateFiveWords, Word.bind, Word.singleton,
    Word.append, Word.append_assoc] using substituted

theorem derivesCK (x y k : Word Nat) :
    Derives basis ((((x ++ y) ++ k) ++ y) ++ x)
      (((x ++ y) ++ k) ++ x) := by
  have substituted :=
    Derives.subst basisCK (instantiateFiveWords x y x k x)
  simpa [w, instantiateFiveWords, Word.bind, Word.singleton,
    Word.append, Word.append_assoc] using substituted

theorem derivesCHK (x y h k : Word Nat) :
    Derives basis (((((x ++ h) ++ y) ++ k) ++ y) ++ x)
      ((((x ++ h) ++ y) ++ k) ++ x) := by
  have substituted :=
    Derives.subst basisCHK (instantiateFiveWords x y h k x)
  simpa [w, instantiateFiveWords, Word.bind, Word.singleton,
    Word.append, Word.append_assoc] using substituted

theorem derivesDEmpty (x y : Word Nat) :
    Derives basis (((x ++ y) ++ x) ++ y)
      (((x ++ y) ++ x) ++ x) := by
  have substituted :=
    Derives.subst basisDEmpty (instantiateFiveWords x y x x x)
  simpa [w, instantiateFiveWords, Word.bind, Word.singleton,
    Word.append, Word.append_assoc] using substituted

theorem derivesDH (x y h : Word Nat) :
    Derives basis ((((x ++ h) ++ y) ++ x) ++ y)
      ((((x ++ h) ++ y) ++ x) ++ x) := by
  have substituted :=
    Derives.subst basisDH (instantiateFiveWords x y h x x)
  simpa [w, instantiateFiveWords, Word.bind, Word.singleton,
    Word.append, Word.append_assoc] using substituted

theorem derivesDK (x y k : Word Nat) :
    Derives basis ((((x ++ y) ++ k) ++ x) ++ y)
      ((((x ++ y) ++ k) ++ x) ++ x) := by
  have substituted :=
    Derives.subst basisDK (instantiateFiveWords x y x k x)
  simpa [w, instantiateFiveWords, Word.bind, Word.singleton,
    Word.append, Word.append_assoc] using substituted

theorem derivesDHK (x y h k : Word Nat) :
    Derives basis (((((x ++ h) ++ y) ++ k) ++ x) ++ y)
      (((((x ++ h) ++ y) ++ k) ++ x) ++ x) := by
  have substituted :=
    Derives.subst basisDHK (instantiateFiveWords x y h k x)
  simpa [w, instantiateFiveWords, Word.bind, Word.singleton,
    Word.append, Word.append_assoc] using substituted

theorem derivesDT (x y t : Word Nat) :
    Derives basis ((((x ++ y) ++ x) ++ t) ++ y)
      ((((x ++ y) ++ x) ++ t) ++ x) := by
  have substituted :=
    Derives.subst basisDT (instantiateFiveWords x y x x t)
  simpa [w, instantiateFiveWords, Word.bind, Word.singleton,
    Word.append, Word.append_assoc] using substituted

theorem derivesDHT (x y h t : Word Nat) :
    Derives basis (((((x ++ h) ++ y) ++ x) ++ t) ++ y)
      (((((x ++ h) ++ y) ++ x) ++ t) ++ x) := by
  have substituted :=
    Derives.subst basisDHT (instantiateFiveWords x y h x t)
  simpa [w, instantiateFiveWords, Word.bind, Word.singleton,
    Word.append, Word.append_assoc] using substituted

theorem derivesDKT (x y k t : Word Nat) :
    Derives basis (((((x ++ y) ++ k) ++ x) ++ t) ++ y)
      (((((x ++ y) ++ k) ++ x) ++ t) ++ x) := by
  have substituted :=
    Derives.subst basisDKT (instantiateFiveWords x y x k t)
  simpa [w, instantiateFiveWords, Word.bind, Word.singleton,
    Word.append, Word.append_assoc] using substituted

theorem derivesDHKT (x y h k t : Word Nat) :
    Derives basis ((((((x ++ h) ++ y) ++ k) ++ x) ++ t) ++ y)
      ((((((x ++ h) ++ y) ++ k) ++ x) ++ t) ++ x) := by
  have substituted :=
    Derives.subst basisDHKT (instantiateFiveWords x y h k t)
  simpa [w, instantiateFiveWords, Word.bind, Word.singleton,
    Word.append, Word.append_assoc] using substituted

theorem derivesEEmpty (x y : Word Nat) :
    Derives basis (((x ++ x) ++ y) ++ y)
      (((x ++ x) ++ y) ++ x) := by
  have substituted :=
    Derives.subst basisEEmpty (instantiateFiveWords x y x x x)
  simpa [w, instantiateFiveWords, Word.bind, Word.singleton,
    Word.append, Word.append_assoc] using substituted

theorem derivesEH (x y h : Word Nat) :
    Derives basis ((((x ++ h) ++ x) ++ y) ++ y)
      ((((x ++ h) ++ x) ++ y) ++ x) := by
  have substituted :=
    Derives.subst basisEH (instantiateFiveWords x y h x x)
  simpa [w, instantiateFiveWords, Word.bind, Word.singleton,
    Word.append, Word.append_assoc] using substituted

theorem derivesEK (x y k : Word Nat) :
    Derives basis ((((x ++ x) ++ y) ++ k) ++ y)
      ((((x ++ x) ++ y) ++ k) ++ x) := by
  have substituted :=
    Derives.subst basisEK (instantiateFiveWords x y x k x)
  simpa [w, instantiateFiveWords, Word.bind, Word.singleton,
    Word.append, Word.append_assoc] using substituted

theorem derivesEHK (x y h k : Word Nat) :
    Derives basis (((((x ++ h) ++ x) ++ y) ++ k) ++ y)
      (((((x ++ h) ++ x) ++ y) ++ k) ++ x) := by
  have substituted :=
    Derives.subst basisEHK (instantiateFiveWords x y h k x)
  simpa [w, instantiateFiveWords, Word.bind, Word.singleton,
    Word.append, Word.append_assoc] using substituted

private abbrev ListDerives : List Nat → List Nat → Prop :=
  S5_107.ListDerives basis

private abbrev listWordOfCons := S5_107.listWordOfCons

/-! ### Arbitrary-gap sorting from (27.2b) -/

private theorem listDerivesSortBothEmpty
    (first second : Nat) :
    ListDerives [first, second, first, second]
      [first, second, second, first] := by
  simpa [listWordOfCons, Word.singleton, Word.append,
    Word.append_assoc] using
      (S5_107.ListDerives.ofWord (basis := basis)
        (derivesBEmpty (Word.singleton first) (Word.singleton second)))

private theorem listDerivesSortInitialGapEmpty
    (first second gapHead : Nat) (gapTail : List Nat) :
    ListDerives
      ([first, second] ++ (gapHead :: gapTail) ++ [first, second])
      ([first, second] ++ (gapHead :: gapTail) ++ [second, first]) := by
  simpa [listWordOfCons, Word.singleton, Word.append,
    Word.append_assoc, List.append_assoc] using
      (S5_107.ListDerives.ofWord (basis := basis)
        (derivesBK (Word.singleton first) (Word.singleton second)
          (listWordOfCons gapHead gapTail)))

private theorem listDerivesSortFinalGapEmpty
    (first gapHead second : Nat) (gapTail : List Nat) :
    ListDerives
      ([first] ++ (gapHead :: gapTail) ++ [second, first, second])
      ([first] ++ (gapHead :: gapTail) ++ [second, second, first]) := by
  simpa [listWordOfCons, Word.singleton, Word.append,
    Word.append_assoc, List.append_assoc] using
      (S5_107.ListDerives.ofWord (basis := basis)
        (derivesBH (Word.singleton first) (Word.singleton second)
          (listWordOfCons gapHead gapTail)))

private theorem listDerivesSortGeneral
    (first firstGapHead second secondGapHead : Nat)
    (firstGapTail secondGapTail : List Nat) :
    ListDerives
      ([first] ++ (firstGapHead :: firstGapTail) ++ [second] ++
        (secondGapHead :: secondGapTail) ++ [first, second])
      ([first] ++ (firstGapHead :: firstGapTail) ++ [second] ++
        (secondGapHead :: secondGapTail) ++ [second, first]) := by
  simpa [listWordOfCons, Word.singleton, Word.append,
    Word.append_assoc, List.append_assoc] using
      (S5_107.ListDerives.ofWord (basis := basis)
        (derivesBHK (Word.singleton first) (Word.singleton second)
          (listWordOfCons firstGapHead firstGapTail)
          (listWordOfCons secondGapHead secondGapTail)))

theorem listDerivesSwapDisplayedSeconds
    (first second : Nat)
    (before firstGap secondGap after : List Nat) :
    ListDerives
      (before ++ [first] ++ firstGap ++ [second] ++ secondGap ++
        [first, second] ++ after)
      (before ++ [first] ++ firstGap ++ [second] ++ secondGap ++
        [second, first] ++ after) := by
  cases firstGap with
  | nil =>
      cases secondGap with
      | nil =>
          simpa [List.append_assoc] using
            S5_107.ListDerives.context before after
              (listDerivesSortBothEmpty first second)
      | cons secondGapHead secondGapTail =>
          simpa [List.append_assoc] using
            S5_107.ListDerives.context before after
              (listDerivesSortInitialGapEmpty
                first second secondGapHead secondGapTail)
  | cons firstGapHead firstGapTail =>
      cases secondGap with
      | nil =>
          simpa [List.append_assoc] using
            S5_107.ListDerives.context before after
              (listDerivesSortFinalGapEmpty
                first firstGapHead second firstGapTail)
      | cons secondGapHead secondGapTail =>
          simpa [List.append_assoc] using
            S5_107.ListDerives.context before after
              (listDerivesSortGeneral
                first firstGapHead second secondGapHead
                firstGapTail secondGapTail)

theorem listDerivesSwapAfterSeen
    (stem suffix : List Nat) (left right : Nat)
    (leftSeen : left ∈ stem) (rightSeen : right ∈ stem) :
    ListDerives (stem ++ [left, right] ++ suffix)
      (stem ++ [right, left] ++ suffix) := by
  by_cases equal : left = right
  · subst right
    exact S5_107.ListDerives.refl _
  · obtain ⟨leftBefore, leftAfter, prefixSplit⟩ :=
      List.mem_iff_append.mp leftSeen
    have rightInSplit :
        right ∈ leftBefore ∨ right ∈ leftAfter := by
      rw [prefixSplit] at rightSeen
      rcases List.mem_append.mp rightSeen with beforeMember | afterMember
      · exact Or.inl beforeMember
      · rcases List.mem_cons.mp afterMember with atLeft | inAfter
        · exact False.elim (equal atLeft.symm)
        · exact Or.inr inAfter
    rcases rightInSplit with rightBefore | rightAfter
    · obtain ⟨before, middle, beforeSplit⟩ :=
        List.mem_iff_append.mp rightBefore
      have displayed := listDerivesSwapDisplayedSeconds
        right left before middle leftAfter suffix
      simpa [prefixSplit, beforeSplit, List.append_assoc] using
        displayed.symm
    · obtain ⟨middle, tail, afterSplit⟩ :=
        List.mem_iff_append.mp rightAfter
      simpa [prefixSplit, afterSplit, List.append_assoc] using
        listDerivesSwapDisplayedSeconds
          left right leftBefore middle tail suffix

theorem listDerivesPermuteAfterSeen
    (stem suffix : List Nat) {source target : List Nat}
    (sourceSeen : ∀ letter, letter ∈ source → letter ∈ stem)
    (permutation : source.Perm target) :
    ListDerives (stem ++ source ++ suffix)
      (stem ++ target ++ suffix) := by
  induction permutation generalizing stem with
  | nil =>
      exact S5_107.ListDerives.refl _
  | cons head _ induction =>
      have derivation := induction (stem ++ [head]) (by
        intro letter member
        exact List.mem_append.mpr <| Or.inl <|
          sourceSeen letter (List.Mem.tail head member))
      simpa [List.append_assoc] using derivation
  | swap first second rest =>
      have firstSeen : first ∈ stem := sourceSeen first (by simp)
      have secondSeen : second ∈ stem := sourceSeen second (by simp)
      simpa [List.append_assoc] using
        listDerivesSwapAfterSeen
          stem (rest ++ suffix) second first secondSeen firstSeen
  | trans firstPermutation _ firstInduction secondInduction =>
      have firstDerivation := firstInduction stem sourceSeen
      have secondDerivation := secondInduction stem (by
        intro letter member
        exact sourceSeen letter ((firstPermutation.mem_iff).mpr member))
      exact firstDerivation.trans secondDerivation

/-! ### Letter removal and retargeting from (27.2c--e) -/

theorem listDerivesCDisplayed
    (first second : Nat)
    (before firstGap secondGap after : List Nat) :
    ListDerives
      (before ++ [first] ++ firstGap ++ [second] ++ secondGap ++
        [second, first] ++ after)
      (before ++ [first] ++ firstGap ++ [second] ++ secondGap ++
        [first] ++ after) := by
  cases firstGap with
  | nil =>
      cases secondGap with
      | nil =>
          have base := S5_107.ListDerives.ofWord (basis := basis)
            (derivesCEmpty (Word.singleton first) (Word.singleton second))
          simpa [listWordOfCons, Word.singleton, Word.append,
            Word.append_assoc, List.append_assoc] using
              S5_107.ListDerives.context before after base
      | cons kHead kTail =>
          have base := S5_107.ListDerives.ofWord (basis := basis)
            (derivesCK (Word.singleton first) (Word.singleton second)
              (listWordOfCons kHead kTail))
          simpa [listWordOfCons, Word.singleton, Word.append,
            Word.append_assoc, List.append_assoc] using
              S5_107.ListDerives.context before after base
  | cons hHead hTail =>
      cases secondGap with
      | nil =>
          have base := S5_107.ListDerives.ofWord (basis := basis)
            (derivesCH (Word.singleton first) (Word.singleton second)
              (listWordOfCons hHead hTail))
          simpa [listWordOfCons, Word.singleton, Word.append,
            Word.append_assoc, List.append_assoc] using
              S5_107.ListDerives.context before after base
      | cons kHead kTail =>
          have base := S5_107.ListDerives.ofWord (basis := basis)
            (derivesCHK (Word.singleton first) (Word.singleton second)
              (listWordOfCons hHead hTail) (listWordOfCons kHead kTail))
          simpa [listWordOfCons, Word.singleton, Word.append,
            Word.append_assoc, List.append_assoc] using
              S5_107.ListDerives.context before after base

theorem listDerivesDDisplayed
    (first second : Nat)
    (before hGap kGap tGap after : List Nat) :
    ListDerives
      (before ++ [first] ++ hGap ++ [second] ++ kGap ++
        [first] ++ tGap ++ [second] ++ after)
      (before ++ [first] ++ hGap ++ [second] ++ kGap ++
        [first] ++ tGap ++ [first] ++ after) := by
  cases hGap with
  | nil =>
      cases kGap with
      | nil =>
          cases tGap with
          | nil =>
              have base := S5_107.ListDerives.ofWord (basis := basis)
                (derivesDEmpty
                  (Word.singleton first) (Word.singleton second))
              simpa [listWordOfCons, Word.singleton, Word.append,
                Word.append_assoc, List.append_assoc] using
                  S5_107.ListDerives.context before after base
          | cons tHead tTail =>
              have base := S5_107.ListDerives.ofWord (basis := basis)
                (derivesDT
                  (Word.singleton first) (Word.singleton second)
                  (listWordOfCons tHead tTail))
              simpa [listWordOfCons, Word.singleton, Word.append,
                Word.append_assoc, List.append_assoc] using
                  S5_107.ListDerives.context before after base
      | cons kHead kTail =>
          cases tGap with
          | nil =>
              have base := S5_107.ListDerives.ofWord (basis := basis)
                (derivesDK
                  (Word.singleton first) (Word.singleton second)
                  (listWordOfCons kHead kTail))
              simpa [listWordOfCons, Word.singleton, Word.append,
                Word.append_assoc, List.append_assoc] using
                  S5_107.ListDerives.context before after base
          | cons tHead tTail =>
              have base := S5_107.ListDerives.ofWord (basis := basis)
                (derivesDKT
                  (Word.singleton first) (Word.singleton second)
                  (listWordOfCons kHead kTail)
                  (listWordOfCons tHead tTail))
              simpa [listWordOfCons, Word.singleton, Word.append,
                Word.append_assoc, List.append_assoc] using
                  S5_107.ListDerives.context before after base
  | cons hHead hTail =>
      cases kGap with
      | nil =>
          cases tGap with
          | nil =>
              have base := S5_107.ListDerives.ofWord (basis := basis)
                (derivesDH
                  (Word.singleton first) (Word.singleton second)
                  (listWordOfCons hHead hTail))
              simpa [listWordOfCons, Word.singleton, Word.append,
                Word.append_assoc, List.append_assoc] using
                  S5_107.ListDerives.context before after base
          | cons tHead tTail =>
              have base := S5_107.ListDerives.ofWord (basis := basis)
                (derivesDHT
                  (Word.singleton first) (Word.singleton second)
                  (listWordOfCons hHead hTail)
                  (listWordOfCons tHead tTail))
              simpa [listWordOfCons, Word.singleton, Word.append,
                Word.append_assoc, List.append_assoc] using
                  S5_107.ListDerives.context before after base
      | cons kHead kTail =>
          cases tGap with
          | nil =>
              have base := S5_107.ListDerives.ofWord (basis := basis)
                (derivesDHK
                  (Word.singleton first) (Word.singleton second)
                  (listWordOfCons hHead hTail)
                  (listWordOfCons kHead kTail))
              simpa [listWordOfCons, Word.singleton, Word.append,
                Word.append_assoc, List.append_assoc] using
                  S5_107.ListDerives.context before after base
          | cons tHead tTail =>
              have base := S5_107.ListDerives.ofWord (basis := basis)
                (derivesDHKT
                  (Word.singleton first) (Word.singleton second)
                  (listWordOfCons hHead hTail)
                  (listWordOfCons kHead kTail)
                  (listWordOfCons tHead tTail))
              simpa [listWordOfCons, Word.singleton, Word.append,
                Word.append_assoc, List.append_assoc] using
                  S5_107.ListDerives.context before after base

theorem listDerivesEDisplayed
    (first second : Nat)
    (before hGap kGap after : List Nat) :
    ListDerives
      (before ++ [first] ++ hGap ++ [first, second] ++
        kGap ++ [second] ++ after)
      (before ++ [first] ++ hGap ++ [first, second] ++
        kGap ++ [first] ++ after) := by
  cases hGap with
  | nil =>
      cases kGap with
      | nil =>
          have base := S5_107.ListDerives.ofWord (basis := basis)
            (derivesEEmpty (Word.singleton first) (Word.singleton second))
          simpa [listWordOfCons, Word.singleton, Word.append,
            Word.append_assoc, List.append_assoc] using
              S5_107.ListDerives.context before after base
      | cons kHead kTail =>
          have base := S5_107.ListDerives.ofWord (basis := basis)
            (derivesEK (Word.singleton first) (Word.singleton second)
              (listWordOfCons kHead kTail))
          simpa [listWordOfCons, Word.singleton, Word.append,
            Word.append_assoc, List.append_assoc] using
              S5_107.ListDerives.context before after base
  | cons hHead hTail =>
      cases kGap with
      | nil =>
          have base := S5_107.ListDerives.ofWord (basis := basis)
            (derivesEH (Word.singleton first) (Word.singleton second)
              (listWordOfCons hHead hTail))
          simpa [listWordOfCons, Word.singleton, Word.append,
            Word.append_assoc, List.append_assoc] using
              S5_107.ListDerives.context before after base
      | cons kHead kTail =>
          have base := S5_107.ListDerives.ofWord (basis := basis)
            (derivesEHK (Word.singleton first) (Word.singleton second)
              (listWordOfCons hHead hTail) (listWordOfCons kHead kTail))
          simpa [listWordOfCons, Word.singleton, Word.append,
            Word.append_assoc, List.append_assoc] using
              S5_107.ListDerives.context before after base

/-! ### Duplicate contraction from (27.2a) -/

private theorem listDerivesPowerContraction (letter : Nat) :
    ListDerives [letter, letter, letter] [letter, letter] := by
  simpa [listWordOfCons, Word.singleton, Word.append, Word.append_assoc] using
    (S5_107.ListDerives.ofWord (basis := basis)
      (derivesAEmpty (Word.singleton letter)))

private theorem listDerivesGapContraction
    (letter bridgeHead : Nat) (bridgeTail : List Nat) :
    ListDerives
      ([letter] ++ (bridgeHead :: bridgeTail) ++ [letter, letter])
      ([letter] ++ (bridgeHead :: bridgeTail) ++ [letter]) := by
  simpa [listWordOfCons, Word.singleton, Word.append,
    Word.append_assoc, List.append_assoc] using
      (S5_107.ListDerives.ofWord (basis := basis)
        (derivesAH (Word.singleton letter)
          (listWordOfCons bridgeHead bridgeTail)))

theorem listDerivesContractAdjacentAfterSeen
    (stem suffix : List Nat) (letter : Nat)
    (seen : letter ∈ stem) :
    ListDerives (stem ++ [letter, letter] ++ suffix)
      (stem ++ [letter] ++ suffix) := by
  obtain ⟨before, after, stemShape⟩ := List.mem_iff_append.mp seen
  cases after with
  | nil =>
      simpa [stemShape, List.append_assoc] using
        S5_107.ListDerives.context before suffix
          (listDerivesPowerContraction letter)
  | cons bridgeHead bridgeTail =>
      simpa [stemShape, List.append_assoc] using
        S5_107.ListDerives.context before suffix
          (listDerivesGapContraction letter bridgeHead bridgeTail)

/-- Keep the final occurrence of every displayed letter. -/
def deduplicateLater : List Nat → List Nat
  | [] => []
  | letter :: rest =>
      if letter ∈ rest then deduplicateLater rest
      else letter :: deduplicateLater rest

theorem deduplicateLater_mem_iff (tested : Nat) :
    ∀ letters : List Nat,
      tested ∈ deduplicateLater letters ↔ tested ∈ letters
  | [] => by simp [deduplicateLater]
  | letter :: rest => by
      by_cases present : letter ∈ rest
      · rw [deduplicateLater, if_pos present,
          deduplicateLater_mem_iff tested rest]
        constructor
        · exact List.Mem.tail letter
        · intro member
          rcases List.mem_cons.mp member with atLetter | inRest
          · simpa [atLetter] using present
          · exact inRest
      · by_cases equal : tested = letter
        · subst tested
          simp [deduplicateLater, present]
        · simp [deduplicateLater, present, equal,
            deduplicateLater_mem_iff tested rest]

theorem deduplicateLater_nodup :
    ∀ letters : List Nat, (deduplicateLater letters).Nodup
  | [] => by simp [deduplicateLater]
  | letter :: rest => by
      by_cases present : letter ∈ rest
      · simpa [deduplicateLater, present] using
          deduplicateLater_nodup rest
      · rw [deduplicateLater, if_neg present, List.nodup_cons]
        exact ⟨by
          intro member
          exact present <|
            (deduplicateLater_mem_iff letter rest).mp member,
          deduplicateLater_nodup rest⟩

theorem listDerivesDeduplicateLater
    (suffix : List Nat) :
    ∀ (stem source : List Nat),
      (∀ letter, letter ∈ source → letter ∈ stem) →
      ListDerives (stem ++ source ++ suffix)
        (stem ++ deduplicateLater source ++ suffix)
  | _, [], _ => by
      simpa using S5_107.ListDerives.refl (basis := basis) _
  | stem, letter :: rest, sourceSeen => by
      have restSeen :
          ∀ tested, tested ∈ rest → tested ∈ stem ++ [letter] := by
        intro tested member
        exact List.mem_append.mpr <| Or.inl <|
          sourceSeen tested (List.Mem.tail letter member)
      have recurse :=
        listDerivesDeduplicateLater suffix (stem ++ [letter]) rest restSeen
      have recurseShape :
          ListDerives (stem ++ (letter :: rest) ++ suffix)
            (stem ++ [letter] ++ deduplicateLater rest ++ suffix) := by
        simpa [List.append_assoc] using recurse
      by_cases present : letter ∈ rest
      · have retained : letter ∈ deduplicateLater rest :=
          (deduplicateLater_mem_iff letter rest).mpr present
        have exposePermutation :
            (letter :: deduplicateLater rest).Perm
              (letter :: letter :: (deduplicateLater rest).erase letter) :=
          List.Perm.cons letter (List.perm_cons_erase retained)
        have exposeSeen :
            ∀ tested, tested ∈ letter :: deduplicateLater rest →
              tested ∈ stem := by
          intro tested member
          rcases List.mem_cons.mp member with atLetter | inRest
          · simpa [atLetter] using
              sourceSeen letter (List.Mem.head rest)
          · exact sourceSeen tested (List.Mem.tail letter <|
              (deduplicateLater_mem_iff tested rest).mp inRest)
        have expose :
            ListDerives
              (stem ++ [letter] ++ deduplicateLater rest ++ suffix)
              (stem ++ [letter, letter] ++
                (deduplicateLater rest).erase letter ++ suffix) := by
          simpa [List.append_assoc] using
            listDerivesPermuteAfterSeen stem suffix exposeSeen
              exposePermutation
        have contract :
            ListDerives
              (stem ++ [letter, letter] ++
                (deduplicateLater rest).erase letter ++ suffix)
              (stem ++ [letter] ++
                (deduplicateLater rest).erase letter ++ suffix) := by
          simpa [List.append_assoc] using
            listDerivesContractAdjacentAfterSeen
              stem ((deduplicateLater rest).erase letter ++ suffix)
              letter (sourceSeen letter (List.Mem.head rest))
        have restoreForward :=
          listDerivesPermuteAfterSeen stem suffix
            (by
              intro tested member
              exact sourceSeen tested (List.Mem.tail letter <|
                (deduplicateLater_mem_iff tested rest).mp member))
            (List.perm_cons_erase retained)
        have restore :
            ListDerives
              (stem ++ [letter] ++
                (deduplicateLater rest).erase letter ++ suffix)
              (stem ++ deduplicateLater rest ++ suffix) := by
          simpa [List.append_assoc] using restoreForward.symm
        rw [deduplicateLater, if_pos present]
        simpa [List.append_assoc] using
          recurseShape.trans (expose.trans (contract.trans restore))
      · rw [deduplicateLater, if_neg present]
        simpa [List.append_assoc] using recurseShape

end SemigroupBasis.CoRoots.Order6SporadicSection27
