import SemigroupBasis.CoRoots.S5_107ListDerives
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite

namespace SemigroupBasis.CoRoots.S5_1089

open SemigroupBasis

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def x : Word Nat := w 0 []
def xx : Word Nat := w 0 [0]
def xyz : Word Nat := w 0 [1, 2]
def xzyz : Word Nat := w 0 [2, 1, 2]

def idempotenceLaw : Identity Nat :=
  ⟨x, xx⟩

def r2s2Law : Identity Nat :=
  ⟨xyz, xzyz⟩

/-- The exact Fennemore `R2 = S2` basis. -/
def basis : List (Identity Nat) :=
  [idempotenceLaw, r2s2Law]

/-- The literal reverse-word basis `x = xx`, `zyx = zyzx`. -/
def oppositeBasis : List (Identity Nat) :=
  reversedBasis basis

def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

def finiteBasis : List (Identity (Fin 3)) :=
  basis.map fun identity => identity.map toFinThree

private theorem basis_roundTrip_checked :
    basis.all (fun identity =>
      decide ((identity.map toFinThree).map Fin.val = identity)) = true := by
  decide

private theorem basis_roundTrip
    (identity : Identity Nat) (member : identity ∈ basis) :
    (identity.map toFinThree).map Fin.val = identity := by
  exact of_decide_eq_true <|
    (List.all_eq_true.mp basis_roundTrip_checked) identity member

theorem models_of_finite_checks
    (table : FiniteTable)
    (checks : finiteBasis.all table.checkIdentity = true) :
    Models table.semigroup basis := by
  intro identity member
  have finiteMember : identity.map toFinThree ∈ finiteBasis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    table.checkIdentityNat_sound (identity.map toFinThree)
      ((List.all_eq_true.mp checks) _ finiteMember)
  rw [basis_roundTrip identity member] at finiteValid
  exact finiteValid

private def instantiateThreeWords
    (u v z : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => z
  | n + 3 => Word.singleton (n + 3)

private theorem idempotenceLaw_mem :
    idempotenceLaw ∈ basis := by
  simp [basis]

private theorem r2s2Law_mem :
    r2s2Law ∈ basis := by
  simp [basis]

theorem derivesIdempotenceExpansion (u : Word Nat) :
    Derives basis u (u ++ u) := by
  have base : Derives basis x xx :=
    Derives.fromBasis (e := idempotenceLaw) idempotenceLaw_mem
  have substituted := Derives.subst base (fun _ => u)
  simpa [idempotenceLaw, x, xx, w, Word.bind, Word.append] using
    substituted

theorem derivesIdempotenceContraction (u : Word Nat) :
    Derives basis (u ++ u) u :=
  (derivesIdempotenceExpansion u).symm

/-- Generic `UVW -> UWVW`, the defining `R2 = S2` move. -/
theorem derivesR2S2Expansion (u v z : Word Nat) :
    Derives basis
      ((u ++ v) ++ z)
      (((u ++ z) ++ v) ++ z) := by
  have base : Derives basis xyz xzyz :=
    Derives.fromBasis (e := r2s2Law) r2s2Law_mem
  have substituted :=
    Derives.subst base (instantiateThreeWords u v z)
  simpa [r2s2Law, xyz, xzyz, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

theorem derivesR2S2Contraction (u v z : Word Nat) :
    Derives basis
      (((u ++ z) ++ v) ++ z)
      ((u ++ v) ++ z) :=
  (derivesR2S2Expansion u v z).symm

end SemigroupBasis.CoRoots.S5_1089
