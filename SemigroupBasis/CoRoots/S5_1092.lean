import SemigroupBasis.CoRoots.S5_107ListDerives
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite

namespace SemigroupBasis.CoRoots.S5_1092

open SemigroupBasis

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def x : Word Nat := w 0 []
def xx : Word Nat := w 0 [0]
def xyzx : Word Nat := w 0 [1, 2, 0]
def xyxzx : Word Nat := w 0 [1, 0, 2, 0]

def idempotenceLaw : Identity Nat :=
  ⟨x, xx⟩

def regularBandLaw : Identity Nat :=
  ⟨xyzx, xyxzx⟩

def basis : List (Identity Nat) :=
  [idempotenceLaw, regularBandLaw]

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

private def instantiateThreeWords (u v z : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => z
  | n + 3 => Word.singleton (n + 3)

private theorem idempotenceLaw_mem :
    idempotenceLaw ∈ basis := by
  simp [basis]

private theorem regularBandLaw_mem :
    regularBandLaw ∈ basis := by
  simp [basis]

theorem derivesIdempotenceExpansion (u : Word Nat) :
    Derives basis u (u ++ u) := by
  have hbase :
      Derives basis x xx :=
    Derives.fromBasis (e := idempotenceLaw) idempotenceLaw_mem
  have h := Derives.subst hbase (fun _ => u)
  simpa [idempotenceLaw, x, xx, w, Word.bind, Word.append] using h

theorem derivesIdempotenceContraction (u : Word Nat) :
    Derives basis (u ++ u) u :=
  (derivesIdempotenceExpansion u).symm

theorem derivesRegularExpansion (u v z : Word Nat) :
    Derives basis (((u ++ v) ++ z) ++ u) ((((u ++ v) ++ u) ++ z) ++ u) := by
  have hbase :
      Derives basis xyzx xyxzx :=
    Derives.fromBasis (e := regularBandLaw) regularBandLaw_mem
  have h := Derives.subst hbase (instantiateThreeWords u v z)
  simpa [regularBandLaw, xyzx, xyxzx, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using h

theorem derivesRegularContraction (u v z : Word Nat) :
    Derives basis ((((u ++ v) ++ u) ++ z) ++ u) (((u ++ v) ++ z) ++ u) :=
  (derivesRegularExpansion u v z).symm

end SemigroupBasis.CoRoots.S5_1092
