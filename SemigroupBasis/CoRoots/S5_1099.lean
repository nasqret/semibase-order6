import SemigroupBasis.CoRoots.S5_107ListDerives
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite

namespace SemigroupBasis.CoRoots.S5_1099

open SemigroupBasis

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def x : Word Nat := w 0 []
def xx : Word Nat := w 0 [0]
def xyz : Word Nat := w 0 [1, 2]
def xyzxz : Word Nat := w 0 [1, 2, 0, 2]

def idempotenceLaw : Identity Nat :=
  ⟨x, xx⟩

def r3q3Law : Identity Nat :=
  ⟨xyz, xyzxz⟩

/-- The exact Fennemore `R3 = Q3` basis. -/
def basis : List (Identity Nat) :=
  [idempotenceLaw, r3q3Law]

/-- The literal reverse-word basis `x = xx`, `zyx = zxzyx`. -/
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

/-- Exhaustive checks on the three basis variables imply unrestricted
soundness over natural-number variables. -/
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

private theorem r3q3Law_mem :
    r3q3Law ∈ basis := by
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

/-- Generic `UVW -> UVWUW`, the defining `R3 = Q3` move. -/
theorem derivesR3Q3Expansion (u v z : Word Nat) :
    Derives basis
      ((u ++ v) ++ z)
      (((((u ++ v) ++ z) ++ u) ++ z)) := by
  have base : Derives basis xyz xyzxz :=
    Derives.fromBasis (e := r3q3Law) r3q3Law_mem
  have substituted :=
    Derives.subst base (instantiateThreeWords u v z)
  simpa [r3q3Law, xyz, xyzxz, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

theorem derivesR3Q3Contraction (u v z : Word Nat) :
    Derives basis
      (((((u ++ v) ++ z) ++ u) ++ z))
      ((u ++ v) ++ z) :=
  (derivesR3Q3Expansion u v z).symm

/-- Derived bridge `UVWV -> UVWUV`. It inserts the edge `UV` immediately
before a terminal `V`. -/
theorem derivesForwardBridge (u v z : Word Nat) :
    Derives basis
      (((u ++ v) ++ z) ++ v)
      ((((u ++ v) ++ z) ++ u) ++ v) := by
  let stem := (u ++ v) ++ z
  have duplicate :=
    Derives.appendRight (derivesIdempotenceExpansion stem) v
  have contract :=
    Derives.prepend (u ++ v)
      (derivesR3Q3Contraction z u v)
  exact duplicate.trans <| by
    simpa [stem, Word.append_assoc] using contract

/-- Derived bridge `UVWU -> UVWVU`. It inserts the reverse edge `VU`
immediately before a terminal `U`. -/
theorem derivesReverseBridge (u v z : Word Nat) :
    Derives basis
      (((u ++ v) ++ z) ++ u)
      ((((u ++ v) ++ z) ++ v) ++ u) := by
  let vw := v ++ z
  have duplicate :=
    Derives.appendRight
      (Derives.prepend u (derivesIdempotenceExpansion vw)) u
  have expand :=
    Derives.appendRight
      (derivesR3Q3Expansion u vw v) (z ++ u)
  have contract :=
    Derives.prepend u
      (derivesR3Q3Contraction (v ++ z) v u)
  apply Derives.trans
  · simpa [vw, Word.append_assoc] using duplicate
  · apply Derives.trans
    · simpa [vw, Word.append_assoc] using expand
    · simpa [vw, Word.append_assoc] using contract

end SemigroupBasis.CoRoots.S5_1099
