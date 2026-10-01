import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite

namespace SemigroupBasis.CoRoots.S5_831

open SemigroupBasis

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def xx : Word Nat := w 0 [0]
def xxx : Word Nat := w 0 [0, 0]
def xyx : Word Nat := w 0 [1, 0]
def xyy : Word Nat := w 0 [1, 1]
def yyx : Word Nat := w 1 [1, 0]

def powerLaw : Identity Nat :=
  ⟨xx, xxx⟩

def copyLaw : Identity Nat :=
  ⟨xyx, xyy⟩

/-- The exact basis shared by `S5_831` and `S5_832`. -/
def basis : List (Identity Nat) :=
  [powerLaw, copyLaw]

/-- The literal reverse-word basis for the non-self-dual opposite classes. -/
def expectedOppositeBasis : List (Identity Nat) :=
  [⟨xx, xxx⟩, ⟨xyx, yyx⟩]

theorem reversedBasis_eq_expected :
    reversedBasis basis = expectedOppositeBasis := by
  rfl

private def toFinTwo : Nat → Fin 2
  | 0 => 0
  | _ => 1

private def finiteBasis : List (Identity (Fin 2)) :=
  basis.map fun identity => identity.map toFinTwo

private theorem basis_roundTrip_checked :
    basis.all (fun identity =>
      decide ((identity.map toFinTwo).map Fin.val = identity)) = true := by
  decide

private theorem basis_roundTrip
    (identity : Identity Nat) (member : identity ∈ basis) :
    (identity.map toFinTwo).map Fin.val = identity := by
  exact of_decide_eq_true <|
    (List.all_eq_true.mp basis_roundTrip_checked) identity member

/-- Exhaustive checks on the two basis variables imply infinite-variable
soundness. -/
theorem models_of_finite_checks
    (table : FiniteTable)
    (checks : finiteBasis.all table.checkIdentity = true) :
    Models table.semigroup basis := by
  intro identity member
  have finiteMember : identity.map toFinTwo ∈ finiteBasis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    table.checkIdentityNat_sound (identity.map toFinTwo)
      ((List.all_eq_true.mp checks) _ finiteMember)
  rw [basis_roundTrip identity member] at finiteValid
  exact finiteValid

private def instantiateTwoWords
    (u v : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | n + 2 => Word.singleton (n + 2)

private theorem powerLaw_mem :
    powerLaw ∈ basis := by
  simp [basis]

private theorem copyLaw_mem :
    copyLaw ∈ basis := by
  simp [basis]

/-- Generic substitution instance `uu = uuu`. -/
theorem derivesPowerExpansion (u : Word Nat) :
    Derives basis (u ++ u) ((u ++ u) ++ u) := by
  have base : Derives basis xx xxx :=
    Derives.fromBasis (e := powerLaw) powerLaw_mem
  have substituted :=
    Derives.subst base (instantiateTwoWords u u)
  simpa [powerLaw, xx, xxx, w, instantiateTwoWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

/-- Generic contraction `uuu -> uu`. -/
theorem derivesPowerContraction (u : Word Nat) :
    Derives basis ((u ++ u) ++ u) (u ++ u) :=
  (derivesPowerExpansion u).symm

/-- Generic substitution instance `uvu -> uvv`. -/
theorem derivesCopy (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) ((u ++ v) ++ v) := by
  have base : Derives basis xyx xyy :=
    Derives.fromBasis (e := copyLaw) copyLaw_mem
  have substituted :=
    Derives.subst base (instantiateTwoWords u v)
  simpa [copyLaw, xyx, xyy, w, instantiateTwoWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

end SemigroupBasis.CoRoots.S5_831
