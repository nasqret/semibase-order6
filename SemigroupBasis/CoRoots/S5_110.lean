import SemigroupBasis.FiniteReflection
import SemigroupBasis.Generated.CatalogueOrder5Part01
import SemigroupBasis.Opposite

namespace SemigroupBasis.CoRoots.S5_110

open SemigroupBasis

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def xx : Word Nat := w 0 [0]
def xxx : Word Nat := w 0 [0, 0]
def xyx : Word Nat := w 0 [1, 0]
def xxy : Word Nat := w 0 [0, 1]
def yxx : Word Nat := w 1 [0, 0]

def powerLaw : Identity Nat := ⟨xx, xxx⟩
def leftFoldLaw : Identity Nat := ⟨xyx, xxy⟩
def rightFoldLaw : Identity Nat := ⟨xyx, yxx⟩

/-- The exact ordered basis recorded for the published `S5_110` root.
This definition does not formalize the published completeness proof. -/
def basis : List (Identity Nat) :=
  [powerLaw, leftFoldLaw, rightFoldLaw]

def oppositeBasis : List (Identity Nat) :=
  reversedBasis basis

private def toFinTwo : Nat → Fin 2
  | 0 => 0
  | _ => 1

def finiteBasis : List (Identity (Fin 2)) :=
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

theorem models_of_finite_checks
    (table : FiniteTable)
    (checked : finiteBasis.all table.checkIdentity = true) :
    Models table.semigroup basis := by
  intro identity member
  have finiteMember : identity.map toFinTwo ∈ finiteBasis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    table.checkIdentityNat_sound (identity.map toFinTwo)
      ((List.all_eq_true.mp checked) _ finiteMember)
  rw [basis_roundTrip identity member] at finiteValid
  exact finiteValid

abbrev table : FiniteTable :=
  Generated.Catalogue.S5_110.table

set_option maxRecDepth 100000 in
theorem models : Models table.semigroup basis :=
  models_of_finite_checks table (by decide)

theorem oppositeModels :
    Models table.semigroup.opposite oppositeBasis :=
  models.oppositeReversed

private def instantiateTwoWords
    (u v : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | n + 2 => Word.singleton (n + 2)

private theorem basisPower : Derives basis xx xxx :=
  Derives.fromBasis (e := powerLaw) <| by simp [basis]

private theorem basisLeftFold : Derives basis xyx xxy :=
  Derives.fromBasis (e := leftFoldLaw) <| by simp [basis]

private theorem basisRightFold : Derives basis xyx yxx :=
  Derives.fromBasis (e := rightFoldLaw) <| by simp [basis]

theorem derivesPowerExpansion (u : Word Nat) :
    Derives basis (u ++ u) ((u ++ u) ++ u) := by
  have substituted := Derives.subst basisPower (instantiateTwoWords u u)
  simpa [powerLaw, xx, xxx, w, instantiateTwoWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

theorem derivesLeftFold (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) ((u ++ u) ++ v) := by
  have substituted := Derives.subst basisLeftFold (instantiateTwoWords u v)
  simpa [leftFoldLaw, xyx, xxy, w, instantiateTwoWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

theorem derivesRightFold (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) ((v ++ u) ++ u) := by
  have substituted := Derives.subst basisRightFold (instantiateTwoWords u v)
  simpa [rightFoldLaw, xyx, yxx, w, instantiateTwoWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

end SemigroupBasis.CoRoots.S5_110
