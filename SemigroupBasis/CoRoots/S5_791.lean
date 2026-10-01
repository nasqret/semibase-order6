import SemigroupBasis.CoRoots.S5_107ListDerives
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite

namespace SemigroupBasis.CoRoots.S5_791

open SemigroupBasis

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def xx : Word Nat := w 0 [0]
def xxx : Word Nat := w 0 [0, 0]
def xyx : Word Nat := w 0 [1, 0]
def xxyx : Word Nat := w 0 [0, 1, 0]
def xyxx : Word Nat := w 0 [1, 0, 0]
def xyxy : Word Nat := w 0 [1, 0, 1]
def xyzx : Word Nat := w 0 [1, 2, 0]
def xyxzx : Word Nat := w 0 [1, 0, 2, 0]

def powerLaw : Identity Nat := ⟨xx, xxx⟩
def leftDuplicationLaw : Identity Nat := ⟨xyx, xxyx⟩
def rightDuplicationLaw : Identity Nat := ⟨xyx, xyxx⟩
def alternatingLaw : Identity Nat := ⟨xyx, xyxy⟩
def regularBandLaw : Identity Nat := ⟨xyzx, xyxzx⟩

/-- The common five-law basis for `S5_791` and `S5_807`:
`xx = xxx`, `xyx = xxyx`, `xyx = xyxx`, `xyx = xyxy`, and
`xyzx = xyxzx`. -/
def basis : List (Identity Nat) :=
  [powerLaw, leftDuplicationLaw, rightDuplicationLaw,
    alternatingLaw, regularBandLaw]

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

/-- Lift finite checks for the three variables occurring in the basis to a
`Models` theorem over natural-number variables. -/
theorem models_of_finite_checks
    (table : FiniteTable)
    (checked : finiteBasis.all table.checkIdentity = true) :
    Models table.semigroup basis := by
  intro identity member
  have finiteMember : identity.map toFinThree ∈ finiteBasis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    table.checkIdentityNat_sound (identity.map toFinThree)
      ((List.all_eq_true.mp checked) _ finiteMember)
  rw [basis_roundTrip identity member] at finiteValid
  exact finiteValid

private def instantiateThreeWords
    (u v z : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => z
  | n + 3 => Word.singleton (n + 3)

private theorem basisPower :
    Derives basis xx xxx :=
  Derives.fromBasis (e := powerLaw) <| by
    simp [basis]

private theorem basisLeftDuplication :
    Derives basis xyx xxyx :=
  Derives.fromBasis (e := leftDuplicationLaw) <| by
    simp [basis]

private theorem basisRightDuplication :
    Derives basis xyx xyxx :=
  Derives.fromBasis (e := rightDuplicationLaw) <| by
    simp [basis]

private theorem basisAlternating :
    Derives basis xyx xyxy :=
  Derives.fromBasis (e := alternatingLaw) <| by
    simp [basis]

private theorem basisRegularBand :
    Derives basis xyzx xyxzx :=
  Derives.fromBasis (e := regularBandLaw) <| by
    simp [basis]

theorem derivesPowerExpansion (u : Word Nat) :
    Derives basis (u ++ u) ((u ++ u) ++ u) := by
  have substituted :=
    Derives.subst basisPower (instantiateThreeWords u u u)
  simpa [xx, xxx, w, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem derivesLeftDuplication (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) (((u ++ u) ++ v) ++ u) := by
  have substituted :=
    Derives.subst basisLeftDuplication
      (instantiateThreeWords u v v)
  simpa [xyx, xxyx, w, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem derivesRightDuplication (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) (((u ++ v) ++ u) ++ u) := by
  have substituted :=
    Derives.subst basisRightDuplication
      (instantiateThreeWords u v v)
  simpa [xyx, xyxx, w, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem derivesAlternating (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) (((u ++ v) ++ u) ++ v) := by
  have substituted :=
    Derives.subst basisAlternating
      (instantiateThreeWords u v v)
  simpa [xyx, xyxy, w, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem derivesRegularExpansion (u v z : Word Nat) :
    Derives basis (((u ++ v) ++ z) ++ u)
      ((((u ++ v) ++ u) ++ z) ++ u) := by
  have substituted :=
    Derives.subst basisRegularBand
      (instantiateThreeWords u v z)
  simpa [xyzx, xyxzx, w, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem derivesRegularContraction (u v z : Word Nat) :
    Derives basis ((((u ++ v) ++ u) ++ z) ++ u)
      (((u ++ v) ++ z) ++ u) :=
  (derivesRegularExpansion u v z).symm

end SemigroupBasis.CoRoots.S5_791
