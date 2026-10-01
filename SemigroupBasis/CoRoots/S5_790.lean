import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite

namespace SemigroupBasis.CoRoots.S5_790

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
def xzyx : Word Nat := w 0 [2, 1, 0]
def xyzy : Word Nat := w 0 [1, 2, 1]
def xzyz : Word Nat := w 0 [2, 1, 2]

def powerLaw : Identity Nat := ⟨xx, xxx⟩
def leftDuplicationLaw : Identity Nat := ⟨xyx, xxyx⟩
def rightDuplicationLaw : Identity Nat := ⟨xyx, xyxx⟩
def alternatingLaw : Identity Nat := ⟨xyx, xyxy⟩
def closedInteriorSwapLaw : Identity Nat := ⟨xyzx, xzyx⟩
def prefixedRotationLaw : Identity Nat := ⟨xyzy, xzyz⟩

/-- The common six-law basis for `S5_790`, `S5_792`, and `S5_798`:
`xx = xxx`, `xyx = xxyx`, `xyx = xyxx`, `xyx = xyxy`,
`xyzx = xzyx`, and `xyzy = xzyz`. -/
def basis : List (Identity Nat) :=
  [powerLaw, leftDuplicationLaw, rightDuplicationLaw, alternatingLaw,
    closedInteriorSwapLaw, prefixedRotationLaw]

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

/-- Turn the finite checks for the three variables in the basis into a
`Models` theorem over `Nat` variables. -/
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

private theorem basisClosedInteriorSwap :
    Derives basis xyzx xzyx :=
  Derives.fromBasis (e := closedInteriorSwapLaw) <| by
    simp [basis]

private theorem basisPrefixedRotation :
    Derives basis xyzy xzyz :=
  Derives.fromBasis (e := prefixedRotationLaw) <| by
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

theorem derivesClosedInteriorSwap (u v z : Word Nat) :
    Derives basis (((u ++ v) ++ z) ++ u)
      (((u ++ z) ++ v) ++ u) := by
  have substituted :=
    Derives.subst basisClosedInteriorSwap
      (instantiateThreeWords u v z)
  simpa [xyzx, xzyx, w, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- After a fixed nonempty prefix, the last basis law replays the endpoint
rotation `uvu = vuv` without changing the global first variable. -/
theorem derivesPrefixedRotation (pref u v : Word Nat) :
    Derives basis (((pref ++ u) ++ v) ++ u)
      (((pref ++ v) ++ u) ++ v) := by
  have substituted :=
    Derives.subst basisPrefixedRotation
      (instantiateThreeWords pref u v)
  simpa [xyzy, xzyz, w, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- The advertised chain
`xyx = xyxx = xyxyx = xxyyx = xyyx` derives the missing middle
duplication law of the `S4_70` basis. -/
theorem derivesMiddleDuplication (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) (((u ++ v) ++ v) ++ u) := by
  have first :=
    derivesRightDuplication u v
  have second :=
    Derives.appendRight (derivesAlternating u v) u
  have third :=
    derivesClosedInteriorSwap u v (u ++ v)
  have fourth :=
    Derives.symm (derivesLeftDuplication u (v ++ v))
  exact Derives.trans first <|
    Derives.trans
      (by simpa [Word.append_assoc] using second) <|
      Derives.trans
        (by simpa [Word.append_assoc] using third)
        (by simpa [Word.append_assoc] using fourth)

end SemigroupBasis.CoRoots.S5_790
