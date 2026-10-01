import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite

namespace SemigroupBasis.CoRoots.S5_793

open SemigroupBasis

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def xx : Word Nat := w 0 [0]
def xxx : Word Nat := w 0 [0, 0]
def xyx : Word Nat := w 0 [1, 0]
def xxyx : Word Nat := w 0 [0, 1, 0]
def xyxx : Word Nat := w 0 [1, 0, 0]
def xxyy : Word Nat := w 0 [0, 1, 1]
def xyxy : Word Nat := w 0 [1, 0, 1]
def xyyx : Word Nat := w 0 [1, 1, 0]
def xyzx : Word Nat := w 0 [1, 2, 0]
def xyxzx : Word Nat := w 0 [1, 0, 2, 0]
def xyzy : Word Nat := w 0 [1, 2, 1]
def xzyy : Word Nat := w 0 [2, 1, 1]
def xyxzz : Word Nat := w 0 [1, 0, 2, 2]
def xyzzx : Word Nat := w 0 [1, 2, 2, 0]

def powerLaw : Identity Nat := ⟨xx, xxx⟩
def leftDuplicationLaw : Identity Nat := ⟨xyx, xxyx⟩
def rightDuplicationLaw : Identity Nat := ⟨xyx, xyxx⟩
def squareInterleaveLaw : Identity Nat := ⟨xxyy, xyxy⟩
def squareFinalSwitchLaw : Identity Nat := ⟨xxyy, xyyx⟩
def interiorInsertionLaw : Identity Nat := ⟨xyzx, xyxzx⟩
def prefixedGatherLaw : Identity Nat := ⟨xyzy, xzyy⟩
def headSquareRotationLaw : Identity Nat := ⟨xyxzz, xyzzx⟩

/-- The exact common basis recorded for `S5_793`, `S5_801`, and `S5_843`. -/
def basis : List (Identity Nat) :=
  [powerLaw, leftDuplicationLaw, rightDuplicationLaw,
    squareInterleaveLaw, squareFinalSwitchLaw, interiorInsertionLaw,
    prefixedGatherLaw, headSquareRotationLaw]

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

/-- Turn the finite three-variable checks for the eight displayed laws into
a `Models` theorem over the repository's standard `Nat` variables. -/
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

private theorem basisSquareInterleave :
    Derives basis xxyy xyxy :=
  Derives.fromBasis (e := squareInterleaveLaw) <| by
    simp [basis]

private theorem basisSquareFinalSwitch :
    Derives basis xxyy xyyx :=
  Derives.fromBasis (e := squareFinalSwitchLaw) <| by
    simp [basis]

private theorem basisInteriorInsertion :
    Derives basis xyzx xyxzx :=
  Derives.fromBasis (e := interiorInsertionLaw) <| by
    simp [basis]

private theorem basisPrefixedGather :
    Derives basis xyzy xzyy :=
  Derives.fromBasis (e := prefixedGatherLaw) <| by
    simp [basis]

private theorem basisHeadSquareRotation :
    Derives basis xyxzz xyzzx :=
  Derives.fromBasis (e := headSquareRotationLaw) <| by
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

theorem derivesSquareInterleave (u v : Word Nat) :
    Derives basis ((u ++ u) ++ (v ++ v))
      (((u ++ v) ++ u) ++ v) := by
  have substituted :=
    Derives.subst basisSquareInterleave
      (instantiateThreeWords u v v)
  simpa [xxyy, xyxy, w, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem derivesSquareFinalSwitch (u v : Word Nat) :
    Derives basis ((u ++ u) ++ (v ++ v))
      (((u ++ v) ++ v) ++ u) := by
  have substituted :=
    Derives.subst basisSquareFinalSwitch
      (instantiateThreeWords u v v)
  simpa [xxyy, xyyx, w, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem derivesInteriorInsertion (u v z : Word Nat) :
    Derives basis (((u ++ v) ++ z) ++ u)
      ((((u ++ v) ++ u) ++ z) ++ u) := by
  have substituted :=
    Derives.subst basisInteriorInsertion
      (instantiateThreeWords u v z)
  simpa [xyzx, xyxzx, w, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- After a fixed nonempty prefix, move the first copy of `u` across a
nonempty middle word and gather the two copies at the right endpoint. -/
theorem derivesPrefixedGather
    (pre u middle : Word Nat) :
    Derives basis (((pre ++ u) ++ middle) ++ u)
      (((pre ++ middle) ++ u) ++ u) := by
  have substituted :=
    Derives.subst basisPrefixedGather
      (instantiateThreeWords pre u middle)
  simpa [xyzy, xzyy, w, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- Move the repeated initial block across a square at the end of its
current simple-variable gap. -/
theorem derivesHeadAcrossSquare
    (head middle square : Word Nat) :
    Derives basis
      ((((head ++ middle) ++ head) ++ square) ++ square)
      ((((head ++ middle) ++ square) ++ square) ++ head) := by
  have substituted :=
    Derives.subst basisHeadSquareRotation
      (instantiateThreeWords head middle square)
  simpa [xyxzz, xyzzx, w, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- Delete the middle copy in `u v u z u = u v z u`. -/
theorem derivesThirdOccurrenceDeletion
    (u v z : Word Nat) :
    Derives basis ((((u ++ v) ++ u) ++ z) ++ u)
      (((u ++ v) ++ z) ++ u) := by
  exact Derives.symm <| by
    simpa [Word.append_assoc] using
      derivesInteriorInsertion u v z

/-- The two advertised laws
`x²y² = x y² x` and `P x U x = P U x²` commute two square blocks after
any nonempty prefix. -/
theorem derivesPrefixedSquareCommutation
    (pre u v : Word Nat) :
    Derives basis
      (pre ++ ((u ++ u) ++ (v ++ v)))
      (pre ++ ((v ++ v) ++ (u ++ u))) := by
  have first :=
    Derives.prepend pre (derivesSquareFinalSwitch u v)
  have second :=
    derivesPrefixedGather pre u (v ++ v)
  exact first.trans <| by
    simpa [Word.append_assoc] using second

end SemigroupBasis.CoRoots.S5_793
