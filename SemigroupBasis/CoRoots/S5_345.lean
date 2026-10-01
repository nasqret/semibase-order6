import SemigroupBasis.CoRoots.S5_107ListDerives
import SemigroupBasis.FiniteReflection

namespace SemigroupBasis.CoRoots.S5_345

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
def xxyz : Word Nat := w 0 [0, 1, 2]
def xyxz : Word Nat := w 0 [1, 0, 2]
def xxyzy : Word Nat := w 0 [0, 1, 2, 1]
def xyyzx : Word Nat := w 0 [1, 1, 2, 0]
def xxyzz : Word Nat := w 0 [0, 1, 2, 2]
def xyzzx : Word Nat := w 0 [1, 2, 2, 0]

def powerLaw : Identity Nat := ⟨xx, xxx⟩
def leftEndpointDuplicationLaw : Identity Nat := ⟨xyx, xxyx⟩
def rightEndpointDuplicationLaw : Identity Nat := ⟨xyx, xyxx⟩
def squareInterleaveLaw : Identity Nat := ⟨xxyy, xyxy⟩
def squareFinalSwitchLaw : Identity Nat := ⟨xxyy, xyyx⟩
def doubledInitialMoveLaw : Identity Nat := ⟨xxyz, xyxz⟩
def openTerminalSwitchLaw : Identity Nat := ⟨xxyzy, xyyzx⟩
def closedTerminalSwitchLaw : Identity Nat := ⟨xxyzz, xyzzx⟩

/-- The common exact eight-identity basis of
`S5_345`, `S5_374`, and `S5_593`. -/
def basis : List (Identity Nat) :=
  [powerLaw, leftEndpointDuplicationLaw, rightEndpointDuplicationLaw,
    squareInterleaveLaw, squareFinalSwitchLaw, doubledInitialMoveLaw,
    openTerminalSwitchLaw, closedTerminalSwitchLaw]

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

private theorem basisLeftEndpointDuplication :
    Derives basis xyx xxyx :=
  Derives.fromBasis (e := leftEndpointDuplicationLaw) <| by
    simp [basis]

private theorem basisRightEndpointDuplication :
    Derives basis xyx xyxx :=
  Derives.fromBasis (e := rightEndpointDuplicationLaw) <| by
    simp [basis]

private theorem basisSquareInterleave :
    Derives basis xxyy xyxy :=
  Derives.fromBasis (e := squareInterleaveLaw) <| by
    simp [basis]

private theorem basisSquareFinalSwitch :
    Derives basis xxyy xyyx :=
  Derives.fromBasis (e := squareFinalSwitchLaw) <| by
    simp [basis]

private theorem basisDoubledInitialMove :
    Derives basis xxyz xyxz :=
  Derives.fromBasis (e := doubledInitialMoveLaw) <| by
    simp [basis]

private theorem basisOpenTerminalSwitch :
    Derives basis xxyzy xyyzx :=
  Derives.fromBasis (e := openTerminalSwitchLaw) <| by
    simp [basis]

private theorem basisClosedTerminalSwitch :
    Derives basis xxyzz xyzzx :=
  Derives.fromBasis (e := closedTerminalSwitchLaw) <| by
    simp [basis]

/-- Contract three consecutive copies of a nonempty block to two. -/
theorem derivesPowerContraction (u : Word Nat) :
    Derives basis ((u ++ u) ++ u) (u ++ u) := by
  have substituted :=
    Derives.subst basisPower.symm
      (instantiateThreeWords u u u)
  simpa [powerLaw, xx, xxx, w, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- Duplicate the left occurrence of a repeated endpoint. -/
theorem derivesLeftEndpointExpansion (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) (((u ++ u) ++ v) ++ u) := by
  have substituted :=
    Derives.subst basisLeftEndpointDuplication
      (instantiateThreeWords u v v)
  simpa [leftEndpointDuplicationLaw, xyx, xxyx, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Duplicate the right occurrence of a repeated endpoint. -/
theorem derivesRightEndpointExpansion (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) (((u ++ v) ++ u) ++ u) := by
  have substituted :=
    Derives.subst basisRightEndpointDuplication
      (instantiateThreeWords u v v)
  simpa [rightEndpointDuplicationLaw, xyx, xyxx, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Interleave two adjacent nonempty squares. -/
theorem derivesSquareInterleave (u v : Word Nat) :
    Derives basis
      ((u ++ u) ++ (v ++ v))
      (((u ++ v) ++ u) ++ v) := by
  have substituted :=
    Derives.subst basisSquareInterleave
      (instantiateThreeWords u v v)
  simpa [squareInterleaveLaw, xxyy, xyxy, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Replace adjacent squares by a square at the second letter followed by
the first letter as a terminal marker. -/
theorem derivesSquareFinalSwitch (u v : Word Nat) :
    Derives basis
      ((u ++ u) ++ (v ++ v))
      (((u ++ v) ++ v) ++ u) := by
  have substituted :=
    Derives.subst basisSquareFinalSwitch
      (instantiateThreeWords u v v)
  simpa [squareFinalSwitchLaw, xxyy, xyyx, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Move one copy of a doubled initial block across a nonempty middle block. -/
theorem derivesDoubledInitialMove (u v z : Word Nat) :
    Derives basis
      (((u ++ u) ++ v) ++ z)
      (((u ++ v) ++ u) ++ z) := by
  have substituted :=
    Derives.subst basisDoubledInitialMove
      (instantiateThreeWords u v z)
  simpa [doubledInitialMoveLaw, xxyz, xyxz, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Switch a doubled initial block with a repeated terminal letter when the
intervening right context is nonempty. -/
theorem derivesOpenTerminalSwitch (u v z : Word Nat) :
    Derives basis
      ((((u ++ u) ++ v) ++ z) ++ v)
      ((((u ++ v) ++ v) ++ z) ++ u) := by
  have substituted :=
    Derives.subst basisOpenTerminalSwitch
      (instantiateThreeWords u v z)
  simpa [openTerminalSwitchLaw, xxyzy, xyyzx, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Switch a doubled initial block with a terminal square. -/
theorem derivesClosedTerminalSwitch (u v z : Word Nat) :
    Derives basis
      (((u ++ u) ++ v) ++ (z ++ z))
      ((((u ++ v) ++ z) ++ z) ++ u) := by
  have substituted :=
    Derives.subst basisClosedTerminalSwitch
      (instantiateThreeWords u v z)
  simpa [closedTerminalSwitchLaw, xxyzz, xyzzx, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

private def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

/-- The executable three-variable image of the common eight-law basis. -/
def finiteBasis : List (Identity (Fin 3)) :=
  basis.map fun identity => identity.map toFinThree

private theorem basisRoundTripChecked :
    basis.all (fun identity =>
      decide ((identity.map toFinThree).map Fin.val = identity)) = true := by
  decide

private theorem basisRoundTrip
    (identity : Identity Nat) (member : identity ∈ basis) :
    (identity.map toFinThree).map Fin.val = identity := by
  exact of_decide_eq_true <|
    (List.all_eq_true.mp basisRoundTripChecked) identity member

/-- A finite table models the eight laws once their three-variable images
pass the executable finite-table checker. -/
theorem modelsOfFiniteChecks
    (table : FiniteTable)
    (checked : finiteBasis.all table.checkIdentity = true) :
    Models table.semigroup basis := by
  intro identity member
  have finiteMember : identity.map toFinThree ∈ finiteBasis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    table.checkIdentityNat_sound (identity.map toFinThree)
      ((List.all_eq_true.mp checked) _ finiteMember)
  rw [basisRoundTrip identity member] at finiteValid
  exact finiteValid

end SemigroupBasis.CoRoots.S5_345
