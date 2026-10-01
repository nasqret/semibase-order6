import SemigroupBasis.FiniteReflection
import SemigroupBasis.Generated.CatalogueOrder5Part07
import SemigroupBasis.Opposite

namespace SemigroupBasis.CoRoots.S5_863

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
def xxyz : Word Nat := w 0 [0, 1, 2]
def xyxz : Word Nat := w 0 [1, 0, 2]

def powerLaw : Identity Nat := ⟨xx, xxx⟩
def leftEndpointDuplicationLaw : Identity Nat := ⟨xyx, xxyx⟩
def rightEndpointDuplicationLaw : Identity Nat := ⟨xyx, xyxx⟩
def squareInterleaveLaw : Identity Nat := ⟨xxyy, xyxy⟩
def doubledInitialMoveLaw : Identity Nat := ⟨xxyz, xyxz⟩

/-- The recorded five-law candidate basis of catalogue class `S5_863`. -/
def basis : List (Identity Nat) :=
  [powerLaw, leftEndpointDuplicationLaw, rightEndpointDuplicationLaw,
    squareInterleaveLaw, doubledInitialMoveLaw]

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

set_option maxRecDepth 100000 in
/-- The catalogue representative satisfies the exact five-law basis. -/
theorem catalogueModels :
    Models Generated.Catalogue.S5_863.table.semigroup basis :=
  models_of_finite_checks Generated.Catalogue.S5_863.table (by decide)

/-- The opposite catalogue representative satisfies the reversed basis. -/
theorem catalogueOppositeModels :
    Models Generated.Catalogue.S5_863.table.semigroup.opposite
      oppositeBasis := by
  simpa [oppositeBasis] using catalogueModels.oppositeReversed

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

private theorem basisDoubledInitialMove :
    Derives basis xxyz xyxz :=
  Derives.fromBasis (e := doubledInitialMoveLaw) <| by
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

end SemigroupBasis.CoRoots.S5_863
