import SemigroupBasis.FiniteReflection
import SemigroupBasis.Generated.CatalogueOrder5Part07
import SemigroupBasis.Opposite

namespace SemigroupBasis.CoRoots.S5_806

open SemigroupBasis

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def xx : Word Nat := w 0 [0]
def xxx : Word Nat := w 0 [0, 0]
def xyx : Word Nat := w 0 [1, 0]
def xxyx : Word Nat := w 0 [0, 1, 0]
def xyxx : Word Nat := w 0 [1, 0, 0]
def xyyx : Word Nat := w 0 [1, 1, 0]
def yxyx : Word Nat := w 1 [0, 1, 0]
def xyzx : Word Nat := w 0 [1, 2, 0]
def xzyx : Word Nat := w 0 [2, 1, 0]
def xyyzx : Word Nat := w 0 [1, 1, 2, 0]
def xyxz : Word Nat := w 0 [1, 0, 2]
def yxyz : Word Nat := w 1 [0, 1, 2]

def powerLaw : Identity Nat := ⟨xx, xxx⟩
def leftEndpointDuplicationLaw : Identity Nat := ⟨xyx, xxyx⟩
def rightEndpointDuplicationLaw : Identity Nat := ⟨xyx, xyxx⟩
def middleDuplicationLaw : Identity Nat := ⟨xyx, xyyx⟩
def prefixedSandwichLaw : Identity Nat := ⟨xyx, yxyx⟩
def closedInteriorSwapLaw : Identity Nat := ⟨xyzx, xzyx⟩
def closedMiddleDuplicationLaw : Identity Nat := ⟨xyzx, xyyzx⟩
def finalRotationLaw : Identity Nat := ⟨xyxz, yxyz⟩

/-- The exact eight-law basis recorded for catalogue class `S5_806`, in
catalogue order. -/
def basis : List (Identity Nat) :=
  [powerLaw, leftEndpointDuplicationLaw, rightEndpointDuplicationLaw,
    middleDuplicationLaw, prefixedSandwichLaw, closedInteriorSwapLaw,
    closedMiddleDuplicationLaw, finalRotationLaw]

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

/-- Lift finite checks for the three variables displayed in the basis to a
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
/-- The catalogue representative satisfies the exact eight-law basis. -/
theorem catalogueModels :
    Models Generated.Catalogue.S5_806.table.semigroup basis :=
  models_of_finite_checks Generated.Catalogue.S5_806.table (by decide)

/-- The opposite catalogue representative satisfies the reversed basis. -/
theorem catalogueOppositeModels :
    Models Generated.Catalogue.S5_806.table.semigroup.opposite
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

private theorem basisMiddleDuplication :
    Derives basis xyx xyyx :=
  Derives.fromBasis (e := middleDuplicationLaw) <| by
    simp [basis]

private theorem basisPrefixedSandwich :
    Derives basis xyx yxyx :=
  Derives.fromBasis (e := prefixedSandwichLaw) <| by
    simp [basis]

private theorem basisClosedInteriorSwap :
    Derives basis xyzx xzyx :=
  Derives.fromBasis (e := closedInteriorSwapLaw) <| by
    simp [basis]

private theorem basisClosedMiddleDuplication :
    Derives basis xyzx xyyzx :=
  Derives.fromBasis (e := closedMiddleDuplicationLaw) <| by
    simp [basis]

private theorem basisFinalRotation :
    Derives basis xyxz yxyz :=
  Derives.fromBasis (e := finalRotationLaw) <| by
    simp [basis]

/-- Substitute one arbitrary nonempty word into `xx = xxx`. -/
theorem derivesPowerExpansion (u : Word Nat) :
    Derives basis (u ++ u) ((u ++ u) ++ u) := by
  have substituted :=
    Derives.subst basisPower (instantiateThreeWords u u u)
  simpa [powerLaw, xx, xxx, w, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- Substitute arbitrary nonempty words into `xyx = xxyx`. -/
theorem derivesLeftEndpointExpansion (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) (((u ++ u) ++ v) ++ u) := by
  have substituted :=
    Derives.subst basisLeftEndpointDuplication
      (instantiateThreeWords u v v)
  simpa [leftEndpointDuplicationLaw, xyx, xxyx, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Substitute arbitrary nonempty words into `xyx = xyxx`. -/
theorem derivesRightEndpointExpansion (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) (((u ++ v) ++ u) ++ u) := by
  have substituted :=
    Derives.subst basisRightEndpointDuplication
      (instantiateThreeWords u v v)
  simpa [rightEndpointDuplicationLaw, xyx, xyxx, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Substitute arbitrary nonempty words into `xyx = xyyx`. -/
theorem derivesMiddleDuplication (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) (((u ++ v) ++ v) ++ u) := by
  have substituted :=
    Derives.subst basisMiddleDuplication (instantiateThreeWords u v v)
  simpa [middleDuplicationLaw, xyx, xyyx, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

/-- Substitute arbitrary nonempty words into `xyx = yxyx`. -/
theorem derivesPrefixedSandwich (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) (((v ++ u) ++ v) ++ u) := by
  have substituted :=
    Derives.subst basisPrefixedSandwich (instantiateThreeWords u v v)
  simpa [prefixedSandwichLaw, xyx, yxyx, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

/-- Substitute arbitrary nonempty words into `xyzx = xzyx`. -/
theorem derivesClosedInteriorSwap (u v z : Word Nat) :
    Derives basis
      (((u ++ v) ++ z) ++ u)
      (((u ++ z) ++ v) ++ u) := by
  have substituted :=
    Derives.subst basisClosedInteriorSwap (instantiateThreeWords u v z)
  simpa [closedInteriorSwapLaw, xyzx, xzyx, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

/-- Substitute arbitrary nonempty words into `xyzx = xyyzx`. -/
theorem derivesClosedMiddleDuplication (u v z : Word Nat) :
    Derives basis
      (((u ++ v) ++ z) ++ u)
      ((((u ++ v) ++ v) ++ z) ++ u) := by
  have substituted :=
    Derives.subst basisClosedMiddleDuplication
      (instantiateThreeWords u v z)
  simpa [closedMiddleDuplicationLaw, xyzx, xyyzx, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Substitute arbitrary nonempty words into the S5_806 eighth law
`xyxz = yxyz`. -/
theorem derivesFinalRotation (u v z : Word Nat) :
    Derives basis
      (((u ++ v) ++ u) ++ z)
      (((v ++ u) ++ v) ++ z) := by
  have substituted :=
    Derives.subst basisFinalRotation (instantiateThreeWords u v z)
  simpa [finalRotationLaw, xyxz, yxyz, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

end SemigroupBasis.CoRoots.S5_806
