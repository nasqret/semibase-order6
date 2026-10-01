import SemigroupBasis.FiniteReflection
import SemigroupBasis.Generated.CatalogueOrder5Part06
import SemigroupBasis.Opposite

namespace SemigroupBasis.CoRoots.S5_730

open SemigroupBasis

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def xx : Word Nat := w 0 [0]
def xxx : Word Nat := w 0 [0, 0]
def xy : Word Nat := w 0 [1]
def xxy : Word Nat := w 0 [0, 1]
def xyz : Word Nat := w 0 [1, 2]
def xyxz : Word Nat := w 0 [1, 0, 2]
def xyx : Word Nat := w 0 [1, 0]
def xyxx : Word Nat := w 0 [1, 0, 0]
def xyzx : Word Nat := w 0 [1, 2, 0]
def xzyx : Word Nat := w 0 [2, 1, 0]
def xyzt : Word Nat := w 0 [1, 2, 3]
def xzyt : Word Nat := w 0 [2, 1, 3]

def leftDuplicationLaw : Identity Nat := ⟨xy, xxy⟩
def returnDuplicationLaw : Identity Nat := ⟨xyz, xyxz⟩
def closedInteriorSwapLaw : Identity Nat := ⟨xyzx, xzyx⟩

/-- The exact ordered law list recorded for catalogue class `S5_730`.
This definition makes no normal-form or completeness claim. -/
def basis : List (Identity Nat) :=
  [leftDuplicationLaw, returnDuplicationLaw, closedInteriorSwapLaw]

def oppositeBasis : List (Identity Nat) :=
  reversedBasis basis

private def toFinThree : Nat → Fin 3
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

/-- Exhaustive checks on the three variables displayed in the basis imply
the corresponding `Models` theorem over natural-number variables. -/
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

abbrev table : FiniteTable :=
  Generated.Catalogue.S5_730.table

set_option maxRecDepth 100000 in
/-- The generated catalogue representative satisfies the three recorded
laws. -/
theorem models : Models table.semigroup basis :=
  models_of_finite_checks table (by decide)

/-- The opposite catalogue representative satisfies the reversed laws. -/
theorem oppositeModels :
    Models table.semigroup.opposite oppositeBasis :=
  models.oppositeReversed

private def instantiateThreeWords
    (u v z : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => z
  | n + 3 => Word.singleton (n + 3)

private theorem basisLeftDuplication :
    Derives basis xy xxy :=
  Derives.fromBasis (e := leftDuplicationLaw) <| by
    simp [basis]

private theorem basisReturnDuplication :
    Derives basis xyz xyxz :=
  Derives.fromBasis (e := returnDuplicationLaw) <| by
    simp [basis]

private theorem basisClosedInteriorSwap :
    Derives basis xyzx xzyx :=
  Derives.fromBasis (e := closedInteriorSwapLaw) <| by
    simp [basis]

/-- Direct block substitution in `xy = xxy`. -/
theorem derivesLeftDuplication (u v : Word Nat) :
    Derives basis (u ++ v) ((u ++ u) ++ v) := by
  have substituted :=
    Derives.subst basisLeftDuplication
      (instantiateThreeWords u v v)
  simpa [leftDuplicationLaw, xy, xxy, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

/-- Direct block substitution in `xyz = xyxz`. -/
theorem derivesReturnDuplication (u v z : Word Nat) :
    Derives basis
      ((u ++ v) ++ z)
      (((u ++ v) ++ u) ++ z) := by
  have substituted :=
    Derives.subst basisReturnDuplication
      (instantiateThreeWords u v z)
  simpa [returnDuplicationLaw, xyz, xyxz, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

/-- Direct block substitution in `xyzx = xzyx`. -/
theorem derivesClosedInteriorSwap (u v z : Word Nat) :
    Derives basis
      (((u ++ v) ++ z) ++ u)
      (((u ++ z) ++ v) ++ u) := by
  have substituted :=
    Derives.subst basisClosedInteriorSwap
      (instantiateThreeWords u v z)
  simpa [closedInteriorSwapLaw, xyzx, xzyx, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- The derived power expansion `xx = xxx`. -/
theorem derivesPowerExpansion (u : Word Nat) :
    Derives basis (u ++ u) ((u ++ u) ++ u) :=
  derivesLeftDuplication u u

/-- The derived right-endpoint expansion `xyx = xyxx`. -/
theorem derivesRightEndpointExpansion (u v : Word Nat) :
    Derives basis
      ((u ++ v) ++ u)
      (((u ++ v) ++ u) ++ u) :=
  derivesReturnDuplication u v u

/-- Derive the open interior swap `xyzt = xzyt`: insert the initial block
before the suffix with `xyz = xyxz`, use `xyzx = xzyx` under that suffix,
then contract the inserted block with `xyz = xyxz` in reverse. -/
theorem derivesInteriorSwap (u v z t : Word Nat) :
    Derives basis
      (((u ++ v) ++ z) ++ t)
      (((u ++ z) ++ v) ++ t) := by
  have insertInitial :=
    derivesReturnDuplication u (v ++ z) t
  have swapInside :=
    Derives.appendRight (derivesClosedInteriorSwap u v z) t
  have contractInitial :=
    (derivesReturnDuplication u (z ++ v) t).symm
  apply Derives.trans
  · simpa [Word.append_assoc] using insertInitial
  · apply Derives.trans
    · simpa [Word.append_assoc] using swapInside
    · simpa [Word.append_assoc] using contractInitial

end SemigroupBasis.CoRoots.S5_730
