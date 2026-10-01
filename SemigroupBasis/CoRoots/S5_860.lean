import SemigroupBasis.CoRoots.S5_863

namespace SemigroupBasis.CoRoots.S5_860

open SemigroupBasis

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def xyzx : Word Nat := w 0 [1, 2, 0]
def xzyx : Word Nat := w 0 [2, 1, 0]
def xyzy : Word Nat := w 0 [1, 2, 1]
def xzyy : Word Nat := w 0 [2, 1, 1]
def xyzt : Word Nat := w 0 [1, 2, 3]
def xzyt : Word Nat := w 0 [2, 1, 3]

/-- The five-law prefix shared with the recorded basis of `S5_863`. -/
def sharedCore : List (Identity Nat) :=
  SemigroupBasis.CoRoots.S5_863.basis

def closedInteriorSwapLaw : Identity Nat := ⟨xyzx, xzyx⟩
def repeatedFinalSwapLaw : Identity Nat := ⟨xyzy, xzyy⟩
def interiorSwapLaw : Identity Nat := ⟨xyzt, xzyt⟩

/-- The exact eight-law candidate basis recorded for catalogue class
`S5_860`. -/
def basis : List (Identity Nat) :=
  sharedCore ++
    [closedInteriorSwapLaw, repeatedFinalSwapLaw, interiorSwapLaw]

def oppositeBasis : List (Identity Nat) :=
  reversedBasis basis

def toFinFour : Nat → Fin 4
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 3

def finiteBasis : List (Identity (Fin 4)) :=
  basis.map fun identity => identity.map toFinFour

private theorem basis_roundTrip_checked :
    basis.all (fun identity =>
      decide ((identity.map toFinFour).map Fin.val = identity)) = true := by
  decide

private theorem basis_roundTrip
    (identity : Identity Nat) (member : identity ∈ basis) :
    (identity.map toFinFour).map Fin.val = identity := by
  exact of_decide_eq_true <|
    (List.all_eq_true.mp basis_roundTrip_checked) identity member

/-- Lift exhaustive checks on the four displayed variables to a `Models`
theorem over natural-number variables. -/
theorem models_of_finite_checks
    (table : FiniteTable)
    (checked : finiteBasis.all table.checkIdentity = true) :
    Models table.semigroup basis := by
  intro identity member
  have finiteMember : identity.map toFinFour ∈ finiteBasis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    table.checkIdentityNat_sound (identity.map toFinFour)
      ((List.all_eq_true.mp checked) _ finiteMember)
  rw [basis_roundTrip identity member] at finiteValid
  exact finiteValid

set_option maxRecDepth 100000 in
/-- The catalogue representative satisfies all eight recorded laws. -/
theorem catalogueModels :
    Models Generated.Catalogue.S5_860.table.semigroup basis :=
  models_of_finite_checks Generated.Catalogue.S5_860.table (by decide)

/-- The opposite catalogue representative satisfies the reversed laws. -/
theorem catalogueOppositeModels :
    Models Generated.Catalogue.S5_860.table.semigroup.opposite
      oppositeBasis := by
  simpa [oppositeBasis] using catalogueModels.oppositeReversed

private def instantiateFourWords
    (u v z t : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => z
  | 3 => t
  | n + 4 => Word.singleton (n + 4)

private theorem basisClosedInteriorSwap :
    Derives basis xyzx xzyx :=
  Derives.fromBasis (e := closedInteriorSwapLaw) <| by
    simp [basis]

private theorem basisRepeatedFinalSwap :
    Derives basis xyzy xzyy :=
  Derives.fromBasis (e := repeatedFinalSwapLaw) <| by
    simp [basis]

private theorem basisInteriorSwap :
    Derives basis xyzt xzyt :=
  Derives.fromBasis (e := interiorSwapLaw) <| by
    simp [basis]

/-- Swap arbitrary adjacent blocks inside equal nonempty endpoint blocks. -/
theorem derivesClosedInteriorSwap (u v z : Word Nat) :
    Derives basis
      (((u ++ v) ++ z) ++ u)
      (((u ++ z) ++ v) ++ u) := by
  have substituted :=
    Derives.subst basisClosedInteriorSwap
      (instantiateFourWords u v z u)
  simpa [closedInteriorSwapLaw, xyzx, xzyx, w,
    instantiateFourWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Swap arbitrary adjacent blocks when the final block repeats the first
interior block. -/
theorem derivesRepeatedFinalSwap (u v z : Word Nat) :
    Derives basis
      (((u ++ v) ++ z) ++ v)
      (((u ++ z) ++ v) ++ v) := by
  have substituted :=
    Derives.subst basisRepeatedFinalSwap
      (instantiateFourWords u v z v)
  simpa [repeatedFinalSwapLaw, xyzy, xzyy, w,
    instantiateFourWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Swap arbitrary adjacent blocks between arbitrary nonempty endpoint
blocks. -/
theorem derivesInteriorSwap (u v z t : Word Nat) :
    Derives basis
      (((u ++ v) ++ z) ++ t)
      (((u ++ z) ++ v) ++ t) := by
  have substituted :=
    Derives.subst basisInteriorSwap
      (instantiateFourWords u v z t)
  simpa [interiorSwapLaw, xyzt, xzyt, w, instantiateFourWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

end SemigroupBasis.CoRoots.S5_860
