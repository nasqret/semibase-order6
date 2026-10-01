import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite

namespace SemigroupBasis.CoRoots.S5_787

open SemigroupBasis

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def xx : Word Nat := w 0 [0]
def xxx : Word Nat := w 0 [0, 0]
def xyx : Word Nat := w 0 [1, 0]
def xxyx : Word Nat := w 0 [0, 1, 0]
def xxyy : Word Nat := w 0 [0, 1, 1]
def xyzx : Word Nat := w 0 [1, 2, 0]
def xzyx : Word Nat := w 0 [2, 1, 0]
def xyzy : Word Nat := w 0 [1, 2, 1]
def xzyz : Word Nat := w 0 [2, 1, 2]

def powerLaw : Identity Nat := ⟨xx, xxx⟩
def leftDuplicationLaw : Identity Nat := ⟨xyx, xxyx⟩
def squaresLaw : Identity Nat := ⟨xyx, xxyy⟩
def closedInteriorSwapLaw : Identity Nat := ⟨xyzx, xzyx⟩
def prefixedRotationLaw : Identity Nat := ⟨xyzy, xzyz⟩

/-- The common five-law candidate basis for `S5_787`, `S5_789`, and
`S5_796`:
`xx = xxx`, `xyx = xxyx`, `xyx = xxyy`, `xyzx = xzyx`, and
`xyzy = xzyz`. -/
def basis : List (Identity Nat) :=
  [powerLaw, leftDuplicationLaw, squaresLaw, closedInteriorSwapLaw,
    prefixedRotationLaw]

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

/-- Reduce a finite model check on the three variables occurring in the
candidate basis to a `Models` theorem over `Nat` variables. -/
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

private theorem basisSquares :
    Derives basis xyx xxyy :=
  Derives.fromBasis (e := squaresLaw) <| by
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

theorem derivesSquares (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) ((u ++ u) ++ (v ++ v)) := by
  have substituted :=
    Derives.subst basisSquares (instantiateThreeWords u v v)
  simpa [xyx, xxyy, w, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem derivesClosedInteriorSwap (u v z : Word Nat) :
    Derives basis (((u ++ v) ++ z) ++ u)
      (((u ++ z) ++ v) ++ u) := by
  have substituted :=
    Derives.subst basisClosedInteriorSwap
      (instantiateThreeWords u v z)
  simpa [xyzx, xzyx, w, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- After a nonempty prefix, the final law supplies the rotation
`Puvu = Pvuv`. This is the operation that permits later separator gaps to
choose a canonical endpoint without changing the global first variable. -/
theorem derivesPrefixedRotation (pre u v : Word Nat) :
    Derives basis (((pre ++ u) ++ v) ++ u)
      (((pre ++ v) ++ u) ++ v) := by
  have substituted :=
    Derives.subst basisPrefixedRotation
      (instantiateThreeWords pre u v)
  simpa [xyzy, xzyz, w, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- The advertised two-step chain `xyx = xxyx = xyxx`. -/
theorem derivesRightDuplication (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) (((u ++ v) ++ u) ++ u) := by
  exact Derives.trans (derivesLeftDuplication u v) <| by
    simpa [Word.append_assoc] using
      derivesClosedInteriorSwap u u v

/-- The advertised two-step chain `xyx = xxyx = xyxy`. -/
theorem derivesAlternatingExtension (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) (((u ++ v) ++ u) ++ v) := by
  exact Derives.trans (derivesLeftDuplication u v) <| by
    simpa [Word.append_assoc] using
      derivesPrefixedRotation u u v

/-- The advertised chain
`xyx = xxyx = xyxx = xxyyx = xyyx`, deriving the missing middle
duplication law from the five-law basis. -/
theorem derivesMiddleDuplication (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) (((u ++ v) ++ v) ++ u) := by
  have first := derivesLeftDuplication u v
  have second := derivesClosedInteriorSwap u u v
  have third :=
    Derives.appendRight (derivesSquares u v) u
  have fourth :=
    Derives.symm (derivesLeftDuplication u (v ++ v))
  exact Derives.trans first <|
    Derives.trans
      (by simpa [Word.append_assoc] using second) <|
      Derives.trans
        (by simpa [Word.append_assoc] using third)
        (by simpa [Word.append_assoc] using fourth)

/-- Delete the middle copy in `uvuwu = uvwu`. -/
theorem derivesThirdOccurrenceDeletion
    (u v w : Word Nat) :
    Derives basis ((((u ++ v) ++ u) ++ w) ++ u)
      (((u ++ v) ++ w) ++ u) := by
  have first :=
    derivesClosedInteriorSwap u v (u ++ w)
  have second :=
    Derives.symm (derivesLeftDuplication u (w ++ v))
  have third :=
    derivesClosedInteriorSwap u w v
  exact Derives.trans
    (by simpa [Word.append_assoc] using first) <|
      Derives.trans
        (by simpa [Word.append_assoc] using second)
        (by simpa [Word.append_assoc] using third)

/-- Merge the shortest crossing pair, `uvuzv = uvzu`. -/
theorem derivesShortCrossingAbsorption
    (u v z : Word Nat) :
    Derives basis ((((u ++ v) ++ u) ++ z) ++ v)
      (((u ++ v) ++ z) ++ u) := by
  have first :=
    Derives.appendRight (derivesSquares u v) (z ++ v)
  have second :=
    derivesPrefixedRotation ((u ++ u) ++ v) v z
  have third :=
    Derives.symm (derivesSquares u (v ++ z))
  exact Derives.trans
    (by simpa [Word.append_assoc] using first) <|
      Derives.trans
        (by simpa [Word.append_assoc] using second)
        (by simpa [Word.append_assoc] using third)

end SemigroupBasis.CoRoots.S5_787
