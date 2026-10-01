import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite

namespace SemigroupBasis.CoRoots.S5_869

open SemigroupBasis

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def xx : Word Nat := w 0 [0]
def xxx : Word Nat := w 0 [0, 0]
def xy : Word Nat := w 0 [1]
def xyy : Word Nat := w 0 [1, 1]
def xxy : Word Nat := w 0 [0, 1]
def xxyx : Word Nat := w 0 [0, 1, 0]
def xyxz : Word Nat := w 0 [1, 0, 2]
def xyxzx : Word Nat := w 0 [1, 0, 2, 0]

def powerLaw : Identity Nat := ⟨xx, xxx⟩
def tailDuplicationLaw : Identity Nat := ⟨xy, xyy⟩
def squaredPrefixLaw : Identity Nat := ⟨xxy, xxyx⟩
def initialGapLaw : Identity Nat := ⟨xyxz, xyxzx⟩

/-- The common four-law basis planned for `S5_869` and `S5_871`. -/
def basis : List (Identity Nat) :=
  [powerLaw, tailDuplicationLaw, squaredPrefixLaw, initialGapLaw]

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

/-- Lift finite checks for the variables occurring in the basis to a
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

private theorem basisTailDuplication :
    Derives basis xy xyy :=
  Derives.fromBasis (e := tailDuplicationLaw) <| by
    simp [basis]

private theorem basisSquaredPrefix :
    Derives basis xxy xxyx :=
  Derives.fromBasis (e := squaredPrefixLaw) <| by
    simp [basis]

private theorem basisInitialGap :
    Derives basis xyxz xyxzx :=
  Derives.fromBasis (e := initialGapLaw) <| by
    simp [basis]

theorem derivesPowerExpansion (u : Word Nat) :
    Derives basis (u ++ u) ((u ++ u) ++ u) := by
  have substituted :=
    Derives.subst basisPower (instantiateThreeWords u u u)
  simpa [xx, xxx, w, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem derivesPowerContraction (u : Word Nat) :
    Derives basis ((u ++ u) ++ u) (u ++ u) :=
  (derivesPowerExpansion u).symm

theorem derivesTailExpansion (u v : Word Nat) :
    Derives basis (u ++ v) ((u ++ v) ++ v) := by
  have substituted :=
    Derives.subst basisTailDuplication
      (instantiateThreeWords u v v)
  simpa [xy, xyy, w, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem derivesTailContraction (u v : Word Nat) :
    Derives basis ((u ++ v) ++ v) (u ++ v) :=
  (derivesTailExpansion u v).symm

theorem derivesSquaredPrefixExpansion (u v : Word Nat) :
    Derives basis ((u ++ u) ++ v) (((u ++ u) ++ v) ++ u) := by
  have substituted :=
    Derives.subst basisSquaredPrefix
      (instantiateThreeWords u v v)
  simpa [xxy, xxyx, w, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem derivesSquaredPrefixContraction (u v : Word Nat) :
    Derives basis (((u ++ u) ++ v) ++ u) ((u ++ u) ++ v) :=
  (derivesSquaredPrefixExpansion u v).symm

theorem derivesInitialGapExpansion (u v z : Word Nat) :
    Derives basis (((u ++ v) ++ u) ++ z)
      ((((u ++ v) ++ u) ++ z) ++ u) := by
  have substituted :=
    Derives.subst basisInitialGap
      (instantiateThreeWords u v z)
  simpa [xyxz, xyxzx, w, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem derivesInitialGapContraction (u v z : Word Nat) :
    Derives basis ((((u ++ v) ++ u) ++ z) ++ u)
      (((u ++ v) ++ u) ++ z) :=
  (derivesInitialGapExpansion u v z).symm

/-- Delete a repeated noninitial block when both surrounding contexts are
nonempty: `P a Q a = P a Q`. -/
theorem derivesNoninitialRepeatDeletion (p a q : Word Nat) :
    Derives basis (((p ++ a) ++ q) ++ a) ((p ++ a) ++ q) := by
  have duplicate :=
    Derives.appendRight (derivesTailExpansion p a) (q ++ a)
  have deleteLast :=
    Derives.prepend p (derivesSquaredPrefixContraction a q)
  have contract :=
    Derives.appendRight (derivesTailContraction p a) q
  exact Derives.trans
    (by simpa [Word.append_assoc] using duplicate) <|
    Derives.trans
      (by simpa [Word.append_assoc] using deleteLast)
      (by simpa [Word.append_assoc] using contract)

/-- Delete a third initial block when both interiors are nonempty. -/
theorem derivesInitialExcessDeletion (x a b : Word Nat) :
    Derives basis ((((x ++ a) ++ x) ++ b) ++ x)
      (((x ++ a) ++ x) ++ b) :=
  derivesInitialGapContraction x a b

/-- Delete a third initial block when the first interior is empty. -/
theorem derivesInitialExcessDeletion_leftEmpty (x b : Word Nat) :
    Derives basis (((x ++ x) ++ b) ++ x) ((x ++ x) ++ b) :=
  derivesSquaredPrefixContraction x b

/-- Delete a third initial block when the second interior is empty. -/
theorem derivesInitialExcessDeletion_rightEmpty (x a : Word Nat) :
    Derives basis (((x ++ a) ++ x) ++ x) ((x ++ a) ++ x) :=
  derivesTailContraction (x ++ a) x

/-- Delete a third initial block when both interiors are empty. -/
theorem derivesInitialExcessDeletion_bothEmpty (x : Word Nat) :
    Derives basis ((x ++ x) ++ x) (x ++ x) :=
  derivesPowerContraction x

end SemigroupBasis.CoRoots.S5_869
