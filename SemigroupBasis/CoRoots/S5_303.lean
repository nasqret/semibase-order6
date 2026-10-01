import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite

namespace SemigroupBasis.CoRoots.S5_303

open SemigroupBasis

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def xy : Word Nat := w 0 [1]
def xxy : Word Nat := w 0 [0, 1]
def xyx : Word Nat := w 0 [1, 0]
def yxx : Word Nat := w 1 [0, 0]
def xyzx : Word Nat := w 0 [1, 2, 0]
def xzyx : Word Nat := w 0 [2, 1, 0]

def prefixDuplicationLaw : Identity Nat := ⟨xy, xxy⟩
def rotateLaw : Identity Nat := ⟨xyx, yxx⟩
def interiorSwapLaw : Identity Nat := ⟨xyzx, xzyx⟩

/-- The exact catalogue basis `xy = xxy`, `xyx = yxx`,
`xyzx = xzyx`. -/
def basis : List (Identity Nat) :=
  [prefixDuplicationLaw, rotateLaw, interiorSwapLaw]

def yx : Word Nat := w 1 [0]

def expectedOppositeBasis : List (Identity Nat) :=
  [⟨yx, yxx⟩, ⟨xyx, xxy⟩, ⟨xzyx, xyzx⟩]

def oppositeBasis : List (Identity Nat) :=
  reversedBasis basis

theorem oppositeBasis_eq_expected :
    oppositeBasis = expectedOppositeBasis := by
  rfl

private def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

private def finiteBasis : List (Identity (Fin 3)) :=
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

/-- Finite checking of the displayed three-variable laws yields `Models`
over the repository's standard `Nat` variables. -/
theorem models_of_finite_checks
    (table : FiniteTable)
    (checks : finiteBasis.all table.checkIdentity = true) :
    Models table.semigroup basis := by
  intro identity member
  have finiteMember : identity.map toFinThree ∈ finiteBasis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    table.checkIdentityNat_sound (identity.map toFinThree)
      ((List.all_eq_true.mp checks) _ finiteMember)
  rw [basis_roundTrip identity member] at finiteValid
  exact finiteValid

private def instantiateThreeWords
    (u v z : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => z
  | n + 3 => Word.singleton (n + 3)

private theorem prefixDuplicationLaw_mem :
    prefixDuplicationLaw ∈ basis := by
  simp [basis]

private theorem rotateLaw_mem : rotateLaw ∈ basis := by
  simp [basis]

private theorem interiorSwapLaw_mem :
    interiorSwapLaw ∈ basis := by
  simp [basis]

/-- Duplicate the first nonempty block before a nonempty suffix. -/
theorem derivesPrefixDuplication (u v : Word Nat) :
    Derives basis (u ++ v) ((u ++ u) ++ v) := by
  have base : Derives basis xy xxy :=
    Derives.fromBasis
      (e := prefixDuplicationLaw) prefixDuplicationLaw_mem
  have substituted :=
    Derives.subst base (instantiateThreeWords u v v)
  simpa [prefixDuplicationLaw, xy, xxy, w,
    instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem derivesPrefixContraction (u v : Word Nat) :
    Derives basis ((u ++ u) ++ v) (u ++ v) :=
  (derivesPrefixDuplication u v).symm

theorem derivesPowerExpansion (u : Word Nat) :
    Derives basis (u ++ u) ((u ++ u) ++ u) :=
  derivesPrefixDuplication u u

theorem derivesPowerContraction (u : Word Nat) :
    Derives basis ((u ++ u) ++ u) (u ++ u) :=
  (derivesPowerExpansion u).symm

/-- Move a terminal repeated block to the front of its two-block suffix. -/
theorem derivesRotate (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) ((v ++ u) ++ u) := by
  have base : Derives basis xyx yxx :=
    Derives.fromBasis (e := rotateLaw) rotateLaw_mem
  have substituted :=
    Derives.subst base (instantiateThreeWords u v v)
  simpa [rotateLaw, xyx, yxx, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

/-- Swap two interior blocks before a repeated final block. -/
theorem derivesInteriorSwap (u v z : Word Nat) :
    Derives basis (((u ++ v) ++ z) ++ u)
      (((u ++ z) ++ v) ++ u) := by
  have base : Derives basis xyzx xzyx :=
    Derives.fromBasis (e := interiorSwapLaw) interiorSwapLaw_mem
  have substituted :=
    Derives.subst base (instantiateThreeWords u v z)
  simpa [interiorSwapLaw, xyzx, xzyx, w,
    instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- Derived prefix commutation `uvqr = vuqr`. The two final nonempty
blocks remain fixed. -/
theorem derivesPrefixSwap (u v q r : Word Nat) :
    Derives basis (((u ++ v) ++ q) ++ r)
      (((v ++ u) ++ q) ++ r) := by
  have duplicate :=
    Derives.prepend (u ++ v) (derivesPrefixDuplication q r)
  have moveLeft :=
    Derives.appendRight
      (Derives.symm (derivesRotate q (u ++ v))) r
  have swapMiddle :=
    Derives.appendRight (derivesInteriorSwap q u v) r
  have moveRight :=
    Derives.appendRight (derivesRotate q (v ++ u)) r
  have contract :=
    Derives.prepend (v ++ u) (derivesPrefixContraction q r)
  apply Derives.trans
  · simpa [Word.append_assoc] using duplicate
  · apply Derives.trans
    · simpa [Word.append_assoc] using moveLeft
    · apply Derives.trans
      · simpa [Word.append_assoc] using swapMiddle
      · apply Derives.trans
        · simpa [Word.append_assoc] using moveRight
        · simpa [Word.append_assoc] using contract

end SemigroupBasis.CoRoots.S5_303
