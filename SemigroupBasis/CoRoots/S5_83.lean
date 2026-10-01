import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite

namespace SemigroupBasis.CoRoots.S5_83

open SemigroupBasis

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def xx : Word Nat := w 0 [0]
def xxx : Word Nat := w 0 [0, 0]
def xyx : Word Nat := w 0 [1, 0]
def xyy : Word Nat := w 0 [1, 1]
def yxx : Word Nat := w 1 [0, 0]
def xyz : Word Nat := w 0 [1, 2]
def xxyz : Word Nat := w 0 [0, 1, 2]

def powerLaw : Identity Nat := ⟨xx, xxx⟩
def copyLaw : Identity Nat := ⟨xyx, xyy⟩
def rotateLaw : Identity Nat := ⟨xyx, yxx⟩
def longInsertionLaw : Identity Nat := ⟨xyz, xxyz⟩

/-- The exact basis `xx = xxx`, `xyx = xyy`, `xyx = yxx`,
`xyz = xxyz`. -/
def basis : List (Identity Nat) :=
  [powerLaw, copyLaw, rotateLaw, longInsertionLaw]

def oppositeBasis : List (Identity Nat) :=
  reversedBasis basis

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

private theorem powerLaw_mem : powerLaw ∈ basis := by
  simp [basis]

private theorem copyLaw_mem : copyLaw ∈ basis := by
  simp [basis]

private theorem rotateLaw_mem : rotateLaw ∈ basis := by
  simp [basis]

private theorem longInsertionLaw_mem : longInsertionLaw ∈ basis := by
  simp [basis]

theorem derivesPowerExpansion (u : Word Nat) :
    Derives basis (u ++ u) ((u ++ u) ++ u) := by
  have base : Derives basis xx xxx :=
    Derives.fromBasis (e := powerLaw) powerLaw_mem
  have substituted := Derives.subst base (instantiateThreeWords u u u)
  simpa [powerLaw, xx, xxx, w, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

theorem derivesPowerContraction (u : Word Nat) :
    Derives basis ((u ++ u) ++ u) (u ++ u) :=
  (derivesPowerExpansion u).symm

theorem derivesCopy (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) ((u ++ v) ++ v) := by
  have base : Derives basis xyx xyy :=
    Derives.fromBasis (e := copyLaw) copyLaw_mem
  have substituted := Derives.subst base (instantiateThreeWords u v v)
  simpa [copyLaw, xyx, xyy, w, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

theorem derivesRotate (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) ((v ++ u) ++ u) := by
  have base : Derives basis xyx yxx :=
    Derives.fromBasis (e := rotateLaw) rotateLaw_mem
  have substituted := Derives.subst base (instantiateThreeWords u v v)
  simpa [rotateLaw, xyx, yxx, w, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- The common-word consequence `xyy = yxx`. -/
theorem derivesTransfer (u v : Word Nat) :
    Derives basis ((u ++ v) ++ v) ((v ++ u) ++ u) :=
  (derivesCopy u v).symm.trans (derivesRotate u v)

theorem derivesLongInsertion (u v z : Word Nat) :
    Derives basis ((u ++ v) ++ z) (((u ++ u) ++ v) ++ z) := by
  have base : Derives basis xyz xxyz :=
    Derives.fromBasis (e := longInsertionLaw) longInsertionLaw_mem
  have substituted := Derives.subst base (instantiateThreeWords u v z)
  simpa [longInsertionLaw, xyz, xxyz, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

theorem derivesLongContraction (u v z : Word Nat) :
    Derives basis (((u ++ u) ++ v) ++ z) ((u ++ v) ++ z) :=
  (derivesLongInsertion u v z).symm

/-- The exact promotion derivation `xyzt = yxzt`: duplicate `y`, use
`xyx = xyy` backwards, rotate with `xyx = yxx`, and contract the exposed
initial square. -/
theorem derivesPrefixSwap (u v q r : Word Nat) :
    Derives basis (((u ++ v) ++ q) ++ r) (((v ++ u) ++ q) ++ r) := by
  have duplicate :=
    Derives.prepend u (derivesLongInsertion v q r)
  have copyBack :=
    Derives.appendRight (Derives.symm (derivesCopy u v)) (q ++ r)
  have rotate :=
    Derives.appendRight (derivesRotate u v) (q ++ r)
  have contract :=
    Derives.prepend v (derivesLongContraction u q r)
  exact Derives.trans
    (by simpa [Word.append_assoc] using duplicate) <|
    Derives.trans
      (by simpa [Word.append_assoc] using copyBack) <|
    Derives.trans
      (by simpa [Word.append_assoc] using rotate)
      (by simpa [Word.append_assoc] using contract)

end SemigroupBasis.CoRoots.S5_83
