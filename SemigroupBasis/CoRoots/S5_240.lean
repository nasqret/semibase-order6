import SemigroupBasis.FiniteReflection
import SemigroupBasis.Generated.CatalogueOrder5Part02
import SemigroupBasis.Opposite

namespace SemigroupBasis.CoRoots.S5_240

open SemigroupBasis

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def xx : Word Nat := w 0 [0]
def xxx : Word Nat := w 0 [0, 0]
def xyy : Word Nat := w 0 [1, 1]
def yxx : Word Nat := w 1 [0, 0]
def xyz : Word Nat := w 0 [1, 2]
def xxyz : Word Nat := w 0 [0, 1, 2]

def powerLaw : Identity Nat := ⟨xx, xxx⟩
def markerSwitchLaw : Identity Nat := ⟨xyy, yxx⟩
def longInsertionLaw : Identity Nat := ⟨xyz, xxyz⟩

/-- The exact basis `xx = xxx`, `xyy = yxx`, `xyz = xxyz`. -/
def basis : List (Identity Nat) :=
  [powerLaw, markerSwitchLaw, longInsertionLaw]

def yyx : Word Nat := w 1 [1, 0]
def xxy : Word Nat := w 0 [0, 1]
def zyx : Word Nat := w 2 [1, 0]
def zyxx : Word Nat := w 2 [1, 0, 0]

/-- The literal reverse-word orientation for the opposite semigroup. -/
def expectedOppositeBasis : List (Identity Nat) :=
  [⟨xx, xxx⟩, ⟨yyx, xxy⟩, ⟨zyx, zyxx⟩]

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

/-- Finite checking of the three displayed laws yields `Models` over `Nat`
variables. -/
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

private theorem markerSwitchLaw_mem : markerSwitchLaw ∈ basis := by
  simp [basis]

private theorem longInsertionLaw_mem : longInsertionLaw ∈ basis := by
  simp [basis]

/-- Expand the square of a nonempty block to its cube. -/
theorem derivesPowerExpansion (u : Word Nat) :
    Derives basis (u ++ u) ((u ++ u) ++ u) := by
  have base : Derives basis xx xxx :=
    Derives.fromBasis (e := powerLaw) powerLaw_mem
  have substituted :=
    Derives.subst base (instantiateThreeWords u u u)
  simpa [powerLaw, xx, xxx, w, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- Contract the cube of a nonempty block to its square. -/
theorem derivesPowerContraction (u : Word Nat) :
    Derives basis ((u ++ u) ++ u) (u ++ u) :=
  (derivesPowerExpansion u).symm

/-- The basis marker switch, with arbitrary nonempty word substitutions. -/
theorem derivesMarkerSwitch (u v : Word Nat) :
    Derives basis ((u ++ v) ++ v) ((v ++ u) ++ u) := by
  have base : Derives basis xyy yxx :=
    Derives.fromBasis (e := markerSwitchLaw) markerSwitchLaw_mem
  have substituted :=
    Derives.subst base (instantiateThreeWords u v v)
  simpa [markerSwitchLaw, xyy, yxx, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

/-- Insert a duplicate of the first nonempty block in a two-sided context. -/
theorem derivesLongInsertion (u v z : Word Nat) :
    Derives basis ((u ++ v) ++ z) (((u ++ u) ++ v) ++ z) := by
  have base : Derives basis xyz xxyz :=
    Derives.fromBasis (e := longInsertionLaw) longInsertionLaw_mem
  have substituted :=
    Derives.subst base (instantiateThreeWords u v z)
  simpa [longInsertionLaw, xyz, xxyz, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

/-- Delete a duplicate of the first nonempty block in a two-sided context. -/
theorem derivesLongContraction (u v z : Word Nat) :
    Derives basis (((u ++ u) ++ v) ++ z) ((u ++ v) ++ z) :=
  (derivesLongInsertion u v z).symm

/-- Derived prefix commutation `uvqr = vuqr`. The last two nonempty factors
remain fixed. -/
theorem derivesPrefixSwap (u v q r : Word Nat) :
    Derives basis (((u ++ v) ++ q) ++ r) (((v ++ u) ++ q) ++ r) := by
  have duplicate :=
    Derives.prepend u (derivesLongInsertion v q r)
  have switch :=
    Derives.appendRight (derivesMarkerSwitch u v) (q ++ r)
  have contract :=
    Derives.prepend v (derivesLongContraction u q r)
  apply Derives.trans
  · simpa [Word.append_assoc] using duplicate
  · apply Derives.trans
    · simpa [Word.append_assoc] using switch
    · simpa [Word.append_assoc] using contract

/-- Derived two-variable terminal collapse `uvuv = uvv`. -/
theorem derivesTerminalCollapse (u v : Word Nat) :
    Derives basis (((u ++ v) ++ u) ++ v) ((u ++ v) ++ v) := by
  let uv := u ++ v
  have expand := derivesPowerExpansion uv
  have switch :=
    Derives.prepend u (derivesMarkerSwitch v uv)
  have contractPower :=
    Derives.prepend (u ++ u) (derivesPowerContraction v)
  have contractLong := derivesLongContraction u v v
  apply Derives.trans
  · simpa [uv, Word.append_assoc] using expand
  · apply Derives.trans
    · simpa [uv, Word.append_assoc] using switch
    · apply Derives.trans
      · simpa [Word.append_assoc] using contractPower
      · simpa [Word.append_assoc] using contractLong

end SemigroupBasis.CoRoots.S5_240
