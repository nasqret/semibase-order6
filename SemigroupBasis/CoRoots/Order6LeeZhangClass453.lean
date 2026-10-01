import SemigroupBasis.CoRoots.S5_107ListDerives
import SemigroupBasis.CoRoots.S5_254PairExtraction
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite

namespace SemigroupBasis.CoRoots.Order6LeeZhangClass453

open SemigroupBasis

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def xx : Word Nat := w 0 [0]
def xxx : Word Nat := w 0 [0, 0]
def xyx : Word Nat := w 0 [1, 0]
def xxyx : Word Nat := w 0 [0, 1, 0]
def xyxx : Word Nat := w 0 [1, 0, 0]
def xxyy : Word Nat := w 0 [0, 1, 1]
def yyxx : Word Nat := w 1 [1, 0, 0]
def xxyzz : Word Nat := w 0 [0, 1, 2, 2]
def xyzzx : Word Nat := w 0 [1, 2, 2, 0]

def powerLaw : Identity Nat := ⟨xxx, xx⟩
def leftEndpointLaw : Identity Nat := ⟨xxyx, xyx⟩
def rightEndpointLaw : Identity Nat := ⟨xyxx, xyx⟩
def squareCommutationLaw : Identity Nat := ⟨xxyy, yyxx⟩
def squareMoveLaw : Identity Nat := ⟨xxyzz, xyzzx⟩

/-- Lee--Zhang Condition 10, in the packet's opposite orientation. -/
def basis : List (Identity Nat) :=
  [powerLaw, leftEndpointLaw, rightEndpointLaw,
    squareCommutationLaw, squareMoveLaw]

/-- The literal basis for the direct Smallsemi orientation. -/
def oppositeBasis : List (Identity Nat) :=
  reversedBasis basis

def packetRecordType : String :=
  "order6_lee_zhang_condition10_basis_population"

def packetSHA256 : String :=
  "bd7db3f533135e60f33e2523699a33ffa4297ff438994f63f546fc29926c8491"

private def instantiateThreeWords
    (u v z : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => z
  | n + 3 => Word.singleton (n + 3)

private theorem basisPower : Derives basis xxx xx :=
  Derives.fromBasis (e := powerLaw) (by simp [basis])

private theorem basisLeftEndpoint : Derives basis xxyx xyx :=
  Derives.fromBasis (e := leftEndpointLaw) (by simp [basis])

private theorem basisRightEndpoint : Derives basis xyxx xyx :=
  Derives.fromBasis (e := rightEndpointLaw) (by simp [basis])

private theorem basisSquareCommutation : Derives basis xxyy yyxx :=
  Derives.fromBasis (e := squareCommutationLaw) (by simp [basis])

private theorem basisSquareMove : Derives basis xxyzz xyzzx :=
  Derives.fromBasis (e := squareMoveLaw) (by simp [basis])

/-- Expand two consecutive copies of any nonempty block to three. -/
theorem derivesPowerExpansion (u : Word Nat) :
    Derives basis (u ++ u) ((u ++ u) ++ u) := by
  have substituted :=
    Derives.subst basisPower.symm (instantiateThreeWords u u u)
  simpa [xxx, xx, w, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- Contract three consecutive copies of any nonempty block to two. -/
theorem derivesPowerContraction (u : Word Nat) :
    Derives basis ((u ++ u) ++ u) (u ++ u) :=
  (derivesPowerExpansion u).symm

/-- Contract four consecutive copies of a block to two. -/
theorem derivesFourToTwo (u : Word Nat) :
    Derives basis (((u ++ u) ++ u) ++ u) (u ++ u) := by
  have first := Derives.prepend u (derivesPowerContraction u)
  have fourToThree :
      Derives basis (((u ++ u) ++ u) ++ u) ((u ++ u) ++ u) := by
    simpa [Word.append_assoc] using first
  exact fourToThree.trans (derivesPowerContraction u)

/-- Duplicate the left occurrence of a repeated endpoint. -/
theorem derivesLeftEndpointExpansion (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) (((u ++ u) ++ v) ++ u) := by
  have substituted :=
    Derives.subst basisLeftEndpoint.symm
      (instantiateThreeWords u v v)
  simpa [xxyx, xyx, w, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- Duplicate the right occurrence of a repeated endpoint. -/
theorem derivesRightEndpointExpansion (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) (((u ++ v) ++ u) ++ u) := by
  have substituted :=
    Derives.subst basisRightEndpoint.symm
      (instantiateThreeWords u v v)
  simpa [xyxx, xyx, w, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- Commute two adjacent nonempty square blocks. -/
theorem derivesSquareBlockCommutation (u v : Word Nat) :
    Derives basis ((u ++ u) ++ (v ++ v))
      ((v ++ v) ++ (u ++ u)) := by
  have substituted :=
    Derives.subst basisSquareCommutation
      (instantiateThreeWords u v v)
  simpa [xxyy, yyxx, w, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- Move one copy of a doubled block across an arbitrary nonempty middle
and a terminal square. -/
theorem derivesSquareMove (u v z : Word Nat) :
    Derives basis (((u ++ u) ++ v) ++ (z ++ z))
      (((u ++ v) ++ (z ++ z)) ++ u) := by
  have substituted :=
    Derives.subst basisSquareMove (instantiateThreeWords u v z)
  simpa [xxyzz, xyzzx, w, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

private def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

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

/-- Executable checks of the five displayed laws imply `Models` over the
unrestricted `Nat` variable type. -/
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

end SemigroupBasis.CoRoots.Order6LeeZhangClass453
