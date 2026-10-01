import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite

namespace SemigroupBasis.CoRoots.S5_213

open SemigroupBasis

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def xxx : Word Nat := w 0 [0, 0]
def xxxx : Word Nat := w 0 [0, 0, 0]
def xyx : Word Nat := w 0 [1, 0]
def xxy : Word Nat := w 0 [0, 1]
def yxx : Word Nat := w 1 [0, 0]

def powerLaw : Identity Nat := ⟨xxx, xxxx⟩
def leftGatherLaw : Identity Nat := ⟨xyx, xxy⟩
def rightGatherLaw : Identity Nat := ⟨xyx, yxx⟩

/-- Edmunds' exact Proposition 3.1(g) basis for `M2` and `M8`. -/
def basis : List (Identity Nat) :=
  [powerLaw, leftGatherLaw, rightGatherLaw]

/-- Reversal fixes the power law and exchanges the two gather laws. -/
def expectedReversedBasis : List (Identity Nat) :=
  [powerLaw, rightGatherLaw, leftGatherLaw]

theorem reversedBasis_eq_expected :
    reversedBasis basis = expectedReversedBasis := by
  rfl

def toFinTwo : Nat → Fin 2
  | 0 => 0
  | _ => 1

def finiteBasis : List (Identity (Fin 2)) :=
  basis.map fun identity => identity.map toFinTwo

private theorem basisRoundTripChecked :
    basis.all (fun identity =>
      decide ((identity.map toFinTwo).map Fin.val = identity)) = true := by
  decide

private theorem basisRoundTrip
    (identity : Identity Nat) (member : identity ∈ basis) :
    (identity.map toFinTwo).map Fin.val = identity := by
  exact of_decide_eq_true <|
    (List.all_eq_true.mp basisRoundTripChecked) identity member

/-- Convert the exhaustive two-variable table checks into a `Models` proof. -/
theorem models_of_finite_checks
    (table : FiniteTable)
    (checked : finiteBasis.all table.checkIdentity = true) :
    Models table.semigroup basis := by
  intro identity member
  have finiteMember : identity.map toFinTwo ∈ finiteBasis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    table.checkIdentityNat_sound (identity.map toFinTwo)
      ((List.all_eq_true.mp checked) _ finiteMember)
  rw [basisRoundTrip identity member] at finiteValid
  exact finiteValid

private def instantiateTwoWords
    (u v : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | n + 2 => Word.singleton (n + 2)

private theorem basisPower :
    Derives basis xxx xxxx :=
  Derives.fromBasis (e := powerLaw) <| by
    simp [basis]

private theorem basisLeftGather :
    Derives basis xyx xxy :=
  Derives.fromBasis (e := leftGatherLaw) <| by
    simp [basis]

private theorem basisRightGather :
    Derives basis xyx yxx :=
  Derives.fromBasis (e := rightGatherLaw) <| by
    simp [basis]

/-- Expand three consecutive copies of a nonempty block to four. -/
theorem derivesPowerExpansion (u : Word Nat) :
    Derives basis
      ((u ++ u) ++ u)
      (((u ++ u) ++ u) ++ u) := by
  have substituted :=
    Derives.subst basisPower (instantiateTwoWords u u)
  simpa [xxx, xxxx, w, instantiateTwoWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- Contract four consecutive copies of a nonempty block to three. -/
theorem derivesPowerContraction (u : Word Nat) :
    Derives basis
      (((u ++ u) ++ u) ++ u)
      ((u ++ u) ++ u) :=
  (derivesPowerExpansion u).symm

/-- Gather a later copy of `u` into a square at the left endpoint. -/
theorem derivesLeftGather (u v : Word Nat) :
    Derives basis
      ((u ++ v) ++ u)
      ((u ++ u) ++ v) := by
  have substituted :=
    Derives.subst basisLeftGather (instantiateTwoWords u v)
  simpa [xyx, xxy, w, instantiateTwoWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- Gather a later copy of `u` into a square at the right endpoint. -/
theorem derivesRightGather (u v : Word Nat) :
    Derives basis
      ((u ++ v) ++ u)
      (v ++ (u ++ u)) := by
  have substituted :=
    Derives.subst basisRightGather (instantiateTwoWords u v)
  simpa [xyx, yxx, w, instantiateTwoWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- The two mixed laws imply `u^2 v = v u^2`. -/
theorem derivesSquareAcross (u v : Word Nat) :
    Derives basis
      ((u ++ u) ++ v)
      (v ++ (u ++ u)) :=
  (derivesLeftGather u v).symm.trans
    (derivesRightGather u v)

/-- A cube also commutes with every nonempty block. -/
theorem derivesCubeAcross (u v : Word Nat) :
    Derives basis
      (((u ++ u) ++ u) ++ v)
      (v ++ ((u ++ u) ++ u)) := by
  have first :=
    Derives.prepend u (derivesSquareAcross u v)
  have second :=
    Derives.appendRight (derivesRightGather u v) u
  have first' :
      Derives basis
        (((u ++ u) ++ u) ++ v)
        ((u ++ v) ++ (u ++ u)) := by
    simpa [Word.append_assoc] using first
  have second' :
      Derives basis
        ((u ++ v) ++ (u ++ u))
        (v ++ ((u ++ u) ++ u)) := by
    simpa [Word.append_assoc] using second
  exact first'.trans second'

theorem derivesSquareSquareCommutation (u v : Word Nat) :
    Derives basis
      ((u ++ u) ++ (v ++ v))
      ((v ++ v) ++ (u ++ u)) :=
  derivesSquareAcross u (v ++ v)

theorem derivesSquareCubeCommutation (u v : Word Nat) :
    Derives basis
      ((u ++ u) ++ ((v ++ v) ++ v))
      (((v ++ v) ++ v) ++ (u ++ u)) :=
  derivesSquareAcross u ((v ++ v) ++ v)

theorem derivesCubeSquareCommutation (u v : Word Nat) :
    Derives basis
      (((u ++ u) ++ u) ++ (v ++ v))
      ((v ++ v) ++ ((u ++ u) ++ u)) :=
  derivesCubeAcross u (v ++ v)

theorem derivesCubeCubeCommutation (u v : Word Nat) :
    Derives basis
      (((u ++ u) ++ u) ++ ((v ++ v) ++ v))
      (((v ++ v) ++ v) ++ ((u ++ u) ++ u)) :=
  derivesCubeAcross u ((v ++ v) ++ v)

end SemigroupBasis.CoRoots.S5_213
