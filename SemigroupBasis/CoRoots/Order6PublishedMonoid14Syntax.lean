import SemigroupBasis.CoRoots.S5_107ListDerives
import SemigroupBasis.CoRoots.S5_254PairExtraction
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6PublishedMonoid14

open SemigroupBasis

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

/-! ## Lee--Li Proposition 14.1 for monoid I -/

def xx : Word Nat := w 0 [0]
def xxx : Word Nat := w 0 [0, 0]
def xyx : Word Nat := w 0 [1, 0]
def xxyx : Word Nat := w 0 [0, 1, 0]
def xyxx : Word Nat := w 0 [1, 0, 0]
def xxyy : Word Nat := w 0 [0, 1, 1]
def xxyyx : Word Nat := w 0 [0, 1, 1, 0]

/-- `x² = x³`. -/
def powerLaw : Identity Nat := ⟨xx, xxx⟩

/-- `x²yx = xyx²`, the first equality in (14.1a). -/
def endpointTransferLaw : Identity Nat := ⟨xxyx, xyxx⟩

/-- `x²y² = x²y²x`, the symmetric orientation of (14.1b). -/
def squareReturnLaw : Identity Nat := ⟨xxyy, xxyyx⟩

/-- `xyx = xyx²`, the second equality in (14.1a). -/
def rightEndpointLaw : Identity Nat := ⟨xyx, xyxx⟩

/-- The literal four-law expansion of Lee--Li Proposition 14.1. -/
def basis : List (Identity Nat) :=
  [powerLaw, endpointTransferLaw, squareReturnLaw, rightEndpointLaw]

def oppositeBasis : List (Identity Nat) :=
  reversedBasis basis

private def toFinTwo : Nat → Fin 2
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

/-- Executable checks of the two displayed variables prove unrestricted
soundness of the literal basis for an exact finite table. -/
theorem modelsOfFiniteChecks
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

/-! ## Primitive block derivations -/

private def instantiateTwoWords
    (u v : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | n + 2 => Word.singleton (n + 2)

private theorem basisPower : Derives basis xx xxx :=
  Derives.fromBasis (e := powerLaw) (by simp [basis])

private theorem basisEndpointTransfer : Derives basis xxyx xyxx :=
  Derives.fromBasis (e := endpointTransferLaw) (by simp [basis])

private theorem basisSquareReturn : Derives basis xxyy xxyyx :=
  Derives.fromBasis (e := squareReturnLaw) (by simp [basis])

private theorem basisRightEndpoint : Derives basis xyx xyxx :=
  Derives.fromBasis (e := rightEndpointLaw) (by simp [basis])

theorem derivesPowerExpansion (u : Word Nat) :
    Derives basis (u ++ u) ((u ++ u) ++ u) := by
  have substituted :=
    Derives.subst basisPower (instantiateTwoWords u u)
  simpa [xx, xxx, w, instantiateTwoWords, Word.bind,
    Word.singleton, Word.append, Word.append_assoc] using substituted

theorem derivesPowerContraction (u : Word Nat) :
    Derives basis ((u ++ u) ++ u) (u ++ u) :=
  (derivesPowerExpansion u).symm

theorem derivesFourToTwo (u : Word Nat) :
    Derives basis (((u ++ u) ++ u) ++ u) (u ++ u) := by
  have fourToThree :=
    Derives.prepend u (derivesPowerContraction u)
  have first :
      Derives basis (((u ++ u) ++ u) ++ u) ((u ++ u) ++ u) := by
    simpa [Word.append_assoc] using fourToThree
  exact first.trans (derivesPowerContraction u)

theorem derivesRightEndpointExpansion (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) (((u ++ v) ++ u) ++ u) := by
  have substituted :=
    Derives.subst basisRightEndpoint (instantiateTwoWords u v)
  simpa [xyx, xyxx, w, instantiateTwoWords, Word.bind,
    Word.singleton, Word.append, Word.append_assoc] using substituted

theorem derivesRightEndpointContraction (u v : Word Nat) :
    Derives basis (((u ++ v) ++ u) ++ u) ((u ++ v) ++ u) :=
  (derivesRightEndpointExpansion u v).symm

theorem derivesEndpointTransfer (u v : Word Nat) :
    Derives basis (((u ++ u) ++ v) ++ u)
      (((u ++ v) ++ u) ++ u) := by
  have substituted :=
    Derives.subst basisEndpointTransfer (instantiateTwoWords u v)
  simpa [xxyx, xyxx, w, instantiateTwoWords, Word.bind,
    Word.singleton, Word.append, Word.append_assoc] using substituted

theorem derivesLeftEndpointContraction (u v : Word Nat) :
    Derives basis (((u ++ u) ++ v) ++ u) ((u ++ v) ++ u) :=
  (derivesEndpointTransfer u v).trans
    (derivesRightEndpointContraction u v)

theorem derivesLeftEndpointExpansion (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) (((u ++ u) ++ v) ++ u) :=
  (derivesLeftEndpointContraction u v).symm

theorem derivesSquareReturnExpansion (u v : Word Nat) :
    Derives basis ((u ++ u) ++ (v ++ v))
      (((u ++ u) ++ (v ++ v)) ++ u) := by
  have substituted :=
    Derives.subst basisSquareReturn (instantiateTwoWords u v)
  simpa [xxyy, xxyyx, w, instantiateTwoWords, Word.bind,
    Word.singleton, Word.append, Word.append_assoc] using substituted

theorem derivesSquareReturnContraction (u v : Word Nat) :
    Derives basis (((u ++ u) ++ (v ++ v)) ++ u)
      ((u ++ u) ++ (v ++ v)) :=
  (derivesSquareReturnExpansion u v).symm

end SemigroupBasis.CoRoots.Order6PublishedMonoid14
