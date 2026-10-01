import SemigroupBasis.FiniteReflection
import SemigroupBasis.Generated.CatalogueOrder5Part02
import SemigroupBasis.Opposite

namespace SemigroupBasis.CoRoots.S5_207

open SemigroupBasis

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def xxx : Word Nat := w 0 [0, 0]
def xxxx : Word Nat := w 0 [0, 0, 0]
def xxy : Word Nat := w 0 [0, 1]
def xxxy : Word Nat := w 0 [0, 0, 1]
def xyx : Word Nat := w 0 [1, 0]
def yxx : Word Nat := w 1 [0, 0]
def xyz : Word Nat := w 0 [1, 2]
def yxz : Word Nat := w 1 [0, 2]
def xxyyx : Word Nat := w 0 [0, 1, 1, 0]
def xxyyy : Word Nat := w 0 [0, 1, 1, 1]

def powerExpansionLaw : Identity Nat := ⟨xxx, xxxx⟩
def prefixMultiplicityExpansionLaw : Identity Nat := ⟨xxy, xxxy⟩
def terminalRotationLaw : Identity Nat := ⟨xyx, yxx⟩
def prefixSwapLaw : Identity Nat := ⟨xyz, yxz⟩
def doubledFinalSwitchLaw : Identity Nat := ⟨xxyyx, xxyyy⟩

/-- The exact ordered five-law basis recorded for catalogue class `S5_207`.
This definition does not assert unrestricted normal-form completeness. -/
def basis : List (Identity Nat) :=
  [powerExpansionLaw, prefixMultiplicityExpansionLaw,
    terminalRotationLaw, prefixSwapLaw, doubledFinalSwitchLaw]

def oppositeBasis : List (Identity Nat) :=
  reversedBasis basis

/- Definitions that describe the recorded finite-state invariant without
asserting that it is complete for derivability. -/
namespace DirectCompletenessArchitecture

/-- The five marker states separated by assigning the tested variable to
table element 4 and every other variable to table element 5. -/
inductive MarkerState where
  | absent
  | finalOnly
  | oneNonfinal
  | oneNonfinalAndFinal
  | atLeastTwoNonfinal
  deriving DecidableEq, Repr

/-- All letters except the literal final letter. -/
def prefixLetters (word : Word Nat) : List Nat :=
  word.toList.dropLast

/-- Whether `letter` is the literal final letter. -/
def isFinal (word : Word Nat) (letter : Nat) : Bool :=
  word.toList.getLast? == some letter

/-- Prefix multiplicity capped at two, matching the recorded certificate. -/
def cappedPrefixMultiplicity (word : Word Nat) (letter : Nat) : Nat :=
  min ((prefixLetters word).count letter) 2

/-- The exact per-variable state recorded by the finite marker calculation.
The final choice is intentionally forgotten once the prefix multiplicity is
at least two. -/
def markerState (word : Word Nat) (letter : Nat) : MarkerState :=
  match cappedPrefixMultiplicity word letter, isFinal word letter with
  | 0, false => .absent
  | 0, true => .finalOnly
  | 1, false => .oneNonfinal
  | 1, true => .oneNonfinalAndFinal
  | _, _ => .atLeastTwoNonfinal

/-- Equality of the recorded marker vector. No completeness theorem for this
relation is asserted in this partial source. -/
def SameMarkerSignature (left right : Word Nat) : Prop :=
  ∀ letter, markerState left letter = markerState right letter

end DirectCompletenessArchitecture

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

/-- Exhaustive checks on the three displayed variables imply the corresponding
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

abbrev table : FiniteTable :=
  Generated.Catalogue.S5_207.table

set_option maxRecDepth 100000 in
/-- The generated catalogue representative satisfies all five recorded laws. -/
theorem models : Models table.semigroup basis :=
  models_of_finite_checks table (by decide)

/-- The opposite representative satisfies the literal reversed laws. -/
theorem oppositeModels :
    Models table.semigroup.opposite oppositeBasis :=
  models.oppositeReversed

private def instantiateThreeWords
    (u v z : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => z
  | n + 3 => Word.singleton (n + 3)

private theorem basisPowerExpansion :
    Derives basis xxx xxxx :=
  Derives.fromBasis (e := powerExpansionLaw) <| by simp [basis]

private theorem basisPrefixMultiplicityExpansion :
    Derives basis xxy xxxy :=
  Derives.fromBasis (e := prefixMultiplicityExpansionLaw) <| by simp [basis]

private theorem basisTerminalRotation :
    Derives basis xyx yxx :=
  Derives.fromBasis (e := terminalRotationLaw) <| by simp [basis]

private theorem basisPrefixSwap :
    Derives basis xyz yxz :=
  Derives.fromBasis (e := prefixSwapLaw) <| by simp [basis]

private theorem basisDoubledFinalSwitch :
    Derives basis xxyyx xxyyy :=
  Derives.fromBasis (e := doubledFinalSwitchLaw) <| by simp [basis]

/-- Direct block substitution in `xxx = xxxx`. -/
theorem derivesPowerExpansion (u : Word Nat) :
    Derives basis
      ((u ++ u) ++ u)
      (((u ++ u) ++ u) ++ u) := by
  have substituted :=
    Derives.subst basisPowerExpansion (instantiateThreeWords u u u)
  simpa [powerExpansionLaw, xxx, xxxx, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

/-- Direct block substitution in `xxy = xxxy`. -/
theorem derivesPrefixMultiplicityExpansion (u v : Word Nat) :
    Derives basis
      ((u ++ u) ++ v)
      (((u ++ u) ++ u) ++ v) := by
  have substituted :=
    Derives.subst basisPrefixMultiplicityExpansion
      (instantiateThreeWords u v v)
  simpa [prefixMultiplicityExpansionLaw, xxy, xxxy, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Direct block substitution in `xyx = yxx`. -/
theorem derivesTerminalRotation (u v : Word Nat) :
    Derives basis
      ((u ++ v) ++ u)
      ((v ++ u) ++ u) := by
  have substituted :=
    Derives.subst basisTerminalRotation (instantiateThreeWords u v v)
  simpa [terminalRotationLaw, xyx, yxx, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

/-- Direct block substitution in `xyz = yxz`. This swaps two nonempty blocks
while retaining a nonempty suffix block; it is not a global sorting theorem. -/
theorem derivesPrefixSwap (u v z : Word Nat) :
    Derives basis
      ((u ++ v) ++ z)
      ((v ++ u) ++ z) := by
  have substituted :=
    Derives.subst basisPrefixSwap (instantiateThreeWords u v z)
  simpa [prefixSwapLaw, xyz, yxz, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

/-- Direct block substitution in `xxyyx = xxyyy`. -/
theorem derivesDoubledFinalSwitch (u v : Word Nat) :
    Derives basis
      ((((u ++ u) ++ v) ++ v) ++ u)
      ((((u ++ u) ++ v) ++ v) ++ v) := by
  have substituted :=
    Derives.subst basisDoubledFinalSwitch
      (instantiateThreeWords u v v)
  simpa [doubledFinalSwitchLaw, xxyyx, xxyyy, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- The reverse of the first primitive substitution, useful for capping a
terminal block at three copies. -/
theorem derivesPowerCap (u : Word Nat) :
    Derives basis
      (((u ++ u) ++ u) ++ u)
      ((u ++ u) ++ u) :=
  (derivesPowerExpansion u).symm

/-- The reverse of the second primitive substitution, useful for capping a
prefix block at two copies before a nonempty suffix. -/
theorem derivesPrefixMultiplicityCap (u v : Word Nat) :
    Derives basis
      (((u ++ u) ++ u) ++ v)
      ((u ++ u) ++ v) :=
  (derivesPrefixMultiplicityExpansion u v).symm

end SemigroupBasis.CoRoots.S5_207
