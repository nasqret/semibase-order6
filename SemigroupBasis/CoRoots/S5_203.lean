import SemigroupBasis.CoRoots.S5_83Invariant
import SemigroupBasis.CoRoots.S5_240Normalization
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Generated.CatalogueOrder5Part02
import SemigroupBasis.Opposite

namespace SemigroupBasis.CoRoots.S5_203

open SemigroupBasis

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def xxx : Word Nat := w 0 [0, 0]
def xxxx : Word Nat := w 0 [0, 0, 0]
def xxy : Word Nat := w 0 [0, 1]
def xxxy : Word Nat := w 0 [0, 0, 1]
def xyx : Word Nat := w 0 [1, 0]
def yxy : Word Nat := w 1 [0, 1]
def xxyx : Word Nat := w 0 [0, 1, 0]
def xyyy : Word Nat := w 0 [1, 1, 1]
def xyyxx : Word Nat := w 0 [1, 1, 0, 0]
def xyy : Word Nat := w 0 [1, 1]
def xxyy : Word Nat := w 0 [0, 1, 1]
def xyz : Word Nat := w 0 [1, 2]
def xxyz : Word Nat := w 0 [0, 1, 2]
def xyzx : Word Nat := w 0 [1, 2, 0]
def xyzy : Word Nat := w 0 [1, 2, 1]
def xyzz : Word Nat := w 0 [1, 2, 2]
def yxzz : Word Nat := w 1 [0, 2, 2]

def powerExpansionLaw : Identity Nat := ⟨xxx, xxxx⟩
def repeatedPrefixExpansionLaw : Identity Nat := ⟨xxy, xxxy⟩
def alternatingSwitchLaw : Identity Nat := ⟨xyx, yxy⟩
def initialDuplicationLaw : Identity Nat := ⟨xyx, xxyx⟩
def terminalCubeLaw : Identity Nat := ⟨xyx, xyyy⟩
def doublePairExpansionLaw : Identity Nat := ⟨xyx, xyyxx⟩
def pairedPrefixExpansionLaw : Identity Nat := ⟨xyy, xxyy⟩
def prefixDuplicationLaw : Identity Nat := ⟨xyz, xxyz⟩
def terminalRetargetLaw : Identity Nat := ⟨xyzx, xyzy⟩
def squareSuffixSwapLaw : Identity Nat := ⟨xyzz, yxzz⟩

/-- The exact ordered ten-law basis recorded for catalogue class `S5_203`.
This definition does not assert unrestricted normal-form completeness. -/
def basis : List (Identity Nat) :=
  [powerExpansionLaw, repeatedPrefixExpansionLaw,
    alternatingSwitchLaw, initialDuplicationLaw, terminalCubeLaw,
    doublePairExpansionLaw, pairedPrefixExpansionLaw,
    prefixDuplicationLaw, terminalRetargetLaw, squareSuffixSwapLaw]

def oppositeBasis : List (Identity Nat) :=
  reversedBasis basis

/- Definitions shared by the planned direct completeness proof. They extend
the S5_83 terminal predicates by the terminal-doubleton state. The relational
prefix proof is intended to follow the S5_240 normalization architecture. -/
namespace DirectCompletenessArchitecture

abbrev SameSupport (left right : Word Nat) : Prop :=
  SemigroupBasis.CoRoots.S5_83.SameSupport left right

abbrev IsSingletonWord (word : Word Nat) : Prop :=
  SemigroupBasis.CoRoots.S5_83.IsSingletonWord word

abbrev UniqueFinal (word : Word Nat) (final : Nat) : Prop :=
  SemigroupBasis.CoRoots.S5_83.UniqueFinal word final

abbrev UniqueTerminalPair
    (word : Word Nat) (penultimate final : Nat) : Prop :=
  SemigroupBasis.CoRoots.S5_83.UniqueTerminalPair
    word penultimate final

/-- The word ends in the only two occurrences of `final`. -/
def TerminalDoubleton (word : Word Nat) (final : Nat) : Prop :=
  match SemigroupBasis.CoRoots.S5_83.terminalSplit word with
  | .singleton _ => False
  | .pair stem penultimate actualFinal =>
      penultimate = final ∧ actualFinal = final ∧ final ∉ stem

/-- The generic terminal-pair renderer used by S5_240's relational prefix
normalization. No S5_203 normalization theorem is asserted here. -/
abbrev wordOfTerminalPair
    (stem : List Nat) (penultimate final : Nat) : Word Nat :=
  SemigroupBasis.CoRoots.S5_240.wordOfTerminalPair
    stem penultimate final

/-- The planned S5_203 signature. Pair comparison is deliberately available
only after the final variable is known to be globally unique. -/
structure SameSupportTerminalStateSignature
    (left right : Word Nat) : Prop where
  support : SameSupport left right
  singleton : IsSingletonWord left ↔ IsSingletonWord right
  uniqueFinal :
    ∀ final, UniqueFinal left final ↔ UniqueFinal right final
  terminalDoubleton :
    ∀ final,
      TerminalDoubleton left final ↔
        TerminalDoubleton right final
  uniqueTerminalPairOfUniqueFinal :
    ∀ penultimate final,
      UniqueFinal left final →
        (UniqueTerminalPair left penultimate final ↔
          UniqueTerminalPair right penultimate final)

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
  Generated.Catalogue.S5_203.table

set_option maxRecDepth 100000 in
/-- The generated catalogue representative satisfies all ten recorded laws. -/
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

private theorem basisRepeatedPrefixExpansion :
    Derives basis xxy xxxy :=
  Derives.fromBasis (e := repeatedPrefixExpansionLaw) <| by simp [basis]

private theorem basisAlternatingSwitch :
    Derives basis xyx yxy :=
  Derives.fromBasis (e := alternatingSwitchLaw) <| by simp [basis]

private theorem basisInitialDuplication :
    Derives basis xyx xxyx :=
  Derives.fromBasis (e := initialDuplicationLaw) <| by simp [basis]

private theorem basisTerminalCube :
    Derives basis xyx xyyy :=
  Derives.fromBasis (e := terminalCubeLaw) <| by simp [basis]

private theorem basisDoublePairExpansion :
    Derives basis xyx xyyxx :=
  Derives.fromBasis (e := doublePairExpansionLaw) <| by simp [basis]

private theorem basisPairedPrefixExpansion :
    Derives basis xyy xxyy :=
  Derives.fromBasis (e := pairedPrefixExpansionLaw) <| by simp [basis]

private theorem basisPrefixDuplication :
    Derives basis xyz xxyz :=
  Derives.fromBasis (e := prefixDuplicationLaw) <| by simp [basis]

private theorem basisTerminalRetarget :
    Derives basis xyzx xyzy :=
  Derives.fromBasis (e := terminalRetargetLaw) <| by simp [basis]

private theorem basisSquareSuffixSwap :
    Derives basis xyzz yxzz :=
  Derives.fromBasis (e := squareSuffixSwapLaw) <| by simp [basis]

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
theorem derivesRepeatedPrefixExpansion (u v : Word Nat) :
    Derives basis
      ((u ++ u) ++ v)
      (((u ++ u) ++ u) ++ v) := by
  have substituted :=
    Derives.subst basisRepeatedPrefixExpansion
      (instantiateThreeWords u v v)
  simpa [repeatedPrefixExpansionLaw, xxy, xxxy, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Direct block substitution in `xyx = yxy`. -/
theorem derivesAlternatingSwitch (u v : Word Nat) :
    Derives basis
      ((u ++ v) ++ u)
      ((v ++ u) ++ v) := by
  have substituted :=
    Derives.subst basisAlternatingSwitch
      (instantiateThreeWords u v v)
  simpa [alternatingSwitchLaw, xyx, yxy, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

/-- Direct block substitution in `xyx = xxyx`. -/
theorem derivesInitialDuplication (u v : Word Nat) :
    Derives basis
      ((u ++ v) ++ u)
      (((u ++ u) ++ v) ++ u) := by
  have substituted :=
    Derives.subst basisInitialDuplication
      (instantiateThreeWords u v v)
  simpa [initialDuplicationLaw, xyx, xxyx, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

/-- Direct block substitution in `xyx = xyyy`. -/
theorem derivesTerminalCube (u v : Word Nat) :
    Derives basis
      ((u ++ v) ++ u)
      (((u ++ v) ++ v) ++ v) := by
  have substituted :=
    Derives.subst basisTerminalCube (instantiateThreeWords u v v)
  simpa [terminalCubeLaw, xyx, xyyy, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

/-- Direct block substitution in `xyx = xyyxx`. -/
theorem derivesDoublePairExpansion (u v : Word Nat) :
    Derives basis
      ((u ++ v) ++ u)
      ((((u ++ v) ++ v) ++ u) ++ u) := by
  have substituted :=
    Derives.subst basisDoublePairExpansion
      (instantiateThreeWords u v v)
  simpa [doublePairExpansionLaw, xyx, xyyxx, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Direct block substitution in `xyy = xxyy`. -/
theorem derivesPairedPrefixExpansion (u v : Word Nat) :
    Derives basis
      ((u ++ v) ++ v)
      (((u ++ u) ++ v) ++ v) := by
  have substituted :=
    Derives.subst basisPairedPrefixExpansion
      (instantiateThreeWords u v v)
  simpa [pairedPrefixExpansionLaw, xyy, xxyy, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Direct block substitution in `xyz = xxyz`. -/
theorem derivesPrefixDuplication (u v z : Word Nat) :
    Derives basis
      ((u ++ v) ++ z)
      (((u ++ u) ++ v) ++ z) := by
  have substituted :=
    Derives.subst basisPrefixDuplication
      (instantiateThreeWords u v z)
  simpa [prefixDuplicationLaw, xyz, xxyz, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

/-- Direct block substitution in `xyzx = xyzy`. -/
theorem derivesTerminalRetarget (u v z : Word Nat) :
    Derives basis
      (((u ++ v) ++ z) ++ u)
      (((u ++ v) ++ z) ++ v) := by
  have substituted :=
    Derives.subst basisTerminalRetarget
      (instantiateThreeWords u v z)
  simpa [terminalRetargetLaw, xyzx, xyzy, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

/-- Direct block substitution in `xyzz = yxzz`. -/
theorem derivesSquareSuffixSwap (u v z : Word Nat) :
    Derives basis
      (((u ++ v) ++ z) ++ z)
      (((v ++ u) ++ z) ++ z) := by
  have substituted :=
    Derives.subst basisSquareSuffixSwap
      (instantiateThreeWords u v z)
  simpa [squareSuffixSwapLaw, xyzz, yxzz, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

/-- The recorded chain `xyzu -> xyxyzu -> yxyyzu -> yxyxzu -> yxzu`,
with arbitrary nonempty blocks substituted for its variables. -/
theorem derivesPrefixCommutation (u v z t : Word Nat) :
    Derives basis
      (((u ++ v) ++ z) ++ t)
      (((v ++ u) ++ z) ++ t) := by
  have duplicate := derivesPrefixDuplication (u ++ v) z t
  have alternate :=
    Derives.appendRight (derivesAlternatingSwitch u v) ((v ++ z) ++ t)
  have retarget :=
    Derives.appendRight (derivesTerminalRetarget v u v) (z ++ t)
  have contract := (derivesPrefixDuplication (v ++ u) z t).symm
  simp only [Word.append_assoc] at duplicate alternate retarget contract ⊢
  exact duplicate.trans <| alternate.trans <| retarget.trans contract

/-- The recorded direct duplicate deletion `xxyzu -> xyzu`. -/
theorem derivesPrefixDeduplication (u v z t : Word Nat) :
    Derives basis
      ((((u ++ u) ++ v) ++ z) ++ t)
      (((u ++ v) ++ z) ++ t) := by
  simpa [Word.append_assoc] using
    (derivesPrefixDuplication u v (z ++ t)).symm

/-- The recorded chain
`xyyz -> xyyyz -> xyxz -> yxyz -> yxxxz -> yxxz`. -/
theorem derivesPenultimateSwitch (u v z : Word Nat) :
    Derives basis
      (((u ++ v) ++ v) ++ z)
      (((v ++ u) ++ u) ++ z) := by
  have expand :=
    Derives.prepend u (derivesRepeatedPrefixExpansion v z)
  have collapse :=
    Derives.appendRight (derivesTerminalCube u v).symm z
  have alternate :=
    Derives.appendRight (derivesAlternatingSwitch u v) z
  have makeCube :=
    Derives.appendRight (derivesTerminalCube v u) z
  have contract :=
    Derives.prepend v (derivesRepeatedPrefixExpansion u z).symm
  simp only [Word.append_assoc] at expand collapse alternate makeCube contract ⊢
  exact expand.trans <| collapse.trans <| alternate.trans <|
    makeCube.trans contract

/-- The recorded chain `xyyy -> xyx -> yxy -> yxxx`. -/
theorem derivesTerminalCubeSwitch (u v : Word Nat) :
    Derives basis
      (((u ++ v) ++ v) ++ v)
      (((v ++ u) ++ u) ++ u) :=
  (derivesTerminalCube u v).symm |>.trans <|
    (derivesAlternatingSwitch u v).trans <|
      derivesTerminalCube v u

end SemigroupBasis.CoRoots.S5_203
