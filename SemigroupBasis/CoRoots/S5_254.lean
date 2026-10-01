import SemigroupBasis.FiniteReflection
import SemigroupBasis.Generated.CatalogueOrder5Part02
import SemigroupBasis.Opposite

namespace SemigroupBasis.CoRoots.S5_254

open SemigroupBasis

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def xx : Word Nat := w 0 [0]
def xxxx : Word Nat := w 0 [0, 0, 0]
def xxxyx : Word Nat := w 0 [0, 0, 1, 0]
def xyx : Word Nat := w 0 [1, 0]
def xxy : Word Nat := w 0 [0, 1]
def yxx : Word Nat := w 1 [0, 0]
def xxzwz : Word Nat := w 0 [0, 2, 3, 2]
def xzxwz : Word Nat := w 0 [2, 0, 3, 2]
def xxzz : Word Nat := w 0 [0, 2, 2]
def xzxz : Word Nat := w 0 [2, 0, 2]
def xyxwy : Word Nat := w 0 [1, 0, 3, 1]
def yxxwy : Word Nat := w 1 [0, 0, 3, 1]
def xyxy : Word Nat := w 0 [1, 0, 1]
def yxxy : Word Nat := w 1 [0, 0, 1]
def xyxzwz : Word Nat := w 0 [1, 0, 2, 3, 2]
def xyzxwz : Word Nat := w 0 [1, 2, 0, 3, 2]
def xyxzz : Word Nat := w 0 [1, 0, 2, 2]
def xyzxz : Word Nat := w 0 [1, 2, 0, 2]
def xyzwxz : Word Nat := w 0 [1, 2, 3, 0, 2]
def xyzwzx : Word Nat := w 0 [1, 2, 3, 2, 0]
def xyzxwy : Word Nat := w 0 [1, 2, 0, 3, 1]
def yxzxwy : Word Nat := w 1 [0, 2, 0, 3, 1]
def xyzxy : Word Nat := w 0 [1, 2, 0, 1]
def yxzxy : Word Nat := w 1 [0, 2, 0, 1]
def xyzzx : Word Nat := w 0 [1, 2, 2, 0]
def xzwxz : Word Nat := w 0 [2, 3, 0, 2]
def xzwzx : Word Nat := w 0 [2, 3, 2, 0]
def xzzx : Word Nat := w 0 [2, 2, 0]

def powerLaw : Identity Nat := ⟨xx, xxxx⟩
def sandwichContractionLaw : Identity Nat := ⟨xxxyx, xyx⟩
def prefixRotationLaw : Identity Nat := ⟨xxy, yxx⟩
def zwzPrefixLaw : Identity Nat := ⟨xxzwz, xzxwz⟩
def doubleZPrefixLaw : Identity Nat := ⟨xxzz, xzxz⟩
def wyRotationLaw : Identity Nat := ⟨xyxwy, yxxwy⟩
def alternatingPairLaw : Identity Nat := ⟨xyxy, yxxy⟩
def longZwzTransportLaw : Identity Nat := ⟨xyxzwz, xyzxwz⟩
def doubleZTransportLaw : Identity Nat := ⟨xyxzz, xyzxz⟩
def crossedWZLaw : Identity Nat := ⟨xyzwxz, xyzwzx⟩
def wyPrefixTransportLaw : Identity Nat := ⟨xyzxwy, yxzxwy⟩
def terminalYTransportLaw : Identity Nat := ⟨xyzxy, yxzxy⟩
def terminalZTransportLaw : Identity Nat := ⟨xyzxz, xyzzx⟩
def wzCrossingLaw : Identity Nat := ⟨xzwxz, xzwzx⟩
def alternatingZLaw : Identity Nat := ⟨xzxz, xzzx⟩

/-- The exact ordered fifteen-law basis recorded for Edmunds' monoid M18
and catalogue representative `S5_254`. This definition does not assert an
unrestricted completeness endpoint. -/
def basis : List (Identity Nat) :=
  [powerLaw, sandwichContractionLaw, prefixRotationLaw, zwzPrefixLaw,
    doubleZPrefixLaw, wyRotationLaw, alternatingPairLaw,
    longZwzTransportLaw, doubleZTransportLaw, crossedWZLaw,
    wyPrefixTransportLaw, terminalYTransportLaw, terminalZTransportLaw,
    wzCrossingLaw, alternatingZLaw]

def oppositeBasis : List (Identity Nat) :=
  reversedBasis basis

/-- Extensional support agreement. -/
def SameSupport (left right : Word Nat) : Prop :=
  ∀ letter, letter ∈ left.toList ↔ letter ∈ right.toList

/-- Pointwise parity agreement for total occurrence counts. -/
def SameTotalParity (left right : Word Nat) : Prop :=
  ∀ letter,
    left.toList.count letter % 2 = right.toList.count letter % 2

/-- A variable is globally simple when it occurs exactly once in the word. -/
def GloballySimple (word : Word Nat) (letter : Nat) : Prop :=
  word.toList.count letter = 1

/-- Agreement on the set of globally simple variables. -/
def SameGloballySimpleVariables (left right : Word Nat) : Prop :=
  ∀ letter, GloballySimple left letter ↔ GloballySimple right letter

/-- `parity` is the occurrence parity of `letter` in a prefix ending just
before one occurrence of `separator`. For a globally simple separator the
split is unique, but the definition deliberately records only the split
relation needed by the future proof. -/
def PrefixParityBefore
    (word : Word Nat) (separator letter parity : Nat) : Prop :=
  ∃ before after,
    word.toList = before ++ separator :: after ∧
      before.count letter % 2 = parity

/-- Agreement of all prefix parities before every separator that is globally
simple in both words. No derivational sufficiency claim is attached to this
relation. -/
def SamePrefixParityBeforeSimpleSeparators
    (left right : Word Nat) : Prop :=
  ∀ separator,
    GloballySimple left separator →
      GloballySimple right separator →
        ∀ letter parity,
          PrefixParityBefore left separator letter parity ↔
            PrefixParityBefore right separator letter parity

/-- The M18 signature used by the canonicalization and concrete-table
semantics layers. Its four components are proved sufficient in
`S5_254Canonical` and necessary in `S5_254Semantics`. -/
structure SameM18Signature (left right : Word Nat) : Prop where
  support : SameSupport left right
  totalParity : SameTotalParity left right
  globallySimple : SameGloballySimpleVariables left right
  prefixParity : SamePrefixParityBeforeSimpleSeparators left right

private def toFinFour : Nat → Fin 4
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 3

def finiteBasis : List (Identity (Fin 4)) :=
  basis.map fun identity => identity.map toFinFour

private theorem basis_roundTrip_checked :
    basis.all (fun identity =>
      decide ((identity.map toFinFour).map Fin.val = identity)) = true := by
  decide

private theorem basis_roundTrip
    (identity : Identity Nat) (member : identity ∈ basis) :
    (identity.map toFinFour).map Fin.val = identity := by
  exact of_decide_eq_true <|
    (List.all_eq_true.mp basis_roundTrip_checked) identity member

theorem models_of_finite_checks
    (candidate : FiniteTable)
    (checked : finiteBasis.all candidate.checkIdentity = true) :
    Models candidate.semigroup basis := by
  intro identity member
  have finiteMember : identity.map toFinFour ∈ finiteBasis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    candidate.checkIdentityNat_sound (identity.map toFinFour)
      ((List.all_eq_true.mp checked) _ finiteMember)
  rw [basis_roundTrip identity member] at finiteValid
  exact finiteValid

abbrev table : FiniteTable :=
  Generated.Catalogue.S5_254.table

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem models : Models table.semigroup basis :=
  models_of_finite_checks table (by decide)

theorem oppositeModels :
    Models table.semigroup.opposite oppositeBasis :=
  models.oppositeReversed

private theorem basisPower : Derives basis xx xxxx :=
  Derives.fromBasis (e := powerLaw) <| by simp [basis]

private theorem basisSandwichContraction : Derives basis xxxyx xyx :=
  Derives.fromBasis (e := sandwichContractionLaw) <| by simp [basis]

private theorem basisPrefixRotation : Derives basis xxy yxx :=
  Derives.fromBasis (e := prefixRotationLaw) <| by simp [basis]

private theorem basisZwzPrefix : Derives basis xxzwz xzxwz :=
  Derives.fromBasis (e := zwzPrefixLaw) <| by simp [basis]

private theorem basisDoubleZPrefix : Derives basis xxzz xzxz :=
  Derives.fromBasis (e := doubleZPrefixLaw) <| by simp [basis]

private theorem basisWyRotation : Derives basis xyxwy yxxwy :=
  Derives.fromBasis (e := wyRotationLaw) <| by simp [basis]

private theorem basisAlternatingPair : Derives basis xyxy yxxy :=
  Derives.fromBasis (e := alternatingPairLaw) <| by simp [basis]

private theorem basisLongZwzTransport : Derives basis xyxzwz xyzxwz :=
  Derives.fromBasis (e := longZwzTransportLaw) <| by simp [basis]

private theorem basisDoubleZTransport : Derives basis xyxzz xyzxz :=
  Derives.fromBasis (e := doubleZTransportLaw) <| by simp [basis]

private theorem basisCrossedWZ : Derives basis xyzwxz xyzwzx :=
  Derives.fromBasis (e := crossedWZLaw) <| by simp [basis]

private theorem basisWyPrefixTransport : Derives basis xyzxwy yxzxwy :=
  Derives.fromBasis (e := wyPrefixTransportLaw) <| by simp [basis]

private theorem basisTerminalYTransport : Derives basis xyzxy yxzxy :=
  Derives.fromBasis (e := terminalYTransportLaw) <| by simp [basis]

private theorem basisTerminalZTransport : Derives basis xyzxz xyzzx :=
  Derives.fromBasis (e := terminalZTransportLaw) <| by simp [basis]

private theorem basisWzCrossing : Derives basis xzwxz xzwzx :=
  Derives.fromBasis (e := wzCrossingLaw) <| by simp [basis]

private theorem basisAlternatingZ : Derives basis xzxz xzzx :=
  Derives.fromBasis (e := alternatingZLaw) <| by simp [basis]

/-- Every substituted word is nonempty because substitutions target `Word`,
not a monoid word type. -/
theorem derivesPowerSubstitution (substitution : Nat → Word Nat) :
    Derives basis (xx.bind substitution) (xxxx.bind substitution) :=
  Derives.subst basisPower substitution

theorem derivesSandwichContractionSubstitution
    (substitution : Nat → Word Nat) :
    Derives basis (xxxyx.bind substitution) (xyx.bind substitution) :=
  Derives.subst basisSandwichContraction substitution

theorem derivesPrefixRotationSubstitution
    (substitution : Nat → Word Nat) :
    Derives basis (xxy.bind substitution) (yxx.bind substitution) :=
  Derives.subst basisPrefixRotation substitution

theorem derivesZwzPrefixSubstitution (substitution : Nat → Word Nat) :
    Derives basis (xxzwz.bind substitution) (xzxwz.bind substitution) :=
  Derives.subst basisZwzPrefix substitution

theorem derivesDoubleZPrefixSubstitution
    (substitution : Nat → Word Nat) :
    Derives basis (xxzz.bind substitution) (xzxz.bind substitution) :=
  Derives.subst basisDoubleZPrefix substitution

theorem derivesWyRotationSubstitution (substitution : Nat → Word Nat) :
    Derives basis (xyxwy.bind substitution) (yxxwy.bind substitution) :=
  Derives.subst basisWyRotation substitution

theorem derivesAlternatingPairSubstitution
    (substitution : Nat → Word Nat) :
    Derives basis (xyxy.bind substitution) (yxxy.bind substitution) :=
  Derives.subst basisAlternatingPair substitution

theorem derivesLongZwzTransportSubstitution
    (substitution : Nat → Word Nat) :
    Derives basis (xyxzwz.bind substitution) (xyzxwz.bind substitution) :=
  Derives.subst basisLongZwzTransport substitution

theorem derivesDoubleZTransportSubstitution
    (substitution : Nat → Word Nat) :
    Derives basis (xyxzz.bind substitution) (xyzxz.bind substitution) :=
  Derives.subst basisDoubleZTransport substitution

theorem derivesCrossedWZSubstitution (substitution : Nat → Word Nat) :
    Derives basis (xyzwxz.bind substitution) (xyzwzx.bind substitution) :=
  Derives.subst basisCrossedWZ substitution

theorem derivesWyPrefixTransportSubstitution
    (substitution : Nat → Word Nat) :
    Derives basis (xyzxwy.bind substitution) (yxzxwy.bind substitution) :=
  Derives.subst basisWyPrefixTransport substitution

theorem derivesTerminalYTransportSubstitution
    (substitution : Nat → Word Nat) :
    Derives basis (xyzxy.bind substitution) (yxzxy.bind substitution) :=
  Derives.subst basisTerminalYTransport substitution

theorem derivesTerminalZTransportSubstitution
    (substitution : Nat → Word Nat) :
    Derives basis (xyzxz.bind substitution) (xyzzx.bind substitution) :=
  Derives.subst basisTerminalZTransport substitution

theorem derivesWzCrossingSubstitution (substitution : Nat → Word Nat) :
    Derives basis (xzwxz.bind substitution) (xzwzx.bind substitution) :=
  Derives.subst basisWzCrossing substitution

theorem derivesAlternatingZSubstitution
    (substitution : Nat → Word Nat) :
    Derives basis (xzxz.bind substitution) (xzzx.bind substitution) :=
  Derives.subst basisAlternatingZ substitution

end SemigroupBasis.CoRoots.S5_254
