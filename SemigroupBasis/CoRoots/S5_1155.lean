import SemigroupBasis.FiniteReflection
import SemigroupBasis.Generated.CatalogueOrder3
import SemigroupBasis.Generated.CatalogueOrder4
import SemigroupBasis.Generated.CatalogueOrder5Part10
import SemigroupBasis.Opposite
import SemigroupBasis.TransferPower

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.S5_1155

open SemigroupBasis

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def xx : Word Nat := w 0 [0]
def xxxxx : Word Nat := w 0 [0, 0, 0, 0]
def xy : Word Nat := w 0 [1]
def xyyyy : Word Nat := w 0 [1, 1, 1, 1]
def xxy : Word Nat := w 0 [0, 1]
def yxxyyy : Word Nat := w 1 [0, 0, 1, 1, 1]
def xyz : Word Nat := w 0 [1, 2]
def xzy : Word Nat := w 0 [2, 1]

def xxyyy : Word Nat := w 0 [0, 1, 1, 1]
def yxxyyyyy : Word Nat := w 1 [0, 0, 1, 1, 1, 1, 1]
def yxxyy : Word Nat := w 1 [0, 0, 1, 1]

def powerLaw : Identity Nat := ⟨xx, xxxxx⟩
def tailExpansionLaw : Identity Nat := ⟨xy, xyyyy⟩
def headMovementLaw : Identity Nat := ⟨xxy, yxxyyy⟩
def suffixSwapLaw : Identity Nat := ⟨xyz, xzy⟩
def dualMovementLaw : Identity Nat := ⟨xxyyy, yxxyy⟩

/- The exact ordered four-law system recorded for `S5_1155`. This
foundation records sound finite semantics and explicit derivations only. -/
def basis : List (Identity Nat) :=
  [powerLaw, tailExpansionLaw, headMovementLaw, suffixSwapLaw]

/- The locally stated renamed-reversal comparison system. Only its exact
interderivability with `basis` is asserted below. -/
def dualComparisonBasis : List (Identity Nat) :=
  [powerLaw, tailExpansionLaw, dualMovementLaw, suffixSwapLaw]

def oppositeBasis : List (Identity Nat) :=
  reversedBasis basis

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

/- Exhaustive checks on the three displayed variables lift to the standard
natural-number variable type. This theorem establishes soundness only. -/
theorem models_of_finite_checks
    (candidate : FiniteTable)
    (checked : finiteBasis.all candidate.checkIdentity = true) :
    Models candidate.semigroup basis := by
  intro identity member
  have finiteMember : identity.map toFinThree ∈ finiteBasis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    candidate.checkIdentityNat_sound (identity.map toFinThree)
      ((List.all_eq_true.mp checked) _ finiteMember)
  rw [basis_roundTrip identity member] at finiteValid
  exact finiteValid

abbrev table : FiniteTable :=
  Generated.Catalogue.S5_1155.table

abbrev residueFactorTable : FiniteTable :=
  Generated.Catalogue.S4_125.table

abbrev initialMarkerFactorTable : FiniteTable :=
  Generated.Catalogue.S3_6.table

def tableRowsOneBased : List (List Nat) :=
  List.ofFn fun left : Fin 5 =>
    List.ofFn fun right : Fin 5 =>
      (table.mul left right).val + 1

theorem tableRowsOneBased_certificate :
    tableRowsOneBased =
      [[1, 1, 3, 4, 4],
        [1, 2, 3, 4, 4],
        [3, 3, 4, 1, 1],
        [4, 4, 1, 3, 3],
        [4, 5, 1, 3, 3]] := by
  decide

def residueFactorRowsOneBased : List (List Nat) :=
  List.ofFn fun left : Fin 4 =>
    List.ofFn fun right : Fin 4 =>
      (residueFactorTable.mul left right).val + 1

theorem residueFactorRowsOneBased_certificate :
    residueFactorRowsOneBased =
      [[1, 1, 3, 4],
        [1, 2, 3, 4],
        [3, 3, 4, 1],
        [4, 4, 1, 3]] := by
  decide

def initialMarkerOppositeRowsOneBased : List (List Nat) :=
  List.ofFn fun left : Fin 3 =>
    List.ofFn fun right : Fin 3 =>
      (initialMarkerFactorTable.semigroup.opposite.mul left right).val + 1

theorem initialMarkerOppositeRowsOneBased_certificate :
    initialMarkerOppositeRowsOneBased =
      [[1, 1, 1],
        [1, 1, 2],
        [1, 1, 3]] := by
  decide

set_option maxRecDepth 100000 in
/- Direct finite verification on the exact catalogue table. -/
theorem models : Models table.semigroup basis :=
  models_of_finite_checks table (by decide)

/- The opposite semigroup satisfies the literal reversed system. No
self-duality of the catalogue representative is asserted. -/
theorem oppositeModels :
    Models table.semigroup.opposite oppositeBasis :=
  models.oppositeReversed

/-! ## Exact split factors -/

/- The one-based quotient `[1,2,3,4,4]` onto `S4_125` in its catalogue
orientation, with section `[1,2,3,4]`. -/
def residueQuotient :
    SplitSurjection table.semigroup residueFactorTable.semigroup where
  toFun := fun value =>
    if value.val = 0 then ⟨0, by decide⟩
    else if value.val = 1 then ⟨1, by decide⟩
    else if value.val = 2 then ⟨2, by decide⟩
    else if value.val = 3 then ⟨3, by decide⟩
    else ⟨3, by decide⟩
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  preimage := fun value =>
    if value.val = 0 then ⟨0, by decide⟩
    else if value.val = 1 then ⟨1, by decide⟩
    else if value.val = 2 then ⟨2, by decide⟩
    else ⟨3, by decide⟩
  right_inverse := by
    intro value
    apply Fin.ext
    revert value
    decide

/- The one-based quotient `[1,3,1,1,2]` onto `S3_6` opposite, with
section `[1,5,2]`. The opposite orientation is part of the declaration. -/
def initialMarkerQuotient :
    SplitSurjection table.semigroup
      initialMarkerFactorTable.semigroup.opposite where
  toFun := fun value =>
    if value.val = 0 then ⟨0, by decide⟩
    else if value.val = 1 then ⟨2, by decide⟩
    else if value.val = 2 then ⟨0, by decide⟩
    else if value.val = 3 then ⟨0, by decide⟩
    else ⟨1, by decide⟩
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  preimage := fun value =>
    if value.val = 0 then ⟨0, by decide⟩
    else if value.val = 1 then ⟨4, by decide⟩
    else ⟨1, by decide⟩
  right_inverse := by
    intro value
    apply Fin.ext
    revert value
    decide

def residueQuotientValuesOneBased : List Nat :=
  List.ofFn fun value : Fin 5 =>
    (residueQuotient.toFun value).val + 1

def residueSectionValuesOneBased : List Nat :=
  List.ofFn fun value : Fin 4 =>
    (residueQuotient.preimage value).val + 1

def initialMarkerQuotientValuesOneBased : List Nat :=
  List.ofFn fun value : Fin 5 =>
    (initialMarkerQuotient.toFun value).val + 1

def initialMarkerSectionValuesOneBased : List Nat :=
  List.ofFn fun value : Fin 3 =>
    (initialMarkerQuotient.preimage value).val + 1

theorem residueQuotientValuesOneBased_certificate :
    residueQuotientValuesOneBased = [1, 2, 3, 4, 4] := by
  decide

theorem residueSectionValuesOneBased_certificate :
    residueSectionValuesOneBased = [1, 2, 3, 4] := by
  decide

theorem initialMarkerQuotientValuesOneBased_certificate :
    initialMarkerQuotientValuesOneBased = [1, 3, 1, 1, 2] := by
  decide

theorem initialMarkerSectionValuesOneBased_certificate :
    initialMarkerSectionValuesOneBased = [1, 5, 2] := by
  decide

def factorPairValuesOneBased : List (Nat × Nat) :=
  List.ofFn fun value : Fin 5 =>
    ((residueQuotient.toFun value).val + 1,
      (initialMarkerQuotient.toFun value).val + 1)

theorem factorPairValuesOneBased_certificate :
    factorPairValuesOneBased =
      [(1, 1), (2, 3), (3, 1), (4, 1), (4, 2)] := by
  decide

theorem factorPair_injective :
    Function.Injective fun value =>
      (residueQuotient.toFun value,
        initialMarkerQuotient.toFun value) := by
  intro left right
  revert left right
  decide

private theorem satisfiedBy_of_joint_homs
    {A : Type u} {B : Type v} {C : Type w} {α : Type z}
    {G : Semigroup A} {H : Semigroup B} {K : Semigroup C}
    (left : Hom G H) (right : Hom G K)
    (joint :
      Function.Injective fun value =>
        (left.toFun value, right.toFun value))
    (identity : Identity α)
    (leftValid : identity.SatisfiedBy H)
    (rightValid : identity.SatisfiedBy K) :
    identity.SatisfiedBy G := by
  intro valuation
  apply joint
  apply Prod.ext
  · change
      left.toFun (G.eval valuation identity.lhs) =
        left.toFun (G.eval valuation identity.rhs)
    rw [left.map_eval, left.map_eval]
    exact leftValid (fun x => left.toFun (valuation x))
  · change
      right.toFun (G.eval valuation identity.lhs) =
        right.toFun (G.eval valuation identity.rhs)
    rw [right.map_eval, right.map_eval]
    exact rightValid (fun x => right.toFun (valuation x))

theorem valid_residueFactor (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy residueFactorTable.semigroup :=
  residueQuotient.pushforwardIdentity identity valid

theorem valid_initialMarkerFactor (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy initialMarkerFactorTable.semigroup.opposite :=
  initialMarkerQuotient.pushforwardIdentity identity valid

/- The two factor term functions jointly determine the direct table term
function. This is a semantic identity sandwich, not a basis endpoint. -/
theorem valid_iff_factors (identity : Identity Nat) :
    identity.SatisfiedBy table.semigroup ↔
      identity.SatisfiedBy residueFactorTable.semigroup ∧
        identity.SatisfiedBy
          initialMarkerFactorTable.semigroup.opposite := by
  constructor
  · intro valid
    exact ⟨valid_residueFactor identity valid,
      valid_initialMarkerFactor identity valid⟩
  · rintro ⟨residueValid, markerValid⟩
    exact satisfiedBy_of_joint_homs
      residueQuotient.toHom initialMarkerQuotient.toHom
      factorPair_injective identity residueValid markerValid

/-! ## Intended signature and direct marker -/

def simpleInitialMarker (word : Word Nat) : Option Nat :=
  if word.toList.count word.head = 1 then some word.head else none

structure SameSemanticSignature (left right : Word Nat) : Prop where
  support :
    ∀ letter, letter ∈ left.toList ↔ letter ∈ right.toList
  positiveMultiplicityModuloThree :
    ∀ letter,
      left.toList.count letter % 3 = right.toList.count letter % 3
  simpleInitial :
    simpleInitialMarker left = simpleInitialMarker right

structure LiteralSignature where
  support : List Bool
  positiveMultiplicityModuloThree : List Nat
  simpleInitial : Option Nat
deriving DecidableEq, Repr

def literalSignature (word : Word Nat) : LiteralSignature where
  support := List.ofFn fun letter : Fin 3 =>
    decide (letter.val ∈ word.toList)
  positiveMultiplicityModuloThree := List.ofFn fun letter : Fin 3 =>
    word.toList.count letter.val % 3
  simpleInitial := simpleInitialMarker word

/- This is only a finite computation on the four literal law pairs. -/
theorem literalBasisSignaturesAgree :
    basis.all (fun identity =>
      decide (literalSignature identity.lhs =
        literalSignature identity.rhs)) = true := by
  decide

/- Assign the tested variable to one-based element `5` and every other
variable to element `2`, as in the authoritative finite marker. -/
def signatureMarkerValuation (selected : Nat) : Nat → Fin 5 :=
  fun letter =>
    if letter = selected then ⟨4, by decide⟩ else ⟨1, by decide⟩

def signatureMarkerValuation01OneBased : List Nat :=
  List.ofFn fun letter : Fin 2 =>
    (signatureMarkerValuation 0 letter.val).val + 1

theorem signatureMarkerValuation01OneBased_certificate :
    signatureMarkerValuation01OneBased = [5, 2] := by
  decide

def signatureMarkerProbeWords : List (Word Nat) :=
  [w 1 [], w 0 [1], w 0 [0, 0, 0], w 0 [0], w 0 [0, 0]]

def signatureMarkerOutputsOneBased : List Nat :=
  signatureMarkerProbeWords.map fun word =>
    (table.semigroup.eval (signatureMarkerValuation 0) word).val + 1

theorem signatureMarkerOutputsOneBased_certificate :
    signatureMarkerOutputsOneBased = [2, 5, 4, 3, 1] := by
  decide

private theorem residueFactorModels :
    Models residueFactorTable.semigroup basis := by
  intro identity member
  exact valid_residueFactor identity (models identity member)

private theorem initialMarkerFactorModels :
    Models initialMarkerFactorTable.semigroup.opposite basis := by
  intro identity member
  exact valid_initialMarkerFactor identity (models identity member)

/- Every authored derivation preserves both exact factor theories. No
converse syntactic theorem is asserted. -/
theorem derives_factorSemantics {left right : Word Nat}
    (derivation : Derives basis left right) :
    (Identity.mk left right).SatisfiedBy residueFactorTable.semigroup ∧
      (Identity.mk left right).SatisfiedBy
        initialMarkerFactorTable.semigroup.opposite := by
  constructor
  · intro valuation
    exact derivation.sound residueFactorModels valuation
  · intro valuation
    exact derivation.sound initialMarkerFactorModels valuation

/-! ## Primitive substitutions and the local dual bridge -/

private def instantiateThreeWords
    (u v z : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => z
  | n + 3 => Word.singleton (n + 3)

private theorem basisPower : Derives basis xx xxxxx :=
  Derives.fromBasis (e := powerLaw) <| by simp [basis]

private theorem basisTailExpansion : Derives basis xy xyyyy :=
  Derives.fromBasis (e := tailExpansionLaw) <| by simp [basis]

private theorem basisHeadMovement : Derives basis xxy yxxyyy :=
  Derives.fromBasis (e := headMovementLaw) <| by simp [basis]

private theorem basisSuffixSwap : Derives basis xyz xzy :=
  Derives.fromBasis (e := suffixSwapLaw) <| by simp [basis]

theorem derivesPowerExpansion (u : Word Nat) :
    Derives basis (u ++ u) ((((u ++ u) ++ u) ++ u) ++ u) := by
  have substituted :=
    Derives.subst basisPower (instantiateThreeWords u u u)
  simpa [xx, xxxxx, w, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

theorem derivesTailExpansion (u v : Word Nat) :
    Derives basis (u ++ v) ((((u ++ v) ++ v) ++ v) ++ v) := by
  have substituted :=
    Derives.subst basisTailExpansion (instantiateThreeWords u v v)
  simpa [xy, xyyyy, w, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

theorem derivesHeadMovement (u v : Word Nat) :
    Derives basis ((u ++ u) ++ v)
      (((((v ++ u) ++ u) ++ v) ++ v) ++ v) := by
  have substituted :=
    Derives.subst basisHeadMovement (instantiateThreeWords u v v)
  simpa [xxy, yxxyyy, w, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

theorem derivesSuffixSwap (u v z : Word Nat) :
    Derives basis ((u ++ v) ++ z) ((u ++ z) ++ v) := by
  have substituted :=
    Derives.subst basisSuffixSwap (instantiateThreeWords u v z)
  simpa [xyz, xzy, w, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/- The mechanically replayed chain
`u^2 v^3 -> v u^2 v^5 -> v u^2 v^2`. -/
theorem derivesDualMovement (u v : Word Nat) :
    Derives basis ((((u ++ u) ++ v) ++ v) ++ v)
      ((((v ++ u) ++ u) ++ v) ++ v) := by
  have moved :=
    Derives.appendRight (derivesHeadMovement u v) (v ++ v)
  have contracted :=
    Derives.prepend (v ++ u) <|
      Derives.appendRight (Derives.symm (derivesTailExpansion u v)) v
  apply Derives.trans
  · simpa [Word.append_assoc] using moved
  · simpa [Word.append_assoc] using contracted

private theorem dualBasisPower :
    Derives dualComparisonBasis xx xxxxx :=
  Derives.fromBasis (e := powerLaw) <| by simp [dualComparisonBasis]

private theorem dualBasisTailExpansion :
    Derives dualComparisonBasis xy xyyyy :=
  Derives.fromBasis (e := tailExpansionLaw) <| by
    simp [dualComparisonBasis]

private theorem dualBasisMovement :
    Derives dualComparisonBasis xxyyy yxxyy :=
  Derives.fromBasis (e := dualMovementLaw) <| by
    simp [dualComparisonBasis]

private theorem dualBasisSuffixSwap :
    Derives dualComparisonBasis xyz xzy :=
  Derives.fromBasis (e := suffixSwapLaw) <| by
    simp [dualComparisonBasis]

private theorem dualDerivesTailExpansion (u v : Word Nat) :
    Derives dualComparisonBasis (u ++ v)
      ((((u ++ v) ++ v) ++ v) ++ v) := by
  have substituted :=
    Derives.subst dualBasisTailExpansion (instantiateThreeWords u v v)
  simpa [xy, xyyyy, w, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

private theorem dualDerivesMovement (u v : Word Nat) :
    Derives dualComparisonBasis ((((u ++ u) ++ v) ++ v) ++ v)
      ((((v ++ u) ++ u) ++ v) ++ v) := by
  have substituted :=
    Derives.subst dualBasisMovement (instantiateThreeWords u v v)
  simpa [xxyyy, yxxyy, w, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/- Conversely, the original movement follows in the comparison system by
`u^2 v -> u^2 v^4 -> v u^2 v^3`. -/
theorem derivesHeadMovementFromDual (u v : Word Nat) :
    Derives dualComparisonBasis ((u ++ u) ++ v)
      (((((v ++ u) ++ u) ++ v) ++ v) ++ v) := by
  have expanded := Derives.prepend u (dualDerivesTailExpansion u v)
  have moved := Derives.appendRight (dualDerivesMovement u v) v
  apply Derives.trans
  · simpa [Word.append_assoc] using expanded
  · simpa [Word.append_assoc] using moved

private theorem basisAxiomsDeriveFromDual
    (identity : Identity Nat) (member : identity ∈ basis) :
    Derives dualComparisonBasis identity.lhs identity.rhs := by
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact dualBasisPower
  · exact dualBasisTailExpansion
  · simpa [xxy, yxxyyy, w, Word.singleton, Word.append,
      Word.append_assoc] using
        derivesHeadMovementFromDual (Word.singleton 0) (Word.singleton 1)
  · exact dualBasisSuffixSwap

private theorem dualAxiomsDeriveFromBasis
    (identity : Identity Nat) (member : identity ∈ dualComparisonBasis) :
    Derives basis identity.lhs identity.rhs := by
  simp only [dualComparisonBasis, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact basisPower
  · exact basisTailExpansion
  · simpa [xxyyy, yxxyy, w, Word.singleton, Word.append,
      Word.append_assoc] using
        derivesDualMovement (Word.singleton 0) (Word.singleton 1)
  · exact basisSuffixSwap

theorem derivesInDualComparison {left right : Word Nat}
    (derivation : Derives basis left right) :
    Derives dualComparisonBasis left right :=
  derivation.transport basisAxiomsDeriveFromDual

theorem derivesFromDualComparison {left right : Word Nat}
    (derivation : Derives dualComparisonBasis left right) :
    Derives basis left right :=
  derivation.transport dualAxiomsDeriveFromBasis

theorem derives_iff_dualComparison {left right : Word Nat} :
    Derives basis left right ↔
      Derives dualComparisonBasis left right :=
  ⟨derivesInDualComparison, derivesFromDualComparison⟩

/-! ## Explicitly unwitnessed obligations -/

/- The first honest blocker: retargeting an arbitrary repeated head inside
an arbitrary word while retaining the intended signature. -/
structure RepeatedHeadNormalizationObligation : Prop where
  retarget :
    ∀ (word : Word Nat) (selected : Nat),
      2 ≤ word.toList.count word.head →
      selected ∈ word.toList →
      ∃ normalized : Word Nat,
        normalized.head = selected ∧
        2 ≤ normalized.toList.count selected ∧
        SameSemanticSignature word normalized ∧
        Derives basis word normalized

/- The next blocker after repeated-head normalization. No inhabitant is
provided and no unrestricted derivation theorem follows from this source. -/
structure CanonicalCompletenessObligation
    (_normalization : RepeatedHeadNormalizationObligation) : Prop where
  derive :
    ∀ left right : Word Nat,
      SameSemanticSignature left right →
      Derives basis left right

/- Exact finite chains replayed by the metadata-only packet. -/
def recordedFiniteChains : List (List (Word Nat)) :=
  [
    [w 0 [0], w 0 [0, 0, 0, 0]],
    [w 0 [1], w 0 [1, 1, 1, 1]],
    [w 0 [0, 1], w 1 [0, 0, 1, 1, 1]],
    [w 0 [1, 2], w 0 [2, 1]],
    [w 0 [0, 1, 1, 1],
      w 1 [0, 0, 1, 1, 1, 1, 1],
      w 1 [0, 0, 1, 1]]
  ]

/- The source intentionally stops at the two unwitnessed obligations. -/

end SemigroupBasis.CoRoots.S5_1155
