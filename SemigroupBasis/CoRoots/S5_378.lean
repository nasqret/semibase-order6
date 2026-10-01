import SemigroupBasis.Examples.CommutativeExponentThree
import SemigroupBasis.Examples.UniqueSeparatorFourInvariant
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Generated.CatalogueOrder5Part03
import SemigroupBasis.Generated.S3_8
import SemigroupBasis.Generated.S4_69
import SemigroupBasis.Opposite
import SemigroupBasis.TransferPower

namespace SemigroupBasis.CoRoots.S5_378

open SemigroupBasis

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def xx : Word Nat := w 0 [0]
def xxx : Word Nat := w 0 [0, 0]
def xyx : Word Nat := w 0 [1, 0]
def xxyx : Word Nat := w 0 [0, 1, 0]
def xyxx : Word Nat := w 0 [1, 0, 0]
def xxyy : Word Nat := w 0 [0, 1, 1]
def xyxy : Word Nat := w 0 [1, 0, 1]
def xyyx : Word Nat := w 0 [1, 1, 0]
def yxxy : Word Nat := w 1 [0, 0, 1]
def xyzx : Word Nat := w 0 [1, 2, 0]
def xzyx : Word Nat := w 0 [2, 1, 0]

def powerLaw : Identity Nat := ⟨xx, xxx⟩
def leftDuplicationLaw : Identity Nat := ⟨xyx, xxyx⟩
def rightDuplicationLaw : Identity Nat := ⟨xyx, xyxx⟩
def squareInterleaveLaw : Identity Nat := ⟨xxyy, xyxy⟩
def squareFinalSwitchLaw : Identity Nat := ⟨xxyy, xyyx⟩
def squareInitialSwitchLaw : Identity Nat := ⟨xxyy, yxxy⟩
def closedInteriorSwapLaw : Identity Nat := ⟨xyzx, xzyx⟩

/-- The exact ordered seven-law basis recorded for catalogue class `S5_378`.
This file asserts finite semantics and finite derivations only. -/
def basis : List (Identity Nat) :=
  [powerLaw, leftDuplicationLaw, rightDuplicationLaw,
    squareInterleaveLaw, squareFinalSwitchLaw,
    squareInitialSwitchLaw, closedInteriorSwapLaw]

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

/-- Exhaustive checks on the three displayed variables lift to natural-number
variables. This theorem does not assert completeness. -/
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
  Generated.Catalogue.S5_378.table

set_option maxRecDepth 100000 in
/-- The direct Smallsemi representative satisfies the seven recorded laws. -/
theorem models : Models table.semigroup basis :=
  models_of_finite_checks table (by decide)

/-- The opposite representative satisfies the literal reversed laws. -/
theorem oppositeModels :
    Models table.semigroup.opposite oppositeBasis :=
  models.oppositeReversed

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

/-- The recorded homomorphic copy `[1,3,4,5]` of `S4_69`. -/
def separatorEmbedding :
    Embedding Generated.S4_69.table.semigroup table.semigroup where
  toFun := fun a =>
    if a.val = 0 then ⟨0, by decide⟩ else
      if a.val = 1 then ⟨2, by decide⟩ else
        if a.val = 2 then ⟨3, by decide⟩ else ⟨4, by decide⟩
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  injective := by
    intro a b
    revert a b
    decide

/-- The recorded separator quotient `[1,1,2,3,4]`. -/
def separatorQuotient :
    SplitSurjection table.semigroup Generated.S4_69.table.semigroup where
  toFun := fun a =>
    if a.val = 0 then ⟨0, by decide⟩ else
      if a.val = 1 then ⟨0, by decide⟩ else
        if a.val = 2 then ⟨1, by decide⟩ else
          if a.val = 3 then ⟨2, by decide⟩ else ⟨3, by decide⟩
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  preimage := separatorEmbedding.toFun
  right_inverse := by
    intro b
    apply Fin.ext
    revert b
    decide

/-- The recorded homomorphic copy `[1,2,5]` of `S3_8 = N_2^1`. -/
def multiplicityEmbedding :
    Embedding Generated.S3_8.table.semigroup table.semigroup where
  toFun := fun a =>
    if a.val = 0 then ⟨0, by decide⟩ else
      if a.val = 1 then ⟨1, by decide⟩ else ⟨4, by decide⟩
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  injective := by
    intro a b
    revert a b
    decide

/-- The recorded multiplicity quotient `[1,2,1,1,3]`. -/
def multiplicityQuotient :
    SplitSurjection table.semigroup Generated.S3_8.table.semigroup where
  toFun := fun a =>
    if a.val = 0 then ⟨0, by decide⟩ else
      if a.val = 1 then ⟨1, by decide⟩ else
        if a.val = 4 then ⟨2, by decide⟩ else ⟨0, by decide⟩
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  preimage := multiplicityEmbedding.toFun
  right_inverse := by
    intro b
    apply Fin.ext
    revert b
    decide

/-- The five recorded product images are pairwise distinct. -/
theorem factorPair_injective :
    Function.Injective fun a =>
      (separatorQuotient.toFun a, multiplicityQuotient.toFun a) := by
  intro a b
  revert a b
  decide

theorem valid_s4_69 (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy Generated.S4_69.table.semigroup :=
  separatorQuotient.pushforwardIdentity identity valid

theorem valid_s3_8 (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy Generated.S3_8.table.semigroup :=
  multiplicityQuotient.pushforwardIdentity identity valid

/-- The two quotient term functions jointly determine the target term
function. This is a semantic identity sandwich, not a derivational endpoint. -/
theorem valid_iff_factors (identity : Identity Nat) :
    identity.SatisfiedBy table.semigroup ↔
      identity.SatisfiedBy Generated.S4_69.table.semigroup ∧
        identity.SatisfiedBy Generated.S3_8.table.semigroup := by
  constructor
  · intro valid
    exact ⟨valid_s4_69 identity valid, valid_s3_8 identity valid⟩
  · rintro ⟨separatorValid, multiplicityValid⟩
    exact satisfiedBy_of_joint_homs
      separatorQuotient.toHom multiplicityQuotient.toHom
      factorPair_injective identity separatorValid multiplicityValid

/-- Extensional support agreement. -/
def SameSupport (left right : Word Nat) : Prop :=
  ∀ letter, letter ∈ left.toList ↔ letter ∈ right.toList

/-- One exact unique-separator cut with prescribed side supports. -/
def ExactCutSignature
    (word : Word Nat) (separator : Nat)
    (leftSupport rightSupport : List Nat) : Prop :=
  ∃ left right,
    Examples.UniqueSeparatorFourExactCut
        word.toList left separator right ∧
      (∀ letter, letter ∈ left ↔ letter ∈ leftSupport) ∧
      (∀ letter, letter ∈ right ↔ letter ∈ rightSupport)

/-- Agreement on every exact unique-separator cut. -/
def SameExactCutSignature (left right : Word Nat) : Prop :=
  ∀ separator leftSupport rightSupport,
    ExactCutSignature left separator leftSupport rightSupport ↔
      ExactCutSignature right separator leftSupport rightSupport

def GloballySimple (word : Word Nat) (letter : Nat) : Prop :=
  word.toList.count letter = 1

def SameGloballySimpleVariables (left right : Word Nat) : Prop :=
  ∀ letter, GloballySimple left letter ↔ GloballySimple right letter

/-- The necessary semantic signature exposed by the certified factors. No
claim here says that equal signatures are derivable from `basis`. -/
structure SameSeparatorSimpleSignature
    (left right : Word Nat) : Prop where
  support : SameSupport left right
  exactCuts : SameExactCutSignature left right
  globallySimple : SameGloballySimpleVariables left right

private theorem cappedCount_eq_one_iff (count : Nat) :
    min count 2 = 1 ↔ count = 1 := by
  omega

/-- Validity in the two factors supplies the separator/simple signature. -/
theorem sameSignature_of_factors
    (identity : Identity Nat)
    (separatorValid :
      identity.SatisfiedBy Generated.S4_69.table.semigroup)
    (multiplicityValid :
      identity.SatisfiedBy Generated.S3_8.table.semigroup) :
    SameSeparatorSimpleSignature identity.lhs identity.rhs := by
  have generatedSeparatorValid :
      identity.SatisfiedBy Generated.S4_69.table.semigroup :=
    separatorValid
  have semanticSeparatorValid :
      identity.SatisfiedBy Examples.uniqueSeparatorFour.semigroup := by
    simpa only [Generated.S4_69.table_eq_catalogue_model] using
      generatedSeparatorValid
  have semanticMultiplicityValid :
      identity.SatisfiedBy Examples.commutativeExponentThree.semigroup := by
    simpa only [Generated.S3_8.table_eq_catalogue_model] using
      multiplicityValid
  refine ⟨?_, ?_, ?_⟩
  · intro letter
    exact Examples.uniqueSeparatorFourValid_support_iff
      identity semanticSeparatorValid letter
  · intro separator leftSupport rightSupport
    simpa only [ExactCutSignature] using
      Examples.uniqueSeparatorFourEqualEval_exactCut_iff
        identity.lhs identity.rhs semanticSeparatorValid
        separator leftSupport rightSupport
  · intro letter
    have capped :=
      Examples.exponentValid_capped_count_eq
        identity semanticMultiplicityValid letter
    constructor
    · intro leftSimple
      have leftCapped : min (identity.lhs.toList.count letter) 2 = 1 :=
        (cappedCount_eq_one_iff _).2 leftSimple
      have rightCapped : min (identity.rhs.toList.count letter) 2 = 1 := by
        rw [← capped]
        exact leftCapped
      exact (cappedCount_eq_one_iff _).1 rightCapped
    · intro rightSimple
      have rightCapped : min (identity.rhs.toList.count letter) 2 = 1 :=
        (cappedCount_eq_one_iff _).2 rightSimple
      have leftCapped : min (identity.lhs.toList.count letter) 2 = 1 := by
        rw [capped]
        exact rightCapped
      exact (cappedCount_eq_one_iff _).1 leftCapped

theorem valid_sameSignature
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    SameSeparatorSimpleSignature identity.lhs identity.rhs :=
  sameSignature_of_factors identity
    (valid_s4_69 identity valid) (valid_s3_8 identity valid)

private theorem s4_69Models :
    Models Generated.S4_69.table.semigroup basis :=
  models_of_finite_checks Generated.S4_69.table (by decide)

private theorem s3_8Models :
    Models Generated.S3_8.table.semigroup basis :=
  models_of_finite_checks Generated.S3_8.table (by decide)

/-- Every finite derivation preserves the necessary factor signature. -/
theorem derives_sameSignature {left right : Word Nat}
    (derivation : Derives basis left right) :
    SameSeparatorSimpleSignature left right :=
  sameSignature_of_factors ⟨left, right⟩
    (fun valuation => derivation.sound s4_69Models valuation)
    (fun valuation => derivation.sound s3_8Models valuation)

private def instantiateThreeWords
    (u v z : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => z
  | n + 3 => Word.singleton (n + 3)

private theorem basisPower : Derives basis xx xxx :=
  Derives.fromBasis (e := powerLaw) <| by simp [basis]

private theorem basisLeftDuplication : Derives basis xyx xxyx :=
  Derives.fromBasis (e := leftDuplicationLaw) <| by simp [basis]

private theorem basisRightDuplication : Derives basis xyx xyxx :=
  Derives.fromBasis (e := rightDuplicationLaw) <| by simp [basis]

private theorem basisSquareInterleave : Derives basis xxyy xyxy :=
  Derives.fromBasis (e := squareInterleaveLaw) <| by simp [basis]

private theorem basisSquareFinalSwitch : Derives basis xxyy xyyx :=
  Derives.fromBasis (e := squareFinalSwitchLaw) <| by simp [basis]

private theorem basisSquareInitialSwitch : Derives basis xxyy yxxy :=
  Derives.fromBasis (e := squareInitialSwitchLaw) <| by simp [basis]

private theorem basisClosedInteriorSwap : Derives basis xyzx xzyx :=
  Derives.fromBasis (e := closedInteriorSwapLaw) <| by simp [basis]

theorem derivesPowerExpansion (u : Word Nat) :
    Derives basis (u ++ u) ((u ++ u) ++ u) := by
  have substituted :=
    Derives.subst basisPower (instantiateThreeWords u u u)
  simpa [xx, xxx, w, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem derivesLeftDuplication (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) (((u ++ u) ++ v) ++ u) := by
  have substituted :=
    Derives.subst basisLeftDuplication
      (instantiateThreeWords u v v)
  simpa [xyx, xxyx, w, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem derivesRightDuplication (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) (((u ++ v) ++ u) ++ u) := by
  have substituted :=
    Derives.subst basisRightDuplication
      (instantiateThreeWords u v v)
  simpa [xyx, xyxx, w, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem derivesSquareInterleave (u v : Word Nat) :
    Derives basis ((u ++ u) ++ (v ++ v)) (((u ++ v) ++ u) ++ v) := by
  have substituted :=
    Derives.subst basisSquareInterleave
      (instantiateThreeWords u v v)
  simpa [xxyy, xyxy, w, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem derivesSquareFinalSwitch (u v : Word Nat) :
    Derives basis ((u ++ u) ++ (v ++ v)) (((u ++ v) ++ v) ++ u) := by
  have substituted :=
    Derives.subst basisSquareFinalSwitch
      (instantiateThreeWords u v v)
  simpa [xxyy, xyyx, w, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem derivesSquareInitialSwitch (u v : Word Nat) :
    Derives basis ((u ++ u) ++ (v ++ v)) (((v ++ u) ++ u) ++ v) := by
  have substituted :=
    Derives.subst basisSquareInitialSwitch
      (instantiateThreeWords u v v)
  simpa [xxyy, yxxy, w, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem derivesClosedInteriorSwap (u v z : Word Nat) :
    Derives basis (((u ++ v) ++ z) ++ u)
      (((u ++ z) ++ v) ++ u) := by
  have substituted :=
    Derives.subst basisClosedInteriorSwap
      (instantiateThreeWords u v z)
  simpa [xyzx, xzyx, w, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- The recorded chain `xyxy -> xxyy -> xyyx`. -/
theorem derivesConnectedCrossingOne (u v : Word Nat) :
    Derives basis (((u ++ v) ++ u) ++ v)
      (((u ++ v) ++ v) ++ u) :=
  (derivesSquareInterleave u v).symm.trans
    (derivesSquareFinalSwitch u v)

/-- The recorded chain `xyxy -> xxyy -> yxxy`. -/
theorem derivesConnectedCrossingTwo (u v : Word Nat) :
    Derives basis (((u ++ v) ++ u) ++ v)
      (((v ++ u) ++ u) ++ v) :=
  (derivesSquareInterleave u v).symm.trans
    (derivesSquareInitialSwitch u v)

/-- The recorded chain `xyxzx -> xxzyx -> xxyzx -> xyzx`. -/
theorem derivesThirdOccurrenceDeletion (u v z : Word Nat) :
    Derives basis ((((u ++ v) ++ u) ++ z) ++ u)
      (((u ++ v) ++ z) ++ u) := by
  have first := derivesClosedInteriorSwap u v (u ++ z)
  have second := Derives.prepend u (derivesClosedInteriorSwap u z v)
  have third := (derivesLeftDuplication u (v ++ z)).symm
  apply Derives.trans
  · simpa [Word.append_assoc] using first
  · apply Derives.trans
    · simpa [Word.append_assoc] using second
    · simpa [Word.append_assoc] using third

/-- The recorded seven-word crossing-envelope chain. -/
theorem derivesCrossingEnvelopeOne (u v z : Word Nat) :
    Derives basis ((((u ++ v) ++ u) ++ z) ++ v)
      ((((u ++ v) ++ v) ++ z) ++ u) := by
  have first := Derives.prepend u (derivesClosedInteriorSwap v u z)
  have second := Derives.appendRight (derivesClosedInteriorSwap u v z) v
  have third :=
    Derives.appendRight (derivesRightDuplication u (z ++ v)) v
  have fourth :=
    Derives.prepend (u ++ z) (derivesSquareFinalSwitch v u).symm
  have fifth :=
    Derives.appendRight (derivesClosedInteriorSwap u z (v ++ v)) u
  have sixth := (derivesRightDuplication u ((v ++ v) ++ z)).symm
  apply Derives.trans
  · simpa [Word.append_assoc] using first
  · apply Derives.trans
    · simpa [Word.append_assoc] using second
    · apply Derives.trans
      · simpa [Word.append_assoc] using third
      · apply Derives.trans
        · simpa [Word.append_assoc] using fourth
        · apply Derives.trans
          · simpa [Word.append_assoc] using fifth
          · simpa [Word.append_assoc] using sixth

/-- The recorded four-word crossing-envelope chain. -/
theorem derivesCrossingEnvelopeTwo (u v z : Word Nat) :
    Derives basis ((((u ++ v) ++ u) ++ z) ++ v)
      ((((v ++ u) ++ u) ++ z) ++ v) := by
  have first := Derives.prepend u (derivesLeftDuplication v (u ++ z))
  have second :=
    Derives.appendRight (derivesSquareInitialSwitch v u).symm (z ++ v)
  have third := (derivesLeftDuplication v ((u ++ u) ++ z)).symm
  apply Derives.trans
  · simpa [Word.append_assoc] using first
  · apply Derives.trans
    · simpa [Word.append_assoc] using second
    · simpa [Word.append_assoc] using third

/-- The recorded nine-word envelope-switch chain. -/
theorem derivesEnvelopeSwitch (u v z : Word Nat) :
    Derives basis ((((u ++ v) ++ v) ++ z) ++ u)
      ((((v ++ u) ++ u) ++ z) ++ v) := by
  have first := derivesClosedInteriorSwap u v (v ++ z)
  have second :=
    Derives.prepend u <|
      Derives.appendRight (derivesRightDuplication v z) u
  have third := derivesRightDuplication u (((v ++ z) ++ v) ++ v)
  have fourth :=
    Derives.prepend ((u ++ v) ++ z) (derivesSquareFinalSwitch v u)
  have fifth :=
    Derives.prepend u <|
      derivesClosedInteriorSwap v z ((v ++ u) ++ u)
  have sixth :=
    Derives.appendRight (derivesSquareInitialSwitch v u).symm
      ((u ++ z) ++ v)
  have seventh := (derivesLeftDuplication v (((u ++ u) ++ u) ++ z)).symm
  have eighth :=
    Derives.prepend v <|
      Derives.appendRight (derivesPowerExpansion u).symm (z ++ v)
  apply Derives.trans
  · simpa [Word.append_assoc] using first
  · apply Derives.trans
    · simpa [Word.append_assoc] using second
    · apply Derives.trans
      · simpa [Word.append_assoc] using third
      · apply Derives.trans
        · simpa [Word.append_assoc] using fourth
        · apply Derives.trans
          · simpa [Word.append_assoc] using fifth
          · apply Derives.trans
            · simpa [Word.append_assoc] using sixth
            · apply Derives.trans
              · simpa [Word.append_assoc] using seventh
              · simpa [Word.append_assoc] using eighth

/-- Finite chain for nonempty left and right envelope interiors. -/
theorem derivesMergeBothNonemptyFiniteChain
    (x a y b : Word Nat) :
    Derives basis (((((x ++ a) ++ x) ++ y) ++ b) ++ y)
      (((((x ++ a) ++ y) ++ y) ++ b) ++ x) := by
  have first :=
    Derives.prepend ((x ++ a) ++ x) (derivesLeftDuplication y b)
  have second :=
    Derives.appendRight (derivesRightDuplication x a)
      (((y ++ y) ++ b) ++ y)
  have third :=
    Derives.appendRight
      (Derives.prepend (x ++ a) (derivesSquareInitialSwitch x y))
      (b ++ y)
  have fourth :=
    Derives.prepend (x ++ a) <|
      derivesClosedInteriorSwap y (((x ++ x) ++ y)) b
  have fifth :=
    Derives.prepend (x ++ a) <|
      (derivesRightDuplication y ((b ++ x) ++ x)).symm
  have sixth :=
    Derives.appendRight (derivesClosedInteriorSwap x (a ++ y) b)
      (x ++ y)
  have seventh :=
    Derives.prepend ((x ++ b) ++ a)
      (derivesSquareFinalSwitch y x).symm
  have eighth := (derivesRightDuplication x (((b ++ a) ++ y) ++ y)).symm
  have ninth := derivesClosedInteriorSwap x b ((a ++ y) ++ y)
  apply Derives.trans
  · simpa [Word.append_assoc] using first
  · apply Derives.trans
    · simpa [Word.append_assoc] using second
    · apply Derives.trans
      · simpa [Word.append_assoc] using third
      · apply Derives.trans
        · simpa [Word.append_assoc] using fourth
        · apply Derives.trans
          · simpa [Word.append_assoc] using fifth
          · apply Derives.trans
            · simpa [Word.append_assoc] using sixth
            · apply Derives.trans
              · simpa [Word.append_assoc] using seventh
              · apply Derives.trans
                · simpa [Word.append_assoc] using eighth
                · simpa [Word.append_assoc] using ninth

/-- Finite chain for an empty left and nonempty right envelope interior. -/
theorem derivesMergeLeftEmptyFiniteChain (x y b : Word Nat) :
    Derives basis ((((x ++ x) ++ y) ++ b) ++ y)
      ((((x ++ y) ++ y) ++ b) ++ x) := by
  have first := Derives.prepend (x ++ x) (derivesLeftDuplication y b)
  have second :=
    Derives.appendRight (derivesSquareFinalSwitch x y) (b ++ y)
  have third :=
    Derives.appendRight (derivesRightDuplication x (y ++ y)) (b ++ y)
  have fourth :=
    Derives.prepend x <|
      derivesClosedInteriorSwap y (((y ++ x) ++ x)) b
  have fifth :=
    Derives.prepend ((x ++ y) ++ b)
      (derivesSquareFinalSwitch y x).symm
  have sixth := (derivesRightDuplication x (((y ++ b) ++ y) ++ y)).symm
  have seventh :=
    Derives.prepend x <|
      Derives.appendRight (derivesRightDuplication y b).symm x
  have eighth := derivesClosedInteriorSwap x (y ++ b) y
  apply Derives.trans
  · simpa [Word.append_assoc] using first
  · apply Derives.trans
    · simpa [Word.append_assoc] using second
    · apply Derives.trans
      · simpa [Word.append_assoc] using third
      · apply Derives.trans
        · simpa [Word.append_assoc] using fourth
        · apply Derives.trans
          · simpa [Word.append_assoc] using fifth
          · apply Derives.trans
            · simpa [Word.append_assoc] using sixth
            · apply Derives.trans
              · simpa [Word.append_assoc] using seventh
              · simpa [Word.append_assoc] using eighth

/-- Finite chain for a nonempty left and empty right envelope interior. -/
theorem derivesMergeRightEmptyFiniteChain (x a y : Word Nat) :
    Derives basis ((((x ++ a) ++ x) ++ y) ++ y)
      ((((x ++ a) ++ y) ++ y) ++ x) := by
  have first :=
    Derives.appendRight (derivesRightDuplication x a) (y ++ y)
  have second :=
    Derives.prepend (x ++ a) (derivesSquareFinalSwitch x y)
  have third :=
    Derives.prepend (x ++ a) (derivesSquareInitialSwitch y x).symm
  have fourth := (derivesRightDuplication x ((a ++ y) ++ y)).symm
  apply Derives.trans
  · simpa [Word.append_assoc] using first
  · apply Derives.trans
    · simpa [Word.append_assoc] using second
    · apply Derives.trans
      · simpa [Word.append_assoc] using third
      · simpa [Word.append_assoc] using fourth

/-- Finite chain for two empty envelope interiors. -/
theorem derivesMergeBothEmptyFiniteChain (x y : Word Nat) :
    Derives basis ((x ++ x) ++ (y ++ y))
      (((x ++ y) ++ y) ++ x) :=
  derivesSquareFinalSwitch x y

/-- The ten exact word chains pinned by the B378 structural certificate. -/
def recordedFiniteChains : List (List (Word Nat)) :=
  [
    [w 0 [1, 0, 1], w 0 [0, 1, 1], w 0 [1, 1, 0]],
    [w 0 [1, 0, 1], w 0 [0, 1, 1], w 1 [0, 0, 1]],
    [w 0 [1, 0, 2, 0], w 0 [0, 2, 1, 0],
      w 0 [0, 1, 2, 0], w 0 [1, 2, 0]],
    [w 0 [1, 0, 2, 1], w 0 [1, 2, 0, 1],
      w 0 [2, 1, 0, 1], w 0 [2, 1, 0, 0, 1],
      w 0 [2, 1, 1, 0, 0], w 0 [1, 1, 2, 0, 0],
      w 0 [1, 1, 2, 0]],
    [w 0 [1, 0, 2, 1], w 0 [1, 1, 0, 2, 1],
      w 1 [1, 0, 0, 2, 1], w 1 [0, 0, 2, 1]],
    [w 0 [1, 1, 2, 0], w 0 [1, 2, 1, 0],
      w 0 [1, 2, 1, 1, 0], w 0 [1, 2, 1, 1, 0, 0],
      w 0 [1, 2, 1, 0, 0, 1], w 0 [1, 1, 0, 0, 2, 1],
      w 1 [1, 0, 0, 0, 2, 1], w 1 [0, 0, 0, 2, 1],
      w 1 [0, 0, 2, 1]],
    [w 0 [2, 0, 1, 3, 1], w 0 [2, 0, 1, 1, 3, 1],
      w 0 [2, 0, 0, 1, 1, 3, 1], w 0 [2, 1, 0, 0, 1, 3, 1],
      w 0 [2, 1, 3, 0, 0, 1, 1], w 0 [2, 1, 3, 0, 0, 1],
      w 0 [3, 2, 1, 0, 0, 1], w 0 [3, 2, 1, 1, 0, 0],
      w 0 [3, 2, 1, 1, 0], w 0 [2, 1, 1, 3, 0]],
    [w 0 [0, 1, 2, 1], w 0 [0, 1, 1, 2, 1],
      w 0 [1, 1, 0, 2, 1], w 0 [1, 1, 0, 0, 2, 1],
      w 0 [1, 2, 1, 0, 0, 1], w 0 [1, 2, 1, 1, 0, 0],
      w 0 [1, 2, 1, 1, 0], w 0 [1, 2, 1, 0],
      w 0 [1, 1, 2, 0]],
    [w 0 [2, 0, 1, 1], w 0 [2, 0, 0, 1, 1],
      w 0 [2, 0, 1, 1, 0], w 0 [2, 1, 1, 0, 0],
      w 0 [2, 1, 1, 0]],
    [w 0 [0, 1, 1], w 0 [1, 1, 0]]
  ]

end SemigroupBasis.CoRoots.S5_378
