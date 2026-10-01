import SemigroupBasis.CoRoots.S5_378
import SemigroupBasis.Examples.ConnectedComponentFourSemantics
import SemigroupBasis.Examples.CommutativeExponentThree
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Generated.CatalogueOrder5Part03
import SemigroupBasis.Opposite

namespace SemigroupBasis.CoRoots.S5_379

open SemigroupBasis

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def xx : Word Nat := w 0 [0]
def xxx : Word Nat := w 0 [0, 0]
def xyx : Word Nat := w 0 [1, 0]
def xxyx : Word Nat := w 0 [0, 1, 0]
def xyxx : Word Nat := w 0 [1, 0, 0]
def xyxy : Word Nat := w 0 [1, 0, 1]
def xyyx : Word Nat := w 0 [1, 1, 0]
def yxxy : Word Nat := w 1 [0, 0, 1]
def xyzx : Word Nat := w 0 [1, 2, 0]
def xzyx : Word Nat := w 0 [2, 1, 0]

def powerLaw : Identity Nat := ⟨xx, xxx⟩
def leftDuplicationLaw : Identity Nat := ⟨xyx, xxyx⟩
def rightDuplicationLaw : Identity Nat := ⟨xyx, xyxx⟩
def crossingFinalLaw : Identity Nat := ⟨xyxy, xyyx⟩
def crossingInitialLaw : Identity Nat := ⟨xyxy, yxxy⟩
def closedInteriorSwapLaw : Identity Nat := ⟨xyzx, xzyx⟩

/-- The exact ordered six-law basis recorded for catalogue class `S5_379`.
This partial source asserts finite semantics and finite derivations only. -/
def basis : List (Identity Nat) :=
  [powerLaw, leftDuplicationLaw, rightDuplicationLaw,
    crossingFinalLaw, crossingInitialLaw, closedInteriorSwapLaw]

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
  Generated.Catalogue.S5_379.table

set_option maxRecDepth 100000 in
/-- The direct Smallsemi representative satisfies the six recorded laws. -/
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

/-- The recorded homomorphic copy `[1,3,4,5]` of the `S4_70` table. -/
def componentEmbedding :
    Embedding Examples.connectedComponentFour.semigroup table.semigroup where
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

/-- The recorded component quotient `[1,1,2,3,4]` onto `S4_70`. -/
def componentQuotient :
    SplitSurjection table.semigroup Examples.connectedComponentFour.semigroup where
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
  preimage := componentEmbedding.toFun
  right_inverse := by
    intro b
    apply Fin.ext
    revert b
    decide

/-- The recorded homomorphic copy `[1,2,5]` of `S3_8 = N_2^1`. -/
def multiplicityEmbedding :
    Embedding Examples.commutativeExponentThree.semigroup table.semigroup where
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

/-- The recorded multiplicity quotient `[1,2,1,1,3]` onto `S3_8`. -/
def multiplicityQuotient :
    SplitSurjection table.semigroup
      Examples.commutativeExponentThree.semigroup where
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
      (componentQuotient.toFun a, multiplicityQuotient.toFun a) := by
  intro a b
  revert a b
  decide

theorem valid_s4_70 (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy Examples.connectedComponentFour.semigroup :=
  componentQuotient.pushforwardIdentity identity valid

theorem valid_s3_8 (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy Examples.commutativeExponentThree.semigroup :=
  multiplicityQuotient.pushforwardIdentity identity valid

/-- The two quotient term functions jointly determine the target term
function. This is a semantic identity sandwich, not a basis endpoint. -/
theorem valid_iff_factors (identity : Identity Nat) :
    identity.SatisfiedBy table.semigroup ↔
      identity.SatisfiedBy Examples.connectedComponentFour.semigroup ∧
        identity.SatisfiedBy Examples.commutativeExponentThree.semigroup := by
  constructor
  · intro valid
    exact ⟨valid_s4_70 identity valid, valid_s3_8 identity valid⟩
  · rintro ⟨componentValid, multiplicityValid⟩
    exact satisfiedBy_of_joint_homs
      componentQuotient.toHom multiplicityQuotient.toHom
      factorPair_injective identity componentValid multiplicityValid

/-- Extensional support agreement. -/
def SameSupport (left right : Word Nat) : Prop :=
  ∀ letter, letter ∈ left.toList ↔ letter ∈ right.toList

def GloballySimple (word : Word Nat) (letter : Nat) : Prop :=
  word.toList.count letter = 1

def SameGloballySimpleVariables (left right : Word Nat) : Prop :=
  ∀ letter, GloballySimple left letter ↔ GloballySimple right letter

/-- Exact agreement of the two term functions in the semantic `S4_70`
factor. No concrete `S4_70` derivation normalizer is imported here. -/
def SameS4_70TermFunction (left right : Word Nat) : Prop :=
  (Identity.mk left right).SatisfiedBy
    Examples.connectedComponentFour.semigroup

/-- The necessary factor signature available before component normalization:
the `S4_70` term function, support, and the global simple-variable set. -/
structure SameComponentSimpleSignature
    (left right : Word Nat) : Prop where
  component : SameS4_70TermFunction left right
  support : SameSupport left right
  globallySimple : SameGloballySimpleVariables left right

private theorem cappedCount_eq_one_iff (count : Nat) :
    min count 2 = 1 ↔ count = 1 := by
  omega

/-- Validity in the two factors supplies the necessary signature. This does
not assert that the signature is sufficient for a derivation. -/
theorem sameSignature_of_factors
    (identity : Identity Nat)
    (componentValid :
      identity.SatisfiedBy Examples.connectedComponentFour.semigroup)
    (multiplicityValid :
      identity.SatisfiedBy Examples.commutativeExponentThree.semigroup) :
    SameComponentSimpleSignature identity.lhs identity.rhs := by
  refine ⟨componentValid, ?_, ?_⟩
  · intro letter
    exact Examples.connectedComponentFourValid_support_iff
      identity componentValid letter
  · intro letter
    have capped :=
      Examples.exponentValid_capped_count_eq
        identity multiplicityValid letter
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
    SameComponentSimpleSignature identity.lhs identity.rhs :=
  sameSignature_of_factors identity
    (valid_s4_70 identity valid) (valid_s3_8 identity valid)

private theorem s4_70Models :
    Models Examples.connectedComponentFour.semigroup basis :=
  models_of_finite_checks Examples.connectedComponentFour (by decide)

private theorem s3_8Models :
    Models Examples.commutativeExponentThree.semigroup basis :=
  models_of_finite_checks Examples.commutativeExponentThree (by decide)

/-- Every finite derivation preserves the necessary factor signature. -/
theorem derives_sameSignature {left right : Word Nat}
    (derivation : Derives basis left right) :
    SameComponentSimpleSignature left right :=
  sameSignature_of_factors ⟨left, right⟩
    (fun valuation => derivation.sound s4_70Models valuation)
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

private theorem basisCrossingFinal : Derives basis xyxy xyyx :=
  Derives.fromBasis (e := crossingFinalLaw) <| by simp [basis]

private theorem basisCrossingInitial : Derives basis xyxy yxxy :=
  Derives.fromBasis (e := crossingInitialLaw) <| by simp [basis]

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

theorem derivesCrossingFinal (u v : Word Nat) :
    Derives basis (((u ++ v) ++ u) ++ v)
      (((u ++ v) ++ v) ++ u) := by
  have substituted :=
    Derives.subst basisCrossingFinal
      (instantiateThreeWords u v v)
  simpa [xyxy, xyyx, w, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem derivesCrossingInitial (u v : Word Nat) :
    Derives basis (((u ++ v) ++ u) ++ v)
      (((v ++ u) ++ u) ++ v) := by
  have substituted :=
    Derives.subst basisCrossingInitial
      (instantiateThreeWords u v v)
  simpa [xyxy, yxxy, w, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem derivesClosedInteriorSwap (u v z : Word Nat) :
    Derives basis (((u ++ v) ++ z) ++ u)
      (((u ++ z) ++ v) ++ u) := by
  have substituted :=
    Derives.subst basisClosedInteriorSwap
      (instantiateThreeWords u v z)
  simpa [xyzx, xzyx, w, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- The recorded chain `xyxzx -> xxzyx -> xzyx -> xyzx`. -/
theorem derivesThirdOccurrenceDeletion (u v z : Word Nat) :
    Derives basis ((((u ++ v) ++ u) ++ z) ++ u)
      (((u ++ v) ++ z) ++ u) := by
  have first := derivesClosedInteriorSwap u v (u ++ z)
  have second := (derivesLeftDuplication u (z ++ v)).symm
  have third := (derivesClosedInteriorSwap u v z).symm
  simp only [Word.append_assoc] at first second third
  simpa only [Word.append_assoc] using first.trans (second.trans third)

/-- The recorded seven-word chain `xyxzy -> ... -> xyyzx`. -/
theorem derivesCrossingEnvelopeRight (u v z : Word Nat) :
    Derives basis ((((u ++ v) ++ u) ++ z) ++ v)
      ((((u ++ v) ++ v) ++ z) ++ u) := by
  have first :=
    Derives.appendRight (derivesLeftDuplication u v) (z ++ v)
  have second :=
    Derives.prepend (u ++ u) (derivesClosedInteriorSwap v u z)
  have third :=
    Derives.appendRight
      (derivesClosedInteriorSwap u (u ++ v) z) v
  have fourth :=
    Derives.prepend (u ++ z) (derivesCrossingFinal u v)
  have fifth :=
    derivesClosedInteriorSwap u z ((u ++ v) ++ v)
  have sixth :=
    (derivesLeftDuplication u ((v ++ v) ++ z)).symm
  simp only [Word.append_assoc] at first second third fourth fifth sixth
  simpa only [Word.append_assoc] using
    first.trans <| second.trans <| third.trans <| fourth.trans <|
      fifth.trans sixth

/-- The recorded six-word chain `xyxzy -> ... -> yxxzy`. -/
theorem derivesCrossingEnvelopeLeft (u v z : Word Nat) :
    Derives basis ((((u ++ v) ++ u) ++ z) ++ v)
      ((((v ++ u) ++ u) ++ z) ++ v) := by
  have first :=
    Derives.prepend u (derivesLeftDuplication v (u ++ z))
  have second :=
    Derives.appendRight (derivesCrossingInitial v u).symm (z ++ v)
  have third :=
    derivesClosedInteriorSwap v u ((v ++ u) ++ z)
  have fourth :=
    (derivesLeftDuplication v ((u ++ z) ++ u)).symm
  have fifth := derivesClosedInteriorSwap v (u ++ z) u
  simp only [Word.append_assoc] at first second third fourth fifth
  simpa only [Word.append_assoc] using
    first.trans <| second.trans <| third.trans <| fourth.trans fifth

/-- The fourth recorded chain is the common consequence
`xyyzx -> ... -> xyxzy -> ... -> yxxzy`. -/
theorem derivesEnvelopeSwitch (u v z : Word Nat) :
    Derives basis ((((u ++ v) ++ v) ++ z) ++ u)
      ((((v ++ u) ++ u) ++ z) ++ v) :=
  (derivesCrossingEnvelopeRight u v z).symm.trans
    (derivesCrossingEnvelopeLeft u v z)

private theorem strongerPower :
    Derives SemigroupBasis.CoRoots.S5_378.basis
      powerLaw.lhs powerLaw.rhs := by
  simpa [powerLaw, xx, xxx, w, Word.singleton, Word.append,
    Word.append_assoc] using
      SemigroupBasis.CoRoots.S5_378.derivesPowerExpansion (Word.singleton 0)

private theorem strongerLeftDuplication :
    Derives SemigroupBasis.CoRoots.S5_378.basis
      leftDuplicationLaw.lhs leftDuplicationLaw.rhs := by
  simpa [leftDuplicationLaw, xyx, xxyx, w, Word.singleton, Word.append,
    Word.append_assoc] using
      SemigroupBasis.CoRoots.S5_378.derivesLeftDuplication
        (Word.singleton 0) (Word.singleton 1)

private theorem strongerRightDuplication :
    Derives SemigroupBasis.CoRoots.S5_378.basis
      rightDuplicationLaw.lhs rightDuplicationLaw.rhs := by
  simpa [rightDuplicationLaw, xyx, xyxx, w, Word.singleton, Word.append,
    Word.append_assoc] using
      SemigroupBasis.CoRoots.S5_378.derivesRightDuplication
        (Word.singleton 0) (Word.singleton 1)

private theorem strongerCrossingFinal :
    Derives SemigroupBasis.CoRoots.S5_378.basis
      crossingFinalLaw.lhs crossingFinalLaw.rhs := by
  simpa [crossingFinalLaw, xyxy, xyyx, w, Word.singleton, Word.append,
    Word.append_assoc] using
      SemigroupBasis.CoRoots.S5_378.derivesConnectedCrossingOne
        (Word.singleton 0) (Word.singleton 1)

private theorem strongerCrossingInitial :
    Derives SemigroupBasis.CoRoots.S5_378.basis
      crossingInitialLaw.lhs crossingInitialLaw.rhs := by
  simpa [crossingInitialLaw, xyxy, yxxy, w, Word.singleton, Word.append,
    Word.append_assoc] using
      SemigroupBasis.CoRoots.S5_378.derivesConnectedCrossingTwo
        (Word.singleton 0) (Word.singleton 1)

private theorem strongerClosedInteriorSwap :
    Derives SemigroupBasis.CoRoots.S5_378.basis
      closedInteriorSwapLaw.lhs closedInteriorSwapLaw.rhs := by
  simpa [closedInteriorSwapLaw, xyzx, xzyx, w, Word.singleton,
    Word.append, Word.append_assoc] using
      SemigroupBasis.CoRoots.S5_378.derivesClosedInteriorSwap
        (Word.singleton 0) (Word.singleton 1) (Word.singleton 2)

/-- Every S5_379 basis law is derivable from the stronger seven-law S5_378
basis. This records only law-level derivability; no component normalizer is
transported or claimed here. -/
theorem strongerBasisDerives
    (identity : Identity Nat) (member : identity ∈ basis) :
    Derives SemigroupBasis.CoRoots.S5_378.basis
      identity.lhs identity.rhs := by
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact strongerPower
  · exact strongerLeftDuplication
  · exact strongerRightDuplication
  · exact strongerCrossingFinal
  · exact strongerCrossingInitial
  · exact strongerClosedInteriorSwap

/-- The four exact word chains pinned by the S5_379 structural certificate. -/
def recordedFiniteChains : List (List (Word Nat)) :=
  [
    [w 0 [1, 0, 2, 0], w 0 [0, 2, 1, 0],
      w 0 [2, 1, 0], w 0 [1, 2, 0]],
    [w 0 [1, 0, 2, 1], w 0 [0, 1, 0, 2, 1],
      w 0 [0, 1, 2, 0, 1], w 0 [2, 0, 1, 0, 1],
      w 0 [2, 0, 1, 1, 0], w 0 [0, 1, 1, 2, 0],
      w 0 [1, 1, 2, 0]],
    [w 0 [1, 0, 2, 1], w 0 [1, 1, 0, 2, 1],
      w 1 [0, 1, 0, 2, 1], w 1 [1, 0, 2, 0, 1],
      w 1 [0, 2, 0, 1], w 1 [0, 0, 2, 1]],
    [w 0 [1, 1, 2, 0], w 0 [0, 1, 1, 2, 0],
      w 0 [2, 0, 1, 1, 0], w 0 [2, 0, 1, 0, 1],
      w 0 [0, 1, 2, 0, 1], w 0 [0, 1, 0, 2, 1],
      w 0 [1, 0, 2, 1], w 0 [1, 1, 0, 2, 1],
      w 1 [0, 1, 0, 2, 1], w 1 [1, 0, 2, 0, 1],
      w 1 [0, 2, 0, 1], w 1 [0, 0, 2, 1]]
  ]

/- The next theorem in the planned family module is
`derivesConnectedComponentNormal`. It is intentionally absent here: the
empty crossing-interval and endpoint branches require explicit nonempty-Word
derivations before the component induction can be stated without a hole. -/

end SemigroupBasis.CoRoots.S5_379
