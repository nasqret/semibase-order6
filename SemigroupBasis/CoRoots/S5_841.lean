import SemigroupBasis.CoRoots.S5_107ListDerives
import SemigroupBasis.Examples.UniqueSeparatorFourNormalForm
import SemigroupBasis.Examples.UniqueSeparatorFourQuadraticSwap
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Generated.CatalogueOrder4
import SemigroupBasis.Generated.CatalogueOrder5Part07
import SemigroupBasis.Opposite
import SemigroupBasis.TransferPower

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.S5_841

open SemigroupBasis
open SemigroupBasis.Examples

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def xx : Word Nat := w 0 [0]
def xxx : Word Nat := w 0 [0, 0]
def xxzx : Word Nat := w 0 [0, 2, 0]
def xzx : Word Nat := w 0 [2, 0]
def xyx : Word Nat := w 0 [1, 0]
def xyxx : Word Nat := w 0 [1, 0, 0]
def xyxwy : Word Nat := w 0 [1, 0, 3, 1]
def yxxwy : Word Nat := w 1 [0, 0, 3, 1]
def xyxy : Word Nat := w 0 [1, 0, 1]
def yxxy : Word Nat := w 1 [0, 0, 1]
def xyxzx : Word Nat := w 0 [1, 0, 2, 0]
def xyzx : Word Nat := w 0 [1, 2, 0]
def xyzwxz : Word Nat := w 0 [1, 2, 3, 0, 2]
def xyzwzx : Word Nat := w 0 [1, 2, 3, 2, 0]
def xyzxwy : Word Nat := w 0 [1, 2, 0, 3, 1]
def yxzxwy : Word Nat := w 1 [0, 2, 0, 3, 1]
def xyzxy : Word Nat := w 0 [1, 2, 0, 1]
def yxzxy : Word Nat := w 1 [0, 2, 0, 1]
def xyzxz : Word Nat := w 0 [1, 2, 0, 2]
def xyzzx : Word Nat := w 0 [1, 2, 2, 0]
def xzwxz : Word Nat := w 0 [2, 3, 0, 2]
def xzwzx : Word Nat := w 0 [2, 3, 2, 0]
def xzxz : Word Nat := w 0 [2, 0, 2]
def xzzx : Word Nat := w 0 [2, 2, 0]

def powerLaw : Identity Nat := ⟨xx, xxx⟩
def leftDeletionLaw : Identity Nat := ⟨xxzx, xzx⟩
def rightExpansionLaw : Identity Nat := ⟨xyx, xyxx⟩
def rightContextSwapLaw : Identity Nat := ⟨xyxwy, yxxwy⟩
def shortSwapLaw : Identity Nat := ⟨xyxy, yxxy⟩
def middleDeletionLaw : Identity Nat := ⟨xyxzx, xyzx⟩
def longRotationLaw : Identity Nat := ⟨xyzwxz, xyzwzx⟩
def longContextSwapLaw : Identity Nat := ⟨xyzxwy, yxzxwy⟩
def terminalContextSwapLaw : Identity Nat := ⟨xyzxy, yxzxy⟩
def terminalSquareLaw : Identity Nat := ⟨xyzxz, xyzzx⟩
def shortRotationLaw : Identity Nat := ⟨xzwxz, xzwzx⟩
def alternatingSquareLaw : Identity Nat := ⟨xzxz, xzzx⟩

/-- The exact ordered twelve-law deletion-closure basis recorded for
Edmunds' `M20` and catalogue representative `S5_841`. -/
def basis : List (Identity Nat) :=
  [powerLaw, leftDeletionLaw, rightExpansionLaw,
    rightContextSwapLaw, shortSwapLaw, middleDeletionLaw,
    longRotationLaw, longContextSwapLaw, terminalContextSwapLaw,
    terminalSquareLaw, shortRotationLaw, alternatingSquareLaw]

/-- The three monoid laws printed in Edmunds Proposition 3.2(a), before
closure under deletion of variables. -/
def publishedCoreBasis : List (Identity Nat) :=
  [⟨xyzx, xyxzx⟩, longRotationLaw, longContextSwapLaw]

def oppositeBasis : List (Identity Nat) :=
  reversedBasis basis

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

/-- Exhaustive checks on the four displayed variables lift to natural-number
variables. This theorem establishes soundness only. -/
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

/-! ## Edmunds M20 and exact catalogue identification -/

/-- Edmunds' `M20` multiplication in historical order `0, e, a, b, c`.
The nonidentity star table is `00a/aba/00c`. -/
def publishedM20Mul (left right : Fin 5) : Fin 5 :=
  if left = 0 then 0
  else if right = 0 then 0
  else if left = 1 then right
  else if right = 1 then left
  else if left = 2 then
    if right = 4 then 2 else 0
  else if left = 3 then
    if right = 2 then 2
    else if right = 3 then 3
    else if right = 4 then 2
    else 0
  else if right = 4 then 4
  else 0

def publishedM20Table : FiniteTable where
  order := 5
  mul := publishedM20Mul
  assoc := by decide

abbrev table : FiniteTable :=
  Generated.Catalogue.S5_841.table

abbrev s4_70Table : FiniteTable :=
  Generated.Catalogue.S4_70.table

abbrev s4_71Table : FiniteTable :=
  Generated.Catalogue.S4_71.table

abbrev s4_105Table : FiniteTable :=
  Generated.Catalogue.S4_105.table

/-- Historical `[0,e,a,b,c]` to catalogue order. In one-based notation this
is `[1,5,2,3,4]`. -/
def historicalToCatalogueValue (value : Fin 5) : Fin 5 :=
  if value.val = 0 then ⟨0, by decide⟩
  else if value.val = 1 then ⟨4, by decide⟩
  else if value.val = 2 then ⟨1, by decide⟩
  else if value.val = 3 then ⟨2, by decide⟩
  else ⟨3, by decide⟩

/-- Catalogue order to historical `[0,e,a,b,c]`. In one-based notation this
is `[1,3,4,5,2]`. -/
def catalogueToHistoricalValue (value : Fin 5) : Fin 5 :=
  if value.val = 0 then ⟨0, by decide⟩
  else if value.val = 1 then ⟨2, by decide⟩
  else if value.val = 2 then ⟨3, by decide⟩
  else if value.val = 3 then ⟨4, by decide⟩
  else ⟨1, by decide⟩

def historicalToCatalogueValuesOneBased : List Nat :=
  List.ofFn fun value : Fin 5 =>
    (historicalToCatalogueValue value).val + 1

def catalogueToHistoricalValuesOneBased : List Nat :=
  List.ofFn fun value : Fin 5 =>
    (catalogueToHistoricalValue value).val + 1

theorem historicalToCatalogueValuesOneBased_certificate :
    historicalToCatalogueValuesOneBased = [1, 5, 2, 3, 4] := by
  decide

theorem catalogueToHistoricalValuesOneBased_certificate :
    catalogueToHistoricalValuesOneBased = [1, 3, 4, 5, 2] := by
  decide

@[simp]
theorem catalogueToHistorical_historicalToCatalogue (value : Fin 5) :
    catalogueToHistoricalValue (historicalToCatalogueValue value) =
      value := by
  decide +revert

@[simp]
theorem historicalToCatalogue_catalogueToHistorical (value : Fin 5) :
    historicalToCatalogueValue (catalogueToHistoricalValue value) =
      value := by
  decide +revert

def publishedM20ToCatalogue :
    Embedding publishedM20Table.semigroup table.semigroup where
  toFun := historicalToCatalogueValue
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right equality
    have inverseEquality :=
      congrArg catalogueToHistoricalValue equality
    simpa using inverseEquality

def catalogueToPublishedM20 :
    Embedding table.semigroup publishedM20Table.semigroup where
  toFun := catalogueToHistoricalValue
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right equality
    have inverseEquality :=
      congrArg historicalToCatalogueValue equality
    simpa using inverseEquality

/-- The catalogue anti-automorphism `[1,2,4,3,5]`, represented as an
isomorphism from the opposite table to the original table. -/
def antiAutomorphismValue (value : Fin 5) : Fin 5 :=
  if value.val = 0 then ⟨0, by decide⟩
  else if value.val = 1 then ⟨1, by decide⟩
  else if value.val = 2 then ⟨3, by decide⟩
  else if value.val = 3 then ⟨2, by decide⟩
  else ⟨4, by decide⟩

def antiAutomorphismValuesOneBased : List Nat :=
  List.ofFn fun value : Fin 5 =>
    (antiAutomorphismValue value).val + 1

theorem antiAutomorphismValuesOneBased_certificate :
    antiAutomorphismValuesOneBased = [1, 2, 4, 3, 5] := by
  decide

@[simp]
theorem antiAutomorphism_involutive (value : Fin 5) :
    antiAutomorphismValue (antiAutomorphismValue value) = value := by
  decide +revert

def selfDuality :
    Embedding table.semigroup.opposite table.semigroup where
  toFun := antiAutomorphismValue
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right equality
    have inverseEquality := congrArg antiAutomorphismValue equality
    simpa using inverseEquality

/-- The one-based section `[1,2,3,4]` embeds `S4_70`. -/
def s4_70Embedding :
    Embedding s4_70Table.semigroup table.semigroup where
  toFun := fun value =>
    if value.val = 0 then ⟨0, by decide⟩
    else if value.val = 1 then ⟨1, by decide⟩
    else if value.val = 2 then ⟨2, by decide⟩
    else ⟨3, by decide⟩
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

/-- The one-based section `[1,2,3,5]` embeds `S4_71`. -/
def s4_71Embedding :
    Embedding s4_71Table.semigroup table.semigroup where
  toFun := fun value =>
    if value.val = 0 then ⟨0, by decide⟩
    else if value.val = 1 then ⟨1, by decide⟩
    else if value.val = 2 then ⟨2, by decide⟩
    else ⟨4, by decide⟩
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

/-- The one-based section `[1,2,4,5]` embeds the opposite of `S4_71`. -/
def s4_71OppositeEmbedding :
    Embedding s4_71Table.semigroup.opposite table.semigroup where
  toFun := fun value =>
    if value.val = 0 then ⟨0, by decide⟩
    else if value.val = 1 then ⟨1, by decide⟩
    else if value.val = 2 then ⟨3, by decide⟩
    else ⟨4, by decide⟩
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

/-- The one-based quotient `[1,1,2,3,4]` onto `S4_105`. The chosen
right-inverse is `[1,3,4,5]`. -/
def s4_105Quotient :
    SplitSurjection table.semigroup s4_105Table.semigroup where
  toFun := fun value =>
    if value.val = 0 then ⟨0, by decide⟩
    else if value.val = 1 then ⟨0, by decide⟩
    else if value.val = 2 then ⟨1, by decide⟩
    else if value.val = 3 then ⟨2, by decide⟩
    else ⟨3, by decide⟩
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  preimage := fun value =>
    if value.val = 0 then ⟨0, by decide⟩
    else if value.val = 1 then ⟨2, by decide⟩
    else if value.val = 2 then ⟨3, by decide⟩
    else ⟨4, by decide⟩
  right_inverse := by
    intro value
    apply Fin.ext
    revert value
    decide

set_option maxRecDepth 100000 in
/-- Direct finite verification on Edmunds' historical `M20` table. -/
theorem publishedM20Models :
    Models publishedM20Table.semigroup basis :=
  models_of_finite_checks publishedM20Table (by decide)

set_option maxRecDepth 100000 in
/-- Direct finite verification on the catalogue representative. -/
theorem models : Models table.semigroup basis :=
  models_of_finite_checks table (by decide)

/-- The opposite representative satisfies the literal reversed basis. -/
theorem oppositeModels :
    Models table.semigroup.opposite oppositeBasis :=
  models.oppositeReversed

/-! ## Capped multiplicity and complete precedence necessity -/

/-- Evaluate a possibly empty historical word from the identity `e`. -/
def m20ListEval
    (valuation : Nat → Fin 5) (letters : List Nat) : Fin 5 :=
  letters.foldl
    (fun current letter =>
      publishedM20Mul current (valuation letter)) 1

def M20ListEquivalent (left right : List Nat) : Prop :=
  ∀ valuation, m20ListEval valuation left = m20ListEval valuation right

private theorem publishedM20Mul_leftIdentity (value : Fin 5) :
    publishedM20Mul 1 value = value := by
  decide +revert

private theorem m20ListEval_toList
    (valuation : Nat → Fin 5) (word : Word Nat) :
    m20ListEval valuation word.toList =
      publishedM20Table.semigroup.eval valuation word := by
  cases word with
  | mk head tail =>
      unfold m20ListEval
      simp only [Word.toList, Semigroup.eval, List.foldl_cons]
      rw [publishedM20Mul_leftIdentity]
      rfl

/-- The required capped multiplicity `min(count,2)`. -/
def CappedMultiplicity (word : Word Nat) (letter : Nat) : Nat :=
  Nat.min (word.toList.count letter) 2

private def multiplicityState (count : Nat) : Fin 5 :=
  if count = 0 then 1 else if count = 1 then 2 else 0

private def multiplicityValuation (selected : Nat) : Nat → Fin 5 :=
  fun letter => if letter = selected then 2 else 1

private theorem multiplicityMul_selected (count : Nat) :
    publishedM20Mul (multiplicityState count) 2 =
      multiplicityState (count + 1) := by
  by_cases zero : count = 0
  · subst count
    decide
  · by_cases one : count = 1
    · subst count
      decide
    · have nextZero : count + 1 ≠ 0 := by omega
      have nextOne : count + 1 ≠ 1 := by omega
      simp [multiplicityState, zero, one, nextZero, nextOne,
        publishedM20Mul]

private theorem multiplicityMul_other (count : Nat) :
    publishedM20Mul (multiplicityState count) 1 =
      multiplicityState count := by
  by_cases zero : count = 0
  · subst count
    decide
  · by_cases one : count = 1
    · subst count
      decide
    · simp [multiplicityState, zero, one, publishedM20Mul]

private theorem multiplicityFold
    (selected : Nat) (letters : List Nat) (accumulated : Nat) :
    letters.foldl
        (fun current letter =>
          publishedM20Mul current (multiplicityValuation selected letter))
        (multiplicityState accumulated) =
      multiplicityState
        (accumulated + letters.count selected) := by
  induction letters generalizing accumulated with
  | nil => simp
  | cons letter rest induction =>
      simp only [List.foldl_cons]
      by_cases equal : letter = selected
      · subst letter
        rw [List.count_cons_self]
        rw [show multiplicityValuation selected selected = (2 : Fin 5) by
          simp [multiplicityValuation]]
        rw [multiplicityMul_selected, induction]
        congr 1
        omega
      · rw [List.count_cons_of_ne equal]
        rw [show multiplicityValuation selected letter = (1 : Fin 5) by
          simp [multiplicityValuation, equal]]
        rw [multiplicityMul_other, induction]

private theorem m20Eval_multiplicity
    (selected : Nat) (word : Word Nat) :
    publishedM20Table.semigroup.eval
        (multiplicityValuation selected) word =
      multiplicityState (word.toList.count selected) := by
  rw [← m20ListEval_toList]
  unfold m20ListEval
  change
    word.toList.foldl
        (fun current letter =>
          publishedM20Mul current (multiplicityValuation selected letter))
        (multiplicityState 0) =
      multiplicityState (word.toList.count selected)
  simpa using multiplicityFold selected word.toList 0

private theorem multiplicityState_capped_injective
    {left right : Nat}
    (equal : multiplicityState left = multiplicityState right) :
    Nat.min left 2 = Nat.min right 2 := by
  by_cases leftZero : left = 0
  · subst left
    by_cases rightZero : right = 0
    · subst right
      rfl
    · by_cases rightOne : right = 1
      · subst right
        simp [multiplicityState] at equal
      · simp [multiplicityState, rightZero, rightOne] at equal
  · by_cases leftOne : left = 1
    · subst left
      by_cases rightOne : right = 1
      · subst right
        rfl
      · by_cases rightZero : right = 0
        · subst right
          simp [multiplicityState] at equal
        · simp [multiplicityState, rightZero, rightOne] at equal
    · by_cases rightZero : right = 0
      · subst right
        simp [multiplicityState, leftZero, leftOne] at equal
      · by_cases rightOne : right = 1
        · subst right
          simp [multiplicityState, leftZero, leftOne] at equal
        · simp only [Nat.min_def]
          split <;> split <;> omega

/-- Direct separator `x ↦ a`, all other variables `↦ e`. -/
theorem valid_cappedMultiplicity
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy publishedM20Table.semigroup)
    (letter : Nat) :
    CappedMultiplicity identity.lhs letter =
      CappedMultiplicity identity.rhs letter := by
  have evaluated := valid (multiplicityValuation letter)
  rw [m20Eval_multiplicity, m20Eval_multiplicity] at evaluated
  exact multiplicityState_capped_injective evaluated

inductive PrecedenceState where
  | neither
  | onlyX
  | onlyY
  | ordered
  | violated
deriving DecidableEq, Repr

private def precedenceStep
    (x y : Nat) (state : PrecedenceState) (letter : Nat) :
    PrecedenceState :=
  if letter = x then
    match state with
    | .neither => .onlyX
    | .onlyX => .onlyX
    | .onlyY | .ordered | .violated => .violated
  else if letter = y then
    match state with
    | .neither => .onlyY
    | .onlyX => .ordered
    | .onlyY => .onlyY
    | .ordered => .ordered
    | .violated => .violated
  else state

def precedenceScanList
    (letters : List Nat) (x y : Nat) : PrecedenceState :=
  letters.foldl (precedenceStep x y) .neither

/-- `CP_w(x,y)`: both variables occur and every occurrence of `x` lies
before the first occurrence of `y`. -/
def CompletePrecedenceList
    (letters : List Nat) (x y : Nat) : Prop :=
  x ≠ y ∧ precedenceScanList letters x y = .ordered

def CompletePrecedence (word : Word Nat) (x y : Nat) : Prop :=
  CompletePrecedenceList word.toList x y

private def PrecedenceState.code : PrecedenceState → Fin 5
  | .neither => 1
  | .onlyX => 3
  | .onlyY => 4
  | .ordered => 2
  | .violated => 0

private theorem precedenceCode_injective :
    Function.Injective PrecedenceState.code := by
  intro left right equal
  cases left <;> cases right <;>
    simp [PrecedenceState.code] at equal ⊢

private def precedenceValuation (x y : Nat) : Nat → Fin 5 :=
  fun letter => if letter = x then 3 else if letter = y then 4 else 1

private theorem precedenceStep_code
    {x y : Nat} (different : x ≠ y)
    (state : PrecedenceState) (letter : Nat) :
    publishedM20Mul state.code (precedenceValuation x y letter) =
      (precedenceStep x y state letter).code := by
  cases state <;> by_cases isX : letter = x
  <;> by_cases isY : letter = y
  <;> simp [precedenceValuation, precedenceStep, isX, isY,
    different, Ne.symm different, PrecedenceState.code, publishedM20Mul] at *

private theorem precedenceFold_code
    {x y : Nat} (different : x ≠ y) :
    ∀ (letters : List Nat) (state : PrecedenceState),
      letters.foldl
          (fun current letter =>
            publishedM20Mul current (precedenceValuation x y letter))
          state.code =
        (letters.foldl (precedenceStep x y) state).code
  | [], _ => rfl
  | letter :: rest, state => by
      simp only [List.foldl_cons]
      rw [precedenceStep_code different]
      exact precedenceFold_code different rest
        (precedenceStep x y state letter)

private theorem m20Eval_precedence
    {x y : Nat} (different : x ≠ y) (word : Word Nat) :
    publishedM20Table.semigroup.eval
        (precedenceValuation x y) word =
      (precedenceScanList word.toList x y).code := by
  rw [← m20ListEval_toList]
  unfold m20ListEval precedenceScanList
  change
    word.toList.foldl
        (fun current letter =>
          publishedM20Mul current (precedenceValuation x y letter))
        PrecedenceState.neither.code =
      (word.toList.foldl
        (precedenceStep x y) PrecedenceState.neither).code
  exact precedenceFold_code different word.toList .neither

/-- Direct separator `x ↦ b`, `y ↦ c`, all other variables `↦ e`. -/
theorem valid_completePrecedence
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy publishedM20Table.semigroup)
    (x y : Nat) :
    CompletePrecedence identity.lhs x y ↔
      CompletePrecedence identity.rhs x y := by
  by_cases different : x ≠ y
  · have evaluated := valid (precedenceValuation x y)
    rw [m20Eval_precedence different,
      m20Eval_precedence different] at evaluated
    have stateEqual := precedenceCode_injective evaluated
    simp only [CompletePrecedence, CompletePrecedenceList, different,
      true_and]
    rw [stateEqual]
  · simp [CompletePrecedence, CompletePrecedenceList, different]

/-- The necessary `M20` signature. No sufficiency claim is made. -/
structure SameM20Signature (left right : Word Nat) : Prop where
  cappedMultiplicity :
    ∀ letter,
      CappedMultiplicity left letter =
        CappedMultiplicity right letter
  completePrecedence :
    ∀ x y,
      CompletePrecedence left x y ↔
        CompletePrecedence right x y

theorem sameM20Signature_of_valid
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy publishedM20Table.semigroup) :
    SameM20Signature identity.lhs identity.rhs :=
  ⟨valid_cappedMultiplicity identity valid,
    valid_completePrecedence identity valid⟩

theorem catalogueValid_sameM20Signature
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    SameM20Signature identity.lhs identity.rhs :=
  sameM20Signature_of_valid identity
    (publishedM20ToCatalogue.pullback_identity identity valid)

theorem derives_sameM20Signature
    {left right : Word Nat}
    (derivation : Derives basis left right) :
    SameM20Signature left right :=
  sameM20Signature_of_valid ⟨left, right⟩
    (fun valuation => derivation.sound publishedM20Models valuation)

/-! ## Primitive substitutions and the two-limited cap -/

private def instantiateFourWords
    (u v z q : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => z
  | 3 => q
  | n + 4 => Word.singleton (n + 4)

private theorem basisPower : Derives basis xx xxx :=
  Derives.fromBasis (e := powerLaw) <| by simp [basis]

private theorem basisLeftDeletion : Derives basis xxzx xzx :=
  Derives.fromBasis (e := leftDeletionLaw) <| by simp [basis]

private theorem basisRightExpansion : Derives basis xyx xyxx :=
  Derives.fromBasis (e := rightExpansionLaw) <| by simp [basis]

private theorem basisRightContextSwap : Derives basis xyxwy yxxwy :=
  Derives.fromBasis (e := rightContextSwapLaw) <| by simp [basis]

private theorem basisShortSwap : Derives basis xyxy yxxy :=
  Derives.fromBasis (e := shortSwapLaw) <| by simp [basis]

private theorem basisMiddleDeletion : Derives basis xyxzx xyzx :=
  Derives.fromBasis (e := middleDeletionLaw) <| by simp [basis]

private theorem basisLongRotation : Derives basis xyzwxz xyzwzx :=
  Derives.fromBasis (e := longRotationLaw) <| by simp [basis]

private theorem basisLongContextSwap : Derives basis xyzxwy yxzxwy :=
  Derives.fromBasis (e := longContextSwapLaw) <| by simp [basis]

private theorem basisTerminalContextSwap : Derives basis xyzxy yxzxy :=
  Derives.fromBasis (e := terminalContextSwapLaw) <| by simp [basis]

private theorem basisTerminalSquare : Derives basis xyzxz xyzzx :=
  Derives.fromBasis (e := terminalSquareLaw) <| by simp [basis]

private theorem basisShortRotation : Derives basis xzwxz xzwzx :=
  Derives.fromBasis (e := shortRotationLaw) <| by simp [basis]

private theorem basisAlternatingSquare : Derives basis xzxz xzzx :=
  Derives.fromBasis (e := alternatingSquareLaw) <| by simp [basis]

theorem derivesPowerExpansion (u : Word Nat) :
    Derives basis (u ++ u) ((u ++ u) ++ u) := by
  have substituted :=
    Derives.subst basisPower (instantiateFourWords u u u u)
  simpa [xx, xxx, w, instantiateFourWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem derivesLeftDuplication (u z : Word Nat) :
    Derives basis ((u ++ z) ++ u) (((u ++ u) ++ z) ++ u) := by
  have substituted :=
    Derives.subst basisLeftDeletion (instantiateFourWords u u z z)
  simpa [xxzx, xzx, w, instantiateFourWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted.symm

theorem derivesRightDuplication (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) (((u ++ v) ++ u) ++ u) := by
  have substituted :=
    Derives.subst basisRightExpansion (instantiateFourWords u v v v)
  simpa [xyx, xyxx, w, instantiateFourWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem derivesRightContextSwap (u v q : Word Nat) :
    Derives basis ((((u ++ v) ++ u) ++ q) ++ v)
      ((((v ++ u) ++ u) ++ q) ++ v) := by
  have substituted :=
    Derives.subst basisRightContextSwap
      (instantiateFourWords u v v q)
  simpa [xyxwy, yxxwy, w, instantiateFourWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

theorem derivesShortSwap (u v : Word Nat) :
    Derives basis (((u ++ v) ++ u) ++ v)
      (((v ++ u) ++ u) ++ v) := by
  have substituted :=
    Derives.subst basisShortSwap (instantiateFourWords u v v v)
  simpa [xyxy, yxxy, w, instantiateFourWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem derivesThirdOccurrenceDeletion (u v z : Word Nat) :
    Derives basis ((((u ++ v) ++ u) ++ z) ++ u)
      (((u ++ v) ++ z) ++ u) := by
  have substituted :=
    Derives.subst basisMiddleDeletion (instantiateFourWords u v z z)
  simpa [xyxzx, xyzx, w, instantiateFourWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem derivesLongRotation (u v z q : Word Nat) :
    Derives basis (((((u ++ v) ++ z) ++ q) ++ u) ++ z)
      (((((u ++ v) ++ z) ++ q) ++ z) ++ u) := by
  have substituted :=
    Derives.subst basisLongRotation (instantiateFourWords u v z q)
  simpa [xyzwxz, xyzwzx, w, instantiateFourWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

theorem derivesLongContextSwap (u v z q : Word Nat) :
    Derives basis (((((u ++ v) ++ z) ++ u) ++ q) ++ v)
      (((((v ++ u) ++ z) ++ u) ++ q) ++ v) := by
  have substituted :=
    Derives.subst basisLongContextSwap
      (instantiateFourWords u v z q)
  simpa [xyzxwy, yxzxwy, w, instantiateFourWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

theorem derivesTerminalContextSwap (u v z : Word Nat) :
    Derives basis ((((u ++ v) ++ z) ++ u) ++ v)
      ((((v ++ u) ++ z) ++ u) ++ v) := by
  have substituted :=
    Derives.subst basisTerminalContextSwap
      (instantiateFourWords u v z z)
  simpa [xyzxy, yxzxy, w, instantiateFourWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

theorem derivesTerminalSquare (u v z : Word Nat) :
    Derives basis ((((u ++ v) ++ z) ++ u) ++ z)
      ((((u ++ v) ++ z) ++ z) ++ u) := by
  have substituted :=
    Derives.subst basisTerminalSquare
      (instantiateFourWords u v z z)
  simpa [xyzxz, xyzzx, w, instantiateFourWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

theorem derivesShortRotation (u z q : Word Nat) :
    Derives basis ((((u ++ z) ++ q) ++ u) ++ z)
      ((((u ++ z) ++ q) ++ z) ++ u) := by
  have substituted :=
    Derives.subst basisShortRotation
      (instantiateFourWords u u z q)
  simpa [xzwxz, xzwzx, w, instantiateFourWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

theorem derivesAlternatingSquare (u z : Word Nat) :
    Derives basis (((u ++ z) ++ u) ++ z)
      (((u ++ z) ++ z) ++ u) := by
  have substituted :=
    Derives.subst basisAlternatingSquare
      (instantiateFourWords u u z z)
  simpa [xzxz, xzzx, w, instantiateFourWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

private theorem listDerivesDeleteMiddleCore
    (x : Nat) (left right : List Nat) :
    S5_107.ListDerives basis
      ([x] ++ left ++ [x] ++ right ++ [x])
      ([x] ++ left ++ right ++ [x]) := by
  cases left with
  | nil =>
      cases right with
      | nil =>
          exact S5_107.ListDerives.words <| by
            simpa [S5_107.listWordOfCons, Word.singleton,
              Word.append, Word.append_assoc, List.append_assoc] using
              (derivesPowerExpansion (Word.singleton x)).symm
      | cons y ys =>
          exact S5_107.ListDerives.words <| by
            simpa [S5_107.listWordOfCons, Word.singleton,
              Word.append, Word.append_assoc, List.append_assoc] using
              (derivesLeftDuplication
                (Word.singleton x)
                (S5_107.listWordOfCons y ys)).symm
  | cons y ys =>
      cases right with
      | nil =>
          exact S5_107.ListDerives.words <| by
            simpa [S5_107.listWordOfCons, Word.singleton,
              Word.append, Word.append_assoc, List.append_assoc] using
              (derivesRightDuplication
                (Word.singleton x)
                (S5_107.listWordOfCons y ys)).symm
      | cons z zs =>
          exact S5_107.ListDerives.words <| by
            simpa [S5_107.listWordOfCons, Word.singleton,
              Word.append, Word.append_assoc, List.append_assoc] using
              derivesThirdOccurrenceDeletion
                (Word.singleton x)
                (S5_107.listWordOfCons y ys)
                (S5_107.listWordOfCons z zs)

private theorem listDerivesDeleteCurrent
    (pre suffix : List Nat) (x : Nat)
    (past : x ∈ pre) (future : x ∈ suffix) :
    S5_107.ListDerives basis
      (pre ++ x :: suffix) (pre ++ suffix) := by
  rcases List.append_of_mem past with
    ⟨before, left, preShape⟩
  rcases List.append_of_mem future with
    ⟨right, after, suffixShape⟩
  rw [preShape, suffixShape]
  simpa [List.append_assoc] using
    (listDerivesDeleteMiddleCore x left right).context before after

private theorem listDerivesEndpointCapAux
    (pre seen : List Nat)
    (seenInPre : ∀ z ∈ seen, z ∈ pre) :
    ∀ suffix : List Nat,
      S5_107.ListDerives basis
        (pre ++ suffix)
        (pre ++ uniqueSeparatorEndpointCapAux seen suffix)
  | [] => by
      simpa using S5_107.ListDerives.refl (basis := basis) pre
  | x :: xs => by
      by_cases middle : x ∈ seen ∧ x ∈ xs
      · have xInPre : x ∈ pre := seenInPre x middle.1
        have deleteCurrent :
            S5_107.ListDerives basis
              (pre ++ x :: xs) (pre ++ xs) :=
          listDerivesDeleteCurrent pre xs x xInPre middle.2
        have nextSeenInPre : ∀ z ∈ x :: seen, z ∈ pre := by
          intro z member
          rcases List.mem_cons.mp member with rfl | member
          · exact xInPre
          · exact seenInPre z member
        have recurse :=
          listDerivesEndpointCapAux pre (x :: seen) nextSeenInPre xs
        rw [uniqueSeparatorEndpointCapAux, if_pos middle]
        exact deleteCurrent.trans recurse
      · have nextSeenInPre :
            ∀ z ∈ x :: seen, z ∈ pre ++ [x] := by
          intro z member
          rcases List.mem_cons.mp member with rfl | member
          · exact List.mem_append_right pre (List.Mem.head [])
          · exact List.mem_append_left [x] (seenInPre z member)
        have recurse :=
          listDerivesEndpointCapAux
            (pre ++ [x]) (x :: seen) nextSeenInPre xs
        rw [uniqueSeparatorEndpointCapAux, if_neg middle]
        simpa [List.append_assoc] using recurse

/-- Every list derives to the endpoint cap retaining exactly the first and
last occurrence of each letter. -/
theorem listDerivesTwoLimitedReduction (letters : List Nat) :
    S5_107.ListDerives basis letters
      (uniqueSeparatorEndpointCap letters) := by
  simpa [uniqueSeparatorEndpointCap] using
    listDerivesEndpointCapAux [] [] (by simp) letters

theorem endpointCap_twoLimited (letters : List Nat) :
    UniqueSeparatorTwoLimited (uniqueSeparatorEndpointCap letters) :=
  uniqueSeparatorEndpointCap_twoLimited letters

abbrev QuadraticSegment := UniqueSeparatorSquareSegment

abbrev QuadraticSwapPosition :=
  UniqueSeparatorAdjacentQuadraticPosition

def quadraticSegments
    (letters : List Nat) : List QuadraticSegment :=
  uniqueSeparatorSplitLinear letters

/-- The first honest proof obligation. Its local field is the six-position
adjacent swap; its global field is the permutation induction over a complete
quadratic block. No inhabitant is asserted. -/
structure QuadraticBlockPermutationSixCaseObligation : Prop where
  adjacent :
    ∀ {x y : Nat} {pre post : List Nat},
      x ≠ y →
      (pre ++ (x :: y :: post)).count x = 2 →
      (pre ++ (x :: y :: post)).count y = 2 →
      QuadraticSwapPosition x y pre post →
      M20ListEquivalent
        (pre ++ (x :: y :: post))
        (pre ++ (y :: x :: post)) →
      S5_107.ListDerives basis
        (pre ++ (x :: y :: post))
        (pre ++ (y :: x :: post))
  blockPermutation :
    ∀ (target source pre post : List Nat),
      source.Perm target →
      (∀ letter, letter ∈ source →
        (pre ++ source ++ post).count letter = 2) →
      M20ListEquivalent
        (pre ++ source ++ post)
        (pre ++ target ++ post) →
      S5_107.ListDerives basis
        (pre ++ source ++ post)
        (pre ++ target ++ post)

/-- The subsequent segmentation obligation. It starts only after a
six-case block-permutation witness has been supplied. -/
def M20SegmentationCompletenessObligation
    (_ : QuadraticBlockPermutationSixCaseObligation) : Prop :=
  ∀ {left right : List Nat},
    UniqueSeparatorTwoLimited left →
    UniqueSeparatorTwoLimited right →
    M20ListEquivalent left right →
    (∀ letter,
      Nat.min (left.count letter) 2 =
        Nat.min (right.count letter) 2) →
    (∀ x y,
      CompletePrecedenceList left x y ↔
        CompletePrecedenceList right x y) →
    S5_107.ListDerives basis left right

/-- The remaining unrestricted content of Edmunds Proposition 3.2(a),
recorded only as a proposition. -/
def M20CompletenessObligation : Prop :=
  ∀ identity : Identity Nat,
    identity.SatisfiedBy publishedM20Table.semigroup →
      Derives basis identity.lhs identity.rhs

/-- Conditional direct endpoint for the historical table. -/
theorem publishedM20BasisFor_of_completeness
    (complete : M20CompletenessObligation) :
    BasisFor publishedM20Table.semigroup basis :=
  ⟨publishedM20Models, complete⟩

/-- Conditional direct endpoint for the catalogue table. The exact table
map is used only to transport identity validity into historical `M20`; no
`BasisFor` transfer theorem is used. -/
theorem catalogueS5_841BasisFor_of_publishedCompleteness
    (complete : M20CompletenessObligation) :
    BasisFor table.semigroup basis := by
  refine ⟨models, ?_⟩
  intro identity valid
  exact complete identity
    (publishedM20ToCatalogue.pullback_identity identity valid)

/-- Exact finite chains replayed by the metadata-only packet. -/
def recordedFiniteChains : List (List (Word Nat)) :=
  [
    [w 0 [0], w 0 [0, 0]],
    [w 0 [0, 2, 0], w 0 [2, 0]],
    [w 0 [1, 0], w 0 [1, 0, 0]],
    [w 0 [1, 0, 3, 1], w 1 [0, 0, 3, 1]],
    [w 0 [1, 0, 1], w 1 [0, 0, 1]],
    [w 0 [1, 0, 2, 0], w 0 [1, 2, 0]],
    [w 0 [1, 2, 3, 0, 2], w 0 [1, 2, 3, 2, 0]],
    [w 0 [1, 2, 0, 3, 1], w 1 [0, 2, 0, 3, 1]],
    [w 0 [1, 2, 0, 1], w 1 [0, 2, 0, 1]],
    [w 0 [1, 2, 0, 2], w 0 [1, 2, 2, 0]],
    [w 0 [2, 3, 0, 2], w 0 [2, 3, 2, 0]],
    [w 0 [2, 0, 2], w 0 [2, 2, 0]]
  ]

/- The source intentionally stops at the three named obligations. It does not
assert the six-case quadratic-block permutation, segmented completeness,
`m20Completeness`, an unconditional `BasisFor`, compilation, proof-object
acceptance, or release. -/

end SemigroupBasis.CoRoots.S5_841
