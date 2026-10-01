import SemigroupBasis.CoRoots.S5_869
import SemigroupBasis.CoRoots.S5_345Factors
import SemigroupBasis.Generated.CatalogueOrder5Part07

/-!
Source-only semantic invariants for the `S5_869`/`S5_871` family.
The theorem claims in this module have not yet been compiled or elaborated.
-/

namespace SemigroupBasis.CoRoots.S5_869

open SemigroupBasis
open SemigroupBasis.Examples

/-- The maximal prefix strictly before the first selected letter. If the
selected letter is absent, the whole list is returned. -/
def prefixBefore (selected : Nat) : List Nat → List Nat
  | [] => []
  | letter :: rest =>
      if letter = selected then []
      else letter :: prefixBefore selected rest

theorem prefixBefore_eq_self_of_not_mem
    (selected : Nat) :
    ∀ {letters : List Nat}, selected ∉ letters →
      prefixBefore selected letters = letters
  | [], _ => rfl
  | letter :: rest, absent => by
      have different : letter ≠ selected := by
        intro equal
        subst letter
        exact absent (List.Mem.head rest)
      simp only [prefixBefore, different, ↓reduceIte]
      rw [prefixBefore_eq_self_of_not_mem selected (fun member =>
        absent (List.Mem.tail letter member))]

theorem mem_of_mem_prefixBefore
    (selected tested : Nat) :
    ∀ {letters : List Nat},
      tested ∈ prefixBefore selected letters → tested ∈ letters
  | [], member => by
      simp [prefixBefore] at member
  | letter :: rest, member => by
      by_cases equal : letter = selected
      · simp [prefixBefore, equal] at member
      · simp only [prefixBefore, equal, ↓reduceIte,
          List.mem_cons] at member ⊢
        rcases member with testedEqual | member
        · exact Or.inl testedEqual
        · exact Or.inr <|
            mem_of_mem_prefixBefore selected tested member

private theorem mem_firstOccurrenceSequence_iff
    (selected : Nat) :
    ∀ letters : List Nat,
      selected ∈ firstOccurrenceSequence letters ↔ selected ∈ letters
  | [] => by simp [firstOccurrenceSequence]
  | letter :: rest => by
      by_cases equal : selected = letter
      · subst letter
        simp [firstOccurrenceSequence]
      · simp [firstOccurrenceSequence, equal,
          mem_firstOccurrenceSequence_iff selected rest]

/-- Whether the initial variable occurs again in the tail. -/
def repeatedInitial (word : Word Nat) : Bool :=
  decide (word.head ∈ word.tail)

/-- Pointwise profile of variables encountered weakly before the second
initial occurrence. The initial variable is always included. -/
def beforeSecondProfile (word : Word Nat) : Nat → Bool :=
  fun tested =>
    decide
      (tested = word.head ∨
        tested ∈ prefixBefore word.head word.tail)

/-- The exact semantic signature for the initial-second-gap family. -/
structure SameInitialSecondGapSignature
    (left right : Word Nat) : Prop where
  firstOccurrences :
    firstOccurrenceSequence left.toList =
      firstOccurrenceSequence right.toList
  repeatedInitial :
    S5_869.repeatedInitial left = S5_869.repeatedInitial right
  beforeSecond :
    beforeSecondProfile left = beforeSecondProfile right

namespace SameInitialSecondGapSignature

theorem refl (word : Word Nat) :
    SameInitialSecondGapSignature word word :=
  ⟨rfl, rfl, rfl⟩

theorem symm {left right : Word Nat}
    (same : SameInitialSecondGapSignature left right) :
    SameInitialSecondGapSignature right left :=
  ⟨same.firstOccurrences.symm,
    same.repeatedInitial.symm,
    same.beforeSecond.symm⟩

theorem trans {left middle right : Word Nat}
    (first : SameInitialSecondGapSignature left middle)
    (second : SameInitialSecondGapSignature middle right) :
    SameInitialSecondGapSignature left right :=
  ⟨first.firstOccurrences.trans second.firstOccurrences,
    first.repeatedInitial.trans second.repeatedInitial,
    first.beforeSecond.trans second.beforeSecond⟩

theorem head_eq {left right : Word Nat}
    (same : SameInitialSecondGapSignature left right) :
    left.head = right.head := by
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail =>
          have first := same.firstOccurrences
          simp only [Word.toList, firstOccurrenceSequence,
            List.cons.injEq] at first
          exact first.1

end SameInitialSecondGapSignature

theorem head_eq_of_firstOccurrenceSequence_eq
    {left right : Word Nat}
    (equal :
      firstOccurrenceSequence left.toList =
        firstOccurrenceSequence right.toList) :
    left.head = right.head := by
  have heads := congrArg List.head? equal
  simpa [Word.toList, firstOccurrenceSequence] using heads

/-- Marker for detecting a second occurrence of the initial variable. -/
def initialMarker (tested : Nat) : Nat → Fin 5 :=
  fun letter => if letter = tested then 1 else 3

/-- Marker for comparing a variable with the second initial occurrence. -/
def secondGapMarker
    (initial comparator : Nat) : Nat → Fin 5 :=
  fun letter =>
    if letter = initial then 1
    else if letter = comparator then 4
    else 3

/-- The five finite multiplication facts used by both marker automata. -/
structure MarkerLaws
    (mul : Fin 5 → Fin 5 → Fin 5) : Prop where
  zeroAbsorbing : ∀ value, mul 0 value = 0
  twoAbsorbing : ∀ value, mul 2 value = 2
  repeatInitial : mul 1 1 = 0
  passOther : mul 1 3 = 1
  seeComparator : mul 1 4 = 2

namespace MarkerLaws

variable {mul : Fin 5 → Fin 5 → Fin 5}

theorem foldZero
    (laws : MarkerLaws mul) (valuation : Nat → Fin 5) :
    ∀ letters : List Nat,
      letters.foldl
          (fun current letter => mul current (valuation letter)) 0 = 0
  | [] => rfl
  | letter :: rest => by
      simp only [List.foldl_cons]
      rw [laws.zeroAbsorbing]
      exact foldZero laws valuation rest

theorem foldTwo
    (laws : MarkerLaws mul) (valuation : Nat → Fin 5) :
    ∀ letters : List Nat,
      letters.foldl
          (fun current letter => mul current (valuation letter)) 2 = 2
  | [] => rfl
  | letter :: rest => by
      simp only [List.foldl_cons]
      rw [laws.twoAbsorbing]
      exact foldTwo laws valuation rest

theorem initialFold
    (laws : MarkerLaws mul) (tested : Nat) :
    ∀ letters : List Nat,
      letters.foldl
          (fun current letter =>
            mul current (initialMarker tested letter)) 1 =
        if tested ∈ letters then 0 else 1
  | [] => rfl
  | letter :: rest => by
      simp only [List.foldl_cons]
      by_cases equal : letter = tested
      · subst letter
        rw [show initialMarker tested tested = (1 : Fin 5) by
          simp [initialMarker]]
        rw [laws.repeatInitial]
        rw [foldZero laws (initialMarker tested)]
        simp
      · rw [show initialMarker tested letter = (3 : Fin 5) by
          simp [initialMarker, equal]]
        rw [laws.passOther]
        rw [initialFold laws tested rest]
        simp [Ne.symm equal]

/-- Starting in state `1`, the first occurrence among the initial variable
and the comparator chooses an absorbing result: `0` for the second initial
and `2` for the comparator. -/
theorem secondGapFold
    (laws : MarkerLaws mul)
    (initial comparator : Nat)
    (different : comparator ≠ initial) :
    ∀ letters : List Nat,
      initial ∈ letters →
      comparator ∈ letters →
      letters.foldl
          (fun current letter =>
            mul current (secondGapMarker initial comparator letter)) 1 =
        if comparator ∈ prefixBefore initial letters then 2 else 0
  | [], initialMember, _ => by
      simp at initialMember
  | letter :: rest, initialMember, comparatorMember => by
      simp only [List.foldl_cons]
      by_cases initialHit : letter = initial
      · subst letter
        rw [show secondGapMarker initial comparator initial =
            (1 : Fin 5) by
          simp [secondGapMarker]]
        rw [laws.repeatInitial]
        rw [foldZero laws (secondGapMarker initial comparator)]
        simp [prefixBefore]
      · by_cases comparatorHit : letter = comparator
        · subst letter
          rw [show secondGapMarker initial comparator comparator =
              (4 : Fin 5) by
            simp [secondGapMarker, different]]
          rw [laws.seeComparator]
          rw [foldTwo laws (secondGapMarker initial comparator)]
          simp [prefixBefore, different]
        · have initialNeLetter : initial ≠ letter :=
            Ne.symm initialHit
          have comparatorNeLetter : comparator ≠ letter :=
            Ne.symm comparatorHit
          have initialRest : initial ∈ rest := by
            simpa [initialNeLetter] using initialMember
          have comparatorRest : comparator ∈ rest := by
            simpa [comparatorNeLetter] using comparatorMember
          rw [show secondGapMarker initial comparator letter =
              (3 : Fin 5) by
            simp [secondGapMarker, initialHit, comparatorHit]]
          rw [laws.passOther]
          rw [secondGapFold laws initial comparator different rest
            initialRest comparatorRest]
          simp [prefixBefore, initialHit, comparatorNeLetter]

end MarkerLaws

namespace MarkerBridge

theorem repeatedInitial_eq
    (semigroup : Semigroup (Fin 5))
    (evalMarker :
      ∀ (tested : Nat) (tail : List Nat),
        semigroup.eval (initialMarker tested) ⟨tested, tail⟩ =
          if tested ∈ tail then 0 else 1)
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy semigroup)
    (heads : identity.lhs.head = identity.rhs.head) :
    repeatedInitial identity.lhs = repeatedInitial identity.rhs := by
  rcases identity with
    ⟨⟨leftHead, leftTail⟩, ⟨rightHead, rightTail⟩⟩
  let tested := leftHead
  have evaluated := valid (initialMarker tested)
  change leftHead = rightHead at heads
  subst rightHead
  change
    semigroup.eval (initialMarker leftHead)
        ⟨leftHead, leftTail⟩ =
      semigroup.eval (initialMarker leftHead)
        ⟨leftHead, rightTail⟩ at evaluated
  rw [evalMarker, evalMarker] at evaluated
  unfold repeatedInitial
  by_cases leftMember : leftHead ∈ leftTail
  · by_cases rightMember : leftHead ∈ rightTail
    · simp [leftMember, rightMember]
    · simp [leftMember, rightMember] at evaluated
  · by_cases rightMember : leftHead ∈ rightTail
    · simp [leftMember, rightMember] at evaluated
    · simp [leftMember, rightMember]

theorem beforeSecondProfile_eq
    (semigroup : Semigroup (Fin 5))
    (evalMarker :
      ∀ (initial comparator : Nat) (tail : List Nat),
        comparator ≠ initial →
        initial ∈ tail →
        comparator ∈ tail →
        semigroup.eval (secondGapMarker initial comparator)
            ⟨initial, tail⟩ =
          if comparator ∈ prefixBefore initial tail then 2 else 0)
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy semigroup)
    (firstOccurrences :
      firstOccurrenceSequence identity.lhs.toList =
        firstOccurrenceSequence identity.rhs.toList)
    (repetitions :
      repeatedInitial identity.lhs = repeatedInitial identity.rhs) :
    beforeSecondProfile identity.lhs =
      beforeSecondProfile identity.rhs := by
  have heads := head_eq_of_firstOccurrenceSequence_eq firstOccurrences
  rcases identity with
    ⟨⟨leftHead, leftTail⟩, ⟨rightHead, rightTail⟩⟩
  change leftHead = rightHead at heads
  subst rightHead
  simp only [Word.toList] at firstOccurrences
  have supportIff (letter : Nat) :
      letter ∈ leftHead :: leftTail ↔
        letter ∈ leftHead :: rightTail := by
    rw [← mem_firstOccurrenceSequence_iff letter
          (leftHead :: leftTail),
      firstOccurrences,
      mem_firstOccurrenceSequence_iff letter
        (leftHead :: rightTail)]
  funext comparator
  by_cases sameHead : comparator = leftHead
  · subst comparator
    simp [beforeSecondProfile]
  · by_cases leftSupported : comparator ∈ leftTail
    · have rightSupported : comparator ∈ rightTail := by
        have rightWordMember :=
          (supportIff comparator).mp (by
            simp [sameHead, leftSupported])
        simpa [sameHead] using rightWordMember
      by_cases leftRepeated : leftHead ∈ leftTail
      · have rightRepeated : leftHead ∈ rightTail := by
          by_cases rightRepeated : leftHead ∈ rightTail
          · exact rightRepeated
          · unfold repeatedInitial at repetitions
            simp [leftRepeated, rightRepeated] at repetitions
        have evaluated :=
          valid (secondGapMarker leftHead comparator)
        change
          semigroup.eval
              (secondGapMarker leftHead comparator)
              ⟨leftHead, leftTail⟩ =
            semigroup.eval
              (secondGapMarker leftHead comparator)
              ⟨leftHead, rightTail⟩ at evaluated
        rw [evalMarker leftHead comparator leftTail sameHead
            leftRepeated leftSupported,
          evalMarker leftHead comparator rightTail sameHead
            rightRepeated rightSupported] at evaluated
        have beforeIff :
            comparator ∈ prefixBefore leftHead leftTail ↔
              comparator ∈ prefixBefore leftHead rightTail := by
          constructor
          · intro leftBefore
            by_cases rightBefore :
                comparator ∈ prefixBefore leftHead rightTail
            · exact rightBefore
            · simp [leftBefore, rightBefore] at evaluated
          · intro rightBefore
            by_cases leftBefore :
                comparator ∈ prefixBefore leftHead leftTail
            · exact leftBefore
            · simp [leftBefore, rightBefore] at evaluated
        by_cases leftBefore :
            comparator ∈ prefixBefore leftHead leftTail
        · have rightBefore := beforeIff.mp leftBefore
          simp [beforeSecondProfile, sameHead,
            leftBefore, rightBefore]
        · have rightBefore :
              comparator ∉ prefixBefore leftHead rightTail :=
            fun member => leftBefore (beforeIff.mpr member)
          simp [beforeSecondProfile, sameHead,
            leftBefore, rightBefore]
      · have rightNotRepeated : leftHead ∉ rightTail := by
          intro rightRepeated
          unfold repeatedInitial at repetitions
          simp [leftRepeated, rightRepeated] at repetitions
        simp [beforeSecondProfile, sameHead,
          prefixBefore_eq_self_of_not_mem leftHead leftRepeated,
          prefixBefore_eq_self_of_not_mem leftHead rightNotRepeated,
          leftSupported, rightSupported]
    · have rightNotSupported : comparator ∉ rightTail := by
        intro rightSupported
        have leftWordMember :=
          (supportIff comparator).mpr (by
            simp [sameHead, rightSupported])
        have : comparator ∈ leftTail := by
          simpa [sameHead] using leftWordMember
        exact leftSupported this
      have leftNotBefore :
          comparator ∉ prefixBefore leftHead leftTail :=
        fun member =>
          leftSupported <|
            mem_of_mem_prefixBefore leftHead comparator member
      have rightNotBefore :
          comparator ∉ prefixBefore leftHead rightTail :=
        fun member =>
          rightNotSupported <|
            mem_of_mem_prefixBefore leftHead comparator member
      simp [beforeSecondProfile, sameHead,
        leftNotBefore, rightNotBefore]

end MarkerBridge

abbrev table : FiniteTable :=
  Generated.Catalogue.S5_869.table

/-- Quotient with zero-based fibers `[0, 0, 0, 1, 2]`. -/
def firstOccurrenceQuotient :
    SplitSurjection table.semigroup leftRegularBandThree.semigroup where
  toFun := fun value =>
    if value.val = 0 then ⟨0, by decide⟩ else
      if value.val = 1 then ⟨0, by decide⟩ else
        if value.val = 2 then ⟨0, by decide⟩ else
          if value.val = 3 then ⟨1, by decide⟩ else
            ⟨2, by decide⟩
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  preimage := fun value =>
    if value.val = 0 then ⟨0, by decide⟩ else
      if value.val = 1 then ⟨3, by decide⟩ else
        ⟨4, by decide⟩
  right_inverse := by
    intro value
    apply Fin.ext
    revert value
    decide

theorem valid_firstOccurrenceSequence_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    firstOccurrenceSequence identity.lhs.toList =
      firstOccurrenceSequence identity.rhs.toList :=
  S5_345Factors.leftRegularBandThreeValid_firstOccurrenceSequence_eq
    identity
    (firstOccurrenceQuotient.pushforwardIdentity identity valid)

def markerLaws : MarkerLaws Generated.Catalogue.S5_869.mul where
  zeroAbsorbing := by
    intro value
    revert value
    decide
  twoAbsorbing := by
    intro value
    revert value
    decide
  repeatInitial := by decide
  passOther := by decide
  seeComparator := by decide

theorem initialMarker_eval
    (tested : Nat) (tail : List Nat) :
    table.semigroup.eval (initialMarker tested) ⟨tested, tail⟩ =
      if tested ∈ tail then (0 : Fin 5) else 1 := by
  change
    tail.foldl
        (fun current letter =>
          Generated.Catalogue.S5_869.mul current
            (initialMarker tested letter))
        (initialMarker tested tested) =
      if tested ∈ tail then 0 else 1
  rw [show initialMarker tested tested = (1 : Fin 5) by
    simp [initialMarker]]
  exact MarkerLaws.initialFold markerLaws tested tail

theorem secondGapMarker_eval
    (initial comparator : Nat) (tail : List Nat)
    (different : comparator ≠ initial)
    (initialRepeated : initial ∈ tail)
    (comparatorSupported : comparator ∈ tail) :
    table.semigroup.eval (secondGapMarker initial comparator)
        ⟨initial, tail⟩ =
      if comparator ∈ prefixBefore initial tail then (2 : Fin 5) else 0 := by
  change
    tail.foldl
        (fun current letter =>
          Generated.Catalogue.S5_869.mul current
            (secondGapMarker initial comparator letter))
        (secondGapMarker initial comparator initial) =
      if comparator ∈ prefixBefore initial tail then 2 else 0
  rw [show secondGapMarker initial comparator initial = (1 : Fin 5) by
    simp [secondGapMarker]]
  exact MarkerLaws.secondGapFold markerLaws initial comparator different
    tail initialRepeated comparatorSupported

theorem valid_repeatedInitial_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    repeatedInitial identity.lhs = repeatedInitial identity.rhs := by
  have firstOccurrences :=
    valid_firstOccurrenceSequence_eq identity valid
  have heads := head_eq_of_firstOccurrenceSequence_eq firstOccurrences
  exact MarkerBridge.repeatedInitial_eq table.semigroup
    initialMarker_eval identity valid heads

theorem valid_beforeSecondProfile_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    beforeSecondProfile identity.lhs =
      beforeSecondProfile identity.rhs := by
  exact MarkerBridge.beforeSecondProfile_eq table.semigroup
    secondGapMarker_eval identity valid
    (valid_firstOccurrenceSequence_eq identity valid)
    (valid_repeatedInitial_eq identity valid)

theorem valid_sameSignature
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    SameInitialSecondGapSignature identity.lhs identity.rhs :=
  ⟨valid_firstOccurrenceSequence_eq identity valid,
    valid_repeatedInitial_eq identity valid,
    valid_beforeSecondProfile_eq identity valid⟩

set_option maxRecDepth 100000 in
/-- Every derivation from the four-law basis preserves the exact signature. -/
theorem derives_sameSignature
    {left right : Word Nat}
    (derivation : Derives basis left right) :
    SameInitialSecondGapSignature left right := by
  have modelsTable : Models table.semigroup basis :=
    models_of_finite_checks table (by decide)
  exact valid_sameSignature ⟨left, right⟩
    (fun valuation => derivation.sound modelsTable valuation)

end SemigroupBasis.CoRoots.S5_869

namespace SemigroupBasis.CoRoots.S5_871

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.S5_869

abbrev table : FiniteTable :=
  Generated.Catalogue.S5_871.table

/-- Quotient with zero-based fibers `[0, 0, 0, 1, 2]`. -/
def firstOccurrenceQuotient :
    SplitSurjection table.semigroup leftRegularBandThree.semigroup where
  toFun := fun value =>
    if value.val = 0 then ⟨0, by decide⟩ else
      if value.val = 1 then ⟨0, by decide⟩ else
        if value.val = 2 then ⟨0, by decide⟩ else
          if value.val = 3 then ⟨1, by decide⟩ else
            ⟨2, by decide⟩
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  preimage := fun value =>
    if value.val = 0 then ⟨0, by decide⟩ else
      if value.val = 1 then ⟨3, by decide⟩ else
        ⟨4, by decide⟩
  right_inverse := by
    intro value
    apply Fin.ext
    revert value
    decide

theorem valid_firstOccurrenceSequence_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    firstOccurrenceSequence identity.lhs.toList =
      firstOccurrenceSequence identity.rhs.toList :=
  S5_345Factors.leftRegularBandThreeValid_firstOccurrenceSequence_eq
    identity
    (firstOccurrenceQuotient.pushforwardIdentity identity valid)

def markerLaws : MarkerLaws Generated.Catalogue.S5_871.mul where
  zeroAbsorbing := by
    intro value
    revert value
    decide
  twoAbsorbing := by
    intro value
    revert value
    decide
  repeatInitial := by decide
  passOther := by decide
  seeComparator := by decide

theorem initialMarker_eval
    (tested : Nat) (tail : List Nat) :
    table.semigroup.eval (initialMarker tested) ⟨tested, tail⟩ =
      if tested ∈ tail then (0 : Fin 5) else 1 := by
  change
    tail.foldl
        (fun current letter =>
          Generated.Catalogue.S5_871.mul current
            (initialMarker tested letter))
        (initialMarker tested tested) =
      if tested ∈ tail then 0 else 1
  rw [show initialMarker tested tested = (1 : Fin 5) by
    simp [initialMarker]]
  exact MarkerLaws.initialFold markerLaws tested tail

theorem secondGapMarker_eval
    (initial comparator : Nat) (tail : List Nat)
    (different : comparator ≠ initial)
    (initialRepeated : initial ∈ tail)
    (comparatorSupported : comparator ∈ tail) :
    table.semigroup.eval (secondGapMarker initial comparator)
        ⟨initial, tail⟩ =
      if comparator ∈ prefixBefore initial tail then (2 : Fin 5) else 0 := by
  change
    tail.foldl
        (fun current letter =>
          Generated.Catalogue.S5_871.mul current
            (secondGapMarker initial comparator letter))
        (secondGapMarker initial comparator initial) =
      if comparator ∈ prefixBefore initial tail then 2 else 0
  rw [show secondGapMarker initial comparator initial = (1 : Fin 5) by
    simp [secondGapMarker]]
  exact MarkerLaws.secondGapFold markerLaws initial comparator different
    tail initialRepeated comparatorSupported

theorem valid_repeatedInitial_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    repeatedInitial identity.lhs = repeatedInitial identity.rhs := by
  have firstOccurrences :=
    valid_firstOccurrenceSequence_eq identity valid
  have heads := head_eq_of_firstOccurrenceSequence_eq firstOccurrences
  exact MarkerBridge.repeatedInitial_eq table.semigroup
    initialMarker_eval identity valid heads

theorem valid_beforeSecondProfile_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    beforeSecondProfile identity.lhs =
      beforeSecondProfile identity.rhs := by
  exact MarkerBridge.beforeSecondProfile_eq table.semigroup
    secondGapMarker_eval identity valid
    (valid_firstOccurrenceSequence_eq identity valid)
    (valid_repeatedInitial_eq identity valid)

theorem valid_sameSignature
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    SameInitialSecondGapSignature identity.lhs identity.rhs :=
  ⟨valid_firstOccurrenceSequence_eq identity valid,
    valid_repeatedInitial_eq identity valid,
    valid_beforeSecondProfile_eq identity valid⟩

end SemigroupBasis.CoRoots.S5_871
