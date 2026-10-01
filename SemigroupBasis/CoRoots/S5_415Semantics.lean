import SemigroupBasis.CoRoots.S5_415

namespace SemigroupBasis.CoRoots.S5_415

open SemigroupBasis

private def coordinateForbidden (left right : Fin 5) : Prop :=
  finalCoordinate left ≠ firstCoordinate right

def BrandtSupportZero
    (valuation : Nat → Fin 5) (word : Word Nat) : Prop :=
  ∃ letter, letter ∈ word.toList ∧ valuation letter = 0

def BrandtForbiddenEdge
    (valuation : Nat → Fin 5) (word : Word Nat) : Prop :=
  ∃ source target,
    (source, target) ∈ word.adjacentPairs ∧
      coordinateForbidden (valuation source) (valuation target)

private theorem catalogueMul_coordinate_good
    (initial : Fin 2) (previous right : Fin 5)
    (rightNonzero : right ≠ 0)
    (good : ¬coordinateForbidden previous right) :
    Generated.Catalogue.S5_415.mul
        (coordinateValue initial (finalCoordinate previous))
        right =
      coordinateValue initial (finalCoordinate right) := by
  unfold coordinateForbidden at good
  decide +revert

private theorem catalogueMul_coordinate_bad
    (initial : Fin 2) (previous right : Fin 5)
    (bad : coordinateForbidden previous right) :
    Generated.Catalogue.S5_415.mul
        (coordinateValue initial (finalCoordinate previous))
        right = 0 := by
  unfold coordinateForbidden at bad
  decide +revert

private theorem catalogueMul_zero_left (right : Fin 5) :
    Generated.Catalogue.S5_415.mul 0 right = 0 := by
  decide +revert

private theorem catalogueMul_zero_right (left : Fin 5) :
    Generated.Catalogue.S5_415.mul left 0 = 0 := by
  decide +revert

private theorem brandtFold_zero
    (valuation : Nat → Fin 5) (letters : List Nat) :
    letters.foldl
        (fun current letter =>
          Generated.Catalogue.S5_415.mul current (valuation letter))
        0 = 0 := by
  induction letters with
  | nil => rfl
  | cons letter rest ih =>
      simp only [List.foldl_cons, catalogueMul_zero_left]
      exact ih

private theorem brandtFold_zero_of_member
    (valuation : Nat → Fin 5) (letters : List Nat) (initial : Fin 5)
    (zeroMember : ∃ letter, letter ∈ letters ∧ valuation letter = 0) :
    letters.foldl
        (fun current letter =>
          Generated.Catalogue.S5_415.mul current (valuation letter))
        initial = 0 := by
  induction letters generalizing initial with
  | nil =>
      rcases zeroMember with ⟨letter, member, _⟩
      simp at member
  | cons next rest ih =>
      rcases zeroMember with ⟨letter, member, zeroValue⟩
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · simp only [List.foldl_cons, zeroValue, catalogueMul_zero_right]
        exact brandtFold_zero valuation rest
      · simp only [List.foldl_cons]
        exact ih
          (Generated.Catalogue.S5_415.mul initial (valuation next))
          ⟨letter, member, zeroValue⟩

theorem brandtEval_zero_of_support
    (valuation : Nat → Fin 5) (word : Word Nat)
    (zeroSupport : BrandtSupportZero valuation word) :
    Generated.Catalogue.S5_415.table.semigroup.eval
        valuation word = (0 : Fin 5) := by
  cases word with
  | mk head tail =>
      rcases zeroSupport with ⟨letter, member, zeroValue⟩
      simp only [Word.toList, List.mem_cons] at member
      rcases member with rfl | member
      · simp only [Semigroup.eval, zeroValue]
        exact brandtFold_zero valuation tail
      · exact brandtFold_zero_of_member valuation tail
          (valuation head) ⟨letter, member, zeroValue⟩

private theorem brandtFold_good
    (valuation : Nat → Fin 5) (initial : Fin 2)
    (previous : Nat) (letters : List Nat)
    (lettersNonzero :
      ∀ letter, letter ∈ letters → valuation letter ≠ 0)
    (edgesGood :
      ∀ source target,
        (source, target) ∈ Word.adjacentPairsFrom previous letters →
          ¬coordinateForbidden
            (valuation source) (valuation target)) :
    letters.foldl
        (fun current letter =>
          Generated.Catalogue.S5_415.mul current (valuation letter))
        (coordinateValue initial (finalCoordinate (valuation previous))) =
      coordinateValue initial
        (finalCoordinate (valuation (letters.getLastD previous))) := by
  induction letters generalizing previous with
  | nil => rfl
  | cons next rest ih =>
      simp only [List.foldl_cons, List.getLastD_cons]
      rw [catalogueMul_coordinate_good initial (valuation previous)
        (valuation next)
        (lettersNonzero next (by simp))]
      · apply ih
        · intro letter member
          exact lettersNonzero letter (by simp [member])
        · intro source target member
          exact edgesGood source target (by
            simp only [Word.adjacentPairsFrom, List.mem_cons]
            exact Or.inr member)
      · exact edgesGood previous next (by
          simp [Word.adjacentPairsFrom])

theorem brandtEval_good
    (valuation : Nat → Fin 5) (word : Word Nat)
    (supportGood : ¬BrandtSupportZero valuation word)
    (edgesGood : ¬BrandtForbiddenEdge valuation word) :
    Generated.Catalogue.S5_415.table.semigroup.eval valuation word =
      coordinateValue
        (firstCoordinate (valuation word.head))
        (finalCoordinate (valuation word.final)) := by
  cases word with
  | mk head tail =>
      have headNonzero : valuation head ≠ 0 := by
        intro zeroValue
        exact supportGood ⟨head, by simp [Word.toList], zeroValue⟩
      have tailNonzero :
          ∀ letter, letter ∈ tail → valuation letter ≠ 0 := by
        intro letter member zeroValue
        exact supportGood
          ⟨letter, by simp [Word.toList, member], zeroValue⟩
      have allEdgesGood :
          ∀ source target,
            (source, target) ∈ Word.adjacentPairsFrom head tail →
              ¬coordinateForbidden
                (valuation source) (valuation target) := by
        intro source target member bad
        exact edgesGood
          ⟨source, target, by
            simpa [Word.adjacentPairs] using member, bad⟩
      change
        tail.foldl
            (fun current letter =>
              Generated.Catalogue.S5_415.mul current
                (valuation letter))
            (valuation head) =
          coordinateValue (firstCoordinate (valuation head))
            (finalCoordinate (valuation (tail.getLastD head)))
      calc
        _ =
            tail.foldl
              (fun current letter =>
                Generated.Catalogue.S5_415.mul current
                  (valuation letter))
              (coordinateValue (firstCoordinate (valuation head))
                (finalCoordinate (valuation head))) := by
              congr 1
              exact (coordinateValue_eq
                (valuation head) headNonzero).symm
        _ = _ :=
          brandtFold_good valuation
            (firstCoordinate (valuation head)) head tail
            tailNonzero allEdgesGood

private theorem brandtFold_zero_of_forbidden
    (valuation : Nat → Fin 5) (initial : Fin 2)
    (previous : Nat) (letters : List Nat)
    (lettersNonzero :
      ∀ letter, letter ∈ letters → valuation letter ≠ 0)
    (forbidden :
      ∃ source target,
        (source, target) ∈ Word.adjacentPairsFrom previous letters ∧
          coordinateForbidden (valuation source) (valuation target)) :
    letters.foldl
        (fun current letter =>
          Generated.Catalogue.S5_415.mul current (valuation letter))
        (coordinateValue initial (finalCoordinate (valuation previous))) =
      0 := by
  induction letters generalizing previous with
  | nil =>
      rcases forbidden with ⟨source, target, member, _⟩
      simp [Word.adjacentPairsFrom] at member
  | cons next rest ih =>
      simp only [List.foldl_cons]
      by_cases firstBad :
          coordinateForbidden (valuation previous) (valuation next)
      · rw [catalogueMul_coordinate_bad initial
          (valuation previous) (valuation next) firstBad]
        exact brandtFold_zero valuation rest
      · rw [catalogueMul_coordinate_good initial
          (valuation previous) (valuation next)
          (lettersNonzero next (by simp)) firstBad]
        apply ih
        · intro letter member
          exact lettersNonzero letter (by simp [member])
        · rcases forbidden with ⟨source, target, member, bad⟩
          simp only [Word.adjacentPairsFrom, List.mem_cons] at member
          rcases member with first | later
          · have sourceEq : source = previous :=
              congrArg Prod.fst first
            have targetEq : target = next :=
              congrArg Prod.snd first
            subst source
            subst target
            exact False.elim (firstBad bad)
          · exact ⟨source, target, later, bad⟩

theorem brandtEval_zero_of_forbidden
    (valuation : Nat → Fin 5) (word : Word Nat)
    (supportGood : ¬BrandtSupportZero valuation word)
    (forbidden : BrandtForbiddenEdge valuation word) :
    Generated.Catalogue.S5_415.table.semigroup.eval
        valuation word = (0 : Fin 5) := by
  cases word with
  | mk head tail =>
      have headNonzero : valuation head ≠ 0 := by
        intro zeroValue
        exact supportGood ⟨head, by simp [Word.toList], zeroValue⟩
      have tailNonzero :
          ∀ letter, letter ∈ tail → valuation letter ≠ 0 := by
        intro letter member zeroValue
        exact supportGood
          ⟨letter, by simp [Word.toList, member], zeroValue⟩
      rcases forbidden with ⟨source, target, member, bad⟩
      simp only [Semigroup.eval]
      rw [← coordinateValue_eq (valuation head) headNonzero]
      exact brandtFold_zero_of_forbidden valuation
        (firstCoordinate (valuation head)) head tail tailNonzero
        ⟨source, target, by
          simpa [Word.adjacentPairs] using member, bad⟩

def EndpointAssignment := Nat → Fin 2 × Fin 2

def unitValue (coordinates : Fin 2 × Fin 2) : Fin 5 :=
  coordinateValue coordinates.1 coordinates.2

def unitValuation
    (assignment : EndpointAssignment) : Nat → Fin 5 :=
  fun letter => unitValue (assignment letter)

def endpointAssignment
    (valuation : Nat → Fin 5) : EndpointAssignment :=
  fun letter =>
    (firstCoordinate (valuation letter),
      finalCoordinate (valuation letter))

@[simp]
theorem firstCoordinate_unitValue (coordinates : Fin 2 × Fin 2) :
    firstCoordinate (unitValue coordinates) = coordinates.1 := by
  simp [unitValue]

@[simp]
theorem finalCoordinate_unitValue (coordinates : Fin 2 × Fin 2) :
    finalCoordinate (unitValue coordinates) = coordinates.2 := by
  simp [unitValue]

theorem unitValue_ne_zero (coordinates : Fin 2 × Fin 2) :
    unitValue coordinates ≠ (0 : Fin 5) := by
  exact coordinateValue_ne_zero coordinates.1 coordinates.2

theorem unitValue_injective : Function.Injective unitValue := by
  intro left right equality
  apply Prod.ext
  · simpa using congrArg firstCoordinate equality
  · simpa using congrArg finalCoordinate equality

/-- A coordinate assignment is compatible with a word when no adjacent
matrix-unit coordinates mismatch. -/
def Compatible
    (assignment : EndpointAssignment) (word : Word Nat) : Prop :=
  ¬BrandtForbiddenEdge (unitValuation assignment) word

/-- Compatibility is exactly equality of the outgoing coordinate of each
letter with the incoming coordinate of its successor. This public form is
the bridge from endpoint assignments to the undirected constraint graph. -/
theorem compatible_iff_adjacent_endpoint_eq
    (assignment : EndpointAssignment) (word : Word Nat) :
    Compatible assignment word ↔
      ∀ source target,
        (source, target) ∈ word.adjacentPairs →
          (assignment source).2 = (assignment target).1 := by
  constructor
  · intro compatible source target member
    apply Decidable.byContradiction
    intro different
    exact compatible
      ⟨source, target, member, by
        simpa [coordinateForbidden, unitValuation, unitValue] using
          different⟩
  · intro adjacent
    rintro ⟨source, target, member, different⟩
    exact different <| by
      simpa [coordinateForbidden, unitValuation, unitValue] using
        adjacent source target member

/-- The exact structural signature of a Brandt-semigroup term function:
support, compatibility under every endpoint assignment, and the exposed
initial/final coordinates whenever the product is nonzero. -/
def SameBrandtSignature (left right : Word Nat) : Prop :=
  (∀ letter, letter ∈ left.toList ↔ letter ∈ right.toList) ∧
    ∀ assignment : EndpointAssignment,
      (Compatible assignment left ↔ Compatible assignment right) ∧
        (Compatible assignment left →
          (assignment left.head).1 = (assignment right.head).1 ∧
            (assignment left.final).2 =
              (assignment right.final).2)

private def supportSeparator (tested : Nat) : Nat → Fin 5 :=
  fun letter =>
    if letter = tested then 0 else coordinateValue 0 0

private theorem fold_supportSeparator
    (tested : Nat) (letters : List Nat) (present : Bool) :
    letters.foldl
        (fun current letter =>
          Generated.Catalogue.S5_415.mul current
            (supportSeparator tested letter))
        (if present then 0 else coordinateValue 0 0) =
      if present || letters.contains tested then
        0
      else
        coordinateValue 0 0 := by
  induction letters generalizing present with
  | nil => simp
  | cons letter rest ih =>
      simp only [List.foldl_cons, List.contains_cons]
      cases present with
      | false =>
          by_cases hit : letter = tested
          · subst letter
            simpa [supportSeparator,
              Generated.Catalogue.S5_415.mul] using ih true
          · have reverse : tested ≠ letter := Ne.symm hit
            simpa [supportSeparator, hit, reverse,
              Generated.Catalogue.S5_415.mul] using ih false
      | true =>
          change
            rest.foldl
                (fun current next =>
                  Generated.Catalogue.S5_415.mul current
                    (supportSeparator tested next))
                (Generated.Catalogue.S5_415.mul 0
                  (supportSeparator tested letter)) = 0
          rw [catalogueMul_zero_left]
          simpa using ih true

theorem eval_supportSeparator_zero_iff
    (tested : Nat) (word : Word Nat) :
    Generated.Catalogue.S5_415.table.semigroup.eval
        (supportSeparator tested) word = (0 : Fin 5) ↔
      tested ∈ word.toList := by
  cases word with
  | mk head tail =>
      simp only [Semigroup.eval, Word.toList, List.mem_cons]
      by_cases hit : head = tested
      · subst head
        rw [show supportSeparator tested tested = (0 : Fin 5) by
          simp [supportSeparator]]
        change
          tail.foldl
              (fun current letter =>
                Generated.Catalogue.S5_415.mul current
                  (supportSeparator tested letter))
              0 = 0 ↔ _
        rw [brandtFold_zero]
        simp
      · have reverse : tested ≠ head := Ne.symm hit
        rw [show supportSeparator tested head =
            coordinateValue 0 0 by
          simp [supportSeparator, hit]]
        change
          tail.foldl
              (fun current letter =>
                Generated.Catalogue.S5_415.mul current
                  (supportSeparator tested letter))
              (coordinateValue 0 0) = 0 ↔ _
        have foldEquality :
            tail.foldl
                (fun current letter =>
                  Generated.Catalogue.S5_415.mul current
                    (supportSeparator tested letter))
                (coordinateValue 0 0) =
              if tail.contains tested then 0 else coordinateValue 0 0 := by
          simpa using fold_supportSeparator tested tail false
        rw [foldEquality]
        simp [hit, reverse, coordinateValue_ne_zero]

private theorem unitSupportGood
    (assignment : EndpointAssignment) (word : Word Nat) :
    ¬BrandtSupportZero (unitValuation assignment) word := by
  rintro ⟨letter, _, zeroValue⟩
  exact unitValue_ne_zero (assignment letter) zeroValue

theorem eval_unit_of_compatible
    (assignment : EndpointAssignment) (word : Word Nat)
    (compatible : Compatible assignment word) :
    Generated.Catalogue.S5_415.table.semigroup.eval
        (unitValuation assignment) word =
      unitValue
        ((assignment word.head).1,
          (assignment word.final).2) := by
  simpa [unitValuation, unitValue] using
    brandtEval_good (unitValuation assignment) word
      (unitSupportGood assignment word) compatible

private theorem forbiddenEdge_endpoint_iff
    (valuation : Nat → Fin 5) (word : Word Nat) :
    BrandtForbiddenEdge
        (unitValuation (endpointAssignment valuation)) word ↔
      BrandtForbiddenEdge valuation word := by
  constructor
  · rintro ⟨source, target, member, bad⟩
    exact ⟨source, target, member, by
      simpa [coordinateForbidden, unitValuation, unitValue,
        endpointAssignment] using bad⟩
  · rintro ⟨source, target, member, bad⟩
    exact ⟨source, target, member, by
      simpa [coordinateForbidden, unitValuation, unitValue,
        endpointAssignment] using bad⟩

private theorem supportZero_iff_of_sameSupport
    (valuation : Nat → Fin 5) {left right : Word Nat}
    (sameSupport :
      ∀ letter, letter ∈ left.toList ↔ letter ∈ right.toList) :
    BrandtSupportZero valuation left ↔
      BrandtSupportZero valuation right := by
  constructor
  · rintro ⟨letter, member, zeroValue⟩
    exact ⟨letter, (sameSupport letter).mp member, zeroValue⟩
  · rintro ⟨letter, member, zeroValue⟩
    exact ⟨letter, (sameSupport letter).mpr member, zeroValue⟩

private theorem forbiddenEdge_iff_of_sameSignature
    (valuation : Nat → Fin 5) {left right : Word Nat}
    (same : SameBrandtSignature left right) :
    BrandtForbiddenEdge valuation left ↔
      BrandtForbiddenEdge valuation right := by
  classical
  let assignment := endpointAssignment valuation
  have compatibleIff := (same.2 assignment).1
  have leftEndpoint :=
    forbiddenEdge_endpoint_iff valuation left
  have rightEndpoint :=
    forbiddenEdge_endpoint_iff valuation right
  constructor
  · intro leftBad
    have unitLeftBad : BrandtForbiddenEdge
        (unitValuation assignment) left :=
      leftEndpoint.mpr leftBad
    apply Decidable.byContradiction
    intro rightGood
    have unitRightGood : Compatible assignment right := by
      intro unitRightBad
      exact rightGood (rightEndpoint.mp unitRightBad)
    exact (compatibleIff.mpr unitRightGood) unitLeftBad
  · intro rightBad
    have unitRightBad : BrandtForbiddenEdge
        (unitValuation assignment) right :=
      rightEndpoint.mpr rightBad
    apply Decidable.byContradiction
    intro leftGood
    have unitLeftGood : Compatible assignment left := by
      intro unitLeftBad
      exact leftGood (leftEndpoint.mp unitLeftBad)
    exact (compatibleIff.mp unitLeftGood) unitRightBad

/-- Every valid Brandt identity has the exact endpoint-connectivity
signature. -/
theorem valid_sameBrandtSignature
    {identity : Identity Nat}
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_415.table.semigroup) :
    SameBrandtSignature identity.lhs identity.rhs := by
  refine ⟨?_, ?_⟩
  · intro letter
    have evaluated := valid (supportSeparator letter)
    constructor
    · intro leftMember
      have leftZero :=
        (eval_supportSeparator_zero_iff letter identity.lhs).mpr
          leftMember
      have rightZero :
          Generated.Catalogue.S5_415.table.semigroup.eval
              (supportSeparator letter) identity.rhs = (0 : Fin 5) := by
        rw [← evaluated]
        exact leftZero
      exact
        (eval_supportSeparator_zero_iff letter identity.rhs).mp
          rightZero
    · intro rightMember
      have rightZero :=
        (eval_supportSeparator_zero_iff letter identity.rhs).mpr
          rightMember
      have leftZero :
          Generated.Catalogue.S5_415.table.semigroup.eval
              (supportSeparator letter) identity.lhs = (0 : Fin 5) := by
        rw [evaluated]
        exact rightZero
      exact
        (eval_supportSeparator_zero_iff letter identity.lhs).mp
          leftZero
  · intro assignment
    have evaluated := valid (unitValuation assignment)
    have compatibleIff :
        Compatible assignment identity.lhs ↔
          Compatible assignment identity.rhs := by
      constructor
      · intro leftCompatible
        by_cases rightForbidden :
            BrandtForbiddenEdge
              (unitValuation assignment) identity.rhs
        · have leftEval :=
            eval_unit_of_compatible assignment identity.lhs
              leftCompatible
          have rightEval :=
            brandtEval_zero_of_forbidden
              (unitValuation assignment) identity.rhs
              (unitSupportGood assignment identity.rhs)
              rightForbidden
          rw [leftEval, rightEval] at evaluated
          exact False.elim
            (unitValue_ne_zero
              ((assignment identity.lhs.head).1,
                (assignment identity.lhs.final).2) evaluated)
        · exact rightForbidden
      · intro rightCompatible
        by_cases leftForbidden :
            BrandtForbiddenEdge
              (unitValuation assignment) identity.lhs
        · have leftEval :=
            brandtEval_zero_of_forbidden
              (unitValuation assignment) identity.lhs
              (unitSupportGood assignment identity.lhs)
              leftForbidden
          have rightEval :=
            eval_unit_of_compatible assignment identity.rhs
              rightCompatible
          rw [leftEval, rightEval] at evaluated
          exact False.elim
            (unitValue_ne_zero
              ((assignment identity.rhs.head).1,
                (assignment identity.rhs.final).2) evaluated.symm)
        · exact leftForbidden
    refine ⟨compatibleIff, ?_⟩
    intro leftCompatible
    have rightCompatible := compatibleIff.mp leftCompatible
    have pairEquality :
        ((assignment identity.lhs.head).1,
            (assignment identity.lhs.final).2) =
          ((assignment identity.rhs.head).1,
            (assignment identity.rhs.final).2) := by
      apply unitValue_injective
      simpa only [
        eval_unit_of_compatible assignment identity.lhs
          leftCompatible,
        eval_unit_of_compatible assignment identity.rhs
          rightCompatible] using evaluated
    have firstEquality :=
      congrArg (fun pair : Fin 2 × Fin 2 => pair.1) pairEquality
    have finalEquality :=
      congrArg (fun pair : Fin 2 × Fin 2 => pair.2) pairEquality
    exact ⟨firstEquality, finalEquality⟩

/-- The endpoint-connectivity signature is sufficient for a Brandt
identity, uniformly over arbitrary words and valuations. -/
theorem valid_of_sameBrandtSignature
    {identity : Identity Nat}
    (same : SameBrandtSignature identity.lhs identity.rhs) :
    identity.SatisfiedBy
      Generated.Catalogue.S5_415.table.semigroup := by
  intro valuation
  have supportIff :=
    supportZero_iff_of_sameSupport valuation same.1
  have forbiddenIff :=
    forbiddenEdge_iff_of_sameSignature valuation same
  by_cases leftSupportZero :
      BrandtSupportZero valuation identity.lhs
  · rw [brandtEval_zero_of_support valuation identity.lhs
      leftSupportZero]
    rw [brandtEval_zero_of_support valuation identity.rhs
      (supportIff.mp leftSupportZero)]
  · have rightSupportGood :
        ¬BrandtSupportZero valuation identity.rhs :=
      fun bad => leftSupportZero (supportIff.mpr bad)
    by_cases leftForbidden :
        BrandtForbiddenEdge valuation identity.lhs
    · rw [brandtEval_zero_of_forbidden valuation identity.lhs
        leftSupportZero leftForbidden]
      rw [brandtEval_zero_of_forbidden valuation identity.rhs
        rightSupportGood (forbiddenIff.mp leftForbidden)]
    · have rightEdgesGood :
          ¬BrandtForbiddenEdge valuation identity.rhs :=
        fun bad => leftForbidden (forbiddenIff.mpr bad)
      let assignment := endpointAssignment valuation
      have leftCompatible : Compatible assignment identity.lhs := by
        intro unitBad
        exact leftForbidden
          ((forbiddenEdge_endpoint_iff valuation identity.lhs).mp
            unitBad)
      have endpoints := (same.2 assignment).2 leftCompatible
      rw [brandtEval_good valuation identity.lhs
        leftSupportZero leftForbidden]
      rw [brandtEval_good valuation identity.rhs
        rightSupportGood rightEdgesGood]
      have endpointPairEquality :
          ((assignment identity.lhs.head).1,
              (assignment identity.lhs.final).2) =
            ((assignment identity.rhs.head).1,
              (assignment identity.rhs.final).2) := by
        apply Prod.ext
        · exact endpoints.1
        · exact endpoints.2
      simpa [assignment, endpointAssignment] using
        congrArg
          (fun pair : Fin 2 × Fin 2 =>
            coordinateValue pair.1 pair.2)
          endpointPairEquality

/-- Exact table-level word problem for identities of catalogue `S5_415`. -/
theorem satisfiedBy_iff_sameBrandtSignature
    (identity : Identity Nat) :
    identity.SatisfiedBy
        Generated.Catalogue.S5_415.table.semigroup ↔
      SameBrandtSignature identity.lhs identity.rhs :=
  ⟨valid_sameBrandtSignature, valid_of_sameBrandtSignature⟩

/-- The same exact semantic word problem in the literal opposite
orientation, transported through matrix-unit transposition. -/
theorem opposite_satisfiedBy_iff_sameBrandtSignature
    (identity : Identity Nat) :
    identity.SatisfiedBy
        Generated.Catalogue.S5_415.table.semigroup.opposite ↔
      SameBrandtSignature identity.lhs identity.rhs :=
  (sameIdentityTheory_opposite identity).symm.trans
    (satisfiedBy_iff_sameBrandtSignature identity)

end SemigroupBasis.CoRoots.S5_415
