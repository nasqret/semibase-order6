import SemigroupBasis.CoRoots.Order6LeeLiProposition8ANormalization
import SemigroupBasis.CoRoots.S5_841

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6LeeLiProposition8A

open SemigroupBasis

/-!
# Lee--Li Proposition 8.1/A pair semantics

This module isolates the finite semantic part of Lee--Li Lemma 8.4(ii).
For a fixed ordered pair of variables, every cap-three word projects to a
binary word of length at most six.  Direct evaluation in the published
monoid `A` then determines complete precedence except for the two published
exception families

* `xxyyy` versus `xyyyx`;
* `xxxyyy` versus `yyyxxx`;

for the currently queried ordered pair.  Reversing the queried pair performs
the corresponding binary re-encoding, so no larger exception orbit is needed
inside the ordered classifier.

The final public theorem deliberately receives one explicit
`CanonicalExceptionsExcluded` premise.  The forthcoming canonicalization
layer must discharge exactly this adapter from canonical conditions V and VI
(using the intermediate first occurrence in case V and the fixed adjacent
cube order in case VI).  No completeness or normalization claim is made here.
-/

namespace Semantics

/-! ## Binary words and the finite universe -/

/-- All binary words of one exact length. -/
def binaryWordsExact : Nat → List (List (Fin 2))
  | 0 => [[]]
  | length + 1 =>
      (binaryWordsExact length).flatMap fun tail =>
        [(0 : Fin 2) :: tail, (1 : Fin 2) :: tail]

/-- All binary words whose length is at most the displayed bound. -/
def allBinaryWordsUpTo (bound : Nat) : List (List (Fin 2)) :=
  (List.range (bound + 1)).flatMap binaryWordsExact

private theorem finTwo_eq_zero_or_one (value : Fin 2) :
    value = 0 ∨ value = 1 := by
  have cases : value.val = 0 ∨ value.val = 1 := by
    omega
  rcases cases with zero | one
  · left
    apply Fin.ext
    simpa using zero
  · right
    apply Fin.ext
    simpa using one

private theorem mem_binaryWordsExact_iff
    (letters : List (Fin 2)) (length : Nat) :
    letters ∈ binaryWordsExact length ↔
      letters.length = length := by
  induction length generalizing letters with
  | zero =>
      simp [binaryWordsExact]
  | succ length induction =>
      cases letters with
      | nil =>
          simp [binaryWordsExact]
      | cons head tail =>
          rcases finTwo_eq_zero_or_one head with rfl | rfl
          · simp [binaryWordsExact, induction]
          · simp [binaryWordsExact, induction]

private theorem mem_allBinaryWordsUpTo_of_length_le
    {letters : List (Fin 2)} {bound : Nat}
    (bounded : letters.length ≤ bound) :
    letters ∈ allBinaryWordsUpTo bound := by
  rw [allBinaryWordsUpTo, List.mem_flatMap]
  refine ⟨letters.length, ?_, ?_⟩
  · simp
    omega
  · exact (mem_binaryWordsExact_iff letters letters.length).mpr rfl

private theorem binary_length_eq_counts
    (letters : List (Fin 2)) :
    letters.length = letters.count 0 + letters.count 1 := by
  induction letters with
  | nil =>
      simp
  | cons head tail induction =>
      rcases finTwo_eq_zero_or_one head with rfl | rfl
      · simp [induction, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      · simp [induction, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- A Boolean search for a contiguous cube of one binary letter. -/
def binaryHasTripleBlock (bit : Fin 2) :
    List (Fin 2) → Bool
  | [] => false
  | first :: rest =>
      ((first :: rest).take 3 == [bit, bit, bit]) ||
        binaryHasTripleBlock bit rest

/-- The finite hypotheses inherited from Proposition 8 canonical form:
both multiplicities are at most three, and every multiplicity-three letter
is one contiguous cube. -/
def BinaryProjectionReady (letters : List (Fin 2)) : Prop :=
  letters.count 0 ≤ 3 ∧
    letters.count 1 ≤ 3 ∧
    (letters.count 0 = 3 →
      binaryHasTripleBlock 0 letters = true) ∧
    (letters.count 1 = 3 →
      binaryHasTripleBlock 1 letters = true)

private theorem BinaryProjectionReady.length_le_six
    {letters : List (Fin 2)}
    (ready : BinaryProjectionReady letters) :
    letters.length ≤ 6 := by
  have zeroBound : letters.count 0 ≤ 3 := ready.1
  have oneBound : letters.count 1 ≤ 3 := ready.2.1
  rw [binary_length_eq_counts]
  omega

/-! ## Binary published-A term functions -/

def binaryValue
    (zeroValue oneValue : Fin 6) (bit : Fin 2) : Fin 6 :=
  if bit = 0 then zeroValue else oneValue

/-- Evaluate a possibly empty binary word from the identity of published
monoid `A`. -/
def binaryListEval
    (zeroValue oneValue : Fin 6)
    (letters : List (Fin 2)) : Fin 6 :=
  letters.foldl
    (fun current bit =>
      publishedMul current (binaryValue zeroValue oneValue bit))
    publishedIdentityElement

/-- Equality of the complete two-variable term functions in published
monoid `A`. -/
def BinaryTermEquivalent
    (left right : List (Fin 2)) : Prop :=
  ∀ zeroValue oneValue : Fin 6,
    binaryListEval zeroValue oneValue left =
      binaryListEval zeroValue oneValue right

private def binaryPrecedenceStep
    (state : S5_841.PrecedenceState) (bit : Fin 2) :
    S5_841.PrecedenceState :=
  if bit = 0 then
    match state with
    | .neither => .onlyX
    | .onlyX => .onlyX
    | .onlyY | .ordered | .violated => .violated
  else
    match state with
    | .neither => .onlyY
    | .onlyX => .ordered
    | .onlyY => .onlyY
    | .ordered => .ordered
    | .violated => .violated

/-- Complete precedence of binary letter zero over binary letter one. -/
def BinaryCompletePrecedence (letters : List (Fin 2)) : Prop :=
  letters.foldl binaryPrecedenceStep .neither = .ordered

/-! ## The exact finite obstruction orbit -/

def binaryPairMatches
    (left right first second : List (Fin 2)) : Prop :=
  (left = first ∧ right = second) ∨
    (left = second ∧ right = first)

/-- The two CP-changing Lee--Li exceptional families for the ordered query
`BinaryCompletePrecedence(0,1)`, closed under interchange of the two sides.
Bit-swapped or reversed queries are handled by calling the classifier for the
oppositely ordered original-variable pair. -/
def BinaryExceptionalPair
    (left right : List (Fin 2)) : Prop :=
  binaryPairMatches left right
      [0, 0, 1, 1, 1] [0, 1, 1, 1, 0] ∨
    binaryPairMatches left right
      [0, 0, 0, 1, 1, 1] [1, 1, 1, 0, 0, 0]

/-- The finite search universe after enforcing cap three and contiguous
cubes.  Filtering first keeps the kernel decision certificate small. -/
def binaryReadyWords : List (List (Fin 2)) :=
  (allBinaryWordsUpTo 6).filter fun letters =>
    @decide (BinaryProjectionReady letters) (by
      unfold BinaryProjectionReady
      infer_instance)

private theorem mem_binaryReadyWords
    {letters : List (Fin 2)}
    (ready : BinaryProjectionReady letters) :
    letters ∈ binaryReadyWords := by
  letI : Decidable (BinaryProjectionReady letters) := by
    unfold BinaryProjectionReady
    infer_instance
  apply List.mem_filter.mpr
  exact ⟨mem_allBinaryWordsUpTo_of_length_le ready.length_le_six,
    decide_eq_true ready⟩

/- PROOF-SHAPE-FRAGMENT-BEGIN semantics_decided_classifier_and_typed_bridge -/
set_option maxHeartbeats 0 in
private theorem binaryTermClassifier_checked :
    binaryReadyWords.all (fun left =>
      binaryReadyWords.all (fun right =>
        @decide
          (BinaryTermEquivalent left right →
            ((BinaryCompletePrecedence left ↔
                BinaryCompletePrecedence right) ∨
              BinaryExceptionalPair left right)) (by
            unfold BinaryTermEquivalent BinaryCompletePrecedence
              BinaryExceptionalPair binaryPairMatches
            infer_instance))) = true := by
  decide

/-- Exhaustive classifier for Lee--Li Lemma 8.4(ii), over the filtered
binary words of length at most six.  Under cap three and contiguous cubes,
equal published-A binary term functions preserve complete precedence unless
the pair belongs to the explicit exceptional orbit. -/
theorem binaryTermClassifier
    {left right : List (Fin 2)}
    (leftReady : BinaryProjectionReady left)
    (rightReady : BinaryProjectionReady right)
    (equivalent : BinaryTermEquivalent left right) :
    (BinaryCompletePrecedence left ↔
        BinaryCompletePrecedence right) ∨
      BinaryExceptionalPair left right := by
  have leftMember : left ∈ binaryReadyWords :=
    mem_binaryReadyWords leftReady
  have rightMember : right ∈ binaryReadyWords :=
    mem_binaryReadyWords rightReady
  have leftChecked :=
    (List.all_eq_true.mp binaryTermClassifier_checked) left leftMember
  have checked :=
    (List.all_eq_true.mp leftChecked) right rightMember
  letI : Decidable
      (BinaryTermEquivalent left right →
        ((BinaryCompletePrecedence left ↔
            BinaryCompletePrecedence right) ∨
          BinaryExceptionalPair left right)) := by
    unfold BinaryTermEquivalent BinaryCompletePrecedence
      BinaryExceptionalPair binaryPairMatches
    infer_instance
  exact (of_decide_eq_true checked) equivalent
/- PROOF-SHAPE-FRAGMENT-END semantics_decided_classifier_and_typed_bridge -/

/-! ## Projection of arbitrary words -/

/-- Retain one ordered pair of variables and encode it by binary letters
zero and one. -/
def pairProjection
    (letters : List Nat) (x y : Nat) : List (Fin 2) :=
  letters.filterMap fun letter =>
    if letter = x then some 0
    else if letter = y then some 1
    else none

private def pairValuation
    (x y : Nat) (xValue yValue : Fin 6) :
    Nat → Fin 6 :=
  fun letter =>
    if letter = x then xValue
    else if letter = y then yValue
    else publishedIdentityElement

private def publishedListEval
    (valuation : Nat → Fin 6) (letters : List Nat) : Fin 6 :=
  letters.foldl
    (fun current letter =>
      publishedMul current (valuation letter))
    publishedIdentityElement

private theorem publishedListEval_toList
    (valuation : Nat → Fin 6) (word : Word Nat) :
    publishedListEval valuation word.toList =
      publishedTable.semigroup.eval valuation word := by
  cases word with
  | mk head tail =>
      unfold publishedListEval
      simp only [Word.toList, Semigroup.eval, List.foldl_cons]
      rw [publishedIdentityElement_certificate.1]
      rfl

private theorem pairProjection_evalFold
    (x y : Nat) (xValue yValue : Fin 6) :
    ∀ (letters : List Nat) (initial : Fin 6),
      letters.foldl
          (fun current letter =>
            publishedMul current
              (pairValuation x y xValue yValue letter))
          initial =
        (pairProjection letters x y).foldl
          (fun current bit =>
            publishedMul current
              (binaryValue xValue yValue bit))
          initial
  | [], _ => rfl
  | letter :: rest, initial => by
      simp only [List.foldl_cons]
      by_cases isX : letter = x
      · subst letter
        simpa [pairProjection, pairValuation, binaryValue] using
          pairProjection_evalFold x y xValue yValue rest
            (publishedMul initial xValue)
      · by_cases isY : letter = y
        · subst letter
          simpa [pairProjection, pairValuation, binaryValue, isX] using
            pairProjection_evalFold x y xValue yValue rest
              (publishedMul initial yValue)
        · have rightIdentity :
              publishedMul initial publishedIdentityElement = initial :=
            publishedIdentityElement_certificate.2 initial
          simpa [pairProjection, pairValuation, isX, isY,
            rightIdentity] using
              pairProjection_evalFold x y xValue yValue rest initial

private theorem publishedListEval_pairProjection
    (letters : List Nat) (x y : Nat)
    (xValue yValue : Fin 6) :
    publishedListEval (pairValuation x y xValue yValue) letters =
      binaryListEval xValue yValue (pairProjection letters x y) := by
  unfold publishedListEval binaryListEval
  exact pairProjection_evalFold x y xValue yValue letters
    publishedIdentityElement

/-- Validity in published monoid `A`, with every variable outside the
chosen pair sent to the identity element, gives equality of the complete
binary term functions. -/
theorem valid_pairProjectionTermEquivalent
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy publishedTable.semigroup)
    (x y : Nat) :
    BinaryTermEquivalent
      (pairProjection identity.lhs.toList x y)
      (pairProjection identity.rhs.toList x y) := by
  intro xValue yValue
  have evaluated :=
    valid (pairValuation x y xValue yValue)
  rw [← publishedListEval_toList, ← publishedListEval_toList] at evaluated
  rw [publishedListEval_pairProjection,
    publishedListEval_pairProjection] at evaluated
  exact evaluated

/-! ## Complete-precedence projection -/

private def pairPrecedenceStep
    (x y : Nat) (state : S5_841.PrecedenceState) (letter : Nat) :
    S5_841.PrecedenceState :=
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

private theorem precedenceScanList_eq_pairFold
    (letters : List Nat) (x y : Nat) :
    S5_841.precedenceScanList letters x y =
      letters.foldl (pairPrecedenceStep x y) .neither := by
  rfl

private theorem pairProjection_precedenceFold
    (x y : Nat) :
    ∀ (letters : List Nat) (state : S5_841.PrecedenceState),
      letters.foldl (pairPrecedenceStep x y) state =
        (pairProjection letters x y).foldl
          binaryPrecedenceStep state
  | [], _ => rfl
  | letter :: rest, state => by
      simp only [List.foldl_cons]
      by_cases isX : letter = x
      · subst letter
        simpa [pairProjection, pairPrecedenceStep,
          binaryPrecedenceStep] using
            pairProjection_precedenceFold x y rest
              (pairPrecedenceStep x y state x)
      · by_cases isY : letter = y
        · subst letter
          simpa [pairProjection, pairPrecedenceStep,
            binaryPrecedenceStep, isX] using
              pairProjection_precedenceFold x y rest
                (pairPrecedenceStep x y state y)
        · simpa [pairProjection, pairPrecedenceStep, isX, isY] using
            pairProjection_precedenceFold x y rest state

/-- Complete precedence depends only on the binary projection of the chosen
ordered pair. -/
theorem completePrecedenceList_iff_binaryProjection
    {letters : List Nat} {x y : Nat}
    (different : x ≠ y) :
    S5_841.CompletePrecedenceList letters x y ↔
      BinaryCompletePrecedence (pairProjection letters x y) := by
  unfold S5_841.CompletePrecedenceList BinaryCompletePrecedence
  rw [precedenceScanList_eq_pairFold,
    pairProjection_precedenceFold]
  simp [different]

/-! ## Canonicalization adapter boundary -/

/-- The cap-three/contiguous-cube part of Proposition 8 canonicalization,
stated only through every two-variable projection. -/
def CanonicalProjectionReady (letters : List Nat) : Prop :=
  ∀ x y, x ≠ y →
    BinaryProjectionReady (pairProjection letters x y)

/-- The one remaining bridge from canonical conditions V and VI: none of
the projected side pairs is one of the finite exceptional shapes. -/
def CanonicalExceptionsExcluded
    (left right : List Nat) : Prop :=
  ∀ x y, x ≠ y →
    ¬ BinaryExceptionalPair
      (pairProjection left x y)
      (pairProjection right x y)

end Semantics

/-- Semantic Lee--Li Lemma 8.4(ii), factored at the exact canonicalization
boundary.  `CanonicalProjectionReady` is the cap-three/contiguous-cube
adapter.  `CanonicalExceptionsExcluded` is precisely the V/VI adapter
that rules out the two exceptional binary families. -/
theorem validCanonicalCompletePrecedence
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy publishedTable.semigroup)
    (leftReady :
      Semantics.CanonicalProjectionReady identity.lhs.toList)
    (rightReady :
      Semantics.CanonicalProjectionReady identity.rhs.toList)
    (exceptionsExcluded :
      Semantics.CanonicalExceptionsExcluded
        identity.lhs.toList identity.rhs.toList) :
    ∀ x y,
      S5_841.CompletePrecedenceList identity.lhs.toList x y ↔
        S5_841.CompletePrecedenceList identity.rhs.toList x y := by
  intro x y
  by_cases different : x ≠ y
  · have termEquivalent :=
      Semantics.valid_pairProjectionTermEquivalent identity valid x y
    have classified :=
      Semantics.binaryTermClassifier
        (leftReady x y different)
        (rightReady x y different)
        termEquivalent
    rcases classified with preserved | exceptional
    · exact
        (Semantics.completePrecedenceList_iff_binaryProjection
          (letters := identity.lhs.toList) different).trans <|
          preserved.trans <|
            (Semantics.completePrecedenceList_iff_binaryProjection
              (letters := identity.rhs.toList) different).symm
    · exact False.elim
        ((exceptionsExcluded x y different) exceptional)
  · simp [S5_841.CompletePrecedenceList, different]

end SemigroupBasis.CoRoots.Order6LeeLiProposition8A
