import SemigroupBasis.FiniteReflection
import SemigroupBasis.Nonfinite.GraphParity
import SemigroupBasis.Nonfinite.AC2.CycleObstruction
import SemigroupBasis.Examples.CyclicTwo
import SemigroupBasis.Transfer

namespace SemigroupBasis.Examples.AC2

open SemigroupBasis

/-!
The six elements are in the source order `0, a, ab, b, ba, c`.
The resulting table is the published `A_2^g = AC2` table and is isomorphic
to the zero-based Smallsemi catalogue representative `S6_8878`.
-/

def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then
    if right = 5 then 5 else 0
  else if left = 1 then
    if right = 3 then 1
    else if right = 4 then 2
    else if right = 5 then 5
    else 0
  else if left = 2 then
    if right = 0 then 0
    else if right = 1 then 1
    else if right = 2 then 2
    else if right = 3 then 1
    else if right = 4 then 2
    else 5
  else if left = 3 then
    if right = 3 then 3
    else if right = 4 then 4
    else if right = 5 then 5
    else 0
  else if left = 4 then
    if right = 0 then 0
    else if right = 1 then 3
    else if right = 2 then 4
    else if right = 3 then 3
    else if right = 4 then 4
    else 5
  else
    if right = 5 then 0 else 5

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

@[simp]
private theorem table_semigroup_mul (left right : Fin 6) :
    table.semigroup.mul left right = mul left right :=
  rfl

theorem table_rows :
    List.ofFn (fun left : Fin 6 =>
      List.ofFn (fun right : Fin 6 => (table.mul left right).val)) =
      [[0, 0, 0, 0, 0, 5],
       [0, 0, 0, 1, 2, 5],
       [0, 1, 2, 1, 2, 5],
       [0, 0, 0, 3, 4, 5],
       [0, 3, 4, 3, 4, 5],
       [5, 5, 5, 5, 5, 0]] := by
  decide

/-!
The Lee--Zhang/Smallsemi catalogue order for `S6_8878` differs from the
published AC2 order by the zero-based permutation

`0 ↦ 0, 1 ↦ 1, 2 ↦ 3, 3 ↦ 4, 4 ↦ 5, 5 ↦ 2`.
-/

private def publishedToCatalogue (value : Fin 6) : Fin 6 :=
  if value = 0 then 0
  else if value = 1 then 1
  else if value = 2 then 3
  else if value = 3 then 4
  else if value = 4 then 5
  else 2

private def catalogueToPublished (value : Fin 6) : Fin 6 :=
  if value = 0 then 0
  else if value = 1 then 1
  else if value = 2 then 5
  else if value = 3 then 2
  else if value = 4 then 3
  else 4

private theorem catalogueToPublished_publishedToCatalogue
    (value : Fin 6) :
    catalogueToPublished (publishedToCatalogue value) = value := by
  decide +revert

private theorem publishedToCatalogue_catalogueToPublished
    (value : Fin 6) :
    publishedToCatalogue (catalogueToPublished value) = value := by
  decide +revert

def catalogueMul (left right : Fin 6) : Fin 6 :=
  publishedToCatalogue
    (mul (catalogueToPublished left) (catalogueToPublished right))

def catalogueTable : FiniteTable where
  order := 6
  mul := catalogueMul
  assoc := by decide

theorem catalogueTable_rows :
    List.ofFn (fun left : Fin 6 =>
      List.ofFn (fun right : Fin 6 =>
        (catalogueTable.mul left right).val)) =
      [[0, 0, 2, 0, 0, 0],
       [0, 0, 2, 0, 1, 3],
       [2, 2, 0, 2, 2, 2],
       [0, 1, 2, 3, 1, 3],
       [0, 0, 2, 0, 4, 5],
       [0, 4, 2, 5, 4, 5]] := by
  decide

def publishedToCatalogueEmbedding :
    Embedding table.semigroup catalogueTable.semigroup where
  toFun := publishedToCatalogue
  map_mul := by decide +revert
  injective := by
    intro left right equality
    have inverseEquality :=
      congrArg catalogueToPublished equality
    simpa only [catalogueToPublished_publishedToCatalogue] using
      inverseEquality

def catalogueToPublishedEmbedding :
    Embedding catalogueTable.semigroup table.semigroup where
  toFun := catalogueToPublished
  map_mul := by decide +revert
  injective := by
    intro left right equality
    have inverseEquality :=
      congrArg publishedToCatalogue equality
    simpa only [publishedToCatalogue_catalogueToPublished] using
      inverseEquality

theorem sameIdentityTheory_catalogue :
    SameIdentityTheory table.semigroup catalogueTable.semigroup := by
  intro identity
  constructor
  · exact catalogueToPublishedEmbedding.pullback_identity identity
  · exact publishedToCatalogueEmbedding.pullback_identity identity

private def supportSeparator (tested : Nat) : Nat → Fin 6 :=
  fun letter => if letter = tested then 0 else 4

private theorem fold_supportSeparator
    (tested : Nat) (letters : List Nat) (present : Bool) :
    letters.foldl
        (fun current letter => mul current (supportSeparator tested letter))
        (if present then 0 else 4) =
      if present || letters.contains tested then 0 else 4 := by
  induction letters generalizing present with
  | nil => simp
  | cons letter rest ih =>
      simp only [List.foldl_cons, List.contains_cons]
      cases present with
      | false =>
          by_cases hit : letter = tested
          · subst letter
            simpa [supportSeparator, mul] using ih true
          · have reverse : tested ≠ letter := Ne.symm hit
            simpa [supportSeparator, hit, reverse, mul] using ih false
      | true =>
          change
            rest.foldl
                (fun current next =>
                  mul current (supportSeparator tested next))
                (mul 0 (supportSeparator tested letter)) = 0
          have valueNotFive :
              supportSeparator tested letter ≠ (5 : Fin 6) := by
            by_cases hit : letter = tested <;>
              simp [supportSeparator, hit]
          rw [show mul 0 (supportSeparator tested letter) = (0 : Fin 6) by
            simp [mul, valueNotFive]]
          simpa using ih true

private theorem eval_supportSeparator
    (tested : Nat) (word : Word Nat) :
    table.semigroup.eval (supportSeparator tested) word =
      if tested ∈ word.toList then (0 : Fin 6) else 4 := by
  cases word with
  | mk head tail =>
      simp only [Semigroup.eval, table_semigroup_mul, Word.toList]
      by_cases hit : head = tested
      · subst head
        rw [show supportSeparator tested tested = (0 : Fin 6) by
          simp [supportSeparator]]
        simpa using fold_supportSeparator tested tail true
      · have reverse : tested ≠ head := Ne.symm hit
        rw [show supportSeparator tested head = (4 : Fin 6) by
          simp [supportSeparator, hit]]
        simpa [hit, reverse] using
          fold_supportSeparator tested tail false

private def initialSeparator (tested : Nat) : Nat → Fin 6 :=
  fun letter => if letter = tested then 2 else 4

private theorem initialSeparator_right
    (tested letter : Nat) (current : Fin 6)
    (currentShape : current = 2 ∨ current = 4) :
    mul current (initialSeparator tested letter) = current := by
  rcases currentShape with rfl | rfl <;>
    simp [initialSeparator, mul] <;>
    split <;> rfl

private theorem eval_initialSeparator
    (tested : Nat) (word : Word Nat) :
    table.semigroup.eval (initialSeparator tested) word =
      initialSeparator tested word.head := by
  cases word with
  | mk head tail =>
      simp only [Semigroup.eval, table_semigroup_mul]
      induction tail generalizing head with
      | nil => rfl
      | cons next rest ih =>
          simp only [List.foldl_cons]
          have shape :
              initialSeparator tested head = 2 ∨
                initialSeparator tested head = 4 := by
            by_cases hit : head = tested
            · left
              simp [initialSeparator, hit]
            · right
              simp [initialSeparator, hit]
          rw [initialSeparator_right tested next
            (initialSeparator tested head) shape]
          exact ih head

private def finalSeparator (tested : Nat) : Nat → Fin 6 :=
  fun letter => if letter = tested then 3 else 4

private theorem finalSeparator_left
    (tested previous next : Nat) :
    mul (finalSeparator tested previous) (finalSeparator tested next) =
      finalSeparator tested next := by
  by_cases previousHit : previous = tested <;>
    by_cases nextHit : next = tested <;>
    simp [finalSeparator, previousHit, nextHit, mul]

private theorem fold_finalSeparator
    (tested : Nat) (letters : List Nat) (previous : Nat) :
    letters.foldl
        (fun current letter => mul current (finalSeparator tested letter))
        (finalSeparator tested previous) =
      finalSeparator tested (letters.getLastD previous) := by
  induction letters generalizing previous with
  | nil => rfl
  | cons next rest ih =>
      simp only [List.foldl_cons, List.getLastD_cons]
      rw [finalSeparator_left]
      exact ih next

private theorem eval_finalSeparator
    (tested : Nat) (word : Word Nat) :
    table.semigroup.eval (finalSeparator tested) word =
      finalSeparator tested word.final := by
  cases word with
  | mk head tail =>
      exact fold_finalSeparator tested tail head

private def edgeValue (source target letter : Nat) : Fin 6 :=
  if letter = target then
    if letter = source then 1 else 2
  else if letter = source then 3 else 4

private def edgePrefixValue
    (source target first previous : Nat) : Fin 6 :=
  if first = target then
    if previous = source then 1 else 2
  else if previous = source then 3 else 4

private theorem edgeValue_eq_prefix
    (source target letter : Nat) :
    edgeValue source target letter =
      edgePrefixValue source target letter letter := by
  simp [edgeValue, edgePrefixValue]

private theorem edgePrefix_mul
    (source target first previous next : Nat) :
    mul (edgePrefixValue source target first previous)
        (edgeValue source target next) =
      if previous = source ∧ next = target then 0
      else edgePrefixValue source target first next := by
  by_cases firstTarget : first = target <;>
    by_cases sourceTarget : source = target <;>
    by_cases previousSource : previous = source <;>
    by_cases nextTarget : next = target <;>
    by_cases nextSource : next = source <;>
    simp_all [edgePrefixValue, edgeValue, mul]

private theorem fold_zero_edgeValue
    (source target : Nat) (letters : List Nat) :
    letters.foldl
        (fun current letter => mul current (edgeValue source target letter))
        0 = 0 := by
  induction letters with
  | nil => rfl
  | cons letter rest ih =>
      simp only [List.foldl_cons]
      have valueNotFive :
          edgeValue source target letter ≠ (5 : Fin 6) := by
        simp only [edgeValue]
        split <;> split <;> decide
      rw [show mul 0 (edgeValue source target letter) = (0 : Fin 6) by
        simp [mul, valueNotFive]]
      exact ih

private theorem fold_edgePrefix_zero_iff
    (source target first previous : Nat) (letters : List Nat) :
    letters.foldl
        (fun current letter => mul current (edgeValue source target letter))
        (edgePrefixValue source target first previous) = 0 ↔
      (source, target) ∈ Word.adjacentPairsFrom previous letters := by
  induction letters generalizing previous with
  | nil =>
      by_cases firstTarget : first = target <;>
        by_cases previousSource : previous = source <;>
        simp [Word.adjacentPairsFrom, edgePrefixValue, firstTarget,
          previousSource]
  | cons next rest ih =>
      simp only [List.foldl_cons, Word.adjacentPairsFrom, List.mem_cons]
      rw [edgePrefix_mul]
      by_cases bad : previous = source ∧ next = target
      · rw [if_pos bad, fold_zero_edgeValue]
        simp [bad]
      · rw [if_neg bad, ih]
        simp only [Prod.mk.injEq]
        constructor
        · exact Or.inr
        · intro occurrence
          rcases occurrence with firstEdge | laterEdge
          · exact False.elim <| bad
              ⟨firstEdge.1.symm, firstEdge.2.symm⟩
          · exact laterEdge

private theorem eval_edgeSeparator_zero_iff
    (source target : Nat) (word : Word Nat) :
    table.semigroup.eval (edgeValue source target) word = (0 : Fin 6) ↔
      (source, target) ∈ word.adjacentPairs := by
  cases word with
  | mk head tail =>
      simp only [Semigroup.eval, table_semigroup_mul, Word.adjacentPairs]
      rw [edgeValue_eq_prefix]
      exact fold_edgePrefix_zero_iff source target head head tail

private def paritySeparator (tested : Nat) : Nat → Fin 6 :=
  fun letter => if letter = tested then 5 else 0

private def parityValue (count : Nat) : Fin 6 :=
  if count % 2 = 0 then 0 else 5

private theorem parityValue_mul_hit (count : Nat) :
    mul (parityValue count) 5 = parityValue (count + 1) := by
  by_cases even : count % 2 = 0
  · have next : (count + 1) % 2 = 1 := by omega
    simp [parityValue, even, next, mul]
  · have odd : count % 2 = 1 := by omega
    have next : (count + 1) % 2 = 0 := by omega
    simp [parityValue, odd, next, mul]

private theorem parityValue_mul_miss (count : Nat) :
    mul (parityValue count) 0 = parityValue count := by
  by_cases even : count % 2 = 0 <;>
    simp [parityValue, even, mul]

private theorem fold_parityValue
    (tested : Nat) (letters : List Nat) (initial : Nat) :
    letters.foldl
        (fun current letter =>
          mul current (paritySeparator tested letter))
        (parityValue initial) =
      parityValue (initial + letters.count tested) := by
  induction letters generalizing initial with
  | nil => simp
  | cons letter rest ih =>
      simp only [List.foldl_cons]
      by_cases hit : letter = tested
      · subst letter
        rw [show paritySeparator tested tested = (5 : Fin 6) by
          simp [paritySeparator]]
        rw [parityValue_mul_hit, ih, List.count_cons_self]
        congr 1
        omega
      · rw [show paritySeparator tested letter = (0 : Fin 6) by
          simp [paritySeparator, hit]]
        rw [parityValue_mul_miss, ih, List.count_cons_of_ne hit]

private theorem eval_paritySeparator
    (tested : Nat) (word : Word Nat) :
    table.semigroup.eval (paritySeparator tested) word =
      parityValue (word.toList.count tested) := by
  cases word with
  | mk head tail =>
      simp only [Semigroup.eval, table_semigroup_mul, Word.toList]
      by_cases hit : head = tested
      · subst head
        simpa [paritySeparator, parityValue, Nat.add_comm] using
          fold_parityValue tested tail 1
      · simpa [paritySeparator, parityValue, hit] using
          fold_parityValue tested tail 0

private theorem parityValue_injective_mod_two
    {left right : Nat}
    (equality : parityValue left = parityValue right) :
    left % 2 = right % 2 := by
  have leftCases : left % 2 = 0 ∨ left % 2 = 1 := by omega
  have rightCases : right % 2 = 0 ∨ right % 2 = 1 := by omega
  rcases leftCases with leftEven | leftOdd
  · rcases rightCases with rightEven | rightOdd
    · exact leftEven.trans rightEven.symm
    · simp [parityValue, leftEven, rightOdd] at equality
  · rcases rightCases with rightEven | rightOdd
    · simp [parityValue, leftOdd, rightEven] at equality
    · exact leftOdd.trans rightOdd.symm

/-- Every AC2 identity has the same variable support on both sides. -/
theorem valid_identity_sameSupport
    {identity : Identity Nat}
    (valid : identity.SatisfiedBy table.semigroup) :
    ∀ letter,
      letter ∈ identity.lhs.toList ↔
        letter ∈ identity.rhs.toList := by
  intro letter
  have evaluated := valid (supportSeparator letter)
  rw [eval_supportSeparator, eval_supportSeparator] at evaluated
  by_cases leftMem : letter ∈ identity.lhs.toList <;>
    by_cases rightMem : letter ∈ identity.rhs.toList <;>
    simp [leftMem, rightMem] at evaluated ⊢

/-- Every AC2 identity has the same marked initial vertex. -/
theorem valid_identity_sameInitial
    {identity : Identity Nat}
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.lhs.head = identity.rhs.head := by
  let tested := identity.lhs.head
  have evaluated := valid (initialSeparator tested)
  rw [eval_initialSeparator, eval_initialSeparator] at evaluated
  have leftValue :
      initialSeparator tested identity.lhs.head = (2 : Fin 6) := by
    simp [tested, initialSeparator]
  rw [leftValue] at evaluated
  by_cases same : identity.lhs.head = identity.rhs.head
  · exact same
  · have rightValue :
        initialSeparator tested identity.rhs.head = (4 : Fin 6) := by
      simp [tested, initialSeparator, Ne.symm same]
    rw [rightValue] at evaluated
    exact False.elim ((by decide : (2 : Fin 6) ≠ 4) evaluated)

/-- Every AC2 identity has the same marked final vertex. -/
theorem valid_identity_sameFinal
    {identity : Identity Nat}
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.lhs.final = identity.rhs.final := by
  let tested := identity.lhs.final
  have evaluated := valid (finalSeparator tested)
  rw [eval_finalSeparator, eval_finalSeparator] at evaluated
  have leftValue :
      finalSeparator tested identity.lhs.final = (3 : Fin 6) := by
    simp [tested, finalSeparator]
  rw [leftValue] at evaluated
  by_cases same : identity.lhs.final = identity.rhs.final
  · exact same
  · have rightValue :
        finalSeparator tested identity.rhs.final = (4 : Fin 6) := by
      simp [tested, finalSeparator, Ne.symm same]
    rw [rightValue] at evaluated
    exact False.elim ((by decide : (3 : Fin 6) ≠ 4) evaluated)

/-- Every AC2 identity has the same directed adjacency relation. -/
theorem valid_identity_sameEdges
    {identity : Identity Nat}
    (valid : identity.SatisfiedBy table.semigroup) :
    ∀ source target,
      (source, target) ∈ identity.lhs.adjacentPairs ↔
        (source, target) ∈ identity.rhs.adjacentPairs := by
  intro source target
  have evaluated := valid (edgeValue source target)
  have zeroIff :
      table.semigroup.eval (edgeValue source target) identity.lhs =
          (0 : Fin 6) ↔
        table.semigroup.eval (edgeValue source target) identity.rhs =
          (0 : Fin 6) := by
    rw [evaluated]
  simpa only [eval_edgeSeparator_zero_iff] using zeroIff

/-- Necessity half of the source's directed-graph characterization. -/
theorem valid_identity_sameMarkedDigraph
    {identity : Identity Nat}
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.lhs.SameMarkedDigraph identity.rhs :=
  ⟨valid_identity_sameInitial valid,
    valid_identity_sameFinal valid,
    valid_identity_sameSupport valid,
    valid_identity_sameEdges valid⟩

/-- Necessity half of the source's parity characterization. -/
theorem valid_identity_sameParity
    {identity : Identity Nat}
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.lhs.SameParity identity.rhs := by
  intro letter
  have evaluated := valid (paritySeparator letter)
  rw [eval_paritySeparator, eval_paritySeparator] at evaluated
  exact parityValue_injective_mod_two evaluated

theorem valid_identity_graphParity
    {identity : Identity Nat}
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.GraphParityEquivalent :=
  ⟨valid_identity_sameMarkedDigraph valid,
    valid_identity_sameParity valid⟩

/-- The five-element `A₂` subsemigroup in the same element order as the first
five rows and columns of `table`. -/
def a2Mul (left right : Fin 5) : Fin 5 :=
  if left = 0 then 0
  else if left = 1 then
    if right = 3 then 1
    else if right = 4 then 2
    else 0
  else if left = 2 then
    if right = 0 then 0
    else if right = 1 then 1
    else if right = 2 then 2
    else if right = 3 then 1
    else 2
  else if left = 3 then
    if right = 3 then 3
    else if right = 4 then 4
    else 0
  else
    if right = 0 then 0
    else if right = 1 then 3
    else if right = 2 then 4
    else if right = 3 then 3
    else 4

def a2Table : FiniteTable where
  order := 5
  mul := a2Mul
  assoc := by decide

/-!
The four nonzero elements of `A₂` are Rees coordinates `(i, λ)` over the
two-point index sets.  In the chosen table order they are

`1 = (0,0)`, `2 = (0,1)`, `3 = (1,0)`, `4 = (1,1)`.

The only zero sandwich entry is `(λ, j) = (0,0)`.  Consequently a nonzero
word value is determined by the first coordinate of its initial letter and
the second coordinate of its final letter; it becomes zero exactly when a
zero-valued variable occurs or a directed edge crosses the zero sandwich
entry.  This gives a direct table-level proof of Trahtman's marked-digraph
criterion.
-/

private def a2FirstCoordinate (value : Fin 5) : Fin 2 :=
  if value = 1 ∨ value = 2 then 0 else 1

private def a2FinalCoordinate (value : Fin 5) : Fin 2 :=
  if value = 1 ∨ value = 3 then 0 else 1

private def a2CoordinateValue (first final : Fin 2) : Fin 5 :=
  if first = 0 then
    if final = 0 then 1 else 2
  else
    if final = 0 then 3 else 4

private theorem a2CoordinateValue_eq
    (value : Fin 5) (nonzero : value ≠ 0) :
    a2CoordinateValue (a2FirstCoordinate value)
        (a2FinalCoordinate value) = value := by
  decide +revert

private theorem a2Mul_coordinate_good
    (initial : Fin 2) (previous right : Fin 5)
    (rightNonzero : right ≠ 0)
    (good :
      ¬(a2FinalCoordinate previous = 0 ∧
        a2FirstCoordinate right = 0)) :
    a2Mul
        (a2CoordinateValue initial (a2FinalCoordinate previous))
        right =
      a2CoordinateValue initial (a2FinalCoordinate right) := by
  decide +revert

private theorem a2Mul_coordinate_bad
    (initial : Fin 2) (previous right : Fin 5)
    (bad :
      a2FinalCoordinate previous = 0 ∧
        a2FirstCoordinate right = 0) :
    a2Mul
        (a2CoordinateValue initial (a2FinalCoordinate previous))
        right = 0 := by
  decide +revert

private theorem a2Mul_zero_left (right : Fin 5) :
    a2Mul 0 right = 0 := by
  decide +revert

private theorem a2Mul_zero_right (left : Fin 5) :
    a2Mul left 0 = 0 := by
  decide +revert

private def A2Forbidden
    (valuation : Nat → Fin 5) (source target : Nat) : Prop :=
  a2FinalCoordinate (valuation source) = 0 ∧
    a2FirstCoordinate (valuation target) = 0

private def A2SupportZero
    (valuation : Nat → Fin 5) (word : Word Nat) : Prop :=
  ∃ letter, letter ∈ word.toList ∧ valuation letter = 0

private def A2ForbiddenEdge
    (valuation : Nat → Fin 5) (word : Word Nat) : Prop :=
  ∃ source target,
    (source, target) ∈ word.adjacentPairs ∧
      A2Forbidden valuation source target

private theorem a2Fold_zero
    (valuation : Nat → Fin 5) (letters : List Nat) :
    letters.foldl
        (fun current letter => a2Mul current (valuation letter)) 0 = 0 := by
  induction letters with
  | nil => rfl
  | cons letter rest ih =>
      simp only [List.foldl_cons, a2Mul_zero_left]
      exact ih

private theorem a2Fold_zero_of_member
    (valuation : Nat → Fin 5) (letters : List Nat) (initial : Fin 5)
    (zeroMember : ∃ letter, letter ∈ letters ∧ valuation letter = 0) :
    letters.foldl
        (fun current letter => a2Mul current (valuation letter)) initial = 0 := by
  induction letters generalizing initial with
  | nil =>
      rcases zeroMember with ⟨letter, member, _⟩
      simp at member
  | cons next rest ih =>
      rcases zeroMember with ⟨letter, member, zeroValue⟩
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · simp only [List.foldl_cons, zeroValue, a2Mul_zero_right]
        exact a2Fold_zero valuation rest
      · simp only [List.foldl_cons]
        exact ih (a2Mul initial (valuation next))
          ⟨letter, member, zeroValue⟩

private theorem a2Eval_zero_of_support
    (valuation : Nat → Fin 5) (word : Word Nat)
    (zeroSupport : A2SupportZero valuation word) :
    a2Table.semigroup.eval valuation word = (0 : Fin 5) := by
  cases word with
  | mk head tail =>
      rcases zeroSupport with ⟨letter, member, zeroValue⟩
      simp only [Word.toList, List.mem_cons] at member
      rcases member with rfl | member
      · simp only [Semigroup.eval, zeroValue]
        exact a2Fold_zero valuation tail
      · exact a2Fold_zero_of_member valuation tail (valuation head)
          ⟨letter, member, zeroValue⟩

private theorem a2Fold_good
    (valuation : Nat → Fin 5) (initial : Fin 2)
    (previous : Nat) (letters : List Nat)
    (lettersNonzero :
      ∀ letter, letter ∈ letters → valuation letter ≠ 0)
    (edgesGood :
      ∀ source target,
        (source, target) ∈ Word.adjacentPairsFrom previous letters →
          ¬A2Forbidden valuation source target) :
    letters.foldl
        (fun current letter => a2Mul current (valuation letter))
        (a2CoordinateValue initial
          (a2FinalCoordinate (valuation previous))) =
      a2CoordinateValue initial
        (a2FinalCoordinate (valuation (letters.getLastD previous))) := by
  induction letters generalizing previous with
  | nil => rfl
  | cons next rest ih =>
      simp only [List.foldl_cons, List.getLastD_cons]
      rw [a2Mul_coordinate_good initial (valuation previous)
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

private theorem a2Eval_good
    (valuation : Nat → Fin 5) (word : Word Nat)
    (supportGood : ¬A2SupportZero valuation word)
    (edgesGood : ¬A2ForbiddenEdge valuation word) :
    a2Table.semigroup.eval valuation word =
      a2CoordinateValue (a2FirstCoordinate (valuation word.head))
        (a2FinalCoordinate (valuation word.final)) := by
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
              ¬A2Forbidden valuation source target := by
        intro source target member bad
        exact edgesGood
          ⟨source, target, by
            simpa [Word.adjacentPairs] using member, bad⟩
      change
        tail.foldl
            (fun current letter => a2Mul current (valuation letter))
            (valuation head) =
          a2CoordinateValue (a2FirstCoordinate (valuation head))
            (a2FinalCoordinate (valuation (tail.getLastD head)))
      calc
        _ =
            tail.foldl
              (fun current letter => a2Mul current (valuation letter))
              (a2CoordinateValue (a2FirstCoordinate (valuation head))
                (a2FinalCoordinate (valuation head))) := by
              congr 1
              exact (a2CoordinateValue_eq
                (valuation head) headNonzero).symm
        _ = _ :=
          a2Fold_good valuation (a2FirstCoordinate (valuation head))
            head tail tailNonzero allEdgesGood

private theorem a2Fold_zero_of_forbidden
    (valuation : Nat → Fin 5) (initial : Fin 2)
    (previous : Nat) (letters : List Nat)
    (lettersNonzero :
      ∀ letter, letter ∈ letters → valuation letter ≠ 0)
    (forbidden :
      ∃ source target,
        (source, target) ∈ Word.adjacentPairsFrom previous letters ∧
          A2Forbidden valuation source target) :
    letters.foldl
        (fun current letter => a2Mul current (valuation letter))
        (a2CoordinateValue initial
          (a2FinalCoordinate (valuation previous))) = 0 := by
  induction letters generalizing previous with
  | nil =>
      rcases forbidden with ⟨source, target, member, _⟩
      simp [Word.adjacentPairsFrom] at member
  | cons next rest ih =>
      simp only [List.foldl_cons]
      by_cases firstBad : A2Forbidden valuation previous next
      · rw [a2Mul_coordinate_bad initial (valuation previous)
          (valuation next) firstBad]
        exact a2Fold_zero valuation rest
      · rw [a2Mul_coordinate_good initial (valuation previous)
          (valuation next)
          (lettersNonzero next (by simp)) firstBad]
        apply ih
        · intro letter member
          exact lettersNonzero letter (by simp [member])
        · rcases forbidden with ⟨source, target, member, bad⟩
          simp only [Word.adjacentPairsFrom, List.mem_cons] at member
          rcases member with first | later
          · have sourceEq : source = previous := congrArg Prod.fst first
            have targetEq : target = next := congrArg Prod.snd first
            subst source
            subst target
            exact False.elim (firstBad bad)
          · exact ⟨source, target, later, bad⟩

private theorem a2Eval_zero_of_forbidden
    (valuation : Nat → Fin 5) (word : Word Nat)
    (supportGood : ¬A2SupportZero valuation word)
    (forbidden : A2ForbiddenEdge valuation word) :
    a2Table.semigroup.eval valuation word = (0 : Fin 5) := by
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
      rw [← a2CoordinateValue_eq (valuation head) headNonzero]
      exact a2Fold_zero_of_forbidden valuation
        (a2FirstCoordinate (valuation head)) head tail tailNonzero
        ⟨source, target, by
          simpa [Word.adjacentPairs] using member, bad⟩

private theorem a2SupportZero_iff_of_sameMarkedDigraph
    (valuation : Nat → Fin 5) {left right : Word Nat}
    (same : left.SameMarkedDigraph right) :
    A2SupportZero valuation left ↔ A2SupportZero valuation right := by
  constructor
  · rintro ⟨letter, member, zeroValue⟩
    exact ⟨letter, (same.support letter).mp member, zeroValue⟩
  · rintro ⟨letter, member, zeroValue⟩
    exact ⟨letter, (same.support letter).mpr member, zeroValue⟩

private theorem a2ForbiddenEdge_iff_of_sameMarkedDigraph
    (valuation : Nat → Fin 5) {left right : Word Nat}
    (same : left.SameMarkedDigraph right) :
    A2ForbiddenEdge valuation left ↔ A2ForbiddenEdge valuation right := by
  constructor
  · rintro ⟨source, target, member, bad⟩
    exact ⟨source, target, (same.edge source target).mp member, bad⟩
  · rintro ⟨source, target, member, bad⟩
    exact ⟨source, target, (same.edge source target).mpr member, bad⟩

/-- Table-level sufficiency half of Trahtman's graph theorem for `A₂`. -/
theorem a2_valid_of_sameMarkedDigraph
    {identity : Identity Nat}
    (same : identity.lhs.SameMarkedDigraph identity.rhs) :
    identity.SatisfiedBy a2Table.semigroup := by
  intro valuation
  have supportIff :=
    a2SupportZero_iff_of_sameMarkedDigraph valuation same
  have edgeIff :=
    a2ForbiddenEdge_iff_of_sameMarkedDigraph valuation same
  by_cases leftSupportZero : A2SupportZero valuation identity.lhs
  · rw [a2Eval_zero_of_support valuation identity.lhs leftSupportZero]
    rw [a2Eval_zero_of_support valuation identity.rhs
      (supportIff.mp leftSupportZero)]
  · have rightSupportGood : ¬A2SupportZero valuation identity.rhs :=
      fun bad => leftSupportZero (supportIff.mpr bad)
    by_cases leftForbidden : A2ForbiddenEdge valuation identity.lhs
    · rw [a2Eval_zero_of_forbidden valuation identity.lhs
        leftSupportZero leftForbidden]
      rw [a2Eval_zero_of_forbidden valuation identity.rhs
        rightSupportGood (edgeIff.mp leftForbidden)]
    · have rightEdgesGood : ¬A2ForbiddenEdge valuation identity.rhs :=
        fun bad => leftForbidden (edgeIff.mpr bad)
      rw [a2Eval_good valuation identity.lhs leftSupportZero leftForbidden]
      rw [a2Eval_good valuation identity.rhs rightSupportGood rightEdgesGood]
      rw [same.initial, same.final]

def productSemigroup (G : Semigroup S) (H : Semigroup T) :
    Semigroup (S × T) where
  mul left right :=
    (G.mul left.1 right.1, H.mul left.2 right.2)
  assoc := by
    intro a b c
    apply Prod.ext
    · exact G.assoc a.1 b.1 c.1
    · exact H.assoc a.2 b.2 c.2

private theorem product_fold
    (G : Semigroup S) (H : Semigroup T)
    (valuation : α → S × T) (letters : List α) (initial : S × T) :
    letters.foldl
        (fun current x => (productSemigroup G H).mul current (valuation x))
        initial =
      (letters.foldl
          (fun current x => G.mul current (valuation x).1) initial.1,
        letters.foldl
          (fun current x => H.mul current (valuation x).2) initial.2) := by
  induction letters generalizing initial with
  | nil => rfl
  | cons next rest ih =>
      simp only [List.foldl_cons]
      exact ih _

private theorem product_eval
    (G : Semigroup S) (H : Semigroup T)
    (valuation : α → S × T) (word : Word α) :
    (productSemigroup G H).eval valuation word =
      (G.eval (fun x => (valuation x).1) word,
        H.eval (fun x => (valuation x).2) word) := by
  cases word with
  | mk head tail =>
      exact product_fold G H valuation tail (valuation head)

private theorem satisfiedBy_product_iff
    (identity : Identity α) :
    identity.SatisfiedBy
        (productSemigroup a2Table.semigroup cyclicTwo.semigroup) ↔
      identity.SatisfiedBy a2Table.semigroup ∧
        identity.SatisfiedBy cyclicTwo.semigroup := by
  constructor
  · intro valid
    constructor
    · intro valuation
      have evaluated :=
        valid (fun x => (valuation x, (0 : Fin 2)))
      rw [product_eval, product_eval] at evaluated
      exact congrArg Prod.fst evaluated
    · intro valuation
      have evaluated :=
        valid (fun x => ((0 : Fin 5), valuation x))
      rw [product_eval, product_eval] at evaluated
      exact congrArg Prod.snd evaluated
  · rintro ⟨validA2, validC2⟩ valuation
    rw [product_eval, product_eval]
    exact Prod.ext
      (validA2 fun x => (valuation x).1)
      (validC2 fun x => (valuation x).2)

private def includeA2 : Fin 5 → Fin 6 :=
  fun x => ⟨x.val, Nat.lt_trans x.isLt (by decide)⟩

private def includeC2 : Fin 2 → Fin 6 :=
  fun x => if x = 0 then 0 else 5

private def projectA2 : Fin 6 → Fin 5 :=
  fun x =>
    if bound : x.val < 5 then ⟨x.val, bound⟩ else 0

private def projectC2 : Fin 6 → Fin 2 :=
  fun x => if x = 5 then 1 else 0

def a2Embedding : Embedding a2Table.semigroup table.semigroup where
  toFun := includeA2
  map_mul := by decide +revert
  injective := by
    intro left right equality
    apply Fin.ext
    exact Fin.mk.inj equality

def c2Embedding : Embedding cyclicTwo.semigroup table.semigroup where
  toFun := includeC2
  map_mul := by decide +revert
  injective := by
    change Function.Injective includeC2
    intro left right equality
    by_cases leftZero : left = 0
    · subst left
      by_cases rightZero : right = 0
      · exact rightZero.symm
      · simp [includeC2, rightZero] at equality
    · by_cases rightZero : right = 0
      · subst right
        simp [includeC2, leftZero] at equality
      · apply Fin.ext
        omega

def productEmbedding :
    Embedding table.semigroup
      (productSemigroup a2Table.semigroup cyclicTwo.semigroup) where
  toFun := fun x => (projectA2 x, projectC2 x)
  map_mul := by decide +revert
  injective := by
    change Function.Injective
      (fun x : Fin 6 => (projectA2 x, projectC2 x))
    intro left right equality
    by_cases leftC : left = 5
    · subst left
      by_cases rightC : right = 5
      · exact rightC.symm
      · have secondValues := congrArg (fun pair => pair.2) equality
        simp [projectC2, rightC] at secondValues
    · by_cases rightC : right = 5
      · subst right
        have secondValues := congrArg (fun pair => pair.2) equality
        simp [projectC2, leftC] at secondValues
      · have leftValueNe : left.val ≠ 5 := by
          intro value
          exact leftC (Fin.ext value)
        have rightValueNe : right.val ≠ 5 := by
          intro value
          exact rightC (Fin.ext value)
        have leftBound : left.val < 5 := by omega
        have rightBound : right.val < 5 := by omega
        have firstValues := congrArg (fun pair => pair.1) equality
        simp [projectA2, leftBound, rightBound] at firstValues
        exact Fin.ext firstValues

/-- The primary source's variety sandwich, checked directly from the three
finite multiplication tables. AC2 and `A₂ × C₂` satisfy exactly the same
identities. -/
theorem sameIdentityTheory_product :
    SameIdentityTheory table.semigroup
      (productSemigroup a2Table.semigroup cyclicTwo.semigroup) := by
  intro identity
  constructor
  · intro valid
    apply (satisfiedBy_product_iff identity).mpr
    exact
      ⟨a2Embedding.pullback_identity identity valid,
        c2Embedding.pullback_identity identity valid⟩
  · intro valid
    exact productEmbedding.pullback_identity identity valid

/-- Marked-digraph equality implies validity in the concrete `A₂` table. -/
def PublishedA2GraphSufficiency : Prop :=
  ∀ identity : Identity Nat,
    identity.lhs.SameMarkedDigraph identity.rhs →
      identity.SatisfiedBy a2Table.semigroup

/-- The formerly external Trahtman boundary is now discharged directly from
the five-element multiplication table. -/
theorem a2GraphSufficiency : PublishedA2GraphSufficiency :=
  fun _ same => a2_valid_of_sameMarkedDigraph same

private theorem cyclicTwo_valid_of_sameParity
    {identity : Identity Nat}
    (same : identity.lhs.SameParity identity.rhs) :
    identity.SatisfiedBy cyclicTwo.semigroup := by
  apply Derives.sound cyclicTwoBasis_models
  have reducedPerm :
      (parityReduce identity.lhs.toList).Perm
        (parityReduce identity.rhs.toList) :=
    parityReduce_perm_of_parity_eq same
  have lhsNormal := cyclicDerivesNormal identity.lhs
  have rhsNormal := cyclicDerivesNormal identity.rhs
  cases hl : parityReduce identity.lhs.toList with
  | nil =>
      rw [hl] at reducedPerm
      have hr : parityReduce identity.rhs.toList = [] :=
        reducedPerm.nil_eq.symm
      rw [hl] at lhsNormal
      rw [hr] at rhsNormal
      exact Derives.trans lhsNormal <|
        Derives.trans
          (cyclicDerivesCommonSquare
            (Word.singleton identity.lhs.head)
            (Word.singleton identity.rhs.head))
          (Derives.symm rhsNormal)
  | cons x xs =>
      cases hr : parityReduce identity.rhs.toList with
      | nil =>
          rw [hl, hr] at reducedPerm
          exact False.elim (List.not_perm_cons_nil reducedPerm)
      | cons y ys =>
          rw [hl] at lhsNormal
          rw [hr] at rhsNormal
          rw [hl, hr] at reducedPerm
          have middle :
              Derives cyclicTwoBasis (Word.mk x xs) (Word.mk y ys) :=
            cyclicDerivesPermutation (Word.mk x xs) (Word.mk y ys) <| by
              simpa [Word.toList] using reducedPerm
          exact Derives.trans lhsNormal <|
            Derives.trans
              middle
              (Derives.symm rhsNormal)

/-- Proposition 3 of the primary source, parameterized by the `A₂` graph
sufficiency statement for compatibility with earlier callers. -/
theorem hasGraphParityIdentityTheory_of_a2GraphSufficiency
    (published : PublishedA2GraphSufficiency) :
    HasGraphParityIdentityTheory table.semigroup (α := Nat) := by
  intro identity
  constructor
  · exact valid_identity_graphParity
  · rintro ⟨sameGraph, sameParity⟩
    apply productEmbedding.pullback_identity identity
    exact (satisfiedBy_product_iff identity).mpr
      ⟨published identity sameGraph,
        cyclicTwo_valid_of_sameParity sameParity⟩

/-- Unconditional, table-checked graph-plus-parity characterization of every
identity of AC2. -/
theorem hasGraphParityIdentityTheory :
    HasGraphParityIdentityTheory table.semigroup (α := Nat) :=
  hasGraphParityIdentityTheory_of_a2GraphSufficiency a2GraphSufficiency

/-- Every explicit cycle obstruction is an AC2 identity. -/
theorem cycleObstruction_valid (bound : Nat) :
    (AC2Cycle.cycleObstruction bound).SatisfiedBy table.semigroup :=
  (hasGraphParityIdentityTheory
    (AC2Cycle.cycleObstruction bound)).mpr
      (AC2Cycle.cycleObstruction_graphParity bound)

/-- A formal nonfinite-basis theorem for the abstract graph-plus-parity theory
implies the concrete AC2 result. -/
theorem nonfinitelyBased_of_graphParityNonfinite
    (graphParityNonfinite : GraphParityNonfinitelyBased Nat) :
    NonfinitelyBased table.semigroup :=
  nonfinitelyBasedOver_of_graphParity
    hasGraphParityIdentityTheory graphParityNonfinite

/-- Compatibility wrapper for the previous two-hypothesis API. The graph
sufficiency argument is now proved internally. -/
theorem nonfinitelyBased_of_graphParityTheorems
    (_graphSufficiency : PublishedA2GraphSufficiency)
    (graphParityNonfinite : GraphParityNonfinitelyBased Nat) :
    NonfinitelyBased table.semigroup :=
  nonfinitelyBased_of_graphParityNonfinite graphParityNonfinite

/-- Compatibility name for the bounded graph-plus-parity cycle rewrite
statement proved in `AC2Cycle`. -/
def VolkovBoundedCycleUnderivability : Prop :=
  AC2Cycle.BoundedGraphParityCycleRewrite

/-- The bounded cycle rewrite statement, now proved internally. -/
theorem volkovBoundedCycleUnderivability :
    VolkovBoundedCycleUnderivability :=
  AC2Cycle.boundedGraphParityCycleRewrite

/-- All finite-basis bookkeeping and all AC2-specific obligations after the
one-step winding lemma are checked in Lean. -/
theorem nonfinitelyBased_of_boundedCycleUnderivability
    (underivable : VolkovBoundedCycleUnderivability) :
    NonfinitelyBased table.semigroup :=
  nonfinitelyBased_of_graphParityNonfinite
    (AC2Cycle.graphParityNonfinitelyBased_of_cycleRewrite
      underivable)

/-- Unconditional nonfinite basability of the published six-element AC2
table. -/
theorem nonfinitelyBased :
    NonfinitelyBased table.semigroup :=
  nonfinitelyBased_of_graphParityNonfinite
    AC2Cycle.graphParityNonfinitelyBased

/-- Constructive finite-countermodel route to the AC2 nonfinite-basis
theorem. -/
theorem nonfinitelyBased_of_finiteBoundedCycleCountermodels
    (countermodels : AC2Cycle.FiniteBoundedCycleCountermodels) :
    NonfinitelyBased table.semigroup :=
  nonfinitelyBased_of_graphParityNonfinite
    (AC2Cycle.graphParityNonfinitelyBased_of_boundedCycleUnderivability
      (AC2Cycle.boundedCycleUnderivability_of_finiteCountermodels
        countermodels))

/-- Historical compatibility name. Unlike the former definition, this no
longer assumes nonfinite basability of the ten-element product; it abbreviates
only the one-step bounded winding lemma above. -/
abbrev PublishedProductNonfiniteBasis : Prop :=
  VolkovBoundedCycleUnderivability

theorem nonfinitelyBased_of_publishedProductTheorem
    (published : PublishedProductNonfiniteBasis) :
    NonfinitelyBased table.semigroup :=
  nonfinitelyBased_of_boundedCycleUnderivability published

/-- The minimal bounded-cycle boundary transported to the exact Smallsemi
catalogue table `S6_8878`. -/
theorem s6_8878_nonfinitelyBased_of_boundedCycleUnderivability
    (underivable : VolkovBoundedCycleUnderivability) :
    NonfinitelyBased catalogueTable.semigroup :=
  (nonfinitelyBased_iff_of_sameIdentityTheory
    sameIdentityTheory_catalogue).mp
      (nonfinitelyBased_of_boundedCycleUnderivability underivable)

/-- Unconditional nonfinite basability of the exact Smallsemi catalogue table
`S6_8878`. -/
theorem s6_8878_nonfinitelyBased :
    NonfinitelyBased catalogueTable.semigroup :=
  (nonfinitelyBased_iff_of_sameIdentityTheory
    sameIdentityTheory_catalogue).mp nonfinitelyBased

end SemigroupBasis.Examples.AC2
