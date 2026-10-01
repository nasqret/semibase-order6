import SemigroupBasis.FiniteTable
import SemigroupBasis.Nonfinite
import SemigroupBasis.Nonfinite.A2One.TrahtmanCriterion
import SemigroupBasis.Nonfinite.A2One.NonseparatorTwoCountControl
import SemigroupBasis.Nonfinite.GraphParity
import SemigroupBasis.Transfer

namespace SemigroupBasis.Examples.A2One

open SemigroupBasis
open SemigroupBasis.Nonfinite.A2One

/-!
The six-element monoid `A_2^1` in the published order

`0, b, ba, ab, 1, a`.

Its five-element ideal `A_2` has presentation

`<a, b | a^2 = aba = a, bab = b, b^2 = 0>`.

Lee and Zhang print this table and list `A_2^1` in their Main Theorem:

E. W. H. Lee and W. T. Zhang,
"Finite basis problem for semigroups of order six",
LMS Journal of Computation and Mathematics 18 (2015), 1-129,
DOI 10.1112/S1461157014000412.

Their introduction records that the nonfinite-basis property was proved
independently by Sapir and Trahtman:

M. V. Sapir, "Problems of Burnside type and the finite basis property in
varieties of semigroups", Math. USSR-Izv. 30 (1988), 295-314,
DOI 10.1070/IM1988v030n02ABEH001012;

A. N. Trahtman, "Some finite infinitely basable semigroups",
Ural. Gos. Univ. Mat. Zap. 14 (1987), no. 2, 128-131.

The local order-six catalogue stores the same table as `S6_13747`, with the
published labels unchanged. This file proves the table, presentation
relations, normal forms, exact catalogue identification, equality of identity
theories, self-duality, every identity in Trahtman's explicit infinite
sequence, and the reduction from arbitrary equational derivations to the
one-step occurrence-order statement in Trahtman's proof.
-/

def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then 0
  else if left = 1 then
    if right = 3 then 1
    else if right = 4 then 1
    else if right = 5 then 2
    else 0
  else if left = 2 then
    if right = 1 then 1
    else if right = 2 then 2
    else if right = 3 then 1
    else if right = 4 then 2
    else if right = 5 then 2
    else 0
  else if left = 3 then
    if right = 3 then 3
    else if right = 4 then 3
    else if right = 5 then 5
    else 0
  else if left = 4 then right
  else
    if right = 1 then 3
    else if right = 2 then 5
    else if right = 3 then 3
    else if right = 4 then 5
    else if right = 5 then 5
    else 0

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

theorem table_rows :
    List.ofFn (fun left : Fin 6 =>
      List.ofFn (fun right : Fin 6 => (table.mul left right).val)) =
      [[0, 0, 0, 0, 0, 0],
       [0, 0, 0, 1, 1, 2],
       [0, 1, 2, 1, 2, 2],
       [0, 0, 0, 3, 3, 5],
       [0, 1, 2, 3, 4, 5],
       [0, 3, 5, 3, 5, 5]] := by
  decide

def zero : Fin 6 := 0
def b : Fin 6 := 1
def ba : Fin 6 := 2
def ab : Fin 6 := 3
def one : Fin 6 := 4
def a : Fin 6 := 5

@[simp] theorem zero_mul (value : Fin 6) : mul zero value = zero := by
  revert value
  decide

@[simp] theorem mul_zero (value : Fin 6) : mul value zero = zero := by
  revert value
  decide

@[simp] theorem one_mul (value : Fin 6) : mul one value = value := by
  revert value
  decide

@[simp] theorem mul_one (value : Fin 6) : mul value one = value := by
  revert value
  decide

@[simp] theorem a_mul_a : mul a a = a := by decide
@[simp] theorem b_mul_b : mul b b = zero := by decide
@[simp] theorem a_mul_b : mul a b = ab := by decide
@[simp] theorem b_mul_a : mul b a = ba := by decide

theorem a_mul_b_mul_a : mul (mul a b) a = a := by decide
theorem b_mul_a_mul_b : mul (mul b a) b = b := by decide

/-- Every element is one of the six normal forms supplied by the presentation
of `A_2` followed by adjoining an identity. -/
theorem carrier_normal_forms (value : Fin 6) :
    value = zero ∨ value = b ∨ value = mul b a ∨
      value = mul a b ∨ value = one ∨ value = a := by
  revert value
  decide

/-- Published-source labels to zero-based `S6_13747` labels. The map is the
identity permutation. -/
def publishedToCatalogue (value : Fin 6) : Fin 6 := value

def catalogueToPublished (value : Fin 6) : Fin 6 := value

theorem published_to_catalogue_values :
    List.ofFn (fun value : Fin 6 => (publishedToCatalogue value).val) =
      [0, 1, 2, 3, 4, 5] := by
  decide

theorem catalogue_to_published_values :
    List.ofFn (fun value : Fin 6 => (catalogueToPublished value).val) =
      [0, 1, 2, 3, 4, 5] := by
  decide

@[simp]
theorem catalogueToPublished_publishedToCatalogue (value : Fin 6) :
    catalogueToPublished (publishedToCatalogue value) = value :=
  rfl

@[simp]
theorem publishedToCatalogue_catalogueToPublished (value : Fin 6) :
    publishedToCatalogue (catalogueToPublished value) = value :=
  rfl

def catalogueMul (left right : Fin 6) : Fin 6 :=
  publishedToCatalogue
    (mul (catalogueToPublished left) (catalogueToPublished right))

def catalogueTable : FiniteTable where
  order := 6
  mul := catalogueMul
  assoc := by decide

/-- The zero-based Cayley table stored for `S6_13747`. Its SHA-256 digest in
`research/order6/published_classification.json` is
`d235ffd81c4cd30922538b31d6272781c1be32c222d06e4e5f24ac35eabe206e`. -/
theorem catalogue_table_rows :
    List.ofFn (fun left : Fin 6 =>
      List.ofFn (fun right : Fin 6 =>
        (catalogueTable.mul left right).val)) =
      [[0, 0, 0, 0, 0, 0],
       [0, 0, 0, 1, 1, 2],
       [0, 1, 2, 1, 2, 2],
       [0, 0, 0, 3, 3, 5],
       [0, 1, 2, 3, 4, 5],
       [0, 3, 5, 3, 5, 5]] := by
  decide

theorem publishedToCatalogue_map_mul (left right : Fin 6) :
    publishedToCatalogue (mul left right) =
      catalogueMul (publishedToCatalogue left) (publishedToCatalogue right) :=
  rfl

theorem catalogueToPublished_map_mul (left right : Fin 6) :
    catalogueToPublished (catalogueMul left right) =
      mul (catalogueToPublished left) (catalogueToPublished right) :=
  rfl

def publishedIntoCatalogue :
    Embedding table.semigroup catalogueTable.semigroup where
  toFun := publishedToCatalogue
  map_mul := publishedToCatalogue_map_mul
  injective := fun _ _ equality => equality

def catalogueIntoPublished :
    Embedding catalogueTable.semigroup table.semigroup where
  toFun := catalogueToPublished
  map_mul := catalogueToPublished_map_mul
  injective := fun _ _ equality => equality

/-- The printed `A_2^1` table and the stored `S6_13747` table have exactly
the same semigroup identities. -/
theorem sameIdentityTheory_catalogue :
    SameIdentityTheory table.semigroup catalogueTable.semigroup := by
  intro identity
  constructor
  · exact catalogueIntoPublished.pullback_identity identity
  · exact publishedIntoCatalogue.pullback_identity identity

/-! ## Deletion-marked-digraph invariant

Assigning the adjoined identity element to a variable erases every occurrence
of that variable.  The remaining five-element ideal has enough separating
valuations to recover the support, first letter, last letter, and directed
adjacency graph of every nonempty deletion projection.

This is the exact table-theoretic input to Trahtman's word argument.  The
proofs below are uniform over arbitrary words and arbitrary deletion
predicates; no bound on word length or number of variables is used.
-/

def evalList (valuation : Nat → Fin 6) (letters : List Nat) : Fin 6 :=
  letters.foldl (fun current letter => mul current (valuation letter)) one

def deletionValuation
    (keep : Nat → Bool) (valuation : Nat → Fin 6) : Nat → Fin 6 :=
  fun letter => if keep letter then valuation letter else one

private theorem foldl_mul_one (initial : Fin 6) (letters : List Nat)
    (valuation : Nat → Fin 6) :
    letters.foldl (fun current letter => mul current (valuation letter))
        (mul one initial) =
      letters.foldl (fun current letter => mul current (valuation letter))
        initial := by
  rw [one_mul]

private theorem evalList_toList
    (valuation : Nat → Fin 6) (word : Word Nat) :
    evalList valuation word.toList =
      table.semigroup.eval valuation word := by
  cases word with
  | mk head tail =>
      simp only [evalList, Word.toList, List.foldl_cons, Semigroup.eval]
      exact foldl_mul_one (valuation head) tail valuation

private theorem foldl_deletionValuation
    (keep : Nat → Bool) (valuation : Nat → Fin 6)
    (letters : List Nat) (initial : Fin 6) :
    letters.foldl
        (fun current letter =>
          mul current (deletionValuation keep valuation letter))
        initial =
      (letters.filter keep).foldl
        (fun current letter => mul current (valuation letter))
        initial := by
  induction letters generalizing initial with
  | nil => rfl
  | cons letter rest ih =>
      simp only [List.foldl_cons, List.filter_cons]
      by_cases kept : keep letter
      · rw [ih]
        simp [deletionValuation, kept]
      · rw [ih]
        simp [deletionValuation, kept, mul_one]

private theorem evalList_deletionValuation
    (keep : Nat → Bool) (valuation : Nat → Fin 6)
    (letters : List Nat) :
    evalList (deletionValuation keep valuation) letters =
      evalList valuation (letters.filter keep) := by
  simp only [evalList]
  exact foldl_deletionValuation keep valuation letters one

theorem eval_deletionValuation
    (keep : Nat → Bool) (valuation : Nat → Fin 6)
    (word : Word Nat) :
    table.semigroup.eval (deletionValuation keep valuation) word =
      evalList valuation (word.toList.filter keep) := by
  rw [← evalList_toList]
  simp only [evalList]
  exact foldl_deletionValuation keep valuation word.toList one

private def supportSeparator (tested : Nat) : Nat → Fin 6 :=
  fun letter => if letter = tested then zero else a

private theorem fold_supportSeparator
    (tested : Nat) (letters : List Nat) (present : Bool) :
    letters.foldl
        (fun current letter => mul current (supportSeparator tested letter))
        (if present then zero else a) =
      if present || letters.contains tested then zero else a := by
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
          simp only [if_true]
          rw [show
            mul zero (supportSeparator tested letter) = zero by
              simp [supportSeparator]]
          simpa using ih true

private theorem evalList_supportSeparator
    (tested : Nat) (letters : List Nat) :
    evalList (supportSeparator tested) letters =
      if letters = [] then one
      else if tested ∈ letters then zero else a := by
  cases letters with
  | nil => rfl
  | cons first rest =>
      simp only [evalList, List.foldl_cons]
      by_cases hit : first = tested
      · subst first
        rw [show
          mul one (supportSeparator tested tested) = zero by
            simp [supportSeparator]]
        simpa using fold_supportSeparator tested rest true
      · rw [show
          mul one (supportSeparator tested first) = a by
            simp [supportSeparator, hit]]
        have reverse : tested ≠ first := Ne.symm hit
        simpa [hit, reverse] using
          fold_supportSeparator tested rest false

private def initialSeparator (tested : Nat) : Nat → Fin 6 :=
  fun letter => if letter = tested then ba else a

private theorem initialSeparator_right
    (tested letter : Nat) (current : Fin 6)
    (shape : current = ba ∨ current = a) :
    mul current (initialSeparator tested letter) = current := by
  rcases shape with rfl | rfl <;>
    by_cases hit : letter = tested <;>
    simp [initialSeparator, hit, mul, ba, a]

private theorem evalList_initialSeparator
    (tested : Nat) (letters : List Nat) :
    evalList (initialSeparator tested) letters =
      match letters with
      | [] => one
      | first :: _ => initialSeparator tested first := by
  cases letters with
  | nil => rfl
  | cons first rest =>
      simp only [evalList, List.foldl_cons, one_mul]
      induction rest generalizing first with
      | nil => rfl
      | cons next remaining ih =>
          simp only [List.foldl_cons]
          have shape :
              initialSeparator tested first = ba ∨
                initialSeparator tested first = a := by
            by_cases hit : first = tested
            · left
              simp [initialSeparator, hit]
            · right
              simp [initialSeparator, hit]
          rw [initialSeparator_right tested next
            (initialSeparator tested first) shape]
          exact ih first

private def finalSeparator (tested : Nat) : Nat → Fin 6 :=
  fun letter => if letter = tested then ab else a

private theorem finalSeparator_left
    (tested previous next : Nat) :
    mul (finalSeparator tested previous) (finalSeparator tested next) =
      finalSeparator tested next := by
  by_cases previousHit : previous = tested <;>
    by_cases nextHit : next = tested <;>
    simp [finalSeparator, previousHit, nextHit, mul, ab, a]

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

private theorem evalList_finalSeparator
    (tested : Nat) (letters : List Nat) :
    evalList (finalSeparator tested) letters =
      match letters.getLast? with
      | none => one
      | some final => finalSeparator tested final := by
  cases letters with
  | nil => rfl
  | cons first rest =>
      simp only [evalList, List.foldl_cons, one_mul, List.getLast?_cons]
      rw [fold_finalSeparator]
      cases rest with
      | nil => rfl
      | cons next remaining => rfl

private def edgeValue (source target letter : Nat) : Fin 6 :=
  if letter = target then
    if letter = source then b else ba
  else if letter = source then ab else a

private def edgePrefixValue
    (source target first previous : Nat) : Fin 6 :=
  if first = target then
    if previous = source then b else ba
  else if previous = source then ab else a

private theorem edgeValue_eq_prefix
    (source target letter : Nat) :
    edgeValue source target letter =
      edgePrefixValue source target letter letter := by
  simp [edgeValue, edgePrefixValue]

private theorem edgePrefix_mul
    (source target first previous next : Nat) :
    mul (edgePrefixValue source target first previous)
        (edgeValue source target next) =
      if previous = source ∧ next = target then zero
      else edgePrefixValue source target first next := by
  set_option maxHeartbeats 800000 in
  by_cases firstTarget : first = target <;>
    by_cases sourceTarget : source = target <;>
    by_cases previousSource : previous = source <;>
    by_cases nextTarget : next = target <;>
    by_cases nextSource : next = source <;>
    simp_all [edgePrefixValue, edgeValue, mul, zero, b, ba, ab, a]

private theorem fold_zero_edgeValue
    (source target : Nat) (letters : List Nat) :
    letters.foldl
        (fun current letter => mul current (edgeValue source target letter))
        zero = zero := by
  induction letters with
  | nil => rfl
  | cons letter rest ih =>
      simp only [List.foldl_cons]
      rw [show mul zero (edgeValue source target letter) = zero by
        simp [edgeValue]]
      exact ih

private theorem fold_edgePrefix_zero_iff
    (source target first previous : Nat) (letters : List Nat) :
    letters.foldl
        (fun current letter => mul current (edgeValue source target letter))
        (edgePrefixValue source target first previous) = zero ↔
      (source, target) ∈ Word.adjacentPairsFrom previous letters := by
  induction letters generalizing previous with
  | nil =>
      by_cases firstTarget : first = target <;>
        by_cases previousSource : previous = source <;>
        simp [Word.adjacentPairsFrom, edgePrefixValue, firstTarget,
          previousSource, zero, b, ba, ab, a]
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

private theorem evalList_edgeValue_zero_iff
    (source target : Nat) (letters : List Nat) :
    evalList (edgeValue source target) letters = zero ↔
      (source, target) ∈
        SemigroupBasis.Nonfinite.A2One.adjacentPairsList letters := by
  cases letters with
  | nil =>
      simp [evalList,
        SemigroupBasis.Nonfinite.A2One.adjacentPairsList, one, zero]
  | cons first rest =>
      simp only [evalList, List.foldl_cons, one_mul,
        SemigroupBasis.Nonfinite.A2One.adjacentPairsList]
      rw [edgeValue_eq_prefix]
      exact fold_edgePrefix_zero_iff source target first first rest

private theorem filtered_eval_equal
    {left right : Word Nat}
    (valid : (Identity.mk left right).SatisfiedBy table.semigroup)
    (keep : Nat → Bool) (valuation : Nat → Fin 6) :
    evalList valuation (left.toList.filter keep) =
      evalList valuation (right.toList.filter keep) := by
  simpa only [eval_deletionValuation] using
    valid (deletionValuation keep valuation)

private theorem foldl_mul_assoc_value
    (valuation : Nat → Fin 6) (letters : List Nat)
    (left right : Fin 6) :
    letters.foldl
        (fun current letter => mul current (valuation letter))
        (mul left right) =
      mul left
        (letters.foldl
          (fun current letter => mul current (valuation letter))
          right) := by
  induction letters generalizing right with
  | nil => rfl
  | cons letter rest ih =>
      simp only [List.foldl_cons]
      have assoc := table.assoc left right (valuation letter)
      change
        mul (mul left right) (valuation letter) =
          mul left (mul right (valuation letter)) at assoc
      rw [assoc]
      exact ih (mul right (valuation letter))

private theorem evalList_append
    (valuation : Nat → Fin 6) (left right : List Nat) :
    evalList valuation (left ++ right) =
      mul (evalList valuation left) (evalList valuation right) := by
  simp only [evalList, List.foldl_append]
  have folded :=
    foldl_mul_assoc_value valuation right
      (left.foldl
        (fun current letter => mul current (valuation letter)) one)
      one
  simpa only [mul_one] using folded

private theorem evalList_bind_equal
    {left right : Word Nat}
    (valid : (Identity.mk left right).SatisfiedBy table.semigroup)
    (substitution : Nat → Word Nat) (valuation : Nat → Fin 6) :
    evalList valuation (left.bind substitution).toList =
      evalList valuation (right.bind substitution).toList := by
  rw [evalList_toList, evalList_toList,
    Semigroup.eval_bind, Semigroup.eval_bind]
  exact valid
    (fun letter =>
      table.semigroup.eval valuation (substitution letter))

theorem contextualInstance_eval_equal
    {identity : Identity Nat}
    (valid : identity.SatisfiedBy table.semigroup)
    (pre post : List Nat) (substitution : Nat → Word Nat)
    (valuation : Nat → Fin 6) :
    evalList valuation
        (pre ++ (identity.lhs.bind substitution).toList ++ post) =
      evalList valuation
        (pre ++ (identity.rhs.bind substitution).toList ++ post) := by
  rw [evalList_append, evalList_append,
    evalList_append, evalList_append]
  exact congrArg
    (fun middle =>
      mul (mul (evalList valuation pre) middle)
        (evalList valuation post))
    (evalList_bind_equal valid substitution valuation)

private theorem evalList_const_zero :
    ∀ letters : List Nat,
      evalList (fun _ => zero) letters =
        if letters = [] then one else zero
  | [] => rfl
  | _ :: rest => by
      simp only [evalList, List.foldl_cons, one_mul]
      induction rest with
      | nil => rfl
      | cons letter remaining ih =>
          simp only [List.foldl_cons]
          rw [zero_mul]
          exact ih

private theorem sameMarkedDigraphList_of_eval_equal
    (left right : List Nat)
    (evaluated :
      ∀ valuation : Nat → Fin 6,
        evalList valuation left = evalList valuation right) :
    SemigroupBasis.Nonfinite.A2One.SameMarkedDigraphList left right := by
  have sameEmpty : left = [] ↔ right = [] := by
    constructor
    · intro leftEmpty
      by_cases rightEmpty : right = []
      · exact rightEmpty
      have equality := evaluated (fun _ => zero)
      rw [evalList_const_zero, evalList_const_zero,
        leftEmpty] at equality
      simp [rightEmpty, one, zero] at equality
    · intro rightEmpty
      by_cases leftEmpty : left = []
      · exact leftEmpty
      have equality := evaluated (fun _ => zero)
      rw [evalList_const_zero, evalList_const_zero,
        rightEmpty] at equality
      simp [leftEmpty, one, zero] at equality
  refine ⟨?_, ?_, ?_, ?_⟩
  · cases left with
    | nil =>
        have rightEmpty := sameEmpty.mp rfl
        simp [rightEmpty]
    | cons leftFirst leftRest =>
        cases right with
        | nil =>
            have impossible :
                (leftFirst :: leftRest : List Nat) = [] :=
              sameEmpty.mpr rfl
            simp at impossible
        | cons rightFirst rightRest =>
            let tested := leftFirst
            have equality :
                initialSeparator tested leftFirst =
                  initialSeparator tested rightFirst := by
              simpa only [evalList_initialSeparator] using
                evaluated (initialSeparator tested)
            simp only [List.head?_cons, Option.some.injEq]
            by_cases same : leftFirst = rightFirst
            · exact same
            · have leftValue :
                  initialSeparator tested leftFirst = ba := by
                simp [tested, initialSeparator]
              have rightValue :
                  initialSeparator tested rightFirst = a := by
                simp [tested, initialSeparator, Ne.symm same]
              rw [leftValue, rightValue] at equality
              exact False.elim ((by decide : ba ≠ a) equality)
  · cases left with
    | nil =>
        have rightEmpty := sameEmpty.mp rfl
        simp [rightEmpty]
    | cons leftFirst leftRest =>
        cases right with
        | nil =>
            have impossible :
                (leftFirst :: leftRest : List Nat) = [] :=
              sameEmpty.mpr rfl
            simp at impossible
        | cons rightFirst rightRest =>
            let leftFinal := leftRest.getLast?.getD leftFirst
            let rightFinal := rightRest.getLast?.getD rightFirst
            let tested := leftFinal
            have equality :
                finalSeparator tested leftFinal =
                  finalSeparator tested rightFinal := by
              simpa only [evalList_finalSeparator, List.getLast?_cons,
                leftFinal, rightFinal] using
                evaluated (finalSeparator tested)
            simp only [List.getLast?_cons, Option.some.injEq]
            by_cases same : leftFinal = rightFinal
            · exact same
            · have leftValue :
                  finalSeparator tested leftFinal = ab := by
                simp [tested, finalSeparator]
              have rightValue :
                  finalSeparator tested rightFinal = a := by
                simp [tested, finalSeparator, Ne.symm same]
              rw [leftValue, rightValue] at equality
              exact False.elim ((by decide : ab ≠ a) equality)
  · intro letter
    constructor
    · intro leftMem
      by_cases rightMem : letter ∈ right
      · exact rightMem
      have leftNonempty : left ≠ [] :=
        List.ne_nil_of_mem leftMem
      have rightNonempty : right ≠ [] := by
        intro rightEmpty
        exact leftNonempty (sameEmpty.mpr rightEmpty)
      have equality := evaluated (supportSeparator letter)
      rw [evalList_supportSeparator,
        evalList_supportSeparator] at equality
      simp [leftNonempty, rightNonempty, leftMem, rightMem,
        zero, a] at equality
    · intro rightMem
      by_cases leftMem : letter ∈ left
      · exact leftMem
      have rightNonempty : right ≠ [] :=
        List.ne_nil_of_mem rightMem
      have leftNonempty : left ≠ [] := by
        intro leftEmpty
        exact rightNonempty (sameEmpty.mp leftEmpty)
      have equality := evaluated (supportSeparator letter)
      rw [evalList_supportSeparator,
        evalList_supportSeparator] at equality
      simp [leftNonempty, rightNonempty, leftMem, rightMem,
        zero, a] at equality
  · intro source target
    have equality := evaluated (edgeValue source target)
    have zeroIff :
        evalList (edgeValue source target) left = zero ↔
          evalList (edgeValue source target) right = zero := by
      rw [equality]
    simpa only [evalList_edgeValue_zero_iff] using zeroIff

theorem contextualInstance_sameDeletionMarkedDigraph
    {identity : Identity Nat}
    (valid : identity.SatisfiedBy table.semigroup)
    (pre post : List Nat) (substitution : Nat → Word Nat) :
    ∀ keep,
      SemigroupBasis.Nonfinite.A2One.SameMarkedDigraphList
        ((pre ++ (identity.lhs.bind substitution).toList ++ post).filter keep)
        ((pre ++ (identity.rhs.bind substitution).toList ++ post).filter keep) := by
  intro keep
  apply sameMarkedDigraphList_of_eval_equal
  intro valuation
  rw [← evalList_deletionValuation,
    ← evalList_deletionValuation]
  exact contextualInstance_eval_equal valid pre post substitution
    (deletionValuation keep valuation)

theorem valid_identity_sameDeletionMarkedDigraph
    {identity : Identity Nat}
    (valid : identity.SatisfiedBy table.semigroup) :
    SemigroupBasis.Nonfinite.A2One.SameDeletionMarkedDigraph
      identity.lhs identity.rhs := by
  intro keep
  apply sameMarkedDigraphList_of_eval_equal
  intro valuation
  exact filtered_eval_equal valid keep valuation

/-- The anti-automorphism witnessing self-duality. It exchanges `ba` and
`ab` and fixes `0`, `a`, `b`, and `1`. -/
def dual (value : Fin 6) : Fin 6 :=
  if value = ba then ab
  else if value = ab then ba
  else value

@[simp]
theorem dual_dual (value : Fin 6) : dual (dual value) = value := by
  revert value
  decide

theorem dual_mul (left right : Fin 6) :
    dual (mul left right) = mul (dual right) (dual left) := by
  revert left right
  decide

/-! ## Trahtman's explicit infinite identity sequence -/

namespace Trahtman

open SemigroupBasis.Nonfinite.A2One

/-- Forward and reverse products are simultaneously equal to the identity
element, or simultaneously nonidentity. -/
abbrev MirrorPair (forward reverse : Fin 6) : Prop :=
  (forward = one ↔ reverse = one)

private def pairAssignment (left right : Fin 6) : Fin 2 → Fin 6 :=
  Fin.cases left (fun _ => right)

private def tripleAssignment
    (first second third : Fin 6) : Fin 3 → Fin 6 :=
  Fin.cases first (Fin.cases second (fun _ => third))

private theorem mirrorPair_two_checked :
    (FiniteTable.assignments 2 6).all (fun values =>
      decide (MirrorPair
        (mul (values 0) (values 1))
        (mul (values 1) (values 0)))) = true := by
  decide

theorem mirrorPair_two (left right : Fin 6) :
    MirrorPair (mul left right) (mul right left) := by
  have checked :=
    (List.all_eq_true.mp mirrorPair_two_checked)
      (pairAssignment left right)
      (FiniteTable.assignment_mem (pairAssignment left right))
  simpa [pairAssignment] using of_decide_eq_true checked

private theorem mirrorPair_step_checked :
    (FiniteTable.assignments 3 6).all (fun values =>
      decide (MirrorPair (values 0) (values 1) →
        MirrorPair
          (mul (values 0) (values 2))
          (mul (values 2) (values 1)))) = true := by
  decide

theorem mirrorPair_step
    {forward reverse : Fin 6}
    (pair : MirrorPair forward reverse) (next : Fin 6) :
    MirrorPair (mul forward next) (mul next reverse) := by
  have checked :=
    (List.all_eq_true.mp mirrorPair_step_checked)
      (tripleAssignment forward reverse next)
      (FiniteTable.assignment_mem
        (tripleAssignment forward reverse next))
  have implication :
      MirrorPair forward reverse →
        MirrorPair (mul forward next) (mul next reverse) := by
    simpa [tripleAssignment] using of_decide_eq_true checked
  exact implication pair

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1200000 in
private theorem mirror_identity_checked :
    (FiniteTable.assignments 3 6).all (fun values =>
      decide (MirrorPair (values 0) (values 1) →
        mul
            (mul
              (mul (mul (values 0) (values 2)) (values 1))
              (values 2))
            (values 0) =
          mul
            (mul
              (mul
                (mul
                  (mul
                    (mul
                      (mul
                        (mul (values 0) (values 2))
                        (values 1))
                      (values 2))
                    (values 0))
                  (values 2))
                (values 1))
              (values 2))
            (values 0))) = true := by
  decide

/-- The finite table calculation behind Trahtman's sequence.  Once a forward
product and its reversed product satisfy `MirrorPair`, inserting
`y reverse y forward` after `forward y reverse y forward` is idempotent. -/
theorem mirror_identity
    {forward reverse : Fin 6}
    (pair : MirrorPair forward reverse) (middle : Fin 6) :
    mul (mul (mul (mul forward middle) reverse) middle) forward =
      mul
        (mul
          (mul
            (mul
              (mul (mul (mul (mul forward middle) reverse) middle) forward)
                middle)
              reverse)
            middle)
          forward := by
  have checked :=
    (List.all_eq_true.mp mirror_identity_checked)
      (tripleAssignment forward reverse middle)
      (FiniteTable.assignment_mem
        (tripleAssignment forward reverse middle))
  have implication :
      MirrorPair forward reverse →
        mul (mul (mul (mul forward middle) reverse) middle) forward =
          mul
            (mul
              (mul
                (mul
                  (mul (mul (mul (mul forward middle) reverse) middle) forward)
                    middle)
                  reverse)
                middle)
              forward := by
    simpa [tripleAssignment] using of_decide_eq_true checked
  exact implication pair

set_option maxHeartbeats 800000 in
theorem eval_forward_reverse_mirror
    (valuation : Nat → Fin 6) :
    ∀ extra,
      MirrorPair
        (table.semigroup.eval valuation (forwardBlock extra))
        (table.semigroup.eval valuation (reverseBlock extra))
  | 0 => by
      simpa [forwardBlock, reverseBlock, Semigroup.eval_append] using
        mirrorPair_two (valuation 0) (valuation 1)
  | extra + 1 => by
      simp only [forwardBlock, reverseBlock, Semigroup.eval_append,
        Semigroup.eval_singleton]
      exact mirrorPair_step
        (eval_forward_reverse_mirror valuation extra)
        (valuation (extra + 2))

private theorem eval_anchor
    (valuation : Nat → Fin 6) (extra : Nat) :
    table.semigroup.eval valuation (anchor extra) =
      mul
        (mul
          (mul
            (mul
              (table.semigroup.eval valuation (forwardBlock extra))
              (valuation (extra + 2)))
            (table.semigroup.eval valuation (reverseBlock extra)))
          (valuation (extra + 2)))
        (table.semigroup.eval valuation (forwardBlock extra)) := by
  simp only [anchor, separator, Semigroup.eval_append,
    Semigroup.eval_singleton]
  rfl

private theorem eval_extended
    (valuation : Nat → Fin 6) (extra : Nat) :
    table.semigroup.eval valuation (extended extra) =
      mul
        (mul
          (mul
            (mul
              (table.semigroup.eval valuation (anchor extra))
              (valuation (extra + 2)))
            (table.semigroup.eval valuation (reverseBlock extra)))
          (valuation (extra + 2)))
        (table.semigroup.eval valuation (forwardBlock extra)) := by
  simp only [extended, separator, Semigroup.eval_append,
    Semigroup.eval_singleton]
  rfl

/-- Every member of Trahtman's explicit sequence is valid in the exact
six-element table.  The proof is uniform in `n`; only the 26 reachable
forward/reverse product pairs and the six values of `y` are discharged by
finite kernel computation. -/
theorem trahtmanIdentity_valid (extra : Nat) :
    (trahtmanIdentity extra).SatisfiedBy table.semigroup := by
  intro valuation
  have pair := eval_forward_reverse_mirror valuation extra
  change table.semigroup.eval valuation (anchor extra) =
    table.semigroup.eval valuation (extended extra)
  rw [eval_anchor, eval_extended, eval_anchor]
  exact mirror_identity pair (valuation (extra + 2))

end Trahtman

/-- The `A₂¹` table converts the pure deletion-graph preimage theorem into
Trahtman's exact isoterm statement.  All semigroup-specific work is supplied
by `valid_identity_sameDeletionMarkedDigraph`; the remaining hypothesis is
only a theorem about words and the explicit anchor. -/
theorem trahtmanPreimageIsoterm_of_deletionGraph
    (rigid :
      SemigroupBasis.Nonfinite.A2One.BoundedDeletionGraphPreimageRigidity) :
    SemigroupBasis.Nonfinite.A2One.BoundedAnchorPreimageIsoterm
      table.semigroup := by
  intro bound word uses substitution mapped other valid
  exact rigid bound word uses substitution mapped other
    (valid_identity_sameDeletionMarkedDigraph valid)

/-- Compatibility bridge to the contextual formulation.  The actual
mathematical input is now the preimage-isoterm theorem above. -/
theorem trahtmanAnchorRigidity_of_deletionGraph
    (rigid :
      SemigroupBasis.Nonfinite.A2One.BoundedDeletionGraphPreimageRigidity) :
    SemigroupBasis.Nonfinite.A2One.TrahtmanAnchorRigidity
      table.semigroup :=
  SemigroupBasis.Nonfinite.A2One.trahtmanAnchorRigidity_of_preimageIsoterm
    (trahtmanPreimageIsoterm_of_deletionGraph rigid)

/-- The weaker contextual deletion-graph boundary also suffices directly.
This isolates the exact statement needed by the derivational argument from
the stronger full preimage-reconstruction route. -/
theorem trahtmanAnchorRigidity_of_deletionGraphAnchor
    (rigid :
      SemigroupBasis.Nonfinite.A2One.BoundedDeletionGraphAnchorRigidity) :
    SemigroupBasis.Nonfinite.A2One.TrahtmanAnchorRigidity
      table.semigroup :=
  SemigroupBasis.Nonfinite.A2One.trahtmanAnchorRigidity_of_deletionGraphAnchorRigidity
      (fun _identity valid =>
        valid_identity_sameDeletionMarkedDigraph valid)
      rigid

/-- The sole remaining external mathematical boundary.

This proposition is purely combinatorial.  It has no semigroup parameter and
no validity hypothesis: if `u` uses at most `bound` variables and maps to
`Xₙ y Xₙʳ y Xₙ`, where `n = 3 * bound + 2`, then every word with the same
deletion marked-digraph family as `u` must equal `u`. -/
def TrahtmanInfiniteWordLemma : Prop :=
  SemigroupBasis.Nonfinite.A2One.BoundedDeletionGraphPreimageRigidity

/-- The exact one-step infinite-word lemma implies the former bounded
derivational boundary. -/
theorem boundedTrahtmanUnderivability_of_infiniteWord
    (infiniteWord : TrahtmanInfiniteWordLemma) :
    SemigroupBasis.Nonfinite.A2One.BoundedTrahtmanUnderivability
      table.semigroup :=
  SemigroupBasis.Nonfinite.A2One.boundedTrahtmanUnderivability_of_preimageIsoterm
    (trahtmanPreimageIsoterm_of_deletionGraph infiniteWord)

/-- Trahtman's explicit sequence and one-step infinite-word lemma imply the
nonfinite-basis theorem for the printed `A₂¹` table. -/
theorem nonfinitelyBased_of_trahtman
    (infiniteWord : TrahtmanInfiniteWordLemma) :
    NonfinitelyBased table.semigroup :=
  SemigroupBasis.Nonfinite.A2One.nonfinitelyBased_of_preimageIsoterm
    Trahtman.trahtmanIdentity_valid
    (trahtmanPreimageIsoterm_of_deletionGraph infiniteWord)

/-- The result transported through the checked identity relabeling to the
exact catalogue representative `S6_13747`. -/
theorem s6_13747_nonfinitelyBased_of_trahtman
    (infiniteWord : TrahtmanInfiniteWordLemma) :
    NonfinitelyBased catalogueTable.semigroup :=
  (nonfinitelyBased_iff_of_sameIdentityTheory
    sameIdentityTheory_catalogue).mp
      (nonfinitelyBased_of_trahtman infiniteWord)

/-- Compatibility name for the project-wide axiom audit.  Its hypothesis is
the explicit Trahtman infinite-word lemma, not the former broad proposition
that the table is already nonfinitely based. -/
theorem s6_13747_nonfinitelyBased_of_mainTheorem
    (infiniteWord : TrahtmanInfiniteWordLemma) :
    NonfinitelyBased catalogueTable.semigroup :=
  s6_13747_nonfinitelyBased_of_trahtman infiniteWord

/-- The exact catalogue representative `S6_13747` is nonfinitely based.
The Trahtman infinite-word lemma is discharged by the checked anchor-preimage
rigidity theorem. -/
theorem s6_13747_nonfinitelyBased :
    NonfinitelyBased catalogueTable.semigroup :=
  s6_13747_nonfinitelyBased_of_trahtman
    SemigroupBasis.Nonfinite.A2One.boundedDeletionGraphPreimageRigidity

end SemigroupBasis.Examples.A2One
