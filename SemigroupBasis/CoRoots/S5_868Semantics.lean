import SemigroupBasis.CoRoots.S5_868
import SemigroupBasis.Nonfinite.GraphParity

namespace SemigroupBasis.CoRoots.S5_868

open SemigroupBasis

/-- Lean representation of Trahtman's augmented adjacency graph: equal
initial and final vertices, equal variable support, and equal directed
adjacency edge support. Marking the endpoints is equivalent to adjoining a
fresh vertex with an edge to the initial variable and an edge from the final
variable. -/
def SameTrahtmanGraph (left right : Word Nat) : Prop :=
  left.SameMarkedDigraph right

theorem sameTrahtmanGraph_iff_sameMarkedDigraph
    (left right : Word Nat) :
    SameTrahtmanGraph left right ↔ left.SameMarkedDigraph right :=
  Iff.rfl

@[simp]
private theorem a2Table_semigroup_mul (left right : Fin 5) :
    SemigroupBasis.Examples.AC2.a2Table.semigroup.mul left right =
      SemigroupBasis.Examples.AC2.a2Mul left right :=
  rfl

/-! ## Separators for the necessity direction -/

private def supportSeparator (tested : Nat) : Nat → Fin 5 :=
  fun letter => if letter = tested then 0 else 4

private theorem fold_supportSeparator
    (tested : Nat) (letters : List Nat) (present : Bool) :
    letters.foldl
        (fun current letter =>
          SemigroupBasis.Examples.AC2.a2Mul current
            (supportSeparator tested letter))
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
            simpa [supportSeparator,
              SemigroupBasis.Examples.AC2.a2Mul] using ih true
          · have reverse : tested ≠ letter := Ne.symm hit
            simpa [supportSeparator, hit, reverse,
              SemigroupBasis.Examples.AC2.a2Mul] using ih false
      | true =>
          change
            rest.foldl
                (fun current next =>
                  SemigroupBasis.Examples.AC2.a2Mul current
                    (supportSeparator tested next))
                (SemigroupBasis.Examples.AC2.a2Mul 0
                  (supportSeparator tested letter)) = 0
          rw [show
            SemigroupBasis.Examples.AC2.a2Mul 0
                (supportSeparator tested letter) = (0 : Fin 5) by
              simp [SemigroupBasis.Examples.AC2.a2Mul]]
          simpa using ih true

private theorem eval_supportSeparator
    (tested : Nat) (word : Word Nat) :
    SemigroupBasis.Examples.AC2.a2Table.semigroup.eval
        (supportSeparator tested) word =
      if tested ∈ word.toList then (0 : Fin 5) else 4 := by
  cases word with
  | mk head tail =>
      simp only [Semigroup.eval, a2Table_semigroup_mul, Word.toList]
      by_cases hit : head = tested
      · subst head
        rw [show supportSeparator tested tested = (0 : Fin 5) by
          simp [supportSeparator]]
        simpa using fold_supportSeparator tested tail true
      · have reverse : tested ≠ head := Ne.symm hit
        rw [show supportSeparator tested head = (4 : Fin 5) by
          simp [supportSeparator, hit]]
        simpa [hit, reverse] using
          fold_supportSeparator tested tail false

private def initialSeparator (tested : Nat) : Nat → Fin 5 :=
  fun letter => if letter = tested then 2 else 4

private theorem initialSeparator_right
    (tested letter : Nat) (current : Fin 5)
    (currentShape : current = 2 ∨ current = 4) :
    SemigroupBasis.Examples.AC2.a2Mul current
        (initialSeparator tested letter) = current := by
  rcases currentShape with rfl | rfl <;>
    simp [initialSeparator, SemigroupBasis.Examples.AC2.a2Mul] <;>
    split <;> rfl

private theorem eval_initialSeparator
    (tested : Nat) (word : Word Nat) :
    SemigroupBasis.Examples.AC2.a2Table.semigroup.eval
        (initialSeparator tested) word =
      initialSeparator tested word.head := by
  cases word with
  | mk head tail =>
      simp only [Semigroup.eval, a2Table_semigroup_mul]
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

private def finalSeparator (tested : Nat) : Nat → Fin 5 :=
  fun letter => if letter = tested then 3 else 4

private theorem finalSeparator_left
    (tested previous next : Nat) :
    SemigroupBasis.Examples.AC2.a2Mul
        (finalSeparator tested previous)
        (finalSeparator tested next) =
      finalSeparator tested next := by
  by_cases previousHit : previous = tested <;>
    by_cases nextHit : next = tested <;>
    simp [finalSeparator, previousHit, nextHit,
      SemigroupBasis.Examples.AC2.a2Mul]

private theorem fold_finalSeparator
    (tested : Nat) (letters : List Nat) (previous : Nat) :
    letters.foldl
        (fun current letter =>
          SemigroupBasis.Examples.AC2.a2Mul current
            (finalSeparator tested letter))
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
    SemigroupBasis.Examples.AC2.a2Table.semigroup.eval
        (finalSeparator tested) word =
      finalSeparator tested word.final := by
  cases word with
  | mk head tail =>
      exact fold_finalSeparator tested tail head

private def edgeValue (source target letter : Nat) : Fin 5 :=
  if letter = target then
    if letter = source then 1 else 2
  else if letter = source then 3 else 4

private def edgePrefixValue
    (source target first previous : Nat) : Fin 5 :=
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
    SemigroupBasis.Examples.AC2.a2Mul
        (edgePrefixValue source target first previous)
        (edgeValue source target next) =
      if previous = source ∧ next = target then 0
      else edgePrefixValue source target first next := by
  by_cases firstTarget : first = target <;>
    by_cases sourceTarget : source = target <;>
    by_cases previousSource : previous = source <;>
    by_cases nextTarget : next = target <;>
    by_cases nextSource : next = source <;>
    simp_all [edgePrefixValue, edgeValue,
      SemigroupBasis.Examples.AC2.a2Mul]

private theorem fold_zero_edgeValue
    (source target : Nat) (letters : List Nat) :
    letters.foldl
        (fun current letter =>
          SemigroupBasis.Examples.AC2.a2Mul current
            (edgeValue source target letter))
        0 = 0 := by
  induction letters with
  | nil => rfl
  | cons letter rest ih =>
      simp only [List.foldl_cons]
      rw [show
        SemigroupBasis.Examples.AC2.a2Mul 0
            (edgeValue source target letter) = (0 : Fin 5) by
          simp [SemigroupBasis.Examples.AC2.a2Mul]]
      exact ih

private theorem fold_edgePrefix_zero_iff
    (source target first previous : Nat) (letters : List Nat) :
    letters.foldl
        (fun current letter =>
          SemigroupBasis.Examples.AC2.a2Mul current
            (edgeValue source target letter))
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
    SemigroupBasis.Examples.AC2.a2Table.semigroup.eval
        (edgeValue source target) word = (0 : Fin 5) ↔
      (source, target) ∈ word.adjacentPairs := by
  cases word with
  | mk head tail =>
      simp only [Semigroup.eval, a2Table_semigroup_mul,
        Word.adjacentPairs]
      rw [edgeValue_eq_prefix]
      exact fold_edgePrefix_zero_iff source target head head tail

/-! ## Exact marked-graph semantics -/

theorem valid_identity_sameSupport
    {identity : Identity Nat}
    (valid : identity.SatisfiedBy
      SemigroupBasis.Examples.AC2.a2Table.semigroup) :
    ∀ letter,
      letter ∈ identity.lhs.toList ↔
        letter ∈ identity.rhs.toList := by
  intro letter
  have evaluated := valid (supportSeparator letter)
  rw [eval_supportSeparator, eval_supportSeparator] at evaluated
  by_cases leftMem : letter ∈ identity.lhs.toList <;>
    by_cases rightMem : letter ∈ identity.rhs.toList <;>
    simp [leftMem, rightMem] at evaluated ⊢

theorem valid_identity_sameInitial
    {identity : Identity Nat}
    (valid : identity.SatisfiedBy
      SemigroupBasis.Examples.AC2.a2Table.semigroup) :
    identity.lhs.head = identity.rhs.head := by
  let tested := identity.lhs.head
  have evaluated := valid (initialSeparator tested)
  rw [eval_initialSeparator, eval_initialSeparator] at evaluated
  have leftValue :
      initialSeparator tested identity.lhs.head = (2 : Fin 5) := by
    simp [tested, initialSeparator]
  rw [leftValue] at evaluated
  by_cases same : identity.lhs.head = identity.rhs.head
  · exact same
  · have rightValue :
        initialSeparator tested identity.rhs.head = (4 : Fin 5) := by
      simp [tested, initialSeparator, Ne.symm same]
    rw [rightValue] at evaluated
    exact False.elim ((by decide : (2 : Fin 5) ≠ 4) evaluated)

theorem valid_identity_sameFinal
    {identity : Identity Nat}
    (valid : identity.SatisfiedBy
      SemigroupBasis.Examples.AC2.a2Table.semigroup) :
    identity.lhs.final = identity.rhs.final := by
  let tested := identity.lhs.final
  have evaluated := valid (finalSeparator tested)
  rw [eval_finalSeparator, eval_finalSeparator] at evaluated
  have leftValue :
      finalSeparator tested identity.lhs.final = (3 : Fin 5) := by
    simp [tested, finalSeparator]
  rw [leftValue] at evaluated
  by_cases same : identity.lhs.final = identity.rhs.final
  · exact same
  · have rightValue :
        finalSeparator tested identity.rhs.final = (4 : Fin 5) := by
      simp [tested, finalSeparator, Ne.symm same]
    rw [rightValue] at evaluated
    exact False.elim ((by decide : (3 : Fin 5) ≠ 4) evaluated)

theorem valid_identity_sameEdges
    {identity : Identity Nat}
    (valid : identity.SatisfiedBy
      SemigroupBasis.Examples.AC2.a2Table.semigroup) :
    ∀ source target,
      (source, target) ∈ identity.lhs.adjacentPairs ↔
        (source, target) ∈ identity.rhs.adjacentPairs := by
  intro source target
  have evaluated := valid (edgeValue source target)
  have zeroIff :
      SemigroupBasis.Examples.AC2.a2Table.semigroup.eval
            (edgeValue source target) identity.lhs = (0 : Fin 5) ↔
        SemigroupBasis.Examples.AC2.a2Table.semigroup.eval
            (edgeValue source target) identity.rhs = (0 : Fin 5) := by
    rw [evaluated]
  simpa only [eval_edgeSeparator_zero_iff] using zeroIff

/-- Necessity half of Trahtman's marked-graph characterization, proved only
from explicit valuations into the five-element table. -/
theorem valid_identity_sameMarkedDigraph
    {identity : Identity Nat}
    (valid : identity.SatisfiedBy
      SemigroupBasis.Examples.AC2.a2Table.semigroup) :
    identity.lhs.SameMarkedDigraph identity.rhs :=
  ⟨valid_identity_sameInitial valid,
    valid_identity_sameFinal valid,
    valid_identity_sameSupport valid,
    valid_identity_sameEdges valid⟩

theorem catalogue_valid_identity_sameMarkedDigraph
    {identity : Identity Nat}
    (valid : identity.SatisfiedBy
      Generated.Catalogue.S5_868.table.semigroup) :
    identity.lhs.SameMarkedDigraph identity.rhs := by
  rw [← a2Table_eq_catalogue] at valid
  exact valid_identity_sameMarkedDigraph valid

/-- Exact identity criterion for the catalogue representative. The
sufficiency direction reuses the already kernel-structured Rees-coordinate
evaluation theorem for the identical `A₂` table. -/
theorem satisfiedBy_iff_sameMarkedDigraph (identity : Identity Nat) :
    identity.SatisfiedBy
        Generated.Catalogue.S5_868.table.semigroup ↔
      identity.lhs.SameMarkedDigraph identity.rhs := by
  constructor
  · exact catalogue_valid_identity_sameMarkedDigraph
  · intro same
    rw [← a2Table_eq_catalogue]
    exact
      SemigroupBasis.Examples.AC2.a2_valid_of_sameMarkedDigraph same

/-- Every formal derivation from the three published laws preserves exactly
the marked directed graph. This closes the sound half of the published
normal-form argument without any separate syntactic induction. -/
theorem derives_sameMarkedDigraph
    {left right : Word Nat}
    (derivation : Derives basis left right) :
    left.SameMarkedDigraph right := by
  have valid :
      (Identity.mk left right).SatisfiedBy
        SemigroupBasis.Examples.AC2.a2Table.semigroup :=
    fun valuation =>
      Derives.sound publishedA2Models derivation valuation
  exact valid_identity_sameMarkedDigraph valid

theorem basis_law_sameMarkedDigraph
    (identity : Identity Nat) (member : identity ∈ basis) :
    identity.lhs.SameMarkedDigraph identity.rhs :=
  derives_sameMarkedDigraph (Derives.fromBasis member)

end SemigroupBasis.CoRoots.S5_868
