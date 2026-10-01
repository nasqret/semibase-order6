import SemigroupBasis.Nonfinite

namespace SemigroupBasis

namespace Word

/-- The final variable of a nonempty semigroup word. -/
def final (word : Word α) : α :=
  word.tail.getLastD word.head

/-- Consecutive directed edges, retaining multiplicity and order. -/
def adjacentPairsFrom (previous : α) : List α → List (α × α)
  | [] => []
  | next :: rest =>
      (previous, next) :: adjacentPairsFrom next rest

def adjacentPairs (word : Word α) : List (α × α) :=
  adjacentPairsFrom word.head word.tail

theorem adjacentPairsFrom_append
    (previous : α) (segment : List α) (next : α) (suffix : List α) :
    adjacentPairsFrom previous (segment ++ next :: suffix) =
      adjacentPairsFrom previous segment ++
        (segment.getLastD previous, next) :: adjacentPairsFrom next suffix := by
  induction segment generalizing previous with
  | nil => rfl
  | cons letter rest ih =>
      simp only [List.cons_append, adjacentPairsFrom, List.getLastD_cons,
        List.cons_append, List.cons.injEq, true_and]
      exact ih letter

theorem adjacentPairs_append (left right : Word α) :
    (left ++ right).adjacentPairs =
      left.adjacentPairs ++
        (left.final, right.head) :: right.adjacentPairs := by
  cases left with
  | mk head tail =>
      exact adjacentPairsFrom_append head tail right.head right.tail

@[simp]
theorem final_append (left right : Word α) :
    (left ++ right).final = right.final := by
  have getLastD_append_nonempty :
      ∀ (segment : List α) (previous next : α) (suffix : List α),
        (segment ++ next :: suffix).getLastD previous =
          suffix.getLastD next := by
    intro segment previous next suffix
    induction segment generalizing previous with
    | nil =>
        simp only [List.nil_append, List.getLastD_cons]
    | cons letter rest ih =>
        simp only [List.cons_append, List.getLastD_cons]
        exact ih letter
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail =>
          simp only [final, append_tail, append_head]
          exact getLastD_append_nonempty leftTail leftHead
            rightHead rightTail

/-- Equality of the directed adjacency graphs used in the AC2
characterization, including vertex set and marked initial/final vertices. -/
def SameMarkedDigraph [BEq α] (left right : Word α) : Prop :=
  left.head = right.head ∧
    left.final = right.final ∧
    (∀ letter, letter ∈ left.toList ↔ letter ∈ right.toList) ∧
    (∀ source target,
      (source, target) ∈ left.adjacentPairs ↔
        (source, target) ∈ right.adjacentPairs)

/-- Equality modulo two of every variable multiplicity. -/
def SameParity [BEq α] (left right : Word α) : Prop :=
  ∀ letter,
    left.toList.count letter % 2 =
      right.toList.count letter % 2

theorem SameMarkedDigraph.initial
    [BEq α] {left right : Word α}
    (same : left.SameMarkedDigraph right) :
    left.head = right.head :=
  same.1

theorem SameMarkedDigraph.final
    [BEq α] {left right : Word α}
    (same : left.SameMarkedDigraph right) :
    left.final = right.final :=
  same.2.1

theorem SameMarkedDigraph.support
    [BEq α] {left right : Word α}
    (same : left.SameMarkedDigraph right) (letter : α) :
    letter ∈ left.toList ↔ letter ∈ right.toList :=
  same.2.2.1 letter

theorem SameMarkedDigraph.edge
    [BEq α] {left right : Word α}
    (same : left.SameMarkedDigraph right) (source target : α) :
    (source, target) ∈ left.adjacentPairs ↔
      (source, target) ∈ right.adjacentPairs :=
  same.2.2.2 source target

theorem sameMarkedDigraph_refl [BEq α] (word : Word α) :
    word.SameMarkedDigraph word := by
  exact ⟨rfl, rfl, fun _ => Iff.rfl, fun _ _ => Iff.rfl⟩

theorem sameParity_refl [BEq α] (word : Word α) :
    word.SameParity word :=
  fun _ => rfl

end Word

/-- The exact graph-plus-parity predicate from the AC2 identity
characterization. -/
def Identity.GraphParityEquivalent [BEq α] (identity : Identity α) : Prop :=
  identity.lhs.SameMarkedDigraph identity.rhs ∧
    identity.lhs.SameParity identity.rhs

/-- A semigroup whose identities are exactly the graph-plus-parity
identities. -/
def HasGraphParityIdentityTheory (G : Semigroup S) [BEq α] : Prop :=
  ∀ identity : Identity α,
    identity.SatisfiedBy G ↔ identity.GraphParityEquivalent

/-- Finite axiomatizability of the abstract graph-plus-parity identity
theory, without choosing a concrete semigroup model. -/
def GraphParityFinitelyBased (α : Type u) [BEq α] : Prop :=
  ∃ basis : List (Identity α),
    (∀ identity : Identity α, identity ∈ basis →
      identity.GraphParityEquivalent) ∧
    (∀ identity : Identity α, identity.GraphParityEquivalent →
      Derives basis identity.lhs identity.rhs)

def GraphParityNonfinitelyBased (α : Type u) [BEq α] : Prop :=
  ¬GraphParityFinitelyBased α

theorem sameIdentityTheoryOver_of_graphParity
    [BEq α] {G : Semigroup S} {H : Semigroup T}
    (hG : HasGraphParityIdentityTheory G (α := α))
    (hH : HasGraphParityIdentityTheory H (α := α)) :
    SameIdentityTheoryOver G H α := by
  intro identity
  exact (hG identity).trans (hH identity).symm

/-- Once the graph-plus-parity theory itself is proved not finitely
axiomatizable, every concrete semigroup with exactly that identity theory is
nonfinitely based. -/
theorem nonfinitelyBasedOver_of_graphParity
    [BEq α] {G : Semigroup S}
    (hTheory : HasGraphParityIdentityTheory G (α := α))
    (hNonfinite : GraphParityNonfinitelyBased α) :
    NonfinitelyBasedOver G α := by
  rintro ⟨basis, basisFor⟩
  apply hNonfinite
  refine ⟨basis, ?_, ?_⟩
  · intro identity member
    exact (hTheory identity).mp (basisFor.1 identity member)
  · intro identity graphParity
    exact basisFor.2 identity ((hTheory identity).mpr graphParity)

end SemigroupBasis
