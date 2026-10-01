import SemigroupBasis.Nonfinite.GraphParity
import SemigroupBasis.Examples.CyclicTwo

namespace SemigroupBasis

namespace AC2Cycle

/-!
The identity series used for `AC₂` is

`(x₁² x₂² ... xₙ²)² = (x₁² x₂² ... xₙ²)³`, `n ≥ 2`.

For a variable bound `bound`, `cycleCore bound` uses exactly the variables
`0, ..., bound + 1`, each twice.  Thus `cycleObstruction bound` is the member
of the series with `n = bound + 2`.
-/

def cycleVariables (bound : Nat) : List Nat :=
  0 :: (List.range (bound + 1)).map Nat.succ

def cycleCore (bound : Nat) : Word Nat :=
  ⟨0,
    0 ::
      (List.range (bound + 1)).flatMap
        (fun index => [Nat.succ index, Nat.succ index])⟩

def cycleObstruction (bound : Nat) : Identity Nat :=
  let core := cycleCore bound
  ⟨core ++ core, (core ++ core) ++ core⟩

theorem cycleCore_toList (bound : Nat) :
    (cycleCore bound).toList =
      (cycleVariables bound).flatMap (fun letter => [letter, letter]) := by
  simp [cycleCore, cycleVariables, Word.toList, List.flatMap_map]

private theorem doubled_count_even
    (variables : List Nat) (tested : Nat) :
    (variables.flatMap (fun letter => [letter, letter])).count tested %
        2 = 0 := by
  induction variables with
  | nil => rfl
  | cons letter rest ih =>
      simp only [List.flatMap_cons, List.count_append, List.count_cons,
        List.count_nil]
      split <;> omega

theorem cycleCore_count_even (bound tested : Nat) :
    (cycleCore bound).toList.count tested % 2 = 0 := by
  rw [cycleCore_toList]
  exact doubled_count_even (cycleVariables bound) tested

private theorem square_triple_sameMarkedDigraph (word : Word Nat) :
    (word ++ word).SameMarkedDigraph ((word ++ word) ++ word) := by
  refine ⟨rfl, by simp, ?_, ?_⟩
  · intro letter
    simp [Word.toList_append]
  · intro source target
    simp only [Word.adjacentPairs_append, Word.final_append,
      List.mem_append, List.mem_cons, Prod.mk.injEq]
    constructor
    · intro occurrence
      exact Or.inl occurrence
    · intro occurrence
      rcases occurrence with leftOccurrence | boundary | edge
      · exact leftOccurrence
      · exact Or.inr (Or.inl boundary)
      · exact Or.inl edge

private theorem cycle_square_triple_sameParity (bound : Nat) :
    (cycleCore bound ++ cycleCore bound).SameParity
      ((cycleCore bound ++ cycleCore bound) ++ cycleCore bound) := by
  intro tested
  simp only [Word.toList_append, List.count_append]
  have even := cycleCore_count_even bound tested
  omega

/-- Every member of the explicit AC2 obstruction series satisfies the exact
graph-plus-parity identity criterion. -/
theorem cycleObstruction_graphParity (bound : Nat) :
    (cycleObstruction bound).GraphParityEquivalent := by
  exact
    ⟨square_triple_sameMarkedDigraph (cycleCore bound),
      cycle_square_triple_sameParity bound⟩

/-!
The missing Volkov argument is a bounded winding-number argument on the
directed cycle carried by `cycleCore bound`.  The definitions below make that
argument explicit.

The target cycle has `bound + 2` vertices.  A permitted walk may stay at its
current vertex or move once around the directed cycle.  Its winding parity is
the parity of the number of transitions from the last vertex back to `0`.
-/

def cycleSize (bound : Nat) : Nat :=
  bound + 2

def CycleStep (bound source target : Nat) : Prop :=
  source = target ∨
    (source + 1 < cycleSize bound ∧ target = source + 1) ∨
    (source + 1 = cycleSize bound ∧ target = 0)

def listAdjacentPairs : List Nat → List (Nat × Nat)
  | [] => []
  | head :: tail => Word.adjacentPairsFrom head tail

def CycleWalkList (bound : Nat) (letters : List Nat) : Prop :=
  (∀ letter, letter ∈ letters → letter < cycleSize bound) ∧
    ∀ source target,
      (source, target) ∈ listAdjacentPairs letters →
        CycleStep bound source target

def CycleWalk (bound : Nat) (word : Word Nat) : Prop :=
  CycleWalkList bound word.toList

def windingParityList (bound : Nat) (letters : List Nat) : Nat :=
  (listAdjacentPairs letters).count (cycleSize bound - 1, 0) % 2

def windingParity (bound : Nat) (word : Word Nat) : Nat :=
  windingParityList bound word.toList

private def doubledLetter (letter : Nat) : Word Nat :=
  ⟨letter, [letter]⟩

private theorem cycleCore_succ (bound : Nat) :
    cycleCore (bound + 1) =
      cycleCore bound ++ doubledLetter (bound + 2) := by
  apply Word.toList_injective
  simp [cycleCore, doubledLetter, List.range_succ, Nat.add_assoc,
    Word.toList, List.append_assoc]

theorem cycleCore_final (bound : Nat) :
    (cycleCore bound).final = bound + 1 := by
  induction bound with
  | zero =>
      rfl
  | succ bound _ =>
      rw [cycleCore_succ, Word.final_append]
      rfl

private def LinearCycleWalk (bound : Nat) (word : Word Nat) : Prop :=
  (∀ letter, letter ∈ word.toList → letter < cycleSize bound) ∧
    ∀ source target,
      (source, target) ∈ word.adjacentPairs →
        source = target ∨ target = source + 1

private theorem linearCycleWalk_cycleCore (bound : Nat) :
    LinearCycleWalk bound (cycleCore bound) := by
  induction bound with
  | zero =>
      constructor
      · intro letter member
        simp [cycleCore, Word.toList] at member
        rcases member with rfl | rfl <;> simp [cycleSize]
      · intro source target member
        simp [cycleCore, Word.adjacentPairs, Word.adjacentPairsFrom] at member
        rcases member with equality | equality | equality
        · rcases equality with ⟨rfl, rfl⟩
          exact Or.inl rfl
        · rcases equality with ⟨rfl, rfl⟩
          exact Or.inr rfl
        · rcases equality with ⟨rfl, rfl⟩
          exact Or.inl rfl
  | succ bound ih =>
      rw [cycleCore_succ]
      constructor
      · intro letter member
        simp only [Word.toList_append, List.mem_append] at member
        rcases member with old | added
        · have oldBound := ih.1 letter old
          simp only [cycleSize] at oldBound ⊢
          omega
        · simp [doubledLetter, Word.toList] at added
          simp only [cycleSize]
          omega
      · intro source target member
        simp only [Word.adjacentPairs_append, List.mem_append,
          List.mem_cons] at member
        rcases member with old | boundary | added
        · exact ih.2 source target old
        · injection boundary with sourceEq targetEq
          rw [cycleCore_final] at sourceEq
          simp [doubledLetter] at targetEq
          subst source
          subst target
          exact Or.inr (by omega)
        · simp [doubledLetter, Word.adjacentPairs,
            Word.adjacentPairsFrom] at added
          exact Or.inl (added.1.trans added.2.symm)

private theorem adjacentPairs_target_mem
    (word : Word Nat) {source target : Nat}
    (member : (source, target) ∈ word.adjacentPairs) :
    target ∈ word.toList := by
  cases word with
  | mk head tail =>
      induction tail generalizing head with
      | nil =>
          simp [Word.adjacentPairs, Word.adjacentPairsFrom] at member
      | cons next rest ih =>
          simp only [Word.adjacentPairs, Word.adjacentPairsFrom,
            List.mem_cons] at member
          rcases member with first | later
          · have targetEq : target = next :=
              congrArg Prod.snd first
            rw [targetEq]
            simp [Word.toList]
          · have laterMember :
                target ∈ (Word.mk next rest).toList :=
              ih next later
            simp only [Word.toList] at laterMember ⊢
            exact List.mem_cons_of_mem head laterMember

theorem cycleCore_cycleWalk (bound : Nat) :
    CycleWalk bound (cycleCore bound) := by
  rcases linearCycleWalk_cycleCore bound with ⟨vertices, edges⟩
  refine ⟨vertices, ?_⟩
  intro source target member
  have edge :
      (source, target) ∈ (cycleCore bound).adjacentPairs := by
    simpa [listAdjacentPairs, Word.toList,
      Word.adjacentPairs] using member
  rcases edges source target edge with same | forward
  · exact Or.inl same
  · exact Or.inr (Or.inl ⟨by
      have targetBound :=
        vertices target (adjacentPairs_target_mem _ edge)
      simpa [forward] using targetBound,
      forward⟩)

private theorem cycleWalk_iff (bound : Nat) (word : Word Nat) :
    CycleWalk bound word ↔
      (∀ letter, letter ∈ word.toList → letter < cycleSize bound) ∧
      ∀ source target,
        (source, target) ∈ word.adjacentPairs →
          CycleStep bound source target := by
  cases word
  rfl

private theorem CycleWalk.append
    {bound : Nat} {left right : Word Nat}
    (leftWalk : CycleWalk bound left)
    (rightWalk : CycleWalk bound right)
    (boundary : CycleStep bound left.final right.head) :
    CycleWalk bound (left ++ right) := by
  rw [cycleWalk_iff] at leftWalk rightWalk ⊢
  constructor
  · intro letter member
    simp only [Word.toList_append, List.mem_append] at member
    exact member.elim (leftWalk.1 letter) (rightWalk.1 letter)
  · intro source target member
    simp only [Word.adjacentPairs_append, List.mem_append,
      List.mem_cons] at member
    rcases member with leftEdge | crossing | rightEdge
    · exact leftWalk.2 source target leftEdge
    · simp only [Prod.mk.injEq] at crossing
      rcases crossing with ⟨rfl, rfl⟩
      exact boundary
    · exact rightWalk.2 source target rightEdge

private theorem cycleCore_boundaryStep (bound : Nat) :
    CycleStep bound (cycleCore bound).final (cycleCore bound).head := by
  exact Or.inr (Or.inr ⟨by
    simp [cycleCore_final, cycleSize],
    rfl⟩)

theorem cycleObstruction_lhs_cycleWalk (bound : Nat) :
    CycleWalk bound (cycleObstruction bound).lhs := by
  exact (cycleCore_cycleWalk bound).append
    (cycleCore_cycleWalk bound) (cycleCore_boundaryStep bound)

theorem cycleObstruction_rhs_cycleWalk (bound : Nat) :
    CycleWalk bound (cycleObstruction bound).rhs := by
  exact cycleObstruction_lhs_cycleWalk bound |>.append
    (cycleCore_cycleWalk bound) (by
      change CycleStep bound
        (cycleCore bound ++ cycleCore bound).final
        (cycleCore bound).head
      rw [Word.final_append]
      exact cycleCore_boundaryStep bound)

private theorem windingParity_append (bound : Nat)
    (left right : Word Nat) :
    windingParity bound (left ++ right) =
      (left.adjacentPairs.count (cycleSize bound - 1, 0) +
        (if (left.final, right.head) = (cycleSize bound - 1, 0)
          then 1 else 0) +
        right.adjacentPairs.count (cycleSize bound - 1, 0)) % 2 := by
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail =>
          simp [windingParity, windingParityList, listAdjacentPairs,
            Word.adjacentPairs, Word.final, Word.toList,
            Word.adjacentPairsFrom_append, List.count_append,
            List.count_cons, Nat.add_assoc]
          omega

private theorem cycleCore_no_wrap (bound : Nat) :
    (cycleSize bound - 1, 0) ∉ (cycleCore bound).adjacentPairs := by
  intro member
  rcases (linearCycleWalk_cycleCore bound).2
      (cycleSize bound - 1) 0 member with same | forward
  · simp [cycleSize] at same
  · simp [cycleSize] at forward

private theorem cycleCore_wrap_count_zero (bound : Nat) :
    (cycleCore bound).adjacentPairs.count
        (cycleSize bound - 1, 0) = 0 :=
  List.count_eq_zero.mpr (cycleCore_no_wrap bound)

private theorem cycleCore_boundary_pair (bound : Nat) :
    ((cycleCore bound).final, (cycleCore bound).head) =
      (cycleSize bound - 1, 0) := by
  rw [cycleCore_final]
  simp [cycleSize, cycleCore]

private theorem cycleCore_square_wrap_count (bound : Nat) :
    (cycleCore bound ++ cycleCore bound).adjacentPairs.count
        (cycleSize bound - 1, 0) = 1 := by
  simp [Word.adjacentPairs_append, cycleCore_wrap_count_zero,
    cycleCore_boundary_pair]

private theorem cycleCore_square_boundary_pair (bound : Nat) :
    ((cycleCore bound ++ cycleCore bound).final,
        (cycleCore bound).head) =
      (cycleSize bound - 1, 0) := by
  simpa using cycleCore_boundary_pair bound

theorem cycleObstruction_lhs_windingParity (bound : Nat) :
    windingParity bound (cycleObstruction bound).lhs = 1 := by
  simp only [cycleObstruction]
  rw [windingParity_append, cycleCore_wrap_count_zero,
    cycleCore_boundary_pair]
  simp

theorem cycleObstruction_rhs_windingParity (bound : Nat) :
    windingParity bound (cycleObstruction bound).rhs = 0 := by
  simp only [cycleObstruction]
  rw [windingParity_append, cycleCore_square_wrap_count,
    cycleCore_wrap_count_zero, cycleCore_square_boundary_pair]
  simp

/-- Equality of the cycle-walk status and winding parity in every semigroup
context and after every nonempty-word substitution. -/
def ContextuallySameCycleWinding
    (bound : Nat) (left right : Word Nat) : Prop :=
  ∀ pre post substitution,
    (CycleWalkList bound
        (pre ++ (left.bind substitution).toList ++ post) ↔
      CycleWalkList bound
        (pre ++ (right.bind substitution).toList ++ post)) ∧
    (CycleWalkList bound
        (pre ++ (left.bind substitution).toList ++ post) →
      windingParityList bound
          (pre ++ (left.bind substitution).toList ++ post) =
        windingParityList bound
          (pre ++ (right.bind substitution).toList ++ post))

private theorem bind_append (left right : Word Nat)
    (substitution : Nat → Word Nat) :
    (left ++ right).bind substitution =
      left.bind substitution ++ right.bind substitution := by
  apply Word.toList_injective
  simp only [Word.toList_bind, Word.toList_append, List.flatMap_append]

private theorem bind_bind (word : Word Nat)
    (first second : Nat → Word Nat) :
    (word.bind first).bind second =
      word.bind (fun letter => (first letter).bind second) := by
  apply Word.toList_injective
  simp only [Word.toList_bind, List.flatMap_assoc]

private theorem bind_singleton (word : Word Nat) :
    word.bind Word.singleton = word := by
  apply Word.toList_injective
  rw [Word.toList_bind]
  induction word.toList with
  | nil =>
      cases word with
      | mk head tail =>
          simp [Word.toList] at *
  | cons head tail ih =>
      simp only [List.flatMap_cons, Word.toList_singleton,
        List.singleton_append]
      change List.flatMap (fun letter => [letter]) tail = tail at ih
      exact congrArg (List.cons head) ih

theorem ContextuallySameCycleWinding.refl
    (bound : Nat) (word : Word Nat) :
    ContextuallySameCycleWinding bound word word := by
  intro pre post substitution
  exact ⟨Iff.rfl, fun _ => rfl⟩

theorem ContextuallySameCycleWinding.symm
    {bound : Nat} {left right : Word Nat}
    (same : ContextuallySameCycleWinding bound left right) :
    ContextuallySameCycleWinding bound right left := by
  intro pre post substitution
  rcases same pre post substitution with ⟨walks, winding⟩
  refine ⟨walks.symm, ?_⟩
  intro rightWalk
  exact (winding (walks.mpr rightWalk)).symm

theorem ContextuallySameCycleWinding.trans
    {bound : Nat} {left middle right : Word Nat}
    (leftMiddle : ContextuallySameCycleWinding bound left middle)
    (middleRight : ContextuallySameCycleWinding bound middle right) :
    ContextuallySameCycleWinding bound left right := by
  intro pre post substitution
  rcases leftMiddle pre post substitution with
    ⟨leftMiddleWalks, leftMiddleWinding⟩
  rcases middleRight pre post substitution with
    ⟨middleRightWalks, middleRightWinding⟩
  refine ⟨leftMiddleWalks.trans middleRightWalks, ?_⟩
  intro leftWalk
  exact (leftMiddleWinding leftWalk).trans
    (middleRightWinding (leftMiddleWalks.mp leftWalk))

/-- One-step contextual cycle invariance propagates through every constructor
of equational derivability. -/
theorem Derives.contextuallySameCycleWinding
    {basis : List (Identity Nat)} {left right : Word Nat}
    (axiomPreserves :
      ∀ identity, identity ∈ basis →
        ContextuallySameCycleWinding bound identity.lhs identity.rhs)
    (derivation : Derives basis left right) :
    ContextuallySameCycleWinding bound left right := by
  induction derivation with
  | fromBasis member =>
      exact axiomPreserves _ member
  | refl word =>
      exact ContextuallySameCycleWinding.refl bound word
  | symm _ ih =>
      exact ih.symm
  | trans _ _ ihLeft ihRight =>
      exact ihLeft.trans ihRight
  | prepend p _ ih =>
      intro pre post substitution
      rw [bind_append, bind_append, Word.toList_append,
        Word.toList_append, ← List.append_assoc, ← List.append_assoc]
      exact ih
        (pre ++ (p.bind substitution).toList)
        post substitution
  | appendRight _ suffix ih =>
      intro pre post substitution
      rw [bind_append, bind_append, Word.toList_append,
        Word.toList_append]
      simpa only [List.append_assoc] using
        ih pre ((suffix.bind substitution).toList ++ post)
          substitution
  | subst _ first ih =>
      intro pre post second
      rw [bind_bind, bind_bind]
      exact ih pre post
        (fun letter => (first letter).bind second)

private def cyclePredecessor (bound gap : Nat) : Nat :=
  if gap = 0 then cycleSize bound - 1 else gap - 1

private def cycleCutEdge (bound gap : Nat) : Nat × Nat :=
  (cyclePredecessor bound gap, gap)

private theorem listAdjacentPairs_append_cons
    (leftHead : Nat) (leftTail : List Nat)
    (rightHead : Nat) (rightTail : List Nat) :
    listAdjacentPairs
        (leftHead :: (leftTail ++ rightHead :: rightTail)) =
      listAdjacentPairs (leftHead :: leftTail) ++
        (leftTail.getLastD leftHead, rightHead) ::
          listAdjacentPairs (rightHead :: rightTail) := by
  simpa [listAdjacentPairs, Word.adjacentPairs, Word.final, Word.toList] using
    Word.adjacentPairs_append
      (Word.mk leftHead leftTail) (Word.mk rightHead rightTail)

private theorem listAdjacentPairs_toList (word : Word Nat) :
    listAdjacentPairs word.toList = word.adjacentPairs := by
  cases word
  rfl

private theorem cycleCutEdge_count_flatMap
    (bound gap : Nat) (variables : List Nat)
    (substitution : Nat → Word Nat)
    (headsAvoid :
      ∀ testedVariable, testedVariable ∈ variables →
        (substitution testedVariable).head ≠ gap) :
    (listAdjacentPairs
        (variables.flatMap
          (fun testedVariable =>
            (substitution testedVariable).toList))).count
        (cycleCutEdge bound gap) =
      (variables.map
        (fun testedVariable =>
          (substitution testedVariable).adjacentPairs.count
            (cycleCutEdge bound gap))).sum := by
  induction variables with
  | nil =>
      rfl
  | cons testedVariable rest ih =>
      cases rest with
      | nil =>
          rw [List.flatMap_cons]
          simp only [List.flatMap_nil, List.append_nil, List.map_cons,
            List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
          exact congrArg
            (fun edges => edges.count (cycleCutEdge bound gap))
            (listAdjacentPairs_toList (substitution testedVariable))
      | cons next tail =>
          have nextAvoid :
              (substitution next).head ≠ gap :=
            headsAvoid next (by simp)
          have boundaryNe :
              ((substitution testedVariable).final,
                  (substitution next).head) ≠
                cycleCutEdge bound gap := by
            intro equality
            exact nextAvoid (congrArg Prod.snd equality)
          rw [List.flatMap_cons]
          change
            (listAdjacentPairs
                ((substitution testedVariable).head ::
                  ((substitution testedVariable).tail ++
                    (substitution next).head ::
                      ((substitution next).tail ++
                        tail.flatMap
                          (fun letter =>
                            (substitution letter).toList))))).count
                (cycleCutEdge bound gap) =
              _
          rw [listAdjacentPairs_append_cons, List.count_append,
            List.count_cons]
          rw [show
            listAdjacentPairs
                ((substitution testedVariable).head ::
                  (substitution testedVariable).tail) =
              (substitution testedVariable).adjacentPairs by
                exact
                  listAdjacentPairs_toList
                    (substitution testedVariable)]
          change
            (substitution testedVariable).adjacentPairs.count
                  (cycleCutEdge bound gap) +
                ((listAdjacentPairs
                    ((substitution next).head ::
                      ((substitution next).tail ++
                        tail.flatMap
                          (fun letter =>
                            (substitution letter).toList)))).count
                      (cycleCutEdge bound gap) +
                  if
                    (((substitution testedVariable).final,
                        (substitution next).head) ==
                      cycleCutEdge bound gap)
                  then 1 else 0) =
              _
          simp only [beq_iff_eq, boundaryNe, if_false, Nat.add_zero,
            List.map_cons, List.sum_cons]
          exact congrArg
            (fun count =>
              (substitution testedVariable).adjacentPairs.count
                  (cycleCutEdge bound gap) + count)
            (ih (fun letter member =>
              headsAvoid letter (by simp [member])))

private theorem mem_listAdjacentPairs_flatMap_iff
    (variables : List Nat) (substitution : Nat → Word Nat)
    (source target : Nat) :
    (source, target) ∈
        listAdjacentPairs
          (variables.flatMap
            (fun testedVariable =>
              (substitution testedVariable).toList)) ↔
      (∃ testedVariable, testedVariable ∈ variables ∧
        (source, target) ∈
          (substitution testedVariable).adjacentPairs) ∨
      (∃ leftVariable rightVariable,
        (leftVariable, rightVariable) ∈
            listAdjacentPairs variables ∧
          (source, target) =
            ((substitution leftVariable).final,
              (substitution rightVariable).head)) := by
  induction variables with
  | nil =>
      simp [listAdjacentPairs]
  | cons testedVariable rest ih =>
      cases rest with
      | nil =>
          rw [List.flatMap_cons]
          simp only [List.flatMap_nil, List.append_nil]
          rw [listAdjacentPairs_toList]
          constructor
          · intro edge
            exact Or.inl ⟨testedVariable, by simp, edge⟩
          · rintro (⟨other, member, edge⟩ |
                ⟨leftVariable, rightVariable, edge, _⟩)
            · have : other = testedVariable := by
                simpa using member
              subst other
              exact edge
            · simp [listAdjacentPairs, Word.adjacentPairsFrom] at edge
      | cons next tail =>
          have expansion :
              listAdjacentPairs
                  ((testedVariable :: next :: tail).flatMap
                    (fun letter =>
                      (substitution letter).toList)) =
                (substitution testedVariable).adjacentPairs ++
                  ((substitution testedVariable).final,
                    (substitution next).head) ::
                    listAdjacentPairs
                      ((next :: tail).flatMap
                        (fun letter =>
                          (substitution letter).toList)) := by
            rw [List.flatMap_cons]
            change
              listAdjacentPairs
                  ((substitution testedVariable).head ::
                    ((substitution testedVariable).tail ++
                      (substitution next).head ::
                        ((substitution next).tail ++
                          tail.flatMap
                            (fun letter =>
                              (substitution letter).toList)))) =
                _
            rw [listAdjacentPairs_append_cons]
            rw [show
              listAdjacentPairs
                  ((substitution testedVariable).head ::
                    (substitution testedVariable).tail) =
                (substitution testedVariable).adjacentPairs by
                  exact
                    listAdjacentPairs_toList
                      (substitution testedVariable)]
            rfl
          constructor
          · intro edge
            rw [expansion] at edge
            simp only [List.mem_append, List.mem_cons] at edge
            rcases edge with firstBlock | boundary | remaining
            · exact Or.inl
                ⟨testedVariable, by simp, firstBlock⟩
            · exact Or.inr
                ⟨testedVariable, next, by
                  simp [listAdjacentPairs, Word.adjacentPairsFrom],
                  boundary⟩
            · rcases (ih.mp remaining) with
                ⟨other, member, internal⟩ |
                ⟨leftVariable, rightVariable, pair, crossing⟩
              · exact Or.inl
                  ⟨other, by simp [member], internal⟩
              · exact Or.inr
                  ⟨leftVariable, rightVariable, by
                    simpa [listAdjacentPairs, Word.adjacentPairsFrom]
                      using Or.inr pair,
                    crossing⟩
          · rintro (⟨other, member, internal⟩ |
                ⟨leftVariable, rightVariable, pair, crossing⟩)
            · rw [expansion]
              simp only [List.mem_append, List.mem_cons]
              rcases List.eq_or_mem_of_mem_cons member with rfl | member
              · exact Or.inl internal
              · exact Or.inr (Or.inr <|
                  ih.mpr (Or.inl ⟨other, member, internal⟩))
            · rw [expansion]
              simp only [List.mem_append, List.mem_cons]
              have pairCases :
                  (leftVariable, rightVariable) =
                      (testedVariable, next) ∨
                    (leftVariable, rightVariable) ∈
                      listAdjacentPairs (next :: tail) := by
                simpa [listAdjacentPairs, Word.adjacentPairsFrom]
                  using pair
              rcases pairCases with pairHead | pairRest
              · injection pairHead with leftEq rightEq
                subst leftVariable
                subst rightVariable
                exact Or.inr (Or.inl crossing)
              · exact Or.inr (Or.inr <|
                  ih.mpr (Or.inr
                    ⟨leftVariable, rightVariable, pairRest, crossing⟩))

private theorem foldl_append_head
    (substitution : Nat → Word Nat)
    (letters : List Nat) (initial : Word Nat) :
    (letters.foldl
      (fun accumulated letter =>
        accumulated ++ substitution letter) initial).head =
      initial.head := by
  induction letters generalizing initial with
  | nil =>
      rfl
  | cons letter rest ih =>
      exact ih (initial ++ substitution letter)

private theorem foldl_append_final_ignores_prefix
    (substitution : Nat → Word Nat)
    (letters : List Nat) (prefixWord suffixWord : Word Nat) :
    (letters.foldl
      (fun accumulated letter =>
        accumulated ++ substitution letter)
        (prefixWord ++ suffixWord)).final =
      (letters.foldl
        (fun accumulated letter =>
          accumulated ++ substitution letter) suffixWord).final := by
  induction letters generalizing prefixWord suffixWord with
  | nil =>
      simp
  | cons letter rest ih =>
      simp only [List.foldl_cons]
      rw [Word.append_assoc]
      exact ih prefixWord (suffixWord ++ substitution letter)

private theorem bind_head (word : Word Nat)
    (substitution : Nat → Word Nat) :
    (word.bind substitution).head =
      (substitution word.head).head := by
  cases word with
  | mk head tail =>
      exact foldl_append_head substitution tail (substitution head)

private theorem bind_final (word : Word Nat)
    (substitution : Nat → Word Nat) :
    (word.bind substitution).final =
      (substitution word.final).final := by
  cases word with
  | mk head tail =>
      induction tail generalizing head with
      | nil =>
          rfl
      | cons next rest ih =>
          simp only [Word.bind, Word.final, List.foldl_cons,
            List.getLastD_cons]
          change
            (rest.foldl
              (fun accumulated letter =>
                accumulated ++ substitution letter)
              (substitution head ++ substitution next)).final =
              (substitution
                (rest.getLastD next)).final
          rw [foldl_append_final_ignores_prefix]
          exact ih next

private theorem sameMarkedDigraph_bind
    {left right : Word Nat}
    (same : left.SameMarkedDigraph right)
    (substitution : Nat → Word Nat) :
    (left.bind substitution).SameMarkedDigraph
      (right.bind substitution) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [bind_head, bind_head, same.initial]
  · rw [bind_final, bind_final, same.final]
  · intro testedLetter
    simp only [Word.toList_bind, List.mem_flatMap]
    constructor
    · rintro ⟨testedVariable, member, occurrence⟩
      exact
        ⟨testedVariable, (same.support testedVariable).mp member,
          occurrence⟩
    · rintro ⟨testedVariable, member, occurrence⟩
      exact
        ⟨testedVariable, (same.support testedVariable).mpr member,
          occurrence⟩
  · intro source target
    rw [← listAdjacentPairs_toList, ← listAdjacentPairs_toList]
    simp only [Word.toList_bind]
    rw [
      mem_listAdjacentPairs_flatMap_iff,
      mem_listAdjacentPairs_flatMap_iff]
    constructor
    · rintro (⟨testedVariable, member, internal⟩ |
          ⟨leftVariable, rightVariable, pair, crossing⟩)
      · exact Or.inl
          ⟨testedVariable, (same.support testedVariable).mp member,
            internal⟩
      · exact Or.inr
          ⟨leftVariable, rightVariable, by
            have leftPair :
                (leftVariable, rightVariable) ∈
                  left.adjacentPairs := by
              simpa [listAdjacentPairs_toList] using pair
            have rightPair :=
              (same.edge leftVariable rightVariable).mp leftPair
            simpa [listAdjacentPairs_toList] using rightPair,
            crossing⟩
    · rintro (⟨testedVariable, member, internal⟩ |
          ⟨leftVariable, rightVariable, pair, crossing⟩)
      · exact Or.inl
          ⟨testedVariable, (same.support testedVariable).mpr member,
            internal⟩
      · exact Or.inr
          ⟨leftVariable, rightVariable, by
            have rightPair :
                (leftVariable, rightVariable) ∈
                  right.adjacentPairs := by
              simpa [listAdjacentPairs_toList] using pair
            have leftPair :=
              (same.edge leftVariable rightVariable).mpr rightPair
            simpa [listAdjacentPairs_toList] using leftPair,
            crossing⟩

private theorem SameMarkedDigraph.prepend
    {left right : Word Nat}
    (same : left.SameMarkedDigraph right)
    (prefixWord : Word Nat) :
    (prefixWord ++ left).SameMarkedDigraph
      (prefixWord ++ right) := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · simp [same.final]
  · intro testedLetter
    simp only [Word.toList_append, List.mem_append]
    exact or_congr Iff.rfl (same.support testedLetter)
  · intro source target
    simp only [Word.adjacentPairs_append, List.mem_append,
      List.mem_cons, Prod.mk.injEq]
    rw [same.initial]
    exact or_congr Iff.rfl (or_congr Iff.rfl (same.edge source target))

private theorem SameMarkedDigraph.append
    {left right : Word Nat}
    (same : left.SameMarkedDigraph right)
    (suffixWord : Word Nat) :
    (left ++ suffixWord).SameMarkedDigraph
      (right ++ suffixWord) := by
  refine ⟨same.initial, by simp, ?_, ?_⟩
  · intro testedLetter
    simp only [Word.toList_append, List.mem_append]
    exact or_congr (same.support testedLetter) Iff.rfl
  · intro source target
    simp only [Word.adjacentPairs_append, List.mem_append,
      List.mem_cons, Prod.mk.injEq]
    rw [same.final]
    exact or_congr (same.edge source target) (or_congr Iff.rfl Iff.rfl)

private def contextWord
    (pre : List Nat) (middle : Word Nat) (post : List Nat) :
    Word Nat :=
  match pre with
  | [] => ⟨middle.head, middle.tail ++ post⟩
  | head :: tail => ⟨head, tail ++ middle.toList ++ post⟩

private theorem contextWord_toList
    (pre : List Nat) (middle : Word Nat) (post : List Nat) :
    (contextWord pre middle post).toList =
      pre ++ middle.toList ++ post := by
  cases pre <;> simp [contextWord, Word.toList]

private theorem sameMarkedDigraph_context
    {left right : Word Nat}
    (same : left.SameMarkedDigraph right)
    (pre post : List Nat) :
    (contextWord pre left post).SameMarkedDigraph
      (contextWord pre right post) := by
  cases pre with
  | nil =>
      cases post with
      | nil =>
          simpa [contextWord] using same
      | cons postHead postTail =>
          simpa [contextWord, Word.append] using
            SameMarkedDigraph.append same (Word.mk postHead postTail)
  | cons preHead preTail =>
      cases post with
      | nil =>
          simpa [contextWord, Word.append, Word.toList] using
            SameMarkedDigraph.prepend same (Word.mk preHead preTail)
      | cons postHead postTail =>
          simpa [contextWord, Word.append, Word.toList,
            Word.append_assoc] using
              SameMarkedDigraph.append
                (SameMarkedDigraph.prepend same
                  (Word.mk preHead preTail))
                (Word.mk postHead postTail)

private theorem CycleWalk.of_sameMarkedDigraph
    {bound : Nat} {left right : Word Nat}
    (same : left.SameMarkedDigraph right)
    (leftWalk : CycleWalk bound left) :
    CycleWalk bound right := by
  rw [cycleWalk_iff] at leftWalk ⊢
  constructor
  · intro testedLetter member
    exact leftWalk.1 testedLetter
      ((same.support testedLetter).mpr member)
  · intro source target member
    exact leftWalk.2 source target
      ((same.edge source target).mpr member)

private theorem adjacentPairs_count_append_mod_two
    {left right : Word Nat} (suffixWord : Word Nat)
    (edge : Nat × Nat)
    (finalEq : left.final = right.final)
    (countEq :
      left.adjacentPairs.count edge % 2 =
        right.adjacentPairs.count edge % 2) :
    (left ++ suffixWord).adjacentPairs.count edge % 2 =
      (right ++ suffixWord).adjacentPairs.count edge % 2 := by
  simp only [Word.adjacentPairs_append, List.count_append,
    List.count_cons]
  rw [finalEq]
  omega

private theorem adjacentPairs_count_prepend_mod_two
    {left right : Word Nat} (prefixWord : Word Nat)
    (edge : Nat × Nat)
    (headEq : left.head = right.head)
    (countEq :
      left.adjacentPairs.count edge % 2 =
        right.adjacentPairs.count edge % 2) :
    (prefixWord ++ left).adjacentPairs.count edge % 2 =
      (prefixWord ++ right).adjacentPairs.count edge % 2 := by
  simp only [Word.adjacentPairs_append, List.count_append,
    List.count_cons]
  rw [headEq]
  omega

private theorem contextWord_edge_count_mod_two_eq
    {left right : Word Nat} (pre post : List Nat)
    (edge : Nat × Nat)
    (headEq : left.head = right.head)
    (finalEq : left.final = right.final)
    (countEq :
      left.adjacentPairs.count edge % 2 =
        right.adjacentPairs.count edge % 2) :
    (contextWord pre left post).adjacentPairs.count edge % 2 =
      (contextWord pre right post).adjacentPairs.count edge % 2 := by
  cases pre with
  | nil =>
      cases post with
      | nil =>
          simpa [contextWord] using countEq
      | cons postHead postTail =>
          simpa [contextWord, Word.append] using
            adjacentPairs_count_append_mod_two
              (Word.mk postHead postTail) edge finalEq countEq
  | cons preHead preTail =>
      have prefixed :=
        adjacentPairs_count_prepend_mod_two
          (Word.mk preHead preTail) edge headEq countEq
      cases post with
      | nil =>
          simpa [contextWord, Word.append, Word.toList] using prefixed
      | cons postHead postTail =>
          have prefixedFinal :
              (Word.mk preHead preTail ++ left).final =
                (Word.mk preHead preTail ++ right).final := by
            simp [finalEq]
          simpa [contextWord, Word.append, Word.toList,
            Word.append_assoc] using
              adjacentPairs_count_append_mod_two
                (Word.mk postHead postTail) edge prefixedFinal prefixed

private def cutSide (gap vertex : Nat) : Nat :=
  if gap ≤ vertex then 1 else 0

private theorem cycleStep_cut_balance
    {bound gap source target : Nat}
    (gapBound : gap < cycleSize bound)
    (targetBound : target < cycleSize bound)
    (step : CycleStep bound source target) :
    ((if (source, target) = cycleCutEdge bound gap then 1 else 0) +
        (if (source, target) = (cycleSize bound - 1, 0)
          then 1 else 0)) % 2 =
      (cutSide gap source + cutSide gap target) % 2 := by
  rcases step with same | forward | wrap
  · subst target
    by_cases gapZero : gap = 0
    · subst gap
      simp [cycleCutEdge, cyclePredecessor, cutSide, cycleSize] at *
      omega
    · have gapPositive : 0 < gap := Nat.pos_of_ne_zero gapZero
      have predecessorNe : gap - 1 ≠ gap := by omega
      have lastNeZero : cycleSize bound - 1 ≠ 0 := by
        simp [cycleSize]
      have noCut :
          ¬(source = gap - 1 ∧ source = gap) := by
        intro equalities
        exact predecessorNe (equalities.1.symm.trans equalities.2)
      have noWrap :
          ¬(source = cycleSize bound - 1 ∧ source = 0) := by
        intro equalities
        exact lastNeZero (equalities.1.symm.trans equalities.2)
      by_cases onCutSide : gap ≤ source <;>
        simp [cycleCutEdge, cyclePredecessor, cutSide, gapZero,
          noCut, noWrap, onCutSide]
  · rcases forward with ⟨forwardBound, rfl⟩
    by_cases gapZero : gap = 0
    · subst gap
      simp [cycleCutEdge, cyclePredecessor, cutSide, cycleSize]
    · by_cases hitsCut : gap = source + 1
      · subst gap
        simp [cycleCutEdge, cyclePredecessor, cutSide, cycleSize,
          Nat.not_succ_le_self]
      · by_cases beforeCut : gap ≤ source
        · have noCut :
              ¬(source = gap - 1 ∧ source + 1 = gap) := by
            intro cut
            exact hitsCut cut.2.symm
          have beforeTarget : gap ≤ source + 1 :=
            Nat.le_trans beforeCut (Nat.le_succ source)
          simp [cycleCutEdge, cyclePredecessor, cutSide, gapZero,
            noCut, beforeCut, beforeTarget, cycleSize]
        · have noCut :
              ¬(source = gap - 1 ∧ source + 1 = gap) := by
            intro cut
            exact hitsCut cut.2.symm
          have targetBefore : ¬gap ≤ source + 1 := by
            omega
          simp [cycleCutEdge, cyclePredecessor, cutSide, gapZero,
            noCut, beforeCut, targetBefore, cycleSize]
  · rcases wrap with ⟨last, rfl⟩
    by_cases gapZero : gap = 0
    · subst gap
      simp [cycleCutEdge, cyclePredecessor, cutSide, cycleSize] at *
      omega
    · have gapPositive : 0 < gap := Nat.pos_of_ne_zero gapZero
      have gapLeSource : gap ≤ source := by
        omega
      have sourceLast : source = cycleSize bound - 1 := by
        simp [cycleSize] at last ⊢
        omega
      have zeroNeGap : ¬0 = gap := Ne.symm gapZero
      have gapLeLast : gap ≤ bound + 1 := by
        rw [sourceLast] at gapLeSource
        simpa [cycleSize] using gapLeSource
      simp [cycleCutEdge, cyclePredecessor, cutSide, gapZero,
        zeroNeGap, gapLeLast, sourceLast, cycleSize]

private theorem mod_two_chain
    (firstCut firstWrap remainingCut remainingWrap
      firstSide middleSide finalSide : Nat)
    (firstBalance :
      (firstCut + firstWrap) % 2 =
        (firstSide + middleSide) % 2)
    (remainingBalance :
      (remainingCut + remainingWrap) % 2 =
        (middleSide + finalSide) % 2) :
    ((remainingCut + firstCut) +
        (remainingWrap + firstWrap)) % 2 =
      (firstSide + finalSide) % 2 := by
  omega

private theorem cycleWalk_cut_balance
    (bound gap : Nat) (word : Word Nat)
    (gapBound : gap < cycleSize bound)
    (walk : CycleWalk bound word) :
    (word.adjacentPairs.count (cycleCutEdge bound gap) +
        word.adjacentPairs.count (cycleSize bound - 1, 0)) % 2 =
      (cutSide gap word.head + cutSide gap word.final) % 2 := by
  cases word with
  | mk head tail =>
      induction tail generalizing head with
      | nil =>
          by_cases onCutSide : gap ≤ head <;>
            simp [Word.adjacentPairs, Word.adjacentPairsFrom, Word.final,
              cutSide, onCutSide]
      | cons next rest ih =>
          rw [cycleWalk_iff] at walk
          have nextBound :
              next < cycleSize bound :=
            walk.1 next (by simp [Word.toList])
          have firstStep :
              CycleStep bound head next :=
            walk.2 head next (by
              simp [Word.adjacentPairs, Word.adjacentPairsFrom])
          have remainingWalk :
              CycleWalk bound (Word.mk next rest) := by
            rw [cycleWalk_iff]
            constructor
            · intro testedLetter member
              exact walk.1 testedLetter (by
                simp only [Word.toList] at member ⊢
                exact List.mem_cons_of_mem head member)
            · intro source target member
              exact walk.2 source target (by
                simp only [Word.adjacentPairs,
                  Word.adjacentPairsFrom, List.mem_cons]
                exact Or.inr member)
          have firstBalance :=
            cycleStep_cut_balance gapBound nextBound firstStep
          have remainingBalance := ih next remainingWalk
          simp only [Word.adjacentPairs, Word.adjacentPairsFrom,
            List.count_cons, beq_iff_eq, Word.final,
            List.getLastD_cons] at remainingBalance ⊢
          exact mod_two_chain _ _ _ _ _ _ _
            firstBalance remainingBalance

private theorem cycleWalk_windingParity_eq_of_cut
    {bound gap : Nat} {left right : Word Nat}
    (gapBound : gap < cycleSize bound)
    (headEq : left.head = right.head)
    (finalEq : left.final = right.final)
    (leftWalk : CycleWalk bound left)
    (rightWalk : CycleWalk bound right)
    (cutEq :
      left.adjacentPairs.count (cycleCutEdge bound gap) % 2 =
        right.adjacentPairs.count (cycleCutEdge bound gap) % 2) :
    windingParity bound left = windingParity bound right := by
  have leftBalance :=
    cycleWalk_cut_balance bound gap left gapBound leftWalk
  have rightBalance :=
    cycleWalk_cut_balance bound gap right gapBound rightWalk
  rw [headEq, finalEq] at leftBalance
  simp only [windingParity, windingParityList,
    listAdjacentPairs_toList]
  omega

private theorem exists_lt_not_mem_of_length_lt
    (forbidden : List Nat) (size : Nat)
    (short : forbidden.length < size) :
    ∃ gap, gap < size ∧ gap ∉ forbidden := by
  induction size generalizing forbidden with
  | zero =>
      omega
  | succ size ih =>
      by_cases lastUsed : size ∈ forbidden
      · have erasedShort : (forbidden.erase size).length < size := by
          have positive := List.length_pos_of_mem lastUsed
          rw [List.length_erase_of_mem lastUsed]
          omega
        rcases ih (forbidden.erase size) erasedShort with
          ⟨gap, gapBound, gapUnused⟩
        refine ⟨gap, by omega, ?_⟩
        intro gapUsed
        exact gapUnused
          ((List.mem_erase_of_ne (Nat.ne_of_lt gapBound)).mpr gapUsed)
      · exact ⟨size, Nat.lt_succ_self size, lastUsed⟩

private theorem weighted_sum_mod_two_eq_parityReduce
    (weight : Nat → Nat) (letters : List Nat) :
    (letters.map weight).sum % 2 =
      ((Examples.parityReduce letters).map weight).sum % 2 := by
  induction letters with
  | nil =>
      rfl
  | cons letter rest ih =>
      simp only [Examples.parityReduce]
      by_cases member : letter ∈ Examples.parityReduce rest
      · rw [if_pos member]
        have reordered :=
          List.perm_cons_erase member
        have mappedSum :
            ((Examples.parityReduce rest).map weight).sum =
              weight letter +
                (((Examples.parityReduce rest).erase letter).map weight).sum := by
          exact (reordered.map weight).sum_nat
        simp only [List.map_cons, List.sum_cons]
        omega
      · rw [if_neg member]
        simp only [List.map_cons, List.sum_cons]
        omega

private theorem weighted_sum_mod_two_eq_of_sameParity
    (weight : Nat → Nat) {left right : Word Nat}
    (same : left.SameParity right) :
    (left.toList.map weight).sum % 2 =
      (right.toList.map weight).sum % 2 := by
  calc
    (left.toList.map weight).sum % 2 =
        ((Examples.parityReduce left.toList).map weight).sum % 2 :=
      weighted_sum_mod_two_eq_parityReduce weight left.toList
    _ = ((Examples.parityReduce right.toList).map weight).sum % 2 :=
      congrArg (fun total => total % 2) <|
        (Examples.parityReduce_perm_of_parity_eq same).map weight |>.sum_nat
    _ = (right.toList.map weight).sum % 2 :=
      (weighted_sum_mod_two_eq_parityReduce weight right.toList).symm

private theorem bind_cycleCutEdge_count_mod_two_eq
    {left right : Word Nat}
    (sameParity : left.SameParity right)
    (bound gap : Nat) (substitution : Nat → Word Nat)
    (leftHeadsAvoid :
      ∀ testedVariable, testedVariable ∈ left.toList →
        (substitution testedVariable).head ≠ gap)
    (rightHeadsAvoid :
      ∀ testedVariable, testedVariable ∈ right.toList →
        (substitution testedVariable).head ≠ gap) :
    (left.bind substitution).adjacentPairs.count
          (cycleCutEdge bound gap) % 2 =
      (right.bind substitution).adjacentPairs.count
          (cycleCutEdge bound gap) % 2 := by
  rw [← listAdjacentPairs_toList, ← listAdjacentPairs_toList]
  simp only [Word.toList_bind]
  rw [cycleCutEdge_count_flatMap bound gap left.toList substitution
      leftHeadsAvoid,
    cycleCutEdge_count_flatMap bound gap right.toList substitution
      rightHeadsAvoid]
  exact weighted_sum_mod_two_eq_of_sameParity
    (fun testedVariable =>
      (substitution testedVariable).adjacentPairs.count
        (cycleCutEdge bound gap))
    sameParity

/-- The exact remaining graph-combinatorics lemma, in one orientation.  If
one contextual substitution instance of a bounded graph-plus-parity identity
is a walk on the target cycle, then the other side is also such a walk and has
the same winding parity.  There is no basis, derivation, semigroup, symmetry
requirement, or nonfinite-basis conclusion in this statement. -/
def BoundedGraphParityCycleRewrite : Prop :=
  ∀ bound (identity : Identity Nat) pre post substitution,
    identity.GraphParityEquivalent →
    identity.UsesAtMost bound →
    CycleWalkList bound
      (pre ++ (identity.lhs.bind substitution).toList ++ post) →
    CycleWalkList bound
        (pre ++ (identity.rhs.bind substitution).toList ++ post) ∧
      windingParityList bound
          (pre ++ (identity.lhs.bind substitution).toList ++ post) =
      windingParityList bound
          (pre ++ (identity.rhs.bind substitution).toList ++ post)

/-- The bounded graph-plus-parity rewrite lemma.  The variable bound leaves an
unused cycle vertex among the heads of the substituted variables.  Counting
crossings at that cut reduces to the parity condition, and cycle-flow balance
transfers the result to the distinguished wrap edge. -/
theorem boundedGraphParityCycleRewrite :
    BoundedGraphParityCycleRewrite := by
  intro bound identity pre post substitution graphParity uses leftWalkList
  rcases uses with
    ⟨variables, variablesBound, leftOnly, rightOnly⟩
  let forbiddenHeads :=
    variables.map (fun testedVariable =>
      (substitution testedVariable).head)
  have forbiddenShort :
      forbiddenHeads.length < cycleSize bound := by
    simp only [forbiddenHeads, List.length_map, cycleSize]
    omega
  rcases exists_lt_not_mem_of_length_lt
      forbiddenHeads (cycleSize bound) forbiddenShort with
    ⟨gap, gapBound, gapUnused⟩
  have leftHeadsAvoid :
      ∀ testedVariable, testedVariable ∈ identity.lhs.toList →
        (substitution testedVariable).head ≠ gap := by
    intro testedVariable member equality
    apply gapUnused
    exact List.mem_map.mpr
      ⟨testedVariable, leftOnly testedVariable member, equality⟩
  have rightHeadsAvoid :
      ∀ testedVariable, testedVariable ∈ identity.rhs.toList →
        (substitution testedVariable).head ≠ gap := by
    intro testedVariable member equality
    apply gapUnused
    exact List.mem_map.mpr
      ⟨testedVariable, rightOnly testedVariable member, equality⟩
  have sameBind :
      (identity.lhs.bind substitution).SameMarkedDigraph
        (identity.rhs.bind substitution) :=
    sameMarkedDigraph_bind graphParity.1 substitution
  let leftContext :=
    contextWord pre (identity.lhs.bind substitution) post
  let rightContext :=
    contextWord pre (identity.rhs.bind substitution) post
  have sameContext :
      leftContext.SameMarkedDigraph rightContext := by
    exact sameMarkedDigraph_context sameBind pre post
  have leftWalk : CycleWalk bound leftContext := by
    simpa [leftContext, CycleWalk, contextWord_toList] using leftWalkList
  have rightWalk : CycleWalk bound rightContext :=
    CycleWalk.of_sameMarkedDigraph sameContext leftWalk
  have bindCutEq :
      (identity.lhs.bind substitution).adjacentPairs.count
            (cycleCutEdge bound gap) % 2 =
        (identity.rhs.bind substitution).adjacentPairs.count
            (cycleCutEdge bound gap) % 2 :=
    bind_cycleCutEdge_count_mod_two_eq graphParity.2
      bound gap substitution leftHeadsAvoid rightHeadsAvoid
  have contextCutEq :
      leftContext.adjacentPairs.count (cycleCutEdge bound gap) % 2 =
        rightContext.adjacentPairs.count (cycleCutEdge bound gap) % 2 := by
    exact contextWord_edge_count_mod_two_eq pre post
      (cycleCutEdge bound gap) sameBind.initial sameBind.final bindCutEq
  have windingEq :
      windingParity bound leftContext =
        windingParity bound rightContext := by
    exact cycleWalk_windingParity_eq_of_cut gapBound
      sameContext.initial sameContext.final leftWalk rightWalk contextCutEq
  refine ⟨?_, ?_⟩
  · simpa [rightContext, CycleWalk, contextWord_toList] using rightWalk
  · simpa [leftContext, rightContext, windingParity,
      contextWord_toList] using windingEq

/-- Symmetric one-step contextual preservation used by derivation closure. -/
def BoundedGraphParityWindingPreservation : Prop :=
  ∀ bound (identity : Identity Nat),
    identity.GraphParityEquivalent →
    identity.UsesAtMost bound →
    ContextuallySameCycleWinding bound identity.lhs identity.rhs

private def swapIdentity (identity : Identity Nat) : Identity Nat :=
  ⟨identity.rhs, identity.lhs⟩

private theorem swapIdentity_graphParity
    {identity : Identity Nat}
    (graphParity : identity.GraphParityEquivalent) :
    (swapIdentity identity).GraphParityEquivalent := by
  refine ⟨?_, ?_⟩
  · exact
      ⟨graphParity.1.initial.symm,
        graphParity.1.final.symm,
        fun letter => (graphParity.1.support letter).symm,
        fun source target => (graphParity.1.edge source target).symm⟩
  · intro letter
    exact (graphParity.2 letter).symm

private theorem swapIdentity_usesAtMost
    {identity : Identity Nat}
    (uses : identity.UsesAtMost bound) :
    (swapIdentity identity).UsesAtMost bound := by
  rcases uses with ⟨variables, lengthBound, leftOnly, rightOnly⟩
  exact ⟨variables, lengthBound, rightOnly, leftOnly⟩

/-- The oriented one-step lemma supplies the symmetric form needed by the
derivation induction. -/
theorem windingPreservation_of_cycleRewrite
    (rewrite : BoundedGraphParityCycleRewrite) :
    BoundedGraphParityWindingPreservation := by
  intro bound identity graphParity uses pre post substitution
  constructor
  · constructor
    · intro leftWalk
      exact (rewrite bound identity pre post substitution
        graphParity uses leftWalk).1
    · intro rightWalk
      exact (rewrite bound (swapIdentity identity) pre post substitution
        (swapIdentity_graphParity graphParity)
        (swapIdentity_usesAtMost uses) rightWalk).1
  · intro leftWalk
    exact (rewrite bound identity pre post substitution
      graphParity uses leftWalk).2

/-- The sole combinatorial nonredundancy statement needed after the explicit
witness family and all finite-basis bookkeeping have been formalized.

It says that graph-plus-parity identities using at most `bound` variables
cannot derive the `(bound + 2)`-variable member of the cycle series.  This is
strictly narrower than assuming that `A₂ × C₂` or AC2 is nonfinitely based.
-/
def BoundedCycleUnderivability : Prop :=
  ∀ bound basis,
    (∀ identity : Identity Nat, identity ∈ basis →
      identity.GraphParityEquivalent) →
    BasisUsesAtMost basis bound →
    ¬Derives basis (cycleObstruction bound).lhs
      (cycleObstruction bound).rhs

/-- The one-step winding lemma implies the full bounded derivational
underivability statement.  The induction over arbitrary derivations and the
separation of the two obstruction words are both checked here. -/
theorem boundedCycleUnderivability_of_windingPreservation
    (preservation : BoundedGraphParityWindingPreservation) :
    BoundedCycleUnderivability := by
  intro bound basis basisGraphParity basisBounded derivation
  have axiomPreserves :
      ∀ identity, identity ∈ basis →
        ContextuallySameCycleWinding bound
          identity.lhs identity.rhs := by
    intro identity member
    exact preservation bound identity
      (basisGraphParity identity member)
      (basisBounded identity member)
  have invariant :=
    Derives.contextuallySameCycleWinding
      axiomPreserves derivation
      ([] : List Nat) ([] : List Nat) Word.singleton
  have lhsWalk :
      CycleWalkList bound (cycleObstruction bound).lhs.toList := by
    exact cycleObstruction_lhs_cycleWalk bound
  have windingEquality :
      windingParity bound (cycleObstruction bound).lhs =
        windingParity bound (cycleObstruction bound).rhs := by
    simpa [bind_singleton, windingParity] using
      invariant.2 (by
        simpa [bind_singleton] using lhsWalk)
  rw [cycleObstruction_lhs_windingParity,
    cycleObstruction_rhs_windingParity] at windingEquality
  omega

/-- Direct public reduction from the sole oriented graph lemma to bounded
underivability. -/
theorem boundedCycleUnderivability_of_cycleRewrite
    (rewrite : BoundedGraphParityCycleRewrite) :
    BoundedCycleUnderivability :=
  boundedCycleUnderivability_of_windingPreservation
    (windingPreservation_of_cycleRewrite rewrite)

/-- Unconditional bounded underivability for the graph-plus-parity cycle
obstructions. -/
theorem boundedCycleUnderivability :
    BoundedCycleUnderivability :=
  boundedCycleUnderivability_of_cycleRewrite
    boundedGraphParityCycleRewrite

/-- A concrete finite countermodel package for one variable bound.  Such a
model satisfies every graph-plus-parity identity using at most `bound`
variables but refutes the next cycle identity. -/
structure BoundedCycleCountermodel (bound : Nat) where
  order : Nat
  semigroup : Semigroup (Fin order)
  modelsBounded :
    ∀ identity : Identity Nat,
      identity.GraphParityEquivalent →
      identity.UsesAtMost bound →
      identity.SatisfiedBy semigroup
  refutesCycle :
    ¬(cycleObstruction bound).SatisfiedBy semigroup

/-- Constructive finite-model form of the remaining Volkov obstruction. -/
def FiniteBoundedCycleCountermodels : Prop :=
  ∀ bound, Nonempty (BoundedCycleCountermodel bound)

/-- Finite countermodels imply the exact derivational nonredundancy statement.
All soundness and finite-basis bookkeeping is internal to Lean. -/
theorem boundedCycleUnderivability_of_finiteCountermodels
    (countermodels : FiniteBoundedCycleCountermodels) :
    BoundedCycleUnderivability := by
  intro bound basis basisGraphParity basisBounded derivation
  rcases countermodels bound with ⟨countermodel⟩
  apply countermodel.refutesCycle
  intro valuation
  have basisModels : Models countermodel.semigroup basis := by
    intro identity member
    exact countermodel.modelsBounded identity
      (basisGraphParity identity member)
      (basisBounded identity member)
  exact Derives.sound basisModels derivation valuation

/-- The explicit bounded-cycle obstruction implies nonfinite basability of the
abstract graph-plus-parity identity theory. -/
theorem graphParityNonfinitelyBased_of_boundedCycleUnderivability
    (underivable : BoundedCycleUnderivability) :
    GraphParityNonfinitelyBased Nat := by
  rintro ⟨basis, basisGraphParity, basisComplete⟩
  let bound := (basisVariables basis).length
  exact underivable bound basis basisGraphParity
    (basis_usesAtMost_basisVariables basis)
    (basisComplete (cycleObstruction bound)
      (cycleObstruction_graphParity bound))

/-- Public one-step route: bounded contextual winding preservation is the only
remaining combinatorial premise for nonfinite basability of the abstract
graph-plus-parity theory. -/
theorem graphParityNonfinitelyBased_of_windingPreservation
    (preservation : BoundedGraphParityWindingPreservation) :
    GraphParityNonfinitelyBased Nat :=
  graphParityNonfinitelyBased_of_boundedCycleUnderivability
    (boundedCycleUnderivability_of_windingPreservation preservation)

/-- Public route from the sole oriented graph lemma to nonfinite basability of
the abstract graph-plus-parity theory. -/
theorem graphParityNonfinitelyBased_of_cycleRewrite
    (rewrite : BoundedGraphParityCycleRewrite) :
    GraphParityNonfinitelyBased Nat :=
  graphParityNonfinitelyBased_of_windingPreservation
    (windingPreservation_of_cycleRewrite rewrite)

/-- The abstract graph-plus-parity identity theory is nonfinitely based. -/
theorem graphParityNonfinitelyBased :
    GraphParityNonfinitelyBased Nat :=
  graphParityNonfinitelyBased_of_cycleRewrite
    boundedGraphParityCycleRewrite

end AC2Cycle

end SemigroupBasis
