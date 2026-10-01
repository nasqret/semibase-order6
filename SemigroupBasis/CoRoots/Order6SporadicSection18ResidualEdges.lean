import SemigroupBasis.CoRoots.Order6SporadicSection18EdgeCut

/-! Residual edge ownership after a COMMON literal prefix. BZ's slot
permutation supplies destinations, and its preceding-gap theorem supplies the
predecessor block. The edge set is derived from semantics, not assumed. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical
open SemigroupBasis

theorem stepEdges_spec (current : Slot) (rest : List Slot) (previous : List Nat) (slot : Slot) :
    (previous, slot) ∈ stepEdges current.block rest ↔
      ∃ before predecessor after,
        current :: rest = before ++ predecessor :: slot :: after ∧ predecessor.block = previous := by
  induction rest generalizing current with
  | nil =>
      constructor
      · intro impossible
        cases impossible
      · rintro ⟨before, predecessor, after, shape, _⟩
        have lengths := congrArg List.length shape
        simp only [List.length_cons, List.length_nil, List.length_append] at lengths
        omega
  | cons head tail ih =>
      constructor
      · intro member
        rcases List.mem_cons.mp member with equal | member
        · have slotEqual : slot = head := congrArg Prod.snd equal
          have previousEqual : previous = current.block := congrArg Prod.fst equal
          subst slot
          exact ⟨[], current, tail, rfl, previousEqual.symm⟩
        · obtain ⟨before, predecessor, after, shape, blockEqual⟩ := (ih head).mp member
          exact ⟨current :: before, predecessor, after, congrArg (List.cons current) shape, blockEqual⟩
      · rintro ⟨before, predecessor, after, shape, blockEqual⟩
        cases before with
        | nil =>
            have firstEqual : current = predecessor := (List.cons.inj shape).1
            have tailEqual : head :: tail = slot :: after := (List.cons.inj shape).2
            have headEqual : head = slot := (List.cons.inj tailEqual).1
            have block : current.block = previous := (congrArg Slot.block firstEqual).trans blockEqual
            have pairEqual : (previous, slot) = (current.block, head) := by rw [block, headEqual]
            exact List.mem_cons.mpr (Or.inl pairEqual)
        | cons front beforeTail =>
            have tailShape : head :: tail = beforeTail ++ predecessor :: slot :: after := (List.cons.inj shape).2
            exact List.mem_cons.mpr (Or.inr ((ih head).mpr ⟨beforeTail, predecessor, after, tailShape, blockEqual⟩))

theorem stepEdge_predecessor_exists (start : List Nat) (chain : List Slot) (slot : Slot) (member : slot ∈ chain) :
    ∃ previous, (previous, slot) ∈ stepEdges start chain := by
  induction chain generalizing start with
  | nil => cases member
  | cons head tail ih =>
      rcases List.mem_cons.mp member with equal | member
      · subst slot
        exact ⟨start, List.Mem.head _⟩
      · obtain ⟨previous, edge⟩ := ih head.block member
        exact ⟨previous, List.Mem.tail (start, head) edge⟩

theorem perm_cancel_prefix (before left right : List Slot)
    (permutation : (before ++ left).Perm (before ++ right)) : left.Perm right := by
  induction before with
  | nil => exact permutation
  | cons head tail ih =>
      exact ih (List.Perm.cons_inv permutation)

theorem canonicalResidualPermutation {left right : Word Nat}
    {leftAlphabet rightAlphabet : List Nat} {leftFirst rightFirst : Slot} {leftRest rightRest : List Slot}
    (same : Actual.SameEval left.toList right.toList)
    (leftWitness : CanonicalWitness left.toList leftAlphabet leftFirst leftRest)
    (rightWitness : CanonicalWitness right.toList rightAlphabet rightFirst rightRest)
    (common : List Slot) (current : Slot) (leftTail rightTail : List Slot)
    (leftShape : leftFirst :: leftRest = common ++ current :: leftTail)
    (rightShape : rightFirst :: rightRest = common ++ current :: rightTail) : leftTail.Perm rightTail := by
  have permutation := canonicalChainPermutation same leftWitness rightWitness
  rw [leftShape, rightShape] at permutation
  exact List.Perm.cons_inv (perm_cancel_prefix common (current :: leftTail) (current :: rightTail) permutation)

theorem CanonicalWitness.residual_edge_inclusion {left right leftAlphabet rightAlphabet : List Nat}
    {leftFirst rightFirst : Slot} {leftRest rightRest : List Slot}
    (leftWitness : CanonicalWitness left leftAlphabet leftFirst leftRest)
    (rightWitness : CanonicalWitness right rightAlphabet rightFirst rightRest)
    (same : Actual.SameEval left right)
    (common : List Slot) (current : Slot) (leftTail rightTail : List Slot)
    (leftShape : leftFirst :: leftRest = common ++ current :: leftTail)
    (rightShape : rightFirst :: rightRest = common ++ current :: rightTail)
    (covers : ∀ slot ∈ leftTail, slot ∈ rightTail) :
    ∀ edge ∈ stepEdges current.block leftTail, edge ∈ stepEdges current.block rightTail := by
  rintro ⟨previous, slot⟩ member
  obtain ⟨leftBefore, leftPrevious, leftAfter, localLeft, previousEqual⟩ :=
    (stepEdges_spec current leftTail previous slot).mp member
  have rightMember := covers slot (stepEdge_target_mem member)
  obtain ⟨rightLabel, rightEdge⟩ := stepEdge_predecessor_exists current.block rightTail slot rightMember
  obtain ⟨rightBefore, rightPrevious, rightAfter, localRight, rightEqual⟩ :=
    (stepEdges_spec current rightTail rightLabel slot).mp rightEdge
  have globalLeft : leftFirst :: leftRest = (common ++ leftBefore) ++ leftPrevious :: slot :: leftAfter := by
    rw [leftShape, localLeft]
    simp only [List.append_assoc]
  have globalRight : rightFirst :: rightRest = (common ++ rightBefore) ++ rightPrevious :: slot :: rightAfter := by
    rw [rightShape, localRight]
    simp only [List.append_assoc]
  have equal := leftWitness.same_block_before_equal_gap rightWitness same
    (common ++ leftBefore) leftPrevious slot leftAfter (common ++ rightBefore) rightPrevious slot rightAfter
    globalLeft globalRight rfl
  have labelEqual : previous = rightLabel := previousEqual.symm.trans (equal.trans rightEqual)
  rw [labelEqual]
  exact rightEdge

theorem canonicalResidualEdgeMembership {left right : Word Nat}
    {leftAlphabet rightAlphabet : List Nat} {leftFirst rightFirst : Slot} {leftRest rightRest : List Slot}
    (same : Actual.SameEval left.toList right.toList)
    (leftWitness : CanonicalWitness left.toList leftAlphabet leftFirst leftRest)
    (rightWitness : CanonicalWitness right.toList rightAlphabet rightFirst rightRest)
    (common : List Slot) (current : Slot) (leftTail rightTail : List Slot)
    (leftShape : leftFirst :: leftRest = common ++ current :: leftTail)
    (rightShape : rightFirst :: rightRest = common ++ current :: rightTail) (edge : List Nat × Slot) :
    edge ∈ stepEdges current.block leftTail ↔ edge ∈ stepEdges current.block rightTail := by
  have permutation := canonicalResidualPermutation same leftWitness rightWitness common current leftTail rightTail leftShape rightShape
  exact ⟨leftWitness.residual_edge_inclusion rightWitness same common current leftTail rightTail leftShape rightShape
      (fun slot member => permutation.mem_iff.mp member) edge,
    rightWitness.residual_edge_inclusion leftWitness same.symm common current rightTail leftTail rightShape leftShape
      (fun slot member => permutation.mem_iff.mpr member) edge⟩

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.stepEdges_spec
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.stepEdge_predecessor_exists
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.perm_cancel_prefix
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.canonicalResidualPermutation
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.CanonicalWitness.residual_edge_inclusion
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.canonicalResidualEdgeMembership

end SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical
