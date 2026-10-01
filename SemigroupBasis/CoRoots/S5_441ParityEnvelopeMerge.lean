import SemigroupBasis.CoRoots.S5_441ParityEnvelopeReplay

namespace SemigroupBasis.CoRoots.S5_441

open SemigroupBasis
open SemigroupBasis.Examples

/-- Empty-trailing odd/even anchor switch:
`A A B B A -> B A B`. This is the reverse of the primitive
`B A B -> A A B B A`, so two copies of the old anchor are removed. -/
theorem derivesOddEvenAnchorSwitch
    (oldAnchor newAnchor : Word Nat) :
    Derives basis
      ((((oldAnchor ++ oldAnchor) ++ newAnchor) ++ newAnchor) ++
        oldAnchor)
      ((newAnchor ++ oldAnchor) ++ newAnchor) := by
  simpa [Word.append_assoc] using
    (derivesXYXToYYXXY newAnchor oldAnchor).symm

/-- Empty-trailing even/odd anchor switch:
`A B A -> B B A A B`. It is the forward primitive used above. -/
theorem derivesEvenOddAnchorSwitch
    (oldAnchor newAnchor : Word Nat) :
    Derives basis
      ((oldAnchor ++ newAnchor) ++ oldAnchor)
      ((((newAnchor ++ newAnchor) ++ oldAnchor) ++ oldAnchor) ++
        newAnchor) := by
  simpa [Word.append_assoc] using
    derivesXYXToYYXXY oldAnchor newAnchor

/-- List-level odd/even anchor switch with a possibly empty trailing list.
The empty case uses `derivesOddEvenAnchorSwitch`; a nonempty list is packed
into a word and delegated to the existing mixed-parity API. -/
theorem listDerivesOddEvenAnchorSwitch
    (oldAnchor newAnchor : Word Nat) (trailing : List Nat) :
    ListDerives
      (oldAnchor.toList ++ oldAnchor.toList ++ newAnchor.toList ++
        newAnchor.toList ++ trailing ++ oldAnchor.toList)
      (newAnchor.toList ++ oldAnchor.toList ++ trailing ++
        newAnchor.toList) := by
  cases trailing with
  | nil =>
      simpa [Word.toList_append, List.append_assoc] using
        (ListDerives.ofWord
          (derivesOddEvenAnchorSwitch oldAnchor newAnchor))
  | cons trailingHead trailingTail =>
      let trailingWord :=
        S5_107.listWordOfCons trailingHead trailingTail
      simpa [trailingWord, S5_107.listWordOfCons, Word.toList,
        List.append_assoc] using
          listDerivesOddEvenAnchorSwitchWords
            oldAnchor newAnchor trailingWord

/-- Apply the optional-trailing odd/even switch in arbitrary list contexts. -/
theorem listDerivesOddEvenAnchorSwitchWithOptionalTrailingContext
    (pre suffix : List Nat)
    (oldAnchor newAnchor : Word Nat) (trailing : List Nat) :
    ListDerives
      (pre ++ oldAnchor.toList ++ oldAnchor.toList ++
        newAnchor.toList ++ newAnchor.toList ++ trailing ++
        oldAnchor.toList ++ suffix)
      (pre ++ newAnchor.toList ++ oldAnchor.toList ++ trailing ++
        newAnchor.toList ++ suffix) := by
  simpa [List.append_assoc] using
    ListDerives.context pre suffix
      (listDerivesOddEvenAnchorSwitch
        oldAnchor newAnchor trailing)

/-- List-level even/odd anchor switch with a possibly empty trailing list. -/
theorem listDerivesEvenOddAnchorSwitch
    (oldAnchor newAnchor : Word Nat) (trailing : List Nat) :
    ListDerives
      (oldAnchor.toList ++ newAnchor.toList ++ trailing ++
        oldAnchor.toList)
      (newAnchor.toList ++ newAnchor.toList ++ oldAnchor.toList ++
        oldAnchor.toList ++ trailing ++ newAnchor.toList) := by
  cases trailing with
  | nil =>
      simpa [Word.toList_append, List.append_assoc] using
        (ListDerives.ofWord
          (derivesEvenOddAnchorSwitch oldAnchor newAnchor))
  | cons trailingHead trailingTail =>
      let trailingWord :=
        S5_107.listWordOfCons trailingHead trailingTail
      simpa [trailingWord, S5_107.listWordOfCons, Word.toList,
        List.append_assoc] using
          listDerivesEvenOddAnchorSwitchWords
            oldAnchor newAnchor trailingWord

/-- Apply the optional-trailing even/odd switch in arbitrary list contexts. -/
theorem listDerivesEvenOddAnchorSwitchWithOptionalTrailingContext
    (pre suffix : List Nat)
    (oldAnchor newAnchor : Word Nat) (trailing : List Nat) :
    ListDerives
      (pre ++ oldAnchor.toList ++ newAnchor.toList ++ trailing ++
        oldAnchor.toList ++ suffix)
      (pre ++ newAnchor.toList ++ newAnchor.toList ++
        oldAnchor.toList ++ oldAnchor.toList ++ trailing ++
        newAnchor.toList ++ suffix) := by
  simpa [List.append_assoc] using
    ListDerives.context pre suffix
      (listDerivesEvenOddAnchorSwitch
        oldAnchor newAnchor trailing)

private theorem parityEnvelopeFirst_mem_left
    {first : Nat} {tail left right : List Nat}
    (shape : first :: tail = left ++ right)
    (leftNonempty : left ≠ []) :
    first ∈ left := by
  cases left with
  | nil => contradiction
  | cons leftHead leftTail =>
      change first :: tail =
        leftHead :: (leftTail ++ right) at shape
      cases shape
      exact List.Mem.head _

private theorem parityEnvelopeLast_mem_right
    {last : Nat} {body left right : List Nat}
    (shape : body ++ [last] = left ++ right)
    (rightNonempty : right ≠ []) :
    last ∈ right := by
  have reversed :
      last :: body.reverse =
        right.reverse ++ left.reverse := by
    simpa [List.reverse_append] using
      congrArg List.reverse shape
  have rightReverseNonempty : right.reverse ≠ [] := by
    simpa using rightNonempty
  have member :=
    parityEnvelopeFirst_mem_left
      reversed rightReverseNonempty
  simpa using member

/-- Every closed parity envelope is support-connected, independently of its
interior: its endpoint crosses every nontrivial cut. -/
theorem parityEnvelopeRender_supportConnected
    (endpoint : Nat) (interior : List Nat) :
    ConnectedComponentSupportConnected
      (parityEnvelopeRender endpoint interior []) := by
  intro left right shape leftNonempty rightNonempty
  refine ⟨endpoint, ?_, ?_⟩
  · exact
      parityEnvelopeFirst_mem_left
        (first := endpoint)
        (tail := interior ++ [endpoint])
        (by simpa [parityEnvelopeRender] using shape)
        leftNonempty
  · exact
      parityEnvelopeLast_mem_right
        (last := endpoint)
        (body := endpoint :: interior)
        (by
          simpa [parityEnvelopeRender, List.append_assoc] using shape)
        rightNonempty

/-- Two adjacent closed envelopes form exactly the replay state for the first
endpoint iff their supports overlap. This is the boundary condition that
excludes a preserved support-disjoint exact cut. -/
theorem parityEnvelopeState_adjacent_iff
    (a b : Nat) (p q : List Nat) :
    ParityEnvelopeState a p
        (parityEnvelopeRender b q []) ↔
      ConnectedComponentSupportsIntersect
        (parityEnvelopeRender a p [])
        (parityEnvelopeRender b q []) := by
  constructor
  · intro state
    have overlap :=
      state.linked [] (parityEnvelopeRender b q [])
        (by simp) (by simp [parityEnvelopeRender])
    simpa [parityEnvelopeRender, List.append_assoc] using overlap
  · intro overlap
    refine ⟨?_⟩
    intro left right shape rightNonempty
    by_cases leftEmpty : left = []
    · subst left
      simp only [List.nil_append] at shape
      subst right
      simpa [parityEnvelopeRender, List.append_assoc] using overlap
    · obtain ⟨letter, leftMember, rightMember⟩ :=
        parityEnvelopeRender_supportConnected b q
          left right shape leftEmpty rightNonempty
      exact
        ⟨letter,
          List.mem_append_right
            (a :: p ++ [a]) leftMember,
          rightMember⟩

/-- The generic adjacent-envelope merge target is an exact permutation of
the source. In particular, it preserves every occurrence count. -/
theorem adjacentParityEnvelopeMerge_perm
    (a b : Nat) (p q : List Nat) :
    ([a] ++ p ++ [a] ++ [b] ++ q ++ [b]).Perm
      ([a] ++ p ++ [b, b] ++ q ++ [a]) := by
  rw [List.perm_iff_count]
  intro tested
  simp only [List.count_append, List.count_cons, List.count_nil]
  omega

/-- Exact occurrence-count preservation for the adjacent merge shape. -/
theorem adjacentParityEnvelopeMerge_count_eq
    (a b tested : Nat) (p q : List Nat) :
    ([a] ++ p ++ [a] ++ [b] ++ q ++ [b]).count tested =
      ([a] ++ p ++ [b, b] ++ q ++ [a]).count tested :=
  List.perm_iff_count.mp
    (adjacentParityEnvelopeMerge_perm a b p q) tested

/-- Coordinatewise parity preservation for the adjacent merge shape. -/
theorem adjacentParityEnvelopeMerge_count_mod_two_eq
    (a b tested : Nat) (p q : List Nat) :
    ([a] ++ p ++ [a] ++ [b] ++ q ++ [b]).count tested % 2 =
      ([a] ++ p ++ [b, b] ++ q ++ [a]).count tested % 2 :=
  congrArg (fun count => count % 2)
    (adjacentParityEnvelopeMerge_count_eq
      a b tested p q)

/-- Merge two adjacent support-overlapping envelopes into one envelope with
endpoint `a`:

`a p a b q b -> a p b b q a`.

The overlap hypothesis is the minimal replay bridge at the boundary. The
derivation first absorbs the second envelope into an arbitrary final
`a`-envelope, then uses exact replay counts and interior permutation to select
the displayed target. No occurrence is added or removed. -/
theorem listDerivesAdjacentParityEnvelopeMerge
    (a b : Nat) (p q : List Nat)
    (overlap :
      ConnectedComponentSupportsIntersect
        ([a] ++ p ++ [a])
        ([b] ++ q ++ [b])) :
    ListDerives
      ([a] ++ p ++ [a] ++ [b] ++ q ++ [b])
      ([a] ++ p ++ [b, b] ++ q ++ [a]) := by
  have renderedOverlap :
      ConnectedComponentSupportsIntersect
        (parityEnvelopeRender a p [])
        (parityEnvelopeRender b q []) := by
    simpa [parityEnvelopeRender, List.append_assoc] using overlap
  have state :
      ParityEnvelopeState a p
        (parityEnvelopeRender b q []) :=
    (parityEnvelopeState_adjacent_iff a b p q).2
      renderedOverlap
  obtain ⟨finalInterior, plan, replay⟩ :=
    state.exists_replay
  have sourceTarget :
      (parityEnvelopeRender a p
          (parityEnvelopeRender b q [])).Perm
        (parityEnvelopeRender a
          (p ++ [b, b] ++ q) []) := by
    simpa [parityEnvelopeRender, List.append_assoc] using
      adjacentParityEnvelopeMerge_perm a b p q
  have finalTarget :
      (parityEnvelopeRender a finalInterior []).Perm
        (parityEnvelopeRender a
          (p ++ [b, b] ++ q) []) :=
    plan.render_perm.symm.trans sourceTarget
  have interiorPermutation :
      finalInterior.Perm (p ++ [b, b] ++ q) := by
    rw [List.perm_iff_count]
    intro tested
    have counts :=
      (List.perm_iff_count.mp finalTarget) tested
    simp only [parityEnvelopeRender, List.count_cons,
      List.count_append, List.count_nil] at counts ⊢
    omega
  have arrange :
      ListDerives
        (parityEnvelopeRender a finalInterior [])
        (parityEnvelopeRender a
          (p ++ [b, b] ++ q) []) :=
    listDerivesParityEnvelopeInteriorPermutation
      a [] interiorPermutation
  simpa [parityEnvelopeRender, List.append_assoc] using
    ListDerives.trans replay arrange

/-- Apply the adjacent-envelope merge under arbitrary list contexts. -/
theorem listDerivesAdjacentParityEnvelopeMergeContext
    (pre suffix : List Nat)
    (a b : Nat) (p q : List Nat)
    (overlap :
      ConnectedComponentSupportsIntersect
        ([a] ++ p ++ [a])
        ([b] ++ q ++ [b])) :
    ListDerives
      (pre ++ [a] ++ p ++ [a] ++ [b] ++ q ++ [b] ++ suffix)
      (pre ++ [a] ++ p ++ [b, b] ++ q ++ [a] ++ suffix) := by
  simpa [List.append_assoc] using
    ListDerives.context pre suffix
      (listDerivesAdjacentParityEnvelopeMerge
        a b p q overlap)

end SemigroupBasis.CoRoots.S5_441
