import SemigroupBasis.CoRoots.S5_107ListDerives
import SemigroupBasis.Examples.EdmundsPeriodTwoBlocksSyntax

namespace SemigroupBasis.BlockTrace

open SemigroupBasis
open SemigroupBasis.CoRoots.S5_107
open SemigroupBasis.Examples

universe u

/-! ## Dependency-order combinatorics -/

section Combinatorics

variable {alpha : Type u} [DecidableEq alpha]

/-- `Precedes left right items` means that one occurrence of `left` appears
strictly before an occurrence of `right`. The block-trace theorem only applies
it to noduplicated lists. -/
def Precedes (left right : alpha) (items : List alpha) : Prop :=
  ∃ initial suffix,
    items = initial ++ left :: suffix ∧ right ∈ suffix

theorem precedes_cons_iff
    (head left right : alpha) (tail : List alpha) :
    Precedes left right (head :: tail) ↔
      (head = left ∧ right ∈ tail) ∨
        Precedes left right tail := by
  constructor
  · rintro ⟨initial, suffix, equality, rightMember⟩
    cases initial with
    | nil =>
        simp only [List.nil_append] at equality
        injection equality with headEquality tailEquality
        exact Or.inl ⟨headEquality, by
          simpa [tailEquality] using rightMember⟩
    | cons first rest =>
        simp only [List.cons_append] at equality
        injection equality with _headEquality tailEquality
        exact Or.inr ⟨rest, suffix, tailEquality, rightMember⟩
  · rintro (⟨rfl, rightMember⟩ | ⟨initial, suffix, equality, rightMember⟩)
    · exact ⟨[], tail, rfl, rightMember⟩
    · exact ⟨head :: initial, suffix, by
        simp only [List.cons_append, equality], rightMember⟩

theorem precedes_cons_iff_of_ne
    {head left right : alpha} {tail : List alpha}
    (different : head ≠ left) :
    Precedes left right (head :: tail) ↔
      Precedes left right tail := by
  rw [precedes_cons_iff]
  simp [different]

theorem precedes_cons_self
    {left right : alpha} {tail : List alpha}
    (rightMember : right ∈ tail) :
    Precedes left right (left :: tail) :=
  (precedes_cons_iff left left right tail).2 <|
    Or.inl ⟨rfl, rightMember⟩

theorem precedes_cons
    (head : alpha) {left right : alpha} {tail : List alpha}
    (order : Precedes left right tail) :
    Precedes left right (head :: tail) :=
  (precedes_cons_iff head left right tail).2 (Or.inr order)

theorem precedes_left_mem
    {left right : alpha} {items : List alpha}
    (order : Precedes left right items) :
    left ∈ items := by
  obtain ⟨initial, suffix, equality, _⟩ := order
  rw [equality]
  exact List.mem_append_right initial (List.Mem.head suffix)

theorem precedes_right_mem
    {left right : alpha} {items : List alpha}
    (order : Precedes left right items) :
    right ∈ items := by
  obtain ⟨initial, suffix, equality, rightMember⟩ := order
  rw [equality]
  exact
    List.mem_append_right initial (List.Mem.tail left rightMember)

/-- In a noduplicated list, no item can precede the head item. -/
theorem not_precedes_right_head
    {left right : alpha} {tail : List alpha}
    (nodup : (right :: tail).Nodup) :
    ¬ Precedes left right (right :: tail) := by
  intro order
  have rightNotTail : right ∉ tail :=
    (List.nodup_cons.mp nodup).1
  rcases
      (precedes_cons_iff right left right tail).1 order with
    ⟨_, rightMember⟩ | tailOrder
  · exact rightNotTail rightMember
  · exact rightNotTail (precedes_right_mem tailOrder)

/-- Erasing an item distinct from both endpoints preserves their relative
order. -/
theorem precedes_erase_iff
    {removed left right : alpha} {items : List alpha}
    (removedNeLeft : removed ≠ left)
    (removedNeRight : removed ≠ right) :
    Precedes left right (items.erase removed) ↔
      Precedes left right items := by
  induction items with
  | nil =>
      simp [Precedes]
  | cons head tail inductionHypothesis =>
      by_cases headEq : head = removed
      · subst head
        simpa only [List.erase_cons_head] using
          (precedes_cons_iff_of_ne
            (tail := tail) (right := right) removedNeLeft).symm
      · simp only [List.erase,
          beq_eq_false_iff_ne.mpr headEq]
        rw [precedes_cons_iff, precedes_cons_iff,
          inductionHypothesis]
        rw [List.mem_erase_of_ne (Ne.symm removedNeRight)]

/-- Reflexive-transitive closure of adjacent swaps admitted by
`independent`. Prefix context is represented by `cons`; the `swap`
constructor already carries arbitrary suffix context. -/
inductive SwapClosure (independent : alpha → alpha → Prop) :
    List alpha → List alpha → Prop
  | refl (items : List alpha) :
      SwapClosure independent items items
  | trans {source middle target : List alpha} :
      SwapClosure independent source middle →
      SwapClosure independent middle target →
      SwapClosure independent source target
  | cons (head : alpha) {source target : List alpha} :
      SwapClosure independent source target →
      SwapClosure independent (head :: source) (head :: target)
  | swap (left right : alpha) (suffix : List alpha) :
      independent left right →
      SwapClosure independent
        (left :: right :: suffix) (right :: left :: suffix)

namespace SwapClosure

theorem prepend
    {independent : alpha → alpha → Prop}
    (initial : List alpha) {source target : List alpha}
    (derivation : SwapClosure independent source target) :
    SwapClosure independent
      (initial ++ source) (initial ++ target) := by
  induction initial with
  | nil =>
      simpa using derivation
  | cons head tail inductionHypothesis =>
      simpa using SwapClosure.cons head inductionHypothesis

/-- Bubble a selected item to the front when every item before it is
independent from it. -/
theorem move_to_front
    {independent : alpha → alpha → Prop} {selected : alpha} :
    forall {source : List alpha},
      selected ∈ source →
      (forall item,
        Precedes item selected source →
          independent item selected) →
      SwapClosure independent source
        (selected :: source.erase selected)
  | [], selectedMember, _ => by
      simp at selectedMember
  | head :: tail, selectedMember, crossings => by
      by_cases headEq : head = selected
      · subst head
        simpa using
          (SwapClosure.refl
            (independent := independent) (selected :: tail))
      · have selectedInTail : selected ∈ tail := by
          simpa [Ne.symm headEq] using selectedMember
        have tailCrossings :
            forall item,
              Precedes item selected tail →
                independent item selected := by
          intro item order
          exact crossings item (precedes_cons head order)
        have tailMove :=
          move_to_front selectedInTail tailCrossings
        have prefixed := SwapClosure.cons head tailMove
        have crossed :=
          SwapClosure.swap head selected (tail.erase selected) <|
            crossings head (precedes_cons_self selectedInTail)
        simpa only [List.erase,
          beq_eq_false_iff_ne.mpr headEq] using
          prefixed.trans crossed

/-- Two noduplicated permutations are connected by allowed adjacent swaps
when every dependent pair has the same relative order. -/
theorem of_perm_of_dependent_order
    {independent : alpha → alpha → Prop} :
    forall {target source : List alpha},
      source.Nodup →
      target.Nodup →
      source.Perm target →
      (forall left right,
        left ∈ source →
        right ∈ source →
        ¬ independent left right →
        (Precedes left right source ↔
          Precedes left right target)) →
      SwapClosure independent source target
  | [], source, _, _, permutation, _ => by
      have sourceEmpty : source = [] := by
        apply List.eq_nil_of_length_eq_zero
        simpa using permutation.length_eq
      subst source
      exact SwapClosure.refl (independent := independent) []
  | selected :: targetTail, source, sourceNodup, targetNodup,
      permutation, dependentOrder => by
      classical
      have selectedInSource : selected ∈ source :=
        permutation.mem_iff.mpr (List.Mem.head targetTail)
      have canCross :
          forall item,
            Precedes item selected source →
              independent item selected := by
        intro item order
        by_cases allowed : independent item selected
        · exact allowed
        · have targetOrder :
              Precedes item selected (selected :: targetTail) :=
            (dependentOrder item selected
              (precedes_left_mem order) selectedInSource allowed).mp order
          exact False.elim <|
            not_precedes_right_head targetNodup targetOrder
      have frontMove :
          SwapClosure independent source
            (selected :: source.erase selected) :=
        move_to_front selectedInSource canCross
      let remainder := source.erase selected
      have remainderNodup : remainder.Nodup := by
        exact sourceNodup.erase selected
      have targetTailNodup : targetTail.Nodup :=
        (List.nodup_cons.mp targetNodup).2
      have remainderPermutation : remainder.Perm targetTail := by
        simpa [remainder] using permutation.erase selected
      have exposedPermutation :
          source.Perm (selected :: remainder) := by
        simpa [remainder] using
          List.perm_cons_erase selectedInSource
      have exposedNodup : (selected :: remainder).Nodup :=
        exposedPermutation.nodup_iff.mp sourceNodup
      have selectedNotRemainder : selected ∉ remainder :=
        (List.nodup_cons.mp exposedNodup).1
      have remainderOrder :
          forall left right,
            left ∈ remainder →
            right ∈ remainder →
            ¬ independent left right →
            (Precedes left right remainder ↔
              Precedes left right targetTail) := by
        intro left right leftMember rightMember blocked
        have selectedNeLeft : selected ≠ left := by
          intro equality
          subst left
          exact selectedNotRemainder leftMember
        have selectedNeRight : selected ≠ right := by
          intro equality
          subst right
          exact selectedNotRemainder rightMember
        have leftSource : left ∈ source :=
          List.mem_of_mem_erase leftMember
        have rightSource : right ∈ source :=
          List.mem_of_mem_erase rightMember
        exact
          (precedes_erase_iff
            (items := source) selectedNeLeft selectedNeRight).trans <|
            (dependentOrder left right leftSource rightSource blocked).trans <|
              precedes_cons_iff_of_ne selectedNeLeft
      have remainderDerivation :
          SwapClosure independent remainder targetTail :=
        of_perm_of_dependent_order
          remainderNodup targetTailNodup
          remainderPermutation remainderOrder
      exact frontMove.trans <|
        SwapClosure.cons selected remainderDerivation
termination_by
  target _ => target.length

end SwapClosure

/-- Noduplicated lists with the same members are permutations. -/
theorem perm_of_nodup_mem_iff :
    forall {source target : List alpha},
      source.Nodup →
      target.Nodup →
      (forall item, item ∈ source ↔ item ∈ target) →
      source.Perm target
  | [], [], _, _, _ => List.Perm.refl []
  | [], head :: tail, _, _, sameMembers => by
      have := (sameMembers head).mpr (List.Mem.head tail)
      exact False.elim (List.not_mem_nil this)
  | head :: tail, [], _, _, sameMembers => by
      have := (sameMembers head).mp (List.Mem.head tail)
      exact False.elim (List.not_mem_nil this)
  | head :: tail, targetHead :: targetTail,
      sourceNodup, targetNodup, sameMembers => by
      have headInTarget : head ∈ targetHead :: targetTail :=
        (sameMembers head).mp (List.Mem.head tail)
      have exposeTarget :
          (targetHead :: targetTail).Perm
            (head :: (targetHead :: targetTail).erase head) :=
        List.perm_cons_erase headInTarget
      have tailNodup : tail.Nodup :=
        (List.nodup_cons.mp sourceNodup).2
      have erasedNodup :
          ((targetHead :: targetTail).erase head).Nodup :=
        targetNodup.erase head
      have exposedNodup :
          (head :: (targetHead :: targetTail).erase head).Nodup :=
        exposeTarget.nodup_iff.mp targetNodup
      have headNotTail : head ∉ tail :=
        (List.nodup_cons.mp sourceNodup).1
      have headNotErased :
          head ∉ (targetHead :: targetTail).erase head :=
        (List.nodup_cons.mp exposedNodup).1
      have sameTailMembers :
          forall item,
            item ∈ tail ↔
              item ∈ (targetHead :: targetTail).erase head := by
        intro item
        by_cases itemEq : item = head
        · subst item
          exact iff_of_false headNotTail headNotErased
        · constructor
          · intro itemMember
            have targetMember :=
              (exposeTarget.mem_iff).mp <|
                (sameMembers item).mp (List.Mem.tail head itemMember)
            simp only [List.mem_cons] at targetMember
            rcases targetMember with targetAtHead | targetInTail
            · exact False.elim (itemEq targetAtHead)
            · exact targetInTail
          · intro itemMember
            have exposedMember :
                item ∈ head :: (targetHead :: targetTail).erase head :=
              List.Mem.tail head itemMember
            have sourceMember :=
              (sameMembers item).mpr <|
                (exposeTarget.mem_iff).mpr exposedMember
            simp only [List.mem_cons] at sourceMember
            rcases sourceMember with sourceAtHead | sourceInTail
            · exact False.elim (itemEq sourceAtHead)
            · exact sourceInTail
      exact
        (List.Perm.cons head <|
          perm_of_nodup_mem_iff
            tailNodup erasedNodup sameTailMembers).trans
          exposeTarget.symm

end Combinatorics

/-! ## Retained blocks and semigroup derivations -/

/-- The existing single/double/triple block representation matching the
one/two/three retained exponent states in the `S5_530` and `S5_636`
first-occurrence normal forms. -/
abbrev RetainedBlock := EdmundsPeriodTwoBlock

/-- Flatten retained blocks to their one-, two-, or three-letter renders. -/
abbrev renderRetainedBlocks := renderEdmundsPeriodTwoBlocks

/-- The two block lists carry the same label-to-retained-state map. -/
def SameRetainedStateMap
    (source target : List RetainedBlock) : Prop :=
  ∀ block, block ∈ source ↔ block ∈ target

/-- Every retained label occurs in at most one block. -/
def RetainedLabelsNodup (blocks : List RetainedBlock) : Prop :=
  (blocks.map EdmundsPeriodTwoBlock.label).Nodup

/-- Label uniqueness implies block uniqueness. -/
theorem retainedBlocks_nodup {blocks : List RetainedBlock}
    (labelsNodup : RetainedLabelsNodup blocks) :
    blocks.Nodup := by
  induction blocks with
  | nil =>
      exact List.nodup_nil
  | cons head tail inductionHypothesis =>
      have mappedNodup :
          (head.label :: tail.map EdmundsPeriodTwoBlock.label).Nodup := by
        simpa [RetainedLabelsNodup] using labelsNodup
      have mappedParts := List.nodup_cons.mp mappedNodup
      apply List.nodup_cons.mpr
      constructor
      · intro headMember
        exact mappedParts.1 <|
          List.mem_map.mpr ⟨head, headMember, rfl⟩
      · exact inductionHypothesis mappedParts.2

/-- Retained blocks may cross exactly when their exponent states commute. -/
def BlocksIndependent
    (commutes : Nat → Nat → Prop)
    (left right : RetainedBlock) : Prop :=
  commutes left.exponent right.exponent

/-- Dependent retained blocks have the same relative order in both traces. -/
def SameDependentOrder
    (commutes : Nat → Nat → Prop)
    (source target : List RetainedBlock) : Prop :=
  ∀ left right,
    left ∈ source →
    right ∈ source →
    ¬ BlocksIndependent commutes left right →
    (Precedes left right source ↔ Precedes left right target)

/-- The basis derives every adjacent block swap authorized by `commutes`. -/
def AdjacentSwapDerivable
    (basis : List (Identity Nat))
    (commutes : Nat → Nat → Prop) : Prop :=
  ∀ left right,
    BlocksIndependent commutes left right →
    ListDerives basis
      (left.render ++ right.render)
      (right.render ++ left.render)

/-- Render an allowed block-swap sequence as a basis derivation. -/
theorem renderSwapClosure
    {basis : List (Identity Nat)}
    {commutes : Nat → Nat → Prop}
    (adjacentSwap : AdjacentSwapDerivable basis commutes)
    {source target : List RetainedBlock}
    (derivation :
      SwapClosure (BlocksIndependent commutes) source target) :
    ListDerives basis
      (renderRetainedBlocks source)
      (renderRetainedBlocks target) := by
  induction derivation with
  | refl blocks =>
      exact ListDerives.refl (renderRetainedBlocks blocks)
  | @trans source middle target first second ihFirst ihSecond =>
      exact ihFirst.trans ihSecond
  | @cons head source target tailDerivation inductionHypothesis =>
      simpa [renderRetainedBlocks, renderEdmundsPeriodTwoBlocks] using
        inductionHypothesis.prepend head.render
  | swap left right suffix allowed =>
      simpa [renderRetainedBlocks, renderEdmundsPeriodTwoBlocks,
        List.append_assoc] using
          (adjacentSwap left right allowed).append
            (renderRetainedBlocks suffix)

/-- Shared block-trace derivation theorem for the order-six commutative and
monoid roots. Matching retained states determine a permutation; preservation
of every dependent pair order makes that permutation realizable using only
the basis-authorized adjacent block swaps. -/
theorem blockTraceDerives
    {basis : List (Identity Nat)}
    {commutes : Nat → Nat → Prop}
    {source target : List RetainedBlock}
    (sourceLabelsNodup : RetainedLabelsNodup source)
    (targetLabelsNodup : RetainedLabelsNodup target)
    (sameStateMap : SameRetainedStateMap source target)
    (dependentOrder : SameDependentOrder commutes source target)
    (adjacentSwap : AdjacentSwapDerivable basis commutes) :
    ListDerives basis
      (renderRetainedBlocks source)
      (renderRetainedBlocks target) := by
  have sourceNodup : source.Nodup :=
    retainedBlocks_nodup sourceLabelsNodup
  have targetNodup : target.Nodup :=
    retainedBlocks_nodup targetLabelsNodup
  have permutation : source.Perm target :=
    perm_of_nodup_mem_iff sourceNodup targetNodup sameStateMap
  have blockSwaps :
      SwapClosure (BlocksIndependent commutes) source target :=
    SwapClosure.of_perm_of_dependent_order
      sourceNodup targetNodup permutation dependentOrder
  exact renderSwapClosure adjacentSwap blockSwaps

end SemigroupBasis.BlockTrace
