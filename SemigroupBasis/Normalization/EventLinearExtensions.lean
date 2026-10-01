import Init.Data.List.Perm

/-!
# Adjacent swaps between finite event linear extensions

This module isolates the combinatorial argument used by the one-local
normalizers.  A list is a linear extension of a precedence relation when it is
duplicate-free and never places an event before one that must precede it.

Two such lists with the same events are connected by adjacent swaps of
incomparable events.  No transitivity, antisymmetry, or decidability assumption
on the relation is needed: those properties belong to applications that
construct the precedence relation, while the proof below uses only the two
linear-extension certificates.
-/

namespace SemigroupBasis
namespace Normalization
namespace EventLinearExtensions

universe u

variable {α : Type u}

/-- Two events are incomparable for the supplied precedence relation. -/
def Incomparable
    (precedes : α → α → Prop) (left right : α) : Prop :=
  ¬ precedes left right ∧ ¬ precedes right left

theorem Incomparable.symm
    {precedes : α → α → Prop} {left right : α}
    (independent : Incomparable precedes left right) :
    Incomparable precedes right left :=
  ⟨independent.2, independent.1⟩

/-- A duplicate-free list whose order contains no reversed precedence edge. -/
structure LinearExtension
    (precedes : α → α → Prop) (events : List α) : Prop where
  nodup : events.Nodup
  ordered :
    events.Pairwise (fun earlier later => ¬ precedes later earlier)

/-- Reflexive-transitive closure of adjacent swaps allowed by `independent`.

`cons` supplies arbitrary prefix context.  The `suffix` argument of `swap`
supplies arbitrary suffix context.
-/
inductive AdjacentSwapClosure
    (independent : α → α → Prop) : List α → List α → Prop
  | refl (events : List α) :
      AdjacentSwapClosure independent events events
  | trans {source middle target : List α} :
      AdjacentSwapClosure independent source middle →
      AdjacentSwapClosure independent middle target →
      AdjacentSwapClosure independent source target
  | cons (head : α) {source target : List α} :
      AdjacentSwapClosure independent source target →
      AdjacentSwapClosure independent (head :: source) (head :: target)
  | swap (left right : α) (suffix : List α) :
      independent left right →
      AdjacentSwapClosure independent
        (left :: right :: suffix) (right :: left :: suffix)

/-- Every adjacent-swap chain is, in particular, a list permutation. -/
theorem AdjacentSwapClosure.perm
    {independent : α → α → Prop} {source target : List α}
    (steps : AdjacentSwapClosure independent source target) :
    source.Perm target := by
  induction steps with
  | refl events =>
      exact List.Perm.refl events
  | trans _ _ inductionFirst inductionSecond =>
      exact inductionFirst.trans inductionSecond
  | cons head _ inductionTail =>
      exact inductionTail.cons head
  | swap left right suffix _ =>
      exact List.Perm.swap right left suffix

/-- Delete one event from the middle of a certified linear extension. -/
theorem LinearExtension.erase_middle
    {precedes : α → α → Prop}
    {initial suffix : List α} {pivot : α}
    (extension :
      LinearExtension precedes (initial ++ pivot :: suffix)) :
    LinearExtension precedes (initial ++ suffix) := by
  have suffixSublist : List.Sublist suffix (pivot :: suffix) :=
    List.Sublist.cons pivot (List.Sublist.refl suffix)
  have remainderSublist :
      List.Sublist (initial ++ suffix) (initial ++ pivot :: suffix) :=
    suffixSublist.append_left initial
  exact
    { nodup := extension.nodup.sublist remainderSublist
      ordered := extension.ordered.sublist remainderSublist }

/-- Bubble `pivot` left across a prefix of events incomparable with it. -/
theorem bubble_to_front
    {precedes : α → α → Prop}
    (pivot : α) (initial suffix : List α)
    (independent :
      ∀ event, event ∈ initial →
        Incomparable precedes event pivot) :
    AdjacentSwapClosure (Incomparable precedes)
      (initial ++ pivot :: suffix) (pivot :: (initial ++ suffix)) := by
  induction initial with
  | nil =>
      exact AdjacentSwapClosure.refl (pivot :: suffix)
  | cons head tail inductionTail =>
      have tailIndependent :
          ∀ event, event ∈ tail →
            Incomparable precedes event pivot := by
        intro event member
        exact independent event (List.mem_cons_of_mem head member)
      have moveInsideTail :
          AdjacentSwapClosure (Incomparable precedes)
            (head :: tail ++ pivot :: suffix)
            (head :: pivot :: (tail ++ suffix)) :=
        AdjacentSwapClosure.cons head
          (inductionTail tailIndependent)
      have crossHead :
          AdjacentSwapClosure (Incomparable precedes)
            (head :: pivot :: (tail ++ suffix))
            (pivot :: head :: (tail ++ suffix)) :=
        AdjacentSwapClosure.swap head pivot (tail ++ suffix)
          (independent head (by simp))
      exact AdjacentSwapClosure.trans moveInsideTail crossHead

/-- Every event crossed while moving the target head through the source prefix
is incomparable with that head.

The source extension rules out `pivot ≺ event`; the target extension rules out
`event ≺ pivot`.  Duplicate-freeness identifies a prefix event with an event of
the target tail rather than with `pivot` itself.
-/
theorem prefix_incomparable
    {precedes : α → α → Prop}
    {pivot : α} {initial suffix targetTail : List α}
    (sourceExtension :
      LinearExtension precedes (initial ++ pivot :: suffix))
    (targetExtension :
      LinearExtension precedes (pivot :: targetTail))
    (sameEvents :
      (initial ++ pivot :: suffix).Perm (pivot :: targetTail)) :
    ∀ event, event ∈ initial →
      Incomparable precedes event pivot := by
  intro event eventInPrefix
  have eventNePivot : event ≠ pivot := by
    exact
      (List.nodup_append.mp sourceExtension.nodup).2.2
        event eventInPrefix pivot (by simp)
  have eventInSource : event ∈ initial ++ pivot :: suffix :=
    List.mem_append.mpr (Or.inl eventInPrefix)
  have eventInTarget : event ∈ pivot :: targetTail :=
    sameEvents.mem_iff.mp eventInSource
  have eventInTargetTail : event ∈ targetTail := by
    rcases List.mem_cons.mp eventInTarget with equal | member
    · exact (eventNePivot equal).elim
    · exact member
  have notEventBeforePivot : ¬ precedes event pivot :=
    (List.pairwise_cons.mp targetExtension.ordered).1
      event eventInTargetTail
  have notPivotBeforeEvent : ¬ precedes pivot event :=
    sourceExtension.ordered.rel_of_mem_append
      eventInPrefix (by simp)
  exact ⟨notEventBeforePivot, notPivotBeforeEvent⟩

/-- Two duplicate-free linear extensions of one finite event relation are
connected by adjacent swaps of incomparable events. -/
theorem connected_by_adjacent_incomparable_swaps
    {precedes : α → α → Prop} {source target : List α}
    (sourceExtension : LinearExtension precedes source)
    (targetExtension : LinearExtension precedes target)
    (sameEvents : source.Perm target) :
    AdjacentSwapClosure (Incomparable precedes) source target := by
  induction target generalizing source with
  | nil =>
      have sourceNil : source = [] := sameEvents.eq_nil
      subst source
      exact AdjacentSwapClosure.refl []
  | cons pivot targetTail inductionTail =>
      have pivotInSource : pivot ∈ source :=
        sameEvents.mem_iff.mpr (by simp)
      obtain ⟨initial, suffix, sourceShape⟩ :=
        List.mem_iff_append.mp pivotInSource
      subst source
      have independentPrefix :
          ∀ event, event ∈ initial →
            Incomparable precedes event pivot :=
        prefix_incomparable
          sourceExtension targetExtension sameEvents
      have movePivot :
          AdjacentSwapClosure (Incomparable precedes)
            (initial ++ pivot :: suffix)
            (pivot :: (initial ++ suffix)) :=
        bubble_to_front pivot initial suffix independentPrefix
      have sourceTailExtension :
          LinearExtension precedes (initial ++ suffix) :=
        sourceExtension.erase_middle
      have targetTailExtension :
          LinearExtension precedes targetTail :=
        { nodup :=
            (List.nodup_cons.mp targetExtension.nodup).2
          ordered :=
            (List.pairwise_cons.mp targetExtension.ordered).2 }
      have alignedEvents :
          (pivot :: (initial ++ suffix)).Perm
            (pivot :: targetTail) :=
        (List.perm_middle :
          (initial ++ pivot :: suffix).Perm
            (pivot :: (initial ++ suffix))).symm.trans sameEvents
      have sameTailEvents :
          (initial ++ suffix).Perm targetTail :=
        alignedEvents.cons_inv
      have moveTail :
          AdjacentSwapClosure (Incomparable precedes)
            (initial ++ suffix) targetTail :=
        inductionTail
          sourceTailExtension targetTailExtension sameTailEvents
      exact
        AdjacentSwapClosure.trans movePivot
          (AdjacentSwapClosure.cons pivot moveTail)

end EventLinearExtensions
end Normalization
end SemigroupBasis
