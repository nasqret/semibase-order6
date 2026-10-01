import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_6183TerminalMoves
import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_6183Semantics

/-! Exhaustive terminal reduction: a simple last letter, an absorbed last
letter, or a single marked copy immediately before a globally simple anchor.
The alternatives carry actual raw7 derivations. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_6183

open SemigroupBasis
open S4_71Suffix

theorem split_last_occurrence (word : List Nat) (selected : Nat) (member : selected ∈ word) :
    ∃ before after, word = before ++ selected :: after ∧ selected ∉ after := by
  induction word with
  | nil => cases member
  | cons first rest ih =>
      by_cases later : selected ∈ rest
      · obtain ⟨before, after, shape, absent⟩ := ih later
        exact ⟨first :: before, after, by simp only [List.cons_append, shape], absent⟩
      · have equal : selected = first := (List.mem_cons.mp member).resolve_right later
        subst first
        exact ⟨[], rest, rfl, later⟩

theorem first_simple_or_none (whole middle : List Nat) :
    (∀ letter, letter ∈ middle → whole.count letter ≠ 1) ∨
      ∃ before selected after, middle = before ++ selected :: after ∧ whole.count selected = 1 ∧
        ∀ letter, letter ∈ before → whole.count letter ≠ 1 := by
  induction middle with
  | nil => exact Or.inl (by intro letter member; cases member)
  | cons first rest ih =>
      by_cases simple : whole.count first = 1
      · exact Or.inr ⟨[], first, rest, rfl, simple, by intro letter member; cases member⟩
      · rcases ih with none | some
        · refine Or.inl ?_
          intro letter member
          rcases List.mem_cons.mp member with equal | later
          · subst letter
            exact simple
          · exact none letter later
        · obtain ⟨before, selected, after, shape, selectedSimple, beforeNone⟩ := some
          refine Or.inr ⟨first :: before, selected, after, ?_, selectedSimple, ?_⟩
          · simp only [List.cons_append, shape]
          · intro letter member
            rcases List.mem_cons.mp member with equal | later
            · subst letter
              exact simple
            · exact beforeNone letter later

theorem simple_context_absent (before after : List Nat) (selected : Nat)
    (simple : (before ++ selected :: after).count selected = 1) :
    selected ∉ before ∧ selected ∉ after := by
  simp only [List.count_append, List.count_cons_self] at simple
  exact ⟨List.not_mem_of_count_eq_zero (by omega), List.not_mem_of_count_eq_zero (by omega)⟩

theorem count_end_other (front : List Nat) (last selected : Nat) (different : selected ≠ last) :
    (front ++ [last]).count selected = front.count selected := by
  simp only [List.count_append, List.count_cons_of_ne (Ne.symm different), List.count_nil, Nat.add_zero]

def StableTerminal (front : List Nat) (last : Nat) : Prop :=
  Derives basis (endWord front last) (endWord front last ++ Word.singleton last)

def AnchoredShape (before after : List Nat) (marked simple : Nat) : Prop :=
  simple ≠ marked ∧ (marked ∉ before ∧ marked ∉ after) ∧ (simple ∉ before ∧ simple ∉ after)

theorem anchored_active (before after : List Nat) (marked simple : Nat)
    (shape : AnchoredShape before after marked simple) :
    ActiveCut (before ++ marked :: simple :: after) marked simple := by
  refine ⟨shape.1, before ++ [marked], after, ?_, ?_, shape.2.2.2, shape.2.1.2⟩
  · simp only [List.append_assoc, List.singleton_append]
  · simp [shape.2.2.1, shape.1]

theorem anchored_count_one (before after : List Nat) (marked simple : Nat)
    (shape : AnchoredShape before after marked simple) :
    (before ++ marked :: simple :: after).count simple = 1 := by
  simp only [List.count_append, List.count_cons_of_ne (Ne.symm shape.1), List.count_cons_self,
    List.count_eq_zero.mpr shape.2.2.1, List.count_eq_zero.mpr shape.2.2.2]

theorem terminal_cases (front : List Nat) (last : Nat) :
    last ∉ front ∨ StableTerminal front last ∨
      ∃ before after simple,
        Derives basis (endWord front last) (endWord (before ++ last :: simple :: after) last) ∧
        AnchoredShape before after last simple := by
  by_cases present : last ∈ front
  · obtain ⟨before, middle, frontShape, lastAbsent⟩ := split_last_occurrence front last present
    subst front
    let whole := (before ++ last :: middle) ++ [last]
    rcases first_simple_or_none whole middle with noSimple | hasSimple
    · refine Or.inr (Or.inl ?_)
      apply terminal_stable_of_gap before middle last
      intro letter member
      have different : letter ≠ last := by
        intro equal
        subst letter
        exact lastAbsent member
      have wholeMember : letter ∈ whole := by simp [whole, member]
      have positive : 0 < whole.count letter := List.count_pos_iff.mpr wholeMember
      have notOne := noSimple letter member
      have repeated : 2 ≤ whole.count letter := by omega
      simpa only [whole, count_end_other _ last letter different] using repeated
    · obtain ⟨gap, simple, after, middleShape, simpleCount, gapNotSimple⟩ := hasSimple
      subst middle
      have different : simple ≠ last := by
        intro equal
        subst simple
        exact lastAbsent (by simp)
      have gapAbsent : last ∉ gap := by
        intro member
        exact lastAbsent (List.mem_append_left _ member)
      have afterAbsent : last ∉ after := by
        intro member
        exact lastAbsent (List.mem_append_right _ (List.Mem.tail simple member))
      have clear := remove_terminal_repetitions before (gap ++ simple :: after) last
      have clearEquivalent : EndEquivalent (before ++ last :: (gap ++ simple :: after)) last
          (erase last before ++ last :: (gap ++ simple :: after)) last := Derives.sound models_raw clear
      have repeated : ∀ letter, letter ∈ gap →
          2 ≤ (erase last before ++ last :: (gap ++ (Word.mk simple after).toList)).count letter := by
        intro letter member
        have notLast : letter ≠ last := by
          intro equal
          subst letter
          exact gapAbsent member
        have wholeMember : letter ∈ whole := by simp [whole, member]
        have positive : 0 < whole.count letter := List.count_pos_iff.mpr wholeMember
        have notOne := gapNotSimple letter member
        have originalRepeated : 2 ≤ whole.count letter := by omega
        have sameTheory : ListTheory whole
            ((erase last before ++ last :: (gap ++ simple :: after)) ++ [last]) := clearEquivalent.lower
        have updated := (sameTheory.repeated_iff letter).mp originalRepeated
        simpa only [count_end_other _ last letter notLast, mk_toList] using updated
      have move := move_marked_across_repeated (erase last before) gap last (Word.mk simple after) repeated
      have move' : Derives basis (endWord (erase last before ++ last :: (gap ++ simple :: after)) last)
          (endWord ((erase last before ++ gap) ++ last :: simple :: after) last) := by
        apply derives_of_lists move
        all_goals simp only [endWord, put_toList, Word.toList_append, Word.toList_singleton,
          mk_toList, List.cons_append, List.nil_append, List.append_assoc]
      have reduction := clear.trans move'
      have reducedEquivalent : EndEquivalent (before ++ last :: (gap ++ simple :: after)) last
          ((erase last before ++ gap) ++ last :: simple :: after) last := Derives.sound models_raw reduction
      have sameTheory : ListTheory whole (((erase last before ++ gap) ++ last :: simple :: after) ++ [last]) :=
        reducedEquivalent.lower
      have reducedSimple := (sameTheory.count_one simple).mp simpleCount
      rw [count_end_other _ last simple different] at reducedSimple
      have simpleAbsent := simple_context_absent ((erase last before ++ gap) ++ [last]) after simple (by
        simpa only [List.append_assoc, List.singleton_append] using reducedSimple)
      have simpleBefore : simple ∉ erase last before ++ gap := by
        intro member
        exact simpleAbsent.1 (List.mem_append_left _ member)
      refine Or.inr (Or.inr ⟨erase last before ++ gap, after, simple, reduction, different, ?_,
        simpleBefore, simpleAbsent.2⟩)
      exact ⟨by simp [erased_absent, gapAbsent], afterAbsent⟩
  · exact Or.inl present

theorem unique_first_split (leftBefore leftAfter rightBefore rightAfter : List Nat) (selected : Nat)
    (same : leftBefore ++ selected :: leftAfter = rightBefore ++ selected :: rightAfter)
    (leftAbsent : selected ∉ leftBefore) (rightAbsent : selected ∉ rightBefore) :
    leftBefore = rightBefore ∧ leftAfter = rightAfter := by
  induction leftBefore generalizing rightBefore with
  | nil =>
      cases rightBefore with
      | nil => exact ⟨rfl, (List.cons.inj same).2⟩
      | cons first rest =>
          have equal := (List.cons.inj same).1
          exact False.elim (rightAbsent (by simp [equal]))
  | cons first rest ih =>
      cases rightBefore with
      | nil =>
          have equal := (List.cons.inj same).1
          exact False.elim (leftAbsent (by simp [equal]))
      | cons other tail =>
          obtain ⟨equal, restSame⟩ := List.cons.inj same
          have remaining := ih tail restSame
            (fun member => leftAbsent (List.Mem.tail first member))
            (fun member => rightAbsent (List.Mem.tail other member))
          exact ⟨by rw [equal, remaining.1], remaining.2⟩

theorem active_after_anchor (before after : List Nat) (marked anchor selected : Nat)
    (active : ActiveCut (before ++ marked :: anchor :: after) marked selected) :
    selected = anchor ∨ selected ∈ after := by
  obtain ⟨different, cutBefore, cutAfter, cutShape, cutBeforeAbsent, cutAfterAbsent, markedAbsent⟩ := active
  have selectedSimple : (before ++ marked :: anchor :: after).count selected = 1 := by
    rw [cutShape]
    simp only [List.count_append, List.count_cons_self,
      List.count_eq_zero.mpr cutBeforeAbsent, List.count_eq_zero.mpr cutAfterAbsent]
  have notBefore : selected ∉ before := by
    intro member
    obtain ⟨first, rest, beforeShape⟩ := List.append_of_mem member
    have alternative : before ++ marked :: anchor :: after = first ++ selected :: (rest ++ marked :: anchor :: after) := by
      rw [beforeShape]
      simp only [List.append_assoc, List.cons_append]
    have firstAbsent := (simple_context_absent first (rest ++ marked :: anchor :: after) selected (by
      rw [← alternative]
      exact selectedSimple)).1
    have unique := unique_first_split cutBefore cutAfter first (rest ++ marked :: anchor :: after) selected
      (cutShape.symm.trans alternative) cutBeforeAbsent firstAbsent
    exact markedAbsent (by rw [unique.2]; simp)
  have member : selected ∈ before ++ marked :: anchor :: after := by rw [cutShape]; simp
  simpa only [List.mem_append, List.mem_cons, notBefore, different, false_or] using member

theorem anchored_anchor_preserved (leftBefore leftAfter rightBefore rightAfter : List Nat)
    (marked leftAnchor rightAnchor : Nat)
    (leftShape : AnchoredShape leftBefore leftAfter marked leftAnchor)
    (rightShape : AnchoredShape rightBefore rightAfter marked rightAnchor)
    (same : EndEquivalent (leftBefore ++ marked :: leftAnchor :: leftAfter) marked
      (rightBefore ++ marked :: rightAnchor :: rightAfter) marked) : leftAnchor = rightAnchor := by
  by_cases equal : leftAnchor = rightAnchor
  · exact equal
  · have leftActive := anchored_active leftBefore leftAfter marked leftAnchor leftShape
    have rightActive := anchored_active rightBefore rightAfter marked rightAnchor rightShape
    have leftOnRight := (active_terminal_preserved _ _ marked marked leftAnchor same leftActive).2
    have rightOnLeft := (active_terminal_preserved _ _ marked marked rightAnchor same.symm rightActive).2
    have leftInRight : leftAnchor ∈ rightAfter :=
      (active_after_anchor rightBefore rightAfter marked rightAnchor leftAnchor leftOnRight).resolve_left equal
    have rightInLeft : rightAnchor ∈ leftAfter :=
      (active_after_anchor leftBefore leftAfter marked leftAnchor rightAnchor rightOnLeft).resolve_left (Ne.symm equal)
    obtain ⟨leading, suffix, rightAfterShape⟩ := List.append_of_mem leftInRight
    let rightPrefix := rightBefore ++ marked :: rightAnchor :: leading
    have rightWordShape : (rightBefore ++ marked :: rightAnchor :: rightAfter) ++ [marked] =
        rightPrefix ++ leftAnchor :: (suffix ++ [marked]) := by
      simp only [rightAfterShape, rightPrefix, List.append_assoc, List.cons_append]
    have leftWordShape : (leftBefore ++ marked :: leftAnchor :: leftAfter) ++ [marked] =
        (leftBefore ++ [marked]) ++ leftAnchor :: (leftAfter ++ [marked]) := by
      simp only [List.append_assoc, List.cons_append, List.nil_append]
    have wholeTheory : ListTheory
        ((leftBefore ++ [marked]) ++ leftAnchor :: (leftAfter ++ [marked]))
        (rightPrefix ++ leftAnchor :: (suffix ++ [marked])) := by
      intro valuation
      rw [← leftWordShape, ← rightWordShape]
      exact same.lower valuation
    have leftSimple : ((leftBefore ++ [marked]) ++ leftAnchor :: (leftAfter ++ [marked])).count leftAnchor = 1 := by
      rw [← leftWordShape, count_end_other _ marked leftAnchor leftShape.1]
      exact anchored_count_one leftBefore leftAfter marked leftAnchor leftShape
    have rightSimple := (wholeTheory.count_one leftAnchor).mp leftSimple
    have leftAbsent := simple_context_absent (leftBefore ++ [marked]) (leftAfter ++ [marked]) leftAnchor leftSimple
    have rightAbsent := simple_context_absent rightPrefix (suffix ++ [marked]) leftAnchor rightSimple
    have support := wholeTheory.simple_suffix_support leftAbsent.1 leftAbsent.2 rightAbsent.1 rightAbsent.2 rightAnchor
    have member : rightAnchor ∈ suffix ++ [marked] := support.mp (List.mem_append_left _ rightInLeft)
    have notSuffix : rightAnchor ∉ suffix := by
      intro present
      exact rightShape.2.2.2 (by rw [rightAfterShape]; simp [present])
    have impossible : rightAnchor ∉ suffix ++ [marked] := by simp [notSuffix, rightShape.1]
    exact False.elim (impossible member)

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_6183
