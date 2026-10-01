import SemigroupBasis.CoRoots.Order6Day11.FordLordProfile15.Profile15CountNormalization

/-! Equal-count alignment after a growing common prefix. All swaps carry
actual earlier/later occurrences. Simple-marker post-support supplies the
future copy that prevents crossing a last occurrence. The recursion consumes
one target letter, without a rank bound or a confluence assumption. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day11.FordLordProfile15

open SemigroupBasis
open SemigroupBasis.Examples
open Moves
open KeyTheory

namespace Alignment

def SameCounts (left right : List Nat) : Prop :=
  ∀ selected, left.count selected = right.count selected

/-- An internal x can cross any adjacent letter: both x anchors are retained. -/
theorem swapInternal (front : List Nat) (x y : Nat) (rest : List Nat)
    (seen : x ∈ front) (future : x ∈ rest) :
    L (front ++ [x,y] ++ rest) (front ++ [y,x] ++ rest) := by
  obtain ⟨initial, between, rfl⟩ := splitMember x front seen
  obtain ⟨after, suffix, rfl⟩ := splitMember x rest future
  have first : L ([x] ++ between ++ [x,y] ++ after ++ [x])
      ([x] ++ between ++ [y] ++ after ++ [x,x]) := by
    simpa [List.append_assoc] using middleToLast x between (y :: after)
  have second : L ([x] ++ between ++ [y] ++ after ++ [x,x])
      ([x] ++ between ++ [y,x] ++ after ++ [x]) := by
    simpa [List.append_assoc] using (middleToLast x (between ++ [y]) after).symm
  simpa [List.append_assoc] using (first.trans second).context initial suffix

/-- Move an already-seen letter left through an arbitrary block. If a
crossed marker is globally simple, a future selected copy must remain. -/
theorem bubbleSeen (selected : Nat) : ∀ (before front after : List Nat),
    selected ∈ front →
    (∀ marker, marker ∈ before →
      (front ++ before ++ selected :: after).count marker = 1 → selected ∈ after) →
    L (front ++ before ++ selected :: after) (front ++ selected :: (before ++ after))
  | [], front, after, _, _ => by
      simpa using (SemigroupBasis.CoRoots.S5_107.ListDerives.refl
        (basis := basis) (front ++ selected :: after))
  | marker :: before, front, after, seen, blocked => by
      have moved := bubbleSeen selected before (front ++ [marker]) after
        (List.mem_append.mpr (Or.inl seen)) (by
          intro tested member simple
          apply blocked tested (List.Mem.tail marker member)
          simpa [List.append_assoc] using simple)
      have first : L (front ++ (marker :: before) ++ selected :: after)
          (front ++ marker :: selected :: (before ++ after)) := by
        simpa [List.append_assoc] using moved
      have swapped : L (front ++ marker :: selected :: (before ++ after))
          (front ++ selected :: marker :: (before ++ after)) := by
        by_cases equal : marker = selected
        · subst marker
          exact .refl _
        · by_cases earlier : marker ∈ front
          · simpa using swapSeen front marker selected (before ++ after) earlier seen
          · by_cases later : marker ∈ before ++ after
            · simpa using (swapSeenFuture front selected marker (before ++ after) seen later).symm
            · have frontZero : front.count marker = 0 := List.count_eq_zero.mpr earlier
              have beforeZero : before.count marker = 0 := List.count_eq_zero.mpr (by
                intro member
                exact later (List.mem_append.mpr (Or.inl member)))
              have afterZero : after.count marker = 0 := List.count_eq_zero.mpr (by
                intro member
                exact later (List.mem_append.mpr (Or.inr member)))
              have simple : (front ++ (marker :: before) ++ selected :: after).count marker = 1 := by
                simp [frontZero, beforeZero, afterZero, Ne.symm equal]
              have laterSelected := blocked marker (by simp) simple
              simpa using (swapInternal front selected marker (before ++ after) seen
                (List.mem_append.mpr (Or.inr laterSelected))).symm
      simpa using first.trans swapped

/-- Move an initial letter past already-seen letters. Either it has its own
future copy, or every crossed letter has a future copy. -/
theorem bubbleInitial (selected : Nat) : ∀ (before front after : List Nat),
    (∀ marker, marker ∈ before → marker ∈ front) →
    (selected ∈ after ∨ ∀ marker, marker ∈ before → marker ∈ after) →
    L (front ++ before ++ selected :: after) (front ++ selected :: (before ++ after))
  | [], front, after, _, _ => by
      simpa using (SemigroupBasis.CoRoots.S5_107.ListDerives.refl
        (basis := basis) (front ++ selected :: after))
  | marker :: before, front, after, seen, later => by
      have moved := bubbleInitial selected before (front ++ [marker]) after (by
          intro tested member
          exact List.mem_append.mpr (Or.inl (seen tested (List.Mem.tail marker member)))) (by
          rcases later with future | future
          · exact Or.inl future
          · exact Or.inr (fun tested member => future tested (List.Mem.tail marker member)))
      have first : L (front ++ (marker :: before) ++ selected :: after)
          (front ++ marker :: selected :: (before ++ after)) := by
        simpa [List.append_assoc] using moved
      have swapped : L (front ++ marker :: selected :: (before ++ after))
          (front ++ selected :: marker :: (before ++ after)) := by
        rcases later with future | future
        · simpa using swapSeenFuture front marker selected (before ++ after)
            (seen marker (by simp)) (List.mem_append.mpr (Or.inr future))
        · simpa using swapInternal front marker selected (before ++ after)
            (seen marker (by simp)) (List.mem_append.mpr (Or.inr (future marker (by simp))))
      simpa using first.trans swapped

theorem filter_eq_nil_of_drop (keep : Nat → Bool) : ∀ (letters : List Nat),
    (∀ selected, selected ∈ letters → keep selected = false) → letters.filter keep = []
  | [], _ => rfl
  | selected :: letters, drop => by
      simp only [List.filter_cons, drop selected (by simp), Bool.false_eq_true, if_false]
      exact filter_eq_nil_of_drop keep letters (fun x member => drop x (List.Mem.tail selected member))

/-- After removing a common prefix's support, the next unseen first letter
must agree. Thus no unseen letter can stand before the selected initial one. -/
theorem ford_before_seen (front left before after : List Nat) (selected : Nat)
    (sameFord : firstOccurrenceSequence (front ++ selected :: left) =
      firstOccurrenceSequence (front ++ before ++ selected :: after))
    (unseen : selected ∉ front) (absentBefore : selected ∉ before) :
    ∀ marker, marker ∈ before → marker ∈ front := by
  let keep : Nat → Bool := fun x => decide (x ∉ front)
  have dropped : front.filter keep = [] := filter_eq_nil_of_drop keep front (by
    intro x member
    simp [keep, member])
  have kept : keep selected = true := by simp [keep, unseen]
  have filtered : firstOccurrenceSequence ((front ++ selected :: left).filter keep) =
      firstOccurrenceSequence ((front ++ before ++ selected :: after).filter keep) := by
    simpa only [firstOccurrenceSequence_filter] using congrArg (List.filter keep) sameFord
  simp only [List.filter_append, dropped, List.nil_append, List.filter_cons, kept, if_true] at filtered
  have beforeEmpty : before.filter keep = [] := by
    cases shape : before.filter keep with
    | nil => rfl
    | cons marker rest =>
        rw [shape] at filtered
        have heads : selected = marker := (List.cons.inj filtered).1
        have member : marker ∈ before.filter keep := by rw [shape]; simp
        have original : marker ∈ before := (List.mem_filter.mp member).1
        exact False.elim (absentBefore (by simpa only [heads] using original))
  intro marker member
  apply Decidable.byContradiction
  intro absent
  have included : marker ∈ before.filter keep := by simp [keep, member, absent]
  rw [beforeEmpty] at included
  simp at included

theorem cancel_selected_counts (front left before after : List Nat) (selected : Nat)
    (counts : SameCounts (front ++ selected :: left) (front ++ before ++ selected :: after)) :
    SameCounts left (before ++ after) := by
  intro tested
  have equal := counts tested
  simp only [List.count_append, List.count_cons] at equal ⊢
  omega

theorem post_mem_tail (front tail : List Nat) (marker selected : Nat)
    (absentFront : marker ∉ front) (simple : (front ++ tail).count marker = 1)
    (member : selected ∈ postList (front ++ tail) marker) : selected ∈ tail := by
  have frontZero : front.count marker = 0 := List.count_eq_zero.mpr absentFront
  have markerPresent : marker ∈ tail := by
    apply List.count_pos_iff.mp
    simp only [List.count_append, frontZero, Nat.zero_add] at simple
    omega
  obtain ⟨before, after, rfl⟩ := splitMember marker tail markerPresent
  have split : postList (front ++ (before ++ marker :: after)) marker = after := by
    simpa only [List.append_assoc] using postList_split marker (front ++ before) after
      (by simpa only [List.append_assoc] using simple)
  rw [split] at member
  exact List.mem_append.mpr (Or.inr (List.Mem.tail marker member))

/-- A globally simple crossed marker forces another selected copy after the
chosen occurrence. This is exactly the post-support guard, not cancellation. -/
theorem simple_before_forces_future (front left before after : List Nat) (selected marker : Nat)
    (same : SameKey (front ++ selected :: left) (front ++ before ++ selected :: after))
    (counts : SameCounts (front ++ selected :: left) (front ++ before ++ selected :: after))
    (absentBefore : selected ∉ before) (member : marker ∈ before)
    (simple : (front ++ before ++ selected :: after).count marker = 1) : selected ∈ after := by
  have different : selected ≠ marker := by
    intro equal
    exact absentBefore (by simpa only [equal] using member)
  have positive : 0 < before.count marker := List.count_pos_iff.mpr member
  have frontZero : front.count marker = 0 := by
    have equation := simple
    simp only [List.count_append, List.count_cons_of_ne different] at equation
    omega
  have simpleLeft : (front ++ selected :: left).count marker = 1 :=
    (counts marker).trans simple
  have inRight : selected ∈ postList (front ++ before ++ selected :: after) marker := by
    obtain ⟨earlier, later, shape⟩ := splitMember marker before member
    have split := postList_split marker (front ++ earlier) (later ++ selected :: after)
      (by simpa [shape, List.append_assoc] using simple)
    have actual : postList (front ++ before ++ selected :: after) marker = later ++ selected :: after := by
      simpa [shape, List.append_assoc] using split
    rw [actual]
    simp
  have inLeft : selected ∈ postList (front ++ selected :: left) marker :=
    (same.post marker selected simpleLeft).mpr inRight
  have tailMember : selected ∈ left := post_mem_tail (front ++ [selected]) left marker selected (by
      have absent : marker ∉ front := List.count_eq_zero.mp frontZero
      simp [absent, Ne.symm different])
    (by simpa [List.append_assoc] using simpleLeft)
    (by simpa [List.append_assoc] using inLeft)
  have tailPositive : 0 < left.count selected := List.count_pos_iff.mpr tailMember
  have equal := cancel_selected_counts front left before after selected counts selected
  have beforeZero : before.count selected = 0 := List.count_eq_zero.mpr absentBefore
  simp only [List.count_append, beforeZero, Nat.zero_add] at equal
  apply List.count_pos_iff.mp
  omega

/-- The first unmatched selected occurrence can be brought forward, with
all occurrence guards discharged from the exact full key and literal counts. -/
theorem moveToFront (front left before after : List Nat) (selected : Nat)
    (same : SameKey (front ++ selected :: left) (front ++ before ++ selected :: after))
    (counts : SameCounts (front ++ selected :: left) (front ++ before ++ selected :: after))
    (absentBefore : selected ∉ before) :
    L (front ++ before ++ selected :: after) (front ++ selected :: (before ++ after)) := by
  by_cases seen : selected ∈ front
  · apply bubbleSeen selected before front after seen
    intro marker member simple
    exact simple_before_forces_future front left before after selected marker same counts
      absentBefore member simple
  · apply bubbleInitial selected before front after
      (ford_before_seen front left before after selected same.ford seen absentBefore)
    by_cases future : selected ∈ after
    · exact Or.inl future
    · apply Or.inr
      have frontZero : front.count selected = 0 := List.count_eq_zero.mpr seen
      have beforeZero : before.count selected = 0 := List.count_eq_zero.mpr absentBefore
      have afterZero : after.count selected = 0 := List.count_eq_zero.mpr future
      have simpleRight : (front ++ before ++ selected :: after).count selected = 1 := by
        simp [frontZero, beforeZero, afterZero]
      have simpleLeft : (front ++ selected :: left).count selected = 1 :=
        (counts selected).trans simpleRight
      have leftSplit := postList_split selected front left simpleLeft
      have rightSplit := postList_split selected (front ++ before) after simpleRight
      intro marker member
      have positive : 0 < before.count marker := List.count_pos_iff.mpr member
      have equal := cancel_selected_counts front left before after selected counts marker
      have tailMember : marker ∈ left := by
        apply List.count_pos_iff.mp
        simp only [List.count_append] at equal
        omega
      have post := same.post selected marker simpleLeft
      rw [leftSplit, rightSplit] at post
      exact post.mp tailMember

/-- Structural recursion consumes one letter of the target tail. The common
prefix is data carried by the induction; no semigroup cancellation is used. -/
theorem align : ∀ (left front right : List Nat),
    SameKey (front ++ left) (front ++ right) →
    SameCounts (front ++ left) (front ++ right) → L (front ++ left) (front ++ right)
  | [], front, right, _, counts => by
      cases right with
      | nil => exact .refl _
      | cons selected rest =>
          have equal := counts selected
          simp only [List.count_append, List.count_nil, List.count_cons_self] at equal
          omega
  | selected :: left, front, right, same, counts => by
      have present : selected ∈ right := by
        apply List.count_pos_iff.mp
        have equal := counts selected
        simp only [List.count_append, List.count_cons_self] at equal
        omega
      obtain ⟨before, after, rfl, absentBefore⟩ := CountNormalization.splitFirst selected right present
      have sameAssociated : SameKey (front ++ selected :: left)
          (front ++ before ++ selected :: after) := by
        simpa only [List.append_assoc] using same
      have moved := moveToFront front left before after selected
        sameAssociated
        (by simpa only [List.append_assoc] using counts) absentBefore
      have movedKey := listDerives_sameKey moved
      have smallerKey : SameKey ((front ++ [selected]) ++ left)
          ((front ++ [selected]) ++ (before ++ after)) := by
        simpa only [List.append_assoc, List.cons_append, List.nil_append] using sameAssociated.trans movedKey
      have smallerCounts : SameCounts ((front ++ [selected]) ++ left)
          ((front ++ [selected]) ++ (before ++ after)) := by
        intro tested
        have equal := counts tested
        simp only [List.count_append, List.count_cons, List.count_nil] at equal ⊢
        omega
      have continued := align left (front ++ [selected]) (before ++ after) smallerKey smallerCounts
      have first : L (front ++ selected :: left) (front ++ selected :: (before ++ after)) := by
        simpa only [List.append_assoc, List.cons_append, List.nil_append] using continued
      simpa only [List.append_assoc] using first.trans moved.symm

theorem equalCountsReach (left right : List Nat) (same : SameKey left right)
    (counts : SameCounts left right) : L left right := by
  simpa using align left [] right (by simpa using same) (by simpa using counts)

/-- Unrestricted key sufficiency for the exact sixteen laws. -/
theorem sameKeyReach (left right : List Nat) (same : SameKey left right) : L left right := by
  obtain ⟨reducedLeft, reducedRight, leftReached, rightReached, reducedKey, counts, _⟩ :=
    CountNormalization.reduceSameKey left right same
  exact leftReached.trans ((equalCountsReach reducedLeft reducedRight reducedKey counts).trans rightReached.symm)

theorem derivesOfSameKey (left right : Word Nat) (same : SameKey left.toList right.toList) :
    Derives basis left right := by
  cases left with
  | mk x xs =>
      cases right with
      | mk y ys =>
          exact SemigroupBasis.CoRoots.S5_107.ListDerives.toWord (sameKeyReach (x :: xs) (y :: ys) same)

end Alignment
end SemigroupBasis.CoRoots.Order6Day11.FordLordProfile15
