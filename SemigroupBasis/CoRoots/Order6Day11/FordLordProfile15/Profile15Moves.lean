import SemigroupBasis.CoRoots.Order6Day11.FordLordProfile15.Profile15Basics
import SemigroupBasis.CoRoots.S5_107ListDerives

/-! All sixteen finite witness edges are ordinary contextual instantiations
of the frozen displayed laws.  The list-level lemmas below quantify over
arbitrary gaps, prefixes and suffixes.  Gathering and capping use structural
recursion, not the finite search bound. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day11.FordLordProfile15

open SemigroupBasis

namespace Moves

abbrev L : List Nat → List Nat → Prop :=
  SemigroupBasis.CoRoots.S5_107.ListDerives basis

theorem splitMember (x : Nat) : ∀ word : List Nat, x ∈ word →
    ∃ left right : List Nat, word = left ++ x :: right
  | [], member => by simp at member
  | head :: rest, member => by
      rcases List.mem_cons.mp member with equal | later
      · subst head
        exact ⟨[], rest, rfl⟩
      · obtain ⟨left, right, shape⟩ := splitMember x rest later
        exact ⟨head :: left, right, by simp [shape]⟩

theorem pastBoth00 (u v : Word Nat) :
    Derives basis (((u ++ v) ++ u) ++ v) (((u ++ v) ++ v) ++ u) := by
  have step0 : Derives basis (((u ++ v) ++ u) ++ v) (((u ++ u) ++ v) ++ v) := by
    simpa only [Word.append_assoc] using (rawLaw04 u v).symm
  have step1 : Derives basis (((u ++ u) ++ v) ++ v) (((u ++ v) ++ v) ++ u) := by
    simpa only [Word.append_assoc] using (rawLaw05 u v)
  exact step0.trans (step1)

theorem pastBoth10 (u v p : Word Nat) :
    Derives basis ((((u ++ p) ++ v) ++ u) ++ v) ((((u ++ p) ++ v) ++ v) ++ u) := by
  have step0 : Derives basis ((((u ++ p) ++ v) ++ u) ++ v) ((((u ++ p) ++ u) ++ v) ++ v) := by
    simpa only [Word.append_assoc] using (rawLaw11 u p v).symm
  have step1 : Derives basis ((((u ++ p) ++ u) ++ v) ++ v) ((((u ++ p) ++ v) ++ v) ++ u) := by
    simpa only [Word.append_assoc] using (rawLaw12 u p v)
  exact step0.trans (step1)

theorem pastBoth01 (u v p : Word Nat) :
    Derives basis ((((u ++ v) ++ p) ++ u) ++ v) ((((u ++ v) ++ p) ++ v) ++ u) := by
  have step0 : Derives basis ((((u ++ v) ++ p) ++ u) ++ v) ((((u ++ v) ++ p) ++ v) ++ u) := by
    simpa only [Word.append_assoc] using (rawLaw14 u v p)
  exact step0

theorem pastBoth11 (u v p q : Word Nat) :
    Derives basis (((((u ++ p) ++ v) ++ q) ++ u) ++ v) (((((u ++ p) ++ v) ++ q) ++ v) ++ u) := by
  have step0 : Derives basis (((((u ++ p) ++ v) ++ q) ++ u) ++ v) (((((((u ++ u) ++ p) ++ v) ++ q) ++ u) ++ u) ++ v) := by
    simpa only [Word.append_assoc] using (Derives.appendRight (rawLaw02 u ((p ++ v) ++ q)) v)
  have step1 : Derives basis (((((((u ++ u) ++ p) ++ v) ++ q) ++ u) ++ u) ++ v) (((((((u ++ u) ++ p) ++ v) ++ q) ++ v) ++ u) ++ u) := by
    simpa only [Word.append_assoc] using (Derives.prepend ((u ++ u) ++ p) (rawLaw12 v q u).symm)
  have step2 : Derives basis (((((((u ++ u) ++ p) ++ v) ++ q) ++ v) ++ u) ++ u) (((((u ++ p) ++ v) ++ q) ++ v) ++ u) := by
    simpa only [Word.append_assoc] using (rawLaw02 u (((p ++ v) ++ q) ++ v)).symm
  exact step0.trans (step1.trans (step2))

theorem pastFuture00 (u v : Word Nat) :
    Derives basis (((u ++ u) ++ v) ++ v) (((u ++ v) ++ u) ++ v) := by
  have step0 : Derives basis (((u ++ u) ++ v) ++ v) (((u ++ v) ++ u) ++ v) := by
    simpa only [Word.append_assoc] using (rawLaw04 u v)
  exact step0

theorem pastFuture10 (u v p : Word Nat) :
    Derives basis ((((u ++ p) ++ u) ++ v) ++ v) ((((u ++ p) ++ v) ++ u) ++ v) := by
  have step0 : Derives basis ((((u ++ p) ++ u) ++ v) ++ v) ((((u ++ p) ++ v) ++ u) ++ v) := by
    simpa only [Word.append_assoc] using (rawLaw11 u p v)
  exact step0

theorem pastFuture01 (u v p : Word Nat) :
    Derives basis ((((u ++ u) ++ v) ++ p) ++ v) ((((u ++ v) ++ u) ++ p) ++ v) := by
  have step0 : Derives basis ((((u ++ u) ++ v) ++ p) ++ v) ((((u ++ v) ++ u) ++ p) ++ v) := by
    simpa only [Word.append_assoc] using (rawLaw10 u v p)
  exact step0

theorem pastFuture11 (u v p q : Word Nat) :
    Derives basis (((((u ++ p) ++ u) ++ v) ++ q) ++ v) (((((u ++ p) ++ v) ++ u) ++ q) ++ v) := by
  have step0 : Derives basis (((((u ++ p) ++ u) ++ v) ++ q) ++ v) (((((((u ++ p) ++ u) ++ v) ++ v) ++ q) ++ v) ++ v) := by
    simpa only [Word.append_assoc] using (Derives.prepend ((u ++ p) ++ u) (rawLaw02 v q))
  have step1 : Derives basis (((((((u ++ p) ++ u) ++ v) ++ v) ++ q) ++ v) ++ v) (((((((u ++ p) ++ v) ++ v) ++ u) ++ q) ++ v) ++ v) := by
    simpa only [Word.append_assoc] using (Derives.appendRight (rawLaw12 u p v) ((q ++ v) ++ v))
  have step2 : Derives basis (((((((u ++ p) ++ v) ++ v) ++ u) ++ q) ++ v) ++ v) (((((u ++ p) ++ v) ++ u) ++ q) ++ v) := by
    simpa only [Word.append_assoc] using (Derives.prepend (u ++ p) (rawLaw02 v (u ++ q)).symm)
  exact step0.trans (step1.trans (step2))

theorem middleToFirst00 (u : Word Nat) :
    Derives basis ((u ++ u) ++ u) ((u ++ u) ++ u) := by
  exact Derives.refl _

theorem middleToFirst10 (u p : Word Nat) :
    Derives basis (((u ++ p) ++ u) ++ u) (((u ++ u) ++ p) ++ u) := by
  have step0 : Derives basis (((u ++ p) ++ u) ++ u) (((u ++ u) ++ p) ++ u) := by
    simpa only [Word.append_assoc] using (rawLaw15 u p).symm
  exact step0

theorem middleToFirst01 (u p : Word Nat) :
    Derives basis (((u ++ u) ++ p) ++ u) (((u ++ u) ++ p) ++ u) := by
  exact Derives.refl _

theorem middleToFirst11 (u p q : Word Nat) :
    Derives basis ((((u ++ p) ++ u) ++ q) ++ u) ((((u ++ u) ++ p) ++ q) ++ u) := by
  have step0 : Derives basis ((((u ++ p) ++ u) ++ q) ++ u) ((((u ++ u) ++ p) ++ q) ++ u) := by
    simpa only [Word.append_assoc] using (rawLaw08 u p q).symm
  exact step0

/-- Swap two later occurrences after arbitrary earlier occurrences of both. -/
theorem pastBoth (x y : Nat) (between after : List Nat) :
    L ([x] ++ between ++ [y] ++ after ++ [x,y])
      ([x] ++ between ++ [y] ++ after ++ [y,x]) := by
  cases between with
  | nil =>
      cases after with
      | nil =>
          simpa [Word.toList_append, Word.toList, Word.singleton, List.append_assoc] using
            SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
              (pastBoth00 (Word.singleton x) (Word.singleton y))
      | cons a tail =>
          simpa [Word.toList_append, Word.toList, Word.singleton, List.append_assoc] using
            SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
              (pastBoth01 (Word.singleton x) (Word.singleton y) (Word.mk a tail))
  | cons a tail =>
      cases after with
      | nil =>
          simpa [Word.toList_append, Word.toList, Word.singleton, List.append_assoc] using
            SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
              (pastBoth10 (Word.singleton x) (Word.singleton y) (Word.mk a tail))
      | cons b rest =>
          simpa [Word.toList_append, Word.toList, Word.singleton, List.append_assoc] using
            SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
              (pastBoth11 (Word.singleton x) (Word.singleton y) (Word.mk a tail) (Word.mk b rest))

/-- A later x crosses an initial y when a further y remains. -/
theorem pastFuture (x y : Nat) (between after : List Nat) :
    L ([x] ++ between ++ [x,y] ++ after ++ [y])
      ([x] ++ between ++ [y,x] ++ after ++ [y]) := by
  cases between with
  | nil =>
      cases after with
      | nil =>
          simpa [Word.toList_append, Word.toList, Word.singleton, List.append_assoc] using
            SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
              (pastFuture00 (Word.singleton x) (Word.singleton y))
      | cons a tail =>
          simpa [Word.toList_append, Word.toList, Word.singleton, List.append_assoc] using
            SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
              (pastFuture01 (Word.singleton x) (Word.singleton y) (Word.mk a tail))
  | cons a tail =>
      cases after with
      | nil =>
          simpa [Word.toList_append, Word.toList, Word.singleton, List.append_assoc] using
            SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
              (pastFuture10 (Word.singleton x) (Word.singleton y) (Word.mk a tail))
      | cons b rest =>
          simpa [Word.toList_append, Word.toList, Word.singleton, List.append_assoc] using
            SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
              (pastFuture11 (Word.singleton x) (Word.singleton y) (Word.mk a tail) (Word.mk b rest))

/-- Neither earlier occurrence is required to be at a fixed position. -/
theorem swapSeen (front : List Nat) (x y : Nat) (rest : List Nat)
    (seenX : x ∈ front) (seenY : y ∈ front) :
    L (front ++ [x,y] ++ rest) (front ++ [y,x] ++ rest) := by
  obtain ⟨before, after, rfl⟩ := splitMember x front seenX
  rcases List.mem_append.mp seenY with leftY | rightY
  · obtain ⟨initial, middle, rfl⟩ := splitMember y before leftY
    simpa [List.append_assoc] using
      ((pastBoth y x middle after).symm.context initial rest)
  · rcases List.mem_cons.mp rightY with equal | afterY
    · subst y
      exact SemigroupBasis.CoRoots.S5_107.ListDerives.refl _
    · obtain ⟨middle, suffix, rfl⟩ := splitMember y after afterY
      simpa [List.append_assoc] using
        ((pastBoth x y middle suffix).context before rest)

/-- The earlier x and later y may occur anywhere in their contexts. -/
theorem swapSeenFuture (front : List Nat) (x y : Nat) (rest : List Nat)
    (seenX : x ∈ front) (futureY : y ∈ rest) :
    L (front ++ [x,y] ++ rest) (front ++ [y,x] ++ rest) := by
  obtain ⟨initial, between, rfl⟩ := splitMember x front seenX
  obtain ⟨after, suffix, rfl⟩ := splitMember y rest futureY
  simpa [List.append_assoc] using
    ((pastFuture x y between after).context initial suffix)

/-- Move an internal occurrence to the last anchor, allowing empty gaps. -/
theorem middleToLast (x : Nat) (left right : List Nat) :
    L ([x] ++ left ++ [x] ++ right ++ [x])
      ([x] ++ left ++ right ++ [x,x]) := by
  cases left with
  | nil =>
      cases right with
      | nil => exact SemigroupBasis.CoRoots.S5_107.ListDerives.refl _
      | cons a tail =>
          simpa [Word.toList_append, Word.toList, Word.singleton, List.append_assoc] using
            SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
              (rawLaw15 (Word.singleton x) (Word.mk a tail))
  | cons a tail =>
      cases right with
      | nil =>
          simpa [List.append_assoc] using
            (SemigroupBasis.CoRoots.S5_107.ListDerives.refl (basis := basis)
              ([x] ++ (a :: tail) ++ [x,x]))
      | cons b rest =>
          have first := (rawLaw08 (Word.singleton x) (Word.mk a tail) (Word.mk b rest)).symm
          have second := rawLaw09 (Word.singleton x) (Word.mk a tail) (Word.mk b rest)
          simpa [Word.toList_append, Word.toList, Word.singleton, List.append_assoc] using
            SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord (first.trans second)

theorem replicate_snoc (count letter : Nat) :
    List.replicate (count + 1) letter = List.replicate count letter ++ [letter] := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simpa only [List.replicate_succ, List.cons_append] using congrArg (List.cons letter) ih

/-- Gather every internal x at the last anchor. The first anchor is retained.
Termination is by the arbitrary input length, not an alphabet or word bound. -/
theorem gatherInternal (x : Nat) (middle : List Nat) :
    L ([x] ++ middle ++ [x])
      ([x] ++ middle.filter (fun y => decide (y ≠ x)) ++ List.replicate (middle.count x + 1) x) := by
  by_cases present : x ∈ middle
  · obtain ⟨left, right, rfl⟩ := splitMember x middle present
    have moved := middleToLast x left right
    have smaller := (gatherInternal x (left ++ right)).append [x]
    have continued : L ([x] ++ left ++ right ++ [x,x])
        (([x] ++ (left ++ right).filter (fun y => decide (y ≠ x)) ++
          List.replicate ((left ++ right).count x + 1) x) ++ [x]) := by
      simpa [List.append_assoc] using smaller
    have joined := moved.trans continued
    have filtered :
        (left ++ x :: right).filter (fun y => decide (y ≠ x)) =
          (left ++ right).filter (fun y => decide (y ≠ x)) := by
      simp
    have counted : (left ++ x :: right).count x = (left ++ right).count x + 1 := by
      simp only [List.count_append, List.count_cons_self]
      omega
    rw [filtered, counted, replicate_snoc]
    simpa [List.append_assoc] using joined
  · have filtered : middle.filter (fun y => decide (y ≠ x)) = middle := by
      apply List.filter_eq_self.mpr
      intro y member
      exact decide_eq_true (by intro equal; subst y; exact present member)
    have counted : middle.count x = 0 := List.count_eq_zero.mpr present
    rw [filtered, counted]
    simpa using
      (SemigroupBasis.CoRoots.S5_107.ListDerives.refl (basis := basis) ([x] ++ middle ++ [x]))
termination_by middle.length
decreasing_by simp_all <;> omega

theorem contractThreeFinal (x : Nat) (middle : List Nat) :
    L ([x] ++ middle ++ [x,x,x]) ([x] ++ middle ++ [x]) := by
  cases middle with
  | nil =>
      simpa [Word.toList_append, Word.toList, Word.singleton, List.append_assoc] using
        SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord (rawLaw00 (Word.singleton x)).symm
  | cons a tail =>
      simpa [Word.toList_append, Word.toList, Word.singleton, List.append_assoc] using
        SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
          (rawLaw03 (Word.singleton x) (Word.mk a tail)).symm

/-- A positive final block contracts to one or two copies with the right
period-two count. The retained first anchor makes the threshold exact. -/
theorem capFinal (x : Nat) (middle : List Nat) (excess : Nat) :
    L ([x] ++ middle ++ List.replicate (excess + 1) x)
      ([x] ++ middle ++ List.replicate (1 + (excess + 2) % 2) x) := by
  cases excess with
  | zero => exact SemigroupBasis.CoRoots.S5_107.ListDerives.refl _
  | succ excess =>
      cases excess with
      | zero => exact SemigroupBasis.CoRoots.S5_107.ListDerives.refl _
      | succ excess =>
          have reduced : L ([x] ++ middle ++ List.replicate (excess + 3) x)
              ([x] ++ middle ++ List.replicate (excess + 1) x) := by
            simpa [List.replicate_succ, List.append_assoc] using
              (contractThreeFinal x middle).append (List.replicate excess x)
          have followed := reduced.trans (capFinal x middle excess)
          change L ([x] ++ middle ++ List.replicate (excess + 3) x)
            ([x] ++ middle ++ List.replicate (1 + (excess + 4) % 2) x)
          have parity : (excess + 4) % 2 = (excess + 2) % 2 := by omega
          rw [parity]
          exact followed
termination_by excess

/-- Unrestricted one-letter normalization: retain the first copy, gather at the
last anchor, and use msg0448's two-anchor budget. -/
theorem gatherAndCap (x : Nat) (middle : List Nat) :
    L ([x] ++ middle ++ [x])
      ([x] ++ middle.filter (fun y => decide (y ≠ x)) ++
        List.replicate (1 + tailBudget22 (middle.count x + 2)) x) := by
  have gathered := gatherInternal x middle
  have capped := capFinal x (middle.filter (fun y => decide (y ≠ x))) (middle.count x)
  exact gathered.trans capped

end Moves
end SemigroupBasis.CoRoots.Order6Day11.FordLordProfile15
