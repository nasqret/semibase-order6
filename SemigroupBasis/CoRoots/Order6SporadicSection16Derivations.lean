import SemigroupBasis.CoRoots.Order6SporadicSection16Basis
import SemigroupBasis.CoRoots.S5_107ListDerives

/-!
Context-safe derivations for Lee and Zhang (2015), Proposition 16.1 and
Lemma 16.3, pp.49-51. These are unrestricted equational derivations from
the exact ten-law basis, including every empty optional-context boundary.
-/

namespace SemigroupBasis.CoRoots.Order6SporadicSection16

open SemigroupBasis

abbrev ListDerives : List Nat → List Nat → Prop := S5_107.ListDerives basis

private def replacement (x y z h k : Word Nat) : Nat → Word Nat
  | 0 => x
  | 1 => y
  | 2 => z
  | 3 => h
  | _ => k

private theorem instantiate (law : Identity Nat) (member : law ∈ basis)
    (x y z h k : Word Nat) :
    ListDerives (law.lhs.bind (replacement x y z h k)).toList
      (law.rhs.bind (replacement x y z h k)).toList :=
  S5_107.ListDerives.ofWord
    (Derives.subst (Derives.fromBasis (e := law) member) (replacement x y z h k))

theorem listPower (x : Nat) : ListDerives [x, x, x] [x, x] := by
  exact instantiate lawPower (by decide) (Word.singleton x) (Word.singleton x)
    (Word.singleton x) (Word.singleton x) (Word.singleton x)

/-- Duplicate a first occurrence when a later occurrence is displayed. -/
theorem duplicateFirst (x : Nat) (gap : List Nat) :
    ListDerives ([x] ++ gap ++ [x]) ([x, x] ++ gap ++ [x]) := by
  cases gap with
  | nil => exact (listPower x).symm
  | cons h t =>
      have raw := instantiate lawLeft (by decide) (Word.singleton x)
        (S5_107.listWordOfCons h t) (Word.singleton x) (Word.singleton x) (Word.singleton x)
      simpa [lawLeft, replacement, Word.bind, Word.toList, Word.append,
        Word.singleton, S5_107.listWordOfCons, List.append_assoc] using raw.symm

/-- Duplicate a later occurrence with its earlier occurrence protected. -/
theorem duplicateLast (x : Nat) (gap : List Nat) :
    ListDerives ([x] ++ gap ++ [x]) ([x] ++ gap ++ [x, x]) := by
  cases gap with
  | nil => exact (listPower x).symm
  | cons h t =>
      have raw := instantiate lawRight (by decide) (Word.singleton x)
        (S5_107.listWordOfCons h t) (Word.singleton x) (Word.singleton x) (Word.singleton x)
      simpa [lawRight, replacement, Word.bind, Word.toList, Word.append,
        Word.singleton, S5_107.listWordOfCons, List.append_assoc] using raw.symm

theorem duplicateLastOfSeen (stem : List Nat) (x : Nat) (seen : x ∈ stem) :
    ListDerives (stem ++ [x]) (stem ++ [x, x]) := by
  obtain ⟨before, gap, shape⟩ := List.mem_iff_append.mp seen
  simpa [shape, List.append_assoc] using (duplicateLast x gap).prepend before

theorem duplicateFirstOfSeen (x : Nat) (rest : List Nat) (seen : x ∈ rest) :
    ListDerives (x :: rest) (x :: x :: rest) := by
  obtain ⟨gap, after, shape⟩ := List.mem_iff_append.mp seen
  simpa [shape, List.append_assoc] using (duplicateFirst x gap).append after

/-- Move a later x to its first displayed occurrence immediately before a square.
The empty middle case is reflexive, not an empty substitution into (16.1b). -/
theorem collectBeforeSquare (x z : Nat) (gap : List Nat) :
    ListDerives ([x] ++ gap ++ [x, z, z]) ([x, x] ++ gap ++ [z, z]) := by
  cases gap with
  | nil => exact S5_107.ListDerives.refl _
  | cons h t =>
      have raw := instantiate lawCollect (by decide) (Word.singleton x)
        (S5_107.listWordOfCons h t) (Word.singleton z) (Word.singleton x) (Word.singleton x)
      simpa [lawCollect, replacement, Word.bind, Word.toList, Word.append,
        Word.singleton, S5_107.listWordOfCons, List.append_assoc] using raw

/-- Both optional-H instances of (16.1c). -/
theorem moveAnchor (anchor y : Nat) (gap : List Nat) :
    ListDerives ([anchor, anchor] ++ gap ++ [y, y])
      ([anchor] ++ gap ++ [y, y, anchor]) := by
  cases gap with
  | nil =>
      exact instantiate lawAnchor (by decide) (Word.singleton anchor) (Word.singleton y)
        (Word.singleton anchor) (Word.singleton anchor) (Word.singleton anchor)
  | cons h t =>
      have raw := instantiate lawAnchorH (by decide) (Word.singleton anchor) (Word.singleton y)
        (Word.singleton anchor) (S5_107.listWordOfCons h t) (Word.singleton anchor)
      simpa [lawAnchorH, replacement, Word.bind, Word.toList, Word.append,
        Word.singleton, S5_107.listWordOfCons, List.append_assoc] using raw

/-- All four optional-H/K instances of (16.1d). -/
theorem swapOrdered (x y : Nat) (firstGap secondGap : List Nat) :
    ListDerives ([x] ++ firstGap ++ [y] ++ secondGap ++ [x, y])
      ([x] ++ firstGap ++ [y] ++ secondGap ++ [y, x]) := by
  cases firstGap with
  | nil =>
      cases secondGap with
      | nil =>
          exact instantiate lawSwap (by decide) (Word.singleton x) (Word.singleton y)
            (Word.singleton x) (Word.singleton x) (Word.singleton x)
      | cons h t =>
          have raw := instantiate lawSwapK (by decide) (Word.singleton x) (Word.singleton y)
            (Word.singleton x) (Word.singleton x) (S5_107.listWordOfCons h t)
          simpa [lawSwapK, replacement, Word.bind, Word.toList, Word.append,
            Word.singleton, S5_107.listWordOfCons, List.append_assoc] using raw
  | cons h t =>
      cases secondGap with
      | nil =>
          have raw := instantiate lawSwapH (by decide) (Word.singleton x) (Word.singleton y)
            (Word.singleton x) (S5_107.listWordOfCons h t) (Word.singleton x)
          simpa [lawSwapH, replacement, Word.bind, Word.toList, Word.append,
            Word.singleton, S5_107.listWordOfCons, List.append_assoc] using raw
      | cons k s =>
          have raw := instantiate lawSwapHK (by decide) (Word.singleton x) (Word.singleton y)
            (Word.singleton x) (S5_107.listWordOfCons h t) (S5_107.listWordOfCons k s)
          simpa [lawSwapHK, replacement, Word.bind, Word.toList, Word.append,
            Word.singleton, S5_107.listWordOfCons, List.append_assoc] using raw

/-- Any two already-seen letters may be swapped in an adjacent later pair.
The two possible orders of their earlier occurrences are handled explicitly. -/
theorem swapAfterSeen (stem : List Nat) (x y : Nat)
    (seenX : x ∈ stem) (seenY : y ∈ stem) :
    ListDerives (stem ++ [x, y]) (stem ++ [y, x]) := by
  by_cases same : x = y
  · subst y
    exact S5_107.ListDerives.refl _
  induction stem with
  | nil => simp at seenX
  | cons head tail ih =>
      by_cases headX : head = x
      · subst head
        have inTail : y ∈ tail := (List.mem_cons.mp seenY).resolve_left (Ne.symm same)
        obtain ⟨firstGap, secondGap, shape⟩ := List.mem_iff_append.mp inTail
        simpa [shape, List.append_assoc] using swapOrdered x y firstGap secondGap
      · by_cases headY : head = y
        · subst head
          have inTail : x ∈ tail := (List.mem_cons.mp seenX).resolve_left same
          obtain ⟨firstGap, secondGap, shape⟩ := List.mem_iff_append.mp inTail
          simpa [shape, List.append_assoc] using (swapOrdered y x firstGap secondGap).symm
        · have xTail : x ∈ tail := (List.mem_cons.mp seenX).resolve_left (Ne.symm headX)
          have yTail : y ∈ tail := (List.mem_cons.mp seenY).resolve_left (Ne.symm headY)
          simpa using (ih xTail yTail).prepend [head]

/-- The permutation step in Lemma 16.3: a block containing only letters seen
before that block may be rearranged arbitrarily inside its fixed context. -/
theorem permuteSeenBlock {left right : List Nat} (permutation : left.Perm right)
    (stem : List Nat) (seen : ∀ x ∈ left, x ∈ stem) :
    ListDerives (stem ++ left) (stem ++ right) := by
  induction permutation generalizing stem with
  | nil => exact S5_107.ListDerives.refl _
  | cons head permutation ih =>
      have permuted := ih (stem ++ [head]) (fun x member =>
        List.mem_append.mpr (Or.inl (seen x (List.mem_cons_of_mem head member))))
      simpa [List.append_assoc] using permuted
  | swap x y rest =>
      have hx : x ∈ stem := seen x (by simp)
      have hy : y ∈ stem := seen y (by simp)
      simpa [List.append_assoc] using ((swapAfterSeen stem x y hx hy).append rest).symm
  | trans first second ihFirst ihSecond =>
      exact (ihFirst stem seen).trans
        (ihSecond stem (fun x member => seen x (first.mem_iff.mpr member)))

#print axioms duplicateFirstOfSeen
#print axioms duplicateLastOfSeen
#print axioms collectBeforeSquare
#print axioms swapAfterSeen
#print axioms permuteSeenBlock

end SemigroupBasis.CoRoots.Order6SporadicSection16
