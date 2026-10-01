import SemigroupBasis.CoRoots.Order6SporadicSection16Derivations

/-!
The marker-insertion and block-erasure steps of Lee and Zhang (2015),
Lemma 16.3, p.51. We expose the earlier-square premise used after nonsimple
first occurrences have been doubled. No completeness or normalization
statement is assumed: every move below is derived from Proposition 16.1.
-/

namespace SemigroupBasis.CoRoots.Order6SporadicSection16

open SemigroupBasis

/-- A concrete earlier square, not merely an earlier occurrence. -/
def SquareSeen (letter : Nat) (stem : List Nat) : Prop :=
  ∃ before after, stem = before ++ [letter, letter] ++ after

theorem squareSeen_mem {letter : Nat} {stem : List Nat}
    (seen : SquareSeen letter stem) : letter ∈ stem := by
  obtain ⟨before, after, shape⟩ := seen
  simp [shape]

theorem squareSeen_append {letter : Nat} {stem : List Nat}
    (seen : SquareSeen letter stem) (suffix : List Nat) :
    SquareSeen letter (stem ++ suffix) := by
  obtain ⟨before, after, shape⟩ := seen
  exact ⟨before, after ++ suffix, by simp [shape, List.append_assoc]⟩

/-- Gather a later occurrence into an earlier square before a protected square,
then reduce the resulting cube by (16.1a). -/
theorem eraseSquareSeenBeforeSquare (stem : List Nat) (letter guard : Nat)
    (seen : SquareSeen letter stem) :
    ListDerives (stem ++ [letter, guard, guard]) (stem ++ [guard, guard]) := by
  obtain ⟨before, gap, shape⟩ := seen
  have gather :
      ListDerives (stem ++ [letter, guard, guard])
        (before ++ [letter, letter, letter] ++ gap ++ [guard, guard]) := by
    simpa [shape, List.append_assoc] using
      (collectBeforeSquare letter guard (letter :: gap)).prepend before
  have reduce :
      ListDerives (before ++ [letter, letter, letter] ++ gap ++ [guard, guard])
        (stem ++ [guard, guard]) := by
    simpa [shape, List.append_assoc] using
      S5_107.ListDerives.context before (gap ++ [guard, guard]) (listPower letter)
  exact gather.trans reduce

/-- The three displayed transformations at the start of p.51, with the two
uses of (16.1a) separated into typed steps. The last letter must already occur
in the stem; otherwise adding the anchor could change the simple-letter key. -/
theorem appendAnchorAfterSeen (anchor letter : Nat) (gap : List Nat)
    (seen : letter ∈ [anchor, anchor] ++ gap) :
    ListDerives ([anchor, anchor] ++ gap ++ [letter])
      ([anchor, anchor] ++ gap ++ [letter, anchor, anchor]) := by
  let stem := [anchor, anchor] ++ gap
  have step1 : ListDerives (stem ++ [letter]) (stem ++ [letter, letter]) :=
    duplicateLastOfSeen stem letter seen
  have step2 : ListDerives (stem ++ [letter, letter])
      ([anchor] ++ gap ++ [letter, letter, anchor]) := moveAnchor anchor letter gap
  have step3 : ListDerives ([anchor] ++ gap ++ [letter, letter, anchor])
      (stem ++ [letter, letter, anchor]) := by
    simpa [stem, List.append_assoc] using duplicateFirst anchor (gap ++ [letter, letter])
  have step4 : ListDerives (stem ++ [letter, letter, anchor])
      (stem ++ [letter, anchor]) := by
    simpa [List.append_assoc] using (duplicateLastOfSeen stem letter seen).symm.append [anchor]
  have anchorSeen : anchor ∈ stem ++ [letter] := by simp [stem]
  have step5 : ListDerives (stem ++ [letter, anchor])
      (stem ++ [letter, anchor, anchor]) := by
    simpa [List.append_assoc] using duplicateLastOfSeen (stem ++ [letter]) anchor anchorSeen
  exact step1.trans (step2.trans (step3.trans (step4.trans step5)))

/-- Remove an entire later block before a square, provided each of its letters
has a protected earlier square. The induction never loses that premise. -/
theorem eraseSquaredBlockBeforeSquare (stem block : List Nat) (guard : Nat)
    (seen : ∀ letter ∈ block, SquareSeen letter stem) :
    ListDerives (stem ++ block ++ [guard, guard]) (stem ++ [guard, guard]) := by
  induction block generalizing stem with
  | nil =>
      simpa only [List.append_nil] using
        S5_107.ListDerives.refl (basis := basis) (stem ++ [guard, guard])
  | cons letter rest ih =>
      have restSeen : ∀ x ∈ rest, SquareSeen x (stem ++ [letter]) := by
        intro x member
        exact squareSeen_append (seen x (List.mem_cons_of_mem letter member)) [letter]
      have eraseRest : ListDerives (stem ++ (letter :: rest) ++ [guard, guard])
          (stem ++ [letter, guard, guard]) := by
        simpa [List.append_assoc] using ih (stem ++ [letter]) restSeen
      exact eraseRest.trans (eraseSquareSeenBeforeSquare stem letter guard (seen letter (by simp)))

private theorem splitLast (letters : List Nat) :
    letters ≠ [] → ∃ before last, letters = before ++ [last] := by
  induction letters with
  | nil => intro nonempty; exact False.elim (nonempty rfl)
  | cons head tail ih =>
      intro _
      cases tail with
      | nil => exact ⟨[], head, rfl⟩
      | cons next rest =>
          obtain ⟨before, last, shape⟩ := ih (by simp)
          exact ⟨head :: before, last, by simp [shape]⟩

/-- The block-collapse step of Lemma 16.3. Once its letters have earlier
squares, any NONEMPTY non-first-occurrence block may be replaced by the
anchor square, while retaining the preceding word exactly. This statement
does not silently discard the earlier-square condition. -/
theorem collapseSquaredSeenBlock (anchor : Nat) (gap block : List Nat)
    (nonempty : block ≠ [])
    (seen : ∀ letter ∈ block, SquareSeen letter ([anchor, anchor] ++ gap)) :
    ListDerives ([anchor, anchor] ++ gap ++ block)
      ([anchor, anchor] ++ gap ++ [anchor, anchor]) := by
  obtain ⟨before, last, shape⟩ := splitLast block nonempty
  have lastMem : last ∈ block := by simp [shape]
  have lastSeen : last ∈ [anchor, anchor] ++ gap := squareSeen_mem (seen last lastMem)
  have lastExtended : last ∈ [anchor, anchor] ++ (gap ++ before) := by
    have member : last ∈ ([anchor, anchor] ++ gap) ++ before :=
      List.mem_append.mpr (Or.inl lastSeen)
    simpa [List.append_assoc] using member
  have addMarker :
      ListDerives ([anchor, anchor] ++ gap ++ block)
        (([anchor, anchor] ++ gap) ++ block ++ [anchor, anchor]) := by
    simpa [shape, List.append_assoc] using appendAnchorAfterSeen anchor last (gap ++ before) lastExtended
  exact addMarker.trans (eraseSquaredBlockBeforeSquare ([anchor, anchor] ++ gap) block anchor seen)

#print axioms eraseSquareSeenBeforeSquare
#print axioms appendAnchorAfterSeen
#print axioms eraseSquaredBlockBeforeSquare
#print axioms collapseSquaredSeenBlock

end SemigroupBasis.CoRoots.Order6SporadicSection16
