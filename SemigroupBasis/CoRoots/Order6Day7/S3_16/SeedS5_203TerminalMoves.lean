import SemigroupBasis.CoRoots.Order6Day7.S3_16.SeedS5_203DoubleGuardBridge
import SemigroupBasis.CoRoots.Order6Day7.S3_16.SeedS5_240

/-!
# Safe terminal moves for the exact rank-081 presentation

The previously checked first-occurrence bridge is used only with its two
literal nonempty guards.  Laws 05 and 11 provide the additional terminal
moves below.  The final absorption requires a final letter already present
in the stem; it therefore never cancels the distinction between a fresh
terminal doubleton and a cube.  All statements are unrestricted in the
alphabet and word length.  No finite screen is a proof premise.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank081.TerminalSeed

open SemigroupBasis
open SemigroupBasis.Examples
open DoubleGuard
open SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank087.Seed
  (firstOccurrenceSequence_append_final mem_firstOccurrenceSequence_iff)

abbrev pairWord := SemigroupBasis.CoRoots.S5_240.wordOfTerminalPair

private def substituteThree (first second third : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | letter + 3 => Word.singleton (letter + 3)

/-- Literal substitution into frozen law 11, `xyzx = xyzy`. -/
theorem derivesTerminalRetarget (first second third : Word Nat) :
    Derives basis (((first ++ second) ++ third) ++ first)
      (((first ++ second) ++ third) ++ second) := by
  have primitive :
      Derives basis (Word.mk 0 [1, 2, 0]) (Word.mk 0 [1, 2, 1]) :=
    Derives.fromBasis (e := law11) (by simp [basis])
  have substituted :=
    Derives.subst primitive (substituteThree first second third)
  simpa [substituteThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Literal substitution into frozen law 05, `xyx = xyxx`. -/
theorem derivesReturnExpansion (first middle : Word Nat) :
    Derives basis ((first ++ middle) ++ first)
      (((first ++ middle) ++ first) ++ first) := by
  have primitive :
      Derives basis (Word.mk 0 [1, 0]) (Word.mk 0 [1, 0, 0]) :=
    Derives.fromBasis (e := law05) (by simp [basis])
  have substituted :=
    Derives.subst primitive (substituteThree first middle middle)
  simpa [substituteThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- A nonempty stem renders as the same literal word with two guards. -/
theorem pairWord_of_word (stem : Word Nat) (penultimate final : Nat) :
    pairWord stem.toList penultimate final =
      ((stem ++ Word.singleton penultimate) ++ Word.singleton final) := by
  apply Word.toList_injective
  simp [pairWord, Word.toList_append, List.append_assoc]

/-- Equal stem first orders may be replayed even when the stems are empty. -/
theorem derivesSameStemFirstOrder
    (leftStem rightStem : List Nat) (penultimate final : Nat)
    (order : firstOccurrenceSequence leftStem =
      firstOccurrenceSequence rightStem) :
    Derives basis (pairWord leftStem penultimate final)
      (pairWord rightStem penultimate final) := by
  cases leftStem with
  | nil =>
      cases rightStem with
      | nil => exact Derives.refl _
      | cons first rest => simp [firstOccurrenceSequence] at order
  | cons leftFirst leftRest =>
      cases rightStem with
      | nil => simp [firstOccurrenceSequence] at order
      | cons rightFirst rightRest =>
          change Derives basis
            (pairWord (Word.mk leftFirst leftRest).toList penultimate final)
            (pairWord (Word.mk rightFirst rightRest).toList penultimate final)
          rw [pairWord_of_word, pairWord_of_word]
          exact derivesSameFirstOrderUnderDoubleGuard
            (Word.mk leftFirst leftRest) (Word.mk rightFirst rightRest)
            (Word.singleton penultimate) (Word.singleton final) order

/-- Change the final letter only when both choices occur in the stem. -/
theorem derivesChangeSeenFinal (stem : Word Nat)
    (penultimate old replacement : Nat)
    (oldSeen : old ∈ stem.toList)
    (replacementSeen : replacement ∈ stem.toList) :
    Derives basis
      ((stem ++ Word.singleton penultimate) ++ Word.singleton old)
      ((stem ++ Word.singleton penultimate) ++ Word.singleton replacement) := by
  let decorated := (stem ++ Word.singleton old) ++ Word.singleton replacement
  have order : firstOccurrenceSequence stem.toList =
      firstOccurrenceSequence decorated.toList := by
    simp only [decorated, Word.toList_append, Word.toList_singleton,
      firstOccurrenceSequence_append_final, List.mem_append, List.mem_singleton,
      oldSeen, replacementSeen, true_or, if_true]
  have middle :
      Derives basis
        ((decorated ++ Word.singleton penultimate) ++ Word.singleton old)
        ((decorated ++ Word.singleton penultimate) ++
          Word.singleton replacement) := by
    simpa [decorated, Word.append_assoc] using
      Derives.prepend stem
        (derivesTerminalRetarget (Word.singleton old)
          (Word.singleton replacement) (Word.singleton penultimate))
  exact (derivesSameFirstOrderUnderDoubleGuard stem decorated
    (Word.singleton penultimate) (Word.singleton old) order).trans <|
    middle.trans <|
      derivesSameFirstOrderUnderDoubleGuard decorated stem
        (Word.singleton penultimate) (Word.singleton replacement) order.symm

/-- Change the penultimate letter only when both choices occur in the stem. -/
theorem derivesChangeSeenPenultimate (stem : Word Nat)
    (old replacement final : Nat)
    (oldSeen : old ∈ stem.toList)
    (replacementSeen : replacement ∈ stem.toList) :
    Derives basis ((stem ++ Word.singleton old) ++ Word.singleton final)
      ((stem ++ Word.singleton replacement) ++ Word.singleton final) := by
  let decorated :=
    ((stem ++ Word.singleton replacement) ++ Word.singleton old) ++
      Word.singleton replacement
  have order : firstOccurrenceSequence stem.toList =
      firstOccurrenceSequence decorated.toList := by
    simp only [decorated, Word.toList_append, Word.toList_singleton,
      firstOccurrenceSequence_append_final, List.mem_append, List.mem_singleton,
      oldSeen, replacementSeen, true_or, if_true]
  have middle :
      Derives basis
        ((decorated ++ Word.singleton old) ++ Word.singleton final)
        ((decorated ++ Word.singleton replacement) ++ Word.singleton final) := by
    simpa [decorated, Word.append_assoc] using
      Derives.appendRight
        (Derives.prepend stem
          (derivesTerminalRetarget (Word.singleton replacement)
            (Word.singleton old) (Word.singleton replacement)).symm)
        (Word.singleton final)
  exact (derivesSameFirstOrderUnderDoubleGuard stem decorated
    (Word.singleton old) (Word.singleton final) order).trans <|
    middle.trans <|
      derivesSameFirstOrderUnderDoubleGuard decorated stem
        (Word.singleton replacement) (Word.singleton final) order.symm

private theorem split_at_mem (selected : Nat) :
    ∀ {letters : List Nat}, selected ∈ letters →
      ∃ before after, letters = before ++ selected :: after
  | [], present => False.elim (List.not_mem_nil present)
  | first :: rest, present => by
      rcases List.mem_cons.mp present with equal | later
      · subst first
        exact ⟨[], rest, rfl⟩
      · obtain ⟨before, after, shape⟩ := split_at_mem selected later
        exact ⟨first :: before, after, by simp [shape]⟩

private theorem derives_of_lists {left right actualLeft actualRight : Word Nat}
    (leftShape : left.toList = actualLeft.toList)
    (rightShape : right.toList = actualRight.toList)
    (derivation : Derives basis actualLeft actualRight) :
    Derives basis left right := by
  rw [Word.toList_injective leftShape, Word.toList_injective rightShape]
  exact derivation

/-- A final return with a nonempty intervening block can be expanded. -/
theorem derivesRepeatedFinalExpansion (stem : Word Nat)
    (penultimate final : Nat) (present : final ∈ stem.toList) :
    Derives basis
      ((stem ++ Word.singleton penultimate) ++ Word.singleton final)
      (((stem ++ Word.singleton penultimate) ++ Word.singleton final) ++
        Word.singleton final) := by
  obtain ⟨before, after, shape⟩ := split_at_mem final present
  have core := derivesReturnExpansion (Word.singleton final)
    (wordOfPrefixFinal after penultimate)
  cases before with
  | nil =>
      refine derives_of_lists ?_ ?_ core <;>
        simp only [Word.toList_append, Word.toList_singleton,
          toList_wordOfPrefixFinal, shape] <;>
        simp only [List.nil_append, List.cons_append, List.append_assoc]
  | cons first rest =>
      have lifted := Derives.prepend (Word.mk first rest) core
      refine derives_of_lists ?_ ?_ lifted <;>
        simp only [Word.toList_append, Word.toList_singleton,
          toList_wordOfPrefixFinal, shape] <;>
        simp only [Word.toList, List.nil_append, List.cons_append, List.append_assoc]

/-- Safe absorption in the generic terminal stratum.  In particular, this
does NOT apply to a fresh terminal doubleton. -/
theorem derivesGenericDoubleGuard (stem : Word Nat)
    (penultimate final guard : Nat)
    (finalSeen : final ∈ stem.toList)
    (guardSeen : guard ∈ stem.toList) :
    Derives basis
      ((stem ++ Word.singleton penultimate) ++ Word.singleton final)
      ((((stem ++ Word.singleton penultimate) ++ Word.singleton final) ++
        Word.singleton guard) ++ Word.singleton guard) := by
  have retarget := derivesChangeSeenFinal stem penultimate final guard
    finalSeen guardSeen
  have firstExpansion :=
    derivesRepeatedFinalExpansion stem penultimate guard guardSeen
  have guardSeenLater : guard ∈ (stem ++ Word.singleton penultimate).toList := by
    simp [Word.toList_append, guardSeen]
  have secondExpansion :=
    derivesRepeatedFinalExpansion (stem ++ Word.singleton penultimate)
      guard guard guardSeenLater
  have order :
      firstOccurrenceSequence
          (((stem ++ Word.singleton penultimate) ++ Word.singleton guard).toList) =
        firstOccurrenceSequence
          (((stem ++ Word.singleton penultimate) ++ Word.singleton final).toList) := by
    simp only [Word.toList_append, Word.toList_singleton,
      firstOccurrenceSequence_append_final, List.mem_append, List.mem_singleton,
      guardSeen, finalSeen, true_or, if_true]
  have finish := derivesSameFirstOrderUnderDoubleGuard
    ((stem ++ Word.singleton penultimate) ++ Word.singleton guard)
    ((stem ++ Word.singleton penultimate) ++ Word.singleton final)
    (Word.singleton guard) (Word.singleton guard) order
  exact retarget.trans <| firstExpansion.trans <|
    secondExpansion.trans finish

/-- Equal full first-occurrence orders have the same initial letter. -/
theorem head_eq_of_firstOrder {left right : Word Nat}
    (order : firstOccurrenceSequence left.toList =
      firstOccurrenceSequence right.toList) : left.head = right.head := by
  have heads := congrArg List.head? order
  simpa [Word.toList, firstOccurrenceSequence] using heads

end SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank081.TerminalSeed
