import SemigroupBasis.CoRoots.Order6Day10.S3_6op.Rank073Semantics

/-!
# Rank073: eligible prefix letters for the exact S5_303 signature

A support letter may be prepended to a nonsingleton word unless it is the
globally unique final letter. This is a semantic lower-factor lemma, not an
unguarded B12 rewrite. The lower completeness theorem is used only to turn
the proved exact signature into lower validity.
-/

namespace SemigroupBasis.CoRoots.Order6Day10.S3_6op.Rank073Eligibility

open SemigroupBasis
open SemigroupBasis.CoRoots.S5_83
open SemigroupBasis.CoRoots.S5_303 (FinalLetter UniqueFinalPair)
open SemigroupBasis.CoRoots.Order6Day10.S3_6op.Rank073Replay

def Eligible (word : Word Nat) (letter : Nat) : Prop :=
  letter ∈ word.toList ∧ ∀ penultimate, ¬ UniqueFinalPair word penultimate letter

theorem longTerminalPair (word : Word Nat) (long : word.tail ≠ []) :
    ∃ stem penultimate final, terminalSplit word = .pair stem penultimate final := by
  cases shape : terminalSplit word with
  | singleton final =>
      have reconstruct := terminalSplit_renderWord word
      rw [shape] at reconstruct
      have same : Word.singleton final = word := reconstruct
      have tailNil : word.tail = [] := by rw [← same]; rfl
      exact False.elim (long tailNil)
  | pair stem penultimate final => exact ⟨stem, penultimate, final, rfl⟩

theorem terminalSplitPrepend (letter : Nat) (word : Word Nat) :
    terminalSplit (Word.singleton letter ++ word) =
      match terminalSplit word with
      | .singleton final => .pair [] letter final
      | .pair stem penultimate final => .pair (letter :: stem) penultimate final := rfl

theorem eligibleOfSignature {left right : Word Nat} (same : LowerSignature left right)
    {letter : Nat} (eligible : Eligible left letter) : Eligible right letter := by
  refine ⟨(same.support letter).mp eligible.1, ?_⟩
  intro penultimate pair
  exact eligible.2 penultimate ((same.uniqueFinalPair penultimate letter).mpr pair)

/-- Every initial letter of a nonsingleton word is eligible. -/
theorem eligibleHead (word : Word Nat) (long : word.tail ≠ []) : Eligible word word.head := by
  refine ⟨by simp [Word.toList], ?_⟩
  intro tested pair
  obtain ⟨stem, penultimate, final, shape⟩ := longTerminalPair word long
  have parts : penultimate = tested ∧ final = word.head ∧ final ≠ penultimate ∧ final ∉ stem := by
    simpa [UniqueFinalPair, shape] using pair
  have rendered := terminalSplit_renderList word
  rw [shape] at rendered
  cases stem with
  | nil =>
      have headEqual : penultimate = word.head := by
        have heads := congrArg List.head? rendered
        simpa [TerminalSplit.renderList, Word.toList] using heads
      exact parts.2.2.1 (parts.2.1.trans headEqual.symm)
  | cons first rest =>
      have headEqual : first = word.head := by
        have heads := congrArg List.head? rendered
        simpa [TerminalSplit.renderList, Word.toList] using heads
      exact parts.2.2.2 (by simp [parts.2.1, headEqual])

theorem eligiblePrefixSignature (word : Word Nat) (letter : Nat)
    (long : word.tail ≠ []) (eligible : Eligible word letter) :
    LowerSignature word (Word.singleton letter ++ word) := by
  obtain ⟨stem, penultimate, final, shape⟩ := longTerminalPair word long
  have expanded : terminalSplit (Word.mk letter (word.head :: word.tail)) =
      .pair (letter :: stem) penultimate final := by
    change terminalSplit (Word.singleton letter ++ word) = .pair (letter :: stem) penultimate final
    rw [terminalSplitPrepend, shape]
  constructor
  · intro tested
    change (tested ∈ word.toList ↔ tested ∈ letter :: word.toList)
    constructor
    · intro member
      exact List.mem_cons_of_mem letter member
    · intro member
      have either : tested = letter ∨ tested ∈ word.toList := List.mem_cons.mp member
      rcases either with equal | old
      · subst tested
        exact eligible.1
      · exact old
  · simp [IsSingletonWord, shape, expanded]
  · intro tested
    simp [FinalLetter, shape, expanded]
  · intro testedPenultimate testedFinal
    constructor
    · intro pair
      have parts : penultimate = testedPenultimate ∧ final = testedFinal ∧
          final ≠ penultimate ∧ final ∉ stem := by
        simpa [UniqueFinalPair, shape] using pair
      have notInserted : final ≠ letter := by
        intro equal
        apply eligible.2 penultimate
        simpa [UniqueFinalPair, shape] using
          (show penultimate = penultimate ∧ final = letter ∧ final ≠ penultimate ∧ final ∉ stem from
            ⟨rfl, equal, parts.2.2.1, parts.2.2.2⟩)
      have absent : final ∉ letter :: stem := by simp [notInserted, parts.2.2.2]
      simpa [UniqueFinalPair, expanded] using
        (show penultimate = testedPenultimate ∧ final = testedFinal ∧
            final ≠ penultimate ∧ final ∉ letter :: stem from
          ⟨parts.1, parts.2.1, parts.2.2.1, absent⟩)
    · intro pair
      have parts : penultimate = testedPenultimate ∧ final = testedFinal ∧
          final ≠ penultimate ∧ final ∉ letter :: stem := by
        simpa [UniqueFinalPair, expanded] using pair
      have absent : final ∉ stem := by
        intro member
        exact parts.2.2.2 (by simp [member])
      simpa [UniqueFinalPair, shape] using
        (show penultimate = testedPenultimate ∧ final = testedFinal ∧
            final ≠ penultimate ∧ final ∉ stem from
          ⟨parts.1, parts.2.1, parts.2.2.1, absent⟩)

theorem eligiblePrefixValid (word : Word Nat) (letter : Nat)
    (long : word.tail ≠ []) (eligible : Eligible word letter) :
    (Identity.mk word (Word.singleton letter ++ word)).SatisfiedBy rightTable.semigroup := by
  have derivation := SemigroupBasis.CoRoots.S5_303.derives_of_sameContentEndpointSignature
    (eligiblePrefixSignature word letter long eligible)
  exact derivation.sound SemigroupBasis.CoRoots.S5_303.models

/-- Semantic congruence only: this does not claim a B12 prefix-free rewrite. -/
theorem lowerValidPrepend {left right : Word Nat}
    (valid : (Identity.mk left right).SatisfiedBy rightTable.semigroup) (guard : Word Nat) :
    (Identity.mk (guard ++ left) (guard ++ right)).SatisfiedBy rightTable.semigroup := by
  intro valuation
  simpa only [Semigroup.eval_append] using
    congrArg (fun value => rightTable.semigroup.mul (rightTable.semigroup.eval valuation guard) value)
      (valid valuation)

end SemigroupBasis.CoRoots.Order6Day10.S3_6op.Rank073Eligibility
