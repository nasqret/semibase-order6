import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_5595ActionSemantics
import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_5595Derivations

/-! Heavy terminals are brought to cubes and compared through the proved lower theory.
No extra count profile or universal free-band key is assumed. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_5595

open SemigroupBasis
open S4_71Suffix

def cube (word : Word Nat) : Word Nat := (word ++ word) ++ word
def cubicWord (front : List Nat) (letter : Nat) : Word Nat := put front (cube (Word.singleton letter))

theorem put_append_word (front : List Nat) (left right : Word Nat) :
    put front (left ++ right) = put front left ++ right := by
  apply Word.toList_injective
  simp only [put_toList, Word.toList_append, List.append_assoc]

theorem put_derives {system : List (Identity Nat)} {left right : Word Nat}
    (front : List Nat) (derivation : Derives system left right) :
    Derives system (put front left) (put front right) := by
  induction front with
  | nil => exact derivation
  | cons first rest ih => exact Derives.prepend (Word.singleton first) ih

theorem lower_eval_put (valuation : Nat → Fin 4) (front : List Nat) (suffix : Word Nat) :
    lowerTable.semigroup.eval valuation (put front suffix) =
      lowerMul (listEval valuation front) (lowerTable.semigroup.eval valuation suffix) := by
  rw [← listEval_toList, put_toList, listEval_append, listEval_toList]

theorem lift_lower_words {system : List (Identity Nat)} (rules : S4_71Suffix.Rules system)
    (left right suffix : Word Nat)
    (same : ∀ valuation, lowerTable.semigroup.eval valuation left = lowerTable.semigroup.eval valuation right) :
    Derives system (left ++ suffix) (right ++ suffix) := by
  have lifted := rules.derivesLists left.toList right.toList suffix (by
    intro valuation
    simpa only [listEval_toList] using same valuation)
  simpa only [put_word] using lifted

private theorem split_two_occurrences (word : List Nat) (selected : Nat) :
    2 ≤ word.count selected →
      ∃ before middle after, word = before ++ selected :: (middle ++ selected :: after) := by
  induction word with
  | nil => intro count; simp at count
  | cons first rest ih =>
      intro count
      by_cases equal : first = selected
      · subst first
        have positive : 0 < rest.count selected := by
          simp only [List.count_cons_self] at count
          omega
        obtain ⟨middle, after, shape⟩ := List.append_of_mem (List.count_pos_iff.mp positive)
        exact ⟨[], middle, after, by simp [shape]⟩
      · have restCount : 2 ≤ rest.count selected := by
          simpa only [List.count_cons_of_ne equal] using count
        obtain ⟨before, middle, after, shape⟩ := ih restCount
        exact ⟨first :: before, middle, after, by simp [shape]⟩

namespace TerminalRules

variable {system : List (Identity Nat)}

private theorem gather_pair (rules : TerminalRules system) (middle after : List Nat) (selected : Nat) :
    Derives system (endWord (selected :: (middle ++ selected :: after)) selected)
      (put middle ((Word.singleton selected ++ Word.singleton selected) ++ put after (Word.singleton selected))) := by
  cases middle with
  | nil => exact Derives.refl _
  | cons first rest =>
      have sourceShape : endWord (selected :: ((first :: rest) ++ selected :: after)) selected =
          (((Word.singleton selected ++ Word.mk first rest) ++ Word.singleton selected) ++
            put after (Word.singleton selected)) := by
        apply Word.toList_injective
        simp only [endWord, put_toList, Word.toList_append, Word.toList_singleton, List.append_assoc]
        simp only [Word.toList, List.cons_append, List.nil_append, List.append_assoc]
      have targetShape : put (first :: rest)
          ((Word.singleton selected ++ Word.singleton selected) ++ put after (Word.singleton selected)) =
          (((Word.mk first rest ++ Word.singleton selected) ++ Word.singleton selected) ++
            put after (Word.singleton selected)) := by
        apply Word.toList_injective
        simp only [put_toList, Word.toList_append, Word.toList_singleton, List.append_assoc]
        rfl
      rw [sourceShape, targetShape]
      exact rules.prefixRules.gather (Word.singleton selected) (Word.mk first rest) (put after (Word.singleton selected))

private theorem finish_pair (rules : TerminalRules system) (after : List Nat) (selected : Nat) :
    Derives system ((Word.singleton selected ++ Word.singleton selected) ++ put after (Word.singleton selected))
      (put after (cube (Word.singleton selected))) := by
  cases after with
  | nil => exact Derives.refl _
  | cons first rest =>
      change Derives system
        ((Word.singleton selected ++ Word.singleton selected) ++ put (Word.mk first rest).toList (Word.singleton selected))
        (put (Word.mk first rest).toList (cube (Word.singleton selected)))
      rw [put_word, put_word]
      simpa only [cube, Word.append_assoc] using rules.heavyGather (Word.singleton selected) (Word.mk first rest)

/-- Two prefix occurrences plus the terminal produce an actual terminal cube. -/
theorem derivesHeavyExtraction (rules : TerminalRules system) (front : List Nat) (selected : Nat)
    (heavy : 2 ≤ front.count selected) :
    ∃ rest, Derives system (endWord front selected) (cubicWord rest selected) := by
  obtain ⟨before, middle, after, rfl⟩ := split_two_occurrences front selected heavy
  refine ⟨(before ++ middle) ++ after, ?_⟩
  have localDerivation := (rules.gather_pair middle after selected).trans
    (put_derives middle (rules.finish_pair after selected))
  have result := put_derives before localDerivation
  simpa only [endWord, cubicWord, put_append, List.append_assoc] using result

theorem derivesCubeAbsorbCube (rules : TerminalRules system) (word : Word Nat) :
    Derives system (cube word) (cube word ++ cube word) := by
  have first := rules.cubeExpand word
  have second := first.appendRight word
  have third : Derives system (((((word ++ word) ++ word) ++ word) ++ word))
      (cube word ++ cube word) := by
    simpa only [cube, Word.append_assoc] using first.appendRight (word ++ word)
  exact first.trans (second.trans third)

private theorem lower_square_cube (before value : Fin 4) :
    lowerMul before (lowerMul value value) = lowerMul before (lowerMul (lowerMul value value) value) := by decide +revert

private theorem lower_cube_absorb (before value : Fin 4) :
    lowerMul (lowerMul before (lowerMul (lowerMul value value) value)) value =
      lowerMul before (lowerMul (lowerMul value value) value) := by decide +revert

/-- Common cube padding transports a genuine lower identity into the heavy stratum. -/
theorem derivesCubeEndings (rules : TerminalRules system) (leftFront rightFront : List Nat)
    (leftLast rightLast : Nat)
    (same : ∀ valuation, lowerTable.semigroup.eval valuation (cubicWord leftFront leftLast) =
      lowerTable.semigroup.eval valuation (cubicWord rightFront rightLast)) :
    Derives system (cubicWord leftFront leftLast) (cubicWord rightFront rightLast) := by
  let leftLetter := Word.singleton leftLast
  let rightLetter := Word.singleton rightLast
  let leftWord := cubicWord leftFront leftLast
  let rightWord := cubicWord rightFront rightLast
  let rightPrefix := put rightFront (rightLetter ++ rightLetter)
  have paddingLower : ∀ valuation, lowerTable.semigroup.eval valuation rightPrefix =
      lowerTable.semigroup.eval valuation (rightWord ++ (leftLetter ++ leftLetter)) := by
    intro valuation
    have equivalent : lowerTable.semigroup.eval valuation leftWord = lowerTable.semigroup.eval valuation rightWord := same valuation
    have leftAbsorb : lowerMul (lowerTable.semigroup.eval valuation leftWord) (valuation leftLast) =
        lowerTable.semigroup.eval valuation leftWord := by
      simpa only [leftWord, cubicWord, lower_eval_put, cube, Semigroup.eval_append, Semigroup.eval_singleton] using
        lower_cube_absorb (listEval valuation leftFront) (valuation leftLast)
    have rightAbsorb : lowerMul (lowerTable.semigroup.eval valuation rightWord) (valuation leftLast) =
        lowerTable.semigroup.eval valuation rightWord := by
      rw [← equivalent]
      exact leftAbsorb
    have prefixEqual : lowerTable.semigroup.eval valuation rightPrefix = lowerTable.semigroup.eval valuation rightWord := by
      simpa only [rightPrefix, rightWord, rightLetter, cubicWord, lower_eval_put, cube,
        Semigroup.eval_append, Semigroup.eval_singleton] using lower_square_cube (listEval valuation rightFront) (valuation rightLast)
    have doubleAbsorb : lowerTable.semigroup.eval valuation (rightWord ++ (leftLetter ++ leftLetter)) =
        lowerTable.semigroup.eval valuation rightWord := by
      simp only [Semigroup.eval_append, leftLetter, Semigroup.eval_singleton]
      change lowerMul (lowerTable.semigroup.eval valuation rightWord) (lowerMul (valuation leftLast) (valuation leftLast)) = _
      rw [← lower_assoc, rightAbsorb, rightAbsorb]
    exact prefixEqual.trans doubleAbsorb.symm
  have liftedPadding := lift_lower_words rules.prefixRules rightPrefix
    (rightWord ++ (leftLetter ++ leftLetter)) rightLetter paddingLower
  have firstPadding : Derives system rightWord ((rightWord ++ (leftLetter ++ leftLetter)) ++ rightLetter) := by
    simpa only [rightWord, rightPrefix, rightLetter, cubicWord, cube, put_append_word, Word.append_assoc] using liftedPadding
  have switchPadding : Derives system ((rightWord ++ (leftLetter ++ leftLetter)) ++ rightLetter)
      (rightWord ++ cube leftLetter) := by
    simpa only [rightWord, rightLetter, cubicWord, cube, put_append_word, Word.append_assoc] using
      Derives.prepend (put rightFront rightLetter) (rules.heavySwitch rightLetter leftLetter)
  have rightPadding := firstPadding.trans switchPadding
  have leftPadding : Derives system leftWord (leftWord ++ cube leftLetter) := by
    simpa only [leftWord, leftLetter, cubicWord, put_append_word] using
      put_derives leftFront (rules.derivesCubeAbsorbCube leftLetter)
  have middle := lift_lower_words rules.prefixRules leftWord rightWord (cube leftLetter) same
  exact leftPadding.trans (middle.trans rightPadding.symm)

end TerminalRules
end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_5595
