import SemigroupBasis.CoRoots.Order6Day7.Level2.Rank109

/-!
# Arbitrary connected components with a fixed final letter

The previously proved ordered envelope is reversed through nine explicit
rank109 law derivations. It retains the original final variable and capped
multiplicities. Interior commutation then removes the unnecessary first-order
restriction. Every comparison below ranges over arbitrary finite lists.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace SemigroupBasis.CoRoots.Order6Day7.Level2.Rank109.FinalEnvelope

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots

theorem listDeleteMiddle (endpoint : Nat) (left right : List Nat) :
    ListDerives (endpoint :: left ++ endpoint :: right ++ [endpoint])
      (endpoint :: left ++ right ++ [endpoint]) := by
  have reversed := reverseListTransport
    (S3_16.Rank105.OrderedEnvelope.listDeleteMiddle endpoint right.reverse left.reverse)
  simpa [List.reverse_append, List.reverse_cons, List.append_assoc] using reversed

theorem listInteriorSwap (endpoint : Nat) (left right : List Nat)
    (leftNonempty : left ≠ []) (rightNonempty : right ≠ []) :
    ListDerives (endpoint :: left ++ right ++ [endpoint])
      (endpoint :: right ++ left ++ [endpoint]) := by
  obtain ⟨leftHead, leftTail, rfl⟩ := List.exists_cons_of_ne_nil leftNonempty
  obtain ⟨rightHead, rightTail, rfl⟩ := List.exists_cons_of_ne_nil rightNonempty
  exact S5_107.ListDerives.words <| by
    simpa [S5_107.listWordOfCons, Word.singleton, Word.append, Word.append_assoc,
      List.append_assoc] using derivesClosedInteriorSwap (Word.singleton endpoint)
        (S5_107.listWordOfCons leftHead leftTail) (S5_107.listWordOfCons rightHead rightTail)

theorem listInteriorCons (endpoint letter : Nat) (suffix : List Nat)
    {left right : List Nat}
    (derivation : ListDerives (endpoint :: left ++ endpoint :: suffix)
      (endpoint :: right ++ endpoint :: suffix)) :
    ListDerives (endpoint :: letter :: left ++ endpoint :: suffix)
      (endpoint :: letter :: right ++ endpoint :: suffix) := by
  have first := ((listDeleteMiddle endpoint [letter] left).symm).append suffix
  have second := derivation.prepend [endpoint, letter]
  have third := (listDeleteMiddle endpoint [letter] right).append suffix
  simp only [List.cons_append, List.nil_append, List.append_assoc]
    at first second third
  exact first.trans (second.trans third)

theorem listSwapFirstInterior (endpoint first second : Nat) (rest suffix : List Nat) :
    ListDerives (endpoint :: first :: second :: rest ++ endpoint :: suffix)
      (endpoint :: second :: first :: rest ++ endpoint :: suffix) := by
  have inserted := (listDeleteMiddle endpoint [first, second] rest).symm
  have swapped := (listInteriorSwap endpoint [first] [second] (by simp) (by simp)).append
    (rest ++ [endpoint])
  have deleted := listDeleteMiddle endpoint [second, first] rest
  have core : ListDerives (endpoint :: first :: second :: rest ++ [endpoint])
      (endpoint :: second :: first :: rest ++ [endpoint]) := by
    simpa [List.append_assoc] using inserted.trans (swapped.trans deleted)
  simpa [List.append_assoc] using core.append suffix

theorem listInteriorPermutation (endpoint : Nat) (suffix : List Nat)
    {left right : List Nat} (permutation : left.Perm right) :
    ListDerives (endpoint :: left ++ endpoint :: suffix)
      (endpoint :: right ++ endpoint :: suffix) := by
  induction permutation with
  | nil => exact S5_107.ListDerives.refl _
  | cons letter _ induction => exact listInteriorCons endpoint letter suffix induction
  | swap first second rest => exact listSwapFirstInterior endpoint second first rest suffix
  | trans _ _ first second => exact first.trans second

theorem splitFinal {letters : List Nat} (nonempty : letters ≠ []) :
    letters.dropLast ++ [S5_804.componentFinal letters] = letters := by
  cases letters with
  | nil => exact False.elim (nonempty rfl)
  | cons head tail =>
      have reconstruction := List.dropLast_concat_getLast (l := head :: tail) (by simp)
      rw [List.getLast_eq_getLastD] at reconstruction
      simpa only [S5_804.componentFinal, List.getLastD_cons] using reconstruction

/-- No interior order premise: the final variable and two-limited counts are
retained by actual derivations through the transported envelope calculus. -/
theorem existsFinalNormalizedEnvelope (stem : List Nat) (endpoint : Nat)
    (stemNonempty : stem ≠ [])
    (connected : ConnectedComponentSupportConnected (stem ++ [endpoint])) :
    ∃ interior, ListDerives (stem ++ [endpoint]) (endpoint :: interior ++ [endpoint]) ∧
      endpoint ∉ interior ∧ (∀ tested, interior.count tested ≤ 2) := by
  have reverseConnected := S5_804.connectedComponentSupportConnected_reverse connected
  have stemReverseNonempty : stem.reverse ≠ [] := by simpa using stemNonempty
  obtain ⟨next, rest, shape⟩ := List.exists_cons_of_ne_nil stemReverseNonempty
  have orderedConnected : ConnectedComponentSupportConnected (endpoint :: next :: rest) := by
    simpa [List.reverse_append, List.reverse_cons, shape] using reverseConnected
  obtain ⟨interior, derivation, absent, limited⟩ :=
    S3_16.Rank105.OrderedInterior.existsNormalizedEnvelope endpoint next rest orderedConnected
  have original : S3_16.Rank105.ListDerives (endpoint :: stem.reverse)
      (endpoint :: interior ++ [endpoint]) := by
    simpa only [shape] using derivation
  refine ⟨interior.reverse, ?_, ?_, ?_⟩
  · simpa [List.reverse_append, List.reverse_cons, List.append_assoc] using reverseListTransport original
  · simpa using absent
  · intro tested
    simpa using limited tested

theorem compareNormalizedEnvelopes (endpoint : Nat) (left right : List Nat)
    (leftAbsent : endpoint ∉ left) (rightAbsent : endpoint ∉ right)
    (leftLimited : ∀ tested, left.count tested ≤ 2)
    (rightLimited : ∀ tested, right.count tested ≤ 2)
    (counts : ∀ tested, min ((endpoint :: left ++ [endpoint]).count tested) 2 =
      min ((endpoint :: right ++ [endpoint]).count tested) 2) :
    ListDerives (endpoint :: left ++ [endpoint]) (endpoint :: right ++ [endpoint]) := by
  have innerCounts : ∀ tested, left.count tested = right.count tested := by
    intro tested
    by_cases equal : tested = endpoint
    · subst tested
      rw [List.count_eq_zero.mpr leftAbsent, List.count_eq_zero.mpr rightAbsent]
    · have outer := counts tested
      simpa [List.count_append, List.count_cons_of_ne (Ne.symm equal), equal,
        Nat.min_eq_left (leftLimited tested), Nat.min_eq_left (rightLimited tested)] using outer
  simpa [List.append_assoc] using listInteriorPermutation endpoint [] (List.perm_iff_count.mpr innerCounts)

theorem compareFinalStems (endpoint : Nat) (leftStem rightStem : List Nat)
    (leftConnected : ConnectedComponentSupportConnected (leftStem ++ [endpoint]))
    (rightConnected : ConnectedComponentSupportConnected (rightStem ++ [endpoint]))
    (counts : ∀ tested, min ((leftStem ++ [endpoint]).count tested) 2 =
      min ((rightStem ++ [endpoint]).count tested) 2) :
    ListDerives (leftStem ++ [endpoint]) (rightStem ++ [endpoint]) := by
  by_cases leftEmpty : leftStem = []
  · by_cases rightEmpty : rightStem = []
    · subst leftStem
      subst rightStem
      exact S5_107.ListDerives.refl _
    · obtain ⟨interior, derivation, absent, _⟩ :=
        existsFinalNormalizedEnvelope rightStem endpoint rightEmpty rightConnected
      have equal := (counts endpoint).trans (listDerives_cappedCounts derivation endpoint)
      simp [leftEmpty, List.count_append, List.count_eq_zero.mpr absent] at equal
  · by_cases rightEmpty : rightStem = []
    · obtain ⟨interior, derivation, absent, _⟩ :=
        existsFinalNormalizedEnvelope leftStem endpoint leftEmpty leftConnected
      have equal := (listDerives_cappedCounts derivation endpoint).symm.trans (counts endpoint)
      simp [rightEmpty, List.count_append, List.count_eq_zero.mpr absent] at equal
    · obtain ⟨left, leftDerivation, leftAbsent, leftLimited⟩ :=
        existsFinalNormalizedEnvelope leftStem endpoint leftEmpty leftConnected
      obtain ⟨right, rightDerivation, rightAbsent, rightLimited⟩ :=
        existsFinalNormalizedEnvelope rightStem endpoint rightEmpty rightConnected
      have normalizedCounts : ∀ tested, min ((endpoint :: left ++ [endpoint]).count tested) 2 =
          min ((endpoint :: right ++ [endpoint]).count tested) 2 := by
        intro tested
        exact (listDerives_cappedCounts leftDerivation tested).symm.trans
          ((counts tested).trans (listDerives_cappedCounts rightDerivation tested))
      exact leftDerivation.trans ((compareNormalizedEnvelopes endpoint left right
        leftAbsent rightAbsent leftLimited rightLimited normalizedCounts).trans rightDerivation.symm)

/-- Complete comparison of arbitrary connected components with equal cap-two
multiplicities and the same actual final letter. -/
theorem listDerivesConnectedFinal {left right : List Nat}
    (leftNonempty : left ≠ []) (rightNonempty : right ≠ [])
    (leftConnected : ConnectedComponentSupportConnected left)
    (rightConnected : ConnectedComponentSupportConnected right)
    (sameFinal : S5_804.componentFinal left = S5_804.componentFinal right)
    (counts : ∀ tested, min (left.count tested) 2 = min (right.count tested) 2) :
    ListDerives left right := by
  let endpoint := S5_804.componentFinal left
  have leftShape : left = left.dropLast ++ [endpoint] := (splitFinal leftNonempty).symm
  have rightShape : right = right.dropLast ++ [endpoint] := by
    change right = right.dropLast ++ [S5_804.componentFinal left]
    rw [sameFinal]
    exact (splitFinal rightNonempty).symm
  have joined := compareFinalStems endpoint left.dropLast right.dropLast
    (by simpa only [← leftShape] using leftConnected)
    (by simpa only [← rightShape] using rightConnected)
    (by intro tested; simpa only [← leftShape, ← rightShape] using counts tested)
  simpa only [← leftShape, ← rightShape] using joined

end SemigroupBasis.CoRoots.Order6Day7.Level2.Rank109.FinalEnvelope
