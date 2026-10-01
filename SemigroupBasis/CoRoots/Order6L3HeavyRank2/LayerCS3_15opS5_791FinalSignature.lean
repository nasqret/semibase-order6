import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCS3_15opProfile
import SemigroupBasis.CoRoots.S5_791Invariant

/-!
# Final-coordinate consequence of the `S5_791` component signature

A final variable occurs exactly once precisely when the last deterministic
support component is the simple unary component.  Therefore equality of the
ordered component signatures, together with equality of finals, preserves
this property.  This is the structural bridge needed by the unrestricted
`S3_15^op x S5_791` transfer.
-/

namespace SemigroupBasis.CoRoots.Order6L3HeavyRank2.S3_15opS5_791

open SemigroupBasis
open SemigroupBasis.Examples

private theorem final_wordOfPrefixFinal
    (stem : List Nat) (final : Nat) :
    (wordOfPrefixFinal stem final).final = final := by
  induction stem with
  | nil => rfl
  | cons letter rest induction =>
      rw [wordOfPrefixFinal_cons, Word.final_append]
      exact induction

theorem splitFinal_eq (word : Word Nat) :
    (splitPrefixFinal word).2 = word.final := by
  have reconstructed :=
    congrArg Word.final (wordOfPrefixFinal_split word)
  rw [final_wordOfPrefixFinal] at reconstructed
  exact reconstructed

theorem toList_eq_splitPrefixFinal (word : Word Nat) :
    word.toList =
      (splitPrefixFinal word).1 ++ [(splitPrefixFinal word).2] := by
  have reconstructed :=
    congrArg Word.toList (wordOfPrefixFinal_split word)
  rw [toList_wordOfPrefixFinal] at reconstructed
  exact reconstructed.symm

theorem splitFinal_not_mem_prefix_of_count_one
    (word : Word Nat)
    (countOne : word.toList.count word.final = 1) :
    (splitPrefixFinal word).2 ∉ (splitPrefixFinal word).1 := by
  have finalEq := splitFinal_eq word
  have countOne' :
      word.toList.count (splitPrefixFinal word).2 = 1 := by
    simpa [finalEq] using countOne
  rw [toList_eq_splitPrefixFinal, List.count_append] at countOne'
  simp only [List.count_singleton_self] at countOne'
  have prefixCount :
      (splitPrefixFinal word).1.count
        (splitPrefixFinal word).2 = 0 := by
    omega
  exact List.count_eq_zero.mp prefixCount

theorem splitFinal_mem_prefix_of_count_ne_one
    (word : Word Nat)
    (countNotOne : word.toList.count word.final ≠ 1) :
    (splitPrefixFinal word).2 ∈ (splitPrefixFinal word).1 := by
  have finalEq := splitFinal_eq word
  have countNotOne' :
      word.toList.count (splitPrefixFinal word).2 ≠ 1 := by
    simpa [finalEq] using countNotOne
  have countShape :
      word.toList.count (splitPrefixFinal word).2 =
        (splitPrefixFinal word).1.count
          (splitPrefixFinal word).2 + 1 := by
    rw [toList_eq_splitPrefixFinal, List.count_append]
    simp
  have positive :
      0 < (splitPrefixFinal word).1.count
        (splitPrefixFinal word).2 := by
    omega
  exact List.count_pos_iff.mp positive

private theorem decompositionLast
    (word : Word Nat) :
    ∃ before last,
      connectedComponentDecomposeList word.toList =
        before ++ [last] ∧
      last ≠ [] ∧
      last.getLast? = some word.final := by
  let components := connectedComponentDecomposeList word.toList
  have componentsNonempty : components ≠ [] :=
    connectedComponentDecomposeList_nonempty (by
      simp [Word.toList])
  let last := components.getLast componentsNonempty
  have lastOption : components.getLast? = some last :=
    List.getLast?_eq_some_getLast componentsNonempty
  obtain ⟨before, shape⟩ :=
    List.getLast?_eq_some_iff.mp lastOption
  have lastMember : last ∈ components :=
    List.getLast_mem componentsNonempty
  have lastNonempty : last ≠ [] :=
    connectedComponentDecomposeList_nonempty_components
      word.toList last lastMember
  have flattened :=
    connectedComponentDecomposeList_flatten word.toList
  change components.flatten = word.toList at flattened
  rw [shape, List.flatten_append] at flattened
  simp only [List.flatten_singleton] at flattened
  have lastEnd : last.getLast? = some word.final := by
    calc
      last.getLast? = (before.flatten ++ last).getLast? := by
        rw [List.getLast?_append,
          List.getLast?_eq_some_getLast lastNonempty]
        rfl
      _ = word.toList.getLast? := congrArg List.getLast? flattened
      _ = some word.final := by
        rw [toList_eq_splitPrefixFinal]
        simp [splitFinal_eq]
  exact ⟨before, last, shape, lastNonempty, lastEnd⟩

private theorem lastComponentSingleton_of_finalCountOne
    (word : Word Nat)
    (countOne : word.toList.count word.final = 1) :
    ∃ before,
      connectedComponentDecomposeList word.toList =
        before ++ [[word.final]] := by
  obtain ⟨before, last, shape, _lastNonempty, lastEnd⟩ :=
    decompositionLast word
  obtain ⟨stem, lastShape⟩ :=
    List.getLast?_eq_some_iff.mp lastEnd
  have flattened :=
    connectedComponentDecomposeList_flatten word.toList
  rw [shape, List.flatten_append] at flattened
  simp only [List.flatten_singleton] at flattened
  rw [lastShape] at flattened
  have stemFinalAbsent : word.final ∉ stem := by
    have countShape :
        before.flatten.count word.final +
            stem.count word.final + 1 = 1 := by
      have counted :=
        congrArg (List.count word.final) flattened
      simpa [List.count_append, Nat.add_assoc] using
        counted.trans countOne
    have stemCount : stem.count word.final = 0 := by omega
    exact List.count_eq_zero.mp stemCount
  have lastMember : stem ++ [word.final] ∈
      connectedComponentDecomposeList word.toList := by
    rw [shape, lastShape]
    simp
  have lastConnected :=
    connectedComponentDecomposeList_supportConnected
      word.toList (stem ++ [word.final]) lastMember
  have stemEmpty : stem = [] := by
    cases stem with
    | nil => rfl
    | cons head tail =>
        have stemNonempty : head :: tail ≠ [] := by simp
        obtain ⟨letter, inStem, inFinal⟩ :=
          lastConnected (head :: tail) [word.final]
            rfl stemNonempty (by simp)
        have letterEq : letter = word.final := by simpa using inFinal
        exact False.elim <| stemFinalAbsent (letterEq ▸ inStem)
  refine ⟨before, ?_⟩
  rw [shape, lastShape, stemEmpty]
  rfl

private theorem unarySimpleSignature_forces_singleton
    {letters : List Nat} {final : Nat}
    (nonempty : letters ≠ [])
    (lastEnd : letters.getLast? = some final)
    (signature :
      connectedComponentSignatureOfList letters =
        connectedComponentSignatureOfList [final]) :
    letters = [final] := by
  have singletonSignature :
      connectedComponentSignatureOfList [final] =
        ⟨[final], false⟩ := by
    simp [connectedComponentSignatureOfList,
      connectedComponentSortedSupport,
      connectedComponentDistinctSupport]
  have signature' :
      connectedComponentSignatureOfList letters =
        ⟨[final], false⟩ := signature.trans singletonSignature
  have supportShape :
      connectedComponentSortedSupport letters = [final] := by
    simpa only [connectedComponentSignatureOfList_support] using
      congrArg connectedComponentSignature.support signature'
  have repeatedFalse :=
    congrArg connectedComponentSignature.repeatedUnary signature'
  have lengthOne : letters.length = 1 := by
    unfold connectedComponentSignatureOfList at repeatedFalse
    rw [supportShape] at repeatedFalse
    simp at repeatedFalse
    omega
  obtain ⟨letter, lettersShape⟩ :=
    List.length_eq_one_iff.mp lengthOne
  subst letters
  simp at lastEnd
  subst letter
  rfl

private theorem finalCountOne_of_lastComponentSingleton
    (word : Word Nat) (before : List (List Nat))
    (shape :
      connectedComponentDecomposeList word.toList =
        before ++ [[word.final]]) :
    word.toList.count word.final = 1 := by
  have pairwise :=
    connectedComponentDecomposeList_pairwiseDisjoint word.toList
  rw [shape] at pairwise
  have cross := (List.pairwise_append.mp pairwise).2.2
  have finalAbsent : word.final ∉ before.flatten := by
    intro member
    rw [List.mem_flatten] at member
    obtain ⟨component, componentMember, finalMember⟩ := member
    exact
      (cross component componentMember [word.final] (by simp)
        word.final finalMember (by simp))
  have flattened :=
    connectedComponentDecomposeList_flatten word.toList
  rw [shape] at flattened
  rw [← flattened]
  simp [List.count_append, List.count_eq_zero.mpr finalAbsent]

private theorem finalCountOne_of_sameComponents
    {left right : Word Nat}
    (sameComponents :
      connectedComponentSignaturesWord left =
        connectedComponentSignaturesWord right)
    (finalEq : left.final = right.final)
    (leftSimple : left.toList.count left.final = 1) :
    right.toList.count right.final = 1 := by
  obtain ⟨leftBefore, leftShape⟩ :=
    lastComponentSingleton_of_finalCountOne left leftSimple
  obtain ⟨rightBefore, rightLast, rightShape,
      rightLastNonempty, rightLastEnd⟩ := decompositionLast right
  have lastSignatures := congrArg List.getLast? sameComponents
  unfold connectedComponentSignaturesWord
    connectedComponentSignaturesList at lastSignatures
  rw [leftShape, rightShape] at lastSignatures
  simp only [List.map_append, List.map_singleton,
    List.getLast?_append, List.getLast?_singleton,
    Option.some_or] at lastSignatures
  have rightSignature :
      connectedComponentSignatureOfList rightLast =
        connectedComponentSignatureOfList [right.final] := by
    simpa only [Option.some.injEq, finalEq] using
      lastSignatures.symm
  have rightLastShape : rightLast = [right.final] :=
    unarySimpleSignature_forces_singleton
      rightLastNonempty rightLastEnd rightSignature
  apply finalCountOne_of_lastComponentSingleton right rightBefore
  simpa only [rightLastShape] using rightShape

theorem finalCountOneIff
    {left right : Word Nat}
    (same :
      SemigroupBasis.CoRoots.S5_791Invariant.SameComponentInitialSignature
        left right)
    (finalEq : left.final = right.final) :
    left.toList.count left.final = 1 ↔
      right.toList.count right.final = 1 := by
  constructor
  · exact finalCountOne_of_sameComponents
      same.components finalEq
  · exact finalCountOne_of_sameComponents
      same.symm.components finalEq.symm

end SemigroupBasis.CoRoots.Order6L3HeavyRank2.S3_15opS5_791
