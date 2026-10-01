import SemigroupBasis.CoRoots.Order6Day7.S2_2.SeedS5_804FrontNormalize
import SemigroupBasis.CoRoots.S5_804Completeness
import SemigroupBasis.CoRoots.S5_442Invariant

/-!
# Arbitrary connected components with parity and a fixed final letter

Reverse the proved first-letter envelope in the reversed eleven-law basis,
then compare fixed-endpoint interiors by support and coordinate parity.
The singleton case is kept separate using the genuine component signature.
There is no length bound, cancellation assumption or owner normalizer input.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank092.FinalComponents

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots

abbrev ListDerives : List Nat → List Nat → Prop := S5_107.ListDerives Rank092.basis
abbrev render := S5_441.parityEnvelopeRender

theorem leftTable_eq_cyclic : Rank092.leftTable = cyclicTwo := by
  unfold Rank092.leftTable Generated.Catalogue.S2_2.table cyclicTwo
  rw [FiniteTable.mk.injEq]
  refine ⟨rfl, heq_of_eq ?_⟩
  funext a b
  decide +revert

structure SameSignature (left right : Word Nat) : Prop where
  componentFinal : S5_804.SameConnectedCutSignature left right
  parity : ∀ tested, left.toList.count tested % 2 = right.toList.count tested % 2

theorem sameSignature_of_factorValid (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy Rank092.leftTable.semigroup)
    (rightValid : identity.SatisfiedBy Rank092.rightTable.semigroup) :
    SameSignature identity.lhs identity.rhs := by
  refine ⟨S5_804.valid_sameConnectedCutSignature identity rightValid, ?_⟩
  rw [leftTable_eq_cyclic] at leftValid
  exact S5_442Invariant.sameOccurrenceParity_of_cyclicTwo_equalEval
    identity.lhs identity.rhs leftValid

theorem reverseFrontDerivation {left right : Word Nat}
    (derivation : Derives Front.basis left right) :
    Derives Rank092.basis left.reverse right.reverse := by
  simpa only [Front.basis, reversedBasis_reversedBasis] using derivation.reverse

theorem reverseFrontListDerivation {left right : List Nat}
    (derivation : Front.ListDerives left right) :
    ListDerives left.reverse right.reverse := by
  cases derivation with
  | empty => exact S5_107.ListDerives.empty
  | @words leftHead rightHead leftTail rightTail proof =>
      have result := S5_107.ListDerives.ofWord (reverseFrontDerivation proof)
      change ListDerives (S5_107.listWordOfCons leftHead leftTail).reverse.toList
        (S5_107.listWordOfCons rightHead rightTail).reverse.toList at result
      rw [Word.toList_reverse, Word.toList_reverse] at result
      exact result

theorem splitFinal {letters : List Nat} (nonempty : letters ≠ []) :
    letters.dropLast ++ [S5_804.componentFinal letters] = letters := by
  cases letters with
  | nil => exact False.elim (nonempty rfl)
  | cons head tail =>
      have reconstruction := List.dropLast_concat_getLast (l := head :: tail) (by simp)
      rw [List.getLast_eq_getLastD] at reconstruction
      simpa only [S5_804.componentFinal, List.getLastD_cons] using reconstruction

/-- Every nontrivial connected component derives to an envelope at its
ACTUAL final variable. The scanner preserves the full multiset. -/
theorem existsFinalEnvelope (letters : List Nat) (nonempty : letters ≠ [])
    (connected : ConnectedComponentSupportConnected letters)
    (lengthAtLeastTwo : 2 ≤ letters.length) :
    ∃ interior,
      ListDerives letters (render (S5_804.componentFinal letters) interior []) ∧
      letters.Perm (render (S5_804.componentFinal letters) interior []) := by
  have shape : letters = letters.dropLast ++ [S5_804.componentFinal letters] :=
    (splitFinal nonempty).symm
  have reverseShape : letters.reverse =
      S5_804.componentFinal letters :: letters.dropLast.reverse := by
    simpa [List.reverse_append] using congrArg List.reverse shape
  have frontConnected : ConnectedComponentSupportConnected
      (S5_804.componentFinal letters :: letters.dropLast.reverse) := by
    rw [← reverseShape]
    exact S5_804.connectedComponentSupportConnected_reverse connected
  have frontLength : 2 ≤ (S5_804.componentFinal letters :: letters.dropLast.reverse).length := by
    rw [← reverseShape]
    simpa using lengthAtLeastTwo
  obtain ⟨interior, frontDerivation, frontPermutation⟩ :=
    Front.exists_parityEnvelopeDerivation_of_connected frontConnected frontLength
  have finalDerivation : ListDerives
      (letters.dropLast ++ [S5_804.componentFinal letters])
      (render (S5_804.componentFinal letters) interior.reverse []) := by
    simpa [render, Front.parityEnvelopeRender, S5_441.parityEnvelopeRender,
      List.reverse_append, List.reverse_cons, List.append_assoc] using
      reverseFrontListDerivation frontDerivation
  have finalPermutation :
      (letters.dropLast ++ [S5_804.componentFinal letters]).Perm
      (render (S5_804.componentFinal letters) interior.reverse []) := by
    have reversedPermutation :
        (S5_804.componentFinal letters :: letters.dropLast.reverse).reverse.Perm
        (S5_441.parityEnvelopeRender (S5_804.componentFinal letters) interior []).reverse := by
      apply List.perm_iff_count.mpr
      intro tested
      simpa only [List.count_reverse] using List.perm_iff_count.mp frontPermutation tested
    simpa [render, Front.parityEnvelopeRender, S5_441.parityEnvelopeRender,
      List.reverse_append, List.reverse_cons, List.append_assoc] using reversedPermutation
  refine ⟨interior.reverse, ?_, ?_⟩
  · simpa only [← shape] using finalDerivation
  · simpa only [← shape] using finalPermutation

private theorem reversedInteriorPermutation (endpoint : Nat) (interior : List Nat) :
    (render endpoint interior.reverse []).Perm (render endpoint interior []) := by
  apply List.perm_iff_count.mpr
  intro tested
  change (endpoint :: interior.reverse ++ [endpoint]).count tested =
    (endpoint :: interior ++ [endpoint]).count tested
  by_cases equal : endpoint = tested
  · subst tested
    simp only [List.count_cons_self, List.count_append, List.count_reverse]
  · simp only [List.count_cons_of_ne equal, List.count_append, List.count_reverse]

/-- Fixed-final envelope equality follows from the actual support and parity
invariants; all rewriting is in the original eleven-law basis. -/
theorem compareFinalEnvelopes (endpoint : Nat) {left right : List Nat}
    (support : ∀ tested, tested ∈ render endpoint left [] ↔ tested ∈ render endpoint right [])
    (parity : ∀ tested,
      (render endpoint left []).count tested % 2 = (render endpoint right []).count tested % 2) :
    ListDerives (render endpoint left []) (render endpoint right []) := by
  have leftPermutation := reversedInteriorPermutation endpoint left
  have rightPermutation := reversedInteriorPermutation endpoint right
  have frontSupport : ∀ tested,
      tested ∈ render endpoint left.reverse [] ↔ tested ∈ render endpoint right.reverse [] := by
    intro tested
    exact leftPermutation.mem_iff.trans ((support tested).trans rightPermutation.mem_iff.symm)
  have frontParity : ∀ tested,
      (render endpoint left.reverse []).count tested % 2 =
      (render endpoint right.reverse []).count tested % 2 := by
    intro tested
    exact (congrArg (fun n => n % 2) (List.perm_iff_count.mp leftPermutation tested)).trans
      ((parity tested).trans
        (congrArg (fun n => n % 2) (List.perm_iff_count.mp rightPermutation tested)).symm)
  have front := Front.listDerivesParityEnvelopeInteriorNormalizeOfRenderedInvariants
    endpoint frontSupport frontParity
  simpa [render, Front.parityEnvelopeRender, S5_441.parityEnvelopeRender,
    List.reverse_append, List.reverse_cons, List.append_assoc] using reverseFrontListDerivation front

theorem supportIffOfSignature {left right : List Nat}
    (same : connectedComponentSignatureOfList left = connectedComponentSignatureOfList right)
    (tested : Nat) : tested ∈ left ↔ tested ∈ right := by
  have supports := congrArg (fun signature => tested ∈ signature.support) same
  have membership : (tested ∈ left) = (tested ∈ right) := by
    simpa only [connectedComponentSignatureOfList_support,
      connectedComponentSortedSupport_mem_iff] using supports
  exact Iff.of_eq membership

private theorem length_eq_one_of_componentSignature_eq {left right : List Nat}
    (same : connectedComponentSignatureOfList left = connectedComponentSignatureOfList right)
    (leftLength : left.length = 1) : right.length = 1 := by
  obtain ⟨letter, rfl⟩ := List.length_eq_one_iff.mp leftLength
  have leftSignature : connectedComponentSignatureOfList [letter] = ⟨[letter], false⟩ := by
    simp [connectedComponentSignatureOfList,
      connectedComponentSortedSupport, connectedComponentDistinctSupport]
  have rightSignature : connectedComponentSignatureOfList right = ⟨[letter], false⟩ := by
    rw [← same, leftSignature]
  have rightSupport : connectedComponentSortedSupport right = [letter] := by
    rw [← connectedComponentSignatureOfList_support]
    exact congrArg connectedComponentSignature.support rightSignature
  have repeatedFalse : decide (right.length ≠ 1) = false := by
    simpa [connectedComponentSignatureOfList, rightSupport] using
      congrArg connectedComponentSignature.repeatedUnary rightSignature
  by_cases lengthOne : right.length = 1
  · exact lengthOne
  · exact False.elim ((of_decide_eq_false repeatedFalse) lengthOne)

/-- Unrestricted connected-component comparison with every required
coordinate retained, including the actual final variable. -/
theorem listDerivesConnectedFinal {left right : List Nat}
    (leftNonempty : left ≠ []) (rightNonempty : right ≠ [])
    (leftConnected : ConnectedComponentSupportConnected left)
    (rightConnected : ConnectedComponentSupportConnected right)
    (sameBase : connectedComponentSignatureOfList left = connectedComponentSignatureOfList right)
    (sameFinal : S5_804.componentFinal left = S5_804.componentFinal right)
    (sameParity : ∀ tested, left.count tested % 2 = right.count tested % 2) :
    ListDerives left right := by
  by_cases leftLengthOne : left.length = 1
  · have rightLengthOne := length_eq_one_of_componentSignature_eq sameBase leftLengthOne
    obtain ⟨leftLetter, rfl⟩ := List.length_eq_one_iff.mp leftLengthOne
    obtain ⟨rightLetter, rfl⟩ := List.length_eq_one_iff.mp rightLengthOne
    have lettersEqual : leftLetter = rightLetter := by
      have support := supportIffOfSignature sameBase leftLetter
      simpa using support.mp (by simp)
    subst rightLetter
    exact S5_107.ListDerives.refl _
  · have rightLengthNotOne : right.length ≠ 1 := by
      intro rightLengthOne
      exact leftLengthOne (length_eq_one_of_componentSignature_eq sameBase.symm rightLengthOne)
    have leftLengthAtLeastTwo : 2 ≤ left.length := by
      have positive : 0 < left.length := by
        cases left with
        | nil => contradiction
        | cons _ _ => simp
      omega
    have rightLengthAtLeastTwo : 2 ≤ right.length := by
      have positive : 0 < right.length := by
        cases right with
        | nil => contradiction
        | cons _ _ => simp
      omega
    obtain ⟨leftInterior, leftDerivation, leftPermutation⟩ :=
      existsFinalEnvelope left leftNonempty leftConnected leftLengthAtLeastTwo
    obtain ⟨rightInterior, rightDerivation, rightPermutation⟩ :=
      existsFinalEnvelope right rightNonempty rightConnected rightLengthAtLeastTwo
    rw [← sameFinal] at rightDerivation rightPermutation
    have support : ∀ tested,
        tested ∈ render (S5_804.componentFinal left) leftInterior [] ↔
        tested ∈ render (S5_804.componentFinal left) rightInterior [] := by
      intro tested
      exact leftPermutation.mem_iff.symm.trans
        ((supportIffOfSignature sameBase tested).trans rightPermutation.mem_iff)
    have parity : ∀ tested,
        (render (S5_804.componentFinal left) leftInterior []).count tested % 2 =
        (render (S5_804.componentFinal left) rightInterior []).count tested % 2 := by
      intro tested
      exact (congrArg (fun n => n % 2) (List.perm_iff_count.mp leftPermutation tested)).symm.trans
        ((sameParity tested).trans
          (congrArg (fun n => n % 2) (List.perm_iff_count.mp rightPermutation tested)))
    exact leftDerivation.trans
      ((compareFinalEnvelopes (S5_804.componentFinal left) support parity).trans rightDerivation.symm)

end SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank092.FinalComponents
