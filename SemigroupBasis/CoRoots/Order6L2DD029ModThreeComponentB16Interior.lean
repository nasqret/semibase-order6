import SemigroupBasis.CoRoots.Order6L2DD029ModThreeComponentB16Envelope
import SemigroupBasis.Examples.CommutativePositiveModThreeFour

/-!
# Mod-three interior normalization inside literal-B16 envelopes

This module lifts the two-law commutative positive-mod-three normalization
only after replacing each of its basis leaves by an explicit B16 derivation
inside a fixed envelope.  It therefore does not retarget a derivation between
bases.  The fixed endpoint is treated separately: three internal endpoint
copies are absorbed into the two displayed boundary copies.
-/

namespace SemigroupBasis.CoRoots.Order6L2DD029ModThreeComponentB16

open SemigroupBasis
open SemigroupBasis.Examples

private theorem derivesEnvelopeFourToOne
    (endpoint block : Word Nat) :
    Derives B16
      ((((((endpoint ++ block) ++ block) ++ block) ++ block) ++ endpoint))
      (((endpoint ++ block) ++ endpoint)) := by
  have expose :
      Derives B16
        ((((((endpoint ++ block) ++ block) ++ block) ++ block) ++ endpoint))
        ((((((block ++ block) ++ endpoint) ++ block) ++ block) ++ endpoint)) := by
    simpa [Word.append_assoc] using
      (derivesSquareInitialSwitch (block ++ block) endpoint).symm
  have collect :
      Derives B16
        ((((((block ++ block) ++ endpoint) ++ block) ++ block) ++ endpoint))
        ((((((block ++ block) ++ block) ++ endpoint) ++ block) ++ endpoint)) := by
    simpa [Word.append_assoc] using
      Derives.appendRight
        (derivesEndpointTransfer block (block ++ endpoint)).symm endpoint
  have contract :
      Derives B16
        ((((((block ++ block) ++ block) ++ endpoint) ++ block) ++ endpoint))
        (((endpoint ++ block) ++ endpoint)) := by
    simpa [Word.append_assoc] using
      derivesUnaryAnchorContraction block endpoint
  exact expose.trans (collect.trans contract)

private theorem derivesEnvelopeFourToOneWithTrailing
    (endpoint block trailing : Word Nat) :
    Derives B16
      (((((((endpoint ++ block) ++ block) ++ block) ++ block) ++ trailing) ++
        endpoint))
      ((((endpoint ++ block) ++ trailing) ++ endpoint)) := by
  have first :
      Derives B16
        (((((((endpoint ++ block) ++ block) ++ block) ++ block) ++ trailing) ++
          endpoint))
        (((((((endpoint ++ block) ++ endpoint) ++ block) ++ block) ++
          trailing) ++ block)) := by
    simpa [Word.append_assoc] using
      (derivesAttachmentXYYZX endpoint block
        ((block ++ block) ++ trailing)).symm
  have second :
      Derives B16
        (((((((endpoint ++ block) ++ endpoint) ++ block) ++ block) ++
          trailing) ++ block))
        (((((((endpoint ++ block) ++ trailing) ++ endpoint) ++ block) ++
          block) ++ block)) := by
    simpa [Word.append_assoc] using
      Derives.prepend endpoint <|
        derivesAnchoredSwap block
          ((endpoint ++ block) ++ block) trailing
  have third :
      Derives B16
        (((((((endpoint ++ block) ++ trailing) ++ endpoint) ++ block) ++
          block) ++ block))
        (((((((endpoint ++ endpoint) ++ trailing) ++ endpoint) ++ endpoint) ++
          block) ++ endpoint)) := by
    simpa [Word.append_assoc] using
      Derives.prepend endpoint <|
        derivesThreeLetterAnchorRepair trailing endpoint block
  have fourth :
      Derives B16
        (((((((endpoint ++ endpoint) ++ trailing) ++ endpoint) ++ endpoint) ++
          block) ++ endpoint))
        (((((((endpoint ++ endpoint) ++ endpoint) ++ endpoint) ++ block) ++
          trailing) ++ endpoint)) := by
    simpa [Word.append_assoc] using
      Derives.prepend endpoint <|
        derivesAnchoredSwap endpoint trailing
          ((endpoint ++ endpoint) ++ block)
  have fifth :
      Derives B16
        (((((((endpoint ++ endpoint) ++ endpoint) ++ endpoint) ++ block) ++
          trailing) ++ endpoint))
        ((((endpoint ++ block) ++ trailing) ++ endpoint)) := by
    simpa [Word.append_assoc] using
      (derivesUnaryAnchorExpansion endpoint (block ++ trailing)).symm
  exact first.trans <| second.trans <| third.trans <| fourth.trans fifth

/-- Contract four copies of one interior block to one while retaining the
rest of a closed envelope.  Every step is a literal B16 substitution. -/
theorem listDerivesEnvelopeBlockFourToOne
    (endpoint block : Word Nat) (trailing : List Nat) :
    B16ListDerives
      (endpoint.toList ++ block.toList ++ block.toList ++ block.toList ++
        block.toList ++ trailing ++ endpoint.toList)
      (endpoint.toList ++ block.toList ++ trailing ++ endpoint.toList) := by
  cases trailing with
  | nil =>
      simpa [Word.toList_append, List.append_assoc] using
        B16ListDerives.ofWord
          (derivesEnvelopeFourToOne endpoint block)
  | cons trailingHead trailingTail =>
      let trailingWord :=
        S5_107.listWordOfCons trailingHead trailingTail
      simpa [trailingWord, S5_107.listWordOfCons, Word.toList,
        Word.toList_append, List.append_assoc] using
          B16ListDerives.ofWord
            (derivesEnvelopeFourToOneWithTrailing
              endpoint block trailingWord)

private theorem bind_append (u v : Word Nat) (sigma : Nat → Word Nat) :
    (u ++ v).bind sigma = u.bind sigma ++ v.bind sigma := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem bind_bind (word : Word Nat)
    (tau sigma : Nat → Word Nat) :
    (word.bind tau).bind sigma =
      word.bind (fun x => (tau x).bind sigma) := by
  apply Word.toList_injective
  simp [Word.toList_bind, List.flatMap_assoc]

private theorem bind_singleton (word : Word Nat) :
    word.bind Word.singleton = word := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private def wordOfCons (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

/-- Add three copies of a nonempty block at an arbitrary interior position. -/
theorem listDerivesEnvelopeInteriorPowerContext
    (endpoint : Nat) (before after suffix : List Nat)
    (block : Word Nat) :
    B16ListDerives
      (modThreeEnvelopeRender endpoint
        (before ++ block.toList ++ after) suffix)
      (modThreeEnvelopeRender endpoint
        (before ++ block.toList ++ block.toList ++ block.toList ++
          block.toList ++ after) suffix) := by
  have moveToFrontPermutation :
      (before ++ block.toList ++ after).Perm
        (block.toList ++ before ++ after) := by
    rw [List.perm_iff_count]
    intro tested
    simp only [List.count_append]
    omega
  have moveToFront :=
    listDerivesEnvelopeInteriorPermutation
      endpoint suffix moveToFrontPermutation
  have expandFront :
      B16ListDerives
        (modThreeEnvelopeRender endpoint
          (block.toList ++ before ++ after) suffix)
        (modThreeEnvelopeRender endpoint
          (block.toList ++ block.toList ++ block.toList ++ block.toList ++
            before ++ after) suffix) := by
    simpa [modThreeEnvelopeRender, S5_441.parityEnvelopeRender,
      Word.toList_singleton, List.append_assoc] using
        B16ListDerives.append
          (B16ListDerives.symm <|
            listDerivesEnvelopeBlockFourToOne
              (Word.singleton endpoint) block (before ++ after))
          suffix
  have moveBackPermutation :
      (block.toList ++ block.toList ++ block.toList ++ block.toList ++
          before ++ after).Perm
        (before ++ block.toList ++ block.toList ++ block.toList ++
          block.toList ++ after) := by
    rw [List.perm_iff_count]
    intro tested
    simp only [List.count_append]
    omega
  have moveBack :=
    listDerivesEnvelopeInteriorPermutation
      endpoint suffix moveBackPermutation
  exact B16ListDerives.trans moveToFront <|
    B16ListDerives.trans expandFront moveBack

/-- Swap adjacent nonempty blocks at an arbitrary interior position. -/
theorem listDerivesEnvelopeInteriorSwapContext
    (endpoint : Nat) (before after suffix : List Nat)
    (left right : Word Nat) :
    B16ListDerives
      (modThreeEnvelopeRender endpoint
        (before ++ left.toList ++ right.toList ++ after) suffix)
      (modThreeEnvelopeRender endpoint
        (before ++ right.toList ++ left.toList ++ after) suffix) := by
  have permutation :
      (before ++ left.toList ++ right.toList ++ after).Perm
        (before ++ right.toList ++ left.toList ++ after) := by
    rw [List.perm_iff_count]
    intro tested
    simp only [List.count_append]
    omega
  exact
    listDerivesEnvelopeInteriorPermutation
      endpoint suffix permutation

/-- Explicitly lift the commutative positive-mod-three proof system inside a
fixed B16 envelope.  Its two basis leaves are replaced by the preceding
literal B16 power and swap macros. -/
theorem liftInteriorModThree
    {u v : Word Nat}
    (derivation : Derives commutativePositiveModThreeBasis u v)
    (endpoint : Nat) (before after suffix : List Nat)
    (sigma : Nat → Word Nat) :
    B16ListDerives
      (modThreeEnvelopeRender endpoint
        (before ++ (u.bind sigma).toList ++ after) suffix)
      (modThreeEnvelopeRender endpoint
        (before ++ (v.bind sigma).toList ++ after) suffix) := by
  induction derivation generalizing before after sigma with
  | fromBasis member =>
      simp only [commutativePositiveModThreeBasis, List.mem_cons,
        List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · simpa [positiveModThreePowerLaw, positiveModThreeX,
          positiveModThreeXXXX, Word.bind, Word.append,
          Word.singleton, modThreeEnvelopeRender,
          List.append_assoc] using
          listDerivesEnvelopeInteriorPowerContext
            endpoint before after suffix (sigma 0)
      · simpa [positiveModThreeCommutativityLaw,
          positiveModThreeXY, positiveModThreeYX,
          Word.bind, Word.append, Word.singleton,
          modThreeEnvelopeRender, List.append_assoc] using
          listDerivesEnvelopeInteriorSwapContext
            endpoint before after suffix (sigma 0) (sigma 1)
  | refl =>
      exact B16ListDerives.refl _
  | symm _ induction =>
      exact B16ListDerives.symm
        (induction before after sigma)
  | trans _ _ inductionFirst inductionSecond =>
      exact B16ListDerives.trans
        (inductionFirst before after sigma)
        (inductionSecond before after sigma)
  | prepend preWord _ induction =>
      simpa [bind_append, Word.toList_append,
        List.append_assoc] using
        induction
          (before ++ (preWord.bind sigma).toList) after sigma
  | appendRight _ postWord induction =>
      simpa [bind_append, Word.toList_append,
        List.append_assoc] using
        induction before
          ((postWord.bind sigma).toList ++ after) sigma
  | subst _ tau induction =>
      simpa [bind_bind] using
        induction before after (fun x => (tau x).bind sigma)

/-- Normalize every positive interior multiplicity to one, two, or three
copies according to its positive residue modulo three. -/
theorem listDerivesEnvelopePositiveModThreeReduce
    (endpoint : Nat) (interior suffix : List Nat) :
    B16ListDerives
      (modThreeEnvelopeRender endpoint interior suffix)
      (modThreeEnvelopeRender endpoint
        (positiveModThreeReduce interior) suffix) := by
  cases interior with
  | nil =>
      exact B16ListDerives.refl _
  | cons head tail =>
      have normalized :=
        positiveModThreeDerivesNormal (wordOfCons head tail)
      change
        match positiveModThreeReduce (head :: tail) with
        | [] => False
        | nextHead :: nextTail =>
            Derives commutativePositiveModThreeBasis
              (wordOfCons head tail)
              (Word.mk nextHead nextTail)
        at normalized
      cases reduced : positiveModThreeReduce (head :: tail) with
      | nil =>
          have present :
              head ∈ positiveModThreeReduce (head :: tail) :=
            (mem_positiveModThreeReduce_iff
              head (head :: tail)).mpr (by simp)
          exact False.elim (by simpa [reduced] using present)
      | cons nextHead nextTail =>
          rw [reduced] at normalized
          have lifted :=
            liftInteriorModThree normalized endpoint
              [] [] suffix Word.singleton
          rw [bind_singleton, bind_singleton] at lifted
          simpa [wordOfCons, Word.toList, reduced] using lifted

/-- The reduced interior has at most two internal endpoint copies and at
most three copies of every other supported letter. -/
structure ModThreeEnvelopeInteriorReduced
    (endpoint : Nat) (interior : List Nat) : Prop where
  endpoint_count_le_two : interior.count endpoint ≤ 2
  other_count_le_three :
    ∀ letter, letter ≠ endpoint → interior.count letter ≤ 3

/-- Delete three internal endpoint copies after positive-mod-three
normalization.  The two displayed boundary copies retain endpoint support. -/
def fixedEndpointModThreeReduce
    (endpoint : Nat) (interior : List Nat) : List Nat :=
  if (positiveModThreeReduce interior).count endpoint = 3 then
    (((positiveModThreeReduce interior).erase endpoint).erase endpoint).erase
      endpoint
  else
    positiveModThreeReduce interior

private theorem three_endpoint_copies_perm
    (endpoint : Nat) (letters : List Nat)
    (countEq : letters.count endpoint = 3) :
    letters.Perm
      (endpoint :: endpoint :: endpoint ::
        (((letters.erase endpoint).erase endpoint).erase endpoint)) := by
  have firstPresent : endpoint ∈ letters :=
    List.count_pos_iff.mp (by omega)
  have first := List.perm_cons_erase firstPresent
  have countAfterFirst :
      (letters.erase endpoint).count endpoint = 2 := by
    rw [List.count_erase_self, countEq]
  have secondPresent : endpoint ∈ letters.erase endpoint :=
    List.count_pos_iff.mp (by omega)
  have second := List.perm_cons_erase secondPresent
  have countAfterSecond :
      ((letters.erase endpoint).erase endpoint).count endpoint = 1 := by
    rw [List.count_erase_self, countAfterFirst]
  have thirdPresent :
      endpoint ∈ (letters.erase endpoint).erase endpoint :=
    List.count_pos_iff.mp (by omega)
  exact first.trans <|
    List.Perm.cons endpoint <|
      second.trans <|
        List.Perm.cons endpoint <| by
          simpa using List.perm_cons_erase thirdPresent

theorem fixedEndpointModThreeReduce_count_endpoint
    (endpoint : Nat) (interior : List Nat) :
    (fixedEndpointModThreeReduce endpoint interior).count endpoint =
      interior.count endpoint % 3 := by
  have countLe :=
    positiveModThreeReduce_count_le_three endpoint interior
  have residue :=
    positiveModThreeReduce_count_mod_three endpoint interior
  by_cases countEq :
      (positiveModThreeReduce interior).count endpoint = 3
  · rw [fixedEndpointModThreeReduce, if_pos countEq,
      List.count_erase_self, List.count_erase_self,
      List.count_erase_self, countEq]
    omega
  · rw [fixedEndpointModThreeReduce, if_neg countEq]
    omega

theorem fixedEndpointModThreeReduce_count_of_ne
    (endpoint tested : Nat) (interior : List Nat)
    (different : tested ≠ endpoint) :
    (fixedEndpointModThreeReduce endpoint interior).count tested =
      (positiveModThreeReduce interior).count tested := by
  by_cases countEq :
      (positiveModThreeReduce interior).count endpoint = 3
  · simp [fixedEndpointModThreeReduce, countEq,
      List.count_erase_of_ne different]
  · simp [fixedEndpointModThreeReduce, countEq]

theorem fixedEndpointModThreeReduce_reduced
    (endpoint : Nat) (interior : List Nat) :
    ModThreeEnvelopeInteriorReduced endpoint
      (fixedEndpointModThreeReduce endpoint interior) := by
  refine
    { endpoint_count_le_two := ?_
      other_count_le_three := ?_ }
  · rw [fixedEndpointModThreeReduce_count_endpoint]
    have bound : interior.count endpoint % 3 < 3 :=
      Nat.mod_lt (interior.count endpoint) (by decide : (0 : Nat) < 3)
    omega
  · intro tested different
    rw [fixedEndpointModThreeReduce_count_of_ne
      endpoint tested interior different]
    exact positiveModThreeReduce_count_le_three tested interior

theorem fixedEndpointModThreeReduce_perm
    {endpoint : Nat} {left right : List Nat}
    (supportEq :
      ∀ tested, tested ≠ endpoint →
        (tested ∈ left ↔ tested ∈ right))
    (modThreeEq :
      ∀ tested,
        left.count tested % 3 = right.count tested % 3) :
    (fixedEndpointModThreeReduce endpoint left).Perm
      (fixedEndpointModThreeReduce endpoint right) := by
  rw [List.perm_iff_count]
  intro tested
  by_cases same : tested = endpoint
  · subst tested
    calc
      (fixedEndpointModThreeReduce endpoint left).count endpoint =
          left.count endpoint % 3 :=
        fixedEndpointModThreeReduce_count_endpoint endpoint left
      _ = right.count endpoint % 3 := modThreeEq endpoint
      _ =
          (fixedEndpointModThreeReduce endpoint right).count endpoint :=
        Eq.symm <|
          fixedEndpointModThreeReduce_count_endpoint endpoint right
  · rw [fixedEndpointModThreeReduce_count_of_ne
        endpoint tested left same,
      fixedEndpointModThreeReduce_count_of_ne
        endpoint tested right same]
    have leftLe :=
      positiveModThreeReduce_count_le_three tested left
    have rightLe :=
      positiveModThreeReduce_count_le_three tested right
    have reducedSupport :
        tested ∈ positiveModThreeReduce left ↔
          tested ∈ positiveModThreeReduce right := by
      rw [mem_positiveModThreeReduce_iff,
        mem_positiveModThreeReduce_iff]
      exact supportEq tested same
    have reducedModThree :
        (positiveModThreeReduce left).count tested % 3 =
          (positiveModThreeReduce right).count tested % 3 := by
      rw [positiveModThreeReduce_count_mod_three,
        positiveModThreeReduce_count_mod_three]
      exact modThreeEq tested
    by_cases present : tested ∈ positiveModThreeReduce left
    · have leftPos := List.count_pos_iff.mpr present
      have rightPos :=
        List.count_pos_iff.mpr (reducedSupport.mp present)
      omega
    · have leftZero := List.count_eq_zero.mpr present
      have rightZero :=
        List.count_eq_zero.mpr <| by
          intro rightPresent
          exact present (reducedSupport.mpr rightPresent)
      omega

private theorem listDerivesEnvelopeRemoveEndpointTriple
    (endpoint : Nat) (middle suffix : List Nat) :
    B16ListDerives
      (modThreeEnvelopeRender endpoint
        ([endpoint, endpoint, endpoint] ++ middle) suffix)
      (modThreeEnvelopeRender endpoint middle suffix) := by
  cases middle with
  | nil =>
      simpa [modThreeEnvelopeRender, S5_441.parityEnvelopeRender,
        Word.toList_append, Word.toList_singleton,
        List.append_assoc] using
        B16ListDerives.append
          (B16ListDerives.symm <|
            B16ListDerives.ofWord <|
              derivesPowerExpansion (Word.singleton endpoint))
          suffix
  | cons middleHead middleTail =>
      let middleWord :=
        S5_107.listWordOfCons middleHead middleTail
      simpa [modThreeEnvelopeRender, S5_441.parityEnvelopeRender,
        middleWord, S5_107.listWordOfCons, Word.toList,
        Word.toList_append, Word.toList_singleton,
        List.append_assoc] using
        B16ListDerives.append
          (B16ListDerives.symm <|
            B16ListDerives.ofWord <|
              derivesUnaryAnchorExpansion
                (Word.singleton endpoint) middleWord)
          suffix

/-- Derive the fixed-endpoint positive-mod-three normal form. -/
theorem listDerivesEnvelopeFixedEndpointReduce
    (endpoint : Nat) (interior suffix : List Nat) :
    B16ListDerives
      (modThreeEnvelopeRender endpoint interior suffix)
      (modThreeEnvelopeRender endpoint
        (fixedEndpointModThreeReduce endpoint interior) suffix) := by
  have positiveReduction :=
    listDerivesEnvelopePositiveModThreeReduce
      endpoint interior suffix
  by_cases countEq :
      (positiveModThreeReduce interior).count endpoint = 3
  · let remainder :=
      (((positiveModThreeReduce interior).erase endpoint).erase
        endpoint).erase endpoint
    have arrangePermutation :
        (positiveModThreeReduce interior).Perm
          ([endpoint, endpoint, endpoint] ++ remainder) := by
      simpa [remainder] using
        three_endpoint_copies_perm endpoint
          (positiveModThreeReduce interior) countEq
    have arrange :=
      listDerivesEnvelopeInteriorPermutation
        endpoint suffix arrangePermutation
    have removeTriple :=
      listDerivesEnvelopeRemoveEndpointTriple
        endpoint remainder suffix
    exact B16ListDerives.trans positiveReduction <| by
      simpa [fixedEndpointModThreeReduce, countEq, remainder] using
        B16ListDerives.trans arrange removeTriple
  · simpa [fixedEndpointModThreeReduce, countEq] using
      positiveReduction

/-- Same fixed endpoint, support away from it, and coordinatewise residues
determine a literal-B16 derivation. -/
theorem listDerivesEnvelopeInteriorNormalizeFixedEndpoint
    (endpoint : Nat) (suffix : List Nat)
    {left right : List Nat}
    (supportEq :
      ∀ tested, tested ≠ endpoint →
        (tested ∈ left ↔ tested ∈ right))
    (modThreeEq :
      ∀ tested,
        left.count tested % 3 = right.count tested % 3) :
    B16ListDerives
      (modThreeEnvelopeRender endpoint left suffix)
      (modThreeEnvelopeRender endpoint right suffix) := by
  have reducedPermutation :=
    fixedEndpointModThreeReduce_perm supportEq modThreeEq
  have leftNormal :=
    listDerivesEnvelopeFixedEndpointReduce endpoint left suffix
  have rightNormal :=
    listDerivesEnvelopeFixedEndpointReduce endpoint right suffix
  have middle :=
    listDerivesEnvelopeInteriorPermutation
      endpoint suffix reducedPermutation
  exact B16ListDerives.trans leftNormal <|
    B16ListDerives.trans middle <|
      B16ListDerives.symm rightNormal

private theorem mem_closedEnvelope_iff_of_ne
    (endpoint tested : Nat) (interior : List Nat)
    (different : tested ≠ endpoint) :
    tested ∈ modThreeEnvelopeRender endpoint interior [] ↔
      tested ∈ interior := by
  simp [modThreeEnvelopeRender, S5_441.parityEnvelopeRender,
    different, Ne.symm different]

/-- Closed rendered support and coordinatewise residues determine a B16
derivation when both envelopes have the same endpoint. -/
theorem listDerivesEnvelopeInteriorNormalizeOfRenderedInvariants
    (endpoint : Nat) {left right : List Nat}
    (supportEq :
      ∀ tested,
        tested ∈ modThreeEnvelopeRender endpoint left [] ↔
          tested ∈ modThreeEnvelopeRender endpoint right [])
    (modThreeEq :
      ∀ tested,
        (modThreeEnvelopeRender endpoint left []).count tested % 3 =
          (modThreeEnvelopeRender endpoint right []).count tested % 3) :
    B16ListDerives
      (modThreeEnvelopeRender endpoint left [])
      (modThreeEnvelopeRender endpoint right []) := by
  have interiorSupport :
      ∀ tested, tested ≠ endpoint →
        (tested ∈ left ↔ tested ∈ right) := by
    intro tested different
    rw [← mem_closedEnvelope_iff_of_ne
        endpoint tested left different,
      ← mem_closedEnvelope_iff_of_ne
        endpoint tested right different]
    exact supportEq tested
  have interiorModThree :
      ∀ tested,
        left.count tested % 3 = right.count tested % 3 := by
    intro tested
    have rendered := modThreeEq tested
    by_cases same : tested = endpoint
    · subst tested
      simp only [modThreeEnvelopeRender,
        S5_441.parityEnvelopeRender, List.count_cons,
        List.count_append, List.count_nil]
        at rendered
      omega
    · simpa [modThreeEnvelopeRender,
        S5_441.parityEnvelopeRender, same, Ne.symm same] using rendered
  exact
    listDerivesEnvelopeInteriorNormalizeFixedEndpoint
      endpoint [] interiorSupport interiorModThree

end SemigroupBasis.CoRoots.Order6L2DD029ModThreeComponentB16
