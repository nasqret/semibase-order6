import SemigroupBasis.CoRoots.Order6LeeA2LatticeNodesH92

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6LeeA2LatticeNodesH92Chain

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.Order6LeeA2LatticeNodesNormal
open SemigroupBasis.CoRoots.Order6LeeA2LatticeNodesH92
open SemigroupBasis.CoRoots.Order6LeeA2LatticeNodesSingletonNormal
open SemigroupBasis.CoRoots.S5_868
  (maximalFactorWord maximalFactorWord_toList)
open SemigroupBasis.CoRoots.S5_804
  (ConnectedCutComponentSignature
    connectedCutComponentSignatureOfList
    componentFinal componentFinal_mem)

/-!
# Explicit local chain moves for H92

This module discharges the three local obligations isolated in
`Order6LeeA2LatticeNodesH92` without assuming the endpoint completeness
statement or its chain-assembly reformulation.

The construction uses one square-normal block.  The unguarded initial
switch changes its head.  In front of a square successor, the H92 erase law
removes the final-dependent tail of the block; the frozen exact-component
connector then retargets the erased block, after which the erase is reversed.

The final sections carry out the aligned component-chain induction: at a
bare successor they extract the predecessor-final equality, while at a
non-bare successor they expose the square guard, change the current
component, restore the successor, and recurse.  Every result in this file is
source-staged only until the authorized pinned WMI compile succeeds.
-/

private abbrev laws : List (Identity Nat) :=
  Order6LeeA2LatticeNodesSingletonNormal.S6_7982.laws

private abbrev environment :=
  Order6LeeA2LatticeNodesSingletonNormal.S6_7982.squareFinalEraseEnvironment

private theorem h92PilotLawDerives :
    ∀ identity ∈
        Generated.Order6LeeA2LatticeNodes.SystemHebf52dbf4ddc.basis,
      Derives laws identity.lhs identity.rhs :=
  pilotLawDerives environment.toInitialSwitchLawEnvironment

private theorem h92DerivesComponentWords
    {chead dhead : Nat} {ctail dtail : List Nat}
    (cConnected :
      ConnectedComponentSupportConnected (chead :: ctail))
    (dConnected :
      ConnectedComponentSupportConnected (dhead :: dtail))
    (signature :
      connectedCutComponentSignatureOfList (chead :: ctail) =
        connectedCutComponentSignatureOfList (dhead :: dtail))
    (heads : chead = dhead) :
    Derives laws
      (maximalFactorWord (chead :: ctail))
      (maximalFactorWord (dhead :: dtail)) :=
  (Order6LeeA2LatticeNodesNormal.derivesComponentWords
      Order6LeeA2LatticeNodesNormal.trioEnvironment
      cConnected dConnected signature heads).transport
    h92PilotLawDerives

private theorem h92DerivesComponentBehindGuard
    (guard : Word Nat)
    {chead dhead : Nat} {ctail dtail : List Nat}
    (cConnected :
      ConnectedComponentSupportConnected (chead :: ctail))
    (dConnected :
      ConnectedComponentSupportConnected (dhead :: dtail))
    (signature :
      connectedCutComponentSignatureOfList (chead :: ctail) =
        connectedCutComponentSignatureOfList (dhead :: dtail)) :
    Derives laws
      (guard ++ maximalFactorWord (chead :: ctail))
      (guard ++ maximalFactorWord (dhead :: dtail)) :=
  (Order6LeeA2LatticeNodesNormal.derivesComponentSwitchWords
      Order6LeeA2LatticeNodesNormal.trioEnvironment guard
      cConnected dConnected signature).transport h92PilotLawDerives

/-! ## Square blocks -/

private theorem sorted_nodup_ext
    {left right : List Nat}
    (leftSorted : left.Pairwise (· ≤ ·))
    (rightSorted : right.Pairwise (· ≤ ·))
    (leftNodup : left.Nodup) (rightNodup : right.Nodup)
    (sameMembers : ∀ letter, letter ∈ left ↔ letter ∈ right) :
    left = right := by
  have permutation : left.Perm right := by
    rw [List.perm_iff_count]
    intro letter
    rw [leftNodup.count, rightNodup.count]
    simp only [sameMembers letter]
  exact List.Perm.eq_of_pairwise
    (fun _ _ _ _ leftLe rightLe => Nat.le_antisymm leftLe rightLe)
    leftSorted rightSorted permutation

private theorem getLastD_append
    (left right : List Nat) (fallback : Nat) :
    (left ++ right).getLastD fallback =
      right.getLastD (left.getLastD fallback) := by
  induction left generalizing fallback with
  | nil => rfl
  | cons head tail induction =>
      simp only [List.cons_append, List.getLastD_cons]
      exact induction head

private theorem componentFinal_append_singleton
    (letters : List Nat) (letter : Nat) :
    componentFinal (letters ++ [letter]) = letter := by
  cases letters with
  | nil => rfl
  | cons head tail =>
      simp only [List.cons_append, componentFinal]
      rw [getLastD_append]
      rfl

private theorem componentFinal_append_of_right_nonempty
    (left right : List Nat) (rightNonempty : right ≠ []) :
    componentFinal (left ++ right) = componentFinal right := by
  obtain ⟨rightHead, rightTail, rfl⟩ :=
    List.exists_cons_of_ne_nil rightNonempty
  cases left with
  | nil => rfl
  | cons leftHead leftTail =>
      simp only [List.cons_append, componentFinal]
      rw [getLastD_append]
      simpa only [List.getLastD_cons]

private def blockX (head : Nat) (support : List Nat) : List Nat :=
  head :: support.erase head

private def blockY (final : Nat) (support : List Nat) : List Nat :=
  support.erase final ++ [final]

private theorem blockX_nonempty (head : Nat) (support : List Nat) :
    blockX head support ≠ [] := by
  simp [blockX]

private theorem blockY_nonempty (final : Nat) (support : List Nat) :
    blockY final support ≠ [] := by
  simp [blockY]

private theorem blockX_subset
    {head : Nat} {support : List Nat} (headMem : head ∈ support) :
    ∀ tested ∈ blockX head support, tested ∈ support := by
  intro tested member
  rcases List.mem_cons.mp member with rfl | erased
  · exact headMem
  · exact List.mem_of_mem_erase erased

private theorem blockY_subset
    {final : Nat} {support : List Nat} (finalMem : final ∈ support) :
    ∀ tested ∈ blockY final support, tested ∈ support := by
  intro tested member
  rcases List.mem_append.mp member with erased | last
  · exact List.mem_of_mem_erase erased
  · simp only [List.mem_singleton] at last
    exact last ▸ finalMem

private theorem blockX_full
    {head : Nat} {support : List Nat} :
    ∀ tested ∈ support, tested ∈ blockX head support := by
  intro tested member
  by_cases equal : tested = head
  · subst tested
    simp [blockX]
  · exact
      List.mem_cons_of_mem head
        (List.mem_erase_of_ne equal |>.mpr member)

private theorem blockY_full
    {final : Nat} {support : List Nat} :
    ∀ tested ∈ support, tested ∈ blockY final support := by
  intro tested member
  by_cases equal : tested = final
  · exact List.mem_append_right _ (by simp [equal])
  · exact
      List.mem_append_left _
        (List.mem_erase_of_ne equal |>.mpr member)

private theorem suffix_of_suffix_length_le
    {short long whole : List Nat}
    (shortSuffix : short <:+ whole) (longSuffix : long <:+ whole)
    (lengthLe : short.length ≤ long.length) :
    short <:+ long := by
  rw [← List.reverse_prefix] at shortSuffix longSuffix ⊢
  exact List.prefix_of_prefix_length_le shortSuffix longSuffix
    (by simpa using lengthLe)

private theorem supportConnected_of_full_ends
    {support letters front suffix : List Nat}
    (frontShape : front <+: letters)
    (suffixShape : suffix <:+ letters)
    (lengthBound : front.length + suffix.length ≤ letters.length)
    (frontFull : ∀ tested ∈ support, tested ∈ front)
    (suffixFull : ∀ tested ∈ support, tested ∈ suffix)
    (subset : ∀ tested ∈ letters, tested ∈ support) :
    ConnectedComponentSupportConnected letters := by
  intro left right shape leftNonempty rightNonempty
  by_cases lengthCase : suffix.length ≤ right.length
  · have rightSuffix : right <:+ letters := ⟨left, shape.symm⟩
    have inner : suffix <:+ right :=
      suffix_of_suffix_length_le suffixShape rightSuffix lengthCase
    rcases List.exists_mem_of_ne_nil left leftNonempty with
      ⟨tested, testedLeft⟩
    have testedWhole : tested ∈ letters := by
      rw [shape]
      exact List.mem_append_left right testedLeft
    exact
      ⟨tested, testedLeft,
        inner.subset (suffixFull tested (subset tested testedWhole))⟩
  · have leftPrefix : left <+: letters := ⟨right, shape.symm⟩
    have lengths : left.length + right.length = letters.length := by
      rw [shape, List.length_append]
    have frontLe : front.length ≤ left.length := by omega
    have inner : front <+: left :=
      List.prefix_of_prefix_length_le frontShape leftPrefix frontLe
    rcases List.exists_mem_of_ne_nil right rightNonempty with
      ⟨tested, testedRight⟩
    have testedWhole : tested ∈ letters := by
      rw [shape]
      exact List.mem_append_right left testedRight
    exact
      ⟨tested,
        inner.subset (frontFull tested (subset tested testedWhole)),
        testedRight⟩

private def longBlock
    (head final : Nat) (support : List Nat) : List Nat :=
  blockX head support ++
    (blockX head support ++
      (blockY final support ++
        (blockY final support ++
          (blockX head support ++
            (blockX head support ++
              (blockY final support ++ blockY final support))))))

private def shortBlock
    (head final : Nat) (support : List Nat) : List Nat :=
  blockY final support ++
    (blockY final support ++
      (blockX head support ++
        (blockX head support ++
          (blockY final support ++ blockY final support))))

private def erasedBlock
    (head final : Nat) (support : List Nat) : List Nat :=
  blockX head support ++
    (blockX head support ++
      (blockY final support ++
        (blockY final support ++
          (blockX head support ++ blockX head support))))

private theorem longBlock_subset
    {head final : Nat} {support : List Nat}
    (headMem : head ∈ support) (finalMem : final ∈ support) :
    ∀ tested ∈ longBlock head final support, tested ∈ support := by
  intro tested member
  simp only [longBlock, List.mem_append] at member
  rcases member with m | m | m | m | m | m | m | m
  all_goals
    first
      | exact blockX_subset headMem tested m
      | exact blockY_subset finalMem tested m

private theorem shortBlock_subset
    {head final : Nat} {support : List Nat}
    (headMem : head ∈ support) (finalMem : final ∈ support) :
    ∀ tested ∈ shortBlock head final support, tested ∈ support := by
  intro tested member
  simp only [shortBlock, List.mem_append] at member
  rcases member with m | m | m | m | m | m
  all_goals
    first
      | exact blockX_subset headMem tested m
      | exact blockY_subset finalMem tested m

private theorem erasedBlock_subset
    {head final : Nat} {support : List Nat}
    (headMem : head ∈ support) (finalMem : final ∈ support) :
    ∀ tested ∈ erasedBlock head final support, tested ∈ support := by
  intro tested member
  simp only [erasedBlock, List.mem_append] at member
  rcases member with m | m | m | m | m | m
  all_goals
    first
      | exact blockX_subset headMem tested m
      | exact blockY_subset finalMem tested m

private theorem longBlock_connected
    {head final : Nat} {support : List Nat}
    (headMem : head ∈ support) (finalMem : final ∈ support) :
    ConnectedComponentSupportConnected
      (longBlock head final support) := by
  apply supportConnected_of_full_ends
    (front := blockX head support)
    (suffix := blockY final support)
    (support := support)
  · exact ⟨_, rfl⟩
  · refine
      ⟨blockX head support ++
        (blockX head support ++
          (blockY final support ++
            (blockY final support ++
              (blockX head support ++
                (blockX head support ++ blockY final support))))), ?_⟩
    simp [longBlock, List.append_assoc]
  · simp only [longBlock, List.length_append]
    omega
  · exact blockX_full
  · exact blockY_full
  · exact longBlock_subset headMem finalMem

private theorem shortBlock_connected
    {head final : Nat} {support : List Nat}
    (headMem : head ∈ support) (finalMem : final ∈ support) :
    ConnectedComponentSupportConnected
      (shortBlock head final support) := by
  apply supportConnected_of_full_ends
    (front := blockY final support)
    (suffix := blockY final support)
    (support := support)
  · exact ⟨_, rfl⟩
  · refine
      ⟨blockY final support ++
        (blockY final support ++
          (blockX head support ++
            (blockX head support ++ blockY final support))), ?_⟩
    simp [shortBlock, List.append_assoc]
  · simp only [shortBlock, List.length_append]
    omega
  · exact blockY_full
  · exact blockY_full
  · exact shortBlock_subset headMem finalMem

private theorem erasedBlock_connected
    {head final : Nat} {support : List Nat}
    (headMem : head ∈ support) (finalMem : final ∈ support) :
    ConnectedComponentSupportConnected
      (erasedBlock head final support) := by
  apply supportConnected_of_full_ends
    (front := blockX head support)
    (suffix := blockX head support)
    (support := support)
  · exact ⟨_, rfl⟩
  · refine
      ⟨blockX head support ++
        (blockX head support ++
          (blockY final support ++
            (blockY final support ++ blockX head support))), ?_⟩
    simp [erasedBlock, List.append_assoc]
  · simp only [erasedBlock, List.length_append]
    omega
  · exact blockX_full
  · exact blockX_full
  · exact erasedBlock_subset headMem finalMem

private theorem block_sortedSupport
    {head final : Nat} {support : List Nat}
    (sorted : support.Pairwise (· ≤ ·)) (nodup : support.Nodup)
    (headMem : head ∈ support) (finalMem : final ∈ support)
    {letters : List Nat}
    (subset : ∀ tested ∈ letters, tested ∈ support)
    (full : ∀ tested ∈ support, tested ∈ letters) :
    connectedComponentSortedSupport letters = support := by
  apply sorted_nodup_ext
    (connectedComponentSortedSupport_sorted _) sorted
    (connectedComponentSortedSupport_nodup _) nodup
  intro tested
  rw [connectedComponentSortedSupport_mem_iff]
  exact ⟨fun member => subset tested member,
    fun member => full tested member⟩

private theorem longBlock_sortedSupport
    {head final : Nat} {support : List Nat}
    (sorted : support.Pairwise (· ≤ ·)) (nodup : support.Nodup)
    (headMem : head ∈ support) (finalMem : final ∈ support) :
    connectedComponentSortedSupport
        (longBlock head final support) =
      support :=
  block_sortedSupport sorted nodup headMem finalMem
    (longBlock_subset headMem finalMem)
    (fun tested member => by
      simp only [longBlock, List.mem_append]
      exact Or.inl (blockX_full tested member))

private theorem shortBlock_sortedSupport
    {head final : Nat} {support : List Nat}
    (sorted : support.Pairwise (· ≤ ·)) (nodup : support.Nodup)
    (headMem : head ∈ support) (finalMem : final ∈ support) :
    connectedComponentSortedSupport
        (shortBlock head final support) =
      support :=
  block_sortedSupport sorted nodup headMem finalMem
    (shortBlock_subset headMem finalMem)
    (fun tested member => by
      simp only [shortBlock, List.mem_append]
      exact Or.inl (blockY_full tested member))

private theorem erasedBlock_sortedSupport
    {head final : Nat} {support : List Nat}
    (sorted : support.Pairwise (· ≤ ·)) (nodup : support.Nodup)
    (headMem : head ∈ support) (finalMem : final ∈ support) :
    connectedComponentSortedSupport
        (erasedBlock head final support) =
      support :=
  block_sortedSupport sorted nodup headMem finalMem
    (erasedBlock_subset headMem finalMem)
    (fun tested member => by
      simp only [erasedBlock, List.mem_append]
      exact Or.inl (blockX_full tested member))

private theorem longBlock_final
    {head final : Nat} {support : List Nat} :
    componentFinal (longBlock head final support) = final := by
  have shape :
      longBlock head final support =
        (blockX head support ++
          (blockX head support ++
            (blockY final support ++
              (blockY final support ++
                (blockX head support ++
                  (blockX head support ++
                    (blockY final support ++
                      support.erase final))))))) ++ [final] := by
    simp [longBlock, blockY, List.append_assoc]
  rw [shape]
  exact componentFinal_append_singleton _ final

private theorem erasedBlock_final_eq
    {head firstFinal secondFinal : Nat} {support : List Nat} :
    componentFinal (erasedBlock head firstFinal support) =
      componentFinal (erasedBlock head secondFinal support) := by
  have shape : ∀ final,
      erasedBlock head final support =
        (blockX head support ++
          (blockX head support ++
            (blockY final support ++
              (blockY final support ++ blockX head support)))) ++
            blockX head support := by
    intro final
    simp [erasedBlock, List.append_assoc]
  rw [shape firstFinal, shape secondFinal,
    componentFinal_append_of_right_nonempty _ _
      (blockX_nonempty head support),
    componentFinal_append_of_right_nonempty _ _
      (blockX_nonempty head support)]

private theorem multi_cutSignature
    {support : List Nat} {one two : Nat} {rest : List Nat}
    (shape : support = one :: two :: rest)
    {letters : List Nat}
    (supportEq :
      connectedComponentSortedSupport letters = support)
    {final : Nat} (finalEq : componentFinal letters = final) :
    connectedCutComponentSignatureOfList letters =
      ⟨⟨support, false⟩, final⟩ := by
  rw [connectedCutComponentSignatureOfList, finalEq]
  congr 1
  rw [connectedComponentSignatureOfList, supportEq, shape]

private theorem maximalFactorWord_longBlock
    (head final : Nat) (support : List Nat) :
    maximalFactorWord (longBlock head final support) =
      maximalFactorWord (blockX head support) ++
      maximalFactorWord (blockX head support) ++
      maximalFactorWord (blockY final support) ++
      maximalFactorWord (blockY final support) ++
      maximalFactorWord (blockX head support) ++
      maximalFactorWord (blockX head support) ++
      maximalFactorWord (blockY final support) ++
      maximalFactorWord (blockY final support) := by
  apply Word.toList_injective
  rw [maximalFactorWord_toList (by simp [longBlock, blockX])]
  simp only [Word.toList_append,
    maximalFactorWord_toList (blockX_nonempty head support),
    maximalFactorWord_toList (blockY_nonempty final support)]
  simp [longBlock, List.append_assoc]

private theorem maximalFactorWord_shortBlock
    (head final : Nat) (support : List Nat) :
    maximalFactorWord (shortBlock head final support) =
      maximalFactorWord (blockY final support) ++
      maximalFactorWord (blockY final support) ++
      maximalFactorWord (blockX head support) ++
      maximalFactorWord (blockX head support) ++
      maximalFactorWord (blockY final support) ++
      maximalFactorWord (blockY final support) := by
  apply Word.toList_injective
  rw [maximalFactorWord_toList (by simp [shortBlock, blockY])]
  simp only [Word.toList_append,
    maximalFactorWord_toList (blockX_nonempty head support),
    maximalFactorWord_toList (blockY_nonempty final support)]
  simp [shortBlock, List.append_assoc]

private theorem maximalFactorWord_erasedBlock
    (head final : Nat) (support : List Nat) :
    maximalFactorWord (erasedBlock head final support) =
      maximalFactorWord (blockX head support) ++
      maximalFactorWord (blockX head support) ++
      maximalFactorWord (blockY final support) ++
      maximalFactorWord (blockY final support) ++
      maximalFactorWord (blockX head support) ++
      maximalFactorWord (blockX head support) := by
  apply Word.toList_injective
  rw [maximalFactorWord_toList (by simp [erasedBlock, blockX])]
  simp only [Word.toList_append,
    maximalFactorWord_toList (blockX_nonempty head support),
    maximalFactorWord_toList (blockY_nonempty final support)]
  simp [erasedBlock, List.append_assoc]

private theorem exactCutSignature_of_base_and_final
    {left right : List Nat}
    (base :
      connectedComponentSignatureOfList left =
        connectedComponentSignatureOfList right)
    (final : componentFinal left = componentFinal right) :
    connectedCutComponentSignatureOfList left =
      connectedCutComponentSignatureOfList right := by
  change
    ConnectedCutComponentSignature.mk
        (connectedComponentSignatureOfList left) (componentFinal left) =
      ConnectedCutComponentSignature.mk
        (connectedComponentSignatureOfList right) (componentFinal right)
  rw [base, final]

private theorem baseSignature_eq_of_support_length_ge_two
    {left right : List Nat}
    (leftLength : 2 ≤ left.length)
    (rightLength : 2 ≤ right.length)
    (supportEq :
      connectedComponentSortedSupport left =
        connectedComponentSortedSupport right) :
    connectedComponentSignatureOfList left =
      connectedComponentSignatureOfList right := by
  cases supportShape :
      connectedComponentSortedSupport right with
  | nil =>
      have leftSupport :
          connectedComponentSortedSupport left = [] :=
        supportEq.trans supportShape
      simp [connectedComponentSignatureOfList,
        leftSupport, supportShape]
  | cons first remaining =>
      cases remaining with
      | nil =>
          have leftSupport :
              connectedComponentSortedSupport left = [first] :=
            supportEq.trans supportShape
          have leftNotOne : left.length ≠ 1 := by omega
          have rightNotOne : right.length ≠ 1 := by omega
          simp [connectedComponentSignatureOfList,
            leftSupport, supportShape, leftNotOne, rightNotOne]
      | cons second rest =>
          have leftSupport :
              connectedComponentSortedSupport left =
                first :: second :: rest :=
            supportEq.trans supportShape
          simp [connectedComponentSignatureOfList,
            leftSupport, supportShape]

private theorem longBlock_length_ge_two
    (head final : Nat) (support : List Nat) :
    2 ≤ (longBlock head final support).length := by
  have positive : 0 < (blockX head support).length :=
    List.length_pos_iff.mpr (blockX_nonempty head support)
  simp only [longBlock, List.length_append]
  omega

private theorem erasedBlock_length_ge_two
    (head final : Nat) (support : List Nat) :
    2 ≤ (erasedBlock head final support).length := by
  have positive : 0 < (blockX head support).length :=
    List.length_pos_iff.mpr (blockX_nonempty head support)
  simp only [erasedBlock, List.length_append]
  omega

private theorem longBlock_cons
    (head final : Nat) (support : List Nat) :
    longBlock head final support =
      head ::
        (support.erase head ++
          (blockX head support ++
            (blockY final support ++
              (blockY final support ++
                (blockX head support ++
                  (blockX head support ++
                    (blockY final support ++
                      blockY final support))))))) := by
  simp [longBlock, blockX, List.cons_append]

private theorem erasedBlock_cons
    (head final : Nat) (support : List Nat) :
    erasedBlock head final support =
      head ::
        (support.erase head ++
          (blockX head support ++
            (blockY final support ++
              (blockY final support ++
                (blockX head support ++ blockX head support))))) := by
  simp [erasedBlock, blockX, List.cons_append]

/-! ## The unguarded exact-component switch -/

private theorem derivesInitialComponentSwitch
    {chead dhead : Nat} {ctail dtail : List Nat}
    (cConnected :
      ConnectedComponentSupportConnected (chead :: ctail))
    (dConnected :
      ConnectedComponentSupportConnected (dhead :: dtail))
    (signature :
      connectedCutComponentSignatureOfList (chead :: ctail) =
        connectedCutComponentSignatureOfList (dhead :: dtail)) :
    Derives laws
      (maximalFactorWord (chead :: ctail))
      (maximalFactorWord (dhead :: dtail)) := by
  have baseEq :
      connectedComponentSignatureOfList (chead :: ctail) =
        connectedComponentSignatureOfList (dhead :: dtail) :=
    congrArg ConnectedCutComponentSignature.base signature
  have supportEq :
      connectedComponentSortedSupport (chead :: ctail) =
        connectedComponentSortedSupport (dhead :: dtail) := by
    have projected :=
      congrArg connectedComponentSignature.support baseEq
    rwa [connectedComponentSignatureOfList_support,
      connectedComponentSignatureOfList_support] at projected
  have cheadSupport :
      chead ∈ connectedComponentSortedSupport (chead :: ctail) :=
    (connectedComponentSortedSupport_mem_iff chead _).mpr (by simp)
  have dheadSupport :
      dhead ∈ connectedComponentSortedSupport (dhead :: dtail) :=
    (connectedComponentSortedSupport_mem_iff dhead _).mpr (by simp)
  rcases supportShape :
      connectedComponentSortedSupport (chead :: ctail) with
    _ | ⟨one, rest⟩
  · exact absurd supportShape
      (connectedComponentSortedSupport_nonempty (by simp))
  rcases rest with _ | ⟨two, rest⟩
  · have cheadEq : chead = one := by
      rw [supportShape] at cheadSupport
      simpa using cheadSupport
    have dheadEq : dhead = one := by
      rw [← supportEq, supportShape] at dheadSupport
      simpa using dheadSupport
    exact h92DerivesComponentWords cConnected dConnected signature
      (cheadEq.trans dheadEq.symm)
  · let support : List Nat := one :: two :: rest
    have supportDef : support = one :: two :: rest := rfl
    have sorted : support.Pairwise (· ≤ ·) := by
      have source :=
        connectedComponentSortedSupport_sorted (chead :: ctail)
      rw [supportShape] at source
      exact source
    have nodup : support.Nodup := by
      have source :=
        connectedComponentSortedSupport_nodup (chead :: ctail)
      rw [supportShape] at source
      exact source
    have cheadMem : chead ∈ support := by
      change chead ∈ one :: two :: rest
      rw [← supportShape]
      exact cheadSupport
    have dheadMem : dhead ∈ support := by
      rw [← supportEq, supportShape] at dheadSupport
      exact dheadSupport
    let final := componentFinal (chead :: ctail)
    have finalMem : final ∈ support := by
      have inList := componentFinal_mem chead ctail
      have inSupport :
          final ∈
            connectedComponentSortedSupport (chead :: ctail) :=
        (connectedComponentSortedSupport_mem_iff final _).mpr inList
      rw [supportShape] at inSupport
      exact inSupport
    have cSignature :
        connectedCutComponentSignatureOfList (chead :: ctail) =
          ⟨⟨support, false⟩, final⟩ :=
      multi_cutSignature supportDef supportShape rfl
    have dSignature :
        connectedCutComponentSignatureOfList (dhead :: dtail) =
          ⟨⟨support, false⟩, final⟩ :=
      signature.symm.trans cSignature
    have longCSupport :
        connectedComponentSortedSupport
            (longBlock chead final support) =
          support :=
      longBlock_sortedSupport sorted nodup cheadMem finalMem
    have longDSupport :
        connectedComponentSortedSupport
            (longBlock dhead final support) =
          support :=
      longBlock_sortedSupport sorted nodup dheadMem finalMem
    have shortCSupport :
        connectedComponentSortedSupport
            (shortBlock chead final support) =
          support :=
      shortBlock_sortedSupport sorted nodup cheadMem finalMem
    have shortDSupport :
        connectedComponentSortedSupport
            (shortBlock dhead final support) =
          support :=
      shortBlock_sortedSupport sorted nodup dheadMem finalMem
    have longCSig :
        connectedCutComponentSignatureOfList
            (longBlock chead final support) =
          ⟨⟨support, false⟩, final⟩ :=
      multi_cutSignature supportDef longCSupport longBlock_final
    have longDSig :
        connectedCutComponentSignatureOfList
            (longBlock dhead final support) =
          ⟨⟨support, false⟩, final⟩ :=
      multi_cutSignature supportDef longDSupport longBlock_final
    have shortCSig :
        connectedCutComponentSignatureOfList
            (shortBlock chead final support) =
          ⟨⟨support, false⟩, final⟩ :=
      multi_cutSignature supportDef shortCSupport
        (by
          have shape :
              shortBlock chead final support =
                (blockY final support ++
                  (blockY final support ++
                    (blockX chead support ++
                      (blockX chead support ++
                        (blockY final support ++
                          support.erase final))))) ++ [final] := by
            simp [shortBlock, blockY, List.append_assoc]
          rw [shape]
          exact componentFinal_append_singleton _ final)
    have shortDSig :
        connectedCutComponentSignatureOfList
            (shortBlock dhead final support) =
          ⟨⟨support, false⟩, final⟩ :=
      multi_cutSignature supportDef shortDSupport
        (by
          have shape :
              shortBlock dhead final support =
                (blockY final support ++
                  (blockY final support ++
                    (blockX dhead support ++
                      (blockX dhead support ++
                        (blockY final support ++
                          support.erase final))))) ++ [final] := by
            simp [shortBlock, blockY, List.append_assoc]
          rw [shape]
          exact componentFinal_append_singleton _ final)
    have eraseNonempty : support.erase final ≠ [] := by
      intro eraseEmpty
      have twoLetters : (2 : Nat) ≤ support.length := by
        rw [supportDef]
        simp
      have eraseLength := List.length_erase_of_mem finalMem
      rw [eraseEmpty] at eraseLength
      simp at eraseLength
      omega
    rcases eraseShape : support.erase final with
      _ | ⟨shortHead, shortTail⟩
    · exact absurd eraseShape eraseNonempty
    have shortCCons :
        shortBlock chead final support =
          shortHead ::
            (shortTail ++
              ([final] ++
                (blockY final support ++
                  (blockX chead support ++
                    (blockX chead support ++
                      (blockY final support ++
                        blockY final support)))))) := by
      simp [shortBlock, blockY, eraseShape, List.cons_append,
        List.append_assoc]
    have shortDCons :
        shortBlock dhead final support =
          shortHead ::
            (shortTail ++
              ([final] ++
                (blockY final support ++
                  (blockX dhead support ++
                    (blockX dhead support ++
                      (blockY final support ++
                        blockY final support)))))) := by
      simp [shortBlock, blockY, eraseShape, List.cons_append,
        List.append_assoc]
    have hopOne :
        Derives laws
          (maximalFactorWord (chead :: ctail))
          (maximalFactorWord (longBlock chead final support)) := by
      rw [longBlock_cons]
      exact
        h92DerivesComponentWords cConnected
          (longBlock_cons chead final support ▸
            longBlock_connected cheadMem finalMem)
          (by
            rw [← longBlock_cons chead final support,
              longCSig, cSignature])
          rfl
    have hopFive :
        Derives laws
          (maximalFactorWord (longBlock dhead final support))
          (maximalFactorWord (dhead :: dtail)) := by
      rw [longBlock_cons]
      exact
        h92DerivesComponentWords
          (longBlock_cons dhead final support ▸
            longBlock_connected dheadMem finalMem)
          dConnected
          (by
            rw [← longBlock_cons dhead final support,
              longDSig, dSignature])
          rfl
    have hopThree :
        Derives laws
          (maximalFactorWord (shortBlock chead final support))
          (maximalFactorWord (shortBlock dhead final support)) := by
      rw [shortCCons, shortDCons]
      exact
        h92DerivesComponentWords
          (shortCCons ▸ shortBlock_connected cheadMem finalMem)
          (shortDCons ▸ shortBlock_connected dheadMem finalMem)
          (by
            rw [← shortCCons, ← shortDCons,
              shortCSig, shortDSig])
          rfl
    have hopTwo :
        Derives laws
          (maximalFactorWord (longBlock chead final support))
          (maximalFactorWord (shortBlock chead final support)) := by
      rw [maximalFactorWord_longBlock,
        maximalFactorWord_shortBlock]
      simpa [Word.append_assoc] using
        derivesInitialSwitch
          environment.toInitialSwitchLawEnvironment
          (maximalFactorWord (blockX chead support))
          (maximalFactorWord (blockY final support))
    have hopFour :
        Derives laws
          (maximalFactorWord (shortBlock dhead final support))
          (maximalFactorWord (longBlock dhead final support)) := by
      rw [maximalFactorWord_longBlock,
        maximalFactorWord_shortBlock]
      have switched :=
        (derivesInitialSwitch
          environment.toInitialSwitchLawEnvironment
          (maximalFactorWord (blockX dhead support))
          (maximalFactorWord (blockY final support))).symm
      simpa [Word.append_assoc] using switched
    exact
      hopOne.trans
        (hopTwo.trans (hopThree.trans (hopFour.trans hopFive)))

/-- The first local obligation is discharged by the unguarded block switch. -/
theorem firstComponentSwitch :
    FirstComponentSwitchObligation := by
  intro chead dhead ctail dtail
    cConnected dConnected signature
  exact derivesInitialComponentSwitch cConnected dConnected signature

/-! ## Square exposure -/

private theorem derivesComponentToLongBlock
    {head : Nat} {tail : List Nat}
    (connected :
      ConnectedComponentSupportConnected (head :: tail))
    (lengthAtLeastTwo : 2 ≤ (head :: tail).length) :
    Derives laws
      (maximalFactorWord (head :: tail))
      (maximalFactorWord
        (longBlock head (componentFinal (head :: tail))
          (connectedComponentSortedSupport (head :: tail)))) := by
  let support :=
    connectedComponentSortedSupport (head :: tail)
  let final := componentFinal (head :: tail)
  have sorted : support.Pairwise (· ≤ ·) :=
    connectedComponentSortedSupport_sorted _
  have nodup : support.Nodup :=
    connectedComponentSortedSupport_nodup _
  have headMem : head ∈ support := by
    change
      head ∈ connectedComponentSortedSupport (head :: tail)
    exact
      (connectedComponentSortedSupport_mem_iff
        head (head :: tail)).2 (by simp)
  have finalMem : final ∈ support := by
    change
      componentFinal (head :: tail) ∈
        connectedComponentSortedSupport (head :: tail)
    exact
      (connectedComponentSortedSupport_mem_iff
        (componentFinal (head :: tail))
        (head :: tail)).2
          (componentFinal_mem head tail)
  have targetSupport :
      connectedComponentSortedSupport
          (longBlock head final support) =
        support :=
    longBlock_sortedSupport sorted nodup headMem finalMem
  have baseSignature :
      connectedComponentSignatureOfList (head :: tail) =
        connectedComponentSignatureOfList
          (longBlock head final support) := by
    apply baseSignature_eq_of_support_length_ge_two
      lengthAtLeastTwo
      (longBlock_length_ge_two head final support)
    rw [targetSupport]
  have exactSignature :
      connectedCutComponentSignatureOfList (head :: tail) =
        connectedCutComponentSignatureOfList
          (longBlock head final support) :=
    exactCutSignature_of_base_and_final baseSignature
      (by simp [final, longBlock_final])
  rw [longBlock_cons]
  exact
    h92DerivesComponentWords connected
      (longBlock_cons head final support ▸
        longBlock_connected headMem finalMem)
      (by
        rw [← longBlock_cons head final support]
        exact exactSignature)
      rfl

/-- Every non-bare aligned component exposes a literal square at its start. -/
theorem squarePrefixExposure :
    SquarePrefixExposureObligation := by
  intro head tail connected nonBare
  have lengthNotOne : (head :: tail).length ≠ 1 := by
    intro lengthOne
    cases tail with
    | nil =>
        apply nonBare
        exact
          (bareComponentSignature_iff (by simp)).2
            ⟨head, rfl⟩
    | cons next rest =>
        simp at lengthOne
  have lengthAtLeastTwo : 2 ≤ (head :: tail).length := by
    simp only [List.length_cons] at lengthNotOne ⊢
    omega
  let support :=
    connectedComponentSortedSupport (head :: tail)
  let final := componentFinal (head :: tail)
  let H := maximalFactorWord (blockX head support)
  let rest := maximalFactorWord (shortBlock head final support)
  refine ⟨H, rest, ?_⟩
  have normalized :=
    derivesComponentToLongBlock connected lengthAtLeastTwo
  change Derives laws
    (maximalFactorWord (head :: tail))
    (H ++ H ++ rest)
  simpa only [H, rest, support, final,
    maximalFactorWord_longBlock,
    maximalFactorWord_shortBlock,
    Word.append_assoc] using normalized

/-! ## Square-guarded component retargeting -/

private theorem length_eq_one_of_componentSignature_eq
    {left right : List Nat}
    (same :
      connectedComponentSignatureOfList left =
        connectedComponentSignatureOfList right)
    (leftLength : left.length = 1) :
    right.length = 1 := by
  obtain ⟨letter, rfl⟩ :=
    List.length_eq_one_iff.mp leftLength
  have leftSignature :
      connectedComponentSignatureOfList [letter] =
        ⟨[letter], false⟩ := by
    simp [connectedComponentSignatureOfList,
      connectedComponentSortedSupport,
      connectedComponentDistinctSupport]
  have rightSignature :
      connectedComponentSignatureOfList right =
        ⟨[letter], false⟩ := by
    rw [← same, leftSignature]
  have rightSupport :
      connectedComponentSortedSupport right = [letter] := by
    rw [← connectedComponentSignatureOfList_support]
    exact congrArg connectedComponentSignature.support rightSignature
  have repeatedFalse :
      decide (right.length ≠ 1) = false := by
    simpa [connectedComponentSignatureOfList, rightSupport] using
      congrArg connectedComponentSignature.repeatedUnary rightSignature
  by_cases lengthOne : right.length = 1
  · exact lengthOne
  · exact False.elim ((of_decide_eq_false repeatedFalse) lengthOne)

private theorem singleton_lists_eq_of_signature_eq
    {left right : List Nat}
    (same :
      connectedComponentSignatureOfList left =
        connectedComponentSignatureOfList right)
    (leftLength : left.length = 1)
    (rightLength : right.length = 1) :
    left = right := by
  obtain ⟨leftLetter, rfl⟩ :=
    List.length_eq_one_iff.mp leftLength
  obtain ⟨rightLetter, rfl⟩ :=
    List.length_eq_one_iff.mp rightLength
  have supportEq :
      connectedComponentSortedSupport [leftLetter] =
        connectedComponentSortedSupport [rightLetter] := by
    have projected :=
      congrArg connectedComponentSignature.support same
    simpa only [connectedComponentSignatureOfList_support] using projected
  have letterEq : leftLetter = rightLetter := by
    simpa [connectedComponentSortedSupport,
      connectedComponentDistinctSupport] using supportEq
  rw [letterEq]

private theorem erasedExactSignature
    {head firstFinal secondFinal : Nat} {support : List Nat}
    (sorted : support.Pairwise (· ≤ ·))
    (nodup : support.Nodup)
    (headMem : head ∈ support)
    (firstFinalMem : firstFinal ∈ support)
    (secondFinalMem : secondFinal ∈ support) :
    connectedCutComponentSignatureOfList
        (erasedBlock head firstFinal support) =
      connectedCutComponentSignatureOfList
        (erasedBlock head secondFinal support) := by
  apply exactCutSignature_of_base_and_final
  · apply baseSignature_eq_of_support_length_ge_two
      (erasedBlock_length_ge_two head firstFinal support)
      (erasedBlock_length_ge_two head secondFinal support)
    rw [erasedBlock_sortedSupport sorted nodup headMem firstFinalMem,
      erasedBlock_sortedSupport sorted nodup headMem secondFinalMem]
  · exact erasedBlock_final_eq

private theorem longExactSignature
    {firstHead secondHead final : Nat} {support : List Nat}
    (sorted : support.Pairwise (· ≤ ·))
    (nodup : support.Nodup)
    (firstHeadMem : firstHead ∈ support)
    (secondHeadMem : secondHead ∈ support)
    (finalMem : final ∈ support) :
    connectedCutComponentSignatureOfList
        (longBlock firstHead final support) =
      connectedCutComponentSignatureOfList
        (longBlock secondHead final support) := by
  apply exactCutSignature_of_base_and_final
  · apply baseSignature_eq_of_support_length_ge_two
      (longBlock_length_ge_two firstHead final support)
      (longBlock_length_ge_two secondHead final support)
    rw [longBlock_sortedSupport sorted nodup firstHeadMem finalMem,
      longBlock_sortedSupport sorted nodup secondHeadMem finalMem]
  · simp [longBlock_final]

private theorem derivesLongFinalChangeFirst
    (H rest : Word Nat)
    {head firstFinal secondFinal : Nat} {support : List Nat}
    (sorted : support.Pairwise (· ≤ ·))
    (nodup : support.Nodup)
    (headMem : head ∈ support)
    (firstFinalMem : firstFinal ∈ support)
    (secondFinalMem : secondFinal ∈ support) :
    Derives laws
      (maximalFactorWord
          (longBlock head firstFinal support) ++
        H ++ H ++ rest)
      (maximalFactorWord
          (longBlock head secondFinal support) ++
        H ++ H ++ rest) := by
  have eraseFirst :=
    Derives.appendRight
      (derivesSquareFinalErase environment
        (maximalFactorWord (blockX head support))
        (maximalFactorWord (blockY firstFinal support)) H)
      rest
  have erasedRetarget :
      Derives laws
        (maximalFactorWord
            (erasedBlock head firstFinal support) ++
          H ++ H ++ rest)
        (maximalFactorWord
            (erasedBlock head secondFinal support) ++
          H ++ H ++ rest) := by
    rw [erasedBlock_cons head firstFinal support,
      erasedBlock_cons head secondFinal support]
    simpa [Word.append_assoc] using
      Derives.appendRight
        (derivesInitialComponentSwitch
          (erasedBlock_cons head firstFinal support ▸
            erasedBlock_connected headMem firstFinalMem)
          (erasedBlock_cons head secondFinal support ▸
            erasedBlock_connected headMem secondFinalMem)
          (by
            rw [← erasedBlock_cons head firstFinal support,
              ← erasedBlock_cons head secondFinal support]
            exact erasedExactSignature sorted nodup headMem
              firstFinalMem secondFinalMem))
        (H ++ H ++ rest)
  have restoreSecond :=
    Derives.appendRight
      (derivesSquareFinalErase environment
        (maximalFactorWord (blockX head support))
        (maximalFactorWord (blockY secondFinal support)) H).symm
      rest
  have eraseStep :
      Derives laws
        (maximalFactorWord
            (longBlock head firstFinal support) ++
          H ++ H ++ rest)
        (maximalFactorWord
            (erasedBlock head firstFinal support) ++
          H ++ H ++ rest) := by
    simpa [maximalFactorWord_longBlock,
      maximalFactorWord_erasedBlock, Word.append_assoc]
      using eraseFirst
  have restoreStep :
      Derives laws
        (maximalFactorWord
            (erasedBlock head secondFinal support) ++
          H ++ H ++ rest)
        (maximalFactorWord
            (longBlock head secondFinal support) ++
          H ++ H ++ rest) := by
    simpa [maximalFactorWord_longBlock,
      maximalFactorWord_erasedBlock, Word.append_assoc]
      using restoreSecond
  exact
    eraseStep.trans
      (erasedRetarget.trans restoreStep)

private theorem derivesLongFinalChangeGuarded
    (guard H rest : Word Nat)
    {head firstFinal secondFinal : Nat} {support : List Nat}
    (sorted : support.Pairwise (· ≤ ·))
    (nodup : support.Nodup)
    (headMem : head ∈ support)
    (firstFinalMem : firstFinal ∈ support)
    (secondFinalMem : secondFinal ∈ support) :
    Derives laws
      ((guard ++ maximalFactorWord
          (longBlock head firstFinal support)) ++
        H ++ H ++ rest)
      ((guard ++ maximalFactorWord
          (longBlock head secondFinal support)) ++
        H ++ H ++ rest) := by
  have eraseFirst :=
    derivesSquareFinalEraseAtBoundary guard
      (maximalFactorWord (blockX head support))
      (maximalFactorWord (blockY firstFinal support))
      H rest
  have erasedRetarget :
      Derives laws
        ((guard ++ maximalFactorWord
            (erasedBlock head firstFinal support)) ++
          H ++ H ++ rest)
        ((guard ++ maximalFactorWord
            (erasedBlock head secondFinal support)) ++
          H ++ H ++ rest) := by
    rw [erasedBlock_cons head firstFinal support,
      erasedBlock_cons head secondFinal support]
    simpa [Word.append_assoc] using
      Derives.appendRight
        (h92DerivesComponentBehindGuard guard
          (erasedBlock_cons head firstFinal support ▸
            erasedBlock_connected headMem firstFinalMem)
          (erasedBlock_cons head secondFinal support ▸
            erasedBlock_connected headMem secondFinalMem)
          (by
            rw [← erasedBlock_cons head firstFinal support,
              ← erasedBlock_cons head secondFinal support]
            exact erasedExactSignature sorted nodup headMem
              firstFinalMem secondFinalMem))
        (H ++ H ++ rest)
  have restoreSecond :=
    (derivesSquareFinalEraseAtBoundary guard
      (maximalFactorWord (blockX head support))
      (maximalFactorWord (blockY secondFinal support))
      H rest).symm
  have eraseStep :
      Derives laws
        ((guard ++ maximalFactorWord
            (longBlock head firstFinal support)) ++
          H ++ H ++ rest)
        ((guard ++ maximalFactorWord
            (erasedBlock head firstFinal support)) ++
          H ++ H ++ rest) := by
    simpa [maximalFactorWord_longBlock,
      maximalFactorWord_erasedBlock, Word.append_assoc]
      using eraseFirst
  have restoreStep :
      Derives laws
        ((guard ++ maximalFactorWord
            (erasedBlock head secondFinal support)) ++
          H ++ H ++ rest)
        ((guard ++ maximalFactorWord
            (longBlock head secondFinal support)) ++
          H ++ H ++ rest) := by
    simpa [maximalFactorWord_longBlock,
      maximalFactorWord_erasedBlock, Word.append_assoc]
      using restoreSecond
  exact
    eraseStep.trans
      (erasedRetarget.trans restoreStep)

private theorem derivesNonsingletonFirstAtSquare
    (H rest : Word Nat)
    {chead dhead : Nat} {ctail dtail : List Nat}
    (cConnected :
      ConnectedComponentSupportConnected (chead :: ctail))
    (dConnected :
      ConnectedComponentSupportConnected (dhead :: dtail))
    (signature :
      connectedComponentSignatureOfList (chead :: ctail) =
        connectedComponentSignatureOfList (dhead :: dtail))
    (cLength : 2 ≤ (chead :: ctail).length)
    (dLength : 2 ≤ (dhead :: dtail).length) :
    Derives laws
      (maximalFactorWord (chead :: ctail) ++ H ++ H ++ rest)
      (maximalFactorWord (dhead :: dtail) ++ H ++ H ++ rest) := by
  let support :=
    connectedComponentSortedSupport (chead :: ctail)
  let cFinal := componentFinal (chead :: ctail)
  let dFinal := componentFinal (dhead :: dtail)
  have supportEq :
      connectedComponentSortedSupport (chead :: ctail) =
        connectedComponentSortedSupport (dhead :: dtail) := by
    have projected :=
      congrArg connectedComponentSignature.support signature
    rwa [connectedComponentSignatureOfList_support,
      connectedComponentSignatureOfList_support] at projected
  have sorted : support.Pairwise (· ≤ ·) :=
    connectedComponentSortedSupport_sorted _
  have nodup : support.Nodup :=
    connectedComponentSortedSupport_nodup _
  have cheadMem : chead ∈ support := by
    change
      chead ∈ connectedComponentSortedSupport (chead :: ctail)
    exact
      (connectedComponentSortedSupport_mem_iff
        chead (chead :: ctail)).2 (by simp)
  have dheadMem : dhead ∈ support := by
    change
      dhead ∈ connectedComponentSortedSupport (chead :: ctail)
    rw [supportEq]
    exact
      (connectedComponentSortedSupport_mem_iff
        dhead (dhead :: dtail)).2 (by simp)
  have cFinalMem : cFinal ∈ support := by
    change
      componentFinal (chead :: ctail) ∈
        connectedComponentSortedSupport (chead :: ctail)
    exact
      (connectedComponentSortedSupport_mem_iff
        (componentFinal (chead :: ctail))
        (chead :: ctail)).2
          (componentFinal_mem chead ctail)
  have dFinalMem : dFinal ∈ support := by
    change
      componentFinal (dhead :: dtail) ∈
        connectedComponentSortedSupport (chead :: ctail)
    rw [supportEq]
    exact
      (connectedComponentSortedSupport_mem_iff
        (componentFinal (dhead :: dtail))
        (dhead :: dtail)).2
          (componentFinal_mem dhead dtail)
  have normalizeC :
      Derives laws
        (maximalFactorWord (chead :: ctail) ++ H ++ H ++ rest)
        (maximalFactorWord
            (longBlock chead cFinal support) ++
          H ++ H ++ rest) := by
    simpa only [support, cFinal, Word.append_assoc] using
      Derives.appendRight
        (derivesComponentToLongBlock cConnected cLength)
        (H ++ H ++ rest)
  have normalizeD :
      Derives laws
        (maximalFactorWord
            (longBlock dhead dFinal support) ++
          H ++ H ++ rest)
        (maximalFactorWord (dhead :: dtail) ++ H ++ H ++ rest) := by
    have base :=
      Derives.appendRight
        (derivesComponentToLongBlock dConnected dLength).symm
        (H ++ H ++ rest)
    rw [← supportEq] at base
    simpa only [support, dFinal, Word.append_assoc] using base
  have finalStep :=
    derivesLongFinalChangeFirst H rest sorted nodup cheadMem
      cFinalMem dFinalMem
  have headStep :
      Derives laws
        (maximalFactorWord
            (longBlock chead dFinal support) ++
          H ++ H ++ rest)
        (maximalFactorWord
            (longBlock dhead dFinal support) ++
          H ++ H ++ rest) := by
    rw [longBlock_cons chead dFinal support,
      longBlock_cons dhead dFinal support]
    simpa [Word.append_assoc] using
      Derives.appendRight
        (derivesInitialComponentSwitch
          (longBlock_cons chead dFinal support ▸
            longBlock_connected cheadMem dFinalMem)
          (longBlock_cons dhead dFinal support ▸
            longBlock_connected dheadMem dFinalMem)
          (by
            rw [← longBlock_cons chead dFinal support,
              ← longBlock_cons dhead dFinal support]
            exact longExactSignature sorted nodup
              cheadMem dheadMem dFinalMem))
        (H ++ H ++ rest)
  exact
    normalizeC.trans
      (finalStep.trans (headStep.trans normalizeD))

private theorem derivesNonsingletonGuardedAtSquare
    (guard H rest : Word Nat)
    {chead dhead : Nat} {ctail dtail : List Nat}
    (cConnected :
      ConnectedComponentSupportConnected (chead :: ctail))
    (dConnected :
      ConnectedComponentSupportConnected (dhead :: dtail))
    (signature :
      connectedComponentSignatureOfList (chead :: ctail) =
        connectedComponentSignatureOfList (dhead :: dtail))
    (cLength : 2 ≤ (chead :: ctail).length)
    (dLength : 2 ≤ (dhead :: dtail).length) :
    Derives laws
      ((guard ++ maximalFactorWord (chead :: ctail)) ++
        H ++ H ++ rest)
      ((guard ++ maximalFactorWord (dhead :: dtail)) ++
        H ++ H ++ rest) := by
  let support :=
    connectedComponentSortedSupport (chead :: ctail)
  let cFinal := componentFinal (chead :: ctail)
  let dFinal := componentFinal (dhead :: dtail)
  have supportEq :
      connectedComponentSortedSupport (chead :: ctail) =
        connectedComponentSortedSupport (dhead :: dtail) := by
    have projected :=
      congrArg connectedComponentSignature.support signature
    rwa [connectedComponentSignatureOfList_support,
      connectedComponentSignatureOfList_support] at projected
  have sorted : support.Pairwise (· ≤ ·) :=
    connectedComponentSortedSupport_sorted _
  have nodup : support.Nodup :=
    connectedComponentSortedSupport_nodup _
  have cheadMem : chead ∈ support := by
    change
      chead ∈ connectedComponentSortedSupport (chead :: ctail)
    exact
      (connectedComponentSortedSupport_mem_iff
        chead (chead :: ctail)).2 (by simp)
  have dheadMem : dhead ∈ support := by
    change
      dhead ∈ connectedComponentSortedSupport (chead :: ctail)
    rw [supportEq]
    exact
      (connectedComponentSortedSupport_mem_iff
        dhead (dhead :: dtail)).2 (by simp)
  have cFinalMem : cFinal ∈ support := by
    change
      componentFinal (chead :: ctail) ∈
        connectedComponentSortedSupport (chead :: ctail)
    exact
      (connectedComponentSortedSupport_mem_iff
        (componentFinal (chead :: ctail))
        (chead :: ctail)).2
          (componentFinal_mem chead ctail)
  have dFinalMem : dFinal ∈ support := by
    change
      componentFinal (dhead :: dtail) ∈
        connectedComponentSortedSupport (chead :: ctail)
    rw [supportEq]
    exact
      (connectedComponentSortedSupport_mem_iff
        (componentFinal (dhead :: dtail))
        (dhead :: dtail)).2
          (componentFinal_mem dhead dtail)
  have normalizeC :
      Derives laws
        ((guard ++ maximalFactorWord (chead :: ctail)) ++
          H ++ H ++ rest)
        ((guard ++ maximalFactorWord
            (longBlock chead cFinal support)) ++
          H ++ H ++ rest) := by
    simpa only [support, cFinal, Word.append_assoc] using
      Derives.appendRight
        (Derives.prepend guard
          (derivesComponentToLongBlock cConnected cLength))
        (H ++ H ++ rest)
  have normalizeD :
      Derives laws
        ((guard ++ maximalFactorWord
            (longBlock dhead dFinal support)) ++
          H ++ H ++ rest)
        ((guard ++ maximalFactorWord (dhead :: dtail)) ++
          H ++ H ++ rest) := by
    have base :=
      Derives.appendRight
        (Derives.prepend guard
          (derivesComponentToLongBlock dConnected dLength).symm)
        (H ++ H ++ rest)
    rw [← supportEq] at base
    simpa only [support, dFinal, Word.append_assoc] using base
  have finalStep :=
    derivesLongFinalChangeGuarded guard H rest sorted nodup
      cheadMem cFinalMem dFinalMem
  have headStep :
      Derives laws
        ((guard ++ maximalFactorWord
            (longBlock chead dFinal support)) ++
          H ++ H ++ rest)
        ((guard ++ maximalFactorWord
            (longBlock dhead dFinal support)) ++
          H ++ H ++ rest) := by
    rw [longBlock_cons chead dFinal support,
      longBlock_cons dhead dFinal support]
    simpa [Word.append_assoc] using
      Derives.appendRight
        (h92DerivesComponentBehindGuard guard
          (longBlock_cons chead dFinal support ▸
            longBlock_connected cheadMem dFinalMem)
          (longBlock_cons dhead dFinal support ▸
            longBlock_connected dheadMem dFinalMem)
          (by
            rw [← longBlock_cons chead dFinal support,
              ← longBlock_cons dhead dFinal support]
            exact longExactSignature sorted nodup
              cheadMem dheadMem dFinalMem))
        (H ++ H ++ rest)
  exact
    normalizeC.trans
      (finalStep.trans (headStep.trans normalizeD))

/-- Both square-guarded component fields are constructed explicitly. -/
theorem squareInteriorComponent :
    SquareInteriorComponentObligation where
  first := by
    intro H rest chead dhead ctail dtail
      cConnected dConnected signature
    by_cases cLengthOne : (chead :: ctail).length = 1
    · have dLengthOne :=
        length_eq_one_of_componentSignature_eq signature cLengthOne
      have listsEq :=
        singleton_lists_eq_of_signature_eq signature
          cLengthOne dLengthOne
      rw [listsEq]
      exact Derives.refl _
    · have dLengthNotOne : (dhead :: dtail).length ≠ 1 := by
        intro dLengthOne
        exact cLengthOne <|
          length_eq_one_of_componentSignature_eq
            signature.symm dLengthOne
      have cLength : 2 ≤ (chead :: ctail).length := by
        simp only [List.length_cons] at cLengthOne ⊢
        omega
      have dLength : 2 ≤ (dhead :: dtail).length := by
        simp only [List.length_cons] at dLengthNotOne ⊢
        omega
      exact
        derivesNonsingletonFirstAtSquare H rest
          cConnected dConnected signature cLength dLength
  guarded := by
    intro guard H rest chead dhead ctail dtail
      cConnected dConnected signature
    by_cases cLengthOne : (chead :: ctail).length = 1
    · have dLengthOne :=
        length_eq_one_of_componentSignature_eq signature cLengthOne
      have listsEq :=
        singleton_lists_eq_of_signature_eq signature
          cLengthOne dLengthOne
      rw [listsEq]
      exact Derives.refl _
    · have dLengthNotOne : (dhead :: dtail).length ≠ 1 := by
        intro dLengthOne
        exact cLengthOne <|
          length_eq_one_of_componentSignature_eq
            signature.symm dLengthOne
      have cLength : 2 ≤ (chead :: ctail).length := by
        simp only [List.length_cons] at cLengthOne ⊢
        omega
      have dLength : 2 ≤ (dhead :: dtail).length := by
        simp only [List.length_cons] at dLengthNotOne ⊢
        omega
      exact
        derivesNonsingletonGuardedAtSquare guard H rest
          cConnected dConnected signature cLength dLength

/-! ## Turning a bare successor into the required final equality -/

private theorem connectedComponent_pairwise_flatten_append_disjoint
    {before after : List (List Nat)}
    (pairwise :
      (before ++ after).Pairwise
        ConnectedComponentSupportsDisjoint) :
    ConnectedComponentSupportsDisjoint
      before.flatten after.flatten := by
  have cross :=
    (List.pairwise_append.mp pairwise).2.2
  intro letter beforeMember afterMember
  rw [List.mem_flatten] at beforeMember afterMember
  rcases beforeMember with
    ⟨left, leftMember, letterInLeft⟩
  rcases afterMember with
    ⟨right, rightMember, letterInRight⟩
  exact
    (cross left leftMember right rightMember)
      letter letterInLeft letterInRight

private theorem connectedComponentDecomposeList_singleton_exactCut
    {letters : List Nat} {before after : List (List Nat)}
    {separator : Nat}
    (decompositionEq :
      connectedComponentDecomposeList letters =
        before ++ [separator] :: after) :
    UniqueSeparatorFourExactCut letters
      before.flatten separator after.flatten := by
  have flattenEq :=
    connectedComponentDecomposeList_flatten letters
  rw [decompositionEq] at flattenEq
  have lettersShape :
      letters = before.flatten ++ separator :: after.flatten := by
    simpa [List.append_assoc] using flattenEq.symm
  have pairwise :=
    connectedComponentDecomposeList_pairwiseDisjoint letters
  rw [decompositionEq] at pairwise
  have beforeSuffixDisjoint :
      ConnectedComponentSupportsDisjoint
        before.flatten
        ([separator] :: after).flatten :=
    connectedComponent_pairwise_flatten_append_disjoint
      (before := before)
      (after := [separator] :: after)
      pairwise
  have tailPairwise :
      ([separator] :: after).Pairwise
        ConnectedComponentSupportsDisjoint :=
    (List.pairwise_append.mp pairwise).2.1
  have singletonAfterDisjoint :
      ConnectedComponentSupportsDisjoint
        [[separator]].flatten after.flatten :=
    connectedComponent_pairwise_flatten_append_disjoint
      (before := [[separator]])
      (after := after)
      (by simpa using tailPairwise)
  have separatorNotBefore :
      separator ∉ before.flatten := by
    intro separatorBefore
    apply
      beforeSuffixDisjoint separator separatorBefore
    change separator ∈ [separator] ++ after.flatten
    simp
  have separatorNotAfter :
      separator ∉ after.flatten := by
    exact singletonAfterDisjoint separator (by simp)
  have beforeCountZero :
      before.flatten.count separator = 0 :=
    List.count_eq_zero.mpr separatorNotBefore
  have afterCountZero :
      after.flatten.count separator = 0 :=
    List.count_eq_zero.mpr separatorNotAfter
  have countOne : letters.count separator = 1 := by
    rw [lettersShape, List.count_append, List.count_cons_self,
      beforeCountZero, afterCountZero]
  have disjoint :
      UniqueSeparatorFourSupportsDisjoint
        before.flatten after.flatten := by
    intro letter beforeMember afterMember
    apply beforeSuffixDisjoint letter beforeMember
    change letter ∈ [separator] ++ after.flatten
    exact List.mem_append_right _ afterMember
  exact ⟨lettersShape, countOne, disjoint⟩

private theorem exactCut_separator_not_left
    {letters left right : List Nat} {separator : Nat}
    (cut :
      UniqueSeparatorFourExactCut
        letters left separator right) :
    separator ∉ left := by
  intro member
  have positive : 0 < left.count separator :=
    List.count_pos_iff.mpr member
  have countOne := cut.2.1
  rw [cut.1, List.count_append, List.count_cons_self] at countOne
  omega

private theorem exactCut_append_separator_injective
    {α : Type} [DecidableEq α] {separator : α} :
    ∀ {left right leftTail rightTail : List α},
      separator ∉ left →
      separator ∉ right →
      left ++ separator :: leftTail =
        right ++ separator :: rightTail →
      left = right ∧ leftTail = rightTail
  | [], [], leftTail, rightTail, _, _, equality => by
      simpa using equality
  | [], rightHead :: right, leftTail, rightTail, _,
      separatorNotRight, equality => by
      have separatorNeRightHead : separator ≠ rightHead := by
        intro separatorEq
        subst rightHead
        exact separatorNotRight (by simp)
      have headsEqual : separator = rightHead := by
        simpa using congrArg List.head? equality
      exact False.elim (separatorNeRightHead headsEqual)
  | leftHead :: left, [], leftTail, rightTail,
      separatorNotLeft, _, equality => by
      have separatorNeLeftHead : separator ≠ leftHead := by
        intro separatorEq
        subst leftHead
        exact separatorNotLeft (by simp)
      have headsEqual : leftHead = separator := by
        simpa using congrArg List.head? equality
      exact False.elim (separatorNeLeftHead headsEqual.symm)
  | leftHead :: left, rightHead :: right, leftTail, rightTail,
      separatorNotLeft, separatorNotRight, equality => by
      have leftAbsence :
          separator ≠ leftHead ∧ separator ∉ left := by
        simpa only [List.mem_cons, not_or] using separatorNotLeft
      have rightAbsence :
          separator ≠ rightHead ∧ separator ∉ right := by
        simpa only [List.mem_cons, not_or] using separatorNotRight
      have consEquality :
          leftHead = rightHead ∧
            left ++ separator :: leftTail =
              right ++ separator :: rightTail := by
        simpa only [List.cons_append, List.cons.injEq] using equality
      rcases consEquality with ⟨rfl, restEquality⟩
      have tailEquality :=
        exactCut_append_separator_injective
          leftAbsence.2 rightAbsence.2 restEquality
      exact
        ⟨congrArg (List.cons leftHead) tailEquality.1,
          tailEquality.2⟩

private theorem exactCut_sides_unique
    {letters firstLeft firstRight secondLeft secondRight : List Nat}
    {separator : Nat}
    (first :
      UniqueSeparatorFourExactCut
        letters firstLeft separator firstRight)
    (second :
      UniqueSeparatorFourExactCut
        letters secondLeft separator secondRight) :
    firstLeft = secondLeft ∧ firstRight = secondRight :=
  exactCut_append_separator_injective
    (exactCut_separator_not_left first)
    (exactCut_separator_not_left second)
    (first.1.symm.trans second.1)

private theorem s5_806_componentFinal_eq (letters : List Nat) :
    SemigroupBasis.CoRoots.S5_806.componentFinal letters =
      componentFinal letters := by
  cases letters <;> rfl

private theorem alignedBarePredecessorFinal_eq
    {left right : Word Nat}
    (same : SameH92PlainConditionalFinals left right)
    {leftBefore rightBefore : List (List Nat)}
    {leftCurrent rightCurrent : List Nat}
    {leftAfter rightAfter : List (List Nat)}
    {separator : Nat}
    (leftDecomposition :
      connectedComponentDecomposeList left.toList =
        (leftBefore ++ [leftCurrent]) ++
          [separator] :: leftAfter)
    (rightDecomposition :
      connectedComponentDecomposeList right.toList =
        (rightBefore ++ [rightCurrent]) ++
          [separator] :: rightAfter)
    (leftCurrentNonempty : leftCurrent ≠ [])
    (rightCurrentNonempty : rightCurrent ≠ []) :
    componentFinal leftCurrent =
      componentFinal rightCurrent := by
  have leftCut :
      UniqueSeparatorFourExactCut left.toList
        (leftBefore ++ [leftCurrent]).flatten
        separator leftAfter.flatten :=
    connectedComponentDecomposeList_singleton_exactCut
      leftDecomposition
  have rightCut :
      UniqueSeparatorFourExactCut right.toList
        (rightBefore ++ [rightCurrent]).flatten
        separator rightAfter.flatten :=
    connectedComponentDecomposeList_singleton_exactCut
      rightDecomposition
  obtain
    ⟨transportedBefore, transportedAfter, transportedCut,
      transportedBeforeSupport, transportedAfterSupport⟩ :=
    SemigroupBasis.CoRoots.S5_441Invariant.SameExactCutSignature.transport
      (sameExactCutSignature_of_sameComponents same.components)
      leftCut
  have transportedSides :=
    exactCut_sides_unique transportedCut rightCut
  have beforeSupport :
      ∀ tested,
        tested ∈ (leftBefore ++ [leftCurrent]).flatten ↔
          tested ∈ (rightBefore ++ [rightCurrent]).flatten := by
    intro tested
    rw [← transportedSides.1]
    exact (transportedBeforeSupport tested).symm
  have afterSupport :
      ∀ tested,
        tested ∈ leftAfter.flatten ↔
          tested ∈ rightAfter.flatten := by
    intro tested
    rw [← transportedSides.2]
    exact (transportedAfterSupport tested).symm
  have leftBeforeNonempty :
      (leftBefore ++ [leftCurrent]).flatten ≠ [] := by
    simpa [List.flatten_append] using
      List.append_ne_nil_of_right_ne_nil
        leftBefore.flatten leftCurrentNonempty
  have rightBeforeNonempty :
      (rightBefore ++ [rightCurrent]).flatten ≠ [] := by
    simpa [List.flatten_append] using
      List.append_ne_nil_of_right_ne_nil
        rightBefore.flatten rightCurrentNonempty
  have prefixFinals :
      componentFinal (leftBefore ++ [leftCurrent]).flatten =
        componentFinal (rightBefore ++ [rightCurrent]).flatten :=
    same.predecessorFinals leftCut rightCut
      beforeSupport afterSupport
      leftBeforeNonempty rightBeforeNonempty
  calc
    componentFinal leftCurrent =
        componentFinal
          (leftBefore ++ [leftCurrent]).flatten := by
      rw [List.flatten_append, List.flatten_cons, List.flatten_nil,
        List.append_nil,
        componentFinal_append_of_right_nonempty
          leftBefore.flatten leftCurrent leftCurrentNonempty]
    _ = componentFinal
          (rightBefore ++ [rightCurrent]).flatten :=
      prefixFinals
    _ = componentFinal rightCurrent := by
      rw [List.flatten_append, List.flatten_cons, List.flatten_nil,
        List.append_nil,
        componentFinal_append_of_right_nonempty
          rightBefore.flatten rightCurrent rightCurrentNonempty]

private theorem alignedLastComponentFinal_eq
    {left right : Word Nat}
    (same : SameH92PlainConditionalFinals left right)
    {leftBefore rightBefore : List (List Nat)}
    {leftCurrent rightCurrent : List Nat}
    (leftDecomposition :
      connectedComponentDecomposeList left.toList =
        leftBefore ++ [leftCurrent])
    (rightDecomposition :
      connectedComponentDecomposeList right.toList =
        rightBefore ++ [rightCurrent])
    (leftCurrentNonempty : leftCurrent ≠ [])
    (rightCurrentNonempty : rightCurrent ≠ []) :
    componentFinal leftCurrent =
      componentFinal rightCurrent := by
  have leftFlatten :=
    connectedComponentDecomposeList_flatten left.toList
  have rightFlatten :=
    connectedComponentDecomposeList_flatten right.toList
  rw [leftDecomposition] at leftFlatten
  rw [rightDecomposition] at rightFlatten
  have leftFinal :
      componentFinal left.toList =
        componentFinal leftCurrent := by
    rw [← leftFlatten, List.flatten_append,
      List.flatten_cons, List.flatten_nil, List.append_nil,
      componentFinal_append_of_right_nonempty
        leftBefore.flatten leftCurrent leftCurrentNonempty]
  have rightFinal :
      componentFinal right.toList =
        componentFinal rightCurrent := by
    rw [← rightFlatten, List.flatten_append,
      List.flatten_cons, List.flatten_nil, List.append_nil,
      componentFinal_append_of_right_nonempty
        rightBefore.flatten rightCurrent rightCurrentNonempty]
  have wholeFinal :
      componentFinal left.toList =
        componentFinal right.toList := by
    simpa only [s5_806_componentFinal_eq] using same.final
  exact leftFinal.symm.trans (wholeFinal.trans rightFinal)

/-- Public component-decomposition form of the H92 predecessor-final
coordinate.  A literal singleton successor in both aligned decompositions
forces equality of the finals of the immediately preceding nonempty
components. -/
theorem predecessorFinal_eq_at_bareSuccessor
    {left right : Word Nat}
    (same : SameH92PlainConditionalFinals left right)
    {leftBefore rightBefore : List (List Nat)}
    {leftCurrent rightCurrent : List Nat}
    {leftAfter rightAfter : List (List Nat)}
    {separator : Nat}
    (leftDecomposition :
      connectedComponentDecomposeList left.toList =
        (leftBefore ++ [leftCurrent]) ++
          [separator] :: leftAfter)
    (rightDecomposition :
      connectedComponentDecomposeList right.toList =
        (rightBefore ++ [rightCurrent]) ++
          [separator] :: rightAfter)
    (leftCurrentNonempty : leftCurrent ≠ [])
    (rightCurrentNonempty : rightCurrent ≠ []) :
    componentFinal leftCurrent =
      componentFinal rightCurrent :=
  alignedBarePredecessorFinal_eq same
    leftDecomposition rightDecomposition
    leftCurrentNonempty rightCurrentNonempty

/-- Public component-decomposition form of the whole-word final coordinate:
the finals of the two last aligned nonempty components agree. -/
theorem lastComponentFinal_eq
    {left right : Word Nat}
    (same : SameH92PlainConditionalFinals left right)
    {leftBefore rightBefore : List (List Nat)}
    {leftCurrent rightCurrent : List Nat}
    (leftDecomposition :
      connectedComponentDecomposeList left.toList =
        leftBefore ++ [leftCurrent])
    (rightDecomposition :
      connectedComponentDecomposeList right.toList =
        rightBefore ++ [rightCurrent])
    (leftCurrentNonempty : leftCurrent ≠ [])
    (rightCurrentNonempty : rightCurrent ≠ []) :
    componentFinal leftCurrent =
      componentFinal rightCurrent :=
  alignedLastComponentFinal_eq same
    leftDecomposition rightDecomposition
    leftCurrentNonempty rightCurrentNonempty

/-! ## Exact remaining structural induction -/

/-- The final coordinates actually needed by a left-to-right component
induction.  The last component always retains its final.  An earlier
component retains its final only when the following aligned component is
bare; otherwise the square-guarded move may change it. -/
def SameRequiredComponentFinals :
    List (List Nat) → List (List Nat) → Prop
  | [], [] => True
  | [left], [right] =>
      componentFinal left = componentFinal right
  | left :: leftNext :: leftTail,
      right :: rightNext :: rightTail =>
      (BareComponentSignature
          (connectedComponentSignatureOfList leftNext) →
        componentFinal left = componentFinal right) ∧
      SameRequiredComponentFinals
        (leftNext :: leftTail) (rightNext :: rightTail)
  | _, _ => False

/-- The isolated global proposition consumed after `localChainMoves`.
It has no semantic or endpoint premise: it says only that aligned
support-connected component lists, equipped with exactly the finals demanded
by `SameRequiredComponentFinals`, can be assembled syntactically.

The two semantic lemmas above supply the two clauses of
`SameRequiredComponentFinals` from an H92 descriptor.  The proof below is the
structural recursion which exposes and restores a non-bare successor while
changing the current component, then recurses behind the newly aligned
front. -/
def AlignedH92ComponentChainInduction : Prop :=
  ∀ {leftChain rightChain : List (List Nat)},
    leftChain ≠ [] →
    (∀ component, component ∈ leftChain → component ≠ []) →
    (∀ component, component ∈ rightChain → component ≠ []) →
    (∀ component, component ∈ leftChain →
      ConnectedComponentSupportConnected component) →
    (∀ component, component ∈ rightChain →
      ConnectedComponentSupportConnected component) →
    leftChain.map connectedComponentSignatureOfList =
      rightChain.map connectedComponentSignatureOfList →
    SameRequiredComponentFinals leftChain rightChain →
    Derives
      Order6LeeA2LatticeNodesSingletonNormal.S6_7982.laws
      (maximalFactorWord leftChain.flatten)
      (maximalFactorWord rightChain.flatten)

private theorem flatten_nonempty_of_components
    {components : List (List Nat)}
    (componentsNonempty : components ≠ [])
    (nonempty :
      ∀ component, component ∈ components → component ≠ []) :
    components.flatten ≠ [] := by
  rcases List.exists_cons_of_ne_nil componentsNonempty with
    ⟨first, rest, rfl⟩
  have firstNonempty := nonempty first (by simp)
  simpa using
    List.append_ne_nil_of_left_ne_nil firstNonempty rest.flatten

private theorem maximalFactorWord_flatten_cons
    {first : List Nat} {rest : List (List Nat)}
    (firstNonempty : first ≠ [])
    (restNonempty : rest.flatten ≠ []) :
    maximalFactorWord (first :: rest).flatten =
      maximalFactorWord first ++
        maximalFactorWord rest.flatten := by
  have wholeNonempty : (first :: rest).flatten ≠ [] := by
    simpa only [List.flatten_cons] using
      List.append_ne_nil_of_left_ne_nil firstNonempty rest.flatten
  apply Word.toList_injective
  rw [Word.toList_append,
    maximalFactorWord_toList wholeNonempty,
    maximalFactorWord_toList firstNonempty,
    maximalFactorWord_toList restNonempty]
  rfl

private theorem derivesExactFirstKeepingTail
    {source target : List Nat} {tail : List (List Nat)}
    (sourceNonempty : source ≠ [])
    (targetNonempty : target ≠ [])
    (tailNonempty : tail.flatten ≠ [])
    (sourceConnected :
      ConnectedComponentSupportConnected source)
    (targetConnected :
      ConnectedComponentSupportConnected target)
    (signature :
      connectedComponentSignatureOfList source =
        connectedComponentSignatureOfList target)
    (final :
      componentFinal source = componentFinal target) :
    Derives laws
      (maximalFactorWord (source :: tail).flatten)
      (maximalFactorWord (target :: tail).flatten) := by
  obtain ⟨sourceHead, sourceTail, rfl⟩ :=
    List.exists_cons_of_ne_nil sourceNonempty
  obtain ⟨targetHead, targetTail, rfl⟩ :=
    List.exists_cons_of_ne_nil targetNonempty
  have exactSignature :=
    exactCutSignature_of_base_and_final signature final
  have componentStep :=
    derivesInitialComponentSwitch
      sourceConnected targetConnected exactSignature
  have contextual :=
    Derives.appendRight componentStep
      (maximalFactorWord tail.flatten)
  rw [maximalFactorWord_flatten_cons (by simp) tailNonempty,
    maximalFactorWord_flatten_cons (by simp) tailNonempty]
  exact contextual

private theorem derivesExactBehindGuardKeepingTail
    (guard : Word Nat)
    {source target : List Nat} {tail : List (List Nat)}
    (sourceNonempty : source ≠ [])
    (targetNonempty : target ≠ [])
    (tailNonempty : tail.flatten ≠ [])
    (sourceConnected :
      ConnectedComponentSupportConnected source)
    (targetConnected :
      ConnectedComponentSupportConnected target)
    (signature :
      connectedComponentSignatureOfList source =
        connectedComponentSignatureOfList target)
    (final :
      componentFinal source = componentFinal target) :
    Derives laws
      (guard ++ maximalFactorWord (source :: tail).flatten)
      (guard ++ maximalFactorWord (target :: tail).flatten) := by
  obtain ⟨sourceHead, sourceTail, rfl⟩ :=
    List.exists_cons_of_ne_nil sourceNonempty
  obtain ⟨targetHead, targetTail, rfl⟩ :=
    List.exists_cons_of_ne_nil targetNonempty
  have exactSignature :=
    exactCutSignature_of_base_and_final signature final
  have componentStep :=
    h92DerivesComponentBehindGuard guard
      sourceConnected targetConnected exactSignature
  have contextual :=
    Derives.appendRight componentStep
      (maximalFactorWord tail.flatten)
  rw [maximalFactorWord_flatten_cons (by simp) tailNonempty,
    maximalFactorWord_flatten_cons (by simp) tailNonempty]
  simpa [Word.append_assoc] using contextual

private theorem derivesFirstBeforeNonBareSuccessor
    {source target successor : List Nat}
    {more : List (List Nat)}
    (sourceNonempty : source ≠ [])
    (targetNonempty : target ≠ [])
    (successorNonempty : successor ≠ [])
    (moreNonempty :
      ∀ component, component ∈ more → component ≠ [])
    (sourceConnected :
      ConnectedComponentSupportConnected source)
    (targetConnected :
      ConnectedComponentSupportConnected target)
    (successorConnected :
      ConnectedComponentSupportConnected successor)
    (signature :
      connectedComponentSignatureOfList source =
        connectedComponentSignatureOfList target)
    (nonBare :
      ¬BareComponentSignature
        (connectedComponentSignatureOfList successor)) :
    Derives laws
      (maximalFactorWord (source :: successor :: more).flatten)
      (maximalFactorWord (target :: successor :: more).flatten) := by
  obtain ⟨sourceHead, sourceTail, rfl⟩ :=
    List.exists_cons_of_ne_nil sourceNonempty
  obtain ⟨targetHead, targetTail, rfl⟩ :=
    List.exists_cons_of_ne_nil targetNonempty
  obtain ⟨successorHead, successorTail, rfl⟩ :=
    List.exists_cons_of_ne_nil successorNonempty
  obtain ⟨H, exposedRest, exposure⟩ :=
    squarePrefixExposure successorConnected nonBare
  cases more with
  | nil =>
      have exposeStep :=
        Derives.prepend
          (maximalFactorWord (sourceHead :: sourceTail))
          exposure
      have changeStep :=
        squareInteriorComponent.first H exposedRest
          sourceConnected targetConnected signature
      have restoreStep :=
        Derives.prepend
          (maximalFactorWord (targetHead :: targetTail))
          exposure.symm
      have exposeStepNormalized :
          Derives laws
            (maximalFactorWord (sourceHead :: sourceTail) ++
              maximalFactorWord (successorHead :: successorTail))
            (maximalFactorWord (sourceHead :: sourceTail) ++
              H ++ H ++ exposedRest) := by
        simpa only [Word.append_assoc] using exposeStep
      have restoreStepNormalized :
          Derives laws
            (maximalFactorWord (targetHead :: targetTail) ++
              H ++ H ++ exposedRest)
            (maximalFactorWord (targetHead :: targetTail) ++
              maximalFactorWord
                (successorHead :: successorTail)) := by
        simpa only [Word.append_assoc] using restoreStep
      have combined :=
        exposeStepNormalized.trans
          (changeStep.trans restoreStepNormalized)
      rw [
        maximalFactorWord_flatten_cons
          (first := sourceHead :: sourceTail)
          (rest := [successorHead :: successorTail])
          (by simp) (by simp),
        maximalFactorWord_flatten_cons
          (first := targetHead :: targetTail)
          (rest := [successorHead :: successorTail])
          (by simp) (by simp)]
      simpa [Word.append_assoc] using combined
  | cons moreHead moreTail =>
      let moreComponents := moreHead :: moreTail
      have moreFlattenNonempty :
          moreComponents.flatten ≠ [] := by
        apply flatten_nonempty_of_components (by simp)
        intro component member
        apply moreNonempty component
        simpa only [moreComponents] using member
      let moreWord := maximalFactorWord moreComponents.flatten
      have exposedWithMore :=
        Derives.appendRight exposure moreWord
      have exposeStep :=
        Derives.prepend
          (maximalFactorWord (sourceHead :: sourceTail))
          exposedWithMore
      have changeStep :=
        squareInteriorComponent.first H
          (exposedRest ++ moreWord)
          sourceConnected targetConnected signature
      have restoreStep :=
        Derives.prepend
          (maximalFactorWord (targetHead :: targetTail))
          (Derives.appendRight exposure moreWord).symm
      simp only [Word.append_assoc] at exposeStep changeStep restoreStep
      have combined :=
        exposeStep.trans (changeStep.trans restoreStep)
      have tailFlattenNonempty :
          ((successorHead :: successorTail) ::
            moreComponents).flatten ≠ [] := by
        simp
      have sourceSplit :=
        maximalFactorWord_flatten_cons
          (first := sourceHead :: sourceTail)
          (rest :=
            (successorHead :: successorTail) :: moreComponents)
          (by simp) tailFlattenNonempty
      have targetSplit :=
        maximalFactorWord_flatten_cons
          (first := targetHead :: targetTail)
          (rest :=
            (successorHead :: successorTail) :: moreComponents)
          (by simp) tailFlattenNonempty
      have successorSplit :=
        maximalFactorWord_flatten_cons
          (first := successorHead :: successorTail)
          (rest := moreComponents)
          (by simp) moreFlattenNonempty
      simpa only [moreComponents, moreWord, sourceSplit,
        targetSplit, successorSplit, Word.append_assoc] using combined

private theorem derivesBehindGuardBeforeNonBareSuccessor
    (guard : Word Nat)
    {source target successor : List Nat}
    {more : List (List Nat)}
    (sourceNonempty : source ≠ [])
    (targetNonempty : target ≠ [])
    (successorNonempty : successor ≠ [])
    (moreNonempty :
      ∀ component, component ∈ more → component ≠ [])
    (sourceConnected :
      ConnectedComponentSupportConnected source)
    (targetConnected :
      ConnectedComponentSupportConnected target)
    (successorConnected :
      ConnectedComponentSupportConnected successor)
    (signature :
      connectedComponentSignatureOfList source =
        connectedComponentSignatureOfList target)
    (nonBare :
      ¬BareComponentSignature
        (connectedComponentSignatureOfList successor)) :
    Derives laws
      (guard ++
        maximalFactorWord (source :: successor :: more).flatten)
      (guard ++
        maximalFactorWord (target :: successor :: more).flatten) := by
  obtain ⟨sourceHead, sourceTail, rfl⟩ :=
    List.exists_cons_of_ne_nil sourceNonempty
  obtain ⟨targetHead, targetTail, rfl⟩ :=
    List.exists_cons_of_ne_nil targetNonempty
  obtain ⟨successorHead, successorTail, rfl⟩ :=
    List.exists_cons_of_ne_nil successorNonempty
  obtain ⟨H, exposedRest, exposure⟩ :=
    squarePrefixExposure successorConnected nonBare
  cases more with
  | nil =>
      have exposeStep :=
        Derives.prepend
          (guard ++
            maximalFactorWord (sourceHead :: sourceTail))
          exposure
      have changeStep :=
        squareInteriorComponent.guarded guard H exposedRest
          sourceConnected targetConnected signature
      have restoreStep :=
        Derives.prepend
          (guard ++
            maximalFactorWord (targetHead :: targetTail))
          exposure.symm
      have exposeStepNormalized :
          Derives laws
            (guard ++
              maximalFactorWord (sourceHead :: sourceTail) ++
              maximalFactorWord (successorHead :: successorTail))
            (guard ++
              maximalFactorWord (sourceHead :: sourceTail) ++
              H ++ H ++ exposedRest) := by
        simpa only [Word.append_assoc] using exposeStep
      have restoreStepNormalized :
          Derives laws
            (guard ++
              maximalFactorWord (targetHead :: targetTail) ++
              H ++ H ++ exposedRest)
            (guard ++
              maximalFactorWord (targetHead :: targetTail) ++
              maximalFactorWord
                (successorHead :: successorTail)) := by
        simpa only [Word.append_assoc] using restoreStep
      have combined :=
        exposeStepNormalized.trans
          (changeStep.trans restoreStepNormalized)
      rw [
        maximalFactorWord_flatten_cons
          (first := sourceHead :: sourceTail)
          (rest := [successorHead :: successorTail])
          (by simp) (by simp),
        maximalFactorWord_flatten_cons
          (first := targetHead :: targetTail)
          (rest := [successorHead :: successorTail])
          (by simp) (by simp)]
      simpa [Word.append_assoc] using combined
  | cons moreHead moreTail =>
      let moreComponents := moreHead :: moreTail
      have moreFlattenNonempty :
          moreComponents.flatten ≠ [] := by
        apply flatten_nonempty_of_components (by simp)
        intro component member
        apply moreNonempty component
        simpa only [moreComponents] using member
      let moreWord := maximalFactorWord moreComponents.flatten
      have exposedWithMore :=
        Derives.appendRight exposure moreWord
      have exposeStep :=
        Derives.prepend
          (guard ++
            maximalFactorWord (sourceHead :: sourceTail))
          exposedWithMore
      have changeStep :=
        squareInteriorComponent.guarded guard H
          (exposedRest ++ moreWord)
          sourceConnected targetConnected signature
      have restoreStep :=
        Derives.prepend
          (guard ++
            maximalFactorWord (targetHead :: targetTail))
          (Derives.appendRight exposure moreWord).symm
      simp only [Word.append_assoc] at exposeStep changeStep restoreStep
      have combined :=
        exposeStep.trans (changeStep.trans restoreStep)
      have tailFlattenNonempty :
          ((successorHead :: successorTail) ::
            moreComponents).flatten ≠ [] := by
        simp
      have sourceSplit :=
        maximalFactorWord_flatten_cons
          (first := sourceHead :: sourceTail)
          (rest :=
            (successorHead :: successorTail) :: moreComponents)
          (by simp) tailFlattenNonempty
      have targetSplit :=
        maximalFactorWord_flatten_cons
          (first := targetHead :: targetTail)
          (rest :=
            (successorHead :: successorTail) :: moreComponents)
          (by simp) tailFlattenNonempty
      have successorSplit :=
        maximalFactorWord_flatten_cons
          (first := successorHead :: successorTail)
          (rest := moreComponents)
          (by simp) moreFlattenNonempty
      simpa only [moreComponents, moreWord, sourceSplit,
        targetSplit, successorSplit, Word.append_assoc] using combined

private theorem derivesAlignedComponentsBehindGuard
    (leftChain rightChain : List (List Nat))
    (guard : Word Nat)
    (leftChainNonempty : leftChain ≠ [])
    (leftNonempty :
      ∀ component, component ∈ leftChain → component ≠ [])
    (rightNonempty :
      ∀ component, component ∈ rightChain → component ≠ [])
    (leftConnected :
      ∀ component, component ∈ leftChain →
        ConnectedComponentSupportConnected component)
    (rightConnected :
      ∀ component, component ∈ rightChain →
        ConnectedComponentSupportConnected component)
    (signatures :
      leftChain.map connectedComponentSignatureOfList =
        rightChain.map connectedComponentSignatureOfList)
    (required :
      SameRequiredComponentFinals leftChain rightChain) :
    Derives laws
      (guard ++ maximalFactorWord leftChain.flatten)
      (guard ++ maximalFactorWord rightChain.flatten) := by
  induction leftChain generalizing rightChain guard with
  | nil =>
      exact False.elim (leftChainNonempty rfl)
  | cons leftCurrent leftTail induction =>
      cases rightChain with
      | nil =>
          simp at signatures
      | cons rightCurrent rightTail =>
          simp only [List.map_cons, List.cons.injEq] at signatures
          have leftCurrentNonempty :
              leftCurrent ≠ [] :=
            leftNonempty leftCurrent (by simp)
          have rightCurrentNonempty :
              rightCurrent ≠ [] :=
            rightNonempty rightCurrent (by simp)
          have leftCurrentConnected :
              ConnectedComponentSupportConnected leftCurrent :=
            leftConnected leftCurrent (by simp)
          have rightCurrentConnected :
              ConnectedComponentSupportConnected rightCurrent :=
            rightConnected rightCurrent (by simp)
          cases leftTail with
          | nil =>
              cases rightTail with
              | nil =>
                  change
                    componentFinal leftCurrent =
                      componentFinal rightCurrent
                    at required
                  obtain ⟨leftHead, leftRest, rfl⟩ :=
                    List.exists_cons_of_ne_nil
                      leftCurrentNonempty
                  obtain ⟨rightHead, rightRest, rfl⟩ :=
                    List.exists_cons_of_ne_nil
                      rightCurrentNonempty
                  have exactSignature :=
                    exactCutSignature_of_base_and_final
                      signatures.1 required
                  have componentStep :=
                    h92DerivesComponentBehindGuard guard
                      leftCurrentConnected rightCurrentConnected
                      exactSignature
                  simpa [List.flatten_cons] using componentStep
              | cons rightNext rightMore =>
                  simp at signatures
          | cons leftNext leftMore =>
              cases rightTail with
              | nil =>
                  simp at signatures
              | cons rightNext rightMore =>
                  change
                    (BareComponentSignature
                        (connectedComponentSignatureOfList
                          leftNext) →
                      componentFinal leftCurrent =
                        componentFinal rightCurrent) ∧
                      SameRequiredComponentFinals
                        (leftNext :: leftMore)
                        (rightNext :: rightMore)
                    at required
                  have leftNextNonempty :
                      leftNext ≠ [] :=
                    leftNonempty leftNext (by simp)
                  have leftNextConnected :
                      ConnectedComponentSupportConnected leftNext :=
                    leftConnected leftNext (by simp)
                  have leftTailFlattenNonempty :
                      (leftNext :: leftMore).flatten ≠ [] :=
                    flatten_nonempty_of_components
                      (by simp)
                      (fun component member =>
                        leftNonempty component
                          (List.mem_cons_of_mem leftCurrent member))
                  have rightTailFlattenNonempty :
                      (rightNext :: rightMore).flatten ≠ [] :=
                    flatten_nonempty_of_components
                      (by simp)
                      (fun component member =>
                        rightNonempty component
                          (List.mem_cons_of_mem rightCurrent member))
                  have firstStep :
                      Derives laws
                        (guard ++
                          maximalFactorWord
                            (leftCurrent ::
                              leftNext :: leftMore).flatten)
                        (guard ++
                          maximalFactorWord
                            (rightCurrent ::
                              leftNext :: leftMore).flatten) := by
                    by_cases bare :
                        BareComponentSignature
                          (connectedComponentSignatureOfList
                            leftNext)
                    · exact
                        derivesExactBehindGuardKeepingTail guard
                          leftCurrentNonempty
                          rightCurrentNonempty
                          leftTailFlattenNonempty
                          leftCurrentConnected
                          rightCurrentConnected
                          signatures.1 (required.1 bare)
                    · exact
                        derivesBehindGuardBeforeNonBareSuccessor
                          guard
                          leftCurrentNonempty
                          rightCurrentNonempty
                          leftNextNonempty
                          (fun component member =>
                            leftNonempty component
                              (List.mem_cons_of_mem leftCurrent
                                (List.mem_cons_of_mem
                                  leftNext member)))
                          leftCurrentConnected
                          rightCurrentConnected
                          leftNextConnected
                          signatures.1 bare
                  have tailStep :=
                    induction
                      (rightNext :: rightMore)
                      (guard ++ maximalFactorWord rightCurrent)
                      (by simp)
                      (fun component member =>
                        leftNonempty component
                          (List.mem_cons_of_mem leftCurrent member))
                      (fun component member =>
                        rightNonempty component
                          (List.mem_cons_of_mem rightCurrent member))
                      (fun component member =>
                        leftConnected component
                          (List.mem_cons_of_mem leftCurrent member))
                      (fun component member =>
                        rightConnected component
                          (List.mem_cons_of_mem rightCurrent member))
                      signatures.2 required.2
                  rw [
                    maximalFactorWord_flatten_cons
                      rightCurrentNonempty
                      leftTailFlattenNonempty]
                    at firstStep
                  have tailStepAligned :
                      Derives laws
                        (guard ++
                          (maximalFactorWord rightCurrent ++
                            maximalFactorWord
                              (leftNext :: leftMore).flatten))
                        (guard ++
                          (maximalFactorWord rightCurrent ++
                            maximalFactorWord
                              (rightNext :: rightMore).flatten)) := by
                    simpa [Word.append_assoc] using tailStep
                  have combined :=
                    firstStep.trans tailStepAligned
                  rw [
                    maximalFactorWord_flatten_cons
                      rightCurrentNonempty
                      rightTailFlattenNonempty]
                  simpa [Word.append_assoc] using combined

private theorem derivesAlignedComponentsFirst
    (leftChain rightChain : List (List Nat))
    (leftChainNonempty : leftChain ≠ [])
    (leftNonempty :
      ∀ component, component ∈ leftChain → component ≠ [])
    (rightNonempty :
      ∀ component, component ∈ rightChain → component ≠ [])
    (leftConnected :
      ∀ component, component ∈ leftChain →
        ConnectedComponentSupportConnected component)
    (rightConnected :
      ∀ component, component ∈ rightChain →
        ConnectedComponentSupportConnected component)
    (signatures :
      leftChain.map connectedComponentSignatureOfList =
        rightChain.map connectedComponentSignatureOfList)
    (required :
      SameRequiredComponentFinals leftChain rightChain) :
    Derives laws
      (maximalFactorWord leftChain.flatten)
      (maximalFactorWord rightChain.flatten) := by
  cases leftChain with
  | nil =>
      exact False.elim (leftChainNonempty rfl)
  | cons leftCurrent leftTail =>
      cases rightChain with
      | nil =>
          simp at signatures
      | cons rightCurrent rightTail =>
          simp only [List.map_cons, List.cons.injEq] at signatures
          have leftCurrentNonempty :
              leftCurrent ≠ [] :=
            leftNonempty leftCurrent (by simp)
          have rightCurrentNonempty :
              rightCurrent ≠ [] :=
            rightNonempty rightCurrent (by simp)
          have leftCurrentConnected :
              ConnectedComponentSupportConnected leftCurrent :=
            leftConnected leftCurrent (by simp)
          have rightCurrentConnected :
              ConnectedComponentSupportConnected rightCurrent :=
            rightConnected rightCurrent (by simp)
          cases leftTail with
          | nil =>
              cases rightTail with
              | nil =>
                  change
                    componentFinal leftCurrent =
                      componentFinal rightCurrent
                    at required
                  obtain ⟨leftHead, leftRest, rfl⟩ :=
                    List.exists_cons_of_ne_nil
                      leftCurrentNonempty
                  obtain ⟨rightHead, rightRest, rfl⟩ :=
                    List.exists_cons_of_ne_nil
                      rightCurrentNonempty
                  have exactSignature :=
                    exactCutSignature_of_base_and_final
                      signatures.1 required
                  have componentStep :=
                    derivesInitialComponentSwitch
                      leftCurrentConnected rightCurrentConnected
                      exactSignature
                  simpa [List.flatten_cons] using componentStep
              | cons rightNext rightMore =>
                  simp at signatures
          | cons leftNext leftMore =>
              cases rightTail with
              | nil =>
                  simp at signatures
              | cons rightNext rightMore =>
                  change
                    (BareComponentSignature
                        (connectedComponentSignatureOfList
                          leftNext) →
                      componentFinal leftCurrent =
                        componentFinal rightCurrent) ∧
                      SameRequiredComponentFinals
                        (leftNext :: leftMore)
                        (rightNext :: rightMore)
                    at required
                  have leftNextNonempty :
                      leftNext ≠ [] :=
                    leftNonempty leftNext (by simp)
                  have leftNextConnected :
                      ConnectedComponentSupportConnected leftNext :=
                    leftConnected leftNext (by simp)
                  have leftTailFlattenNonempty :
                      (leftNext :: leftMore).flatten ≠ [] :=
                    flatten_nonempty_of_components
                      (by simp)
                      (fun component member =>
                        leftNonempty component
                          (List.mem_cons_of_mem leftCurrent member))
                  have rightTailFlattenNonempty :
                      (rightNext :: rightMore).flatten ≠ [] :=
                    flatten_nonempty_of_components
                      (by simp)
                      (fun component member =>
                        rightNonempty component
                          (List.mem_cons_of_mem rightCurrent member))
                  have firstStep :
                      Derives laws
                        (maximalFactorWord
                          (leftCurrent ::
                            leftNext :: leftMore).flatten)
                        (maximalFactorWord
                          (rightCurrent ::
                            leftNext :: leftMore).flatten) := by
                    by_cases bare :
                        BareComponentSignature
                          (connectedComponentSignatureOfList
                            leftNext)
                    · exact
                        derivesExactFirstKeepingTail
                          leftCurrentNonempty
                          rightCurrentNonempty
                          leftTailFlattenNonempty
                          leftCurrentConnected
                          rightCurrentConnected
                          signatures.1 (required.1 bare)
                    · exact
                        derivesFirstBeforeNonBareSuccessor
                          leftCurrentNonempty
                          rightCurrentNonempty
                          leftNextNonempty
                          (fun component member =>
                            leftNonempty component
                              (List.mem_cons_of_mem leftCurrent
                                (List.mem_cons_of_mem
                                  leftNext member)))
                          leftCurrentConnected
                          rightCurrentConnected
                          leftNextConnected
                          signatures.1 bare
                  have tailStep :=
                    derivesAlignedComponentsBehindGuard
                      (leftNext :: leftMore)
                      (rightNext :: rightMore)
                      (maximalFactorWord rightCurrent)
                      (by simp)
                      (fun component member =>
                        leftNonempty component
                          (List.mem_cons_of_mem leftCurrent member))
                      (fun component member =>
                        rightNonempty component
                          (List.mem_cons_of_mem rightCurrent member))
                      (fun component member =>
                        leftConnected component
                          (List.mem_cons_of_mem leftCurrent member))
                      (fun component member =>
                        rightConnected component
                          (List.mem_cons_of_mem rightCurrent member))
                      signatures.2 required.2
                  rw [
                    maximalFactorWord_flatten_cons
                      rightCurrentNonempty
                      leftTailFlattenNonempty]
                    at firstStep
                  have combined :=
                    firstStep.trans tailStep
                  rw [
                    maximalFactorWord_flatten_cons
                      rightCurrentNonempty
                      rightTailFlattenNonempty]
                  exact combined

/-- The expose/change/restore recursion discharges the isolated structural
component-chain proposition. -/
theorem alignedH92ComponentChainInduction :
    AlignedH92ComponentChainInduction := by
  intro leftChain rightChain
    leftChainNonempty leftNonempty rightNonempty
    leftConnected rightConnected signatures required
  exact
    derivesAlignedComponentsFirst
      leftChain rightChain leftChainNonempty
      leftNonempty rightNonempty leftConnected rightConnected
      signatures required

private theorem singleton_pair_of_bare_signature
    {left right : List Nat}
    (leftNonempty : left ≠ [])
    (rightNonempty : right ≠ [])
    (signature :
      connectedComponentSignatureOfList left =
        connectedComponentSignatureOfList right)
    (bare :
      BareComponentSignature
        (connectedComponentSignatureOfList left)) :
    ∃ separator, left = [separator] ∧ right = [separator] := by
  obtain ⟨separator, leftShape⟩ :=
    (bareComponentSignature_iff leftNonempty).1 bare
  have leftLength : left.length = 1 := by
    simpa [leftShape]
  have rightLength :=
    length_eq_one_of_componentSignature_eq
      signature leftLength
  have listsEq :=
    singleton_lists_eq_of_signature_eq
      signature leftLength rightLength
  exact
    ⟨separator, leftShape,
      listsEq.symm.trans leftShape⟩

private theorem sameRequiredComponentFinalsAux
    {left right : Word Nat}
    (same : SameH92PlainConditionalFinals left right) :
    ∀ (leftBefore rightBefore
        leftRemaining rightRemaining : List (List Nat)),
      connectedComponentDecomposeList left.toList =
          leftBefore ++ leftRemaining →
      connectedComponentDecomposeList right.toList =
          rightBefore ++ rightRemaining →
      (∀ component, component ∈ leftRemaining →
        component ≠ []) →
      (∀ component, component ∈ rightRemaining →
        component ≠ []) →
      leftRemaining.map connectedComponentSignatureOfList =
        rightRemaining.map connectedComponentSignatureOfList →
      SameRequiredComponentFinals
        leftRemaining rightRemaining
  | leftBefore, rightBefore, [], rightRemaining,
      leftDecomposition, rightDecomposition,
      leftNonempty, rightNonempty, signatures => by
      cases rightRemaining with
      | nil => trivial
      | cons rightCurrent rightTail =>
          simp at signatures
  | leftBefore, rightBefore, leftCurrent :: leftTail,
      rightRemaining, leftDecomposition, rightDecomposition,
      leftNonempty, rightNonempty, signatures => by
      cases rightRemaining with
      | nil =>
          simp at signatures
      | cons rightCurrent rightTail =>
          simp only [List.map_cons, List.cons.injEq] at signatures
          have leftCurrentNonempty :
              leftCurrent ≠ [] :=
            leftNonempty leftCurrent (by simp)
          have rightCurrentNonempty :
              rightCurrent ≠ [] :=
            rightNonempty rightCurrent (by simp)
          cases leftTail with
          | nil =>
              cases rightTail with
              | nil =>
                  change
                    componentFinal leftCurrent =
                      componentFinal rightCurrent
                  exact
                    lastComponentFinal_eq same
                      (by
                        simpa [List.append_assoc] using
                          leftDecomposition)
                      (by
                        simpa [List.append_assoc] using
                          rightDecomposition)
                      leftCurrentNonempty
                      rightCurrentNonempty
              | cons rightNext rightMore =>
                  simp at signatures
          | cons leftNext leftMore =>
              cases rightTail with
              | nil =>
                  simp at signatures
              | cons rightNext rightMore =>
                  change
                    (BareComponentSignature
                        (connectedComponentSignatureOfList
                          leftNext) →
                      componentFinal leftCurrent =
                        componentFinal rightCurrent) ∧
                      SameRequiredComponentFinals
                        (leftNext :: leftMore)
                        (rightNext :: rightMore)
                  refine ⟨?_, ?_⟩
                  · intro bare
                    have nextSignatureData := signatures.2
                    simp only [List.map_cons,
                      List.cons.injEq] at nextSignatureData
                    have leftNextNonempty :
                        leftNext ≠ [] :=
                      leftNonempty leftNext (by simp)
                    have rightNextNonempty :
                        rightNext ≠ [] :=
                      rightNonempty rightNext (by simp)
                    obtain
                      ⟨separator, leftNextShape,
                        rightNextShape⟩ :=
                      singleton_pair_of_bare_signature
                        leftNextNonempty rightNextNonempty
                        nextSignatureData.1 bare
                    exact
                      predecessorFinal_eq_at_bareSuccessor same
                        (by
                          simpa [leftNextShape,
                            List.append_assoc] using
                              leftDecomposition)
                        (by
                          simpa [rightNextShape,
                            List.append_assoc] using
                              rightDecomposition)
                        leftCurrentNonempty
                        rightCurrentNonempty
                  · exact
                      sameRequiredComponentFinalsAux same
                        (leftBefore ++ [leftCurrent])
                        (rightBefore ++ [rightCurrent])
                        (leftNext :: leftMore)
                        (rightNext :: rightMore)
                        (by
                          simpa [List.append_assoc] using
                            leftDecomposition)
                        (by
                          simpa [List.append_assoc] using
                            rightDecomposition)
                        (fun component member =>
                          leftNonempty component
                            (List.mem_cons_of_mem
                              leftCurrent member))
                        (fun component member =>
                          rightNonempty component
                            (List.mem_cons_of_mem
                              rightCurrent member))
                        signatures.2

private theorem sameRequiredComponentFinals_of_descriptor
    {left right : Word Nat}
    (same : SameH92PlainConditionalFinals left right) :
    SameRequiredComponentFinals
      (connectedComponentDecomposeList left.toList)
      (connectedComponentDecomposeList right.toList) := by
  have signatures :
      (connectedComponentDecomposeList left.toList).map
          connectedComponentSignatureOfList =
        (connectedComponentDecomposeList right.toList).map
          connectedComponentSignatureOfList := by
    simpa [connectedComponentSignaturesWord,
      connectedComponentSignaturesList] using same.components
  exact
    sameRequiredComponentFinalsAux same
      [] []
      (connectedComponentDecomposeList left.toList)
      (connectedComponentDecomposeList right.toList)
      (by simp)
      (by simp)
      (connectedComponentDecomposeList_nonempty_components
        left.toList)
      (connectedComponentDecomposeList_nonempty_components
        right.toList)
      signatures

/-- Full H92 component-chain assembly.  The descriptor supplies precisely
the conditional finals consumed by the source-only structural induction. -/
theorem squareGuardedChainAssembly :
    SquareGuardedChainAssembly := by
  intro left right components bareData final
  let same : SameH92PlainConditionalFinals left right :=
    ⟨components, bareData.predecessorFinals, final⟩
  let leftChain :=
    connectedComponentDecomposeList left.toList
  let rightChain :=
    connectedComponentDecomposeList right.toList
  have leftChainNonempty : leftChain ≠ [] := by
    simpa [leftChain] using
      connectedComponentDecomposeList_nonempty
        (letters := left.toList) (by simp [Word.toList])
  have signatures :
      leftChain.map connectedComponentSignatureOfList =
        rightChain.map connectedComponentSignatureOfList := by
    simpa [leftChain, rightChain,
      connectedComponentSignaturesWord,
      connectedComponentSignaturesList] using components
  have derivation :=
    alignedH92ComponentChainInduction
      leftChainNonempty
      (by
        intro component member
        exact
          connectedComponentDecomposeList_nonempty_components
            left.toList component (by
              simpa only [leftChain] using member))
      (by
        intro component member
        exact
          connectedComponentDecomposeList_nonempty_components
            right.toList component (by
              simpa only [rightChain] using member))
      (by
        intro component member
        exact
          connectedComponentDecomposeList_supportConnected
            left.toList component (by
              simpa only [leftChain] using member))
      (by
        intro component member
        exact
          connectedComponentDecomposeList_supportConnected
            right.toList component (by
              simpa only [rightChain] using member))
      signatures
      (by
        simpa [leftChain, rightChain] using
          sameRequiredComponentFinals_of_descriptor same)
  have leftFlatten :
      leftChain.flatten = left.toList := by
    simpa [leftChain] using
      connectedComponentDecomposeList_flatten left.toList
  have rightFlatten :
      rightChain.flatten = right.toList := by
    simpa [rightChain] using
      connectedComponentDecomposeList_flatten right.toList
  have leftWord :
      maximalFactorWord leftChain.flatten = left := by
    apply
      SemigroupBasis.CoRoots.S5_868.maximalFactorWord_eq_of_toList
    rw [leftFlatten]
  have rightWord :
      maximalFactorWord rightChain.flatten = right := by
    apply
      SemigroupBasis.CoRoots.S5_868.maximalFactorWord_eq_of_toList
    rw [rightFlatten]
  rw [leftWord, rightWord] at derivation
  exact derivation

/-- The isolated H92 derivational-completeness obligation is discharged. -/
theorem derivationalCompleteness :
    Order6LeeA2LatticeNodesSingletonNormal.S6_7982.DerivationalCompleteness :=
  derivationalCompleteness_of_squareGuardedChainAssembly
    squareGuardedChainAssembly

/-- Representative endpoint wrapper. -/
theorem representative_basis :
    BasisFor
      Order6LeeA2LatticeNodesSingletonNormal.S6_7982.table.semigroup
      Order6LeeA2LatticeNodesSingletonNormal.S6_7982.laws :=
  Order6LeeA2LatticeNodesSingletonNormal.S6_7982.representative_basis_of_derivationalCompleteness
    derivationalCompleteness

/-- Opposite endpoint wrapper. -/
theorem opposite_basis :
    BasisFor
      Order6LeeA2LatticeNodesSingletonNormal.S6_7982.table.semigroup.opposite
      (reversedBasis
        Order6LeeA2LatticeNodesSingletonNormal.S6_7982.laws) :=
  Order6LeeA2LatticeNodesSingletonNormal.S6_7982.opposite_basis_of_derivationalCompleteness
    derivationalCompleteness

/-- The complete source-level local package used by the aligned
component-chain induction above.  None of its fields assumes the endpoint
descriptor completeness or `SquareGuardedChainAssembly`. -/
theorem localChainMoves :
    FirstComponentSwitchObligation ∧
      SquarePrefixExposureObligation ∧
        SquareInteriorComponentObligation :=
  ⟨firstComponentSwitch, squarePrefixExposure,
    squareInteriorComponent⟩

end SemigroupBasis.CoRoots.Order6LeeA2LatticeNodesH92Chain

namespace SemigroupBasis.CoRoots.Order6LeeA2LatticeNodesSingletonNormal.S6_7982

/-! ## Canonical endpoint API -/

/-- Canonical H92 derivational-completeness theorem for downstream endpoint
integration. -/
theorem derivationalCompleteness : DerivationalCompleteness :=
  SemigroupBasis.CoRoots.Order6LeeA2LatticeNodesH92Chain.derivationalCompleteness

/-- Canonical representative endpoint wrapper. -/
theorem representative_basis : BasisFor table.semigroup laws :=
  representative_basis_of_derivationalCompleteness
    derivationalCompleteness

/-- Canonical opposite endpoint wrapper. -/
theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis laws) :=
  opposite_basis_of_derivationalCompleteness
    derivationalCompleteness

end SemigroupBasis.CoRoots.Order6LeeA2LatticeNodesSingletonNormal.S6_7982
