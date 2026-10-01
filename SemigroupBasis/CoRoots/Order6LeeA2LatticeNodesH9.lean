import SemigroupBasis.CoRoots.Order6LeeA2LatticeNodesSingletonNormal

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6LeeA2LatticeNodesSingletonNormal.S6_7976

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.Order6LeeA2LatticeNodesNormal
open SemigroupBasis.CoRoots.S5_868
  (maximalFactorWord maximalFactorWord_toList)
open SemigroupBasis.CoRoots.S5_804
  (ConnectedCutComponentSignature
    connectedCutComponentSignatureOfList
    componentFinal componentFinal_mem)

/-!
# The H9 coalesced-chain normalizer

The H9 descriptor retains every literal final immediately before an exact
separator.  Consequently its gap induction never needs the Hc06
interior-final erasure.  Adjacent nonsingleton components are merged with
the shared collapse law, interior heads are changed with the transported
guarded switch, and the first gap uses the genuinely unguarded H9 switch.
-/

private theorem h9PilotLawDerives :
    ∀ identity ∈
        Generated.Order6LeeA2LatticeNodes.SystemHebf52dbf4ddc.basis,
      Derives laws identity.lhs identity.rhs :=
  pilotLawDerives
    initialCollapseEnvironment.toInitialSwitchLawEnvironment

/-- Reuse the frozen component connector without requiring the pilot laws
to occur literally in the H9 basis. -/
private theorem h9DerivesComponentWords
    {chead dhead : Nat} {ctail dtail : List Nat}
    (cConnected : ConnectedComponentSupportConnected (chead :: ctail))
    (dConnected : ConnectedComponentSupportConnected (dhead :: dtail))
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
    h9PilotLawDerives

/-- The transported guarded connector is used after at least one retained
segment has already been aligned. -/
private theorem h9DerivesComponentBehindGuard
    (guard : Word Nat)
    {chead dhead : Nat} {ctail dtail : List Nat}
    (cConnected : ConnectedComponentSupportConnected (chead :: ctail))
    (dConnected : ConnectedComponentSupportConnected (dhead :: dtail))
    (signature :
      connectedCutComponentSignatureOfList (chead :: ctail) =
        connectedCutComponentSignatureOfList (dhead :: dtail)) :
    Derives laws
      (guard ++ maximalFactorWord (chead :: ctail))
      (guard ++ maximalFactorWord (dhead :: dtail)) :=
  (Order6LeeA2LatticeNodesNormal.derivesComponentSwitchWords
      Order6LeeA2LatticeNodesNormal.trioEnvironment guard
      cConnected dConnected signature).transport h9PilotLawDerives

/-! ## Square-normal blocks -/

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
    {support letters leftContext suffix : List Nat}
    (prefixShape : leftContext <+: letters)
    (suffixShape : suffix <:+ letters)
    (lengthBound : leftContext.length + suffix.length ≤ letters.length)
    (prefixFull : ∀ tested ∈ support, tested ∈ leftContext)
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
    have prefixLe : leftContext.length ≤ left.length := by omega
    have inner : leftContext <+: left :=
      List.prefix_of_prefix_length_le prefixShape leftPrefix prefixLe
    rcases List.exists_mem_of_ne_nil right rightNonempty with
      ⟨tested, testedRight⟩
    have testedWhole : tested ∈ letters := by
      rw [shape]
      exact List.mem_append_right left testedRight
    exact
      ⟨tested,
        inner.subset (prefixFull tested (subset tested testedWhole)),
        testedRight⟩

/-- The H9 square-normal component is the literal left side of both the
initial switch and collapse laws after word substitution. -/
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

private theorem longBlock_connected
    {head final : Nat} {support : List Nat}
    (headMem : head ∈ support) (finalMem : final ∈ support) :
    ConnectedComponentSupportConnected
      (longBlock head final support) := by
  apply supportConnected_of_full_ends
    (leftContext := blockX head support)
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
    (leftContext := blockY final support)
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

private theorem shortBlock_final
    {head final : Nat} {support : List Nat} :
    componentFinal (shortBlock head final support) = final := by
  have shape :
      shortBlock head final support =
        (blockY final support ++
          (blockY final support ++
            (blockX head support ++
              (blockX head support ++
                (blockY final support ++ support.erase final))))) ++
          [final] := by
    simp [shortBlock, blockY, List.append_assoc]
  rw [shape]
  exact componentFinal_append_singleton _ final

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

/-! ## The unguarded first-component switch -/

/-- Two support-connected components with equal exact signatures can be
connected at the beginning of an H9 word even when their heads differ. -/
private theorem h9DerivesInitialComponentSwitch
    {chead dhead : Nat} {ctail dtail : List Nat}
    (cConnected : ConnectedComponentSupportConnected (chead :: ctail))
    (dConnected : ConnectedComponentSupportConnected (dhead :: dtail))
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
    exact h9DerivesComponentWords cConnected dConnected signature
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
      multi_cutSignature supportDef shortCSupport shortBlock_final
    have shortDSig :
        connectedCutComponentSignatureOfList
            (shortBlock dhead final support) =
          ⟨⟨support, false⟩, final⟩ :=
      multi_cutSignature supportDef shortDSupport shortBlock_final
    have longCCons :
        ∃ tail, longBlock chead final support = chead :: tail := by
      refine
        ⟨support.erase chead ++
          (blockX chead support ++
            (blockY final support ++
              (blockY final support ++
                (blockX chead support ++
                  (blockX chead support ++
                    (blockY final support ++
                      blockY final support)))))), ?_⟩
      simp [longBlock, blockX, List.cons_append]
    have longDCons :
        ∃ tail, longBlock dhead final support = dhead :: tail := by
      refine
        ⟨support.erase dhead ++
          (blockX dhead support ++
            (blockY final support ++
              (blockY final support ++
                (blockX dhead support ++
                  (blockX dhead support ++
                    (blockY final support ++
                      blockY final support)))))), ?_⟩
      simp [longBlock, blockX, List.cons_append]
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
        ∃ tail,
          shortBlock chead final support = shortHead :: tail := by
      refine
        ⟨shortTail ++
          ([final] ++
            (blockY final support ++
              (blockX chead support ++
                (blockX chead support ++
                  (blockY final support ++
                    blockY final support))))), ?_⟩
      simp [shortBlock, blockY, eraseShape, List.cons_append,
        List.append_assoc]
    have shortDCons :
        ∃ tail,
          shortBlock dhead final support = shortHead :: tail := by
      refine
        ⟨shortTail ++
          ([final] ++
            (blockY final support ++
              (blockX dhead support ++
                (blockX dhead support ++
                  (blockY final support ++
                    blockY final support))))), ?_⟩
      simp [shortBlock, blockY, eraseShape, List.cons_append,
        List.append_assoc]
    obtain ⟨longCTail, longCCons⟩ := longCCons
    obtain ⟨longDTail, longDCons⟩ := longDCons
    obtain ⟨shortCTail, shortCCons⟩ := shortCCons
    obtain ⟨shortDTail, shortDCons⟩ := shortDCons
    have hopOne :
        Derives laws
          (maximalFactorWord (chead :: ctail))
          (maximalFactorWord (longBlock chead final support)) := by
      rw [longCCons]
      exact
        h9DerivesComponentWords cConnected
          (longCCons ▸ longBlock_connected cheadMem finalMem)
          (by rw [← longCCons, longCSig, cSignature]) rfl
    have hopFive :
        Derives laws
          (maximalFactorWord (longBlock dhead final support))
          (maximalFactorWord (dhead :: dtail)) := by
      rw [longDCons]
      exact
        h9DerivesComponentWords
          (longDCons ▸ longBlock_connected dheadMem finalMem)
          dConnected
          (by rw [← longDCons, longDSig, dSignature]) rfl
    have hopThree :
        Derives laws
          (maximalFactorWord (shortBlock chead final support))
          (maximalFactorWord (shortBlock dhead final support)) := by
      rw [shortCCons, shortDCons]
      exact
        h9DerivesComponentWords
          (shortCCons ▸ shortBlock_connected cheadMem finalMem)
          (shortDCons ▸ shortBlock_connected dheadMem finalMem)
          (by
            rw [← shortCCons, ← shortDCons, shortCSig, shortDSig])
          rfl
    have hopTwo :
        Derives laws
          (maximalFactorWord (longBlock chead final support))
          (maximalFactorWord (shortBlock chead final support)) := by
      rw [maximalFactorWord_longBlock,
        maximalFactorWord_shortBlock]
      simpa [Word.append_assoc] using
        derivesInitialSwitch
          initialCollapseEnvironment.toInitialSwitchLawEnvironment
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
          initialCollapseEnvironment.toInitialSwitchLawEnvironment
          (maximalFactorWord (blockX dhead support))
          (maximalFactorWord (blockY final support))).symm
      simpa [Word.append_assoc] using switched
    exact
      hopOne.trans
        (hopTwo.trans (hopThree.trans (hopFour.trans hopFive)))

/-! ## Collapsing a separator-free component chain -/

/-- A support-connected component of length at least two derives to the H9
square block with its literal head and final. -/
private theorem h9DerivesComponentToLongBlock
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
    change head ∈ connectedComponentSortedSupport (head :: tail)
    rw [connectedComponentSortedSupport_mem_iff]
    simp
  have finalMem : final ∈ support := by
    change final ∈ connectedComponentSortedSupport (head :: tail)
    rw [connectedComponentSortedSupport_mem_iff]
    exact componentFinal_mem head tail
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
      lengthAtLeastTwo (longBlock_length_ge_two head final support)
    rw [targetSupport]
  have exactSignature :
      connectedCutComponentSignatureOfList (head :: tail) =
        connectedCutComponentSignatureOfList
          (longBlock head final support) :=
    exactCutSignature_of_base_and_final baseSignature
      (by simp [final, longBlock_final])
  have targetShape :
      ∃ targetTail,
        longBlock head final support = head :: targetTail := by
    refine
      ⟨support.erase head ++
        (blockX head support ++
          (blockY final support ++
            (blockY final support ++
              (blockX head support ++
                (blockX head support ++
                  (blockY final support ++
                    blockY final support)))))), ?_⟩
    simp [longBlock, blockX, List.cons_append]
  obtain ⟨targetTail, targetShape⟩ := targetShape
  rw [targetShape]
  exact
    h9DerivesComponentWords connected
      (targetShape ▸ longBlock_connected headMem finalMem)
      (by rw [← targetShape]; exact exactSignature) rfl

private def halfBlock
    (head final : Nat) (support : List Nat) : List Nat :=
  blockX head support ++
    (blockX head support ++
      (blockY final support ++ blockY final support))

private theorem halfBlock_nonempty
    (head final : Nat) (support : List Nat) :
    halfBlock head final support ≠ [] := by
  simp [halfBlock, blockX]

private theorem longBlock_eq_halfBlock_square
    (head final : Nat) (support : List Nat) :
    longBlock head final support =
      halfBlock head final support ++
        halfBlock head final support := by
  simp [longBlock, halfBlock, List.append_assoc]

private theorem maximalFactorWord_append_of_nonempty
    {left right : List Nat}
    (leftNonempty : left ≠ []) (rightNonempty : right ≠ []) :
    maximalFactorWord (left ++ right) =
      maximalFactorWord left ++ maximalFactorWord right := by
  have appendNonempty : left ++ right ≠ [] := by
    intro appendEmpty
    exact leftNonempty (List.append_eq_nil_iff.mp appendEmpty).1
  apply Word.toList_injective
  rw [Word.toList_append,
    maximalFactorWord_toList appendNonempty,
    maximalFactorWord_toList leftNonempty,
    maximalFactorWord_toList rightNonempty]

/-- Reverse collapse merges two adjacent H9 square blocks.  The doubled
intermediate is support-connected and is retargeted with the frozen
component connector, preserving the outer head and final. -/
private theorem h9DerivesMergeLongBlocks
    {leftHead leftFinal rightHead rightFinal : Nat}
    {leftSupport rightSupport : List Nat}
    (leftSorted : leftSupport.Pairwise (· ≤ ·))
    (leftNodup : leftSupport.Nodup)
    (leftHeadMem : leftHead ∈ leftSupport)
    (leftFinalMem : leftFinal ∈ leftSupport)
    (rightSorted : rightSupport.Pairwise (· ≤ ·))
    (rightNodup : rightSupport.Nodup)
    (rightHeadMem : rightHead ∈ rightSupport)
    (rightFinalMem : rightFinal ∈ rightSupport) :
    Derives laws
      (maximalFactorWord
          (longBlock leftHead leftFinal leftSupport) ++
        maximalFactorWord
          (longBlock rightHead rightFinal rightSupport))
      (maximalFactorWord
        (longBlock leftHead rightFinal
          (connectedComponentSortedSupport
            (leftSupport ++ rightSupport)))) := by
  let leftHalf :=
    halfBlock leftHead leftFinal leftSupport
  let rightHalf :=
    halfBlock rightHead rightFinal rightSupport
  let leftBlock :=
    longBlock leftHead leftFinal leftSupport
  let rightBlock :=
    longBlock rightHead rightFinal rightSupport
  let pair := leftBlock ++ rightBlock
  let merged := pair ++ pair
  let unionSupport :=
    connectedComponentSortedSupport
      (leftSupport ++ rightSupport)
  have leftHalfNonempty : leftHalf ≠ [] :=
    halfBlock_nonempty leftHead leftFinal leftSupport
  have rightHalfNonempty : rightHalf ≠ [] :=
    halfBlock_nonempty rightHead rightFinal rightSupport
  have leftBlockNonempty : leftBlock ≠ [] := by
    simp [leftBlock, longBlock, blockX]
  have rightBlockNonempty : rightBlock ≠ [] := by
    simp [rightBlock, longBlock, blockX]
  have pairNonempty : pair ≠ [] := by
    intro pairEmpty
    exact leftBlockNonempty
      (List.append_eq_nil_iff.mp pairEmpty).1
  have leftWordSplit :
      maximalFactorWord leftBlock =
        maximalFactorWord leftHalf ++
          maximalFactorWord leftHalf := by
    change
      maximalFactorWord
          (longBlock leftHead leftFinal leftSupport) =
        maximalFactorWord
            (halfBlock leftHead leftFinal leftSupport) ++
          maximalFactorWord
            (halfBlock leftHead leftFinal leftSupport)
    rw [longBlock_eq_halfBlock_square]
    exact maximalFactorWord_append_of_nonempty
      leftHalfNonempty leftHalfNonempty
  have rightWordSplit :
      maximalFactorWord rightBlock =
        maximalFactorWord rightHalf ++
          maximalFactorWord rightHalf := by
    change
      maximalFactorWord
          (longBlock rightHead rightFinal rightSupport) =
        maximalFactorWord
            (halfBlock rightHead rightFinal rightSupport) ++
          maximalFactorWord
            (halfBlock rightHead rightFinal rightSupport)
    rw [longBlock_eq_halfBlock_square]
    exact maximalFactorWord_append_of_nonempty
      rightHalfNonempty rightHalfNonempty
  have pairWordSplit :
      maximalFactorWord pair =
        maximalFactorWord leftBlock ++
          maximalFactorWord rightBlock :=
    maximalFactorWord_append_of_nonempty
      leftBlockNonempty rightBlockNonempty
  have mergedWordSplit :
      maximalFactorWord merged =
        maximalFactorWord pair ++ maximalFactorWord pair :=
    maximalFactorWord_append_of_nonempty
      pairNonempty pairNonempty
  have expansion :
      Derives laws
        (maximalFactorWord leftBlock ++
          maximalFactorWord rightBlock)
        (maximalFactorWord merged) := by
    simpa only [mergedWordSplit, pairWordSplit,
      leftWordSplit, rightWordSplit, Word.append_assoc] using
      (derivesCollapse initialCollapseEnvironment
        (maximalFactorWord leftHalf)
        (maximalFactorWord rightHalf)).symm
  have leftBlockMem :
      ∀ tested, tested ∈ leftBlock ↔ tested ∈ leftSupport := by
    intro tested
    constructor
    · exact longBlock_subset
        leftHeadMem leftFinalMem tested
    · intro member
      change tested ∈
        longBlock leftHead leftFinal leftSupport
      simp only [longBlock, List.mem_append]
      exact Or.inl (blockX_full tested member)
  have rightBlockMem :
      ∀ tested, tested ∈ rightBlock ↔ tested ∈ rightSupport := by
    intro tested
    constructor
    · exact longBlock_subset
        rightHeadMem rightFinalMem tested
    · intro member
      change tested ∈
        longBlock rightHead rightFinal rightSupport
      simp only [longBlock, List.mem_append]
      exact Or.inl (blockX_full tested member)
  have pairMem :
      ∀ tested,
        tested ∈ pair ↔
          tested ∈ leftSupport ∨ tested ∈ rightSupport := by
    intro tested
    change
      tested ∈ leftBlock ++ rightBlock ↔
        tested ∈ leftSupport ∨ tested ∈ rightSupport
    rw [List.mem_append,
      leftBlockMem tested, rightBlockMem tested]
  have unionMem :
      ∀ tested,
        tested ∈ unionSupport ↔
          tested ∈ leftSupport ∨ tested ∈ rightSupport := by
    intro tested
    change
      tested ∈ connectedComponentSortedSupport
          (leftSupport ++ rightSupport) ↔
        tested ∈ leftSupport ∨ tested ∈ rightSupport
    rw [connectedComponentSortedSupport_mem_iff,
      List.mem_append]
  have pairFull :
      ∀ tested, tested ∈ unionSupport → tested ∈ pair := by
    intro tested member
    exact (pairMem tested).2 ((unionMem tested).1 member)
  have pairSubset :
      ∀ tested, tested ∈ pair → tested ∈ unionSupport := by
    intro tested member
    exact (unionMem tested).2 ((pairMem tested).1 member)
  have unionSorted : unionSupport.Pairwise (· ≤ ·) :=
    connectedComponentSortedSupport_sorted _
  have unionNodup : unionSupport.Nodup :=
    connectedComponentSortedSupport_nodup _
  have leftHeadUnion : leftHead ∈ unionSupport :=
    (unionMem leftHead).2 (Or.inl leftHeadMem)
  have rightFinalUnion : rightFinal ∈ unionSupport :=
    (unionMem rightFinal).2 (Or.inr rightFinalMem)
  have mergedSubset :
      ∀ tested, tested ∈ merged → tested ∈ unionSupport := by
    intro tested member
    rcases List.mem_append.mp member with inFirst | inSecond
    · exact pairSubset tested inFirst
    · exact pairSubset tested inSecond
  have mergedFull :
      ∀ tested, tested ∈ unionSupport → tested ∈ merged := by
    intro tested member
    exact List.mem_append_left pair (pairFull tested member)
  have mergedConnected :
      ConnectedComponentSupportConnected merged := by
    apply supportConnected_of_full_ends
      (support := unionSupport) (leftContext := pair) (suffix := pair)
    · exact ⟨pair, rfl⟩
    · exact ⟨pair, rfl⟩
    · simp only [merged, List.length_append]
      omega
    · exact pairFull
    · exact pairFull
    · exact mergedSubset
  have mergedSupport :
      connectedComponentSortedSupport merged = unionSupport :=
    block_sortedSupport unionSorted unionNodup
      leftHeadUnion rightFinalUnion mergedSubset mergedFull
  have targetSupport :
      connectedComponentSortedSupport
          (longBlock leftHead rightFinal unionSupport) =
        unionSupport :=
    longBlock_sortedSupport unionSorted unionNodup
      leftHeadUnion rightFinalUnion
  have mergedFinal :
      componentFinal merged = rightFinal := by
    change componentFinal (pair ++ pair) = rightFinal
    rw [componentFinal_append_of_right_nonempty
      pair pair pairNonempty]
    change componentFinal (leftBlock ++ rightBlock) = rightFinal
    rw [componentFinal_append_of_right_nonempty
      leftBlock rightBlock rightBlockNonempty]
    change componentFinal
      (longBlock rightHead rightFinal rightSupport) = rightFinal
    exact longBlock_final
  have mergedLength : 2 ≤ merged.length := by
    have pairPositive : 0 < pair.length :=
      List.length_pos_iff.mpr pairNonempty
    simp only [merged, List.length_append]
    omega
  have baseSignature :
      connectedComponentSignatureOfList merged =
        connectedComponentSignatureOfList
          (longBlock leftHead rightFinal unionSupport) :=
    baseSignature_eq_of_support_length_ge_two
      mergedLength
      (longBlock_length_ge_two leftHead rightFinal unionSupport)
      (mergedSupport.trans targetSupport.symm)
  have exactSignature :
      connectedCutComponentSignatureOfList merged =
        connectedCutComponentSignatureOfList
          (longBlock leftHead rightFinal unionSupport) :=
    exactCutSignature_of_base_and_final baseSignature
      (by rw [mergedFinal, longBlock_final])
  have mergedShape :
      ∃ tail, merged = leftHead :: tail := by
    refine
      ⟨leftSupport.erase leftHead ++
        (blockX leftHead leftSupport ++
          (blockY leftFinal leftSupport ++
            (blockY leftFinal leftSupport ++
              (blockX leftHead leftSupport ++
                (blockX leftHead leftSupport ++
                  (blockY leftFinal leftSupport ++
                    blockY leftFinal leftSupport)))))) ++
        rightBlock ++ pair, ?_⟩
    simp [merged, pair, leftBlock, longBlock, blockX,
      List.cons_append, List.append_assoc]
  have targetShape :
      ∃ tail,
        longBlock leftHead rightFinal unionSupport =
          leftHead :: tail := by
    refine
      ⟨unionSupport.erase leftHead ++
        (blockX leftHead unionSupport ++
          (blockY rightFinal unionSupport ++
            (blockY rightFinal unionSupport ++
              (blockX leftHead unionSupport ++
                (blockX leftHead unionSupport ++
                  (blockY rightFinal unionSupport ++
                    blockY rightFinal unionSupport)))))), ?_⟩
    simp [longBlock, blockX, List.cons_append]
  obtain ⟨mergedTail, mergedShape⟩ := mergedShape
  obtain ⟨targetTail, targetShape⟩ := targetShape
  have connector :
      Derives laws
        (maximalFactorWord merged)
        (maximalFactorWord
          (longBlock leftHead rightFinal unionSupport)) := by
    rw [mergedShape, targetShape]
    exact
      h9DerivesComponentWords
        (mergedShape ▸ mergedConnected)
        (targetShape ▸
          longBlock_connected leftHeadUnion rightFinalUnion)
        (by
          rw [← mergedShape, ← targetShape]
          exact exactSignature)
        rfl
  exact expansion.trans connector

private theorem headD_mem_of_nonempty
    {letters : List Nat} (nonempty : letters ≠ []) :
    letters.headD 0 ∈ letters := by
  obtain ⟨head, tail, rfl⟩ :=
    List.exists_cons_of_ne_nil nonempty
  simp

private theorem componentFinal_mem_of_nonempty
    {letters : List Nat} (nonempty : letters ≠ []) :
    componentFinal letters ∈ letters := by
  obtain ⟨head, tail, rfl⟩ :=
    List.exists_cons_of_ne_nil nonempty
  exact componentFinal_mem head tail

/-- Fold every nonsingleton component in one separator-free gap to a
single H9 square block. -/
private theorem h9ListDerivesComponentChainToLongBlock :
    ∀ (components : List (List Nat)),
      components ≠ [] →
      (∀ component ∈ components, component ≠ []) →
      (∀ component ∈ components,
        ConnectedComponentSupportConnected component) →
      (∀ component ∈ components, 2 ≤ component.length) →
      SemigroupBasis.CoRoots.S5_107.ListDerives
        laws components.flatten
        (longBlock (components.flatten.headD 0)
          (componentFinal components.flatten)
          (connectedComponentSortedSupport components.flatten))
  | [], componentsNonempty, _, _, _ =>
      False.elim (componentsNonempty rfl)
  | component :: rest, _, allNonempty, allConnected, allLength => by
      have componentNonempty : component ≠ [] :=
        allNonempty component (by simp)
      obtain ⟨head, tail, componentShape⟩ :=
        List.exists_cons_of_ne_nil componentNonempty
      subst component
      have componentConnected :
          ConnectedComponentSupportConnected (head :: tail) :=
        allConnected (head :: tail) (by simp)
      have componentLength :
          2 ≤ (head :: tail).length :=
        allLength (head :: tail) (by simp)
      have componentWordDerivation :=
        h9DerivesComponentToLongBlock
          componentConnected componentLength
      have componentListDerivation :=
        SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
          componentWordDerivation
      rw [maximalFactorWord_toList (by simp),
        maximalFactorWord_toList
          (by simp [longBlock, blockX])]
        at componentListDerivation
      cases rest with
      | nil =>
          simpa [List.flatten_cons] using componentListDerivation
      | cons next remaining =>
          let restComponents := next :: remaining
          let restLetters := restComponents.flatten
          have restComponentsNonempty : restComponents ≠ [] := by
            simp [restComponents]
          have nextNonempty : next ≠ [] :=
            allNonempty next (by simp)
          have restLettersNonempty : restLetters ≠ [] := by
            intro restEmpty
            change (next :: remaining).flatten = [] at restEmpty
            rw [List.flatten_cons] at restEmpty
            exact
              nextNonempty
                (List.append_eq_nil_iff.mp restEmpty).1
          have restDerivation :=
            h9ListDerivesComponentChainToLongBlock
              restComponents restComponentsNonempty
              (fun current member => by
                change
                  List.Mem current (next :: remaining) at member
                exact
                  allNonempty current
                    (List.Mem.tail (head :: tail) member))
              (fun current member => by
                change
                  List.Mem current (next :: remaining) at member
                exact
                  allConnected current
                    (List.Mem.tail (head :: tail) member))
              (fun current member => by
                change
                  List.Mem current (next :: remaining) at member
                exact
                  allLength current
                    (List.Mem.tail (head :: tail) member))
          let leftSupport :=
            connectedComponentSortedSupport (head :: tail)
          let rightSupport :=
            connectedComponentSortedSupport restLetters
          let leftFinal := componentFinal (head :: tail)
          let rightHead := restLetters.headD 0
          let rightFinal := componentFinal restLetters
          let leftBlock :=
            longBlock head leftFinal leftSupport
          let rightBlock :=
            longBlock rightHead rightFinal rightSupport
          have leftSorted : leftSupport.Pairwise (· ≤ ·) :=
            connectedComponentSortedSupport_sorted _
          have leftNodup : leftSupport.Nodup :=
            connectedComponentSortedSupport_nodup _
          have rightSorted : rightSupport.Pairwise (· ≤ ·) :=
            connectedComponentSortedSupport_sorted _
          have rightNodup : rightSupport.Nodup :=
            connectedComponentSortedSupport_nodup _
          have headMem : head ∈ leftSupport := by
            change
              head ∈
                connectedComponentSortedSupport (head :: tail)
            exact
              (connectedComponentSortedSupport_mem_iff
                head (head :: tail)).2 (by simp)
          have leftFinalMem : leftFinal ∈ leftSupport := by
            change
              componentFinal (head :: tail) ∈
                connectedComponentSortedSupport (head :: tail)
            exact
              (connectedComponentSortedSupport_mem_iff
                (componentFinal (head :: tail))
                (head :: tail)).2
                  (componentFinal_mem_of_nonempty (by simp))
          have rightHeadMem : rightHead ∈ rightSupport := by
            change
              restLetters.headD 0 ∈
                connectedComponentSortedSupport restLetters
            exact
              (connectedComponentSortedSupport_mem_iff
                (restLetters.headD 0) restLetters).2
                  (headD_mem_of_nonempty restLettersNonempty)
          have rightFinalMem : rightFinal ∈ rightSupport := by
            change
              componentFinal restLetters ∈
                connectedComponentSortedSupport restLetters
            exact
              (connectedComponentSortedSupport_mem_iff
                (componentFinal restLetters) restLetters).2
                  (componentFinal_mem_of_nonempty
                    restLettersNonempty)
          have normalizeFirst :
              SemigroupBasis.CoRoots.S5_107.ListDerives laws
                ((head :: tail) ++ restLetters)
                (leftBlock ++ restLetters) := by
            simpa [leftBlock, leftSupport, leftFinal] using
              SemigroupBasis.CoRoots.S5_107.ListDerives.append
                componentListDerivation restLetters
          have normalizeRest :
              SemigroupBasis.CoRoots.S5_107.ListDerives laws
                (leftBlock ++ restLetters)
                (leftBlock ++ rightBlock) := by
            simpa [rightBlock, rightSupport,
              rightHead, rightFinal] using
              SemigroupBasis.CoRoots.S5_107.ListDerives.prepend
                leftBlock restDerivation
          have mergeWord :=
            h9DerivesMergeLongBlocks
              leftSorted leftNodup headMem leftFinalMem
              rightSorted rightNodup
              rightHeadMem rightFinalMem
          have leftBlockNonempty : leftBlock ≠ [] := by
            simp [leftBlock, longBlock, blockX]
          have rightBlockNonempty : rightBlock ≠ [] := by
            simp [rightBlock, longBlock, blockX]
          have unionBlockNonempty :
              longBlock head rightFinal
                  (connectedComponentSortedSupport
                    (leftSupport ++ rightSupport)) ≠ [] := by
            simp [longBlock, blockX]
          have merge :
              SemigroupBasis.CoRoots.S5_107.ListDerives laws
                (leftBlock ++ rightBlock)
                (longBlock head rightFinal
                  (connectedComponentSortedSupport
                    (leftSupport ++ rightSupport))) := by
            have asLists :=
              SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
                mergeWord
            simpa only [Word.toList_append,
              maximalFactorWord_toList leftBlockNonempty,
              maximalFactorWord_toList rightBlockNonempty,
              maximalFactorWord_toList unionBlockNonempty]
              using asLists
          have unionSupportEq :
              connectedComponentSortedSupport
                  (leftSupport ++ rightSupport) =
                connectedComponentSortedSupport
                  ((head :: tail) ++ restLetters) := by
            apply sorted_nodup_ext
              (connectedComponentSortedSupport_sorted _)
              (connectedComponentSortedSupport_sorted _)
              (connectedComponentSortedSupport_nodup _)
              (connectedComponentSortedSupport_nodup _)
            intro tested
            change
              tested ∈
                  connectedComponentSortedSupport
                    (connectedComponentSortedSupport
                        (head :: tail) ++
                      connectedComponentSortedSupport
                        restLetters) ↔
                tested ∈
                  connectedComponentSortedSupport
                    ((head :: tail) ++ restLetters)
            simp only [
              connectedComponentSortedSupport_mem_iff,
              List.mem_append]
          have finalEq :
              componentFinal ((head :: tail) ++ restLetters) =
                rightFinal := by
            change
              componentFinal ((head :: tail) ++ restLetters) =
                componentFinal restLetters
            exact componentFinal_append_of_right_nonempty
              (head :: tail) restLetters restLettersNonempty
          have combined :=
            normalizeFirst.trans (normalizeRest.trans merge)
          change
            SemigroupBasis.CoRoots.S5_107.ListDerives laws
              ((head :: tail) ++ restLetters)
              (longBlock head
                (componentFinal
                  ((head :: tail) ++ restLetters))
                (connectedComponentSortedSupport
                  ((head :: tail) ++ restLetters)))
          rw [finalEq, ← unionSupportEq]
          exact combined

private abbrev H9CutSegment :=
  SemigroupBasis.CoRoots.S5_441.ExactCutSegment

/-- Every nonempty exact-cut gap derives to one square-normal component. -/
private theorem h9ListDerivesExactCutGapToLongBlock
    {letters : List Nat} {segment : H9CutSegment}
    (segmentMember :
      segment ∈
        SemigroupBasis.CoRoots.S5_441.exactCutDecomposition letters)
    (gapNonempty : segment.gap ≠ []) :
    SemigroupBasis.CoRoots.S5_107.ListDerives laws segment.gap
      (longBlock (segment.gap.headD 0)
        (componentFinal segment.gap)
        (connectedComponentSortedSupport segment.gap)) := by
  let components :=
    connectedComponentDecomposeList segment.gap
  have componentsNonempty : components ≠ [] := by
    simpa [components] using
      connectedComponentDecomposeList_nonempty gapNonempty
  rcases componentsShape : components with _ | ⟨first, rest⟩
  · exact False.elim (componentsNonempty componentsShape)
  have allNonempty :
      ∀ component ∈ first :: rest, component ≠ [] := by
    intro component member
    apply connectedComponentDecomposeList_nonempty_components
      segment.gap component
    change component ∈ components
    rw [componentsShape]
    exact member
  have allConnected :
      ∀ component ∈ first :: rest,
        ConnectedComponentSupportConnected component := by
    intro component member
    apply connectedComponentDecomposeList_supportConnected
      segment.gap component
    change component ∈ components
    rw [componentsShape]
    exact member
  have allLength :
      ∀ component ∈ first :: rest,
        2 ≤ component.length := by
    intro component member
    apply
      SemigroupBasis.CoRoots.S5_441.exactCutDecomposition_gap_component_length_ge_two
        segmentMember
    change component ∈ components
    rw [componentsShape]
    exact member
  have chain :=
    h9ListDerivesComponentChainToLongBlock
      (first :: rest) (by simp)
      allNonempty allConnected allLength
  have flattenEq : (first :: rest).flatten = segment.gap := by
    rw [← componentsShape]
    simpa [components] using
      connectedComponentDecomposeList_flatten segment.gap
  rw [flattenEq] at chain
  exact chain

/-- Retarget one normalized gap.  H9 supplies the final equality explicitly;
the unguarded initial switch removes the Hc06 head-boundary side condition. -/
private theorem h9ListDerivesRetargetLongBlockInContext
    {leftContext suffix support : List Nat}
    {sourceHead sourceFinal targetHead targetFinal : Nat}
    (sorted : support.Pairwise (· ≤ ·))
    (nodup : support.Nodup)
    (sourceHeadMem : sourceHead ∈ support)
    (sourceFinalMem : sourceFinal ∈ support)
    (targetHeadMem : targetHead ∈ support)
    (targetFinalMem : targetFinal ∈ support)
    (finalEq : sourceFinal = targetFinal) :
    SemigroupBasis.CoRoots.S5_107.ListDerives laws
      (leftContext ++
        longBlock sourceHead sourceFinal support ++ suffix)
      (leftContext ++
        longBlock targetHead targetFinal support ++ suffix) := by
  let sourceBlock :=
    longBlock sourceHead sourceFinal support
  let targetBlock :=
    longBlock targetHead targetFinal support
  have sourceNonempty : sourceBlock ≠ [] := by
    simp [sourceBlock, longBlock, blockX]
  have targetNonempty : targetBlock ≠ [] := by
    simp [targetBlock, longBlock, blockX]
  have sourceSupport :
      connectedComponentSortedSupport sourceBlock = support :=
    longBlock_sortedSupport sorted nodup
      sourceHeadMem sourceFinalMem
  have targetSupport :
      connectedComponentSortedSupport targetBlock = support :=
    longBlock_sortedSupport sorted nodup
      targetHeadMem targetFinalMem
  have baseSignature :
      connectedComponentSignatureOfList sourceBlock =
        connectedComponentSignatureOfList targetBlock :=
    baseSignature_eq_of_support_length_ge_two
      (longBlock_length_ge_two
        sourceHead sourceFinal support)
      (longBlock_length_ge_two
        targetHead targetFinal support)
      (sourceSupport.trans targetSupport.symm)
  have exactSignature :
      connectedCutComponentSignatureOfList sourceBlock =
        connectedCutComponentSignatureOfList targetBlock :=
    exactCutSignature_of_base_and_final baseSignature
      (by
        simpa only [sourceBlock, targetBlock, longBlock_final]
          using finalEq)
  have sourceConnected :
      ConnectedComponentSupportConnected sourceBlock :=
    longBlock_connected sourceHeadMem sourceFinalMem
  have targetConnected :
      ConnectedComponentSupportConnected targetBlock :=
    longBlock_connected targetHeadMem targetFinalMem
  have sourceShape :
      ∃ tail, sourceBlock = sourceHead :: tail := by
    refine
      ⟨support.erase sourceHead ++
        (blockX sourceHead support ++
          (blockY sourceFinal support ++
            (blockY sourceFinal support ++
              (blockX sourceHead support ++
                (blockX sourceHead support ++
                  (blockY sourceFinal support ++
                    blockY sourceFinal support)))))), ?_⟩
    simp [sourceBlock, longBlock, blockX, List.cons_append]
  have targetShape :
      ∃ tail, targetBlock = targetHead :: tail := by
    refine
      ⟨support.erase targetHead ++
        (blockX targetHead support ++
          (blockY targetFinal support ++
            (blockY targetFinal support ++
              (blockX targetHead support ++
                (blockX targetHead support ++
                  (blockY targetFinal support ++
                    blockY targetFinal support)))))), ?_⟩
    simp [targetBlock, longBlock, blockX, List.cons_append]
  obtain ⟨sourceTail, sourceShape⟩ := sourceShape
  obtain ⟨targetTail, targetShape⟩ := targetShape
  cases leftContext with
  | nil =>
      have wordDerivation :
          Derives laws
            (maximalFactorWord sourceBlock)
            (maximalFactorWord targetBlock) := by
        rw [sourceShape, targetShape]
        exact
          h9DerivesInitialComponentSwitch
            (sourceShape ▸ sourceConnected)
            (targetShape ▸ targetConnected)
            (by
              rw [← sourceShape, ← targetShape]
              exact exactSignature)
      have asLists :=
        SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
          wordDerivation
      have contextual :=
        SemigroupBasis.CoRoots.S5_107.ListDerives.context
          [] suffix asLists
      simpa only [List.nil_append,
        maximalFactorWord_toList sourceNonempty,
        maximalFactorWord_toList targetNonempty]
        using contextual
  | cons prefixHead prefixTail =>
      let prefixWord :=
        SemigroupBasis.CoRoots.S5_107.listWordOfCons
          prefixHead prefixTail
      have wordDerivation :
          Derives laws
            (prefixWord ++ maximalFactorWord sourceBlock)
            (prefixWord ++ maximalFactorWord targetBlock) := by
        rw [sourceShape, targetShape]
        exact
          h9DerivesComponentBehindGuard prefixWord
            (sourceShape ▸ sourceConnected)
            (targetShape ▸ targetConnected)
            (by
              rw [← sourceShape, ← targetShape]
              exact exactSignature)
      have asLists :=
        SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
          wordDerivation
      have suffixed :=
        SemigroupBasis.CoRoots.S5_107.ListDerives.append
          asLists suffix
      simpa [prefixWord,
        SemigroupBasis.CoRoots.S5_107.listWordOfCons,
        Word.toList_append,
        maximalFactorWord_toList sourceNonempty,
        maximalFactorWord_toList targetNonempty,
        List.append_assoc] using suffixed

/-! ## Exact-cut final transport -/

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

private theorem exactCutGap_final_eq_whole
    {letters : List Nat} {segment : H9CutSegment}
    (segmentMember :
      segment ∈
        SemigroupBasis.CoRoots.S5_441.exactCutDecomposition letters)
    (gapNonempty : segment.gap ≠ [])
    (separatorNone : segment.separator = none) :
    componentFinal segment.gap = componentFinal letters := by
  obtain ⟨before, after, decompositionEq⟩ :=
    List.mem_iff_append.mp segmentMember
  have afterEmpty : after = [] :=
    (SemigroupBasis.CoRoots.S5_441.exactCutDecomposition_separator_none_iff_after_nil
      decompositionEq).mp separatorNone
  have rendered :=
    SemigroupBasis.CoRoots.S5_441.render_exactCutDecomposition letters
  rw [decompositionEq, afterEmpty] at rendered
  have renderedFinal :
      SemigroupBasis.CoRoots.S5_441.renderExactCutSegments before ++
          segment.gap =
        letters := by
    simpa [
      SemigroupBasis.CoRoots.S5_441.renderExactCutSegments,
      SemigroupBasis.CoRoots.S5_441.ExactCutSegment.render,
      List.flatMap_append, separatorNone] using rendered
  rw [← renderedFinal]
  exact
    (componentFinal_append_of_right_nonempty
      (SemigroupBasis.CoRoots.S5_441.renderExactCutSegments before)
      segment.gap gapNonempty).symm

private theorem s5_806_componentFinal_eq (letters : List Nat) :
    SemigroupBasis.CoRoots.S5_806.componentFinal letters =
      componentFinal letters := by
  cases letters <;> rfl

/-- The semantic H9 descriptor gives equality of the literal final in every
pair of aligned nonempty gaps. -/
private theorem h9AlignedGapFinal_eq
    {left right : Word Nat}
    (same : SameH9CoalescedAllFinals left right)
    {leftSegment rightSegment : H9CutSegment}
    (leftMember :
      leftSegment ∈
        SemigroupBasis.CoRoots.S5_441.exactCutDecomposition
          left.toList)
    (rightMember :
      rightSegment ∈
        SemigroupBasis.CoRoots.S5_441.exactCutDecomposition
          right.toList)
    (separatorEq :
      leftSegment.separator = rightSegment.separator)
    (leftGapNonempty : leftSegment.gap ≠ [])
    (rightGapNonempty : rightSegment.gap ≠ []) :
    componentFinal leftSegment.gap =
      componentFinal rightSegment.gap := by
  cases leftSeparator : leftSegment.separator with
  | none =>
      have rightSeparator : rightSegment.separator = none := by
        rw [← separatorEq]
        exact leftSeparator
      have leftFinal :=
        exactCutGap_final_eq_whole
          leftMember leftGapNonempty leftSeparator
      have rightFinal :=
        exactCutGap_final_eq_whole
          rightMember rightGapNonempty rightSeparator
      have wholeFinal :
          componentFinal left.toList =
            componentFinal right.toList := by
        simpa only [s5_806_componentFinal_eq] using same.final
      exact leftFinal.trans (wholeFinal.trans rightFinal.symm)
  | some separator =>
      have rightSeparator :
          rightSegment.separator = some separator := by
        rw [← separatorEq]
        exact leftSeparator
      obtain
        ⟨leftBeforeSegments, leftAfterSegments,
          leftDecomposition⟩ :=
        List.mem_iff_append.mp leftMember
      obtain
        ⟨rightBeforeSegments, rightAfterSegments,
          rightDecomposition⟩ :=
        List.mem_iff_append.mp rightMember
      let leftBefore :=
        SemigroupBasis.CoRoots.S5_441.renderExactCutSegments
            leftBeforeSegments ++
          leftSegment.gap
      let leftAfter :=
        SemigroupBasis.CoRoots.S5_441.renderExactCutSegments
          leftAfterSegments
      let rightBefore :=
        SemigroupBasis.CoRoots.S5_441.renderExactCutSegments
            rightBeforeSegments ++
          rightSegment.gap
      let rightAfter :=
        SemigroupBasis.CoRoots.S5_441.renderExactCutSegments
          rightAfterSegments
      have leftCut :
          UniqueSeparatorFourExactCut
            left.toList leftBefore separator leftAfter :=
        SemigroupBasis.CoRoots.S5_441.exactCutDecomposition_separator_exactCut
          leftDecomposition leftSeparator
      have rightCut :
          UniqueSeparatorFourExactCut
            right.toList rightBefore separator rightAfter :=
        SemigroupBasis.CoRoots.S5_441.exactCutDecomposition_separator_exactCut
          rightDecomposition rightSeparator
      obtain
        ⟨transportedBefore, transportedAfter, transportedCut,
          transportedBeforeSupport, transportedAfterSupport⟩ :=
        SemigroupBasis.CoRoots.S5_441Invariant.SameExactCutSignature.transport
          same.exactCuts leftCut
      have transportedSides :=
        exactCut_sides_unique transportedCut rightCut
      have beforeSupport :
          ∀ tested, tested ∈ leftBefore ↔ tested ∈ rightBefore := by
        intro tested
        rw [← transportedSides.1]
        exact (transportedBeforeSupport tested).symm
      have afterSupport :
          ∀ tested, tested ∈ leftAfter ↔ tested ∈ rightAfter := by
        intro tested
        rw [← transportedSides.2]
        exact (transportedAfterSupport tested).symm
      have leftBeforeNonempty : leftBefore ≠ [] := by
        intro beforeEmpty
        change
          SemigroupBasis.CoRoots.S5_441.renderExactCutSegments
              leftBeforeSegments ++ leftSegment.gap = []
          at beforeEmpty
        exact leftGapNonempty
          (List.append_eq_nil_iff.mp beforeEmpty).2
      have rightBeforeNonempty : rightBefore ≠ [] := by
        intro beforeEmpty
        change
          SemigroupBasis.CoRoots.S5_441.renderExactCutSegments
              rightBeforeSegments ++ rightSegment.gap = []
          at beforeEmpty
        exact rightGapNonempty
          (List.append_eq_nil_iff.mp beforeEmpty).2
      have prefixFinals :
          componentFinal leftBefore =
            componentFinal rightBefore :=
        same.predecessorFinals leftCut rightCut
          beforeSupport afterSupport
          leftBeforeNonempty rightBeforeNonempty
      calc
        componentFinal leftSegment.gap =
            componentFinal leftBefore := by
          change
            componentFinal leftSegment.gap =
              componentFinal
                (SemigroupBasis.CoRoots.S5_441.renderExactCutSegments
                    leftBeforeSegments ++ leftSegment.gap)
          exact
            (componentFinal_append_of_right_nonempty
              (SemigroupBasis.CoRoots.S5_441.renderExactCutSegments
                leftBeforeSegments)
              leftSegment.gap leftGapNonempty).symm
        _ = componentFinal rightBefore := prefixFinals
        _ = componentFinal rightSegment.gap := by
          change
            componentFinal
                (SemigroupBasis.CoRoots.S5_441.renderExactCutSegments
                    rightBeforeSegments ++ rightSegment.gap) =
              componentFinal rightSegment.gap
          exact
            componentFinal_append_of_right_nonempty
              (SemigroupBasis.CoRoots.S5_441.renderExactCutSegments
                rightBeforeSegments)
              rightSegment.gap rightGapNonempty

/-! ## Retained support-skeleton segments -/

private def h9RetainCutSegment
    (segment : H9CutSegment) : Bool :=
  decide (¬ (segment.gap = [] ∧ segment.separator = none))

private def h9RetainedCutSegments
    (segments : List H9CutSegment) : List H9CutSegment :=
  segments.filter h9RetainCutSegment

private theorem render_h9RetainedCutSegments
    (segments : List H9CutSegment) :
    SemigroupBasis.CoRoots.S5_441.renderExactCutSegments
        (h9RetainedCutSegments segments) =
      SemigroupBasis.CoRoots.S5_441.renderExactCutSegments
        segments := by
  induction segments with
  | nil => rfl
  | cons segment remaining induction =>
      unfold h9RetainedCutSegments at induction
      by_cases omitted :
          segment.gap = [] ∧ segment.separator = none
      · simp [h9RetainedCutSegments, h9RetainCutSegment,
          SemigroupBasis.CoRoots.S5_441.ExactCutSegment.render,
          omitted, induction]
      · simp [h9RetainedCutSegments, h9RetainCutSegment,
          SemigroupBasis.CoRoots.S5_441.ExactCutSegment.render,
          omitted, induction]

private theorem h9SupportSegments_eq_map_retained
    (segments : List H9CutSegment) :
    SemigroupBasis.CoRoots.S5_441.exactCutSupportSegments
        segments =
      (h9RetainedCutSegments segments).map
        SemigroupBasis.CoRoots.S5_441.exactCutSupportSegment := by
  induction segments with
  | nil => rfl
  | cons segment remaining induction =>
      unfold h9RetainedCutSegments at induction
      unfold
        SemigroupBasis.CoRoots.S5_441.exactCutSupportSegments
        at induction
      by_cases omitted :
          segment.gap = [] ∧ segment.separator = none
      · simp [h9RetainedCutSegments, h9RetainCutSegment,
          SemigroupBasis.CoRoots.S5_441.exactCutSupportSegments,
          SemigroupBasis.CoRoots.S5_441.exactCutSupportSegment?,
          omitted, induction]
      · simp [h9RetainedCutSegments, h9RetainCutSegment,
          SemigroupBasis.CoRoots.S5_441.exactCutSupportSegments,
          SemigroupBasis.CoRoots.S5_441.exactCutSupportSegment?,
          omitted, induction]

private theorem h9RetainedCutSegments_member
    {segment : H9CutSegment} {segments : List H9CutSegment}
    (member : segment ∈ h9RetainedCutSegments segments) :
    segment ∈ segments :=
  (List.mem_filter.mp member).1

private theorem h9RetainedCutSegments_retained
    {segment : H9CutSegment} {segments : List H9CutSegment}
    (member : segment ∈ h9RetainedCutSegments segments) :
    ¬ (segment.gap = [] ∧ segment.separator = none) :=
  of_decide_eq_true (List.mem_filter.mp member).2

private theorem h9CutSegment_render_nonempty_of_retained
    {segment : H9CutSegment}
    (retained :
      ¬ (segment.gap = [] ∧ segment.separator = none)) :
    segment.render ≠ [] := by
  intro renderEmpty
  change segment.gap ++ segment.separator.toList = [] at renderEmpty
  have emptyParts := List.append_eq_nil_iff.mp renderEmpty
  have gapEmpty : segment.gap = [] := emptyParts.1
  have separatorEmpty : segment.separator.toList = [] := emptyParts.2
  have separatorNone : segment.separator = none := by
    cases separatorShape : segment.separator with
    | none => rfl
    | some separator =>
        simp [separatorShape] at separatorEmpty
  exact retained ⟨gapEmpty, separatorNone⟩

/-! ## Segment assembly -/

/-- Align retained H9 segments from left to right.  Each nonempty gap is
normalized, retargeted with its transported final, and denormalized. -/
private theorem assembleH9RetainedSegments
    (left right : Word Nat)
    (same : SameH9CoalescedAllFinals left right) :
    ∀ (leftSegments rightSegments : List H9CutSegment)
      (leftContext : List Nat),
      (∀ segment, segment ∈ leftSegments →
        segment ∈
          SemigroupBasis.CoRoots.S5_441.exactCutDecomposition
            left.toList) →
      (∀ segment, segment ∈ rightSegments →
        segment ∈
          SemigroupBasis.CoRoots.S5_441.exactCutDecomposition
            right.toList) →
      (∀ segment, segment ∈ leftSegments →
        ¬ (segment.gap = [] ∧ segment.separator = none)) →
      (∀ segment, segment ∈ rightSegments →
        ¬ (segment.gap = [] ∧ segment.separator = none)) →
      leftSegments.map
          SemigroupBasis.CoRoots.S5_441.exactCutSupportSegment =
        rightSegments.map
          SemigroupBasis.CoRoots.S5_441.exactCutSupportSegment →
      SemigroupBasis.CoRoots.S5_107.ListDerives laws
        (leftContext ++
          SemigroupBasis.CoRoots.S5_441.renderExactCutSegments
            leftSegments)
        (leftContext ++
          SemigroupBasis.CoRoots.S5_441.renderExactCutSegments
            rightSegments)
  | [], [], leftContext, _, _, _, _, _ => by
      simpa using
        (SemigroupBasis.CoRoots.S5_107.ListDerives.refl
          (basis := laws) leftContext)
  | [], _ :: _, _, _, _, _, _, supportEq => by
      simp at supportEq
  | _ :: _, [], _, _, _, _, _, supportEq => by
      simp at supportEq
  | leftSegment :: leftRemaining,
      rightSegment :: rightRemaining,
      leftContext, leftMembers, rightMembers,
      leftRetained, rightRetained,
      supportSegmentsEq => by
      simp only [List.map_cons, List.cons.injEq]
        at supportSegmentsEq
      have supportSegmentEq := supportSegmentsEq.1
      have tailSupportSegmentsEq := supportSegmentsEq.2
      have leftSegmentMember :=
        leftMembers leftSegment (by simp)
      have rightSegmentMember :=
        rightMembers rightSegment (by simp)
      have leftSegmentRetained :=
        leftRetained leftSegment (by simp)
      have rightSegmentRetained :=
        rightRetained rightSegment (by simp)
      have supportEq :
          connectedComponentSortedSupport leftSegment.gap =
            connectedComponentSortedSupport rightSegment.gap :=
        congrArg
          UniqueSeparatorCanonicalSegment.quadratic
          supportSegmentEq
      have separatorEq :
          leftSegment.separator = rightSegment.separator :=
        congrArg
          UniqueSeparatorCanonicalSegment.separator
          supportSegmentEq
      by_cases leftGapEmpty : leftSegment.gap = []
      · have rightGapEmpty : rightSegment.gap = [] := by
          apply List.eq_nil_iff_forall_not_mem.mpr
          intro tested rightGapMember
          have rightSupportMember :
              tested ∈
                connectedComponentSortedSupport
                  rightSegment.gap :=
            (connectedComponentSortedSupport_mem_iff
              tested rightSegment.gap).2 rightGapMember
          rw [← supportEq] at rightSupportMember
          have leftGapMember : tested ∈ leftSegment.gap :=
            (connectedComponentSortedSupport_mem_iff
              tested leftSegment.gap).1 rightSupportMember
          simpa [leftGapEmpty] using leftGapMember
        have segmentRenderEq :
            leftSegment.render = rightSegment.render := by
          simp [
            SemigroupBasis.CoRoots.S5_441.ExactCutSegment.render,
            leftGapEmpty, rightGapEmpty, separatorEq]
        have tailDerivation :=
          assembleH9RetainedSegments left right same
            leftRemaining rightRemaining
            (leftContext ++ rightSegment.render)
            (fun segment member =>
              leftMembers segment
                (List.Mem.tail leftSegment member))
            (fun segment member =>
              rightMembers segment
                (List.Mem.tail rightSegment member))
            (fun segment member =>
              leftRetained segment
                (List.Mem.tail leftSegment member))
            (fun segment member =>
              rightRetained segment
                (List.Mem.tail rightSegment member))
            tailSupportSegmentsEq
        simpa [
          SemigroupBasis.CoRoots.S5_441.renderExactCutSegments_cons,
          segmentRenderEq, List.append_assoc] using tailDerivation
      · have rightGapNonempty : rightSegment.gap ≠ [] := by
          intro rightGapEmpty
          obtain ⟨tested, testedMember⟩ :=
            List.exists_mem_of_ne_nil
              leftSegment.gap leftGapEmpty
          have leftSupportMember :
              tested ∈
                connectedComponentSortedSupport
                  leftSegment.gap :=
            (connectedComponentSortedSupport_mem_iff
              tested leftSegment.gap).2 testedMember
          rw [supportEq] at leftSupportMember
          have rightGapMember : tested ∈ rightSegment.gap :=
            (connectedComponentSortedSupport_mem_iff
              tested rightSegment.gap).1 leftSupportMember
          exact
            (List.ne_nil_of_mem rightGapMember) rightGapEmpty
        have supportSorted :
            (connectedComponentSortedSupport
              leftSegment.gap).Pairwise (· ≤ ·) :=
          connectedComponentSortedSupport_sorted _
        have supportNodup :
            (connectedComponentSortedSupport
              leftSegment.gap).Nodup :=
          connectedComponentSortedSupport_nodup _
        have leftHeadMem :
            leftSegment.gap.headD 0 ∈
              connectedComponentSortedSupport leftSegment.gap := by
          rw [connectedComponentSortedSupport_mem_iff]
          exact headD_mem_of_nonempty leftGapEmpty
        have leftFinalMem :
            componentFinal leftSegment.gap ∈
              connectedComponentSortedSupport leftSegment.gap := by
          rw [connectedComponentSortedSupport_mem_iff]
          exact componentFinal_mem_of_nonempty leftGapEmpty
        have rightHeadMem :
            rightSegment.gap.headD 0 ∈
              connectedComponentSortedSupport leftSegment.gap := by
          rw [supportEq,
            connectedComponentSortedSupport_mem_iff]
          exact headD_mem_of_nonempty rightGapNonempty
        have rightFinalMem :
            componentFinal rightSegment.gap ∈
              connectedComponentSortedSupport leftSegment.gap := by
          rw [supportEq,
            connectedComponentSortedSupport_mem_iff]
          exact componentFinal_mem_of_nonempty rightGapNonempty
        have gapFinalEq :
            componentFinal leftSegment.gap =
              componentFinal rightSegment.gap :=
          h9AlignedGapFinal_eq same
            leftSegmentMember rightSegmentMember separatorEq
            leftGapEmpty rightGapNonempty
        have leftGapNormalization :=
          h9ListDerivesExactCutGapToLongBlock
            leftSegmentMember leftGapEmpty
        have rightGapNormalization :=
          h9ListDerivesExactCutGapToLongBlock
            rightSegmentMember rightGapNonempty
        have rightGapNormalizationCommon :
            SemigroupBasis.CoRoots.S5_107.ListDerives laws
              rightSegment.gap
              (longBlock
                (rightSegment.gap.headD 0)
                (componentFinal rightSegment.gap)
                (connectedComponentSortedSupport
                  leftSegment.gap)) := by
          simpa only [supportEq] using rightGapNormalization
        let suffix :=
          leftSegment.separator.toList ++
            SemigroupBasis.CoRoots.S5_441.renderExactCutSegments
              leftRemaining
        have normalizeLeft :
            SemigroupBasis.CoRoots.S5_107.ListDerives laws
              (leftContext ++ leftSegment.gap ++ suffix)
              (leftContext ++
                longBlock
                  (leftSegment.gap.headD 0)
                  (componentFinal leftSegment.gap)
                  (connectedComponentSortedSupport
                    leftSegment.gap) ++ suffix) :=
          SemigroupBasis.CoRoots.S5_107.ListDerives.context
            leftContext suffix leftGapNormalization
        have retarget :
            SemigroupBasis.CoRoots.S5_107.ListDerives laws
              (leftContext ++
                longBlock
                  (leftSegment.gap.headD 0)
                  (componentFinal leftSegment.gap)
                  (connectedComponentSortedSupport
                    leftSegment.gap) ++ suffix)
              (leftContext ++
                longBlock
                  (rightSegment.gap.headD 0)
                  (componentFinal rightSegment.gap)
                  (connectedComponentSortedSupport
                    leftSegment.gap) ++ suffix) :=
          h9ListDerivesRetargetLongBlockInContext
            supportSorted supportNodup
            leftHeadMem leftFinalMem
            rightHeadMem rightFinalMem gapFinalEq
        have denormalizeRight :
            SemigroupBasis.CoRoots.S5_107.ListDerives laws
              (leftContext ++
                longBlock
                  (rightSegment.gap.headD 0)
                  (componentFinal rightSegment.gap)
                  (connectedComponentSortedSupport
                    leftSegment.gap) ++ suffix)
              (leftContext ++ rightSegment.gap ++ suffix) :=
          SemigroupBasis.CoRoots.S5_107.ListDerives.context
            leftContext suffix rightGapNormalizationCommon.symm
        have currentSegmentStep :
            SemigroupBasis.CoRoots.S5_107.ListDerives laws
              (leftContext ++
                leftSegment.render ++
                SemigroupBasis.CoRoots.S5_441.renderExactCutSegments
                  leftRemaining)
              (leftContext ++
                rightSegment.render ++
                SemigroupBasis.CoRoots.S5_441.renderExactCutSegments
                  leftRemaining) := by
          have combined :=
            normalizeLeft.trans (retarget.trans denormalizeRight)
          simpa [suffix,
            SemigroupBasis.CoRoots.S5_441.ExactCutSegment.render,
            separatorEq, List.append_assoc] using combined
        have tailDerivation :=
          assembleH9RetainedSegments left right same
            leftRemaining rightRemaining
            (leftContext ++ rightSegment.render)
            (fun segment member =>
              leftMembers segment
                (List.Mem.tail leftSegment member))
            (fun segment member =>
              rightMembers segment
                (List.Mem.tail rightSegment member))
            (fun segment member =>
              leftRetained segment
                (List.Mem.tail leftSegment member))
            (fun segment member =>
              rightRetained segment
                (List.Mem.tail rightSegment member))
            tailSupportSegmentsEq
        have combined :=
          currentSegmentStep.trans tailDerivation
        simpa [
          SemigroupBasis.CoRoots.S5_441.renderExactCutSegments_cons,
          List.append_assoc] using combined
termination_by leftSegments rightSegments =>
  leftSegments.length + rightSegments.length

/-- List-level completeness of the H9 descriptor. -/
theorem listDerivesOfSameH9CoalescedAllFinals
    {left right : Word Nat}
    (same : SameH9CoalescedAllFinals left right) :
    SemigroupBasis.CoRoots.S5_107.ListDerives
      laws left.toList right.toList := by
  let leftSegments :=
    SemigroupBasis.CoRoots.S5_441.exactCutDecomposition left.toList
  let rightSegments :=
    SemigroupBasis.CoRoots.S5_441.exactCutDecomposition right.toList
  let leftRetained := h9RetainedCutSegments leftSegments
  let rightRetained := h9RetainedCutSegments rightSegments
  have supportSkeletonEq :
      SemigroupBasis.CoRoots.S5_441.exactCutSupportSkeleton
          left.toList =
        SemigroupBasis.CoRoots.S5_441.exactCutSupportSkeleton
          right.toList :=
    SemigroupBasis.CoRoots.S5_441.exactCutSupportSkeleton_eq_of_sameSupport_sameExactCutSignature
      same.support same.exactCuts
  have supportSegmentsEq :
      SemigroupBasis.CoRoots.S5_441.exactCutSupportSegments
          leftSegments =
        SemigroupBasis.CoRoots.S5_441.exactCutSupportSegments
          rightSegments := by
    simpa [leftSegments, rightSegments,
      SemigroupBasis.CoRoots.S5_441.exactCutSupportSkeleton]
      using supportSkeletonEq
  have retainedSupportEq :
      leftRetained.map
          SemigroupBasis.CoRoots.S5_441.exactCutSupportSegment =
        rightRetained.map
          SemigroupBasis.CoRoots.S5_441.exactCutSupportSegment := by
    rw [← h9SupportSegments_eq_map_retained,
      ← h9SupportSegments_eq_map_retained]
    exact supportSegmentsEq
  have leftMembers :
      ∀ segment, segment ∈ leftRetained →
        segment ∈
          SemigroupBasis.CoRoots.S5_441.exactCutDecomposition
            left.toList := by
    intro segment member
    exact h9RetainedCutSegments_member member
  have rightMembers :
      ∀ segment, segment ∈ rightRetained →
        segment ∈
          SemigroupBasis.CoRoots.S5_441.exactCutDecomposition
            right.toList := by
    intro segment member
    exact h9RetainedCutSegments_member member
  have leftRetainedProof :
      ∀ segment, segment ∈ leftRetained →
        ¬ (segment.gap = [] ∧ segment.separator = none) := by
    intro segment member
    exact h9RetainedCutSegments_retained member
  have rightRetainedProof :
      ∀ segment, segment ∈ rightRetained →
        ¬ (segment.gap = [] ∧ segment.separator = none) := by
    intro segment member
    exact h9RetainedCutSegments_retained member
  have leftRenderEq :
      SemigroupBasis.CoRoots.S5_441.renderExactCutSegments
          leftRetained = left.toList := by
    calc
      SemigroupBasis.CoRoots.S5_441.renderExactCutSegments
          leftRetained =
          SemigroupBasis.CoRoots.S5_441.renderExactCutSegments
            leftSegments :=
        render_h9RetainedCutSegments leftSegments
      _ = left.toList := by
        simpa [leftSegments] using
          SemigroupBasis.CoRoots.S5_441.render_exactCutDecomposition
            left.toList
  have rightRenderEq :
      SemigroupBasis.CoRoots.S5_441.renderExactCutSegments
          rightRetained = right.toList := by
    calc
      SemigroupBasis.CoRoots.S5_441.renderExactCutSegments
          rightRetained =
          SemigroupBasis.CoRoots.S5_441.renderExactCutSegments
            rightSegments :=
        render_h9RetainedCutSegments rightSegments
      _ = right.toList := by
        simpa [rightSegments] using
          SemigroupBasis.CoRoots.S5_441.render_exactCutDecomposition
            right.toList
  have derivation :=
    assembleH9RetainedSegments left right same
      leftRetained rightRetained []
      leftMembers rightMembers
      leftRetainedProof rightRetainedProof
      retainedSupportEq
  simpa [leftRenderEq, rightRenderEq] using derivation

/-- Word-level H9 descriptor completeness. -/
theorem derivesOfSameH9CoalescedAllFinals
    {left right : Word Nat}
    (same : SameH9CoalescedAllFinals left right) :
    Derives laws left right := by
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail =>
          simpa [
            SemigroupBasis.CoRoots.S5_107.listWordOfCons,
            Word.toList] using
            SemigroupBasis.CoRoots.S5_107.ListDerives.toWord
              (listDerivesOfSameH9CoalescedAllFinals same)

/-- The isolated obligation from `SingletonNormal` is discharged by the
retained exact-cut induction above. -/
theorem derivationalCompleteness : DerivationalCompleteness :=
  fun same => derivesOfSameH9CoalescedAllFinals same

/-- The representative endpoint now follows from the semantic extractor
already frozen in `SingletonNormal`. -/
theorem representative_basis : BasisFor table.semigroup laws :=
  representative_basis_of_derivationalCompleteness
    derivationalCompleteness

/-- The paired opposite endpoint follows without a second normalizer. -/
theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis laws) :=
  opposite_basis_of_derivationalCompleteness
    derivationalCompleteness

end SemigroupBasis.CoRoots.Order6LeeA2LatticeNodesSingletonNormal.S6_7976
