import SemigroupBasis.CoRoots.Order6L2DD029ModThreeComponentB16Interior
import SemigroupBasis.CoRoots.Order6L2DD029ModThreeComponentB16AnchorSwitch
import SemigroupBasis.CoRoots.Order6L2DD029ModThreeComponentB16Signature

/-!
# Retargeting reduced literal-B16 envelopes

After fixed-endpoint reduction, the old endpoint occurs internally zero,
one, or two times and every supported different endpoint occurs one, two,
or three times.  These nine cases are arranged to the nine independently
audited literal-B16 anchor-switch leaves.  No derivation theorem for a
different basis is used.
-/

namespace SemigroupBasis.CoRoots.Order6L2DD029ModThreeComponentB16

open SemigroupBasis
open SemigroupBasis.Examples

private theorem reducedProfile_perm_of_listDerives
    {oldEndpoint newEndpoint : Nat}
    {sourceInterior targetInterior : List Nat}
    (derivation :
      B16ListDerives
        (modThreeEnvelopeRender oldEndpoint sourceInterior [])
        (modThreeEnvelopeRender newEndpoint targetInterior [])) :
    (positiveModThreeReduce
        (modThreeEnvelopeRender oldEndpoint sourceInterior [])).Perm
      (positiveModThreeReduce
        (modThreeEnvelopeRender newEndpoint targetInterior [])) := by
  have same :=
    derives_sameModThreeComponentSignature
      (S5_107.ListDerives.toWord derivation)
  apply positiveModThreeReduce_perm
  · intro tested
    simpa [S5_107.listWordOfCons, Word.toList,
      modThreeEnvelopeRender, S5_441.parityEnvelopeRender] using
      sameSupport_of_sameComponentSignature same.components tested
  · intro tested
    simpa [S5_107.listWordOfCons, Word.toList,
      modThreeEnvelopeRender, S5_441.parityEnvelopeRender] using
      same.modThree tested

private theorem finishRetarget
    {oldEndpoint newEndpoint : Nat}
    {interior sourceInterior targetInterior : List Nat}
    (arrange : interior.Perm sourceInterior)
    (switch :
      B16ListDerives
        (modThreeEnvelopeRender oldEndpoint sourceInterior [])
        (modThreeEnvelopeRender newEndpoint targetInterior []))
    (targetReduced :
      ModThreeEnvelopeInteriorReduced newEndpoint targetInterior) :
    ∃ finalInterior,
      B16ListDerives
          (modThreeEnvelopeRender oldEndpoint interior [])
          (modThreeEnvelopeRender newEndpoint finalInterior []) ∧
        (positiveModThreeReduce
            (modThreeEnvelopeRender oldEndpoint interior [])).Perm
          (positiveModThreeReduce
            (modThreeEnvelopeRender newEndpoint finalInterior [])) ∧
        ModThreeEnvelopeInteriorReduced newEndpoint finalInterior := by
  have arrangeDerivation :=
    listDerivesEnvelopeInteriorPermutation oldEndpoint [] arrange
  have derivation :=
    B16ListDerives.trans arrangeDerivation switch
  exact
    ⟨targetInterior, derivation,
      reducedProfile_perm_of_listDerives derivation,
      targetReduced⟩

private theorem existsRetarget01
    {oldEndpoint newEndpoint : Nat} {interior : List Nat}
    (different : oldEndpoint ≠ newEndpoint)
    (oldCount : interior.count oldEndpoint = 0)
    (newCount : interior.count newEndpoint = 1)
    (newMember : newEndpoint ∈ interior)
    (reduced :
      ModThreeEnvelopeInteriorReduced oldEndpoint interior) :
    ∃ targetInterior,
      B16ListDerives
          (modThreeEnvelopeRender oldEndpoint interior [])
          (modThreeEnvelopeRender newEndpoint targetInterior []) ∧
        (positiveModThreeReduce
            (modThreeEnvelopeRender oldEndpoint interior [])).Perm
          (positiveModThreeReduce
            (modThreeEnvelopeRender newEndpoint targetInterior [])) ∧
        ModThreeEnvelopeInteriorReduced newEndpoint targetInterior := by
  let trailing := interior.erase newEndpoint
  have arrange : interior.Perm (newEndpoint :: trailing) := by
    simpa [trailing] using List.perm_cons_erase newMember
  let targetInterior :=
    newEndpoint :: newEndpoint :: oldEndpoint :: oldEndpoint :: trailing
  have switch :
      B16ListDerives
        (modThreeEnvelopeRender oldEndpoint
          (newEndpoint :: trailing) [])
        (modThreeEnvelopeRender newEndpoint targetInterior []) := by
    simpa [targetInterior, modThreeEnvelopeRender,
      S5_441.parityEnvelopeRender, List.append_assoc] using
      listDerivesAnchorSwitch01 oldEndpoint newEndpoint trailing
  apply finishRetarget arrange switch
  refine
    { endpoint_count_le_two := ?_
      other_count_le_three := ?_ }
  · have counts := (List.perm_iff_count.mp arrange) newEndpoint
    simp [targetInterior, newCount, different, Ne.symm different]
      at counts ⊢
    omega
  · intro tested testedNeNew
    by_cases testedEqOld : tested = oldEndpoint
    · subst tested
      have counts := (List.perm_iff_count.mp arrange) oldEndpoint
      simp [targetInterior, oldCount, different, Ne.symm different]
        at counts ⊢
      omega
    · have sourceBound :=
        reduced.other_count_le_three tested testedEqOld
      have counts := (List.perm_iff_count.mp arrange) tested
      simp [targetInterior, testedEqOld, testedNeNew,
        Ne.symm testedEqOld, Ne.symm testedNeNew] at counts ⊢
      omega

private theorem existsRetarget02
    {oldEndpoint newEndpoint : Nat} {interior : List Nat}
    (different : oldEndpoint ≠ newEndpoint)
    (oldCount : interior.count oldEndpoint = 0)
    (newCount : interior.count newEndpoint = 2)
    (newMember : newEndpoint ∈ interior)
    (reduced :
      ModThreeEnvelopeInteriorReduced oldEndpoint interior) :
    ∃ targetInterior,
      B16ListDerives
          (modThreeEnvelopeRender oldEndpoint interior [])
          (modThreeEnvelopeRender newEndpoint targetInterior []) ∧
        (positiveModThreeReduce
            (modThreeEnvelopeRender oldEndpoint interior [])).Perm
          (positiveModThreeReduce
            (modThreeEnvelopeRender newEndpoint targetInterior [])) ∧
        ModThreeEnvelopeInteriorReduced newEndpoint targetInterior := by
  have afterOneCount :
      (interior.erase newEndpoint).count newEndpoint = 1 := by
    rw [List.count_erase_self, newCount]
  have afterOneMember : newEndpoint ∈ interior.erase newEndpoint :=
    List.count_pos_iff.mp (by omega)
  let trailing := (interior.erase newEndpoint).erase newEndpoint
  have arrange :
      interior.Perm (newEndpoint :: newEndpoint :: trailing) :=
    (List.perm_cons_erase newMember).trans <|
      List.Perm.cons newEndpoint <| by
        simpa [trailing] using
          List.perm_cons_erase afterOneMember
  let targetInterior := oldEndpoint :: oldEndpoint :: trailing
  have switch :
      B16ListDerives
        (modThreeEnvelopeRender oldEndpoint
          (newEndpoint :: newEndpoint :: trailing) [])
        (modThreeEnvelopeRender newEndpoint targetInterior []) := by
    simpa [targetInterior, modThreeEnvelopeRender,
      S5_441.parityEnvelopeRender, List.append_assoc] using
      listDerivesAnchorSwitch02 oldEndpoint newEndpoint trailing
  apply finishRetarget arrange switch
  refine
    { endpoint_count_le_two := ?_
      other_count_le_three := ?_ }
  · have counts := (List.perm_iff_count.mp arrange) newEndpoint
    simp [targetInterior, newCount, different, Ne.symm different]
      at counts ⊢
    omega
  · intro tested testedNeNew
    by_cases testedEqOld : tested = oldEndpoint
    · subst tested
      have counts := (List.perm_iff_count.mp arrange) oldEndpoint
      simp [targetInterior, oldCount, different, Ne.symm different]
        at counts ⊢
      omega
    · have sourceBound :=
        reduced.other_count_le_three tested testedEqOld
      have counts := (List.perm_iff_count.mp arrange) tested
      simp [targetInterior, testedEqOld, testedNeNew,
        Ne.symm testedEqOld, Ne.symm testedNeNew] at counts ⊢
      omega

private theorem existsRetarget03
    {oldEndpoint newEndpoint : Nat} {interior : List Nat}
    (different : oldEndpoint ≠ newEndpoint)
    (oldCount : interior.count oldEndpoint = 0)
    (newCount : interior.count newEndpoint = 3)
    (newMember : newEndpoint ∈ interior)
    (reduced :
      ModThreeEnvelopeInteriorReduced oldEndpoint interior) :
    ∃ targetInterior,
      B16ListDerives
          (modThreeEnvelopeRender oldEndpoint interior [])
          (modThreeEnvelopeRender newEndpoint targetInterior []) ∧
        (positiveModThreeReduce
            (modThreeEnvelopeRender oldEndpoint interior [])).Perm
          (positiveModThreeReduce
            (modThreeEnvelopeRender newEndpoint targetInterior [])) ∧
        ModThreeEnvelopeInteriorReduced newEndpoint targetInterior := by
  have afterOneCount :
      (interior.erase newEndpoint).count newEndpoint = 2 := by
    rw [List.count_erase_self, newCount]
  have afterOneMember : newEndpoint ∈ interior.erase newEndpoint :=
    List.count_pos_iff.mp (by omega)
  have afterTwoCount :
      ((interior.erase newEndpoint).erase newEndpoint).count
          newEndpoint = 1 := by
    rw [List.count_erase_self, afterOneCount]
  have afterTwoMember :
      newEndpoint ∈ (interior.erase newEndpoint).erase newEndpoint :=
    List.count_pos_iff.mp (by omega)
  let trailing :=
    ((interior.erase newEndpoint).erase newEndpoint).erase newEndpoint
  have arrange :
      interior.Perm
        (newEndpoint :: newEndpoint :: newEndpoint :: trailing) :=
    (List.perm_cons_erase newMember).trans <|
      List.Perm.cons newEndpoint <|
        (List.perm_cons_erase afterOneMember).trans <|
          List.Perm.cons newEndpoint <| by
            simpa [trailing] using
              List.perm_cons_erase afterTwoMember
  let targetInterior :=
    oldEndpoint :: oldEndpoint :: newEndpoint :: trailing
  have switch :
      B16ListDerives
        (modThreeEnvelopeRender oldEndpoint
          (newEndpoint :: newEndpoint :: newEndpoint :: trailing) [])
        (modThreeEnvelopeRender newEndpoint targetInterior []) := by
    simpa [targetInterior, modThreeEnvelopeRender,
      S5_441.parityEnvelopeRender, List.append_assoc] using
      listDerivesAnchorSwitch03 oldEndpoint newEndpoint trailing
  apply finishRetarget arrange switch
  refine
    { endpoint_count_le_two := ?_
      other_count_le_three := ?_ }
  · have counts := (List.perm_iff_count.mp arrange) newEndpoint
    simp [targetInterior, newCount, different, Ne.symm different]
      at counts ⊢
    omega
  · intro tested testedNeNew
    by_cases testedEqOld : tested = oldEndpoint
    · subst tested
      have counts := (List.perm_iff_count.mp arrange) oldEndpoint
      simp [targetInterior, oldCount, different, Ne.symm different]
        at counts ⊢
      omega
    · have sourceBound :=
        reduced.other_count_le_three tested testedEqOld
      have counts := (List.perm_iff_count.mp arrange) tested
      simp [targetInterior, testedEqOld, testedNeNew,
        Ne.symm testedEqOld, Ne.symm testedNeNew] at counts ⊢
      omega

private theorem existsRetarget11
    {oldEndpoint newEndpoint : Nat} {interior : List Nat}
    (different : oldEndpoint ≠ newEndpoint)
    (oldCount : interior.count oldEndpoint = 1)
    (newCount : interior.count newEndpoint = 1)
    (newMember : newEndpoint ∈ interior)
    (reduced :
      ModThreeEnvelopeInteriorReduced oldEndpoint interior) :
    ∃ targetInterior,
      B16ListDerives
          (modThreeEnvelopeRender oldEndpoint interior [])
          (modThreeEnvelopeRender newEndpoint targetInterior []) ∧
        (positiveModThreeReduce
            (modThreeEnvelopeRender oldEndpoint interior [])).Perm
          (positiveModThreeReduce
            (modThreeEnvelopeRender newEndpoint targetInterior [])) ∧
        ModThreeEnvelopeInteriorReduced newEndpoint targetInterior := by
  have oldAfterNewCount :
      (interior.erase newEndpoint).count oldEndpoint = 1 := by
    rw [List.count_erase_of_ne different, oldCount]
  have oldAfterNewMember : oldEndpoint ∈ interior.erase newEndpoint :=
    List.count_pos_iff.mp (by omega)
  let trailing := (interior.erase newEndpoint).erase oldEndpoint
  have arrange :
      interior.Perm (newEndpoint :: oldEndpoint :: trailing) :=
    (List.perm_cons_erase newMember).trans <|
      List.Perm.cons newEndpoint <| by
        simpa [trailing] using
          List.perm_cons_erase oldAfterNewMember
  let targetInterior :=
    newEndpoint :: newEndpoint :: oldEndpoint :: oldEndpoint ::
      oldEndpoint :: trailing
  have switch :
      B16ListDerives
        (modThreeEnvelopeRender oldEndpoint
          (newEndpoint :: oldEndpoint :: trailing) [])
        (modThreeEnvelopeRender newEndpoint targetInterior []) := by
    simpa [targetInterior, modThreeEnvelopeRender,
      S5_441.parityEnvelopeRender, List.append_assoc] using
      listDerivesAnchorSwitch11 oldEndpoint newEndpoint trailing
  apply finishRetarget arrange switch
  refine
    { endpoint_count_le_two := ?_
      other_count_le_three := ?_ }
  · have counts := (List.perm_iff_count.mp arrange) newEndpoint
    simp [targetInterior, newCount, different, Ne.symm different]
      at counts ⊢
    omega
  · intro tested testedNeNew
    by_cases testedEqOld : tested = oldEndpoint
    · subst tested
      have counts := (List.perm_iff_count.mp arrange) oldEndpoint
      simp [targetInterior, oldCount, different, Ne.symm different]
        at counts ⊢
      omega
    · have sourceBound :=
        reduced.other_count_le_three tested testedEqOld
      have counts := (List.perm_iff_count.mp arrange) tested
      simp [targetInterior, testedEqOld, testedNeNew,
        Ne.symm testedEqOld, Ne.symm testedNeNew] at counts ⊢
      omega

private theorem existsRetarget12
    {oldEndpoint newEndpoint : Nat} {interior : List Nat}
    (different : oldEndpoint ≠ newEndpoint)
    (oldCount : interior.count oldEndpoint = 1)
    (newCount : interior.count newEndpoint = 2)
    (newMember : newEndpoint ∈ interior)
    (reduced :
      ModThreeEnvelopeInteriorReduced oldEndpoint interior) :
    ∃ targetInterior,
      B16ListDerives
          (modThreeEnvelopeRender oldEndpoint interior [])
          (modThreeEnvelopeRender newEndpoint targetInterior []) ∧
        (positiveModThreeReduce
            (modThreeEnvelopeRender oldEndpoint interior [])).Perm
          (positiveModThreeReduce
            (modThreeEnvelopeRender newEndpoint targetInterior [])) ∧
        ModThreeEnvelopeInteriorReduced newEndpoint targetInterior := by
  have oldAfterNewCount :
      (interior.erase newEndpoint).count oldEndpoint = 1 := by
    rw [List.count_erase_of_ne different, oldCount]
  have oldAfterNewMember : oldEndpoint ∈ interior.erase newEndpoint :=
    List.count_pos_iff.mp (by omega)
  have newAfterNewOldCount :
      ((interior.erase newEndpoint).erase oldEndpoint).count
          newEndpoint = 1 := by
    rw [List.count_erase_of_ne (Ne.symm different),
      List.count_erase_self, newCount]
  have newAfterNewOldMember :
      newEndpoint ∈ (interior.erase newEndpoint).erase oldEndpoint :=
    List.count_pos_iff.mp (by omega)
  let trailing :=
    ((interior.erase newEndpoint).erase oldEndpoint).erase newEndpoint
  have arrange :
      interior.Perm
        (newEndpoint :: oldEndpoint :: newEndpoint :: trailing) :=
    (List.perm_cons_erase newMember).trans <|
      List.Perm.cons newEndpoint <|
        (List.perm_cons_erase oldAfterNewMember).trans <|
          List.Perm.cons oldEndpoint <| by
            simpa [trailing] using
              List.perm_cons_erase newAfterNewOldMember
  let targetInterior :=
    oldEndpoint :: oldEndpoint :: oldEndpoint :: trailing
  have switch :
      B16ListDerives
        (modThreeEnvelopeRender oldEndpoint
          (newEndpoint :: oldEndpoint :: newEndpoint :: trailing) [])
        (modThreeEnvelopeRender newEndpoint targetInterior []) := by
    simpa [targetInterior, modThreeEnvelopeRender,
      S5_441.parityEnvelopeRender, List.append_assoc] using
      listDerivesAnchorSwitch12 oldEndpoint newEndpoint trailing
  apply finishRetarget arrange switch
  refine
    { endpoint_count_le_two := ?_
      other_count_le_three := ?_ }
  · have counts := (List.perm_iff_count.mp arrange) newEndpoint
    simp [targetInterior, newCount, different, Ne.symm different]
      at counts ⊢
    omega
  · intro tested testedNeNew
    by_cases testedEqOld : tested = oldEndpoint
    · subst tested
      have counts := (List.perm_iff_count.mp arrange) oldEndpoint
      simp [targetInterior, oldCount, different, Ne.symm different]
        at counts ⊢
      omega
    · have sourceBound :=
        reduced.other_count_le_three tested testedEqOld
      have counts := (List.perm_iff_count.mp arrange) tested
      simp [targetInterior, testedEqOld, testedNeNew,
        Ne.symm testedEqOld, Ne.symm testedNeNew] at counts ⊢
      omega

private theorem existsRetarget13
    {oldEndpoint newEndpoint : Nat} {interior : List Nat}
    (different : oldEndpoint ≠ newEndpoint)
    (oldCount : interior.count oldEndpoint = 1)
    (newCount : interior.count newEndpoint = 3)
    (newMember : newEndpoint ∈ interior)
    (reduced :
      ModThreeEnvelopeInteriorReduced oldEndpoint interior) :
    ∃ targetInterior,
      B16ListDerives
          (modThreeEnvelopeRender oldEndpoint interior [])
          (modThreeEnvelopeRender newEndpoint targetInterior []) ∧
        (positiveModThreeReduce
            (modThreeEnvelopeRender oldEndpoint interior [])).Perm
          (positiveModThreeReduce
            (modThreeEnvelopeRender newEndpoint targetInterior [])) ∧
        ModThreeEnvelopeInteriorReduced newEndpoint targetInterior := by
  have oldMember : oldEndpoint ∈ interior :=
    List.count_pos_iff.mp (by omega)
  have newAfterOldCount :
      (interior.erase oldEndpoint).count newEndpoint = 3 := by
    rw [List.count_erase_of_ne (Ne.symm different), newCount]
  have newAfterOldMember : newEndpoint ∈ interior.erase oldEndpoint :=
    List.count_pos_iff.mp (by omega)
  have newAfterOldOneCount :
      ((interior.erase oldEndpoint).erase newEndpoint).count
          newEndpoint = 2 := by
    rw [List.count_erase_self, newAfterOldCount]
  have newAfterOldOneMember :
      newEndpoint ∈ (interior.erase oldEndpoint).erase newEndpoint :=
    List.count_pos_iff.mp (by omega)
  have newAfterOldTwoCount :
      (((interior.erase oldEndpoint).erase newEndpoint).erase
          newEndpoint).count newEndpoint = 1 := by
    rw [List.count_erase_self, newAfterOldOneCount]
  have newAfterOldTwoMember :
      newEndpoint ∈
        ((interior.erase oldEndpoint).erase newEndpoint).erase
          newEndpoint :=
    List.count_pos_iff.mp (by omega)
  let trailing :=
    (((interior.erase oldEndpoint).erase newEndpoint).erase
      newEndpoint).erase newEndpoint
  have arrange :
      interior.Perm
        (oldEndpoint :: newEndpoint :: newEndpoint :: newEndpoint ::
          trailing) :=
    (List.perm_cons_erase oldMember).trans <|
      List.Perm.cons oldEndpoint <|
        (List.perm_cons_erase newAfterOldMember).trans <|
          List.Perm.cons newEndpoint <|
            (List.perm_cons_erase newAfterOldOneMember).trans <|
              List.Perm.cons newEndpoint <| by
                simpa [trailing] using
                  List.perm_cons_erase newAfterOldTwoMember
  let targetInterior :=
    oldEndpoint :: oldEndpoint :: oldEndpoint :: newEndpoint :: trailing
  have switch :
      B16ListDerives
        (modThreeEnvelopeRender oldEndpoint
          (oldEndpoint :: newEndpoint :: newEndpoint :: newEndpoint ::
            trailing) [])
        (modThreeEnvelopeRender newEndpoint targetInterior []) := by
    simpa [targetInterior, modThreeEnvelopeRender,
      S5_441.parityEnvelopeRender, List.append_assoc] using
      listDerivesAnchorSwitch13 oldEndpoint newEndpoint trailing
  apply finishRetarget arrange switch
  refine
    { endpoint_count_le_two := ?_
      other_count_le_three := ?_ }
  · have counts := (List.perm_iff_count.mp arrange) newEndpoint
    simp [targetInterior, newCount, different, Ne.symm different]
      at counts ⊢
    omega
  · intro tested testedNeNew
    by_cases testedEqOld : tested = oldEndpoint
    · subst tested
      have counts := (List.perm_iff_count.mp arrange) oldEndpoint
      simp [targetInterior, oldCount, different, Ne.symm different]
        at counts ⊢
      omega
    · have sourceBound :=
        reduced.other_count_le_three tested testedEqOld
      have counts := (List.perm_iff_count.mp arrange) tested
      simp [targetInterior, testedEqOld, testedNeNew,
        Ne.symm testedEqOld, Ne.symm testedNeNew] at counts ⊢
      omega

private theorem existsRetarget21
    {oldEndpoint newEndpoint : Nat} {interior : List Nat}
    (different : oldEndpoint ≠ newEndpoint)
    (oldCount : interior.count oldEndpoint = 2)
    (newCount : interior.count newEndpoint = 1)
    (newMember : newEndpoint ∈ interior)
    (reduced :
      ModThreeEnvelopeInteriorReduced oldEndpoint interior) :
    ∃ targetInterior,
      B16ListDerives
          (modThreeEnvelopeRender oldEndpoint interior [])
          (modThreeEnvelopeRender newEndpoint targetInterior []) ∧
        (positiveModThreeReduce
            (modThreeEnvelopeRender oldEndpoint interior [])).Perm
          (positiveModThreeReduce
            (modThreeEnvelopeRender newEndpoint targetInterior [])) ∧
        ModThreeEnvelopeInteriorReduced newEndpoint targetInterior := by
  have firstOldMember : oldEndpoint ∈ interior :=
    List.count_pos_iff.mp (by omega)
  have afterOldCount :
      (interior.erase oldEndpoint).count oldEndpoint = 1 := by
    rw [List.count_erase_self, oldCount]
  have secondOldMember : oldEndpoint ∈ interior.erase oldEndpoint :=
    List.count_pos_iff.mp (by omega)
  have newAfterOldsCount :
      ((interior.erase oldEndpoint).erase oldEndpoint).count
          newEndpoint = 1 := by
    rw [List.count_erase_of_ne (Ne.symm different),
      List.count_erase_of_ne (Ne.symm different), newCount]
  have newAfterOldsMember :
      newEndpoint ∈ (interior.erase oldEndpoint).erase oldEndpoint :=
    List.count_pos_iff.mp (by omega)
  let trailing :=
    ((interior.erase oldEndpoint).erase oldEndpoint).erase newEndpoint
  have canonicalArrange :
      interior.Perm
        (oldEndpoint :: oldEndpoint :: newEndpoint :: trailing) :=
    (List.perm_cons_erase firstOldMember).trans <|
      List.Perm.cons oldEndpoint <|
        (List.perm_cons_erase secondOldMember).trans <|
          List.Perm.cons oldEndpoint <| by
            simpa [trailing] using
              List.perm_cons_erase newAfterOldsMember
  have rotate :
      (oldEndpoint :: oldEndpoint :: newEndpoint :: trailing).Perm
        (trailing ++ [oldEndpoint, oldEndpoint, newEndpoint]) := by
    rw [List.perm_iff_count]
    intro tested
    simp only [List.count_cons, List.count_append,
      List.count_nil]
    omega
  have arrange :
      interior.Perm
        (trailing ++ [oldEndpoint, oldEndpoint, newEndpoint]) :=
    canonicalArrange.trans rotate
  let targetInterior := trailing ++ [oldEndpoint, newEndpoint, newEndpoint]
  have switch :
      B16ListDerives
        (modThreeEnvelopeRender oldEndpoint
          (trailing ++ [oldEndpoint, oldEndpoint, newEndpoint]) [])
        (modThreeEnvelopeRender newEndpoint targetInterior []) := by
    simpa [targetInterior, modThreeEnvelopeRender,
      S5_441.parityEnvelopeRender, List.append_assoc] using
      listDerivesAnchorSwitch21 oldEndpoint newEndpoint trailing
  apply finishRetarget arrange switch
  refine
    { endpoint_count_le_two := ?_
      other_count_le_three := ?_ }
  · have counts := (List.perm_iff_count.mp arrange) newEndpoint
    simp [targetInterior, newCount, different, Ne.symm different]
      at counts ⊢
    omega
  · intro tested testedNeNew
    by_cases testedEqOld : tested = oldEndpoint
    · subst tested
      have counts := (List.perm_iff_count.mp arrange) oldEndpoint
      simp [targetInterior, oldCount, different, Ne.symm different]
        at counts ⊢
      omega
    · have sourceBound :=
        reduced.other_count_le_three tested testedEqOld
      have counts := (List.perm_iff_count.mp arrange) tested
      simp [targetInterior, testedEqOld, testedNeNew,
        Ne.symm testedEqOld, Ne.symm testedNeNew] at counts ⊢
      omega

private theorem existsRetarget22
    {oldEndpoint newEndpoint : Nat} {interior : List Nat}
    (different : oldEndpoint ≠ newEndpoint)
    (oldCount : interior.count oldEndpoint = 2)
    (newCount : interior.count newEndpoint = 2)
    (newMember : newEndpoint ∈ interior)
    (reduced :
      ModThreeEnvelopeInteriorReduced oldEndpoint interior) :
    ∃ targetInterior,
      B16ListDerives
          (modThreeEnvelopeRender oldEndpoint interior [])
          (modThreeEnvelopeRender newEndpoint targetInterior []) ∧
        (positiveModThreeReduce
            (modThreeEnvelopeRender oldEndpoint interior [])).Perm
          (positiveModThreeReduce
            (modThreeEnvelopeRender newEndpoint targetInterior [])) ∧
        ModThreeEnvelopeInteriorReduced newEndpoint targetInterior := by
  have firstOldMember : oldEndpoint ∈ interior :=
    List.count_pos_iff.mp (by omega)
  have afterOldCount :
      (interior.erase oldEndpoint).count oldEndpoint = 1 := by
    rw [List.count_erase_self, oldCount]
  have secondOldMember : oldEndpoint ∈ interior.erase oldEndpoint :=
    List.count_pos_iff.mp (by omega)
  have newAfterOldsCount :
      ((interior.erase oldEndpoint).erase oldEndpoint).count
          newEndpoint = 2 := by
    rw [List.count_erase_of_ne (Ne.symm different),
      List.count_erase_of_ne (Ne.symm different), newCount]
  have firstNewMember :
      newEndpoint ∈ (interior.erase oldEndpoint).erase oldEndpoint :=
    List.count_pos_iff.mp (by omega)
  have afterFirstNewCount :
      (((interior.erase oldEndpoint).erase oldEndpoint).erase
          newEndpoint).count newEndpoint = 1 := by
    rw [List.count_erase_self, newAfterOldsCount]
  have secondNewMember :
      newEndpoint ∈
        ((interior.erase oldEndpoint).erase oldEndpoint).erase
          newEndpoint :=
    List.count_pos_iff.mp (by omega)
  let trailing :=
    (((interior.erase oldEndpoint).erase oldEndpoint).erase
      newEndpoint).erase newEndpoint
  have arrange :
      interior.Perm
        (oldEndpoint :: oldEndpoint :: newEndpoint :: newEndpoint ::
          trailing) :=
    (List.perm_cons_erase firstOldMember).trans <|
      List.Perm.cons oldEndpoint <|
        (List.perm_cons_erase secondOldMember).trans <|
          List.Perm.cons oldEndpoint <|
            (List.perm_cons_erase firstNewMember).trans <|
              List.Perm.cons newEndpoint <| by
                simpa [trailing] using
                  List.perm_cons_erase secondNewMember
  let targetInterior := oldEndpoint :: trailing
  have switch :
      B16ListDerives
        (modThreeEnvelopeRender oldEndpoint
          (oldEndpoint :: oldEndpoint :: newEndpoint :: newEndpoint ::
            trailing) [])
        (modThreeEnvelopeRender newEndpoint targetInterior []) := by
    simpa [targetInterior, modThreeEnvelopeRender,
      S5_441.parityEnvelopeRender, List.append_assoc] using
      listDerivesAnchorSwitch22 oldEndpoint newEndpoint trailing
  apply finishRetarget arrange switch
  refine
    { endpoint_count_le_two := ?_
      other_count_le_three := ?_ }
  · have counts := (List.perm_iff_count.mp arrange) newEndpoint
    simp [targetInterior, newCount, different, Ne.symm different]
      at counts ⊢
    omega
  · intro tested testedNeNew
    by_cases testedEqOld : tested = oldEndpoint
    · subst tested
      have counts := (List.perm_iff_count.mp arrange) oldEndpoint
      simp [targetInterior, oldCount, different, Ne.symm different]
        at counts ⊢
      omega
    · have sourceBound :=
        reduced.other_count_le_three tested testedEqOld
      have counts := (List.perm_iff_count.mp arrange) tested
      simp [targetInterior, testedEqOld, testedNeNew,
        Ne.symm testedEqOld, Ne.symm testedNeNew] at counts ⊢
      omega

private theorem existsRetarget23
    {oldEndpoint newEndpoint : Nat} {interior : List Nat}
    (different : oldEndpoint ≠ newEndpoint)
    (oldCount : interior.count oldEndpoint = 2)
    (newCount : interior.count newEndpoint = 3)
    (newMember : newEndpoint ∈ interior)
    (reduced :
      ModThreeEnvelopeInteriorReduced oldEndpoint interior) :
    ∃ targetInterior,
      B16ListDerives
          (modThreeEnvelopeRender oldEndpoint interior [])
          (modThreeEnvelopeRender newEndpoint targetInterior []) ∧
        (positiveModThreeReduce
            (modThreeEnvelopeRender oldEndpoint interior [])).Perm
          (positiveModThreeReduce
            (modThreeEnvelopeRender newEndpoint targetInterior [])) ∧
        ModThreeEnvelopeInteriorReduced newEndpoint targetInterior := by
  have firstOldMember : oldEndpoint ∈ interior :=
    List.count_pos_iff.mp (by omega)
  have afterOldCount :
      (interior.erase oldEndpoint).count oldEndpoint = 1 := by
    rw [List.count_erase_self, oldCount]
  have secondOldMember : oldEndpoint ∈ interior.erase oldEndpoint :=
    List.count_pos_iff.mp (by omega)
  have newAfterOldsCount :
      ((interior.erase oldEndpoint).erase oldEndpoint).count
          newEndpoint = 3 := by
    rw [List.count_erase_of_ne (Ne.symm different),
      List.count_erase_of_ne (Ne.symm different), newCount]
  have firstNewMember :
      newEndpoint ∈ (interior.erase oldEndpoint).erase oldEndpoint :=
    List.count_pos_iff.mp (by omega)
  have afterFirstNewCount :
      (((interior.erase oldEndpoint).erase oldEndpoint).erase
          newEndpoint).count newEndpoint = 2 := by
    rw [List.count_erase_self, newAfterOldsCount]
  have secondNewMember :
      newEndpoint ∈
        ((interior.erase oldEndpoint).erase oldEndpoint).erase
          newEndpoint :=
    List.count_pos_iff.mp (by omega)
  have afterSecondNewCount :
      ((((interior.erase oldEndpoint).erase oldEndpoint).erase
          newEndpoint).erase newEndpoint).count newEndpoint = 1 := by
    rw [List.count_erase_self, afterFirstNewCount]
  have thirdNewMember :
      newEndpoint ∈
        (((interior.erase oldEndpoint).erase oldEndpoint).erase
          newEndpoint).erase newEndpoint :=
    List.count_pos_iff.mp (by omega)
  let trailing :=
    ((((interior.erase oldEndpoint).erase oldEndpoint).erase
      newEndpoint).erase newEndpoint).erase newEndpoint
  have arrange :
      interior.Perm
        (oldEndpoint :: oldEndpoint :: newEndpoint :: newEndpoint ::
          newEndpoint :: trailing) :=
    (List.perm_cons_erase firstOldMember).trans <|
      List.Perm.cons oldEndpoint <|
        (List.perm_cons_erase secondOldMember).trans <|
          List.Perm.cons oldEndpoint <|
            (List.perm_cons_erase firstNewMember).trans <|
              List.Perm.cons newEndpoint <|
                (List.perm_cons_erase secondNewMember).trans <|
                  List.Perm.cons newEndpoint <| by
                    simpa [trailing] using
                      List.perm_cons_erase thirdNewMember
  let targetInterior := oldEndpoint :: newEndpoint :: trailing
  have switch :
      B16ListDerives
        (modThreeEnvelopeRender oldEndpoint
          (oldEndpoint :: oldEndpoint :: newEndpoint :: newEndpoint ::
            newEndpoint :: trailing) [])
        (modThreeEnvelopeRender newEndpoint targetInterior []) := by
    simpa [targetInterior, modThreeEnvelopeRender,
      S5_441.parityEnvelopeRender, List.append_assoc] using
      listDerivesAnchorSwitch23 oldEndpoint newEndpoint trailing
  apply finishRetarget arrange switch
  refine
    { endpoint_count_le_two := ?_
      other_count_le_three := ?_ }
  · have counts := (List.perm_iff_count.mp arrange) newEndpoint
    simp [targetInterior, newCount, different, Ne.symm different]
      at counts ⊢
    omega
  · intro tested testedNeNew
    by_cases testedEqOld : tested = oldEndpoint
    · subst tested
      have counts := (List.perm_iff_count.mp arrange) oldEndpoint
      simp [targetInterior, oldCount, different, Ne.symm different]
        at counts ⊢
      omega
    · have sourceBound :=
        reduced.other_count_le_three tested testedEqOld
      have counts := (List.perm_iff_count.mp arrange) tested
      simp [targetInterior, testedEqOld, testedNeNew,
        Ne.symm testedEqOld, Ne.symm testedNeNew] at counts ⊢
      omega

/-- Retarget a reduced closed mod-three envelope to any different endpoint
already supported by its interior.  The nine possible old/new internal
multiplicities are discharged by the nine literal B16 anchor-switch leaves. -/
theorem exists_reducedModThreeEnvelopeRetarget
    {oldEndpoint newEndpoint : Nat} {interior : List Nat}
    (different : oldEndpoint ≠ newEndpoint)
    (newMember : newEndpoint ∈ interior)
    (reduced :
      ModThreeEnvelopeInteriorReduced oldEndpoint interior) :
    ∃ targetInterior,
      B16ListDerives
          (modThreeEnvelopeRender oldEndpoint interior [])
          (modThreeEnvelopeRender newEndpoint targetInterior []) ∧
        (positiveModThreeReduce
            (modThreeEnvelopeRender oldEndpoint interior [])).Perm
          (positiveModThreeReduce
            (modThreeEnvelopeRender newEndpoint targetInterior [])) ∧
        ModThreeEnvelopeInteriorReduced newEndpoint targetInterior := by
  have oldCountLe := reduced.endpoint_count_le_two
  have newCountPositive : 0 < interior.count newEndpoint :=
    List.count_pos_iff.mpr newMember
  have newCountLe :=
    reduced.other_count_le_three newEndpoint (Ne.symm different)
  have oldCases :
      interior.count oldEndpoint = 0 ∨
        interior.count oldEndpoint = 1 ∨
          interior.count oldEndpoint = 2 := by
    omega
  have newCases :
      interior.count newEndpoint = 1 ∨
        interior.count newEndpoint = 2 ∨
          interior.count newEndpoint = 3 := by
    omega
  rcases oldCases with oldCount | oldCount | oldCount
  · rcases newCases with newCount | newCount | newCount
    · exact
        existsRetarget01 different oldCount newCount newMember reduced
    · exact
        existsRetarget02 different oldCount newCount newMember reduced
    · exact
        existsRetarget03 different oldCount newCount newMember reduced
  · rcases newCases with newCount | newCount | newCount
    · exact
        existsRetarget11 different oldCount newCount newMember reduced
    · exact
        existsRetarget12 different oldCount newCount newMember reduced
    · exact
        existsRetarget13 different oldCount newCount newMember reduced
  · rcases newCases with newCount | newCount | newCount
    · exact
        existsRetarget21 different oldCount newCount newMember reduced
    · exact
        existsRetarget22 different oldCount newCount newMember reduced
    · exact
        existsRetarget23 different oldCount newCount newMember reduced

end SemigroupBasis.CoRoots.Order6L2DD029ModThreeComponentB16
