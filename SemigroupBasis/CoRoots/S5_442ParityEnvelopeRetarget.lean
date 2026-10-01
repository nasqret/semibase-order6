import SemigroupBasis.CoRoots.S5_442ParityEnvelopeNormalize

namespace SemigroupBasis.CoRoots.S5_442

open SemigroupBasis
open SemigroupBasis.Examples


private def retargetInstantiateThreeWords
    (first second third : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | n + 3 => Word.singleton (n + 3)

private theorem derivesOddOddAnchorSwitch
    (oldAnchor newAnchor : Word Nat) :
    Derives basis
      (((oldAnchor ++ oldAnchor) ++ newAnchor) ++ oldAnchor)
      (((newAnchor ++ oldAnchor) ++ newAnchor) ++ newAnchor) := by
  have base : Derives basis xxyx yxyy :=
    Derives.fromBasis (e := xxyxYXYYLaw) (by simp [basis])
  have substituted :=
    Derives.subst base
      (retargetInstantiateThreeWords oldAnchor newAnchor newAnchor)
  simpa [xxyxYXYYLaw, xxyx, yxyy, w,
    retargetInstantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

private theorem derivesExtendedOddOddAnchorSwitch
    (oldAnchor newAnchor trailing : Word Nat) :
    Derives basis
      ((((oldAnchor ++ oldAnchor) ++ newAnchor) ++ trailing) ++ oldAnchor)
      ((((newAnchor ++ oldAnchor) ++ newAnchor) ++ trailing) ++ newAnchor) := by
  have base : Derives basis xxyzx yxyzy :=
    Derives.fromBasis (e := xxyzxYXYZYLaw) (by simp [basis])
  have substituted :=
    Derives.subst base
      (retargetInstantiateThreeWords oldAnchor newAnchor trailing)
  simpa [xxyzxYXYZYLaw, xxyzx, yxyzy, w,
    retargetInstantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

private theorem derivesClosedEvenInitialSwitch
    (oldAnchor newAnchor : Word Nat) :
    Derives basis
      (((oldAnchor ++ newAnchor) ++ oldAnchor) ++ newAnchor)
      (((newAnchor ++ oldAnchor) ++ oldAnchor) ++ newAnchor) := by
  have base : Derives basis xyxy yxxy :=
    Derives.fromBasis (e := xyxyYXXYLaw) (by simp [basis])
  have substituted :=
    Derives.subst base
      (retargetInstantiateThreeWords oldAnchor newAnchor newAnchor)
  simpa [xyxyYXXYLaw, xyxy, yxxy, w,
    retargetInstantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

private theorem derivesAttachmentYXXZY
    (oldAnchor newAnchor trailing : Word Nat) :
    Derives basis
      ((((oldAnchor ++ newAnchor) ++ oldAnchor) ++ trailing) ++ newAnchor)
      ((((newAnchor ++ oldAnchor) ++ oldAnchor) ++ trailing) ++ newAnchor) := by
  have base : Derives basis xyxzy yxxzy :=
    Derives.fromBasis (e := xyxzyYXXZYLaw) (by simp [basis])
  have substituted :=
    Derives.subst base
      (retargetInstantiateThreeWords oldAnchor newAnchor trailing)
  simpa [xyxzyYXXZYLaw, xyxzy, yxxzy, w,
    retargetInstantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

private theorem derivesXYXToYYXXY
    (oldAnchor newAnchor : Word Nat) :
    Derives basis
      ((oldAnchor ++ newAnchor) ++ oldAnchor)
      ((((newAnchor ++ newAnchor) ++ oldAnchor) ++ oldAnchor) ++
        newAnchor) := by
  have base : Derives basis xyx yyxxy :=
    Derives.fromBasis (e := xyxYYXXYLaw) (by simp [basis])
  have substituted :=
    Derives.subst base
      (retargetInstantiateThreeWords oldAnchor newAnchor newAnchor)
  simpa [xyxYYXXYLaw, xyx, yyxxy, w,
    retargetInstantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

private theorem derivesEvenEvenAnchorSwitch
    (oldAnchor newAnchor : Word Nat) :
    Derives basis
      (((oldAnchor ++ newAnchor) ++ newAnchor) ++ oldAnchor)
      (((newAnchor ++ oldAnchor) ++ oldAnchor) ++ newAnchor) := by
  exact
    (derivesClosedEvenSwitch oldAnchor newAnchor).symm.trans
      (derivesClosedEvenInitialSwitch oldAnchor newAnchor)

private theorem derivesEvenEvenAnchorSwitchWithTrailing
    (oldAnchor newAnchor trailing : Word Nat) :
    Derives basis
      ((((oldAnchor ++ newAnchor) ++ newAnchor) ++ trailing) ++ oldAnchor)
      ((((newAnchor ++ oldAnchor) ++ oldAnchor) ++ trailing) ++ newAnchor) := by
  exact
    (derivesAttachmentXYYZX oldAnchor newAnchor trailing).symm.trans
      (derivesAttachmentYXXZY oldAnchor newAnchor trailing)

private theorem derivesOddEvenAnchorSwitch
    (oldAnchor newAnchor : Word Nat) :
    Derives basis
      ((((oldAnchor ++ oldAnchor) ++ newAnchor) ++ newAnchor) ++ oldAnchor)
      ((newAnchor ++ oldAnchor) ++ newAnchor) := by
  simpa [Word.append_assoc] using
    (derivesXYXToYYXXY newAnchor oldAnchor).symm

private theorem derivesOddEvenAnchorSwitchWithTrailing
    (oldAnchor newAnchor trailing : Word Nat) :
    Derives basis
      (((((oldAnchor ++ oldAnchor) ++ newAnchor) ++ newAnchor) ++
        trailing) ++ oldAnchor)
      (((newAnchor ++ oldAnchor) ++ trailing) ++ newAnchor) := by
  have switch :
      Derives basis
        (((((oldAnchor ++ oldAnchor) ++ newAnchor) ++ newAnchor) ++
          trailing) ++ oldAnchor)
        (((((newAnchor ++ oldAnchor) ++ newAnchor) ++ newAnchor) ++
          trailing) ++ newAnchor) := by
    simpa [Word.append_assoc] using
      derivesExtendedOddOddAnchorSwitch
        oldAnchor newAnchor (newAnchor ++ trailing)
  have moveOldAcrossFirstNew :
      Derives basis
        (((((newAnchor ++ oldAnchor) ++ newAnchor) ++ newAnchor) ++
          trailing) ++ newAnchor)
        (((((newAnchor ++ newAnchor) ++ oldAnchor) ++ newAnchor) ++
          trailing) ++ newAnchor) := by
    simpa [Word.append_assoc] using
      derivesAdjacentInteriorBlockSwap newAnchor oldAnchor newAnchor
        (newAnchor ++ trailing)
  have moveOldAcrossSecondNew :
      Derives basis
        (((((newAnchor ++ newAnchor) ++ oldAnchor) ++ newAnchor) ++
          trailing) ++ newAnchor)
        (((((newAnchor ++ newAnchor) ++ newAnchor) ++ oldAnchor) ++
          trailing) ++ newAnchor) := by
    simpa [Word.append_assoc] using
      Derives.prepend newAnchor
        (derivesAdjacentInteriorBlockSwap
          newAnchor oldAnchor newAnchor trailing)
  have contract :
      Derives basis
        (((((newAnchor ++ newAnchor) ++ newAnchor) ++ oldAnchor) ++
          trailing) ++ newAnchor)
        (((newAnchor ++ oldAnchor) ++ trailing) ++ newAnchor) := by
    simpa [Word.append_assoc] using
      (derivesLeftEnvelopePower
        newAnchor (oldAnchor ++ trailing)).symm
  exact switch.trans <|
    moveOldAcrossFirstNew.trans <|
      moveOldAcrossSecondNew.trans contract

private theorem listDerivesOddOddAnchorSwitch
    (oldAnchor newAnchor : Word Nat) (trailing : List Nat) :
    ListDerives
      (oldAnchor.toList ++ oldAnchor.toList ++ newAnchor.toList ++
        trailing ++ oldAnchor.toList)
      (newAnchor.toList ++ oldAnchor.toList ++ newAnchor.toList ++
        trailing ++ newAnchor.toList) := by
  cases trailing with
  | nil =>
      simpa [Word.toList_append, List.append_assoc] using
        (ListDerives.ofWord
          (derivesOddOddAnchorSwitch oldAnchor newAnchor))
  | cons trailingHead trailingTail =>
      let trailingWord :=
        S5_107.listWordOfCons trailingHead trailingTail
      simpa [trailingWord, S5_107.listWordOfCons, Word.toList,
        Word.toList_append, List.append_assoc] using
          (ListDerives.ofWord
            (derivesExtendedOddOddAnchorSwitch
              oldAnchor newAnchor trailingWord))

private theorem listDerivesEvenEvenAnchorSwitch
    (oldAnchor newAnchor : Word Nat) (trailing : List Nat) :
    ListDerives
      (oldAnchor.toList ++ newAnchor.toList ++ newAnchor.toList ++
        trailing ++ oldAnchor.toList)
      (newAnchor.toList ++ oldAnchor.toList ++ oldAnchor.toList ++
        trailing ++ newAnchor.toList) := by
  cases trailing with
  | nil =>
      simpa [Word.toList_append, List.append_assoc] using
        (ListDerives.ofWord
          (derivesEvenEvenAnchorSwitch oldAnchor newAnchor))
  | cons trailingHead trailingTail =>
      let trailingWord :=
        S5_107.listWordOfCons trailingHead trailingTail
      simpa [trailingWord, S5_107.listWordOfCons, Word.toList,
        Word.toList_append, List.append_assoc] using
          (ListDerives.ofWord
            (derivesEvenEvenAnchorSwitchWithTrailing
              oldAnchor newAnchor trailingWord))

private theorem listDerivesOddEvenAnchorSwitch
    (oldAnchor newAnchor : Word Nat) (trailing : List Nat) :
    ListDerives
      (oldAnchor.toList ++ oldAnchor.toList ++ newAnchor.toList ++
        newAnchor.toList ++ trailing ++ oldAnchor.toList)
      (newAnchor.toList ++ oldAnchor.toList ++ trailing ++
        newAnchor.toList) := by
  cases trailing with
  | nil =>
      simpa [Word.toList_append, List.append_assoc] using
        (ListDerives.ofWord
          (derivesOddEvenAnchorSwitch oldAnchor newAnchor))
  | cons trailingHead trailingTail =>
      let trailingWord :=
        S5_107.listWordOfCons trailingHead trailingTail
      simpa [trailingWord, S5_107.listWordOfCons, Word.toList,
        Word.toList_append, List.append_assoc] using
          (ListDerives.ofWord
            (derivesOddEvenAnchorSwitchWithTrailing
              oldAnchor newAnchor trailingWord))

private theorem listDerivesEvenOddAnchorSwitch
    (oldAnchor newAnchor : Word Nat) (trailing : List Nat) :
    ListDerives
      (oldAnchor.toList ++ newAnchor.toList ++ trailing ++
        oldAnchor.toList)
      (newAnchor.toList ++ newAnchor.toList ++ oldAnchor.toList ++
        oldAnchor.toList ++ trailing ++ newAnchor.toList) := by
  simpa [List.append_assoc] using
    ListDerives.symm <|
      listDerivesOddEvenAnchorSwitch
        newAnchor oldAnchor trailing

/-- An envelope interior is reduced relative to its endpoint when the
endpoint occurs internally at most once and every other letter occurs at
most twice. -/
structure ParityEnvelopeInteriorReduced
    (endpoint : Nat) (interior : List Nat) : Prop where
  endpoint_count_le_one :
    interior.count endpoint ≤ 1
  other_count_le_two :
    ∀ letter, letter ≠ endpoint → interior.count letter ≤ 2

/-- The exact canonical positive-parity profile represented by a closed
envelope. Raw anchor switches can change an anchor count by two, while this
profile is preserved as a multiset. -/
def parityEnvelopeReducedProfile
    (endpoint : Nat) (interior : List Nat) : List Nat :=
  positiveParityReduce
    (parityEnvelopeRender endpoint interior [])

private theorem parityEnvelopeRender_perm_of_interior_perm
    (endpoint : Nat) {left right : List Nat}
    (permutation : left.Perm right) :
    (parityEnvelopeRender endpoint left []).Perm
      (parityEnvelopeRender endpoint right []) := by
  rw [List.perm_iff_count]
  intro tested
  have counts :=
    (List.perm_iff_count.mp permutation) tested
  simp only [parityEnvelopeRender, S5_441.parityEnvelopeRender,
    List.count_cons, List.count_append, List.count_nil] at counts ⊢
  omega

private theorem positiveParityReduce_perm_of_perm
    {left right : List Nat}
    (permutation : left.Perm right) :
    (positiveParityReduce left).Perm
      (positiveParityReduce right) :=
  positiveParityReduce_perm (fun tested => permutation.mem_iff)
    (fun tested =>
      congrArg (fun count => count % 2)
        ((List.perm_iff_count.mp permutation) tested))

private theorem parityEnvelopeReducedProfile_perm_of_interior_perm
    (endpoint : Nat) {left right : List Nat}
    (permutation : left.Perm right) :
    (parityEnvelopeReducedProfile endpoint left).Perm
      (parityEnvelopeReducedProfile endpoint right) :=
  positiveParityReduce_perm_of_perm
    (parityEnvelopeRender_perm_of_interior_perm
      endpoint permutation)

private theorem oddOddAnchorSwitch_reducedProfile_perm
    (oldEndpoint newEndpoint : Nat) (trailing : List Nat) :
    (parityEnvelopeReducedProfile oldEndpoint
        (oldEndpoint :: newEndpoint :: trailing)).Perm
      (parityEnvelopeReducedProfile newEndpoint
        (oldEndpoint :: newEndpoint :: trailing)) := by
  apply positiveParityReduce_perm
  · intro tested
    simp [parityEnvelopeReducedProfile, parityEnvelopeRender,
      S5_441.parityEnvelopeRender, List.mem_append, or_assoc,
      or_left_comm, or_comm]
  · intro tested
    simp only [parityEnvelopeReducedProfile, parityEnvelopeRender,
      S5_441.parityEnvelopeRender, List.count_cons,
      List.count_append, List.count_nil]
    omega

private theorem evenEvenAnchorSwitch_reducedProfile_perm
    (oldEndpoint newEndpoint : Nat) (trailing : List Nat) :
    (parityEnvelopeReducedProfile oldEndpoint
        (newEndpoint :: newEndpoint :: trailing)).Perm
      (parityEnvelopeReducedProfile newEndpoint
        (oldEndpoint :: oldEndpoint :: trailing)) := by
  apply positiveParityReduce_perm
  · intro tested
    simp [parityEnvelopeReducedProfile, parityEnvelopeRender,
      S5_441.parityEnvelopeRender, List.mem_append, or_assoc,
      or_left_comm, or_comm]
  · intro tested
    simp only [parityEnvelopeReducedProfile, parityEnvelopeRender,
      S5_441.parityEnvelopeRender, List.count_cons,
      List.count_append, List.count_nil]
    omega

private theorem oddEvenAnchorSwitch_reducedProfile_perm
    (oldEndpoint newEndpoint : Nat) (trailing : List Nat) :
    (parityEnvelopeReducedProfile oldEndpoint
        (oldEndpoint :: newEndpoint :: newEndpoint :: trailing)).Perm
      (parityEnvelopeReducedProfile newEndpoint
        (oldEndpoint :: trailing)) := by
  apply positiveParityReduce_perm
  · intro tested
    simp [parityEnvelopeReducedProfile, parityEnvelopeRender,
      S5_441.parityEnvelopeRender, List.mem_append, or_assoc,
      or_left_comm, or_comm]
  · intro tested
    simp only [parityEnvelopeReducedProfile, parityEnvelopeRender,
      S5_441.parityEnvelopeRender, List.count_cons,
      List.count_append, List.count_nil]
    omega

private theorem evenOddAnchorSwitch_reducedProfile_perm
    (oldEndpoint newEndpoint : Nat) (trailing : List Nat) :
    (parityEnvelopeReducedProfile oldEndpoint
        (newEndpoint :: trailing)).Perm
      (parityEnvelopeReducedProfile newEndpoint
        (newEndpoint :: oldEndpoint :: oldEndpoint :: trailing)) := by
  apply positiveParityReduce_perm
  · intro tested
    simp [parityEnvelopeReducedProfile, parityEnvelopeRender,
      S5_441.parityEnvelopeRender, List.mem_append, or_assoc,
      or_left_comm, or_comm]
  · intro tested
    simp only [parityEnvelopeReducedProfile, parityEnvelopeRender,
      S5_441.parityEnvelopeRender, List.count_cons,
      List.count_append, List.count_nil]
    omega

private theorem exists_retarget_oddOdd
    {oldEndpoint newEndpoint : Nat} {interior : List Nat}
    (different : oldEndpoint ≠ newEndpoint)
    (oldCount : interior.count oldEndpoint = 1)
    (newCount : interior.count newEndpoint = 1)
    (reduced :
      ParityEnvelopeInteriorReduced oldEndpoint interior) :
    ∃ targetInterior,
      ListDerives
          (parityEnvelopeRender oldEndpoint interior [])
          (parityEnvelopeRender newEndpoint targetInterior []) ∧
        (parityEnvelopeReducedProfile oldEndpoint interior).Perm
          (parityEnvelopeReducedProfile newEndpoint targetInterior) ∧
        ParityEnvelopeInteriorReduced
          newEndpoint targetInterior := by
  have oldMember : oldEndpoint ∈ interior :=
    List.count_pos_iff.mp (by omega)
  have newCountAfterOld :
      (interior.erase oldEndpoint).count newEndpoint = 1 := by
    rw [List.count_erase_of_ne (Ne.symm different), newCount]
  have newMemberAfterOld :
      newEndpoint ∈ interior.erase oldEndpoint :=
    List.count_pos_iff.mp (by omega)
  let trailing :=
    (interior.erase oldEndpoint).erase newEndpoint
  have arrange :
      interior.Perm
        (oldEndpoint :: newEndpoint :: trailing) :=
    (List.perm_cons_erase oldMember).trans <|
      List.Perm.cons oldEndpoint <| by
        simpa [trailing] using
          List.perm_cons_erase newMemberAfterOld
  have arrangeSource :
      ListDerives
        (parityEnvelopeRender oldEndpoint interior [])
        (parityEnvelopeRender oldEndpoint
          (oldEndpoint :: newEndpoint :: trailing) []) :=
    listDerivesParityEnvelopeInteriorPermutation
      oldEndpoint [] arrange
  have switch :
      ListDerives
        (parityEnvelopeRender oldEndpoint
          (oldEndpoint :: newEndpoint :: trailing) [])
        (parityEnvelopeRender newEndpoint
          (oldEndpoint :: newEndpoint :: trailing) []) := by
    simpa [parityEnvelopeRender, Word.toList_singleton,
      List.append_assoc] using
        listDerivesOddOddAnchorSwitch
          (Word.singleton oldEndpoint)
          (Word.singleton newEndpoint) trailing
  have arrangeTarget :
      ListDerives
        (parityEnvelopeRender newEndpoint interior [])
        (parityEnvelopeRender newEndpoint
          (oldEndpoint :: newEndpoint :: trailing) []) :=
    listDerivesParityEnvelopeInteriorPermutation
      newEndpoint [] arrange
  have derivation :
      ListDerives
        (parityEnvelopeRender oldEndpoint interior [])
        (parityEnvelopeRender newEndpoint interior []) :=
    ListDerives.trans arrangeSource <|
      ListDerives.trans switch <|
        ListDerives.symm arrangeTarget
  have sourceProfileArrange :
      (parityEnvelopeReducedProfile oldEndpoint interior).Perm
        (parityEnvelopeReducedProfile oldEndpoint
          (oldEndpoint :: newEndpoint :: trailing)) :=
    parityEnvelopeReducedProfile_perm_of_interior_perm
      oldEndpoint arrange
  have targetProfileArrange :
      (parityEnvelopeReducedProfile newEndpoint interior).Perm
        (parityEnvelopeReducedProfile newEndpoint
          (oldEndpoint :: newEndpoint :: trailing)) :=
    parityEnvelopeReducedProfile_perm_of_interior_perm
      newEndpoint arrange
  have profilePermutation :
      (parityEnvelopeReducedProfile oldEndpoint interior).Perm
        (parityEnvelopeReducedProfile newEndpoint interior) :=
    sourceProfileArrange.trans <|
      (oddOddAnchorSwitch_reducedProfile_perm
        oldEndpoint newEndpoint trailing).trans
          targetProfileArrange.symm
  refine ⟨interior, derivation, profilePermutation, ?_⟩
  refine
    { endpoint_count_le_one := by omega
      other_count_le_two := ?_ }
  intro tested testedNeNew
  by_cases testedEqOld : tested = oldEndpoint
  · subst tested
    exact Nat.le_trans reduced.endpoint_count_le_one (by omega)
  · exact reduced.other_count_le_two tested testedEqOld

private theorem exists_retarget_evenEven
    {oldEndpoint newEndpoint : Nat} {interior : List Nat}
    (different : oldEndpoint ≠ newEndpoint)
    (oldCount : interior.count oldEndpoint = 0)
    (newCount : interior.count newEndpoint = 2)
    (newMember : newEndpoint ∈ interior)
    (reduced :
      ParityEnvelopeInteriorReduced oldEndpoint interior) :
    ∃ targetInterior,
      ListDerives
          (parityEnvelopeRender oldEndpoint interior [])
          (parityEnvelopeRender newEndpoint targetInterior []) ∧
        (parityEnvelopeReducedProfile oldEndpoint interior).Perm
          (parityEnvelopeReducedProfile newEndpoint targetInterior) ∧
        ParityEnvelopeInteriorReduced
          newEndpoint targetInterior := by
  have newCountAfterOne :
      (interior.erase newEndpoint).count newEndpoint = 1 := by
    rw [List.count_erase_self, newCount]
  have newMemberAfterOne :
      newEndpoint ∈ interior.erase newEndpoint :=
    List.count_pos_iff.mp (by omega)
  let trailing :=
    (interior.erase newEndpoint).erase newEndpoint
  have arrange :
      interior.Perm
        (newEndpoint :: newEndpoint :: trailing) :=
    (List.perm_cons_erase newMember).trans <|
      List.Perm.cons newEndpoint <| by
        simpa [trailing] using
          List.perm_cons_erase newMemberAfterOne
  have arrangeSource :
      ListDerives
        (parityEnvelopeRender oldEndpoint interior [])
        (parityEnvelopeRender oldEndpoint
          (newEndpoint :: newEndpoint :: trailing) []) :=
    listDerivesParityEnvelopeInteriorPermutation
      oldEndpoint [] arrange
  have switch :
      ListDerives
        (parityEnvelopeRender oldEndpoint
          (newEndpoint :: newEndpoint :: trailing) [])
        (parityEnvelopeRender newEndpoint
          (oldEndpoint :: oldEndpoint :: trailing) []) := by
    simpa [parityEnvelopeRender, Word.toList_singleton,
      List.append_assoc] using
        listDerivesEvenEvenAnchorSwitch
          (Word.singleton oldEndpoint)
          (Word.singleton newEndpoint) trailing
  have derivation :
      ListDerives
        (parityEnvelopeRender oldEndpoint interior [])
        (parityEnvelopeRender newEndpoint
          (oldEndpoint :: oldEndpoint :: trailing) []) :=
    ListDerives.trans arrangeSource switch
  have profilePermutation :
      (parityEnvelopeReducedProfile oldEndpoint interior).Perm
        (parityEnvelopeReducedProfile newEndpoint
          (oldEndpoint :: oldEndpoint :: trailing)) :=
    (parityEnvelopeReducedProfile_perm_of_interior_perm
      oldEndpoint arrange).trans
        (evenEvenAnchorSwitch_reducedProfile_perm
          oldEndpoint newEndpoint trailing)
  refine
    ⟨oldEndpoint :: oldEndpoint :: trailing,
      derivation, profilePermutation, ?_⟩
  refine
    { endpoint_count_le_one := ?_
      other_count_le_two := ?_ }
  · have counts :=
      (List.perm_iff_count.mp arrange) newEndpoint
    simp [newCount] at counts
    simp [different, Ne.symm different]
    omega
  · intro tested testedNeNew
    by_cases testedEqOld : tested = oldEndpoint
    · subst tested
      have counts :=
        (List.perm_iff_count.mp arrange) oldEndpoint
      simp [oldCount, different, Ne.symm different] at counts ⊢
      omega
    · have sourceBound :=
        reduced.other_count_le_two tested testedEqOld
      have counts :=
        (List.perm_iff_count.mp arrange) tested
      simp [testedEqOld, testedNeNew, Ne.symm testedEqOld,
        Ne.symm testedNeNew] at counts ⊢
      omega

private theorem exists_retarget_oddEven
    {oldEndpoint newEndpoint : Nat} {interior : List Nat}
    (different : oldEndpoint ≠ newEndpoint)
    (oldCount : interior.count oldEndpoint = 1)
    (newCount : interior.count newEndpoint = 2)
    (reduced :
      ParityEnvelopeInteriorReduced oldEndpoint interior) :
    ∃ targetInterior,
      ListDerives
          (parityEnvelopeRender oldEndpoint interior [])
          (parityEnvelopeRender newEndpoint targetInterior []) ∧
        (parityEnvelopeReducedProfile oldEndpoint interior).Perm
          (parityEnvelopeReducedProfile newEndpoint targetInterior) ∧
        ParityEnvelopeInteriorReduced
          newEndpoint targetInterior := by
  have oldMember : oldEndpoint ∈ interior :=
    List.count_pos_iff.mp (by omega)
  have newCountAfterOld :
      (interior.erase oldEndpoint).count newEndpoint = 2 := by
    rw [List.count_erase_of_ne (Ne.symm different), newCount]
  have firstNewMember :
      newEndpoint ∈ interior.erase oldEndpoint :=
    List.count_pos_iff.mp (by omega)
  have newCountAfterOne :
      ((interior.erase oldEndpoint).erase newEndpoint).count
          newEndpoint = 1 := by
    rw [List.count_erase_self, newCountAfterOld]
  have secondNewMember :
      newEndpoint ∈
        (interior.erase oldEndpoint).erase newEndpoint :=
    List.count_pos_iff.mp (by omega)
  let trailing :=
    ((interior.erase oldEndpoint).erase newEndpoint).erase newEndpoint
  have arrange :
      interior.Perm
        (oldEndpoint :: newEndpoint :: newEndpoint :: trailing) :=
    (List.perm_cons_erase oldMember).trans <|
      List.Perm.cons oldEndpoint <|
        (List.perm_cons_erase firstNewMember).trans <|
          List.Perm.cons newEndpoint <| by
            simpa [trailing] using
              List.perm_cons_erase secondNewMember
  have arrangeSource :
      ListDerives
        (parityEnvelopeRender oldEndpoint interior [])
        (parityEnvelopeRender oldEndpoint
          (oldEndpoint :: newEndpoint :: newEndpoint :: trailing) []) :=
    listDerivesParityEnvelopeInteriorPermutation
      oldEndpoint [] arrange
  have switch :
      ListDerives
        (parityEnvelopeRender oldEndpoint
          (oldEndpoint :: newEndpoint :: newEndpoint :: trailing) [])
        (parityEnvelopeRender newEndpoint
          (oldEndpoint :: trailing) []) := by
    simpa [parityEnvelopeRender, Word.toList_singleton,
      List.append_assoc] using
        listDerivesOddEvenAnchorSwitch
          (Word.singleton oldEndpoint)
          (Word.singleton newEndpoint) trailing
  have derivation :
      ListDerives
        (parityEnvelopeRender oldEndpoint interior [])
        (parityEnvelopeRender newEndpoint
          (oldEndpoint :: trailing) []) :=
    ListDerives.trans arrangeSource switch
  have profilePermutation :
      (parityEnvelopeReducedProfile oldEndpoint interior).Perm
        (parityEnvelopeReducedProfile newEndpoint
          (oldEndpoint :: trailing)) :=
    (parityEnvelopeReducedProfile_perm_of_interior_perm
      oldEndpoint arrange).trans
        (oddEvenAnchorSwitch_reducedProfile_perm
          oldEndpoint newEndpoint trailing)
  refine
    ⟨oldEndpoint :: trailing,
      derivation, profilePermutation, ?_⟩
  refine
    { endpoint_count_le_one := ?_
      other_count_le_two := ?_ }
  · have counts :=
      (List.perm_iff_count.mp arrange) newEndpoint
    simp [newCount, different, Ne.symm different] at counts ⊢
    omega
  · intro tested testedNeNew
    by_cases testedEqOld : tested = oldEndpoint
    · subst tested
      have counts :=
        (List.perm_iff_count.mp arrange) oldEndpoint
      simp [oldCount, different, Ne.symm different] at counts ⊢
      omega
    · have sourceBound :=
        reduced.other_count_le_two tested testedEqOld
      have counts :=
        (List.perm_iff_count.mp arrange) tested
      simp [testedEqOld, testedNeNew, Ne.symm testedEqOld,
        Ne.symm testedNeNew] at counts ⊢
      omega

private theorem exists_retarget_evenOdd
    {oldEndpoint newEndpoint : Nat} {interior : List Nat}
    (different : oldEndpoint ≠ newEndpoint)
    (oldCount : interior.count oldEndpoint = 0)
    (newCount : interior.count newEndpoint = 1)
    (newMember : newEndpoint ∈ interior)
    (reduced :
      ParityEnvelopeInteriorReduced oldEndpoint interior) :
    ∃ targetInterior,
      ListDerives
          (parityEnvelopeRender oldEndpoint interior [])
          (parityEnvelopeRender newEndpoint targetInterior []) ∧
        (parityEnvelopeReducedProfile oldEndpoint interior).Perm
          (parityEnvelopeReducedProfile newEndpoint targetInterior) ∧
        ParityEnvelopeInteriorReduced
          newEndpoint targetInterior := by
  let trailing := interior.erase newEndpoint
  have arrange :
      interior.Perm (newEndpoint :: trailing) := by
    simpa [trailing] using List.perm_cons_erase newMember
  have arrangeSource :
      ListDerives
        (parityEnvelopeRender oldEndpoint interior [])
        (parityEnvelopeRender oldEndpoint
          (newEndpoint :: trailing) []) :=
    listDerivesParityEnvelopeInteriorPermutation
      oldEndpoint [] arrange
  have switch :
      ListDerives
        (parityEnvelopeRender oldEndpoint
          (newEndpoint :: trailing) [])
        (parityEnvelopeRender newEndpoint
          (newEndpoint :: oldEndpoint :: oldEndpoint :: trailing) []) := by
    simpa [parityEnvelopeRender, Word.toList_singleton,
      List.append_assoc] using
        listDerivesEvenOddAnchorSwitch
          (Word.singleton oldEndpoint)
          (Word.singleton newEndpoint) trailing
  have derivation :
      ListDerives
        (parityEnvelopeRender oldEndpoint interior [])
        (parityEnvelopeRender newEndpoint
          (newEndpoint :: oldEndpoint :: oldEndpoint :: trailing) []) :=
    ListDerives.trans arrangeSource switch
  have profilePermutation :
      (parityEnvelopeReducedProfile oldEndpoint interior).Perm
        (parityEnvelopeReducedProfile newEndpoint
          (newEndpoint :: oldEndpoint :: oldEndpoint :: trailing)) :=
    (parityEnvelopeReducedProfile_perm_of_interior_perm
      oldEndpoint arrange).trans
        (evenOddAnchorSwitch_reducedProfile_perm
          oldEndpoint newEndpoint trailing)
  refine
    ⟨newEndpoint :: oldEndpoint :: oldEndpoint :: trailing,
      derivation, profilePermutation, ?_⟩
  refine
    { endpoint_count_le_one := ?_
      other_count_le_two := ?_ }
  · have counts :=
      (List.perm_iff_count.mp arrange) newEndpoint
    simp [newCount, different, Ne.symm different] at counts ⊢
    omega
  · intro tested testedNeNew
    by_cases testedEqOld : tested = oldEndpoint
    · subst tested
      have counts :=
        (List.perm_iff_count.mp arrange) oldEndpoint
      simp [oldCount, different, Ne.symm different] at counts ⊢
      omega
    · have sourceBound :=
        reduced.other_count_le_two tested testedEqOld
      have counts :=
        (List.perm_iff_count.mp arrange) tested
      simp [testedEqOld, testedNeNew, Ne.symm testedEqOld,
        Ne.symm testedNeNew] at counts ⊢
      omega

/-- Retarget a reduced closed parity envelope to any different endpoint
already supported by its interior.

The four possible old/new interior multiplicities are `0/1`, `0/2`, `1/1`,
and `1/2`. After an interior permutation, they are exactly the existing
even/odd, even/even, odd/odd, and odd/even anchor-switch shapes. The returned
interior is reduced relative to the new endpoint, and the canonical
positive-parity profiles of the source and target are exactly `List.Perm`
equivalent. -/
theorem exists_reducedParityEnvelopeRetarget
    {oldEndpoint newEndpoint : Nat} {interior : List Nat}
    (different : oldEndpoint ≠ newEndpoint)
    (newMember : newEndpoint ∈ interior)
    (reduced :
      ParityEnvelopeInteriorReduced oldEndpoint interior) :
    ∃ targetInterior,
      ListDerives
          (parityEnvelopeRender oldEndpoint interior [])
          (parityEnvelopeRender newEndpoint targetInterior []) ∧
        (parityEnvelopeReducedProfile oldEndpoint interior).Perm
          (parityEnvelopeReducedProfile newEndpoint targetInterior) ∧
        ParityEnvelopeInteriorReduced
          newEndpoint targetInterior := by
  have newCountPositive : 0 < interior.count newEndpoint :=
    List.count_pos_iff.mpr newMember
  have newCountLeTwo :
      interior.count newEndpoint ≤ 2 :=
    reduced.other_count_le_two newEndpoint
      (Ne.symm different)
  have oldCountLeOne :
      interior.count oldEndpoint ≤ 1 :=
    reduced.endpoint_count_le_one
  have oldCountCases :
      interior.count oldEndpoint = 0 ∨
        interior.count oldEndpoint = 1 := by
    omega
  have newCountCases :
      interior.count newEndpoint = 1 ∨
        interior.count newEndpoint = 2 := by
    omega
  rcases oldCountCases with oldCount | oldCount
  · rcases newCountCases with newCount | newCount
    · exact
        exists_retarget_evenOdd
          different oldCount newCount newMember reduced
    · exact
        exists_retarget_evenEven
          different oldCount newCount newMember reduced
  · rcases newCountCases with newCount | newCount
    · exact
        exists_retarget_oddOdd
          different oldCount newCount reduced
    · exact
        exists_retarget_oddEven
          different oldCount newCount reduced

end SemigroupBasis.CoRoots.S5_442
