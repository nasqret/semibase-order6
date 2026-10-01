import SemigroupBasis.CoRoots.Order6LeeZhangCondition14Canonical
import SemigroupBasis.CoRoots.Order6LeeZhangCondition14ConnectedNormalForm

/-!
# Endpoint adjustment for Lee--Zhang Condition 14

The unrestricted parity normalizer does not privilege the closing endpoint.
This file isolates the final local adjustment.  The endpoint block is absent,
single, or double in a `ParityInitialNormal` list.  A singleton is moved to the
front with the gather law, while a double block is deleted with (9.2a).  The
result is exactly the anchor block used by `componentInitialParityRender`.
-/

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6LeeZhangAmbientConditions.Condition14

open SemigroupBasis
open SemigroupBasis.Examples

private abbrev ListDerives : List Nat → List Nat → Prop :=
  SemigroupBasis.CoRoots.S5_107.ListDerives basis

private abbrev listWordOfCons :=
  SemigroupBasis.CoRoots.S5_107.listWordOfCons

private def instantiateThreeWords
    (first second third : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | n + 3 => Word.singleton (n + 3)

private def endpointGatherLhs : Word Nat := ⟨0, [1, 0, 2, 0]⟩
private def endpointGatherRhs : Word Nat := ⟨0, [0, 1, 2, 0]⟩

private def endpointGatherLaw : Identity Nat :=
  ⟨endpointGatherLhs, endpointGatherRhs⟩

private theorem endpointGatherLaw_mem : endpointGatherLaw ∈ basis := by
  decide

private theorem derivesEndpointGather
    (x y z : Word Nat) :
    Derives basis ((((x ++ y) ++ x) ++ z) ++ x)
      ((((x ++ x) ++ y) ++ z) ++ x) := by
  have base :
      Derives basis endpointGatherLhs endpointGatherRhs :=
    Derives.fromBasis endpointGatherLaw_mem
  have substituted :=
    Derives.subst base (instantiateThreeWords x y z)
  simpa [endpointGatherLaw, endpointGatherLhs, endpointGatherRhs,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

private def squareTransferLhs : Word Nat := ⟨0, [0, 1, 0]⟩
private def squareTransferRhs : Word Nat := ⟨0, [1, 0, 0]⟩

private def squareTransferLaw : Identity Nat :=
  ⟨squareTransferLhs, squareTransferRhs⟩

private theorem squareTransferLaw_mem : squareTransferLaw ∈ basis := by
  decide

private theorem derivesSquareTransfer
    (x y : Word Nat) :
    Derives basis (((x ++ x) ++ y) ++ x)
      (((x ++ y) ++ x) ++ x) := by
  have base :
      Derives basis squareTransferLhs squareTransferRhs :=
    Derives.fromBasis squareTransferLaw_mem
  have substituted :=
    Derives.subst base (instantiateThreeWords x y y)
  simpa [squareTransferLaw, squareTransferLhs, squareTransferRhs,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

private theorem listDerivesMoveEndpointSingleton
    (endpoint : Nat) (before after : List Nat) :
    ListDerives
      ([endpoint] ++ before ++ [endpoint] ++ after ++ [endpoint])
      ([endpoint, endpoint] ++ before ++ after ++ [endpoint]) := by
  cases before with
  | nil =>
      simpa [List.append_assoc] using
        (SemigroupBasis.CoRoots.S5_107.ListDerives.refl
          (basis := basis) ([endpoint, endpoint] ++ after ++ [endpoint]))
  | cons beforeHead beforeTail =>
      let beforeWord := listWordOfCons beforeHead beforeTail
      cases after with
      | nil =>
          have moved :=
            SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
              (basis := basis)
              (derivesSquareTransfer
                (Word.singleton endpoint) beforeWord).symm
          simpa [beforeWord, listWordOfCons, Word.singleton,
            Word.toList, Word.append, List.append_assoc] using moved
      | cons afterHead afterTail =>
          let afterWord := listWordOfCons afterHead afterTail
          have moved :=
            SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
              (basis := basis)
              (derivesEndpointGather
                (Word.singleton endpoint) beforeWord afterWord)
          simpa [beforeWord, afterWord, listWordOfCons, Word.singleton,
            Word.toList, Word.append, List.append_assoc] using moved

private inductive EndpointBlockCase (endpoint : Nat) : List Nat → Prop
  | absent {letters : List Nat} :
      endpoint ∉ letters → EndpointBlockCase endpoint letters
  | single (before after : List Nat) :
      endpoint ∉ before → endpoint ∉ after →
        EndpointBlockCase endpoint
          (before ++ [endpoint] ++ after)
  | double (before after : List Nat) :
      endpoint ∉ before → endpoint ∉ after →
        EndpointBlockCase endpoint
          (before ++ [endpoint, endpoint] ++ after)

private theorem parityInitialNormal_endpointBlockCase
    {letters : List Nat} (normal : ParityInitialNormal letters)
    (endpoint : Nat) : EndpointBlockCase endpoint letters := by
  induction normal with
  | nil =>
      exact EndpointBlockCase.absent (by simp)
  | single letter remaining remainingNormal letterAbsent ih =>
      by_cases equal : letter = endpoint
      · subst letter
        simpa using
          (EndpointBlockCase.single (endpoint := endpoint) [] remaining
            (by simp) letterAbsent)
      · cases ih with
        | absent endpointAbsent =>
            exact EndpointBlockCase.absent
              (by simp [Ne.symm equal, endpointAbsent])
        | single before after beforeAbsent afterAbsent =>
            simpa [List.append_assoc] using
              (EndpointBlockCase.single (endpoint := endpoint)
                (letter :: before) after
                (by simp [Ne.symm equal, beforeAbsent]) afterAbsent)
        | double before after beforeAbsent afterAbsent =>
            simpa [List.append_assoc] using
              (EndpointBlockCase.double (endpoint := endpoint)
                (letter :: before) after
                (by simp [Ne.symm equal, beforeAbsent]) afterAbsent)
  | double letter remaining remainingNormal letterAbsent ih =>
      by_cases equal : letter = endpoint
      · subst letter
        simpa using
          (EndpointBlockCase.double (endpoint := endpoint) [] remaining
            (by simp) letterAbsent)
      · cases ih with
        | absent endpointAbsent =>
            exact EndpointBlockCase.absent
              (by simp [Ne.symm equal, endpointAbsent])
        | single before after beforeAbsent afterAbsent =>
            simpa [List.append_assoc] using
              (EndpointBlockCase.single (endpoint := endpoint)
                (letter :: letter :: before) after
                (by simp [Ne.symm equal, beforeAbsent]) afterAbsent)
        | double before after beforeAbsent afterAbsent =>
            simpa [List.append_assoc] using
              (EndpointBlockCase.double (endpoint := endpoint)
                (letter :: letter :: before) after
                (by simp [Ne.symm equal, beforeAbsent]) afterAbsent)

private theorem filter_ne_eq_self
    {endpoint : Nat} {letters : List Nat}
    (endpointAbsent : endpoint ∉ letters) :
    letters.filter (fun letter => decide (letter ≠ endpoint)) = letters := by
  apply List.filter_eq_self.mpr
  intro letter member
  have different : letter ≠ endpoint := by
    intro equal
    subst letter
    exact endpointAbsent member
  simp [different]

/-- Adjust a parity-initial interior to the anchor convention used by the
Condition 14 component renderer.  The filter removes the unique endpoint block
and leaves every non-endpoint block in its existing first-occurrence order. -/
theorem listDerivesClosedEndpointAdjusted
    (source : List Nat) (endpoint : Nat) (normal : List Nat)
    (normalForm : ParityInitialNormal normal)
    (sameParity :
      source.count endpoint % 2 = normal.count endpoint % 2) :
    ListDerives
      ([endpoint] ++ normal ++ [endpoint])
      (componentParityBlock source endpoint endpoint ++
        normal.filter (fun letter => decide (letter ≠ endpoint)) ++
          [endpoint]) := by
  cases parityInitialNormal_endpointBlockCase normalForm endpoint with
  | absent endpointAbsent =>
      have normalCount : normal.count endpoint = 0 :=
        List.count_eq_zero.mpr endpointAbsent
      have sourceEven : source.count endpoint % 2 = 0 := by
        simpa [normalCount] using sameParity
      rw [filter_ne_eq_self endpointAbsent]
      simpa [componentParityBlock, sourceEven,
        List.append_assoc] using
        (SemigroupBasis.CoRoots.S5_107.ListDerives.refl
          (basis := basis) ([endpoint] ++ normal ++ [endpoint]))
  | single before after beforeAbsent afterAbsent =>
      have beforeCount : before.count endpoint = 0 :=
        List.count_eq_zero.mpr beforeAbsent
      have afterCount : after.count endpoint = 0 :=
        List.count_eq_zero.mpr afterAbsent
      have sourceOdd : source.count endpoint % 2 = 1 := by
        simpa [List.count_append, beforeCount, afterCount] using sameParity
      have filteredNormal :
          (before ++ [endpoint] ++ after).filter
              (fun letter => decide (letter ≠ endpoint)) =
            before ++ after := by
        simp only [List.filter_append]
        rw [filter_ne_eq_self beforeAbsent,
          filter_ne_eq_self afterAbsent]
        simp
      rw [filteredNormal]
      simpa [componentParityBlock, sourceOdd,
        List.append_assoc] using
        listDerivesMoveEndpointSingleton endpoint before after
  | double before after beforeAbsent afterAbsent =>
      have beforeCount : before.count endpoint = 0 :=
        List.count_eq_zero.mpr beforeAbsent
      have afterCount : after.count endpoint = 0 :=
        List.count_eq_zero.mpr afterAbsent
      have sourceEven : source.count endpoint % 2 = 0 := by
        simpa [List.count_append, beforeCount, afterCount] using sameParity
      have filteredNormal :
          (before ++ [endpoint, endpoint] ++ after).filter
              (fun letter => decide (letter ≠ endpoint)) =
            before ++ after := by
        simp only [List.filter_append]
        rw [filter_ne_eq_self beforeAbsent,
          filter_ne_eq_self afterAbsent]
        simp
      rw [filteredNormal]
      simpa [componentParityBlock, sourceEven,
        List.append_assoc] using
        listDerivesContextSquareDeletion endpoint before after

/-- Every non-singleton connected component derives to the exact endpoint
block selected by `componentInitialParityRender`; only the non-endpoint parity
blocks remain to be identified with the renderer's ordered payload. -/
theorem existsClosedEndpointAdjustedNormal
    {head : Nat} {tail : List Nat}
    (connected : ConnectedComponentSupportConnected (head :: tail))
    (tailNonempty : tail ≠ []) :
    ∃ interior,
      ListDerives (head :: tail)
        (componentParityBlock (head :: tail) head head ++
          (parityInitialNormalList interior).filter
            (fun letter => decide (letter ≠ head)) ++ [head]) := by
  obtain ⟨interior, closed⟩ :=
    existsClosedParityInteriorNormal connected tailNonempty
  let normal := parityInitialNormalList interior
  have closedNormal :
      ListDerives (head :: tail) ([head] ++ normal ++ [head]) := by
    simpa [normal] using closed
  have preserved :=
    (derives_sameComponentInitialParitySignature
      (SemigroupBasis.CoRoots.S5_107.ListDerives.toWord closedNormal)).parity
        head
  have preservedList :
      (head :: tail).count head % 2 =
        ([head] ++ normal ++ [head]).count head % 2 := by
    change
      (head :: tail).count head % 2 =
        (head :: normal ++ [head]).count head % 2 at preserved
    simpa [List.append_assoc] using preserved
  have targetParity :
      ([head] ++ normal ++ [head]).count head % 2 =
        normal.count head % 2 := by
    simp only [List.count_append, List.count_cons_self,
      List.count_nil]
    omega
  have sameParity :
      (head :: tail).count head % 2 = normal.count head % 2 :=
    preservedList.trans targetParity
  have adjusted :=
    listDerivesClosedEndpointAdjusted (head :: tail) head normal
      (by simpa [normal] using parityInitialNormalList_normal interior)
      sameParity
  exact ⟨interior, closedNormal.trans (by
    simpa [normal] using adjusted)⟩

private theorem parityInitialNormal_filter_ne
    {letters : List Nat} (normal : ParityInitialNormal letters)
    (endpoint : Nat) :
    ParityInitialNormal
      (letters.filter (fun letter => decide (letter ≠ endpoint))) := by
  induction normal with
  | nil =>
      exact ParityInitialNormal.nil
  | single letter remaining remainingNormal letterAbsent ih =>
      by_cases equal : letter = endpoint
      · subst letter
        have remainingFilter :
            remaining.filter
                (fun candidate => decide (candidate ≠ endpoint)) =
              remaining :=
          filter_ne_eq_self letterAbsent
        rw [List.filter_cons_of_neg (by simp), remainingFilter]
        exact remainingNormal
      · have letterAbsentFiltered :
            letter ∉ remaining.filter
              (fun candidate => decide (candidate ≠ endpoint)) := by
          simp only [List.mem_filter]
          exact fun member => letterAbsent member.1
        simpa [equal] using
          ParityInitialNormal.single letter
            (remaining.filter
              (fun candidate => decide (candidate ≠ endpoint)))
            ih letterAbsentFiltered
  | double letter remaining remainingNormal letterAbsent ih =>
      by_cases equal : letter = endpoint
      · subst letter
        have remainingFilter :
            remaining.filter
                (fun candidate => decide (candidate ≠ endpoint)) =
              remaining :=
          filter_ne_eq_self letterAbsent
        rw [List.filter_cons_of_neg (by simp),
          List.filter_cons_of_neg (by simp), remainingFilter]
        exact remainingNormal
      · have letterAbsentFiltered :
            letter ∉ remaining.filter
              (fun candidate => decide (candidate ≠ endpoint)) := by
          simp only [List.mem_filter]
          exact fun member => letterAbsent member.1
        simpa [equal] using
          ParityInitialNormal.double letter
            (remaining.filter
              (fun candidate => decide (candidate ≠ endpoint)))
            ih letterAbsentFiltered

private theorem mem_firstOccurrenceSequence_iff
    (selected : Nat) :
    ∀ letters : List Nat,
      selected ∈ firstOccurrenceSequence letters ↔ selected ∈ letters
  | [] => by simp [firstOccurrenceSequence]
  | letter :: remaining => by
      by_cases equal : selected = letter
      · subst letter
        simp [firstOccurrenceSequence]
      · simp [firstOccurrenceSequence, equal,
          mem_firstOccurrenceSequence_iff selected remaining]

private theorem filter_filter_ne_comm
    (keep : Nat → Bool) (selected : Nat) (letters : List Nat) :
    (letters.filter keep).filter
        (fun letter => decide (letter ≠ selected)) =
      (letters.filter
        (fun letter => decide (letter ≠ selected))).filter keep := by
  rw [List.filter_filter, List.filter_filter]
  apply List.filter_congr
  intro letter _
  exact Bool.and_comm _ _

private theorem filter_ne_then_keep_of_drop
    (keep : Nat → Bool) (selected : Nat)
    (dropped : ¬keep selected) (letters : List Nat) :
    (letters.filter
        (fun letter => decide (letter ≠ selected))).filter keep =
      letters.filter keep := by
  rw [List.filter_filter]
  apply List.filter_congr
  intro letter _
  by_cases equal : letter = selected
  · subst letter
    simp [dropped]
  · simp [equal]

private theorem condition14FirstOccurrenceSequence_filter
    (keep : Nat → Bool) :
    ∀ letters : List Nat,
      firstOccurrenceSequence (letters.filter keep) =
        (firstOccurrenceSequence letters).filter keep
  | [] => rfl
  | letter :: remaining => by
      by_cases kept : keep letter
      · rw [List.filter_cons, if_pos kept,
          firstOccurrenceSequence, firstOccurrenceSequence,
          condition14FirstOccurrenceSequence_filter keep remaining,
          List.filter_cons, if_pos kept]
        exact congrArg (List.cons letter) <|
          filter_filter_ne_comm keep letter
            (firstOccurrenceSequence remaining)
      · rw [List.filter_cons, if_neg kept,
          condition14FirstOccurrenceSequence_filter keep remaining,
          firstOccurrenceSequence, List.filter_cons, if_neg kept]
        exact
          (filter_ne_then_keep_of_drop keep letter kept
            (firstOccurrenceSequence remaining)).symm

private theorem count_filter_ne_of_ne
    {endpoint selected : Nat} (different : selected ≠ endpoint)
    (letters : List Nat) :
    (letters.filter
      (fun letter => decide (letter ≠ endpoint))).count selected =
        letters.count selected := by
  induction letters with
  | nil => rfl
  | cons letter remaining ih =>
      by_cases equal : letter = endpoint
      · subst letter
        rw [List.filter_cons_of_neg (by simp),
          List.count_cons_of_ne (Ne.symm different)]
        exact ih
      · rw [List.filter_cons_of_pos (by simpa)]
        simp only [List.count_cons]
        rw [ih]

/-- A head-free parity-normal payload is literally the flat-map of its
first-occurrence sequence by the non-anchor blocks of the component renderer. -/
private theorem parityInitialNormal_eq_componentPayloadRender
    (source : List Nat) (anchor : Nat) {payload : List Nat}
    (normal : ParityInitialNormal payload)
    (anchorAbsent : anchor ∉ payload)
    (sameParity : ∀ letter, letter ∈ payload →
      source.count letter % 2 = payload.count letter % 2) :
    payload =
      (firstOccurrenceSequence payload).flatMap
        (componentParityBlock source anchor) := by
  induction normal generalizing anchor with
  | nil =>
      simp [firstOccurrenceSequence]
  | single letter remaining remainingNormal letterAbsent ih =>
      have letterNeAnchor : letter ≠ anchor := by
        intro equal
        subst letter
        exact anchorAbsent (by simp)
      have anchorAbsentRemaining : anchor ∉ remaining := by
        intro member
        exact anchorAbsent (by simp [member])
      have remainingParity : ∀ selected, selected ∈ remaining →
          source.count selected % 2 = remaining.count selected % 2 := by
        intro selected member
        have selectedNeLetter : selected ≠ letter := by
          intro equal
          subst selected
          exact letterAbsent member
        simpa [List.count_cons_of_ne (Ne.symm selectedNeLetter)] using
          sameParity selected (by simp [member])
      have renderedRemaining :=
        ih anchor anchorAbsentRemaining remainingParity
      have letterNotInitials :
          letter ∉ firstOccurrenceSequence remaining := by
        intro member
        exact letterAbsent <|
          (mem_firstOccurrenceSequence_iff letter remaining).1 member
      have initialsShape :
          firstOccurrenceSequence (letter :: remaining) =
            letter :: firstOccurrenceSequence remaining := by
        change
          letter :: (firstOccurrenceSequence remaining).filter
              (fun candidate => decide (candidate ≠ letter)) =
            letter :: firstOccurrenceSequence remaining
        rw [filter_ne_eq_self letterNotInitials]
      have sourceOdd : source.count letter % 2 = 1 := by
        simpa [List.count_eq_zero.mpr letterAbsent] using
          sameParity letter (by simp)
      rw [initialsShape, List.flatMap_cons]
      have blockEq :
          componentParityBlock source anchor letter = [letter] := by
        simp [componentParityBlock, letterNeAnchor, sourceOdd]
      rw [blockEq, ← renderedRemaining]
      simp
  | double letter remaining remainingNormal letterAbsent ih =>
      have letterNeAnchor : letter ≠ anchor := by
        intro equal
        subst letter
        exact anchorAbsent (by simp)
      have anchorAbsentRemaining : anchor ∉ remaining := by
        intro member
        exact anchorAbsent (by simp [member])
      have remainingParity : ∀ selected, selected ∈ remaining →
          source.count selected % 2 = remaining.count selected % 2 := by
        intro selected member
        have selectedNeLetter : selected ≠ letter := by
          intro equal
          subst selected
          exact letterAbsent member
        simpa [List.count_cons_of_ne (Ne.symm selectedNeLetter)] using
          sameParity selected (by simp [member])
      have renderedRemaining :=
        ih anchor anchorAbsentRemaining remainingParity
      have letterNotInitials :
          letter ∉ firstOccurrenceSequence remaining := by
        intro member
        exact letterAbsent <|
          (mem_firstOccurrenceSequence_iff letter remaining).1 member
      have initialsShape :
          firstOccurrenceSequence (letter :: letter :: remaining) =
            letter :: firstOccurrenceSequence remaining := by
        have innerShape :
            firstOccurrenceSequence (letter :: remaining) =
              letter :: firstOccurrenceSequence remaining := by
          change
            letter :: (firstOccurrenceSequence remaining).filter
                (fun candidate => decide (candidate ≠ letter)) =
              letter :: firstOccurrenceSequence remaining
          rw [filter_ne_eq_self letterNotInitials]
        change
          letter :: (firstOccurrenceSequence (letter :: remaining)).filter
              (fun candidate => decide (candidate ≠ letter)) =
            letter :: firstOccurrenceSequence remaining
        rw [innerShape, List.filter_cons_of_neg (by simp),
          filter_ne_eq_self letterNotInitials]
      have sourceEven : source.count letter % 2 = 0 := by
        simpa [List.count_eq_zero.mpr letterAbsent] using
          sameParity letter (by simp)
      rw [initialsShape, List.flatMap_cons]
      have blockEq :
          componentParityBlock source anchor letter = [letter, letter] := by
        simp [componentParityBlock, letterNeAnchor, sourceEven]
      rw [blockEq, ← renderedRemaining]
      simp

private theorem firstOccurrenceSequence_restrict_ownSupport
    (component : List Nat) :
    (firstOccurrenceSequence component).filter
        (fun letter => decide
          (letter ∈ (connectedComponentSignatureOfList component).support)) =
      firstOccurrenceSequence component := by
  apply List.filter_eq_self.mpr
  intro letter member
  simp only [decide_eq_true_eq]
  rw [connectedComponentSignatureOfList_support,
    connectedComponentSortedSupport_mem_iff]
  exact (mem_firstOccurrenceSequence_iff letter component).1 member

/-- Componentwise local normalizer in the exact form consumed by the global
Condition 14 canonical renderer. -/
theorem listDerivesComponentInitialParityLocalNormal
    (component : List Nat) (nonempty : component ≠ [])
    (connected : ConnectedComponentSupportConnected component) :
    ListDerives component
      (componentInitialParityRender component
        (firstOccurrenceSequence component)
        (connectedComponentSignatureOfList component)) := by
  cases component with
  | nil =>
      contradiction
  | cons head tail =>
      cases tail with
      | nil =>
          have signatureShape :
              connectedComponentSignatureOfList [head] =
                ⟨[head], false⟩ := by
            simp [connectedComponentSignatureOfList,
              connectedComponentSortedSupport,
              connectedComponentDistinctSupport]
          simpa [componentInitialParityRender, signatureShape,
            firstOccurrenceSequence] using
            (SemigroupBasis.CoRoots.S5_107.ListDerives.refl
              (basis := basis) [head])
      | cons next remaining =>
          let source := head :: next :: remaining
          obtain ⟨interior, closed⟩ :=
            existsClosedParityInteriorNormal connected (by simp)
          let normal := parityInitialNormalList interior
          let payload :=
            normal.filter (fun letter => decide (letter ≠ head))
          have closedNormal :
              ListDerives source ([head] ++ normal ++ [head]) := by
            simpa [source, normal] using closed
          have same :=
            derives_sameComponentInitialParitySignature
              (SemigroupBasis.CoRoots.S5_107.ListDerives.toWord closedNormal)
          have sameParity :
              source.count head % 2 = normal.count head % 2 := by
            have preserved := same.parity head
            change
              source.count head % 2 =
                (head :: normal ++ [head]).count head % 2 at preserved
            have targetParity :
                (head :: normal ++ [head]).count head % 2 =
                  normal.count head % 2 := by
              simp only [List.count_append, List.count_cons_self,
                List.count_nil]
              omega
            exact preserved.trans targetParity
          have adjustedStep :=
            listDerivesClosedEndpointAdjusted source head normal
              (by simpa [normal] using
                parityInitialNormalList_normal interior)
              sameParity
          have adjusted :
              ListDerives source
                (componentParityBlock source head head ++ payload ++
                  [head]) := by
            simpa [payload] using closedNormal.trans adjustedStep
          have payloadNormal : ParityInitialNormal payload := by
            exact parityInitialNormal_filter_ne
              (by simpa [normal] using
                parityInitialNormalList_normal interior) head
          have headAbsentPayload : head ∉ payload := by
            simp [payload]
          have payloadParity : ∀ letter, letter ∈ payload →
              source.count letter % 2 = payload.count letter % 2 := by
            intro letter member
            have different : letter ≠ head := by
              intro equal
              subst letter
              exact headAbsentPayload member
            have preserved := same.parity letter
            change
              source.count letter % 2 =
                (head :: normal ++ [head]).count letter % 2 at preserved
            have payloadCount : payload.count letter = normal.count letter := by
              exact count_filter_ne_of_ne different normal
            simpa [List.count_append,
              List.count_cons_of_ne (Ne.symm different),
              payloadCount] using preserved
          have payloadRender :=
            parityInitialNormal_eq_componentPayloadRender
              source head payloadNormal headAbsentPayload payloadParity
          have closedInitials :
              firstOccurrenceSequence (head :: normal ++ [head]) =
                head :: firstOccurrenceSequence payload := by
            change
              head :: (firstOccurrenceSequence (normal ++ [head])).filter
                  (fun letter => decide (letter ≠ head)) =
                head :: firstOccurrenceSequence payload
            congr 1
            rw [← condition14FirstOccurrenceSequence_filter
              (fun letter => decide (letter ≠ head))
              (normal ++ [head])]
            have filteredTail :
                (normal ++ [head]).filter
                    (fun letter => decide (letter ≠ head)) = payload := by
              simp [payload, List.filter_append]
            rw [filteredTail]
          have sourceInitials :
              firstOccurrenceSequence source =
                head :: firstOccurrenceSequence payload := by
            have preserved := same.componentInitial.initials
            change
              firstOccurrenceSequence source =
                firstOccurrenceSequence (head :: normal ++ [head])
              at preserved
            exact preserved.trans closedInitials
          have supportRestriction :=
            firstOccurrenceSequence_restrict_ownSupport source
          have notSimple :
              ¬((connectedComponentSignatureOfList source).support.length = 1 ∧
                (connectedComponentSignatureOfList source).repeatedUnary =
                  false) := by
            rintro ⟨supportLength, repeatedFalse⟩
            obtain ⟨letter, supportShape⟩ :=
              List.length_eq_one_iff.mp supportLength
            have sortedShape :
                connectedComponentSortedSupport source = [letter] := by
              rw [← connectedComponentSignatureOfList_support]
              exact supportShape
            have repeatedTrue :
                (connectedComponentSignatureOfList source).repeatedUnary =
                  true := by
              simp [connectedComponentSignatureOfList, sortedShape, source]
            rw [repeatedTrue] at repeatedFalse
            contradiction
          have renderEq :
              componentInitialParityRender source
                  (firstOccurrenceSequence source)
                  (connectedComponentSignatureOfList source) =
                componentParityBlock source head head ++ payload ++ [head] := by
            unfold componentInitialParityRender
            rw [supportRestriction, if_neg notSimple, sourceInitials]
            change
              componentParityBlock source head head ++
                  (firstOccurrenceSequence payload).flatMap
                    (componentParityBlock source head) ++ [head] =
                componentParityBlock source head head ++ payload ++ [head]
            rw [← payloadRender]
          simpa [source, renderEq] using adjusted

end SemigroupBasis.CoRoots.Order6LeeZhangAmbientConditions.Condition14
