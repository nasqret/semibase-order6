import SemigroupBasis.Nonfinite.A2One.TwoSingletonSeparatorRigidity
import SemigroupBasis.Nonfinite.A2One.SeparatorOwnerControl

namespace SemigroupBasis.Nonfinite.A2One

open SemigroupBasis

private def pairKeep (first second value : Nat) : Bool :=
  value == first || value == second

private theorem count_filter_of_kept_local
    (letters : List Nat) (keep : Nat → Bool) (letter : Nat)
    (kept : keep letter = true) :
    (letters.filter keep).count letter = letters.count letter := by
  induction letters with
  | nil => simp
  | cons first rest ih =>
      by_cases equality : first = letter
      · subst first
        simp [kept, ih]
      · by_cases firstKept : keep first
        · simp [firstKept, equality, ih]
        · simp [firstKept, equality, ih]

private theorem pairProjection_twoLimited
    (letters : List Nat) (first second : Nat)
    (firstBound : letters.count first ≤ 2)
    (secondBound : letters.count second ≤ 2) :
    TwoLimitedList
      (letters.filter (pairKeep first second)) := by
  intro letter
  by_cases firstEquality : letter = first
  · subst letter
    rw [count_filter_of_kept_local]
    · exact firstBound
    · simp [pairKeep]
  · by_cases secondEquality : letter = second
    · subst letter
      rw [count_filter_of_kept_local]
      · exact secondBound
      · simp [pairKeep]
    · have absent :
        letter ∉ letters.filter (pairKeep first second) := by
        intro member
        have kept := (List.mem_filter.mp member).2
        simp only [pairKeep, Bool.or_eq_true, beq_iff_eq] at kept
        exact kept.elim firstEquality secondEquality
      rw [List.count_eq_zero.mpr absent]
      omega

private theorem filter_eq_singleton_of_count_eq_one_local
    (letters : List Nat) (letter : Nat)
    (countOne : letters.count letter = 1) :
    letters.filter (fun value => value == letter) = [letter] := by
  induction letters with
  | nil => simp at countOne
  | cons first rest ih =>
      by_cases equality : first = letter
      · subst first
        have restCountZero : rest.count letter = 0 := by
          simp only [List.count_cons_self] at countOne
          omega
        have restFilter :
            rest.filter (fun value => value == letter) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro value member
          simp only [beq_iff_eq]
          intro valueEq
          subst value
          exact (List.count_eq_zero.mp restCountZero) member
        simp [restFilter]
      · have restCountOne : rest.count letter = 1 := by
          simpa [equality] using countOne
        simp [equality, ih restCountOne]

private theorem anchor_indexed_separator_projection_local
    {extra marker : Nat}
    (indexed : marker < extra + 2) :
    (anchor extra).toList.filter
        (fun value => value == marker || value == extra + 2) =
      [marker, extra + 2, marker, extra + 2, marker] := by
  let keep :=
    fun value : Nat =>
      value == marker || value == extra + 2
  have separatorAbsent :
      extra + 2 ∉ List.range (extra + 2) := by
    simp
  have markerCount :
      (List.range (extra + 2)).count marker = 1 := by
    simp [indexed]
  have forwardProjection :
      (List.range (extra + 2)).filter keep = [marker] := by
    rw [show
      (List.range (extra + 2)).filter keep =
        (List.range (extra + 2)).filter
          (fun value => value == marker) by
            apply List.filter_congr
            intro value member
            have valueNeSeparator : value ≠ extra + 2 := by
              intro equality
              subst value
              exact separatorAbsent member
            simp [keep, valueNeSeparator]]
    exact
      filter_eq_singleton_of_count_eq_one_local
        (List.range (extra + 2)) marker markerCount
  have reverseProjection :
      ((List.range (extra + 2)).reverse).filter keep = [marker] := by
    simpa [List.filter_reverse, forwardProjection]
  rw [anchor_toList]
  simp [List.filter_append, forwardProjection, reverseProjection, keep]

/-- A two-letter projection is exactly reconstructible when only the two
selected letters, rather than both ambient words, are known to be
2-limited. -/
theorem
    sameDeletionMarkedDigraph_pairProjection_eq_of_localBounds
    {left right : Word Nat}
    (same : SameDeletionMarkedDigraph left right)
    (first second : Nat)
    (firstMember : first ∈ left.toList)
    (leftFirstBound : left.toList.count first ≤ 2)
    (leftSecondBound : left.toList.count second ≤ 2)
    (rightFirstBound : right.toList.count first ≤ 2)
    (rightSecondBound : right.toList.count second ≤ 2) :
    right.toList.filter
        (fun value => value == first || value == second) =
      left.toList.filter
        (fun value => value == first || value == second) := by
  let keep := pairKeep first second
  have leftNonempty :
      left.toList.filter keep ≠ [] := by
    intro empty
    have member :
        first ∈ left.toList.filter keep :=
      List.mem_filter.mpr
        ⟨firstMember, by simp [keep, pairKeep]⟩
    rw [empty] at member
    simp at member
  have rightFirstMember : first ∈ right.toList :=
    (sameDeletionMarkedDigraph_mem_iff same first).mp firstMember
  have rightNonempty :
      right.toList.filter keep ≠ [] := by
    intro empty
    have member :
        first ∈ right.toList.filter keep :=
      List.mem_filter.mpr
        ⟨rightFirstMember, by simp [keep, pairKeep]⟩
    rw [empty] at member
    simp at member
  cases leftProjection : left.toList.filter keep with
  | nil => exact False.elim (leftNonempty leftProjection)
  | cons leftHead leftTail =>
      cases rightProjection : right.toList.filter keep with
      | nil => exact False.elim (rightNonempty rightProjection)
      | cons rightHead rightTail =>
          let leftPair : Word Nat := ⟨leftHead, leftTail⟩
          let rightPair : Word Nat := ⟨rightHead, rightTail⟩
          have leftPairList :
              leftPair.toList = left.toList.filter keep := by
            rw [leftProjection]
            rfl
          have rightPairList :
              rightPair.toList = right.toList.filter keep := by
            rw [rightProjection]
            rfl
          have pairSame :
              SameDeletionMarkedDigraph leftPair rightPair := by
            intro selected
            rw [leftPairList, rightPairList]
            simpa [List.filter_filter, Bool.and_comm] using
              same (fun value => selected value && keep value)
          have leftPairLimited :
              TwoLimitedList leftPair.toList := by
            rw [leftPairList]
            exact
              pairProjection_twoLimited left.toList first second
                leftFirstBound leftSecondBound
          have rightPairLimited :
              TwoLimitedList rightPair.toList := by
            rw [rightPairList]
            exact
              pairProjection_twoLimited right.toList first second
                rightFirstBound rightSecondBound
          have pairEquality :
              rightPair = leftPair :=
            sameDeletionMarkedDigraph_eq_of_twoLimited
              pairSame leftPairLimited rightPairLimited
          have listed := congrArg Word.toList pairEquality
          rw [leftPairList, rightPairList] at listed
          simpa [keep, pairKeep] using listed

/-- Local 2-limited certificates for the selected letters suffice to recover
their exact two-letter projection. -/
theorem
    sameDeletionMarkedDigraph_pairProjection_eq_of_localCertificates
    {left right : Word Nat}
    (same : SameDeletionMarkedDigraph left right)
    (first second : Nat)
    (firstMember : first ∈ left.toList)
    (leftFirstBound : left.toList.count first ≤ 2)
    (leftSecondBound : left.toList.count second ≤ 2)
    (firstCertificate :
      LocalTwoLimitedCertificate left first)
    (secondCertificate :
      LocalTwoLimitedCertificate left second) :
    right.toList.filter
        (fun value => value == first || value == second) =
      left.toList.filter
        (fun value => value == first || value == second) := by
  simpa [pairKeep] using
    sameDeletionMarkedDigraph_pairProjection_eq_of_localBounds
      same first second firstMember leftFirstBound leftSecondBound
      (firstCertificate.right_count_le_two same)
      (secondCertificate.right_count_le_two same)

/-- For a twice-occurring source variable whose image omits the separator,
filtering the mapped two-occurrence split to the image head and separator
produces the fixed five-letter anchor projection.  The three possible
placements of the two displayed head markers are the remaining
nonseparator cases. -/
theorem preimage_two_occurrence_marker_separator_projection
    {bound : Nat} {word : Word Nat}
    {substitution : Nat → Word Nat}
    (mapped : word.bind substitution = anchor (3 * bound))
    {sourceLetter : Nat}
    (sourceCount : word.toList.count sourceLetter = 2)
    (separatorAbsent :
      3 * bound + 2 ∉ (substitution sourceLetter).toList) :
    ∃ before middle after,
      word.toList =
          before ++ sourceLetter :: (middle ++ sourceLetter :: after) ∧
        sourceLetter ∉ before ∧
        sourceLetter ∉ middle ∧
        sourceLetter ∉ after ∧
        let marker := (substitution sourceLetter).head
        let keep :=
          fun value : Nat =>
            value == marker || value == 3 * bound + 2
        (before.flatMap
              (fun letter => (substitution letter).toList)).filter keep ++
            marker ::
              ((middle.flatMap
                    (fun letter =>
                      (substitution letter).toList)).filter keep ++
                marker ::
                  (after.flatMap
                      (fun letter =>
                        (substitution letter).toList)).filter keep) =
          [marker, 3 * bound + 2, marker, 3 * bound + 2, marker] := by
  obtain
    ⟨before, middle, after, sourceNotBefore,
      sourceNotMiddle, sourceNotAfter, sourceSplit⟩ :=
    exists_two_occurrence_split_of_count_eq_two sourceCount
  let marker := (substitution sourceLetter).head
  let keep :=
    fun value : Nat =>
      value == marker || value == 3 * bound + 2
  let images :=
    fun letter : Nat => (substitution letter).toList
  have markerMember :
      marker ∈ images sourceLetter := by
    simp [marker, images, Word.toList]
  have markerNeSeparator : marker ≠ 3 * bound + 2 := by
    intro equality
    have separatorMember :
        3 * bound + 2 ∈ images sourceLetter := by
      simpa only [equality] using markerMember
    exact separatorAbsent (by
      simpa only [images] using separatorMember)
  have markerContribution :=
    count_le_flatMap_count_of_mem
      word.toList images sourceLetter marker markerMember
  have mappedList :
      word.toList.flatMap images =
        (anchor (3 * bound)).toList := by
    have listed := congrArg Word.toList mapped
    rw [Word.toList_bind] at listed
    simpa only [images] using listed
  rw [mappedList, sourceCount] at markerContribution
  have markerIndexed : marker < 3 * bound + 2 := by
    apply Classical.byContradiction
    intro notIndexed
    rw [anchor_toList] at markerContribution
    simp [markerNeSeparator, Ne.symm markerNeSeparator,
      notIndexed] at markerContribution
  have imageNodup :
      (images sourceLetter).Nodup := by
    simpa only [images] using
      preimage_two_occurrence_image_nodup mapped sourceCount
  have markerCount :
      (images sourceLetter).count marker = 1 := by
    have countFormula :
        (images sourceLetter).count marker =
          if marker ∈ images sourceLetter then 1 else 0 :=
      imageNodup.count
    simpa [markerMember] using countFormula
  have imageProjection :
      (images sourceLetter).filter keep = [marker] := by
    rw [show
      (images sourceLetter).filter keep =
        (images sourceLetter).filter
          (fun value => value == marker) by
            apply List.filter_congr
            intro value member
            have valueNeSeparator : value ≠ 3 * bound + 2 := by
              intro equality
              subst value
              exact separatorAbsent (by
                simpa only [images] using member)
            simp [keep, valueNeSeparator]]
    exact
      filter_eq_singleton_of_count_eq_one_local
        (images sourceLetter) marker markerCount
  have targetProjection :
      (anchor (3 * bound)).toList.filter keep =
        [marker, 3 * bound + 2, marker, 3 * bound + 2, marker] := by
    simpa only [keep] using
      (anchor_indexed_separator_projection_local
        (extra := 3 * bound) markerIndexed)
  refine
    ⟨before, middle, after, sourceSplit,
      sourceNotBefore, sourceNotMiddle, sourceNotAfter, ?_⟩
  dsimp only
  change
    (before.flatMap images).filter keep ++
        marker ::
          ((middle.flatMap images).filter keep ++
            marker :: (after.flatMap images).filter keep) =
      [marker, 3 * bound + 2, marker, 3 * bound + 2, marker]
  calc
    _ = (word.toList.flatMap images).filter keep := by
      rw [sourceSplit]
      simp [List.flatMap_append, List.flatMap_cons,
        List.filter_append, imageProjection, List.append_assoc]
    _ = (anchor (3 * bound)).toList.filter keep := by
      rw [mappedList]
    _ = _ := targetProjection

/-- The exact local-certificate obligation left by the count-two
preservation problem, with the redundant source-membership premise removed. -/
def AnchorPreimageTwoCountLocalCertificates : Prop :=
  ∀ bound (word : Word Nat),
    WordUsesAtMost word bound →
    ∀ substitution,
      word.bind substitution = anchor (3 * bound) →
      ∀ letter,
        word.toList.count letter = 2 →
        LocalTwoLimitedCertificate word letter

/-- The remaining structural branch after separator owners have been
certified: exactly twice-occurring variables whose images omit the
distinguished separator. -/
def AnchorPreimageNonseparatorTwoCountLocalCertificates : Prop :=
  ∀ bound (word : Word Nat),
    WordUsesAtMost word bound →
    ∀ substitution,
      word.bind substitution = anchor (3 * bound) →
      ∀ letter,
        word.toList.count letter = 2 →
        3 * bound + 2 ∉ (substitution letter).toList →
        LocalTwoLimitedCertificate word letter

/-- The nonseparator branch, together with the mapped reverse-block
certificate above, supplies local certificates for every count-two source
variable. -/
theorem anchorPreimageTwoCountLocalCertificates_of_nonseparator
    (controlled :
      AnchorPreimageNonseparatorTwoCountLocalCertificates) :
    AnchorPreimageTwoCountLocalCertificates := by
  intro bound word uses substitution mapped letter countTwo
  by_cases separatorMember :
      3 * bound + 2 ∈ (substitution letter).toList
  · exact
      preimage_separator_owner_localTwoLimitedCertificate
        uses mapped countTwo separatorMember
  · exact
      controlled bound word uses substitution mapped
        letter countTwo separatorMember

/-- The membership-free local-certificate interface is equivalent to the
existing two-occurrence-control interface. -/
theorem
    anchorPreimageTwoCountLocalCertificates_iff_twoOccurrenceControl :
    AnchorPreimageTwoCountLocalCertificates ↔
      AnchorPreimageTwoOccurrenceControl := by
  constructor
  · intro certified bound word uses substitution mapped
      letter _member countTwo
    exact
      certified bound word uses substitution mapped letter countTwo
  · intro controlled bound word uses substitution mapped letter countTwo
    have member : letter ∈ word.toList :=
      List.count_pos_iff.mp (by omega)
    exact
      controlled bound word uses substitution mapped
        letter member countTwo

/-- For a twice-occurring anchor-preimage variable, a local certificate
simultaneously yields its interval image, exact competing multiplicity, and
exact projection with every other locally certified 2-limited letter. -/
theorem
    preimage_two_occurrence_interval_and_pairProjection_of_localCertificates
    {bound : Nat} {word other : Word Nat}
    {substitution : Nat → Word Nat}
    (mapped : word.bind substitution = anchor (3 * bound))
    (same : SameDeletionMarkedDigraph word other)
    {sourceLetter controller : Nat}
    (sourceCount : word.toList.count sourceLetter = 2)
    (controllerBound : word.toList.count controller ≤ 2)
    (sourceCertificate :
      LocalTwoLimitedCertificate word sourceLetter)
    (controllerCertificate :
      LocalTwoLimitedCertificate word controller) :
    (substitution sourceLetter).toList =
        List.range' (substitution sourceLetter).head
          (substitution sourceLetter).toList.length ∧
      other.toList.count sourceLetter = 2 ∧
      other.toList.filter
          (fun value =>
            value == sourceLetter || value == controller) =
        word.toList.filter
          (fun value =>
            value == sourceLetter || value == controller) := by
  have sourceMember : sourceLetter ∈ word.toList :=
    List.count_pos_iff.mp (by omega)
  refine
    ⟨preimage_two_occurrence_image_toList_interval
        mapped sourceCount,
      sourceCertificate.right_count_eq_two same sourceCount,
      ?_⟩
  exact
    sameDeletionMarkedDigraph_pairProjection_eq_of_localCertificates
      same sourceLetter controller sourceMember
      (by omega) controllerBound
      sourceCertificate controllerCertificate

/-- Uniform local certificates for the twice-occurring source variables
prove the remaining exact count-two preservation interface. -/
theorem anchorPreimageTwoCountPreservation_of_localCertificates
    (certified : AnchorPreimageTwoCountLocalCertificates) :
    AnchorPreimageTwoCountPreservation := by
  intro bound word uses substitution mapped other same letter countTwo
  exact
    LocalTwoLimitedCertificate.right_count_eq_two
      same
      (certified bound word uses substitution mapped letter countTwo)
      countTwo

/-- The older local-control interface therefore also proves the sharpened
count-two preservation interface directly. -/
theorem anchorPreimageTwoCountPreservation_of_twoOccurrenceControl
    (controlled : AnchorPreimageTwoOccurrenceControl) :
    AnchorPreimageTwoCountPreservation := by
  apply anchorPreimageTwoCountPreservation_of_localCertificates
  exact
    anchorPreimageTwoCountLocalCertificates_iff_twoOccurrenceControl.mpr
      controlled

/-- Consequently, only the nonseparator structural branch remains to prove
the exact count-two preservation interface. -/
theorem anchorPreimageTwoCountPreservation_of_nonseparator
    (controlled :
      AnchorPreimageNonseparatorTwoCountLocalCertificates) :
    AnchorPreimageTwoCountPreservation :=
  anchorPreimageTwoCountPreservation_of_localCertificates
    (anchorPreimageTwoCountLocalCertificates_of_nonseparator controlled)

end SemigroupBasis.Nonfinite.A2One
