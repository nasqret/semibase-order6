import SemigroupBasis.Nonfinite.A2One.TwoCountPreservation

namespace SemigroupBasis.Nonfinite.A2One

open SemigroupBasis

/-- Once the two displayed marker occurrences are inserted into the fixed
five-letter marker/separator projection, there are exactly three possible
placements. -/
private theorem marker_separator_split_cases
    {marker separator : Nat}
    (different : marker ≠ separator)
    {before middle after : List Nat}
    (projection :
      before ++ marker :: (middle ++ marker :: after) =
        [marker, separator, marker, separator, marker]) :
    (before = [] ∧ middle = [separator] ∧
        after = [separator, marker]) ∨
      (before = [] ∧ middle = [separator, marker, separator] ∧
        after = []) ∨
      (before = [marker, separator] ∧ middle = [separator] ∧
        after = []) := by
  cases before with
  | nil =>
      cases middle with
      | nil => simp_all [List.cons_append]
      | cons first middleTail =>
          cases middleTail with
          | nil => simp_all [List.cons_append]
          | cons second middleTail =>
              cases middleTail with
              | nil => simp_all [List.cons_append]
              | cons third middleTail =>
                  cases middleTail <;>
                    simp_all [List.cons_append]
  | cons first beforeTail =>
      cases beforeTail with
      | nil => simp_all [List.cons_append]
      | cons second beforeTail =>
          cases beforeTail with
          | nil =>
              cases middle with
              | nil => simp_all [List.cons_append]
              | cons third middleTail =>
                  cases middleTail <;>
                    simp_all [List.cons_append]
          | cons third beforeTail =>
              cases beforeTail with
              | nil => simp_all [List.cons_append]
              | cons fourth beforeTail =>
                  cases beforeTail with
                  | nil => simp_all [List.cons_append]
                  | cons fifth beforeTail =>
                      simp_all [List.cons_append]

private theorem filter_pair_eq_nil_local
    {letters : List Nat} {first second : Nat}
    (firstAbsent : first ∉ letters)
    (secondAbsent : second ∉ letters) :
    letters.filter
        (fun value => value == first || value == second) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro value valueMember
  simp only [Bool.or_eq_true, beq_iff_eq]
  rintro (equality | equality)
  · subst value
    exact firstAbsent valueMember
  · subst value
    exact secondAbsent valueMember

private theorem filter_pair_eq_singleton_local
    {letters : List Nat} {first second : Nat}
    (different : first ≠ second)
    (firstAbsent : first ∉ letters)
    (secondCountOne : letters.count second = 1) :
    letters.filter
        (fun value => value == first || value == second) = [second] := by
  rw [show
    letters.filter
        (fun value => value == first || value == second) =
      letters.filter (fun value => value == second) by
        apply List.filter_congr
        intro value valueMember
        have valueNeFirst : value ≠ first := by
          intro equality
          subst value
          exact firstAbsent valueMember
        simp [valueNeFirst]]
  induction letters with
  | nil => simp at secondCountOne
  | cons head tail ih =>
      by_cases equality : head = second
      · subst head
        have tailCountZero : tail.count second = 0 := by
          simp only [List.count_cons_self] at secondCountOne
          omega
        have tailFilter :
            tail.filter (fun value => value == second) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro value valueMember
          simp only [beq_iff_eq]
          intro valueEq
          subst value
          exact (List.count_eq_zero.mp tailCountZero) valueMember
        simp [tailFilter]
      · have tailCountOne : tail.count second = 1 := by
          simpa [equality] using secondCountOne
        have tailFirstAbsent : first ∉ tail := by
          intro member
          exact firstAbsent (by simp [member])
        simp [equality, ih tailFirstAbsent tailCountOne]

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

private theorem count_le_filteredFlatMap_count_of_mem
    (source : List Nat) (images : Nat → List Nat)
    (owner value : Nat) (keep : Nat → Bool)
    (valueMember : value ∈ images owner)
    (kept : keep value = true) :
    source.count owner ≤
      ((source.flatMap images).filter keep).count value := by
  rw [count_filter_of_kept_local _ _ _ kept]
  exact
    count_le_flatMap_count_of_mem
      source images owner value valueMember

private theorem singleton_between_two_occurrences_certificate
    {word : Word Nat} {target controller : Nat}
    {before middle after : List Nat}
    (sourceSplit :
      word.toList =
        before ++ target :: (middle ++ target :: after))
    (targetNotBefore : target ∉ before)
    (targetNotMiddle : target ∉ middle)
    (targetNotAfter : target ∉ after)
    (controllerMember : controller ∈ middle)
    (controllerCountOne : word.toList.count controller = 1) :
    LocalTwoLimitedCertificate word target := by
  have different : target ≠ controller := by
    intro equality
    subst controller
    exact targetNotMiddle controllerMember
  have splitCounts := congrArg (List.count controller) sourceSplit
  have middlePositive : 1 ≤ middle.count controller :=
    List.count_pos_iff.mpr controllerMember
  have beforeCountZero : before.count controller = 0 := by
    rw [controllerCountOne] at splitCounts
    simp [different, Ne.symm different] at splitCounts
    omega
  have middleCountOne : middle.count controller = 1 := by
    rw [controllerCountOne] at splitCounts
    simp [different, Ne.symm different] at splitCounts
    omega
  have afterCountZero : after.count controller = 0 := by
    rw [controllerCountOne] at splitCounts
    simp [different, Ne.symm different] at splitCounts
    omega
  have beforeFilter :
      before.filter
          (fun value => value == target || value == controller) = [] :=
    filter_pair_eq_nil_local targetNotBefore
      (List.count_eq_zero.mp beforeCountZero)
  have middleFilter :
      middle.filter
          (fun value => value == target || value == controller) =
        [controller] :=
    filter_pair_eq_singleton_local different targetNotMiddle
      middleCountOne
  have afterFilter :
      after.filter
          (fun value => value == target || value == controller) = [] :=
    filter_pair_eq_nil_local targetNotAfter
      (List.count_eq_zero.mp afterCountZero)
  apply LocalTwoLimitedCertificate.singletonSeparator
      target controller different controllerCountOne
  rw [sourceSplit, List.filter_append, List.filter_cons,
    List.filter_append, List.filter_cons]
  simp [beforeFilter, middleFilter, afterFilter, different,
    adjacentPairsList, Word.adjacentPairsFrom]

private theorem last_controller_certificate
    {word : Word Nat} {target controller : Nat}
    {before middle after : List Nat}
    (sourceSplit :
      word.toList =
        before ++ target :: (middle ++ target :: after))
    (targetNotBefore : target ∉ before)
    (targetNotMiddle : target ∉ middle)
    (targetNotAfter : target ∉ after)
    (different : target ≠ controller)
    (beforeControllerCount : before.count controller = 0)
    (middleControllerCount : middle.count controller = 1)
    (afterControllerCount : after.count controller = 1)
    (controllerCertificate :
      LocalTwoLimitedCertificate word controller) :
    LocalTwoLimitedCertificate word target := by
  have beforeFilter :
      before.filter
          (fun value => value == target || value == controller) = [] :=
    filter_pair_eq_nil_local targetNotBefore
      (List.count_eq_zero.mp beforeControllerCount)
  have middleFilter :
      middle.filter
          (fun value => value == target || value == controller) =
        [controller] :=
    filter_pair_eq_singleton_local different targetNotMiddle
      middleControllerCount
  have afterFilter :
      after.filter
          (fun value => value == target || value == controller) =
        [controller] :=
    filter_pair_eq_singleton_local different targetNotAfter
      afterControllerCount
  apply LocalTwoLimitedCertificate.lastController
      target controller different controllerCertificate
  · rw [sourceSplit, List.filter_append, List.filter_cons,
      List.filter_append, List.filter_cons]
    simp [beforeFilter, middleFilter, afterFilter, different]
  · rw [sourceSplit, List.filter_append, List.filter_cons,
      List.filter_append, List.filter_cons]
    simp [beforeFilter, middleFilter, afterFilter, different,
      adjacentPairsList, Word.adjacentPairsFrom]

private theorem head_controller_certificate
    {word : Word Nat} {target controller : Nat}
    {before middle after : List Nat}
    (sourceSplit :
      word.toList =
        before ++ target :: (middle ++ target :: after))
    (targetNotBefore : target ∉ before)
    (targetNotMiddle : target ∉ middle)
    (targetNotAfter : target ∉ after)
    (different : target ≠ controller)
    (beforeControllerCount : before.count controller = 1)
    (middleControllerCount : middle.count controller = 1)
    (afterControllerCount : after.count controller = 0)
    (controllerCertificate :
      LocalTwoLimitedCertificate word controller) :
    LocalTwoLimitedCertificate word target := by
  have beforeFilter :
      before.filter
          (fun value => value == target || value == controller) =
        [controller] :=
    filter_pair_eq_singleton_local different targetNotBefore
      beforeControllerCount
  have middleFilter :
      middle.filter
          (fun value => value == target || value == controller) =
        [controller] :=
    filter_pair_eq_singleton_local different targetNotMiddle
      middleControllerCount
  have afterFilter :
      after.filter
          (fun value => value == target || value == controller) = [] :=
    filter_pair_eq_nil_local targetNotAfter
      (List.count_eq_zero.mp afterControllerCount)
  apply LocalTwoLimitedCertificate.headController
      target controller different controllerCertificate
  · rw [sourceSplit, List.filter_append, List.filter_cons,
      List.filter_append, List.filter_cons]
    simp [beforeFilter, middleFilter, afterFilter, different]
  · rw [sourceSplit, List.filter_append, List.filter_cons,
      List.filter_append, List.filter_cons]
    simp [beforeFilter, middleFilter, afterFilter, different,
      adjacentPairsList, Word.adjacentPairsFrom]

/-- Every exactly twice-occurring anchor-preimage variable whose image omits
the distinguished separator has a local 2-limited certificate.  The proof
uses the three possible placements of its two image-head markers in the
fixed five-letter marker/separator projection. -/
theorem anchorPreimageNonseparatorTwoCountLocalCertificates :
    AnchorPreimageNonseparatorTwoCountLocalCertificates := by
  intro bound word uses substitution mapped target targetCount
    separatorAbsent
  obtain
    ⟨before, middle, after, sourceSplit,
      targetNotBefore, targetNotMiddle, targetNotAfter, projection⟩ :=
    preimage_two_occurrence_marker_separator_projection
      mapped targetCount separatorAbsent
  let marker := (substitution target).head
  let separator := 3 * bound + 2
  let images :=
    fun letter : Nat => (substitution letter).toList
  let keep :=
    fun value : Nat =>
      value == marker || value == separator
  change
    (before.flatMap images).filter keep ++
        marker ::
          ((middle.flatMap images).filter keep ++
            marker :: (after.flatMap images).filter keep) =
      [marker, separator, marker, separator, marker] at projection
  have markerMember : marker ∈ images target := by
    simp [marker, images, Word.toList]
  have markerNeSeparator : marker ≠ separator := by
    intro equality
    apply separatorAbsent
    simpa only [images, separator, equality] using markerMember
  have mappedList :
      word.toList.flatMap images =
        (anchor (3 * bound)).toList := by
    have listed := congrArg Word.toList mapped
    rw [Word.toList_bind] at listed
    simpa only [images] using listed
  rcases
      marker_separator_split_cases markerNeSeparator projection with
    firstSecond | firstThird | secondThird
  · rcases firstSecond with
      ⟨beforeProjection, middleProjection, afterProjection⟩
    have separatorFilteredMember :
        separator ∈ (middle.flatMap images).filter keep := by
      rw [middleProjection]
      simp
    have separatorFlatMember :=
      (List.mem_filter.mp separatorFilteredMember).1
    rcases List.mem_flatMap.mp separatorFlatMember with
      ⟨owner, ownerMember, separatorOwner⟩
    have different : target ≠ owner := by
      intro equality
      subst owner
      exact targetNotMiddle ownerMember
    have ownerWordMember : owner ∈ word.toList := by
      rw [sourceSplit]
      simp [ownerMember]
    have ownerContribution :=
      count_le_flatMap_count_of_mem
        word.toList images owner separator separatorOwner
    rw [mappedList] at ownerContribution
    have ownerUpper : word.toList.count owner ≤ 2 := by
      simpa only [separator, anchor_separator_count_eq_two]
        using ownerContribution
    have ownerPositive : 1 ≤ word.toList.count owner :=
      List.count_pos_iff.mpr ownerWordMember
    by_cases ownerCountOne : word.toList.count owner = 1
    · exact
        singleton_between_two_occurrences_certificate
          sourceSplit targetNotBefore targetNotMiddle targetNotAfter
          ownerMember ownerCountOne
    · have ownerCountTwo : word.toList.count owner = 2 := by
        omega
      have beforeOwnerBound :=
        count_le_filteredFlatMap_count_of_mem
          before images owner separator keep separatorOwner (by
            simp [keep])
      rw [beforeProjection] at beforeOwnerBound
      have beforeOwnerCount : before.count owner = 0 := by
        simpa using beforeOwnerBound
      have middleOwnerBound :=
        count_le_filteredFlatMap_count_of_mem
          middle images owner separator keep separatorOwner (by
            simp [keep])
      rw [middleProjection] at middleOwnerBound
      have middleOwnerPositive : 1 ≤ middle.count owner :=
        List.count_pos_iff.mpr ownerMember
      have middleOwnerCount : middle.count owner = 1 := by
        have middleOwnerUpper : middle.count owner ≤ 1 := by
          simpa using middleOwnerBound
        omega
      have splitCounts := congrArg (List.count owner) sourceSplit
      have afterOwnerCount : after.count owner = 1 := by
        rw [ownerCountTwo] at splitCounts
        simp [different, Ne.symm different] at splitCounts
        omega
      have ownerCertificate :
          LocalTwoLimitedCertificate word owner :=
        preimage_separator_owner_localTwoLimitedCertificate
          uses mapped ownerCountTwo (by
            simpa only [images, separator] using separatorOwner)
      exact
        last_controller_certificate
          sourceSplit targetNotBefore targetNotMiddle targetNotAfter
          different beforeOwnerCount middleOwnerCount afterOwnerCount
          ownerCertificate
  · rcases firstThird with
      ⟨beforeProjection, middleProjection, afterProjection⟩
    have markerFilteredMember :
        marker ∈ (middle.flatMap images).filter keep := by
      rw [middleProjection]
      simp [markerNeSeparator]
    have markerFlatMember :=
      (List.mem_filter.mp markerFilteredMember).1
    rcases List.mem_flatMap.mp markerFlatMember with
      ⟨controller, controllerMember, controllerMarker⟩
    have different : target ≠ controller := by
      intro equality
      subst controller
      exact targetNotMiddle controllerMember
    have controllerWordMember : controller ∈ word.toList := by
      rw [sourceSplit]
      simp [controllerMember]
    have totalContribution :=
      two_source_count_add_le_flatMap_count_of_mem
        word.toList images target controller marker different
        markerMember controllerMarker
    rw [mappedList, targetCount] at totalContribution
    have markerUpper :=
      anchor_count_le_three (3 * bound) marker
    have controllerPositive :
        1 ≤ word.toList.count controller :=
      List.count_pos_iff.mpr controllerWordMember
    have controllerCountOne :
        word.toList.count controller = 1 := by
      omega
    exact
      singleton_between_two_occurrences_certificate
        sourceSplit targetNotBefore targetNotMiddle targetNotAfter
        controllerMember controllerCountOne
  · rcases secondThird with
      ⟨beforeProjection, middleProjection, afterProjection⟩
    have separatorFilteredMember :
        separator ∈ (middle.flatMap images).filter keep := by
      rw [middleProjection]
      simp
    have separatorFlatMember :=
      (List.mem_filter.mp separatorFilteredMember).1
    rcases List.mem_flatMap.mp separatorFlatMember with
      ⟨owner, ownerMember, separatorOwner⟩
    have different : target ≠ owner := by
      intro equality
      subst owner
      exact targetNotMiddle ownerMember
    have ownerWordMember : owner ∈ word.toList := by
      rw [sourceSplit]
      simp [ownerMember]
    have ownerContribution :=
      count_le_flatMap_count_of_mem
        word.toList images owner separator separatorOwner
    rw [mappedList] at ownerContribution
    have ownerUpper : word.toList.count owner ≤ 2 := by
      simpa only [separator, anchor_separator_count_eq_two]
        using ownerContribution
    have ownerPositive : 1 ≤ word.toList.count owner :=
      List.count_pos_iff.mpr ownerWordMember
    by_cases ownerCountOne : word.toList.count owner = 1
    · exact
        singleton_between_two_occurrences_certificate
          sourceSplit targetNotBefore targetNotMiddle targetNotAfter
          ownerMember ownerCountOne
    · have ownerCountTwo : word.toList.count owner = 2 := by
        omega
      have afterOwnerBound :=
        count_le_filteredFlatMap_count_of_mem
          after images owner separator keep separatorOwner (by
            simp [keep])
      rw [afterProjection] at afterOwnerBound
      have afterOwnerCount : after.count owner = 0 := by
        simpa using afterOwnerBound
      have middleOwnerBound :=
        count_le_filteredFlatMap_count_of_mem
          middle images owner separator keep separatorOwner (by
            simp [keep])
      rw [middleProjection] at middleOwnerBound
      have middleOwnerPositive : 1 ≤ middle.count owner :=
        List.count_pos_iff.mpr ownerMember
      have middleOwnerCount : middle.count owner = 1 := by
        have middleOwnerUpper : middle.count owner ≤ 1 := by
          simpa using middleOwnerBound
        omega
      have splitCounts := congrArg (List.count owner) sourceSplit
      have beforeOwnerCount : before.count owner = 1 := by
        rw [ownerCountTwo] at splitCounts
        simp [different, Ne.symm different] at splitCounts
        omega
      have ownerCertificate :
          LocalTwoLimitedCertificate word owner :=
        preimage_separator_owner_localTwoLimitedCertificate
          uses mapped ownerCountTwo (by
            simpa only [images, separator] using separatorOwner)
      exact
        head_controller_certificate
          sourceSplit targetNotBefore targetNotMiddle targetNotAfter
          different beforeOwnerCount middleOwnerCount afterOwnerCount
          ownerCertificate

/-- Every exactly twice-occurring variable in a bounded anchor preimage has
a local 2-limited certificate. -/
theorem anchorPreimageTwoCountLocalCertificates :
    AnchorPreimageTwoCountLocalCertificates :=
  anchorPreimageTwoCountLocalCertificates_of_nonseparator
    anchorPreimageNonseparatorTwoCountLocalCertificates

/-- Exact count-two multiplicities are preserved across every
deletion-equivalent competitor of a bounded anchor preimage. -/
theorem anchorPreimageTwoCountPreservation :
    AnchorPreimageTwoCountPreservation :=
  anchorPreimageTwoCountPreservation_of_localCertificates
    anchorPreimageTwoCountLocalCertificates

/-- The Trahtman anchor is deletion-graph rigid for every bounded
nonerasing preimage. -/
theorem anchorPreimageDeletionRigidity :
    AnchorPreimageDeletionRigidity :=
  anchorPreimageDeletionRigidity_of_twoCountPreservation
    anchorPreimageTwoCountPreservation

/-- Closed form of the pure infinite-word lemma used by the `A₂¹`
nonfinite-basis proof. -/
theorem boundedDeletionGraphPreimageRigidity :
    BoundedDeletionGraphPreimageRigidity :=
  boundedDeletionGraphPreimageRigidity_of_anchorPreimageDeletionRigidity
    anchorPreimageDeletionRigidity

end SemigroupBasis.Nonfinite.A2One
