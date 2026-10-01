import SemigroupBasis.CoRoots.S5_441GapOwnership
import SemigroupBasis.Examples.ConnectedComponentFourComponents

namespace SemigroupBasis.CoRoots.S5_441

open SemigroupBasis.Examples

/-- One payload block in a canonical parity gap. Odd source multiplicity
renders once, while even source multiplicity renders twice. -/
def canonicalGapPayloadBlock
    (source : List Nat) (letter : Nat) : List Nat :=
  if source.count letter % 2 = 0 then
    [letter, letter]
  else
    [letter]

/-- Render a prescribed ordered payload support with parity multiplicities. -/
def canonicalGapPayload
    (source : List Nat) : List Nat → List Nat
  | [] => []
  | letter :: remaining =>
      canonicalGapPayloadBlock source letter ++
        canonicalGapPayload source remaining

/-- The deterministic separator-free parity envelope of a source list.
The least supported letter is the anchor. Every other supported letter is
rendered in sorted order with one or two copies, and the anchor occurs twice
or three times according to its source parity. -/
def canonicalGap (source : List Nat) : List Nat :=
  match connectedComponentSortedSupport source with
  | [] => []
  | anchor :: payloadSupport =>
      [anchor] ++
        canonicalGapPayload source payloadSupport ++
        (if source.count anchor % 2 = 0 then [] else [anchor]) ++
        [anchor]

@[simp]
theorem canonicalGapPayloadBlock_mem_iff
    (source : List Nat) (letter tested : Nat) :
    tested ∈ canonicalGapPayloadBlock source letter ↔
      tested = letter := by
  by_cases even : source.count letter % 2 = 0
  · simp [canonicalGapPayloadBlock, even]
  · simp [canonicalGapPayloadBlock, even]

@[simp]
theorem canonicalGapPayload_mem_iff
    (source support : List Nat) (tested : Nat) :
    tested ∈ canonicalGapPayload source support ↔
      tested ∈ support := by
  induction support with
  | nil =>
      simp [canonicalGapPayload]
  | cons letter remaining ih =>
      simp [canonicalGapPayload, ih]

theorem canonicalGapPayloadBlock_count
    (source : List Nat) (letter tested : Nat) :
    (canonicalGapPayloadBlock source letter).count tested =
      if tested = letter then
        if source.count letter % 2 = 0 then 2 else 1
      else
        0 := by
  by_cases equal : tested = letter
  · subst tested
    by_cases even : source.count letter % 2 = 0
    · simp [canonicalGapPayloadBlock, even]
    · simp [canonicalGapPayloadBlock, even]
  · by_cases even : source.count letter % 2 = 0
    · simp [canonicalGapPayloadBlock, even, equal, Ne.symm equal]
    · simp [canonicalGapPayloadBlock, even, equal, Ne.symm equal]

theorem canonicalGapPayload_count
    (source support : List Nat) (tested : Nat)
    (supportNodup : support.Nodup) :
    (canonicalGapPayload source support).count tested =
      if tested ∈ support then
        if source.count tested % 2 = 0 then 2 else 1
      else
        0 := by
  induction support with
  | nil =>
      simp [canonicalGapPayload]
  | cons letter remaining ih =>
      have letterAbsent :
          letter ∉ remaining :=
        (List.nodup_cons.mp supportNodup).1
      have remainingNodup :
          remaining.Nodup :=
        (List.nodup_cons.mp supportNodup).2
      simp only [canonicalGapPayload, List.count_append]
      rw [canonicalGapPayloadBlock_count,
        ih remainingNodup]
      by_cases equal : tested = letter
      · subst tested
        simp [letterAbsent]
      · simp [equal]

theorem canonicalGapPayload_count_of_mem
    {source support : List Nat} {tested : Nat}
    (supportNodup : support.Nodup)
    (member : tested ∈ support) :
    (canonicalGapPayload source support).count tested =
      if source.count tested % 2 = 0 then 2 else 1 := by
  simpa [member] using
    canonicalGapPayload_count source support tested supportNodup

theorem canonicalGapPayload_count_of_not_mem
    {source support : List Nat} {tested : Nat}
    (supportNodup : support.Nodup)
    (notMember : tested ∉ support) :
    (canonicalGapPayload source support).count tested = 0 := by
  simpa [notMember] using
    canonicalGapPayload_count source support tested supportNodup

@[simp]
theorem canonicalGap_nil :
    canonicalGap [] = [] := by
  simp [canonicalGap, connectedComponentSortedSupport,
    connectedComponentDistinctSupport]

/-- The displayed anchor really is supported by the source. -/
theorem canonicalGap_anchor_mem
    {source : List Nat} {anchor : Nat} {payloadSupport : List Nat}
    (supportShape :
      connectedComponentSortedSupport source =
        anchor :: payloadSupport) :
    anchor ∈ source := by
  apply
    (connectedComponentSortedSupport_mem_iff
      anchor source).1
  rw [supportShape]
  simp

/-- The head of the sorted support is no larger than any supported letter. -/
theorem canonicalGap_anchor_le
    {source : List Nat} {anchor tested : Nat}
    {payloadSupport : List Nat}
    (supportShape :
      connectedComponentSortedSupport source =
        anchor :: payloadSupport)
    (member : tested ∈ source) :
    anchor ≤ tested := by
  have supportMember :
      tested ∈ anchor :: payloadSupport := by
    rw [← supportShape]
    exact
      (connectedComponentSortedSupport_mem_iff
        tested source).2 member
  rcases List.mem_cons.mp supportMember with equal | tailMember
  · omega
  · have sorted :=
      connectedComponentSortedSupport_sorted source
    rw [supportShape] at sorted
    exact List.rel_of_pairwise_cons sorted tailMember

/-- The canonical gap has exactly the source support. -/
theorem canonicalGap_mem_iff
    (source : List Nat) (tested : Nat) :
    tested ∈ canonicalGap source ↔ tested ∈ source := by
  rw [← connectedComponentSortedSupport_mem_iff tested source]
  cases supportShape :
      connectedComponentSortedSupport source with
  | nil =>
      simp [canonicalGap, supportShape]
  | cons anchor payloadSupport =>
      by_cases anchorEven :
          source.count anchor % 2 = 0
      · simp [canonicalGap, supportShape, anchorEven,
          or_assoc, or_left_comm, or_comm]
      · simp [canonicalGap, supportShape, anchorEven,
          or_assoc, or_left_comm, or_comm]

/-- A canonical gap is empty exactly when its source is empty. -/
theorem canonicalGap_eq_nil_iff
    (source : List Nat) :
    canonicalGap source = [] ↔ source = [] := by
  constructor
  · intro gapEmpty
    cases source with
    | nil => rfl
    | cons first remaining =>
        have firstMember :
            first ∈ canonicalGap (first :: remaining) :=
          (canonicalGap_mem_iff
            (first :: remaining) first).2 (by simp)
        rw [gapEmpty] at firstMember
        simp at firstMember
  · rintro rfl
    exact canonicalGap_nil

/-- A nonempty source has a nonempty canonical gap. -/
theorem canonicalGap_nonempty
    {source : List Nat} (sourceNonempty : source ≠ []) :
    canonicalGap source ≠ [] := by
  exact fun gapEmpty =>
    sourceNonempty <|
      (canonicalGap_eq_nil_iff source).1 gapEmpty

/-- The canonical gap is visibly an envelope with the anchor at both ends. -/
theorem canonicalGap_envelope_shape
    {source : List Nat} {anchor : Nat} {payloadSupport : List Nat}
    (supportShape :
      connectedComponentSortedSupport source =
        anchor :: payloadSupport) :
    canonicalGap source =
      [anchor] ++
        (canonicalGapPayload source payloadSupport ++
          (if source.count anchor % 2 = 0 then [] else [anchor])) ++
        [anchor] := by
  simp [canonicalGap, supportShape, List.append_assoc]

/-- Exact anchor multiplicity: two copies for even parity and three for odd
parity. -/
theorem canonicalGap_count_anchor
    {source : List Nat} {anchor : Nat} {payloadSupport : List Nat}
    (supportShape :
      connectedComponentSortedSupport source =
        anchor :: payloadSupport) :
    (canonicalGap source).count anchor =
      if source.count anchor % 2 = 0 then 2 else 3 := by
  have supportNodup :=
    connectedComponentSortedSupport_nodup source
  rw [supportShape] at supportNodup
  have anchorAbsent :
      anchor ∉ payloadSupport :=
    (List.nodup_cons.mp supportNodup).1
  have payloadCount :
      (canonicalGapPayload source payloadSupport).count anchor = 0 :=
    canonicalGapPayload_count_of_not_mem
      (List.nodup_cons.mp supportNodup).2 anchorAbsent
  by_cases anchorEven :
      source.count anchor % 2 = 0
  · simp [canonicalGap, supportShape, anchorEven, payloadCount]
  · simp [canonicalGap, supportShape, anchorEven, payloadCount]

/-- Exact non-anchor multiplicity for a supported letter: one copy for odd
parity and two for even parity. -/
theorem canonicalGap_count_nonanchor
    {source : List Nat} {anchor tested : Nat}
    {payloadSupport : List Nat}
    (supportShape :
      connectedComponentSortedSupport source =
        anchor :: payloadSupport)
    (member : tested ∈ source)
    (different : tested ≠ anchor) :
    (canonicalGap source).count tested =
      if source.count tested % 2 = 0 then 2 else 1 := by
  have supportNodup :=
    connectedComponentSortedSupport_nodup source
  rw [supportShape] at supportNodup
  have payloadSupportNodup :
      payloadSupport.Nodup :=
    (List.nodup_cons.mp supportNodup).2
  have supportMember :
      tested ∈ anchor :: payloadSupport := by
    rw [← supportShape]
    exact
      (connectedComponentSortedSupport_mem_iff
        tested source).2 member
  have payloadMember :
      tested ∈ payloadSupport := by
    rcases List.mem_cons.mp supportMember with equal | tailMember
    · exact False.elim (different equal)
    · exact tailMember
  have payloadCount :
      (canonicalGapPayload source payloadSupport).count tested =
        if source.count tested % 2 = 0 then 2 else 1 :=
    canonicalGapPayload_count_of_mem
      payloadSupportNodup payloadMember
  by_cases anchorEven :
      source.count anchor % 2 = 0
  · simp [canonicalGap, supportShape, anchorEven,
      different, Ne.symm different, payloadCount]
  · simp [canonicalGap, supportShape, anchorEven,
      different, Ne.symm different, payloadCount]

/-- Canonicalization preserves the occurrence-count parity of every letter. -/
theorem canonicalGap_count_mod_two
    (source : List Nat) (tested : Nat) :
    (canonicalGap source).count tested % 2 =
      source.count tested % 2 := by
  by_cases member : tested ∈ source
  · cases supportShape :
        connectedComponentSortedSupport source with
    | nil =>
        have impossible :
            tested ∈ ([] : List Nat) := by
          rw [← supportShape]
          exact
            (connectedComponentSortedSupport_mem_iff
              tested source).2 member
        simp at impossible
    | cons anchor payloadSupport =>
        by_cases equal : tested = anchor
        · subst tested
          rw [canonicalGap_count_anchor supportShape]
          by_cases even :
              source.count anchor % 2 = 0
          · simp [even]
          · have odd :
                source.count anchor % 2 = 1 := by
              omega
            simp [even, odd]
        · rw [canonicalGap_count_nonanchor
              supportShape member equal]
          by_cases even :
              source.count tested % 2 = 0
          · simp [even]
          · have odd :
                source.count tested % 2 = 1 := by
              omega
            simp [even, odd]
  · have gapAbsent :
        tested ∉ canonicalGap source := by
      intro gapMember
      exact member <|
        (canonicalGap_mem_iff source tested).1 gapMember
    rw [List.count_eq_zero.mpr gapAbsent,
      List.count_eq_zero.mpr member]

private theorem envelope_anchor_mem_left
    {anchor separator : Nat} {middle left right : List Nat}
    (different : anchor ≠ separator)
    (split :
      [anchor] ++ middle ++ [anchor] =
        left ++ separator :: right) :
    anchor ∈ left := by
  cases left with
  | nil =>
      have equal : anchor = separator := by
        simpa using congrArg List.head? split
      exact False.elim (different equal)
  | cons leftHead leftTail =>
      have equal : anchor = leftHead := by
        simpa using congrArg List.head? split
      subst leftHead
      simp

private theorem envelope_anchor_mem_right
    {anchor separator : Nat} {middle left right : List Nat}
    (different : anchor ≠ separator)
    (split :
      [anchor] ++ middle ++ [anchor] =
        left ++ separator :: right) :
    anchor ∈ right := by
  have reversed :
      [anchor] ++ middle.reverse ++ [anchor] =
        right.reverse ++ separator :: left.reverse := by
    simpa [List.reverse_append, List.append_assoc] using
      congrArg List.reverse split
  have reverseMember :
      anchor ∈ right.reverse :=
    envelope_anchor_mem_left different reversed
  simpa using reverseMember

/-- No exact cut can occur in a canonical gap of a nonempty source. Anchor
and even-payload candidates have count greater than one. A count-one
non-anchor payload candidate has the repeated anchor on both sides, violating
support disjointness. -/
theorem canonicalGap_not_exactCut
    {source left right : List Nat} {separator : Nat}
    (sourceNonempty : source ≠ []) :
    ¬ UniqueSeparatorFourExactCut
        (canonicalGap source) left separator right := by
  intro cut
  have supportNonempty :
      connectedComponentSortedSupport source ≠ [] :=
    connectedComponentSortedSupport_nonempty sourceNonempty
  cases supportShape :
      connectedComponentSortedSupport source with
  | nil =>
      exact supportNonempty supportShape
  | cons anchor payloadSupport =>
      have separatorMemberGap :
          separator ∈ canonicalGap source := by
        rw [cut.1]
        exact
          List.mem_append_right left
            (List.Mem.head right)
      have separatorMemberSource :
          separator ∈ source :=
        (canonicalGap_mem_iff source separator).1
          separatorMemberGap
      by_cases separatorAnchor : separator = anchor
      · subst separator
        have countOne := cut.2.1
        rw [canonicalGap_count_anchor supportShape] at countOne
        by_cases anchorEven :
            source.count anchor % 2 = 0
        · simp [anchorEven] at countOne
        · simp [anchorEven] at countOne
      · by_cases separatorEven :
            source.count separator % 2 = 0
        · have countOne := cut.2.1
          rw [
            canonicalGap_count_nonanchor
              supportShape separatorMemberSource separatorAnchor
          ] at countOne
          simp [separatorEven] at countOne
        · have separatorOdd :
              source.count separator % 2 = 1 := by
            omega
          have _singletonCount :
              (canonicalGap source).count separator = 1 := by
            rw [canonicalGap_count_nonanchor
              supportShape separatorMemberSource separatorAnchor]
            simp [separatorOdd]
          have envelopeSplit :
              [anchor] ++
                  (canonicalGapPayload source payloadSupport ++
                    (if source.count anchor % 2 = 0 then
                      []
                    else
                      [anchor])) ++
                  [anchor] =
                left ++ separator :: right :=
            (canonicalGap_envelope_shape supportShape).symm.trans
              cut.1
          have anchorLeft :
              anchor ∈ left :=
            envelope_anchor_mem_left
              (Ne.symm separatorAnchor) envelopeSplit
          have anchorRight :
              anchor ∈ right :=
            envelope_anchor_mem_right
              (Ne.symm separatorAnchor) envelopeSplit
          exact cut.2.2 anchor anchorLeft anchorRight

/-- Existential separator-free form of `canonicalGap_not_exactCut`. -/
theorem canonicalGap_no_exactCut
    {source : List Nat} (sourceNonempty : source ≠ []) :
    ¬ ∃ left separator right,
        UniqueSeparatorFourExactCut
          (canonicalGap source) left separator right := by
  rintro ⟨left, separator, right, cut⟩
  exact
    canonicalGap_not_exactCut
      (source := source) (left := left) (right := right)
      (separator := separator) sourceNonempty cut

end SemigroupBasis.CoRoots.S5_441
