import SemigroupBasis.CoRoots.Order6SporadicSection27BetaRepair

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6SporadicSection27

/-! ## First-occurrence rank extraction -/

/-- A member of a strict prefix has a smaller first-occurrence index than
the fresh letter displayed immediately after that prefix. -/
private theorem idxOf_lt_of_mem_prefix
    {letters prefixList suffix : List Nat} {earlier later : Nat}
    (shape : letters = prefixList ++ later :: suffix)
    (laterAbsent : later ∉ prefixList)
    (earlierMember : earlier ∈ prefixList) :
    letters.idxOf earlier < letters.idxOf later := by
  induction prefixList generalizing letters with
  | nil => simp at earlierMember
  | cons head rest induction =>
      subst shape
      by_cases headEarlier : head = earlier
      · have headLater : head ≠ later := by
          intro equal
          exact laterAbsent (by simp [equal])
        have earlierBeq : (head == earlier) = true := by
          simp [headEarlier]
        have laterBeq : (head == later) = false := by
          simp [headLater]
        simp only [List.cons_append, List.idxOf_cons, earlierBeq,
          laterBeq, cond_true, cond_false]
        omega
      · have earlierInRest : earlier ∈ rest := by
          rcases List.mem_cons.mp earlierMember with equal | member
          · exact False.elim (headEarlier equal.symm)
          · exact member
        have laterAbsentRest : later ∉ rest := by
          intro member
          exact laterAbsent (List.mem_cons_of_mem head member)
        have inner :=
          induction (letters := rest ++ later :: suffix) rfl
            laterAbsentRest earlierInRest
        have earlierBeq : (head == earlier) = false := by
          simp [headEarlier]
        have headLater : head ≠ later := by
          intro equal
          exact laterAbsent (by simp [equal])
        have laterBeq : (head == later) = false := by
          simp [headLater]
        simp only [List.cons_append, List.idxOf_cons, earlierBeq,
          laterBeq, cond_false]
        omega

/-- In a nodup split, the displayed letter occurs in neither side. -/
private theorem not_mem_parts_of_nodup_split
    {letters before after : List Nat} {letter : Nat}
    (nodup : letters.Nodup)
    (split : letters = before ++ letter :: after) :
    letter ∉ before ∧ letter ∉ after := by
  have splitNodup : (before ++ letter :: after).Nodup := by
    rw [← split]
    exact nodup
  have appendData := List.nodup_append.mp splitNodup
  constructor
  · intro member
    exact appendData.2.2
      letter member letter (by simp) rfl
  · exact (List.nodup_cons.mp appendData.2.1).1

/-- Literal first-occurrence order agrees with `List.idxOf` order when the
marker sequence has no duplicates. -/
theorem EarlierIn.idxOf_lt
    {markers : List Nat} {earlier later : Nat}
    (order : EarlierIn markers earlier later)
    (markersNodup : markers.Nodup) :
    markers.idxOf earlier < markers.idxOf later := by
  obtain ⟨before, middle, after, shape⟩ := order
  let prefixList := before ++ earlier :: middle
  have split : markers = prefixList ++ later :: after := by
    dsimp [prefixList]
    simpa [List.append_assoc] using shape
  have laterAbsent : later ∉ prefixList :=
    (not_mem_parts_of_nodup_split markersNodup split).1
  have earlierMember : earlier ∈ prefixList := by
    dsimp [prefixList]
    simp
  exact idxOf_lt_of_mem_prefix split laterAbsent earlierMember

/-! ## Literal proposition-to-repair witnesses -/

/-- Every literal condition-(II) obstruction over a nodup marker order
packages the strict rank decrease required by `CrossingWitness`. -/
theorem Has27Crossing.nonemptyWitness
    {markers source : List Nat}
    (crossing : Has27Crossing markers source)
    (markersNodup : markers.Nodup) :
    Nonempty (CrossingWitness markers source) := by
  obtain ⟨earlier, later, pre, gapOne, gapTwo, gapThree, post,
    order, sourceEq⟩ := crossing
  exact ⟨{
    earlier := earlier
    later := later
    pre := pre
    gapOne := gapOne
    gapTwo := gapTwo
    gapThree := gapThree
    post := post
    source_eq := sourceEq
    order := order
    rank_lt := order.idxOf_lt markersNodup
  }⟩

/-- Every literal condition-(III) obstruction over a nodup marker order
packages the strict rank decrease required by `AdjacentWitness`. -/
theorem Has27AdjacentPair.nonemptyWitness
    {markers source : List Nat}
    (adjacent : Has27AdjacentPair markers source)
    (markersNodup : markers.Nodup) :
    Nonempty (AdjacentWitness markers source) := by
  obtain ⟨earlier, later, pre, gapOne, gapTwo, post,
    order, sourceEq⟩ := adjacent
  exact ⟨{
    earlier := earlier
    later := later
    pre := pre
    gapOne := gapOne
    gapTwo := gapTwo
    post := post
    source_eq := sourceEq
    order := order
    rank_lt := order.idxOf_lt markersNodup
  }⟩

/-- The literal condition-(II) proposition is equivalent to the existence of
the repair witness used by the terminating normalizer. -/
theorem has27Crossing_iff_nonemptyWitness
    {markers source : List Nat} (markersNodup : markers.Nodup) :
    Has27Crossing markers source ↔
      Nonempty (CrossingWitness markers source) := by
  constructor
  · intro crossing
    exact crossing.nonemptyWitness markersNodup
  · rintro ⟨witness⟩
    exact witness.source_hasCrossing

/-- The literal condition-(III) proposition is equivalent to the existence
of the repair witness used by the terminating normalizer. -/
theorem has27AdjacentPair_iff_nonemptyWitness
    {markers source : List Nat} (markersNodup : markers.Nodup) :
    Has27AdjacentPair markers source ↔
      Nonempty (AdjacentWitness markers source) := by
  constructor
  · intro adjacent
    exact adjacent.nonemptyWitness markersNodup
  · rintro ⟨witness⟩
    exact witness.source_hasAdjacentPair

end SemigroupBasis.CoRoots.Order6SporadicSection27
