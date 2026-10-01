import SemigroupBasis.CoRoots.Order6FactorPairS4_69S4_71CountBridge
import SemigroupBasis.Normalization.EventLinearExtensions

/-!
# Endpoint events for the `S4_69 x S4_71` normalizer

A count-reduced word contains each letter at most twice.  This module gives
each occurrence a canonical event name:

* the sole occurrence of a simple letter is a `simple` event;
* the earlier occurrence of a quadratic letter is a `first` event;
* the later occurrence of a quadratic letter is a `last` event.

The resulting list is duplicate-free and decodes to the original list of
letters.  Equal joint signatures give equal reduced multiplicities, hence
permutations of endpoint-event lists.

The precedence relation used by the final normalizer is deliberately kept
separate from this encoding.  In particular, the joint signature does not
fix every first-occurrence/simple-occurrence comparison.
-/

namespace SemigroupBasis.CoRoots.Order6FactorPairS4_69S4_71

open SemigroupBasis

/-- A name for one occurrence in a list whose multiplicities are at most two. -/
inductive EndpointEvent where
  | simple (letter : Nat)
  | first (letter : Nat)
  | last (letter : Nat)
  deriving DecidableEq, Repr

namespace EndpointEvent

/-- Forget the endpoint role and recover the underlying letter. -/
@[simp]
def letter : EndpointEvent → Nat
  | .simple tested => tested
  | .first tested => tested
  | .last tested => tested

end EndpointEvent

/-- Classify the displayed occurrence from its whole-list multiplicity and
the presence or absence of a later occurrence. -/
def endpointEventAt
    (whole : List Nat) (letter : Nat) (suffix : List Nat) :
    EndpointEvent :=
  if whole.count letter = 1 then
    .simple letter
  else if letter ∈ suffix then
    .first letter
  else
    .last letter

/-- Chronologically encode a suffix, classifying every occurrence relative
to the fixed whole list. -/
def encodeEndpointEventsAux
    (whole : List Nat) : List Nat → List EndpointEvent
  | [] => []
  | letter :: suffix =>
      endpointEventAt whole letter suffix ::
        encodeEndpointEventsAux whole suffix

/-- Chronological endpoint-event encoding of a reduced list. -/
def encodeEndpointEvents (letters : List Nat) : List EndpointEvent :=
  encodeEndpointEventsAux letters letters

/-- Decode endpoint events by forgetting their roles. -/
def decodeEndpointEvents (events : List EndpointEvent) : List Nat :=
  events.map EndpointEvent.letter

@[simp]
theorem decodeEndpointEvents_encodeAux
    (whole current : List Nat) :
    decodeEndpointEvents (encodeEndpointEventsAux whole current) =
      current := by
  induction current with
  | nil =>
      rfl
  | cons letter suffix inductionHypothesis =>
      rw [encodeEndpointEventsAux]
      simp only [decodeEndpointEvents, List.map_cons, List.cons.injEq]
      constructor
      · by_cases countOne : whole.count letter = 1
        · simp [endpointEventAt, countOne]
        · by_cases later : letter ∈ suffix
          · simp [endpointEventAt, countOne, later]
          · simp [endpointEventAt, countOne, later]
      · exact inductionHypothesis

/-- Encoding followed by decoding is exactly the identity, not merely a
permutation. -/
@[simp]
theorem decodeEndpointEvents_encode
    (letters : List Nat) :
    decodeEndpointEvents (encodeEndpointEvents letters) =
      letters := by
  exact decodeEndpointEvents_encodeAux letters letters

private theorem letter_mem_of_mem_encodeAux
    {whole current : List Nat} {event : EndpointEvent}
    (member : event ∈ encodeEndpointEventsAux whole current) :
    event.letter ∈ current := by
  have mapped :
      event.letter ∈
        (encodeEndpointEventsAux whole current).map
          EndpointEvent.letter :=
    List.mem_map.mpr ⟨event, member, rfl⟩
  rw [← decodeEndpointEvents_encodeAux whole current]
  exact mapped

private theorem simple_mem_implies_whole_count_one
    {whole current : List Nat} {tested : Nat}
    (member :
      EndpointEvent.simple tested ∈
        encodeEndpointEventsAux whole current) :
    whole.count tested = 1 := by
  induction current with
  | nil =>
      simpa [encodeEndpointEventsAux] using member
  | cons letter suffix inductionHypothesis =>
      simp only [encodeEndpointEventsAux, List.mem_cons] at member
      rcases member with headEqual | tailMember
      · unfold endpointEventAt at headEqual
        split at headEqual
        · cases headEqual
          assumption
        · split at headEqual <;> cases headEqual
      · exact inductionHypothesis tailMember

private theorem first_mem_implies_whole_count_ne_one
    {whole current : List Nat} {tested : Nat}
    (member :
      EndpointEvent.first tested ∈
        encodeEndpointEventsAux whole current) :
    whole.count tested ≠ 1 := by
  induction current with
  | nil =>
      simpa [encodeEndpointEventsAux] using member
  | cons letter suffix inductionHypothesis =>
      simp only [encodeEndpointEventsAux, List.mem_cons] at member
      rcases member with headEqual | tailMember
      · unfold endpointEventAt at headEqual
        split at headEqual
        · cases headEqual
        · split at headEqual
          · cases headEqual
            assumption
          · cases headEqual
      · exact inductionHypothesis tailMember

private theorem last_mem_implies_whole_count_ne_one
    {whole current : List Nat} {tested : Nat}
    (member :
      EndpointEvent.last tested ∈
        encodeEndpointEventsAux whole current) :
    whole.count tested ≠ 1 := by
  induction current with
  | nil =>
      simpa [encodeEndpointEventsAux] using member
  | cons letter suffix inductionHypothesis =>
      simp only [encodeEndpointEventsAux, List.mem_cons] at member
      rcases member with headEqual | tailMember
      · unfold endpointEventAt at headEqual
        split at headEqual
        · cases headEqual
        · split at headEqual
          · cases headEqual
          · cases headEqual
            assumption
      · exact inductionHypothesis tailMember

private theorem two_le_count_of_first_mem
    {whole : List Nat} {tested : Nat} :
    ∀ {current : List Nat},
      EndpointEvent.first tested ∈
          encodeEndpointEventsAux whole current →
        2 ≤ current.count tested
  | [], member => by
      simpa [encodeEndpointEventsAux] using member
  | letter :: suffix, member => by
      simp only [encodeEndpointEventsAux, List.mem_cons] at member
      rcases member with headEqual | tailMember
      · unfold endpointEventAt at headEqual
        split at headEqual
        · cases headEqual
        · split at headEqual
          · cases headEqual
            simp only [List.count_cons_self]
            exact
              Nat.succ_le_succ
                (List.count_pos_iff.mpr ‹tested ∈ suffix›)
          · cases headEqual
      · have tailBound :=
          two_le_count_of_first_mem tailMember
        by_cases equal : letter = tested
        · subst letter
          simp only [List.count_cons_self]
          omega
        · simpa [equal] using tailBound

private theorem simple_mem_of_whole_count_one
    {whole : List Nat} {tested : Nat}
    (countOne : whole.count tested = 1) :
    ∀ {current : List Nat},
      tested ∈ current →
        EndpointEvent.simple tested ∈
          encodeEndpointEventsAux whole current
  | [], member => by
      simpa using member
  | letter :: suffix, member => by
      rcases List.mem_cons.mp member with equal | tailMember
      · subst letter
        simp [encodeEndpointEventsAux, endpointEventAt, countOne]
      · exact
          List.mem_cons_of_mem
            (endpointEventAt whole letter suffix)
            (simple_mem_of_whole_count_one countOne tailMember)

private theorem first_mem_of_two_le_count
    {whole : List Nat} {tested : Nat}
    (wholeNotSimple : whole.count tested ≠ 1) :
    ∀ current : List Nat,
      2 ≤ current.count tested →
        EndpointEvent.first tested ∈
          encodeEndpointEventsAux whole current
  | [], bound => by
      simp at bound
  | letter :: suffix, bound => by
      by_cases equal : letter = tested
      · subst letter
        have later : tested ∈ suffix := by
          apply List.count_pos_iff.mp
          simp only [List.count_cons_self] at bound
          omega
        simp [encodeEndpointEventsAux, endpointEventAt,
          wholeNotSimple, later]
      · have tailBound : 2 ≤ suffix.count tested := by
          simpa [equal] using bound
        exact
          List.mem_cons_of_mem
            (endpointEventAt whole letter suffix)
            (first_mem_of_two_le_count
              wholeNotSimple suffix tailBound)

private theorem last_mem_of_mem
    {whole : List Nat} {tested : Nat}
    (wholeNotSimple : whole.count tested ≠ 1) :
    ∀ current : List Nat,
      tested ∈ current →
        EndpointEvent.last tested ∈
          encodeEndpointEventsAux whole current
  | [], member => by
      simpa using member
  | letter :: suffix, member => by
      by_cases equal : letter = tested
      · subst letter
        by_cases later : tested ∈ suffix
        · exact
            List.mem_cons_of_mem
              (endpointEventAt whole tested suffix)
              (last_mem_of_mem wholeNotSimple suffix later)
        · simp [encodeEndpointEventsAux, endpointEventAt,
            wholeNotSimple, later]
      · have tailMember : tested ∈ suffix := by
          exact
            (List.mem_cons.mp member).resolve_left (Ne.symm equal)
        exact
          List.mem_cons_of_mem
            (endpointEventAt whole letter suffix)
            (last_mem_of_mem wholeNotSimple suffix tailMember)

@[simp]
theorem simple_mem_encodeEndpointEvents_iff
    (letters : List Nat) (tested : Nat) :
    EndpointEvent.simple tested ∈ encodeEndpointEvents letters ↔
      letters.count tested = 1 := by
  constructor
  · exact simple_mem_implies_whole_count_one
  · intro countOne
    exact
      simple_mem_of_whole_count_one countOne
        (List.count_pos_iff.mp (by omega))

theorem first_mem_encodeEndpointEvents_iff
    {letters : List Nat}
    (twoLimited : ∀ letter, letters.count letter ≤ 2)
    (tested : Nat) :
    EndpointEvent.first tested ∈ encodeEndpointEvents letters ↔
      letters.count tested = 2 := by
  constructor
  · intro member
    have lower : 2 ≤ letters.count tested :=
      two_le_count_of_first_mem member
    exact Nat.le_antisymm (twoLimited tested) lower
  · intro countTwo
    exact
      first_mem_of_two_le_count
        (by omega) letters (by omega)

theorem last_mem_encodeEndpointEvents_iff
    {letters : List Nat}
    (twoLimited : ∀ letter, letters.count letter ≤ 2)
    (tested : Nat) :
    EndpointEvent.last tested ∈ encodeEndpointEvents letters ↔
      letters.count tested = 2 := by
  constructor
  · intro member
    have present : tested ∈ letters :=
      letter_mem_of_mem_encodeAux member
    have positive : 0 < letters.count tested :=
      List.count_pos_iff.mpr present
    have notSimple : letters.count tested ≠ 1 :=
      last_mem_implies_whole_count_ne_one member
    have upper := twoLimited tested
    omega
  · intro countTwo
    exact
      last_mem_of_mem
        (by omega) letters
        (List.count_pos_iff.mp (by omega))

private theorem encodeEndpointEventsAux_nodup
    {whole : List Nat}
    (twoLimited : ∀ tested, whole.count tested ≤ 2) :
    ∀ current : List Nat,
      (∀ tested, current.count tested ≤ whole.count tested) →
        (encodeEndpointEventsAux whole current).Nodup
  | [], _ => by
      simp [encodeEndpointEventsAux]
  | letter :: suffix, contained => by
      rw [encodeEndpointEventsAux, List.nodup_cons]
      constructor
      · unfold endpointEventAt
        split
        · intro member
          have later : letter ∈ suffix :=
            letter_mem_of_mem_encodeAux member
          have laterPositive : 0 < suffix.count letter :=
            List.count_pos_iff.mpr later
          have currentBound := contained letter
          simp only [List.count_cons_self] at currentBound
          omega
        · split
          · intro member
            have lower : 2 ≤ suffix.count letter :=
              two_le_count_of_first_mem member
            have currentBound := contained letter
            have wholeBound := twoLimited letter
            simp only [List.count_cons_self] at currentBound
            omega
          · intro member
            exact
              ‹letter ∉ suffix›
                (letter_mem_of_mem_encodeAux member)
      · apply
          encodeEndpointEventsAux_nodup
            twoLimited suffix
        intro tested
        have currentBound := contained tested
        by_cases equal : letter = tested
        · subst letter
          simp only [List.count_cons_self] at currentBound
          omega
        · simpa [equal] using currentBound

/-- The endpoint encoding of a two-limited list has no duplicate events. -/
theorem encodeEndpointEvents_nodup
    {letters : List Nat}
    (twoLimited : ∀ tested, letters.count tested ≤ 2) :
    (encodeEndpointEvents letters).Nodup := by
  exact
    encodeEndpointEventsAux_nodup
      twoLimited letters (fun _ => Nat.le_refl _)

/-- Endpoint events attached to a semigroup word. -/
def encodedWordEvents (word : Word Nat) : List EndpointEvent :=
  encodeEndpointEvents word.toList

@[simp]
theorem decode_encodedWordEvents (word : Word Nat) :
    decodeEndpointEvents (encodedWordEvents word) =
      word.toList := by
  exact decodeEndpointEvents_encode word.toList

theorem encodedWordEvents_nodup
    {word : Word Nat}
    (twoLimited : ∀ tested, word.toList.count tested ≤ 2) :
    (encodedWordEvents word).Nodup :=
  encodeEndpointEvents_nodup twoLimited

/-- On two-limited words, the capped multiplicity component of the joint
signature is exact multiplicity equality. -/
theorem reduced_count_eq_of_sameJointSignature
    {left right : Word Nat}
    (same : SameJointSignature left right)
    (leftTwoLimited :
      ∀ tested, left.toList.count tested ≤ 2)
    (rightTwoLimited :
      ∀ tested, right.toList.count tested ≤ 2)
    (tested : Nat) :
    left.toList.count tested =
      right.toList.count tested := by
  have capped := same.block.capped tested
  unfold S5_107.cappedMultiplicity at capped
  have leftBound := leftTwoLimited tested
  have rightBound := rightTwoLimited tested
  calc
    left.toList.count tested =
        Nat.min 2 (left.toList.count tested) :=
      (Nat.min_eq_right leftBound).symm
    _ = Nat.min 2 (right.toList.count tested) := capped
    _ = right.toList.count tested :=
      Nat.min_eq_right rightBound

private theorem endpointEvents_perm_of_nodup_mem
    {left right : List EndpointEvent}
    (leftNodup : left.Nodup)
    (rightNodup : right.Nodup)
    (sameMembers :
      ∀ event, event ∈ left ↔ event ∈ right) :
    left.Perm right := by
  rw [List.perm_iff_count]
  intro event
  rw [leftNodup.count, rightNodup.count]
  simp only [sameMembers event]

/-- Two count-reduced words with the same joint signature contain exactly
the same endpoint events. -/
theorem encodedWordEvents_perm
    {left right : Word Nat}
    (same : SameJointSignature left right)
    (leftTwoLimited :
      ∀ tested, left.toList.count tested ≤ 2)
    (rightTwoLimited :
      ∀ tested, right.toList.count tested ≤ 2) :
    (encodedWordEvents left).Perm
      (encodedWordEvents right) := by
  apply endpointEvents_perm_of_nodup_mem
    (encodedWordEvents_nodup leftTwoLimited)
    (encodedWordEvents_nodup rightTwoLimited)
  intro event
  have counts :=
    reduced_count_eq_of_sameJointSignature
      same leftTwoLimited rightTwoLimited
  cases event with
  | simple tested =>
      change
        (EndpointEvent.simple tested ∈
            encodeEndpointEvents left.toList) ↔
          EndpointEvent.simple tested ∈
            encodeEndpointEvents right.toList
      rw [
        simple_mem_encodeEndpointEvents_iff
          left.toList tested,
        simple_mem_encodeEndpointEvents_iff
          right.toList tested,
        counts tested]
  | first tested =>
      change
        (EndpointEvent.first tested ∈
            encodeEndpointEvents left.toList) ↔
          EndpointEvent.first tested ∈
            encodeEndpointEvents right.toList
      rw [
        first_mem_encodeEndpointEvents_iff
          leftTwoLimited tested,
        first_mem_encodeEndpointEvents_iff
          rightTwoLimited tested,
        counts tested]
  | last tested =>
      change
        (EndpointEvent.last tested ∈
            encodeEndpointEvents left.toList) ↔
          EndpointEvent.last tested ∈
            encodeEndpointEvents right.toList
      rw [
        last_mem_encodeEndpointEvents_iff
          leftTwoLimited tested,
        last_mem_encodeEndpointEvents_iff
          rightTwoLimited tested,
        counts tested]

/-! ## The maximal common chronological order -/

namespace EventOrder

universe u

variable {α : Type u}

/-- Strict chronological order induced by a list.  The recursive definition
records that the head precedes every member of the tail and preserves all
orders already present inside the tail. -/
def ChronologicallyBefore : List α → α → α → Prop
  | [], _, _ => False
  | head :: tail, earlier, later =>
      (earlier = head ∧ later ∈ tail) ∨
        ChronologicallyBefore tail earlier later

theorem chronologicallyBefore_left_mem
    {events : List α} {earlier later : α}
    (before : ChronologicallyBefore events earlier later) :
    earlier ∈ events := by
  induction events with
  | nil =>
      simpa [ChronologicallyBefore] using before
  | cons head tail inductionHypothesis =>
      simp only [ChronologicallyBefore] at before
      rcases before with ⟨rfl, _⟩ | tailBefore
      · exact List.Mem.head tail
      · exact
          List.Mem.tail head
            (inductionHypothesis tailBefore)

theorem chronologicallyBefore_right_mem
    {events : List α} {earlier later : α}
    (before : ChronologicallyBefore events earlier later) :
    later ∈ events := by
  induction events with
  | nil =>
      simpa [ChronologicallyBefore] using before
  | cons head tail inductionHypothesis =>
      simp only [ChronologicallyBefore] at before
      rcases before with ⟨_, laterMember⟩ | tailBefore
      · exact List.Mem.tail head laterMember
      · exact
          List.Mem.tail head
            (inductionHypothesis tailBefore)

/-- Every list is pairwise ordered by its own chronological relation. -/
theorem pairwise_chronologicallyBefore :
    ∀ events : List α,
      events.Pairwise (ChronologicallyBefore events)
  | [] =>
      List.Pairwise.nil
  | head :: tail => by
      apply List.Pairwise.cons
      · intro later member
        exact Or.inl ⟨rfl, member⟩
      · exact
          (pairwise_chronologicallyBefore tail).imp <| by
            intro earlier later before
            exact Or.inr before

/-- Chronological order is asymmetric on a duplicate-free list. -/
theorem chronologicallyBefore_asymm
    {events : List α} (nodup : events.Nodup)
    {earlier later : α}
    (forward : ChronologicallyBefore events earlier later) :
    ¬ ChronologicallyBefore events later earlier := by
  induction events with
  | nil =>
      simpa [ChronologicallyBefore] using forward
  | cons head tail inductionHypothesis =>
      have headAbsent := (List.nodup_cons.mp nodup).1
      have tailNodup := (List.nodup_cons.mp nodup).2
      simp only [ChronologicallyBefore] at forward ⊢
      intro reverse
      rcases forward with ⟨rfl, laterMember⟩ | tailForward
      · rcases reverse with ⟨laterEqual, headMember⟩ | tailReverse
        · exact headAbsent headMember
        · exact
            headAbsent
              (chronologicallyBefore_right_mem tailReverse)
      · rcases reverse with ⟨laterEqual, earlierMember⟩ | tailReverse
        · subst later
          exact
            headAbsent
              (chronologicallyBefore_right_mem tailForward)
        · exact
            inductionHypothesis tailNodup
              tailForward tailReverse

/-- Two distinct members of one list occur in one of the two strict orders. -/
theorem chronologicallyBefore_total
    (events : List α) {left right : α}
    (different : left ≠ right)
    (leftMember : left ∈ events)
    (rightMember : right ∈ events) :
    ChronologicallyBefore events left right ∨
      ChronologicallyBefore events right left := by
  induction events with
  | nil =>
      simpa using leftMember
  | cons head tail inductionHypothesis =>
      rcases List.mem_cons.mp leftMember with leftHead | leftTail
      · subst left
        rcases List.mem_cons.mp rightMember with rightHead | rightTail
        · subst right
          exact (different rfl).elim
        · exact Or.inl (Or.inl ⟨rfl, rightTail⟩)
      · rcases List.mem_cons.mp rightMember with rightHead | rightTail
        · subst right
          exact Or.inr (Or.inl ⟨rfl, leftTail⟩)
        · rcases
            inductionHypothesis
              leftTail rightTail with
            forward | reverse
          · exact Or.inl (Or.inr forward)
          · exact Or.inr (Or.inr reverse)

/-- The largest strict event order contained in the chronological orders of
both lists. -/
def CommonPrecedes
    (source target : List α) (earlier later : α) : Prop :=
  ChronologicallyBefore source earlier later ∧
    ChronologicallyBefore target earlier later

/-- The source is a linear extension of the maximal common order. -/
theorem source_linearExtension
    {source target : List α}
    (sourceNodup : source.Nodup) :
    SemigroupBasis.Normalization.EventLinearExtensions.LinearExtension
      (CommonPrecedes source target) source := by
  refine ⟨sourceNodup, ?_⟩
  apply (pairwise_chronologicallyBefore source).imp
  intro earlier later forward reverse
  exact
    (chronologicallyBefore_asymm
      sourceNodup forward) reverse.1

/-- The target is a linear extension of the same maximal common order. -/
theorem target_linearExtension
    {source target : List α}
    (targetNodup : target.Nodup) :
    SemigroupBasis.Normalization.EventLinearExtensions.LinearExtension
      (CommonPrecedes source target) target := by
  refine ⟨targetNodup, ?_⟩
  apply (pairwise_chronologicallyBefore target).imp
  intro earlier later forward reverse
  exact
    (chronologicallyBefore_asymm
      targetNodup forward) reverse.2

/-- Opposite chronological orders make two events incomparable in the common
order. -/
theorem incomparable_of_opposite_orders
    {source target : List α} {left right : α}
    (sourceNodup : source.Nodup)
    (targetNodup : target.Nodup)
    (sourceForward :
      ChronologicallyBefore source left right)
    (targetReverse :
      ChronologicallyBefore target right left) :
    SemigroupBasis.Normalization.EventLinearExtensions.Incomparable
      (CommonPrecedes source target) left right := by
  constructor
  · intro commonForward
    exact
      (chronologicallyBefore_asymm
        targetNodup targetReverse) commonForward.2
  · intro commonReverse
    exact
      (chronologicallyBefore_asymm
        sourceNodup sourceForward) commonReverse.1

/-- For two distinct events present in both lists, incomparability in the
maximal common order is exactly disagreement of chronological orientation. -/
theorem incomparable_order_disagreement
    {source target : List α} {left right : α}
    (sourceNodup : source.Nodup)
    (targetNodup : target.Nodup)
    (different : left ≠ right)
    (leftSource : left ∈ source)
    (rightSource : right ∈ source)
    (leftTarget : left ∈ target)
    (rightTarget : right ∈ target)
    (incomparable :
      SemigroupBasis.Normalization.EventLinearExtensions.Incomparable
        (CommonPrecedes source target) left right) :
    (ChronologicallyBefore source left right ∧
        ChronologicallyBefore target right left) ∨
      (ChronologicallyBefore source right left ∧
        ChronologicallyBefore target left right) := by
  rcases chronologicallyBefore_total
      source different leftSource rightSource with
    sourceForward | sourceReverse
  · rcases chronologicallyBefore_total
        target different leftTarget rightTarget with
      targetForward | targetReverse
    · exact (incomparable.1 ⟨sourceForward, targetForward⟩).elim
    · exact Or.inl ⟨sourceForward, targetReverse⟩
  · rcases chronologicallyBefore_total
        target different leftTarget rightTarget with
      targetForward | targetReverse
    · exact Or.inr ⟨sourceReverse, targetForward⟩
    · exact (incomparable.2 ⟨sourceReverse, targetReverse⟩).elim

end EventOrder

open EventOrder

/-- The common chronological precedence relation for two reduced words. -/
def jointEventPrecedes
    (left right : Word Nat) :
    EndpointEvent → EndpointEvent → Prop :=
  CommonPrecedes
    (encodedWordEvents left) (encodedWordEvents right)

/-- The two reduced event lists are linear extensions of one common relation.
Together with `encodedWordEvents_perm`, this is the exact input expected by
`connected_by_adjacent_incomparable_swaps`. -/
theorem encodedWordEvents_commonLinearExtensions
    {left right : Word Nat}
    (leftTwoLimited :
      ∀ tested, left.toList.count tested ≤ 2)
    (rightTwoLimited :
      ∀ tested, right.toList.count tested ≤ 2) :
    SemigroupBasis.Normalization.EventLinearExtensions.LinearExtension
        (jointEventPrecedes left right)
        (encodedWordEvents left) ∧
      SemigroupBasis.Normalization.EventLinearExtensions.LinearExtension
        (jointEventPrecedes left right)
        (encodedWordEvents right) :=
  ⟨source_linearExtension
      (encodedWordEvents_nodup leftTwoLimited),
    target_linearExtension
      (encodedWordEvents_nodup rightTwoLimited)⟩

/-- Pure combinatorial composition: two reduced words with the same joint
signature are connected by adjacent swaps that reverse their chronological
order.  This theorem does not assert that every such move is
quadratic/quadratic; guarded first-endpoint/simple-event moves form the
additional glue lane. -/
theorem encodedWordEvents_connectedByIncomparableSwaps
    {left right : Word Nat}
    (same : SameJointSignature left right)
    (leftTwoLimited :
      ∀ tested, left.toList.count tested ≤ 2)
    (rightTwoLimited :
      ∀ tested, right.toList.count tested ≤ 2) :
    SemigroupBasis.Normalization.EventLinearExtensions.AdjacentSwapClosure
      (SemigroupBasis.Normalization.EventLinearExtensions.Incomparable
        (jointEventPrecedes left right))
      (encodedWordEvents left)
      (encodedWordEvents right) := by
  rcases
      encodedWordEvents_commonLinearExtensions
        leftTwoLimited rightTwoLimited with
    ⟨leftExtension, rightExtension⟩
  exact
    SemigroupBasis.Normalization.EventLinearExtensions.connected_by_adjacent_incomparable_swaps
      leftExtension rightExtension
      (encodedWordEvents_perm
        same leftTwoLimited rightTwoLimited)

private theorem not_last_before_first_encodeAux
    {whole : List Nat} {tested : Nat} :
    ∀ current : List Nat,
      ¬ EventOrder.ChronologicallyBefore
          (encodeEndpointEventsAux whole current)
          (.last tested) (.first tested)
  | [] => by
      simp [encodeEndpointEventsAux,
        EventOrder.ChronologicallyBefore]
  | letter :: suffix => by
      intro before
      simp only [encodeEndpointEventsAux,
        EventOrder.ChronologicallyBefore] at before
      rcases before with ⟨headEqual, firstMember⟩ | tailBefore
      · unfold endpointEventAt at headEqual
        split at headEqual
        · cases headEqual
        · split at headEqual
          · cases headEqual
          · cases headEqual
            exact
              ‹tested ∉ suffix›
                (letter_mem_of_mem_encodeAux firstMember)
      · exact
          not_last_before_first_encodeAux
            suffix tailBefore

/-- In every reduced encoding the first endpoint of a quadratic letter
strictly precedes its last endpoint. -/
theorem first_before_last_encoded
    {letters : List Nat}
    (twoLimited : ∀ tested, letters.count tested ≤ 2)
    {tested : Nat}
    (countTwo : letters.count tested = 2) :
    EventOrder.ChronologicallyBefore
      (encodeEndpointEvents letters)
      (.first tested) (.last tested) := by
  have firstMember :
      EndpointEvent.first tested ∈
        encodeEndpointEvents letters :=
    (first_mem_encodeEndpointEvents_iff
      twoLimited tested).2 countTwo
  have lastMember :
      EndpointEvent.last tested ∈
        encodeEndpointEvents letters :=
    (last_mem_encodeEndpointEvents_iff
      twoLimited tested).2 countTwo
  have different :
      EndpointEvent.first tested ≠
        EndpointEvent.last tested := by
    intro equal
    cases equal
  rcases
      EventOrder.chronologicallyBefore_total
        (encodeEndpointEvents letters)
        different firstMember lastMember with
    forward | reverse
  · exact forward
  · exact
      (not_last_before_first_encodeAux
        letters reverse).elim

private theorem endpointEvent_eq_or_endpoint_pair
    {letters : List Nat}
    (twoLimited : ∀ tested, letters.count tested ≤ 2)
    {left right : EndpointEvent}
    (leftMember : left ∈ encodeEndpointEvents letters)
    (rightMember : right ∈ encodeEndpointEvents letters)
    (sameLetter : left.letter = right.letter) :
    left = right ∨
      (∃ tested,
        left = .first tested ∧ right = .last tested) ∨
      (∃ tested,
        left = .last tested ∧ right = .first tested) := by
  cases left with
  | simple leftLetter =>
      cases right with
      | simple rightLetter =>
          simp only [EndpointEvent.letter] at sameLetter
          subst rightLetter
          exact Or.inl rfl
      | first rightLetter =>
          simp only [EndpointEvent.letter] at sameLetter
          subst rightLetter
          have simpleCount :=
            (simple_mem_encodeEndpointEvents_iff
              letters leftLetter).1 leftMember
          have firstCount :=
            (first_mem_encodeEndpointEvents_iff
              twoLimited leftLetter).1 rightMember
          omega
      | last rightLetter =>
          simp only [EndpointEvent.letter] at sameLetter
          subst rightLetter
          have simpleCount :=
            (simple_mem_encodeEndpointEvents_iff
              letters leftLetter).1 leftMember
          have lastCount :=
            (last_mem_encodeEndpointEvents_iff
              twoLimited leftLetter).1 rightMember
          omega
  | first leftLetter =>
      cases right with
      | simple rightLetter =>
          simp only [EndpointEvent.letter] at sameLetter
          subst rightLetter
          have firstCount :=
            (first_mem_encodeEndpointEvents_iff
              twoLimited leftLetter).1 leftMember
          have simpleCount :=
            (simple_mem_encodeEndpointEvents_iff
              letters leftLetter).1 rightMember
          omega
      | first rightLetter =>
          simp only [EndpointEvent.letter] at sameLetter
          subst rightLetter
          exact Or.inl rfl
      | last rightLetter =>
          simp only [EndpointEvent.letter] at sameLetter
          subst rightLetter
          exact
            Or.inr <| Or.inl
              ⟨leftLetter, rfl, rfl⟩
  | last leftLetter =>
      cases right with
      | simple rightLetter =>
          simp only [EndpointEvent.letter] at sameLetter
          subst rightLetter
          have lastCount :=
            (last_mem_encodeEndpointEvents_iff
              twoLimited leftLetter).1 leftMember
          have simpleCount :=
            (simple_mem_encodeEndpointEvents_iff
              letters leftLetter).1 rightMember
          omega
      | first rightLetter =>
          simp only [EndpointEvent.letter] at sameLetter
          subst rightLetter
          exact
            Or.inr <| Or.inr
              ⟨leftLetter, rfl, rfl⟩
      | last rightLetter =>
          simp only [EndpointEvent.letter] at sameLetter
          subst rightLetter
          exact Or.inl rfl

/-- Correct replacement for the disproved quadratic-only anchor.

Distinct incomparable encoded events always decode to distinct letters.  The
theorem intentionally does not claim that both letters are quadratic:
first-endpoint/simple-event reversals are possible under
`SameJointSignature`. -/
theorem incomparable_decode_distinct
    {left right : Word Nat}
    (same : SameJointSignature left right)
    (leftTwoLimited :
      ∀ tested, left.toList.count tested ≤ 2)
    (rightTwoLimited :
      ∀ tested, right.toList.count tested ≤ 2)
    {leftEvent rightEvent : EndpointEvent}
    (different : leftEvent ≠ rightEvent)
    (leftMember :
      leftEvent ∈ encodedWordEvents left)
    (rightMember :
      rightEvent ∈ encodedWordEvents left)
    (incomparable :
      SemigroupBasis.Normalization.EventLinearExtensions.Incomparable
        (jointEventPrecedes left right)
        leftEvent rightEvent) :
    leftEvent.letter ≠ rightEvent.letter := by
  intro sameLetter
  rcases
      endpointEvent_eq_or_endpoint_pair
        leftTwoLimited leftMember rightMember sameLetter with
    equal | firstLast | lastFirst
  · exact different equal
  · rcases firstLast with
      ⟨tested, rfl, rfl⟩
    have leftCount :
        left.toList.count tested = 2 :=
      (first_mem_encodeEndpointEvents_iff
        leftTwoLimited tested).1 leftMember
    have rightCount :
        right.toList.count tested = 2 :=
      calc
        right.toList.count tested =
            left.toList.count tested :=
          (reduced_count_eq_of_sameJointSignature
            same leftTwoLimited rightTwoLimited tested).symm
        _ = 2 := leftCount
    exact incomparable.1
      ⟨first_before_last_encoded
          leftTwoLimited leftCount,
        first_before_last_encoded
          rightTwoLimited rightCount⟩
  · rcases lastFirst with
      ⟨tested, rfl, rfl⟩
    have leftCount :
        left.toList.count tested = 2 :=
      (last_mem_encodeEndpointEvents_iff
        leftTwoLimited tested).1 leftMember
    have rightCount :
        right.toList.count tested = 2 :=
      calc
        right.toList.count tested =
            left.toList.count tested :=
          (reduced_count_eq_of_sameJointSignature
            same leftTwoLimited rightTwoLimited tested).symm
        _ = 2 := leftCount
    exact incomparable.2
      ⟨first_before_last_encoded
          leftTwoLimited leftCount,
        first_before_last_encoded
          rightTwoLimited rightCount⟩

end SemigroupBasis.CoRoots.Order6FactorPairS4_69S4_71
