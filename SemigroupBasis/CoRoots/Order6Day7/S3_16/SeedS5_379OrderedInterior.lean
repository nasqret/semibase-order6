import SemigroupBasis.CoRoots.Order6Day7.S3_16.SeedS5_379OrderedEnvelope

/-!
# Complete ordered interior comparison for S3_16 × S5_379

The frozen laws gather repeated interior letters at their FIRST occurrence.
They never sort different first occurrences. Endpoint deletion and a genuine
first/last-occurrence cap reduce arbitrary envelopes to two-limited interiors;
induction then compares them from their actual first order and exact counts.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank105.OrderedInterior

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots
open OrderedEnvelope

def without (removed : Nat) (letters : List Nat) : List Nat :=
  letters.filter (fun letter => decide (letter ≠ removed))

theorem count_without (removed tested : Nat) (letters : List Nat) :
    (without removed letters).count tested = if tested = removed then 0 else letters.count tested := by
  by_cases equal : tested = removed
  · subst tested
    rw [if_pos rfl]
    apply List.count_eq_zero.mpr
    simp [without]
  · rw [if_neg equal]
    exact List.count_filter (p := fun letter => decide (letter ≠ removed)) (by simp [equal])

theorem without_eq_self {removed : Nat} {letters : List Nat} (absent : removed ∉ letters) :
    without removed letters = letters := by
  apply List.filter_eq_self.mpr
  intro letter member
  apply decide_eq_true
  intro equal
  subst letter
  exact absent member

theorem splitOnce {letter : Nat} {letters : List Nat} (count : letters.count letter = 1) :
    ∃ pre after, letters = pre ++ letter :: after ∧ without letter letters = pre ++ after := by
  have member : letter ∈ letters := List.count_pos_iff.mp (by omega)
  obtain ⟨pre, after, shape⟩ := List.append_of_mem member
  have total : pre.count letter + (after.count letter + 1) = 1 := by
    simpa [shape, List.count_append, List.count_cons_self] using count
  have preAbsent : letter ∉ pre := List.count_eq_zero.mp (by omega)
  have afterAbsent : letter ∉ after := List.count_eq_zero.mp (by omega)
  have preFilter := without_eq_self preAbsent
  have afterFilter := without_eq_self afterAbsent
  refine ⟨pre, after, shape, ?_⟩
  simp only [without] at preFilter afterFilter
  simp only [without, shape, List.filter_append, List.filter_cons, ne_self_iff_false,
    decide_false, Bool.false_eq_true, if_false, preFilter, afterFilter]

def headBlock (letter : Nat) (tail : List Nat) : List Nat :=
  if letter ∈ tail then [letter, letter] else [letter]

theorem gatherHead (endpoint letter : Nat) (tail : List Nat) (limited : tail.count letter ≤ 1) :
    ListDerives (endpoint :: letter :: tail ++ [endpoint])
      (endpoint :: headBlock letter tail ++ without letter tail ++ [endpoint]) := by
  by_cases member : letter ∈ tail
  · have count : tail.count letter = 1 := by
      have := List.count_pos_iff.mpr member
      omega
    obtain ⟨pre, after, shape, filtered⟩ := splitOnce count
    rw [headBlock, if_pos member, filtered]
    simpa [shape, List.append_assoc] using listGather endpoint letter pre after
  · rw [headBlock, if_neg member, without_eq_self member]
    simpa using S5_107.ListDerives.refl (basis := basis) (endpoint :: letter :: tail ++ [endpoint])

private theorem filteredTailLimited {letter : Nat} {tail : List Nat}
    (limited : ∀ tested, (letter :: tail).count tested ≤ 2) :
    ∀ tested, (without letter tail).count tested ≤ 2 := by
  intro tested
  by_cases equal : tested = letter
  · simp [count_without, equal]
  · rw [count_without, if_neg equal]
    simpa only [List.count_cons_of_ne (Ne.symm equal)] using limited tested

/-- Unrestricted comparison inside a fixed endpoint envelope. The only
invariants are actual first-occurrence order and exact two-limited counts. -/
theorem compareTwoLimited (endpoint : Nat) (left right : List Nat)
    (leftLimited : ∀ tested, left.count tested ≤ 2)
    (rightLimited : ∀ tested, right.count tested ≤ 2)
    (order : firstOccurrenceSequence left = firstOccurrenceSequence right)
    (counts : ∀ tested, left.count tested = right.count tested) :
    ListDerives (endpoint :: left ++ [endpoint]) (endpoint :: right ++ [endpoint]) := by
  cases left with
  | nil =>
      cases right with
      | nil => exact S5_107.ListDerives.refl _
      | cons letter rest => simp [firstOccurrenceSequence] at order
  | cons letter tail =>
      cases right with
      | nil => simp [firstOccurrenceSequence] at order
      | cons other rest =>
          have heads : letter = other := (List.cons.inj order).1
          subst other
          have tailOrder := (List.cons.inj order).2
          have leftHeadBound : tail.count letter ≤ 1 := by
            have bound := leftLimited letter
            simp only [List.count_cons_self] at bound
            omega
          have rightHeadBound : rest.count letter ≤ 1 := by
            have bound := rightLimited letter
            simp only [List.count_cons_self] at bound
            omega
          have headCounts : tail.count letter = rest.count letter := by
            have equal := counts letter
            simp only [List.count_cons_self] at equal
            omega
          have membership : letter ∈ tail ↔ letter ∈ rest := by
            constructor
            · intro member
              apply List.count_pos_iff.mp
              rw [← headCounts]
              exact List.count_pos_iff.mpr member
            · intro member
              apply List.count_pos_iff.mp
              rw [headCounts]
              exact List.count_pos_iff.mpr member
          have blockEqual : headBlock letter tail = headBlock letter rest := by
            by_cases member : letter ∈ tail
            · simp [headBlock, member, membership.mp member]
            · have absent : letter ∉ rest := fun h => member (membership.mpr h)
              simp [headBlock, member, absent]
          have filteredOrder :
              firstOccurrenceSequence (without letter tail) =
                firstOccurrenceSequence (without letter rest) := by
            simpa only [without, firstOccurrenceSequence_filter] using tailOrder
          have filteredCounts : ∀ tested,
              (without letter tail).count tested = (without letter rest).count tested := by
            intro tested
            by_cases equal : tested = letter
            · simp [count_without, equal]
            · rw [count_without, count_without, if_neg equal, if_neg equal]
              simpa only [List.count_cons_of_ne (Ne.symm equal)] using counts tested
          have core := compareTwoLimited endpoint (without letter tail) (without letter rest)
            (filteredTailLimited leftLimited) (filteredTailLimited rightLimited) filteredOrder filteredCounts
          have lifted := listInteriorPrefix endpoint (headBlock letter tail) [] core
          have first := gatherHead endpoint letter tail leftHeadBound
          have last := gatherHead endpoint letter rest rightHeadBound
          rw [← blockEqual] at last
          have middle :
              ListDerives (endpoint :: headBlock letter tail ++ without letter tail ++ [endpoint])
                (endpoint :: headBlock letter tail ++ without letter rest ++ [endpoint]) := by
            simpa [List.append_assoc] using lifted
          exact first.trans (middle.trans last.symm)
termination_by left.length
decreasing_by
  all_goals
    have bound := List.length_filter_le (fun tested => decide (tested ≠ letter)) tail
    simp_all [without]
    omega

/-- Remove all interior occurrences of the already-returned endpoint. -/
theorem listRemoveEndpoint (endpoint : Nat) : ∀ (interior suffix : List Nat),
    ListDerives (endpoint :: interior ++ endpoint :: suffix)
      (endpoint :: without endpoint interior ++ endpoint :: suffix)
  | [], suffix => S5_107.ListDerives.refl _
  | letter :: rest, suffix => by
      by_cases equal : letter = endpoint
      · subst letter
        have deletion := (listDeleteMiddle endpoint [] rest).append suffix
        have recurse := listRemoveEndpoint endpoint rest suffix
        have aligned : ListDerives (endpoint :: endpoint :: rest ++ endpoint :: suffix)
            (endpoint :: rest ++ endpoint :: suffix) := by
          simpa [List.append_assoc] using deletion
        simpa [without, List.append_assoc] using aligned.trans recurse
      · have recurse := listRemoveEndpoint endpoint rest suffix
        have lifted := listInteriorPrefix endpoint [letter] suffix recurse
        simpa [without, equal] using lifted

private theorem deleteCurrent (pre suffix : List Nat) (letter : Nat)
    (past : letter ∈ pre) (future : letter ∈ suffix) :
    ListDerives (pre ++ letter :: suffix) (pre ++ suffix) := by
  obtain ⟨before, firstGap, preShape⟩ := List.append_of_mem past
  obtain ⟨secondGap, after, suffixShape⟩ := List.append_of_mem future
  rw [preShape, suffixShape]
  simpa [List.append_assoc] using (listDeleteMiddle letter firstGap secondGap).context before after

private theorem capAux (pre seen : List Nat) (seenInPre : ∀ tested ∈ seen, tested ∈ pre) :
    ∀ suffix : List Nat, ListDerives (pre ++ suffix) (pre ++ uniqueSeparatorEndpointCapAux seen suffix)
  | [] => by simpa using S5_107.ListDerives.refl (basis := basis) pre
  | letter :: rest => by
      by_cases middle : letter ∈ seen ∧ letter ∈ rest
      · have inPre : letter ∈ pre := seenInPre letter middle.1
        have deletion := deleteCurrent pre rest letter inPre middle.2
        have nextSeen : ∀ tested ∈ letter :: seen, tested ∈ pre := by
          intro tested member
          rcases List.mem_cons.mp member with rfl | member
          · exact inPre
          · exact seenInPre tested member
        have recurse := capAux pre (letter :: seen) nextSeen rest
        rw [uniqueSeparatorEndpointCapAux, if_pos middle]
        exact deletion.trans recurse
      · have nextSeen : ∀ tested ∈ letter :: seen, tested ∈ pre ++ [letter] := by
          intro tested member
          rcases List.mem_cons.mp member with rfl | member
          · exact List.mem_append_right pre (List.Mem.head [])
          · exact List.mem_append_left [letter] (seenInPre tested member)
        have recurse := capAux (pre ++ [letter]) (letter :: seen) nextSeen rest
        rw [uniqueSeparatorEndpointCapAux, if_neg middle]
        simpa [List.append_assoc] using recurse

theorem listCapScan (letters : List Nat) : ListDerives letters (S5_379.capScan letters) := by
  simpa [S5_379.capScan, uniqueSeparatorEndpointCap] using capAux [] [] (by simp) letters

def normalizedInterior (endpoint : Nat) (interior : List Nat) : List Nat :=
  S5_379.capScan (without endpoint interior)

theorem listNormalizeEnvelope (endpoint : Nat) (interior : List Nat) :
    ListDerives (endpoint :: interior ++ [endpoint])
      (endpoint :: normalizedInterior endpoint interior ++ [endpoint]) := by
  have removed := listRemoveEndpoint endpoint interior []
  have capped := (listCapScan (without endpoint interior)).context [endpoint] [endpoint]
  simpa [normalizedInterior, List.append_assoc] using removed.trans capped

theorem normalizedInterior_absent (endpoint : Nat) (interior : List Nat) :
    endpoint ∉ normalizedInterior endpoint interior := by
  intro member
  have filtered := (S5_379.mem_capScan_iff endpoint (without endpoint interior)).mp member
  simp [without] at filtered

theorem normalizedInterior_limited (endpoint : Nat) (interior : List Nat) :
    ∀ tested, (normalizedInterior endpoint interior).count tested ≤ 2 := by
  intro tested
  exact S5_379.capScan_count_le_two tested (without endpoint interior)

theorem existsNormalizedEnvelope (head next : Nat) (rest : List Nat)
    (connected : ConnectedComponentSupportConnected (head :: next :: rest)) :
    ∃ interior,
      ListDerives (head :: next :: rest) (head :: interior ++ [head]) ∧
      head ∉ interior ∧ (∀ tested, interior.count tested ≤ 2) := by
  obtain ⟨raw, derivation⟩ := existsConnectedEnvelope head next rest connected
  exact ⟨normalizedInterior head raw, derivation.trans (listNormalizeEnvelope head raw),
    normalizedInterior_absent head raw, normalizedInterior_limited head raw⟩

theorem compareNormalizedEnvelopes (endpoint : Nat) (left right : List Nat)
    (leftAbsent : endpoint ∉ left) (rightAbsent : endpoint ∉ right)
    (leftLimited : ∀ tested, left.count tested ≤ 2)
    (rightLimited : ∀ tested, right.count tested ≤ 2)
    (order : firstOccurrenceSequence (endpoint :: left ++ [endpoint]) =
      firstOccurrenceSequence (endpoint :: right ++ [endpoint]))
    (counts : ∀ tested, min ((endpoint :: left ++ [endpoint]).count tested) 2 =
      min ((endpoint :: right ++ [endpoint]).count tested) 2) :
    ListDerives (endpoint :: left ++ [endpoint]) (endpoint :: right ++ [endpoint]) := by
  have leftFilter := without_eq_self leftAbsent
  have rightFilter := without_eq_self rightAbsent
  simp only [without] at leftFilter rightFilter
  have innerOrder : firstOccurrenceSequence left = firstOccurrenceSequence right := by
    have filtered := congrArg (List.filter (fun letter => decide (letter ≠ endpoint))) order
    rw [← firstOccurrenceSequence_filter, ← firstOccurrenceSequence_filter] at filtered
    simpa only [List.filter_append, List.filter_cons, List.filter_nil, ne_self_iff_false,
      decide_false, Bool.false_eq_true, if_false, List.append_nil, leftFilter, rightFilter] using filtered
  have innerCounts : ∀ tested, left.count tested = right.count tested := by
    intro tested
    by_cases equal : tested = endpoint
    · subst tested
      rw [List.count_eq_zero.mpr leftAbsent, List.count_eq_zero.mpr rightAbsent]
    · have outer := counts tested
      simpa [List.count_append, List.count_cons_of_ne (Ne.symm equal), equal,
        Nat.min_eq_left (leftLimited tested), Nat.min_eq_left (rightLimited tested)] using outer
  exact compareTwoLimited endpoint left right leftLimited rightLimited innerOrder innerCounts

end SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank105.OrderedInterior
