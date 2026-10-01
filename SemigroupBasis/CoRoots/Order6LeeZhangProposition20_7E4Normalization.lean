import SemigroupBasis.CoRoots.Order6LeeZhangProposition20_7E4Canonical
import SemigroupBasis.CoRoots.Order6LeeZhangProposition20_7E4Derivations

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6LeeZhangProposition20_7E4

open SemigroupBasis

private instance instDecidableSimple
    (whole : List Nat) (letter : Nat) : Decidable (Simple whole letter) := by
  unfold Simple
  infer_instance

/-!
# Lee--Zhang Proposition 20.7 / E4: unrestricted normalization

This file reconstructs Lemmas 20.10--20.12 from the direct laws (20.6).
The occurrence decomposition below freezes simplicity in the source word.
Every movement of a later non-simple marker is justified by one of the two
literal guarded alternatives (20.6d) or (20.6e); no unguarded interchange is
introduced.  Power contraction is used only after three displayed marker
occurrences, with the rank-dependent endpoint required by (Ri3)--(Ri5).
-/

/-! ## The simple-gap / non-simple-marker parser -/

/-- One displayed factor `sᵢ xᵢ`, with the marker stored separately. -/
structure MarkedFactor where
  gap : List Nat
  marker : Nat
deriving DecidableEq, Repr

namespace MarkedFactor

/-- Add one globally simple letter to the left of a factor's gap. -/
def prependGap (letter : Nat) (factor : MarkedFactor) : MarkedFactor :=
  { gap := letter :: factor.gap
    marker := factor.marker }

@[simp] theorem prependGap_gap
    (letter : Nat) (factor : MarkedFactor) :
    (prependGap letter factor).gap = letter :: factor.gap :=
  rfl

@[simp] theorem prependGap_marker
    (letter : Nat) (factor : MarkedFactor) :
    (prependGap letter factor).marker = factor.marker :=
  rfl

end MarkedFactor

/-- Literal rendering of one factor `sᵢ xᵢ`. -/
def renderMarkedFactor (factor : MarkedFactor) : List Nat :=
  factor.gap ++ [factor.marker]

/-- Literal rendering of a factor sequence. -/
def renderMarkedFactors : List MarkedFactor → List Nat
  | [] => []
  | factor :: rest =>
      renderMarkedFactor factor ++ renderMarkedFactors rest

@[simp] theorem renderMarkedFactors_nil :
    renderMarkedFactors [] = [] :=
  rfl

@[simp] theorem renderMarkedFactors_cons
    (factor : MarkedFactor) (rest : List MarkedFactor) :
    renderMarkedFactors (factor :: rest) =
      factor.gap ++ factor.marker :: renderMarkedFactors rest := by
  simp [renderMarkedFactors, renderMarkedFactor, List.append_assoc]

theorem renderMarkedFactors_append
    (left right : List MarkedFactor) :
    renderMarkedFactors (left ++ right) =
      renderMarkedFactors left ++ renderMarkedFactors right := by
  induction left with
  | nil => rfl
  | cons factor rest ih =>
      simp [renderMarkedFactors, renderMarkedFactor, ih,
        List.append_assoc]

/-- The marker occurrence sequence of a parsed factor list. -/
def markedMarkers (factors : List MarkedFactor) : List Nat :=
  factors.map MarkedFactor.marker

/-- The globally simple material carried by gaps and the terminal suffix. -/
def markedSimpleBank
    (factors : List MarkedFactor) (suffix : List Nat) : List Nat :=
  (factors.map MarkedFactor.gap).flatten ++ suffix

/-- Parse a suffix using multiplicities frozen in `whole`.

Simple letters are attached to the next non-simple marker.  Simple letters
after the final marker are retained in the second component. -/
def markedParse (whole : List Nat) :
    List Nat → List MarkedFactor × List Nat
  | [] => ([], [])
  | letter :: rest =>
      match markedParse whole rest with
      | ([], suffix) =>
          if Simple whole letter then
            ([], letter :: suffix)
          else
            ([{ gap := [], marker := letter }], suffix)
      | (first :: tail, suffix) =>
          if Simple whole letter then
            (MarkedFactor.prependGap letter first :: tail, suffix)
          else
            ({ gap := [], marker := letter } :: first :: tail, suffix)

/-- The parser is a literal reconstruction, not a semantic quotient. -/
theorem renderMarkedParse (whole : List Nat) :
    ∀ remaining : List Nat,
      renderMarkedFactors (markedParse whole remaining).1 ++
          (markedParse whole remaining).2 = remaining
  | [] => rfl
  | letter :: rest => by
      have ih := renderMarkedParse whole rest
      rw [markedParse]
      cases parsed : markedParse whole rest with
      | mk factors suffix =>
          rw [parsed] at ih
          cases factors with
          | nil =>
              simp only [renderMarkedFactors, List.nil_append] at ih
              by_cases simple : Simple whole letter
              · simp [simple, renderMarkedFactors, ih]
              · simp [simple, renderMarkedFactors, renderMarkedFactor,
                  ih]
          | cons first tail =>
              simp only [renderMarkedFactors, renderMarkedFactor,
                List.append_assoc, List.cons_append, List.nil_append] at ih
              by_cases simple : Simple whole letter
              · simp [simple, renderMarkedFactors, renderMarkedFactor,
                  MarkedFactor.prependGap, ih, List.append_assoc]
              · simp [simple, renderMarkedFactors, renderMarkedFactor,
                  ih, List.append_assoc]

private theorem markedParse_gap_simple (whole : List Nat) :
    ∀ remaining factor,
      factor ∈ (markedParse whole remaining).1 →
        ∀ letter ∈ factor.gap, Simple whole letter
  | [], factor, member => by
      simp [markedParse] at member
  | current :: rest, factor, member => by
      rw [markedParse] at member
      cases parsed : markedParse whole rest with
      | mk factors suffix =>
          rw [parsed] at member
          cases factors with
          | nil =>
              by_cases simple : Simple whole current
              · simp [simple] at member
              · simp [simple] at member
                subst factor
                simp
          | cons first tail =>
              by_cases simple : Simple whole current
              · simp only [simple, if_true, List.mem_cons] at member
                rcases member with rfl | inTail
                · intro letter letterMember
                  simp only [MarkedFactor.prependGap_gap,
                    List.mem_cons] at letterMember
                  rcases letterMember with rfl | inGap
                  · exact simple
                  · exact markedParse_gap_simple whole rest first
                      (by simpa [parsed]) letter inGap
                · exact markedParse_gap_simple whole rest factor
                    (by simpa [parsed, inTail])
              · simp only [simple, if_false, List.mem_cons] at member
                rcases member with rfl | inRest
                · simp
                · exact markedParse_gap_simple whole rest factor
                    (by simpa [parsed] using inRest)

private theorem markedParse_marker_nonSimple (whole : List Nat) :
    ∀ remaining,
      (∀ letter, letter ∈ remaining → letter ∈ whole) →
      ∀ factor,
        factor ∈ (markedParse whole remaining).1 →
          NonSimple whole factor.marker
  | [], subset, factor, member => by
      simp [markedParse] at member
  | current :: rest, subset, factor, member => by
      have restSubset :
          ∀ letter, letter ∈ rest → letter ∈ whole := by
        intro letter inRest
        exact subset letter (List.Mem.tail current inRest)
      rw [markedParse] at member
      cases parsed : markedParse whole rest with
      | mk factors suffix =>
          rw [parsed] at member
          cases factors with
          | nil =>
              by_cases simple : Simple whole current
              · simp [simple] at member
              · simp only [simple, if_false, List.mem_singleton] at member
                subst factor
                have currentMember : current ∈ whole :=
                  subset current (List.Mem.head rest)
                have positive : 0 < whole.count current :=
                  List.count_pos_iff.mpr currentMember
                unfold Simple at simple
                unfold NonSimple
                simp only
                omega
          | cons first tail =>
              by_cases simple : Simple whole current
              · simp only [simple, if_true, List.mem_cons] at member
                rcases member with rfl | inTail
                · simpa [MarkedFactor.prependGap] using
                    markedParse_marker_nonSimple whole rest restSubset
                      first (by simpa [parsed])
                · exact markedParse_marker_nonSimple whole rest restSubset
                    factor (by simpa [parsed, inTail])
              · simp only [simple, if_false, List.mem_cons] at member
                rcases member with rfl | inRest
                · have currentMember : current ∈ whole :=
                    subset current (List.Mem.head rest)
                  have positive : 0 < whole.count current :=
                    List.count_pos_iff.mpr currentMember
                  unfold Simple at simple
                  unfold NonSimple
                  simp only
                  omega
                · exact markedParse_marker_nonSimple whole rest restSubset
                    factor (by simpa [parsed] using inRest)

private theorem markedParse_suffix_simple (whole : List Nat) :
    ∀ remaining letter,
      letter ∈ (markedParse whole remaining).2 → Simple whole letter
  | [], letter, member => by
      simp [markedParse] at member
  | current :: rest, letter, member => by
      rw [markedParse] at member
      cases parsed : markedParse whole rest with
      | mk factors suffix =>
          rw [parsed] at member
          cases factors with
          | nil =>
              by_cases simple : Simple whole current
              · simp only [simple, if_true, List.mem_cons] at member
                rcases member with rfl | inSuffix
                · exact simple
                · exact markedParse_suffix_simple whole rest letter
                    (by simpa [parsed] using inSuffix)
              · simp only [simple, if_false] at member
                exact markedParse_suffix_simple whole rest letter
                  (by simpa [parsed] using member)
          | cons first tail =>
              by_cases simple : Simple whole current
              · simp only [simple, if_true] at member
                exact markedParse_suffix_simple whole rest letter
                  (by simpa [parsed] using member)
              · simp only [simple, if_false] at member
                exact markedParse_suffix_simple whole rest letter
                  (by simpa [parsed] using member)

/-- Exact structural certificate produced by the parser. -/
structure MarkedDecomposition
    (whole : List Nat) (factors : List MarkedFactor)
    (suffix : List Nat) : Prop where
  render_eq : renderMarkedFactors factors ++ suffix = whole
  gap_simple :
    ∀ factor ∈ factors, ∀ letter ∈ factor.gap,
      Simple whole letter
  marker_nonSimple :
    ∀ factor ∈ factors, NonSimple whole factor.marker
  suffix_simple :
    ∀ letter ∈ suffix, Simple whole letter

/-- Every list has its exact simple-gap / non-simple-marker decomposition. -/
theorem existsMarkedDecomposition (whole : List Nat) :
    ∃ factors suffix,
      MarkedDecomposition whole factors suffix := by
  let parsed := markedParse whole whole
  refine ⟨parsed.1, parsed.2, ?_⟩
  refine
    { render_eq := by
        simpa [parsed] using renderMarkedParse whole whole
      gap_simple := ?_
      marker_nonSimple := ?_
      suffix_simple := ?_ }
  · intro factor member letter inGap
    exact markedParse_gap_simple whole whole factor
      (by simpa [parsed] using member) letter inGap
  · intro factor member
    exact markedParse_marker_nonSimple whole whole
      (fun _ => id) factor (by simpa [parsed] using member)
  · intro letter member
    exact markedParse_suffix_simple whole whole letter
      (by simpa [parsed] using member)

theorem MarkedDecomposition.factors_nonempty_of_nonSimple
    {whole : List Nat} {factors : List MarkedFactor}
    {suffix : List Nat}
    (decomposition : MarkedDecomposition whole factors suffix)
    {multiple : Nat} (nonSimple : NonSimple whole multiple) :
    factors ≠ [] := by
  intro empty
  subst factors
  have shape : suffix = whole := by
    simpa using decomposition.render_eq
  have member : multiple ∈ whole := nonSimple.mem
  have suffixMember : multiple ∈ suffix := by
    simpa [shape] using member
  exact
    (decomposition.suffix_simple multiple suffixMember).not_nonSimple
      nonSimple

/-! ## Exact guarded occurrence-grouping steps -/

/-- The (20.6e) branch in Lemma 20.12.  The blocker marker `y`
already has two displayed occurrences in the intervening factor sequence. -/
theorem listDerivesMoveMarkerLeft20_6e
    (before after : List Nat) (x y : Nat)
    (earlyPrefix earlyGap middle lateGap selectedGap : List Nat) :
    ListDerives
      (before ++ [x] ++ earlyPrefix ++ earlyGap ++ [y] ++
        middle ++ lateGap ++ [y] ++ selectedGap ++ [x] ++ after)
      (before ++ [x] ++ selectedGap ++ [x] ++
        earlyPrefix ++ earlyGap ++ [y] ++
          middle ++ lateGap ++ [y] ++ after) := by
  simpa [List.append_assoc] using
    listDerivesGuardedMove20_6e before after x y
      (earlyPrefix ++ earlyGap) (middle ++ lateGap) selectedGap

/-- The (20.6d) branch in Lemma 20.12.  The blocker marker `y`
has its second displayed occurrence in the unprocessed suffix. -/
theorem listDerivesMoveMarkerLeft20_6d
    (before after : List Nat) (x y : Nat)
    (blockedPrefix blockedGap selectedGap
      laterPrefix laterGap : List Nat) :
    ListDerives
      (before ++ [x] ++ blockedPrefix ++ blockedGap ++ [y] ++
        selectedGap ++ [x] ++ laterPrefix ++ laterGap ++ [y] ++ after)
      (before ++ [x] ++ selectedGap ++ [x] ++
        blockedPrefix ++ blockedGap ++ [y] ++
          laterPrefix ++ laterGap ++ [y] ++ after) := by
  simpa [List.append_assoc] using
    listDerivesGuardedMove20_6d before after x y
      (blockedPrefix ++ blockedGap) selectedGap
      (laterPrefix ++ laterGap)

/-- Factor spelling of the internal (20.6e) grouping step. -/
theorem listDerivesMoveMarkedFactorLeftEarlier
    (before after : List Nat) (x y : Nat)
    (early middle : List MarkedFactor)
    (earlyY lateY selected : MarkedFactor)
    (earlyMarker : earlyY.marker = y)
    (lateMarker : lateY.marker = y)
    (selectedMarker : selected.marker = x) :
    ListDerives
      (before ++ [x] ++
        renderMarkedFactors
          (early ++ earlyY :: middle ++ [lateY]) ++
        renderMarkedFactor selected ++ after)
      (before ++ [x] ++ renderMarkedFactor selected ++
        renderMarkedFactors
          (early ++ earlyY :: middle ++ [lateY]) ++ after) := by
  simpa [renderMarkedFactors_append, renderMarkedFactors,
    renderMarkedFactor, earlyMarker, lateMarker, selectedMarker,
    List.append_assoc] using
      listDerivesMoveMarkerLeft20_6e before after x y
        (renderMarkedFactors early) earlyY.gap
        (renderMarkedFactors middle) lateY.gap selected.gap

/-- Factor spelling of the internal (20.6d) grouping step. -/
theorem listDerivesMoveMarkedFactorLeftLater
    (before after : List Nat) (x y : Nat)
    (blocked later : List MarkedFactor)
    (blockedY selected laterY : MarkedFactor)
    (blockedMarker : blockedY.marker = y)
    (selectedMarker : selected.marker = x)
    (laterMarker : laterY.marker = y) :
    ListDerives
      (before ++ [x] ++
        renderMarkedFactors (blocked ++ [blockedY]) ++
        renderMarkedFactor selected ++
        renderMarkedFactors (later ++ laterY :: []) ++ after)
      (before ++ [x] ++ renderMarkedFactor selected ++
        renderMarkedFactors (blocked ++ [blockedY]) ++
        renderMarkedFactors (later ++ laterY :: []) ++ after) := by
  simpa [renderMarkedFactors_append, renderMarkedFactors,
    renderMarkedFactor, blockedMarker, selectedMarker, laterMarker,
    List.append_assoc] using
      listDerivesMoveMarkerLeft20_6d before after x y
        (renderMarkedFactors blocked) blockedY.gap selected.gap
        (renderMarkedFactors later) laterY.gap

/-! ### Multiplicity bookkeeping for the grouping recursion -/

theorem MarkedDecomposition.marker_not_mem_gap
    {whole : List Nat} {factors : List MarkedFactor}
    {suffix : List Nat}
    (decomposition : MarkedDecomposition whole factors suffix)
    {factor : MarkedFactor} (member : factor ∈ factors)
    {multiple : Nat} (nonSimple : NonSimple whole multiple) :
    multiple ∉ factor.gap := by
  intro inGap
  exact
    (decomposition.gap_simple factor member multiple inGap).not_nonSimple
      nonSimple

theorem MarkedDecomposition.marker_not_mem_suffix
    {whole : List Nat} {factors : List MarkedFactor}
    {suffix : List Nat}
    (decomposition : MarkedDecomposition whole factors suffix)
    {multiple : Nat} (nonSimple : NonSimple whole multiple) :
    multiple ∉ suffix := by
  intro inSuffix
  exact
    (decomposition.suffix_simple multiple inSuffix).not_nonSimple
      nonSimple

private theorem count_renderMarkedFactors_of_gap_absent
    (multiple : Nat) :
    ∀ factors : List MarkedFactor,
      (∀ factor ∈ factors, multiple ∉ factor.gap) →
      (renderMarkedFactors factors).count multiple =
        (markedMarkers factors).count multiple
  | [], _ => by simp [renderMarkedFactors, markedMarkers]
  | factor :: rest, absent => by
      have headAbsent : multiple ∉ factor.gap :=
        absent factor (by simp)
      have tailAbsent :
          ∀ candidate ∈ rest, multiple ∉ candidate.gap := by
        intro candidate member
        exact absent candidate (by simp [member])
      have ih :=
        count_renderMarkedFactors_of_gap_absent
          multiple rest tailAbsent
      dsimp only [markedMarkers] at ih
      simp [renderMarkedFactors, renderMarkedFactor, markedMarkers,
        List.count_append, List.count_cons, List.count_eq_zero.mpr headAbsent, ih]

/-- Every occurrence of a globally non-simple letter is represented by a
marker occurrence in the parsed factor sequence. -/
theorem MarkedDecomposition.count_marker
    {whole : List Nat} {factors : List MarkedFactor}
    {suffix : List Nat}
    (decomposition : MarkedDecomposition whole factors suffix)
    (multiple : Nat) (nonSimple : NonSimple whole multiple) :
    (markedMarkers factors).count multiple = whole.count multiple := by
  have gapsAbsent :
      ∀ factor ∈ factors, multiple ∉ factor.gap := by
    intro factor member
    exact decomposition.marker_not_mem_gap member nonSimple
  have suffixAbsent : multiple ∉ suffix :=
    decomposition.marker_not_mem_suffix nonSimple
  have renderedCount :=
    count_renderMarkedFactors_of_gap_absent
      multiple factors gapsAbsent
  have wholeCount :
      (renderMarkedFactors factors ++ suffix).count multiple = whole.count multiple :=
    congrArg (fun letters => letters.count multiple) decomposition.render_eq
  rw [List.count_append, renderedCount,
    List.count_eq_zero.mpr suffixAbsent] at wholeCount
  simpa using wholeCount

/-- Every marker in a complete parsed factor list has at least two marker
occurrences.  This is the debt invariant used by each d/e choice. -/
def MarkersRepeated (factors : List MarkedFactor) : Prop :=
  ∀ factor ∈ factors,
    2 ≤ (markedMarkers factors).count factor.marker

theorem MarkedDecomposition.markersRepeated
    {whole : List Nat} {factors : List MarkedFactor}
    {suffix : List Nat}
    (decomposition : MarkedDecomposition whole factors suffix) :
    MarkersRepeated factors := by
  intro factor member
  have nonSimple := decomposition.marker_nonSimple factor member
  rw [decomposition.count_marker factor.marker nonSimple]
  exact nonSimple

private theorem markedMarkers_perm
    {left right : List MarkedFactor}
    (permutation : left.Perm right) :
    (markedMarkers left).Perm (markedMarkers right) := by
  simpa [markedMarkers] using
    permutation.map MarkedFactor.marker

theorem MarkersRepeated.of_perm
    {left right : List MarkedFactor}
    (repeated : MarkersRepeated left)
    (permutation : left.Perm right) :
    MarkersRepeated right := by
  intro factor inRight
  have inLeft : factor ∈ left :=
    permutation.mem_iff.mpr inRight
  have bound := repeated factor inLeft
  have markerPermutation := markedMarkers_perm permutation
  rw [markerPermutation.count_eq factor.marker] at bound
  exact bound

private theorem exists_markedFactor_split
    (marker : Nat) :
    ∀ {factors : List MarkedFactor},
      marker ∈ markedMarkers factors →
      ∃ before factor after,
        factors = before ++ factor :: after ∧
          factor.marker = marker
  | [], member => by
      simp [markedMarkers] at member
  | first :: rest, member => by
      simp only [markedMarkers, List.map_cons, List.mem_cons] at member
      rcases member with equal | inRest
      · exact ⟨[], first, rest, rfl, equal.symm⟩
      · obtain ⟨before, factor, after, shape, markerEq⟩ :=
          exists_markedFactor_split marker inRest
        exact ⟨first :: before, factor, after, by simp [shape], markerEq⟩

/-- Split at the first factor carrying `marker`; the strict front contains
no such marker. -/
private theorem exists_first_markedFactor_split
    (marker : Nat) :
    ∀ {factors : List MarkedFactor},
      marker ∈ markedMarkers factors →
      ∃ before factor after,
        factors = before ++ factor :: after ∧
          factor.marker = marker ∧
          (∀ candidate ∈ before, candidate.marker ≠ marker)
  | [], member => by
      simp [markedMarkers] at member
  | first :: rest, member => by
      by_cases equal : first.marker = marker
      · exact ⟨[], first, rest, rfl, equal, by simp⟩
      · have inRest : marker ∈ markedMarkers rest := by
          simpa [markedMarkers, equal, Ne.symm equal] using member
        obtain ⟨before, factor, after, shape, factorMarker,
            prefixFree⟩ :=
          exists_first_markedFactor_split marker inRest
        refine ⟨first :: before, factor, after, by simp [shape],
          factorMarker, ?_⟩
        intro candidate candidateMember
        simp only [List.mem_cons] at candidateMember
        rcases candidateMember with rfl | inBefore
        · exact equal
        · exact prefixFree candidate inBefore

private theorem perm_move_markedFactor_to_front
    (selected : MarkedFactor) :
    ∀ (before after : List MarkedFactor),
      (before ++ selected :: after).Perm
        (selected :: before ++ after)
  | [], after => List.Perm.refl _
  | first :: rest, after => by
      have lifted := List.Perm.cons first
        (perm_move_markedFactor_to_front selected rest after)
      exact lifted.trans
        (List.Perm.swap selected first (rest ++ after))

private theorem marker_count_eq_zero
    {factors : List MarkedFactor} {marker : Nat}
    (absent : ∀ factor ∈ factors, factor.marker ≠ marker) :
    (markedMarkers factors).count marker = 0 := by
  apply List.count_eq_zero.mpr
  intro member
  obtain ⟨before, factor, after, shape, factorMarker⟩ :=
    exists_markedFactor_split marker member
  have factorMember : factor ∈ factors := by
    rw [shape]
    simp
  exact (absent factor factorMember) factorMarker

/-- A strict grouping move removes one selected `x` from the pending debt. -/
def groupingDebt (marker : Nat) (pending : List MarkedFactor) : Nat :=
  (pending.filter fun factor => decide (factor.marker = marker)).length

private theorem groupingDebt_selected_decreases
    (marker : Nat) (before after : List MarkedFactor)
    (selected : MarkedFactor)
    (selectedMarker : selected.marker = marker)
    (beforeFree : ∀ factor ∈ before, factor.marker ≠ marker) :
    groupingDebt marker (before ++ after) <
      groupingDebt marker (before ++ selected :: after) := by
  have filteredBefore :
      before.filter (fun factor => decide (factor.marker = marker)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro factor member
    simp only [decide_eq_true_eq]
    exact beforeFree factor member
  simp [groupingDebt, List.filter_append, filteredBefore,
    selectedMarker]

/-! ### Gathering every occurrence of one marker -/

/-- Gather all pending occurrences of `marker` behind an already displayed
guard occurrence.  The recursion consumes one selected occurrence at a
time.  Its strict structural measure is the pending length; `groupingDebt`
records the sharper occurrence debt discharged by the same step.

The `MarkersRepeated` premise forces the final marker of a nonempty blocker
to occur either earlier in that blocker (20.6e) or later in the pending tail
(20.6d). -/
theorem existsGatherMarkerAfterGuard
    (outer suffix : List Nat) (marker : Nat)
    (done : List MarkedFactor) (guard : MarkedFactor)
    (pending : List MarkedFactor)
    (doneMarkers :
      ∀ factor ∈ done, factor.marker = marker)
    (guardMarker : guard.marker = marker)
    (repeated : MarkersRepeated (done ++ guard :: pending)) :
    ∃ gathered remainder,
      (∀ factor ∈ gathered, factor.marker = marker) ∧
      (∀ factor ∈ remainder, factor.marker ≠ marker) ∧
      (done ++ guard :: pending).Perm (gathered ++ remainder) ∧
      ListDerives
        (outer ++ renderMarkedFactors (done ++ guard :: pending) ++ suffix)
        (outer ++ renderMarkedFactors (gathered ++ remainder) ++ suffix) := by
  classical
  by_cases present : marker ∈ markedMarkers pending
  · obtain ⟨blocked, selected, later, pendingShape, selectedMarker,
        blockedFree⟩ :=
      exists_first_markedFactor_split marker present
    by_cases blockedEmpty : blocked = []
    · subst blocked
      have nextRepeated :
          MarkersRepeated ((done ++ [guard]) ++ selected :: later) := by
        simpa [pendingShape, List.append_assoc] using repeated
      obtain ⟨gathered, remainder, gatheredMarkers, remainderFree,
          finalPermutation, recursive⟩ :=
        existsGatherMarkerAfterGuard outer suffix marker
          (done ++ [guard]) selected later
          (by
            intro factor member
            simp only [List.mem_append, List.mem_singleton] at member
            rcases member with inDone | rfl
            · exact doneMarkers factor inDone
            · exact guardMarker)
          selectedMarker nextRepeated
      refine ⟨gathered, remainder, gatheredMarkers, remainderFree,
        ?_, ?_⟩
      · simpa [pendingShape, List.append_assoc] using finalPermutation
      · simpa [pendingShape, List.append_assoc] using recursive
    · let blockedLast := blocked.getLast blockedEmpty
      let blockedInit := blocked.dropLast
      have blockedShape : blockedInit ++ [blockedLast] = blocked := by
        exact List.dropLast_concat_getLast blockedEmpty
      have lastInBlocked : blockedLast ∈ blocked := by
        rw [← blockedShape]
        simp
      have lastDifferent : blockedLast.marker ≠ marker :=
        blockedFree blockedLast lastInBlocked
      have currentRepeated :
          2 ≤
            (markedMarkers (done ++ guard :: blocked ++
              selected :: later)).count blockedLast.marker := by
        have currentMember :
            blockedLast ∈ done ++ guard :: blocked ++ selected :: later := by
          simp [lastInBlocked]
        have shapedRepeated :
            MarkersRepeated
              (done ++ guard :: blocked ++ selected :: later) := by
          simpa [pendingShape, List.append_assoc] using repeated
        exact shapedRepeated blockedLast currentMember
      have doneZero :
          (markedMarkers done).count blockedLast.marker = 0 := by
        apply marker_count_eq_zero
        intro factor member equality
        have factorMarker := doneMarkers factor member
        exact lastDifferent (equality.symm.trans factorMarker)
      have guardDifferent : guard.marker ≠ blockedLast.marker := by
        intro equality
        exact lastDifferent (equality.symm.trans guardMarker)
      have selectedDifferent : selected.marker ≠ blockedLast.marker := by
        intro equality
        exact lastDifferent (equality.symm.trans selectedMarker)
      have countBound :
          2 ≤
            (markedMarkers blockedInit).count blockedLast.marker + 1 +
              (markedMarkers later).count blockedLast.marker := by
        dsimp only [markedMarkers] at doneZero
        simpa [← blockedShape, markedMarkers, List.map_append,
          List.count_append, doneZero, guardDifferent,
          selectedDifferent, List.append_assoc, Nat.add_assoc,
          Nat.add_comm, Nat.add_left_comm] using currentRepeated
      have alternative :
          blockedLast.marker ∈ markedMarkers blockedInit ∨
            blockedLast.marker ∈ markedMarkers later := by
        by_cases earlier :
            blockedLast.marker ∈ markedMarkers blockedInit
        · exact Or.inl earlier
        · right
          apply List.count_pos_iff.mp
          have earlierZero :
              (markedMarkers blockedInit).count blockedLast.marker = 0 :=
            List.count_eq_zero.mpr earlier
          rw [earlierZero] at countBound
          omega
      have moved :
          ListDerives
            (outer ++ renderMarkedFactors
              (done ++ guard :: blocked ++ selected :: later) ++ suffix)
            (outer ++ renderMarkedFactors
              ((done ++ [guard]) ++ selected :: blocked ++ later) ++
                suffix) := by
        rcases alternative with earlier | afterwards
        · obtain ⟨early, earlyY, middle, initShape, earlyMarker⟩ :=
            exists_markedFactor_split blockedLast.marker earlier
          have blockedExpanded :
              blocked = early ++ earlyY :: middle ++ [blockedLast] := by
            rw [← blockedShape, initShape]
          have step := listDerivesMoveMarkedFactorLeftEarlier
            (outer ++ renderMarkedFactors done ++ guard.gap)
            (renderMarkedFactors later ++ suffix)
            marker blockedLast.marker early middle earlyY blockedLast selected
            earlyMarker rfl selectedMarker
          simpa [blockedExpanded, renderMarkedFactors_append,
            renderMarkedFactors, renderMarkedFactor, guardMarker,
            selectedMarker, List.append_assoc] using step
        · obtain ⟨early, laterY, late, laterShape, laterMarker⟩ :=
            exists_markedFactor_split blockedLast.marker afterwards
          have step := listDerivesMoveMarkedFactorLeftLater
            (outer ++ renderMarkedFactors done ++ guard.gap)
            (renderMarkedFactors late ++ suffix)
            marker blockedLast.marker blockedInit early blockedLast
            selected laterY rfl selectedMarker laterMarker
          simpa [← blockedShape, laterShape, renderMarkedFactors_append,
            renderMarkedFactors, renderMarkedFactor, guardMarker,
            selectedMarker, List.append_assoc] using step
      have movePermutation :
          (done ++ guard :: blocked ++ selected :: later).Perm
            ((done ++ [guard]) ++ selected :: blocked ++ later) := by
        have tailMove :=
          perm_move_markedFactor_to_front selected blocked later
        have prefixed := tailMove.append_left (done ++ [guard])
        simpa [List.append_assoc] using prefixed
      have currentRepeated :
          MarkersRepeated
            (done ++ guard :: blocked ++ selected :: later) := by
        simpa [pendingShape, List.append_assoc] using repeated
      have nextRepeated :
          MarkersRepeated
            ((done ++ [guard]) ++ selected :: blocked ++ later) :=
        currentRepeated.of_perm movePermutation
      obtain ⟨gathered, remainder, gatheredMarkers, remainderFree,
          recursivePermutation, recursive⟩ :=
        existsGatherMarkerAfterGuard outer suffix marker
          (done ++ [guard]) selected (blocked ++ later)
          (by
            intro factor member
            simp only [List.mem_append, List.mem_singleton] at member
            rcases member with inDone | rfl
            · exact doneMarkers factor inDone
            · exact guardMarker)
          selectedMarker (by
            simpa [List.append_assoc] using nextRepeated)
      refine ⟨gathered, remainder, gatheredMarkers, remainderFree,
        ?_, ?_⟩
      · have combined := movePermutation.trans <| by
          simpa [List.append_assoc] using recursivePermutation
        simpa [pendingShape, List.append_assoc] using combined
      · have combined := moved.trans <| by
          simpa [List.append_assoc] using recursive
        simpa [pendingShape, List.append_assoc] using combined
  · refine ⟨done ++ [guard], pending, ?_, ?_, ?_, ?_⟩
    · intro factor member
      simp only [List.mem_append, List.mem_singleton] at member
      rcases member with inDone | rfl
      · exact doneMarkers factor inDone
      · exact guardMarker
    · intro factor member equality
      apply present
      exact List.mem_map.mpr ⟨factor, member, equality⟩
    · simpa [List.append_assoc] using
        (List.Perm.refl (done ++ guard :: pending))
    · simpa [List.append_assoc] using
        (S5_107.ListDerives.refl (basis := basis)
          (outer ++ renderMarkedFactors (done ++ guard :: pending) ++
            suffix))
termination_by pending.length
decreasing_by
  · simp [pendingShape]
  · simp [pendingShape]

/-! ## Grouping all non-simple markers (Lemma 20.12, first stage) -/

/-- One gathered marker block before rigidification. -/
structure MarkedGroup where
  marker : Nat
  factors : List MarkedFactor
deriving DecidableEq, Repr

/-- Flatten the gathered factor groups. -/
def flattenMarkedGroups : List MarkedGroup → List MarkedFactor
  | [] => []
  | group :: rest =>
      group.factors ++ flattenMarkedGroups rest

@[simp] theorem flattenMarkedGroups_nil :
    flattenMarkedGroups [] = [] :=
  rfl

@[simp] theorem flattenMarkedGroups_cons
    (group : MarkedGroup) (rest : List MarkedGroup) :
    flattenMarkedGroups (group :: rest) =
      group.factors ++ flattenMarkedGroups rest :=
  rfl

/-- Marker sequence of the gathered groups. -/
def markedGroupMarkers (groups : List MarkedGroup) : List Nat :=
  groups.map MarkedGroup.marker

/-- Exact structural invariants of the completed grouping stage. -/
structure MarkedGroups.Valid (groups : List MarkedGroup) : Prop where
  factors_nonempty :
    ∀ group ∈ groups, group.factors ≠ []
  factors_marker :
    ∀ group ∈ groups, ∀ factor ∈ group.factors,
      factor.marker = group.marker
  markers_nodup : (markedGroupMarkers groups).Nodup

private theorem MarkersRepeated.of_group_remainder
    {group remainder : List MarkedFactor} {marker : Nat}
    (repeated : MarkersRepeated (group ++ remainder))
    (groupMarkers :
      ∀ factor ∈ group, factor.marker = marker)
    (remainderFree :
      ∀ factor ∈ remainder, factor.marker ≠ marker) :
    MarkersRepeated remainder := by
  intro factor member
  have bound := repeated factor (by simp [member])
  have groupAbsent :
      ∀ candidate ∈ group, candidate.marker ≠ factor.marker := by
    intro candidate candidateMember equality
    have candidateMarker := groupMarkers candidate candidateMember
    have factorDifferent := remainderFree factor member
    exact factorDifferent (equality.symm.trans candidateMarker)
  have groupZero :
      (markedMarkers group).count factor.marker = 0 :=
    marker_count_eq_zero groupAbsent
  dsimp only [markedMarkers] at groupZero
  simpa [markedMarkers, List.map_append, List.count_append,
    groupZero] using bound

private theorem marker_mem_markedGroupMarkers_iff
    (marker : Nat) (groups : List MarkedGroup) :
    marker ∈ markedGroupMarkers groups ↔
      ∃ group ∈ groups, group.marker = marker := by
  simp [markedGroupMarkers]

private theorem factor_mem_flattenMarkedGroups
    {group : MarkedGroup} {groups : List MarkedGroup}
    (groupMember : group ∈ groups)
    {factor : MarkedFactor} (factorMember : factor ∈ group.factors) :
    factor ∈ flattenMarkedGroups groups := by
  induction groups with
  | nil => simp at groupMember
  | cons first rest ih =>
      simp only [List.mem_cons] at groupMember
      rcases groupMember with rfl | inRest
      · simp [factorMember]
      · simp only [flattenMarkedGroups_cons, List.mem_append]
        exact Or.inr (ih inRest)

private theorem gathered_nonempty
    {first : MarkedFactor} {rest gathered remainder : List MarkedFactor}
    {marker : Nat}
    (firstMarker : first.marker = marker)
    (remainderFree :
      ∀ factor ∈ remainder, factor.marker ≠ marker)
    (permutation :
      (first :: rest).Perm (gathered ++ remainder)) :
    gathered ≠ [] := by
  intro empty
  subst gathered
  have firstInTarget : first ∈ remainder := by
    have firstInSource : first ∈ first :: rest := by simp
    simpa using permutation.mem_iff.mp firstInSource
  exact (remainderFree first firstInTarget) firstMarker

/-- Recursively gather every marker class.  The recursive call is on the
strictly shorter remainder left after the nonempty first group. -/
theorem existsGroupedFactorReduction
    (outer suffix : List Nat) :
    ∀ factors : List MarkedFactor,
      factors ≠ [] →
      MarkersRepeated factors →
      ∃ groups : List MarkedGroup,
        MarkedGroups.Valid groups ∧
        factors.Perm (flattenMarkedGroups groups) ∧
        ListDerives
          (outer ++ renderMarkedFactors factors ++ suffix)
          (outer ++ renderMarkedFactors
            (flattenMarkedGroups groups) ++ suffix)
  | [], nonempty, _ => False.elim (nonempty rfl)
  | first :: rest, _, repeated => by
      let marker := first.marker
      obtain ⟨gathered, remainder, groupMarkers, remainderFree,
          gatherPermutation, gatheredDerivation⟩ :=
        existsGatherMarkerAfterGuard outer suffix marker [] first rest
          (by simp) rfl (by simpa using repeated)
      have groupNonempty : gathered ≠ [] :=
        gathered_nonempty rfl remainderFree
          (by simpa using gatherPermutation)
      let firstGroup : MarkedGroup :=
        { marker := marker
          factors := gathered }
      cases remainder with
      | nil =>
          refine ⟨[firstGroup], ?_, ?_, ?_⟩
          · refine
              { factors_nonempty := ?_
                factors_marker := ?_
                markers_nodup := by simp [markedGroupMarkers] }
            · intro group member
              have groupEq : group = firstGroup := by simpa using member
              subst group
              simpa [firstGroup] using groupNonempty
            · intro group member factor factorMember
              have groupEq : group = firstGroup := by
                simpa using member
              subst group
              exact groupMarkers factor factorMember
          · simpa [firstGroup] using gatherPermutation
          · simpa [firstGroup] using gatheredDerivation
      | cons next remainderTail =>
          let remainder := next :: remainderTail
          have remainderRepeated : MarkersRepeated remainder := by
            apply MarkersRepeated.of_group_remainder
              (group := gathered) (marker := marker)
            · simpa [remainder] using
                repeated.of_perm gatherPermutation
            · exact groupMarkers
            · simpa [remainder] using remainderFree
          obtain ⟨laterGroups, laterValid, laterPermutation,
              laterDerivation⟩ :=
            existsGroupedFactorReduction
              (outer ++ renderMarkedFactors gathered) suffix remainder
              (by simp [remainder]) remainderRepeated
          have markerAbsent :
              marker ∉ markedGroupMarkers laterGroups := by
            intro member
            obtain ⟨group, groupMember, groupMarker⟩ :=
              (marker_mem_markedGroupMarkers_iff marker laterGroups).1
                member
            obtain ⟨factor, factorMember⟩ :=
              List.exists_mem_of_ne_nil group.factors
                (laterValid.factors_nonempty group groupMember)
            have factorInFlatten :
                factor ∈ flattenMarkedGroups laterGroups :=
              factor_mem_flattenMarkedGroups groupMember factorMember
            have factorInRemainder : factor ∈ remainder :=
              laterPermutation.mem_iff.mpr factorInFlatten
            have factorMarker :=
              laterValid.factors_marker group groupMember
                factor factorMember
            exact
              (remainderFree factor (by simpa [remainder] using factorInRemainder))
                (factorMarker.trans groupMarker)
          refine ⟨firstGroup :: laterGroups, ?_, ?_, ?_⟩
          · refine
              { factors_nonempty := ?_
                factors_marker := ?_
                markers_nodup := ?_ }
            · intro group member
              simp only [List.mem_cons] at member
              rcases member with rfl | inLater
              · exact groupNonempty
              · exact laterValid.factors_nonempty group inLater
            · intro group member factor factorMember
              simp only [List.mem_cons] at member
              rcases member with rfl | inLater
              · exact groupMarkers factor factorMember
              · exact laterValid.factors_marker group inLater
                  factor factorMember
            · simpa [markedGroupMarkers, firstGroup, marker] using
                List.nodup_cons.mpr
                  ⟨markerAbsent, laterValid.markers_nodup⟩
          · have combined := gatherPermutation.trans <|
              laterPermutation.append_left gathered
            simpa [firstGroup, flattenMarkedGroups,
              List.append_assoc, remainder] using combined
          · have combined := gatheredDerivation.trans <| by
              simpa [renderMarkedFactors_append, firstGroup,
                flattenMarkedGroups, List.append_assoc, remainder] using
                  laterDerivation
            simpa [firstGroup, flattenMarkedGroups,
              renderMarkedFactors_append, List.append_assoc, remainder]
              using combined
termination_by factors => factors.length
decreasing_by
  have lengths := gatherPermutation.length_eq
  have positive : 0 < gathered.length :=
    List.length_pos_iff.mpr groupNonempty
  simp [remainder] at lengths ⊢
  omega

/-- Public grouping stage for a parsed non-simple list. -/
theorem existsGroupedReduction
    {whole : List Nat} {factors : List MarkedFactor}
    {suffix : List Nat}
    (decomposition : MarkedDecomposition whole factors suffix)
    {multiple : Nat} (nonSimple : NonSimple whole multiple) :
    ∃ groups : List MarkedGroup,
      MarkedGroups.Valid groups ∧
      factors.Perm (flattenMarkedGroups groups) ∧
      ListDerives whole
        (renderMarkedFactors (flattenMarkedGroups groups) ++ suffix) := by
  have factorsNonempty :=
    decomposition.factors_nonempty_of_nonSimple nonSimple
  obtain ⟨groups, valid, permutation, derivation⟩ :=
    existsGroupedFactorReduction [] suffix factors factorsNonempty
      decomposition.markersRepeated
  refine ⟨groups, valid, permutation, ?_⟩
  simpa [decomposition.render_eq] using derivation

/-! ## Simple-bank preservation through grouping -/

/-- Executable projection onto the globally simple letters. -/
def simpleProjection (whole : List Nat) : List Nat :=
  whole.filter fun letter => decide (Simple whole letter)

theorem simpleProjection_nodup (whole : List Nat) :
    (simpleProjection whole).Nodup := by
  rw [List.nodup_iff_count]
  intro letter
  by_cases simple : Simple whole letter
  · have kept : decide (Simple whole letter) = true := by
      simp [simple]
    rw [simpleProjection, List.count_filter (p :=
      fun tested => decide (Simple whole tested)) kept]
    unfold Simple at simple
    omega
  · have absent : letter ∉ simpleProjection whole := by
      intro member
      have tested := (List.mem_filter.mp member).2
      exact simple (of_decide_eq_true tested)
    rw [List.count_eq_zero.mpr absent]
    omega

private theorem filter_renderMarkedFactors_simple
    (whole : List Nat) :
    ∀ factors : List MarkedFactor,
      (∀ factor ∈ factors, ∀ letter ∈ factor.gap,
        Simple whole letter) →
      (∀ factor ∈ factors, NonSimple whole factor.marker) →
      (renderMarkedFactors factors).filter
          (fun letter => decide (Simple whole letter)) =
        (factors.map MarkedFactor.gap).flatten
  | [], _, _ => rfl
  | factor :: rest, gapsSimple, markersNonSimple => by
      have gapKept :
          factor.gap.filter
              (fun letter => decide (Simple whole letter)) =
            factor.gap := by
        apply List.filter_eq_self.mpr
        intro letter member
        exact decide_eq_true <|
          gapsSimple factor (by simp) letter member
      have markerRejected :
          decide (Simple whole factor.marker) = false := by
        apply decide_eq_false
        exact (markersNonSimple factor (by simp)).not_simple
      have restGapsSimple :
          ∀ candidate ∈ rest, ∀ letter ∈ candidate.gap,
            Simple whole letter := by
        intro candidate member letter inGap
        exact gapsSimple candidate (by simp [member]) letter inGap
      have restMarkersNonSimple :
          ∀ candidate ∈ rest, NonSimple whole candidate.marker := by
        intro candidate member
        exact markersNonSimple candidate (by simp [member])
      have ih := filter_renderMarkedFactors_simple whole rest
        restGapsSimple restMarkersNonSimple
      simp [renderMarkedFactors, renderMarkedFactor,
        List.filter_append, gapKept, markerRejected, ih]

/-- The parser's simple bank is exactly the global simple projection. -/
theorem MarkedDecomposition.simpleBank_eq
    {whole : List Nat} {factors : List MarkedFactor}
    {suffix : List Nat}
    (decomposition : MarkedDecomposition whole factors suffix) :
    markedSimpleBank factors suffix = simpleProjection whole := by
  have rendered := filter_renderMarkedFactors_simple whole factors
    decomposition.gap_simple decomposition.marker_nonSimple
  have suffixKept :
      suffix.filter (fun letter => decide (Simple whole letter)) =
        suffix := by
    apply List.filter_eq_self.mpr
    intro letter member
    exact decide_eq_true (decomposition.suffix_simple letter member)
  have filteredShape :
      (renderMarkedFactors factors ++ suffix).filter
        (fun letter => decide (Simple whole letter)) =
      whole.filter (fun letter => decide (Simple whole letter)) :=
    congrArg
      (fun letters =>
        letters.filter (fun letter => decide (Simple whole letter)))
      decomposition.render_eq
  rw [List.filter_append, rendered, suffixKept] at filteredShape
  exact filteredShape

theorem MarkedDecomposition.simpleBank_nodup
    {whole : List Nat} {factors : List MarkedFactor}
    {suffix : List Nat}
    (decomposition : MarkedDecomposition whole factors suffix) :
    (markedSimpleBank factors suffix).Nodup := by
  rw [decomposition.simpleBank_eq]
  exact simpleProjection_nodup whole

private theorem gapsFlatten_perm
    {left right : List MarkedFactor}
    (permutation : left.Perm right) :
    (left.map MarkedFactor.gap).flatten.Perm
      (right.map MarkedFactor.gap).flatten := by
  induction permutation with
  | nil => exact List.Perm.refl []
  | cons factor _ ih =>
      simpa using ih.append_left factor.gap
  | swap left right rest =>
      have swapped :
          (right.gap ++ left.gap).Perm
            (left.gap ++ right.gap) :=
        List.perm_append_comm
      simpa [List.append_assoc] using
        swapped.append_right
          ((rest.map MarkedFactor.gap).flatten)
  | trans _ _ first second =>
      exact first.trans second

theorem markedSimpleBank_nodup_of_perm
    {whole : List Nat} {source target : List MarkedFactor}
    {suffix : List Nat}
    (decomposition : MarkedDecomposition whole source suffix)
    (permutation : source.Perm target) :
    (markedSimpleBank target suffix).Nodup := by
  have gapsPermutation := gapsFlatten_perm permutation
  have bankPermutation :
      (markedSimpleBank source suffix).Perm
        (markedSimpleBank target suffix) := by
    exact gapsPermutation.append_right suffix
  exact bankPermutation.nodup_iff.mp decomposition.simpleBank_nodup

private theorem flattenMarkedGroups_split
    {group : MarkedGroup} {groups : List MarkedGroup}
    (member : group ∈ groups) :
    ∃ before after,
      flattenMarkedGroups groups =
        before ++ group.factors ++ after := by
  induction groups with
  | nil => simp at member
  | cons first rest ih =>
      simp only [List.mem_cons] at member
      rcases member with rfl | inRest
      · exact ⟨[], flattenMarkedGroups rest, by simp⟩
      · obtain ⟨before, after, shape⟩ := ih inRest
        exact ⟨first.factors ++ before, after, by
          simp [shape, List.append_assoc]⟩

/-- Every gathered group's complete simple payload is duplicate-free. -/
theorem MarkedGroups.Valid.group_gaps_nodup
    {groups : List MarkedGroup}
    (valid : MarkedGroups.Valid groups)
    {group : MarkedGroup} (member : group ∈ groups)
    {suffix : List Nat}
    (bankNodup :
      (markedSimpleBank (flattenMarkedGroups groups) suffix).Nodup) :
    (group.factors.map MarkedFactor.gap).flatten.Nodup := by
  obtain ⟨before, after, shape⟩ :=
    flattenMarkedGroups_split member
  rw [shape] at bankNodup
  simp only [markedSimpleBank, List.map_append,
    List.flatten_append, List.append_assoc] at bankNodup
  have leftDropped :=
    (List.nodup_append.mp bankNodup).2.1
  exact (List.nodup_append.mp leftDropped).1

/-! ## Segment sorting and rank-sensitive marker caps (Lemma 20.10) -/

/-- Discard the empty segments before sorting by displayed head. -/
def occupiedSegments (segments : List (List Nat)) : List (List Nat) :=
  segments.filter fun segment => decide (segment ≠ [])

/-- Weak head order used by merge sort; distinct simple heads make it strict
on the final segment bank. -/
def segmentHeadLe (left right : List Nat) : Bool :=
  decide (left.headD 0 ≤ right.headD 0)

/-- Canonical sorted list of nonempty segments. -/
def sortedOccupiedSegments
    (segments : List (List Nat)) : List (List Nat) :=
  (occupiedSegments segments).mergeSort segmentHeadLe

/-- Number of empty terminated factors that become terminal marker copies. -/
def emptySegmentCount (segments : List (List Nat)) : Nat :=
  segments.count []

/-- Move all empty factors to the end and sort the occupied factors. -/
def compactSegments (segments : List (List Nat)) : List (List Nat) :=
  sortedOccupiedSegments segments ++
    List.replicate (emptySegmentCount segments) []

private theorem segments_perm_occupied_append_empty
    (segments : List (List Nat)) :
    segments.Perm
      (occupiedSegments segments ++
        List.replicate (emptySegmentCount segments) []) := by
  apply List.perm_iff_count.mpr
  intro tested
  by_cases empty : tested = []
  · subst tested
    have filteredEmpty : (occupiedSegments segments).count [] = 0 := by
      apply List.count_eq_zero.mpr
      intro member
      exact (of_decide_eq_true (List.mem_filter.mp member).2) rfl
    rw [List.count_append, filteredEmpty]
    simp [emptySegmentCount]
  · have kept : decide (tested ≠ []) = true := by
      simp [empty]
    have filteredCount :
        (segments.filter
          (fun segment => decide (segment ≠ []))).count tested =
          segments.count tested :=
      List.count_filter
        (p := fun segment => decide (segment ≠ [])) kept
    have emptyCopies :
        (List.replicate (emptySegmentCount segments) []).count tested = 0 := by
      apply List.count_eq_zero.mpr
      intro member
      exact empty (List.mem_replicate.mp member).2
    rw [List.count_append]
    change segments.count tested =
      (occupiedSegments segments).count tested +
        (List.replicate (emptySegmentCount segments) []).count tested
    rw [show (occupiedSegments segments).count tested = segments.count tested from
      filteredCount, emptyCopies, Nat.add_zero]

theorem segments_perm_compact (segments : List (List Nat)) :
    segments.Perm (compactSegments segments) := by
  have partition := segments_perm_occupied_append_empty segments
  have sorted :
      (occupiedSegments segments).Perm
        (sortedOccupiedSegments segments) :=
    (List.mergeSort_perm _ _).symm
  exact partition.trans <| by
    simpa [compactSegments] using
      sorted.append_right
        (List.replicate (emptySegmentCount segments) [])

theorem sortedOccupiedSegments_nonempty
    {segments : List (List Nat)} {segment : List Nat}
    (member : segment ∈ sortedOccupiedSegments segments) :
    segment ≠ [] := by
  have inOccupied : segment ∈ occupiedSegments segments := by
    simpa [sortedOccupiedSegments] using member
  exact of_decide_eq_true (List.mem_filter.mp inOccupied).2

private theorem segmentHeadLe_transitive :
    ∀ left middle right : List Nat,
      segmentHeadLe left middle = true →
      segmentHeadLe middle right = true →
      segmentHeadLe left right = true := by
  intro left middle right first second
  simp only [segmentHeadLe, decide_eq_true_eq] at first second ⊢
  exact Nat.le_trans first second

private theorem segmentHeadLe_total :
    ∀ left right : List Nat,
      (segmentHeadLe left right || segmentHeadLe right left) = true := by
  intro left right
  simp only [segmentHeadLe, Bool.or_eq_true, decide_eq_true_eq]
  exact Nat.le_total (left.headD 0) (right.headD 0)

theorem sortedOccupiedSegments_pairwise_le
    (segments : List (List Nat)) :
    (sortedOccupiedSegments segments).Pairwise
      (fun left right => left.headD 0 ≤ right.headD 0) := by
  have sorted := List.pairwise_mergeSort
    segmentHeadLe_transitive segmentHeadLe_total
      (occupiedSegments segments)
  simpa [sortedOccupiedSegments, segmentHeadLe] using
    (sorted.imp fun relation => of_decide_eq_true relation)

private theorem heads_nodup_of_flatten_nodup :
    ∀ {segments : List (List Nat)},
      segments.flatten.Nodup →
      (∀ segment ∈ segments, segment ≠ []) →
      (segments.map fun segment => segment.headD 0).Nodup
  | [], _, _ => by simp
  | segment :: rest, flattened, nonempty => by
      have segmentNonempty := nonempty segment (by simp)
      have appendNodup :
          (segment ++ rest.flatten).Nodup := by
        simpa using flattened
      have segmentNodup := (List.nodup_append.mp appendNodup).1
      have restNodup := (List.nodup_append.mp appendNodup).2.1
      have disjoint := (List.nodup_append.mp appendNodup).2.2
      have headMember : segment.headD 0 ∈ segment := by
        cases segment with
        | nil => contradiction
        | cons head tail => simp
      have headNotRest :
          segment.headD 0 ∉
            rest.map (fun candidate => candidate.headD 0) := by
        intro member
        obtain ⟨candidate, candidateMember, headEq⟩ :=
          List.mem_map.mp member
        have candidateNonempty := nonempty candidate
          (List.Mem.tail segment candidateMember)
        have candidateHeadMember : candidate.headD 0 ∈ candidate := by
          cases candidate with
          | nil => contradiction
          | cons head tail => simp
        have inFlatten : candidate.headD 0 ∈ rest.flatten :=
          List.mem_flatten_of_mem candidateMember candidateHeadMember
        exact
          (disjoint (segment.headD 0) headMember
            (candidate.headD 0) inFlatten headEq.symm)
      have restHeads := heads_nodup_of_flatten_nodup restNodup
        (by
          intro candidate member
          exact nonempty candidate (List.Mem.tail segment member))
      simpa using List.nodup_cons.mpr ⟨headNotRest, restHeads⟩

private theorem pairwise_head_lt_of_le_of_ne :
    ∀ segments : List (List Nat),
      segments.Pairwise
          (fun left right => left.headD 0 ≤ right.headD 0) →
      segments.Pairwise
          (fun left right => left.headD 0 ≠ right.headD 0) →
      segments.Pairwise
          (fun left right => left.headD 0 < right.headD 0)
  | [], _, _ => by simp
  | first :: rest, weak, distinct => by
      have weakParts := List.pairwise_cons.mp weak
      have distinctParts := List.pairwise_cons.mp distinct
      refine List.pairwise_cons.mpr ⟨?_,
        pairwise_head_lt_of_le_of_ne rest weakParts.2 distinctParts.2⟩
      intro second member
      exact Nat.lt_of_le_of_ne
        (weakParts.1 second member)
        (distinctParts.1 second member)

theorem sortedOccupiedSegments_pairwise_lt
    (segments : List (List Nat))
    (flattenNodup : segments.flatten.Nodup) :
    (sortedOccupiedSegments segments).Pairwise
      (fun left right => left.headD 0 < right.headD 0) := by
  have compactPermutation := segments_perm_compact segments
  have compactFlattenNodup :
      (compactSegments segments).flatten.Nodup := by
    have flattenedPermutation :
        segments.flatten.Perm (compactSegments segments).flatten := by
      exact compactPermutation.flatten
    exact flattenedPermutation.nodup_iff.mp flattenNodup
  have sortedFlattenNodup :
      (sortedOccupiedSegments segments).flatten.Nodup := by
    simpa [compactSegments] using compactFlattenNodup
  have headNodup := heads_nodup_of_flatten_nodup
    sortedFlattenNodup
      (fun segment member => sortedOccupiedSegments_nonempty member)
  have weak := sortedOccupiedSegments_pairwise_le segments
  have distinct : (sortedOccupiedSegments segments).Pairwise
      (fun left right => left.headD 0 ≠ right.headD 0) :=
    List.pairwise_map.mp headNodup
  exact pairwise_head_lt_of_le_of_ne
    (sortedOccupiedSegments segments) weak distinct

/-! ### Rank-sensitive uses of (20.6a) -/

/-- Positive exponent capped at two for a rank-two rigid block. -/
def capTwoPositive (count : Nat) : Nat :=
  if count < 2 then count else 2

private theorem listDerivesCapRankTwo
    (before segment after : List Nat) (marker : Nat) :
    ∀ extra : Nat,
      ListDerives
        (before ++ [marker] ++ segment ++
          List.replicate (extra + 1) marker ++ after)
        (before ++ [marker] ++ segment ++
          List.replicate (capTwoPositive (extra + 1)) marker ++ after)
  | 0 => by
      simpa [capTwoPositive] using
        (S5_107.ListDerives.refl (basis := basis)
          (before ++ [marker] ++ segment ++ [marker] ++ after))
  | 1 => by
      simpa [capTwoPositive] using
        (S5_107.ListDerives.refl (basis := basis)
          (before ++ [marker] ++ segment ++ [marker, marker] ++ after))
  | extra + 2 => by
      have first :
          ListDerives
            (before ++ [marker] ++ segment ++
              List.replicate (extra + 3) marker ++ after)
            (before ++ [marker] ++ segment ++
              List.replicate (extra + 2) marker ++ after) := by
        simpa [List.replicate_succ, List.append_assoc] using
          listDerives20_6a before
            (List.replicate extra marker ++ after) marker segment []
      exact first.trans
        (listDerivesCapRankTwo before segment after marker (extra + 1))

/-- Renderer with the final marker supplied by the caller. -/
def renderOpenTerminatedBlocks (marker : Nat) :
    List (List Nat) → List Nat
  | [] => []
  | [segment] => segment
  | segment :: next :: rest =>
      segment ++ [marker] ++
        renderOpenTerminatedBlocks marker (next :: rest)

theorem renderTerminatedBlocks_eq_open_append
    (marker : Nat) :
    ∀ {segments : List (List Nat)},
      segments ≠ [] →
      renderTerminatedBlocks marker segments =
        renderOpenTerminatedBlocks marker segments ++ [marker]
  | [], nonempty => False.elim (nonempty rfl)
  | [segment], _ => by
      simp [renderTerminatedBlocks, renderOpenTerminatedBlocks]
  | segment :: next :: rest, _ => by
      have ih := renderTerminatedBlocks_eq_open_append marker
        (segments := next :: rest) (by simp)
      change (segment ++ [marker]) ++
          renderTerminatedBlocks marker (next :: rest) =
        ((segment ++ [marker]) ++
          renderOpenTerminatedBlocks marker (next :: rest)) ++ [marker]
      rw [ih]
      simp only [List.append_assoc]

private theorem listDerivesRemoveRankAtLeastThreeExtras
    (before second after : List Nat) (marker : Nat)
    (later : List (List Nat)) (laterNonempty : later ≠ []) :
    ∀ extra : Nat,
      ListDerives
        (before ++ [marker] ++ second ++ [marker] ++
          renderOpenTerminatedBlocks marker later ++ [marker] ++
          List.replicate extra marker ++ after)
        (before ++ [marker] ++ second ++ [marker] ++
          renderOpenTerminatedBlocks marker later ++ [marker] ++ after)
  | 0 => by
      simpa only [List.replicate_zero, List.append_nil] using
        (S5_107.ListDerives.refl (basis := basis)
          (before ++ [marker] ++ second ++ [marker] ++
            renderOpenTerminatedBlocks marker later ++ [marker] ++ after))
  | extra + 1 => by
      have first :
          ListDerives
            (before ++ [marker] ++ second ++ [marker] ++
              renderOpenTerminatedBlocks marker later ++ [marker] ++
              List.replicate (extra + 1) marker ++ after)
            (before ++ [marker] ++ second ++ [marker] ++
              renderOpenTerminatedBlocks marker later ++ [marker] ++
              List.replicate extra marker ++ after) := by
        simpa [List.replicate_succ, List.append_assoc] using
          listDerives20_6a before
            (List.replicate extra marker ++ after) marker second
            (renderOpenTerminatedBlocks marker later)
      exact first.trans
        (listDerivesRemoveRankAtLeastThreeExtras
          before second after marker later laterNonempty extra)

/-- Rank-dependent terminal exponent selected by (Ri3)--(Ri5). -/
def rigidExponent
    (tailSegments : List (List Nat)) (extra : Nat) : Nat :=
  match tailSegments with
  | [] => capThree (extra + 1)
  | [_] => capTwoPositive (extra + 1)
  | _ :: _ :: _ => 1

theorem rigidExponent_pos
    (tailSegments : List (List Nat)) (extra : Nat) :
    1 <= rigidExponent tailSegments extra := by
  cases tailSegments with
  | nil =>
      simp [rigidExponent, capThree]
      split <;> omega
  | cons first later =>
      cases later with
      | nil =>
          simp [rigidExponent, capTwoPositive]
          split <;> omega
      | cons second rest => simp [rigidExponent]

private theorem replicate_eq_singleton_append_pred
    (marker count : Nat) (positive : 1 <= count) :
    List.replicate count marker =
      [marker] ++ List.replicate (count - 1) marker := by
  cases count with
  | zero => omega
  | succ predecessor => simp [List.replicate_succ]

/-- Cap only the terminal run justified by the displayed rigid-block rank.
This is deliberately not a global cap-three theorem. -/
theorem listDerivesCapRigidTail
    (before after : List Nat) (marker : Nat) :
    ∀ (tailSegments : List (List Nat)) (extra : Nat),
      ListDerives
        (before ++ [marker] ++
          renderTerminatedBlocks marker tailSegments ++
          List.replicate extra marker ++ after)
        (before ++ [marker] ++
          renderTerminatedBlocks marker tailSegments ++
          List.replicate
            (rigidExponent tailSegments extra - 1) marker ++ after)
  | [], extra => by
      have capped := listDerivesCapRunThree before after marker (extra + 1)
      have exponentPositive := rigidExponent_pos [] extra
      have exponentShape := replicate_eq_singleton_append_pred marker
        (rigidExponent [] extra) exponentPositive
      simp only [rigidExponent] at exponentShape
      rw [exponentShape] at capped
      simpa [rigidExponent, renderTerminatedBlocks, List.replicate_succ,
        List.append_assoc] using capped
  | [segment], extra => by
      have capped := listDerivesCapRankTwo
        before segment after marker extra
      have exponentPositive := rigidExponent_pos [segment] extra
      have exponentShape := replicate_eq_singleton_append_pred marker
        (rigidExponent [segment] extra) exponentPositive
      simp only [rigidExponent] at exponentShape
      rw [exponentShape] at capped
      simpa [rigidExponent, renderTerminatedBlocks, List.replicate_succ,
        List.append_assoc] using capped
  | second :: third :: rest, extra => by
      have openShape := renderTerminatedBlocks_eq_open_append marker
        (segments := third :: rest) (by simp)
      have capped := listDerivesRemoveRankAtLeastThreeExtras
        before second after marker (third :: rest) (by simp) extra
      have fullShape :
          renderTerminatedBlocks marker (second :: third :: rest) =
            second ++ [marker] ++
              renderOpenTerminatedBlocks marker (third :: rest) ++ [marker] := by
        change (second ++ [marker]) ++
            renderTerminatedBlocks marker (third :: rest) = _
        rw [openShape]
        simp only [List.append_assoc]
      rw [fullShape]
      simpa only [rigidExponent, List.replicate_zero, List.append_nil,
        List.append_assoc] using capped

/-! ## Rigidifying one gathered marker class (Lemma 20.10(i)) -/

private theorem flatten_perm_of_perm {alpha : Type}
    {source target : List (List alpha)}
    (permutation : source.Perm target) :
    source.flatten.Perm target.flatten := by
  induction permutation with
  | nil => exact List.Perm.refl []
  | cons block _ ih => simpa using ih.append_left block
  | swap left right rest =>
      have swapped : (right ++ left).Perm (left ++ right) :=
        List.perm_append_comm
      simpa [List.append_assoc] using
        swapped.append_right rest.flatten
  | trans _ _ first second => exact first.trans second

/-- The simple segments stored by a gathered marker class. -/
def markedGroupGaps (group : MarkedGroup) : List (List Nat) :=
  group.factors.map MarkedFactor.gap

private theorem renderMarkedFactors_eq_renderTerminatedBlocks
    (marker : Nat) :
    ∀ factors : List MarkedFactor,
      (∀ factor ∈ factors, factor.marker = marker) ->
      renderMarkedFactors factors =
        renderTerminatedBlocks marker
          (factors.map MarkedFactor.gap)
  | [], _ => rfl
  | factor :: rest, markers => by
      have headMarker := markers factor (by simp)
      have tailMarkers :
          ∀ candidate ∈ rest, candidate.marker = marker := by
        intro candidate member
        exact markers candidate (by simp [member])
      have ih := renderMarkedFactors_eq_renderTerminatedBlocks
        marker rest tailMarkers
      simp [renderMarkedFactors, renderMarkedFactor,
        renderTerminatedBlocks, headMarker, ih, List.append_assoc]

theorem MarkedGroups.Valid.render_group
    {groups : List MarkedGroup}
    (valid : MarkedGroups.Valid groups)
    {group : MarkedGroup} (member : group ∈ groups) :
    renderMarkedFactors group.factors =
      renderTerminatedBlocks group.marker (markedGroupGaps group) := by
  apply renderMarkedFactors_eq_renderTerminatedBlocks
  exact valid.factors_marker group member

private theorem count_group_markers
    (marker : Nat) :
    ∀ factors : List MarkedFactor,
      (∀ factor ∈ factors, factor.marker = marker) ->
      (markedMarkers factors).count marker = factors.length
  | [], _ => by simp [markedMarkers]
  | factor :: rest, markers => by
      have headMarker := markers factor (by simp)
      have tailMarkers :
          ∀ candidate ∈ rest, candidate.marker = marker := by
        intro candidate member
        exact markers candidate (by simp [member])
      have ih := count_group_markers marker rest tailMarkers
      simp only [markedMarkers] at ih
      simp [markedMarkers, headMarker, ih]

private theorem count_other_group_markers
    (marker other : Nat) (different : marker ≠ other) :
    ∀ factors : List MarkedFactor,
      (∀ factor ∈ factors, factor.marker = other) ->
      (markedMarkers factors).count marker = 0
  | [], _ => by simp [markedMarkers]
  | factor :: rest, markers => by
      have headMarker := markers factor (by simp)
      have tailMarkers :
          ∀ candidate ∈ rest, candidate.marker = other := by
        intro candidate member
        exact markers candidate (by simp [member])
      have ih := count_other_group_markers marker other different rest tailMarkers
      simp only [markedMarkers] at ih
      simp [markedMarkers, headMarker, different, Ne.symm different, ih]

private theorem exists_group_of_factor_mem_flattenMarkedGroups
    {factor : MarkedFactor} : ∀ {groups : List MarkedGroup},
      factor ∈ flattenMarkedGroups groups ->
      ∃ group ∈ groups, factor ∈ group.factors
  | [], member => by simp at member
  | group :: later, member => by
      simp only [flattenMarkedGroups_cons, List.mem_append] at member
      rcases member with inGroup | inLater
      · exact ⟨group, by simp, inGroup⟩
      · obtain ⟨selected, selectedMember, factorMember⟩ :=
          exists_group_of_factor_mem_flattenMarkedGroups inLater
        exact ⟨selected, by simp [selectedMember], factorMember⟩

private theorem marker_absent_from_later_groups
    {first : MarkedGroup} {later : List MarkedGroup}
    (valid : MarkedGroups.Valid (first :: later)) :
    (markedMarkers (flattenMarkedGroups later)).count first.marker = 0 := by
  have absent : first.marker ∉ markedGroupMarkers later := by
    simpa [markedGroupMarkers] using
      (List.nodup_cons.mp valid.markers_nodup).1
  apply List.count_eq_zero.mpr
  intro markerMember
  obtain ⟨factor, factorMember, factorMarker⟩ :=
    List.mem_map.mp markerMember
  obtain ⟨group, groupMember, inGroup⟩ :=
    exists_group_of_factor_mem_flattenMarkedGroups factorMember
  have groupMarker := valid.factors_marker group
    (by simp [groupMember]) factor inGroup
  apply absent
  exact (marker_mem_markedGroupMarkers_iff _ _).2
    ⟨group, groupMember, groupMarker.symm.trans factorMarker⟩

private theorem MarkedGroups.Valid.count_group_marker
    {groups : List MarkedGroup}
    (valid : MarkedGroups.Valid groups)
    {group : MarkedGroup} (member : group ∈ groups) :
    (markedMarkers (flattenMarkedGroups groups)).count group.marker =
      group.factors.length := by
  induction groups with
  | nil => simp at member
  | cons first later ih =>
      rcases List.mem_cons.mp member with rfl | inLater
      · have headCount := count_group_markers group.marker
          group.factors (valid.factors_marker group (by simp))
        have tailCount := marker_absent_from_later_groups valid
        dsimp only [markedMarkers] at headCount tailCount
        simpa [flattenMarkedGroups, markedMarkers, List.map_append,
          List.count_append, headCount, tailCount]
      · have laterValid : MarkedGroups.Valid later := by
          refine
            { factors_nonempty := ?_
              factors_marker := ?_
              markers_nodup := ?_ }
          · intro selected selectedMember
            exact valid.factors_nonempty selected (by simp [selectedMember])
          · intro selected selectedMember factor factorMember
            exact valid.factors_marker selected (by simp [selectedMember])
              factor factorMember
          · exact (List.nodup_cons.mp valid.markers_nodup).2
        have firstDifferent : group.marker ≠ first.marker := by
          intro equal
          have firstIn : first.marker ∈ markedGroupMarkers later := by
            exact (marker_mem_markedGroupMarkers_iff _ _).2
              ⟨group, inLater, equal⟩
          exact (List.nodup_cons.mp valid.markers_nodup).1 firstIn
        have firstZero := count_other_group_markers group.marker
          first.marker firstDifferent first.factors
            (valid.factors_marker first (by simp))
        have tailCount := ih laterValid inLater
        dsimp only [markedMarkers] at firstZero tailCount
        simpa [flattenMarkedGroups, markedMarkers, List.map_append,
          List.count_append, firstZero, tailCount]

/-- A repeated-marker hypothesis localizes to the length of its unique
gathered class. -/
theorem MarkedGroups.Valid.group_length_at_least_two
    {groups : List MarkedGroup}
    (valid : MarkedGroups.Valid groups)
    (repeated : MarkersRepeated (flattenMarkedGroups groups))
    {group : MarkedGroup} (member : group ∈ groups) :
    2 <= group.factors.length := by
  obtain ⟨factor, factorMember⟩ :=
    List.exists_mem_of_ne_nil group.factors
      (valid.factors_nonempty group member)
  have bound := repeated factor
    (factor_mem_flattenMarkedGroups member factorMember)
  have markerEq := valid.factors_marker group member factor factorMember
  have exactCount := valid.count_group_marker member
  simpa [markerEq, exactCount] using bound

private theorem renderTerminatedBlocks_append
    (marker : Nat) : ∀ left right : List (List Nat),
      renderTerminatedBlocks marker (left ++ right) =
        renderTerminatedBlocks marker left ++
          renderTerminatedBlocks marker right
  | [], _ => rfl
  | segment :: rest, right => by
      simp [renderTerminatedBlocks,
        renderTerminatedBlocks_append marker rest right,
        List.append_assoc]

private theorem renderTerminatedBlocks_replicate_empty
    (marker : Nat) : ∀ count : Nat,
      renderTerminatedBlocks marker
          (List.replicate count ([] : List Nat)) =
        List.replicate count marker
  | 0 => rfl
  | count + 1 => by
      simp [renderTerminatedBlocks, List.replicate_succ,
        renderTerminatedBlocks_replicate_empty marker count]

private theorem renderRigidTail_eq_renderTerminatedBlocks
    (marker : Nat) : ∀ segments : List (List Nat),
      renderRigidTail marker segments =
        renderTerminatedBlocks marker segments
  | [] => rfl
  | segment :: rest => by
      simp [renderRigidTail, renderTerminatedBlocks,
        renderRigidTail_eq_renderTerminatedBlocks marker rest,
        List.append_assoc]

/-- Deterministic rigid representative when the first segment is frozen.
Only tail segments are sorted, exactly as Lemma 20.10(i) permits. -/
def rigidBlockOfFirst
    (marker : Nat) (firstGap : List Nat)
    (tailGaps : List (List Nat)) : RigidBlock :=
  { marker := marker
    first := firstGap
    rest := sortedOccupiedSegments tailGaps
    exponent := rigidExponent
      (sortedOccupiedSegments tailGaps)
      (emptySegmentCount tailGaps) }

theorem rigidBlockOfFirst_payload_perm
    (marker : Nat) (firstGap : List Nat)
    (tailGaps : List (List Nat)) :
    (firstGap ++ tailGaps.flatten).Perm
      ((rigidBlockOfFirst marker firstGap tailGaps).first ++
        (rigidBlockOfFirst marker firstGap tailGaps).rest.flatten) := by
  have compactPermutation :=
    flatten_perm_of_perm (segments_perm_compact tailGaps)
  have tailPermutation : tailGaps.flatten.Perm
      (sortedOccupiedSegments tailGaps).flatten := by
    simpa [compactSegments] using compactPermutation
  simpa [rigidBlockOfFirst] using tailPermutation.append_left firstGap

private theorem count_renderRigidTail_of_ne_marker
    (marker letter : Nat) (different : letter ≠ marker) :
    ∀ segments : List (List Nat),
      (renderRigidTail marker segments).count letter =
        segments.flatten.count letter
  | [] => by simp
  | segment :: rest => by
      simp [renderRigidTail, List.count_append, different, Ne.symm different,
        count_renderRigidTail_of_ne_marker marker letter different rest]

private theorem count_renderRigidBlock_of_ne_marker
    (block : RigidBlock) (letter : Nat)
    (different : letter ≠ block.marker) :
    (renderRigidBlock block).count letter =
      (block.first ++ block.rest.flatten).count letter := by
  simp [renderRigidBlock, List.count_append, List.count_replicate,
    count_renderRigidTail_of_ne_marker block.marker letter different,
    different, Ne.symm different]

private theorem marker_free_sorted_segments
    {marker : Nat} {segments : List (List Nat)}
    (absent : marker ∉ segments.flatten) :
    ∀ segment ∈ sortedOccupiedSegments segments,
      marker ∉ segment := by
  intro segment member inSegment
  have inOccupied : segment ∈ occupiedSegments segments := by
    simpa [sortedOccupiedSegments] using member
  have inSource : segment ∈ segments := by
    exact (List.mem_filter.mp inOccupied).1
  exact absent (List.mem_flatten_of_mem inSource inSegment)

private theorem rigidBlockOfFirst_count_marker
    (marker : Nat) (firstGap : List Nat)
    (tailGaps : List (List Nat))
    (markerAbsent : marker ∉ firstGap ++ tailGaps.flatten) :
    (renderRigidBlock
      (rigidBlockOfFirst marker firstGap tailGaps)).count marker =
      (sortedOccupiedSegments tailGaps).length +
        rigidExponent (sortedOccupiedSegments tailGaps)
          (emptySegmentCount tailGaps) := by
  have firstAbsent : marker ∉ firstGap := by
    intro member
    exact markerAbsent (by simp [member])
  have tailAbsent : marker ∉ tailGaps.flatten := by
    intro member
    exact markerAbsent (by simp [member])
  have sortedAbsent := marker_free_sorted_segments tailAbsent
  have firstCount : firstGap.count marker = 0 :=
    List.count_eq_zero.mpr firstAbsent
  have tailCount := count_renderRigidTail_of_marker_free marker
    (sortedOccupiedSegments tailGaps) sortedAbsent
  have exponentPositive := rigidExponent_pos
    (sortedOccupiedSegments tailGaps) (emptySegmentCount tailGaps)
  simp [rigidBlockOfFirst, renderRigidBlock,
    List.count_append, firstCount, tailCount] <;> omega

private theorem rigidBlockOfFirst_payload_nodup
    (marker : Nat) (firstGap : List Nat)
    (tailGaps : List (List Nat))
    (payloadNodup : (firstGap ++ tailGaps.flatten).Nodup) :
    ((rigidBlockOfFirst marker firstGap tailGaps).first ++
      (rigidBlockOfFirst marker firstGap tailGaps).rest.flatten).Nodup :=
  (rigidBlockOfFirst_payload_perm marker firstGap tailGaps).nodup_iff.mp
    payloadNodup

/-- Conditions (Ri1)--(Ri5) for the exact representative constructed above.
The two-factor premise is the localized non-simplicity debt. -/
theorem rigidBlockOfFirst_valid
    (marker : Nat) (firstGap : List Nat)
    (tailGaps : List (List Nat))
    (twoFactors : 2 <= tailGaps.length + 1)
    (payloadNodup : (firstGap ++ tailGaps.flatten).Nodup)
    (markerAbsent : marker ∉ firstGap ++ tailGaps.flatten) :
    (rigidBlockOfFirst marker firstGap tailGaps).Valid := by
  let block := rigidBlockOfFirst marker firstGap tailGaps
  have compactLength := (segments_perm_compact tailGaps).length_eq
  have lengthEquation :
      tailGaps.length =
        (sortedOccupiedSegments tailGaps).length +
          emptySegmentCount tailGaps := by
    simpa [compactSegments] using compactLength
  have targetPayloadNodup := rigidBlockOfFirst_payload_nodup
    marker firstGap tailGaps payloadNodup
  have targetMarkerAbsent :
      marker ∉ block.first ++ block.rest.flatten := by
    intro member
    have sourceMember :=
      (rigidBlockOfFirst_payload_perm marker firstGap tailGaps).mem_iff.mpr
        member
    exact markerAbsent sourceMember
  have markerCount := rigidBlockOfFirst_count_marker
    marker firstGap tailGaps markerAbsent
  refine
    { nonSimple := ?_
      positiveSegments := ?_
      exponentRange := ?_
      ri1 := ?_
      ri2 := ?_
      ri3 := ?_
      ri4 := ?_
      ri5 := ?_ }
  · unfold NonSimple
    change 2 <= (renderRigidBlock
      (rigidBlockOfFirst marker firstGap tailGaps)).count marker
    rw [markerCount]
    cases restShape : sortedOccupiedSegments tailGaps with
    | nil =>
        simp [block, rigidBlockOfFirst, rigidExponent, restShape]
          at lengthEquation ⊢
        have positiveEmpty : 1 <= emptySegmentCount tailGaps := by omega
        unfold capThree
        split <;> omega
    | cons segment rest =>
        cases rest with
        | nil =>
            simp [block, rigidBlockOfFirst, rigidExponent, restShape,
              capTwoPositive]
            split <;> omega
        | cons next later =>
            simp [block, rigidBlockOfFirst, rigidExponent, restShape]
  · intro segment member
    exact sortedOccupiedSegments_nonempty
      (by simpa [block, rigidBlockOfFirst] using member)
  · cases restShape : sortedOccupiedSegments tailGaps with
    | nil =>
        simp [block, rigidBlockOfFirst, rigidExponent, restShape,
          capThree]
        split <;> omega
    | cons segment rest =>
        cases rest with
        | nil =>
            simp [block, rigidBlockOfFirst, rigidExponent, restShape,
              capTwoPositive]
            split <;> omega
        | cons next later =>
            simp [block, rigidBlockOfFirst, rigidExponent, restShape]
  · intro segment segmentMember letter letterMember
    have payloadMember : letter ∈ block.first ++ block.rest.flatten := by
      rcases List.mem_cons.mp segmentMember with inFirst | inRest
      · subst segment
        exact List.mem_append_left _ letterMember
      · exact List.mem_append_right _
          (List.mem_flatten_of_mem inRest letterMember)
    have different : letter ≠ block.marker := by
      intro equal
      exact targetMarkerAbsent (by simpa [equal] using payloadMember)
    unfold Simple
    rw [count_renderRigidBlock_of_ne_marker block letter different]
    rw [targetPayloadNodup.count, if_pos payloadMember]
  · have tailNodup : tailGaps.flatten.Nodup :=
      (List.nodup_append.mp payloadNodup).2.1
    simpa [block, rigidBlockOfFirst, RigidBlock.heads] using
      (List.pairwise_map.mpr
        (sortedOccupiedSegments_pairwise_lt tailGaps tailNodup))
  · intro rankOne
    have restEmpty : sortedOccupiedSegments tailGaps = [] := by
      simp [block, rigidBlockOfFirst, RigidBlock.rank] at rankOne
      exact rankOne
    have positiveEmpty : 1 <= emptySegmentCount tailGaps := by
      rw [restEmpty] at lengthEquation
      simp at lengthEquation
      omega
    simp [block, rigidBlockOfFirst, rigidExponent, restEmpty, capThree]
    split <;> omega
  · intro rankTwo
    have restLength :
        (sortedOccupiedSegments tailGaps).length = 1 := by
      simp [block, rigidBlockOfFirst, RigidBlock.rank] at rankTwo
      omega
    cases restShape : sortedOccupiedSegments tailGaps with
    | nil => simp [restShape] at restLength
    | cons segment later =>
        cases laterShape : later with
        | nil =>
            simp [block, rigidBlockOfFirst, rigidExponent, restShape,
              laterShape, capTwoPositive]
            split <;> omega
        | cons next rest =>
            simp [restShape, laterShape] at restLength
  · intro rankAtLeastThree
    have restLength :
        2 <= (sortedOccupiedSegments tailGaps).length := by
      simpa [block, rigidBlockOfFirst, RigidBlock.rank] using
        rankAtLeastThree
    cases restShape : sortedOccupiedSegments tailGaps with
    | nil => simp [restShape] at restLength
    | cons second later =>
        cases laterShape : later with
        | nil => simp [restShape, laterShape] at restLength
        | cons third tail =>
            simp [block, rigidBlockOfFirst, rigidExponent,
              restShape, laterShape]

/-- Exact first-block normalization: permute only tail `s_i x` factors,
then apply the rank-sensitive terminal cap. -/
theorem listDerivesRigidBlockOfFirst
    (before after : List Nat) (marker : Nat)
    (firstGap : List Nat) (tailGaps : List (List Nat)) :
    ListDerives
      (before ++ firstGap ++ [marker] ++
        renderTerminatedBlocks marker tailGaps ++ after)
      (before ++ renderRigidBlock
        (rigidBlockOfFirst marker firstGap tailGaps) ++ after) := by
  have permuted := listDerivesPermuteXBlocks
    (before ++ firstGap) after marker
      (segments_perm_compact tailGaps)
  have compactRender :
      renderTerminatedBlocks marker (compactSegments tailGaps) =
        renderTerminatedBlocks marker
            (sortedOccupiedSegments tailGaps) ++
          List.replicate (emptySegmentCount tailGaps) marker := by
    simp [compactSegments, renderTerminatedBlocks_append,
      renderTerminatedBlocks_replicate_empty]
  have capped := listDerivesCapRigidTail
    (before ++ firstGap) after marker
      (sortedOccupiedSegments tailGaps)
      (emptySegmentCount tailGaps)
  have permutedContext :
      ListDerives
        (before ++ firstGap ++ [marker] ++
          renderTerminatedBlocks marker tailGaps ++ after)
        (before ++ firstGap ++ [marker] ++
          renderTerminatedBlocks marker (sortedOccupiedSegments tailGaps) ++
          List.replicate (emptySegmentCount tailGaps) marker ++ after) := by
    simpa [compactRender, List.append_assoc] using permuted
  have cappedContext :
      ListDerives
        (before ++ firstGap ++ [marker] ++
          renderTerminatedBlocks marker (sortedOccupiedSegments tailGaps) ++
          List.replicate (emptySegmentCount tailGaps) marker ++ after)
        (before ++ renderRigidBlock
          (rigidBlockOfFirst marker firstGap tailGaps) ++ after) := by
    simpa [rigidBlockOfFirst, renderRigidBlock,
      renderRigidTail_eq_renderTerminatedBlocks,
      List.append_assoc] using capped
  exact permutedContext.trans cappedContext

/-! ## Fully rigid later blocks (Lemma 20.10(ii)) -/

private theorem renderRigidTail_append
    (marker : Nat) : ∀ left right : List (List Nat),
      renderRigidTail marker (left ++ right) =
        renderRigidTail marker left ++ renderRigidTail marker right
  | [], _ => rfl
  | segment :: rest, right => by
      simp [renderRigidTail,
        renderRigidTail_append marker rest right,
        List.append_assoc]

private theorem exists_append_singleton_of_ne_nil {alpha : Type} :
    ∀ (letters : List alpha), letters ≠ [] ->
      ∃ before final, letters = before ++ [final]
  | [], nonempty => False.elim (nonempty rfl)
  | head :: tail, _ => by
      cases tail with
      | nil => exact ⟨[], head, rfl⟩
      | cons next rest =>
          obtain ⟨before, final, shape⟩ :=
            exists_append_singleton_of_ne_nil (next :: rest) (by simp)
          exact ⟨head :: before, final, by simp [shape]⟩

/-- Every valid rigid block exposes two terminally anchored copies of its
marker.  This is the exact guard shape required by (20.6c) and (20.6f). -/
theorem RigidBlock.Valid.exists_terminalRepeatedSplit
    {block : RigidBlock} (valid : block.Valid) :
    ∃ before middle,
      renderRigidBlock block =
        before ++ [block.marker] ++ middle ++ [block.marker] := by
  rcases valid.exponentRange with exponent | exponent | exponent
  · have restNonempty : block.rest ≠ [] := by
      have count := valid.count_marker
      have multiple := valid.nonSimple
      unfold NonSimple at multiple
      rw [exponent] at count
      intro empty
      rw [empty] at count
      simp at count
      omega
    obtain ⟨beforeRest, finalSegment, restShape⟩ :=
      exists_append_singleton_of_ne_nil block.rest restNonempty
    refine ⟨block.first,
      renderRigidTail block.marker beforeRest ++ finalSegment, ?_⟩
    simp [renderRigidBlock, exponent, restShape,
      renderRigidTail_append, List.append_assoc]
  · refine ⟨block.first, renderRigidTail block.marker block.rest, ?_⟩
    simp [renderRigidBlock, exponent, List.append_assoc]
  · refine ⟨block.first,
      renderRigidTail block.marker block.rest ++ [block.marker], ?_⟩
    simp [renderRigidBlock, exponent, List.append_assoc]

/-- Under a displayed repeated guard `x H x`, (20.6c) selects the first
`s y` factor and (20.6b) permutes every remaining complete factor. -/
theorem listDerivesPermuteTerminatedBlocksAfterGuard20_6c
    (before after : List Nat) (guard marker : Nat)
    (guardMiddle : List Nat)
    {source target : List (List Nat)}
    (sourceNonempty : source ≠ [])
    (permutation : source.Perm target) :
    ListDerives
      (before ++ [guard] ++ guardMiddle ++ [guard] ++
        renderTerminatedBlocks marker source ++ after)
      (before ++ [guard] ++ guardMiddle ++ [guard] ++
        renderTerminatedBlocks marker target ++ after) := by
  cases target with
  | nil =>
      have sourceEmpty : source = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro segment member
        have targetMember := permutation.mem_iff.mp member
        simp at targetMember
      exact False.elim (sourceNonempty sourceEmpty)
  | cons selected targetTail =>
      have selectedInSource : selected ∈ source :=
        permutation.mem_iff.mpr (by simp)
      obtain ⟨front, suffix, sourceShape⟩ :=
        List.mem_iff_append.mp selectedInSource
      have remainderPermutation :
          (front ++ suffix).Perm targetTail := by
        rw [List.perm_iff_count]
        intro tested
        have counts := permutation.count_eq tested
        rw [sourceShape] at counts
        by_cases same : selected = tested <;>
          simp [List.count_append, List.count_cons, same] at counts ⊢ <;> omega
      have selectedFirst :
          ListDerives
            (before ++ [guard] ++ guardMiddle ++ [guard] ++
              renderTerminatedBlocks marker source ++ after)
            (before ++ [guard] ++ guardMiddle ++ [guard] ++
              selected ++ [marker] ++
                renderTerminatedBlocks marker (front ++ suffix) ++
                  after) := by
        cases front with
        | nil =>
            simpa [sourceShape, renderTerminatedBlocks,
              List.append_assoc] using
                (S5_107.ListDerives.refl (basis := basis)
                  (before ++ [guard] ++ guardMiddle ++ [guard] ++
                    selected ++ [marker] ++
                      renderTerminatedBlocks marker suffix ++ after))
        | cons prefixHead prefixTail =>
            let occupiedPrefix := prefixHead :: prefixTail
            have prefixOpen := renderTerminatedBlocks_eq_open_append marker
              (segments := occupiedPrefix) (by simp [occupiedPrefix])
            have moved := listDerivesMoveTerminatedBlockToHead20_6c
              before
                (renderTerminatedBlocks marker suffix ++ after)
              guard marker guardMiddle
                (renderOpenTerminatedBlocks marker occupiedPrefix)
                selected
            have prefixShape :
                renderTerminatedBlocks marker (prefixHead :: prefixTail) =
                  renderOpenTerminatedBlocks marker (prefixHead :: prefixTail) ++
                    [marker] := prefixOpen
            simp only [sourceShape, renderTerminatedBlocks_append, prefixShape]
            simpa [occupiedPrefix, renderTerminatedBlocks, List.append_assoc] using moved
      have tailPermuted := listDerivesPermuteXBlocks
        (before ++ [guard] ++ guardMiddle ++ [guard] ++ selected)
        after marker remainderPermutation
      exact selectedFirst.trans <| by
        simpa [renderTerminatedBlocks_append, renderTerminatedBlocks,
          List.append_assoc] using tailPermuted

/-- Canonical later-block data.  If there is simple material, the least
occupied segment is selected as `s1`; otherwise all factors become the
terminal marker run. -/
def fullyRigidBlock
    (marker : Nat) (gaps : List (List Nat)) : RigidBlock :=
  match sortedOccupiedSegments gaps with
  | [] =>
      { marker := marker
        first := []
        rest := []
        exponent := capThree (emptySegmentCount gaps) }
  | first :: rest =>
      { marker := marker
        first := first
        rest := rest
        exponent := rigidExponent rest (emptySegmentCount gaps) }

@[simp] theorem fullyRigidBlock_marker
    (marker : Nat) (gaps : List (List Nat)) :
    (fullyRigidBlock marker gaps).marker = marker := by
  unfold fullyRigidBlock
  split <;> rfl

theorem fullyRigidBlock_payload_perm
    (marker : Nat) (gaps : List (List Nat)) :
    gaps.flatten.Perm
      ((fullyRigidBlock marker gaps).first ++
        (fullyRigidBlock marker gaps).rest.flatten) := by
  have compactPermutation :=
    flatten_perm_of_perm (segments_perm_compact gaps)
  cases sortedShape : sortedOccupiedSegments gaps with
  | nil =>
      simpa [compactSegments, fullyRigidBlock, sortedShape] using
        compactPermutation
  | cons first rest =>
      simpa [compactSegments, fullyRigidBlock, sortedShape] using
        compactPermutation

private theorem rigidBlock_valid_of_payload
    (block : RigidBlock)
    (payloadNodup : (block.first ++ block.rest.flatten).Nodup)
    (markerAbsent : block.marker ∉
      block.first ++ block.rest.flatten)
    (positiveSegments :
      ∀ segment ∈ block.rest, segment ≠ [])
    (orderedHeads :
      block.heads.Pairwise (fun left right => left < right))
    (exponentRange : block.exponent = 1 ∨
      block.exponent = 2 ∨ block.exponent = 3)
    (markerCount : 2 <= block.rest.length + block.exponent)
    (rankOne : block.rank = 1 ->
      block.exponent = 2 ∨ block.exponent = 3)
    (rankTwo : block.rank = 2 ->
      block.exponent = 1 ∨ block.exponent = 2)
    (rankThree : 3 <= block.rank -> block.exponent = 1) :
    block.Valid := by
  have exponentPositive : 1 <= block.exponent := by
    rcases exponentRange with exponent | exponent | exponent <;> omega
  have firstAbsent : block.marker ∉ block.first := by
    intro member
    exact markerAbsent (by simp [member])
  have restAbsent :
      ∀ segment ∈ block.rest, block.marker ∉ segment := by
    intro segment segmentMember letterMember
    exact markerAbsent <| List.mem_append_right _
      (List.mem_flatten_of_mem segmentMember letterMember)
  have firstCount : block.first.count block.marker = 0 :=
    List.count_eq_zero.mpr firstAbsent
  have tailCount := count_renderRigidTail_of_marker_free
    block.marker block.rest restAbsent
  refine
    { nonSimple := ?_
      positiveSegments := positiveSegments
      exponentRange := exponentRange
      ri1 := ?_
      ri2 := orderedHeads
      ri3 := rankOne
      ri4 := rankTwo
      ri5 := rankThree }
  · unfold NonSimple
    simp [renderRigidBlock, List.count_append,
      firstCount, tailCount] <;> omega
  · intro segment segmentMember letter letterMember
    have payloadMember : letter ∈ block.first ++ block.rest.flatten := by
      rcases List.mem_cons.mp segmentMember with inFirst | inRest
      · subst segment
        exact List.mem_append_left _ letterMember
      · exact List.mem_append_right _
          (List.mem_flatten_of_mem inRest letterMember)
    have different : letter ≠ block.marker := by
      intro equal
      exact markerAbsent (by simpa [equal] using payloadMember)
    unfold Simple
    rw [count_renderRigidBlock_of_ne_marker block letter different]
    rw [payloadNodup.count, if_pos payloadMember]

/-- Lemma 20.10(ii), including the deterministic later-block
left-normalization needed by `CanonicalForm.ReducedValid`. -/
theorem fullyRigidBlock_fullyRigid
    (marker : Nat) (gaps : List (List Nat))
    (twoFactors : 2 <= gaps.length)
    (payloadNodup : gaps.flatten.Nodup)
    (markerAbsent : marker ∉ gaps.flatten) :
    (fullyRigidBlock marker gaps).FullyRigid ∧
      (fullyRigidBlock marker gaps).LeftNormalized := by
  let block := fullyRigidBlock marker gaps
  have compactLength := (segments_perm_compact gaps).length_eq
  have lengthEquation :
      gaps.length = (sortedOccupiedSegments gaps).length +
        emptySegmentCount gaps := by
    simpa [compactSegments] using compactLength
  have targetPayloadNodup :
      (block.first ++ block.rest.flatten).Nodup :=
    (fullyRigidBlock_payload_perm marker gaps).nodup_iff.mp payloadNodup
  have targetMarkerAbsent :
      marker ∉ block.first ++ block.rest.flatten := by
    intro member
    exact markerAbsent
      ((fullyRigidBlock_payload_perm marker gaps).mem_iff.mpr member)
  have sortedStrict := sortedOccupiedSegments_pairwise_lt gaps payloadNodup
  cases sortedShape : sortedOccupiedSegments gaps with
  | nil =>
      have emptyAtLeastTwo : 2 <= emptySegmentCount gaps := by
        rw [sortedShape] at lengthEquation
        simp at lengthEquation
        omega
      have exponentChoice : capThree (emptySegmentCount gaps) = 2 ∨
          capThree (emptySegmentCount gaps) = 3 := by
        unfold capThree
        split <;> omega
      have valid : block.Valid := by
        apply rigidBlock_valid_of_payload block
        · exact targetPayloadNodup
        · simpa only [block, fullyRigidBlock_marker] using targetMarkerAbsent
        · simp [block, fullyRigidBlock, sortedShape]
        · simp [block, fullyRigidBlock, sortedShape,
            RigidBlock.heads]
        · simpa [block, fullyRigidBlock, sortedShape] using
            (Or.inr exponentChoice)
        · change 2 <= block.rest.length + block.exponent
          simp only [block, fullyRigidBlock, sortedShape, List.length_nil,
            Nat.zero_add]
          rcases exponentChoice with exponent | exponent <;> omega
        · intro _
          simpa [block, fullyRigidBlock, sortedShape] using exponentChoice
        · intro rankTwo
          simp [block, fullyRigidBlock, sortedShape,
            RigidBlock.rank] at rankTwo
        · intro rankThree
          simp [block, fullyRigidBlock, sortedShape,
            RigidBlock.rank] at rankThree
      refine ⟨?_, ?_⟩
      · exact
          { toValid := valid
            ri6 := by
              intro firstNonempty
              exact False.elim <| firstNonempty <| by
                simp [block, fullyRigidBlock, sortedShape] }
      · intro _
        simp [block, fullyRigidBlock, sortedShape]
  | cons first rest =>
      have firstNonempty : first ≠ [] :=
        sortedOccupiedSegments_nonempty (segments := gaps) (by simp [sortedShape])
      have restPositive : ∀ segment ∈ rest, segment ≠ [] := by
        intro segment member
        exact sortedOccupiedSegments_nonempty (segments := gaps)
          (by simp [sortedShape, member])
      have allHeadsStrict :
          (first.headD 0 :: rest.map fun segment => segment.headD 0).Pairwise
            (fun left right => left < right) := by
        change ((first :: rest).map fun segment => segment.headD 0).Pairwise
          (fun left right => left < right)
        apply List.pairwise_map.mpr
        simpa only [sortedShape] using sortedStrict
      have tailHeadsStrict :
          (rest.map fun segment => segment.headD 0).Pairwise
            (fun left right => left < right) :=
        (List.pairwise_cons.mp allHeadsStrict).2
      have valid : block.Valid := by
        apply rigidBlock_valid_of_payload block
        · exact targetPayloadNodup
        · simpa only [block, fullyRigidBlock_marker] using targetMarkerAbsent
        · simpa [block, fullyRigidBlock, sortedShape] using restPositive
        · simpa [block, fullyRigidBlock, sortedShape,
            RigidBlock.heads] using tailHeadsStrict
        · cases restShape : rest with
          | nil =>
              simp [block, fullyRigidBlock, sortedShape, restShape,
                rigidExponent, capThree]
              split <;> omega
          | cons second later =>
              cases later with
              | nil =>
                  simp [block, fullyRigidBlock, sortedShape, restShape,
                    rigidExponent, capTwoPositive]
                  split <;> omega
              | cons third tail =>
                  simp [block, fullyRigidBlock, sortedShape, restShape,
                    rigidExponent]
        · cases restShape : rest with
          | nil =>
              have emptyPositive : 1 <= emptySegmentCount gaps := by
                rw [sortedShape, restShape] at lengthEquation
                simp at lengthEquation
                omega
              simp [block, fullyRigidBlock, sortedShape, restShape,
                rigidExponent, capThree]
              split <;> omega
          | cons second later =>
              cases later with
              | nil =>
                  simp [block, fullyRigidBlock, sortedShape, restShape,
                    rigidExponent, capTwoPositive]
                  split <;> omega
              | cons third tail =>
                  simp [block, fullyRigidBlock, sortedShape, restShape,
                    rigidExponent]
        · intro rankOne
          have restEmpty : rest = [] := by
            simp [block, fullyRigidBlock, sortedShape,
              RigidBlock.rank] at rankOne
            exact rankOne
          have emptyPositive : 1 <= emptySegmentCount gaps := by
            rw [sortedShape, restEmpty] at lengthEquation
            simp at lengthEquation
            omega
          simp [block, fullyRigidBlock, sortedShape, restEmpty,
            rigidExponent, capThree]
          split <;> omega
        · intro rankTwo
          have restLength : rest.length = 1 := by
            simp [block, fullyRigidBlock, sortedShape,
              RigidBlock.rank] at rankTwo
            omega
          cases restShape : rest with
          | nil => simp [restShape] at restLength
          | cons second later =>
              cases laterShape : later with
              | nil =>
                  simp [block, fullyRigidBlock, sortedShape, restShape,
                    laterShape, rigidExponent, capTwoPositive]
                  split <;> omega
              | cons third tail =>
                  simp [restShape, laterShape] at restLength
        · intro rankThree
          have restLength : 2 <= rest.length := by
            simpa [block, fullyRigidBlock, sortedShape,
              RigidBlock.rank] using rankThree
          cases restShape : rest with
          | nil => simp [restShape] at restLength
          | cons second later =>
              cases laterShape : later with
              | nil => simp [restShape, laterShape] at restLength
              | cons third tail =>
                  simp [block, fullyRigidBlock, sortedShape,
                    restShape, laterShape, rigidExponent]
      refine ⟨?_, ?_⟩
      · exact
          { toValid := valid
            ri6 := by
              intro _
              simpa [block, fullyRigidBlock, sortedShape,
                RigidBlock.heads] using allHeadsStrict }
      · intro firstEmpty
        have contradiction : first = [] := by
          simpa [block, fullyRigidBlock, sortedShape] using firstEmpty
        exact False.elim (firstNonempty contradiction)

/-- Exact later-block derivation.  The preceding repeated block remains an
explicit `guard H guard`; no unguarded segment permutation is used. -/
theorem listDerivesFullyRigidBlockAfterGuard
    (before after : List Nat) (guard marker : Nat)
    (guardMiddle : List Nat) (gaps : List (List Nat))
    (gapsNonempty : gaps ≠ []) :
    ListDerives
      (before ++ [guard] ++ guardMiddle ++ [guard] ++
        renderTerminatedBlocks marker gaps ++ after)
      (before ++ [guard] ++ guardMiddle ++ [guard] ++
        renderRigidBlock (fullyRigidBlock marker gaps) ++ after) := by
  have permuted := listDerivesPermuteTerminatedBlocksAfterGuard20_6c
    before after guard marker guardMiddle gapsNonempty
      (segments_perm_compact gaps)
  have compactRender :
      renderTerminatedBlocks marker (compactSegments gaps) =
        renderTerminatedBlocks marker
            (sortedOccupiedSegments gaps) ++
          List.replicate (emptySegmentCount gaps) marker := by
    simp [compactSegments, renderTerminatedBlocks_append,
      renderTerminatedBlocks_replicate_empty]
  cases sortedShape : sortedOccupiedSegments gaps with
  | nil =>
      have compactLength := (segments_perm_compact gaps).length_eq
      have emptyPositive : 1 <= emptySegmentCount gaps := by
        have gapsPositive : 0 < gaps.length := List.length_pos_iff.mpr gapsNonempty
        have lengthEquation : gaps.length = emptySegmentCount gaps := by
          simpa [compactSegments, sortedShape] using compactLength
        omega
      have cappedPositive :
          1 <= capThree (emptySegmentCount gaps) := by
        unfold capThree
        split <;> omega
      have cappedShape :
          List.replicate (capThree (emptySegmentCount gaps)) marker =
            [marker] ++
              List.replicate
                (capThree (emptySegmentCount gaps) - 1) marker := by
        cases capped : capThree (emptySegmentCount gaps) with
        | zero => omega
        | succ count => simp [capped, List.replicate_succ]
      have capped := listDerivesCapRunThree
        (before ++ [guard] ++ guardMiddle ++ [guard]) after marker
          (emptySegmentCount gaps)
      have permutedContext :
          ListDerives
            (before ++ [guard] ++ guardMiddle ++ [guard] ++
              renderTerminatedBlocks marker gaps ++ after)
            (before ++ [guard] ++ guardMiddle ++ [guard] ++
              List.replicate (emptySegmentCount gaps) marker ++ after) := by
        simpa [compactRender, sortedShape,
          renderTerminatedBlocks, List.append_assoc] using permuted
      have cappedContext :
          ListDerives
            (before ++ [guard] ++ guardMiddle ++ [guard] ++
              List.replicate (emptySegmentCount gaps) marker ++ after)
            (before ++ [guard] ++ guardMiddle ++ [guard] ++
              renderRigidBlock (fullyRigidBlock marker gaps) ++ after) := by
        simpa [fullyRigidBlock, sortedShape, renderRigidBlock,
          cappedShape, List.append_assoc] using capped
      exact permutedContext.trans cappedContext
  | cons first rest =>
      have capped := listDerivesCapRigidTail
        (before ++ [guard] ++ guardMiddle ++ [guard] ++ first)
        after marker rest (emptySegmentCount gaps)
      have permutedContext :
          ListDerives
            (before ++ [guard] ++ guardMiddle ++ [guard] ++
              renderTerminatedBlocks marker gaps ++ after)
            (before ++ [guard] ++ guardMiddle ++ [guard] ++ first ++ [marker] ++
              renderTerminatedBlocks marker rest ++
              List.replicate (emptySegmentCount gaps) marker ++ after) := by
        simpa [compactRender, sortedShape, renderTerminatedBlocks,
          List.append_assoc] using permuted
      have cappedContext :
          ListDerives
            (before ++ [guard] ++ guardMiddle ++ [guard] ++ first ++ [marker] ++
              renderTerminatedBlocks marker rest ++
              List.replicate (emptySegmentCount gaps) marker ++ after)
            (before ++ [guard] ++ guardMiddle ++ [guard] ++
              renderRigidBlock (fullyRigidBlock marker gaps) ++ after) := by
        simpa [fullyRigidBlock, sortedShape, renderRigidBlock,
          renderRigidTail_eq_renderTerminatedBlocks,
          List.append_assoc] using capped
      exact permutedContext.trans cappedContext

/-! ## Rigidifying the complete gathered block sequence -/

/-- First gathered class with its literal first segment frozen. -/
def firstRigidBlockOfGroup (group : MarkedGroup) : RigidBlock :=
  match group.factors with
  | [] => rigidBlockOfFirst group.marker [] []
  | factor :: rest =>
      rigidBlockOfFirst group.marker factor.gap
        (rest.map MarkedFactor.gap)

/-- Every later gathered class receives the fully rigid representative. -/
def laterRigidBlockOfGroup (group : MarkedGroup) : RigidBlock :=
  fullyRigidBlock group.marker (markedGroupGaps group)

@[simp] theorem firstRigidBlockOfGroup_marker (group : MarkedGroup) :
    (firstRigidBlockOfGroup group).marker = group.marker := by
  unfold firstRigidBlockOfGroup
  split <;> rfl

@[simp] theorem laterRigidBlockOfGroup_marker (group : MarkedGroup) :
    (laterRigidBlockOfGroup group).marker = group.marker := by
  simp [laterRigidBlockOfGroup]

/-- The unsorted block sequence.  Sorting later blocks is a separate exact
(20.6f) stage. -/
def rigidBlocksOfGroups : List MarkedGroup -> List RigidBlock
  | [] => []
  | first :: later =>
      firstRigidBlockOfGroup first ::
        later.map laterRigidBlockOfGroup

/-- Simple payload retained by a rigid block. -/
def rigidBlockPayload (block : RigidBlock) : List Nat :=
  block.first ++ block.rest.flatten

/-- Provenance retained across capping: marker and simple payload only. -/
structure RigidBlock.FromGroup
    (block : RigidBlock) (group : MarkedGroup) : Prop where
  marker_eq : block.marker = group.marker
  payload_perm : (markedGroupGaps group).flatten.Perm
    (rigidBlockPayload block)

theorem firstRigidBlockOfGroup_fromGroup
    (group : MarkedGroup) :
    (firstRigidBlockOfGroup group).FromGroup group := by
  cases factorsShape : group.factors with
  | nil =>
      refine
        { marker_eq := firstRigidBlockOfGroup_marker group
          payload_perm := ?_ }
      simp [firstRigidBlockOfGroup, factorsShape,
        markedGroupGaps, rigidBlockPayload, rigidBlockOfFirst,
        sortedOccupiedSegments, occupiedSegments]
  | cons factor rest =>
      refine
        { marker_eq := by
            simp [firstRigidBlockOfGroup, factorsShape,
              rigidBlockOfFirst]
          payload_perm := ?_ }
      simpa [firstRigidBlockOfGroup, factorsShape,
        markedGroupGaps, rigidBlockPayload] using
          rigidBlockOfFirst_payload_perm group.marker factor.gap
            (rest.map MarkedFactor.gap)

theorem laterRigidBlockOfGroup_fromGroup
    (group : MarkedGroup) :
    (laterRigidBlockOfGroup group).FromGroup group := by
  exact
    { marker_eq := by
        exact laterRigidBlockOfGroup_marker group
      payload_perm := by
        simpa [laterRigidBlockOfGroup, rigidBlockPayload] using
          fullyRigidBlock_payload_perm group.marker
            (markedGroupGaps group) }

private theorem factor_mem_source_of_group_member
    {whole : List Nat} {source : List MarkedFactor}
    {suffix : List Nat} {groups : List MarkedGroup}
    (decomposition : MarkedDecomposition whole source suffix)
    (permutation : source.Perm (flattenMarkedGroups groups))
    {group : MarkedGroup} (groupMember : group ∈ groups)
    {factor : MarkedFactor} (factorMember : factor ∈ group.factors) :
    factor ∈ source := by
  have inFlatten := factor_mem_flattenMarkedGroups
    groupMember factorMember
  exact permutation.mem_iff.mpr inFlatten

theorem MarkedGroups.Valid.group_marker_nonSimple
    {whole : List Nat} {source : List MarkedFactor}
    {suffix : List Nat} {groups : List MarkedGroup}
    (valid : MarkedGroups.Valid groups)
    (decomposition : MarkedDecomposition whole source suffix)
    (permutation : source.Perm (flattenMarkedGroups groups))
    {group : MarkedGroup} (member : group ∈ groups) :
    NonSimple whole group.marker := by
  obtain ⟨factor, factorMember⟩ :=
    List.exists_mem_of_ne_nil group.factors
      (valid.factors_nonempty group member)
  have inSource := factor_mem_source_of_group_member decomposition
    permutation member factorMember
  have multiple := decomposition.marker_nonSimple factor inSource
  have markerEq := valid.factors_marker group member factor factorMember
  simpa [markerEq] using multiple

theorem MarkedGroups.Valid.group_marker_not_mem_simpleBank
    {whole : List Nat} {source : List MarkedFactor}
    {suffix : List Nat} {groups : List MarkedGroup}
    (valid : MarkedGroups.Valid groups)
    (decomposition : MarkedDecomposition whole source suffix)
    (permutation : source.Perm (flattenMarkedGroups groups))
    {group : MarkedGroup} (member : group ∈ groups) :
    group.marker ∉
      markedSimpleBank (flattenMarkedGroups groups) suffix := by
  have multiple := valid.group_marker_nonSimple
    decomposition permutation member
  intro bankMember
  simp only [markedSimpleBank, List.mem_append,
    List.mem_flatten] at bankMember
  rcases bankMember with ⟨gap, gapMember, markerMember⟩ | inSuffix
  · obtain ⟨factor, factorMember, gapEq⟩ :=
      List.mem_map.mp gapMember
    have inSource : factor ∈ source := by
      apply permutation.mem_iff.mpr
      exact factorMember
    have simple := decomposition.gap_simple factor inSource
      group.marker (by simpa [gapEq] using markerMember)
    exact simple.not_nonSimple multiple
  · exact
      (decomposition.suffix_simple group.marker inSuffix).not_nonSimple
        multiple

theorem MarkedGroups.Valid.group_marker_not_mem_gaps
    {whole : List Nat} {source : List MarkedFactor}
    {suffix : List Nat} {groups : List MarkedGroup}
    (valid : MarkedGroups.Valid groups)
    (decomposition : MarkedDecomposition whole source suffix)
    (permutation : source.Perm (flattenMarkedGroups groups))
    {group : MarkedGroup} (member : group ∈ groups) :
    group.marker ∉ (markedGroupGaps group).flatten := by
  intro markerMember
  apply valid.group_marker_not_mem_simpleBank
    decomposition permutation member
  apply List.mem_append_left suffix
  rw [List.mem_flatten]
  obtain ⟨gap, gapMember, inGap⟩ :=
    (List.mem_flatten.mp markerMember)
  refine ⟨gap, ?_, inGap⟩
  obtain ⟨factor, factorMember, gapEq⟩ :=
    List.mem_map.mp gapMember
  exact List.mem_map.mpr
    ⟨factor, factor_mem_flattenMarkedGroups member factorMember, gapEq⟩

theorem MarkedGroups.Valid.firstBlock_valid
    {whole : List Nat} {source : List MarkedFactor}
    {suffix : List Nat} {groups : List MarkedGroup}
    (valid : MarkedGroups.Valid groups)
    (decomposition : MarkedDecomposition whole source suffix)
    (permutation : source.Perm (flattenMarkedGroups groups))
    (repeated : MarkersRepeated (flattenMarkedGroups groups))
    (bankNodup :
      (markedSimpleBank (flattenMarkedGroups groups) suffix).Nodup)
    {group : MarkedGroup} (member : group ∈ groups) :
    (firstRigidBlockOfGroup group).Valid := by
  have twoFactors := valid.group_length_at_least_two repeated member
  have groupPayloadNodup := valid.group_gaps_nodup
    member bankNodup
  have markerAbsent := valid.group_marker_not_mem_gaps
    decomposition permutation member
  cases factorsShape : group.factors with
  | nil =>
      exact False.elim
        ((valid.factors_nonempty group member) factorsShape)
  | cons factor rest =>
      have factorCount : 2 <= rest.length + 1 := by
        simpa [factorsShape] using twoFactors
      have payloadShape :
          (markedGroupGaps group).flatten =
            factor.gap ++ (rest.map MarkedFactor.gap).flatten := by
        simp [markedGroupGaps, factorsShape]
      simp only [firstRigidBlockOfGroup, factorsShape]
      apply rigidBlockOfFirst_valid group.marker factor.gap
        (rest.map MarkedFactor.gap)
      · simpa only [List.length_map] using factorCount
      · simpa only [markedGroupGaps, factorsShape, List.map_cons,
          List.flatten_cons] using groupPayloadNodup
      · simpa only [markedGroupGaps, factorsShape, List.map_cons,
          List.flatten_cons] using markerAbsent

theorem MarkedGroups.Valid.laterBlock_fullyRigid
    {whole : List Nat} {source : List MarkedFactor}
    {suffix : List Nat} {groups : List MarkedGroup}
    (valid : MarkedGroups.Valid groups)
    (decomposition : MarkedDecomposition whole source suffix)
    (permutation : source.Perm (flattenMarkedGroups groups))
    (repeated : MarkersRepeated (flattenMarkedGroups groups))
    (bankNodup :
      (markedSimpleBank (flattenMarkedGroups groups) suffix).Nodup)
    {group : MarkedGroup} (member : group ∈ groups) :
    (laterRigidBlockOfGroup group).FullyRigid ∧
      (laterRigidBlockOfGroup group).LeftNormalized := by
  have twoFactors := valid.group_length_at_least_two repeated member
  have groupPayloadNodup := valid.group_gaps_nodup member bankNodup
  have markerAbsent := valid.group_marker_not_mem_gaps
    decomposition permutation member
  simpa [laterRigidBlockOfGroup] using
    fullyRigidBlock_fullyRigid group.marker (markedGroupGaps group)
      (by simpa [markedGroupGaps] using twoFactors)
      groupPayloadNodup markerAbsent

private theorem renderMarkedGroups
    (groups : List MarkedGroup) :
    renderMarkedFactors (flattenMarkedGroups groups) =
      (groups.map fun group =>
        renderMarkedFactors group.factors).flatten := by
  induction groups with
  | nil => rfl
  | cons group later ih =>
      simp [flattenMarkedGroups, renderMarkedFactors_append, ih]

private def renderLaterRigidBlocks
    (groups : List MarkedGroup) : List Nat :=
  (groups.map fun group =>
    renderRigidBlock (laterRigidBlockOfGroup group)).flatten

/-- Recursively rigidify all later groups.  Each recursive call uses the
immediately preceding valid block as the repeated guard. -/
theorem listDerivesRigidifyLaterGroups
    {whole : List Nat} {source : List MarkedFactor}
    {globalSuffix : List Nat} {allGroups : List MarkedGroup}
    (allValid : MarkedGroups.Valid allGroups)
    (decomposition : MarkedDecomposition whole source globalSuffix)
    (groupPermutation : source.Perm
      (flattenMarkedGroups allGroups))
    (repeated : MarkersRepeated (flattenMarkedGroups allGroups))
    (bankNodup :
      (markedSimpleBank
        (flattenMarkedGroups allGroups) globalSuffix).Nodup)
    (before suffix : List Nat) (guardBlock : RigidBlock)
    (guardValid : guardBlock.Valid) :
    ∀ groups : List MarkedGroup,
      (∀ group ∈ groups, group ∈ allGroups) ->
      ListDerives
        (before ++ renderRigidBlock guardBlock ++
          renderMarkedFactors (flattenMarkedGroups groups) ++ suffix)
        (before ++ renderRigidBlock guardBlock ++
          renderLaterRigidBlocks groups ++ suffix)
  | [], _ => by
      simpa [renderLaterRigidBlocks] using
        (S5_107.ListDerives.refl (basis := basis)
          (before ++ renderRigidBlock guardBlock ++ suffix))
  | group :: later, subset => by
      have groupMember : group ∈ allGroups := subset group (by simp)
      have laterSubset : ∀ selected ∈ later,
          selected ∈ allGroups := by
        intro selected member
        exact subset selected (by simp [member])
      have factorsNonempty := allValid.factors_nonempty group groupMember
      have groupRender := allValid.render_group groupMember
      have laterBlockFacts := allValid.laterBlock_fullyRigid
        decomposition groupPermutation repeated bankNodup groupMember
      let nextBlock := laterRigidBlockOfGroup group
      obtain ⟨guardBefore, guardMiddle, guardShape⟩ :=
        guardValid.exists_terminalRepeatedSplit
      have firstStep := listDerivesFullyRigidBlockAfterGuard
        (before ++ guardBefore)
        (renderMarkedFactors (flattenMarkedGroups later) ++ suffix)
        guardBlock.marker group.marker guardMiddle
        (markedGroupGaps group)
        (by simpa [markedGroupGaps] using factorsNonempty)
      have firstDerivation :
          ListDerives
            (before ++ renderRigidBlock guardBlock ++
              renderMarkedFactors
                (flattenMarkedGroups (group :: later)) ++ suffix)
            (before ++ renderRigidBlock guardBlock ++
              renderRigidBlock nextBlock ++
                renderMarkedFactors
                  (flattenMarkedGroups later) ++ suffix) := by
        simpa [nextBlock, guardShape, groupRender,
          renderMarkedFactors_append, List.append_assoc] using firstStep
      have recursive := listDerivesRigidifyLaterGroups
        allValid decomposition groupPermutation repeated bankNodup
        (before ++ renderRigidBlock guardBlock) suffix nextBlock
          laterBlockFacts.1.toValid later laterSubset
      exact firstDerivation.trans <| by
        simpa [renderLaterRigidBlocks, nextBlock,
          List.append_assoc] using recursive

/-- Rigidification of the complete nonempty group sequence, before the
later-block (20.6f) sort. -/
theorem listDerivesRigidBlocksOfGroups
    {whole : List Nat} {source : List MarkedFactor}
    {suffix : List Nat} {groups : List MarkedGroup}
    (valid : MarkedGroups.Valid groups)
    (decomposition : MarkedDecomposition whole source suffix)
    (groupPermutation : source.Perm (flattenMarkedGroups groups))
    (groupsNonempty : groups ≠ []) :
    ListDerives
      (renderMarkedFactors (flattenMarkedGroups groups) ++ suffix)
      (((rigidBlocksOfGroups groups).map renderRigidBlock).flatten ++
        suffix) := by
  have repeated := decomposition.markersRepeated.of_perm groupPermutation
  have bankNodup := markedSimpleBank_nodup_of_perm
    decomposition groupPermutation
  cases groupsShape : groups with
  | nil => exact False.elim (groupsNonempty groupsShape)
  | cons first later =>
      have firstMember : first ∈ groups := by simp [groupsShape]
      have firstValid := valid.firstBlock_valid decomposition
        groupPermutation repeated bankNodup firstMember
      have firstRender := valid.render_group firstMember
      cases factorsShape : first.factors with
      | nil =>
          exact False.elim
            ((valid.factors_nonempty first firstMember) factorsShape)
      | cons factor factorsTail =>
          have firstStep := listDerivesRigidBlockOfFirst []
            (renderMarkedFactors (flattenMarkedGroups later) ++ suffix)
            first.marker factor.gap
              (factorsTail.map MarkedFactor.gap)
          have allRender :
              renderMarkedFactors (flattenMarkedGroups groups) =
                (factor.gap ++ [first.marker] ++
                  renderTerminatedBlocks first.marker
                    (factorsTail.map MarkedFactor.gap)) ++
                    renderMarkedFactors (flattenMarkedGroups later) := by
            rw [groupsShape, flattenMarkedGroups_cons,
              renderMarkedFactors_append, firstRender]
            simp only [markedGroupGaps, factorsShape, List.map_cons,
              renderTerminatedBlocks]
          have firstDerivation :
              ListDerives
                (renderMarkedFactors
                  (flattenMarkedGroups groups) ++ suffix)
                (renderRigidBlock (firstRigidBlockOfGroup first) ++
                  renderMarkedFactors
                    (flattenMarkedGroups later) ++ suffix) := by
            rw [allRender]
            simpa only [firstRigidBlockOfGroup, factorsShape,
              List.nil_append, List.append_assoc] using firstStep
          have laterDerivation := listDerivesRigidifyLaterGroups
            valid decomposition groupPermutation repeated bankNodup
            [] suffix (firstRigidBlockOfGroup first) firstValid later
              (by
                intro group member
                rw [groupsShape]
                exact List.Mem.tail first member)
          have composed := firstDerivation.trans laterDerivation
          simpa only [groupsShape, rigidBlocksOfGroups,
            renderLaterRigidBlocks, List.map_cons, List.map_map,
            List.flatten_cons, Function.comp_def, List.nil_append,
            List.append_assoc] using composed

/-! ## Sorting later rigid blocks by (20.6f) (Lemma 20.11) -/

/-- Executable inversion measure for the later-marker order. -/
def rigidBlockInversionDebt : List RigidBlock -> Nat
  | [] => 0
  | block :: later =>
      (later.filter fun candidate =>
        decide (candidate.marker < block.marker)).length +
          rigidBlockInversionDebt later

def rigidBlockMarkerLe (left right : RigidBlock) : Bool :=
  decide (left.marker <= right.marker)

def sortedLaterRigidBlocks (blocks : List RigidBlock) : List RigidBlock :=
  blocks.mergeSort rigidBlockMarkerLe

private theorem rigidBlockMarkerLe_transitive :
    ∀ left middle right : RigidBlock,
      rigidBlockMarkerLe left middle = true ->
      rigidBlockMarkerLe middle right = true ->
      rigidBlockMarkerLe left right = true := by
  intro left middle right first second
  simp only [rigidBlockMarkerLe, decide_eq_true_eq] at first second ⊢
  exact Nat.le_trans first second

private theorem rigidBlockMarkerLe_total :
    ∀ left right : RigidBlock,
      (rigidBlockMarkerLe left right ||
        rigidBlockMarkerLe right left) = true := by
  intro left right
  rcases Nat.le_total left.marker right.marker with order | order
  · simp [rigidBlockMarkerLe, order]
  · simp [rigidBlockMarkerLe, order]

theorem sortedLaterRigidBlocks_pairwise_le
    (blocks : List RigidBlock) :
    (sortedLaterRigidBlocks blocks).Pairwise
      (fun left right => left.marker <= right.marker) := by
  have sorted := List.pairwise_mergeSort
    rigidBlockMarkerLe_transitive rigidBlockMarkerLe_total blocks
  simpa [sortedLaterRigidBlocks, rigidBlockMarkerLe] using
    (sorted.imp fun relation => of_decide_eq_true relation)

private theorem pairwise_marker_lt_of_le_of_ne :
    ∀ blocks : List RigidBlock,
      blocks.Pairwise
          (fun left right => left.marker <= right.marker) ->
      blocks.Pairwise
          (fun left right => left.marker ≠ right.marker) ->
      blocks.Pairwise
          (fun left right => left.marker < right.marker)
  | [], _, _ => by simp
  | first :: later, weak, distinct => by
      have weakParts := List.pairwise_cons.mp weak
      have distinctParts := List.pairwise_cons.mp distinct
      refine List.pairwise_cons.mpr ⟨?_,
        pairwise_marker_lt_of_le_of_ne later
          weakParts.2 distinctParts.2⟩
      intro second member
      exact Nat.lt_of_le_of_ne
        (weakParts.1 second member)
        (distinctParts.1 second member)

theorem sortedLaterRigidBlocks_pairwise_lt
    (blocks : List RigidBlock)
    (markersNodup : (blocks.map fun block => block.marker).Nodup) :
    (sortedLaterRigidBlocks blocks).Pairwise
      (fun left right => left.marker < right.marker) := by
  have permutation : blocks.Perm (sortedLaterRigidBlocks blocks) :=
    (List.mergeSort_perm blocks rigidBlockMarkerLe).symm
  have sortedMarkersNodup :
      ((sortedLaterRigidBlocks blocks).map
        fun block => block.marker).Nodup :=
    (permutation.map fun block => block.marker).nodup_iff.mp markersNodup
  have distinct : (sortedLaterRigidBlocks blocks).Pairwise
      (fun left right => left.marker ≠ right.marker) :=
    List.pairwise_map.mp sortedMarkersNodup
  exact pairwise_marker_lt_of_le_of_ne
    (sortedLaterRigidBlocks blocks)
      (sortedLaterRigidBlocks_pairwise_le blocks) distinct

theorem rigidBlockInversionDebt_eq_zero_of_pairwise_le :
    ∀ blocks : List RigidBlock,
      blocks.Pairwise
          (fun left right => left.marker <= right.marker) ->
      rigidBlockInversionDebt blocks = 0
  | [], _ => rfl
  | first :: later, ordered => by
      have parts := List.pairwise_cons.mp ordered
      have noSmaller :
          (later.filter fun candidate =>
            decide (candidate.marker < first.marker)) = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro candidate filteredMember
        have pieces := List.mem_filter.mp filteredMember
        have smaller : candidate.marker < first.marker :=
          of_decide_eq_true pieces.2
        have weak := parts.1 candidate pieces.1
        omega
      simp [rigidBlockInversionDebt, noSmaller,
        rigidBlockInversionDebt_eq_zero_of_pairwise_le later parts.2]

theorem sortedLaterRigidBlocks_inversionDebt
    (blocks : List RigidBlock) :
    rigidBlockInversionDebt (sortedLaterRigidBlocks blocks) = 0 :=
  rigidBlockInversionDebt_eq_zero_of_pairwise_le _
    (sortedLaterRigidBlocks_pairwise_le blocks)

/-- One adjacent later-block swap, with all three repeated anchors exposed.
This is exactly (20.6f), not an unguarded block commutation. -/
theorem listDerivesSwapAdjacentRigidBlocks20_6f
    (before after : List Nat)
    (guard left right : RigidBlock)
    (guardValid : guard.Valid)
    (leftValid : left.Valid) (rightValid : right.Valid) :
    ListDerives
      (before ++ renderRigidBlock guard ++
        renderRigidBlock left ++ renderRigidBlock right ++ after)
      (before ++ renderRigidBlock guard ++
        renderRigidBlock right ++ renderRigidBlock left ++ after) := by
  obtain ⟨guardBefore, guardMiddle, guardShape⟩ :=
    guardValid.exists_terminalRepeatedSplit
  obtain ⟨leftBefore, leftMiddle, leftShape⟩ :=
    leftValid.exists_terminalRepeatedSplit
  obtain ⟨rightBefore, rightMiddle, rightShape⟩ :=
    rightValid.exists_terminalRepeatedSplit
  have swapped := listDerivesSwapRepeatedBlocks20_6f
    (before ++ guardBefore) after
    guard.marker left.marker right.marker guardMiddle
    leftBefore leftMiddle rightBefore rightMiddle
  simpa [guardShape, leftShape, rightShape,
    List.append_assoc] using swapped

private theorem listDerivesPermuteRigidBlocksAfterGuard20_6f
    {source target : List RigidBlock}
    (permutation : source.Perm target) :
    ∀ (before after : List Nat) (guard : RigidBlock),
      guard.Valid ->
      (∀ block ∈ source, block.Valid) ->
      ListDerives
        (before ++ renderRigidBlock guard ++
          (source.map renderRigidBlock).flatten ++ after)
        (before ++ renderRigidBlock guard ++
          (target.map renderRigidBlock).flatten ++ after) := by
  induction permutation with
  | nil =>
      intro before after guard guardValid sourceValid
      simpa using
        (S5_107.ListDerives.refl (basis := basis)
          (before ++ renderRigidBlock guard ++ after))
  | @cons head sourceTail targetTail permutation induction =>
      intro before after guard guardValid sourceValid
      have headValid := sourceValid head (by simp)
      have tailValid : ∀ (block : RigidBlock), block ∈ sourceTail → block.Valid := by
        intro block member
        exact sourceValid block (by simp [member])
      have recursive := induction
        (before ++ renderRigidBlock guard) after head headValid tailValid
      simpa [List.append_assoc] using recursive
  | swap left right later =>
      intro before after guard guardValid sourceValid
      have rightValid := sourceValid right (by simp)
      have leftValid := sourceValid left (by simp)
      have swapped := listDerivesSwapAdjacentRigidBlocks20_6f
        before ((later.map renderRigidBlock).flatten ++ after)
          guard left right guardValid leftValid rightValid
      simpa [List.append_assoc] using swapped.symm
  | @trans firstList middleList lastList firstPermutation secondPermutation firstIH secondIH =>
      intro before after guard guardValid sourceValid
      have first := firstIH before after guard guardValid sourceValid
      have middleValid : ∀ (block : RigidBlock), block ∈ middleList → block.Valid := by
        intro block member
        exact sourceValid block
          (firstPermutation.mem_iff.mpr member)
      exact first.trans
        (secondIH before after guard guardValid middleValid)

/-- The later-marker sort is a chain of guarded (20.6f) swaps and has zero
inversion debt at its endpoint. -/
theorem listDerivesSortLaterRigidBlocks20_6f
    (before after : List Nat) (guard : RigidBlock)
    (guardValid : guard.Valid) (blocks : List RigidBlock)
    (blocksValid : ∀ block ∈ blocks, block.Valid) :
    ListDerives
      (before ++ renderRigidBlock guard ++
        (blocks.map renderRigidBlock).flatten ++ after)
      (before ++ renderRigidBlock guard ++
        ((sortedLaterRigidBlocks blocks).map
          renderRigidBlock).flatten ++ after) := by
  apply listDerivesPermuteRigidBlocksAfterGuard20_6f
    ((List.mergeSort_perm blocks rigidBlockMarkerLe).symm)
      before after guard guardValid blocksValid

/-! ## Support-exact disjointness of the canonical renderer -/

def markedGroupGapBank (groups : List MarkedGroup) : List Nat :=
  (groups.map fun group => (markedGroupGaps group).flatten).flatten

def markedGroupSupportBank : List MarkedGroup -> List Nat
  | [] => []
  | group :: later =>
      group.marker :: (markedGroupGaps group).flatten ++
        markedGroupSupportBank later

def rigidBlockSupport (block : RigidBlock) : List Nat :=
  block.marker :: rigidBlockPayload block

def rigidBlockSupportBank (blocks : List RigidBlock) : List Nat :=
  (blocks.map rigidBlockSupport).flatten

private theorem markedGroupGapBank_eq
    (groups : List MarkedGroup) :
    markedGroupGapBank groups =
      ((flattenMarkedGroups groups).map MarkedFactor.gap).flatten := by
  induction groups with
  | nil => rfl
  | cons group later ih =>
      simp only [markedGroupGapBank, markedGroupGaps] at ih
      simp only [markedGroupGapBank, markedGroupGaps,
        flattenMarkedGroups_cons, List.map_cons, List.map_append,
        List.flatten_cons, List.flatten_append, ih]

private theorem markedGroupSupportBank_perm
    (groups : List MarkedGroup) :
    (markedGroupSupportBank groups).Perm
      (markedGroupMarkers groups ++ markedGroupGapBank groups) := by
  induction groups with
  | nil => exact List.Perm.refl []
  | cons group later ih =>
      have first := ih.append_left
        (group.marker :: (markedGroupGaps group).flatten)
      have swapped :
          ((markedGroupGaps group).flatten ++
              markedGroupMarkers later).Perm
            (markedGroupMarkers later ++
              (markedGroupGaps group).flatten) :=
        List.perm_append_comm
      have lifted := (swapped.append_right
        (markedGroupGapBank later)).append_left [group.marker]
      exact first.trans <| by
        simpa [markedGroupSupportBank, markedGroupMarkers,
          markedGroupGapBank, List.append_assoc] using lifted

theorem MarkedGroups.Valid.supportBank_nodup
    {whole : List Nat} {source : List MarkedFactor}
    {suffix : List Nat} {groups : List MarkedGroup}
    (valid : MarkedGroups.Valid groups)
    (decomposition : MarkedDecomposition whole source suffix)
    (permutation : source.Perm (flattenMarkedGroups groups))
    (simpleBankNodup :
      (markedSimpleBank (flattenMarkedGroups groups) suffix).Nodup) :
    (markedGroupSupportBank groups ++ suffix).Nodup := by
  have bankShape :
      markedGroupGapBank groups ++ suffix =
        markedSimpleBank (flattenMarkedGroups groups) suffix := by
    simp [markedSimpleBank, markedGroupGapBank_eq]
  have cross : ∀ marker ∈ markedGroupMarkers groups,
      ∀ letter ∈ markedGroupGapBank groups ++ suffix,
        marker ≠ letter := by
    intro marker markerMember letter letterMember equal
    obtain ⟨group, groupMember, groupMarker⟩ :=
      (marker_mem_markedGroupMarkers_iff marker groups).1 markerMember
    have absent := valid.group_marker_not_mem_simpleBank
      decomposition permutation groupMember
    apply absent
    simpa [groupMarker, bankShape, equal] using letterMember
  have separated :
      (markedGroupMarkers groups ++
        (markedGroupGapBank groups ++ suffix)).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨valid.markers_nodup, ?_, cross⟩
    simpa [bankShape] using simpleBankNodup
  have supportPermutation :=
    (markedGroupSupportBank_perm groups).append_right suffix
  apply supportPermutation.nodup_iff.mpr
  simpa only [List.append_assoc] using separated

private theorem rigidBlockFromGroup_support_perm
    {block : RigidBlock} {group : MarkedGroup}
    (provenance : block.FromGroup group) :
    (rigidBlockSupport block).Perm
      (group.marker :: (markedGroupGaps group).flatten) := by
  have payload := provenance.payload_perm.symm
  have withMarker := List.Perm.cons group.marker payload
  simpa [rigidBlockSupport, rigidBlockPayload,
    provenance.marker_eq] using withMarker

private theorem laterRigidSupportBank_perm
    (groups : List MarkedGroup) :
    (rigidBlockSupportBank
      (groups.map laterRigidBlockOfGroup)).Perm
        (markedGroupSupportBank groups) := by
  induction groups with
  | nil => exact List.Perm.refl []
  | cons group later ih =>
      have head := rigidBlockFromGroup_support_perm
        (laterRigidBlockOfGroup_fromGroup group)
      have combined := List.Perm.append head ih
      simpa [rigidBlockSupportBank, markedGroupSupportBank,
        List.append_assoc] using combined

theorem rigidBlocksOfGroups_supportBank_perm
    (groups : List MarkedGroup) :
    (rigidBlockSupportBank (rigidBlocksOfGroups groups)).Perm
      (markedGroupSupportBank groups) := by
  cases groups with
  | nil => exact List.Perm.refl []
  | cons first later =>
      have head := rigidBlockFromGroup_support_perm
        (firstRigidBlockOfGroup_fromGroup first)
      have tail := laterRigidSupportBank_perm later
      have combined := List.Perm.append head tail
      simpa [rigidBlocksOfGroups, rigidBlockSupportBank,
        markedGroupSupportBank, List.append_assoc] using combined

theorem MarkedGroups.Valid.rigidSupportBank_nodup
    {whole : List Nat} {source : List MarkedFactor}
    {suffix : List Nat} {groups : List MarkedGroup}
    (valid : MarkedGroups.Valid groups)
    (decomposition : MarkedDecomposition whole source suffix)
    (permutation : source.Perm (flattenMarkedGroups groups))
    (simpleBankNodup :
      (markedSimpleBank (flattenMarkedGroups groups) suffix).Nodup) :
    (rigidBlockSupportBank (rigidBlocksOfGroups groups) ++
      suffix).Nodup := by
  have sourceNodup := valid.supportBank_nodup
    decomposition permutation simpleBankNodup
  have supportPermutation :=
    (rigidBlocksOfGroups_supportBank_perm groups).append_right suffix
  exact supportPermutation.nodup_iff.mpr sourceNodup

theorem mem_renderRigidBlock_iff_mem_support
    (block : RigidBlock) (letter : Nat) :
    letter ∈ renderRigidBlock block ↔
      letter ∈ rigidBlockSupport block := by
  rw [mem_renderRigidBlock_iff]
  simp [rigidBlockSupport, rigidBlockPayload, List.mem_flatten,
    or_assoc, or_left_comm, or_comm]

private theorem canonicalDisjoint_of_supportBank_nodup :
    ∀ (blocks : List RigidBlock) (suffix : List Nat),
      (rigidBlockSupportBank blocks ++ suffix).Nodup ->
      (blocks.map renderRigidBlock).Pairwise ListsDisjoint ∧
        (∀ block ∈ blocks,
          ListsDisjoint (renderRigidBlock block) suffix)
  | [], suffix, _ => by simp
  | first :: later, suffix, bankNodup => by
      have expanded :
          (rigidBlockSupport first ++
            (rigidBlockSupportBank later ++ suffix)).Nodup := by
        simpa [rigidBlockSupportBank, List.append_assoc] using bankNodup
      have parts := List.nodup_append.mp expanded
      have recursive := canonicalDisjoint_of_supportBank_nodup
        later suffix parts.2.1
      have firstRelations : ∀ block ∈ later,
          ListsDisjoint (renderRigidBlock first)
            (renderRigidBlock block) := by
        intro block blockMember letter inFirst inBlock
        have inFirstSupport :=
          (mem_renderRigidBlock_iff_mem_support first letter).1 inFirst
        have inLaterBank :
            letter ∈ rigidBlockSupportBank later ++ suffix := by
          apply List.mem_append_left suffix
          apply List.mem_flatten_of_mem
            (List.mem_map.mpr
              ⟨block, blockMember, rfl⟩)
          exact (mem_renderRigidBlock_iff_mem_support block letter).1 inBlock
        exact parts.2.2 letter inFirstSupport letter inLaterBank rfl
      have firstSuffix :
          ListsDisjoint (renderRigidBlock first) suffix := by
        intro letter inFirst inSuffix
        have inFirstSupport :=
          (mem_renderRigidBlock_iff_mem_support first letter).1 inFirst
        have inLaterBank :
            letter ∈ rigidBlockSupportBank later ++ suffix :=
          List.mem_append_right _ inSuffix
        exact parts.2.2 letter inFirstSupport letter inLaterBank rfl
      refine ⟨?_, ?_⟩
      · exact List.pairwise_cons.mpr ⟨by
          intro rendered renderedMember
          obtain ⟨block, blockMember, renderEq⟩ :=
            List.mem_map.mp renderedMember
          subst rendered
          exact firstRelations block blockMember,
          recursive.1⟩
      · intro block member
        rcases List.mem_cons.mp member with rfl | inLater
        · exact firstSuffix
        · exact recursive.2 block inLater

private theorem suffix_simple_of_supportBank_nodup
    (form : CanonicalForm)
    (supportNodup :
      (rigidBlockSupportBank form.blocks ++ form.suffix).Nodup)
    (disjoint : CanonicalDisjoint form) :
    ∀ letter ∈ form.suffix,
      Simple (renderCanonical form) letter := by
  intro letter suffixMember
  have suffixNodup : form.suffix.Nodup := by
    have expanded := List.nodup_append.mp supportNodup
    exact expanded.2.1
  have absentBlocks :
      letter ∉ form.blockRenders.flatten := by
    intro flattenedMember
    rw [List.mem_flatten] at flattenedMember
    obtain ⟨rendered, renderMember, letterMember⟩ := flattenedMember
    obtain ⟨block, blockMember, renderEq⟩ :=
      List.mem_map.mp renderMember
    subst rendered
    exact
      (disjoint.2 block blockMember letter letterMember) suffixMember
  unfold Simple
  rw [renderCanonical, List.count_append,
    List.count_eq_zero.mpr absentBlocks, suffixNodup.count]
  simp [suffixMember]

/-! ## Complete normalization (Lemma 20.12) -/

private theorem groups_nonempty_of_factor_permutation
    {factors : List MarkedFactor} {groups : List MarkedGroup}
    (factorsNonempty : factors ≠ [])
    (permutation : factors.Perm (flattenMarkedGroups groups)) :
    groups ≠ [] := by
  intro groupsEmpty
  subst groups
  have factorsEmpty : factors = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro factor member
    have targetMember := permutation.mem_iff.mp member
    simp at targetMember
  exact factorsNonempty factorsEmpty

private theorem laterRigidMarkers_nodup
    {first : MarkedGroup} {later : List MarkedGroup}
    (valid : MarkedGroups.Valid (first :: later)) :
    ((later.map laterRigidBlockOfGroup).map
      fun block => block.marker).Nodup := by
  have tailMarkers := (List.nodup_cons.mp valid.markers_nodup).2
  simpa only [markedGroupMarkers, List.map_map, Function.comp_def,
    laterRigidBlockOfGroup_marker] using tailMarkers

/-- Canonicalize an already gathered nonempty group sequence. -/
theorem existsCanonicalReductionOfGroups
    {whole : List Nat} {source : List MarkedFactor}
    {suffix : List Nat} {groups : List MarkedGroup}
    (decomposition : MarkedDecomposition whole source suffix)
    (valid : MarkedGroups.Valid groups)
    (groupPermutation : source.Perm (flattenMarkedGroups groups))
    (groupsNonempty : groups ≠ []) :
    ∃ normal form,
      form.ReducedValid ∧
        normal = renderCanonical form ∧
        ListDerives
          (renderMarkedFactors (flattenMarkedGroups groups) ++ suffix)
          normal := by
  have repeated := decomposition.markersRepeated.of_perm groupPermutation
  have simpleBankNodup := markedSimpleBank_nodup_of_perm
    decomposition groupPermutation
  have unsortedSupportNodup := valid.rigidSupportBank_nodup
    decomposition groupPermutation simpleBankNodup
  cases groupsShape : groups with
  | nil => exact False.elim (groupsNonempty groupsShape)
  | cons first later =>
      let firstBlock := firstRigidBlockOfGroup first
      let laterBlocks := later.map laterRigidBlockOfGroup
      let sortedBlocks := sortedLaterRigidBlocks laterBlocks
      let form : CanonicalForm :=
        { first := firstBlock
          rest := sortedBlocks
          suffix := suffix }
      have firstMember : first ∈ groups := by simp [groupsShape]
      have firstValid : firstBlock.Valid := by
        simpa [firstBlock] using
          valid.firstBlock_valid decomposition groupPermutation
            repeated simpleBankNodup firstMember
      have laterMarkersNodup :
          (laterBlocks.map fun block => block.marker).Nodup := by
        simpa [groupsShape, laterBlocks] using
          laterRigidMarkers_nodup
            (by simpa [groupsShape] using valid)
      have laterPermutation : laterBlocks.Perm sortedBlocks := by
        exact (List.mergeSort_perm laterBlocks rigidBlockMarkerLe).symm
      have fullPermutation :
          (firstBlock :: laterBlocks).Perm
            (firstBlock :: sortedBlocks) :=
        List.Perm.cons firstBlock laterPermutation
      have supportPermutation :
          (rigidBlockSupportBank (firstBlock :: laterBlocks) ++ suffix).Perm
            (rigidBlockSupportBank (firstBlock :: sortedBlocks) ++ suffix) := by
        have mapped := fullPermutation.map rigidBlockSupport
        exact (flatten_perm_of_perm mapped).append_right suffix
      have unsortedSupportNodup' :
          (rigidBlockSupportBank (firstBlock :: laterBlocks) ++
            suffix).Nodup := by
        simpa [groupsShape, rigidBlocksOfGroups, firstBlock,
          laterBlocks] using unsortedSupportNodup
      have sortedSupportNodup :
          (rigidBlockSupportBank (firstBlock :: sortedBlocks) ++
            suffix).Nodup :=
        supportPermutation.nodup_iff.mp unsortedSupportNodup'
      have disjointParts := canonicalDisjoint_of_supportBank_nodup
        (firstBlock :: sortedBlocks) suffix sortedSupportNodup
      have canonicalDisjoint : CanonicalDisjoint form := by
        exact disjointParts
      have laterFacts : ∀ block ∈ sortedBlocks,
          block.FullyRigid ∧ block.LeftNormalized := by
        intro block sortedMember
        have unsortedMember : block ∈ laterBlocks :=
          laterPermutation.mem_iff.mpr sortedMember
        obtain ⟨group, groupMember, blockEq⟩ :=
          List.mem_map.mp unsortedMember
        subst block
        have inAll : group ∈ groups := by
          rw [groupsShape]
          exact List.Mem.tail first groupMember
        exact valid.laterBlock_fullyRigid decomposition
          groupPermutation repeated simpleBankNodup inAll
      have reducedValid : form.ReducedValid := by
        refine
          { toValid :=
              { conditionI := firstValid
                conditionII := ?_
                conditionIII := ?_
                conditionIV := ?_
                conditionV := canonicalDisjoint }
            laterLeftNormalized := ?_ }
        · intro block member
          exact (laterFacts block (by simpa [form] using member)).1
        · change (sortedBlocks.map fun block => block.marker).Pairwise
            (fun left right => left < right)
          exact List.pairwise_map.mpr
            (sortedLaterRigidBlocks_pairwise_lt laterBlocks laterMarkersNodup)
        · intro letter member
          apply suffix_simple_of_supportBank_nodup form
          · simpa [form, CanonicalForm.blocks] using sortedSupportNodup
          · exact canonicalDisjoint
          · simpa [form] using member
        · intro block member
          exact (laterFacts block (by simpa [form] using member)).2
      have rigidified := listDerivesRigidBlocksOfGroups
        valid decomposition groupPermutation groupsNonempty
      have laterBlocksValid : ∀ block ∈ laterBlocks,
          block.Valid := by
        intro block member
        have sortedMember : block ∈ sortedBlocks :=
          laterPermutation.mem_iff.mp member
        exact (laterFacts block sortedMember).1.toValid
      have sortedDerivation := listDerivesSortLaterRigidBlocks20_6f
        [] suffix firstBlock firstValid laterBlocks laterBlocksValid
      have sortStep :
          ListDerives
            (((rigidBlocksOfGroups groups).map
              renderRigidBlock).flatten ++ suffix)
            (renderCanonical form) := by
        simpa [groupsShape, rigidBlocksOfGroups, firstBlock,
          laterBlocks, sortedBlocks, form, renderCanonical,
          CanonicalForm.blockRenders, CanonicalForm.blocks,
          List.append_assoc] using sortedDerivation
      refine ⟨renderCanonical form, form, reducedValid, rfl, ?_⟩
      simpa only [groupsShape] using rigidified.trans sortStep

/-- Lemmas 20.10--20.12: every non-simple list has a deterministic
`ReducedValid` canonical representative, with exact renderer equality and a
direct derivation from the frozen 64-member basis. -/
theorem existsCanonicalReduction
    (whole : List Nat) {multiple : Nat}
    (nonSimple : NonSimple whole multiple) :
    ∃ normal form,
      form.ReducedValid ∧
        normal = renderCanonical form ∧
        ListDerives whole normal := by
  obtain ⟨factors, suffix, decomposition⟩ :=
    existsMarkedDecomposition whole
  obtain ⟨groups, valid, groupPermutation, groupedDerivation⟩ :=
    existsGroupedReduction decomposition nonSimple
  have factorsNonempty :=
    decomposition.factors_nonempty_of_nonSimple nonSimple
  have groupsNonempty := groups_nonempty_of_factor_permutation
    factorsNonempty groupPermutation
  obtain ⟨normal, form, reducedValid, renderEq,
      canonicalDerivation⟩ :=
    existsCanonicalReductionOfGroups decomposition valid
      groupPermutation groupsNonempty
  refine ⟨normal, form, reducedValid, renderEq, ?_⟩
  exact groupedDerivation.trans canonicalDerivation

/-- Word-level bridge for completeness assembly. -/
theorem existsCanonicalWordReduction
    (word : Word Nat) {multiple : Nat}
    (nonSimple : NonSimple word.toList multiple) :
    ∃ target : Word Nat, ∃ form : CanonicalForm,
      form.ReducedValid ∧
        target.toList = renderCanonical form ∧
        Derives basis word target := by
  obtain ⟨normal, form, reducedValid, renderEq, listDerivation⟩ :=
    existsCanonicalReduction word.toList nonSimple
  have normalNonempty : normal ≠ [] := by
    rw [renderEq]
    exact renderCanonical_nonempty form
  cases normalShape : normal with
  | nil => exact False.elim (normalNonempty normalShape)
  | cons targetHead targetTail =>
      let target := S5_107.listWordOfCons targetHead targetTail
      cases word with
      | mk sourceHead sourceTail =>
          have wordDerivation :
              Derives basis
                (S5_107.listWordOfCons sourceHead sourceTail) target := by
            apply S5_107.ListDerives.toWord
            simpa [normalShape, target] using listDerivation
          refine ⟨target, form, reducedValid, ?_, ?_⟩
          · simpa [target, S5_107.listWordOfCons,
              normalShape] using renderEq
          · simpa [target, S5_107.listWordOfCons] using wordDerivation

end SemigroupBasis.CoRoots.Order6LeeZhangProposition20_7E4
