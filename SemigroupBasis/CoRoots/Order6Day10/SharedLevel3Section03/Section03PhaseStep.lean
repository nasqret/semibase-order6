import SemigroupBasis.CoRoots.Order6Day10.SharedLevel3Section03.Section03MarkerMoves
import SemigroupBasis.CoRoots.Order6Day10.SharedLevel3Section03.Section03PhaseData

/-! Every transition of the protected-marker canonical scanner is an explicit
B13 derivation. The first head return is moved to the first doubled phase. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day10.SharedLevel3Section03.Section03PhaseStep

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.S5_107
open SemigroupBasis.CoRoots.S5_831
open SemigroupBasis.CoRoots.Order6Day10.SharedLevel3Section03.Section03Replay
open SemigroupBasis.CoRoots.Order6Day10.SharedLevel3Section03.Section03MarkerMoves
open SemigroupBasis.CoRoots.Order6Day10.SharedLevel3Section03.Section03PhaseData

abbrev basis := Section03Replay.basis

theorem getLastD_append_list (before after : List Nat) (fallback : Nat) (nonempty : after ≠ []) :
    (before ++ after).getLastD fallback = after.getLastD fallback := by
  cases after with
  | nil => exact (nonempty rfl).elim
  | cons head tail =>
      exact (getLastD_append_word before (Word.mk head tail) fallback).trans
        (getLastD_append_word [] (Word.mk head tail) fallback).symm

theorem final_wordOfPrefixFinal (before : List Nat) (last : Nat) :
    (wordOfPrefixFinal before last).final = last := by
  induction before with
  | nil => rfl
  | cons head tail ih =>
      simpa only [wordOfPrefixFinal_cons, Word.final_append] using ih

theorem markLast_last_double (before : List Phase) (phase : Phase) (doubled : phase.doubled = true) :
    markLastDoubled (before ++ [phase]) = before ++ [phase] := by
  rw [markLast_append_nonempty before [phase] (by simp)]
  cases phase with
  | mk label bit => simp_all [markLastDoubled]

/-- If the marker is in the final phase, its duplicate contracts by a
displayed return law. Otherwise only the ordinary final run changes. -/
theorem markMarkedLast (head : Nat) (phases : List Phase)
    (ok : StateOK head phases true) (fallback : Nat) :
    D (marked head phases ++ [(marked head phases).getLastD fallback])
      (marked head (markLastDoubled phases)) := by
  obtain ⟨before, phase, after, shape, none, bit⟩ := first_double_split (ok.markedPhase rfl)
  rw [shape] at ok ⊢
  cases after with
  | nil =>
      rw [markLast_last_double before phase bit]
      have markedEq := marked_first_double head before phase [] none bit
      have member : head ∈ phaseLabels before ++ [phase.label] := by
        simpa [phaseLabels] using ok.head_mem
      simpa [markedEq, renderPhases, List.append_assoc] using
        (duplicateRepeatedFinal (phaseLabels before ++ [phase.label]) head member).symm
  | cons next tail =>
      have nonempty : (next :: tail : List Phase) ≠ [] := by simp
      have markedEq := marked_first_double head before phase (next :: tail) none bit
      have lastShape : markLastDoubled (before ++ phase :: next :: tail) =
          before ++ phase :: markLastDoubled (next :: tail) := by
        simpa [List.append_assoc] using
          markLast_append_nonempty (before ++ [phase]) (next :: tail) nonempty
      have nextEq : marked head (markLastDoubled (before ++ phase :: next :: tail)) =
          phaseLabels before ++ [phase.label, head] ++ renderPhases (markLastDoubled (next :: tail)) := by
        rw [lastShape]
        exact marked_first_double head before phase (markLastDoubled (next :: tail)) none bit
      rw [markedEq, nextEq]
      rw [getLastD_append_list (phaseLabels before ++ [phase.label, head])
        (renderPhases (next :: tail)) fallback (renderPhases_ne_nil nonempty)]
      simpa only [List.append_assoc] using
        (markPlainLast fallback (next :: tail) nonempty).prepend (phaseLabels before ++ [phase.label, head])

/-- On its first return, the initial letter either creates the first double
phase, or relocates from the final phase to the previously first double. -/
theorem firstReturnStep (head : Nat) (phases : List Phase) (ok : StateOK head phases false) :
    D (renderPhases phases ++ [head]) (marked head (markLastDoubled phases)) := by
  by_cases present : HasDouble phases
  · obtain ⟨before, phase, after, shape, none, bit⟩ := first_double_split present
    rw [shape] at ok ⊢
    obtain ⟨remaining, headShape⟩ := ok.freshHead rfl
    cases before with
    | nil =>
        have same : phase = ⟨head, false⟩ := (List.cons.inj headShape).1
        simp [same] at bit
    | cons first before =>
        have same : first = ⟨head, false⟩ := (List.cons.inj headShape).1
        subst first
        let front := wordOfPrefixFinal (phaseLabels before) phase.label
        have frontList : front.toList = phaseLabels before ++ [phase.label] :=
          toList_wordOfPrefixFinal (phaseLabels before) phase.label
        have frontFinal : front.final = phase.label :=
          final_wordOfPrefixFinal (phaseLabels before) phase.label
        have plainEq : renderPhases ((⟨head, false⟩ :: before) ++ phase :: after) =
            head :: (front.toList ++ [phase.label] ++ renderPhases after) := by
          rw [plain_first_double _ phase after none bit, frontList]
          simp [phaseLabels, List.append_assoc]
        have markedEq : marked head ((⟨head, false⟩ :: before) ++ phase :: after) =
            head :: (front.toList ++ [head] ++ renderPhases after) := by
          rw [marked_first_double head _ phase after none bit, frontList]
          simp [phaseLabels, List.append_assoc]
        cases after with
        | nil =>
            rw [markLast_last_double (⟨head, false⟩ :: before) phase bit, plainEq, markedEq]
            simpa [renderPhases, frontFinal, List.append_assoc] using markerAtFinalDouble head front
        | cons next tail =>
            let back := profileWord next tail
            have backList : back.toList = renderPhases (next :: tail) := toList_profileWord next tail
            have backFinal : back.final = (renderPhases (next :: tail)).getLastD head := by
              have lastEq := getLastD_append_word [] back head
              rw [List.nil_append, backList] at lastEq
              exact lastEq.symm
            have move : D ((head :: (front.toList ++ [phase.label] ++ renderPhases (next :: tail))) ++ [head])
                ((head :: (front.toList ++ [head] ++ renderPhases (next :: tail))) ++
                  [(renderPhases (next :: tail)).getLastD head]) := by
              have step := (relocateMarker head front back).symm
              rw [frontFinal, backList, backFinal] at step
              simpa only [List.cons_append, List.append_assoc] using step
            have normalize : D
                ((head :: (front.toList ++ [head] ++ renderPhases (next :: tail))) ++
                  [(renderPhases (next :: tail)).getLastD head])
                (head :: (front.toList ++ [head] ++ renderPhases (markLastDoubled (next :: tail)))) := by
              simpa only [List.cons_append, List.append_assoc] using
                (markPlainLast head (next :: tail) (by simp)).prepend (head :: (front.toList ++ [head]))
            have lastShape : markLastDoubled ((⟨head, false⟩ :: before) ++ phase :: next :: tail) =
                (⟨head, false⟩ :: before) ++ phase :: markLastDoubled (next :: tail) := by
              simpa [List.append_assoc] using
                markLast_append_nonempty ((⟨head, false⟩ :: before) ++ [phase]) (next :: tail) (by simp)
            have nextEq : marked head (markLastDoubled ((⟨head, false⟩ :: before) ++ phase :: next :: tail)) =
                head :: (front.toList ++ [head] ++ renderPhases (markLastDoubled (next :: tail))) := by
              rw [lastShape, marked_first_double head _ phase _ none bit, frontList]
              simp [phaseLabels, List.append_assoc]
            rw [plainEq, nextEq]
            exact move.trans normalize
  · rw [plain_eq_labels_of_noDouble phases present,
      marked_markLast_of_noDouble head phases ok.ne_nil present]
    exact ListDerives.refl _

theorem oldAppendCurrentLast {head : Nat} {phases : List Phase} {repeated : Bool}
    (ok : StateOK head phases repeated) (letter : Nat) (old : letter ∈ phaseLabels phases)
    (allowed : repeated = true ∨ letter ≠ head) :
    D (renderState head phases repeated ++ [letter])
      (renderState head phases repeated ++ [(renderState head phases repeated).getLastD letter]) := by
  obtain ⟨tail, shape⟩ := renderState_shape ok
  have member := renderState_tail_contains ok old allowed
  rw [shape, List.tail_cons] at member
  have nonempty : tail ≠ [] := by intro empty; simp [empty] at member
  have finalEq : (renderState head phases repeated).getLastD letter = tail.getLastD letter := by
    rw [shape]
    exact getLastD_append_list [head] tail letter nonempty
  have first : D (renderState head phases repeated ++ [letter])
      (renderState head phases repeated ++ [tail.getLastD letter]) := by
    rw [shape]
    exact appendOldTail head letter tail member
  rw [← finalEq] at first
  exact first

theorem oldStateStep {head : Nat} {phases : List Phase} {repeated : Bool}
    (ok : StateOK head phases repeated) (letter : Nat) (old : letter ∈ phaseLabels phases)
    (allowed : repeated = true ∨ letter ≠ head) :
    D (renderState head phases repeated ++ [letter])
      (renderState head (markLastDoubled phases) (nextRepeated head repeated letter)) := by
  have first := oldAppendCurrentLast ok letter old allowed
  cases repeated with
  | false =>
      have notHead : letter ≠ head := by simpa using allowed
      simpa [renderState, nextRepeated, notHead] using first.trans (markPlainLast letter phases ok.ne_nil)
  | true =>
      simpa [renderState, nextRepeated] using first.trans (markMarkedLast head phases ok letter)

theorem freshStateStep {head : Nat} {phases : List Phase} {repeated : Bool}
    (ok : StateOK head phases repeated) (letter : Nat) (fresh : letter ∉ phaseLabels phases) :
    D (renderState head phases repeated ++ [letter])
      (renderState head (phaseStep phases letter) (nextRepeated head repeated letter)) := by
  have notHead : letter ≠ head := by
    intro equal
    exact fresh (by simpa only [equal] using ok.head_mem)
  cases repeated with
  | false =>
      simpa [renderState, phaseStep, fresh, nextRepeated, notHead, renderPhases, renderPhase] using
        (ListDerives.refl (basis := basis) (renderPhases phases ++ [letter]))
  | true =>
      have present := ok.markedPhase rfl
      simpa [renderState, phaseStep, fresh, nextRepeated, marked_append, present, renderPhases, renderPhase] using
        (ListDerives.refl (basis := basis) (marked head phases ++ [letter]))

/-- The complete unbounded single-letter transition of the canonical state. -/
theorem stateStep {head : Nat} {phases : List Phase} {repeated : Bool}
    (ok : StateOK head phases repeated) (letter : Nat) :
    D (renderState head phases repeated ++ [letter])
      (renderState head (phaseStep phases letter) (nextRepeated head repeated letter)) := by
  by_cases old : letter ∈ phaseLabels phases
  · cases repeated with
    | true =>
        simpa only [phaseStep, if_pos old] using oldStateStep ok letter old (Or.inl rfl)
    | false =>
        by_cases same : letter = head
        · subst letter
          simpa [renderState, phaseStep, old, nextRepeated] using firstReturnStep head phases ok
        · simpa only [phaseStep, if_pos old] using oldStateStep ok letter old (Or.inr same)
  · exact freshStateStep ok letter old

end SemigroupBasis.CoRoots.Order6Day10.SharedLevel3Section03.Section03PhaseStep
