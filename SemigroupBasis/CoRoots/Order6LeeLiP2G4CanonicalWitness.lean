import SemigroupBasis.CoRoots.Order6LeeLiP2G4MergeCollapse

/-!
# G4 concrete canonical witness (msg-0198)

EVIDENCE LABEL: source-staged draft, NOT compiled here.  Discharges the
six canonical-interface obligations of the corrected L1–L5 section
(msg-0063/0195) for a CONCRETE, closed-form canonical map.

THE KEY DESIGN FACT (from the reduction trace, cross-checked against the
replayed closure data of msg-0054): the G4 canonical of ANY word is a
POSITION FILTER — no recursion, no fixpoint:

* a letter of count 1 keeps its site;
* a letter whose last occurrence is NOT the final position ("closed")
  keeps ONLY its last site, doubled there;
* the letter whose last occurrence IS the final position ("open", count
  ≥ 2) keeps exactly its last-but-one and final sites;
* all other occurrences are deleted; surviving sites emit in ORIGINAL
  order.

This is because every hop relocates an interloper contiguously without
permuting the non-moved subsequence (the compiled `L2` fact), and the
iterated pair-closure of a count-k letter walks the survivor to the last
(closed) resp. last-but-one (open) site.  Spot checks: `xhxyh ↦ hxxyh`,
`yyxy ↦ yxy`, both matching the replayed semantic classes.

Six obligations below match the section interface of
`Order6LeeLiP2G4MergeCollapse.lean` VERBATIM, so instantiation is
literal.  Proven here: nonemptiness (`canonical_ne`) modulo one list
lemma, reducedness half of `canonical_normal`.  Named holes carry one
strategy each.
-/

namespace SemigroupBasis.CoRoots.Order6LeeLiP2G4

open SemigroupBasis

/-! ## The concrete canonical map -/

/-- Index of the last occurrence of `c` in `w` (length if absent). -/
def lastIdx (w : List Nat) (c : Nat) : Nat :=
  w.length - 1 - (w.reverse).idxOf c

/-- Index of the last-but-one occurrence of `c` (only meaningful when
`w.count c ≥ 2`). -/
def sndLastIdx (w : List Nat) (c : Nat) : Nat :=
  lastIdx (w.take (lastIdx w c)) c

/-- Emission at one site (see the module docstring). -/
def emitAt (w : List Nat) (i : Nat) (c : Nat) : List Nat :=
  if w.count c = 1 then [c]
  else if lastIdx w c = w.length - 1 then
    -- open letter: keep last-but-one and final sites
    if i = sndLastIdx w c ∨ i = lastIdx w c then [c] else []
  else
    -- closed letter: keep only the last site, doubled
    if i = lastIdx w c then [c, c] else []

/-- The concrete G4 canonical: a position filter over the original order. -/
def canonicalG4 (w : List Nat) : List Nat :=
  (w.zipIdx.map (fun ci => emitAt w ci.2 ci.1)).flatten

/-! ## Obligation 4: nonemptiness -/

/-- The final position always emits: a count-1 final letter emits itself;
a count-≥2 final letter is open and its final site is kept. -/
theorem emitAt_final_ne {w : List Nat} (hw : w ≠ []) :
    emitAt w (w.length - 1) (w.getLast hw) ≠ [] := by
  have hrev : w.reverse ≠ [] := by
    simpa using hw
  have hget : w.getLast hw = w.reverse.head hrev := by
    simpa using List.getLast_eq_head_reverse hw
  cases hwr : w.reverse with
  | nil => exact (hrev hwr).elim
  | cons c cs =>
      have hget' : w.getLast hw = c := by
        simpa [hwr] using hget
      have hidx : w.reverse.idxOf (w.getLast hw) = 0 := by
        rw [hwr, hget']
        exact List.idxOf_cons_self
      have hlast : lastIdx w (w.getLast hw) = w.length - 1 := by
        simp [lastIdx, hidx]
      simp [emitAt, hlast]

theorem canonical_ne : ∀ a : List Nat, a ≠ [] → canonicalG4 a ≠ [] := by
  intro a ha
  have hlastIndex : a.length - 1 < a.length := by
    cases a with
    | nil => exact (ha rfl).elim
    | cons head tail => exact Nat.le_refl _
  have hzipIndex : a.length - 1 < a.zipIdx.length := by
    simpa using hlastIndex
  have hpair : (a.getLast ha, a.length - 1) ∈ a.zipIdx := by
    simpa only [List.getElem_zipIdx, Nat.zero_add,
      List.getElem_length_sub_one_eq_getLast hlastIndex] using
      (List.getElem_mem hzipIndex)
  have hemission :
      emitAt a (a.length - 1) (a.getLast ha) ∈
        a.zipIdx.map (fun ci => emitAt a ci.2 ci.1) := by
    exact List.mem_map.mpr
      ⟨(a.getLast ha, a.length - 1), hpair, rfl⟩
  have hflatten :
      (a.zipIdx.map (fun ci => emitAt a ci.2 ci.1)).flatten ≠ [] := by
    exact List.flatten_ne_nil_iff.mpr
      ⟨emitAt a (a.length - 1) (a.getLast ha), hemission,
        emitAt_final_ne ha⟩
  simpa only [canonicalG4] using hflatten

/-! ## Obligation 5: outputs are canonical -/

private theorem sum_map_le_sum_map {α : Type}
    (xs : List α) (f g : α → Nat)
    (bounded : ∀ x, f x ≤ g x) :
    (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      exact Nat.add_le_add (bounded x) ih

private theorem sum_map_add {α : Type}
    (xs : List α) (f g : α → Nat) :
    (xs.map (fun x => f x + g x)).sum =
      (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      omega

private theorem sum_indicator_eq_count_map {α : Type}
    (xs : List α) (key : α → Nat) (target : Nat) :
    (xs.map (fun x => if key x = target then 1 else 0)).sum =
      (xs.map key).count target := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      by_cases same : key x = target
      · simp [same, ih, Nat.add_comm]
      · simp [same, ih]

private theorem zipIdx_index_indicator_sum_le_one
    (xs : List Nat) (target : Nat) :
    (xs.zipIdx.map
      (fun ci => if ci.2 = target then 1 else 0)).sum ≤ 1 := by
  rw [sum_indicator_eq_count_map]
  have indicesNodup : (xs.zipIdx.map Prod.snd).Nodup := by
    rw [List.zipIdx_map_snd]
    exact List.nodup_range'
  exact List.nodup_iff_count.mp indicesNodup target

private theorem emitAt_count_eq_zero_of_ne
    (a : List Nat) (i c d : Nat) (different : d ≠ c) :
    (emitAt a i d).count c = 0 := by
  unfold emitAt
  split
  · simp [different]
  · split
    · split <;> simp [different]
    · split <;> simp [different]

private theorem emitAt_count_le_single_indicator
    (a : List Nat) (c : Nat) (hcount : a.count c = 1)
    (ci : Nat × Nat) :
    (emitAt a ci.2 ci.1).count c ≤
      (if ci.1 = c then 1 else 0) := by
  rcases ci with ⟨d, i⟩
  by_cases same : d = c
  · subst d
    simp [emitAt, hcount]
  · rw [emitAt_count_eq_zero_of_ne a i c d same]
    simp [same]

private theorem emitAt_count_le_open_indicators
    (a : List Nat) (c : Nat) (hcount : a.count c ≠ 1)
    (hopen : lastIdx a c = a.length - 1) (ci : Nat × Nat) :
    (emitAt a ci.2 ci.1).count c ≤
      (if ci.2 = sndLastIdx a c then 1 else 0) +
        (if ci.2 = lastIdx a c then 1 else 0) := by
  rcases ci with ⟨d, i⟩
  by_cases same : d = c
  · subst d
    unfold emitAt
    rw [if_neg hcount, if_pos hopen]
    by_cases firstSite : i = sndLastIdx a c <;>
      by_cases lastSite : i = lastIdx a c <;>
        simp [firstSite, lastSite]
  · rw [emitAt_count_eq_zero_of_ne a i c d same]
    exact Nat.zero_le _

private theorem emitAt_count_le_closed_indicators
    (a : List Nat) (c : Nat) (hcount : a.count c ≠ 1)
    (hclosed : lastIdx a c ≠ a.length - 1) (ci : Nat × Nat) :
    (emitAt a ci.2 ci.1).count c ≤
      (if ci.2 = lastIdx a c then 1 else 0) +
        (if ci.2 = lastIdx a c then 1 else 0) := by
  rcases ci with ⟨d, i⟩
  by_cases same : d = c
  · subst d
    unfold emitAt
    rw [if_neg hcount, if_neg hclosed]
    by_cases lastSite : i = lastIdx a c <;>
      simp [lastSite]
  · rw [emitAt_count_eq_zero_of_ne a i c d same]
    exact Nat.zero_le _

private theorem canonical_count_eq_one_of_count_eq_one
    {a : List Nat} {c : Nat} (hcount : a.count c = 1) :
    (canonicalG4 a).count c = 1 := by
  unfold canonicalG4
  rw [List.count_flatten]
  simp only [List.map_map, Function.comp_apply]
  calc
    (a.zipIdx.map
        (fun ci => (emitAt a ci.2 ci.1).count c)).sum =
        (a.zipIdx.map
          (fun ci => if ci.1 = c then 1 else 0)).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro ci _
      apply Nat.le_antisymm
      · exact emitAt_count_le_single_indicator a c hcount ci
      · rcases ci with ⟨d, i⟩
        by_cases same : d = c
        · subst d
          simp [emitAt, hcount]
        · rw [emitAt_count_eq_zero_of_ne a i c d same]
          simp [same]
    _ = (a.zipIdx.map Prod.fst).count c :=
      sum_indicator_eq_count_map a.zipIdx Prod.fst c
    _ = a.count c := by rw [List.zipIdx_map_fst]
    _ = 1 := hcount

/-- Reducedness of outputs: each letter emits at most two symbols in
total (closed: one doubled site; open: two single sites; single: one). -/
theorem canonical_reduced : ∀ a : List Nat, Reduced (canonicalG4 a) := by
  intro a
  intro c
  unfold canonicalG4
  rw [List.count_flatten]
  simp only [List.map_map, Function.comp_apply]
  by_cases hcount : a.count c = 1
  · calc
      (a.zipIdx.map
          (fun ci => (emitAt a ci.2 ci.1).count c)).sum ≤
          (a.zipIdx.map
            (fun ci => if ci.1 = c then 1 else 0)).sum :=
        sum_map_le_sum_map _ _ _
          (emitAt_count_le_single_indicator a c hcount)
      _ = (a.zipIdx.map Prod.fst).count c :=
        sum_indicator_eq_count_map a.zipIdx Prod.fst c
      _ = a.count c := by rw [List.zipIdx_map_fst]
      _ = 1 := hcount
      _ ≤ 2 := by omega
  · by_cases hopen : lastIdx a c = a.length - 1
    · have firstBound :=
        zipIdx_index_indicator_sum_le_one a (sndLastIdx a c)
      have lastBound :=
        zipIdx_index_indicator_sum_le_one a (lastIdx a c)
      calc
        (a.zipIdx.map
            (fun ci => (emitAt a ci.2 ci.1).count c)).sum ≤
            (a.zipIdx.map (fun ci =>
              (if ci.2 = sndLastIdx a c then 1 else 0) +
                (if ci.2 = lastIdx a c then 1 else 0))).sum :=
          sum_map_le_sum_map _ _ _
            (emitAt_count_le_open_indicators a c hcount hopen)
        _ =
            (a.zipIdx.map
              (fun ci => if ci.2 = sndLastIdx a c then 1 else 0)).sum +
            (a.zipIdx.map
              (fun ci => if ci.2 = lastIdx a c then 1 else 0)).sum :=
          sum_map_add _ _ _
        _ ≤ 2 := by omega
    · have lastBound :=
        zipIdx_index_indicator_sum_le_one a (lastIdx a c)
      calc
        (a.zipIdx.map
            (fun ci => (emitAt a ci.2 ci.1).count c)).sum ≤
            (a.zipIdx.map (fun ci =>
              (if ci.2 = lastIdx a c then 1 else 0) +
                (if ci.2 = lastIdx a c then 1 else 0))).sum :=
          sum_map_le_sum_map _ _ _
            (emitAt_count_le_closed_indicators a c hcount hopen)
        _ =
            (a.zipIdx.map
              (fun ci => if ci.2 = lastIdx a c then 1 else 0)).sum +
            (a.zipIdx.map
              (fun ci => if ci.2 = lastIdx a c then 1 else 0)).sum :=
          sum_map_add _ _ _
        _ ≤ 2 := by omega

private theorem lastIdx_getLast {a : List Nat} (ha : a ≠ []) :
    lastIdx a (a.getLast ha) = a.length - 1 := by
  have reverseNe : a.reverse ≠ [] := by
    simpa using ha
  have getLastEq :
      a.getLast ha = a.reverse.head reverseNe := by
    simpa using List.getLast_eq_head_reverse ha
  cases reverseShape : a.reverse with
  | nil => exact (reverseNe reverseShape).elim
  | cons c cs =>
      have getLastEq' : a.getLast ha = c := by
        simpa [reverseShape] using getLastEq
      have indexEq : a.reverse.idxOf (a.getLast ha) = 0 := by
        rw [reverseShape, getLastEq']
        exact List.idxOf_cons_self
      simp [lastIdx, indexEq]

private theorem emitAt_final_eq_singleton {a : List Nat} (ha : a ≠ []) :
    emitAt a (a.length - 1) (a.getLast ha) = [a.getLast ha] := by
  have finalIndex := lastIdx_getLast ha
  simp [emitAt, finalIndex]

private theorem canonicalG4_lastLetter {a : List Nat} (ha : a ≠ []) :
    lastLetter? (canonicalG4 a) = some (a.getLast ha) := by
  have reconstruction : a.dropLast ++ [a.getLast ha] = a :=
    List.dropLast_concat_getLast ha
  have dropLength : a.dropLast.length = a.length - 1 := by
    simp
  have indexedReconstruction :
      a.zipIdx =
        a.dropLast.zipIdx ++ [(a.getLast ha, a.length - 1)] := by
    calc
      a.zipIdx = (a.dropLast ++ [a.getLast ha]).zipIdx := by
        rw [reconstruction]
      _ = a.dropLast.zipIdx ++
          [(a.getLast ha, a.dropLast.length)] := by
        rw [List.zipIdx_append]
        simp
      _ = a.dropLast.zipIdx ++
          [(a.getLast ha, a.length - 1)] := by
        rw [dropLength]
  unfold canonicalG4
  rw [indexedReconstruction]
  simp [emitAt_final_eq_singleton ha, lastLetter?]

private theorem eq_getLast_of_mem_of_lastIdx_eq
    {a : List Nat} {c : Nat} (ha : a ≠ []) (hc : c ∈ a)
    (hlast : lastIdx a c = a.length - 1) :
    c = a.getLast ha := by
  have reverseNe : a.reverse ≠ [] := by
    simpa using ha
  have reverseMem : c ∈ a.reverse := by
    simpa using hc
  have indexLt : a.reverse.idxOf c < a.reverse.length :=
    List.idxOf_lt_length_of_mem reverseMem
  have indexZero : a.reverse.idxOf c = 0 := by
    unfold lastIdx at hlast
    simp only [List.length_reverse] at indexLt
    omega
  have getLastEq :
      a.getLast ha = a.reverse.head reverseNe := by
    simpa using List.getLast_eq_head_reverse ha
  cases reverseShape : a.reverse with
  | nil => exact (reverseNe reverseShape).elim
  | cons d ds =>
      have headEq : d = c := by
        apply Decidable.byContradiction
        intro different
        rw [reverseShape, List.idxOf_cons] at indexZero
        simp only [cond_eq_ite, beq_iff_eq] at indexZero
        rw [if_neg different] at indexZero
        omega
      have getLastEq' : a.getLast ha = d := by
        simpa [reverseShape] using getLastEq
      exact headEq.symm.trans getLastEq'.symm

/-- The same renderer as `canonicalReduced`, exposed with an arbitrary
starting index so that flattened emission blocks can be handled one at a
time. -/
private def canonicalRenderFrom
    (whole : List Nat) (start : Nat) (letters : List Nat) : List Nat :=
  (letters.zipIdx start |>.map (fun ic =>
      match status? whole ic.1 with
      | some .closed =>
          if ic.2 = firstIdx whole ic.1 then ([] : List Nat)
          else [ic.1, ic.1]
      | _ => [ic.1])).flatten

private theorem canonicalRenderFrom_append
    (whole : List Nat) (start : Nat) (left right : List Nat) :
    canonicalRenderFrom whole start (left ++ right) =
      canonicalRenderFrom whole start left ++
        canonicalRenderFrom whole (start + left.length) right := by
  simp [canonicalRenderFrom, List.zipIdx_append]

private def emissionBlocks
    (a : List Nat) (sites : List (Nat × Nat)) : List (List Nat) :=
  sites.map (fun ci => emitAt a ci.2 ci.1)

private theorem canonicalRenderFrom_emitAt
    (a : List Nat) (beforeSites afterSites : List (Nat × Nat))
    (c i : Nat)
    (sites : a.zipIdx = beforeSites ++ (c, i) :: afterSites) :
    canonicalRenderFrom (canonicalG4 a)
        (emissionBlocks a beforeSites).flatten.length
        (emitAt a i c) =
      emitAt a i c := by
  let before := (emissionBlocks a beforeSites).flatten
  let after := (emissionBlocks a afterSites).flatten
  change
    canonicalRenderFrom (canonicalG4 a) before.length (emitAt a i c) =
      emitAt a i c
  have siteMem : (c, i) ∈ a.zipIdx := by
    rw [sites]
    simp
  have letterMem : c ∈ a :=
    List.fst_mem_of_mem_zipIdx siteMem
  have sourceNe : a ≠ [] := by
    intro empty
    subst a
    simp at letterMem
  have outputSplit :
      canonicalG4 a = before ++ emitAt a i c ++ after := by
    dsimp [before, after, emissionBlocks]
    unfold canonicalG4
    rw [sites]
    simp [List.map_append, List.append_assoc]
  by_cases countOne : a.count c = 1
  · have outputCount : (canonicalG4 a).count c = 1 :=
      canonical_count_eq_one_of_count_eq_one countOne
    have outputStatus :
        status? (canonicalG4 a) c = some .single := by
      simp [status?, outputCount]
    simp [emitAt, countOne, canonicalRenderFrom, outputStatus]
  · by_cases openLetter : lastIdx a c = a.length - 1
    · by_cases keptSite : i = sndLastIdx a c ∨ i = lastIdx a c
      · have sourceLast : c = a.getLast sourceNe :=
          eq_getLast_of_mem_of_lastIdx_eq sourceNe letterMem openLetter
        have keptFinal :
            i = sndLastIdx a c ∨ i = a.length - 1 := by
          rcases keptSite with firstSite | lastSite
          · exact Or.inl firstSite
          · exact Or.inr (by simpa [openLetter] using lastSite)
        have emitted : emitAt a i c = [c] := by
          simp [emitAt, countOne, openLetter, keptFinal]
        have outputLast :
            lastLetter? (canonicalG4 a) = some c := by
          simpa [← sourceLast] using canonicalG4_lastLetter sourceNe
        have outputMem : c ∈ canonicalG4 a := by
          rw [outputSplit, emitted]
          simp
        have outputPositive : 1 ≤ (canonicalG4 a).count c :=
          List.one_le_count_iff.mpr outputMem
        have outputBound := canonical_reduced a c
        have countCases :
            (canonicalG4 a).count c = 1 ∨
              (canonicalG4 a).count c = 2 := by
          omega
        rcases countCases with outputCount | outputCount
        · have outputStatus :
              status? (canonicalG4 a) c = some .single := by
            simp [status?, outputCount]
          rw [emitted]
          simp [canonicalRenderFrom, outputStatus]
        · have outputStatus :
              status? (canonicalG4 a) c = some .openPair := by
            simp [status?, outputCount, outputLast]
          rw [emitted]
          simp [canonicalRenderFrom, outputStatus]
      · have notKeptFinal :
            ¬(i = sndLastIdx a c ∨ i = a.length - 1) := by
          intro keptFinal
          apply keptSite
          rcases keptFinal with firstSite | lastSite
          · exact Or.inl firstSite
          · exact Or.inr (by simpa [openLetter] using lastSite)
        have emitted : emitAt a i c = [] := by
          simp [emitAt, countOne, openLetter, notKeptFinal]
        rw [emitted]
        simp [canonicalRenderFrom]
    · by_cases keptSite : i = lastIdx a c
      · have emitted : emitAt a i c = [c, c] := by
          simp [emitAt, countOne, openLetter, keptSite]
        have outputBound := canonical_reduced a c
        have pairLower : 2 ≤ (canonicalG4 a).count c := by
          rw [outputSplit, emitted]
          simp [List.count_append]
          omega
        have outputCount : (canonicalG4 a).count c = 2 := by
          omega
        have beforeCount : before.count c = 0 := by
          have wholeBound := canonical_reduced a c
          rw [outputSplit, emitted] at wholeBound
          simp [List.count_append] at wholeBound
          omega
        have beforeAbsent : c ∉ before :=
          List.count_eq_zero.mp beforeCount
        have firstIndex :
            firstIdx (canonicalG4 a) c = before.length := by
          unfold firstIdx
          rw [outputSplit, emitted]
          simp [List.idxOf_append, beforeAbsent]
        have sourceLastIndex := lastIdx_getLast sourceNe
        have lastDifferent : a.getLast sourceNe ≠ c := by
          intro same
          apply openLetter
          simpa [same] using sourceLastIndex
        have outputNotLast :
            lastLetter? (canonicalG4 a) ≠ some c := by
          rw [canonicalG4_lastLetter sourceNe]
          simp [lastDifferent]
        have outputStatus :
            status? (canonicalG4 a) c = some .closed := by
          simp [status?, outputCount, outputNotLast]
        have nextIndex : before.length + 1 ≠ before.length := by
          omega
        rw [emitted]
        simp [canonicalRenderFrom, outputStatus, firstIndex, nextIndex]
      · have emitted : emitAt a i c = [] := by
          simp [emitAt, countOne, openLetter, keptSite]
        rw [emitted]
        simp [canonicalRenderFrom]

private theorem canonicalRenderFrom_emissions
    (a : List Nat) :
    ∀ (beforeSites remainingSites : List (Nat × Nat)),
      a.zipIdx = beforeSites ++ remainingSites →
      canonicalRenderFrom (canonicalG4 a)
          (emissionBlocks a beforeSites).flatten.length
          (emissionBlocks a remainingSites).flatten =
        (emissionBlocks a remainingSites).flatten := by
  intro beforeSites remainingSites sites
  induction remainingSites generalizing beforeSites with
  | nil => simp [emissionBlocks, canonicalRenderFrom]
  | cons ci remainingSites ih =>
      rcases ci with ⟨c, i⟩
      change
        canonicalRenderFrom (canonicalG4 a)
            (emissionBlocks a beforeSites).flatten.length
            (emitAt a i c ++ (emissionBlocks a remainingSites).flatten) =
          emitAt a i c ++ (emissionBlocks a remainingSites).flatten
      rw [canonicalRenderFrom_append]
      rw [canonicalRenderFrom_emitAt a beforeSites remainingSites c i sites]
      have nextSites :
          a.zipIdx = (beforeSites ++ [(c, i)]) ++ remainingSites := by
        simpa [List.append_assoc] using sites
      have next := ih (beforeSites ++ [(c, i)]) nextSites
      have next' :
          canonicalRenderFrom (canonicalG4 a)
              ((emissionBlocks a beforeSites).flatten.length +
                (emitAt a i c).length)
              (emissionBlocks a remainingSites).flatten =
            (emissionBlocks a remainingSites).flatten := by
        simpa [emissionBlocks, List.map_append, List.append_assoc] using next
      exact congrArg (fun tail => emitAt a i c ++ tail) next'

theorem canonical_normal :
    ∀ a, Reduced (canonicalG4 a) ∧
      canonicalReduced (canonicalG4 a) = canonicalG4 a := by
  intro a
  refine ⟨canonical_reduced a, ?_⟩
  have rendered :=
    canonicalRenderFrom_emissions a [] a.zipIdx (by simp)
  simpa [canonicalReduced, canonicalRenderFrom, canonicalG4,
    emissionBlocks] using rendered

/-! ## Obligation 2: agreement on reduced words -/

theorem canonicalReduced_eq :
    ∀ {a : List Nat}, Reduced a → canonicalG4 a = canonicalReduced a := by
  have splitOne :
      ∀ (xs : List Nat) (c : Nat), xs.count c = 1 →
        ∃ p r, c ∉ p ∧ c ∉ r ∧ xs = p ++ c :: r := by
    intro xs c hcount
    induction xs with
    | nil =>
        simp at hcount
    | cons x xs ih =>
        by_cases hxc : x = c
        · subst x
          have htail : xs.count c = 0 := by
            simp only [List.count_cons_self] at hcount
            omega
          exact
            ⟨[], xs, by simp, List.count_eq_zero.mp htail, by simp⟩
        · have htail : xs.count c = 1 := by
            simpa [hxc] using hcount
          obtain ⟨p, r, hp, hr, hshape⟩ := ih htail
          exact
            ⟨x :: p, r, by simp [Ne.symm hxc, hp], hr, by simp [hshape]⟩
  have splitTwo :
      ∀ (xs : List Nat) (c : Nat), xs.count c = 2 →
        ∃ p q r,
          c ∉ p ∧ c ∉ q ∧ c ∉ r ∧
            xs = p ++ c :: q ++ c :: r := by
    intro xs c hcount
    induction xs with
    | nil =>
        simp at hcount
    | cons x xs ih =>
        by_cases hxc : x = c
        · subst x
          have htail : xs.count c = 1 := by
            simp only [List.count_cons_self] at hcount
            omega
          obtain ⟨q, r, hq, hr, hshape⟩ :=
            splitOne xs c htail
          exact
            ⟨[], q, r, by simp, hq, hr, by simp [hshape]⟩
        · have htail : xs.count c = 2 := by
            simpa [hxc] using hcount
          obtain ⟨p, q, r, hp, hq, hr, hshape⟩ := ih htail
          exact
            ⟨x :: p, q, r, by simp [Ne.symm hxc, hp], hq, hr,
              by simp [hshape]⟩
  intro a ha
  unfold canonicalG4 canonicalReduced
  apply congrArg List.flatten
  apply List.map_congr_left
  intro ci hci
  rcases ci with ⟨c, i⟩
  have hcMem : c ∈ a :=
    List.fst_mem_of_mem_zipIdx hci
  have hcPos : 1 ≤ a.count c :=
    List.one_le_count_iff.mpr hcMem
  have hcLe : a.count c ≤ 2 := ha c
  have hcCases : a.count c = 1 ∨ a.count c = 2 := by
    omega
  rcases hcCases with hcount | hcount
  · simp [emitAt, status?, hcount]
  · obtain ⟨p, q, r, hp, hq, hr, hshape⟩ :=
      splitTwo a c hcount
    subst a
    have hi :
        i = p.length ∨ i = p.length + 1 + q.length := by
      have h := hci
      rw [List.zipIdx_append] at h
      rcases List.mem_append.mp h with hMiddle | hSecondTail
      · rw [List.zipIdx_append] at hMiddle
        rcases List.mem_append.mp hMiddle with hP | hFirstTail
        · exact (hp (List.fst_mem_of_mem_zipIdx hP)).elim
        · simp only [Nat.zero_add] at hFirstTail
          rw [List.zipIdx_cons] at hFirstTail
          rcases List.mem_cons.mp hFirstTail with hFirst | hQ
          · left
            simpa using congrArg Prod.snd hFirst
          · exact (hq (List.fst_mem_of_mem_zipIdx hQ)).elim
      · simp only [Nat.zero_add] at hSecondTail
        rw [List.zipIdx_cons] at hSecondTail
        rcases List.mem_cons.mp hSecondTail with hSecond | hR
        · right
          have hSecondIndex := congrArg Prod.snd hSecond
          simp only [List.length_append, List.length_cons] at hSecondIndex
          omega
        · exact (hr (List.fst_mem_of_mem_zipIdx hR)).elim
    have hmiddleFirstIdx :
        (p ++ c :: q).idxOf c = p.length := by
      rw [List.idxOf_append]
      simp [hp]
    have hfirstIdx :
        firstIdx (p ++ c :: q ++ c :: r) c = p.length := by
      unfold firstIdx
      rw [List.idxOf_append]
      simp [hmiddleFirstIdx]
    have hreverse :
        (p ++ c :: q ++ c :: r).reverse =
          r.reverse ++ [c] ++ q.reverse ++ [c] ++ p.reverse := by
      simp [List.reverse_append, List.append_assoc]
    have hrevR : c ∉ r.reverse := by
      simpa using hr
    have hreverseIdx :
        (p ++ c :: q ++ c :: r).reverse.idxOf c = r.length := by
      rw [hreverse]
      simp [List.idxOf_append, hrevR]
    have hlastIdx :
        lastIdx (p ++ c :: q ++ c :: r) c =
          p.length + 1 + q.length := by
      unfold lastIdx
      rw [hreverseIdx]
      simp
      omega
    have hmiddleLength :
        (p ++ c :: q).length = p.length + 1 + q.length := by
      simp
      omega
    have htake :
        (p ++ c :: q ++ c :: r).take (p.length + 1 + q.length) =
          p ++ c :: q := by
      rw [← hmiddleLength]
      simpa [List.append_assoc] using
        (List.take_left (l₁ := p ++ c :: q) (l₂ := c :: r))
    have hmiddleReverse :
        (p ++ c :: q).reverse = q.reverse ++ [c] ++ p.reverse := by
      simp [List.reverse_append, List.append_assoc]
    have hrevQ : c ∉ q.reverse := by
      simpa using hq
    have hmiddleReverseIdx :
        (p ++ c :: q).reverse.idxOf c = q.length := by
      rw [hmiddleReverse]
      simp [List.idxOf_append, hrevQ]
    have hmiddleLastIdx :
        lastIdx (p ++ c :: q) c = p.length := by
      unfold lastIdx
      rw [hmiddleReverseIdx]
      simp
    have hsndLastIdx :
        sndLastIdx (p ++ c :: q ++ c :: r) c = p.length := by
      unfold sndLastIdx
      rw [hlastIdx, htake]
      exact hmiddleLastIdx
    have hdistinct :
        p.length ≠ p.length + 1 + q.length := by
      omega
    have hdistinct' :
        p.length + 1 + q.length ≠ p.length :=
      Ne.symm hdistinct
    cases r with
    | nil =>
        have hopen :
            lastIdx (p ++ c :: q ++ c :: []) c =
              (p ++ c :: q ++ c :: []).length - 1 := by
          rw [hlastIdx]
          simp
          omega
        have hterminal :
            lastLetter? (p ++ c :: q ++ c :: []) = some c := by
          unfold lastLetter?
          have hshapeLast :
              p ++ c :: q ++ c :: [] = (p ++ c :: q) ++ [c] := by
            simp [List.append_assoc]
          rw [hshapeLast, List.getLast?_append]
          all_goals rfl
        rcases hi with hi | hi
        · subst i
          unfold emitAt status?
          simp only [hcount]
          rw [if_pos hopen]
          rw [if_pos (Or.inl hsndLastIdx.symm)]
          rw [if_pos hterminal]
          all_goals rfl
        · subst i
          unfold emitAt status?
          simp only [hcount]
          rw [if_pos hopen]
          rw [if_pos (Or.inr hlastIdx.symm)]
          rw [if_pos hterminal]
          all_goals rfl
    | cons d ds =>
        have hclosed :
            lastIdx (p ++ c :: q ++ c :: d :: ds) c ≠
              (p ++ c :: q ++ c :: d :: ds).length - 1 := by
          rw [hlastIdx]
          simp
          omega
        have hwholeShape :
            p ++ c :: q ++ c :: d :: ds =
              (p ++ c :: q ++ [c]) ++ (d :: ds) := by
          simp [List.append_assoc]
        have htailSome :
            (d :: ds).getLast? =
              some ((d :: ds).getLast (by simp)) :=
          List.getLast?_eq_some_getLast (by simp)
        have hwholeLast :
            lastLetter? (p ++ c :: q ++ c :: d :: ds) =
              (d :: ds).getLast? := by
          unfold lastLetter?
          rw [hwholeShape, List.getLast?_append, htailSome]
          all_goals rfl
        have hterminal :
            lastLetter? (p ++ c :: q ++ c :: d :: ds) ≠ some c := by
          intro h
          exact hr <| List.mem_of_getLast? (hwholeLast.symm.trans h)
        rcases hi with hi | hi
        · subst i
          have hnotLast :
              p.length ≠ lastIdx (p ++ c :: q ++ c :: d :: ds) c := by
            rw [hlastIdx]
            exact hdistinct
          have hAtFirst :
              p.length = firstIdx (p ++ c :: q ++ c :: d :: ds) c :=
            hfirstIdx.symm
          unfold emitAt status?
          simp only [hcount]
          rw [if_neg hclosed]
          rw [if_neg hnotLast]
          rw [if_neg hterminal]
          rw [if_pos hAtFirst]
          all_goals rfl
        · subst i
          have hAtLast :
              p.length + 1 + q.length =
                lastIdx (p ++ c :: q ++ c :: d :: ds) c :=
            hlastIdx.symm
          have hnotFirst :
              p.length + 1 + q.length ≠
                firstIdx (p ++ c :: q ++ c :: d :: ds) c := by
            rw [hfirstIdx]
            exact hdistinct'
          unfold emitAt status?
          simp only [hcount]
          rw [if_neg hclosed]
          rw [if_pos hAtLast]
          rw [if_neg hterminal]
          rw [if_neg hnotFirst]
          all_goals rfl

/-! ## Obligation 3: the normalization derivation -/

/-- On a reduced word, sum the strict widths of all nonfinal repeated-letter
pairs.  Exactly the first occurrence of each closed pair contributes. -/
def closedGap (w : List Nat) : Nat :=
  (w.zipIdx.map (fun ci =>
    if w.count ci.1 = 2 ∧ lastIdx w ci.1 ≠ w.length - 1 ∧
        ci.2 < lastIdx w ci.1 then
      lastIdx w ci.1 - ci.2 - 1
    else 0)).sum

/- The descent used below scans a reduced word from right to left.  Its
processed suffix is already fixed by `canonicalReduced`; the only possible
letter shared by the unprocessed prefix and that suffix is the final (open)
letter.  These private renderer lemmas isolate the otherwise noisy `zipIdx`
bookkeeping needed to preserve that invariant. -/

private def reducedBlockW3 (whole : List Nat) (ci : Nat × Nat) : List Nat :=
  match status? whole ci.1 with
  | some .closed =>
      if ci.2 = firstIdx whole ci.1 then [] else [ci.1, ci.1]
  | _ => [ci.1]

private def reducedRenderFromW3
    (whole : List Nat) (start : Nat) (letters : List Nat) : List Nat :=
  (letters.zipIdx start |>.map (reducedBlockW3 whole)).flatten

private theorem canonicalReduced_eq_reducedRenderFromW3 (w : List Nat) :
    canonicalReduced w = reducedRenderFromW3 w 0 w := by
  rfl

private theorem reducedRenderFromW3_cons
    (whole : List Nat) (start : Nat) (c : Nat) (rest : List Nat) :
    reducedRenderFromW3 whole start (c :: rest) =
      reducedBlockW3 whole (c, start) ++
        reducedRenderFromW3 whole (start + 1) rest := by
  simp [reducedRenderFromW3, List.zipIdx_cons]

private theorem zipIdx_add_right (letters : List Nat) (start offset : Nat) :
    letters.zipIdx (start + offset) =
      (letters.zipIdx start).map (fun ci => (ci.1, ci.2 + offset)) := by
  induction letters generalizing start with
  | nil => simp
  | cons c rest ih =>
      simp only [List.zipIdx_cons, List.map_cons]
      apply congrArg (List.cons (c, start + offset))
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        ih (start + 1)

private theorem reducedRenderFromW3_shift
    (source shifted letters : List Nat) (offset : Nat)
    (blocks : ∀ ci, ci ∈ letters.zipIdx →
      reducedBlockW3 shifted (ci.1, ci.2 + offset) =
        reducedBlockW3 source ci) :
    reducedRenderFromW3 shifted offset letters =
      reducedRenderFromW3 source 0 letters := by
  unfold reducedRenderFromW3
  have shiftedIndices := zipIdx_add_right letters 0 offset
  simp only [Nat.zero_add] at shiftedIndices
  rw [shiftedIndices]
  simp only [List.map_map, Function.comp_apply]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro ci member
  exact blocks ci member

private theorem lastLetter_cons_eq {c : Nat} {rest : List Nat}
    (restNe : rest ≠ []) :
    lastLetter? (c :: rest) = lastLetter? rest := by
  unfold lastLetter?
  have restLast :
      rest.getLast? = some (rest.getLast restNe) :=
    List.getLast?_eq_some_getLast restNe
  have shape : c :: rest = [c] ++ rest := by simp
  rw [shape, List.getLast?_append, restLast]
  rfl

private theorem reducedBlockW3_cons_shift_of_ne
    (head d i : Nat) {rest : List Nat} (restNe : rest ≠ [])
    (different : head ≠ d) :
    reducedBlockW3 (head :: rest) (d, i + 1) =
      reducedBlockW3 rest (d, i) := by
  have countEq : (head :: rest).count d = rest.count d := by
    simp [different]
  have lastEq :
      lastLetter? (head :: rest) = lastLetter? rest :=
    lastLetter_cons_eq restNe
  have statusEq : status? (head :: rest) d = status? rest d := by
    simp [status?, countEq, lastEq]
  have firstEq : firstIdx (head :: rest) d = firstIdx rest d + 1 := by
    unfold firstIdx
    rw [List.idxOf_cons]
    simp only [cond_eq_ite, beq_iff_eq]
    rw [if_neg different]
  unfold reducedBlockW3
  rw [statusEq, firstEq]
  cases current : status? rest d with
  | none => rfl
  | some kind =>
      cases kind with
      | single => rfl
      | openPair => rfl
      | closed =>
          by_cases atFirst : i = firstIdx rest d
          · simp [atFirst]
          · simp [atFirst]

private theorem reducedRenderFromW3_fresh_cons
    {head : Nat} {rest : List Nat} (restNe : rest ≠ [])
    (fresh : head ∉ rest) :
    reducedRenderFromW3 (head :: rest) 1 rest =
      reducedRenderFromW3 rest 0 rest := by
  apply reducedRenderFromW3_shift rest (head :: rest) rest 1
  intro ci member
  rcases ci with ⟨d, i⟩
  have dMem : d ∈ rest := List.fst_mem_of_mem_zipIdx member
  have different : head ≠ d := by
    intro equality
    subst d
    exact fresh dMem
  exact reducedBlockW3_cons_shift_of_ne head d i restNe different

private theorem reducedRenderFromW3_open_cons
    {head : Nat} {rest : List Nat} (restNe : rest ≠ [])
    (one : rest.count head = 1)
    (terminal : lastLetter? rest = some head) :
    reducedRenderFromW3 (head :: rest) 1 rest =
      reducedRenderFromW3 rest 0 rest := by
  apply reducedRenderFromW3_shift rest (head :: rest) rest 1
  intro ci member
  rcases ci with ⟨d, i⟩
  by_cases same : d = head
  · subst d
    have fullCount : (head :: rest).count head = 2 := by
      simp [one]
    have fullLast : lastLetter? (head :: rest) = some head := by
      rw [lastLetter_cons_eq restNe, terminal]
    have sourceStatus : status? rest head = some .single := by
      simp [status?, one]
    have shiftedStatus : status? (head :: rest) head = some .openPair := by
      simp [status?, fullCount, fullLast]
    simp [reducedBlockW3, sourceStatus, shiftedStatus]
  · exact reducedBlockW3_cons_shift_of_ne head d i restNe
      (Ne.symm same)

private theorem reducedRenderFromW3_fresh_pair
    {head : Nat} {rest : List Nat} (restNe : rest ≠ [])
    (fresh : head ∉ rest) :
    reducedRenderFromW3 (head :: head :: rest) 2 rest =
      reducedRenderFromW3 rest 0 rest := by
  apply reducedRenderFromW3_shift rest (head :: head :: rest) rest 2
  intro ci member
  rcases ci with ⟨d, i⟩
  have dMem : d ∈ rest := List.fst_mem_of_mem_zipIdx member
  have different : head ≠ d := by
    intro equality
    subst d
    exact fresh dMem
  have firstShift :=
    reducedBlockW3_cons_shift_of_ne head d i restNe different
  have secondShift :=
    reducedBlockW3_cons_shift_of_ne head d (i + 1) (by simp : head :: rest ≠ [])
      different
  simpa only [Nat.add_assoc, Nat.reduceAdd] using secondShift.trans firstShift

private theorem canonicalFixed_singleton (c : Nat) :
    Reduced [c] ∧ canonicalReduced [c] = [c] := by
  constructor
  · intro d
    by_cases same : d = c
    · subst d
      simp
    · have different : c ≠ d := Ne.symm same
      simp [different]
  · rw [canonicalReduced_eq_reducedRenderFromW3,
      reducedRenderFromW3_cons]
    simp [reducedRenderFromW3, reducedBlockW3, status?, firstIdx,
      lastLetter?]

private theorem canonicalFixed_fresh_cons
    {head : Nat} {rest : List Nat} (restNe : rest ≠ [])
    (fresh : head ∉ rest) (restReduced : Reduced rest)
    (restFixed : canonicalReduced rest = rest) :
    Reduced (head :: rest) ∧ canonicalReduced (head :: rest) = head :: rest := by
  have countZero : rest.count head = 0 := List.count_eq_zero.mpr fresh
  constructor
  · intro d
    by_cases same : d = head
    · subst d
      simp [countZero]
    · have different : head ≠ d := Ne.symm same
      simpa [different] using restReduced d
  · rw [canonicalReduced_eq_reducedRenderFromW3]
    rw [reducedRenderFromW3_cons]
    have headBlock : reducedBlockW3 (head :: rest) (head, 0) = [head] := by
      simp [reducedBlockW3, status?, countZero]
    rw [headBlock, reducedRenderFromW3_fresh_cons restNe fresh]
    simpa [canonicalReduced_eq_reducedRenderFromW3] using
      congrArg (fun tail => [head] ++ tail) restFixed

private theorem canonicalFixed_open_cons
    {head : Nat} {rest : List Nat} (restNe : rest ≠ [])
    (one : rest.count head = 1)
    (terminal : lastLetter? rest = some head)
    (restReduced : Reduced rest)
    (restFixed : canonicalReduced rest = rest) :
    Reduced (head :: rest) ∧ canonicalReduced (head :: rest) = head :: rest := by
  constructor
  · intro d
    by_cases same : d = head
    · subst d
      simp [one]
    · have different : head ≠ d := Ne.symm same
      simpa [different] using restReduced d
  · rw [canonicalReduced_eq_reducedRenderFromW3]
    rw [reducedRenderFromW3_cons]
    have fullCount : (head :: rest).count head = 2 := by simp [one]
    have fullLast : lastLetter? (head :: rest) = some head := by
      rw [lastLetter_cons_eq restNe, terminal]
    have headBlock : reducedBlockW3 (head :: rest) (head, 0) = [head] := by
      simp [reducedBlockW3, status?, fullCount, fullLast]
    rw [headBlock, reducedRenderFromW3_open_cons restNe one terminal]
    simpa [canonicalReduced_eq_reducedRenderFromW3] using
      congrArg (fun tail => [head] ++ tail) restFixed

private theorem canonicalFixed_fresh_pair
    {head : Nat} {rest : List Nat} (restNe : rest ≠ [])
    (fresh : head ∉ rest) (restReduced : Reduced rest)
    (restFixed : canonicalReduced rest = rest) :
    Reduced (head :: head :: rest) ∧
      canonicalReduced (head :: head :: rest) = head :: head :: rest := by
  have countZero : rest.count head = 0 := List.count_eq_zero.mpr fresh
  have fullCount : (head :: head :: rest).count head = 2 := by
    simp [countZero]
  have fullLastEq :
      lastLetter? (head :: head :: rest) = lastLetter? rest := by
    rw [lastLetter_cons_eq (by simp : head :: rest ≠ []),
      lastLetter_cons_eq restNe]
  have fullNotLast :
      lastLetter? (head :: head :: rest) ≠ some head := by
    intro equality
    have restLast : lastLetter? rest = some head := by
      rwa [fullLastEq] at equality
    exact fresh (List.mem_of_getLast? restLast)
  have fullStatus : status? (head :: head :: rest) head = some .closed := by
    simp [status?, fullCount, fullNotLast]
  have firstZero : firstIdx (head :: head :: rest) head = 0 := by
    simp [firstIdx]
  constructor
  · intro d
    by_cases same : d = head
    · subst d
      simpa [fullCount]
    · have different : head ≠ d := Ne.symm same
      simpa [different] using restReduced d
  · rw [canonicalReduced_eq_reducedRenderFromW3]
    rw [reducedRenderFromW3_cons, reducedRenderFromW3_cons]
    have firstBlock :
        reducedBlockW3 (head :: head :: rest) (head, 0) = [] := by
      simp [reducedBlockW3, fullStatus, firstZero]
    have secondBlock :
        reducedBlockW3 (head :: head :: rest) (head, 1) = [head, head] := by
      simp [reducedBlockW3, fullStatus, firstZero]
    rw [firstBlock, secondBlock,
      reducedRenderFromW3_fresh_pair restNe fresh]
    simpa [canonicalReduced_eq_reducedRenderFromW3] using
      congrArg (fun tail => [head, head] ++ tail) restFixed

/-- Delete the first of three consecutive occurrences of `c`.  The first
step moves the first copy across `U`; contraction deletes it when `V` is
nonempty, while cap handles the adjacent-triple case. -/
theorem deleteFirstOfThree
    (p U V s : List Nat) (c : Nat) (hcU : c ∉ U) (hcV : c ∉ V) :
    BlobReduces c
      (p ++ c :: (U ++ c :: (V ++ c :: s)))
      (p ++ U ++ c :: (V ++ c :: s)) := by
  cases U with
  | nil =>
      cases V with
      | nil =>
          exact BlobReduces.step (by
            simpa [List.append_assoc] using BlobStep.cap p s)
            (BlobReduces.refl _)
      | cons v vs =>
          have hV : v :: vs ≠ [] := by simp
          exact BlobReduces.step (by
            simpa [List.append_assoc] using
              BlobStep.contract p (v :: vs) s hV hcV)
            (BlobReduces.refl _)
  | cons u us =>
      have hU : u :: us ≠ [] := by simp
      have hSuffix : V ++ c :: s ≠ [] := by simp
      refine BlobReduces.step (by
        simpa [List.append_assoc] using
          BlobStep.hop p (u :: us) (V ++ c :: s) hU hSuffix hcU) ?_
      cases V with
      | nil =>
          exact BlobReduces.step (by
            simpa [List.append_assoc] using BlobStep.cap (p ++ u :: us) s)
            (BlobReduces.refl _)
      | cons v vs =>
          have hV : v :: vs ≠ [] := by simp
          exact BlobReduces.step (by
            simpa [List.append_assoc] using
              BlobStep.contract (p ++ u :: us) (v :: vs) s hV hcV)
            (BlobReduces.refl _)

private theorem splitFirstOccurrence (c : Nat) :
    ∀ {w : List Nat}, c ∈ w →
      ∃ p s, c ∉ p ∧ w = p ++ c :: s
  | [], member => by simp at member
  | x :: xs, member => by
      by_cases hxc : x = c
      · subst x
        exact ⟨[], xs, by simp, by simp⟩
      · have tailMember : c ∈ xs := by
          simpa [Ne.symm hxc] using member
        obtain ⟨p, s, hp, shape⟩ := splitFirstOccurrence c tailMember
        exact
          ⟨x :: p, s, by simp [Ne.symm hxc, hp], by simp [shape]⟩

/-- A count of at least three exposes the first three occurrences with
`c`-free prefix and intervening gaps. -/
private theorem splitFirstThreeOccurrences (c : Nat) {w : List Nat}
    (count : 3 ≤ w.count c) :
    ∃ p U V s,
      c ∉ p ∧ c ∉ U ∧ c ∉ V ∧
        w = p ++ c :: (U ++ c :: (V ++ c :: s)) := by
  have firstMember : c ∈ w := by
    exact List.count_pos_iff.mp (by omega)
  obtain ⟨p, firstTail, hp, firstShape⟩ :=
    splitFirstOccurrence c firstMember
  have hpCount : p.count c = 0 := List.count_eq_zero.mpr hp
  have firstTailCount : 2 ≤ firstTail.count c := by
    rw [firstShape, List.count_append, hpCount,
      List.count_cons_self] at count
    omega
  have secondMember : c ∈ firstTail :=
    List.count_pos_iff.mp (by omega)
  obtain ⟨U, secondTail, hU, secondShape⟩ :=
    splitFirstOccurrence c secondMember
  have hUCount : U.count c = 0 := List.count_eq_zero.mpr hU
  have secondTailCount : 1 ≤ secondTail.count c := by
    rw [secondShape, List.count_append, hUCount,
      List.count_cons_self] at firstTailCount
    omega
  have thirdMember : c ∈ secondTail :=
    List.count_pos_iff.mp (by omega)
  obtain ⟨V, s, hV, thirdShape⟩ :=
    splitFirstOccurrence c thirdMember
  refine ⟨p, U, V, s, hp, hU, hV, ?_⟩
  rw [firstShape, secondShape, thirdShape]

/-- Any over-cap letter admits a blob reduction deleting one occurrence and
strictly shortening the word. -/
theorem reduceOneOverCap {w : List Nat} {c : Nat}
    (count : 3 ≤ w.count c) :
    ∃ w', BlobReduces c w w' ∧ w'.length < w.length := by
  obtain ⟨p, U, V, s, hp, hU, hV, shape⟩ :=
    splitFirstThreeOccurrences c count
  let w' := p ++ U ++ c :: (V ++ c :: s)
  refine ⟨w', ?_, ?_⟩
  · rw [shape]
    exact deleteFirstOfThree p U V s c hU hV
  · rw [shape]
    simp [w', List.append_assoc]

/-- Repeatedly delete over-cap occurrences.  This stage changes only word
length; it does not yet fuse the separated closed pairs. -/
theorem derivesSomeReduced :
    ∀ w : List Nat,
      ∃ r, Reduced r ∧
        Derives basisG4 (wordOfD w) (wordOfD r)
  | w => by
      classical
      by_cases reduced : Reduced w
      · exact ⟨w, reduced, Derives.refl (wordOfD w)⟩
      · rw [Reduced] at reduced
        have existsOverCap : ∃ c, ¬w.count c ≤ 2 := by
          apply Classical.byContradiction
          intro none
          apply reduced
          intro c
          apply Classical.byContradiction
          intro overCap
          exact none ⟨c, overCap⟩
        obtain ⟨c, overCap⟩ := existsOverCap
        have count : 3 ≤ w.count c := by omega
        obtain ⟨w', chain, shorter⟩ := reduceOneOverCap count
        obtain ⟨r, rReduced, tail⟩ := derivesSomeReduced w'
        exact
          ⟨r, rReduced, (blobReduces_derives chain).trans tail⟩
termination_by w => w.length
decreasing_by exact shorter

private theorem reduceOneOverCap_nonempty {w : List Nat} {c : Nat}
    (count : 3 ≤ w.count c) :
    ∃ w', BlobReduces c w w' ∧ w'.length < w.length ∧ w' ≠ [] := by
  obtain ⟨p, U, V, s, hp, hU, hV, shape⟩ :=
    splitFirstThreeOccurrences c count
  let w' := p ++ U ++ c :: (V ++ c :: s)
  refine ⟨w', ?_, ?_, ?_⟩
  · rw [shape]
    exact deleteFirstOfThree p U V s c hU hV
  · rw [shape]
    simp [w', List.append_assoc]
  · simp [w']

/-- The stage-one reduction retains nonemptiness, which is needed by the
word-valued soundness interface used after the right-to-left scan. -/
private theorem derivesSomeReduced_nonempty :
    ∀ w : List Nat, w ≠ [] →
      ∃ r, Reduced r ∧ r ≠ [] ∧
        Derives basisG4 (wordOfD w) (wordOfD r)
  | w, wNe => by
      classical
      by_cases reduced : Reduced w
      · exact ⟨w, reduced, wNe, Derives.refl (wordOfD w)⟩
      · rw [Reduced] at reduced
        have existsOverCap : ∃ c, ¬w.count c ≤ 2 := by
          apply Classical.byContradiction
          intro none
          apply reduced
          intro c
          apply Classical.byContradiction
          intro overCap
          exact none ⟨c, overCap⟩
        obtain ⟨c, overCap⟩ := existsOverCap
        have count : 3 ≤ w.count c := by omega
        obtain ⟨w', chain, shorter, w'Ne⟩ :=
          reduceOneOverCap_nonempty count
        obtain ⟨r, rReduced, rNe, tail⟩ :=
          derivesSomeReduced_nonempty w' w'Ne
        exact
          ⟨r, rReduced, rNe, (blobReduces_derives chain).trans tail⟩
termination_by w => w.length
decreasing_by exact shorter

private def OpenCross (stem suffix : List Nat) : Prop :=
  ∀ c, c ∈ stem → c ∈ suffix →
    suffix.count c = 1 ∧ lastLetter? suffix = some c

/-- Scan the unprocessed prefix from its right edge.  A repeated right-edge
letter is a closed pair; one hop moves its first occurrence to the edge and
the adjacent double is transferred to the fixed suffix.  Otherwise the one
right-edge occurrence is transferred unchanged.  Fuel is exactly the prefix
length, so termination does not depend on an arithmetic gap measure. -/
private theorem scanReducedPrefix :
    ∀ (fuel : Nat) (stem suffix : List Nat),
      stem.length ≤ fuel →
      suffix ≠ [] →
      Reduced (stem ++ suffix) →
      Reduced suffix →
      canonicalReduced suffix = suffix →
      OpenCross stem suffix →
      ∃ n, n ≠ [] ∧ Reduced n ∧ canonicalReduced n = n ∧
        Derives basisG4 (wordOfD (stem ++ suffix)) (wordOfD n)
  | 0, stem, suffix, lengthBound, suffixNe, wholeReduced,
      suffixReduced, suffixFixed, cross => by
      have stemLength : stem.length = 0 := by omega
      have stemNil : stem = [] := List.eq_nil_of_length_eq_zero stemLength
      subst stem
      exact
        ⟨suffix, suffixNe, suffixReduced, suffixFixed,
          Derives.refl (wordOfD suffix)⟩
  | fuel + 1, stem, suffix, lengthBound, suffixNe, wholeReduced,
      suffixReduced, suffixFixed, cross => by
      classical
      by_cases stemNil : stem = []
      · subst stem
        exact
          ⟨suffix, suffixNe, suffixReduced, suffixFixed,
            Derives.refl (wordOfD suffix)⟩
      · let before := stem.dropLast
        let current := stem.getLast stemNil
        have stemShape : before ++ [current] = stem := by
          exact List.dropLast_concat_getLast stemNil
        have currentInStem : current ∈ stem := by
          rw [← stemShape]
          simp
        have beforeShort : before.length < stem.length := by
          rw [← stemShape]
          simp
        by_cases repeated : current ∈ before
        · obtain ⟨front, gap, frontFree, beforeShape⟩ :=
            splitFirstOccurrence current repeated
          have frontCount : front.count current = 0 :=
            List.count_eq_zero.mpr frontFree
          have countBound := wholeReduced current
          rw [← stemShape, beforeShape] at countBound
          simp only [List.count_append, List.count_cons_self,
            List.count_singleton] at countBound
          have gapCount : gap.count current = 0 := by omega
          have suffixCount : suffix.count current = 0 := by omega
          have gapFree : current ∉ gap := List.count_eq_zero.mp gapCount
          have suffixFree : current ∉ suffix :=
            List.count_eq_zero.mp suffixCount
          let newStem := front ++ gap
          let newSuffix := current :: current :: suffix
          have currentNewStemFree : current ∉ newStem := by
            simp [newStem, frontFree, gapFree]
          have newSuffixNe : newSuffix ≠ [] := by simp [newSuffix]
          have newFixed :=
            canonicalFixed_fresh_pair suffixNe suffixFree
              suffixReduced suffixFixed
          have countEq : ∀ d,
              (newStem ++ newSuffix).count d =
                (stem ++ suffix).count d := by
            intro d
            by_cases same : d = current
            · subst d
              simp [newStem, newSuffix, ← stemShape, beforeShape,
                List.count_append, frontCount, gapCount, suffixCount]
            · have different : current ≠ d := Ne.symm same
              simp [newStem, newSuffix, ← stemShape, beforeShape,
                List.count_append, different]
          have newReduced : Reduced (newStem ++ newSuffix) := by
            intro d
            rw [countEq d]
            exact wholeReduced d
          have newCross : OpenCross newStem newSuffix := by
            intro d dStem dSuffix
            have dBefore : d ∈ before := by
              rw [beforeShape]
              rcases List.mem_append.mp dStem with dFront | dGap
              · exact List.mem_append_left (current :: gap) dFront
              · exact List.mem_append_right front (List.Mem.tail current dGap)
            have dOldStem : d ∈ stem := by
              rw [← stemShape]
              exact List.mem_append_left [current] dBefore
            have different : current ≠ d := by
              intro equality
              subst d
              exact currentNewStemFree dStem
            have dOldSuffix : d ∈ suffix := by
              simp only [newSuffix, List.mem_cons] at dSuffix
              rcases dSuffix with same | same | old
              · exact (different same.symm).elim
              · exact (different same.symm).elim
              · exact old
            obtain ⟨one, terminal⟩ := cross d dOldStem dOldSuffix
            constructor
            · simpa [newSuffix, different] using one
            · simpa [newSuffix,
                lastLetter_cons_eq suffixNe,
                lastLetter_cons_eq (by simp : current :: suffix ≠ [])] using
                terminal
          have newShort : newStem.length < stem.length := by
            simp [newStem, ← stemShape, beforeShape]
            omega
          have newFuel : newStem.length ≤ fuel := by omega
          obtain ⟨n, nNe, nReduced, nFixed, tail⟩ :=
            scanReducedPrefix fuel newStem newSuffix newFuel newSuffixNe
              newReduced newFixed.1 newFixed.2 newCross
          by_cases gapNil : gap = []
          · subst gap
            refine ⟨n, nNe, nReduced, nFixed, ?_⟩
            simpa [newStem, newSuffix, ← stemShape, beforeShape,
              List.append_assoc] using tail
          · have firstStep :
                BlobStep current (stem ++ suffix) (newStem ++ newSuffix) := by
              rw [← stemShape, beforeShape]
              simpa [newStem, newSuffix, List.append_assoc] using
                BlobStep.hop front gap suffix gapNil suffixNe gapFree
            refine ⟨n, nNe, nReduced, nFixed, ?_⟩
            exact (blobStep_derives firstStep).trans tail
        · let newSuffix := current :: suffix
          have newSuffixNe : newSuffix ≠ [] := by simp [newSuffix]
          have newFixed :
              Reduced newSuffix ∧ canonicalReduced newSuffix = newSuffix := by
            by_cases currentInSuffix : current ∈ suffix
            · obtain ⟨one, terminal⟩ :=
                cross current currentInStem currentInSuffix
              exact canonicalFixed_open_cons suffixNe one terminal
                suffixReduced suffixFixed
            · exact canonicalFixed_fresh_cons suffixNe currentInSuffix
                suffixReduced suffixFixed
          have newReduced : Reduced (before ++ newSuffix) := by
            simpa [newSuffix, ← stemShape, List.append_assoc] using wholeReduced
          have newCross : OpenCross before newSuffix := by
            intro d dBefore dSuffix
            have dOldStem : d ∈ stem := by
              rw [← stemShape]
              exact List.mem_append_left [current] dBefore
            have different : current ≠ d := by
              intro equality
              subst d
              exact repeated dBefore
            have dOldSuffix : d ∈ suffix := by
              simp only [newSuffix, List.mem_cons] at dSuffix
              rcases dSuffix with same | old
              · exact (different same.symm).elim
              · exact old
            obtain ⟨one, terminal⟩ := cross d dOldStem dOldSuffix
            constructor
            · simpa [newSuffix, different] using one
            · simpa [newSuffix, lastLetter_cons_eq suffixNe] using terminal
          have newFuel : before.length ≤ fuel := by omega
          obtain ⟨n, nNe, nReduced, nFixed, tail⟩ :=
            scanReducedPrefix fuel before newSuffix newFuel newSuffixNe
              newReduced newFixed.1 newFixed.2 newCross
          refine ⟨n, nNe, nReduced, nFixed, ?_⟩
          simpa [newSuffix, ← stemShape, List.append_assoc] using tail

private theorem derivesReducedToFixed {w : List Nat}
    (wNe : w ≠ []) (wReduced : Reduced w) :
    ∃ n, n ≠ [] ∧ Reduced n ∧ canonicalReduced n = n ∧
      Derives basisG4 (wordOfD w) (wordOfD n) := by
  let final := w.getLast wNe
  let stem := w.dropLast
  have reconstruction : stem ++ [final] = w := by
    exact List.dropLast_concat_getLast wNe
  have initialFixed := canonicalFixed_singleton final
  have initialCross : OpenCross stem [final] := by
    intro c cStem cSuffix
    have same : c = final := by simpa using cSuffix
    subst c
    simp [lastLetter?]
  obtain ⟨n, nNe, nReduced, nFixed, chain⟩ :=
    scanReducedPrefix stem.length stem [final] (Nat.le_refl _)
      (by simp) (by simpa [reconstruction] using wReduced)
      initialFixed.1 initialFixed.2 initialCross
  refine ⟨n, nNe, nReduced, nFixed, ?_⟩
  simpa [reconstruction] using chain

/-- Constructive W3 core: every nonempty word derives to a nonempty reduced
word fixed by `canonicalReduced`.  This theorem is independent of the W1
soundness and W2 renderer-agreement obligations. -/
theorem derives_to_fixed_normal (w : List Nat) (wNe : w ≠ []) :
    ∃ n, n ≠ [] ∧ Reduced n ∧ canonicalReduced n = n ∧
      Derives basisG4 (wordOfD w) (wordOfD n) := by
  obtain ⟨reduced, reducedNormal, reducedNe, firstStage⟩ :=
    derivesSomeReduced_nonempty w wNe
  obtain ⟨marked, markedNe, markedReduced, markedFixed, secondStage⟩ :=
    derivesReducedToFixed reducedNe reducedNormal
  exact
    ⟨marked, markedNe, markedReduced, markedFixed,
      firstStage.trans secondStage⟩

/-! ## Obligation 1: soundness (laws preserve the canonical) -/

/-- Keep the last occurrence of each letter.  This local copy avoids coupling
the G4 witness to an unrelated normalizer module. -/
private def lastOccurrenceTrace : List Nat → List Nat
  | [] => []
  | letter :: rest =>
      if letter ∈ rest then lastOccurrenceTrace rest
      else letter :: lastOccurrenceTrace rest

/-- A prefix contributes nothing to the last-occurrence trace when every one
of its letters occurs again in the suffix. -/
private theorem lastOccurrenceTrace_drop_coveredPrefix :
    ∀ (front suffix : List Nat),
      (∀ letter, letter ∈ front → letter ∈ suffix) →
      lastOccurrenceTrace (front ++ suffix) =
        lastOccurrenceTrace suffix
  | [], _, _ => rfl
  | letter :: rest, suffix, covered => by
      have letterLater : letter ∈ rest ++ suffix :=
        List.mem_append_right rest
          (covered letter (List.Mem.head rest))
      rw [List.cons_append, lastOccurrenceTrace, if_pos letterLater]
      apply lastOccurrenceTrace_drop_coveredPrefix rest suffix
      intro next member
      exact covered next (List.Mem.tail letter member)

/-- The first copy of an arbitrary block is invisible to a last-occurrence
trace when another copy occurs later.  This is the common combinatorial step
behind the cap, hop, and head-dup G4 instances. -/
private theorem lastOccurrenceTrace_shadowedPrefix
    (front middle suffix : List Nat) :
    lastOccurrenceTrace (front ++ middle ++ front ++ suffix) =
      lastOccurrenceTrace (middle ++ front ++ suffix) := by
  have covered :
      ∀ letter, letter ∈ front →
        letter ∈ middle ++ front ++ suffix := by
    intro letter member
    exact List.mem_append_left suffix
      (List.mem_append_right middle member)
  simpa only [List.append_assoc] using
    lastOccurrenceTrace_drop_coveredPrefix
      front (middle ++ front ++ suffix) covered

/-- A block whose letters all occur in the suffix can be deleted at an
arbitrary position without changing the last-occurrence trace. -/
private theorem lastOccurrenceTrace_drop_coveredBlock
    (before removed suffix : List Nat)
    (covered : ∀ letter, letter ∈ removed → letter ∈ suffix) :
    lastOccurrenceTrace (before ++ removed ++ suffix) =
      lastOccurrenceTrace (before ++ suffix) := by
  induction before with
  | nil =>
      simpa only [List.nil_append, List.append_assoc] using
        lastOccurrenceTrace_drop_coveredPrefix removed suffix covered
  | cons letter rest inductionHypothesis =>
      have laterIff :
          letter ∈ rest ++ removed ++ suffix ↔
            letter ∈ rest ++ suffix := by
        constructor
        · intro member
          rcases List.mem_append.mp member with member | member
          · rcases List.mem_append.mp member with member | member
            · exact List.mem_append_left suffix member
            · exact List.mem_append_right rest (covered letter member)
          · exact List.mem_append_right rest member
        · intro member
          rcases List.mem_append.mp member with member | member
          · exact List.mem_append_left suffix
              (List.mem_append_left removed member)
          · exact List.mem_append_right (rest ++ removed) member
      simp only [List.cons_append, lastOccurrenceTrace]
      by_cases later : letter ∈ rest ++ suffix
      · rw [if_pos (laterIff.mpr later), if_pos later]
        exact inductionHypothesis
      · have notLater : letter ∉ rest ++ removed ++ suffix := by
          exact fun member => later (laterIff.mp member)
        rw [if_neg notLater, if_neg later]
        exact congrArg (List.cons letter) inductionHypothesis

/-- The block emitted at a rightmost nonfinal occurrence.  The final letter
is open and emits once; every other repeated letter emits a closed double. -/
private def traceEmit (whole : List Nat) (final letter : Nat) : List Nat :=
  if letter = final then [letter]
  else if whole.count letter = 1 then [letter] else [letter, letter]

private theorem lastIdx_split_last
    (before after : List Nat) (letter : Nat) (absent : letter ∉ after) :
    lastIdx (before ++ letter :: after) letter = before.length := by
  have reverseShape :
      (before ++ letter :: after).reverse =
        after.reverse ++ [letter] ++ before.reverse := by
    simp [List.reverse_append, List.append_assoc]
  have reverseAbsent : letter ∉ after.reverse := by
    simpa using absent
  have reverseIndex :
      (before ++ letter :: after).reverse.idxOf letter = after.length := by
    rw [reverseShape]
    simp [List.idxOf_append, reverseAbsent]
  unfold lastIdx
  rw [reverseIndex]
  simp

private theorem prefix_lt_lastIdx_of_mem_suffix
    (before after : List Nat) (letter : Nat) (member : letter ∈ after) :
    before.length < lastIdx (before ++ letter :: after) letter := by
  have reverseShape :
      (before ++ letter :: after).reverse =
        after.reverse ++ [letter] ++ before.reverse := by
    simp [List.reverse_append, List.append_assoc]
  have reverseMember : letter ∈ after.reverse := by
    simpa using member
  have indexBound : after.reverse.idxOf letter < after.length := by
    simpa using List.idxOf_lt_length_of_mem reverseMember
  have reverseIndex :
      (before ++ letter :: after).reverse.idxOf letter =
        after.reverse.idxOf letter := by
    rw [reverseShape]
    simp [List.idxOf_append, reverseMember]
  unfold lastIdx
  rw [reverseIndex]
  simp
  omega

private theorem lastIdx_ne_final_of_mem_prefix
    (stem : List Nat) (final letter : Nat)
    (member : letter ∈ stem) (different : letter ≠ final) :
    lastIdx (stem ++ [final]) letter ≠
      (stem ++ [final]).length - 1 := by
  have reverseMember : letter ∈ stem.reverse := by
    simpa using member
  have indexBound : stem.reverse.idxOf letter < stem.length := by
    simpa using List.idxOf_lt_length_of_mem reverseMember
  have different' : final ≠ letter := Ne.symm different
  have finalBeq : (final == letter) = false :=
    beq_eq_false_iff_ne.mpr different'
  have reverseIndex :
      (stem ++ [final]).reverse.idxOf letter =
        stem.reverse.idxOf letter + 1 := by
    simp [List.reverse_append, List.idxOf_cons, finalBeq]
  have strict :
      lastIdx (stem ++ [final]) letter < stem.length := by
    unfold lastIdx
    rw [reverseIndex]
    simp
    omega
  have finalIndex : (stem ++ [final]).length - 1 = stem.length := by
    simp
  rw [finalIndex]
  exact Nat.ne_of_lt strict

private theorem sndLastIdx_split_final
    (before between : List Nat) (letter : Nat)
    (absent : letter ∉ between) :
    sndLastIdx (before ++ letter :: (between ++ [letter])) letter =
      before.length := by
  have finalLast :
      lastIdx (before ++ letter :: (between ++ [letter])) letter =
        (before ++ letter :: between).length := by
    simpa [List.append_assoc] using
      lastIdx_split_last (before ++ letter :: between) [] letter (by simp)
  have takePrefix :
      (before ++ letter :: (between ++ [letter])).take
          (before ++ letter :: between).length =
        before ++ letter :: between := by
    simpa [List.append_assoc] using
      (List.take_left
        (l₁ := before ++ letter :: between) (l₂ := [letter]))
  unfold sndLastIdx
  rw [finalLast, takePrefix]
  exact lastIdx_split_last before between letter absent

/-- Local form of the position filter.  At the current nonfinal position,
the emission is empty exactly when the same letter occurs later in the
nonfinal remainder. -/
private theorem emitAt_split
    (before rest : List Nat) (final letter : Nat) :
    emitAt (before ++ letter :: (rest ++ [final])) before.length letter =
      if letter ∈ rest then []
      else traceEmit (before ++ letter :: (rest ++ [final])) final letter := by
  by_cases later : letter ∈ rest
  · have restPositive : 0 < rest.count letter :=
      List.count_pos_iff.mpr later
    have countLower :
        2 ≤ (before ++ letter :: (rest ++ [final])).count letter := by
      simp [List.count_append]
      omega
    have countNotOne :
        (before ++ letter :: (rest ++ [final])).count letter ≠ 1 := by
      omega
    by_cases finalEqual : letter = final
    · subst final
      have finalLast :
          lastIdx (before ++ letter :: (rest ++ [letter])) letter =
            (before ++ letter :: rest).length := by
        simpa [List.append_assoc] using
          lastIdx_split_last
            (before ++ letter :: rest) [] letter (by simp)
      have openLetter :
          lastIdx (before ++ letter :: (rest ++ [letter])) letter =
            (before ++ letter :: (rest ++ [letter])).length - 1 := by
        rw [finalLast]
        simp
      have takePrefix :
          (before ++ letter :: (rest ++ [letter])).take
              (before ++ letter :: rest).length =
            before ++ letter :: rest := by
        simpa [List.append_assoc] using
          (List.take_left
            (l₁ := before ++ letter :: rest) (l₂ := [letter]))
      have secondLast :
          sndLastIdx (before ++ letter :: (rest ++ [letter])) letter =
            lastIdx (before ++ letter :: rest) letter := by
        unfold sndLastIdx
        rw [finalLast, takePrefix]
      have currentBeforeSecond :
          before.length <
            sndLastIdx (before ++ letter :: (rest ++ [letter])) letter := by
        rw [secondLast]
        exact prefix_lt_lastIdx_of_mem_suffix before rest letter later
      have currentNeSecond :
          before.length ≠
            sndLastIdx (before ++ letter :: (rest ++ [letter])) letter :=
        Nat.ne_of_lt currentBeforeSecond
      have currentNeFinal :
          before.length ≠
            lastIdx (before ++ letter :: (rest ++ [letter])) letter := by
        rw [finalLast]
        simp
      have expandedCountNotOne :
          before.count letter + (rest.count letter + 1 + 1) ≠ 1 := by
        omega
      simp [emitAt, later, expandedCountNotOne, openLetter,
        currentNeSecond, currentNeFinal]
    · have prefixMember :
          letter ∈ before ++ letter :: rest := by simp
      have closedLetter :
          lastIdx (before ++ letter :: (rest ++ [final])) letter ≠
            (before ++ letter :: (rest ++ [final])).length - 1 :=
        by
          simpa [List.append_assoc] using
            lastIdx_ne_final_of_mem_prefix
              (before ++ letter :: rest) final letter prefixMember finalEqual
      have laterInPost : letter ∈ rest ++ [final] :=
        List.mem_append_left [final] later
      have currentBeforeLast :
          before.length <
            lastIdx (before ++ letter :: (rest ++ [final])) letter :=
        prefix_lt_lastIdx_of_mem_suffix
          before (rest ++ [final]) letter laterInPost
      have currentNeLast :
          before.length ≠
            lastIdx (before ++ letter :: (rest ++ [final])) letter :=
        Nat.ne_of_lt currentBeforeLast
      have expandedCountNotOne :
          before.count letter +
              (rest.count letter + [final].count letter + 1) ≠ 1 := by
        omega
      have closedIndex :
          lastIdx (before ++ letter :: (rest ++ [final])) letter ≠
            before.length + (rest.length + 1) := by
        intro equality
        apply closedLetter
        rw [equality]
        simp
      simp [emitAt, later, expandedCountNotOne, closedIndex, currentNeLast]
  · by_cases finalEqual : letter = final
    · subst final
      have countLower :
          2 ≤ (before ++ letter :: (rest ++ [letter])).count letter := by
        simp [List.count_append]
        omega
      have countNotOne :
          (before ++ letter :: (rest ++ [letter])).count letter ≠ 1 := by
        omega
      have finalLast :
          lastIdx (before ++ letter :: (rest ++ [letter])) letter =
            (before ++ letter :: rest).length := by
        simpa [List.append_assoc] using
          lastIdx_split_last
            (before ++ letter :: rest) [] letter (by simp)
      have openLetter :
          lastIdx (before ++ letter :: (rest ++ [letter])) letter =
            (before ++ letter :: (rest ++ [letter])).length - 1 := by
        rw [finalLast]
        simp
      have secondLast :
          sndLastIdx (before ++ letter :: (rest ++ [letter])) letter =
            before.length :=
        sndLastIdx_split_final before rest letter later
      simp [emitAt, traceEmit, later, countNotOne, openLetter, secondLast]
    · have postAbsent : letter ∉ rest ++ [final] := by
        simp [later, finalEqual]
      have currentLast :
          lastIdx (before ++ letter :: (rest ++ [final])) letter =
            before.length := by
        simpa [List.append_assoc] using
          lastIdx_split_last before (rest ++ [final]) letter postAbsent
      have prefixMember :
          letter ∈ before ++ letter :: rest := by simp
      have closedLetter :
          lastIdx (before ++ letter :: (rest ++ [final])) letter ≠
            (before ++ letter :: (rest ++ [final])).length - 1 :=
        by
          simpa [List.append_assoc] using
            lastIdx_ne_final_of_mem_prefix
              (before ++ letter :: rest) final letter prefixMember finalEqual
      simp [emitAt, traceEmit, later, finalEqual, currentLast, closedLetter]

private theorem emitSegment_eq_trace :
    ∀ (rest before : List Nat) (final : Nat),
      ((rest.zipIdx before.length).map (fun ci =>
          emitAt (before ++ rest ++ [final]) ci.2 ci.1)).flatten =
        (lastOccurrenceTrace rest).flatMap
          (traceEmit (before ++ rest ++ [final]) final)
  | [], before, final => by simp [lastOccurrenceTrace]
  | letter :: rest, before, final => by
      have inductionHypothesis :=
        emitSegment_eq_trace rest (before ++ [letter]) final
      by_cases later : letter ∈ rest
      · have siteEmpty :
            emitAt (before ++ letter :: (rest ++ [final]))
                before.length letter = [] := by
          rw [emitAt_split, if_pos later]
        simpa [List.zipIdx_cons, lastOccurrenceTrace, later, siteEmpty,
          List.append_assoc] using inductionHypothesis
      · have siteEmit :
            emitAt (before ++ letter :: (rest ++ [final]))
                before.length letter =
              traceEmit (before ++ letter :: (rest ++ [final]))
                final letter := by
          rw [emitAt_split, if_neg later]
        simpa [List.zipIdx_cons, lastOccurrenceTrace, later, siteEmit,
          List.append_assoc] using inductionHypothesis

private theorem emitAt_append_final (stem : List Nat) (final : Nat) :
    emitAt (stem ++ [final]) stem.length final = [final] := by
  have finalLast :
      lastIdx (stem ++ [final]) final = stem.length := by
    simpa using lastIdx_split_last stem [] final (by simp)
  have openLetter :
      lastIdx (stem ++ [final]) final =
        (stem ++ [final]).length - 1 := by
    rw [finalLast]
    simp
  simp [emitAt, finalLast, openLetter]

/-- Closed-form characterization of the concrete position filter. -/
private theorem canonicalG4_eq_traceRender (stem : List Nat) (final : Nat) :
    canonicalG4 (stem ++ [final]) =
      (lastOccurrenceTrace stem).flatMap
          (traceEmit (stem ++ [final]) final) ++ [final] := by
  have segment := emitSegment_eq_trace stem [] final
  have appended := congrArg (fun letters => letters ++ [final]) segment
  simpa [canonicalG4, List.zipIdx_append, emitAt_append_final,
    List.append_assoc] using appended

private theorem min_two_eq_one_iff (count : Nat) :
    min count 2 = 1 ↔ count = 1 := by
  omega

private theorem traceEmit_eq_of_cappedCounts
    (left right : List Nat) (final : Nat)
    (capped : ∀ letter,
      min (left.count letter) 2 = min (right.count letter) 2)
    (letter : Nat) :
    traceEmit left final letter = traceEmit right final letter := by
  by_cases isFinal : letter = final
  · simp [traceEmit, isFinal]
  · have sameSimple :
        left.count letter = 1 ↔ right.count letter = 1 := by
      calc
        left.count letter = 1 ↔ min (left.count letter) 2 = 1 :=
          (min_two_eq_one_iff (left.count letter)).symm
        _ ↔ min (right.count letter) 2 = 1 := by
          rw [capped letter]
        _ ↔ right.count letter = 1 :=
          min_two_eq_one_iff (right.count letter)
    by_cases leftSimple : left.count letter = 1
    · have rightSimple := sameSimple.mp leftSimple
      simp [traceEmit, isFinal, leftSimple, rightSimple]
    · have rightNotSimple : right.count letter ≠ 1 := by
        exact fun simple => leftSimple (sameSimple.mpr simple)
      simp [traceEmit, isFinal, leftSimple, rightNotSimple]

private theorem flatMap_congr_of_mem
    (left right : Nat → List Nat) :
    ∀ letters : List Nat,
      (∀ letter ∈ letters, left letter = right letter) →
      letters.flatMap left = letters.flatMap right
  | [], _ => rfl
  | letter :: rest, same => by
      rw [List.flatMap_cons, List.flatMap_cons,
        same letter (by simp)]
      exact congrArg (fun suffix => right letter ++ suffix) <|
        flatMap_congr_of_mem left right rest <| by
          intro selected member
          exact same selected (by simp [member])

private theorem canonicalG4_eq_of_splitSignature
    (leftPrefix rightPrefix : List Nat) (final : Nat)
    (capped : ∀ letter,
      min ((leftPrefix ++ [final]).count letter) 2 =
        min ((rightPrefix ++ [final]).count letter) 2)
    (traceEqual :
      lastOccurrenceTrace leftPrefix =
        lastOccurrenceTrace rightPrefix) :
    canonicalG4 (leftPrefix ++ [final]) =
      canonicalG4 (rightPrefix ++ [final]) := by
  rw [canonicalG4_eq_traceRender, canonicalG4_eq_traceRender]
  apply congrArg (fun blocks => blocks ++ [final])
  rw [traceEqual]
  apply flatMap_congr_of_mem
  intro letter _
  exact traceEmit_eq_of_cappedCounts
    (leftPrefix ++ [final]) (rightPrefix ++ [final]) final capped letter

/-- A common nonempty terminal supplies the same final letter on both sides.
The remainder is exactly capped multiplicity plus the last-occurrence trace
of the two nonfinal prefixes. -/
private theorem canonicalG4_eq_of_commonTerminal
    (leftBody rightBody terminal : List Nat)
    (terminalNonempty : terminal ≠ [])
    (capped : ∀ letter,
      min ((leftBody ++ terminal).count letter) 2 =
        min ((rightBody ++ terminal).count letter) 2)
    (traceEqual :
      lastOccurrenceTrace (leftBody ++ terminal.dropLast) =
        lastOccurrenceTrace (rightBody ++ terminal.dropLast)) :
    canonicalG4 (leftBody ++ terminal) =
      canonicalG4 (rightBody ++ terminal) := by
  let final := terminal.getLast terminalNonempty
  have reconstruction : terminal.dropLast ++ [final] = terminal := by
    exact List.dropLast_concat_getLast terminalNonempty
  have leftShape :
      leftBody ++ terminal =
        (leftBody ++ terminal.dropLast) ++ [final] := by
    calc
      leftBody ++ terminal =
          leftBody ++ (terminal.dropLast ++ [final]) :=
        congrArg (fun suffix => leftBody ++ suffix) reconstruction.symm
      _ = (leftBody ++ terminal.dropLast) ++ [final] := by
        simp [List.append_assoc]
  have rightShape :
      rightBody ++ terminal =
        (rightBody ++ terminal.dropLast) ++ [final] := by
    calc
      rightBody ++ terminal =
          rightBody ++ (terminal.dropLast ++ [final]) :=
        congrArg (fun suffix => rightBody ++ suffix) reconstruction.symm
      _ = (rightBody ++ terminal.dropLast) ++ [final] := by
        simp [List.append_assoc]
  rw [leftShape, rightShape]
  apply canonicalG4_eq_of_splitSignature
  · intro letter
    rw [← leftShape, ← rightShape]
    exact capped letter
  · exact traceEqual

/-- Fully invariant forms of the three G4 laws.  `Word` arguments make every
substituted block nonempty by construction, while the list arguments are the
possibly empty outer contexts introduced by congruence. -/
private structure CanonicalG4ContextualLaws : Prop where
  cap : ∀ (before after : List Nat) (x : Word Nat),
    canonicalG4
        (before ++ x.toList ++ x.toList ++ after) =
      canonicalG4
        (before ++ x.toList ++ x.toList ++ x.toList ++ after)
  hop : ∀ (before after : List Nat) (x y z : Word Nat),
    canonicalG4
        (before ++ x.toList ++ y.toList ++ x.toList ++ z.toList ++ after) =
      canonicalG4
        (before ++ y.toList ++ x.toList ++ x.toList ++ z.toList ++ after)
  headDup : ∀ (before after : List Nat) (x y : Word Nat),
    canonicalG4
        (before ++ x.toList ++ y.toList ++ x.toList ++ after) =
      canonicalG4
        (before ++ x.toList ++ x.toList ++ y.toList ++ x.toList ++ after)

private theorem word_toList_ne_nil (word : Word Nat) : word.toList ≠ [] := by
  cases word with
  | mk head tail =>
      simp [Word.toList]

private theorem canonicalG4_contextualLaws : CanonicalG4ContextualLaws := by
  refine
    { cap := ?_
      hop := ?_
      headDup := ?_ }
  · intro before after x
    have terminalNonempty : x.toList ++ after ≠ [] :=
      List.append_ne_nil_of_left_ne_nil (word_toList_ne_nil x) after
    have capped : ∀ letter,
        min (((before ++ x.toList) ++ (x.toList ++ after)).count letter) 2 =
          min (((before ++ x.toList ++ x.toList) ++
            (x.toList ++ after)).count letter) 2 := by
      intro letter
      by_cases member : letter ∈ x.toList
      · have positive : 0 < x.toList.count letter :=
          List.count_pos_iff.mpr member
        simp only [List.count_append]
        omega
      · have zero : x.toList.count letter = 0 :=
          List.count_eq_zero.mpr member
        simp [List.count_append, zero]
    have traceEqual :
        lastOccurrenceTrace
            ((before ++ x.toList) ++ (x.toList ++ after).dropLast) =
          lastOccurrenceTrace
            ((before ++ x.toList ++ x.toList) ++
              (x.toList ++ after).dropLast) := by
      have drop :=
        lastOccurrenceTrace_drop_coveredBlock
          before x.toList
            (x.toList ++ (x.toList ++ after).dropLast) (by
              intro letter member
              exact List.mem_append_left _ member)
      simpa [List.append_assoc] using drop.symm
    simpa only [List.append_assoc] using
      canonicalG4_eq_of_commonTerminal
        (before ++ x.toList)
        (before ++ x.toList ++ x.toList)
        (x.toList ++ after) terminalNonempty capped traceEqual
  · intro before after x y z
    have terminalNonempty : z.toList ++ after ≠ [] :=
      List.append_ne_nil_of_left_ne_nil (word_toList_ne_nil z) after
    have capped : ∀ letter,
        min (((before ++ x.toList ++ y.toList ++ x.toList) ++
          (z.toList ++ after)).count letter) 2 =
        min (((before ++ y.toList ++ x.toList ++ x.toList) ++
          (z.toList ++ after)).count letter) 2 := by
      intro letter
      simp only [List.count_append]
      omega
    have sourceTrace :
        lastOccurrenceTrace
            ((before ++ x.toList ++ y.toList ++ x.toList) ++
              (z.toList ++ after).dropLast) =
          lastOccurrenceTrace
            (before ++ y.toList ++ x.toList ++
              (z.toList ++ after).dropLast) := by
      have drop :=
        lastOccurrenceTrace_drop_coveredBlock
          before x.toList
            (y.toList ++ x.toList ++
              (z.toList ++ after).dropLast) (by
              intro letter member
              exact List.mem_append_left _
                (List.mem_append_right y.toList member))
      simpa [List.append_assoc] using drop
    have targetTrace :
        lastOccurrenceTrace
            ((before ++ y.toList ++ x.toList ++ x.toList) ++
              (z.toList ++ after).dropLast) =
          lastOccurrenceTrace
            (before ++ y.toList ++ x.toList ++
              (z.toList ++ after).dropLast) := by
      have drop :=
        lastOccurrenceTrace_drop_coveredBlock
          (before ++ y.toList) x.toList
            (x.toList ++ (z.toList ++ after).dropLast) (by
              intro letter member
              exact List.mem_append_left _ member)
      simpa [List.append_assoc] using drop
    have traceEqual :
        lastOccurrenceTrace
            ((before ++ x.toList ++ y.toList ++ x.toList) ++
              (z.toList ++ after).dropLast) =
          lastOccurrenceTrace
            ((before ++ y.toList ++ x.toList ++ x.toList) ++
              (z.toList ++ after).dropLast) :=
      sourceTrace.trans targetTrace.symm
    simpa only [List.append_assoc] using
      canonicalG4_eq_of_commonTerminal
        (before ++ x.toList ++ y.toList ++ x.toList)
        (before ++ y.toList ++ x.toList ++ x.toList)
        (z.toList ++ after) terminalNonempty capped traceEqual
  · intro before after x y
    have terminalNonempty : x.toList ++ after ≠ [] :=
      List.append_ne_nil_of_left_ne_nil (word_toList_ne_nil x) after
    have capped : ∀ letter,
        min (((before ++ x.toList ++ y.toList) ++
          (x.toList ++ after)).count letter) 2 =
        min (((before ++ x.toList ++ x.toList ++ y.toList) ++
          (x.toList ++ after)).count letter) 2 := by
      intro letter
      by_cases member : letter ∈ x.toList
      · have positive : 0 < x.toList.count letter :=
          List.count_pos_iff.mpr member
        simp only [List.count_append]
        omega
      · have zero : x.toList.count letter = 0 :=
          List.count_eq_zero.mpr member
        simp [List.count_append, zero]
    have traceEqual :
        lastOccurrenceTrace
            ((before ++ x.toList ++ y.toList) ++
              (x.toList ++ after).dropLast) =
          lastOccurrenceTrace
            ((before ++ x.toList ++ x.toList ++ y.toList) ++
              (x.toList ++ after).dropLast) := by
      have drop :=
        lastOccurrenceTrace_drop_coveredBlock
          before x.toList
            (x.toList ++ y.toList ++
              (x.toList ++ after).dropLast) (by
              intro letter member
              exact List.mem_append_left _
                (List.mem_append_left y.toList member))
      simpa [List.append_assoc] using drop.symm
    simpa only [List.append_assoc] using
      canonicalG4_eq_of_commonTerminal
        (before ++ x.toList ++ y.toList)
        (before ++ x.toList ++ x.toList ++ y.toList)
        (x.toList ++ after) terminalNonempty capped traceEqual

private theorem canonical_bind_append
    (left right : Word Nat) (sigma : Nat → Word Nat) :
    (left ++ right).bind sigma = left.bind sigma ++ right.bind sigma := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem canonical_bind_bind
    (word : Word Nat) (tau sigma : Nat → Word Nat) :
    (word.bind tau).bind sigma =
      word.bind (fun letter => (tau letter).bind sigma) := by
  apply Word.toList_injective
  simp [Word.toList_bind, List.flatMap_assoc]

private theorem canonical_bind_singleton (word : Word Nat) :
    word.bind Word.singleton = word := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem wordOfD_toList (letters : List Nat) (nonempty : letters ≠ []) :
    (wordOfD letters).toList = letters := by
  cases letters with
  | nil => exact (nonempty rfl).elim
  | cons _ _ => rfl

private theorem capL_bind_toList (sigma : Nat → Word Nat) :
    (capL.bind sigma).toList =
      (sigma 1).toList ++ (sigma 1).toList := by
  rw [Word.toList_bind]
  simp [capL, Word.toList]

private theorem capR_bind_toList (sigma : Nat → Word Nat) :
    (capR.bind sigma).toList =
      (sigma 1).toList ++ (sigma 1).toList ++ (sigma 1).toList := by
  rw [Word.toList_bind]
  simp [capR, Word.toList, List.append_assoc]

private theorem hopL_bind_toList (sigma : Nat → Word Nat) :
    (hopL.bind sigma).toList =
      (sigma 1).toList ++ (sigma 0).toList ++
        (sigma 1).toList ++ (sigma 2).toList := by
  rw [Word.toList_bind]
  simp [hopL, Word.toList, List.append_assoc]

private theorem hopR_bind_toList (sigma : Nat → Word Nat) :
    (hopR.bind sigma).toList =
      (sigma 0).toList ++ (sigma 1).toList ++
        (sigma 1).toList ++ (sigma 2).toList := by
  rw [Word.toList_bind]
  simp [hopR, Word.toList, List.append_assoc]

private theorem hdL_bind_toList (sigma : Nat → Word Nat) :
    (hdL.bind sigma).toList =
      (sigma 1).toList ++ (sigma 0).toList ++ (sigma 1).toList := by
  rw [Word.toList_bind]
  simp [hdL, Word.toList, List.append_assoc]

private theorem hdR_bind_toList (sigma : Nat → Word Nat) :
    (hdR.bind sigma).toList =
      (sigma 1).toList ++ (sigma 1).toList ++
        (sigma 0).toList ++ (sigma 1).toList := by
  rw [Word.toList_bind]
  simp [hdR, Word.toList, List.append_assoc]

private theorem contextualLaws_basisInstance
    (laws : CanonicalG4ContextualLaws)
    (e : Identity Nat) (member : e ∈ basisG4)
    (sigma : Nat → Word Nat) (before after : List Nat) :
    canonicalG4 (before ++ (e.lhs.bind sigma).toList ++ after) =
      canonicalG4 (before ++ (e.rhs.bind sigma).toList ++ after) := by
  simp only [basisG4, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · simpa only [capLaw, capL_bind_toList, capR_bind_toList,
      List.append_assoc] using laws.cap before after (sigma 1)
  · simpa only [hopLaw, hopL_bind_toList, hopR_bind_toList,
      List.append_assoc] using
      laws.hop before after (sigma 1) (sigma 0) (sigma 2)
  · simpa only [headDupLaw, hdL_bind_toList, hdR_bind_toList,
      List.append_assoc] using
      laws.headDup before after (sigma 1) (sigma 0)

/-- Once the three arbitrary-block contextual laws are available, soundness
for every derivation is formal.  Prefix and suffix constructors are absorbed
into the list contexts; the substitution constructor composes the pending
substitution using `TierA.bind_bind`. -/
private theorem canonicalG4_eq_of_derives_in_context
    (laws : CanonicalG4ContextualLaws)
    {u v : Word Nat} (derivation : Derives basisG4 u v) :
    ∀ (before after : List Nat) (sigma : Nat → Word Nat),
      canonicalG4 (before ++ (u.bind sigma).toList ++ after) =
        canonicalG4 (before ++ (v.bind sigma).toList ++ after) := by
  induction derivation with
  | fromBasis member =>
      intro before after sigma
      exact contextualLaws_basisInstance
        laws _ member sigma before after
  | refl =>
      intro _ _ _
      rfl
  | symm _ inductionHypothesis =>
      intro before after sigma
      exact (inductionHypothesis before after sigma).symm
  | trans _ _ firstProof secondProof =>
      intro before after sigma
      exact (firstProof before after sigma).trans
        (secondProof before after sigma)
  | prepend preWord _ inductionHypothesis =>
      intro before after sigma
      simpa only [canonical_bind_append, Word.toList_append,
        List.append_assoc] using
        inductionHypothesis
          (before ++ (preWord.bind sigma).toList) after sigma
  | appendRight _ postWord inductionHypothesis =>
      intro before after sigma
      simpa only [canonical_bind_append, Word.toList_append,
        List.append_assoc] using
        inductionHypothesis before
          ((postWord.bind sigma).toList ++ after) sigma
  | subst _ tau inductionHypothesis =>
      intro before after sigma
      simpa only [canonical_bind_bind] using
        inductionHypothesis before after
          (fun letter => (tau letter).bind sigma)

/-- Endpoint form of the preceding induction.  It leaves exactly one
mathematical input: a proof of the three fields of
`CanonicalG4ContextualLaws` for the concrete position filter. -/
private theorem canonicalSound_of_contextualLaws
    (laws : CanonicalG4ContextualLaws) :
    ∀ {a b : List Nat}, a ≠ [] → b ≠ [] →
      Derives basisG4 (wordOfD a) (wordOfD b) →
        canonicalG4 a = canonicalG4 b := by
  intro a b ha hb derivation
  have lifted :=
    canonicalG4_eq_of_derives_in_context laws derivation
      [] [] Word.singleton
  rw [canonical_bind_singleton (wordOfD a),
    canonical_bind_singleton (wordOfD b),
    wordOfD_toList a ha, wordOfD_toList b hb] at lifted
  simpa using lifted

theorem canonical_cap_step (p s : List Nat) (c : Nat) :
    canonicalG4 (p ++ c :: c :: s) = canonicalG4 (p ++ c :: c :: c :: s) := by
  simpa [Word.toList, Word.singleton, List.append_assoc] using
    canonicalG4_contextualLaws.cap p s (Word.singleton c)

theorem canonical_hop_step (p B s : List Nat) (c : Nat)
    (hB : B ≠ []) (hs : s ≠ []) (hcB : c ∉ B) :
    canonicalG4 (p ++ c :: (B ++ c :: s)) =
      canonicalG4 (p ++ B ++ c :: c :: s) := by
  have step := canonicalG4_contextualLaws.hop
    p [] (Word.singleton c) (wordOfD B) (wordOfD s)
  rw [wordOfD_toList B hB, wordOfD_toList s hs] at step
  simpa [Word.toList, Word.singleton, List.append_assoc] using step

theorem canonical_headDup_step (p B s : List Nat) (c : Nat) (hB : B ≠ []) :
    canonicalG4 (p ++ c :: (B ++ c :: s)) =
      canonicalG4 (p ++ c :: c :: (B ++ c :: s)) := by
  have step := canonicalG4_contextualLaws.headDup
    p s (Word.singleton c) (wordOfD B)
  rw [wordOfD_toList B hB] at step
  simpa [Word.toList, Word.singleton, List.append_assoc] using step

theorem canonicalSound :
    ∀ {a b : List Nat}, a ≠ [] → b ≠ [] →
      Derives basisG4 (wordOfD a) (wordOfD b) →
        canonicalG4 a = canonicalG4 b := by
  exact canonicalSound_of_contextualLaws canonicalG4_contextualLaws

/-- Normalize first by deleting over-cap occurrences, then scan the reduced
word from right to left.  Soundness identifies the fixed marked endpoint with
the closed-form canonical of the original word. -/
theorem derives_canonical :
    ∀ a : List Nat, a ≠ [] →
      Derives basisG4 (wordOfD a) (wordOfD (canonicalG4 a)) := by
  intro a aNe
  obtain ⟨marked, markedNe, markedReduced, markedFixed, fullChain⟩ :=
    derives_to_fixed_normal a aNe
  have endpoint : canonicalG4 a = marked := by
    calc
      canonicalG4 a = canonicalG4 marked :=
        canonicalSound aNe markedNe fullChain
      _ = canonicalReduced marked := canonicalReduced_eq markedReduced
      _ = marked := markedFixed
  simpa [endpoint] using fullChain

/-! ## Obligation 6: blob reduction reaches the canonical -/

private theorem blobReduces_trans {z : Nat} {u v w : List Nat}
    (huv : BlobReduces z u v) (hvw : BlobReduces z v w) :
    BlobReduces z u w := by
  induction huv generalizing w with
  | refl _ => exact hvw
  | step first _ ih => exact BlobReduces.step first (ih hvw)

private theorem blobStep_prefix (front : List Nat) {z : Nat}
    {u v : List Nat} (h : BlobStep z u v) :
    BlobStep z (front ++ u) (front ++ v) := by
  cases h with
  | hop p B s hB hs hzB =>
      simpa only [List.append_assoc] using
        (BlobStep.hop (z := z) (front ++ p) B s hB hs hzB)
  | contract p B s hB hzB =>
      simpa only [List.append_assoc] using
        (BlobStep.contract (z := z) (front ++ p) B s hB hzB)
  | cap p s =>
      simpa only [List.append_assoc] using
        (BlobStep.cap (z := z) (front ++ p) s)

private theorem blobReduces_prefix (front : List Nat) {z : Nat}
    {u v : List Nat} (h : BlobReduces z u v) :
    BlobReduces z (front ++ u) (front ++ v) := by
  induction h with
  | refl current => exact BlobReduces.refl (front ++ current)
  | step first _ ih =>
      exact BlobReduces.step (blobStep_prefix front first) ih

private theorem nonBlob_eq_self_of_not_mem {z : Nat} :
    ∀ {w : List Nat}, z ∉ w → nonBlob z w = w := by
  intro w absent
  unfold nonBlob
  apply List.filter_eq_self.mpr
  intro letter member
  simp only [decide_eq_true_eq]
  intro equal
  subst letter
  exact absent member

private theorem not_mem_nonBlob (z : Nat) (w : List Nat) :
    z ∉ nonBlob z w := by
  simp [nonBlob]

/-- If `s` is the nonempty suffix after the last `z`, collapse every earlier
`z` into the doubled last site while preserving all non-`z` letters. -/
private theorem blobReduces_closedPrefix (z : Nat) :
    ∀ (p s : List Nat), z ∈ p → s ≠ [] → z ∉ s →
      BlobReduces z (p ++ z :: s) (nonBlob z p ++ z :: z :: s) := by
  intro p
  induction p with
  | nil =>
      intro s present
      simp at present
  | cons head tail ih =>
      intro s present suffixNe suffixFree
      by_cases headEq : head = z
      · subst head
        by_cases tailHas : z ∈ tail
        · have tailReduction := ih s tailHas suffixNe suffixFree
          have lifted := blobReduces_prefix [z] tailReduction
          let B := nonBlob z tail
          have BFree : z ∉ B := by
            exact not_mem_nonBlob z tail
          have cleanup :
              BlobReduces z
                (z :: B ++ z :: z :: s)
                (B ++ z :: z :: s) := by
            by_cases BNe : B = []
            · rw [BNe]
              exact BlobReduces.step (BlobStep.cap (z := z) [] s)
                (BlobReduces.refl _)
            · have hopStep :
                  BlobStep z
                    (z :: B ++ z :: z :: s)
                    (B ++ z :: z :: z :: s) := by
                simpa only [List.nil_append, List.append_assoc] using
                  (BlobStep.hop (z := z) [] B (z :: s) BNe
                    (by simp) BFree)
              have capStep :
                  BlobStep z
                    (B ++ z :: z :: z :: s)
                    (B ++ z :: z :: s) := by
                simpa only [List.append_assoc] using
                  (BlobStep.cap (z := z) B s)
              exact BlobReduces.step hopStep
                (BlobReduces.step capStep (BlobReduces.refl _))
          have combined := blobReduces_trans lifted cleanup
          simpa [B, nonBlob, List.append_assoc] using combined
        · have tailFixed : nonBlob z tail = tail :=
            nonBlob_eq_self_of_not_mem tailHas
          have wholeFixed : nonBlob z (z :: tail) = tail := by
            calc
              nonBlob z (z :: tail) = nonBlob z tail := by
                simp [nonBlob]
              _ = tail := tailFixed
          cases tail with
          | nil =>
              simpa [nonBlob] using
                (BlobReduces.refl (z :: z :: s) :
                  BlobReduces z (z :: z :: s) (z :: z :: s))
          | cons next rest =>
              have hopStep :
                  BlobStep z
                    (z :: (next :: rest) ++ z :: s)
                    ((next :: rest) ++ z :: z :: s) := by
                simpa only [List.nil_append, List.append_assoc] using
                  (BlobStep.hop (z := z) [] (next :: rest) s
                    (by simp) suffixNe tailHas)
              simpa only [List.cons_append, List.append_assoc, wholeFixed] using
                (BlobReduces.step hopStep (BlobReduces.refl _))
      · have tailHas : z ∈ tail := by
          have zNeHead : z ≠ head := Ne.symm headEq
          simpa [zNeHead] using present
        have tailReduction := ih s tailHas suffixNe suffixFree
        have lifted := blobReduces_prefix [head] tailReduction
        simpa [nonBlob, headEq, List.append_assoc] using lifted

private theorem mem_lastOccurrenceTrace_iff (letter : Nat) :
    ∀ letters : List Nat,
      letter ∈ lastOccurrenceTrace letters ↔ letter ∈ letters
  | [] => by simp [lastOccurrenceTrace]
  | head :: tail => by
      by_cases later : head ∈ tail
      · simp only [lastOccurrenceTrace, if_pos later]
        constructor
        · intro member
          exact List.mem_cons_of_mem head
            ((mem_lastOccurrenceTrace_iff letter tail).mp member)
        · intro member
          apply (mem_lastOccurrenceTrace_iff letter tail).mpr
          rcases List.mem_cons.mp member with equal | member
          · simpa [equal] using later
          · exact member
      · simp only [lastOccurrenceTrace, if_neg later, List.mem_cons]
        rw [mem_lastOccurrenceTrace_iff letter tail]

private theorem lastOccurrenceTrace_nodup :
    ∀ letters : List Nat, (lastOccurrenceTrace letters).Nodup
  | [] => by simp [lastOccurrenceTrace]
  | head :: tail => by
      by_cases later : head ∈ tail
      · simpa [lastOccurrenceTrace, later] using
          lastOccurrenceTrace_nodup tail
      · have headAbsent : head ∉ lastOccurrenceTrace tail := by
          simpa [mem_lastOccurrenceTrace_iff head tail] using later
        simp [lastOccurrenceTrace, later, headAbsent,
          lastOccurrenceTrace_nodup tail]

private theorem mem_flatMap_singleOrDouble_iff
    (image : Nat → Nat) (block : Nat → List Nat)
    (shape : ∀ letter,
      block letter = [image letter] ∨
        block letter = [image letter, image letter])
    (target : Nat) :
    ∀ letters : List Nat,
      target ∈ letters.flatMap block ↔ target ∈ letters.map image
  | [] => by simp
  | head :: tail => by
      rcases shape head with single | double
      · simp [List.flatMap_cons, single,
          mem_flatMap_singleOrDouble_iff image block shape target tail]
      · simp [List.flatMap_cons, double,
          mem_flatMap_singleOrDouble_iff image block shape target tail]

/-- Replacing every trace label by one or two adjacent copies does not
change the last-occurrence trace, apart from applying the label map. -/
private theorem lastOccurrenceTrace_flatMap_singleOrDouble
    (image : Nat → Nat) (block : Nat → List Nat)
    (shape : ∀ letter,
      block letter = [image letter] ∨
        block letter = [image letter, image letter]) :
    ∀ letters : List Nat,
      lastOccurrenceTrace (letters.flatMap block) =
        lastOccurrenceTrace (letters.map image)
  | [] => by simp [lastOccurrenceTrace]
  | head :: tail => by
      have tailMembership :=
        mem_flatMap_singleOrDouble_iff image block shape (image head) tail
      have inductionHypothesis :=
        lastOccurrenceTrace_flatMap_singleOrDouble image block shape tail
      rcases shape head with single | double
      · by_cases later : image head ∈ tail.map image
        · have renderedLater : image head ∈ tail.flatMap block :=
            tailMembership.mpr later
          simp [List.flatMap_cons, single, lastOccurrenceTrace,
            later, renderedLater, inductionHypothesis]
        · have renderedAbsent : image head ∉ tail.flatMap block :=
            fun member => later (tailMembership.mp member)
          simp [List.flatMap_cons, single, lastOccurrenceTrace,
            later, renderedAbsent, inductionHypothesis]
      · by_cases later : image head ∈ tail.map image
        · have renderedLater : image head ∈ tail.flatMap block :=
            tailMembership.mpr later
          simp [List.flatMap_cons, double, lastOccurrenceTrace,
            later, renderedLater, inductionHypothesis]
        · have renderedAbsent : image head ∉ tail.flatMap block :=
            fun member => later (tailMembership.mp member)
          simp [List.flatMap_cons, double, lastOccurrenceTrace,
            later, renderedAbsent, inductionHypothesis]

private theorem traceEmit_map_singleOrDouble
    (whole : List Nat) (final : Nat) (image : Nat → Nat)
    (letter : Nat) :
    (traceEmit whole final letter).map image = [image letter] ∨
      (traceEmit whole final letter).map image =
        [image letter, image letter] := by
  by_cases isFinal : letter = final
  · left
    simp [traceEmit, isFinal]
  · by_cases simple : whole.count letter = 1
    · left
      simp [traceEmit, isFinal, simple]
    · right
      simp [traceEmit, isFinal, simple]

private theorem nonBlob_flatMap (z : Nat) (block : Nat → List Nat) :
    ∀ letters : List Nat,
      nonBlob z (letters.flatMap block) =
        letters.flatMap (fun letter => nonBlob z (block letter))
  | [] => by simp [nonBlob]
  | head :: tail => by
      simp only [List.flatMap_cons]
      have appendFilter :
          nonBlob z (block head ++ tail.flatMap block) =
            nonBlob z (block head) ++ nonBlob z (tail.flatMap block) := by
        simp [nonBlob, List.filter_append]
      rw [appendFilter, nonBlob_flatMap z block tail]

private theorem flatMap_if_mem_eq_filter_flatMap
    (kept : List Nat) (block : Nat → List Nat) :
    ∀ letters : List Nat,
      letters.flatMap (fun letter =>
          if letter ∈ kept then block letter else []) =
        (letters.filter (fun letter => letter ∈ kept)).flatMap block
  | [] => by simp
  | head :: tail => by
      by_cases headKept : head ∈ kept
      · simp [List.flatMap_cons, List.filter_cons, headKept,
          flatMap_if_mem_eq_filter_flatMap kept block tail]
      · simp [List.flatMap_cons, List.filter_cons, headKept,
          flatMap_if_mem_eq_filter_flatMap kept block tail]

private theorem lastOccurrenceTrace_map_eq_self_of_fiber
    (image : Nat → Nat) :
    ∀ {letters : List Nat},
      letters.Nodup →
      (∀ x ∈ letters, ∀ y ∈ letters,
        image x = image y → x = y) →
      lastOccurrenceTrace (letters.map image) = letters.map image
  | [], _, _ => by simp [lastOccurrenceTrace]
  | head :: tail, nodup, fiber => by
      have headAbsent : head ∉ tail := (List.nodup_cons.mp nodup).1
      have tailNodup : tail.Nodup := (List.nodup_cons.mp nodup).2
      have imageAbsent : image head ∉ tail.map image := by
        intro member
        rcases List.mem_map.mp member with ⟨other, otherMem, imageEq⟩
        have equal : head = other :=
          fiber head (by simp) other (by simp [otherMem]) imageEq.symm
        subst other
        exact headAbsent otherMem
      have tailFiber :
          ∀ x ∈ tail, ∀ y ∈ tail,
            image x = image y → x = y := by
        intro x xMem y yMem equal
        exact fiber x (by simp [xMem]) y (by simp [yMem]) equal
      have tailTrace :=
        lastOccurrenceTrace_map_eq_self_of_fiber image tailNodup tailFiber
      simp [lastOccurrenceTrace, imageAbsent, tailTrace]

/-- If `pivot` is the last label outside `kept`, mapping all outside labels
to `z` removes exactly the earlier outside labels from the trace. -/
private theorem lastOccurrenceTrace_map_split_lastOutside
    (image : Nat → Nat) (kept : List Nat) (z : Nat) :
    ∀ (before : List Nat) (pivot : Nat) (after : List Nat),
      (before ++ pivot :: after).Nodup →
      pivot ∉ kept →
      (∀ letter, letter ∈ after → letter ∈ kept) →
      (∀ letter, letter ∈ before ++ pivot :: after →
        letter ∉ kept → image letter = z) →
      (∀ x, x ∈ before ++ pivot :: after → x ∈ kept →
        ∀ y, y ∈ before ++ pivot :: after →
          image x = image y → x = y) →
      lastOccurrenceTrace ((before ++ pivot :: after).map image) =
        (before.filter (fun letter => letter ∈ kept)).map image ++
          z :: after.map image
  | [], pivot, after, nodup, pivotOutside, afterKept, outside, fiber => by
      have pivotImage : image pivot = z :=
        outside pivot (by simp) pivotOutside
      have pivotTailNodup : (pivot :: after).Nodup := by
        simpa using nodup
      have pivotAbsent : pivot ∉ after :=
        (List.nodup_cons.mp pivotTailNodup).1
      have afterNodup : after.Nodup :=
        (List.nodup_cons.mp pivotTailNodup).2
      have afterFiber :
          ∀ x ∈ after, ∀ y ∈ after,
            image x = image y → x = y := by
        intro x xMem y yMem equal
        exact fiber x (by simp [xMem]) (afterKept x xMem)
          y (by simp [yMem]) equal
      have afterTrace :=
        lastOccurrenceTrace_map_eq_self_of_fiber image afterNodup afterFiber
      have zAbsent : z ∉ after.map image := by
        intro member
        rcases List.mem_map.mp member with ⟨letter, letterMem, imageEq⟩
        have equal : letter = pivot :=
          fiber letter (by simp [letterMem]) (afterKept letter letterMem)
            pivot (by simp) (imageEq.trans pivotImage.symm)
        subst letter
        exact pivotAbsent letterMem
      simp [pivotImage, lastOccurrenceTrace, zAbsent, afterTrace]
  | head :: tail, pivot, after, nodup, pivotOutside, afterKept,
      outside, fiber => by
      have fullNodup : (head :: (tail ++ pivot :: after)).Nodup := by
        simpa using nodup
      have headAbsent : head ∉ tail ++ pivot :: after :=
        (List.nodup_cons.mp fullNodup).1
      have restNodup : (tail ++ pivot :: after).Nodup :=
        (List.nodup_cons.mp fullNodup).2
      have restOutside :
          ∀ letter, letter ∈ tail ++ pivot :: after →
            letter ∉ kept → image letter = z := by
        intro letter member notKept
        exact outside letter (by simp [member]) notKept
      have restFiber :
          ∀ x, x ∈ tail ++ pivot :: after → x ∈ kept →
            ∀ y, y ∈ tail ++ pivot :: after →
              image x = image y → x = y := by
        intro x xMem xKept y yMem equal
        exact fiber x (by simp [xMem]) xKept y (by simp [yMem]) equal
      have restTrace :=
        lastOccurrenceTrace_map_split_lastOutside image kept z
          tail pivot after restNodup pivotOutside afterKept
          restOutside restFiber
      by_cases headKept : head ∈ kept
      · have imageAbsent : image head ∉
            (tail ++ pivot :: after).map image := by
          intro member
          rcases List.mem_map.mp member with ⟨other, otherMem, imageEq⟩
          have equal : head = other :=
            fiber head (by simp) headKept other (by simp [otherMem])
              imageEq.symm
          subst other
          exact headAbsent otherMem
        change
          (if image head ∈ (tail ++ pivot :: after).map image then
              lastOccurrenceTrace ((tail ++ pivot :: after).map image)
            else image head ::
              lastOccurrenceTrace ((tail ++ pivot :: after).map image)) = _
        rw [if_neg imageAbsent]
        simpa [headKept] using
          congrArg (List.cons (image head)) restTrace
      · have headImage : image head = z :=
          outside head (by simp) headKept
        have pivotImage : image pivot = z :=
          outside pivot (by simp) pivotOutside
        have zLater : z ∈ (tail ++ pivot :: after).map image :=
          List.mem_map.mpr ⟨pivot, by simp, pivotImage⟩
        change
          (if image head ∈ (tail ++ pivot :: after).map image then
              lastOccurrenceTrace ((tail ++ pivot :: after).map image)
            else image head ::
              lastOccurrenceTrace ((tail ++ pivot :: after).map image)) = _
        rw [if_pos (by simpa [headImage] using zLater)]
        simpa [headKept] using restTrace

private theorem exists_split_lastOutside (kept : List Nat) :
    ∀ {letters : List Nat},
      (∃ letter, letter ∈ letters ∧ letter ∉ kept) →
      ∃ before pivot after,
        letters = before ++ pivot :: after ∧
        pivot ∉ kept ∧
        (∀ letter, letter ∈ after → letter ∈ kept)
  | [], existsOutside => by
      rcases existsOutside with ⟨letter, member, _⟩
      simp at member
  | head :: tail, existsOutside => by
      by_cases tailOutside :
          ∃ letter, letter ∈ tail ∧ letter ∉ kept
      · obtain ⟨before, pivot, after, shape, pivotOutside,
            afterKept⟩ := exists_split_lastOutside kept tailOutside
        exact
          ⟨head :: before, pivot, after, by simp [shape],
            pivotOutside, afterKept⟩
      · have tailKept :
            ∀ letter, letter ∈ tail → letter ∈ kept := by
          intro letter member
          apply Classical.byContradiction
          intro notKept
          exact tailOutside ⟨letter, member, notKept⟩
        have headOutside : head ∉ kept := by
          intro headKept
          rcases existsOutside with ⟨letter, member, notKept⟩
          rcases List.mem_cons.mp member with equal | tailMember
          · subst letter
            exact notKept headKept
          · exact notKept (tailKept letter tailMember)
        exact ⟨[], head, tail, by simp, headOutside, tailKept⟩

theorem canonical_blob_reduces :
    ∀ {a K : List Nat} {z : Nat} {σ : Nat → Nat},
      Reduced a → canonicalReduced a = a →
      FaithfulOn σ K a →
      (∀ t, lastLetter? a = some t → t ∈ K) →
      (∀ c, c ∈ a → c ∉ K → σ c = z) →
      z ∉ K.map σ →
      BlobReduces z (a.map σ) (canonicalG4 (a.map σ)) := by
  classical
  intro a K z σ reduced fixed faithful keepsLast mapsOutside fresh
  by_cases sourceEmpty : a = []
  · subst a
    simpa [canonicalG4] using
      (BlobReduces.refl ([] : List Nat) : BlobReduces z [] [])
  · let stem := a.dropLast
    let final := a.getLast sourceEmpty
    have sourceShape : stem ++ [final] = a := by
      simpa [stem, final] using List.dropLast_concat_getLast sourceEmpty
    have finalLast : lastLetter? a = some final := by
      rw [← sourceShape]
      simp [lastLetter?]
    have finalKept : final ∈ K := keepsLast final finalLast
    have finalImageNe : σ final ≠ z := by
      intro equal
      apply fresh
      exact List.mem_map.mpr ⟨final, finalKept, equal⟩
    have zNeFinalImage : z ≠ σ final := Ne.symm finalImageNe
    have preservation := L1_statusPreservation faithful keepsLast
    have countPreserved :
        ∀ c ∈ K, (a.map σ).count (σ c) = a.count c :=
      preservation.1
    rcases faithful with ⟨keptInjective, noCollision⟩

    let labels := lastOccurrenceTrace stem
    let sourceBlock := fun c => (traceEmit a final c).map σ
    let targetBlock := fun c => traceEmit (a.map σ) (σ final) c
    let renderedStem := labels.flatMap sourceBlock

    have sourceCanonical : canonicalG4 a = a :=
      (canonicalReduced_eq reduced).trans fixed
    have renderedSource := canonicalG4_eq_traceRender stem final
    rw [sourceShape] at renderedSource
    have sourceRender :
        a = labels.flatMap (traceEmit a final) ++ [final] := by
      exact sourceCanonical.symm.trans (by
        simpa [labels] using renderedSource)
    have stemRender :
        stem = labels.flatMap (traceEmit a final) := by
      apply List.append_cancel_right
      exact sourceShape.trans sourceRender
    have stemMapped : stem.map σ = renderedStem := by
      rw [stemRender]
      simp [renderedStem, sourceBlock, List.map_flatMap]
    have wordShape :
        a.map σ = renderedStem ++ [σ final] := by
      calc
        a.map σ = (stem ++ [final]).map σ := by rw [sourceShape]
        _ = stem.map σ ++ [σ final] := by simp
        _ = renderedStem ++ [σ final] := by rw [stemMapped]

    have labelMember :
        ∀ c, c ∈ labels → c ∈ a := by
      intro c member
      have stemMember : c ∈ stem :=
        (mem_lastOccurrenceTrace_iff c stem).mp (by
          simpa [labels] using member)
      rw [← sourceShape]
      exact List.mem_append_left [final] stemMember
    have labelsNodup : labels.Nodup := by
      simpa [labels] using lastOccurrenceTrace_nodup stem
    have outsideLabel :
        ∀ c, c ∈ labels → c ∉ K → σ c = z := by
      intro c member notKept
      exact mapsOutside c (labelMember c member) notKept
    have keptImageNe :
        ∀ c, c ∈ labels → c ∈ K → σ c ≠ z := by
      intro c _ kept equal
      apply fresh
      exact List.mem_map.mpr ⟨c, kept, equal⟩
    have keptFiber :
        ∀ x, x ∈ labels → x ∈ K →
          ∀ y, y ∈ labels → σ x = σ y → x = y := by
      intro x xMember xKept y yMember imageEqual
      by_cases yKept : y ∈ K
      · exact keptInjective x xKept y yKept imageEqual
      · exact False.elim
          ((noCollision y (labelMember y yMember) yKept x xKept)
            imageEqual.symm)
    have blockShape :
        ∀ c, sourceBlock c = [σ c] ∨
          sourceBlock c = [σ c, σ c] := by
      intro c
      simpa [sourceBlock] using
        traceEmit_map_singleOrDouble a final σ c
    have keptBlock :
        ∀ c, c ∈ labels → c ∈ K →
          sourceBlock c = targetBlock (σ c) := by
      intro c member kept
      by_cases isFinal : c = final
      · subst c
        simp [sourceBlock, targetBlock, traceEmit]
      · have imageNotFinal : σ c ≠ σ final := by
          intro equal
          exact isFinal
            (keptInjective c kept final finalKept equal)
        have countEqual := countPreserved c kept
        by_cases countOne : a.count c = 1
        · simp [sourceBlock, targetBlock, traceEmit, isFinal,
            imageNotFinal, countEqual, countOne]
        · simp [sourceBlock, targetBlock, traceEmit, isFinal,
            imageNotFinal, countEqual, countOne]
    have traceRendered :
        lastOccurrenceTrace renderedStem =
          lastOccurrenceTrace (labels.map σ) := by
      simpa [renderedStem] using
        lastOccurrenceTrace_flatMap_singleOrDouble
          σ sourceBlock blockShape labels
    have canonicalShape :
        canonicalG4 (a.map σ) =
          (lastOccurrenceTrace renderedStem).flatMap targetBlock ++
            [σ final] := by
      have rendered :=
        canonicalG4_eq_traceRender renderedStem (σ final)
      simpa [targetBlock, wordShape] using rendered

    by_cases hasOutside :
        ∃ c, c ∈ labels ∧ c ∉ K
    · obtain ⟨before, pivot, after, labelShape, pivotOutside,
          afterKept⟩ := exists_split_lastOutside K hasOutside
      have pivotMember : pivot ∈ labels := by
        rw [labelShape]
        simp
      have beforeMember :
          ∀ c, c ∈ before → c ∈ labels := by
        intro c member
        rw [labelShape]
        exact List.mem_append_left _ member
      have afterMember :
          ∀ c, c ∈ after → c ∈ labels := by
        intro c member
        rw [labelShape]
        exact List.mem_append_right before (by simp [member])
      have splitNodup : (before ++ pivot :: after).Nodup := by
        simpa [labelShape] using labelsNodup
      have splitOutside :
          ∀ c, c ∈ before ++ pivot :: after →
            c ∉ K → σ c = z := by
        intro c member notKept
        exact outsideLabel c (by simpa [labelShape] using member) notKept
      have splitFiber :
          ∀ x, x ∈ before ++ pivot :: after → x ∈ K →
            ∀ y, y ∈ before ++ pivot :: after →
              σ x = σ y → x = y := by
        intro x xMember xKept y yMember equal
        exact keptFiber x (by simpa [labelShape] using xMember) xKept
          y (by simpa [labelShape] using yMember) equal
      have mappedTrace :
          lastOccurrenceTrace (labels.map σ) =
            (before.filter (fun c => c ∈ K)).map σ ++
              z :: after.map σ := by
        rw [labelShape]
        exact lastOccurrenceTrace_map_split_lastOutside
          σ K z before pivot after splitNodup pivotOutside
          afterKept splitOutside splitFiber

      let front := before.flatMap sourceBlock
      let suffix := after.flatMap sourceBlock
      have renderedSplit :
          renderedStem = front ++ sourceBlock pivot ++ suffix := by
        simp [renderedStem, front, suffix, labelShape,
          List.flatMap_append, List.flatMap_cons, List.append_assoc]
      have pivotImage : σ pivot = z :=
        outsideLabel pivot pivotMember pivotOutside
      have pivotBlockShape :
          sourceBlock pivot = [z] ∨ sourceBlock pivot = [z, z] := by
        rcases blockShape pivot with single | double
        · left
          simpa [pivotImage] using single
        · right
          simpa [pivotImage] using double

      have sourceBlockFilter :
          ∀ c, c ∈ labels →
            nonBlob z (sourceBlock c) =
              if c ∈ K then targetBlock (σ c) else [] := by
        intro c member
        by_cases kept : c ∈ K
        · rw [if_pos kept, ← keptBlock c member kept]
          have imageNe := keptImageNe c member kept
          rcases blockShape c with single | double
          · simp [single, nonBlob, imageNe]
          · simp [double, nonBlob, imageNe]
        · rw [if_neg kept]
          have imageEq := outsideLabel c member kept
          rcases blockShape c with single | double
          · simp [single, nonBlob, imageEq]
          · simp [double, nonBlob, imageEq]
      have prefixCanonical :
          nonBlob z front =
            ((before.filter (fun c => c ∈ K)).map σ).flatMap
              targetBlock := by
        calc
          nonBlob z front =
              before.flatMap (fun c => nonBlob z (sourceBlock c)) := by
            simpa [front] using nonBlob_flatMap z sourceBlock before
          _ = before.flatMap (fun c =>
                if c ∈ K then targetBlock (σ c) else []) := by
            exact flatMap_congr_of_mem _ _ before (by
              intro c member
              exact sourceBlockFilter c (beforeMember c member))
          _ = (before.filter (fun c => c ∈ K)).flatMap
                (fun c => targetBlock (σ c)) :=
            flatMap_if_mem_eq_filter_flatMap K
              (fun c => targetBlock (σ c)) before
          _ = ((before.filter (fun c => c ∈ K)).map σ).flatMap
                targetBlock := by
            simp [List.flatMap_map]
      have suffixCanonical :
          suffix = (after.map σ).flatMap targetBlock := by
        calc
          suffix = after.flatMap sourceBlock := rfl
          _ = after.flatMap (fun c => targetBlock (σ c)) := by
            exact flatMap_congr_of_mem _ _ after (by
              intro c member
              exact keptBlock c (afterMember c member)
                (afterKept c member))
          _ = (after.map σ).flatMap targetBlock := by
            simp [List.flatMap_map]
      have suffixFree : z ∉ suffix := by
        intro member
        have mappedMember : z ∈ after.map σ :=
          (mem_flatMap_singleOrDouble_iff
            σ sourceBlock blockShape z after).mp (by
              simpa [suffix] using member)
        rcases List.mem_map.mp mappedMember with
          ⟨c, cMember, imageEq⟩
        exact (keptImageNe c (afterMember c cMember)
          (afterKept c cMember)) imageEq
      have suffixCount : suffix.count z = 0 :=
        List.count_eq_zero.mpr suffixFree
      have terminalFree : z ∉ suffix ++ [σ final] := by
        simp [suffixFree, zNeFinalImage]
      have terminalNonempty : suffix ++ [σ final] ≠ [] := by simp

      have canonicalCollapsed :
          canonicalG4 (a.map σ) =
            nonBlob z front ++ targetBlock z ++ suffix ++ [σ final] := by
        calc
          canonicalG4 (a.map σ) =
              (lastOccurrenceTrace renderedStem).flatMap targetBlock ++
                [σ final] := canonicalShape
          _ = (lastOccurrenceTrace (labels.map σ)).flatMap
                targetBlock ++ [σ final] := by rw [traceRendered]
          _ = (((before.filter (fun c => c ∈ K)).map σ ++
                z :: after.map σ).flatMap targetBlock) ++
                [σ final] := by rw [mappedTrace]
          _ = nonBlob z front ++ targetBlock z ++ suffix ++
                [σ final] := by
            simp [List.flatMap_append, prefixCanonical.symm,
              suffixCanonical.symm, List.append_assoc]

      rcases pivotBlockShape with pivotSingle | pivotDouble
      · have wordSingle :
            a.map σ = front ++ z :: (suffix ++ [σ final]) := by
          calc
            a.map σ = renderedStem ++ [σ final] := wordShape
            _ = (front ++ sourceBlock pivot ++ suffix) ++
                [σ final] := by rw [renderedSplit]
            _ = front ++ z :: (suffix ++ [σ final]) := by
              simp [pivotSingle, List.append_assoc]
        by_cases earlier : z ∈ front
        · have prefixPositive : 0 < front.count z :=
            List.count_pos_iff.mpr earlier
          have countAtLeast : 2 ≤ (a.map σ).count z := by
            rw [wordSingle]
            simp [List.count_append, suffixCount, finalImageNe]
            omega
          have countNotOne : (a.map σ).count z ≠ 1 := by omega
          have targetZ : targetBlock z = [z, z] := by
            simp [targetBlock, traceEmit, zNeFinalImage, countNotOne]
          have targetEq :
              canonicalG4
                  (front ++ z :: (suffix ++ [σ final])) =
                nonBlob z front ++ z :: z ::
                  (suffix ++ [σ final]) := by
            rw [← wordSingle]
            simpa [targetZ, List.append_assoc] using canonicalCollapsed
          rw [wordSingle, targetEq]
          exact blobReduces_closedPrefix z front
            (suffix ++ [σ final]) earlier terminalNonempty terminalFree
        · have prefixFixed : nonBlob z front = front :=
            nonBlob_eq_self_of_not_mem earlier
          have countOne : (a.map σ).count z = 1 := by
            rw [wordSingle]
            simp [List.count_append, List.count_eq_zero.mpr earlier,
              suffixCount, finalImageNe]
          have targetZ : targetBlock z = [z] := by
            simp [targetBlock, traceEmit, zNeFinalImage, countOne]
          have targetEq :
              canonicalG4
                  (front ++ z :: (suffix ++ [σ final])) =
                front ++ z :: (suffix ++ [σ final]) := by
            have canonicalAtSource :
                canonicalG4 (a.map σ) =
                  front ++ z :: (suffix ++ [σ final]) := by
              simpa [targetZ, prefixFixed, List.append_assoc] using
                canonicalCollapsed
            exact (congrArg canonicalG4 wordSingle).symm.trans
              canonicalAtSource
          rw [wordSingle, targetEq]
          exact BlobReduces.refl _
      · have wordDouble :
            a.map σ =
              (front ++ [z]) ++ z :: (suffix ++ [σ final]) := by
          calc
            a.map σ = renderedStem ++ [σ final] := wordShape
            _ = (front ++ sourceBlock pivot ++ suffix) ++
                [σ final] := by rw [renderedSplit]
            _ = (front ++ [z]) ++ z :: (suffix ++ [σ final]) := by
              simp [pivotDouble, List.append_assoc]
        have countAtLeast : 2 ≤ (a.map σ).count z := by
          rw [wordDouble]
          simp [List.count_append, suffixCount, finalImageNe]
        have countNotOne : (a.map σ).count z ≠ 1 := by omega
        have targetZ : targetBlock z = [z, z] := by
          simp [targetBlock, traceEmit, zNeFinalImage, countNotOne]
        have targetEq :
            canonicalG4
                ((front ++ [z]) ++ z :: (suffix ++ [σ final])) =
              nonBlob z (front ++ [z]) ++ z :: z ::
                (suffix ++ [σ final]) := by
          rw [← wordDouble]
          simpa [targetZ, nonBlob, List.filter_append,
            List.append_assoc] using canonicalCollapsed
        rw [wordDouble, targetEq]
        exact blobReduces_closedPrefix z (front ++ [z])
          (suffix ++ [σ final]) (by simp) terminalNonempty terminalFree
    · have allKept : ∀ c, c ∈ labels → c ∈ K := by
        intro c member
        apply Classical.byContradiction
        intro notKept
        exact hasOutside ⟨c, member, notKept⟩
      have imageFiber :
          ∀ x ∈ labels, ∀ y ∈ labels,
            σ x = σ y → x = y := by
        intro x xMember y yMember equal
        exact keptFiber x xMember (allKept x xMember)
          y yMember equal
      have mappedTraceSelf :
          lastOccurrenceTrace (labels.map σ) = labels.map σ :=
        lastOccurrenceTrace_map_eq_self_of_fiber
          σ labelsNodup imageFiber
      have renderedTarget :
          renderedStem = (labels.map σ).flatMap targetBlock := by
        calc
          renderedStem = labels.flatMap sourceBlock := rfl
          _ = labels.flatMap (fun c => targetBlock (σ c)) := by
            exact flatMap_congr_of_mem _ _ labels (by
              intro c member
              exact keptBlock c member (allKept c member))
          _ = (labels.map σ).flatMap targetBlock := by
            simp [List.flatMap_map]
      have targetEq : canonicalG4 (a.map σ) = a.map σ := by
        calc
          canonicalG4 (a.map σ) =
              (lastOccurrenceTrace renderedStem).flatMap targetBlock ++
                [σ final] := canonicalShape
          _ = (lastOccurrenceTrace (labels.map σ)).flatMap
                targetBlock ++ [σ final] := by rw [traceRendered]
          _ = (labels.map σ).flatMap targetBlock ++ [σ final] := by
            rw [mappedTraceSelf]
          _ = renderedStem ++ [σ final] := by rw [renderedTarget]
          _ = a.map σ := wordShape.symm
      rw [targetEq]
      exact BlobReduces.refl _

/-! ## The instantiated interface

With the six obligations above, every theorem of the
`CanonicalInterface` section of `Order6LeeLiP2G4MergeCollapse.lean`
specializes to `canonicalG4`; in particular `L5_mergeCollapse` becomes an
unconditional statement about the concrete G4 canonical once holes B, D,
E of the shared module and W1–W6 here are closed.

REMAINING ENDPOINT OBLIGATIONS for S6_8232, S6_8233, S6_10988, S6_10989,
S6_11124, S6_11126 (per member, all mechanical after the above):
1. `Models` of `basisG4` by the member table (decide; 216 + 1296 + 216
   valuations for cap/hop/headDup).
2. The member's four-letter fingerprint data module over the 1,424 G4
   canonicals (emitted by the generalized v3 emitter with per-member
   separator sets; class-specific data stays OUTSIDE this shared module
   per msg-0198).
3. `InvariantSeparation` assembly = merge-collapse (shared) + fingerprint
   Nodup (member data) + `canonicalSound`/`derives_canonical` transport —
   the same chain as the G2 representative.
4. The `BasisFor` endpoint instantiation.
-/

end SemigroupBasis.CoRoots.Order6LeeLiP2G4
