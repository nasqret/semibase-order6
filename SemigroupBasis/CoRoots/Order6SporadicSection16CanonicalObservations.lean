import SemigroupBasis.CoRoots.Order6SporadicSection16CanonicalShape

/-! Recover the canonical marker bits from the actual simple-final and FSS
observations. The unique-occurrence boundary is proved at the List/Word
interface before applying it to the canonical renderer. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection16.CanonicalObservations

open SemigroupBasis CanonicalCounts SimplePairExclusion

theorem source_absent_before (letters stem suffix : List Nat) (source : Nat)
    (one : letters.count source = 1) (split : letters = stem ++ source :: suffix) :
    source ∉ stem := by
  rw [split, List.count_append, List.count_cons_self] at one
  exact List.count_eq_zero.mp (by omega)

theorem unique_source_suffix (letters : List Nat) (source : Nat)
    (one : letters.count source = 1) (left right xs ys : List Nat)
    (leftSplit : letters = left ++ source :: xs)
    (rightSplit : letters = right ++ source :: ys) : xs = ys := by
  have leftAbsent := source_absent_before letters left xs source one leftSplit
  have rightAbsent := source_absent_before letters right ys source one rightSplit
  have result := CanonicalShape.split_at_first_failure (fun x => x ≠ source)
    left right source source xs ys (leftSplit.symm.trans rightSplit)
    (fun x member same => leftAbsent (same ▸ member))
    (fun x member same => rightAbsent (same ▸ member))
    (fun different => different rfl) (fun different => different rfl)
  exact result.2.2

theorem next_pair_iff (word : Word Nat) (source target next : Nat)
    (stem suffix : List Nat) (one : word.toList.count source = 1)
    (split : word.toList = stem ++ source :: next :: suffix) :
    (source,target) ∈ word.adjacentPairs ↔ next = target := by
  constructor
  · intro edge
    obtain ⟨before,after,other⟩ := (mem_adjacentPairs_iff_exists_split source target word).mp edge
    have tails := unique_source_suffix word.toList source one stem before
      (next :: suffix) (target :: after) split other
    exact (List.cons.inj tails).1
  · intro equal
    subst target
    exact (mem_adjacentPairs_iff_exists_split source next word).mpr ⟨stem,suffix,split⟩

theorem getLastD_append_nonempty (stem : List Nat) (first previous : Nat) (suffix : List Nat) :
    (stem ++ first :: suffix).getLastD previous = suffix.getLastD first := by
  induction stem generalizing previous with
  | nil => simp only [List.nil_append, List.getLastD_cons]
  | cons x rest ih =>
      simp only [List.cons_append, List.getLastD_cons]
      exact ih x

theorem toList_getLastD (word : Word Nat) (previous : Nat) :
    word.toList.getLastD previous = word.final := by
  cases word
  simp only [Word.toList, List.getLastD_cons, Word.final]

def blockTail (anchor : Nat) (block : CanonicalBlock) : List Nat :=
  (if block.doubled then [block.letter] else []) ++
    (if block.markerAfter then [anchor,anchor] else [])

theorem renderBlock_eq_cons (anchor : Nat) (block : CanonicalBlock) :
    renderBlock anchor block = block.letter :: blockTail anchor block := by
  cases doubled : block.doubled <;> simp [renderBlock, blockTail, doubled]

theorem renderBlock_simple (anchor : Nat) (block : CanonicalBlock) (simple : block.doubled = false) :
    renderBlock anchor block = block.letter :: (if block.markerAfter then [anchor,anchor] else []) := by
  simp [renderBlock, simple]

theorem neighboring_pair_iff (data : CanonicalData) (wellFormed : CanonicalWellFormed data)
    (before : List CanonicalBlock) (first second : CanonicalBlock) (after : List CanonicalBlock)
    (split : data.blocks = before ++ first :: second :: after) (simple : first.doubled = false) :
    (first.letter,second.letter) ∈ (canonicalWord data).adjacentPairs ↔ first.markerAfter = false := by
  have firstMem : first ∈ data.blocks := by rw [split]; simp
  have secondMem : second ∈ data.blocks := by rw [split]; simp
  have one : (canonicalWord data).toList.count first.letter = 1 := by
    rw [canonicalWord_toList]
    exact (simple_block_iff data wellFormed first firstMem).mpr simple
  have nextFresh : data.anchor ≠ second.letter := (block_freshness data wellFormed second secondMem).2.symm
  let stem := data.initial ++ [data.anchor,data.anchor] ++ renderBlocks data.anchor before
  have rendered : (canonicalWord data).toList = stem ++ renderBlock data.anchor first ++
      renderBlock data.anchor second ++ renderBlocks data.anchor after := by
    simp only [canonicalWord_toList, renderCanonical, split, stem, renderBlocks,
      List.flatMap_append, List.flatMap_cons, List.append_assoc]
  cases marker : first.markerAfter with
  | false =>
      have nextSplit : (canonicalWord data).toList = stem ++ first.letter :: second.letter ::
          (blockTail data.anchor second ++ renderBlocks data.anchor after) := by
        rw [rendered, renderBlock_simple data.anchor first simple, renderBlock_eq_cons data.anchor second]
        simp only [marker, Bool.false_eq_true, if_false, List.append_assoc, List.cons_append, List.nil_append]
      have edge := next_pair_iff (canonicalWord data) first.letter second.letter second.letter stem
        (blockTail data.anchor second ++ renderBlocks data.anchor after) one nextSplit
      simpa [marker] using edge
  | true =>
      have nextSplit : (canonicalWord data).toList = stem ++ first.letter :: data.anchor ::
          (data.anchor :: (renderBlock data.anchor second ++ renderBlocks data.anchor after)) := by
        rw [rendered, renderBlock_simple data.anchor first simple]
        simp only [marker, if_true, List.append_assoc, List.cons_append, List.nil_append]
      have edge := next_pair_iff (canonicalWord data) first.letter second.letter data.anchor stem
        (data.anchor :: (renderBlock data.anchor second ++ renderBlocks data.anchor after)) one nextSplit
      simpa [marker, nextFresh] using edge

theorem neighboring_simple_pair_iff (data : CanonicalData) (wellFormed : CanonicalWellFormed data)
    (before : List CanonicalBlock) (first second : CanonicalBlock) (after : List CanonicalBlock)
    (split : data.blocks = before ++ first :: second :: after)
    (firstSimple : first.doubled = false) (secondSimple : second.doubled = false) :
    S5_107.SimpleAdjacent (canonicalWord data) first.letter second.letter ↔ first.markerAfter = false := by
  have firstMem : first ∈ data.blocks := by rw [split]; simp
  have secondMem : second ∈ data.blocks := by rw [split]; simp
  have firstOne : S5_107.SimpleIn (canonicalWord data) first.letter := by
    change (canonicalWord data).toList.count first.letter = 1
    rw [canonicalWord_toList]
    exact (simple_block_iff data wellFormed first firstMem).mpr firstSimple
  have secondOne : S5_107.SimpleIn (canonicalWord data) second.letter := by
    change (canonicalWord data).toList.count second.letter = 1
    rw [canonicalWord_toList]
    exact (simple_block_iff data wellFormed second secondMem).mpr secondSimple
  have edge := neighboring_pair_iff data wellFormed before first second after split firstSimple
  exact ⟨fun h => edge.mp h.2.2, fun h => ⟨firstOne,secondOne,edge.mpr h⟩⟩

theorem final_of_terminal_block (data : CanonicalData)
    (before : List CanonicalBlock) (last : CanonicalBlock)
    (split : data.blocks = before ++ [last]) :
    (canonicalWord data).final = if last.markerAfter then data.anchor else last.letter := by
  let stem := data.initial ++ [data.anchor,data.anchor] ++ renderBlocks data.anchor before
  have rendered : (canonicalWord data).toList = stem ++ renderBlock data.anchor last := by
    simp only [canonicalWord_toList, renderCanonical, split, stem, renderBlocks,
      List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]
  calc
    (canonicalWord data).final = (stem ++ renderBlock data.anchor last).getLastD data.anchor := by
      rw [← toList_getLastD (canonicalWord data) data.anchor, rendered]
    _ = if last.markerAfter then data.anchor else last.letter := by
      rw [renderBlock_eq_cons, getLastD_append_nonempty]
      cases doubled : last.doubled <;> cases marker : last.markerAfter <;>
        simp [blockTail, doubled, marker]

theorem terminal_simple_iff (data : CanonicalData) (wellFormed : CanonicalWellFormed data)
    (before : List CanonicalBlock) (last : CanonicalBlock)
    (split : data.blocks = before ++ [last]) (simple : last.doubled = false) :
    S5_107.SimpleFinal (canonicalWord data) last.letter ↔ last.markerAfter = false := by
  have member : last ∈ data.blocks := by rw [split]; simp
  have one : S5_107.SimpleIn (canonicalWord data) last.letter := by
    change (canonicalWord data).toList.count last.letter = 1
    rw [canonicalWord_toList]
    exact (simple_block_iff data wellFormed last member).mpr simple
  have fresh : data.anchor ≠ last.letter := (block_freshness data wellFormed last member).2.symm
  change (S5_107.SimpleIn (canonicalWord data) last.letter ∧ (canonicalWord data).final = last.letter) ↔ _
  rw [final_of_terminal_block data before last split]
  cases marker : last.markerAfter <;> simp [marker, one, fresh]

theorem admissible_suffix (before rest : List CanonicalBlock)
    (admissible : AdmissibleMarkers (before ++ rest)) : AdmissibleMarkers rest := by
  induction before with
  | nil => exact admissible
  | cons first before ih => exact ih admissible.2

#print axioms unique_source_suffix
#print axioms next_pair_iff
#print axioms neighboring_simple_pair_iff
#print axioms final_of_terminal_block
#print axioms terminal_simple_iff
#print axioms admissible_suffix

end SemigroupBasis.CoRoots.Order6SporadicSection16.CanonicalObservations
