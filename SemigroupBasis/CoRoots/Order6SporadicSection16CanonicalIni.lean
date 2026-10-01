import SemigroupBasis.CoRoots.Order6SporadicSection16CanonicalForm
import SemigroupBasis.Examples.LeftRegularBandThree

/-! Structural first-occurrence facts for the actual Section16 canonical
renderer. These connect semantic ini equality to the distinct label list;
they do not assume or assert the remaining canonical uniqueness theorem. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection16.CanonicalIni

open SemigroupBasis SemigroupBasis.Examples

theorem ini_mem {letter : Nat} {letters : List Nat}
    (member : letter ∈ firstOccurrenceSequence letters) : letter ∈ letters := by
  induction letters with
  | nil => simp [firstOccurrenceSequence] at member
  | cons first rest ih =>
      simp only [firstOccurrenceSequence, List.mem_cons, List.mem_filter] at member
      rcases member with same | ⟨later, _⟩
      · exact List.mem_cons.mpr (Or.inl same)
      · exact List.mem_cons_of_mem first (ih later)

theorem filter_ne_self (letter : Nat) : ∀ letters : List Nat,
    letter ∉ letters → letters.filter (fun x => decide (x ≠ letter)) = letters
  | [], _ => rfl
  | first :: rest, absent => by
      have different : first ≠ letter := by
        intro same
        apply absent
        simp [same]
      have tailAbsent : letter ∉ rest := fun member => absent (List.Mem.tail first member)
      have kept : decide (first ≠ letter) = true := by simp [different]
      rw [List.filter_cons, kept]
      exact congrArg (List.cons first) (filter_ne_self letter rest tailAbsent)

theorem ini_cons_fresh (letter : Nat) (letters : List Nat) (fresh : letter ∉ letters) :
    firstOccurrenceSequence (letter :: letters) = letter :: firstOccurrenceSequence letters := by
  rw [firstOccurrenceSequence, filter_ne_self letter _ (fun member => fresh (ini_mem member))]

theorem ini_filter (predicate : Nat → Bool) : ∀ letters : List Nat,
    firstOccurrenceSequence (letters.filter predicate) = (firstOccurrenceSequence letters).filter predicate
  | [] => rfl
  | first :: rest => by
      by_cases kept : predicate first = true
      · simp [firstOccurrenceSequence, kept, ini_filter predicate rest,
          List.filter_filter, Bool.and_comm]
      · have dropped : predicate first = false := Bool.eq_false_iff.mpr kept
        have squash : (fun x => decide (x ≠ first) && predicate x) = predicate := by
          funext x
          by_cases same : x = first
          · subst x; simp [dropped]
          · simp [same]
        have squash' : (fun x => predicate x && decide (x ≠ first)) = predicate := by
          funext x
          rw [Bool.and_comm]
          exact congrFun squash x
        change firstOccurrenceSequence ((first :: rest).filter predicate) =
          (first :: (firstOccurrenceSequence rest).filter (fun x => decide (x ≠ first))).filter predicate
        rw [List.filter_cons, dropped, List.filter_cons, dropped]
        change firstOccurrenceSequence (rest.filter predicate) =
          ((firstOccurrenceSequence rest).filter (fun x => decide (x ≠ first))).filter predicate
        rw [ini_filter predicate rest, List.filter_filter, squash']

theorem ini_double (letter : Nat) (letters : List Nat) :
    firstOccurrenceSequence (letter :: letter :: letters) = firstOccurrenceSequence (letter :: letters) := by
  simp [firstOccurrenceSequence, List.filter_filter, Bool.and_self]

theorem ini_prefix (suffix : List Nat) : ∀ stem : List Nat,
    stem.Nodup → (∀ x ∈ stem, x ∉ suffix) →
      firstOccurrenceSequence (stem ++ suffix) = stem ++ firstOccurrenceSequence suffix
  | [], _, _ => rfl
  | first :: rest, distinct, disjoint => by
      have firstFresh : first ∉ rest ++ suffix := by
        intro member
        rcases List.mem_append.mp member with inRest | inSuffix
        · exact (List.nodup_cons.mp distinct).1 inRest
        · exact disjoint first (List.Mem.head rest) inSuffix
      simp only [List.cons_append]
      rw [ini_cons_fresh first (rest ++ suffix) firstFresh,
        ini_prefix suffix rest (List.nodup_cons.mp distinct).2
          (fun x member => disjoint x (List.Mem.tail first member))]

def bareBlocks (blocks : List CanonicalBlock) : List Nat :=
  blocks.flatMap fun block => if block.doubled then [block.letter,block.letter] else [block.letter]

theorem bareBlocks_cons (first : CanonicalBlock) (rest : List CanonicalBlock) :
    bareBlocks (first :: rest) =
      (if first.doubled then [first.letter,first.letter] else [first.letter]) ++ bareBlocks rest := rfl

theorem renderBlocks_cons (anchor : Nat) (first : CanonicalBlock) (rest : List CanonicalBlock) :
    renderBlocks anchor (first :: rest) = renderBlock anchor first ++ renderBlocks anchor rest := rfl

theorem renderBlock_mem (anchor x : Nat) (block : CanonicalBlock)
    (member : x ∈ renderBlock anchor block) : x = block.letter ∨ x = anchor := by
  cases doubled : block.doubled <;> cases marker : block.markerAfter <;>
    simp [renderBlock, doubled, marker] at member <;> simp_all

theorem renderBlocks_mem (anchor x : Nat) (blocks : List CanonicalBlock)
    (member : x ∈ renderBlocks anchor blocks) :
    x = anchor ∨ x ∈ blocks.map CanonicalBlock.letter := by
  obtain ⟨block, inBlocks, inBlock⟩ := List.mem_flatMap.mp member
  rcases renderBlock_mem anchor x block inBlock with equal | equal
  · exact Or.inr (List.mem_map.mpr ⟨block,inBlocks,equal.symm⟩)
  · exact Or.inl equal

theorem filter_anchor (anchor : Nat) : ∀ blocks : List CanonicalBlock,
    anchor ∉ blocks.map CanonicalBlock.letter →
      (renderBlocks anchor blocks).filter (fun x => decide (x ≠ anchor)) = bareBlocks blocks
  | [], _ => rfl
  | first :: rest, absent => by
      have different : first.letter ≠ anchor := by
        intro same
        apply absent
        simp [same]
      have tailAbsent : anchor ∉ rest.map CanonicalBlock.letter := by
        intro member
        exact absent (List.mem_cons_of_mem first.letter member)
      rw [renderBlocks_cons, List.filter_append, filter_anchor anchor rest tailAbsent]
      cases doubled : first.doubled <;> cases marker : first.markerAfter <;>
        simp [bareBlocks, renderBlock, doubled, marker, different]

theorem ini_bareBlocks : ∀ blocks : List CanonicalBlock,
    (blocks.map CanonicalBlock.letter).Nodup →
      firstOccurrenceSequence (bareBlocks blocks) = blocks.map CanonicalBlock.letter
  | [], _ => rfl
  | first :: rest, distinct => by
      have nodup : (first.letter :: rest.map CanonicalBlock.letter).Nodup := distinct
      have tailIni := ini_bareBlocks rest (List.nodup_cons.mp nodup).2
      have filtered := filter_ne_self first.letter (rest.map CanonicalBlock.letter)
        (List.nodup_cons.mp nodup).1
      rw [bareBlocks_cons]
      cases doubled : first.doubled
      · change firstOccurrenceSequence (first.letter :: bareBlocks rest) = first.letter :: rest.map CanonicalBlock.letter
        rw [firstOccurrenceSequence, tailIni, filtered]
      · change firstOccurrenceSequence (first.letter :: first.letter :: bareBlocks rest) = first.letter :: rest.map CanonicalBlock.letter
        rw [ini_double, firstOccurrenceSequence, tailIni, filtered]

theorem ini_anchor_blocks (anchor : Nat) (blocks : List CanonicalBlock)
    (distinct : (blocks.map CanonicalBlock.letter).Nodup)
    (anchorAbsent : anchor ∉ blocks.map CanonicalBlock.letter) :
    firstOccurrenceSequence ([anchor,anchor] ++ renderBlocks anchor blocks) =
      anchor :: blocks.map CanonicalBlock.letter := by
  change firstOccurrenceSequence (anchor :: anchor :: renderBlocks anchor blocks) = _
  rw [ini_double, firstOccurrenceSequence,
      ← ini_filter (fun x => decide (x ≠ anchor)), filter_anchor anchor blocks anchorAbsent,
      ini_bareBlocks blocks distinct]

theorem ini_renderCanonical (data : CanonicalData) (wellFormed : CanonicalWellFormed data) :
    firstOccurrenceSequence (renderCanonical data) = canonicalLabels data := by
  have distinct : (data.initial ++ data.anchor :: data.blocks.map CanonicalBlock.letter).Nodup := by
    simpa [canonicalLabels, List.append_assoc] using wellFormed.1
  have parts := List.nodup_append.mp distinct
  have anchorParts := List.nodup_cons.mp parts.2.1
  have disjoint : ∀ x ∈ data.initial, x ∉ [data.anchor,data.anchor] ++ renderBlocks data.anchor data.blocks := by
    intro x inInitial member
    have inLabels : x ∈ data.anchor :: data.blocks.map CanonicalBlock.letter := by
      rcases List.mem_append.mp member with inAnchor | inBlocks
      · have equal : x = data.anchor := by simpa using inAnchor
        exact List.mem_cons.mpr (Or.inl equal)
      · rcases renderBlocks_mem data.anchor x data.blocks inBlocks with equal | later
        · exact List.mem_cons.mpr (Or.inl equal)
        · exact List.mem_cons_of_mem data.anchor later
    exact parts.2.2 x inInitial x inLabels rfl
  unfold renderCanonical canonicalLabels
  rw [List.append_assoc, ini_prefix _ data.initial parts.1 disjoint,
    ini_anchor_blocks data.anchor data.blocks anchorParts.2 anchorParts.1]
  simp [List.append_assoc]

#print axioms ini_filter
#print axioms ini_bareBlocks
#print axioms ini_anchor_blocks
#print axioms ini_renderCanonical

end SemigroupBasis.CoRoots.Order6SporadicSection16.CanonicalIni
