import SemigroupBasis.CoRoots.Order6SporadicSection19PublishedMarkedZones

namespace SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SquareCoalescing

open CrossFactor CrossSweep CrossLeftSweep AnchorPropagation MiddleSweep
  BinaryPowers SquareAlgebra PerfectSweeps FactorContexts OccurrenceWitnesses MarkedZones

/-- The final word is nonempty; an empty gap is not a semigroup unit. -/
def prefixChain (block : Word Nat) : List (List Nat) → Word Nat → Word Nat
  | [], finalWord => finalWord
  | letters :: rest, finalWord =>
      gap block (contextWord letters) ++ prefixChain block rest finalWord

def chain (block : Word Nat) (gaps : List (List Nat)) : Word Nat :=
  prefixChain block gaps block

theorem prefixChain_append (block : Word Nat) (left right : List (List Nat))
    (finalWord : Word Nat) :
    prefixChain block (left ++ right) finalWord =
      prefixChain block left (prefixChain block right finalWord) := by
  induction left with
  | nil => rfl
  | cons letters rest ih =>
      simp only [List.cons_append, prefixChain, ih]

theorem prefixChain_append_word (block : Word Nat) (gaps : List (List Nat))
    (finalWord suffix : Word Nat) :
    prefixChain block gaps (finalWord ++ suffix) =
      prefixChain block gaps finalWord ++ suffix := by
  induction gaps with
  | nil => rfl
  | cons letters rest ih =>
      simp only [prefixChain, ih, Word.append_assoc]

theorem prefixChain_gap (block : Word Nat) (gaps : List (List Nat))
    (finalWord : Word Nat) (tailContext : Option (Word Nat)) :
    prefixChain block gaps (gap finalWord tailContext) =
      gap (prefixChain block gaps finalWord) tailContext := by
  cases tailContext with
  | none => rfl
  | some suffix => exact prefixChain_append_word block gaps finalWord suffix

theorem chain_append_last (block : Word Nat) (gaps : List (List Nat))
    (letters : List Nat) :
    chain block (gaps ++ [letters]) =
      gap (chain block gaps) (contextWord letters) ++ block := by
  change prefixChain block (gaps ++ [letters]) block = _
  rw [prefixChain_append]
  change prefixChain block gaps (gap block (contextWord letters) ++ block) = _
  rw [prefixChain_append_word, prefixChain_gap]
  rfl

theorem renderLeft_chain (block finalWord : Word Nat) (items : List RawSegment) :
    renderLeft (fun _ => block) finalWord (segments items) =
      prefixChain block (items.map Prod.fst) finalWord := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
      change gap block (contextWord item.1) ++
        renderLeft (fun _ => block) finalWord (segments rest) =
        gap block (contextWord item.1) ++ prefixChain block (rest.map Prod.fst) finalWord
      rw [ih]

theorem render_chain (block : Word Nat) (initialGaps : List (List Nat))
    (items : List RawSegment) :
    render (fun _ => block) (chain block initialGaps) (segments items) =
      chain block (initialGaps ++ items.map Prod.fst) := by
  induction items generalizing initialGaps with
  | nil =>
      change chain block initialGaps = chain block (initialGaps ++ [])
      rw [List.append_nil]
  | cons item rest ih =>
      change render (fun _ => block)
        (gap (chain block initialGaps) (contextWord item.1) ++ block) (segments rest) = _
      rw [← chain_append_last, ih]
      simp only [List.map_cons, List.append_assoc, List.cons_append, List.nil_append]

theorem middle_chain (block : Word Nat) (items : List RawSegment)
    (trailing : List Nat) :
    gap block
      (joinGap (joinGap none (foldGap (fun _ => block) (segments items)))
        (contextWord trailing)) ++ block =
      chain block (items.map Prod.fst ++ [trailing]) := by
  have rendered : render (fun _ => block) block (segments items) =
      chain block (items.map Prod.fst) := by
    simpa only [chain, prefixChain, List.nil_append] using render_chain block [] items
  rw [chain_append_last]
  change gap block (joinGap (foldGap (fun _ => block) (segments items))
    (contextWord trailing)) ++ block = _
  rw [gap_join, ← render_foldGap, rendered]

/-- The actual codecs supply every gap, including the last middle gap. -/
def actualGaps (x y : Nat) (before middle after : List Nat) : List (List Nat) :=
  ((encodeLeft x y before).2.map Prod.fst ++
    ((encodeRight x y middle).1.map Prod.fst ++ [(encodeRight x y middle).2])) ++
      (encodeRight x y after).1.map Prod.fst

theorem squareBlocks_as_chain (x y : Nat) (before middle after : List Nat) :
    squareBlocks x y before middle after =
      Context.frame (contextWord (encodeLeft x y before).1)
        (contextWord (encodeRight x y after).2)
        (chain (square (Word.singleton x) (Word.singleton y))
          (actualGaps x y before middle after)) := by
  unfold squareBlocks
  rw [middle_chain, renderLeft_chain]
  have leftPart :
      prefixChain (square (Word.singleton x) (Word.singleton y))
        ((encodeLeft x y before).2.map Prod.fst)
        (chain (square (Word.singleton x) (Word.singleton y))
          ((encodeRight x y middle).1.map Prod.fst ++ [(encodeRight x y middle).2])) =
      chain (square (Word.singleton x) (Word.singleton y))
        ((encodeLeft x y before).2.map Prod.fst ++
          ((encodeRight x y middle).1.map Prod.fst ++ [(encodeRight x y middle).2])) :=
    (prefixChain_append _ _ _ _).symm
  rw [leftPart, render_chain]
  rfl

/-- Delete only empty separators, retaining the exact other lists in order. -/
def keepNonempty : List (List Nat) → List (List Nat)
  | [] => []
  | [] :: rest => keepNonempty rest
  | (first :: later) :: rest => (first :: later) :: keepNonempty rest

theorem keepNonempty_append (left right : List (List Nat)) :
    keepNonempty (left ++ right) = keepNonempty left ++ keepNonempty right := by
  induction left with
  | nil => rfl
  | cons letters rest ih =>
      cases letters <;> simp only [List.cons_append, keepNonempty, ih]

theorem keepNonempty_idempotent (gaps : List (List Nat)) :
    keepNonempty (keepNonempty gaps) = keepNonempty gaps := by
  induction gaps with
  | nil => rfl
  | cons letters rest ih =>
      cases letters <;> simp only [keepNonempty, ih]

theorem keepNonempty_member (gaps : List (List Nat)) (letters : List Nat)
    (member : letters ∈ keepNonempty gaps) : letters ∈ gaps ∧ letters ≠ [] := by
  induction gaps with
  | nil => cases member
  | cons next rest ih =>
      cases next with
      | nil =>
          have retained := ih member
          exact ⟨List.mem_cons.mpr (Or.inr retained.1), retained.2⟩
      | cons first later =>
          change letters ∈ (first :: later) :: keepNonempty rest at member
          rcases List.mem_cons.mp member with equal | inside
          · subst letters
            exact ⟨List.mem_cons.mpr (Or.inl rfl), by intro impossible; cases impossible⟩
          · have retained := ih inside
            exact ⟨List.mem_cons.mpr (Or.inr retained.1), retained.2⟩

theorem square_prefix_collapse (u v : Word Nat) (gaps : List (List Nat)) :
    Derives basis (square u v ++ chain (square u v) gaps) (chain (square u v) gaps) := by
  cases gaps with
  | nil => exact square_idempotent u v
  | cons letters rest =>
      have step := Derives.appendRight
        (gap_derives (square_idempotent u v) (contextWord letters))
        (chain (square u v) rest)
      simpa only [chain, prefixChain, gap_append, Word.append_assoc] using step

theorem chain_coalesce (u v : Word Nat) (gaps : List (List Nat)) :
    Derives basis (chain (square u v) gaps)
      (chain (square u v) (keepNonempty gaps)) := by
  induction gaps with
  | nil => exact Derives.refl _
  | cons letters rest ih =>
      cases letters with
      | nil =>
          change Derives basis (square u v ++ chain (square u v) rest)
            (chain (square u v) (keepNonempty rest))
          exact (Derives.prepend (square u v) ih).trans
            (square_prefix_collapse u v (keepNonempty rest))
      | cons first later =>
          exact Derives.prepend (gap (square u v) (some ⟨first, later⟩)) ih

def coalescedSquareBlocks (x y : Nat) (before middle after : List Nat) : Word Nat :=
  Context.frame (contextWord (encodeLeft x y before).1)
    (contextWord (encodeRight x y after).2)
    (chain (square (Word.singleton x) (Word.singleton y))
      (keepNonempty (actualGaps x y before middle after)))

theorem square_blocks_coalesce (x y : Nat) (before middle after : List Nat) :
    Derives basis (squareBlocks x y before middle after)
      (coalescedSquareBlocks x y before middle after) := by
  rw [squareBlocks_as_chain]
  exact Context.frame_derives
    (chain_coalesce (Word.singleton x) (Word.singleton y) (actualGaps x y before middle after))
    (contextWord (encodeLeft x y before).1) (contextWord (encodeRight x y after).2)

theorem arbitrary_anchor_coalesced (x y : Nat) (before middle after : List Nat) :
    Derives basis
      (Context.frame (contextWord before) (contextWord after)
        (anchor (Word.singleton x) (Word.singleton y) (contextWord middle)))
      (coalescedSquareBlocks x y before middle after) :=
  (arbitrary_anchor_square_blocks x y before middle after).trans
    (square_blocks_coalesce x y before middle after)

theorem anchor_seed_coalesced (x y : Nat) (word : Word Nat)
    (seed : HasAnchorSeed x y word) :
    ∃ before middle after : List Nat,
      Derives basis word (coalescedSquareBlocks x y before middle after) := by
  obtain ⟨before, middle, after, step⟩ := anchor_seed_square_blocks x y word seed
  exact ⟨before, middle, after, step.trans (square_blocks_coalesce x y before middle after)⟩

theorem related_coalesced (x y : Nat) (word : Word Nat)
    (different : x ≠ y) (xRepeated : 2 ≤ word.toList.count x)
    (yRepeated : 2 ≤ word.toList.count y) (related : PairRelated x y word.toList) :
    (∃ before middle after : List Nat,
      Derives basis word (coalescedSquareBlocks x y before middle after)) ∨
    (∃ before middle after : List Nat,
      Derives basis word (coalescedSquareBlocks y x before middle after)) := by
  rcases related_has_anchor_seed x y word different xRepeated yRepeated related with forward | backward
  · exact Or.inl (anchor_seed_coalesced x y word forward)
  · exact Or.inr (anchor_seed_coalesced y x word backward)

theorem clean_map_outside (x y : Nat) (items : List RawSegment)
    (clean : Clean x y items) (letters : List Nat)
    (member : letters ∈ items.map Prod.fst) : Outside x y letters := by
  obtain ⟨item, inside, equal⟩ := List.mem_map.mp member
  exact equal ▸ clean item inside

theorem actual_gaps_outside (x y : Nat) (before middle after letters : List Nat)
    (member : letters ∈ actualGaps x y before middle after) : Outside x y letters := by
  rcases List.mem_append.mp member with firstTwo | rightPart
  · rcases List.mem_append.mp firstTwo with leftPart | middlePart
    · exact clean_map_outside x y _ (left_clean x y before).2 letters leftPart
    · rcases List.mem_append.mp middlePart with marked | trailing
      · exact clean_map_outside x y _ (right_clean x y middle).1 letters marked
      · have equal := List.mem_singleton.mp trailing
        exact equal ▸ (right_clean x y middle).2
  · exact clean_map_outside x y _ (right_clean x y after).1 letters rightPart

/-- Exterior contexts and every retained separator are proved complementary.
No separator nonemptiness or marked-rendering premise is supplied by a caller. -/
theorem coalesced_boundaries (x y : Nat) (before middle after : List Nat) :
    Outside x y (encodeLeft x y before).1 ∧
    Outside x y (encodeRight x y after).2 ∧
    (∀ letters ∈ keepNonempty (actualGaps x y before middle after),
      letters ≠ [] ∧ Outside x y letters) := by
  refine ⟨(left_clean x y before).1, (right_clean x y after).2, ?_⟩
  intro letters member
  have retained := keepNonempty_member (actualGaps x y before middle after) letters member
  exact ⟨retained.2, actual_gaps_outside x y before middle after letters retained.1⟩

end SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SquareCoalescing

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SquareCoalescing.prefixChain_append
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SquareCoalescing.prefixChain_append_word
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SquareCoalescing.prefixChain_gap
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SquareCoalescing.chain_append_last
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SquareCoalescing.renderLeft_chain
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SquareCoalescing.render_chain
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SquareCoalescing.middle_chain
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SquareCoalescing.squareBlocks_as_chain
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SquareCoalescing.keepNonempty_append
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SquareCoalescing.keepNonempty_idempotent
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SquareCoalescing.keepNonempty_member
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SquareCoalescing.square_prefix_collapse
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SquareCoalescing.chain_coalesce
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SquareCoalescing.square_blocks_coalesce
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SquareCoalescing.arbitrary_anchor_coalesced
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SquareCoalescing.anchor_seed_coalesced
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SquareCoalescing.related_coalesced
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SquareCoalescing.clean_map_outside
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SquareCoalescing.actual_gaps_outside
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SquareCoalescing.coalesced_boundaries
