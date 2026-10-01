import SemigroupBasis.CoRoots.Order6SporadicSection19PublishedConnectedNormalization

namespace SemigroupBasis.CoRoots.Order6SporadicSection19.Published.CanonicalPresentation

open MaximalFactors FactorBoundaries BlockAlignment MacroWitnesses RootFamily
open RootBlockPartition SimpleFactorInvariant MaximalSimpleAlignment
open TerminalRepeatBoundary ConnectedTerminalEndpoints ConnectedNormalization

/-- A literal optional gap, retained as nonempty factors, followed by one
root square. Its printed gap is `flatten entry.1`, not a support set. -/
abbrev Chunk := List (Word Nat) × Word Nat

def RootSquare (roots : List (Word Nat)) (piece : Word Nat) : Prop :=
  ∃ root ∈ roots, piece = root ++ root

def AllOutside (roots : List (Word Nat)) (pieces : List (Word Nat)) : Prop :=
  ∀ piece ∈ pieces, Outside roots piece

def GoodChunks (roots : List (Word Nat)) (chunks : List Chunk) : Prop :=
  ∀ entry ∈ chunks, AllOutside roots entry.1 ∧ RootSquare roots entry.2

def expand : List Chunk → List (Word Nat)
  | [] => []
  | (gap, square) :: rest => gap ++ square :: expand rest

def render : List Chunk → List Nat
  | [] => []
  | (gap, square) :: rest => flatten gap ++ (square.toList ++ render rest)

/-- This is printed condition IV with an explicit earlier-prefix witness,
including the initial square. No finite index bound is imposed. -/
def RepeatGaps (first : Word Nat) (chunks : List Chunk) : Prop :=
  ∀ (before : List Chunk) (gap : List (Word Nat)) (square : Word Nat)
    (after : List Chunk),
    chunks = before ++ (gap, square) :: after →
    square ∈ first :: before.map Prod.snd → flatten gap ≠ []

theorem expand_append (before after : List Chunk) :
    expand (before ++ after) = expand before ++ expand after := by
  induction before with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨gap, square⟩
    simp only [List.cons_append, expand, ih, List.append_assoc]

theorem flatten_expand (chunks : List Chunk) :
    flatten (expand chunks) = render chunks := by
  induction chunks with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨gap, square⟩
    simp only [expand, render, FactorBoundaries.flatten_append, flatten, ih]

/-- Pack actual factors without deleting, permuting or merging their letters.
The leftover is exactly a trailing outside gap, if one exists. -/
theorem pack_parts (roots : List (Word Nat)) :
    ∀ pieces : List (Word Nat),
      (∀ piece ∈ pieces, RootPiece roots piece) →
      ∃ chunks : List Chunk, ∃ trailing : List (Word Nat),
        pieces = expand chunks ++ trailing ∧ GoodChunks roots chunks ∧
          AllOutside roots trailing := by
  intro pieces
  induction pieces with
  | nil =>
    intro _kinds
    refine ⟨[], [], rfl, ?_, ?_⟩
    · intro entry member
      cases member
    · intro part member
      cases member
  | cons part rest ih =>
    intro kinds
    have restKinds : ∀ piece ∈ rest, RootPiece roots piece := by
      intro piece member
      exact kinds piece (List.mem_cons.mpr (Or.inr member))
    obtain ⟨chunks, trailing, trace, good, trailingGood⟩ := ih restKinds
    rcases kinds part (List.mem_cons.mpr (Or.inl rfl)) with square | outside
    · refine ⟨([], part) :: chunks, trailing, ?_, ?_, trailingGood⟩
      · change part :: rest = part :: (expand chunks ++ trailing)
        rw [trace]
      · intro entry member
        rcases List.mem_cons.mp member with equal | later
        · subst entry
          refine ⟨?_, square⟩
          intro piece inGap
          cases inGap
        · exact good entry later
    · cases chunks with
      | nil =>
        have restEqual : rest = trailing := by
          simpa only [expand, List.nil_append] using trace
        refine ⟨[], part :: trailing, ?_, ?_, ?_⟩
        · change part :: rest = part :: trailing
          rw [restEqual]
        · intro entry member
          cases member
        · intro piece member
          rcases List.mem_cons.mp member with equal | later
          · subst piece
            exact outside
          · exact trailingGood piece later
      | cons entry tail =>
        rcases entry with ⟨gap, next⟩
        have headGood := good (gap, next) (List.mem_cons.mpr (Or.inl rfl))
        refine ⟨(part :: gap, next) :: tail, trailing, ?_, ?_, trailingGood⟩
        · change part :: rest = part :: ((gap ++ next :: expand tail) ++ trailing)
          simpa only [expand] using congrArg (fun parts : List (Word Nat) => part :: parts) trace
        · intro entry member
          rcases List.mem_cons.mp member with equal | later
          · subst entry
            refine ⟨?_, headGood.2⟩
            intro piece inGap
            rcases List.mem_cons.mp inGap with equal | inOldGap
            · subst piece
              exact outside
            · exact headGood.1 piece inOldGap
          · exact good entry (List.mem_cons.mpr (Or.inr later))

theorem entry_part_mem :
    ∀ (chunks : List Chunk) (entry : Chunk), entry ∈ chunks →
      ∀ part : Word Nat, part ∈ entry.1 ++ [entry.2] → part ∈ expand chunks := by
  intro chunks
  induction chunks with
  | nil =>
    intro entry member
    cases member
  | cons head rest ih =>
    rcases head with ⟨gap, square⟩
    intro entry member part inside
    change part ∈ gap ++ square :: expand rest
    rcases List.mem_cons.mp member with equal | later
    · subst entry
      rcases List.mem_append.mp inside with inGap | atSquare
      · exact List.mem_append.mpr (Or.inl inGap)
      · exact List.mem_append.mpr (Or.inr
          (List.mem_cons.mpr (Or.inl (List.mem_singleton.mp atSquare))))
    · exact List.mem_append.mpr (Or.inr
        (List.mem_cons.mpr (Or.inr (ih entry later part inside))))

theorem root_sequence_member_expansion (first : Word Nat) (chunks : List Chunk)
    (square : Word Nat) (member : square ∈ first :: chunks.map Prod.snd) :
    square ∈ first :: expand chunks := by
  rcases List.mem_cons.mp member with equal | later
  · exact List.mem_cons.mpr (Or.inl equal)
  · obtain ⟨entry, inChunks, equal⟩ := List.mem_map.mp later
    subst square
    exact List.mem_cons.mpr (Or.inr (entry_part_mem chunks entry inChunks entry.2
      (List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl)))))

theorem root_sequence_squares (roots : List (Word Nat)) (first : Word Nat)
    (chunks : List Chunk) (firstSquare : RootSquare roots first)
    (good : GoodChunks roots chunks) (square : Word Nat)
    (member : square ∈ first :: chunks.map Prod.snd) : RootSquare roots square := by
  rcases List.mem_cons.mp member with equal | later
  · subst square
    exact firstSquare
  · obtain ⟨entry, inChunks, equal⟩ := List.mem_map.mp later
    subst square
    exact (good entry inChunks).2

theorem square_not_outside (roots : List (Word Nat)) (piece : Word Nat)
    (square : RootSquare roots piece) : ¬ Outside roots piece := by
  intro outside
  obtain ⟨root, member, equal⟩ := square
  have inSquare : root.head ∈ piece.toList := by
    rw [equal, Word.toList_append]
    exact List.mem_append.mpr (Or.inl (word_head_member root))
  exact outside root.head inSquare ⟨root, member, word_head_member root⟩

theorem last_mem_suffix (last : Word Nat) :
    ∀ before after initial : List (Word Nat), after ≠ [] →
      before ++ after = initial ++ [last] → last ∈ after := by
  intro before
  induction before with
  | nil =>
    intro after initial _nonempty equal
    change after = initial ++ [last] at equal
    rw [equal]
    exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))
  | cons first rest ih =>
    intro after initial nonempty equal
    cases initial with
    | nil =>
      have tailEmpty : rest ++ after = [] := (List.cons.inj equal).2
      exact False.elim (nonempty (List.append_eq_nil_iff.mp tailEmpty).2)
    | cons other initial =>
      exact ih after initial nonempty (List.cons.inj equal).2

theorem last_eq_of_suffix (before : List (Word Nat)) (left : Word Nat)
    (after : List (Word Nat)) (right : Word Nat)
    (equal : before ++ [left] = after ++ [right]) : left = right := by
  have reversed := congrArg List.reverse equal
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append] at reversed
  exact (List.cons.inj reversed).1

/-- Actual factors and the root-square subsequence have the very same last
square, including when `chunks = []` (the printed n = 0 case). -/
theorem final_root_data (first : Word Nat) (chunks : List Chunk) :
    ∃ actualBefore rootBefore : List (Word Nat), ∃ last : Word Nat,
      first :: expand chunks = actualBefore ++ [last] ∧
      first :: chunks.map Prod.snd = rootBefore ++ [last] := by
  induction chunks generalizing first with
  | nil => exact ⟨[], [], first, rfl, rfl⟩
  | cons entry rest ih =>
    rcases entry with ⟨gap, next⟩
    obtain ⟨actualBefore, rootBefore, last, actual, rootTrace⟩ := ih next
    refine ⟨first :: (gap ++ actualBefore), first :: rootBefore, last, ?_, ?_⟩
    · change first :: (gap ++ next :: expand rest) =
        (first :: (gap ++ actualBefore)) ++ [last]
      rw [actual]
      simp only [List.cons_append, List.append_assoc]
    · change first :: (next :: rest.map Prod.snd) = (first :: rootBefore) ++ [last]
      rw [rootTrace, List.cons_append]

/-- An empty gap would put a root square immediately after a previous root
square. If it occurred earlier, DQ's literal boundary theorem forces that
previous square to be outside the family, which is impossible. -/
theorem repeat_gaps_of_boundary (roots : List (Word Nat)) (pieces : List (Word Nat))
    (first : Word Nat) (chunks : List Chunk) (firstSquare : RootSquare roots first)
    (good : GoodChunks roots chunks) (trace : pieces = first :: expand chunks)
    (repeatBoundary : RepeatBoundary roots pieces) : RepeatGaps first chunks := by
  intro before gap square after chunkSplit earlier
  apply flatten_nonempty
  intro empty
  subst gap
  have beforeGood : GoodChunks roots before := by
    intro entry member
    apply good entry
    rw [chunkSplit]
    exact List.mem_append.mpr (Or.inl member)
  have currentGood : RootSquare roots square := by
    apply (good ([], square) ?_).2
    rw [chunkSplit]
    exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
  obtain ⟨actualBefore, rootBefore, previous, actual, rootTrace⟩ := final_root_data first before
  have previousMember : previous ∈ first :: before.map Prod.snd := by
    rw [rootTrace]
    exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))
  have previousSquare : RootSquare roots previous :=
    root_sequence_squares roots first before firstSquare beforeGood previous previousMember
  have earlierActual : square ∈ actualBefore ++ [previous] := by
    rw [← actual]
    exact root_sequence_member_expansion first before square earlier
  have atStep : pieces = (first :: expand before) ++ square :: expand after := by
    rw [trace, chunkSplit, expand_append]
    simp only [expand, List.nil_append, List.cons_append]
  have literal : pieces = actualBefore ++ previous :: square :: expand after := by
    calc
      pieces = (first :: expand before) ++ square :: expand after := atStep
      _ = (actualBefore ++ [previous]) ++ square :: expand after := by rw [actual]
      _ = actualBefore ++ previous :: square :: expand after := by
        simp only [List.append_assoc, List.cons_append, List.nil_append]
  obtain ⟨root, rootMember, squareEqual⟩ := currentGood
  have previousOutside : Outside roots previous := repeatBoundary root rootMember actualBefore
    previous (expand after) (by simpa only [squareEqual] using literal)
      (by simpa only [squareEqual] using earlierActual)
  exact square_not_outside roots previous previousSquare previousOutside

/-- Exact syntax reification; terminal matching squares remove the only
possible trailing gap. The final repeated-square gap is not discarded. -/
theorem reify_partition (roots : List (Word Nat)) (pieces : List (Word Nat))
    (first : Word Nat) (tail initial : List (Word Nat))
    (kinds : ∀ piece ∈ pieces, RootPiece roots piece) (firstSquare : RootSquare roots first)
    (firstSplit : pieces = first :: tail) (lastSplit : pieces = initial ++ [first])
    (repeatBoundary : RepeatBoundary roots pieces) :
    ∃ chunks : List Chunk, pieces = first :: expand chunks ∧ GoodChunks roots chunks ∧
      RepeatGaps first chunks ∧
      ∃ rootBefore : List (Word Nat), first :: chunks.map Prod.snd = rootBefore ++ [first] := by
  have tailKinds : ∀ piece ∈ tail, RootPiece roots piece := by
    intro piece member
    apply kinds piece
    rw [firstSplit]
    exact List.mem_cons.mpr (Or.inr member)
  obtain ⟨chunks, trailing, tailTrace, good, trailingGood⟩ := pack_parts roots tail tailKinds
  have whole : pieces = (first :: expand chunks) ++ trailing := by
    rw [firstSplit, tailTrace, List.cons_append]
  have trailingEmpty : trailing = [] := by
    apply Classical.byContradiction
    intro nonempty
    have firstMember : first ∈ trailing := last_mem_suffix first (first :: expand chunks)
      trailing initial nonempty (whole.symm.trans lastSplit)
    exact square_not_outside roots first firstSquare (trailingGood first firstMember)
  have trace : pieces = first :: expand chunks := by
    simpa only [trailingEmpty, List.append_nil] using whole
  obtain ⟨actualBefore, rootBefore, last, actual, rootTrace⟩ := final_root_data first chunks
  have endEqual : last = first := last_eq_of_suffix actualBefore last initial first
    ((trace.trans actual).symm.trans lastSplit)
  refine ⟨chunks, trace, good,
    repeat_gaps_of_boundary roots pieces first chunks firstSquare good trace repeatBoundary,
    rootBefore, ?_⟩
  simpa only [endEqual] using rootTrace

theorem gap_letters_simple (roots : List (Word Nat)) (word : Word Nat)
    (pieces : List (Word Nat)) (first : Word Nat) (chunks : List Chunk)
    (partition : SquarePartition roots word pieces)
    (coverage : ∀ value, Covered roots value ↔ 2 ≤ word.toList.count value)
    (good : GoodChunks roots chunks) (trace : pieces = first :: expand chunks) :
    ∀ entry ∈ chunks, ∀ value ∈ flatten entry.1, word.toList.count value = 1 := by
  intro entry member value inGap
  obtain ⟨part, inParts, inPart⟩ := (mem_flatten value entry.1).mp inGap
  have partExpanded : part ∈ expand chunks := entry_part_mem chunks entry member part
    (List.mem_append.mpr (Or.inl inParts))
  have partAll : part ∈ pieces := by
    rw [trace]
    exact List.mem_cons.mpr (Or.inr partExpanded)
  exact outside_part_simple roots word pieces partition coverage part partAll
    ((good entry member).1 part inParts) value inPart

/-- Faithful list encoding of printed z0 * product(s_i z_i), n >= 0:
`n = chunks.length`, each s_i is the actual `flatten gap`, each z_i is the
stored nonempty square. I: `gaps_simple`; II: `family`, `coverage`, and square
membership; III: `terminal`; IV: `repeat_gaps`; V: `endpoints`.
Pairwise root support disjointness (printed VI) is retained in `family`.
This structure contains no semantic comparison or completeness assumption. -/
structure Form (word : Word Nat) where
  roots : List (Word Nat)
  first : Word Nat
  chunks : List Chunk
  connected : Connected word
  family : Family roots word
  terminal : Terminal roots word
  coverage : ∀ value, Covered roots value ↔ 2 ≤ word.toList.count value
  first_square : RootSquare roots first
  chunk_good : GoodChunks roots chunks
  literal : word.toList = first.toList ++ render chunks
  gaps_simple : ∀ entry ∈ chunks, ∀ value ∈ flatten entry.1, word.toList.count value = 1
  repeat_gaps : RepeatGaps first chunks
  endpoints : ∃ initial : List (Word Nat), first :: chunks.map Prod.snd = initial ++ [first]

theorem canonical_of_partition (roots : List (Word Nat)) (word : Word Nat)
    (pieces : List (Word Nat)) (first : Word Nat) (tail initial : List (Word Nat))
    (connected : Connected word) (family : Family roots word) (terminal : Terminal roots word)
    (coverage : ∀ value, Covered roots value ↔ 2 ≤ word.toList.count value)
    (partition : SquarePartition roots word pieces) (firstSquare : RootSquare roots first)
    (firstSplit : pieces = first :: tail) (lastSplit : pieces = initial ++ [first])
    (repeatBoundary : RepeatBoundary roots pieces) : Nonempty (Form word) := by
  obtain ⟨chunks, trace, good, repeatGaps, endpoints⟩ := reify_partition roots pieces first
    tail initial partition.2 firstSquare firstSplit lastSplit repeatBoundary
  have literal : word.toList = first.toList ++ render chunks := by
    rw [← partition.1, trace]
    change first.toList ++ flatten (expand chunks) = first.toList ++ render chunks
    rw [flatten_expand]
  let presentation : Form word :=
    ⟨roots, first, chunks, connected, family, terminal, coverage, firstSquare, good, literal,
      gap_letters_simple roots word pieces first chunks partition coverage good trace,
      repeatGaps, endpoints⟩
  exact ⟨presentation⟩

/-- Connected canonical normalization for arbitrary nonempty words under the
unchanged literal38 basis. Maximal simple-factor order is preserved. This is
not the later semantic comparison of two canonical presentations. -/
theorem normalize_connected_canonical (word : Word Nat) (connected : Connected word) :
    ∃ normal : Word Nat, Derives basis word normal ∧ Nonempty (Form normal) ∧
      simpleFactors normal = simpleFactors word := by
  obtain ⟨normal, roots, pieces, derived, outputConnected, family, terminal, _original, current,
    partition, alignedNormal, alignedOriginal, _kinds, repeatBoundary, endpoints⟩ :=
      normalize_connected_with_endpoints word connected
  obtain ⟨root, rootMember, tail, initial, firstSplit, lastSplit⟩ := endpoints
  refine ⟨normal, derived, ?_, alignedNormal.symm.trans alignedOriginal⟩
  exact canonical_of_partition roots normal pieces (root ++ root) tail initial outputConnected
    family terminal current partition ⟨root, rootMember, rfl⟩ firstSplit lastSplit repeatBoundary

end SemigroupBasis.CoRoots.Order6SporadicSection19.Published.CanonicalPresentation

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.CanonicalPresentation.flatten_expand
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.CanonicalPresentation.pack_parts
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.CanonicalPresentation.final_root_data
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.CanonicalPresentation.repeat_gaps_of_boundary
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.CanonicalPresentation.reify_partition
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.CanonicalPresentation.gap_letters_simple
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.CanonicalPresentation.canonical_of_partition
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.CanonicalPresentation.normalize_connected_canonical
