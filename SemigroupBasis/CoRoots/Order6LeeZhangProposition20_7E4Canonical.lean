import SemigroupBasis.CoRoots.S5_107BlockCombinatorics

namespace SemigroupBasis.CoRoots.Order6LeeZhangProposition20_7E4

open SemigroupBasis

/-!
# Lee--Zhang Proposition 20.7: E4 canonical data

This file formalizes only the word combinatorics on printed pages 87--90 of
Lee--Zhang.  It contains no multiplication table, semantic separator, or
derivation from the identities (20.6).  In particular, the structures below
are the codomain of the later normalization proof; they are not an
unjustified parser for arbitrary words.

The representation of an `x`-rigid block stores `s₁` separately and stores
`[s₂, ..., sᵣ]` in `rest`.  Thus `rank = rest.length + 1`, and the renderer
is literally

`s₁ x s₂ x ... sᵣ xᵉ`.
-/

/-! ## Simple letters and the factors FSN and FSS -/

/-- A letter is simple in a list when it occurs exactly once. -/
def Simple (whole : List Nat) (letter : Nat) : Prop :=
  whole.count letter = 1

/-- A letter is non-simple in a list when it occurs at least twice. -/
def NonSimple (whole : List Nat) (letter : Nat) : Prop :=
  2 ≤ whole.count letter

namespace Simple

theorem mem
    {whole : List Nat} {letter : Nat}
    (simple : Simple whole letter) :
    letter ∈ whole := by
  apply List.count_pos_iff.mp
  unfold Simple at simple
  omega

theorem not_nonSimple
    {whole : List Nat} {letter : Nat}
    (simple : Simple whole letter) :
    ¬ NonSimple whole letter := by
  intro multiple
  unfold Simple at simple
  unfold NonSimple at multiple
  omega

end Simple

namespace NonSimple

theorem mem
    {whole : List Nat} {letter : Nat}
    (multiple : NonSimple whole letter) :
    letter ∈ whole := by
  apply List.count_pos_iff.mp
  unfold NonSimple at multiple
  omega

theorem not_simple
    {whole : List Nat} {letter : Nat}
    (multiple : NonSimple whole letter) :
    ¬ Simple whole letter := by
  intro simple
  exact simple.not_nonSimple multiple

end NonSimple

/-- Every letter present in a word is either simple or non-simple. -/
theorem simple_or_nonSimple_of_mem
    {whole : List Nat} {letter : Nat}
    (member : letter ∈ whole) :
    Simple whole letter ∨ NonSimple whole letter := by
  have positive : 0 < whole.count letter :=
    List.count_pos_iff.mpr member
  unfold Simple NonSimple
  omega

/-- Relational form of `F_SN(w)`: an adjacent simple--non-simple factor. -/
def FSN (whole : List Nat) (simple multiple : Nat) : Prop :=
  Simple whole simple ∧
    NonSimple whole multiple ∧
      (simple, multiple) ∈ S5_107.listAdjacentPairs whole

/-- Relational form of `F_SS(w)`: an adjacent simple--simple factor. -/
def FSS (whole : List Nat) (first second : Nat) : Prop :=
  Simple whole first ∧
    Simple whole second ∧
      (first, second) ∈ S5_107.listAdjacentPairs whole

/-- Duplicate-free list presentation of the set `F_SN(w)`. -/
def fsn (whole : List Nat) : List (Nat × Nat) :=
  ((S5_107.listAdjacentPairs whole).filter fun edge =>
    decide
      (whole.count edge.1 = 1 ∧ 2 ≤ whole.count edge.2)).eraseDups

/-- Duplicate-free list presentation of the set `F_SS(w)`. -/
def fss (whole : List Nat) : List (Nat × Nat) :=
  ((S5_107.listAdjacentPairs whole).filter fun edge =>
    decide
      (whole.count edge.1 = 1 ∧ whole.count edge.2 = 1)).eraseDups

private theorem mem_eraseDups_iff [BEq α] [LawfulBEq α] :
    ∀ (entry : α) (entries : List α),
      entry ∈ entries.eraseDups ↔ entry ∈ entries
  | entry, [] => by simp
  | entry, head :: tail => by
      rw [List.eraseDups_cons]
      simp only [List.mem_cons]
      rw [mem_eraseDups_iff entry
        (tail.filter fun candidate => !candidate == head)]
      by_cases same : entry = head
      · subst entry
        simp
      · simp [same]
termination_by
  _ entries => entries.length
decreasing_by
  have filteredLength :
      (tail.filter fun candidate => !candidate == head).length ≤
        tail.length := List.filter_sublist.length_le
  simpa only [List.length_cons] using Nat.lt_succ_of_le filteredLength

theorem mem_fsn_iff
    (whole : List Nat) (simple multiple : Nat) :
    (simple, multiple) ∈ fsn whole ↔ FSN whole simple multiple := by
  simp only [fsn, mem_eraseDups_iff, List.mem_filter,
    decide_eq_true_eq, FSN, Simple, NonSimple]
  constructor
  · rintro ⟨adjacent, simpleLetter, multipleLetter⟩
    exact ⟨simpleLetter, multipleLetter, adjacent⟩
  · rintro ⟨simpleLetter, multipleLetter, adjacent⟩
    exact ⟨adjacent, simpleLetter, multipleLetter⟩

theorem mem_fss_iff
    (whole : List Nat) (first second : Nat) :
    (first, second) ∈ fss whole ↔ FSS whole first second := by
  simp only [fss, mem_eraseDups_iff, List.mem_filter,
    decide_eq_true_eq, FSS, Simple]
  constructor
  · rintro ⟨adjacent, firstSimple, secondSimple⟩
    exact ⟨firstSimple, secondSimple, adjacent⟩
  · rintro ⟨firstSimple, secondSimple, adjacent⟩
    exact ⟨adjacent, firstSimple, secondSimple⟩

/-- Word-level spelling of the relation `F_SN`. -/
abbrev WordFSN (word : Word Nat) (simple multiple : Nat) : Prop :=
  FSN word.toList simple multiple

/-- Word-level spelling of the relation `F_SS`. -/
abbrev WordFSS (word : Word Nat) (first second : Nat) : Prop :=
  FSS word.toList first second

/-! ## The invariant data isolated in Lemma 20.8 -/

/-- The exact multiplicity alternative in Lemma 20.8(i). -/
def SameMultiplicityClass
    (left right : List Nat) (letter : Nat) : Prop :=
  (left.count letter = right.count letter ∧
      left.count letter ≤ 2) ∨
    (3 ≤ left.count letter ∧ 3 ≤ right.count letter)

/-- Pure formulation of the four invariants in Lemma 20.8.

The later target-semantics layer is responsible for proving this structure
from equality of evaluations in E4. -/
structure SameInvariant (left right : List Nat) : Prop where
  multiplicity : ∀ letter, SameMultiplicityClass left right letter
  firstLetter : left.head? = right.head?
  fsn : ∀ x y, FSN left x y ↔ FSN right x y
  fss : ∀ x y, FSS left x y ↔ FSS right x y

namespace SameInvariant

theorem support
    {left right : List Nat}
    (same : SameInvariant left right) (letter : Nat) :
    letter ∈ left ↔ letter ∈ right := by
  rw [← List.count_pos_iff, ← List.count_pos_iff]
  rcases same.multiplicity letter with small | large
  · omega
  · omega

theorem simple
    {left right : List Nat}
    (same : SameInvariant left right) (letter : Nat) :
    Simple left letter ↔ Simple right letter := by
  unfold Simple
  rcases same.multiplicity letter with small | large
  · omega
  · omega

theorem nonSimple
    {left right : List Nat}
    (same : SameInvariant left right) (letter : Nat) :
    NonSimple left letter ↔ NonSimple right letter := by
  unfold NonSimple
  rcases same.multiplicity letter with small | large
  · omega
  · omega

end SameInvariant

/-! ## The rigid-block representation (20.7) -/

/-- Data for `s₁ x s₂ x ... sᵣ xᵉ`.

`first` is `s₁`, `rest` is `[s₂, ..., sᵣ]`, and `exponent` is `e`.
Validity below supplies nonemptiness of the tail segments, `e ∈ {1,2,3}`,
and conditions (Ri1)--(Ri5). -/
structure RigidBlock where
  marker : Nat
  first : List Nat
  rest : List (List Nat)
  exponent : Nat
deriving DecidableEq, Repr

namespace RigidBlock

/-- The displayed segment list `[s₁, ..., sᵣ]`. -/
def segments (block : RigidBlock) : List (List Nat) :=
  block.first :: block.rest

/-- The integer `r` in display (20.7). -/
def rank (block : RigidBlock) : Nat :=
  block.rest.length + 1

/-- The ordered list `h(s₂), ..., h(sᵣ)` used in (Ri2).

The default is irrelevant for valid blocks because every segment in `rest`
is nonempty. -/
def heads (block : RigidBlock) : List Nat :=
  block.rest.map fun segment => segment.headD 0

end RigidBlock

/-- Render `s₂ x ... sᵣ x`, including the displayed copy of `x` after
each tail segment. -/
def renderRigidTail (marker : Nat) : List (List Nat) → List Nat
  | [] => []
  | segment :: rest =>
      segment ++ marker :: renderRigidTail marker rest

@[simp]
theorem renderRigidTail_nil (marker : Nat) :
    renderRigidTail marker [] = [] :=
  rfl

@[simp]
theorem renderRigidTail_cons
    (marker : Nat) (segment : List Nat) (rest : List (List Nat)) :
    renderRigidTail marker (segment :: rest) =
      segment ++ marker :: renderRigidTail marker rest :=
  rfl

/-- Literal renderer for display (20.7). -/
def renderRigidBlock (block : RigidBlock) : List Nat :=
  block.first ++ [block.marker] ++
    renderRigidTail block.marker block.rest ++
      List.replicate (block.exponent - 1) block.marker

theorem mem_renderRigidTail_iff
    (marker letter : Nat) :
    ∀ segments : List (List Nat),
      letter ∈ renderRigidTail marker segments ↔
        (∃ segment ∈ segments, letter ∈ segment) ∨
          (letter = marker ∧ segments ≠ [])
  | [] => by simp
  | segment :: rest => by
      simp only [renderRigidTail_cons, List.mem_append, List.mem_cons,
        mem_renderRigidTail_iff marker letter rest]
      constructor
      · intro member
        rcases member with inSegment | isMarker | inTail
        · exact Or.inl ⟨segment, by simp, inSegment⟩
        · exact Or.inr ⟨isMarker, by simp⟩
        · rcases inTail with ⟨tailSegment, tailMember, inSegment⟩ |
              ⟨isMarker, _⟩
          · exact Or.inl
              ⟨tailSegment, Or.inr tailMember, inSegment⟩
          · exact Or.inr ⟨isMarker, by simp⟩
      · intro member
        rcases member with ⟨selected, selectedMember, inSelected⟩ |
              ⟨isMarker, _⟩
        · rcases selectedMember with rfl | inRest
          · exact Or.inl inSelected
          · have tailWitness :
                (∃ segment ∈ rest, letter ∈ segment) ∨
                  (letter = marker ∧ rest ≠ []) :=
                Or.inl ⟨selected, inRest, inSelected⟩
            exact Or.inr (Or.inr tailWitness)
        · exact Or.inr <| Or.inl isMarker

/-- Reconstruction of the support of a rendered rigid block. -/
theorem mem_renderRigidBlock_iff
    (block : RigidBlock) (letter : Nat) :
    letter ∈ renderRigidBlock block ↔
      letter = block.marker ∨
        letter ∈ block.first ∨
          ∃ segment ∈ block.rest, letter ∈ segment := by
  constructor
  · intro member
    have classified :
        letter ∈ block.first ∨
        letter = block.marker ∨
        letter ∈ renderRigidTail block.marker block.rest ∨
        letter ∈ List.replicate (block.exponent - 1) block.marker := by
      simpa only [renderRigidBlock, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false, or_assoc] using member
    rcases classified with inFirst | isMarker | inTail | inRepeat
    · exact Or.inr (Or.inl inFirst)
    · exact Or.inl isMarker
    · rcases (mem_renderRigidTail_iff block.marker letter block.rest).1
          inTail with inSegment | isMarker
      · exact Or.inr (Or.inr inSegment)
      · exact Or.inl isMarker.1
    · exact Or.inl (List.eq_of_mem_replicate inRepeat)
  · intro member
    rcases member with isMarker | inFirst | inRest
    · subst letter
      simp [renderRigidBlock]
    · simp [renderRigidBlock, inFirst]
    · have inTail : letter ∈ renderRigidTail block.marker block.rest :=
        (mem_renderRigidTail_iff block.marker letter block.rest).2
          (Or.inl inRest)
      simp [renderRigidBlock, inTail]

theorem marker_mem_renderRigidBlock (block : RigidBlock) :
    block.marker ∈ renderRigidBlock block :=
  (mem_renderRigidBlock_iff block block.marker).2 (Or.inl rfl)

theorem renderRigidBlock_nonempty (block : RigidBlock) :
    renderRigidBlock block ≠ [] := by
  intro empty
  have absent : block.marker ∉ renderRigidBlock block := by
    rw [empty]
    simp
  exact absent (marker_mem_renderRigidBlock block)

theorem count_renderRigidTail_of_marker_free
    (marker : Nat) :
    ∀ (segments : List (List Nat)),
      (∀ segment ∈ segments, marker ∉ segment) →
      (renderRigidTail marker segments).count marker = segments.length
  | [], _ => by simp
  | segment :: rest, markerFree => by
      have segmentFree : marker ∉ segment :=
        markerFree segment (by simp)
      have restFree : ∀ candidate ∈ rest, marker ∉ candidate := by
        intro candidate member
        exact markerFree candidate (List.Mem.tail segment member)
      have segmentCount : segment.count marker = 0 :=
        List.count_eq_zero.mpr segmentFree
      have tailCount :=
        count_renderRigidTail_of_marker_free marker rest restFree
      simp [renderRigidTail, List.count_append, segmentCount, tailCount]

/-- Conditions (Ri1)--(Ri5), together with the side conditions in the
sentence introducing display (20.7). -/
structure RigidBlock.Valid (block : RigidBlock) : Prop where
  nonSimple : NonSimple (renderRigidBlock block) block.marker
  positiveSegments :
    ∀ segment ∈ block.rest, segment ≠ []
  exponentRange :
    block.exponent = 1 ∨
      block.exponent = 2 ∨ block.exponent = 3
  ri1 :
    ∀ segment ∈ block.segments,
      ∀ letter ∈ segment, Simple (renderRigidBlock block) letter
  ri2 :
    block.heads.Pairwise (fun left right => left < right)
  ri3 :
    block.rank = 1 →
      block.exponent = 2 ∨ block.exponent = 3
  ri4 :
    block.rank = 2 →
      block.exponent = 1 ∨ block.exponent = 2
  ri5 :
    3 ≤ block.rank → block.exponent = 1

/-- A rigid block satisfying the additional condition (Ri6). -/
structure RigidBlock.FullyRigid (block : RigidBlock)
    extends RigidBlock.Valid block : Prop where
  ri6 :
    block.first ≠ [] →
      (block.first.headD 0 :: block.heads).Pairwise
        (fun left right => left < right)

/-- Deterministic left-boundary convention for a later fully rigid block.

The printed definition permits both `x s x` (`s₁ = ∅`) and `s x²`
(`s₁ = s`) as fully rigid descriptions with the same Lemma-20.8 data.
For later canonical blocks we select the latter description: an empty `s₁`
is permitted only when there are no nonempty tail segments.  This predicate
does not alter the provenance-honest printed `RigidBlock.Valid` above. -/
def RigidBlock.LeftNormalized (block : RigidBlock) : Prop :=
  block.first = [] → block.rest = []

namespace RigidBlock.Valid

theorem exponent_pos
    {block : RigidBlock} (valid : block.Valid) :
    1 ≤ block.exponent := by
  rcases valid.exponentRange with exponent | exponent | exponent <;>
    omega

theorem exponent_le_three
    {block : RigidBlock} (valid : block.Valid) :
    block.exponent ≤ 3 := by
  rcases valid.exponentRange with exponent | exponent | exponent <;>
    omega

theorem marker_not_mem_segment
    {block : RigidBlock} (valid : block.Valid)
    {segment : List Nat}
    (segmentMember : segment ∈ block.segments) :
    block.marker ∉ segment := by
  intro markerMember
  have simple := valid.ri1 segment segmentMember
    block.marker markerMember
  exact simple.not_nonSimple valid.nonSimple

theorem marker_not_mem_first
    {block : RigidBlock} (valid : block.Valid) :
    block.marker ∉ block.first :=
  valid.marker_not_mem_segment (by simp [RigidBlock.segments])

theorem marker_not_mem_rest
    {block : RigidBlock} (valid : block.Valid) :
    ∀ segment ∈ block.rest, block.marker ∉ segment := by
  intro segment member
  exact valid.marker_not_mem_segment
    (by simp [RigidBlock.segments, member])

/-- In a valid block the marker count is exactly `(r - 1) + e`. -/
theorem count_marker
    {block : RigidBlock} (valid : block.Valid) :
    (renderRigidBlock block).count block.marker =
      block.rest.length + block.exponent := by
  have firstCount : block.first.count block.marker = 0 :=
    List.count_eq_zero.mpr valid.marker_not_mem_first
  have tailCount :
      (renderRigidTail block.marker block.rest).count block.marker =
        block.rest.length :=
    count_renderRigidTail_of_marker_free
      block.marker block.rest valid.marker_not_mem_rest
  have exponentPositive := valid.exponent_pos
  simp only [renderRigidBlock, List.count_append,
    List.count_cons_self, List.count_nil, List.count_replicate_self]
  rw [firstCount, tailCount]
  omega

/-- Remark 20.9(i): the marker is the only non-simple letter of a valid
rigid block. -/
theorem eq_marker_of_nonSimple
    {block : RigidBlock} (valid : block.Valid)
    {letter : Nat}
    (member : letter ∈ renderRigidBlock block)
    (multiple : NonSimple (renderRigidBlock block) letter) :
    letter = block.marker := by
  rcases (mem_renderRigidBlock_iff block letter).1 member with
      isMarker | inFirst | inRest
  · exact isMarker
  · have simple := valid.ri1 block.first
        (by simp [RigidBlock.segments]) letter inFirst
    exact (simple.not_nonSimple multiple).elim
  · rcases inRest with ⟨segment, segmentMember, letterMember⟩
    have simple := valid.ri1 segment
      (by simp [RigidBlock.segments, segmentMember]) letter letterMember
    exact (simple.not_nonSimple multiple).elim

theorem heads_nodup
    {block : RigidBlock} (valid : block.Valid) :
    block.heads.Nodup :=
  valid.ri2.imp fun less => Nat.ne_of_lt less

theorem exponent_eq_count_sub_rank
    {block : RigidBlock} (valid : block.Valid) :
    block.exponent =
      (renderRigidBlock block).count block.marker - block.rest.length := by
  rw [valid.count_marker]
  omega

end RigidBlock.Valid

namespace RigidBlock.FullyRigid

theorem allHeads_nodup
    {block : RigidBlock} (fully : block.FullyRigid)
    (firstNonempty : block.first ≠ []) :
    (block.first.headD 0 :: block.heads).Nodup :=
  (fully.ri6 firstNonempty).imp fun less => Nat.ne_of_lt less

end RigidBlock.FullyRigid

/-! ## Pairwise disjoint list combinatorics -/

/-- Directed disjointness of supports.  The relation is symmetric, but its
directed spelling works directly with `List.Pairwise`. -/
def ListsDisjoint (left right : List Nat) : Prop :=
  ∀ letter, letter ∈ left → letter ∉ right

namespace ListsDisjoint

theorem symm
    {left right : List Nat}
    (disjoint : ListsDisjoint left right) :
    ListsDisjoint right left := by
  intro letter inRight inLeft
  exact (disjoint letter inLeft) inRight

theorem not_mem_flatten
    {anchor : List Nat} {parts : List (List Nat)} {letter : Nat}
    (relations : ∀ part ∈ parts, ListsDisjoint anchor part)
    (member : letter ∈ anchor) :
    letter ∉ parts.flatten := by
  intro flattenedMember
  rw [List.mem_flatten] at flattenedMember
  rcases flattenedMember with ⟨part, partMember, letterMember⟩
  exact (relations part partMember letter member) letterMember

end ListsDisjoint

/-- A count localizes to its unique part in a pairwise-disjoint flattening. -/
theorem count_flatten_eq_count_of_mem_of_pairwise
    {selected : List Nat} {letter : Nat} :
    ∀ {parts : List (List Nat)},
      parts.Pairwise ListsDisjoint →
      selected ∈ parts →
      letter ∈ selected →
      parts.flatten.count letter = selected.count letter
  | [], _, selectedMember, _ => by
      simp at selectedMember
  | first :: rest, pairwise, selectedMember, letterMember => by
      have firstRelations := (List.pairwise_cons.mp pairwise).1
      have restPairwise := (List.pairwise_cons.mp pairwise).2
      rcases List.mem_cons.mp selectedMember with selectedFirst | selectedRest
      · subst selected
        have absent : letter ∉ rest.flatten :=
          ListsDisjoint.not_mem_flatten firstRelations letterMember
        simp [List.count_append, List.count_eq_zero.mpr absent]
      · have absent : letter ∉ first := by
          intro firstMember
          exact
            (firstRelations selected selectedRest letter firstMember)
              letterMember
        have induction :=
          count_flatten_eq_count_of_mem_of_pairwise
            restPairwise selectedRest letterMember
        simp [List.count_append, List.count_eq_zero.mpr absent,
          induction]

/-! ## Canonical form (20.8) -/

/-- Data for `x₁ ... xₘ z` in display (20.8).  Storing the first block
separately makes the non-simple case `m ≥ 1` structural. -/
structure CanonicalForm where
  first : RigidBlock
  rest : List RigidBlock
  suffix : List Nat
deriving DecidableEq, Repr

namespace CanonicalForm

/-- The block list `[x₁, ..., xₘ]`. -/
def blocks (form : CanonicalForm) : List RigidBlock :=
  form.first :: form.rest

/-- Rendered block list `[x₁, ..., xₘ]`. -/
def blockRenders (form : CanonicalForm) : List (List Nat) :=
  form.blocks.map renderRigidBlock

/-- Marker list `[x₁, ..., xₘ]`. -/
def markers (form : CanonicalForm) : List Nat :=
  form.blocks.map fun block => block.marker

/-- The markers `[x₂, ..., xₘ]` constrained by condition (III). -/
def tailMarkers (form : CanonicalForm) : List Nat :=
  form.rest.map fun block => block.marker

end CanonicalForm

/-- Literal renderer for display (20.8). -/
def renderCanonical (form : CanonicalForm) : List Nat :=
  form.blockRenders.flatten ++ form.suffix

theorem renderCanonical_eq
    (form : CanonicalForm) :
    renderCanonical form =
      renderRigidBlock form.first ++
        (form.rest.map renderRigidBlock).flatten ++ form.suffix := by
  simp [renderCanonical, CanonicalForm.blockRenders,
    CanonicalForm.blocks, List.append_assoc]

theorem renderCanonical_nonempty (form : CanonicalForm) :
    renderCanonical form ≠ [] := by
  intro empty
  have firstMember :
      form.first.marker ∈ renderCanonical form := by
    unfold renderCanonical CanonicalForm.blockRenders CanonicalForm.blocks
    simp only [List.map_cons, List.flatten_cons, List.mem_append]
    exact Or.inl (Or.inl (marker_mem_renderRigidBlock form.first))
  rw [empty] at firstMember
  simp at firstMember

/-- Pairwise-disjoint spelling of condition (V), split into block--block and
block--suffix clauses for later count localization. -/
def CanonicalDisjoint (form : CanonicalForm) : Prop :=
  form.blockRenders.Pairwise ListsDisjoint ∧
    ∀ block ∈ form.blocks,
      ListsDisjoint (renderRigidBlock block) form.suffix

/-- Conditions (I)--(V) following display (20.8). -/
structure CanonicalForm.Valid (form : CanonicalForm) : Prop where
  conditionI : form.first.Valid
  conditionII :
    ∀ block ∈ form.rest, block.FullyRigid
  conditionIII :
    form.tailMarkers.Pairwise (fun left right => left < right)
  conditionIV :
    ∀ letter ∈ form.suffix, Simple (renderCanonical form) letter
  conditionV : CanonicalDisjoint form

/-- A deterministic refinement of the printed form used for uniqueness.

Only later blocks receive the left-boundary convention.  The first block
retains the literal printed definition because Lemma 20.8(ii), the first
letter, distinguishes whether its `s₁` is empty. -/
structure CanonicalForm.ReducedValid (form : CanonicalForm)
    extends CanonicalForm.Valid form : Prop where
  laterLeftNormalized :
    ∀ block ∈ form.rest, block.LeftNormalized

namespace CanonicalForm.Valid

theorem block_valid
    {form : CanonicalForm} (valid : form.Valid)
    {block : RigidBlock}
    (member : block ∈ form.blocks) :
    block.Valid := by
  rcases List.mem_cons.mp member with isFirst | inRest
  · subst block
    exact valid.conditionI
  · exact (valid.conditionII block inRest).toValid

theorem tailMarkers_nodup
    {form : CanonicalForm} (valid : form.Valid) :
    form.tailMarkers.Nodup :=
  valid.conditionIII.imp fun less => Nat.ne_of_lt less

theorem blockRenders_pairwise
    {form : CanonicalForm} (valid : form.Valid) :
    form.blockRenders.Pairwise ListsDisjoint :=
  valid.conditionV.1

theorem block_disjoint_suffix
    {form : CanonicalForm} (valid : form.Valid)
    {block : RigidBlock} (member : block ∈ form.blocks) :
    ListsDisjoint (renderRigidBlock block) form.suffix :=
  valid.conditionV.2 block member

theorem first_disjoint_rest
    {form : CanonicalForm} (valid : form.Valid)
    {block : RigidBlock} (member : block ∈ form.rest) :
    ListsDisjoint
      (renderRigidBlock form.first) (renderRigidBlock block) := by
  have pairwise := valid.blockRenders_pairwise
  have expanded :
      (renderRigidBlock form.first ::
          form.rest.map renderRigidBlock).Pairwise ListsDisjoint := by
    simpa [CanonicalForm.blockRenders, CanonicalForm.blocks] using pairwise
  exact
    (List.pairwise_cons.mp expanded).1
      (renderRigidBlock block) (List.mem_map.mpr ⟨block, member, rfl⟩)

/-- Every letter in a canonical block has exactly its within-block count in
the complete canonical renderer. -/
theorem count_block_letter
    {form : CanonicalForm} (valid : form.Valid)
    {block : RigidBlock} (blockMember : block ∈ form.blocks)
    {letter : Nat} (letterMember : letter ∈ renderRigidBlock block) :
    (renderCanonical form).count letter =
      (renderRigidBlock block).count letter := by
  have renderMember :
      renderRigidBlock block ∈ form.blockRenders :=
    List.mem_map.mpr ⟨block, blockMember, rfl⟩
  have flattenedCount :=
    count_flatten_eq_count_of_mem_of_pairwise
      valid.blockRenders_pairwise renderMember letterMember
  have suffixAbsent : letter ∉ form.suffix :=
    valid.block_disjoint_suffix blockMember letter letterMember
  rw [renderCanonical, List.count_append, flattenedCount,
    List.count_eq_zero.mpr suffixAbsent, Nat.add_zero]

theorem count_block_marker
    {form : CanonicalForm} (valid : form.Valid)
    {block : RigidBlock} (blockMember : block ∈ form.blocks) :
    (renderCanonical form).count block.marker =
      block.rest.length + block.exponent := by
  rw [valid.count_block_letter blockMember
    (marker_mem_renderRigidBlock block)]
  exact (valid.block_valid blockMember).count_marker

theorem block_segment_simple
    {form : CanonicalForm} (valid : form.Valid)
    {block : RigidBlock} (blockMember : block ∈ form.blocks)
    {segment : List Nat} (segmentMember : segment ∈ block.segments)
    {letter : Nat} (letterMember : letter ∈ segment) :
    Simple (renderCanonical form) letter := by
  have blockValid := valid.block_valid blockMember
  have withinSimple :=
    blockValid.ri1 segment segmentMember letter letterMember
  unfold Simple at withinSimple ⊢
  rw [valid.count_block_letter blockMember
    ((mem_renderRigidBlock_iff block letter).2 <|
      Or.inr <| by
        rcases List.mem_cons.mp segmentMember with rfl | inRest
        · exact Or.inl letterMember
        · exact Or.inr ⟨segment, inRest, letterMember⟩)]
  exact withinSimple

theorem block_marker_nonSimple
    {form : CanonicalForm} (valid : form.Valid)
    {block : RigidBlock} (blockMember : block ∈ form.blocks) :
    NonSimple (renderCanonical form) block.marker := by
  unfold NonSimple
  rw [valid.count_block_letter blockMember
    (marker_mem_renderRigidBlock block)]
  exact (valid.block_valid blockMember).nonSimple

theorem block_markers_pairwise_ne
    {form : CanonicalForm} (valid : form.Valid) :
    form.blocks.Pairwise
      (fun left right => left.marker ≠ right.marker) := by
  have pairwise := valid.blockRenders_pairwise
  rw [CanonicalForm.blockRenders, List.pairwise_map] at pairwise
  exact pairwise.imp fun {left right} disjoint => by
    intro equal
    have leftMember := marker_mem_renderRigidBlock left
    have rightMember := marker_mem_renderRigidBlock right
    exact
      (disjoint _ leftMember) (by simpa [equal] using rightMember)

theorem markers_nodup
    {form : CanonicalForm} (valid : form.Valid) :
    form.markers.Nodup := by
  change (form.blocks.map fun block => block.marker).Pairwise (· ≠ ·)
  rw [List.pairwise_map]
  exact valid.block_markers_pairwise_ne

theorem suffix_nodup
    {form : CanonicalForm} (valid : form.Valid) :
    form.suffix.Nodup := by
  rw [List.nodup_iff_count]
  intro letter
  by_cases member : letter ∈ form.suffix
  · have simple := valid.conditionIV letter member
    unfold Simple at simple
    rw [renderCanonical, List.count_append] at simple
    omega
  · rw [List.count_eq_zero.mpr member]
    omega

end CanonicalForm.Valid

namespace CanonicalForm.ReducedValid

theorem later_fullyRigid
    {form : CanonicalForm} (valid : form.ReducedValid)
    {block : RigidBlock} (member : block ∈ form.rest) :
    block.FullyRigid :=
  valid.toValid.conditionII block member

theorem later_rest_empty_of_first_empty
    {form : CanonicalForm} (valid : form.ReducedValid)
    {block : RigidBlock} (member : block ∈ form.rest) :
    block.first = [] → block.rest = [] :=
  valid.laterLeftNormalized block member

end CanonicalForm.ReducedValid

/-! ## Recognition and structural uniqueness interfaces -/

/-- A list is a valid `x`-rigid block when it has a witness for (20.7). -/
def IsRigidBlock (letters : List Nat) (marker : Nat) : Prop :=
  ∃ block : RigidBlock,
    block.marker = marker ∧
      block.Valid ∧ renderRigidBlock block = letters

/-- A list is a fully valid `x`-rigid block when its witness also satisfies
(Ri6). -/
def IsFullyRigidBlock (letters : List Nat) (marker : Nat) : Prop :=
  ∃ block : RigidBlock,
    block.marker = marker ∧
      block.FullyRigid ∧ renderRigidBlock block = letters

/-- A non-simple list is in the published form (20.8) when it is rendered by
some witness satisfying conditions (I)--(V). -/
def IsCanonical (letters : List Nat) : Prop :=
  ∃ form : CanonicalForm,
    form.Valid ∧ renderCanonical form = letters

abbrev WordIsCanonical (word : Word Nat) : Prop :=
  IsCanonical word.toList

/-- Frozen component equality used as the last, purely structural step of
the uniqueness proof on pages 89--90. -/
structure SameCanonicalComponents
    (left right : CanonicalForm) : Prop where
  first : left.first = right.first
  rest : left.rest = right.rest
  suffix : left.suffix = right.suffix

namespace SameCanonicalComponents

theorem form_eq
    {left right : CanonicalForm}
    (same : SameCanonicalComponents left right) :
    left = right := by
  cases left with
  | mk leftFirst leftRest leftSuffix =>
    cases right with
    | mk rightFirst rightRest rightSuffix =>
      have firstEq : leftFirst = rightFirst := same.first
      have restEq : leftRest = rightRest := same.rest
      have suffixEq : leftSuffix = rightSuffix := same.suffix
      cases firstEq
      cases restEq
      cases suffixEq
      rfl

theorem render_eq
    {left right : CanonicalForm}
    (same : SameCanonicalComponents left right) :
    renderCanonical left = renderCanonical right := by
  rw [same.form_eq]

end SameCanonicalComponents

end SemigroupBasis.CoRoots.Order6LeeZhangProposition20_7E4
