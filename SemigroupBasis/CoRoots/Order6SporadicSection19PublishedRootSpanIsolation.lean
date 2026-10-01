import SemigroupBasis.CoRoots.Order6SporadicSection19PublishedCanonicalPresentation

namespace SemigroupBasis.CoRoots.Order6SporadicSection19.Published.RootSpanIsolation

open MaximalFactors FactorBoundaries BlockAlignment MacroWitnesses RootFamily
open RootBlockPartition ConnectedTerminalEndpoints CanonicalPresentation

theorem expanded_piece_kind (roots : List (Word Nat)) (chunks : List Chunk)
    (good : GoodChunks roots chunks) :
    ∀ part ∈ expand chunks, RootPiece roots part := by
  induction chunks with
  | nil =>
    intro part member
    cases member
  | cons entry rest ih =>
    rcases entry with ⟨gap, square⟩
    have firstGood := good (gap, square) (List.mem_cons.mpr (Or.inl rfl))
    have restGood : GoodChunks roots rest := by
      intro next member
      exact good next (List.mem_cons.mpr (Or.inr member))
    intro part member
    change part ∈ gap ++ square :: expand rest at member
    rcases List.mem_append.mp member with inGap | remaining
    · exact Or.inr (firstGood.1 part inGap)
    · rcases List.mem_cons.mp remaining with equal | later
      · subst part
        exact Or.inl firstGood.2
      · exact ih restGood part later

/-- Recover the literal square/outside partition of the unchanged Form. -/
theorem form_partition (word : Word Nat) (form : Form word) :
    SquarePartition form.roots word (form.first :: expand form.chunks) := by
  constructor
  · change form.first.toList ++ flatten (expand form.chunks) = word.toList
    rw [flatten_expand]
    exact form.literal.symm
  · intro part member
    rcases List.mem_cons.mp member with equal | later
    · subst part
      exact Or.inl form.first_square
    · exact expanded_piece_kind form.roots form.chunks form.chunk_good part later

/-- Family perfection is nonvacuous, so each root's square really occurs in
every literal square/outside partition. This is not an added occurrence premise. -/
theorem family_square_member (roots : List (Word Nat)) (word : Word Nat)
    (pieces : List (Word Nat)) (family : Family roots word)
    (partition : SquarePartition roots word pieces)
    (root : Word Nat) (rootMember : root ∈ roots) : (root ++ root) ∈ pieces := by
  obtain ⟨before, after, literal⟩ :=
    canonical_perfect_literal_factor root word (family.2 root rootMember).2
  have inSquare : root.head ∈ (root ++ root).toList := by
    rw [Word.toList_append]
    exact List.mem_append.mpr (Or.inl (word_head_member root))
  have inWord : root.head ∈ word.toList := by
    rw [literal]
    exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl inSquare)))
  rw [← partition.1] at inWord
  obtain ⟨part, member, inPart⟩ := (mem_flatten root.head pieces).mp inWord
  have equal := covered_letter_piece roots word pieces family partition root rootMember
    root.head (word_head_member root) part member inPart
  rwa [equal] at member

/-- A root square strictly between two copies of a distinct root cannot
also occur in either exterior context: either occurrence gives a literal G2. -/
theorem terminal_inner_root_absent (roots : List (Word Nat)) (word : Word Nat)
    (pieces : List (Word Nat)) (terminal : Terminal roots word)
    (partition : SquarePartition roots word pieces)
    (root other : Word Nat) (rootMember : root ∈ roots) (otherMember : other ∈ roots)
    (different : root ≠ other) (before middle after : List (Word Nat))
    (split : pieces = before ++ ((root ++ root) :: (middle ++ (root ++ root) :: after)))
    (inside : (other ++ other) ∈ middle) :
    (other ++ other) ∉ before ∧ (other ++ other) ∉ after := by
  obtain ⟨gap1, gap2, middleSplit⟩ := split_member (other ++ other) middle inside
  constructor
  · intro earlier
    obtain ⟨start, gap0, beforeSplit⟩ := split_member (other ++ other) before earlier
    have crossing : G2 (other ++ other) (root ++ root) word.toList := by
      refine ⟨flatten start, flatten gap0, flatten gap1, flatten gap2, flatten after, ?_⟩
      rw [← partition.1, split, beforeSplit, middleSplit]
      simp only [flatten, FactorBoundaries.flatten_append, List.append_assoc]
    have related : GeneralizedRelated other root word := Or.inr (Or.inr (Or.inl crossing))
    exact (terminal_members roots word terminal other root otherMember rootMember
      (Ne.symm different)) related
  · intro later
    obtain ⟨gap3, finish, afterSplit⟩ := split_member (other ++ other) after later
    have crossing : G2 (root ++ root) (other ++ other) word.toList := by
      refine ⟨flatten before, flatten gap1, flatten gap2, flatten gap3, flatten finish, ?_⟩
      rw [← partition.1, split, middleSplit, afterSplit]
      simp only [flatten, FactorBoundaries.flatten_append, List.append_assoc]
    have related : GeneralizedRelated root other word := Or.inr (Or.inr (Or.inl crossing))
    exact (terminal_members roots word terminal root other rootMember otherMember different) related

/-- The singleton case is genuine: it contains just one square, not two
copies at coincident indices. The other branch preserves the literal interior. -/
def SpanShape (square : Word Nat) (inside : List (Word Nat)) : Prop :=
  inside = [square] ∨ ∃ middle : List (Word Nat), inside = square :: (middle ++ [square])

theorem split_first_absent (square : Word Nat) (pieces : List (Word Nat))
    (member : square ∈ pieces) :
    ∃ before after : List (Word Nat), pieces = before ++ square :: after ∧ square ∉ before := by
  classical
  induction pieces with
  | nil => cases member
  | cons first rest ih =>
    by_cases equal : square = first
    · subst first
      refine ⟨[], rest, rfl, ?_⟩
      intro impossible
      cases impossible
    · have later : square ∈ rest := (List.mem_cons.mp member).resolve_left equal
      obtain ⟨before, after, split, absent⟩ := ih later
      refine ⟨first :: before, after, ?_, ?_⟩
      · simp only [List.cons_append, split]
      · intro present
        rcases List.mem_cons.mp present with same | remaining
        · exact equal same
        · exact absent remaining

theorem root_span_exists (square : Word Nat) (pieces : List (Word Nat))
    (member : square ∈ pieces) :
    ∃ before inside after : List (Word Nat),
      pieces = before ++ (inside ++ after) ∧ square ∉ before ∧ square ∉ after ∧
        SpanShape square inside := by
  classical
  obtain ⟨before, tail, firstSplit, beforeAbsent⟩ := split_first_absent square pieces member
  by_cases later : square ∈ tail
  · obtain ⟨middle, after, lastSplit, afterAbsent⟩ := split_last_member square tail later
    refine ⟨before, square :: (middle ++ [square]), after, ?_, beforeAbsent, afterAbsent,
      Or.inr ⟨middle, rfl⟩⟩
    rw [firstSplit, lastSplit]
    simp only [List.cons_append, List.append_assoc, List.nil_append]
  · exact ⟨before, [square], tail, firstSplit, beforeAbsent, later, Or.inl rfl⟩

/-- Exact nonsimple coverage upgrades separated root-square occurrences to
separated LETTER supports. Shared outside letters would have count at least
two and hence would themselves belong to a root; none are silently dropped. -/
theorem separated_squares_separate_letters (roots : List (Word Nat)) (word : Word Nat)
    (pieces : List (Word Nat)) (family : Family roots word)
    (partition : SquarePartition roots word pieces)
    (coverage : ∀ value, Covered roots value ↔ 2 ≤ word.toList.count value)
    (before inside after : List (Word Nat))
    (split : pieces = before ++ (inside ++ after))
    (separated : ∀ root ∈ roots, (root ++ root) ∈ inside → (root ++ root) ∉ before ++ after) :
    ∀ value ∈ flatten inside, value ∉ flatten (before ++ after) := by
  intro value inInside inOutside
  have insideCount : 0 < (flatten inside).count value := List.count_pos_iff.mpr inInside
  have outsideCount : 0 < (flatten before).count value + (flatten after).count value := by
    have positive : 0 < (flatten (before ++ after)).count value := List.count_pos_iff.mpr inOutside
    simpa only [FactorBoundaries.flatten_append, List.count_append] using positive
  have repeated : 2 ≤ word.toList.count value := by
    rw [← partition.1, split]
    simp only [FactorBoundaries.flatten_append, List.count_append]
    omega
  obtain ⟨root, rootMember, inRoot⟩ := (coverage value).mpr repeated
  obtain ⟨innerPart, innerMember, innerLetter⟩ := (mem_flatten value inside).mp inInside
  obtain ⟨outerPart, outerMember, outerLetter⟩ := (mem_flatten value (before ++ after)).mp inOutside
  have innerAll : innerPart ∈ pieces := by
    rw [split]
    exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl innerMember)))
  have outerAll : outerPart ∈ pieces := by
    rw [split]
    rcases List.mem_append.mp outerMember with earlier | later
    · exact List.mem_append.mpr (Or.inl earlier)
    · exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr later)))
  have innerEqual := covered_letter_piece roots word pieces family partition root rootMember
    value inRoot innerPart innerAll innerLetter
  have outerEqual := covered_letter_piece roots word pieces family partition root rootMember
    value inRoot outerPart outerAll outerLetter
  rw [innerEqual] at innerMember
  rw [outerEqual] at outerMember
  exact separated root rootMember innerMember outerMember

theorem terminal_span_isolated (roots : List (Word Nat)) (word : Word Nat)
    (pieces : List (Word Nat)) (family : Family roots word) (terminal : Terminal roots word)
    (partition : SquarePartition roots word pieces)
    (coverage : ∀ value, Covered roots value ↔ 2 ≤ word.toList.count value)
    (root : Word Nat) (rootMember : root ∈ roots) (before inside after : List (Word Nat))
    (split : pieces = before ++ (inside ++ after))
    (beforeAbsent : (root ++ root) ∉ before) (afterAbsent : (root ++ root) ∉ after)
    (shape : SpanShape (root ++ root) inside) :
    ∀ value ∈ flatten inside, value ∉ flatten (before ++ after) := by
  classical
  apply separated_squares_separate_letters roots word pieces family partition coverage
    before inside after split
  intro other otherMember inInside inOutside
  by_cases sameSquare : (other ++ other) = root ++ root
  · rw [sameSquare] at inOutside
    rcases List.mem_append.mp inOutside with earlier | later
    · exact beforeAbsent earlier
    · exact afterAbsent later
  · have different : root ≠ other := by
      intro equal
      exact sameSquare (by rw [equal])
    rcases shape with singleton | repeatedShape
    · rw [singleton] at inInside
      exact sameSquare (List.mem_singleton.mp inInside)
    · obtain ⟨middle, insideEqual⟩ := repeatedShape
      have middleMember : (other ++ other) ∈ middle := by
        rw [insideEqual] at inInside
        rcases List.mem_cons.mp inInside with initial | remaining
        · exact False.elim (sameSquare initial)
        · rcases List.mem_append.mp remaining with middlePresent | finalPresent
          · exact middlePresent
          · exact False.elim (sameSquare (List.mem_singleton.mp finalPresent))
      have arranged : pieces = before ++ ((root ++ root) :: (middle ++ (root ++ root) :: after)) := by
        simpa only [insideEqual, List.cons_append, List.append_assoc, List.nil_append] using split
      have absent := terminal_inner_root_absent roots word pieces terminal partition
        root other rootMember otherMember different before middle after arranged middleMember
      rcases List.mem_append.mp inOutside with earlier | later
      · exact absent.1 earlier
      · exact absent.2 later

/-- The literal first-to-last span exists for EVERY root and is support-disjoint
from both exterior contexts. Neither connectedness nor a detector is assumed. -/
theorem terminal_root_span_isolated (roots : List (Word Nat)) (word : Word Nat)
    (pieces : List (Word Nat)) (family : Family roots word) (terminal : Terminal roots word)
    (partition : SquarePartition roots word pieces)
    (coverage : ∀ value, Covered roots value ↔ 2 ≤ word.toList.count value)
    (root : Word Nat) (rootMember : root ∈ roots) :
    ∃ before inside after : List (Word Nat),
      pieces = before ++ (inside ++ after) ∧
      (root ++ root) ∉ before ∧ (root ++ root) ∉ after ∧
      SpanShape (root ++ root) inside ∧
      (∀ value ∈ flatten inside, value ∉ flatten (before ++ after)) := by
  have member := family_square_member roots word pieces family partition root rootMember
  obtain ⟨before, inside, after, split, beforeAbsent, afterAbsent, shape⟩ :=
    root_span_exists (root ++ root) pieces member
  exact ⟨before, inside, after, split, beforeAbsent, afterAbsent, shape,
    terminal_span_isolated roots word pieces family terminal partition coverage
      root rootMember before inside after split beforeAbsent afterAbsent shape⟩

/-- Printed cut property (d), with actual letter lists, is a consequence of
the existing canonical Form. The p=q singleton case is included exactly. -/
theorem form_root_span_isolated (word : Word Nat) (form : Form word)
    (root : Word Nat) (rootMember : root ∈ form.roots) :
    ∃ before inside after : List (Word Nat),
      form.first :: expand form.chunks = before ++ (inside ++ after) ∧
      (root ++ root) ∉ before ∧ (root ++ root) ∉ after ∧
      SpanShape (root ++ root) inside ∧
      (∀ value ∈ flatten inside, value ∉ flatten (before ++ after)) :=
  terminal_root_span_isolated form.roots word (form.first :: expand form.chunks)
    form.family form.terminal (form_partition word form) form.coverage root rootMember

end SemigroupBasis.CoRoots.Order6SporadicSection19.Published.RootSpanIsolation

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.RootSpanIsolation.form_partition
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.RootSpanIsolation.family_square_member
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.RootSpanIsolation.terminal_inner_root_absent
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.RootSpanIsolation.root_span_exists
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.RootSpanIsolation.separated_squares_separate_letters
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.RootSpanIsolation.terminal_span_isolated
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.RootSpanIsolation.terminal_root_span_isolated
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.RootSpanIsolation.form_root_span_isolated
