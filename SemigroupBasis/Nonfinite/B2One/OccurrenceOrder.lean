import SemigroupBasis.Nonfinite
import SemigroupBasis.Opposite

namespace SemigroupBasis.Nonfinite.B2One

open SemigroupBasis

/-!
Occurrence-order bookkeeping for Perkins's `B₂¹` obstruction.

For `extra + 1` variables `y₁, ..., yₙ`, the left side has the form

`x y₁ P x Q y₁`,

where `P` and `Q` are two permutations of `y₂, ..., yₙ`.  This is the
source proof's stable occurrence-order property: for every `z ≠ y₁`, the
six selected occurrences appear as

`x₁ < y₁₁ < z₁ < x₂ < z₂ < y₁₂`.

The unresolved mathematical step is now only the preservation of this
property by one contextual instance of one valid bounded-variable identity.
All propagation through an arbitrary equational derivation is proved here.
-/

/-- The variables `y₂, ..., yₙ`, represented by `2, ..., extra + 1`. -/
def middleVariables (extra : Nat) : List Nat :=
  (List.range extra).map (fun index => index + 2)

/-- The stable occurrence-order property used in Perkins's proof.

The two middle lists may be independently permuted.  Thus this records only
the occurrence information used by the source argument, not the exact word.
-/
def OccurrencePattern (extra : Nat) (letters : List Nat) : Prop :=
  ∃ firstMiddle secondMiddle,
    firstMiddle.Perm (middleVariables extra) ∧
    secondMiddle.Perm (middleVariables extra) ∧
    letters =
      [0, 1] ++ firstMiddle ++ [0] ++ secondMiddle ++ [1]

/-- The six-letter projection used in the local form of Perkins's argument. -/
def occurrenceProjection (z : Nat) (letters : List Nat) : List Nat :=
  letters.filter fun letter =>
    letter == 0 || letter == 1 || letter == z

theorem OccurrencePattern.mem
    {extra : Nat} {letters : List Nat}
    (pattern : OccurrencePattern extra letters)
    {letter : Nat} (member : letter ∈ letters) :
    letter = 0 ∨ letter = 1 ∨ letter ∈ middleVariables extra := by
  rcases pattern with
    ⟨firstMiddle, secondMiddle, firstPerm, secondPerm, rfl⟩
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false] at member
  simp only [firstPerm.mem_iff, secondPerm.mem_iff, or_assoc,
    or_left_comm, or_comm] at member
  rcases member with h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inr h)

private def skeletonLetter (letter : Nat) : Bool :=
  letter == 0 || letter == 1

private theorem separated_projection_sections
    (z : Nat) (z0 : z ≠ 0) (z1 : z ≠ 1)
    (a0 a1 a2 a3 a4 : List Nat)
    (ha0 : ∀ x, x ∈ a0 → x = z)
    (ha1 : ∀ x, x ∈ a1 → x = z)
    (ha2 : ∀ x, x ∈ a2 → x = z)
    (ha3 : ∀ x, x ∈ a3 → x = z)
    (ha4 : ∀ x, x ∈ a4 → x = z)
    (shape :
      a0 ++ [0] ++ a1 ++ [1] ++ a2 ++ [0] ++ a3 ++ [1] ++ a4 =
        [0, 1, z, 0, z, 1]) :
    a0 = [] ∧ a1 = [] ∧ a2 = [z] ∧ a3 = [z] ∧ a4 = [] := by
  cases a0 with
  | cons x0 a0 =>
      have hx0 := ha0 x0 (by simp)
      subst x0
      simp_all
  | nil =>
      simp only [List.nil_append] at shape
      cases a1 with
      | cons x1 a1 =>
          have hx1 := ha1 x1 (by simp)
          subst x1
          simp_all
      | nil =>
          cases a2 with
          | nil => simp_all
          | cons x2 a2 =>
              have hx2 := ha2 x2 (by simp)
              subst x2
              simp only [List.cons_append, List.cons.injEq, true_and] at shape
              cases a2 with
              | cons x2 a2 =>
                  have hx2 := ha2 x2 (by simp)
                  subst x2
                  simp_all
              | nil =>
                  cases a3 with
                  | nil => simp_all
                  | cons x3 a3 =>
                      have hx3 := ha3 x3 (by simp)
                      subst x3
                      cases a3 with
                      | cons x3 a3 =>
                          have hx3 := ha3 x3 (by simp)
                          subst x3
                          simp_all
                      | nil =>
                          cases a4 with
                          | nil => simp_all
                          | cons x4 a4 =>
                              have hx4 := ha4 x4 (by simp)
                              subst x4
                              simp_all

private theorem middleVariables_count_of_mem
    {extra z : Nat} (member : z ∈ middleVariables extra) :
    (middleVariables extra).count z = 1 := by
  induction extra with
  | zero =>
      simp [middleVariables] at member
  | succ extra ih =>
      have step :
          middleVariables (extra + 1) =
            middleVariables extra ++ [extra + 2] := by
        simp [middleVariables, List.range_succ]
      rw [step] at member ⊢
      rcases List.mem_append.mp member with earlier | latest
      · have zNe : z ≠ extra + 2 := by
          intro equality
          subst z
          rcases List.mem_map.mp earlier with
            ⟨index, indexMember, equality⟩
          have indexSmall := List.mem_range.mp indexMember
          omega
        have notLatest : z ∉ [extra + 2] := by simpa using zNe
        rw [List.count_append, ih earlier,
          List.count_eq_zero.mpr notLatest]
      · have zEq : z = extra + 2 := by simpa using latest
        subst z
        have absent : extra + 2 ∉ middleVariables extra := by
          intro earlier
          rcases List.mem_map.mp earlier with
            ⟨index, indexMember, equality⟩
          have indexSmall := List.mem_range.mp indexMember
          omega
        simp [List.count_append, List.count_eq_zero.mpr absent]

private theorem filter_eq_singleton_of_nodup_mem
    {letters : List Nat} {selected : Nat}
    (nodup : letters.Nodup)
    (member : selected ∈ letters) :
    letters.filter (fun letter => letter == selected) = [selected] := by
  induction letters with
  | nil =>
      simp at member
  | cons head tail ih =>
      by_cases headSelected : head = selected
      · subst head
        have tailAbsent : selected ∉ tail := by
          exact (List.nodup_cons.mp nodup).1
        have tailFiltered :
            tail.filter (fun letter => letter == selected) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro letter letterMember
          have different : letter ≠ selected := by
            intro equality
            subst letter
            exact tailAbsent letterMember
          simp [different]
        simp [tailFiltered]
      · have tailMember : selected ∈ tail := by
          rcases List.mem_cons.mp member with selectedHead | tailMember
          · exact (headSelected selectedHead.symm).elim
          · exact tailMember
        have tailNodup : tail.Nodup := by
          exact (List.nodup_cons.mp nodup).2
        simpa [headSelected] using ih tailNodup tailMember

/-- Every Perkins occurrence pattern has the expected six-letter projection
for each distinguished middle marker. -/
theorem OccurrencePattern.occurrenceProjection_eq
    {extra : Nat} {letters : List Nat}
    (pattern : OccurrencePattern extra letters)
    {z : Nat} (zMiddle : z ∈ middleVariables extra) :
    occurrenceProjection z letters = [0, 1, z, 0, z, 1] := by
  rcases pattern with
    ⟨firstMiddle, secondMiddle, firstPerm, secondPerm, rfl⟩
  have middleNodup : (middleVariables extra).Nodup := by
    simp only [middleVariables]
    exact
      (List.nodup_range : (List.range extra).Nodup).map
        (fun index => index + 2)
        (by
          intro first second different equality
          apply different
          exact Nat.add_right_cancel equality)
  have firstNodup : firstMiddle.Nodup :=
    firstPerm.nodup_iff.mpr middleNodup
  have secondNodup : secondMiddle.Nodup :=
    secondPerm.nodup_iff.mpr middleNodup
  have firstMember : z ∈ firstMiddle :=
    firstPerm.mem_iff.mpr zMiddle
  have secondMember : z ∈ secondMiddle :=
    secondPerm.mem_iff.mpr zMiddle
  have filterMiddle :
      ∀ (segment : List Nat),
        segment.Perm (middleVariables extra) →
        segment.Nodup →
        z ∈ segment →
        segment.filter
            (fun letter =>
              letter == 0 || letter == 1 || letter == z) =
          [z] := by
    intro segment segmentPerm segmentNodup zMember
    calc
      segment.filter
          (fun letter =>
            letter == 0 || letter == 1 || letter == z) =
          segment.filter (fun letter => letter == z) := by
        apply List.filter_congr
        intro letter letterMember
        have letterMiddle :=
          segmentPerm.mem_iff.mp letterMember
        rcases List.mem_map.mp letterMiddle with
          ⟨index, _, rfl⟩
        have nonzero : index + 2 ≠ 0 := by omega
        have nonone : index + 2 ≠ 1 := by omega
        simp [nonzero, nonone]
      _ = [z] :=
        filter_eq_singleton_of_nodup_mem segmentNodup zMember
  have firstFiltered :=
    filterMiddle firstMiddle firstPerm firstNodup firstMember
  have secondFiltered :=
    filterMiddle secondMiddle secondPerm secondNodup secondMember
  have zLower : 2 ≤ z := by
    rcases List.mem_map.mp zMiddle with
      ⟨index, _, rfl⟩
    omega
  have zZero : z ≠ 0 := by omega
  have zOne : z ≠ 1 := by omega
  unfold occurrenceProjection
  simp [List.filter_append, firstFiltered, secondFiltered,
    zZero, zOne]

/-- The local six-letter projections, together with absence of foreign
letters, reconstruct the full Perkins occurrence pattern. -/
theorem occurrencePattern_of_domain_and_projections
    (extra : Nat) (letters : List Nat)
    (positive : 1 ≤ extra)
    (domain :
      ∀ letter, letter ∈ letters →
        letter = 0 ∨ letter = 1 ∨ letter ∈ middleVariables extra)
    (projections :
      ∀ z, z ∈ middleVariables extra →
        occurrenceProjection z letters = [0, 1, z, 0, z, 1]) :
    OccurrencePattern extra letters := by
  have twoMiddle : 2 ∈ middleVariables extra := by
    cases extra with
    | zero => omega
    | succ extra => simp [middleVariables]
  have skeleton :
      letters.filter skeletonLetter = [0, 1, 0, 1] := by
    have projected := projections 2 twoMiddle
    have filtered :=
      congrArg (List.filter skeletonLetter) projected
    unfold occurrenceProjection at filtered
    have absorb :
        List.filter skeletonLetter
            (List.filter
              (fun letter =>
                letter == 0 || letter == 1 || letter == 2)
              letters) =
          List.filter skeletonLetter letters := by
      rw [List.filter_filter]
      apply List.filter_congr
      intro x _
      by_cases h0 : x == 0
      · simp [skeletonLetter, h0]
      · by_cases h1 : x == 1
        · simp [skeletonLetter, h0, h1]
        · simp [skeletonLetter, h0, h1]
    rw [absorb] at filtered
    have concrete :
        List.filter skeletonLetter [0, 1, 2, 0, 2, 1] =
          [0, 1, 0, 1] := by decide
    rw [concrete] at filtered
    exact filtered
  rcases (List.filter_eq_cons_iff.mp skeleton) with
    ⟨a0, rest0, shape0, a0NoSkeleton, _, rest0Skeleton⟩
  rcases (List.filter_eq_cons_iff.mp rest0Skeleton) with
    ⟨a1, rest1, shape1, a1NoSkeleton, _, rest1Skeleton⟩
  rcases (List.filter_eq_cons_iff.mp rest1Skeleton) with
    ⟨a2, rest2, shape2, a2NoSkeleton, _, rest2Skeleton⟩
  rcases (List.filter_eq_cons_iff.mp rest2Skeleton) with
    ⟨a3, a4, shape3, a3NoSkeleton, _, a4NoSkeleton⟩
  have shape :
      letters =
        a0 ++ [0] ++ a1 ++ [1] ++ a2 ++ [0] ++ a3 ++ [1] ++ a4 := by
    rw [shape0, shape1, shape2, shape3]
    simp
  have filterSection :
      ∀ z (segment : List Nat),
        (∀ x, x ∈ segment → ¬skeletonLetter x = true) →
        segment.filter
            (fun letter =>
              letter == 0 || letter == 1 || letter == z) =
          segment.filter (fun x => x == z) := by
    intro z segment noSkeleton
    apply List.filter_congr
    intro x member
    have excluded := noSkeleton x member
    simp [skeletonLetter] at excluded
    simp [excluded.1, excluded.2]
  have filteredSections :
      ∀ z, z ∈ middleVariables extra →
        a0.filter (fun x => x == z) = [] ∧
        a1.filter (fun x => x == z) = [] ∧
        a2.filter (fun x => x == z) = [z] ∧
        a3.filter (fun x => x == z) = [z] ∧
        a4.filter (fun x => x == z) = [] := by
    intro z zMiddle
    have zLower : 2 ≤ z := by
      rcases List.mem_map.mp zMiddle with
        ⟨index, _, rfl⟩
      omega
    have z0 : z ≠ 0 := by omega
    have z1 : z ≠ 1 := by omega
    have projected := projections z zMiddle
    unfold occurrenceProjection at projected
    rw [shape] at projected
    simp only [List.filter_append, List.filter_cons, List.filter_nil] at projected
    rw [filterSection z a0 a0NoSkeleton,
      filterSection z a1 a1NoSkeleton,
      filterSection z a2 a2NoSkeleton,
      filterSection z a3 a3NoSkeleton,
      filterSection z a4
        (List.filter_eq_nil_iff.mp a4NoSkeleton)] at projected
    simp at projected
    apply separated_projection_sections z z0 z1
      (a0.filter fun x => x == z)
      (a1.filter fun x => x == z)
      (a2.filter fun x => x == z)
      (a3.filter fun x => x == z)
      (a4.filter fun x => x == z)
    · intro x member
      simpa using (List.mem_filter.mp member).2
    · intro x member
      simpa using (List.mem_filter.mp member).2
    · intro x member
      simpa using (List.mem_filter.mp member).2
    · intro x member
      simpa using (List.mem_filter.mp member).2
    · intro x member
      simpa using (List.mem_filter.mp member).2
    · simpa only [List.append_assoc] using projected
  have a4NoSkeleton' :
      ∀ x, x ∈ a4 → ¬skeletonLetter x = true :=
    List.filter_eq_nil_iff.mp a4NoSkeleton
  have sectionEmpty :
      ∀ (segment : List Nat),
        (∀ x, x ∈ segment → x ∈ letters) →
        (∀ x, x ∈ segment → ¬skeletonLetter x = true) →
        (∀ z, z ∈ middleVariables extra →
          segment.filter (fun x => x == z) = []) →
        segment = [] := by
    intro segment sublist noSkeleton filters
    cases segment with
    | nil => rfl
    | cons x xs =>
        exfalso
        have member : x ∈ x :: xs := by simp
        have inLetters := sublist x member
        have xDomain := domain x inLetters
        have excluded := noSkeleton x member
        simp [skeletonLetter] at excluded
        rcases xDomain with rfl | rfl | xMiddle
        · exact excluded.1 rfl
        · exact excluded.2 rfl
        · have inFilter :
              x ∈ (x :: xs).filter (fun y => y == x) := by simp
          rw [filters x xMiddle] at inFilter
          exact (by simp at inFilter)
  have a0Empty : a0 = [] := by
    apply sectionEmpty a0
    · intro x member
      rw [shape]
      simp [member]
    · exact a0NoSkeleton
    · intro z zMiddle
      exact (filteredSections z zMiddle).1
  have a1Empty : a1 = [] := by
    apply sectionEmpty a1
    · intro x member
      rw [shape]
      simp [member]
    · exact a1NoSkeleton
    · intro z zMiddle
      exact (filteredSections z zMiddle).2.1
  have a4Empty : a4 = [] := by
    apply sectionEmpty a4
    · intro x member
      rw [shape]
      simp [member]
    · exact a4NoSkeleton'
    · intro z zMiddle
      exact (filteredSections z zMiddle).2.2.2.2
  have sectionPerm :
      ∀ (segment : List Nat),
        (∀ x, x ∈ segment → x ∈ letters) →
        (∀ x, x ∈ segment → ¬skeletonLetter x = true) →
        (∀ z, z ∈ middleVariables extra →
          segment.filter (fun x => x == z) = [z]) →
        segment.Perm (middleVariables extra) := by
    intro segment sublist noSkeleton filters
    apply List.perm_iff_count.mpr
    intro x
    by_cases xMiddle : x ∈ middleVariables extra
    · have filtered := filters x xMiddle
      have countSegment :
          segment.count x =
            (segment.filter (fun y => y == x)).length := by
        exact List.count_eq_length_filter
      rw [countSegment, filtered]
      have countMiddle : (middleVariables extra).count x = 1 :=
        middleVariables_count_of_mem xMiddle
      simpa using countMiddle.symm
    · have absent : x ∉ segment := by
        intro member
        have xDomain := domain x (sublist x member)
        have excluded := noSkeleton x member
        simp [skeletonLetter] at excluded
        rcases xDomain with rfl | rfl | xMiddle'
        · exact excluded.1 rfl
        · exact excluded.2 rfl
        · exact xMiddle xMiddle'
      simp [List.count_eq_zero.mpr absent,
        List.count_eq_zero.mpr xMiddle]
  have a2Perm : a2.Perm (middleVariables extra) := by
    apply sectionPerm a2
    · intro x member
      rw [shape]
      simp [member]
    · exact a2NoSkeleton
    · intro z zMiddle
      exact (filteredSections z zMiddle).2.2.1
  have a3Perm : a3.Perm (middleVariables extra) := by
    apply sectionPerm a3
    · intro x member
      rw [shape]
      simp [member]
    · exact a3NoSkeleton
    · intro z zMiddle
      exact (filteredSections z zMiddle).2.2.2.1
  refine ⟨a2, a3, a2Perm, a3Perm, ?_⟩
  simpa [a0Empty, a1Empty, a4Empty] using shape

/-- Directional occurrence-order preservation in every semigroup context and
after every nonempty-word substitution.  This is the exact shape proved for
one rewrite in the source argument. -/
def ContextuallyPreservesOccurrencePattern
    (extra : Nat) (left right : Word Nat) : Prop :=
  ∀ pre post substitution,
    OccurrencePattern extra
        (pre ++ (left.bind substitution).toList ++ post) →
      OccurrencePattern extra
        (pre ++ (right.bind substitution).toList ++ post)

/-- Bidirectional occurrence-order stability.  For valid identities this is
obtained by applying the directional lemma to the identity and its swap. -/
def ContextuallySameOccurrencePattern
    (extra : Nat) (left right : Word Nat) : Prop :=
  ∀ pre post substitution,
    OccurrencePattern extra
        (pre ++ (left.bind substitution).toList ++ post) ↔
      OccurrencePattern extra
        (pre ++ (right.bind substitution).toList ++ post)

/-- The nonempty word represented by a possibly empty prefix, a nonempty
middle word, and a possibly empty suffix. -/
def contextWord
    (pre : List Nat) (middle : Word Nat) (post : List Nat) :
    Word Nat :=
  match pre with
  | [] => ⟨middle.head, middle.tail ++ post⟩
  | head :: tail => ⟨head, tail ++ middle.toList ++ post⟩

@[simp]
theorem contextWord_toList
    (pre : List Nat) (middle : Word Nat) (post : List Nat) :
    (contextWord pre middle post).toList =
      pre ++ middle.toList ++ post := by
  cases pre <;> simp [contextWord, Word.toList]

@[simp]
theorem contextWord_nil_nil (middle : Word Nat) :
    contextWord [] middle [] = middle := by
  cases middle
  simp [contextWord]

theorem bind_append (left right : Word Nat)
    (substitution : Nat → Word Nat) :
    (left ++ right).bind substitution =
      left.bind substitution ++ right.bind substitution := by
  apply Word.toList_injective
  simp only [Word.toList_bind, Word.toList_append, List.flatMap_append]

theorem bind_bind (word : Word Nat)
    (first second : Nat → Word Nat) :
    (word.bind first).bind second =
      word.bind (fun letter => (first letter).bind second) := by
  apply Word.toList_injective
  simp only [Word.toList_bind, List.flatMap_assoc]

theorem ContextuallySameOccurrencePattern.refl
    (extra : Nat) (word : Word Nat) :
    ContextuallySameOccurrencePattern extra word word := by
  intro pre post substitution
  exact Iff.rfl

theorem ContextuallySameOccurrencePattern.symm
    {extra : Nat} {left right : Word Nat}
    (same : ContextuallySameOccurrencePattern extra left right) :
    ContextuallySameOccurrencePattern extra right left := by
  intro pre post substitution
  exact (same pre post substitution).symm

theorem ContextuallySameOccurrencePattern.trans
    {extra : Nat} {left middle right : Word Nat}
    (leftMiddle : ContextuallySameOccurrencePattern extra left middle)
    (middleRight : ContextuallySameOccurrencePattern extra middle right) :
    ContextuallySameOccurrencePattern extra left right := by
  intro pre post substitution
  exact
    (leftMiddle pre post substitution).trans
      (middleRight pre post substitution)

/-- One-step contextual occurrence-order preservation propagates through all
constructors of equational derivability. -/
theorem Derives.contextuallySameOccurrencePattern
    {basis : List (Identity Nat)} {left right : Word Nat}
    (axiomPreserves :
      ∀ identity, identity ∈ basis →
        ContextuallySameOccurrencePattern extra
          identity.lhs identity.rhs)
    (derivation : Derives basis left right) :
    ContextuallySameOccurrencePattern extra left right := by
  induction derivation with
  | fromBasis member =>
      exact axiomPreserves _ member
  | refl word =>
      exact ContextuallySameOccurrencePattern.refl extra word
  | symm _ ih =>
      exact ih.symm
  | trans _ _ ihLeft ihRight =>
      exact ihLeft.trans ihRight
  | prepend p _ ih =>
      intro pre post substitution
      rw [bind_append, bind_append, Word.toList_append,
        Word.toList_append, ← List.append_assoc, ← List.append_assoc]
      exact ih
        (pre ++ (p.bind substitution).toList)
        post substitution
  | appendRight _ suffix ih =>
      intro pre post substitution
      rw [bind_append, bind_append, Word.toList_append,
        Word.toList_append]
      simpa only [List.append_assoc] using
        ih pre ((suffix.bind substitution).toList ++ post)
          substitution
  | subst _ first ih =>
      intro pre post second
      rw [bind_bind, bind_bind]
      exact ih pre post
        (fun letter => (first letter).bind second)

end SemigroupBasis.Nonfinite.B2One
