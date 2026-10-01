import SemigroupBasis.Nonfinite.B2One.SemanticProjection

namespace SemigroupBasis.Nonfinite.B2One

open SemigroupBasis
open SemigroupBasis.Examples.B2One

/-!
Kernel-checked combinatorics for the remaining local step in Perkins's
`B₂¹` argument.

This module keeps the source word explicit.  Arbitrary semigroup contexts
are represented by at most two fresh source variables, and the quantitative
`4 * bound + 7` pigeonhole argument is stated for occurrences of that packed
source word.
-/

private def freshAbove : List Nat → Nat
  | [] => 0
  | letter :: rest => max (letter + 1) (freshAbove rest)

private theorem lt_freshAbove_of_mem
    {letter : Nat} {variables : List Nat}
    (member : letter ∈ variables) :
    letter < freshAbove variables := by
  induction variables with
  | nil => simp at member
  | cons first rest ih =>
      simp only [List.mem_cons] at member
      simp only [freshAbove]
      rcases member with rfl | member
      · omega
      · have := ih member
        omega

private theorem freshAbove_not_mem (variables : List Nat) :
    freshAbove variables ∉ variables := by
  intro member
  exact Nat.lt_irrefl _ (lt_freshAbove_of_mem member)

private theorem freshAbove_succ_not_mem (variables : List Nat) :
    freshAbove variables + 1 ∉ variables := by
  intro member
  have := lt_freshAbove_of_mem member
  omega

private theorem bind_congr_of_usesOnly
    {word : Word Nat} {variables : List Nat}
    (uses : word.UsesOnly variables)
    {first second : Nat → Word Nat}
    (agree :
      ∀ letter, letter ∈ variables →
        first letter = second letter) :
    word.bind first = word.bind second := by
  apply Word.toList_injective
  simp only [Word.toList_bind]
  have flatMapEquality :
      ∀ letters : List Nat,
        (∀ letter, letter ∈ letters → letter ∈ variables) →
        letters.flatMap (fun letter => (first letter).toList) =
          letters.flatMap (fun letter => (second letter).toList) := by
    intro letters contained
    induction letters with
    | nil => rfl
    | cons letter rest ih =>
        simp only [List.flatMap_cons]
        rw [agree letter (contained letter (by simp))]
        exact congrArg
          (List.append (second letter).toList)
          (ih (fun x member =>
            contained x (by simp [member])))
  exact flatMapEquality word.toList uses

private theorem append_usesOnly
    {left right : Word Nat} {variables : List Nat}
    (leftUses : left.UsesOnly variables)
    (rightUses : right.UsesOnly variables) :
    (left ++ right).UsesOnly variables := by
  intro letter member
  rw [Word.toList_append] at member
  rcases List.mem_append.mp member with member | member
  · exact leftUses letter member
  · exact rightUses letter member

private theorem singleton_usesOnly
    (letter : Nat) (variables : List Nat)
    (member : letter ∈ variables) :
    (Word.singleton letter).UsesOnly variables := by
  intro value occurrence
  have equality : value = letter := by
    simpa using occurrence
  simpa [equality] using member

private theorem prepend_valid
    {G : Semigroup S} {left right prefixWord : Word Nat}
    (valid : (Identity.mk left right).SatisfiedBy G) :
    (Identity.mk
      (prefixWord ++ left) (prefixWord ++ right)).SatisfiedBy G := by
  intro valuation
  simp only [Semigroup.eval_append]
  exact congrArg (G.mul (G.eval valuation prefixWord)) (valid valuation)

private theorem append_valid
    {G : Semigroup S} {left right suffix : Word Nat}
    (valid : (Identity.mk left right).SatisfiedBy G) :
    (Identity.mk (left ++ suffix) (right ++ suffix)).SatisfiedBy G := by
  intro valuation
  simp only [Semigroup.eval_append]
  exact congrArg
    (fun value => G.mul value (G.eval valuation suffix))
    (valid valuation)

private theorem singleton_bind
    (letter : Nat) (substitution : Nat → Word Nat) :
    (Word.singleton letter).bind substitution = substitution letter :=
  rfl

private theorem append_as_context
    (middle : Word Nat) (postHead : Nat) (postTail : List Nat) :
    middle ++ Word.mk postHead postTail =
      contextWord [] middle (postHead :: postTail) := by
  apply Word.toList_injective
  rw [Word.toList_append, contextWord_toList]
  rfl

private theorem prepend_as_context
    (preHead : Nat) (preTail : List Nat) (middle : Word Nat) :
    Word.mk preHead preTail ++ middle =
      contextWord (preHead :: preTail) middle [] := by
  apply Word.toList_injective
  rw [Word.toList_append, contextWord_toList]
  simp [Word.toList]

private theorem both_as_context
    (preHead : Nat) (preTail : List Nat) (middle : Word Nat)
    (postHead : Nat) (postTail : List Nat) :
    (Word.mk preHead preTail ++ middle) ++ Word.mk postHead postTail =
      contextWord (preHead :: preTail) middle (postHead :: postTail) := by
  apply Word.toList_injective
  rw [Word.toList_append, Word.toList_append, contextWord_toList]
  simp [Word.toList, List.append_assoc]

/-- Arbitrary left and right contexts can be absorbed into a source identity
using at most two fresh variables.  Empty contexts consume no fresh variable.
The packed identity remains valid, and both packed sides map exactly to the
two contextual substitution instances. -/
theorem exists_context_packing
    {G : Semigroup S} {identity : Identity Nat} {bound : Nat}
    (valid : identity.SatisfiedBy G)
    (uses : identity.UsesAtMost bound)
    (pre post : List Nat) (substitution : Nat → Word Nat) :
    ∃ packed : Identity Nat, ∃ augmented : Nat → Word Nat,
      packed.SatisfiedBy G ∧
      packed.UsesAtMost (bound + 2) ∧
      packed.lhs.bind augmented =
        contextWord pre (identity.lhs.bind substitution) post ∧
      packed.rhs.bind augmented =
        contextWord pre (identity.rhs.bind substitution) post := by
  rcases uses with
    ⟨variables, lengthBound, leftUses, rightUses⟩
  cases pre with
  | nil =>
      cases post with
      | nil =>
          refine ⟨identity, substitution, valid, ?_, ?_, ?_⟩
          · exact
              ⟨variables, by omega, leftUses, rightUses⟩
          · simp
          · simp
      | cons postHead postTail =>
          let fresh := freshAbove variables
          let postWord : Word Nat := ⟨postHead, postTail⟩
          let augmented : Nat → Word Nat :=
            fun letter =>
              if letter = fresh then postWord else substitution letter
          have freshNot : fresh ∉ variables :=
            freshAbove_not_mem variables
          have leftBind :
              identity.lhs.bind augmented =
                identity.lhs.bind substitution := by
            apply bind_congr_of_usesOnly leftUses
            intro letter member
            have different : letter ≠ fresh := by
              intro equality
              apply freshNot
              simpa [equality] using member
            simp [augmented, different]
          have rightBind :
              identity.rhs.bind augmented =
                identity.rhs.bind substitution := by
            apply bind_congr_of_usesOnly rightUses
            intro letter member
            have different : letter ≠ fresh := by
              intro equality
              apply freshNot
              simpa [equality] using member
            simp [augmented, different]
          let packed : Identity Nat :=
            ⟨identity.lhs ++ Word.singleton fresh,
              identity.rhs ++ Word.singleton fresh⟩
          refine ⟨packed, augmented, append_valid valid, ?_, ?_, ?_⟩
          · refine
              ⟨fresh :: variables, by simp; omega, ?_, ?_⟩
            · apply append_usesOnly
              · exact leftUses.mono (fun x member => by simp [member])
              · exact singleton_usesOnly _ _ (by simp)
            · apply append_usesOnly
              · exact rightUses.mono (fun x member => by simp [member])
              · exact singleton_usesOnly _ _ (by simp)
          · simp only [packed, bind_append, singleton_bind, leftBind]
            simpa [augmented, postWord] using
              append_as_context
                (identity.lhs.bind substitution) postHead postTail
          · simp only [packed, bind_append, singleton_bind, rightBind]
            simpa [augmented, postWord] using
              append_as_context
                (identity.rhs.bind substitution) postHead postTail
  | cons preHead preTail =>
      cases post with
      | nil =>
          let fresh := freshAbove variables
          let preWord : Word Nat := ⟨preHead, preTail⟩
          let augmented : Nat → Word Nat :=
            fun letter =>
              if letter = fresh then preWord else substitution letter
          have freshNot : fresh ∉ variables :=
            freshAbove_not_mem variables
          have leftBind :
              identity.lhs.bind augmented =
                identity.lhs.bind substitution := by
            apply bind_congr_of_usesOnly leftUses
            intro letter member
            have different : letter ≠ fresh := by
              intro equality
              apply freshNot
              simpa [equality] using member
            simp [augmented, different]
          have rightBind :
              identity.rhs.bind augmented =
                identity.rhs.bind substitution := by
            apply bind_congr_of_usesOnly rightUses
            intro letter member
            have different : letter ≠ fresh := by
              intro equality
              apply freshNot
              simpa [equality] using member
            simp [augmented, different]
          let packed : Identity Nat :=
            ⟨Word.singleton fresh ++ identity.lhs,
              Word.singleton fresh ++ identity.rhs⟩
          refine ⟨packed, augmented, prepend_valid valid, ?_, ?_, ?_⟩
          · refine
              ⟨fresh :: variables, by simp; omega, ?_, ?_⟩
            · apply append_usesOnly
              · exact singleton_usesOnly _ _ (by simp)
              · exact leftUses.mono (fun x member => by simp [member])
            · apply append_usesOnly
              · exact singleton_usesOnly _ _ (by simp)
              · exact rightUses.mono (fun x member => by simp [member])
          · simp only [packed, bind_append, singleton_bind, leftBind]
            simpa [augmented, preWord] using
              prepend_as_context preHead preTail
                (identity.lhs.bind substitution)
          · simp only [packed, bind_append, singleton_bind, rightBind]
            simpa [augmented, preWord] using
              prepend_as_context preHead preTail
                (identity.rhs.bind substitution)
      | cons postHead postTail =>
          let leftFresh := freshAbove variables
          let rightFresh := leftFresh + 1
          let preWord : Word Nat := ⟨preHead, preTail⟩
          let postWord : Word Nat := ⟨postHead, postTail⟩
          let augmented : Nat → Word Nat :=
            fun letter =>
              if letter = leftFresh then preWord
              else if letter = rightFresh then postWord
              else substitution letter
          have leftFreshNot : leftFresh ∉ variables :=
            freshAbove_not_mem variables
          have rightFreshNot : rightFresh ∉ variables :=
            freshAbove_succ_not_mem variables
          have freshDifferent : rightFresh ≠ leftFresh := by
            simp [rightFresh]
          have leftBind :
              identity.lhs.bind augmented =
                identity.lhs.bind substitution := by
            apply bind_congr_of_usesOnly leftUses
            intro letter member
            have leftDifferent : letter ≠ leftFresh := by
              intro equality
              apply leftFreshNot
              simpa [equality] using member
            have rightDifferent : letter ≠ rightFresh := by
              intro equality
              apply rightFreshNot
              simpa [equality] using member
            simp [augmented, leftDifferent, rightDifferent]
          have rightBind :
              identity.rhs.bind augmented =
                identity.rhs.bind substitution := by
            apply bind_congr_of_usesOnly rightUses
            intro letter member
            have leftDifferent : letter ≠ leftFresh := by
              intro equality
              apply leftFreshNot
              simpa [equality] using member
            have rightDifferent : letter ≠ rightFresh := by
              intro equality
              apply rightFreshNot
              simpa [equality] using member
            simp [augmented, leftDifferent, rightDifferent]
          let packed : Identity Nat :=
            ⟨(Word.singleton leftFresh ++ identity.lhs) ++
                Word.singleton rightFresh,
              (Word.singleton leftFresh ++ identity.rhs) ++
                Word.singleton rightFresh⟩
          refine
            ⟨packed, augmented, append_valid (prepend_valid valid),
              ?_, ?_, ?_⟩
          · refine
              ⟨leftFresh :: rightFresh :: variables,
                by simp; omega, ?_, ?_⟩
            · apply append_usesOnly
              · apply append_usesOnly
                · exact singleton_usesOnly _ _ (by simp)
                · exact leftUses.mono (fun x member => by simp [member])
              · exact singleton_usesOnly _ _ (by simp)
            · apply append_usesOnly
              · apply append_usesOnly
                · exact singleton_usesOnly _ _ (by simp)
                · exact rightUses.mono (fun x member => by simp [member])
              · exact singleton_usesOnly _ _ (by simp)
          · simp only [packed, bind_append, singleton_bind, leftBind]
            simpa [augmented, freshDifferent, preWord, postWord] using
              both_as_context preHead preTail
                (identity.lhs.bind substitution) postHead postTail
          · simp only [packed, bind_append, singleton_bind, rightBind]
            simpa [augmented, freshDifferent, preWord, postWord] using
              both_as_context preHead preTail
                (identity.rhs.bind substitution) postHead postTail

/-- A single source word has a variable cover of the stated size. -/
def WordUsesAtMost (word : Word Nat) (bound : Nat) : Prop :=
  ∃ variables : List Nat,
    variables.length ≤ bound ∧ word.UsesOnly variables

private theorem middleVariables_count_le_one
    (extra letter : Nat) :
    (middleVariables extra).count letter ≤ 1 := by
  induction extra with
  | zero => simp [middleVariables]
  | succ extra ih =>
      have step :
          middleVariables (extra + 1) =
            middleVariables extra ++ [extra + 2] := by
        simp [middleVariables, List.range_succ]
      rw [step, List.count_append]
      by_cases equality : letter = extra + 2
      · subst letter
        have absent : extra + 2 ∉ middleVariables extra := by
          intro member
          rcases List.mem_map.mp member with
            ⟨index, indexMember, equality⟩
          have indexSmall := List.mem_range.mp indexMember
          omega
        simp [List.count_eq_zero.mpr absent]
      · have reverseEquality : extra + 2 ≠ letter :=
          Ne.symm equality
        simp [reverseEquality]
        exact ih

private theorem middleVariables_member_bounds
    {extra letter : Nat}
    (member : letter ∈ middleVariables extra) :
    letter ≠ 0 ∧ letter ≠ 1 := by
  rcases List.mem_map.mp member with
    ⟨index, _, rfl⟩
  omega

/-- Every letter occurs at most twice in a Perkins occurrence-pattern word. -/
theorem OccurrencePattern.count_le_two
    {extra : Nat} {letters : List Nat}
    (pattern : OccurrencePattern extra letters)
    (letter : Nat) :
    letters.count letter ≤ 2 := by
  rcases pattern with
    ⟨firstMiddle, secondMiddle, firstPerm, secondPerm, rfl⟩
  have firstCount :
      firstMiddle.count letter =
        (middleVariables extra).count letter :=
    (List.perm_iff_count.mp firstPerm) letter
  have secondCount :
      secondMiddle.count letter =
        (middleVariables extra).count letter :=
    (List.perm_iff_count.mp secondPerm) letter
  simp only [List.count_append, List.count_cons, List.count_nil]
  rw [firstCount, secondCount]
  have middleBound := middleVariables_count_le_one extra letter
  by_cases zero : letter = 0
  · subst letter
    have absent : 0 ∉ middleVariables extra := by
      intro member
      exact (middleVariables_member_bounds member).1 rfl
    simp [List.count_eq_zero.mpr absent]
  · by_cases oneLetter : letter = 1
    · subst letter
      have absent : 1 ∉ middleVariables extra := by
        intro member
        exact (middleVariables_member_bounds member).2 rfl
      simp [List.count_eq_zero.mpr absent]
    · have zeroReverse : 0 ≠ letter := by
        exact Ne.symm zero
      have oneReverse : 1 ≠ letter := by
        exact Ne.symm oneLetter
      simp [zeroReverse, oneReverse]
      omega

private def nonskeleton (letter : Nat) : Bool :=
  letter != 0 && letter != 1

/-- Deleting `x` and `y₁` from a Perkins occurrence-pattern word leaves
exactly the two blocks of `4 * bound + 7` middle occurrences. -/
theorem OccurrencePattern.nonskeleton_length
    {extra : Nat} {letters : List Nat}
    (pattern : OccurrencePattern extra letters) :
    (letters.filter nonskeleton).length = 2 * extra := by
  rcases pattern with
    ⟨firstMiddle, secondMiddle, firstPerm, secondPerm, rfl⟩
  have firstFilter :
      firstMiddle.filter nonskeleton = firstMiddle := by
    apply List.filter_eq_self.mpr
    intro letter member
    have middleMember : letter ∈ middleVariables extra :=
      firstPerm.mem_iff.mp member
    have bounds := middleVariables_member_bounds middleMember
    simp [nonskeleton, bounds.1, bounds.2]
  have secondFilter :
      secondMiddle.filter nonskeleton = secondMiddle := by
    apply List.filter_eq_self.mpr
    intro letter member
    have middleMember : letter ∈ middleVariables extra :=
      secondPerm.mem_iff.mp member
    have bounds := middleVariables_member_bounds middleMember
    simp [nonskeleton, bounds.1, bounds.2]
  have firstLength := firstPerm.length_eq
  have secondLength := secondPerm.length_eq
  simp only [List.filter_append, List.filter_cons, List.filter_nil]
  rw [firstFilter, secondFilter]
  simp [nonskeleton]
  rw [firstLength, secondLength]
  simp [middleVariables]
  omega

private theorem count_le_flatMap_count_of_mem
    (source : List Nat) (images : Nat → List Nat)
    (sourceLetter marker : Nat)
    (markerMember : marker ∈ images sourceLetter) :
    source.count sourceLetter ≤
      (source.flatMap images).count marker := by
  induction source with
  | nil => simp
  | cons first rest ih =>
      simp only [List.flatMap_cons, List.count_append, List.count_cons]
      by_cases equality : first = sourceLetter
      · subst first
        have positive :
            1 ≤ (images sourceLetter).count marker :=
          List.count_pos_iff.mpr markerMember
        have combined := Nat.add_le_add positive ih
        simpa [Nat.add_comm] using combined
      · simp [equality]
        exact Nat.le_trans ih (Nat.le_add_left _ _)

/-- Every source variable occurs at most twice when a nonerasing
substitution maps the source word to a Perkins occurrence-pattern word. -/
theorem preimage_variable_count_le_two
    {source target : Word Nat}
    {substitution : Nat → Word Nat}
    (mapped : source.bind substitution = target)
    (pattern : OccurrencePattern extra target.toList)
    {sourceLetter : Nat}
    (_member : sourceLetter ∈ source.toList) :
    source.toList.count sourceLetter ≤ 2 := by
  let marker := (substitution sourceLetter).head
  have markerMember :
      marker ∈ (substitution sourceLetter).toList := by
    simp [marker, Word.toList]
  have bound :=
    count_le_flatMap_count_of_mem source.toList
      (fun letter => (substitution letter).toList)
      sourceLetter marker markerMember
  rw [← Word.toList_bind, mapped] at bound
  exact Nat.le_trans bound (pattern.count_le_two marker)

private theorem length_eq_count_add_filter_ne
    (letters : List Nat) (letter : Nat) :
    letters.length =
      letters.count letter +
        (letters.filter fun value => value != letter).length := by
  induction letters with
  | nil => simp
  | cons first rest ih =>
      by_cases equality : first = letter
      · subst first
        simp [ih]
        omega
      · simp [equality, ih]
        omega

private theorem count_filter_ne_eq
    (letters : List Nat) {removed retained : Nat}
    (different : retained ≠ removed) :
    (letters.filter fun value => value != removed).count retained =
      letters.count retained := by
  induction letters with
  | nil => simp
  | cons first rest ih =>
      by_cases firstRemoved : first = removed
      · subst first
        have reverseDifferent : removed ≠ retained :=
          Ne.symm different
        simp [reverseDifferent, ih]
      · by_cases firstRetained : first = retained
        · subst first
          simp [firstRemoved, ih]
        · simp [firstRemoved, firstRetained, ih]

private theorem length_le_two_mul_of_cover :
    ∀ (letters variables : List Nat),
      (∀ letter, letter ∈ letters → letter ∈ variables) →
      (∀ letter, letter ∈ letters → letters.count letter ≤ 2) →
      letters.length ≤ 2 * variables.length
  | [], variables, _, _ => by simp
  | first :: rest, [], covered, _ => by
      have impossible := covered first (by simp)
      simp at impossible
  | letters, pivot :: variables, covered, bounded => by
      let remainder :=
        letters.filter fun letter => letter != pivot
      have remainderCovered :
          ∀ letter, letter ∈ remainder → letter ∈ variables := by
        intro letter member
        have filtered := List.mem_filter.mp member
        have notPivot : letter ≠ pivot := by
          simpa using filtered.2
        have inCover := covered letter filtered.1
        simp only [List.mem_cons] at inCover
        rcases inCover with equality | member
        · exact False.elim (notPivot equality)
        · exact member
      have remainderBounded :
          ∀ letter, letter ∈ remainder →
            remainder.count letter ≤ 2 := by
        intro letter member
        have filtered := List.mem_filter.mp member
        have notPivot : letter ≠ pivot := by
          simpa using filtered.2
        rw [count_filter_ne_eq letters notPivot]
        exact bounded letter filtered.1
      have inductionBound :=
        length_le_two_mul_of_cover
          remainder variables remainderCovered remainderBounded
      have pivotBound : letters.count pivot ≤ 2 := by
        by_cases member : pivot ∈ letters
        · exact bounded pivot member
        · simp [List.count_eq_zero.mpr member]
      have decomposition :=
        length_eq_count_add_filter_ne letters pivot
      change letters.length ≤ 2 * (pivot :: variables).length
      change remainder.length ≤ 2 * variables.length at inductionBound
      change
        letters.length =
          letters.count pivot + remainder.length at decomposition
      simp only [List.length_cons]
      omega

/-- A packed source word covered by `bound` variables has at most
`2 * bound` source occurrences. -/
theorem preimage_word_length_le_two_mul
    {source target : Word Nat}
    (uses : WordUsesAtMost source bound)
    {substitution : Nat → Word Nat}
    (mapped : source.bind substitution = target)
    (pattern : OccurrencePattern extra target.toList) :
    source.toList.length ≤ 2 * bound := by
  rcases uses with ⟨variables, variableBound, covered⟩
  have lengthBound :
      source.toList.length ≤ 2 * variables.length :=
    length_le_two_mul_of_cover source.toList variables covered
      (fun letter member =>
        preimage_variable_count_le_two mapped pattern member)
  omega

private theorem filtered_flatMap_length_le_two_mul
    (source : List Nat) (images : Nat → List Nat)
    (keep : Nat → Bool)
    (small :
      ∀ letter, letter ∈ source →
        ((images letter).filter keep).length ≤ 2) :
    ((source.flatMap images).filter keep).length ≤
      2 * source.length := by
  induction source with
  | nil => simp
  | cons first rest ih =>
      simp only [List.flatMap_cons, List.filter_append,
        List.length_append, List.length_cons]
      have firstSmall := small first (by simp)
      have restSmall :
          ∀ letter, letter ∈ rest →
            ((images letter).filter keep).length ≤ 2 := by
        intro letter member
        exact small letter (by simp [member])
      have restBound := ih restSmall
      omega

/-- Among the `4 * bound + 7` middle variables, one occurrence-container
of a source word on at most `bound + 2` variables contains at least three
middle occurrences.  The `+2` is exactly the context-packing overhead. -/
theorem exists_occurrence_container_with_three_middle
    {source target : Word Nat}
    (uses : WordUsesAtMost source (bound + 2))
    {substitution : Nat → Word Nat}
    (mapped : source.bind substitution = target)
    (pattern :
      OccurrencePattern (4 * bound + 7) target.toList) :
    ∃ sourceLetter,
      sourceLetter ∈ source.toList ∧
      3 ≤ ((substitution sourceLetter).toList.filter nonskeleton).length := by
  by_cases existsLarge :
      ∃ sourceLetter,
        sourceLetter ∈ source.toList ∧
        3 ≤
          ((substitution sourceLetter).toList.filter nonskeleton).length
  · exact existsLarge
  · exfalso
    have everySmall :
        ∀ sourceLetter, sourceLetter ∈ source.toList →
          ((substitution sourceLetter).toList.filter nonskeleton).length ≤ 2 := by
      intro sourceLetter member
      have notLarge :
          ¬3 ≤
            ((substitution sourceLetter).toList.filter nonskeleton).length := by
        intro large
        exact existsLarge ⟨sourceLetter, member, large⟩
      omega
    have filteredBound :=
      filtered_flatMap_length_le_two_mul source.toList
        (fun letter => (substitution letter).toList)
        nonskeleton everySmall
    rw [← Word.toList_bind, mapped] at filteredBound
    have sourceBound :=
      preimage_word_length_le_two_mul uses mapped pattern
    have targetLength := pattern.nonskeleton_length
    omega

private theorem count_le_flatMap_count_of_source_mem
    {source : List Nat} {images : Nat → List Nat}
    {sourceLetter marker : Nat}
    (sourceMember : sourceLetter ∈ source) :
    (images sourceLetter).count marker ≤
      (source.flatMap images).count marker := by
  induction source with
  | nil => simp at sourceMember
  | cons first rest ih =>
      simp only [List.mem_cons] at sourceMember
      simp only [List.flatMap_cons, List.count_append]
      rcases sourceMember with rfl | sourceMember
      · exact Nat.le_add_right _ _
      · exact Nat.le_trans (ih sourceMember) (Nat.le_add_left _ _)

private theorem count_filter_le
    (letters : List Nat) (keep : Nat → Bool) (letter : Nat) :
    (letters.filter keep).count letter ≤ letters.count letter := by
  induction letters with
  | nil => simp
  | cons first rest ih =>
      by_cases kept : keep first
      · by_cases equality : first = letter
        · subst first
          simp [kept]
        · have reverseEquality : letter ≠ first :=
            Ne.symm equality
          simpa [kept, equality, reverseEquality] using ih
      · by_cases equality : first = letter
        · subst first
          simp [kept]
          exact Nat.le_trans ih (Nat.le_add_right _ _)
        · have reverseEquality : letter ≠ first :=
            Ne.symm equality
          simpa [kept, equality, reverseEquality] using ih

private theorem exists_distinct_of_length_three_of_count_le_two
    {letters : List Nat}
    (large : 3 ≤ letters.length)
    (counts : ∀ letter, letters.count letter ≤ 2) :
    ∃ first second,
      first ≠ second ∧ first ∈ letters ∧ second ∈ letters := by
  rcases letters with _ | ⟨first, rest⟩
  · simp at large
  rcases rest with _ | ⟨second, rest⟩
  · simp at large
  rcases rest with _ | ⟨third, rest⟩
  · simp at large
  by_cases equality : first = second
  · subst second
    by_cases differentThird : first ≠ third
    · exact ⟨first, third, differentThird, by simp, by simp⟩
    · have thirdEquality : third = first := by
        exact (Decidable.byContradiction differentThird).symm
      subst third
      have bound := counts first
      simp at bound
  · refine ⟨first, second, ?_, ?_, ?_⟩
    · exact equality
    · simp
    · simp

/-- The large occurrence-container contains two distinct middle markers.
They are genuine members of `middleVariables (4 * bound + 7)`, not merely
letters different from `x` and `y₁`. -/
theorem occurrence_container_has_distinct_middle_markers
    {source target : Word Nat}
    {substitution : Nat → Word Nat}
    (mapped : source.bind substitution = target)
    (pattern :
      OccurrencePattern (4 * bound + 7) target.toList)
    {sourceLetter : Nat}
    (sourceMember : sourceLetter ∈ source.toList)
    (large :
      3 ≤ ((substitution sourceLetter).toList.filter nonskeleton).length) :
    ∃ first second,
      first ≠ second ∧
      first ∈ middleVariables (4 * bound + 7) ∧
      second ∈ middleVariables (4 * bound + 7) ∧
      first ∈ (substitution sourceLetter).toList ∧
      second ∈ (substitution sourceLetter).toList := by
  let selected :=
    (substitution sourceLetter).toList.filter nonskeleton
  have selectedCounts :
      ∀ letter, selected.count letter ≤ 2 := by
    intro letter
    have filterBound :=
      count_filter_le
        (substitution sourceLetter).toList nonskeleton letter
    have imageBound :=
      count_le_flatMap_count_of_source_mem
        (images := fun value => (substitution value).toList)
        (marker := letter) sourceMember
    rw [← Word.toList_bind, mapped] at imageBound
    exact Nat.le_trans filterBound
      (Nat.le_trans imageBound (pattern.count_le_two letter))
  rcases
      exists_distinct_of_length_three_of_count_le_two
        (letters := selected) large selectedCounts with
    ⟨first, second, different, firstSelected, secondSelected⟩
  have firstImage := (List.mem_filter.mp firstSelected).1
  have secondImage := (List.mem_filter.mp secondSelected).1
  have firstTarget : first ∈ target.toList := by
    rw [← mapped, Word.toList_bind]
    exact List.mem_flatMap.mpr
      ⟨sourceLetter, sourceMember, firstImage⟩
  have secondTarget : second ∈ target.toList := by
    rw [← mapped, Word.toList_bind]
    exact List.mem_flatMap.mpr
      ⟨sourceLetter, sourceMember, secondImage⟩
  have firstDomain := pattern.mem firstTarget
  have secondDomain := pattern.mem secondTarget
  have firstKept := (List.mem_filter.mp firstSelected).2
  have secondKept := (List.mem_filter.mp secondSelected).2
  simp [nonskeleton] at firstKept secondKept
  rcases firstDomain with rfl | rfl | firstMiddle
  · exact False.elim (firstKept.1 rfl)
  · exact False.elim (firstKept.2 rfl)
  · rcases secondDomain with rfl | rfl | secondMiddle
    · exact False.elim (secondKept.1 rfl)
    · exact False.elim (secondKept.2 rfl)
    · exact
        ⟨first, second, different, firstMiddle, secondMiddle,
          firstImage, secondImage⟩

/-- Combined quantitative selection theorem used by the four isoterm cases:
after context packing, a bounded source has an occurrence-container carrying
two distinct middle markers. -/
theorem select_distinct_middle_markers
    {source target : Word Nat}
    (uses : WordUsesAtMost source (bound + 2))
    {substitution : Nat → Word Nat}
    (mapped : source.bind substitution = target)
    (pattern :
      OccurrencePattern (4 * bound + 7) target.toList) :
    ∃ sourceLetter first second,
      sourceLetter ∈ source.toList ∧
      source.toList.count sourceLetter ≤ 2 ∧
      first ≠ second ∧
      first ∈ middleVariables (4 * bound + 7) ∧
      second ∈ middleVariables (4 * bound + 7) ∧
      first ∈ (substitution sourceLetter).toList ∧
      second ∈ (substitution sourceLetter).toList := by
  rcases
      exists_occurrence_container_with_three_middle
        uses mapped pattern with
    ⟨sourceLetter, sourceMember, large⟩
  rcases
      occurrence_container_has_distinct_middle_markers
        mapped pattern sourceMember large with
    ⟨first, second, different, firstMiddle, secondMiddle,
      firstImage, secondImage⟩
  exact
    ⟨sourceLetter, first, second, sourceMember,
      preimage_variable_count_le_two mapped pattern sourceMember,
      different, firstMiddle, secondMiddle, firstImage, secondImage⟩

private theorem count_mul_le_flatMap_count
    (source : List Nat) (images : Nat → List Nat)
    (sourceLetter marker : Nat) :
    source.count sourceLetter * (images sourceLetter).count marker ≤
      (source.flatMap images).count marker := by
  induction source with
  | nil => simp
  | cons first rest ih =>
      simp only [List.flatMap_cons, List.count_append]
      by_cases equality : first = sourceLetter
      · subst first
        have combined :=
          Nat.add_le_add ih
            (Nat.le_refl ((images sourceLetter).count marker))
        simpa [Nat.add_mul, Nat.add_comm, Nat.add_left_comm,
          Nat.add_assoc] using combined
      · rw [List.count_cons_of_ne equality]
        exact Nat.le_trans ih (Nat.le_add_left _ _)

private theorem count_filter_of_kept
    (letters : List Nat) (keep : Nat → Bool) (letter : Nat)
    (kept : keep letter = true) :
    (letters.filter keep).count letter = letters.count letter := by
  induction letters with
  | nil => simp
  | cons first rest ih =>
      by_cases firstKept : keep first
      · by_cases equality : first = letter
        · subst first
          simp [kept, ih]
        · simp [firstKept, equality, ih]
      · have firstDifferent : first ≠ letter := by
          intro equality
          subst first
          exact firstKept kept
        simp [firstKept, firstDifferent, ih]

private theorem count_eq_one_decompose
    (letter : Nat) :
    ∀ letters : List Nat,
      letters.count letter = 1 →
      ∃ before after,
        letters = before ++ letter :: after
  | [], count => by simp at count
  | first :: rest, count => by
      by_cases equality : first = letter
      · subst first
        exact ⟨[], rest, rfl⟩
      · have reverseEquality : letter ≠ first :=
          Ne.symm equality
        have restCount : rest.count letter = 1 := by
          rw [List.count_cons_of_ne equality] at count
          exact count
        rcases count_eq_one_decompose letter rest restCount with
          ⟨before, after, decomposition⟩
        exact ⟨first :: before, after, by simp [decomposition]⟩

private theorem count_eq_two_decompose
    (letter : Nat) :
    ∀ letters : List Nat,
      letters.count letter = 2 →
      ∃ before between after,
        letters =
          before ++ letter :: between ++ letter :: after
  | [], count => by simp at count
  | first :: rest, count => by
      by_cases equality : first = letter
      · subst first
        have restCount : rest.count letter = 1 := by
          simpa using count
        rcases count_eq_one_decompose letter rest restCount with
          ⟨between, after, decomposition⟩
        exact ⟨[], between, after, by simp [decomposition]⟩
      · have reverseEquality : letter ≠ first :=
          Ne.symm equality
        have restCount : rest.count letter = 2 := by
          rw [List.count_cons_of_ne equality] at count
          exact count
        rcases count_eq_two_decompose letter rest restCount with
          ⟨before, between, after, decomposition⟩
        exact
          ⟨first :: before, between, after,
            by simp [decomposition]⟩

private theorem pairKeep_member
    {letters : List Nat} {first second letter : Nat}
    (member :
      letter ∈
        (letters.filter (pairKeep first second))) :
    letter = first ∨ letter = second := by
  have kept := (List.mem_filter.mp member).2
  simp [pairKeep] at kept
  exact kept

private theorem length_eq_pair_counts
    {first second : Nat} (different : first ≠ second) :
    ∀ letters : List Nat,
      (∀ letter, letter ∈ letters →
        letter = first ∨ letter = second) →
      letters.length =
        letters.count first + letters.count second
  | [], _ => by simp
  | letter :: rest, onlyPair => by
      have headPair := onlyPair letter (by simp)
      have restPair :
          ∀ value, value ∈ rest →
            value = first ∨ value = second := by
        intro value member
        exact onlyPair value (by simp [member])
      have induction := length_eq_pair_counts different rest restPair
      rcases headPair with rfl | rfl
      · simp [different, induction]
        omega
      · simp [Ne.symm different, induction]
        omega

private theorem pair_filter_shape_of_counts_one
    (letters : List Nat) {first second : Nat}
    (different : first ≠ second)
    (firstCount : letters.count first = 1)
    (secondCount : letters.count second = 1)
    (onlyPair :
      ∀ letter, letter ∈ letters →
        letter = first ∨ letter = second) :
    letters = [first, second] ∨ letters = [second, first] := by
  have lengthTwo :
      letters.length = 2 := by
    rw [length_eq_pair_counts different letters onlyPair,
      firstCount, secondCount]
  rcases letters with _ | ⟨head, rest⟩
  · simp at lengthTwo
  rcases rest with _ | ⟨next, rest⟩
  · simp at lengthTwo
  have restEmpty : rest = [] := by
    apply List.eq_nil_of_length_eq_zero
    simpa using lengthTwo
  subst rest
  have headPair := onlyPair head (by simp)
  have nextPair := onlyPair next (by simp)
  rcases headPair with rfl | rfl
  · rcases nextPair with rfl | rfl
    · simp at firstCount
    · exact Or.inl rfl
  · rcases nextPair with rfl | rfl
    · exact Or.inr rfl
    · simp at secondCount

private theorem pair_filter_eq_nil_of_counts_zero
    (letters : List Nat) {first second : Nat}
    (firstZero : letters.count first = 0)
    (secondZero : letters.count second = 0) :
    letters.filter (pairKeep first second) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro letter member
  have firstAbsent : first ∉ letters :=
    List.count_eq_zero.mp firstZero
  have secondAbsent : second ∉ letters :=
    List.count_eq_zero.mp secondZero
  have firstDifferent : letter ≠ first := by
    intro equality
    subst letter
    exact firstAbsent member
  have secondDifferent : letter ≠ second := by
    intro equality
    subst letter
    exact secondAbsent member
  simp [pairKeep, firstDifferent, secondDifferent]

/-- If a source variable occurs twice and its image contains two distinct
markers, the two-marker projection of the target is alternating.  The proof
uses the global two-occurrence bound to show that no other source occurrence
can contribute either marker. -/
theorem repeated_source_forces_alternating_projection
    {source target : Word Nat}
    {substitution : Nat → Word Nat}
    (mapped : source.bind substitution = target)
    (pattern : OccurrencePattern extra target.toList)
    {sourceLetter first second : Nat}
    (sourceCount : source.toList.count sourceLetter = 2)
    (different : first ≠ second)
    (firstImage : first ∈ (substitution sourceLetter).toList)
    (secondImage : second ∈ (substitution sourceLetter).toList) :
    target.toList.filter (pairKeep first second) =
        [first, second, first, second] ∨
      target.toList.filter (pairKeep first second) =
        [second, first, second, first] := by
  let images : Nat → List Nat :=
    fun letter => (substitution letter).toList
  let imageProjection :=
    (images sourceLetter).filter (pairKeep first second)
  have targetFirstLower :
      2 ≤ target.toList.count first := by
    have product :=
      count_mul_le_flatMap_count source.toList images
        sourceLetter first
    rw [sourceCount, ← Word.toList_bind, mapped] at product
    have positive : 1 ≤ (images sourceLetter).count first :=
      List.count_pos_iff.mpr firstImage
    omega
  have targetSecondLower :
      2 ≤ target.toList.count second := by
    have product :=
      count_mul_le_flatMap_count source.toList images
        sourceLetter second
    rw [sourceCount, ← Word.toList_bind, mapped] at product
    have positive : 1 ≤ (images sourceLetter).count second :=
      List.count_pos_iff.mpr secondImage
    omega
  have targetFirstCount : target.toList.count first = 2 :=
    Nat.le_antisymm (pattern.count_le_two first) targetFirstLower
  have targetSecondCount : target.toList.count second = 2 :=
    Nat.le_antisymm (pattern.count_le_two second) targetSecondLower
  have imageFirstCount :
      (images sourceLetter).count first = 1 := by
    have product :=
      count_mul_le_flatMap_count source.toList images
        sourceLetter first
    rw [sourceCount, ← Word.toList_bind, mapped,
      targetFirstCount] at product
    have positive : 1 ≤ (images sourceLetter).count first :=
      List.count_pos_iff.mpr firstImage
    omega
  have imageSecondCount :
      (images sourceLetter).count second = 1 := by
    have product :=
      count_mul_le_flatMap_count source.toList images
        sourceLetter second
    rw [sourceCount, ← Word.toList_bind, mapped,
      targetSecondCount] at product
    have positive : 1 ≤ (images sourceLetter).count second :=
      List.count_pos_iff.mpr secondImage
    omega
  have firstKept : pairKeep first second first = true := by
    simp [pairKeep]
  have secondKept : pairKeep first second second = true := by
    simp [pairKeep]
  have projectionFirstCount :
      imageProjection.count first = 1 := by
    simpa [imageProjection] using
      (count_filter_of_kept
        (images sourceLetter) (pairKeep first second)
        first firstKept).trans imageFirstCount
  have projectionSecondCount :
      imageProjection.count second = 1 := by
    simpa [imageProjection] using
      (count_filter_of_kept
        (images sourceLetter) (pairKeep first second)
        second secondKept).trans imageSecondCount
  have projectionOnlyPair :
      ∀ letter, letter ∈ imageProjection →
        letter = first ∨ letter = second := by
    intro letter member
    exact pairKeep_member member
  have projectionShape :=
    pair_filter_shape_of_counts_one imageProjection different
      projectionFirstCount projectionSecondCount projectionOnlyPair
  rcases
      count_eq_two_decompose sourceLetter source.toList sourceCount with
    ⟨before, between, after, sourceShape⟩
  let beforeImage := before.flatMap images
  let betweenImage := between.flatMap images
  let afterImage := after.flatMap images
  have targetShape :
      target.toList =
        beforeImage ++ images sourceLetter ++ betweenImage ++
          images sourceLetter ++ afterImage := by
    rw [← mapped, Word.toList_bind, sourceShape]
    simp [images, beforeImage, betweenImage, afterImage,
      List.flatMap_append, List.append_assoc]
  have firstCountEquation :
      beforeImage.count first +
          betweenImage.count first +
          afterImage.count first = 0 := by
    rw [targetShape] at targetFirstCount
    simp only [List.count_append] at targetFirstCount
    rw [imageFirstCount] at targetFirstCount
    omega
  have secondCountEquation :
      beforeImage.count second +
          betweenImage.count second +
          afterImage.count second = 0 := by
    rw [targetShape] at targetSecondCount
    simp only [List.count_append] at targetSecondCount
    rw [imageSecondCount] at targetSecondCount
    omega
  have beforeProjection :
      beforeImage.filter (pairKeep first second) = [] := by
    apply pair_filter_eq_nil_of_counts_zero beforeImage
    · omega
    · omega
  have betweenProjection :
      betweenImage.filter (pairKeep first second) = [] := by
    apply pair_filter_eq_nil_of_counts_zero betweenImage
    · omega
    · omega
  have afterProjection :
      afterImage.filter (pairKeep first second) = [] := by
    apply pair_filter_eq_nil_of_counts_zero afterImage
    · omega
    · omega
  rw [targetShape]
  simp only [List.filter_append]
  rw [beforeProjection, betweenProjection, afterProjection]
  simp only [List.nil_append, List.append_nil]
  change
    imageProjection ++ imageProjection =
        [first, second, first, second] ∨
      imageProjection ++ imageProjection =
        [second, first, second, first]
  rcases projectionShape with projectionShape | projectionShape
  · left
    rw [projectionShape]
    rfl
  · right
    rw [projectionShape]
    rfl

/-- The selected occurrence-container is a linear source variable.  If it
occurred twice, `repeated_source_forces_alternating_projection` would
contradict the semantic anti-alternation invariant. -/
theorem selected_source_variable_is_linear
    {anchor source target : Word Nat}
    {substitution : Nat → Word Nat}
    (mapped : source.bind substitution = target)
    (pattern : OccurrencePattern extra target.toList)
    (semantic :
      (Identity.mk anchor target).SatisfiedBy table.semigroup)
    {sourceLetter first second : Nat}
    (sourceMember : sourceLetter ∈ source.toList)
    (different : first ≠ second)
    (firstImage : first ∈ (substitution sourceLetter).toList)
    (secondImage : second ∈ (substitution sourceLetter).toList)
    (anchorProjection :
      anchor.toList.filter (pairKeep first second) =
          [first, second, second, first] ∨
        anchor.toList.filter (pairKeep first second) =
          [second, first, first, second]) :
    source.toList.count sourceLetter = 1 := by
  have positive :
      1 ≤ source.toList.count sourceLetter :=
    List.count_pos_iff.mpr sourceMember
  have atMostTwo :=
    preimage_variable_count_le_two mapped pattern sourceMember
  by_cases repeated : source.toList.count sourceLetter = 2
  · have alternating :=
      repeated_source_forces_alternating_projection
        mapped pattern repeated different firstImage secondImage
    exact False.elim
      (semanticClass_forbids_alternating_pair
        different semantic anchorProjection alternating)
  · omega

/-- The obstruction left side has a nested projection on every pair of
distinct middle variables. -/
theorem perkinsLeft_pair_projection
    {extra first second : Nat}
    (different : first ≠ second)
    (firstMiddle : first ∈ middleVariables extra)
    (secondMiddle : second ∈ middleVariables extra) :
    (perkinsLeft extra).toList.filter (pairKeep first second) =
        [first, second, second, first] ∨
      (perkinsLeft extra).toList.filter (pairKeep first second) =
        [second, first, first, second] := by
  let middleProjection :=
    (middleVariables extra).filter (pairKeep first second)
  have firstKept : pairKeep first second first = true := by
    simp [pairKeep]
  have secondKept : pairKeep first second second = true := by
    simp [pairKeep]
  have firstCount :
      middleProjection.count first = 1 := by
    have originalPositive :
        1 ≤ (middleVariables extra).count first :=
      List.count_pos_iff.mpr firstMiddle
    have originalBound :=
      middleVariables_count_le_one extra first
    have originalCount :
        (middleVariables extra).count first = 1 := by
      omega
    simpa [middleProjection] using
      (count_filter_of_kept
        (middleVariables extra) (pairKeep first second)
        first firstKept).trans originalCount
  have secondCount :
      middleProjection.count second = 1 := by
    have originalPositive :
        1 ≤ (middleVariables extra).count second :=
      List.count_pos_iff.mpr secondMiddle
    have originalBound :=
      middleVariables_count_le_one extra second
    have originalCount :
        (middleVariables extra).count second = 1 := by
      omega
    simpa [middleProjection] using
      (count_filter_of_kept
        (middleVariables extra) (pairKeep first second)
        second secondKept).trans originalCount
  have onlyPair :
      ∀ letter, letter ∈ middleProjection →
        letter = first ∨ letter = second := by
    intro letter member
    exact pairKeep_member member
  have middleShape :=
    pair_filter_shape_of_counts_one middleProjection different
      firstCount secondCount onlyPair
  have firstBounds := middleVariables_member_bounds firstMiddle
  have secondBounds := middleVariables_member_bounds secondMiddle
  rw [perkinsLeft_toList]
  simp only [List.filter_append, List.filter_cons, List.filter_nil]
  have zeroDiscarded :
      pairKeep first second 0 = false := by
    simp [pairKeep, Ne.symm firstBounds.1, Ne.symm secondBounds.1]
  have oneDiscarded :
      pairKeep first second 1 = false := by
    simp [pairKeep, Ne.symm firstBounds.2, Ne.symm secondBounds.2]
  simp only [zeroDiscarded, oneDiscarded, Bool.false_eq_true, if_false,
    List.nil_append, List.append_nil]
  have reverseProjection :
      (middleVariables extra).reverse.filter
          (pairKeep first second) =
        middleProjection.reverse := by
    simp [middleProjection]
  rw [reverseProjection]
  change
    middleProjection ++ middleProjection.reverse =
        [first, second, second, first] ∨
      middleProjection ++ middleProjection.reverse =
        [second, first, first, second]
  rcases middleShape with middleShape | middleShape
  · left
    rw [middleShape]
    rfl
  · right
    rw [middleShape]
    rfl

/-- The complete quantitative-and-semantic selection step: after packing
contexts, some source occurrence contains two distinct middle markers and
its source variable is linear. -/
theorem select_linear_middle_marker_container
    {source target : Word Nat}
    (uses : WordUsesAtMost source (bound + 2))
    {substitution : Nat → Word Nat}
    (mapped : source.bind substitution = target)
    (pattern :
      OccurrencePattern (4 * bound + 7) target.toList)
    (semantic :
      (Identity.mk (obstruction bound).lhs target).SatisfiedBy
        table.semigroup) :
    ∃ sourceLetter first second,
      sourceLetter ∈ source.toList ∧
      source.toList.count sourceLetter = 1 ∧
      first ≠ second ∧
      first ∈ middleVariables (4 * bound + 7) ∧
      second ∈ middleVariables (4 * bound + 7) ∧
      first ∈ (substitution sourceLetter).toList ∧
      second ∈ (substitution sourceLetter).toList := by
  rcases select_distinct_middle_markers uses mapped pattern with
    ⟨sourceLetter, first, second, sourceMember, _,
      different, firstMiddle, secondMiddle, firstImage, secondImage⟩
  have anchorProjection :
      (obstruction bound).lhs.toList.filter
            (pairKeep first second) =
          [first, second, second, first] ∨
        (obstruction bound).lhs.toList.filter
            (pairKeep first second) =
          [second, first, first, second] := by
    simpa [obstruction, perkinsIdentity] using
      perkinsLeft_pair_projection different firstMiddle secondMiddle
  have linear :=
    selected_source_variable_is_linear mapped pattern semantic
      sourceMember different firstImage secondImage anchorProjection
  exact
    ⟨sourceLetter, first, second, sourceMember, linear,
      different, firstMiddle, secondMiddle, firstImage, secondImage⟩

/-! ## The four five-variable source projections

The variable convention is `x = 0`, `y = 1`, `z = 2`, `t₁ = 3`,
`t₂ = 4`.  These are the four words listed in Sapir's reconstruction of
Perkins's proof.
-/

def sourceProjectionCase1 : Word Nat :=
  ⟨0, [1, 3, 2, 0, 4, 2, 1]⟩

def sourceProjectionCase2 : Word Nat :=
  ⟨0, [1, 2, 3, 0, 4, 2, 1]⟩

def sourceProjectionCase3 : Word Nat :=
  ⟨0, [1, 3, 2, 0, 2, 4, 1]⟩

def sourceProjectionCase4 : Word Nat :=
  ⟨0, [1, 2, 3, 0, 2, 4, 1]⟩

private def keepThree
    (first second third letter : Nat) : Bool :=
  letter == first || letter == second || letter == third

theorem sourceProjectionCase1_toList :
    sourceProjectionCase1.toList =
      [0, 1, 3, 2, 0, 4, 2, 1] :=
  rfl

theorem sourceProjectionCase2_toList :
    sourceProjectionCase2.toList =
      [0, 1, 2, 3, 0, 4, 2, 1] :=
  rfl

theorem sourceProjectionCase3_toList :
    sourceProjectionCase3.toList =
      [0, 1, 3, 2, 0, 2, 4, 1] :=
  rfl

theorem sourceProjectionCase4_toList :
    sourceProjectionCase4.toList =
      [0, 1, 2, 3, 0, 2, 4, 1] :=
  rfl

/-- In case 1, the `y,z,t₂` deletion is a renaming of `xytyx`. -/
theorem sourceProjectionCase1_yzt2 :
    sourceProjectionCase1.toList.filter (keepThree 1 2 4) =
      [1, 2, 4, 2, 1] := by
  decide

/-- In case 1, the `x,z,t₁` deletion is a renaming of `xtyxy`. -/
theorem sourceProjectionCase1_xzt1 :
    sourceProjectionCase1.toList.filter (keepThree 0 2 3) =
      [0, 3, 2, 0, 2] := by
  decide

/-- In case 2, the `y,z,t₂` deletion is a renaming of `xytyx`. -/
theorem sourceProjectionCase2_yzt2 :
    sourceProjectionCase2.toList.filter (keepThree 1 2 4) =
      [1, 2, 4, 2, 1] := by
  decide

/-- In case 3, the `x,z,t₁` deletion is a renaming of `xtyxy`. -/
theorem sourceProjectionCase3_xzt1 :
    sourceProjectionCase3.toList.filter (keepThree 0 2 3) =
      [0, 3, 2, 0, 2] := by
  decide

/-- In case 4, the `y,z,t₁` deletion is a renaming of `xytyx`. -/
theorem sourceProjectionCase4_yzt1 :
    sourceProjectionCase4.toList.filter (keepThree 1 2 3) =
      [1, 2, 3, 2, 1] := by
  decide

end SemigroupBasis.Nonfinite.B2One
