import SemigroupBasis.Nonfinite.A2One.TrahtmanCriterion

namespace SemigroupBasis.Nonfinite.A2One

open SemigroupBasis

/-!
Combinatorial infrastructure for Trahtman's preimage-rigidity lemma.

The target `anchor (3 * bound)` contains every indexed marker exactly three
times and the separator exactly twice. Since substitutions in `Word.bind`
are nonerasing, every occurrence of a source variable contributes an
occurrence of the head of its image. Consequently every source variable
occurs at most three times, and a source word covered by `bound` variables
has length at most `3 * bound`.

These are the quantitative pigeonhole bounds behind the strict inequality
`bound < (3 * bound + 2) / 3` in Trahtman's argument.
-/

theorem anchor_toList (extra : Nat) :
    (anchor extra).toList =
      List.range (extra + 2) ++ [extra + 2] ++
        (List.range (extra + 2)).reverse ++ [extra + 2] ++
          List.range (extra + 2) := by
  simp [anchor, separator, forwardBlock_toList, reverseBlock_toList,
    List.append_assoc]

private theorem count_range_le_one (letter length : Nat) :
    (List.range length).count letter ≤ 1 := by
  by_cases member : letter < length <;> simp [member]

/-- The distinguished separator occurs exactly twice in a Trahtman
anchor. -/
theorem anchor_separator_count_eq_two (extra : Nat) :
    (anchor extra).toList.count (extra + 2) = 2 := by
  rw [anchor_toList]
  simp

/-- Every indexed marker occurs exactly once in each of the three indexed
blocks of a Trahtman anchor. -/
theorem anchor_indexed_count_eq_three
    {extra marker : Nat}
    (indexed : marker < extra + 2) :
    (anchor extra).toList.count marker = 3 := by
  rw [anchor_toList]
  have notSeparator : extra + 2 ≠ marker := by
    omega
  simp [indexed, notSeparator]

/-- Every letter occurs at most three times in a Trahtman anchor. Indexed
letters occur three times, while the separator occurs twice. -/
theorem anchor_count_le_three (extra letter : Nat) :
    (anchor extra).toList.count letter ≤ 3 := by
  rw [anchor_toList]
  simp only [List.count_append, List.count_cons, List.count_nil,
    List.count_reverse]
  by_cases separatorLetter : letter = extra + 2
  · subst letter
    simp
  · have separatorLetter' : extra + 2 ≠ letter :=
      Ne.symm separatorLetter
    by_cases indexedLetter : letter < extra + 2 <;>
      simp [separatorLetter', indexedLetter]

/-- A list containing one occurrence of `letter` splits uniquely enough for
the count-two and count-three decomposition lemmas below: neither surrounding
piece contains `letter`. -/
private theorem exists_one_occurrence_split_of_count_eq_one
    {α : Type} [DecidableEq α]
    {letters : List α} {letter : α}
    (countOne : letters.count letter = 1) :
    ∃ before after,
      letter ∉ before ∧
        letter ∉ after ∧
          letters = before ++ letter :: after := by
  induction letters with
  | nil =>
      simp at countOne
  | cons first rest ih =>
      by_cases equality : first = letter
      · subst first
        have restCountZero : rest.count letter = 0 := by
          simp only [List.count_cons_self] at countOne
          omega
        exact
          ⟨[], rest, by simp,
            List.count_eq_zero.mp restCountZero, by simp⟩
      · have restCountOne : rest.count letter = 1 := by
          simpa [equality] using countOne
        obtain ⟨before, after, notBefore, notAfter, split⟩ :=
          ih restCountOne
        exact
          ⟨first :: before, after,
            by simp [Ne.symm equality, notBefore],
            notAfter, by simp [split]⟩

/-- A list containing two occurrences of `letter` splits around those
occurrences, with no additional occurrence in any surrounding piece. -/
theorem exists_two_occurrence_split_of_count_eq_two
    {α : Type} [DecidableEq α]
    {letters : List α} {letter : α}
    (countTwo : letters.count letter = 2) :
    ∃ before middle after,
      letter ∉ before ∧
        letter ∉ middle ∧
          letter ∉ after ∧
            letters =
              before ++ letter :: (middle ++ letter :: after) := by
  induction letters with
  | nil =>
      simp at countTwo
  | cons first rest ih =>
      by_cases equality : first = letter
      · subst first
        have restCountOne : rest.count letter = 1 := by
          simp only [List.count_cons_self] at countTwo
          omega
        obtain ⟨middle, after, notMiddle, notAfter, split⟩ :=
          exists_one_occurrence_split_of_count_eq_one restCountOne
        exact
          ⟨[], middle, after, by simp, notMiddle, notAfter,
            by simp [split]⟩
      · have restCountTwo : rest.count letter = 2 := by
          simpa [equality] using countTwo
        obtain
          ⟨before, middle, after, notBefore, notMiddle, notAfter, split⟩ :=
            ih restCountTwo
        exact
          ⟨first :: before, middle, after,
            by simp [Ne.symm equality, notBefore],
            notMiddle, notAfter,
            by simp [split]⟩

/-- A list containing exactly three occurrences of `letter` decomposes into
four `letter`-free pieces separated by those three occurrences. -/
theorem exists_three_occurrence_split_of_count_eq_three
    {α : Type} [DecidableEq α]
    {letters : List α} {letter : α}
    (countThree : letters.count letter = 3) :
    ∃ before middleFirst middleSecond after,
      letter ∉ before ∧
        letter ∉ middleFirst ∧
          letter ∉ middleSecond ∧
            letter ∉ after ∧
              letters =
                before ++
                  letter :: (middleFirst ++
                    letter :: (middleSecond ++ letter :: after)) := by
  induction letters with
  | nil =>
      simp at countThree
  | cons first rest ih =>
      by_cases equality : first = letter
      · subst first
        have restCountTwo : rest.count letter = 2 := by
          simp only [List.count_cons_self] at countThree
          omega
        obtain
          ⟨middleFirst, middleSecond, after,
            notMiddleFirst, notMiddleSecond, notAfter, split⟩ :=
            exists_two_occurrence_split_of_count_eq_two restCountTwo
        exact
          ⟨[], middleFirst, middleSecond, after, by simp,
            notMiddleFirst, notMiddleSecond, notAfter, by simp [split]⟩
      · have restCountThree : rest.count letter = 3 := by
          simpa [equality] using countThree
        obtain
          ⟨before, middleFirst, middleSecond, after,
            notBefore, notMiddleFirst, notMiddleSecond, notAfter, split⟩ :=
            ih restCountThree
        exact
          ⟨first :: before, middleFirst, middleSecond, after,
            by simp [Ne.symm equality, notBefore],
            notMiddleFirst, notMiddleSecond, notAfter, by simp [split]⟩

/-- Exact anchor length: three indexed blocks and two separators. -/
theorem anchor_length (extra : Nat) :
    (anchor extra).toList.length = 3 * (extra + 2) + 2 := by
  rw [anchor_toList]
  simp
  omega

private theorem one_le_count_of_mem
    {letter : Nat} {letters : List Nat}
    (member : letter ∈ letters) :
    1 ≤ letters.count letter := by
  exact List.count_pos_iff.mpr member

/-- If `marker` occurs in the image of `sourceLetter`, every occurrence of
`sourceLetter` contributes at least one occurrence of `marker` to the
nonerasing flat-map substitution. -/
theorem count_le_flatMap_count_of_mem
    (source : List Nat) (images : Nat → List Nat)
    (sourceLetter marker : Nat)
    (markerMember : marker ∈ images sourceLetter) :
    source.count sourceLetter ≤
      (source.flatMap images).count marker := by
  induction source with
  | nil => simp
  | cons first rest ih =>
      simp only [List.flatMap_cons, List.count_append, List.count_cons]
      by_cases firstIsSource : first = sourceLetter
      · subst first
        have imagePositive :
            1 ≤ (images sourceLetter).count marker :=
          one_le_count_of_mem markerMember
        have combined := Nat.add_le_add imagePositive ih
        simpa [Nat.add_comm] using combined
      · simp [firstIsSource]
        exact Nat.le_trans ih (Nat.le_add_left _ _)

/-- Every source variable in a nonerasing preimage of a Trahtman anchor
occurs at most three times. -/
theorem preimage_variable_count_le_three
    {bound : Nat} {word : Word Nat}
    {substitution : Nat → Word Nat}
    (mapped : word.bind substitution = anchor (3 * bound))
    {sourceLetter : Nat}
    (_sourceMember : sourceLetter ∈ word.toList) :
    word.toList.count sourceLetter ≤ 3 := by
  let marker := (substitution sourceLetter).head
  have markerMember :
      marker ∈ (substitution sourceLetter).toList := by
    simp [marker, Word.toList]
  have occurrenceBound :=
    count_le_flatMap_count_of_mem word.toList
      (fun letter => (substitution letter).toList)
      sourceLetter marker markerMember
  rw [← Word.toList_bind, mapped] at occurrenceBound
  exact Nat.le_trans occurrenceBound
    (anchor_count_le_three (3 * bound) marker)

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

private theorem length_le_three_mul_of_cover :
    ∀ (letters variables : List Nat),
      (∀ letter, letter ∈ letters → letter ∈ variables) →
      (∀ letter, letter ∈ letters → letters.count letter ≤ 3) →
      letters.length ≤ 3 * variables.length
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
            remainder.count letter ≤ 3 := by
        intro letter member
        have filtered := List.mem_filter.mp member
        have notPivot : letter ≠ pivot := by
          simpa using filtered.2
        rw [count_filter_ne_eq letters notPivot]
        exact bounded letter filtered.1
      have inductionBound :=
        length_le_three_mul_of_cover
          remainder variables remainderCovered remainderBounded
      have pivotBound : letters.count pivot ≤ 3 := by
        by_cases member : pivot ∈ letters
        · exact bounded pivot member
        · simp [List.count_eq_zero.mpr member]
      have decomposition :=
        length_eq_count_add_filter_ne letters pivot
      change
        letters.length ≤ 3 * (pivot :: variables).length
      change remainder.length ≤ 3 * variables.length at inductionBound
      change
        letters.length =
          letters.count pivot + remainder.length at decomposition
      simp only [List.length_cons]
      omega

/-- A preimage word covered by at most `bound` variables has at most
`3 * bound` occurrences. -/
theorem preimage_word_length_le_three_mul
    {bound : Nat} {word : Word Nat}
    (uses : WordUsesAtMost word bound)
    {substitution : Nat → Word Nat}
    (mapped : word.bind substitution = anchor (3 * bound)) :
    word.toList.length ≤ 3 * bound := by
  rcases uses with ⟨variables, variableBound, covered⟩
  have lengthBound :
      word.toList.length ≤ 3 * variables.length :=
    length_le_three_mul_of_cover word.toList variables covered
      (fun letter member =>
        preimage_variable_count_le_three mapped member)
  omega

private theorem all_letters_eq_head_of_usesAtMost_one
    {word : Word Nat}
    (uses : WordUsesAtMost word 1) :
    ∀ letter, letter ∈ word.toList → letter = word.head := by
  rcases uses with ⟨variables, lengthBound, covered⟩
  cases variables with
  | nil =>
      have impossible :=
        covered word.head (by simp [Word.toList])
      simp at impossible
  | cons coverLetter rest =>
      have restEmpty : rest = [] := by
        apply List.eq_nil_of_length_eq_zero
        simp only [List.length_cons] at lengthBound
        omega
      subst rest
      have headEq : word.head = coverLetter := by
        have := covered word.head (by simp [Word.toList])
        simpa using this
      intro letter member
      have := covered letter member
      simpa [headEq] using this

private theorem flatMap_length_of_all_eq
    (letters : List Nat) (images : Nat → List Nat) (letter : Nat)
    (allEqual : ∀ value, value ∈ letters → value = letter) :
    (letters.flatMap images).length =
      letters.length * (images letter).length := by
  induction letters with
  | nil => simp
  | cons first rest ih =>
      have firstEq : first = letter :=
        allEqual first (by simp)
      have restEqual :
          ∀ value, value ∈ rest → value = letter := by
        intro value member
        exact allEqual value (by simp [member])
      subst first
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      rw [ih restEqual]
      rw [Nat.succ_mul]
      omega

private theorem word_eq_singleton_of_toList_length_one
    (word : Word Nat)
    (lengthOne : word.toList.length = 1) :
    word = Word.singleton word.head := by
  cases word with
  | mk head tail =>
      simp only [Word.toList, List.length_cons] at lengthOne
      have tailEmpty : tail = [] :=
        List.eq_nil_of_length_eq_zero (by omega)
      subst tail
      rfl

private theorem sameMarkedDigraphList_singleton
    {letter : Nat} {other : List Nat}
    (same : SameMarkedDigraphList [letter] other) :
    other = [letter] := by
  cases other with
  | nil =>
      simp [SameMarkedDigraphList] at same
  | cons head tail =>
      have headEq : head = letter := by
        simpa [SameMarkedDigraphList] using same.1.symm
      subst head
      cases tail with
      | nil => rfl
      | cons next rest =>
          have rightEdge :
              (letter, next) ∈
                adjacentPairsList (letter :: next :: rest) := by
            simp [adjacentPairsList, Word.adjacentPairsFrom]
          have leftEdge :=
            (same.2.2.2 letter next).mpr rightEdge
          simp [adjacentPairsList, Word.adjacentPairsFrom] at leftEdge

private theorem sameDeletionMarkedDigraph_singleton
    {letter : Nat} {other : Word Nat}
    (same :
      SameDeletionMarkedDigraph (Word.singleton letter) other) :
    other = Word.singleton letter := by
  have filterAll :
      ∀ letters : List Nat,
        letters.filter (fun _ => true) = letters := by
    intro letters
    induction letters with
    | nil => rfl
    | cons first rest ih => simp [ih]
  have allKept := same (fun _ => true)
  rw [filterAll, filterAll] at allKept
  have listEq : other.toList = [letter] := by
    apply sameMarkedDigraphList_singleton
    exact allKept
  apply Word.toList_injective
  simpa using listEq

/-- The first positive-bound case of Trahtman's preimage rigidity. The
one-variable source length is at most three, while the target has prime
length `17`; nonerasing substitution therefore forces a singleton source. -/
theorem deletionGraphPreimageRigidity_bound_one
    (word : Word Nat) :
    WordUsesAtMost word 1 →
      ∀ substitution,
        word.bind substitution = anchor 3 →
        ∀ other,
          SameDeletionMarkedDigraph word other →
          other = word := by
  intro uses substitution mapped other same
  have sourceLengthBound :
      word.toList.length ≤ 3 :=
    preimage_word_length_le_three_mul uses mapped
  have sourceLengthPositive : 1 ≤ word.toList.length := by
    cases word
    simp [Word.toList]
  have allEqual :=
    all_letters_eq_head_of_usesAtMost_one uses
  have bindLength :
      (word.bind substitution).toList.length =
        word.toList.length *
          (substitution word.head).toList.length := by
    rw [Word.toList_bind]
    exact flatMap_length_of_all_eq word.toList
      (fun letter => (substitution letter).toList)
      word.head allEqual
  rw [mapped, anchor_length] at bindLength
  have sourceLengthOne : word.toList.length = 1 := by
    have cases :
        word.toList.length = 1 ∨
          word.toList.length = 2 ∨
            word.toList.length = 3 := by
      omega
    rcases cases with one | two | three
    · exact one
    · rw [two] at bindLength
      omega
    · rw [three] at bindLength
      omega
  have wordEq :=
    word_eq_singleton_of_toList_length_one word sourceLengthOne
  rw [wordEq] at same ⊢
  exact sameDeletionMarkedDigraph_singleton same

end SemigroupBasis.Nonfinite.A2One
