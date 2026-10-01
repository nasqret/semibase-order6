import SemigroupBasis.CoRoots.Order6SporadicSection14Invariants

namespace SemigroupBasis.CoRoots.Order6SporadicSection14

open SemigroupBasis

/-! ## The separating substitutions in Propositions 14.1 and 14.4 -/

/-- The finite multiplication facts shared by all four substitutions in the
paper. `ordinary` is assigned to every unmentioned variable, `special` to the
retained earlier marker, and `nextValue` to the next first occurrence. -/
structure GapSeparator (candidate : Semigroup (Fin 6)) where
  ordinary : Fin 6
  special : Fin 6
  nextValue : Fin 6
  hit : Fin 6
  miss : Fin 6
  hit_ne_miss : hit ≠ miss
  mul_ordinary :
    forall current,
      current = ordinary ∨ current = special ->
        candidate.mul current ordinary = ordinary
  mul_special :
    forall current,
      current = ordinary ∨ current = special ->
        candidate.mul current special = special
  special_next : candidate.mul special nextValue = hit
  ordinary_next : candidate.mul ordinary nextValue = miss
  hit_absorbs : forall value, candidate.mul hit value = hit
  miss_absorbs : forall value, candidate.mul miss value = miss

namespace GapSeparator

def valuation
    {candidate : Semigroup (Fin 6)}
    (separator : GapSeparator candidate)
    (selected nextMarker : Nat) : Nat -> Fin 6 :=
  fun letter =>
    if letter = selected then separator.special
    else if letter = nextMarker then separator.nextValue
    else separator.ordinary

@[simp]
theorem valuation_selected
    {candidate : Semigroup (Fin 6)}
    (separator : GapSeparator candidate)
    (selected nextMarker : Nat) :
    separator.valuation selected nextMarker selected =
      separator.special := by
  simp [valuation]

@[simp]
theorem valuation_next
    {candidate : Semigroup (Fin 6)}
    (separator : GapSeparator candidate)
    {selected nextMarker : Nat} (different : selected ≠ nextMarker) :
    separator.valuation selected nextMarker nextMarker =
      separator.nextValue := by
  simp [valuation, Ne.symm different]

theorem valuation_ordinary
    {candidate : Semigroup (Fin 6)}
    (separator : GapSeparator candidate)
    {selected nextMarker letter : Nat}
    (notSelected : letter ≠ selected)
    (notNext : letter ≠ nextMarker) :
    separator.valuation selected nextMarker letter =
      separator.ordinary := by
  simp [valuation, notSelected, notNext]

private theorem valuation_pair_of_ne_next
    {candidate : Semigroup (Fin 6)}
    (separator : GapSeparator candidate)
    {selected nextMarker letter : Nat}
    (notNext : letter ≠ nextMarker) :
    separator.valuation selected nextMarker letter =
        separator.ordinary ∨
      separator.valuation selected nextMarker letter =
        separator.special := by
  by_cases atSelected : letter = selected
  · right
    simp [valuation, atSelected]
  · left
    simp [valuation, atSelected, notNext]

private theorem fold_pair
    {candidate : Semigroup (Fin 6)}
    (separator : GapSeparator candidate)
    {selected nextMarker : Nat} :
    forall (letters : List Nat) (initial : Fin 6),
      initial = separator.ordinary ∨ initial = separator.special ->
      (forall letter, letter ∈ letters -> letter ≠ nextMarker) ->
      letters.foldl
          (fun current letter =>
            candidate.mul current
              (separator.valuation selected nextMarker letter))
          initial = separator.ordinary ∨
        letters.foldl
          (fun current letter =>
            candidate.mul current
              (separator.valuation selected nextMarker letter))
          initial = separator.special
  | [], initial, initialPair, _ => initialPair
  | letter :: rest, initial, initialPair, noNext => by
      have letterNotNext : letter ≠ nextMarker :=
        noNext letter (List.Mem.head rest)
      have restNoNext :
          forall tested, tested ∈ rest -> tested ≠ nextMarker := by
        intro tested member
        exact noNext tested (List.Mem.tail letter member)
      have letterPair :=
        valuation_pair_of_ne_next separator
          (selected := selected) letterNotNext
      have steppedPair :
          candidate.mul initial
              (separator.valuation selected nextMarker letter) =
                separator.ordinary ∨
            candidate.mul initial
              (separator.valuation selected nextMarker letter) =
                separator.special := by
        rcases letterPair with ordinary | special
        · left
          rw [ordinary]
          exact separator.mul_ordinary initial initialPair
        · right
          rw [special]
          exact separator.mul_special initial initialPair
      simpa only [List.foldl_cons] using
        fold_pair separator rest
          (candidate.mul initial
            (separator.valuation selected nextMarker letter))
          steppedPair restNoNext

private theorem fold_ordinary
    {candidate : Semigroup (Fin 6)}
    (separator : GapSeparator candidate)
    {selected nextMarker : Nat} :
    forall letters : List Nat,
      (forall letter, letter ∈ letters ->
        letter ≠ selected ∧ letter ≠ nextMarker) ->
      letters.foldl
          (fun current letter =>
            candidate.mul current
              (separator.valuation selected nextMarker letter))
          separator.ordinary = separator.ordinary
  | [], _ => rfl
  | letter :: rest, ordinaryLetters => by
      have letterOrdinary := ordinaryLetters letter (List.Mem.head rest)
      have restOrdinary :
          forall tested, tested ∈ rest ->
            tested ≠ selected ∧ tested ≠ nextMarker := by
        intro tested member
        exact ordinaryLetters tested (List.Mem.tail letter member)
      rw [List.foldl_cons,
        valuation_ordinary separator letterOrdinary.1 letterOrdinary.2,
        separator.mul_ordinary separator.ordinary (Or.inl rfl)]
      exact fold_ordinary separator rest restOrdinary

private theorem fold_hit_with
    {candidate : Semigroup (Fin 6)}
    (separator : GapSeparator candidate)
    (selected nextMarker : Nat) :
    forall letters : List Nat,
      letters.foldl
          (fun current letter =>
            candidate.mul current
              (separator.valuation selected nextMarker letter))
          separator.hit = separator.hit
  | [] => rfl
  | _ :: rest => by
      rw [List.foldl_cons, separator.hit_absorbs]
      exact fold_hit_with separator selected nextMarker rest

private theorem fold_miss_with
    {candidate : Semigroup (Fin 6)}
    (separator : GapSeparator candidate)
    (selected nextMarker : Nat) :
    forall letters : List Nat,
      letters.foldl
          (fun current letter =>
            candidate.mul current
              (separator.valuation selected nextMarker letter))
          separator.miss = separator.miss
  | [] => rfl
  | _ :: rest => by
      rw [List.foldl_cons, separator.miss_absorbs]
      exact fold_miss_with separator selected nextMarker rest

private theorem eval_eq_foldl_of_toList_eq
    {candidate : Semigroup (Fin 6)}
    (valuation : Nat -> Fin 6) (word : Word Nat)
    (head : Nat) (tail : List Nat)
    (shape : word.toList = head :: tail) :
    candidate.eval valuation word =
      tail.foldl
        (fun current letter =>
          candidate.mul current (valuation letter))
        (valuation head) := by
  have wordEq : word = Word.mk head tail := by
    apply Word.toList_injective
    simpa [Word.toList] using shape
  subst word
  rfl

private theorem fold_after_selected
    {candidate : Semigroup (Fin 6)}
    (separator : GapSeparator candidate)
    {selected nextMarker : Nat}
    (different : selected ≠ nextMarker)
    (suffix : List Nat) :
    (selected :: nextMarker :: suffix).foldl
        (fun current letter =>
          candidate.mul current
            (separator.valuation selected nextMarker letter))
        separator.ordinary = separator.hit := by
  rw [List.foldl_cons, valuation_selected,
    separator.mul_special separator.ordinary (Or.inl rfl),
    List.foldl_cons, valuation_next separator different,
    separator.special_next]
  exact fold_hit_with separator selected nextMarker suffix

private theorem fold_after_ordinary_gap
    {candidate : Semigroup (Fin 6)}
    (separator : GapSeparator candidate)
    {selected nextMarker : Nat}
    (different : selected ≠ nextMarker)
    (gap suffix : List Nat)
    (gapOrdinary : forall letter, letter ∈ gap ->
      letter ≠ selected ∧ letter ≠ nextMarker) :
    (gap ++ nextMarker :: suffix).foldl
        (fun current letter =>
          candidate.mul current
            (separator.valuation selected nextMarker letter))
        separator.ordinary = separator.miss := by
  rw [List.foldl_append,
    fold_ordinary separator gap gapOrdinary,
    List.foldl_cons, valuation_next separator different,
    separator.ordinary_next]
  exact fold_miss_with separator selected nextMarker suffix

/-- The paper's valuation evaluates a retained occurrence of `selected`
immediately before the next fresh marker to the absorbing `hit` value. -/
theorem eval_selected_gap
    {candidate : Semigroup (Fin 6)}
    (separator : GapSeparator candidate)
    (word : Word Nat)
    (before : List Nat)
    (current selected nextMarker : Nat)
    (suffix : List Nat)
    (shape :
      word.toList =
        before ++ [current, selected, nextMarker] ++ suffix)
    (selectedNeNext : selected ≠ nextMarker)
    (currentNeSelected : current ≠ selected)
    (currentNeNext : current ≠ nextMarker)
    (beforeNoNext :
      forall letter, letter ∈ before -> letter ≠ nextMarker) :
    candidate.eval (separator.valuation selected nextMarker) word =
      separator.hit := by
  cases before with
  | nil =>
      have listShape :
          word.toList = current :: selected :: nextMarker :: suffix := by
        simpa using shape
      rw [eval_eq_foldl_of_toList_eq
        (separator.valuation selected nextMarker) word current
        (selected :: nextMarker :: suffix) listShape,
        valuation_ordinary separator currentNeSelected currentNeNext]
      exact fold_after_selected separator selectedNeNext suffix
  | cons head tail =>
      have headNotNext : head ≠ nextMarker :=
        beforeNoNext head (List.Mem.head tail)
      have tailNoNext :
          forall letter, letter ∈ tail -> letter ≠ nextMarker := by
        intro letter member
        exact beforeNoNext letter (List.Mem.tail head member)
      have initialPair :=
        valuation_pair_of_ne_next separator
          (selected := selected) headNotNext
      have prefixPair :=
        fold_pair separator
          (selected := selected) (nextMarker := nextMarker) tail
          (separator.valuation selected nextMarker head)
          initialPair tailNoNext
      have listShape :
          word.toList =
            head :: (tail ++ [current, selected, nextMarker] ++ suffix) := by
        simpa [List.append_assoc] using shape
      rw [eval_eq_foldl_of_toList_eq
        (separator.valuation selected nextMarker) word head
        (tail ++ [current, selected, nextMarker] ++ suffix) listShape]
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [valuation_ordinary separator currentNeSelected currentNeNext,
        separator.mul_ordinary _ prefixPair]
      exact fold_after_selected separator selectedNeNext suffix

/-- If the displayed gap contains no selected marker and no next marker, the
same valuation evaluates the word to the distinct absorbing `miss` value. -/
theorem eval_ordinary_gap
    {candidate : Semigroup (Fin 6)}
    (separator : GapSeparator candidate)
    (word : Word Nat)
    (before gap : List Nat)
    (current selected nextMarker : Nat)
    (suffix : List Nat)
    (shape :
      word.toList =
        before ++ [current] ++ gap ++ (nextMarker :: suffix))
    (selectedNeNext : selected ≠ nextMarker)
    (currentNeSelected : current ≠ selected)
    (currentNeNext : current ≠ nextMarker)
    (beforeNoNext :
      forall letter, letter ∈ before -> letter ≠ nextMarker)
    (gapOrdinary : forall letter, letter ∈ gap ->
      letter ≠ selected ∧ letter ≠ nextMarker) :
    candidate.eval (separator.valuation selected nextMarker) word =
      separator.miss := by
  cases before with
  | nil =>
      have listShape :
          word.toList = current :: (gap ++ nextMarker :: suffix) := by
        simpa [List.append_assoc] using shape
      rw [eval_eq_foldl_of_toList_eq
        (separator.valuation selected nextMarker) word current
        (gap ++ nextMarker :: suffix) listShape,
        valuation_ordinary separator currentNeSelected currentNeNext]
      exact fold_after_ordinary_gap separator selectedNeNext
        gap suffix gapOrdinary
  | cons head tail =>
      have headNotNext : head ≠ nextMarker :=
        beforeNoNext head (List.Mem.head tail)
      have tailNoNext :
          forall letter, letter ∈ tail -> letter ≠ nextMarker := by
        intro letter member
        exact beforeNoNext letter (List.Mem.tail head member)
      have initialPair :=
        valuation_pair_of_ne_next separator
          (selected := selected) headNotNext
      have prefixPair :=
        fold_pair separator
          (selected := selected) (nextMarker := nextMarker) tail
          (separator.valuation selected nextMarker head)
          initialPair tailNoNext
      have listShape :
          word.toList =
            head :: (tail ++ [current] ++ gap ++ (nextMarker :: suffix)) := by
        simpa [List.append_assoc] using shape
      rw [eval_eq_foldl_of_toList_eq
        (separator.valuation selected nextMarker) word head
        (tail ++ [current] ++ gap ++ (nextMarker :: suffix)) listShape]
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [valuation_ordinary separator currentNeSelected currentNeNext,
        separator.mul_ordinary _ prefixPair]
      simpa only [List.foldl_append, List.foldl_cons, List.foldl_nil] using
        (fold_after_ordinary_gap separator selectedNeNext
          gap suffix gapOrdinary)

end GapSeparator

/-- A table element separating the one-letter normal forms `x` and `x^2`. -/
structure UnarySeparator (candidate : Semigroup (Fin 6)) where
  value : Fin 6
  value_ne_square : value ≠ candidate.mul value value

namespace S6_12198

def gapSeparator : GapSeparator publishedSemigroup where
  ordinary := 2
  special := 4
  nextValue := 3
  hit := 5
  miss := 0
  hit_ne_miss := by decide
  mul_ordinary := by
    intro current allowed
    rcases allowed with rfl | rfl <;> decide
  mul_special := by
    intro current allowed
    rcases allowed with rfl | rfl <;> decide
  special_next := by decide
  ordinary_next := by decide
  hit_absorbs := by
    intro value
    apply Fin.ext
    revert value
    decide
  miss_absorbs := by
    intro value
    apply Fin.ext
    revert value
    decide

def unarySeparator : UnarySeparator publishedSemigroup where
  value := 1
  value_ne_square := by decide

end S6_12198

namespace S6_12399

def gapSeparator : GapSeparator publishedSemigroup where
  ordinary := 2
  special := 4
  nextValue := 3
  hit := 5
  miss := 0
  hit_ne_miss := by decide
  mul_ordinary := by
    intro current allowed
    rcases allowed with rfl | rfl <;> decide
  mul_special := by
    intro current allowed
    rcases allowed with rfl | rfl <;> decide
  special_next := by decide
  ordinary_next := by decide
  hit_absorbs := by
    intro value
    apply Fin.ext
    revert value
    decide
  miss_absorbs := by
    intro value
    apply Fin.ext
    revert value
    decide

def unarySeparator : UnarySeparator publishedSemigroup where
  value := 1
  value_ne_square := by decide

end S6_12399

namespace S6_12526

def gapSeparator : GapSeparator publishedSemigroup where
  ordinary := 3
  special := 5
  nextValue := 0
  hit := 4
  miss := 2
  hit_ne_miss := by decide
  mul_ordinary := by
    intro current allowed
    rcases allowed with rfl | rfl <;> decide
  mul_special := by
    intro current allowed
    rcases allowed with rfl | rfl <;> decide
  special_next := by decide
  ordinary_next := by decide
  hit_absorbs := by
    intro value
    apply Fin.ext
    revert value
    decide
  miss_absorbs := by
    intro value
    apply Fin.ext
    revert value
    decide

def unarySeparator : UnarySeparator publishedSemigroup where
  value := 1
  value_ne_square := by decide

end S6_12526

namespace S6_14467

/-- The constants are the paper's `2,5,3,6,1` transported through the
published-to-catalogue anti-isomorphism `[4,1,5,2,3,6]`. -/
def gapSeparator : GapSeparator publishedSemigroup where
  ordinary := 0
  special := 2
  nextValue := 4
  hit := 5
  miss := 3
  hit_ne_miss := by decide
  mul_ordinary := by
    intro current allowed
    rcases allowed with rfl | rfl <;> decide
  mul_special := by
    intro current allowed
    rcases allowed with rfl | rfl <;> decide
  special_next := by decide
  ordinary_next := by decide
  hit_absorbs := by
    intro value
    apply Fin.ext
    revert value
    decide
  miss_absorbs := by
    intro value
    apply Fin.ext
    revert value
    decide

def unarySeparator : UnarySeparator publishedSemigroup where
  value := 1
  value_ne_square := by decide

end S6_14467

end SemigroupBasis.CoRoots.Order6SporadicSection14
