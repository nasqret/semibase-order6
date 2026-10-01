import SemigroupBasis.CoRoots.Order6FennemoreR3BandPrelude

namespace SemigroupBasis.CoRoots.Order6FennemoreR3Band

open Examples

private def r3InstantiateThree (u v w : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => w
  | n + 3 => Word.singleton (n + 3)

/-- Idempotence instantiated by an arbitrary nonempty word. -/
theorem r3DerivesSquareExpansion (u : Word Nat) :
    Derives basis u (u ++ u) := by
  have hbase : Derives basis x xx :=
    Derives.fromBasis (e := idempotenceLaw) (List.Mem.head _)
  have h := Derives.subst hbase (r3InstantiateThree u u u)
  simpa [basis, idempotenceLaw, x, xx, r3InstantiateThree,
    Word.bind, Word.append, Word.singleton] using h

/-- The oriented R3 law instantiated by arbitrary nonempty blocks. -/
theorem r3DerivesExpansion (u v w : Word Nat) :
    Derives basis (((u ++ v) ++ w))
      ((((((u ++ v) ++ w) ++ u) ++ w) ++ v) ++ w) := by
  have hbase : Derives basis xyz xyzxzyz :=
    Derives.fromBasis (e := r3Law)
      (List.Mem.tail _ (List.Mem.head _))
  have h := Derives.subst hbase (r3InstantiateThree u v w)
  simpa [basis, r3Law, xyz, xyzxzyz, r3InstantiateThree,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using h

/-- Keep the last occurrence of every letter, in its original order. -/
def r3LastOccurrenceSequence (xs : List Nat) : List Nat :=
  (firstOccurrenceSequence xs.reverse).reverse

abbrev R3Split := List Nat × Nat × List Nat

/-- Scan from left to right and retain the split at the last newly seen
letter. The parameter records letters already seen before this list. -/
def r3SplitAux (seen : List Nat) : List Nat → Option R3Split
  | [] => none
  | letter :: rest =>
      let nextSeen := if letter ∈ seen then seen else letter :: seen
      match r3SplitAux nextSeen rest with
      | some (stem, pivot, tail) =>
          some (letter :: stem, pivot, tail)
      | none =>
          if letter ∈ seen then none else some ([], letter, rest)

structure R3SplitDataSpec
    (seen xs stem : List Nat) (pivot : Nat) (tail : List Nat) : Prop where
  shape : xs = stem ++ pivot :: tail
  pivotFreshSeen : pivot ∉ seen
  pivotFreshPrefix : pivot ∉ stem
  tailContent :
    ∀ letter, letter ∈ tail →
      letter ∈ seen ∨ letter ∈ stem ∨ letter = pivot

def R3SplitResultSpec
    (seen xs : List Nat) : Option R3Split → Prop
  | none => ∀ letter, letter ∈ xs → letter ∈ seen
  | some (stem, pivot, tail) =>
      R3SplitDataSpec seen xs stem pivot tail

theorem r3SplitAux_spec (seen xs : List Nat) :
    R3SplitResultSpec seen xs (r3SplitAux seen xs) := by
  induction xs generalizing seen with
  | nil =>
      simp [r3SplitAux, R3SplitResultSpec]
  | cons letter rest induction =>
      by_cases member : letter ∈ seen
      · have recursive := induction seen
        cases recursiveEq : r3SplitAux seen rest with
        | none =>
            rw [recursiveEq] at recursive
            simp only [R3SplitResultSpec] at recursive
            simp [r3SplitAux, member, recursiveEq,
              R3SplitResultSpec]
            intro tested testedMember
            exact recursive tested testedMember
        | some result =>
            rcases result with ⟨stem, pivot, tail⟩
            rw [recursiveEq] at recursive
            simp only [R3SplitResultSpec] at recursive
            simp only [r3SplitAux, member, if_pos, recursiveEq]
            refine ⟨?_, recursive.pivotFreshSeen, ?_, ?_⟩
            · simpa using congrArg (List.cons letter) recursive.shape
            · intro pivotMember
              rcases List.mem_cons.mp pivotMember with pivotLetter | pivotStem
              · subst pivot
                exact recursive.pivotFreshSeen member
              · exact recursive.pivotFreshPrefix pivotStem
            · intro tested testedMember
              rcases recursive.tailContent tested testedMember with
                seenMember | prefixMember | pivotEqual
              · exact Or.inl seenMember
              · exact Or.inr (Or.inl (by simp [prefixMember]))
              · exact Or.inr (Or.inr pivotEqual)
      · let nextSeen := letter :: seen
        have recursive := induction nextSeen
        cases recursiveEq : r3SplitAux nextSeen rest with
        | none =>
            rw [recursiveEq] at recursive
            simp only [R3SplitResultSpec] at recursive
            simp only [r3SplitAux, member, if_false, nextSeen, recursiveEq]
            refine ⟨rfl, member, by simp, ?_⟩
            intro tested testedMember
            have nextMember := recursive tested testedMember
            rcases List.mem_cons.mp nextMember with testedLetter | testedSeen
            · exact Or.inr (Or.inr testedLetter)
            · exact Or.inl testedSeen
        | some result =>
            rcases result with ⟨stem, pivot, tail⟩
            rw [recursiveEq] at recursive
            simp only [R3SplitResultSpec] at recursive
            simp only [r3SplitAux, member, if_false, nextSeen, recursiveEq]
            refine ⟨?_, ?_, ?_, ?_⟩
            · simpa using congrArg (List.cons letter) recursive.shape
            · intro pivotSeen
              exact recursive.pivotFreshSeen (by simp [nextSeen, pivotSeen])
            · simp only [List.mem_cons, not_or]
              exact ⟨fun pivotLetter =>
                recursive.pivotFreshSeen (by
                  simp [nextSeen, pivotLetter]),
                recursive.pivotFreshPrefix⟩
            · intro tested testedMember
              rcases recursive.tailContent tested testedMember with
                nextMember | prefixMember | pivotEqual
              · have nextMember' : tested = letter ∨ tested ∈ seen := by
                  simpa [nextSeen] using nextMember
                rcases nextMember' with testedLetter | testedSeen
                · exact Or.inr (Or.inl (by simp [testedLetter]))
                · exact Or.inl testedSeen
              · exact Or.inr (Or.inl (by simp [prefixMember]))
              · exact Or.inr (Or.inr pivotEqual)

/-- The canonical last-new-letter split used by Fennemore's `i3`. -/
def r3Split (xs : List Nat) : Option R3Split :=
  r3SplitAux [] xs

theorem r3Split_none_iff (xs : List Nat) :
    r3Split xs = none ↔ xs = [] := by
  constructor
  · intro splitNone
    have spec := r3SplitAux_spec [] xs
    rw [show r3SplitAux [] xs = none from splitNone] at spec
    simp only [R3SplitResultSpec] at spec
    cases xs with
    | nil => rfl
    | cons head tail =>
        exact False.elim (by simpa using spec head (by simp))
  · rintro rfl
    rfl

theorem r3Split_some_spec
    {xs stem : List Nat} {pivot : Nat} {tail : List Nat}
    (split : r3Split xs = some (stem, pivot, tail)) :
    R3SplitDataSpec [] xs stem pivot tail := by
  have spec := r3SplitAux_spec [] xs
  rw [show r3SplitAux [] xs = some (stem, pivot, tail) from split] at spec
  exact spec

theorem r3Split_prefix_length_lt
    {xs stem : List Nat} {pivot : Nat} {tail : List Nat}
    (split : r3Split xs = some (stem, pivot, tail)) :
    stem.length < xs.length := by
  have shape := (r3Split_some_spec split).shape
  rw [shape]
  simp

/-- Fennemore's recursive `i3` invariant. -/
def r3Invariant (xs : List Nat) : List Nat :=
  match split : r3Split xs with
  | none => []
  | some (stem, pivot, _) =>
      r3Invariant stem ++ pivot :: r3LastOccurrenceSequence xs
termination_by xs.length
decreasing_by
  exact r3Split_prefix_length_lt split

/-- Turn a list into a nonempty word. -/
def r3WordOfList (xs : List Nat) : Word Nat :=
  ⟨xs.headD 0, xs.tail⟩

theorem r3Invariant_eq_of_split
    {xs stem : List Nat} {pivot : Nat} {tail : List Nat}
    (split : r3Split xs = some (stem, pivot, tail)) :
    r3Invariant xs =
      r3Invariant stem ++ pivot :: r3LastOccurrenceSequence xs := by
  rw [r3Invariant]
  rw [split]

/-- The `i3` invariant of a nonempty word is nonempty. -/
theorem r3Invariant_ne_nil (word : Word Nat) :
    r3Invariant word.toList ≠ [] := by
  have wordNonempty : word.toList ≠ [] := by
    cases word
    simp [Word.toList]
  cases split : r3Split word.toList with
  | none =>
      exact False.elim
        (wordNonempty ((r3Split_none_iff word.toList).mp split))
  | some result =>
      rcases result with ⟨stem, pivot, tail⟩
      rw [r3Invariant_eq_of_split split]
      simp

end SemigroupBasis.CoRoots.Order6FennemoreR3Band
