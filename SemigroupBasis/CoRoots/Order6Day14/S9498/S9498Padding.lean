import SemigroupBasis.CoRoots.Order6Day14.S9498.S9498Presentation

/-! Four additional copies of the head leave a nonempty residual word.
The residual invariant is then handled by the published positive-mod-four
normalizer, only behind the retained head. -/

namespace SemigroupBasis.CoRoots.Order6Day14.S9498

open SemigroupBasis

def residualWord (word : Word Nat) : Word Nat :=
  ⟨word.head, word.head :: word.head :: word.head :: word.tail⟩

def paddedWord (word : Word Nat) : Word Nat :=
  Word.singleton word.head ++ residualWord word

theorem residualWord_head (word : Word Nat) :
    (residualWord word).head = word.head := rfl

theorem residualWord_toList (word : Word Nat) :
    (residualWord word).toList =
      word.head :: word.head :: word.head :: word.head :: word.tail := rfl

theorem paddedWord_toList (word : Word Nat) :
    (paddedWord word).toList =
      word.head :: word.head :: word.head :: word.head :: word.head :: word.tail := rfl

theorem derivesPaddedWord (word : Word Nat) :
    Derives basis word (paddedWord word) := by
  cases word with
  | mk head tail =>
      cases tail with
      | nil =>
          have expanded := rawLaw00 (Word.singleton head)
          simpa [paddedWord, residualWord, Word.singleton, Word.append] using expanded
      | cons letter rest =>
          have expanded := (rawLaw00 (Word.singleton head)).appendRight (Word.mk letter rest)
          simpa [paddedWord, residualWord, Word.singleton, Word.append] using expanded

theorem residual_support (word : Word Nat) (letter : Nat) :
    letter ∈ (residualWord word).toList ↔ letter ∈ word.toList := by
  cases word with
  | mk head tail => simp [residualWord, Word.toList]

theorem residual_count (word : Word Nat) (letter : Nat) :
    (residualWord word).toList.count letter =
      word.toList.count letter + (if word.head = letter then 3 else 0) := by
  cases word with
  | mk head tail =>
      by_cases equal : head = letter
      · subst head
        simp [residualWord, Word.toList] <;> omega
      · simp [residualWord, Word.toList, equal]

theorem residual_samePositiveModFour (left right : Word Nat)
    (heads : left.head = right.head)
    (same : Examples.SamePositiveModFour left right) :
    Examples.SamePositiveModFour (residualWord left) (residualWord right) := by
  refine ⟨?_, ?_⟩
  · intro letter
    exact (residual_support left letter).trans
      ((same.1 letter).trans (residual_support right letter).symm)
  · intro letter
    rw [residual_count, residual_count, heads]
    let offset := if right.head = letter then 3 else 0
    calc
      (left.toList.count letter + offset) % 4 =
          (left.toList.count letter % 4 + offset % 4) % 4 := Nat.add_mod _ _ _
      _ = (right.toList.count letter % 4 + offset % 4) % 4 :=
        congrArg (fun residue => (residue + offset % 4) % 4) (same.2 letter)
      _ = (right.toList.count letter + offset) % 4 := (Nat.add_mod _ _ _).symm

theorem derivesOfHeadAndInvariant (left right : Word Nat)
    (heads : left.head = right.head)
    (same : Examples.SamePositiveModFour left right) :
    Derives basis left right := by
  have residual : Derives Examples.commutativePositiveModFourBasis
      (residualWord left) (residualWord right) :=
    Examples.commutativePositiveModFourDerives_of_invariant
      (residual_samePositiveModFour left right heads same)
  have contextual := transportUnderPrefix residual (Word.singleton left.head)
  have middle : Derives basis (paddedWord left) (paddedWord right) := by
    simpa only [paddedWord, heads] using contextual
  exact (derivesPaddedWord left).trans (middle.trans (derivesPaddedWord right).symm)

end SemigroupBasis.CoRoots.Order6Day14.S9498
