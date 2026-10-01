import SemigroupBasis.CoRoots.S5_107Syntax
import SemigroupBasis.Examples.LeftRegularBandThree

namespace SemigroupBasis.CoRoots.S5_345

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.S5_107

/-- The final variable when it is globally simple, and no marker otherwise. -/
def simpleFinalVariable (word : Word Nat) : Option Nat :=
  if word.toList.count word.final = 1 then
    some word.final
  else
    none

theorem simpleFinalVariable_eq_some_iff
    (word : Word Nat) (letter : Nat) :
    simpleFinalVariable word = some letter ↔
      SimpleFinal word letter := by
  unfold simpleFinalVariable
  by_cases finalSimple : word.toList.count word.final = 1
  · rw [if_pos finalSimple]
    constructor
    · intro equal
      injection equal with finalEqual
      subst letter
      exact ⟨finalSimple, rfl⟩
    · rintro ⟨_, finalEqual⟩
      subst letter
      rfl
  · rw [if_neg finalSimple]
    constructor
    · simp
    · rintro ⟨letterSimple, finalEqual⟩
      exfalso
      apply finalSimple
      unfold SimpleIn at letterSimple
      simpa [finalEqual] using letterSimple

/-- Multiplicity two is the saturated value of `cappedMultiplicity`. -/
theorem cappedMultiplicity_eq_two_iff
    (word : Word Nat) (letter : Nat) :
    cappedMultiplicity word letter = 2 ↔
      2 ≤ word.toList.count letter := by
  unfold cappedMultiplicity
  simp only [Nat.min_def]
  split <;> omega

/-- The complete syntactic signature for the `S5_345` family. -/
structure SameInitialSimpleTerminalSignature
    (left right : Word Nat) : Prop where
  firstOccurrences :
    firstOccurrenceSequence left.toList =
      firstOccurrenceSequence right.toList
  capped :
    ∀ letter,
      cappedMultiplicity left letter =
        cappedMultiplicity right letter
  simpleFinal :
    simpleFinalVariable left = simpleFinalVariable right

namespace SameInitialSimpleTerminalSignature

theorem refl (word : Word Nat) :
    SameInitialSimpleTerminalSignature word word :=
  ⟨rfl, fun _ => rfl, rfl⟩

theorem symm {left right : Word Nat}
    (same : SameInitialSimpleTerminalSignature left right) :
    SameInitialSimpleTerminalSignature right left :=
  ⟨same.firstOccurrences.symm,
    fun letter => (same.capped letter).symm,
    same.simpleFinal.symm⟩

theorem trans {left middle right : Word Nat}
    (first : SameInitialSimpleTerminalSignature left middle)
    (second : SameInitialSimpleTerminalSignature middle right) :
    SameInitialSimpleTerminalSignature left right :=
  ⟨first.firstOccurrences.trans second.firstOccurrences,
    fun letter =>
      (first.capped letter).trans (second.capped letter),
    first.simpleFinal.trans second.simpleFinal⟩

/-- The signature preserves absence of every variable. -/
theorem absent {left right : Word Nat}
    (same : SameInitialSimpleTerminalSignature left right)
    (letter : Nat) :
    letter ∉ left.toList ↔ letter ∉ right.toList := by
  rw [← List.count_eq_zero, ← List.count_eq_zero,
    ← cappedMultiplicity_eq_zero_iff,
    ← cappedMultiplicity_eq_zero_iff, same.capped letter]

/-- The signature preserves the support of the word. -/
theorem support {left right : Word Nat}
    (same : SameInitialSimpleTerminalSignature left right)
    (letter : Nat) :
    letter ∈ left.toList ↔ letter ∈ right.toList := by
  simpa using not_congr (same.absent letter)

/-- The signature preserves globally simple variables. -/
theorem simple {left right : Word Nat}
    (same : SameInitialSimpleTerminalSignature left right)
    (letter : Nat) :
    SimpleIn left letter ↔ SimpleIn right letter := by
  unfold SimpleIn
  rw [← cappedMultiplicity_eq_one_iff,
    ← cappedMultiplicity_eq_one_iff, same.capped letter]

/-- The signature preserves variables occurring at least twice. -/
theorem multiple {left right : Word Nat}
    (same : SameInitialSimpleTerminalSignature left right)
    (letter : Nat) :
    2 ≤ left.toList.count letter ↔
      2 ≤ right.toList.count letter := by
  rw [← cappedMultiplicity_eq_two_iff,
    ← cappedMultiplicity_eq_two_iff, same.capped letter]

/-- The optional simple-final variable has the expected relational form. -/
theorem simpleFinal_iff {left right : Word Nat}
    (same : SameInitialSimpleTerminalSignature left right)
    (letter : Nat) :
    SimpleFinal left letter ↔ SimpleFinal right letter := by
  rw [← simpleFinalVariable_eq_some_iff,
    ← simpleFinalVariable_eq_some_iff, same.simpleFinal]

theorem cappedFunction_eq {left right : Word Nat}
    (same : SameInitialSimpleTerminalSignature left right) :
    cappedMultiplicity left = cappedMultiplicity right :=
  funext same.capped

end SameInitialSimpleTerminalSignature

/-- Select the first saturated-multiplicity variable in a prescribed order. -/
def firstMultiple
    (multiplicity : Nat → Nat) : List Nat → Option Nat
  | [] => none
  | letter :: rest =>
      if multiplicity letter = 2 then
        some letter
      else
        firstMultiple multiplicity rest

theorem firstMultiple_congr
    {leftMultiplicity rightMultiplicity : Nat → Nat}
    (same :
      ∀ letter,
        leftMultiplicity letter = rightMultiplicity letter) :
    ∀ letters,
      firstMultiple leftMultiplicity letters =
        firstMultiple rightMultiplicity letters
  | [] => rfl
  | letter :: rest => by
      by_cases leftMultiple : leftMultiplicity letter = 2
      · have rightMultiple : rightMultiplicity letter = 2 := by
          rw [← same letter]
          exact leftMultiple
        simp [firstMultiple, leftMultiple, rightMultiple]
      · have rightNotMultiple : rightMultiplicity letter ≠ 2 := by
          intro rightMultiple
          apply leftMultiple
          rw [same letter]
          exact rightMultiple
        simp [firstMultiple, leftMultiple, rightNotMultiple,
          firstMultiple_congr same rest]

/-- The earliest multiple variable in first-occurrence order. -/
def earliestMultiple (word : Word Nat) : Option Nat :=
  firstMultiple
    (cappedMultiplicity word)
    (firstOccurrenceSequence word.toList)

/-- If the final variable is multiple, the earliest multiple variable becomes
the repeated terminal marker. A simple final variable needs no marker. -/
def terminalMarker (word : Word Nat) : Option Nat :=
  match simpleFinalVariable word with
  | some _ => none
  | none => earliestMultiple word

/-- Render one first-occurrence block. Simple variables and the selected
terminal marker occur once; all other multiple variables occur twice. -/
def canonicalBlock (word : Word Nat) (letter : Nat) : List Nat :=
  if cappedMultiplicity word letter = 1 ∨
      terminalMarker word = some letter then
    [letter]
  else
    [letter, letter]

/-- First-occurrence blocks followed by the optional repeated terminal
marker. This is the deterministic normal form described for the family. -/
def canonicalList (word : Word Nat) : List Nat :=
  (firstOccurrenceSequence word.toList).flatMap
      (canonicalBlock word) ++
    (terminalMarker word).toList

theorem canonicalBlock_ne_nil
    (word : Word Nat) (letter : Nat) :
    canonicalBlock word letter ≠ [] := by
  by_cases single :
      cappedMultiplicity word letter = 1 ∨
        terminalMarker word = some letter
  · simp [canonicalBlock, single]
  · simp [canonicalBlock, single]

theorem canonicalList_ne_nil (word : Word Nat) :
    canonicalList word ≠ [] := by
  cases word with
  | mk head tail =>
      intro canonicalEmpty
      unfold canonicalList at canonicalEmpty
      have blocksEmpty :
          (firstOccurrenceSequence
              (Word.mk head tail).toList).flatMap
                (canonicalBlock (Word.mk head tail)) = [] :=
        (List.append_eq_nil_iff.mp canonicalEmpty).1
      simp only [Word.toList, firstOccurrenceSequence,
        List.flatMap_cons] at blocksEmpty
      have firstBlockEmpty :
          canonicalBlock (Word.mk head tail) head = [] :=
        (List.append_eq_nil_iff.mp blocksEmpty).1
      exact
        canonicalBlock_ne_nil
          (Word.mk head tail) head firstBlockEmpty

private def wordOfListOr
    (fallback : Nat) : List Nat → Word Nat
  | [] => Word.singleton fallback
  | head :: tail => ⟨head, tail⟩

/-- The nonempty canonical word associated with the family signature. -/
def canonicalWord (word : Word Nat) : Word Nat :=
  wordOfListOr word.head (canonicalList word)

@[simp]
theorem toList_canonicalWord (word : Word Nat) :
    (canonicalWord word).toList = canonicalList word := by
  unfold canonicalWord
  cases canonical : canonicalList word with
  | nil =>
      exact False.elim (canonicalList_ne_nil word canonical)
  | cons head tail =>
      rfl

namespace SameInitialSimpleTerminalSignature

theorem earliestMultiple_eq {left right : Word Nat}
    (same : SameInitialSimpleTerminalSignature left right) :
    earliestMultiple left = earliestMultiple right := by
  unfold earliestMultiple
  rw [same.firstOccurrences]
  exact firstMultiple_congr same.capped _

theorem terminalMarker_eq {left right : Word Nat}
    (same : SameInitialSimpleTerminalSignature left right) :
    terminalMarker left = terminalMarker right := by
  unfold terminalMarker
  rw [same.simpleFinal, same.earliestMultiple_eq]

theorem canonicalBlock_eq {left right : Word Nat}
    (same : SameInitialSimpleTerminalSignature left right)
    (letter : Nat) :
    canonicalBlock left letter = canonicalBlock right letter := by
  unfold canonicalBlock
  rw [same.capped letter, same.terminalMarker_eq]

/-- The canonical list depends only on the three signature components. -/
theorem canonicalList_eq {left right : Word Nat}
    (same : SameInitialSimpleTerminalSignature left right) :
    canonicalList left = canonicalList right := by
  unfold canonicalList
  rw [same.firstOccurrences, same.terminalMarker_eq]
  have blocksEqual :
      canonicalBlock left = canonicalBlock right := by
    funext letter
    exact same.canonicalBlock_eq letter
  rw [blocksEqual]

/-- Equal signatures produce literally equal canonical words. -/
theorem canonicalWord_eq {left right : Word Nat}
    (same : SameInitialSimpleTerminalSignature left right) :
    canonicalWord left = canonicalWord right := by
  apply Word.toList_injective
  simpa using same.canonicalList_eq

end SameInitialSimpleTerminalSignature

end SemigroupBasis.CoRoots.S5_345
