import SemigroupBasis.CoRoots.S5_107
import SemigroupBasis.Nonfinite.GraphParity

namespace SemigroupBasis.CoRoots.S5_107

open SemigroupBasis

/-- A variable is simple in a word when it occurs exactly once. -/
def SimpleIn (word : Word Nat) (letter : Nat) : Prop :=
  word.toList.count letter = 1

/-- A simple variable occupying the initial position. -/
def SimpleInitial (word : Word Nat) (letter : Nat) : Prop :=
  SimpleIn word letter ∧ word.head = letter

/-- A simple variable occupying the final position. -/
def SimpleFinal (word : Word Nat) (letter : Nat) : Prop :=
  SimpleIn word letter ∧ word.final = letter

/-- A directed adjacent factor consisting of two globally simple variables. -/
def SimpleAdjacent
    (word : Word Nat) (source target : Nat) : Prop :=
  SimpleIn word source ∧
    SimpleIn word target ∧
      (source, target) ∈ word.adjacentPairs

/-- Multiplicity truncated at two. It records absence, simplicity, and
multiplicity without retaining irrelevant higher exponents. -/
def cappedMultiplicity (word : Word Nat) (letter : Nat) : Nat :=
  Nat.min 2 (word.toList.count letter)

theorem cappedMultiplicity_eq_zero_iff
    (word : Word Nat) (letter : Nat) :
    cappedMultiplicity word letter = 0 ↔
      word.toList.count letter = 0 := by
  unfold cappedMultiplicity
  simp only [Nat.min_def]
  split <;> omega

theorem cappedMultiplicity_eq_one_iff
    (word : Word Nat) (letter : Nat) :
    cappedMultiplicity word letter = 1 ↔
      word.toList.count letter = 1 := by
  unfold cappedMultiplicity
  simp only [Nat.min_def]
  split <;> omega

/-- The complete semantic signature for the `S5_107` family. -/
structure SameSimpleAdjacencySignature
    (left right : Word Nat) : Prop where
  capped :
    ∀ letter,
      cappedMultiplicity left letter =
        cappedMultiplicity right letter
  initial :
    ∀ letter,
      SimpleInitial left letter ↔ SimpleInitial right letter
  final :
    ∀ letter,
      SimpleFinal left letter ↔ SimpleFinal right letter
  adjacent :
    ∀ source target,
      SimpleAdjacent left source target ↔
        SimpleAdjacent right source target

namespace SameSimpleAdjacencySignature

theorem refl (word : Word Nat) :
    SameSimpleAdjacencySignature word word :=
  ⟨fun _ => rfl, fun _ => Iff.rfl, fun _ => Iff.rfl,
    fun _ _ => Iff.rfl⟩

theorem symm {left right : Word Nat}
    (same : SameSimpleAdjacencySignature left right) :
    SameSimpleAdjacencySignature right left :=
  ⟨fun letter => (same.capped letter).symm,
    fun letter => (same.initial letter).symm,
    fun letter => (same.final letter).symm,
    fun source target => (same.adjacent source target).symm⟩

theorem trans {left middle right : Word Nat}
    (first : SameSimpleAdjacencySignature left middle)
    (second : SameSimpleAdjacencySignature middle right) :
    SameSimpleAdjacencySignature left right :=
  ⟨fun letter =>
      (first.capped letter).trans (second.capped letter),
    fun letter =>
      (first.initial letter).trans (second.initial letter),
    fun letter =>
      (first.final letter).trans (second.final letter),
    fun source target =>
      (first.adjacent source target).trans
        (second.adjacent source target)⟩

theorem simple {left right : Word Nat}
    (same : SameSimpleAdjacencySignature left right)
    (letter : Nat) :
    SimpleIn left letter ↔ SimpleIn right letter := by
  constructor
  · intro leftSimple
    have leftCapped :
        cappedMultiplicity left letter = 1 :=
      (cappedMultiplicity_eq_one_iff left letter).2 leftSimple
    have rightCapped :
        cappedMultiplicity right letter = 1 := by
      rw [← same.capped letter]
      exact leftCapped
    exact
      (cappedMultiplicity_eq_one_iff right letter).1 rightCapped
  · intro rightSimple
    have rightCapped :
        cappedMultiplicity right letter = 1 :=
      (cappedMultiplicity_eq_one_iff right letter).2 rightSimple
    have leftCapped :
        cappedMultiplicity left letter = 1 := by
      rw [same.capped letter]
      exact rightCapped
    exact
      (cappedMultiplicity_eq_one_iff left letter).1 leftCapped

theorem absent {left right : Word Nat}
    (same : SameSimpleAdjacencySignature left right)
    (letter : Nat) :
    letter ∉ left.toList ↔ letter ∉ right.toList := by
  rw [← List.count_eq_zero, ← List.count_eq_zero,
    ← cappedMultiplicity_eq_zero_iff,
    ← cappedMultiplicity_eq_zero_iff, same.capped letter]

theorem support {left right : Word Nat}
    (same : SameSimpleAdjacencySignature left right)
    (letter : Nat) :
    letter ∈ left.toList ↔ letter ∈ right.toList := by
  simpa using not_congr (same.absent letter)

end SameSimpleAdjacencySignature

/-- Keep the first occurrence of each letter, in its original order. -/
def distinctLetters : List Nat → List Nat
  | [] => []
  | letter :: rest =>
      letter ::
        (distinctLetters rest).filter
          (fun next => decide (next ≠ letter))

theorem distinctLetters_mem_iff (letter : Nat) :
    ∀ letters : List Nat,
      letter ∈ distinctLetters letters ↔ letter ∈ letters
  | [] => by simp [distinctLetters]
  | head :: tail => by
      simp only [distinctLetters, List.mem_cons, List.mem_filter,
        distinctLetters_mem_iff letter tail]
      by_cases equal : letter = head
      · subst head
        simp
      · simp [equal]

/-- Scan the word while accumulating the current maximal simple block in
reverse order. Multiple variables terminate the current block. -/
def simpleBlockScan (whole current : List Nat) :
    List Nat → List (List Nat)
  | [] =>
      match current with
      | [] => []
      | _ => [current.reverse]
  | letter :: rest =>
      if whole.count letter = 1 then
        simpleBlockScan whole (letter :: current) rest
      else
        match current with
        | [] => simpleBlockScan whole [] rest
        | _ =>
            current.reverse ::
              simpleBlockScan whole [] rest

/-- Maximal consecutive blocks of globally simple variables. -/
def simpleBlocks (letters : List Nat) : List (List Nat) :=
  simpleBlockScan letters [] letters

private def initialIsSimple : List Nat → Bool
  | [] => false
  | head :: tail => decide ((head :: tail).count head = 1)

private def finalIsSimple : List Nat → Bool
  | [] => false
  | head :: tail =>
      let letters := head :: tail
      decide (letters.count (tail.getLastD head) = 1)

/-- The initial maximal simple block, or the empty list when the word begins
with a multiple variable. -/
def initialSimpleBlock (letters : List Nat) : List Nat :=
  if initialIsSimple letters then
    (simpleBlocks letters).headD []
  else
    []

/-- The final maximal simple block, or the empty list when the word ends with
a multiple variable. -/
def finalSimpleBlock (letters : List Nat) : List Nat :=
  if finalIsSimple letters then
    (simpleBlocks letters).getLastD []
  else
    []

/-- Delete the endpoint blocks from the complete simple-block list. -/
def interiorSimpleBlocks (letters : List Nat) : List (List Nat) :=
  let withoutInitial :=
    if initialIsSimple letters then
      (simpleBlocks letters).drop 1
    else
      simpleBlocks letters
  if finalIsSimple letters then
    withoutInitial.dropLast
  else
    withoutInitial

/-- The multiple variables, once each and in increasing order. -/
def sortedMultipleLetters (letters : List Nat) : List Nat :=
  ((distinctLetters letters).filter
      (fun letter => decide (2 ≤ letters.count letter))).mergeSort
    (fun left right : Nat => decide (left ≤ right))

theorem sortedMultipleLetters_mem_iff
    (letter : Nat) (letters : List Nat) :
    letter ∈ sortedMultipleLetters letters ↔
      2 ≤ letters.count letter := by
  simp only [sortedMultipleLetters, List.mem_mergeSort,
    List.mem_filter, distinctLetters_mem_iff, decide_eq_true_eq]
  constructor
  · exact And.right
  · intro multiple
    exact
      ⟨List.count_pos_iff.mp (by omega), multiple⟩

/-- A deterministic lexicographic order on simple blocks. -/
def sortedSimpleBlocks
    (blocks : List (List Nat)) : List (List Nat) :=
  blocks.mergeSort
    (fun left right =>
      decide (compare left right != Ordering.gt))

/-- Render interior blocks, each followed by the selected multiple anchor. -/
def renderAnchoredBlocks
    (anchor : Nat) (blocks : List (List Nat)) : List Nat :=
  blocks.flatMap fun block => block ++ [anchor]

/-- Render two copies of every multiple variable. -/
def renderMultipleSquares (letters : List Nat) : List Nat :=
  letters.flatMap fun letter => [letter, letter]

/-- The deterministic canonical list described by the simple-adjacency
certificate. Simple words remain literal. Otherwise the least multiple
variable anchors the sorted interior simple blocks, followed by sorted
multiple squares and the retained final simple block. -/
def simpleAdjacencyCanonicalList (letters : List Nat) : List Nat :=
  match sortedMultipleLetters letters with
  | [] => letters
  | anchor :: remainingMultiples =>
      initialSimpleBlock letters ++
        [anchor] ++
        renderAnchoredBlocks anchor
          (sortedSimpleBlocks (interiorSimpleBlocks letters)) ++
        renderMultipleSquares (anchor :: remainingMultiples) ++
        finalSimpleBlock letters

private def wordOfListOr
    (fallback : Nat) : List Nat → Word Nat
  | [] => Word.singleton fallback
  | head :: tail => ⟨head, tail⟩

/-- Canonical word associated with the simple-adjacency signature. -/
def simpleAdjacencyCanonicalWord (word : Word Nat) : Word Nat :=
  wordOfListOr word.head
    (simpleAdjacencyCanonicalList word.toList)

theorem simpleAdjacencyCanonicalList_ne_nil (word : Word Nat) :
    simpleAdjacencyCanonicalList word.toList ≠ [] := by
  cases word with
  | mk head tail =>
      unfold simpleAdjacencyCanonicalList
      cases sorted :
          sortedMultipleLetters (Word.mk head tail).toList with
      | nil =>
          simp [Word.toList]
      | cons anchor rest =>
          simp

@[simp]
theorem toList_simpleAdjacencyCanonicalWord (word : Word Nat) :
    (simpleAdjacencyCanonicalWord word).toList =
      simpleAdjacencyCanonicalList word.toList := by
  unfold simpleAdjacencyCanonicalWord
  cases canonical :
      simpleAdjacencyCanonicalList word.toList with
  | nil =>
      exact False.elim <|
        simpleAdjacencyCanonicalList_ne_nil word canonical
  | cons head tail =>
      rfl

end SemigroupBasis.CoRoots.S5_107
