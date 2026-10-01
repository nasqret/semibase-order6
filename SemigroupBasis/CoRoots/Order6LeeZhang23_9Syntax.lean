import SemigroupBasis.CoRoots.S5_402

namespace SemigroupBasis.CoRoots.Order6LeeZhang23_9Syntax

open SemigroupBasis

/-- `FNS(w)` from Lee--Zhang Proposition 23.9: the directed adjacent
pairs whose source is globally non-simple and whose target is globally
simple. -/
def FNS (word : Word Nat) (source target : Nat) : Prop :=
  ¬S5_402.GloballySimple word source ∧
    S5_402.GloballySimple word target ∧
      (source, target) ∈ word.adjacentPairs

/-- `FSS(w)` from Lee--Zhang Proposition 23.9: the directed adjacent
pairs whose two letters are globally simple. -/
def FSS (word : Word Nat) (source target : Nat) : Prop :=
  S5_402.GloballySimple word source ∧
    S5_402.GloballySimple word target ∧
      (source, target) ∈ word.adjacentPairs

/-- The six-coordinate signature stated in Lee--Zhang Lemma 23.11:
content, globally simple letters, literal head and tail, `FNS`, and `FSS`.
The set equalities are written extensionally so downstream proofs do not
depend on a finite-set representation. -/
structure SamePublishedLeeZhang23_9Signature
    (left right : Word Nat) : Prop where
  support : S5_402.SameSupport left right
  globallySimple : S5_402.SameGloballySimpleVariables left right
  head : left.head = right.head
  final : left.final = right.final
  fns : ∀ source target,
    FNS left source target ↔ FNS right source target
  fss : ∀ source target,
    FSS left source target ↔ FSS right source target

/-- A source-native presentation of the Proposition 23.9 signature.
Reversing exposes the published tail and all adjacent pairs ending in a
globally simple letter as the established `S5_402` head/successor data. -/
structure SameLeeZhang23_9Signature
    (left right : Word Nat) : Prop where
  head : left.head = right.head
  reversedS5_402 :
    S5_402.SameSimpleSuccessorSignature left.reverse right.reverse

@[simp]
theorem cappedMultiplicity_reverse
    (word : Word Nat) (letter : Nat) :
    S5_402.cappedMultiplicity word.reverse letter =
      S5_402.cappedMultiplicity word letter := by
  simp [S5_402.cappedMultiplicity, S5_107.cappedMultiplicity,
    List.count_reverse]

theorem adjacentPairs_reverse_iff
    (word : Word Nat) (source target : Nat) :
    (source, target) ∈ word.reverse.adjacentPairs ↔
      (target, source) ∈ word.adjacentPairs := by
  constructor
  · intro member
    obtain ⟨before, after, shape⟩ :=
      (S5_107.mem_adjacentPairs_iff_exists_split
        source target word.reverse).mp member
    apply (S5_107.mem_adjacentPairs_iff_exists_split
      target source word).mpr
    refine ⟨after.reverse, before.reverse, ?_⟩
    have reversed := congrArg List.reverse shape
    simpa [Word.toList_reverse, List.reverse_append] using reversed
  · intro member
    obtain ⟨before, after, shape⟩ :=
      (S5_107.mem_adjacentPairs_iff_exists_split
        target source word).mp member
    apply (S5_107.mem_adjacentPairs_iff_exists_split
      source target word.reverse).mpr
    refine ⟨after.reverse, before.reverse, ?_⟩
    rw [Word.toList_reverse, shape]
    simp [List.reverse_append]

private theorem reverseAux_head_eq_getLastD (head : Nat) :
    ∀ tail : List Nat,
      (Word.reverseAux head tail).head = tail.getLastD head
  | [] => rfl
  | next :: rest => by
      change
        (Word.reverseAux next rest).head =
          (next :: rest).getLastD head
      rw [List.getLastD_cons]
      exact reverseAux_head_eq_getLastD next rest

@[simp]
theorem reverse_head_eq_final (word : Word Nat) :
    word.reverse.head = word.final := by
  cases word with
  | mk head tail => exact reverseAux_head_eq_getLastD head tail

@[simp]
theorem reverse_final_eq_head (word : Word Nat) :
    word.reverse.final = word.head := by
  have reversed := reverse_head_eq_final word.reverse
  simpa using reversed.symm

@[simp]
theorem globallySimple_reverse_iff
    (word : Word Nat) (letter : Nat) :
    S5_402.GloballySimple word.reverse letter ↔
      S5_402.GloballySimple word letter := by
  simp [S5_402.GloballySimple, S5_107.SimpleIn,
    Word.toList_reverse, List.count_reverse]

end SemigroupBasis.CoRoots.Order6LeeZhang23_9Syntax
