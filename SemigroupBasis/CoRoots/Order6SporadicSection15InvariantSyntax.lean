import SemigroupBasis.CoRoots.Order6SporadicSection15CanonicalData
import SemigroupBasis.CoRoots.S5_107BlockCombinatorics
import SemigroupBasis.CoRoots.S5_213Syntax

namespace SemigroupBasis.CoRoots.Order6SporadicSection15

open SemigroupBasis

/-- Equality of the four multiplicity strata: absent, simple, exactly two,
and at least three. -/
abbrev SameCountStrata (left right : Word Nat) : Prop :=
  ∀ letter,
    S5_213Syntax.cappedMultiplicity left letter =
      S5_213Syntax.cappedMultiplicity right letter

/-- Equality of the directed factors formed by two globally simple letters. -/
abbrev SameFSS (left right : Word Nat) : Prop :=
  ∀ source target,
    S5_107.SimpleAdjacent left source target ↔
      S5_107.SimpleAdjacent right source target

/-- The four conclusions of Lee--Zhang Lemma 15.2 used by canonical
uniqueness. The cap-three field deliberately does not assert equality of
multiplicities above three. -/
structure Lemma15_2Invariants (left right : Word Nat) : Prop where
  countStrata : SameCountStrata left right
  simpleInitial :
    ∀ letter,
      S5_107.SimpleInitial left letter ↔
        S5_107.SimpleInitial right letter
  simpleFinal :
    ∀ letter,
      S5_107.SimpleFinal left letter ↔
        S5_107.SimpleFinal right letter
  fss : SameFSS left right

private theorem two_le_count_of_self_mem_adjacentPairsFrom
    (letter previous : Nat) :
    ∀ rest : List Nat,
      (letter, letter) ∈ Word.adjacentPairsFrom previous rest →
        2 ≤ (previous :: rest).count letter
  | [], member => by
      simp [Word.adjacentPairsFrom] at member
  | next :: rest, member => by
      simp only [Word.adjacentPairsFrom, List.mem_cons,
        Prod.mk.injEq] at member
      rcases member with endpoints | later
      · rcases endpoints with ⟨previousEq, nextEq⟩
        subst previous
        subst next
        simp
      · have lower :=
          two_le_count_of_self_mem_adjacentPairsFrom
            letter next rest later
        by_cases previousEq : previous = letter
        · subst previous
          rw [List.count_cons_self]
          omega
        · rw [List.count_cons_of_ne previousEq]
          exact lower

/-- A globally simple letter cannot form a directed adjacent pair with
itself. -/
theorem simpleAdjacent_ne
    {word : Word Nat} {source target : Nat}
    (adjacent : S5_107.SimpleAdjacent word source target) :
    source ≠ target := by
  intro equal
  subst target
  rcases adjacent with ⟨sourceSimple, _, edge⟩
  cases word with
  | mk head tail =>
      change (head :: tail).count source = 1 at sourceSimple
      change
        (source, source) ∈ Word.adjacentPairsFrom head tail at edge
      have repeated :=
        two_le_count_of_self_mem_adjacentPairsFrom
          source head tail edge
      omega

namespace Lemma15_2Invariants

theorem refl (word : Word Nat) :
    Lemma15_2Invariants word word :=
  ⟨fun _ => rfl, fun _ => Iff.rfl, fun _ => Iff.rfl,
    fun _ _ => Iff.rfl⟩

theorem symm {left right : Word Nat}
    (same : Lemma15_2Invariants left right) :
    Lemma15_2Invariants right left :=
  ⟨fun letter => (same.countStrata letter).symm,
    fun letter => (same.simpleInitial letter).symm,
    fun letter => (same.simpleFinal letter).symm,
    fun source target => (same.fss source target).symm⟩

theorem trans {left middle right : Word Nat}
    (first : Lemma15_2Invariants left middle)
    (second : Lemma15_2Invariants middle right) :
    Lemma15_2Invariants left right :=
  ⟨fun letter =>
      (first.countStrata letter).trans (second.countStrata letter),
    fun letter =>
      (first.simpleInitial letter).trans (second.simpleInitial letter),
    fun letter =>
      (first.simpleFinal letter).trans (second.simpleFinal letter),
    fun source target =>
      (first.fss source target).trans (second.fss source target)⟩

/-- Cap-three equality implies the cap-two equality expected by the reusable
simple-block scanner. -/
theorem cappedMultiplicityTwo_eq
    {left right : Word Nat}
    (same : Lemma15_2Invariants left right)
    (letter : Nat) :
    S5_107.cappedMultiplicity left letter =
      S5_107.cappedMultiplicity right letter := by
  have capped := same.countStrata letter
  unfold S5_213Syntax.cappedMultiplicity at capped
  unfold S5_107.cappedMultiplicity
  simp only [Nat.min_def] at capped ⊢
  split at capped <;> split at capped <;>
    split <;> split <;> omega

/-- Forget only the exact-two versus high-count distinction. Every simple-run
fact remains available through the mature `S5_107` combinatorics. -/
theorem toSimpleAdjacencySignature
    {left right : Word Nat}
    (same : Lemma15_2Invariants left right) :
    S5_107.SameSimpleAdjacencySignature left right :=
  { capped := same.cappedMultiplicityTwo_eq
    initial := same.simpleInitial
    final := same.simpleFinal
    adjacent := same.fss }

theorem simple
    {left right : Word Nat}
    (same : Lemma15_2Invariants left right)
    (letter : Nat) :
    S5_107.SimpleIn left letter ↔
      S5_107.SimpleIn right letter :=
  (same.toSimpleAdjacencySignature).simple letter

theorem support
    {left right : Word Nat}
    (same : Lemma15_2Invariants left right)
    (letter : Nat) :
    letter ∈ left.toList ↔ letter ∈ right.toList :=
  (same.toSimpleAdjacencySignature).support letter

end Lemma15_2Invariants

end SemigroupBasis.CoRoots.Order6SporadicSection15
