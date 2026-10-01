import SemigroupBasis.CoRoots.Order6Day7.S3_15op.Rank083
import SemigroupBasis.CoRoots.Order6FactorPairS3_13S5_213M2Normal

/-!
# Exact reversed M2 intersection rebase for rank 083

The independently complete direct S3_15/S5_213 intersection has exactly three
displayed source laws. After word reversal, its power and gather axioms are
literal frozen rank-083 laws. Its transport axiom is the explicit two-step
chain `2110 -> 1210 -> 1120`. Thus all three source laws have concrete target
derivations totaling four displayed rewrites.
-/

namespace SemigroupBasis.CoRoots.Order6Day7.S3_15op.SeedS5_213

open SemigroupBasis

private abbrev targetBasis : List (Identity Nat) := Rank083.basis

private abbrev sourceBasis : List (Identity Nat) :=
  SemigroupBasis.CoRoots.Order6FactorPairS3_13S5_213M2.sigma

private def w (first : Nat) (rest : List Nat) : Word Nat :=
  Word.mk first rest

private theorem displayedPower :
    Derives targetBasis (w 0 [0, 0]) (w 0 [0, 0, 0]) :=
  Derives.fromBasis
    (e := ⟨w 0 [0, 0], w 0 [0, 0, 0]⟩) (by decide)

private theorem displayedTransport :
    Derives targetBasis (w 0 [0, 1, 2]) (w 0 [1, 0, 2]) :=
  Derives.fromBasis
    (e := ⟨w 0 [0, 1, 2], w 0 [1, 0, 2]⟩) (by decide)

private theorem displayedGather :
    Derives targetBasis (w 0 [1, 0]) (w 1 [0, 0]) :=
  Derives.fromBasis
    (e := ⟨w 0 [1, 0], w 1 [0, 0]⟩) (by decide)

private def instantiateThreeWords
    (first second third : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | letter + 3 => Word.singleton (letter + 3)

/-- Explicit frozen-law chain `2110 -> 1210 -> 1120`. -/
theorem derivesReversedTransport :
    Derives targetBasis (w 2 [1, 1, 0]) (w 1 [1, 2, 0]) := by
  let substitution : Nat → Word Nat :=
    instantiateThreeWords
      (Word.singleton 1) (Word.singleton 2) (Word.singleton 0)
  have gather :=
    Derives.appendRight
      (Derives.subst displayedGather.symm substitution)
      (Word.singleton 0)
  have firstStep :
      Derives targetBasis (w 2 [1, 1, 0]) (w 1 [2, 1, 0]) := by
    simpa [substitution, instantiateThreeWords, w, Word.bind,
      Word.singleton, Word.append, Word.append_assoc] using gather
  have moved := Derives.subst displayedTransport.symm substitution
  have secondStep :
      Derives targetBasis (w 1 [2, 1, 0]) (w 1 [1, 2, 0]) := by
    simpa [substitution, instantiateThreeWords, w, Word.bind,
      Word.singleton, Word.append, Word.append_assoc] using moved
  exact firstStep.trans secondStep

/-- Derive every reversed axiom of the actual unrestricted direct intersection. -/
theorem reversedSourceAxiomDerives
    (identity : Identity Nat)
    (member : identity ∈ sourceBasis) :
    Derives targetBasis
      identity.reversed.lhs identity.reversed.rhs := by
  simp only [SemigroupBasis.CoRoots.Order6FactorPairS3_13S5_213M2.sigma,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · change Derives targetBasis (w 0 [0, 0]) (w 0 [0, 0, 0])
    exact displayedPower
  · change Derives targetBasis (w 1 [0, 0]) (w 0 [1, 0])
    exact displayedGather.symm
  · change Derives targetBasis (w 2 [1, 1, 0]) (w 1 [1, 2, 0])
    exact derivesReversedTransport

/-- Structural rebase of an arbitrary unrestricted reversed source proof. -/
theorem transportReversedSourceDerivation
    {left right : Word Nat}
    (derivation : Derives (reversedBasis sourceBasis) left right) :
    Derives targetBasis left right := by
  apply derivation.transport
  intro identity member
  obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp member
  exact reversedSourceAxiomDerives source sourceMember

end SemigroupBasis.CoRoots.Order6Day7.S3_15op.SeedS5_213
