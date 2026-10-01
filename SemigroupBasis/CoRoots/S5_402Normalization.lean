import SemigroupBasis.CoRoots.S5_402

namespace SemigroupBasis.CoRoots.S5_402

open SemigroupBasis

/-! ## Unrestricted normalization of an already grouped multiplicity tail -/

/-- `repeatAtLeastTwo block extraCopies` contains exactly two mandatory
copies of `block`, followed by `extraCopies` further copies. -/
def repeatAtLeastTwo (block : Word Nat) : Nat → Word Nat
  | 0 => block ++ block
  | extraCopies + 1 =>
      repeatAtLeastTwo block extraCopies ++ block

/-- One factor of an already grouped multiplicity tail. The block is a
nonempty semigroup word by construction; its exponent is `2 + extraCopies`.
-/
structure MultiplicityTailFactor where
  block : Word Nat
  extraCopies : Nat

/-- Append an arbitrary finite list of grouped repeated blocks. -/
def appendMultiplicityTail :
    Word Nat → List MultiplicityTailFactor → Word Nat
  | stem, [] => stem
  | stem, factor :: rest =>
      appendMultiplicityTail
        (stem ++ repeatAtLeastTwo factor.block factor.extraCopies) rest

/-- Replace every grouped repeated-block exponent by two. -/
def normalizedMultiplicityTail :
    Word Nat → List MultiplicityTailFactor → Word Nat
  | stem, [] => stem
  | stem, factor :: rest =>
      normalizedMultiplicityTail
        (stem ++ (factor.block ++ factor.block)) rest

/-- Every exponent `2 + k` contracts to two, with no bound on `k` and no
restriction on the nonempty substituted block. -/
theorem derivesRepeatedBlockNormal
    (block : Word Nat) (extraCopies : Nat) :
    Derives basis (repeatAtLeastTwo block extraCopies) (block ++ block) := by
  induction extraCopies with
  | zero =>
      exact Derives.refl _
  | succ extraCopies inductionHypothesis =>
      have removeOne :
          Derives basis
            (repeatAtLeastTwo block extraCopies ++ block)
            ((block ++ block) ++ block) :=
        Derives.appendRight inductionHypothesis block
      exact removeOne.trans (derivesPowerExpansion block).symm

private theorem appendMultiplicityTail_congr
    {left right : Word Nat} (derivation : Derives basis left right)
    (tail : List MultiplicityTailFactor) :
    Derives basis
      (appendMultiplicityTail left tail)
      (appendMultiplicityTail right tail) := by
  induction tail generalizing left right with
  | nil =>
      exact derivation
  | cons factor rest inductionHypothesis =>
      exact inductionHypothesis <|
        Derives.appendRight derivation
          (repeatAtLeastTwo factor.block factor.extraCopies)

/-- Normalize every factor of an arbitrary finite grouped multiplicity tail.
Both the number of factors and every excess exponent are unrestricted. -/
theorem derivesGroupedMultiplicityTailNormal
    (stem : Word Nat) (tail : List MultiplicityTailFactor) :
    Derives basis
      (appendMultiplicityTail stem tail)
      (normalizedMultiplicityTail stem tail) := by
  induction tail generalizing stem with
  | nil =>
      exact Derives.refl stem
  | cons factor rest inductionHypothesis =>
      have normalizeFirst :
          Derives basis
            (stem ++
              repeatAtLeastTwo factor.block factor.extraCopies)
            (stem ++ (factor.block ++ factor.block)) :=
        Derives.prepend stem <|
          derivesRepeatedBlockNormal factor.block factor.extraCopies
      have preserveRest :=
        appendMultiplicityTail_congr normalizeFirst rest
      exact preserveRest.trans <|
        inductionHypothesis (stem ++ (factor.block ++ factor.block))

/-- The grouped multiplicity-tail normalizer in arbitrary nonempty left and
right contexts. This is the precise unrestricted theorem boundary: it does
not assert that arbitrary scattered occurrences have already been gathered
into the displayed factors. -/
theorem derivesMultiplicityTailNormal
    (stem suffix : Word Nat)
    (tail : List MultiplicityTailFactor) :
    Derives basis
      (appendMultiplicityTail stem tail ++ suffix)
      (normalizedMultiplicityTail stem tail ++ suffix) :=
  Derives.appendRight (derivesGroupedMultiplicityTailNormal stem tail)
    suffix

/-- Since normalization is a genuine basis derivation, it preserves the
entire necessary S5_402 signature. -/
theorem multiplicityTailNormal_sameSignature
    (stem suffix : Word Nat)
    (tail : List MultiplicityTailFactor) :
    SameSimpleSuccessorSignature
      (appendMultiplicityTail stem tail ++ suffix)
      (normalizedMultiplicityTail stem tail ++ suffix) :=
  derives_sameSignature <|
    derivesMultiplicityTailNormal stem suffix tail

/-- The unrestricted grouped-tail normalizer preserves the word head. -/
theorem multiplicityTailNormal_preservesHead
    (stem suffix : Word Nat)
    (tail : List MultiplicityTailFactor) :
    (appendMultiplicityTail stem tail ++ suffix).head =
      (normalizedMultiplicityTail stem tail ++ suffix).head :=
  (multiplicityTailNormal_sameSignature stem suffix tail).head

/-- The unrestricted grouped-tail normalizer preserves the immediate
successor of every globally simple nonfinal variable. -/
theorem multiplicityTailNormal_preservesImmediateSuccessors
    (stem suffix : Word Nat)
    (tail : List MultiplicityTailFactor) :
    SameImmediateSuccessors
      (appendMultiplicityTail stem tail ++ suffix)
      (normalizedMultiplicityTail stem tail ++ suffix) :=
  (multiplicityTailNormal_sameSignature stem suffix tail).successor

end SemigroupBasis.CoRoots.S5_402
