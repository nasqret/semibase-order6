import SemigroupBasis.CoRoots.Order6Day14.TwinsA.TwinsAPresentation
import SemigroupBasis.Examples.LeftZeroTwo

namespace SemigroupBasis.CoRoots.Order6Day14.TwinsA

open SemigroupBasis

def residual (w : Word Nat) : Word Nat := Word.singleton w.head ++ w
def padded (w : Word Nat) : Word Nat := Word.singleton w.head ++ residual w

theorem derives_padded (w : Word Nat) : Derives basis w (padded w) := by
  cases w with
  | mk head tail =>
      cases tail with
      | nil =>
          have powered := rawLaw0 (Word.singleton head)
          simpa [padded, residual, Word.singleton, Word.append] using powered
      | cons next rest =>
          have powered := rawLaw0 (Word.singleton head)
          have extended := powered.appendRight (⟨next, rest⟩ : Word Nat)
          simpa [padded, residual, Word.singleton, Word.append] using extended

theorem residual_valid {S : Type u} (G : Semigroup S) {u v : Word Nat}
    (sameHead : u.head = v.head)
    (valid : (⟨u, v⟩ : Identity Nat).SatisfiedBy G) :
    (⟨residual u, residual v⟩ : Identity Nat).SatisfiedBy G := by
  intro valuation
  change G.eval valuation (Word.singleton u.head ++ u) =
    G.eval valuation (Word.singleton v.head ++ v)
  rw [Semigroup.eval_append, Semigroup.eval_append,
    Semigroup.eval_singleton, Semigroup.eval_singleton, sameHead]
  exact congrArg (G.mul (valuation v.head)) (valid valuation)

theorem sameHead_of_leftValid {u v : Word Nat}
    (valid : (⟨u, v⟩ : Identity Nat).SatisfiedBy Examples.leftZeroTwo.semigroup) :
    u.head = v.head := by
  apply Decidable.byContradiction
  intro hne
  let valuation : Nat → Fin 2 := fun z => if z = u.head then 0 else 1
  have heval := valid valuation
  rw [Examples.leftZeroTwo_eval, Examples.leftZeroTwo_eval] at heval
  simp [valuation, Ne.symm hne] at heval

theorem derives_of_sameHead_rightValid {u v : Word Nat}
    (sameHead : u.head = v.head)
    (valid : (⟨u, v⟩ : Identity Nat).SatisfiedBy
      Examples.parityInitialFour.semigroup.opposite) :
    Derives basis u v := by
  have residualValid : (⟨residual u, residual v⟩ : Identity Nat).SatisfiedBy
      Examples.parityInitialFour.semigroup.opposite :=
    residual_valid _ sameHead valid
  have rightDerivation : Derives Examples.parityInitialOppositeBasis
      (residual u) (residual v) :=
    Examples.parityInitialOppositeBasis_complete.2
      ⟨residual u, residual v⟩ residualValid
  have lifted := transportUnderPrefix rightDerivation (Word.singleton u.head)
  have paddedPair : Derives basis (padded u) (padded v) := by
    simpa only [padded, sameHead] using lifted
  exact (derives_padded u).trans (paddedPair.trans (derives_padded v).symm)

theorem derives_of_factorValidity (e : Identity Nat)
    (leftValid : e.SatisfiedBy Examples.leftZeroTwo.semigroup)
    (rightValid : e.SatisfiedBy Examples.parityInitialFour.semigroup.opposite) :
    Derives basis e.lhs e.rhs :=
  derives_of_sameHead_rightValid (sameHead_of_leftValid leftValid) rightValid

end SemigroupBasis.CoRoots.Order6Day14.TwinsA
