import SemigroupBasis.CoRoots.Order6S6_14897InvolutoryBarrierPrelude
import SemigroupBasis.Examples.AffineParityFour
import SemigroupBasis.Subdirect

namespace SemigroupBasis.CoRoots.Order6S6_14897Subdirect

open SemigroupBasis

/-- The row-coordinate quotient onto `S4_96`. -/
def leftProjection : Fin 6 -> Fin 4
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 3
  | 5 => 3

def leftSection : Fin 4 -> Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 4

def ontoLeft :
    SplitSurjection
      SemigroupBasis.CoRoots.Order6S6_14897InvolutoryBarrier.table.semigroup
      SemigroupBasis.Examples.affineParityFour.semigroup where
  toFun := leftProjection
  map_mul := by decide
  preimage := leftSection
  right_inverse := by decide

/-- The column-coordinate quotient onto `S4_96` in the opposite
orientation. -/
def rightProjection : Fin 6 -> Fin 4
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 2
  | 5 => 3

def rightSection : Fin 4 -> Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3

def ontoRight :
    SplitSurjection
      SemigroupBasis.CoRoots.Order6S6_14897InvolutoryBarrier.table.semigroup
      SemigroupBasis.Examples.affineParityFour.semigroup.opposite where
  toFun := rightProjection
  map_mul := by decide
  preimage := rightSection
  right_inverse := by decide

/-- The two quotient coordinates distinguish all six target elements. -/
def subdirectPair :
    SubdirectPair
      SemigroupBasis.CoRoots.Order6S6_14897InvolutoryBarrier.table.semigroup
      SemigroupBasis.Examples.affineParityFour.semigroup
      SemigroupBasis.Examples.affineParityFour.semigroup.opposite where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := by
    intro left right equality
    revert left right
    decide

theorem satisfiedBy_iff_factors
    (identity : Identity Nat) :
    Iff (identity.SatisfiedBy
        SemigroupBasis.CoRoots.Order6S6_14897InvolutoryBarrier.table.semigroup)
      (And
        (identity.SatisfiedBy
          SemigroupBasis.Examples.affineParityFour.semigroup)
        (identity.SatisfiedBy
          SemigroupBasis.Examples.affineParityFour.semigroup.opposite)) :=
  subdirectPair.satisfiedBy_iff identity

end SemigroupBasis.CoRoots.Order6S6_14897Subdirect
