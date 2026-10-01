import SemigroupBasis.CoRoots.Order6S6_14897InvolutoryBarrierPrelude
import SemigroupBasis.Examples.AffineParityFour
import SemigroupBasis.Order6.FactorPairJoin

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6S4_96OppositeCubeIntersectionCounterexample

open SemigroupBasis

/-!
The singleton law `x = x^3` is not complete for the identities common to
`S4_96` and its opposite.  The common identity below is separated from the
cube law by an eight-element Rees matrix semigroup over `C2`.
-/

def xyyx : Word Nat :=
  ⟨0, [1, 1, 0]⟩

def xyxxyx : Word Nat :=
  ⟨0, [1, 0, 0, 1, 0]⟩

def separatingLaw : Identity Nat :=
  ⟨xyyx, xyxxyx⟩

def finiteSeparatingLaw : Identity (Fin 2) :=
  ⟨⟨0, [1, 1, 0]⟩, ⟨0, [1, 0, 0, 1, 0]⟩⟩

theorem finiteSeparatingLaw_map :
    finiteSeparatingLaw.map Fin.val = separatingLaw := rfl

/-- The exact target `S6_14897` satisfies the separating identity. -/
theorem target_separatingLaw_valid :
    separatingLaw.SatisfiedBy
      SemigroupBasis.CoRoots.Order6S6_14897InvolutoryBarrier.table.semigroup := by
  rw [← finiteSeparatingLaw_map]
  exact
    (SemigroupBasis.CoRoots.Order6S6_14897InvolutoryBarrier.table).checkIdentityNat_sound
      finiteSeparatingLaw (by decide)

/-- `S4_96` satisfies the separating identity. -/
theorem factor_separatingLaw_valid :
    separatingLaw.SatisfiedBy
      SemigroupBasis.Examples.affineParityFour.semigroup := by
  rw [← finiteSeparatingLaw_map]
  exact SemigroupBasis.Examples.affineParityFour.checkIdentityNat_sound
    finiteSeparatingLaw (by decide)

theorem separatingLaw_reversed :
    separatingLaw.reversed = separatingLaw := by
  decide

/-- The opposite of `S4_96` satisfies the same, self-reversed identity. -/
theorem oppositeFactor_separatingLaw_valid :
    separatingLaw.SatisfiedBy
      SemigroupBasis.Examples.affineParityFour.semigroup.opposite := by
  rw [Identity.satisfiedBy_opposite_iff_reversed, separatingLaw_reversed]
  exact factor_separatingLaw_valid

theorem factor_models_cubeBasis :
    Models SemigroupBasis.Examples.affineParityFour.semigroup
      SemigroupBasis.CoRoots.Order6S6_14897InvolutoryBarrier.basis := by
  intro identity member
  simp only [
    SemigroupBasis.CoRoots.Order6S6_14897InvolutoryBarrier.basis,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl
  rw [←
    SemigroupBasis.CoRoots.Order6S6_14897InvolutoryBarrier.finitePowerLaw_map]
  exact SemigroupBasis.Examples.affineParityFour.checkIdentityNat_sound
    SemigroupBasis.CoRoots.Order6S6_14897InvolutoryBarrier.finitePowerLaw
    (by decide)

theorem powerLaw_reversed :
    SemigroupBasis.CoRoots.Order6S6_14897InvolutoryBarrier.powerLaw.reversed =
      SemigroupBasis.CoRoots.Order6S6_14897InvolutoryBarrier.powerLaw := by
  decide

theorem oppositeFactor_models_cubeBasis :
    Models SemigroupBasis.Examples.affineParityFour.semigroup.opposite
      SemigroupBasis.CoRoots.Order6S6_14897InvolutoryBarrier.basis := by
  intro identity member
  simp only [
    SemigroupBasis.CoRoots.Order6S6_14897InvolutoryBarrier.basis,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl
  rw [Identity.satisfiedBy_opposite_iff_reversed, powerLaw_reversed]
  exact factor_models_cubeBasis
    SemigroupBasis.CoRoots.Order6S6_14897InvolutoryBarrier.powerLaw
    (by
      simp [SemigroupBasis.CoRoots.Order6S6_14897InvolutoryBarrier.basis])

private def row8
    (c0 c1 c2 c3 c4 c5 c6 c7 : Fin 8)
    (column : Fin 8) : Fin 8 :=
  if column = 0 then c0 else
    if column = 1 then c1 else
      if column = 2 then c2 else
        if column = 3 then c3 else
          if column = 4 then c4 else
            if column = 5 then c5 else
              if column = 6 then c6 else c7

/-- The Rees matrix semigroup `M[C2; {0,1}, {0,1}; P]`, where the only
nonzero sandwich entry is `P(1,1)`. -/
def countermodelMul (left right : Fin 8) : Fin 8 :=
  if left = 0 then row8 0 1 2 3 0 1 2 3 right else
    if left = 1 then row8 0 1 2 3 2 3 0 1 right else
      if left = 2 then row8 2 3 0 1 2 3 0 1 right else
        if left = 3 then row8 2 3 0 1 0 1 2 3 right else
          if left = 4 then row8 4 5 6 7 4 5 6 7 right else
            if left = 5 then row8 4 5 6 7 6 7 4 5 right else
              if left = 6 then row8 6 7 4 5 6 7 4 5 right else
                row8 6 7 4 5 4 5 6 7 right

def countermodelTable : FiniteTable where
  order := 8
  mul := countermodelMul
  assoc := by decide

def countermodelTableOneBased : List (List Nat) :=
  List.ofFn fun left : Fin 8 =>
    List.ofFn fun right : Fin 8 =>
      (countermodelTable.semigroup.mul left right).val + 1

theorem countermodelTableOneBased_certificate :
    countermodelTableOneBased =
      [[1, 2, 3, 4, 1, 2, 3, 4],
       [1, 2, 3, 4, 3, 4, 1, 2],
       [3, 4, 1, 2, 3, 4, 1, 2],
       [3, 4, 1, 2, 1, 2, 3, 4],
       [5, 6, 7, 8, 5, 6, 7, 8],
       [5, 6, 7, 8, 7, 8, 5, 6],
       [7, 8, 5, 6, 7, 8, 5, 6],
       [7, 8, 5, 6, 5, 6, 7, 8]] := by
  decide

/-- Exhaustive checking proves that the countermodel satisfies `x = x^3`. -/
theorem countermodel_models_cubeBasis :
    Models countermodelTable.semigroup
      SemigroupBasis.CoRoots.Order6S6_14897InvolutoryBarrier.basis := by
  intro identity member
  simp only [
    SemigroupBasis.CoRoots.Order6S6_14897InvolutoryBarrier.basis,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl
  rw [←
    SemigroupBasis.CoRoots.Order6S6_14897InvolutoryBarrier.finitePowerLaw_map]
  exact countermodelTable.checkIdentityNat_sound
    SemigroupBasis.CoRoots.Order6S6_14897InvolutoryBarrier.finitePowerLaw
    (by decide)

def countermodelValuation : Nat → Fin 8
  | 0 => 0
  | 1 => 5
  | _ => 0

theorem countermodel_separatingLaw_left :
    countermodelTable.semigroup.eval countermodelValuation xyyx =
      (2 : Fin 8) := by
  decide

theorem countermodel_separatingLaw_right :
    countermodelTable.semigroup.eval countermodelValuation xyxxyx =
      (0 : Fin 8) := by
  decide

theorem countermodel_separates_separatingLaw :
    countermodelTable.semigroup.eval countermodelValuation xyyx ≠
      countermodelTable.semigroup.eval countermodelValuation xyxxyx := by
  decide

/-- The common factor identity cannot be derived from `x = x^3`. -/
theorem separatingLaw_not_derivable :
    ¬ Derives SemigroupBasis.CoRoots.Order6S6_14897InvolutoryBarrier.basis
      separatingLaw.lhs separatingLaw.rhs := by
  intro derivation
  exact countermodel_separates_separatingLaw
    (derivation.sound countermodel_models_cubeBasis countermodelValuation)

/-- The singleton cube law is not a basis for the common identity theory of
`S4_96` and `S4_96^op`. -/
theorem cubeBasis_not_intersectionBasis :
    ¬ IntersectionBasis SemigroupBasis.Examples.affineParityFour.semigroup
      SemigroupBasis.Examples.affineParityFour.semigroup.opposite
      SemigroupBasis.CoRoots.Order6S6_14897InvolutoryBarrier.basis := by
  intro complete
  exact separatingLaw_not_derivable
    (complete.complete separatingLaw factor_separatingLaw_valid
      oppositeFactor_separatingLaw_valid)

/-- In particular, no unrestricted intersection normalizer with only the cube
law can exist for this factor pair. -/
theorem cubeBasis_no_intersectionNormalizer :
    ¬ Nonempty
      (IntersectionNormalizer
        SemigroupBasis.Examples.affineParityFour.semigroup
        SemigroupBasis.Examples.affineParityFour.semigroup.opposite
        SemigroupBasis.CoRoots.Order6S6_14897InvolutoryBarrier.basis) := by
  rintro ⟨normalizer⟩
  exact cubeBasis_not_intersectionBasis
    (normalizer.toIntersectionBasis factor_models_cubeBasis
      oppositeFactor_models_cubeBasis)

/-- The exact recorded candidate is not a basis for `S6_14897`. -/
theorem cubeBasis_not_basisFor_target :
    ¬ BasisFor
      SemigroupBasis.CoRoots.Order6S6_14897InvolutoryBarrier.table.semigroup
      SemigroupBasis.CoRoots.Order6S6_14897InvolutoryBarrier.basis := by
  intro complete
  exact separatingLaw_not_derivable
    (complete.2 separatingLaw target_separatingLaw_valid)

end SemigroupBasis.CoRoots.Order6S4_96OppositeCubeIntersectionCounterexample
