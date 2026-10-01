import SemigroupBasis.CoRoots.S5_415MatrixUnitEquivalence
import SemigroupBasis.CoRoots.S5_415PublishedReduction
import SemigroupBasis.MatrixUnitEmbedding
import SemigroupBasis.SchutzenbergerImage
import SemigroupBasis.StableRegularity

namespace SemigroupBasis
namespace Semigroup

/-- Brandt laws descend through every semigroup congruence. -/
theorem BrandtLaws.congruenceQuotient
    {G : Semigroup S} (laws : G.BrandtLaws) (C : G.Congruence) :
    C.quotientSemigroup.BrandtLaws := by
  refine
    { square_eq_cube := ?_
      sandwich := ?_
      squares_commute := ?_ }
  · intro x
    refine _root_.Quotient.inductionOn x ?_
    intro a
    change
      C.classOf (G.mul a a) =
        C.classOf (G.mul (G.mul a a) a)
    exact congrArg C.classOf (laws.square_eq_cube a)
  · intro x y
    refine _root_.Quotient.inductionOn x ?_
    intro a
    refine _root_.Quotient.inductionOn y ?_
    intro b
    change
      C.classOf (G.mul (G.mul a b) a) =
        C.classOf
          (G.mul (G.mul (G.mul (G.mul a b) a) b) a)
    exact congrArg C.classOf (laws.sandwich a b)
  · intro x y
    refine _root_.Quotient.inductionOn x ?_
    intro a
    refine _root_.Quotient.inductionOn y ?_
    intro b
    change
      C.classOf (G.mul (G.mul a a) (G.mul b b)) =
        C.classOf (G.mul (G.mul b b) (G.mul a a))
    exact congrArg C.classOf (laws.squares_commute a b)

/-- Every regular element remains regular after the right Schutzenberger
projection. In particular, this applies to the selected regular element `z`. -/
theorem rightSchutzenberger_classOf_isRegular
    {G : Semigroup S} {z x : S} (regular : G.IsRegular x) :
    (rightSchutzenbergerCongruence G z).quotientSemigroup.IsRegular
      ((rightSchutzenbergerCongruence G z).classOf x) :=
  (rightSchutzenbergerCongruence G z).projection.map_isRegular regular

/-- Any member of `I_z` represents an absorbing zero in the quotient. This
does not assert that `I_z` is inhabited. -/
theorem rightSchutzenberger_classOf_isZero_of_mem_I_z
    {G : Semigroup S} {z zeroRepresentative : S}
    (member : zeroRepresentative ∈ I_z G z) :
    (rightSchutzenbergerCongruence G z).quotientSemigroup.IsZero
      ((rightSchutzenbergerCongruence G z).classOf zeroRepresentative) := by
  constructor
  · intro q
    refine _root_.Quotient.inductionOn q ?_
    intro x
    change
      (rightSchutzenbergerCongruence G z).classOf
          (G.mul zeroRepresentative x) =
        (rightSchutzenbergerCongruence G z).classOf zeroRepresentative
    apply (rightSchutzenberger_classOf_eq_iff G z).2
    apply reesRel_imp_rightSchutzenbergerRel G z
    exact Or.inr
      ⟨(I_z G z).mul_mem_right member x, member⟩
  · intro q
    refine _root_.Quotient.inductionOn q ?_
    intro x
    change
      (rightSchutzenbergerCongruence G z).classOf
          (G.mul x zeroRepresentative) =
        (rightSchutzenbergerCongruence G z).classOf zeroRepresentative
    apply (rightSchutzenberger_classOf_eq_iff G z).2
    apply reesRel_imp_rightSchutzenbergerRel G z
    exact Or.inr
      ⟨(I_z G z).mul_mem_left x member, member⟩

/-- A quotient is regular once every class is represented by a regular source
element. -/
theorem rightSchutzenbergerQuotient_regularSemigroup_of_representatives
    {G : Semigroup S} {z : S}
    (representative :
      ∀ q : (rightSchutzenbergerCongruence G z).Quotient,
        ∃ x, G.IsRegular x ∧
          (rightSchutzenbergerCongruence G z).classOf x = q) :
    (rightSchutzenbergerCongruence G z).quotientSemigroup.RegularSemigroup := by
  intro q
  rcases representative q with ⟨x, regular, rfl⟩
  exact rightSchutzenberger_classOf_isRegular regular

/-- The exact image condition reduces quotient regularity to regularity of
the source elements in `S z S`. -/
theorem rightSchutzenbergerQuotient_regularSemigroup_of_imageCondition
    {G : Semigroup S} {z : S}
    (imageCondition : G.RightSchutzenbergerImageCondition z)
    (principalRegular :
      ∀ x, G.PrincipalSandwichMem z x → G.IsRegular x) :
    (rightSchutzenbergerCongruence G z).quotientSemigroup.RegularSemigroup := by
  apply rightSchutzenbergerQuotient_regularSemigroup_of_representatives
  intro q
  rcases
      every_rightSchutzenberger_class_has_principalRepresentative_of_imageCondition
        G z imageCondition q with
    ⟨x, principal, classEq⟩
  exact ⟨x, principalRegular x principal, classEq⟩

/-- Under the square-cube law, every nonzero member of the principal sandwich
of a regular `z` is regular: being outside `I_z` supplies the reverse
principal-sandwich inclusion. -/
theorem principalSandwich_isRegular_of_not_mem_I_z
    {G : Semigroup S} {z x : S} (law : G.SquareEqualsCube)
    (zRegular : G.IsRegular z)
    (principal : G.PrincipalSandwichMem z x)
    (notInIdeal : ¬ (x ∈ I_z G z)) :
    G.IsRegular x :=
  law.isRegular_of_mutual_principalSandwichMem
    principal (principalSandwichMem_of_not_mem_I_z notInIdeal) zRegular

end Semigroup

namespace CoRoots.S5_415

open SemigroupBasis

/-- A narrow sufficient structure theorem at a regular `z`: its right
Schutzenberger quotient is regular and has orthogonal idempotents. Commuting
idempotents follow unconditionally from the inherited Brandt laws, so inverse
structure and the faithful matrix-unit representation are derived below. -/
def RightSchutzenbergerMatrixUnitStructure
    (G : Semigroup S) (z : S) : Prop :=
  let Q :=
    (Semigroup.rightSchutzenbergerCongruence G z).quotientSemigroup
  Q.RegularSemigroup ∧ Q.IdempotentsOrthogonal

/-- The right Schutzenberger quotient unconditionally inherits all three
Brandt laws. -/
theorem rightSchutzenbergerQuotient_brandtLaws_of_brandtLaws
    {G : Semigroup S} {z : S} (laws : G.BrandtLaws) :
    (Semigroup.rightSchutzenbergerCongruence G z).quotientSemigroup.BrandtLaws :=
  laws.congruenceQuotient
    (Semigroup.rightSchutzenbergerCongruence G z)

/-- Hence idempotents in every such quotient commute, independently of the
remaining structure theorem. -/
theorem rightSchutzenbergerQuotient_idempotentsCommute
    {G : Semigroup S} {z : S} (laws : G.BrandtLaws) :
    (Semigroup.rightSchutzenbergerCongruence G z).quotientSemigroup.IdempotentsCommute :=
  (rightSchutzenbergerQuotient_brandtLaws_of_brandtLaws
    (z := z) laws).idempotentsCommute

theorem rightSchutzenbergerQuotient_regularSemigroup_of_matrixUnitStructure
    {G : Semigroup S} {z : S}
    (condition : RightSchutzenbergerMatrixUnitStructure G z) :
    (Semigroup.rightSchutzenbergerCongruence G z).quotientSemigroup.RegularSemigroup :=
  condition.1

theorem rightSchutzenbergerQuotient_idempotentsOrthogonal_of_matrixUnitStructure
    {G : Semigroup S} {z : S}
    (condition : RightSchutzenbergerMatrixUnitStructure G z) :
    (Semigroup.rightSchutzenbergerCongruence G z).quotientSemigroup.IdempotentsOrthogonal :=
  condition.2

/-- The structural condition upgrades the quotient's unconditional
commuting idempotents to an inverse-semigroup structure. -/
theorem rightSchutzenbergerQuotient_isInverseSemigroup
    {G : Semigroup S} {z : S} (laws : G.BrandtLaws)
    (condition : RightSchutzenbergerMatrixUnitStructure G z) :
    (Semigroup.rightSchutzenbergerCongruence G z).quotientSemigroup.IsInverseSemigroup :=
  ⟨condition.1,
    rightSchutzenbergerQuotient_idempotentsCommute
      (z := z) laws⟩

/-- The structural condition yields the exact faithful matrix-unit
representation needed for identity transfer. -/
theorem exists_rightSchutzenbergerQuotient_matrixUnitEmbedding
    {S : Type u} {G : Semigroup S} {z : S} (laws : G.BrandtLaws)
    (condition : RightSchutzenbergerMatrixUnitStructure G z) :
    ∃ (I : Type u) (decEq : DecidableEq I),
      Nonempty (Embedding
        (Semigroup.rightSchutzenbergerCongruence G z).quotientSemigroup
        (@MatrixUnit.semigroup I decEq)) :=
  Semigroup.exists_matrixUnitEmbedding
    (rightSchutzenbergerQuotient_isInverseSemigroup laws condition)
    condition.2
    (rightSchutzenbergerQuotient_brandtLaws_of_brandtLaws
      (z := z) laws).squareEqualsCube

/-- Every catalogue-`B_2` identity transfers to a quotient satisfying the
single structural condition. -/
theorem rightSchutzenbergerQuotient_satisfiedBy_of_matrixUnitStructure
    {G : Semigroup S} {z : S} (laws : G.BrandtLaws)
    (condition : RightSchutzenbergerMatrixUnitStructure G z)
    (identity : Identity α)
    (catalogueValid :
      identity.SatisfiedBy Generated.Catalogue.S5_415.table.semigroup) :
    identity.SatisfiedBy
      (Semigroup.rightSchutzenbergerCongruence G z).quotientSemigroup := by
  rcases exists_rightSchutzenbergerQuotient_matrixUnitEmbedding
      laws condition with
    ⟨I, decEq, ⟨embedding⟩⟩
  letI : DecidableEq I := decEq
  exact embedding.pullback_identity identity
    (matrixUnit_satisfiedBy_of_catalogue
      (I := I) identity catalogueValid)

/-- A proof of the one structural condition at every regular term class
discharges the exact residual `RightSchutzenbergerBrandtValidity`. -/
theorem rightSchutzenbergerBrandtValidity_of_matrixUnitStructure
    (condition :
      ∀ z : TermSemigroup basis,
        (termSemigroup basis).IsRegular z →
          RightSchutzenbergerMatrixUnitStructure
            (termSemigroup basis) z) :
    RightSchutzenbergerBrandtValidity := by
  intro z regular identity catalogueValid
  exact rightSchutzenbergerQuotient_satisfiedBy_of_matrixUnitStructure
    termSemigroup_brandtLaws (condition z regular)
    identity catalogueValid

/-- The same structural premise therefore closes the published
minimal-counterexample reduction. -/
theorem derivationalCompleteness_of_matrixUnitStructure
    (condition :
      ∀ z : TermSemigroup basis,
        (termSemigroup basis).IsRegular z →
          RightSchutzenbergerMatrixUnitStructure
            (termSemigroup basis) z) :
    BrandtDerivationalCompleteness :=
  derivationalCompleteness_of_rightSchutzenbergerBrandtValidity
    (rightSchutzenbergerBrandtValidity_of_matrixUnitStructure condition)

end CoRoots.S5_415
end SemigroupBasis
