import SemigroupBasis.CoRoots.Order6LeeA2LatticeNodesH7Repeated
import SemigroupBasis.TransferPower

/-!
# H7 right-projection reduction

The H7 adapter makes every right Schutzenberger quotient of the opposite
term semigroup a Brandt-law semigroup.  This gives the needed equality under
all *left* translates in the original orientation.  The target
`RepeatedPairRightProjectionAgreement` instead asks for equality under right
translates.

This module proves the orientation bridge in three steps.

* The Hall--Kublanovskii fixed-representative construction only uses the
  sandwich and graph-switch laws, not unguarded square commutation.  It
  therefore applies to H7 at every repeated (hence regular) selected class.
* Opposite-right agreement and regularity force the two original right
  translates to enter the Rees ideal `I_z` together.
* In the zero-simple original right quotient, the two repeated classes are
  regular, have a common left factor supplied by their common word head, and
  have identical left actions by opposite-right agreement.  Square-cube
  stability then cancels the common factor.

The older outside-ideal reduction remains below as a reusable sufficient
condition, but it is no longer an unresolved premise.
-/

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6LeeA2LatticeNodesH7Projection

open SemigroupBasis

namespace H7

export SemigroupBasis.CoRoots.Order6LeeA2LatticeNodesH7
  (RootedRepeatedCompleteness SameRootedBrandtSignature basis
    derivesGraphSwitch
    derivesOfSameRootedBrandtSignature_of_repeatedCompleteness
    derivesPowerExpansion derivesSandwichExpansion
    sameRootedBrandtSignature_of_valid
    termSemigroupOpposite_rightSchutzenbergerQuotient_squaresCommute)

end H7

namespace Repeated

export SemigroupBasis.CoRoots.Order6LeeA2LatticeNodesH7Repeated
  (RepeatedPairRightProjectionAgreement repeatedTermClassRegularity
    rootedRepeatedCompleteness_of_repeatedPairProjectionAgreement)

end Repeated

namespace Brandt

export SemigroupBasis.CoRoots.S5_415
  (CellContains RepeatedWord SameBrandtSignature basis
    brandtDerivationalCompleteness
    opposite_satisfiedBy_iff_sameBrandtSignature
    valid_sameBrandtSignature)

end Brandt

namespace Brandt.CellContains

export SemigroupBasis.CoRoots.S5_415.CellContains (two_le_length)

end Brandt.CellContains

abbrev basis : List (Identity Nat) := H7.basis

abbrev G : Semigroup (TermSemigroup basis) :=
  termSemigroup basis

/-! ## Pointwise H7 laws in the term semigroup -/

theorem termSemigroup_square_eq_cube
    (value : TermSemigroup basis) :
    G.mul value value = G.mul (G.mul value value) value := by
  obtain ⟨word, rfl⟩ :=
    (derivationCongruence basis).projection_surjective value
  simpa only [termSemigroup_mul_termClass] using
    (termClass_eq_iff_derives basis).2
      (H7.derivesPowerExpansion word)

theorem termSemigroup_sandwich
    (anchor excursion : TermSemigroup basis) :
    G.mul (G.mul anchor excursion) anchor =
      G.mul
        (G.mul
          (G.mul (G.mul anchor excursion) anchor)
          excursion)
        anchor := by
  obtain ⟨anchorWord, rfl⟩ :=
    (derivationCongruence basis).projection_surjective anchor
  obtain ⟨excursionWord, rfl⟩ :=
    (derivationCongruence basis).projection_surjective excursion
  simpa only [termSemigroup_mul_termClass] using
    (termClass_eq_iff_derives basis).2
      (H7.derivesSandwichExpansion anchorWord excursionWord)

theorem termSemigroup_graphSwitch
    (anchor first second : TermSemigroup basis) :
    G.mul (G.mul (G.mul (G.mul anchor first) anchor) second) anchor =
      G.mul (G.mul (G.mul (G.mul anchor second) anchor) first) anchor := by
  obtain ⟨anchorWord, rfl⟩ :=
    (derivationCongruence basis).projection_surjective anchor
  obtain ⟨firstWord, rfl⟩ :=
    (derivationCongruence basis).projection_surjective first
  obtain ⟨secondWord, rfl⟩ :=
    (derivationCongruence basis).projection_surjective second
  simpa only [termSemigroup_mul_termClass] using
    (termClass_eq_iff_derives basis).2
      (H7.derivesGraphSwitch anchorWord firstWord secondWord)

/-! ## The fixed right-action representative needs no square commutation -/

/-- The fixed Hall--Kublanovskii representative construction under exactly
the two pointwise laws used by its calculation. -/
theorem exists_fixedRightActionRepresentative_of_sandwich_graphSwitch
    {M : Semigroup S}
    (sandwich :
      ∀ x y,
        M.mul (M.mul x y) x =
          M.mul (M.mul (M.mul (M.mul x y) x) y) x)
    (graphSwitch :
      ∀ x y w,
        M.mul (M.mul (M.mul (M.mul x y) x) w) x =
          M.mul (M.mul (M.mul (M.mul x w) x) y) x)
    {z x : S}
    (zRegular : M.IsRegular z)
    (xNotInIdeal : ¬ (x ∈ Semigroup.I_z M z)) :
    ∃ y, M.PrincipalSandwichMem z y ∧
      ∀ t, M.PrincipalSandwichMem z t →
        M.mul x t = M.mul y t := by
  rcases zRegular with ⟨zInv, zInverse⟩
  rcases Semigroup.principalSandwichMem_of_not_mem_I_z xNotInIdeal with
    ⟨p, q, zFactor⟩
  let w := M.mul (M.mul q zInv) p
  let y := M.mul (M.mul x w) x
  have wInSandwich : M.PrincipalSandwichMem z w := by
    have zInvInSandwich : M.PrincipalSandwichMem z zInv :=
      zInverse.inverse_principalSandwichMem
    exact (zInvInSandwich.mul_left q).mul_right p
  have yInSandwich : M.PrincipalSandwichMem z y :=
    (wInSandwich.mul_left x).mul_right x
  have zInYSandwich : M.PrincipalSandwichMem y z := by
    refine ⟨p, q, ?_⟩
    calc
      z = M.mul (M.mul z zInv) z := zInverse.1.symm
      _ =
          M.mul
            (M.mul (M.mul (M.mul p x) q) zInv)
            (M.mul (M.mul p x) q) := by
        calc
          M.mul (M.mul z zInv) z =
              M.mul
                (M.mul (M.mul (M.mul p x) q) zInv)
                z :=
            congrArg (fun value => M.mul (M.mul value zInv) z)
              zFactor
          _ =
              M.mul
                (M.mul (M.mul (M.mul p x) q) zInv)
                (M.mul (M.mul p x) q) :=
            congrArg
              (fun value =>
                M.mul
                  (M.mul (M.mul (M.mul p x) q) zInv)
                  value)
              zFactor
      _ = M.mul (M.mul p y) q := by
        simp only [w, y, M.assoc]
  have principalSandwichEq :
      M.PrincipalSandwichMem z = M.PrincipalSandwichMem y :=
    Semigroup.principalSandwich_eq_of_mutual_mem
      zInYSandwich yInSandwich
  refine ⟨y, yInSandwich, ?_⟩
  intro t tInSandwich
  have tInYSandwich : M.PrincipalSandwichMem y t := by
    rw [← principalSandwichEq]
    exact tInSandwich
  rcases tInYSandwich with ⟨r, s, tFactor⟩
  have expandW :=
    congrArg
      (fun cell => M.mul (M.mul (M.mul x r) cell) s)
      (sandwich x w)
  have switchPrefix :=
    congrArg
      (fun partialProduct =>
        M.mul (M.mul (M.mul partialProduct w) x) s)
      (graphSwitch x r w)
  calc
    M.mul x t =
        M.mul x (M.mul (M.mul r y) s) :=
      congrArg (fun value => M.mul x value) tFactor
    _ =
        M.mul
          (M.mul (M.mul x r) (M.mul (M.mul x w) x))
          s := by
      simp only [y, M.assoc]
    _ =
        M.mul
          (M.mul (M.mul x r)
            (M.mul (M.mul (M.mul (M.mul x w) x) w) x))
          s :=
      expandW
    _ = M.mul y (M.mul (M.mul r y) s) := by
      simpa only [y, M.assoc] using switchPrefix
    _ = M.mul y t :=
      (congrArg (fun value => M.mul y value) tFactor).symm

/-- The weakened fixed-representative theorem supplies the complete
right-Schutzenberger image condition. -/
theorem rightSchutzenbergerImageCondition_of_sandwich_graphSwitch
    {M : Semigroup S}
    (sandwich :
      ∀ x y,
        M.mul (M.mul x y) x =
          M.mul (M.mul (M.mul (M.mul x y) x) y) x)
    (graphSwitch :
      ∀ x y w,
        M.mul (M.mul (M.mul (M.mul x y) x) w) x =
          M.mul (M.mul (M.mul (M.mul x w) x) y) x)
    {z : S} (zRegular : M.IsRegular z) :
    M.RightSchutzenbergerImageCondition z := by
  intro x xNotInIdeal _
  rcases
      exists_fixedRightActionRepresentative_of_sandwich_graphSwitch
        sandwich graphSwitch zRegular xNotInIdeal with
    ⟨y, yInSandwich, sameAction⟩
  exact
    ⟨y, yInSandwich,
      Semigroup.rightSchutzenbergerRel_of_mul_eq_on_principalSandwich
        M z sameAction⟩

/-- Repeated H7 classes therefore have the full principal-sandwich image
property in their original right quotient. -/
theorem repeatedTermClass_rightSchutzenbergerImageCondition
    (word : Word Nat) (repeated : Brandt.RepeatedWord word) :
    G.RightSchutzenbergerImageCondition (termClass basis word) :=
  rightSchutzenbergerImageCondition_of_sandwich_graphSwitch
    termSemigroup_sandwich termSemigroup_graphSwitch
    (Repeated.repeatedTermClassRegularity word repeated)

/-! ## Brandt agreement in the opposite right quotient -/

universe u

private theorem modelsBrandtBasis_of_brandtLaws
    {T : Type u} {M : Semigroup T} (laws : M.BrandtLaws) :
    Models M Brandt.basis := by
  intro identity member
  simp only [Brandt.basis, List.mem_cons, List.not_mem_nil, or_false]
    at member
  rcases member with rfl | rfl | rfl
  · intro valuation
    change
      M.mul (valuation 0) (valuation 0) =
        M.mul (M.mul (valuation 0) (valuation 0)) (valuation 0)
    exact laws.square_eq_cube (valuation 0)
  · intro valuation
    change
      M.mul (M.mul (valuation 0) (valuation 1)) (valuation 0) =
        M.mul
          (M.mul
            (M.mul (M.mul (valuation 0) (valuation 1)) (valuation 0))
            (valuation 1))
          (valuation 0)
    exact laws.sandwich (valuation 0) (valuation 1)
  · intro valuation
    change
      M.mul
          (M.mul
            (M.mul (valuation 0) (valuation 0))
            (valuation 1))
          (valuation 1) =
        M.mul
          (M.mul
            (M.mul (valuation 1) (valuation 1))
            (valuation 0))
          (valuation 0)
    simpa only [M.assoc] using
      laws.squares_commute (valuation 0) (valuation 1)

theorem oppositeRightSchutzenbergerQuotient_brandtLaws
    (z : TermSemigroup basis) :
    let C :=
      Semigroup.rightSchutzenbergerCongruence G.opposite z
    C.quotientSemigroup.BrandtLaws := by
  dsimp only
  let C := Semigroup.rightSchutzenbergerCongruence G.opposite z
  refine
    { square_eq_cube := ?_
      sandwich := ?_
      squares_commute := ?_ }
  · intro value
    refine _root_.Quotient.inductionOn value ?_
    intro representative
    change
      C.classOf (G.opposite.mul representative representative) =
        C.classOf
          (G.opposite.mul
            (G.opposite.mul representative representative)
            representative)
    apply congrArg C.classOf
    simpa only [Semigroup.opposite_mul, G.assoc] using
      termSemigroup_square_eq_cube representative
  · intro left right
    refine _root_.Quotient.inductionOn left ?_
    intro leftRepresentative
    refine _root_.Quotient.inductionOn right ?_
    intro rightRepresentative
    change
      C.classOf
          (G.opposite.mul
            (G.opposite.mul leftRepresentative rightRepresentative)
            leftRepresentative) =
        C.classOf
          (G.opposite.mul
            (G.opposite.mul
              (G.opposite.mul
                (G.opposite.mul
                  leftRepresentative rightRepresentative)
                leftRepresentative)
              rightRepresentative)
            leftRepresentative)
    apply congrArg C.classOf
    simpa only [Semigroup.opposite_mul, G.assoc] using
      termSemigroup_sandwich leftRepresentative rightRepresentative
  · exact
      H7.termSemigroupOpposite_rightSchutzenbergerQuotient_squaresCommute z

theorem oppositeRightSchutzenbergerQuotient_modelsBrandtBasis
    (z : TermSemigroup basis) :
    let C :=
      Semigroup.rightSchutzenbergerCongruence G.opposite z
    Models C.quotientSemigroup Brandt.basis :=
  modelsBrandtBasis_of_brandtLaws <|
    oppositeRightSchutzenbergerQuotient_brandtLaws z

private theorem reverse_sameBrandtSignature
    {left right : Word Nat}
    (same : Brandt.SameBrandtSignature left right) :
    Brandt.SameBrandtSignature left.reverse right.reverse := by
  let identity : Identity Nat := ⟨left, right⟩
  have oppositeValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_415.table.semigroup.opposite :=
    (Brandt.opposite_satisfiedBy_iff_sameBrandtSignature identity).2 same
  have reversedValid :
      identity.reversed.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_415.table.semigroup :=
    (Identity.satisfiedBy_opposite_iff_reversed identity
      SemigroupBasis.Generated.Catalogue.S5_415.table.semigroup).1
        oppositeValid
  exact Brandt.valid_sameBrandtSignature reversedValid

/-- Every rooted Brandt pair is related in the opposite right quotient.
Reversing the words compensates for evaluation in the opposite semigroup. -/
theorem oppositeRightRel_of_sameRootedBrandtSignature
    (z : TermSemigroup basis) {left right : Word Nat}
    (same : H7.SameRootedBrandtSignature left right) :
    (Semigroup.rightSchutzenbergerCongruence G.opposite z).r
      (termClass basis left) (termClass basis right) := by
  let C := Semigroup.rightSchutzenbergerCongruence G.opposite z
  let projection := C.projection
  have quotientModels :
      Models C.quotientSemigroup Brandt.basis :=
    oppositeRightSchutzenbergerQuotient_modelsBrandtBasis z
  have reverseSame :
      Brandt.SameBrandtSignature left.reverse right.reverse :=
    reverse_sameBrandtSignature same.brandt
  have evaluated :=
    Derives.sound quotientModels
      (Brandt.brandtDerivationalCompleteness
        left.reverse right.reverse reverseSame)
      (fun letter =>
        projection.toFun
          (termClass basis (Word.singleton letter)))
  apply (C.classOf_eq_iff).mp
  change
    projection.toFun (termClass basis left) =
      projection.toFun (termClass basis right)
  calc
    projection.toFun (termClass basis left) =
        projection.toFun
          (G.opposite.eval
            (fun letter =>
              termClass basis (Word.singleton letter))
            left.reverse) := by
      rw [Semigroup.eval_opposite_eq_reverse, Word.reverse_reverse,
        termSemigroup_eval_singletonClass]
    _ =
        C.quotientSemigroup.eval
          (fun letter =>
            projection.toFun
              (termClass basis (Word.singleton letter)))
          left.reverse :=
      projection.map_eval
        (fun letter => termClass basis (Word.singleton letter))
        left.reverse
    _ =
        C.quotientSemigroup.eval
          (fun letter =>
            projection.toFun
              (termClass basis (Word.singleton letter)))
          right.reverse :=
      evaluated
    _ =
        projection.toFun
          (G.opposite.eval
            (fun letter =>
              termClass basis (Word.singleton letter))
            right.reverse) :=
      (projection.map_eval
        (fun letter => termClass basis (Word.singleton letter))
        right.reverse).symm
    _ = projection.toFun (termClass basis right) := by
      rw [Semigroup.eval_opposite_eq_reverse, Word.reverse_reverse,
        termSemigroup_eval_singletonClass]

/-! ## Opposite agreement synchronizes original Rees-ideal membership -/

theorem opposite_principalSandwichMem_iff
    {M : Semigroup S} (z x : S) :
    M.opposite.PrincipalSandwichMem z x ↔
      M.PrincipalSandwichMem z x := by
  constructor
  · rintro ⟨left, right, factorization⟩
    refine ⟨right, left, ?_⟩
    simpa only [Semigroup.opposite_mul, M.assoc] using factorization
  · rintro ⟨left, right, factorization⟩
    refine ⟨right, left, ?_⟩
    simpa only [Semigroup.opposite_mul, M.assoc] using factorization

theorem opposite_mem_Iz_iff
    {M : Semigroup S} (z x : S) :
    x ∈ Semigroup.I_z M.opposite z ↔
      x ∈ Semigroup.I_z M z := by
  change
    (¬ M.opposite.PrincipalSandwichMem x z) ↔
      ¬ M.PrincipalSandwichMem x z
  exact not_congr (opposite_principalSandwichMem_iff x z)

/-- At a regular selected element, opposite-right equivalence forces the
two original right translates to lie outside `I_z` simultaneously. -/
theorem rightTranslate_notMem_Iz_imp_of_oppositeRightRel
    {M : Semigroup S} {z left right : S}
    (zRegular : M.IsRegular z)
    (oppositeRelated :
      M.opposite.RightSchutzenbergerRel z left right)
    (translate : S)
    (leftOutside :
      ¬ (M.mul left translate ∈ Semigroup.I_z M z)) :
    ¬ (M.mul right translate ∈ Semigroup.I_z M z) := by
  rcases zRegular with ⟨zInv, zInverse⟩
  rcases Semigroup.principalSandwichMem_of_not_mem_I_z leftOutside with
    ⟨front, suffix, zFactor⟩
  let cycle :=
    M.mul (M.mul (M.mul translate suffix) zInv) front
  have cycleInSandwich : M.PrincipalSandwichMem z cycle := by
    have inverseInSandwich : M.PrincipalSandwichMem z zInv :=
      zInverse.inverse_principalSandwichMem
    exact
      (inverseInSandwich.mul_left (M.mul translate suffix)).mul_right
        front
  have cycleLeftFactor :
      z =
        M.mul
          (M.mul (M.mul front left) (M.mul cycle left))
          (M.mul translate suffix) := by
    calc
      z = M.mul (M.mul z zInv) z := zInverse.1.symm
      _ =
          M.mul
            (M.mul
              (M.mul
                (M.mul front (M.mul left translate))
                suffix)
              zInv)
            (M.mul
              (M.mul front (M.mul left translate))
              suffix) := by
        calc
          M.mul (M.mul z zInv) z =
              M.mul
                (M.mul
                  (M.mul
                    (M.mul front (M.mul left translate))
                    suffix)
                  zInv)
                z :=
            congrArg (fun value => M.mul (M.mul value zInv) z)
              zFactor
          _ =
              M.mul
                (M.mul
                  (M.mul
                    (M.mul front (M.mul left translate))
                    suffix)
                  zInv)
                (M.mul
                  (M.mul front (M.mul left translate))
                  suffix) :=
            congrArg
              (fun value =>
                M.mul
                  (M.mul
                    (M.mul
                      (M.mul front (M.mul left translate))
                      suffix)
                    zInv)
                  value)
              zFactor
      _ =
          M.mul
            (M.mul (M.mul front left) (M.mul cycle left))
            (M.mul translate suffix) := by
        simp only [cycle, M.assoc]
  have cycleLeftOutside :
      ¬ (M.mul cycle left ∈ Semigroup.I_z M z) := by
    intro member
    change
      ¬ M.PrincipalSandwichMem (M.mul cycle left) z
      at member
    exact member ⟨M.mul front left, M.mul translate suffix,
      cycleLeftFactor⟩
  have oppositeRees :=
    oppositeRelated cycle
      ((opposite_principalSandwichMem_iff z cycle).2 cycleInSandwich)
  have cycleEquality : M.mul cycle left = M.mul cycle right := by
    rcases oppositeRees with equality | bothInIdeal
    · simpa only [Semigroup.opposite_mul] using equality
    · exfalso
      apply cycleLeftOutside
      exact (opposite_mem_Iz_iff z (M.mul cycle left)).1 <|
        by
          simpa only [Semigroup.opposite_mul] using bothInIdeal.1
  have rightFactor :
      z =
        M.mul
          (M.mul
            (M.mul (M.mul front left) cycle)
            (M.mul right translate))
          suffix := by
    calc
      z =
          M.mul
            (M.mul (M.mul front left) (M.mul cycle left))
            (M.mul translate suffix) :=
        cycleLeftFactor
      _ =
          M.mul
            (M.mul (M.mul front left) (M.mul cycle right))
            (M.mul translate suffix) := by
        exact congrArg
          (fun value =>
            M.mul (M.mul (M.mul front left) value)
              (M.mul translate suffix))
          cycleEquality
      _ =
          M.mul
            (M.mul
              (M.mul (M.mul front left) cycle)
              (M.mul right translate))
            suffix := by
        simp only [M.assoc]
  intro rightInIdeal
  change
    ¬ M.PrincipalSandwichMem (M.mul right translate) z
    at rightInIdeal
  exact rightInIdeal
    ⟨M.mul (M.mul front left) cycle, suffix, rightFactor⟩

theorem rightTranslate_mem_Iz_iff_of_regular_of_oppositeRightRel
    {M : Semigroup S} {z left right : S}
    (zRegular : M.IsRegular z)
    (oppositeRelated :
      M.opposite.RightSchutzenbergerRel z left right)
    (translate : S) :
    M.mul left translate ∈ Semigroup.I_z M z ↔
      M.mul right translate ∈ Semigroup.I_z M z := by
  constructor
  · intro leftIn
    apply Classical.byContradiction
    intro rightOutside
    have leftOutside :=
      rightTranslate_notMem_Iz_imp_of_oppositeRightRel
        zRegular
        (Semigroup.rightSchutzenbergerRel_symm
          M.opposite z oppositeRelated)
        translate rightOutside
    exact leftOutside leftIn
  · intro rightIn
    apply Classical.byContradiction
    intro leftOutside
    have rightOutside :=
      rightTranslate_notMem_Iz_imp_of_oppositeRightRel
        zRegular oppositeRelated translate leftOutside
    exact rightOutside rightIn

/-! ## Common-left-factor cancellation in the original right quotient -/

/-- Repeated rooted-signature pairs agree in the two original-orientation
right Schutzenberger quotients used by guarded Kublanovskii separation.

Opposite-right agreement supplies equality under every left action after
choosing principal-sandwich representatives.  Repeatedness makes both
projected classes regular and ensures that each word has a nonempty tail.
The common literal head therefore supplies a common left factor, so
zero-simplicity and square-cube stability force the two classes to agree. -/
theorem repeatedPairRightProjectionAgreement :
    Repeated.RepeatedPairRightProjectionAgreement := by
  classical
  intro left right same leftRepeated rightRepeated

  have leftTailNonempty : left.tail ≠ [] := by
    intro tailEmpty
    have lower :=
      Brandt.CellContains.two_le_length
        (leftRepeated left.head (by simp [Word.toList]))
    simpa [Word.toList, tailEmpty] using lower
  have rightTailNonempty : right.tail ≠ [] := by
    intro tailEmpty
    have lower :=
      Brandt.CellContains.two_le_length
        (rightRepeated right.head (by simp [Word.toList]))
    simpa [Word.toList, tailEmpty] using lower

  obtain ⟨leftSecond, leftRest, leftTailShape⟩ :=
    List.exists_cons_of_ne_nil leftTailNonempty
  obtain ⟨rightSecond, rightRest, rightTailShape⟩ :=
    List.exists_cons_of_ne_nil rightTailNonempty

  let leftSuffix : Word Nat := ⟨leftSecond, leftRest⟩
  let rightSuffix : Word Nat := ⟨rightSecond, rightRest⟩

  have leftWordFactor :
      left = Word.singleton left.head ++ leftSuffix := by
    apply Word.toList_injective
    simp [Word.toList, leftSuffix, leftTailShape]
  have rightWordFactor :
      right = Word.singleton right.head ++ rightSuffix := by
    apply Word.toList_injective
    simp [Word.toList, rightSuffix, rightTailShape]

  let common :=
    termClass basis (Word.singleton left.head)
  let leftSuffixClass := termClass basis leftSuffix
  let rightSuffixClass := termClass basis rightSuffix

  have leftClassFactor :
      termClass basis left =
        G.mul common leftSuffixClass := by
    calc
      termClass basis left =
          termClass basis
            (Word.singleton left.head ++ leftSuffix) :=
        congrArg (termClass basis) leftWordFactor
      _ = G.mul common leftSuffixClass := by
        simpa only [common, leftSuffixClass] using
          (termSemigroup_mul_termClass basis
            (Word.singleton left.head) leftSuffix).symm

  have rightClassFactor :
      termClass basis right =
        G.mul common rightSuffixClass := by
    calc
      termClass basis right =
          termClass basis
            (Word.singleton right.head ++ rightSuffix) :=
        congrArg (termClass basis) rightWordFactor
      _ =
          G.mul
            (termClass basis (Word.singleton right.head))
            rightSuffixClass := by
        simpa only [rightSuffixClass] using
          (termSemigroup_mul_termClass basis
            (Word.singleton right.head) rightSuffix).symm
      _ = G.mul common rightSuffixClass := by
        simpa only [common] using
          congrArg
            (fun head =>
              G.mul
                (termClass basis (Word.singleton head))
                rightSuffixClass)
            same.head.symm

  have agreementAt
      (z : Word Nat) (zRepeated : Brandt.RepeatedWord z) :
      (Semigroup.rightSchutzenbergerCongruence
          G (termClass basis z)).projection.toFun
            (termClass basis left) =
        (Semigroup.rightSchutzenbergerCongruence
          G (termClass basis z)).projection.toFun
            (termClass basis right) := by
    let zClass := termClass basis z
    let C :=
      Semigroup.rightSchutzenbergerCongruence G zClass
    let Q := C.quotientSemigroup

    have imageCondition :
        G.RightSchutzenbergerImageCondition zClass := by
      simpa only [zClass] using
        repeatedTermClass_rightSchutzenbergerImageCondition
          z zRepeated

    have quotientZeroSimple : Q.ZeroSimple := by
      change
        (Semigroup.rightSchutzenbergerCongruence
          G zClass).quotientSemigroup.ZeroSimple
      exact
        Semigroup.rightSchutzenbergerQuotient_zeroSimple_of_imageCondition
          (G := G) (z := zClass) imageCondition

    have quotientSquareEqualsCube :
        Q.SquareEqualsCube := by
      intro value
      refine _root_.Quotient.inductionOn value ?_
      intro representative
      change
        C.classOf (G.mul representative representative) =
          C.classOf
            (G.mul
              (G.mul representative representative)
              representative)
      exact
        congrArg C.classOf
          (termSemigroup_square_eq_cube representative)

    have leftRegular :
        Q.IsRegular
          (C.classOf (termClass basis left)) := by
      simpa only [C, Q] using
        Semigroup.rightSchutzenberger_classOf_isRegular
          (G := G) (z := zClass)
          (Repeated.repeatedTermClassRegularity
            left leftRepeated)

    have rightRegular :
        Q.IsRegular
          (C.classOf (termClass basis right)) := by
      simpa only [C, Q] using
        Semigroup.rightSchutzenberger_classOf_isRegular
          (G := G) (z := zClass)
          (Repeated.repeatedTermClassRegularity
            right rightRepeated)

    have leftFactor :
        C.classOf (termClass basis left) =
          Q.mul (C.classOf common)
            (C.classOf leftSuffixClass) := by
      change
        C.classOf (termClass basis left) =
          C.classOf (G.mul common leftSuffixClass)
      exact congrArg C.classOf leftClassFactor

    have rightFactor :
        C.classOf (termClass basis right) =
          Q.mul (C.classOf common)
            (C.classOf rightSuffixClass) := by
      change
        C.classOf (termClass basis right) =
          C.classOf (G.mul common rightSuffixClass)
      exact congrArg C.classOf rightClassFactor

    have oppositeRelated :
        G.opposite.RightSchutzenbergerRel zClass
          (termClass basis left)
          (termClass basis right) :=
      oppositeRightRel_of_sameRootedBrandtSignature
        zClass same

    have sameLeftAction :
        ∀ value : C.Quotient,
          Q.mul value
              (C.classOf (termClass basis left)) =
            Q.mul value
              (C.classOf (termClass basis right)) := by
      intro value
      rcases
          Semigroup.every_rightSchutzenberger_class_has_principalRepresentative_of_imageCondition
            G zClass imageCondition value with
        ⟨representative, representativePrincipal,
          representativeClass⟩
      rw [← representativeClass]
      change
        C.classOf
            (G.mul representative (termClass basis left)) =
          C.classOf
            (G.mul representative (termClass basis right))
      apply
        (Semigroup.rightSchutzenberger_classOf_eq_iff
          G zClass).2
      apply
        Semigroup.reesRel_imp_rightSchutzenbergerRel
          G zClass
      have oppositeRees :=
        oppositeRelated representative
          ((opposite_principalSandwichMem_iff
            (M := G) zClass representative).2
              representativePrincipal)
      rcases oppositeRees with equality | bothInIdeal
      · exact Or.inl <| by
          simpa only [Semigroup.opposite_mul] using
            equality
      · exact Or.inr
          ⟨(opposite_mem_Iz_iff
              (M := G) zClass
              (G.mul representative
                (termClass basis left))).1
              (by
                simpa only [Semigroup.opposite_mul] using
                  bothInIdeal.1),
            (opposite_mem_Iz_iff
              (M := G) zClass
              (G.mul representative
                (termClass basis right))).1
              (by
                simpa only [Semigroup.opposite_mul] using
                  bothInIdeal.2)⟩

    change
      C.classOf (termClass basis left) =
        C.classOf (termClass basis right)
    exact
      Semigroup.ZeroSimple.eq_of_commonLeftFactor_of_leftActionEq
        quotientZeroSimple quotientSquareEqualsCube
        leftRegular rightRegular leftFactor rightFactor
        sameLeftAction

  exact
    ⟨agreementAt left leftRepeated,
      agreementAt right rightRepeated⟩

/-- The common-left-factor quotient argument closes the repeated H7 branch. -/
theorem rootedRepeatedCompleteness :
    H7.RootedRepeatedCompleteness :=
  Repeated.rootedRepeatedCompleteness_of_repeatedPairProjectionAgreement
    repeatedPairRightProjectionAgreement

/-! ## Full H7 completeness and the two concrete endpoints -/

theorem derivesOfSameRootedBrandtSignature
    {left right : Word Nat}
    (same : H7.SameRootedBrandtSignature left right) :
    Derives basis left right :=
  H7.derivesOfSameRootedBrandtSignature_of_repeatedCompleteness
    rootedRepeatedCompleteness same

private theorem foldl_leftZeroBand
    {M : Semigroup (Fin 6)} {p q : Fin 6}
    (pp : M.mul p p = p) (pq : M.mul p q = p)
    (qp : M.mul q p = q) (qq : M.mul q q = q)
    (valuation : Nat → Fin 6)
    (range : ∀ x, valuation x = p ∨ valuation x = q) :
    ∀ (letters : List Nat) (acc : Fin 6), acc = p ∨ acc = q →
      letters.foldl (fun current x => M.mul current (valuation x)) acc =
        acc := by
  intro letters
  induction letters with
  | nil => intro acc _; rfl
  | cons x rest ih =>
      intro acc accRange
      have step : M.mul acc (valuation x) = acc := by
        rcases accRange with rfl | rfl <;>
          rcases range x with hx | hx <;> rw [hx] <;> assumption
      rw [List.foldl_cons, step]
      exact ih acc accRange

/-- A two-element left-zero subsemigroup detects the literal head of every
identity valid in the ambient six-element semigroup. -/
theorem head_eq_of_leftZeroBand_valid
    {M : Semigroup (Fin 6)} {p q : Fin 6}
    (pp : M.mul p p = p) (pq : M.mul p q = p)
    (qp : M.mul q p = q) (qq : M.mul q q = q)
    (distinct : p ≠ q)
    (identity : Identity Nat) (valid : identity.SatisfiedBy M) :
    identity.lhs.head = identity.rhs.head := by
  by_cases same : identity.lhs.head = identity.rhs.head
  · exact same
  have range : ∀ letter : Nat,
      (if letter = identity.lhs.head then p else q) = p ∨
        (if letter = identity.lhs.head then p else q) = q := by
    intro letter
    by_cases equal : letter = identity.lhs.head <;> simp [equal]
  have evalWord : ∀ word : Word Nat,
      M.eval
          (fun letter =>
            if letter = identity.lhs.head then p else q)
          word =
        (if word.head = identity.lhs.head then p else q) := by
    intro word
    exact
      foldl_leftZeroBand pp pq qp qq _ range word.tail _
        (range word.head)
  have evaluated :=
    valid
      (fun letter =>
        if letter = identity.lhs.head then p else q)
  rw [evalWord identity.lhs, evalWord identity.rhs, if_pos rfl,
    if_neg (fun equal => same equal.symm)] at evaluated
  exact (distinct evaluated).elim

namespace S6_8562

abbrev table : FiniteTable :=
  SemigroupBasis.Generated.Order6LeeA2LatticeNodes.S6_8562.table

def brandtQuotient :
    SplitSurjection table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_415.table.semigroup where
  toFun := fun value : Fin 6 =>
    (if value = 0 then 0 else
      if value = 1 then 1 else
        if value = 2 then 2 else
          if value = 3 then 3 else
            if value = 4 then 0 else 4 : Fin 5)
  map_mul := by decide
  preimage := fun value : Fin 5 =>
    (if value = 0 then 0 else
      if value = 1 then 1 else
        if value = 2 then 2 else
          if value = 3 then 3 else 5 : Fin 6)
  right_inverse := by decide

theorem representative_basis :
    BasisFor table.semigroup basis := by
  refine
    ⟨SemigroupBasis.Generated.Order6LeeA2LatticeNodes.S6_8562.models,
      ?_⟩
  intro identity valid
  apply derivesOfSameRootedBrandtSignature
  exact
    H7.sameRootedBrandtSignature_of_valid identity
      (brandtQuotient.pushforwardIdentity identity valid)
      (head_eq_of_leftZeroBand_valid
        (p := (0 : Fin 6)) (q := (4 : Fin 6))
        (by decide) (by decide) (by decide) (by decide) (by decide)
        identity valid)

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_8562

namespace S6_11276

abbrev table : FiniteTable :=
  SemigroupBasis.Generated.Order6LeeA2LatticeNodes.S6_11276.table

def brandtQuotient :
    SplitSurjection table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_415.table.semigroup where
  toFun := fun value : Fin 6 =>
    (if value = 0 then 0 else
      if value = 1 then 1 else
        if value = 2 then 0 else
          if value = 3 then 2 else
            if value = 4 then 3 else 4 : Fin 5)
  map_mul := by decide
  preimage := fun value : Fin 5 =>
    (if value = 0 then 0 else
      if value = 1 then 1 else
        if value = 2 then 3 else
          if value = 3 then 4 else 5 : Fin 6)
  right_inverse := by decide

theorem representative_basis :
    BasisFor table.semigroup basis := by
  refine
    ⟨SemigroupBasis.Generated.Order6LeeA2LatticeNodes.S6_11276.models,
      ?_⟩
  intro identity valid
  apply derivesOfSameRootedBrandtSignature
  exact
    H7.sameRootedBrandtSignature_of_valid identity
      (brandtQuotient.pushforwardIdentity identity valid)
      (head_eq_of_leftZeroBand_valid
        (p := (0 : Fin 6)) (q := (2 : Fin 6))
        (by decide) (by decide) (by decide) (by decide) (by decide)
        identity valid)

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_11276

/-! ## Alternative outside-ideal sufficient condition -/

/-- A stronger alternative cancellation premise retained for callers which
already have literal outside-ideal equality. -/
def RepeatedPairOutsideRightTranslateEquality : Prop :=
  ∀ left right : Word Nat,
    H7.SameRootedBrandtSignature left right →
      Brandt.RepeatedWord left →
        Brandt.RepeatedWord right →
          (∀ translate : TermSemigroup basis,
            G.PrincipalSandwichMem (termClass basis left) translate →
              ¬ (G.mul (termClass basis left) translate ∈
                  Semigroup.I_z G (termClass basis left)) →
                G.mul (termClass basis left) translate =
                  G.mul (termClass basis right) translate) ∧
          (∀ translate : TermSemigroup basis,
            G.PrincipalSandwichMem (termClass basis right) translate →
              ¬ (G.mul (termClass basis left) translate ∈
                  Semigroup.I_z G (termClass basis right)) →
                G.mul (termClass basis left) translate =
                  G.mul (termClass basis right) translate)

theorem repeatedPairRightProjectionAgreement_of_outsideEquality
    (outsideEquality : RepeatedPairOutsideRightTranslateEquality) :
    Repeated.RepeatedPairRightProjectionAgreement := by
  intro left right same leftRepeated rightRepeated
  have oppositeAtLeft :
      G.opposite.RightSchutzenbergerRel
        (termClass basis left)
        (termClass basis left)
        (termClass basis right) :=
    oppositeRightRel_of_sameRootedBrandtSignature
      (termClass basis left) same
  have oppositeAtRight :
      G.opposite.RightSchutzenbergerRel
        (termClass basis right)
        (termClass basis left)
        (termClass basis right) :=
    oppositeRightRel_of_sameRootedBrandtSignature
      (termClass basis right) same
  have leftRegular :=
    Repeated.repeatedTermClassRegularity left leftRepeated
  have rightRegular :=
    Repeated.repeatedTermClassRegularity right rightRepeated
  have outside := outsideEquality left right same leftRepeated rightRepeated
  constructor
  · apply
      (Semigroup.rightSchutzenberger_projection_eq_iff
        G (termClass basis left)).2
    intro translate translateInSandwich
    by_cases leftInIdeal :
        G.mul (termClass basis left) translate ∈
          Semigroup.I_z G (termClass basis left)
    · exact Or.inr
        ⟨leftInIdeal,
          (rightTranslate_mem_Iz_iff_of_regular_of_oppositeRightRel
            leftRegular oppositeAtLeft translate).mp leftInIdeal⟩
    · exact Or.inl <|
        outside.1 translate translateInSandwich leftInIdeal
  · apply
      (Semigroup.rightSchutzenberger_projection_eq_iff
        G (termClass basis right)).2
    intro translate translateInSandwich
    by_cases leftInIdeal :
        G.mul (termClass basis left) translate ∈
          Semigroup.I_z G (termClass basis right)
    · exact Or.inr
        ⟨leftInIdeal,
          (rightTranslate_mem_Iz_iff_of_regular_of_oppositeRightRel
            rightRegular oppositeAtRight translate).mp leftInIdeal⟩
    · exact Or.inl <|
        outside.2 translate translateInSandwich leftInIdeal

theorem rootedRepeatedCompleteness_of_outsideEquality
    (outsideEquality : RepeatedPairOutsideRightTranslateEquality) :
    H7.RootedRepeatedCompleteness :=
  Repeated.rootedRepeatedCompleteness_of_repeatedPairProjectionAgreement
    (repeatedPairRightProjectionAgreement_of_outsideEquality outsideEquality)

/-!
`RepeatedPairOutsideRightTranslateEquality` remains available as a stronger
sufficient condition, but `repeatedPairRightProjectionAgreement` and
`rootedRepeatedCompleteness` are unconditional source theorems above.
-/

end SemigroupBasis.CoRoots.Order6LeeA2LatticeNodesH7Projection
