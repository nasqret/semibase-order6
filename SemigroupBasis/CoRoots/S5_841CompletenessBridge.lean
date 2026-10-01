import SemigroupBasis.CoRoots.S5_841

namespace SemigroupBasis.CoRoots.S5_841

open SemigroupBasis
open SemigroupBasis.Examples

private theorem m20Mul_leftIdentity_bridge (value : Fin 5) :
    publishedM20Mul 1 value = value := by
  decide +revert

private theorem m20ListEval_cons_eq_eval
    (valuation : Nat → Fin 5) (head : Nat) (tail : List Nat) :
    m20ListEval valuation (head :: tail) =
      publishedM20Table.semigroup.eval valuation
        (S5_107.listWordOfCons head tail) := by
  unfold m20ListEval S5_107.listWordOfCons
  change
    tail.foldl
        (fun current letter =>
          publishedM20Mul current (valuation letter))
        (publishedM20Mul 1 (valuation head)) =
      tail.foldl
        (fun current letter =>
          publishedM20Mul current (valuation letter))
        (valuation head)
  rw [m20Mul_leftIdentity_bridge]

namespace M20ListEquivalent

theorem refl (letters : List Nat) :
    M20ListEquivalent letters letters :=
  fun _ => rfl

theorem symm {left right : List Nat}
    (equivalent : M20ListEquivalent left right) :
    M20ListEquivalent right left :=
  fun valuation => (equivalent valuation).symm

theorem trans {left middle right : List Nat}
    (first : M20ListEquivalent left middle)
    (second : M20ListEquivalent middle right) :
    M20ListEquivalent left right :=
  fun valuation => (first valuation).trans (second valuation)

theorem of_derives {left right : List Nat}
    (derivation : S5_107.ListDerives basis left right) :
    M20ListEquivalent left right := by
  cases derivation with
  | empty => exact refl []
  | @words leftHead rightHead leftTail rightTail wordDerivation =>
      intro valuation
      rw [m20ListEval_cons_eq_eval, m20ListEval_cons_eq_eval]
      exact wordDerivation.sound publishedM20Models valuation

theorem of_valid (identity : Identity Nat)
    (valid : identity.SatisfiedBy publishedM20Table.semigroup) :
    M20ListEquivalent identity.lhs.toList identity.rhs.toList := by
  cases identity with
  | mk left right =>
      cases left with
      | mk leftHead leftTail =>
          cases right with
          | mk rightHead rightTail =>
              intro valuation
              simp only [Word.toList]
              rw [m20ListEval_cons_eq_eval, m20ListEval_cons_eq_eval]
              exact valid valuation

end M20ListEquivalent

/-- Once the two-limited segmentation theorem is supplied, endpoint capping
promotes it to unrestricted completeness for Edmunds' historical `M20`.
This theorem does not construct either outstanding witness. -/
theorem m20Completeness_of_segmentation
    (quadratic : QuadraticBlockPermutationSixCaseObligation)
    (segmented : M20SegmentationCompletenessObligation quadratic) :
    M20CompletenessObligation := by
  rintro ⟨left, right⟩ valid
  have signature : SameM20Signature left right :=
    sameM20Signature_of_valid ⟨left, right⟩ valid
  have leftListDerivation :=
    listDerivesTwoLimitedReduction left.toList
  have rightListDerivation :=
    listDerivesTwoLimitedReduction right.toList
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail =>
          obtain
            ⟨leftCapHead, leftCapTail, leftCapShape,
              leftCapDerivation⟩ :=
            leftListDerivation.from_cons
          obtain
            ⟨rightCapHead, rightCapTail, rightCapShape,
              rightCapDerivation⟩ :=
            rightListDerivation.from_cons
          let leftCap : Word Nat :=
            S5_107.listWordOfCons leftCapHead leftCapTail
          let rightCap : Word Nat :=
            S5_107.listWordOfCons rightCapHead rightCapTail
          have leftCapToList :
              leftCap.toList =
                uniqueSeparatorEndpointCap
                  (Word.mk leftHead leftTail).toList := by
            simpa [leftCap, S5_107.listWordOfCons, Word.toList] using
              leftCapShape.symm
          have rightCapToList :
              rightCap.toList =
                uniqueSeparatorEndpointCap
                  (Word.mk rightHead rightTail).toList := by
            simpa [rightCap, S5_107.listWordOfCons, Word.toList] using
              rightCapShape.symm
          have capRawCounts :
              ∀ letter,
                leftCap.toList.count letter =
                  rightCap.toList.count letter := by
            intro letter
            rw [leftCapToList, rightCapToList,
              uniqueSeparatorEndpointCap_count,
              uniqueSeparatorEndpointCap_count]
            simpa [CappedMultiplicity, Nat.min_comm] using
              signature.cappedMultiplicity letter
          have capCounts :
              ∀ letter,
                Nat.min (leftCap.toList.count letter) 2 =
                  Nat.min (rightCap.toList.count letter) 2 := by
            intro letter
            exact congrArg (fun count => Nat.min count 2)
              (capRawCounts letter)
          have leftLimited :
              UniqueSeparatorTwoLimited leftCap.toList := by
            rw [leftCapToList]
            exact
              uniqueSeparatorEndpointCap_twoLimited
                (Word.mk leftHead leftTail).toList
          have rightLimited :
              UniqueSeparatorTwoLimited rightCap.toList := by
            rw [rightCapToList]
            exact
              uniqueSeparatorEndpointCap_twoLimited
                (Word.mk rightHead rightTail).toList
          have leftCapSignature :=
            derives_sameM20Signature leftCapDerivation
          have rightCapSignature :=
            derives_sameM20Signature rightCapDerivation
          have capPrecedence :
              ∀ x y,
                CompletePrecedenceList leftCap.toList x y ↔
                  CompletePrecedenceList rightCap.toList x y := by
            intro x y
            have composed :=
              (leftCapSignature.completePrecedence x y).symm.trans
                ((signature.completePrecedence x y).trans
                  (rightCapSignature.completePrecedence x y))
            simpa [CompletePrecedence] using composed
          have originalEquivalent :
              M20ListEquivalent
                (Word.mk leftHead leftTail).toList
                (Word.mk rightHead rightTail).toList :=
            M20ListEquivalent.of_valid
              ⟨Word.mk leftHead leftTail,
                Word.mk rightHead rightTail⟩ valid
          have capEquivalent :
              M20ListEquivalent leftCap.toList rightCap.toList := by
            rw [leftCapToList, rightCapToList]
            exact
              (M20ListEquivalent.of_derives leftListDerivation).symm.trans
                (originalEquivalent.trans
                  (M20ListEquivalent.of_derives rightListDerivation))
          have capListDerivation :=
            segmented leftLimited rightLimited capEquivalent
              capCounts capPrecedence
          have capWordDerivation :
              Derives basis leftCap rightCap := by
            have represented :
                S5_107.ListDerives basis
                  (leftCapHead :: leftCapTail)
                  (rightCapHead :: rightCapTail) := by
              simpa [leftCap, rightCap, S5_107.listWordOfCons,
                Word.toList] using capListDerivation
            simpa [leftCap, rightCap] using represented.toWord
          exact
            leftCapDerivation.trans
              (capWordDerivation.trans rightCapDerivation.symm)

end SemigroupBasis.CoRoots.S5_841
