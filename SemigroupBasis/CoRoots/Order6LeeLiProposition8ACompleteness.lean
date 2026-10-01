import SemigroupBasis.CoRoots.Order6LeeLiProposition8ANormalization
import SemigroupBasis.CoRoots.Order6LeeLiCompletePrecedencePermutation

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6LeeLiProposition8A

open SemigroupBasis
open SemigroupBasis.CoRoots.Order6LeeLiCompletePrecedencePermutation

private theorem derives_of_listDerives_toList
    {basisSet : List (Identity Nat)}
    (left right : Word Nat)
    (derivation :
      S5_107.ListDerives basisSet left.toList right.toList) :
    Derives basisSet left right := by
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail =>
          simpa [S5_107.listWordOfCons] using
            S5_107.ListDerives.toWord derivation

private theorem listDerives_target_ne_nil_of_word
    {basisSet : List (Identity Nat)}
    {source : Word Nat} {target : List Nat}
    (derivation :
      S5_107.ListDerives basisSet source.toList target) :
    target ≠ [] := by
  cases source with
  | mk head tail =>
      exact S5_107.ListDerives.target_ne_nil derivation

/-- Abstract assembly core for Lee--Li Proposition 8.1/A.

The hypotheses isolate the three constructive adapters still to be supplied:
an unrestricted cap-three canonicalizer, the separator condition of its
output, and the semantic complete-precedence characterization on canonical
outputs.  No particular canonical representation is fixed here. -/
theorem publishedBasisOfCanonicalPipeline
    (Canonical : List Nat → Prop)
    (normalize :
      ∀ source : List Nat,
        ∃ target : List Nat,
          Canonical target ∧
          (∀ letter, target.count letter ≤ 3) ∧
          (∀ letter,
            target.count letter = min (source.count letter) 3) ∧
          S5_107.ListDerives basis source target)
    (canonicalSimpleSplit :
      ∀ {target : List Nat},
        Canonical target → SimpleSplitCanonical target)
    (canonicalCompletePrecedence :
      ∀ {leftHead rightHead : Nat}
          {leftTail rightTail : List Nat},
        Canonical (leftHead :: leftTail) →
        Canonical (rightHead :: rightTail) →
        (Identity.mk
          (S5_107.listWordOfCons leftHead leftTail)
          (S5_107.listWordOfCons rightHead rightTail)).SatisfiedBy
            publishedTable.semigroup →
        ∀ x y,
          S5_841.CompletePrecedenceList
              (leftHead :: leftTail) x y ↔
            S5_841.CompletePrecedenceList
              (rightHead :: rightTail) x y) :
    BasisFor publishedTable.semigroup basis := by
  refine ⟨publishedModels, ?_⟩
  intro identity valid
  obtain ⟨leftNormal, leftCanonical, leftBound, leftCounts,
      leftReduction⟩ := normalize identity.lhs.toList
  obtain ⟨rightNormal, rightCanonical, rightBound, rightCounts,
      rightReduction⟩ := normalize identity.rhs.toList
  have leftNonempty : leftNormal ≠ [] :=
    listDerives_target_ne_nil_of_word leftReduction
  have rightNonempty : rightNormal ≠ [] :=
    listDerives_target_ne_nil_of_word rightReduction
  obtain ⟨leftHead, leftTail, rfl⟩ :=
    List.exists_cons_of_ne_nil leftNonempty
  obtain ⟨rightHead, rightTail, rfl⟩ :=
    List.exists_cons_of_ne_nil rightNonempty
  have originalCappedCounts := valid_cappedCount_eq identity valid
  have normalizedCounts : ∀ letter,
      (leftHead :: leftTail).count letter =
        (rightHead :: rightTail).count letter := by
    intro letter
    calc
      (leftHead :: leftTail).count letter =
          min (identity.lhs.toList.count letter) 3 :=
        leftCounts letter
      _ = min (identity.rhs.toList.count letter) 3 :=
        originalCappedCounts letter
      _ = (rightHead :: rightTail).count letter :=
        (rightCounts letter).symm
  have leftWordReduction :
      Derives basis identity.lhs
        (S5_107.listWordOfCons leftHead leftTail) :=
    derives_of_listDerives_toList
      identity.lhs (S5_107.listWordOfCons leftHead leftTail) <| by
        simpa [S5_107.listWordOfCons, Word.toList] using leftReduction
  have rightWordReduction :
      Derives basis identity.rhs
        (S5_107.listWordOfCons rightHead rightTail) :=
    derives_of_listDerives_toList
      identity.rhs (S5_107.listWordOfCons rightHead rightTail) <| by
        simpa [S5_107.listWordOfCons, Word.toList] using rightReduction
  have normalizedValid :
      (Identity.mk
        (S5_107.listWordOfCons leftHead leftTail)
        (S5_107.listWordOfCons rightHead rightTail)).SatisfiedBy
          publishedTable.semigroup := by
    intro valuation
    have leftSound :=
      leftWordReduction.sound publishedModels valuation
    have rightSound :=
      rightWordReduction.sound publishedModels valuation
    exact leftSound.symm.trans ((valid valuation).trans rightSound)
  have normalizedPrecedence : ∀ x y,
      S5_841.CompletePrecedenceList (leftHead :: leftTail) x y ↔
        S5_841.CompletePrecedenceList
          (rightHead :: rightTail) x y :=
    canonicalCompletePrecedence
      leftCanonical rightCanonical normalizedValid
  have middleSort :
      S5_107.ListDerives sortBasis
        (leftHead :: leftTail) (rightHead :: rightTail) :=
    listDerivesCanonicalPair
      (canonicalSimpleSplit leftCanonical)
      (canonicalSimpleSplit rightCanonical)
      leftBound rightBound normalizedCounts normalizedPrecedence
  have middle :
      S5_107.ListDerives basis
        (leftHead :: leftTail) (rightHead :: rightTail) :=
    liftSortListDerives middleSort
  have assembled :
      S5_107.ListDerives basis
        identity.lhs.toList identity.rhs.toList :=
    leftReduction.trans (middle.trans rightReduction.symm)
  exact derives_of_listDerives_toList
    identity.lhs identity.rhs assembled

end SemigroupBasis.CoRoots.Order6LeeLiProposition8A
