import SemigroupBasis.CoRoots.Order6Day10.Rank084SigmaPlus.Rank084SigmaPlusSemantics
import SemigroupBasis.Subdirect

/-! The approved unrestricted B7 converse. The two actual factors determine
length category, literal first two letters, and short-word support. The
exhaustive short/long split uses only the explicitly proved B7 derivations. -/

namespace SemigroupBasis.CoRoots.Order6Day10.Rank084SigmaPlus.Rank084SigmaPlusIntersection

open SemigroupBasis
open SemigroupBasis.CoRoots.Order6Day10.Rank084SigmaPlus.Rank084SigmaPlusMacros
open SemigroupBasis.CoRoots.Order6Day10.Rank084SigmaPlus.Rank084SigmaPlusSemantics

abbrev basis := Rank084SigmaPlusMacros.basis
abbrev B7 := basis
abbrev leftTable := Rank084SigmaPlusMacros.leftTable
abbrev rightTable := Rank084SigmaPlusMacros.rightTable

theorem tripleToInitial (a b c : Nat) (old : c = a ∨ c = b) :
    Derives basis (Word.mk a [b, c]) (Word.mk a [b, a]) := by
  rcases old with first | second
  · subst c
    exact Derives.refl _
  · subst c
    simpa [Word.singleton, Word.append] using (rawLaw03 (Word.singleton a) (Word.singleton b)).symm

theorem triplesSameSupport (a b c d : Nat)
    (support : SameSupport (Word.mk a [b, c]) (Word.mk a [b, d])) :
    Derives basis (Word.mk a [b, c]) (Word.mk a [b, d]) := by
  by_cases old : c = a ∨ c = b
  · have inLeft : d = a ∨ d = b ∨ d = c := by
      simpa [Word.toList] using (support d).mpr (by simp [Word.toList])
    have rightOld : d = a ∨ d = b := by
      rcases inLeft with first | second | third
      · exact Or.inl first
      · exact Or.inr second
      · rcases old with first | second
        · exact Or.inl (third.trans first)
        · exact Or.inr (third.trans second)
    exact (tripleToInitial a b c old).trans (tripleToInitial a b d rightOld).symm
  · have inRight : c = a ∨ c = b ∨ c = d := by
      simpa [Word.toList] using (support c).mp (by simp [Word.toList])
    rcases inRight with first | second | same
    · exact False.elim (old (Or.inl first))
    · exact False.elim (old (Or.inr second))
    · subst d
      exact Derives.refl _

theorem derivesOfData (left right : Word Nat)
    (lengths : lengthClass left = lengthClass right)
    (prefixEq : FirstTwo left = FirstTwo right)
    (tripleSupport : lengthClass left = .triple → SameSupport left right) :
    Derives basis left right := by
  rcases left with ⟨a, leftTail⟩
  rcases right with ⟨b, rightTail⟩
  cases leftTail with
  | nil =>
      cases rightTail with
      | nil =>
          have heads : a = b := by simpa [FirstTwo, Word.toList] using prefixEq
          subst b
          exact Derives.refl _
      | cons rightSecond rightRest => simp [FirstTwo, Word.toList] at prefixEq
  | cons leftSecond leftRest =>
      cases rightTail with
      | nil => simp [FirstTwo, Word.toList] at prefixEq
      | cons rightSecond rightRest =>
          have coordinates : a = b ∧ leftSecond = rightSecond := by
            simpa [FirstTwo, Word.toList] using prefixEq
          rcases coordinates with ⟨heads, seconds⟩
          subst b
          subst rightSecond
          cases leftRest with
          | nil =>
              cases rightRest with
              | nil => exact Derives.refl _
              | cons rightThird rightMore => cases rightMore <;> simp [lengthClass] at lengths
          | cons leftThird leftMore =>
              cases rightRest with
              | nil => cases leftMore <;> simp [lengthClass] at lengths
              | cons rightThird rightMore =>
                  cases leftMore with
                  | nil =>
                      cases rightMore with
                      | nil => exact triplesSameSupport a leftSecond leftThird rightThird (tripleSupport rfl)
                      | cons rightFourth rightFinal => simp [lengthClass] at lengths
                  | cons leftFourth leftFinal =>
                      cases rightMore with
                      | nil => simp [lengthClass] at lengths
                      | cons rightFourth rightFinal =>
                          exact (derivesLongWord a leftSecond leftThird leftFourth leftFinal).trans
                            (derivesLongWord a leftSecond rightThird rightFourth rightFinal).symm

/-- Exactly the fable0413-approved unbounded statement on the actual factors. -/
theorem valid_in_both_derives (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy Generated.S4_11.table.semigroup)
    (rightValid : identity.SatisfiedBy Generated.S4_77.table.semigroup) :
    Derives B7 identity.lhs identity.rhs := by
  apply derivesOfData identity.lhs identity.rhs
    (cyclicValid_lengthClass identity leftValid) (rightFirstTwo identity rightValid)
  intro triple
  exact cyclicShort_support identity leftValid (by rw [triple]; decide)

def Complete : Prop :=
  ∀ identity : Identity Nat, identity.SatisfiedBy leftTable.semigroup →
    identity.SatisfiedBy rightTable.semigroup → Derives basis identity.lhs identity.rhs

theorem complete : Complete := valid_in_both_derives

theorem derives_iff_joint_valid (identity : Identity Nat) :
    Derives basis identity.lhs identity.rhs ↔
      identity.SatisfiedBy leftTable.semigroup ∧ identity.SatisfiedBy rightTable.semigroup := by
  constructor
  · intro derived
    exact ⟨fun valuation => derived.sound modelsLeft valuation, fun valuation => derived.sound modelsRight valuation⟩
  · intro valid
    exact valid_in_both_derives identity valid.1 valid.2

def intersectionBasis : IntersectionBasis leftTable.semigroup rightTable.semigroup basis where
  leftModels := modelsLeft
  rightModels := modelsRight
  complete := valid_in_both_derives

abbrev FinitePair (target : FiniteTable) := SubdirectPair target.semigroup leftTable.semigroup rightTable.semigroup

theorem basisForOfFinitePair (target : FiniteTable) (pair : FinitePair target) :
    BasisFor target.semigroup basis := intersectionBasis.basisFor pair

theorem basisForOppositeOfFinitePair (target : FiniteTable)
    (pair : SubdirectPair target.semigroup.opposite leftTable.semigroup.opposite rightTable.semigroup.opposite) :
    BasisFor target.semigroup.opposite (reversedBasis basis) := intersectionBasis.oppositeReversed.basisFor pair

end SemigroupBasis.CoRoots.Order6Day10.Rank084SigmaPlus.Rank084SigmaPlusIntersection
