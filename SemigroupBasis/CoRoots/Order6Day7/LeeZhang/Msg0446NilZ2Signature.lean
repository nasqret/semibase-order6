import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0446NilZ2Presentation
import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0446TailBudget
import SemigroupBasis.CoRoots.S5_254Family

/-! The exact unrestricted semantic signature of S6_9386. M18 completeness is
used only INSIDE the M18 factor's identity theory. Its stronger power law is
not replayed into the seven-law target. The target's derivational converse is
exposed as `SignatureReach`, NOT inhabited. A separately verified finite
countermodel refutes that converse for this exact B7. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0446NilZ2

open SemigroupBasis

abbrev countCap := Msg0446TailBudget.cap 3

structure SameSignature (left right : Word Nat) : Prop where
  counts : ∀ letter, countCap (left.toList.count letter) = countCap (right.toList.count letter)
  prefixParity : S5_254.SamePrefixParityBeforeSimpleSeparators left right

namespace SameSignature

theorem cappedCounts {left right : Word Nat} (same : SameSignature left right) (letter : Nat) :
    min (left.toList.count letter) 3 = min (right.toList.count letter) 3 :=
  ((Msg0446TailBudget.cap_eq_iff _ _ _).1 (same.counts letter)).1

theorem totalParity {left right : Word Nat} (same : SameSignature left right) (letter : Nat) :
    left.toList.count letter % 2 = right.toList.count letter % 2 :=
  ((Msg0446TailBudget.cap_eq_iff _ _ _).1 (same.counts letter)).2

theorem toM18 {left right : Word Nat} (same : SameSignature left right) :
    S5_254.SameM18Signature left right where
  support := by
    intro letter
    have counts := same.cappedCounts letter
    constructor
    · intro member
      have positive := List.count_pos_iff.mpr member
      exact List.count_pos_iff.mp (by omega)
    · intro member
      have positive := List.count_pos_iff.mpr member
      exact List.count_pos_iff.mp (by omega)
  totalParity := same.totalParity
  globallySimple := by
    intro letter
    have counts := same.cappedCounts letter
    change left.toList.count letter = 1 ↔ right.toList.count letter = 1
    omega
  prefixParity := same.prefixParity

end SameSignature

/-- The existing commutative factor normalizer also gives sufficiency of the
capped coordinate counts. All words and variables here are unrestricted. -/
theorem exponentValid_of_cappedCounts (identity : Identity Nat)
    (counts : ∀ letter, min (identity.lhs.toList.count letter) 3 =
      min (identity.rhs.toList.count letter) 3) :
    identity.SatisfiedBy exponentTable.semigroup := by
  have leftNormal := Examples.exponentFourDerivesNormal identity.lhs
  have rightNormal := Examples.exponentFourDerivesNormal identity.rhs
  have permutation := Examples.capThreeReduce_perm_of_capped_count_eq counts
  cases leftShape : Examples.capThreeReduce identity.lhs.toList with
  | nil =>
      rw [leftShape] at leftNormal
      exact False.elim leftNormal
  | cons leftHead leftTail =>
      rw [leftShape] at leftNormal
      cases rightShape : Examples.capThreeReduce identity.rhs.toList with
      | nil =>
          rw [rightShape] at rightNormal
          exact False.elim rightNormal
      | cons rightHead rightTail =>
          rw [rightShape] at rightNormal
          rw [leftShape, rightShape] at permutation
          have middle := Examples.exponentFourDerivesPermutation
            (⟨leftHead, leftTail⟩ : Word Nat) (⟨rightHead, rightTail⟩ : Word Nat) permutation
          exact (leftNormal.trans (middle.trans rightNormal.symm)).sound
            Examples.commutativeExponentFourBasis_models

/-- Necessity of the exact counts-plus-simple-prefix-parity invariant. -/
theorem sameSignature_of_valid9386 (identity : Identity Nat)
    (valid : identity.SatisfiedBy table9386.semigroup) :
    SameSignature identity.lhs identity.rhs := by
  have factors := (valid9386_iff_factors identity).1 valid
  have m18Signature := S5_254.sameM18Signature_of_valid identity factors.1
  have cappedCounts := Examples.exponentFourValid_capped_count_eq identity factors.2
  exact ⟨fun letter => (Msg0446TailBudget.cap_eq_iff _ _ _).2
    ⟨cappedCounts letter, m18Signature.totalParity letter⟩, m18Signature.prefixParity⟩

/-- Semantic sufficiency via the two actual factors, not via bounded words. -/
theorem valid9386_of_sameSignature (identity : Identity Nat)
    (same : SameSignature identity.lhs identity.rhs) :
    identity.SatisfiedBy table9386.semigroup := by
  apply (valid9386_iff_factors identity).2
  exact ⟨(S5_254.derivesOfSameM18Signature same.toM18).sound S5_254.models,
    exponentValid_of_cappedCounts identity same.cappedCounts⟩

theorem valid9386_iff_signature (identity : Identity Nat) :
    identity.SatisfiedBy table9386.semigroup ↔ SameSignature identity.lhs identity.rhs :=
  ⟨sameSignature_of_valid9386 identity, valid9386_of_sameSignature identity⟩

theorem sevenLawDerives_preserve_signature {left right : Word Nat}
    (derivation : Derives basis left right) : SameSignature left right :=
  sameSignature_of_valid9386 ⟨left, right⟩ (derivation.sound models9386)

/-- The exact target basis, not M18's fifteen laws, would have to implement
this alignment. No inhabitant is defined; the separate countermodel refutes it. -/
def SignatureReach : Prop :=
  ∀ left right : Word Nat, SameSignature left right → Derives basis left right

/-- This iff exposes the remaining unrestricted obligation; it is not a basis proof. -/
theorem basisFor9386_iff_signatureReach : BasisFor table9386.semigroup basis ↔ SignatureReach := by
  constructor
  · intro complete left right same
    exact complete.2 ⟨left, right⟩ (valid9386_of_sameSignature ⟨left, right⟩ same)
  · intro reach
    exact ⟨models9386, fun identity valid => reach _ _ (sameSignature_of_valid9386 identity valid)⟩

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0446NilZ2
