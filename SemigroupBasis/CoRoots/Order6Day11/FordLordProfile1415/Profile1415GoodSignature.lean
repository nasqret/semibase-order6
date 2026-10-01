import SemigroupBasis.CoRoots.Order6Day11.FordLordProfile1415.Profile1415GoodNormalization

/-! On good words, the three factor theories imply the completed A16 key. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day11.FordLordProfile1415

open SemigroupBasis SemigroupBasis.Examples
open SemigroupBasis.CoRoots.S5_441Invariant
open SemigroupBasis.CoRoots.Order6Day11.FordLordProfile15 (cap22)
open SemigroupBasis.CoRoots.Order6Day11.FordLordProfile15.KeyTheory
  (SameKey postList postList_split)
open GoodWords

/-- Full first-occurrence order, together with the parity/separator theory. -/
structure SameSignature (left right : Word Nat) : Prop where
  lower : SameParitySeparatorSignature left right
  ford : firstOccurrenceSequence left.toList = firstOccurrenceSequence right.toList

namespace SameSignature

theorem refl (word : Word Nat) : SameSignature word word :=
  ⟨SameParitySeparatorSignature.refl word, rfl⟩

theorem symm {left right : Word Nat} (same : SameSignature left right) :
    SameSignature right left := ⟨same.lower.symm, same.ford.symm⟩

theorem trans {left middle right : Word Nat}
    (first : SameSignature left middle) (second : SameSignature middle right) :
    SameSignature left right :=
  ⟨first.lower.trans second.lower, first.ford.trans second.ford⟩

end SameSignature

theorem sameSignatureOfFactorValid (identity : Identity Nat)
    (cyclicValid : identity.SatisfiedBy cyclicTable.semigroup)
    (separatorValid : identity.SatisfiedBy separatorTable.semigroup)
    (initialValid : identity.SatisfiedBy initialTable.semigroup) :
    SameSignature identity.lhs identity.rhs := by
  refine ⟨⟨sameSupport_of_s4_69_equalEval _ _ separatorValid,
    sameExactCutSignature_of_s4_69_equalEval _ _ separatorValid,
    cyclicValid_parity_eq identity cyclicValid⟩, ?_⟩
  exact SemigroupBasis.CoRoots.Order6Day11.FordLordProfile15.KeyTheory.valid_ford
    identity initialValid

theorem derives_sameSignature {left right : Word Nat}
    (derivation : Derives basis left right) : SameSignature left right :=
  sameSignatureOfFactorValid ⟨left, right⟩ (derivation.sound cyclicModels)
    (derivation.sound separatorModels) (derivation.sound initialModels)

theorem good_simple_iff {left right : Word Nat}
    (leftGood : Good left.toList) (rightGood : Good right.toList)
    (same : SameParitySeparatorSignature left right) (marker : Nat) :
    left.toList.count marker = 1 ↔ right.toList.count marker = 1 := by
  constructor
  · intro simple
    obtain ⟨before, after, cut⟩ := leftGood marker simple
    obtain ⟨_, _, targetCut, _, _⟩ := same.exactCuts.transport cut
    exact targetCut.2.1
  · intro simple
    obtain ⟨before, after, cut⟩ := rightGood marker simple
    obtain ⟨_, _, targetCut, _, _⟩ := same.exactCuts.symm.transport cut
    exact targetCut.2.1

theorem cap22_eq_of_status {left right : Nat}
    (zero : left = 0 ↔ right = 0) (one : left = 1 ↔ right = 1)
    (parity : left % 2 = right % 2) : cap22 left = cap22 right := by
  unfold cap22
  split <;> split <;> omega

/-- No full Condition14 factor premise is used in the good-word reduction. -/
theorem sameKey_of_good {left right : Word Nat}
    (leftGood : Good left.toList) (rightGood : Good right.toList)
    (same : SameSignature left right) : SameKey left.toList right.toList := by
  refine ⟨same.ford, ?_, ?_⟩
  · intro letter
    have zero : left.toList.count letter = 0 ↔ right.toList.count letter = 0 := by
      rw [List.count_eq_zero, List.count_eq_zero]
      exact not_congr (same.lower.support letter)
    exact cap22_eq_of_status zero (good_simple_iff leftGood rightGood same.lower letter)
      (same.lower.parity letter)
  · intro marker selected simple
    obtain ⟨before, after, cut⟩ := leftGood marker simple
    obtain ⟨targetBefore, targetAfter, targetCut, _, sameAfter⟩ :=
      same.lower.exactCuts.transport cut
    have leftPost : postList left.toList marker = after := by
      rw [cut.1]
      exact postList_split marker before after (by simpa only [cut.1] using cut.2.1)
    have rightPost : postList right.toList marker = targetAfter := by
      rw [targetCut.1]
      exact postList_split marker targetBefore targetAfter
        (by simpa only [targetCut.1] using targetCut.2.1)
    rw [leftPost, rightPost]
    exact (sameAfter selected).symm

/-- Arbitrary words reduce to good words, whose keys are joined by A16. -/
theorem derivesOfSameSignature {left right : Word Nat}
    (same : SameSignature left right) : Derives basis left right := by
  obtain ⟨leftNormal, leftDerivation, leftGood⟩ := word_derives_good left
  obtain ⟨rightNormal, rightDerivation, rightGood⟩ := word_derives_good right
  have normalizedSame : SameSignature leftNormal rightNormal :=
    (derives_sameSignature leftDerivation).symm.trans
      (same.trans (derives_sameSignature rightDerivation))
  have joined : Derives basis leftNormal rightNormal :=
    derivesOfAKey leftNormal rightNormal (sameKey_of_good leftGood rightGood normalizedSame)
  exact leftDerivation.trans (joined.trans rightDerivation.symm)

theorem derives_iff_signature (left right : Word Nat) :
    Derives basis left right ↔ SameSignature left right :=
  ⟨derives_sameSignature, derivesOfSameSignature⟩

end SemigroupBasis.CoRoots.Order6Day11.FordLordProfile1415
