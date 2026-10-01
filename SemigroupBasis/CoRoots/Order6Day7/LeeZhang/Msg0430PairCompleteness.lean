import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0430HeadAlignment
import SemigroupBasis.Examples.CommutativeExponentThree

/-! Unrestricted completeness of the approved corrected pair8.
The actual S3_6-opposite probe preserves a simple initial letter. The actual
S5_207 factor preserves capped counts. Distinct heads are therefore both
repeated and can be aligned by the proved move, after which the transported
fixed-head seed applies. Only then are C1 quotient/transport fields formed. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0430

open SemigroupBasis Examples

def initialProbe (tested letter : Nat) : Fin 3 := if letter = tested then 1 else 2

theorem initialProbe_fold (tested : Nat) (tail : List Nat) (value : Fin 3) :
    tail.foldl (fun current letter => pairLeft.semigroup.mul current (initialProbe tested letter)) value =
      if tested ∈ tail then 0 else value := by
  induction tail generalizing value with
  | nil => rfl
  | cons letter rest ih =>
      rw [List.foldl_cons, ih]
      by_cases equal : letter = tested
      · subst letter
        simp [initialProbe, Order6Subdirect.oppositeTable,
          Generated.S3_6.table, FiniteTable.semigroup, finalMarkerThreeMul]
      · simp [initialProbe, equal, Ne.symm equal, Order6Subdirect.oppositeTable,
          Generated.S3_6.table, FiniteTable.semigroup, finalMarkerThreeMul]

theorem eval_initialProbe (word : Word Nat) (tested : Nat) :
    pairLeft.semigroup.eval (initialProbe tested) word =
      if tested ∈ word.tail then 0 else initialProbe tested word.head :=
  initialProbe_fold tested word.tail (initialProbe tested word.head)

theorem initialProbe_one_iff (word : Word Nat) (tested : Nat) :
    pairLeft.semigroup.eval (initialProbe tested) word = (1 : Fin 3) ↔
      word.head = tested ∧ tested ∉ word.tail := by
  rw [eval_initialProbe]
  by_cases present : tested ∈ word.tail <;> by_cases equal : word.head = tested <;>
    simp [present, equal, initialProbe]

theorem pairLeft_simple_head_iff (identity : Identity Nat)
    (valid : identity.SatisfiedBy pairLeft.semigroup) (tested : Nat) :
    (identity.lhs.head = tested ∧ tested ∉ identity.lhs.tail) ↔
      (identity.rhs.head = tested ∧ tested ∉ identity.rhs.tail) := by
  have evaluated := valid (initialProbe tested)
  calc
    (identity.lhs.head = tested ∧ tested ∉ identity.lhs.tail) ↔
        pairLeft.semigroup.eval (initialProbe tested) identity.lhs = (1 : Fin 3) :=
      (initialProbe_one_iff identity.lhs tested).symm
    _ ↔ pairLeft.semigroup.eval (initialProbe tested) identity.rhs = (1 : Fin 3) := by rw [evaluated]
    _ ↔ (identity.rhs.head = tested ∧ tested ∉ identity.rhs.tail) :=
      initialProbe_one_iff identity.rhs tested

theorem repeated_head_of_different (identity : Identity Nat)
    (valid : identity.SatisfiedBy pairLeft.semigroup)
    (different : identity.lhs.head ≠ identity.rhs.head) :
    2 ≤ identity.lhs.toList.count identity.lhs.head := by
  apply Decidable.byContradiction
  intro small
  have zero : identity.lhs.tail.count identity.lhs.head = 0 := by
    simp only [Word.toList, List.count_cons_self] at small
    omega
  have forced := (pairLeft_simple_head_iff identity valid identity.lhs.head).mp
    ⟨rfl, List.count_eq_zero.mp zero⟩
  exact different forced.1.symm

def lowerCapMap (value : Fin 3) : Fin 5 := if value = 0 then 0 else if value = 1 then 2 else 4

def lowerCapEmbedding : Embedding commutativeExponentThree.semigroup rightTable.semigroup where
  toFun := lowerCapMap
  map_mul := by decide
  injective := by unfold Function.Injective; decide

theorem lower_capped_counts (identity : Identity Nat)
    (valid : identity.SatisfiedBy rightTable.semigroup) (letter : Nat) :
    min (identity.lhs.toList.count letter) 2 = min (identity.rhs.toList.count letter) 2 :=
  exponentValid_capped_count_eq identity (lowerCapEmbedding.pullback_identity identity valid) letter

/-- ALL nonempty words and ALL finite supports, not a bounded profile screen. -/
theorem pair_complete (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy pairLeft.semigroup)
    (rightValid : identity.SatisfiedBy rightTable.semigroup) :
    Derives pairBasis identity.lhs identity.rhs := by
  by_cases heads : identity.lhs.head = identity.rhs.head
  · exact pairFixedHeadRules.complete identity heads rightValid
  have leftRepeated := repeated_head_of_different identity leftValid heads
  have rightRepeated := repeated_head_of_different ⟨identity.rhs, identity.lhs⟩
    (fun valuation => (leftValid valuation).symm) (Ne.symm heads)
  have nextRepeated : 2 ≤ identity.rhs.toList.count identity.lhs.head := by
    have capped := lower_capped_counts identity rightValid identity.lhs.head
    omega
  obtain ⟨aligned, alignedHead, move⟩ :=
    retargetRepeatedHead identity.rhs identity.lhs.head rightRepeated nextRepeated
  have alignedValid : (Identity.mk identity.lhs aligned).SatisfiedBy rightTable.semigroup :=
    fun valuation => (rightValid valuation).trans (Derives.sound pairRightModels move valuation)
  exact (pairFixedHeadRules.complete ⟨identity.lhs, aligned⟩ alignedHead.symm alignedValid).trans move.symm

def pairIntersection : IntersectionBasis pairLeft.semigroup rightTable.semigroup pairBasis where
  leftModels := pairLeftModels
  rightModels := pairRightModels
  complete := pair_complete

noncomputable def pairQuotientNormalizer : IntersectionNormalizer pairLeft.semigroup rightTable.semigroup pairBasis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer pairIntersection

/-- The reviewed shared-engine interface is used only after actual completion. -/
noncomputable def pairNormalizer : IntersectionNormalizer pairLeft.semigroup rightTable.semigroup pairBasis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.transportNormalizer pairQuotientNormalizer
    (fun _ member => Derives.fromBasis member) (fun _ valid => valid) (fun _ valid => valid)

theorem pair2683_representative_basis : BasisFor table2683.semigroup pairBasis :=
  pairNormalizer.basisFor pairLeftModels pairRightModels subdirect2683
theorem pair2706_representative_basis : BasisFor table2706.semigroup pairBasis :=
  pairNormalizer.basisFor pairLeftModels pairRightModels subdirect2706
theorem pair2683_opposite_basis : BasisFor table2683.semigroup.opposite (reversedBasis pairBasis) :=
  pair2683_representative_basis.oppositeReversed
theorem pair2706_opposite_basis : BasisFor table2706.semigroup.opposite (reversedBasis pairBasis) :=
  pair2706_representative_basis.oppositeReversed

theorem pair2683_complete (identity : Identity Nat) (valid : identity.SatisfiedBy table2683.semigroup) :
    Derives pairBasis identity.lhs identity.rhs := pair2683_representative_basis.2 identity valid
theorem pair2706_complete (identity : Identity Nat) (valid : identity.SatisfiedBy table2706.semigroup) :
    Derives pairBasis identity.lhs identity.rhs := pair2706_representative_basis.2 identity valid
theorem pair2683_opposite_complete (identity : Identity Nat) (valid : identity.SatisfiedBy table2683.semigroup.opposite) :
    Derives (reversedBasis pairBasis) identity.lhs identity.rhs := pair2683_opposite_basis.2 identity valid
theorem pair2706_opposite_complete (identity : Identity Nat) (valid : identity.SatisfiedBy table2706.semigroup.opposite) :
    Derives (reversedBasis pairBasis) identity.lhs identity.rhs := pair2706_opposite_basis.2 identity valid

def pairOppositeIntersection :
    IntersectionBasis pairLeft.semigroup.opposite rightTable.semigroup.opposite (reversedBasis pairBasis) :=
  pairIntersection.oppositeReversed

noncomputable def pairOppositeNormalizer :
    IntersectionNormalizer pairLeft.semigroup.opposite rightTable.semigroup.opposite (reversedBasis pairBasis) :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer pairOppositeIntersection

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0430
