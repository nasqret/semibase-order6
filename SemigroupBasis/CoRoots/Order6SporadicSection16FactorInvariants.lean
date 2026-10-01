import SemigroupBasis.CoRoots.Order6SporadicSection16Divisors

/-!
Lee-Zhang2015 Lemma16.2(i)-(iii), through its exact stated divisors.
The established factor semantics prove the unrestricted word statements.
This module does not assume FSS necessity or class completeness.
-/

namespace SemigroupBasis.CoRoots.Order6SporadicSection16

open SemigroupBasis SemigroupBasis.Examples

structure FactorInvariants (left right : Word Nat) : Prop where
  ini : firstOccurrenceSequence left.toList = firstOccurrenceSequence right.toList
  capped : ∀ letter, min (left.toList.count letter) 2 = min (right.toList.count letter) 2
  simpleFinal : ∀ letter, S5_107.SimpleFinal left letter ↔ S5_107.SimpleFinal right letter

theorem factorInvariants_of_divisor_validity (identity : Identity Nat)
    (iniValid : identity.SatisfiedBy leftRegularBandThree.semigroup)
    (countValid : identity.SatisfiedBy commutativeExponentThree.semigroup)
    (finalValid : identity.SatisfiedBy finalMarkerThree.semigroup) :
    FactorInvariants identity.lhs identity.rhs where
  ini := S5_345Factors.leftRegularBandThreeValid_firstOccurrenceSequence_eq identity iniValid
  capped := exponentValid_capped_count_eq identity countValid
  simpleFinal := S5_345Factors.finalMarkerThreeValid_simpleFinal_iff identity finalValid

namespace FactorInvariants

theorem simple {left right : Word Nat} (same : FactorInvariants left right) (letter : Nat) :
    left.toList.count letter = 1 ↔ right.toList.count letter = 1 := by
  have capped := same.capped letter
  omega

theorem content {left right : Word Nat} (same : FactorInvariants left right) (letter : Nat) :
    letter ∈ left.toList ↔ letter ∈ right.toList := by
  rw [← List.count_pos_iff, ← List.count_pos_iff]
  have capped := same.capped letter
  omega

theorem simpleTail {left right : Word Nat} (same : FactorInvariants left right) :
    left.toList.count left.final = 1 ↔ right.toList.count right.final = 1 := by
  constructor
  · intro h
    have transferred := (same.simpleFinal left.final).mp ⟨h, rfl⟩
    simpa only [transferred.2] using transferred.1
  · intro h
    have transferred := (same.simpleFinal right.final).mpr ⟨h, rfl⟩
    simpa only [transferred.2] using transferred.1

end FactorInvariants

namespace S6_3813
theorem lemma16_2_i_iii (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    FactorInvariants identity.lhs identity.rhs :=
  factorInvariants_of_divisor_validity identity (valid_ini identity valid)
    (valid_count identity valid) (valid_final identity valid)
end S6_3813

namespace S6_3815
theorem lemma16_2_i_iii (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    FactorInvariants identity.lhs identity.rhs :=
  factorInvariants_of_divisor_validity identity (valid_ini identity valid)
    (valid_count identity valid) (valid_final identity valid)
end S6_3815

namespace S6_3826
theorem lemma16_2_i_iii (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    FactorInvariants identity.lhs identity.rhs :=
  factorInvariants_of_divisor_validity identity (valid_ini identity valid)
    (valid_count identity valid) (valid_final identity valid)
end S6_3826

namespace S6_3828
theorem lemma16_2_i_iii (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    FactorInvariants identity.lhs identity.rhs :=
  factorInvariants_of_divisor_validity identity (valid_ini identity valid)
    (valid_count identity valid) (valid_final identity valid)
end S6_3828

namespace S6_6437
theorem lemma16_2_i_iii (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    FactorInvariants identity.lhs identity.rhs :=
  factorInvariants_of_divisor_validity identity (valid_ini identity valid)
    (valid_count identity valid) (valid_final identity valid)
end S6_6437

namespace S6_6444
theorem lemma16_2_i_iii (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    FactorInvariants identity.lhs identity.rhs :=
  factorInvariants_of_divisor_validity identity (valid_ini identity valid)
    (valid_count identity valid) (valid_final identity valid)
end S6_6444

#print axioms factorInvariants_of_divisor_validity
#print axioms FactorInvariants.content
#print axioms FactorInvariants.simple
#print axioms FactorInvariants.simpleTail
#print axioms S6_3813.lemma16_2_i_iii
#print axioms S6_3815.lemma16_2_i_iii
#print axioms S6_3826.lemma16_2_i_iii
#print axioms S6_3828.lemma16_2_i_iii
#print axioms S6_6437.lemma16_2_i_iii
#print axioms S6_6444.lemma16_2_i_iii

end SemigroupBasis.CoRoots.Order6SporadicSection16
