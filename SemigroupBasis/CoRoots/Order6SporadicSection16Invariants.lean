import SemigroupBasis.CoRoots.Order6SporadicSection16FactorInvariants
import SemigroupBasis.CoRoots.SimplePairExclusion

/-! Lee-Zhang2015 Lemma16.2 in full. Parts(i)-(iii) use the exact
subsemigroups and Rees quotients. Part(iv) uses the actual padded
substitution of Lemma2.10 and the table's checked failure of(2.3).
No table-specific detector law, normalization field or completeness
assumption replaces that argument. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection16

open SemigroupBasis
open SimplePairExclusion

theorem fssIdentity_of_scalarExclusion {S : Type u} (G : Semigroup S)
    (forced : ∀ x a b, separatedValue G (G.mul x x) a b = adjacentValue G (G.mul x x) a b) :
    fssExclusionIdentity.SatisfiedBy G := by
  intro valuation
  simpa only [fssExclusionIdentity, Semigroup.eval, List.foldl_cons, List.foldl_nil,
    separatedValue, adjacentValue, G.assoc] using forced (valuation 0) (valuation 1) (valuation 2)

theorem valid_directed_simple_pair {S : Type u} (G : Semigroup S)
    (squares : ∀ a, G.mul (G.mul a a) (G.mul a a) = G.mul a a)
    (exclusion : ¬ fssExclusionIdentity.SatisfiedBy G)
    (identity : Identity Nat) (valid : identity.SatisfiedBy G)
    (source target : Nat) (different : source ≠ target)
    (leftSource : identity.lhs.toList.count source = 1)
    (leftTarget : identity.lhs.toList.count target = 1)
    (rightSource : identity.rhs.toList.count source = 1)
    (rightTarget : identity.rhs.toList.count target = 1) :
    (source,target) ∈ identity.lhs.adjacentPairs ↔ (source,target) ∈ identity.rhs.adjacentPairs := by
  constructor
  · intro adjacent
    apply Decidable.byContradiction
    intro missing
    apply exclusion
    exact fssIdentity_of_scalarExclusion G
      (exclusion_of_adjacency_loss G squares identity valid source target different
        leftSource leftTarget rightSource rightTarget adjacent missing)
  · intro adjacent
    apply Decidable.byContradiction
    intro missing
    apply exclusion
    exact fssIdentity_of_scalarExclusion G
      (exclusion_of_adjacency_loss G squares ⟨identity.rhs,identity.lhs⟩ (fun v => (valid v).symm)
        source target different rightSource rightTarget leftSource leftTarget adjacent missing)

theorem simple_pair_different (word : Word Nat) (source target : Nat)
    (sourceSimple : word.toList.count source = 1)
    (edge : (source,target) ∈ word.adjacentPairs) : source ≠ target := by
  intro equal
  subst target
  obtain ⟨before,after,split⟩ := (mem_adjacentPairs_iff_exists_split source source word).mp edge
  rw [split] at sourceSimple
  simp only [List.count_append, List.count_cons_self] at sourceSimple
  omega

theorem fss_of_exclusion {S : Type u} (G : Semigroup S)
    (squares : ∀ a, G.mul (G.mul a a) (G.mul a a) = G.mul a a)
    (exclusion : ¬ fssExclusionIdentity.SatisfiedBy G)
    (identity : Identity Nat) (valid : identity.SatisfiedBy G)
    (factors : FactorInvariants identity.lhs identity.rhs) :
    ∀ source target, S5_107.SimpleAdjacent identity.lhs source target ↔
      S5_107.SimpleAdjacent identity.rhs source target := by
  intro source target
  constructor
  · rintro ⟨leftSource,leftTarget,edge⟩
    have rightSource := (factors.simple source).mp leftSource
    have rightTarget := (factors.simple target).mp leftTarget
    have different := simple_pair_different identity.lhs source target leftSource edge
    exact ⟨rightSource,rightTarget,(valid_directed_simple_pair G squares exclusion identity valid
      source target different leftSource leftTarget rightSource rightTarget).mp edge⟩
  · rintro ⟨rightSource,rightTarget,edge⟩
    have leftSource := (factors.simple source).mpr rightSource
    have leftTarget := (factors.simple target).mpr rightTarget
    have different := simple_pair_different identity.rhs source target rightSource edge
    exact ⟨leftSource,leftTarget,(valid_directed_simple_pair G squares exclusion identity valid
      source target different leftSource leftTarget rightSource rightTarget).mpr edge⟩

structure Lemma16_2Invariants (left right : Word Nat) extends FactorInvariants left right : Prop where
  fss : ∀ source target, S5_107.SimpleAdjacent left source target ↔ S5_107.SimpleAdjacent right source target

namespace S6_3813
theorem lemma16_2 (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    Lemma16_2Invariants identity.lhs identity.rhs where
  toFactorInvariants := lemma16_2_i_iii identity valid
  fss := fss_of_exclusion table.semigroup squares_idempotent not_fssExclusion identity valid
    (lemma16_2_i_iii identity valid)
end S6_3813
namespace S6_3815
theorem lemma16_2 (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    Lemma16_2Invariants identity.lhs identity.rhs where
  toFactorInvariants := lemma16_2_i_iii identity valid
  fss := fss_of_exclusion table.semigroup squares_idempotent not_fssExclusion identity valid
    (lemma16_2_i_iii identity valid)
end S6_3815
namespace S6_3826
theorem lemma16_2 (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    Lemma16_2Invariants identity.lhs identity.rhs where
  toFactorInvariants := lemma16_2_i_iii identity valid
  fss := fss_of_exclusion table.semigroup squares_idempotent not_fssExclusion identity valid
    (lemma16_2_i_iii identity valid)
end S6_3826
namespace S6_3828
theorem lemma16_2 (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    Lemma16_2Invariants identity.lhs identity.rhs where
  toFactorInvariants := lemma16_2_i_iii identity valid
  fss := fss_of_exclusion table.semigroup squares_idempotent not_fssExclusion identity valid
    (lemma16_2_i_iii identity valid)
end S6_3828
namespace S6_6437
theorem lemma16_2 (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    Lemma16_2Invariants identity.lhs identity.rhs where
  toFactorInvariants := lemma16_2_i_iii identity valid
  fss := fss_of_exclusion table.semigroup squares_idempotent not_fssExclusion identity valid
    (lemma16_2_i_iii identity valid)
end S6_6437
namespace S6_6444
theorem lemma16_2 (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    Lemma16_2Invariants identity.lhs identity.rhs where
  toFactorInvariants := lemma16_2_i_iii identity valid
  fss := fss_of_exclusion table.semigroup squares_idempotent not_fssExclusion identity valid
    (lemma16_2_i_iii identity valid)
end S6_6444

#print axioms valid_directed_simple_pair
#print axioms simple_pair_different
#print axioms fss_of_exclusion
#print axioms S6_3813.lemma16_2
#print axioms S6_3815.lemma16_2
#print axioms S6_3826.lemma16_2
#print axioms S6_3828.lemma16_2
#print axioms S6_6437.lemma16_2
#print axioms S6_6444.lemma16_2

end SemigroupBasis.CoRoots.Order6SporadicSection16
