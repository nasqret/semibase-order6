import SemigroupBasis.CoRoots.Order6SporadicSection13Lemma13_3

namespace SemigroupBasis.CoRoots.Order6SporadicSection13

open SemigroupBasis

private def freshAbove : List Nat → Nat
  | [] => 0
  | selected :: rest => max (selected + 1) (freshAbove rest)

private theorem lt_freshAbove_of_mem
    (selected : Nat) :
    ∀ letters : List Nat,
      selected ∈ letters → selected < freshAbove letters
  | [], member => by
      simp at member
  | head :: rest, member => by
      rcases List.mem_cons.mp member with atHead | inRest
      · subst selected
        exact Nat.lt_of_lt_of_le (Nat.lt_succ_self head)
          (Nat.le_max_left (head + 1) (freshAbove rest))
      · exact Nat.lt_of_lt_of_le
          (lt_freshAbove_of_mem selected rest inRest)
          (Nat.le_max_right (head + 1) (freshAbove rest))

private def freshVariable (identity : Identity Nat) : Nat :=
  freshAbove (identity.lhs.toList ++ identity.rhs.toList)

private theorem freshVariable_not_mem_left
    (identity : Identity Nat) :
    freshVariable identity ∉ identity.lhs.toList := by
  intro member
  have impossible :=
    lt_freshAbove_of_mem (freshVariable identity)
      (identity.lhs.toList ++ identity.rhs.toList)
      (List.mem_append.mpr (Or.inl member))
  exact Nat.lt_irrefl _ impossible

private theorem freshVariable_not_mem_right
    (identity : Identity Nat) :
    freshVariable identity ∉ identity.rhs.toList := by
  intro member
  have impossible :=
    lt_freshAbove_of_mem (freshVariable identity)
      (identity.lhs.toList ++ identity.rhs.toList)
      (List.mem_append.mpr (Or.inr member))
  exact Nat.lt_irrefl _ impossible

/-- Kernel-checkable source inhabitant of the unrestricted completeness
interface for Proposition 13.1.  The two branches are the canonical
simple-final proof and Lemma 13.3 with an explicit fresh variable. -/
def joinCompleteness : JoinCompleteness where
  derives := by
    intro identity jValid oValid
    cases leftSimple : S5_345.simpleFinalVariable identity.lhs with
    | some final =>
        exact derives_of_factors_of_simpleFinal
          identity jValid oValid leftSimple
    | none =>
        exact derives_of_factors_of_nonsimpleFinal
          identity jValid oValid (freshVariable identity)
          (freshVariable_not_mem_left identity)
          (freshVariable_not_mem_right identity) leftSimple

namespace S6_10203

theorem publishedBasisFor : BasisFor publishedSemigroup basis :=
  publishedBasisFor_of_joinCompleteness joinCompleteness

theorem representativeBasisFor : BasisFor table.semigroup basis :=
  representativeBasisFor_of_joinCompleteness joinCompleteness

theorem representativeOppositeBasisFor :
    BasisFor table.semigroup.opposite oppositeBasis :=
  representativeOppositeBasisFor_of_joinCompleteness joinCompleteness

end S6_10203

namespace S6_10409

theorem publishedBasisFor : BasisFor publishedSemigroup basis :=
  publishedBasisFor_of_joinCompleteness joinCompleteness

theorem representativeBasisFor : BasisFor table.semigroup basis :=
  representativeBasisFor_of_joinCompleteness joinCompleteness

theorem representativeOppositeBasisFor :
    BasisFor table.semigroup.opposite oppositeBasis :=
  representativeOppositeBasisFor_of_joinCompleteness joinCompleteness

end S6_10409

namespace S6_10218

theorem publishedBasisFor : BasisFor publishedSemigroup basis :=
  publishedBasisFor_of_joinCompleteness joinCompleteness

theorem representativeBasisFor : BasisFor table.semigroup basis :=
  representativeBasisFor_of_joinCompleteness joinCompleteness

theorem representativeOppositeBasisFor :
    BasisFor table.semigroup.opposite oppositeBasis :=
  representativeOppositeBasisFor_of_joinCompleteness joinCompleteness

end S6_10218

namespace S6_10410

theorem publishedBasisFor : BasisFor publishedSemigroup basis :=
  publishedBasisFor_of_joinCompleteness joinCompleteness

theorem representativeBasisFor : BasisFor table.semigroup basis :=
  representativeBasisFor_of_joinCompleteness joinCompleteness

theorem representativeOppositeBasisFor :
    BasisFor table.semigroup.opposite oppositeBasis :=
  representativeOppositeBasisFor_of_joinCompleteness joinCompleteness

end S6_10410

namespace S6_10411

theorem publishedBasisFor : BasisFor publishedSemigroup basis :=
  publishedBasisFor_of_joinCompleteness joinCompleteness

theorem representativeBasisFor : BasisFor table.semigroup basis :=
  representativeBasisFor_of_joinCompleteness joinCompleteness

theorem representativeOppositeBasisFor :
    BasisFor table.semigroup.opposite oppositeBasis :=
  representativeOppositeBasisFor_of_joinCompleteness joinCompleteness

end S6_10411

namespace S6_9882

theorem publishedBasisFor : BasisFor publishedSemigroup basis :=
  publishedBasisFor_of_joinCompleteness joinCompleteness

theorem representativeBasisFor : BasisFor table.semigroup basis :=
  representativeBasisFor_of_joinCompleteness joinCompleteness

theorem representativeOppositeBasisFor :
    BasisFor table.semigroup.opposite oppositeBasis :=
  representativeOppositeBasisFor_of_joinCompleteness joinCompleteness

end S6_9882

namespace S6_8921

theorem publishedBasisFor : BasisFor publishedSemigroup basis :=
  publishedBasisFor_of_joinCompleteness joinCompleteness

theorem representativeBasisFor : BasisFor table.semigroup basis :=
  representativeBasisFor_of_joinCompleteness joinCompleteness

theorem representativeOppositeBasisFor :
    BasisFor table.semigroup.opposite oppositeBasis :=
  representativeOppositeBasisFor_of_joinCompleteness joinCompleteness

end S6_8921

namespace S6_9062

theorem publishedBasisFor : BasisFor publishedSemigroup basis :=
  publishedBasisFor_of_joinCompleteness joinCompleteness

theorem representativeBasisFor : BasisFor table.semigroup oppositeBasis :=
  representativeBasisFor_of_joinCompleteness joinCompleteness

theorem representativeOppositeBasisFor :
    BasisFor table.semigroup.opposite basis :=
  representativeOppositeBasisFor_of_joinCompleteness joinCompleteness

end S6_9062

end SemigroupBasis.CoRoots.Order6SporadicSection13
