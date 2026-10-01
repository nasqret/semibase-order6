import SemigroupBasis.Examples.LeeLNonfinite

namespace SemigroupBasis.Examples.LeeL

open SemigroupBasis

namespace SourceWords

/-- Two nonempty words have disjoint contents. -/
def Disjoint (left right : Word Nat) : Prop :=
  ∀ letter, letter ∈ left.toList → letter ∉ right.toList

theorem disjoint_symm {left right : Word Nat}
    (h : Disjoint left right) : Disjoint right left := by
  intro letter hright hleft
  exact h letter hleft hright

/-- A source word is disconnected when it has a cut into two nonempty,
content-disjoint semigroup words. -/
def Disconnected (word : Word Nat) : Prop :=
  ∃ left right : Word Nat,
    word = left ++ right ∧ Disjoint left right

/-- Zhang--Luo's connected words have length at least two and have no
content-disjoint nonempty cut. -/
def Connected (word : Word Nat) : Prop :=
  2 ≤ word.toList.length ∧ ¬Disconnected word

def ConnectedIdentity (identity : Identity Nat) : Prop :=
  Connected identity.lhs ∧ Connected identity.rhs

def SameContent (left right : Word Nat) : Prop :=
  ∀ letter, letter ∈ left.toList ↔ letter ∈ right.toList

def SimpleIn (letter : Nat) (word : Word Nat) : Prop :=
  word.toList.count letter = 1

def NonsimpleIn (letter : Nat) (word : Word Nat) : Prop :=
  letter ∈ word.toList ∧ word.toList.count letter ≠ 1

end SourceWords

/-- Lemma 1, content formulation. -/
theorem valid_identity_sameContent {identity : Identity Nat}
    (valid : identity.SatisfiedBy table.semigroup) :
    SourceWords.SameContent identity.lhs identity.rhs := by
  intro letter
  have absence := valid_identity_preserves_absence valid letter
  constructor
  · intro leftMember
    apply List.count_pos_iff.mp
    apply Nat.pos_of_ne_zero
    intro rightZero
    have leftZero := absence.mpr rightZero
    exact (List.count_eq_zero.mp leftZero) leftMember
  · intro rightMember
    apply List.count_pos_iff.mp
    apply Nat.pos_of_ne_zero
    intro leftZero
    have rightZero := absence.mp leftZero
    exact (List.count_eq_zero.mp rightZero) rightMember

end SemigroupBasis.Examples.LeeL
