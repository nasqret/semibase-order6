import SemigroupBasis.FiniteTable

namespace SemigroupBasis.CoRoots.S5_85

open SemigroupBasis

def xx : Word Nat := ⟨0, [0]⟩
def xxx : Word Nat := ⟨0, [0, 0]⟩
def xxy : Word Nat := ⟨0, [0, 1]⟩
def xyx : Word Nat := ⟨0, [1, 0]⟩
def xyz : Word Nat := ⟨0, [1, 2]⟩

def powerLaw : Identity Nat := ⟨xx, xxx⟩
def squareSuffixLaw : Identity Nat := ⟨xx, xxy⟩
def squareMiddleLaw : Identity Nat := ⟨xx, xyx⟩
def firstSquareLaw : Identity Nat := ⟨xx, xyz⟩

/-- The recorded four-identity basis of the `S5_85` family. -/
def basis : List (Identity Nat) :=
  [powerLaw, squareSuffixLaw, squareMiddleLaw, firstSquareLaw]

def wordOfCons (x : Nat) (xs : List Nat) : Word Nat :=
  ⟨x, xs⟩

private def instantiateThreeWords
    (u v w : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => w
  | n + 3 => Word.singleton (n + 3)

/-- The last recorded law already makes the square of any nonempty block
equal to any three-block word beginning with that block. -/
theorem derivesFirstSquareExpansion (u v w : Word Nat) :
    Derives basis (u ++ u) ((u ++ v) ++ w) := by
  have base : Derives basis xx xyz :=
    Derives.fromBasis (e := firstSquareLaw) <| by
      simp [basis]
  have instantiated := Derives.subst base (instantiateThreeWords u v w)
  simpa [basis, firstSquareLaw, xx, xyz, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      instantiated

/-- Every word of length at least three is derivably equal to the square of
its first letter. -/
theorem derivesLongToHeadSquare
    (x y z : Nat) (zs : List Nat) :
    Derives basis
      (wordOfCons x (y :: z :: zs)) (wordOfCons x [x]) := by
  have expansion :=
    derivesFirstSquareExpansion
      (Word.singleton x) (Word.singleton y) (wordOfCons z zs)
  exact Derives.symm <| by
    simpa [wordOfCons, Word.singleton, Word.append, Word.append_assoc] using
      expansion

private theorem word_length_positive (w : Word Nat) :
    1 ≤ w.toList.length := by
  cases w
  simp [Word.toList]

theorem derivesLongToSquare (w : Word Nat)
    (long : 3 ≤ w.toList.length) :
    Derives basis w (wordOfCons w.head [w.head]) := by
  cases w with
  | mk head tail =>
      cases tail with
      | nil =>
          simp [Word.toList] at long
      | cons next rest =>
          cases rest with
          | nil =>
              simp [Word.toList] at long
          | cons third more =>
              exact derivesLongToHeadSquare head next third more

private theorem pair_of_length_two
    (w : Word Nat) (lengthTwo : w.toList.length = 2) :
    ∃ a b, w = wordOfCons a [b] := by
  cases w with
  | mk head tail =>
      cases tail with
      | nil =>
          simp [Word.toList] at lengthTwo
      | cons next rest =>
          cases rest with
          | nil =>
              exact ⟨head, next, rfl⟩
          | cons third more =>
              simp [Word.toList] at lengthTwo

private theorem lengthOne_eq_of_head
    (u v : Word Nat)
    (uOne : u.toList.length = 1)
    (vOne : v.toList.length = 1)
    (heads : u.head = v.head) :
    u = v := by
  cases u with
  | mk uHead uTail =>
      cases uTail with
      | nil =>
          cases v with
          | mk vHead vTail =>
              cases vTail with
              | nil =>
                  simp only at heads
                  subst vHead
                  rfl
              | cons vNext vRest =>
                  simp [Word.toList] at vOne
      | cons uNext uRest =>
          simp [Word.toList] at uOne

/-- Generic unrestricted completeness for the first-square basis. A finite
table must model the laws, recover the first letter and singleton stratum,
separate ordered quadratic words coordinatewise, and keep a distinct
quadratic word apart from every long word. -/
theorem basis_complete_of_separates
    (T : FiniteTable)
    (modelsT : Models T.semigroup basis)
    (headT :
      ∀ e : Identity Nat, e.SatisfiedBy T.semigroup →
        e.lhs.head = e.rhs.head)
    (lengthOneT :
      ∀ e : Identity Nat, e.SatisfiedBy T.semigroup →
        (e.lhs.toList.length = 1 ↔ e.rhs.toList.length = 1))
    (pairT :
      ∀ {a b c d : Nat},
        (Identity.mk
          (wordOfCons a [b]) (wordOfCons c [d])).SatisfiedBy T.semigroup →
        a = c ∧ b = d)
    (distinctPairLongT :
      ∀ {a b : Nat}, a ≠ b → ∀ v : Word Nat,
        3 ≤ v.toList.length →
        ¬ (Identity.mk (wordOfCons a [b]) v).SatisfiedBy T.semigroup) :
    BasisFor T.semigroup basis := by
  refine ⟨modelsT, ?_⟩
  intro e valid
  have heads := headT e valid
  by_cases lhsOne : e.lhs.toList.length = 1
  · have rhsOne := (lengthOneT e valid).mp lhsOne
    have equal :=
      lengthOne_eq_of_head e.lhs e.rhs lhsOne rhsOne heads
    rw [equal]
    exact Derives.refl _
  · have rhsNotOne : e.rhs.toList.length ≠ 1 := by
      intro rhsOne
      exact lhsOne ((lengthOneT e valid).mpr rhsOne)
    by_cases lhsTwo : e.lhs.toList.length = 2
    · obtain ⟨a, b, lhsEq⟩ := pair_of_length_two e.lhs lhsTwo
      by_cases rhsTwo : e.rhs.toList.length = 2
      · obtain ⟨c, d, rhsEq⟩ := pair_of_length_two e.rhs rhsTwo
        have coordinates :=
          pairT (a := a) (b := b) (c := c) (d := d) <| by
            intro valuation
            simpa [lhsEq, rhsEq] using valid valuation
        rcases coordinates with ⟨rfl, rfl⟩
        rw [lhsEq, rhsEq]
        exact Derives.refl _
      · have rhsLong : 3 ≤ e.rhs.toList.length := by
          have positive := word_length_positive e.rhs
          omega
        rw [lhsEq]
        by_cases ab : a = b
        · subst b
          have rhsHead : e.rhs.head = a := by
            simpa [lhsEq, wordOfCons] using heads.symm
          have normalize := derivesLongToSquare e.rhs rhsLong
          exact by
            simpa [wordOfCons, rhsHead] using Derives.symm normalize
        · have pairLongValid :
              (Identity.mk (wordOfCons a [b]) e.rhs).SatisfiedBy
                T.semigroup := by
            intro valuation
            simpa [lhsEq] using valid valuation
          exact False.elim <|
            distinctPairLongT ab e.rhs rhsLong pairLongValid
    · have lhsLong : 3 ≤ e.lhs.toList.length := by
        have positive := word_length_positive e.lhs
        omega
      by_cases rhsTwo : e.rhs.toList.length = 2
      · obtain ⟨c, d, rhsEq⟩ := pair_of_length_two e.rhs rhsTwo
        rw [rhsEq]
        by_cases cd : c = d
        · subst d
          have lhsHead : e.lhs.head = c := by
            simpa [rhsEq, wordOfCons] using heads
          have normalize := derivesLongToSquare e.lhs lhsLong
          simpa [wordOfCons, lhsHead] using normalize
        · have pairLongValid :
              (Identity.mk (wordOfCons c [d]) e.lhs).SatisfiedBy
                T.semigroup := by
            intro valuation
            simpa [rhsEq] using (valid valuation).symm
          exact False.elim <|
            distinctPairLongT cd e.lhs lhsLong pairLongValid
      · have rhsLong : 3 ≤ e.rhs.toList.length := by
          have positive := word_length_positive e.rhs
          omega
        have lhsNormalize := derivesLongToSquare e.lhs lhsLong
        have rhsNormalize := derivesLongToSquare e.rhs rhsLong
        exact Derives.trans lhsNormalize <| by
          simpa [wordOfCons, heads] using Derives.symm rhsNormalize

end SemigroupBasis.CoRoots.S5_85
