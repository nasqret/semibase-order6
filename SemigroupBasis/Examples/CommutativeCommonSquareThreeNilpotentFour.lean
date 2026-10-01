import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite

namespace SemigroupBasis.Examples

open SemigroupBasis

/-- The exact zero-based form of the catalogue table
`[[1,1,1,1],[1,1,1,1],[1,1,1,2],[1,1,2,1]]`. -/
def commutativeCommonSquareThreeNilpotentFourMul
    (a b : Fin 4) : Fin 4 :=
  if (a = 2 ∧ b = 3) ∨ (a = 3 ∧ b = 2) then 1 else 0

/-- The commutative four-element three-nilpotent semigroup representing
`S4_3`. -/
def commutativeCommonSquareThreeNilpotentFour : FiniteTable where
  order := 4
  mul := commutativeCommonSquareThreeNilpotentFourMul
  assoc := by decide

def commutativeCommonSquareXX : Word Nat := ⟨0, [0]⟩
def commutativeCommonSquareYY : Word Nat := ⟨1, [1]⟩
def commutativeCommonSquareXYZ : Word Nat := ⟨0, [1, 2]⟩
def commutativeCommonSquareXY : Word Nat := ⟨0, [1]⟩
def commutativeCommonSquareYX : Word Nat := ⟨1, [0]⟩

def commutativeCommonSquareLaw : Identity Nat :=
  ⟨commutativeCommonSquareXX, commutativeCommonSquareYY⟩

def commutativeCommonSquareLongLaw : Identity Nat :=
  ⟨commutativeCommonSquareXX, commutativeCommonSquareXYZ⟩

def commutativeCommonSquareCommutativityLaw : Identity Nat :=
  ⟨commutativeCommonSquareXY, commutativeCommonSquareYX⟩

/-- The exact basis `xx = yy`, `xx = xyz`, `xy = yx`. -/
def commutativeCommonSquareThreeNilpotentBasis :
    List (Identity Nat) :=
  [commutativeCommonSquareLaw,
    commutativeCommonSquareLongLaw,
    commutativeCommonSquareCommutativityLaw]

private def instantiateTwoWords (u v : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | n + 2 => Word.singleton (n + 2)

private def instantiateThreeWords
    (u v w : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => w
  | n + 3 => Word.singleton (n + 3)

theorem commutativeCommonSquareDerivesSquares
    (u v : Word Nat) :
    Derives commutativeCommonSquareThreeNilpotentBasis
      (u ++ u) (v ++ v) := by
  have hbase :
      Derives commutativeCommonSquareThreeNilpotentBasis
        commutativeCommonSquareXX commutativeCommonSquareYY :=
    Derives.fromBasis (e := commutativeCommonSquareLaw) (by
      simp [commutativeCommonSquareThreeNilpotentBasis])
  have h := Derives.subst hbase (instantiateTwoWords u v)
  simpa [commutativeCommonSquareLaw, commutativeCommonSquareXX,
    commutativeCommonSquareYY, instantiateTwoWords, Word.bind,
    Word.append, Word.singleton] using h

theorem commutativeCommonSquareDerivesLongProduct
    (u v w : Word Nat) :
    Derives commutativeCommonSquareThreeNilpotentBasis
      (u ++ u) ((u ++ v) ++ w) := by
  have hbase :
      Derives commutativeCommonSquareThreeNilpotentBasis
        commutativeCommonSquareXX commutativeCommonSquareXYZ :=
    Derives.fromBasis (e := commutativeCommonSquareLongLaw) (by
      simp [commutativeCommonSquareThreeNilpotentBasis])
  have h := Derives.subst hbase (instantiateThreeWords u v w)
  simpa [commutativeCommonSquareLongLaw, commutativeCommonSquareXX,
    commutativeCommonSquareXYZ, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using h

theorem commutativeCommonSquareDerivesCommonLongProduct
    (u v w marker : Word Nat) :
    Derives commutativeCommonSquareThreeNilpotentBasis
      ((u ++ v) ++ w) (marker ++ marker) := by
  exact Derives.trans
    (Derives.symm
      (commutativeCommonSquareDerivesLongProduct u v w))
    (commutativeCommonSquareDerivesSquares u marker)

theorem commutativeCommonSquareDerivesCommutativity
    (u v : Word Nat) :
    Derives commutativeCommonSquareThreeNilpotentBasis
      (u ++ v) (v ++ u) := by
  have hbase :
      Derives commutativeCommonSquareThreeNilpotentBasis
        commutativeCommonSquareXY commutativeCommonSquareYX :=
    Derives.fromBasis
      (e := commutativeCommonSquareCommutativityLaw) (by
        simp [commutativeCommonSquareThreeNilpotentBasis])
  have h := Derives.subst hbase (instantiateTwoWords u v)
  simpa [commutativeCommonSquareCommutativityLaw,
    commutativeCommonSquareXY, commutativeCommonSquareYX,
    instantiateTwoWords, Word.bind, Word.append, Word.singleton] using h

private def wordOfCons (x : Nat) (xs : List Nat) : Word Nat :=
  ⟨x, xs⟩

private theorem commutativeCommonSquareMul_spec (a b : Fin 4) :
    commutativeCommonSquareThreeNilpotentFourMul a b =
      if (a = 2 ∧ b = 3) ∨ (a = 3 ∧ b = 2) then 1 else 0 := rfl

private theorem commutativeCommonSquareMul_square_zero
    (a : Fin 4) :
    commutativeCommonSquareThreeNilpotentFourMul a a = 0 := by
  rw [commutativeCommonSquareMul_spec]
  by_cases ha : a = 2 <;> by_cases hb : a = 3 <;>
    simp [ha, hb]

private theorem commutativeCommonSquareMul_triple_zero
    (a b c : Fin 4) :
    commutativeCommonSquareThreeNilpotentFourMul
        (commutativeCommonSquareThreeNilpotentFourMul a b) c = 0 := by
  decide +revert

private theorem commutativeCommonSquareMul_zero_left
    (a : Fin 4) :
    commutativeCommonSquareThreeNilpotentFourMul 0 a = 0 := by
  decide +revert

private theorem commutativeCommonSquareFold_zero
    (xs : List Nat) (valuation : Nat → Fin 4) :
    xs.foldl
        (fun current x =>
          commutativeCommonSquareThreeNilpotentFourMul
            current (valuation x))
        0 = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons,
        commutativeCommonSquareMul_zero_left]
      exact ih

theorem commutativeCommonSquareEval_long
    (valuation : Nat → Fin 4) (x y z : Nat) (zs : List Nat) :
    commutativeCommonSquareThreeNilpotentFour.semigroup.eval valuation
      (wordOfCons x (y :: z :: zs)) = (0 : Fin 4) := by
  change
    zs.foldl
      (fun current t =>
        commutativeCommonSquareThreeNilpotentFourMul
          current (valuation t))
      (commutativeCommonSquareThreeNilpotentFourMul
        (commutativeCommonSquareThreeNilpotentFourMul
          (valuation x) (valuation y))
        (valuation z)) = 0
  rw [commutativeCommonSquareMul_triple_zero]
  exact commutativeCommonSquareFold_zero zs valuation

def commutativeCommonSquareFiniteSquareLaw : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨1, [1]⟩⟩

def commutativeCommonSquareFiniteLongLaw : Identity (Fin 3) :=
  ⟨⟨0, [0]⟩, ⟨0, [1, 2]⟩⟩

def commutativeCommonSquareFiniteCommutativityLaw :
    Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

theorem commutativeCommonSquareFiniteSquareLaw_map :
    commutativeCommonSquareFiniteSquareLaw.map Fin.val =
      commutativeCommonSquareLaw := rfl

theorem commutativeCommonSquareFiniteLongLaw_map :
    commutativeCommonSquareFiniteLongLaw.map Fin.val =
      commutativeCommonSquareLongLaw := rfl

theorem commutativeCommonSquareFiniteCommutativityLaw_map :
    commutativeCommonSquareFiniteCommutativityLaw.map Fin.val =
      commutativeCommonSquareCommutativityLaw := rfl

theorem commutativeCommonSquareThreeNilpotentBasis_models :
    Models commutativeCommonSquareThreeNilpotentFour.semigroup
      commutativeCommonSquareThreeNilpotentBasis := by
  intro e he
  simp only [commutativeCommonSquareThreeNilpotentBasis,
    List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl
  · rw [← commutativeCommonSquareFiniteSquareLaw_map]
    exact
      commutativeCommonSquareThreeNilpotentFour.checkIdentityNat_sound
        commutativeCommonSquareFiniteSquareLaw (by decide)
  · rw [← commutativeCommonSquareFiniteLongLaw_map]
    exact
      commutativeCommonSquareThreeNilpotentFour.checkIdentityNat_sound
        commutativeCommonSquareFiniteLongLaw (by decide)
  · rw [← commutativeCommonSquareFiniteCommutativityLaw_map]
    exact
      commutativeCommonSquareThreeNilpotentFour.checkIdentityNat_sound
        commutativeCommonSquareFiniteCommutativityLaw (by decide)

private def singletonSeparator (x : Nat) : Nat → Fin 4 :=
  fun y => if y = x then 3 else 0

private theorem validSingleton_eq {x y : Nat}
    (valid :
      (Identity.mk (Word.singleton x) (Word.singleton y)).SatisfiedBy
        commutativeCommonSquareThreeNilpotentFour.semigroup) :
    x = y := by
  have evaluated := valid (singletonSeparator x)
  change singletonSeparator x x = singletonSeparator x y at evaluated
  apply Decidable.byContradiction
  intro hne
  simp [singletonSeparator, Ne.symm hne] at evaluated

private def unorderedPairSeparator
    (a b : Nat) : Nat → Fin 4 :=
  fun x => if x = a then 2 else if x = b then 3 else 0

private theorem unorderedPairSeparator_eq_two_iff
    (a b c : Nat) (_hab : a ≠ b) :
    unorderedPairSeparator a b c = (2 : Fin 4) ↔ c = a := by
  by_cases hca : c = a
  · subst c
    simp [unorderedPairSeparator]
  · by_cases hcb : c = b
    · subst c
      simp [unorderedPairSeparator, hca]
    · simp [unorderedPairSeparator, hca, hcb]

private theorem unorderedPairSeparator_eq_three_iff
    (a b c : Nat) (hab : a ≠ b) :
    unorderedPairSeparator a b c = (3 : Fin 4) ↔ c = b := by
  by_cases hca : c = a
  · subst c
    simp [unorderedPairSeparator, hab]
  · by_cases hcb : c = b
    · subst c
      simp [unorderedPairSeparator, hca]
    · simp [unorderedPairSeparator, hca, hcb]

private theorem unorderedPairSeparator_eval
    (a b c d : Nat) (hab : a ≠ b) :
    commutativeCommonSquareThreeNilpotentFour.semigroup.eval
        (unorderedPairSeparator a b) (wordOfCons c [d]) =
      if (c = a ∧ d = b) ∨ (c = b ∧ d = a) then
        (1 : Fin 4)
      else
        (0 : Fin 4) := by
  change
    commutativeCommonSquareThreeNilpotentFourMul
      (unorderedPairSeparator a b c)
      (unorderedPairSeparator a b d) =
        if (c = a ∧ d = b) ∨ (c = b ∧ d = a) then 1 else 0
  rw [commutativeCommonSquareMul_spec]
  simp only [unorderedPairSeparator_eq_two_iff a b c hab,
    unorderedPairSeparator_eq_three_iff a b d hab,
    unorderedPairSeparator_eq_three_iff a b c hab,
    unorderedPairSeparator_eq_two_iff a b d hab]

private theorem validOffDiagonalPair_orientation {a b c d : Nat}
    (valid :
      (Identity.mk (wordOfCons a [b]) (wordOfCons c [d])).SatisfiedBy
        commutativeCommonSquareThreeNilpotentFour.semigroup)
    (hab : a ≠ b) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have evaluated := valid (unorderedPairSeparator a b)
  rw [unorderedPairSeparator_eval a b a b hab,
    unorderedPairSeparator_eval a b c d hab] at evaluated
  have exactPair :
      (c = a ∧ d = b) ∨ (c = b ∧ d = a) := by
    apply Decidable.byContradiction
    intro hne
    simp [hab, hne] at evaluated
  exact exactPair.imp
    (fun h => ⟨h.1.symm, h.2.symm⟩)
    (fun h => ⟨h.2.symm, h.1.symm⟩)

private theorem allThree_pair (a b : Nat) :
    commutativeCommonSquareThreeNilpotentFour.semigroup.eval
      (fun _ => (3 : Fin 4)) (wordOfCons a [b]) = (0 : Fin 4) := by
  change commutativeCommonSquareThreeNilpotentFourMul 3 3 = 0
  exact commutativeCommonSquareMul_square_zero 3

private theorem allThree_long
    (x y z : Nat) (zs : List Nat) :
    commutativeCommonSquareThreeNilpotentFour.semigroup.eval
      (fun _ => (3 : Fin 4)) (wordOfCons x (y :: z :: zs)) =
        (0 : Fin 4) :=
  commutativeCommonSquareEval_long _ _ _ _ _

private theorem offDiagonal_pair_one
    (a b : Nat) (hab : a ≠ b) :
    commutativeCommonSquareThreeNilpotentFour.semigroup.eval
      (unorderedPairSeparator a b) (wordOfCons a [b]) =
        (1 : Fin 4) := by
  rw [unorderedPairSeparator_eval a b a b hab]
  simp

private theorem diagonal_pair_zero
    (valuation : Nat → Fin 4) (a : Nat) :
    commutativeCommonSquareThreeNilpotentFour.semigroup.eval valuation
      (wordOfCons a [a]) = (0 : Fin 4) := by
  change
    commutativeCommonSquareThreeNilpotentFourMul
      (valuation a) (valuation a) = 0
  exact commutativeCommonSquareMul_square_zero _

/-- Unrestricted completeness over `Nat` variables. The exact normal forms
are singleton projections, unordered off-diagonal quadratic words, and one
class containing every square and every word of length at least three. -/
theorem commutativeCommonSquareThreeNilpotentBasis_complete :
    BasisFor commutativeCommonSquareThreeNilpotentFour.semigroup
      commutativeCommonSquareThreeNilpotentBasis := by
  refine ⟨commutativeCommonSquareThreeNilpotentBasis_models, ?_⟩
  intro e valid
  cases e with
  | mk lhs rhs =>
      cases lhs with
      | mk lx ltail =>
          cases rhs with
          | mk rx rtail =>
              cases ltail with
              | nil =>
                  cases rtail with
                  | nil =>
                      have same : lx = rx := by
                        apply validSingleton_eq
                        exact valid
                      subst rx
                      exact Derives.refl _
                  | cons ry rrest =>
                      cases rrest with
                      | nil =>
                          have evaluated := valid (fun _ => (3 : Fin 4))
                          change
                            (3 : Fin 4) =
                              commutativeCommonSquareThreeNilpotentFour.semigroup.eval
                                (fun _ => (3 : Fin 4))
                                (wordOfCons rx [ry]) at evaluated
                          rw [allThree_pair] at evaluated
                          simp at evaluated
                      | cons rz rzs =>
                          have evaluated := valid (fun _ => (3 : Fin 4))
                          change
                            (3 : Fin 4) =
                              commutativeCommonSquareThreeNilpotentFour.semigroup.eval
                                (fun _ => (3 : Fin 4))
                                (wordOfCons rx (ry :: rz :: rzs))
                                at evaluated
                          rw [allThree_long] at evaluated
                          simp at evaluated
              | cons ly lrest =>
                  cases lrest with
                  | nil =>
                      cases rtail with
                      | nil =>
                          have evaluated := valid (fun _ => (3 : Fin 4))
                          change
                            commutativeCommonSquareThreeNilpotentFour.semigroup.eval
                                (fun _ => (3 : Fin 4))
                                (wordOfCons lx [ly]) =
                              (3 : Fin 4) at evaluated
                          rw [allThree_pair] at evaluated
                          simp at evaluated
                      | cons ry rrest =>
                          cases rrest with
                          | nil =>
                              by_cases hl : lx = ly
                              · by_cases hr : rx = ry
                                · subst ly
                                  subst ry
                                  simpa [wordOfCons, Word.singleton,
                                    Word.append] using
                                    commutativeCommonSquareDerivesSquares
                                      (Word.singleton lx)
                                      (Word.singleton rx)
                                · have evaluated :=
                                    valid (unorderedPairSeparator rx ry)
                                  change
                                    commutativeCommonSquareThreeNilpotentFour.semigroup.eval
                                        (unorderedPairSeparator rx ry)
                                        (wordOfCons lx [ly]) =
                                      commutativeCommonSquareThreeNilpotentFour.semigroup.eval
                                        (unorderedPairSeparator rx ry)
                                        (wordOfCons rx [ry]) at evaluated
                                  rw [hl, diagonal_pair_zero,
                                    offDiagonal_pair_one rx ry hr]
                                    at evaluated
                                  simp at evaluated
                              · by_cases hr : rx = ry
                                · have evaluated :=
                                    valid (unorderedPairSeparator lx ly)
                                  change
                                    commutativeCommonSquareThreeNilpotentFour.semigroup.eval
                                        (unorderedPairSeparator lx ly)
                                        (wordOfCons lx [ly]) =
                                      commutativeCommonSquareThreeNilpotentFour.semigroup.eval
                                        (unorderedPairSeparator lx ly)
                                        (wordOfCons rx [ry]) at evaluated
                                  rw [offDiagonal_pair_one lx ly hl, hr,
                                    diagonal_pair_zero] at evaluated
                                  simp at evaluated
                                · have orientation :=
                                    validOffDiagonalPair_orientation valid hl
                                  rcases orientation with direct | swapped
                                  · rcases direct with ⟨rfl, rfl⟩
                                    exact Derives.refl _
                                  · rcases swapped with ⟨hleft, hright⟩
                                    rw [← hright, ← hleft]
                                    simpa [wordOfCons, Word.singleton,
                                      Word.append] using
                                      commutativeCommonSquareDerivesCommutativity
                                        (Word.singleton lx)
                                        (Word.singleton ly)
                          | cons rz rzs =>
                              by_cases hl : lx = ly
                              · subst ly
                                have lhsToMarker :=
                                  commutativeCommonSquareDerivesSquares
                                    (Word.singleton lx) (Word.singleton 0)
                                have rhsToMarker :=
                                  commutativeCommonSquareDerivesCommonLongProduct
                                    (Word.singleton rx) (Word.singleton ry)
                                    (wordOfCons rz rzs) (Word.singleton 0)
                                exact Derives.trans
                                  (by simpa [wordOfCons, Word.singleton,
                                      Word.append] using lhsToMarker)
                                  (Derives.symm <| by
                                    simpa [wordOfCons, Word.singleton,
                                      Word.append] using rhsToMarker)
                              · have evaluated :=
                                  valid (unorderedPairSeparator lx ly)
                                change
                                  commutativeCommonSquareThreeNilpotentFour.semigroup.eval
                                      (unorderedPairSeparator lx ly)
                                      (wordOfCons lx [ly]) =
                                    commutativeCommonSquareThreeNilpotentFour.semigroup.eval
                                      (unorderedPairSeparator lx ly)
                                      (wordOfCons rx (ry :: rz :: rzs))
                                      at evaluated
                                rw [offDiagonal_pair_one lx ly hl,
                                  commutativeCommonSquareEval_long]
                                  at evaluated
                                simp at evaluated
                  | cons lz lzs =>
                      cases rtail with
                      | nil =>
                          have evaluated := valid (fun _ => (3 : Fin 4))
                          change
                            commutativeCommonSquareThreeNilpotentFour.semigroup.eval
                                (fun _ => (3 : Fin 4))
                                (wordOfCons lx (ly :: lz :: lzs)) =
                              (3 : Fin 4) at evaluated
                          rw [allThree_long] at evaluated
                          simp at evaluated
                      | cons ry rrest =>
                          cases rrest with
                          | nil =>
                              by_cases hr : rx = ry
                              · subst ry
                                have lhsToMarker :=
                                  commutativeCommonSquareDerivesCommonLongProduct
                                    (Word.singleton lx) (Word.singleton ly)
                                    (wordOfCons lz lzs) (Word.singleton 0)
                                have rhsToMarker :=
                                  commutativeCommonSquareDerivesSquares
                                    (Word.singleton rx) (Word.singleton 0)
                                exact Derives.trans
                                  (by simpa [wordOfCons, Word.singleton,
                                      Word.append] using lhsToMarker)
                                  (Derives.symm <| by
                                    simpa [wordOfCons, Word.singleton,
                                      Word.append] using rhsToMarker)
                              · have evaluated :=
                                  valid (unorderedPairSeparator rx ry)
                                change
                                  commutativeCommonSquareThreeNilpotentFour.semigroup.eval
                                      (unorderedPairSeparator rx ry)
                                      (wordOfCons lx (ly :: lz :: lzs)) =
                                    commutativeCommonSquareThreeNilpotentFour.semigroup.eval
                                      (unorderedPairSeparator rx ry)
                                      (wordOfCons rx [ry]) at evaluated
                                rw [commutativeCommonSquareEval_long,
                                  offDiagonal_pair_one rx ry hr] at evaluated
                                simp at evaluated
                          | cons rz rzs =>
                              have lhsToMarker :=
                                commutativeCommonSquareDerivesCommonLongProduct
                                  (Word.singleton lx) (Word.singleton ly)
                                  (wordOfCons lz lzs) (Word.singleton 0)
                              have rhsToMarker :=
                                commutativeCommonSquareDerivesCommonLongProduct
                                  (Word.singleton rx) (Word.singleton ry)
                                  (wordOfCons rz rzs) (Word.singleton 0)
                              exact Derives.trans
                                (by simpa [wordOfCons, Word.singleton,
                                    Word.append] using lhsToMarker)
                                (Derives.symm <| by
                                  simpa [wordOfCons, Word.singleton,
                                    Word.append] using rhsToMarker)

/-- The three semantic word classes separated by `S4_3`: singleton
projections, unordered off-diagonal quadratic words, and the common class
containing every square and every word of length at least three. -/
inductive CommutativeCommonSquareShape where
  | singleton (letter : Nat)
  | offDiagonal (low high : Nat)
  | common
  deriving DecidableEq

/-- Canonical semantic class of a word in `S4_3`. -/
def commutativeCommonSquareShape : Word Nat →
    CommutativeCommonSquareShape
  | ⟨head, []⟩ => .singleton head
  | ⟨head, next :: []⟩ =>
      if head = next then .common
      else .offDiagonal (min head next) (max head next)
  | ⟨_, _ :: _ :: _⟩ => .common

/-- Validity in `S4_3` forces both sides into the same exact semantic word
class. This is the reusable separation half of the normal-form proof. -/
theorem commutativeCommonSquareShape_eq_of_valid
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        commutativeCommonSquareThreeNilpotentFour.semigroup) :
    commutativeCommonSquareShape identity.lhs =
      commutativeCommonSquareShape identity.rhs := by
  cases identity with
  | mk lhs rhs =>
      cases lhs with
      | mk lx ltail =>
          cases rhs with
          | mk rx rtail =>
              cases ltail with
              | nil =>
                  cases rtail with
                  | nil =>
                      have same : lx = rx := validSingleton_eq valid
                      subst rx
                      rfl
                  | cons ry rrest =>
                      cases rrest with
                      | nil =>
                          have evaluated := valid (fun _ => (3 : Fin 4))
                          change
                            (3 : Fin 4) =
                              commutativeCommonSquareThreeNilpotentFour.semigroup.eval
                                (fun _ => (3 : Fin 4))
                                (wordOfCons rx [ry]) at evaluated
                          rw [allThree_pair] at evaluated
                          simp at evaluated
                      | cons rz rzs =>
                          have evaluated := valid (fun _ => (3 : Fin 4))
                          change
                            (3 : Fin 4) =
                              commutativeCommonSquareThreeNilpotentFour.semigroup.eval
                                (fun _ => (3 : Fin 4))
                                (wordOfCons rx (ry :: rz :: rzs))
                                at evaluated
                          rw [allThree_long] at evaluated
                          simp at evaluated
              | cons ly lrest =>
                  cases lrest with
                  | nil =>
                      cases rtail with
                      | nil =>
                          have evaluated := valid (fun _ => (3 : Fin 4))
                          change
                            commutativeCommonSquareThreeNilpotentFour.semigroup.eval
                                (fun _ => (3 : Fin 4))
                                (wordOfCons lx [ly]) =
                              (3 : Fin 4) at evaluated
                          rw [allThree_pair] at evaluated
                          simp at evaluated
                      | cons ry rrest =>
                          cases rrest with
                          | nil =>
                              by_cases leftDiagonal : lx = ly
                              · by_cases rightDiagonal : rx = ry
                                · subst ly
                                  subst ry
                                  simp [commutativeCommonSquareShape]
                                · have evaluated :=
                                    valid (unorderedPairSeparator rx ry)
                                  change
                                    commutativeCommonSquareThreeNilpotentFour.semigroup.eval
                                        (unorderedPairSeparator rx ry)
                                        (wordOfCons lx [ly]) =
                                      commutativeCommonSquareThreeNilpotentFour.semigroup.eval
                                        (unorderedPairSeparator rx ry)
                                        (wordOfCons rx [ry]) at evaluated
                                  rw [leftDiagonal, diagonal_pair_zero,
                                    offDiagonal_pair_one rx ry
                                      rightDiagonal] at evaluated
                                  simp at evaluated
                              · by_cases rightDiagonal : rx = ry
                                · have evaluated :=
                                    valid (unorderedPairSeparator lx ly)
                                  change
                                    commutativeCommonSquareThreeNilpotentFour.semigroup.eval
                                        (unorderedPairSeparator lx ly)
                                        (wordOfCons lx [ly]) =
                                      commutativeCommonSquareThreeNilpotentFour.semigroup.eval
                                        (unorderedPairSeparator lx ly)
                                        (wordOfCons rx [ry]) at evaluated
                                  rw [offDiagonal_pair_one lx ly
                                      leftDiagonal,
                                    rightDiagonal, diagonal_pair_zero]
                                    at evaluated
                                  simp at evaluated
                                · have orientation :=
                                    validOffDiagonalPair_orientation
                                      valid leftDiagonal
                                  rcases orientation with direct | swapped
                                  · rcases direct with ⟨rfl, rfl⟩
                                    rfl
                                  · rcases swapped with ⟨first, second⟩
                                    rw [← second, ← first]
                                    simp [commutativeCommonSquareShape,
                                      leftDiagonal,
                                      Ne.symm leftDiagonal,
                                      Nat.min_comm, Nat.max_comm]
                          | cons rz rzs =>
                              by_cases leftDiagonal : lx = ly
                              · subst ly
                                simp [commutativeCommonSquareShape]
                              · have evaluated :=
                                  valid (unorderedPairSeparator lx ly)
                                change
                                  commutativeCommonSquareThreeNilpotentFour.semigroup.eval
                                      (unorderedPairSeparator lx ly)
                                      (wordOfCons lx [ly]) =
                                    commutativeCommonSquareThreeNilpotentFour.semigroup.eval
                                      (unorderedPairSeparator lx ly)
                                      (wordOfCons rx (ry :: rz :: rzs))
                                      at evaluated
                                rw [offDiagonal_pair_one lx ly
                                    leftDiagonal,
                                  commutativeCommonSquareEval_long]
                                  at evaluated
                                simp at evaluated
                  | cons lz lzs =>
                      cases rtail with
                      | nil =>
                          have evaluated := valid (fun _ => (3 : Fin 4))
                          change
                            commutativeCommonSquareThreeNilpotentFour.semigroup.eval
                                (fun _ => (3 : Fin 4))
                                (wordOfCons lx (ly :: lz :: lzs)) =
                              (3 : Fin 4) at evaluated
                          rw [allThree_long] at evaluated
                          simp at evaluated
                      | cons ry rrest =>
                          cases rrest with
                          | nil =>
                              by_cases rightDiagonal : rx = ry
                              · subst ry
                                simp [commutativeCommonSquareShape]
                              · have evaluated :=
                                  valid (unorderedPairSeparator rx ry)
                                change
                                  commutativeCommonSquareThreeNilpotentFour.semigroup.eval
                                      (unorderedPairSeparator rx ry)
                                      (wordOfCons lx (ly :: lz :: lzs)) =
                                    commutativeCommonSquareThreeNilpotentFour.semigroup.eval
                                      (unorderedPairSeparator rx ry)
                                      (wordOfCons rx [ry]) at evaluated
                                rw [commutativeCommonSquareEval_long,
                                  offDiagonal_pair_one rx ry
                                    rightDiagonal] at evaluated
                                simp at evaluated
                          | cons _ _ =>
                              rfl

theorem commutativeCommonSquareThreeNilpotentOppositeBasis_complete :
    BasisFor
      commutativeCommonSquareThreeNilpotentFour.semigroup.opposite
      (reversedBasis commutativeCommonSquareThreeNilpotentBasis) :=
  commutativeCommonSquareThreeNilpotentBasis_complete.oppositeReversed

end SemigroupBasis.Examples
