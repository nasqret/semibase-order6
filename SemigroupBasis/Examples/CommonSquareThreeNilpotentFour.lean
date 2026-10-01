import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite

namespace SemigroupBasis.Examples

open SemigroupBasis

/-- The exact zero-based form of the catalogue table
`[[1,1,1,1],[1,1,1,1],[1,1,1,1],[1,1,2,1]]`. -/
def commonSquareThreeNilpotentFourMul (a b : Fin 4) : Fin 4 :=
  if a = 0 then
    if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else 0
  else if a = 1 then
    if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else 0
  else if a = 2 then
    if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else 0
  else
    if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 1 else 0

/-- The four-element three-nilpotent semigroup representing `S4_2`. -/
def commonSquareThreeNilpotentFour : FiniteTable where
  order := 4
  mul := commonSquareThreeNilpotentFourMul
  assoc := by decide

def commonSquareThreeNilpotentXX : Word Nat := ⟨0, [0]⟩
def commonSquareThreeNilpotentYY : Word Nat := ⟨1, [1]⟩
def commonSquareThreeNilpotentXYZ : Word Nat := ⟨0, [1, 2]⟩

def commonSquareThreeNilpotentSquareLaw : Identity Nat :=
  ⟨commonSquareThreeNilpotentXX, commonSquareThreeNilpotentYY⟩

def commonSquareThreeNilpotentLongLaw : Identity Nat :=
  ⟨commonSquareThreeNilpotentXX, commonSquareThreeNilpotentXYZ⟩

/-- The exact basis `xx = yy`, `xx = xyz`. -/
def commonSquareThreeNilpotentBasis : List (Identity Nat) :=
  [commonSquareThreeNilpotentSquareLaw,
    commonSquareThreeNilpotentLongLaw]

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

theorem commonSquareThreeNilpotentDerivesSquares
    (u v : Word Nat) :
    Derives commonSquareThreeNilpotentBasis (u ++ u) (v ++ v) := by
  have hbase :
      Derives commonSquareThreeNilpotentBasis
        commonSquareThreeNilpotentXX
        commonSquareThreeNilpotentYY :=
    Derives.fromBasis
      (e := commonSquareThreeNilpotentSquareLaw) (by
        simp [commonSquareThreeNilpotentBasis])
  have h := Derives.subst hbase (instantiateTwoWords u v)
  simpa [commonSquareThreeNilpotentSquareLaw,
    commonSquareThreeNilpotentXX, commonSquareThreeNilpotentYY,
    instantiateTwoWords, Word.bind, Word.append, Word.singleton] using h

theorem commonSquareThreeNilpotentDerivesLongProduct
    (u v w : Word Nat) :
    Derives commonSquareThreeNilpotentBasis
      (u ++ u) ((u ++ v) ++ w) := by
  have hbase :
      Derives commonSquareThreeNilpotentBasis
        commonSquareThreeNilpotentXX
        commonSquareThreeNilpotentXYZ :=
    Derives.fromBasis
      (e := commonSquareThreeNilpotentLongLaw) (by
        simp [commonSquareThreeNilpotentBasis])
  have h := Derives.subst hbase (instantiateThreeWords u v w)
  simpa [commonSquareThreeNilpotentLongLaw,
    commonSquareThreeNilpotentXX, commonSquareThreeNilpotentXYZ,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using h

/-- Every product of three nonempty blocks is derivably equal to every
square. -/
theorem commonSquareThreeNilpotentDerivesCommonLongProduct
    (u v w marker : Word Nat) :
    Derives commonSquareThreeNilpotentBasis
      ((u ++ v) ++ w) (marker ++ marker) := by
  exact Derives.trans
    (Derives.symm
      (commonSquareThreeNilpotentDerivesLongProduct u v w))
    (commonSquareThreeNilpotentDerivesSquares u marker)

private def wordOfCons (x : Nat) (xs : List Nat) : Word Nat :=
  ⟨x, xs⟩

private theorem commonSquareThreeNilpotentMul_spec (a b : Fin 4) :
    commonSquareThreeNilpotentFourMul a b =
      if a = 3 ∧ b = 2 then 1 else 0 := by
  decide +revert

private theorem commonSquareThreeNilpotentMul_square_zero
    (a : Fin 4) :
    commonSquareThreeNilpotentFourMul a a = 0 := by
  rw [commonSquareThreeNilpotentMul_spec]
  by_cases ha : a = 3 <;> simp [ha]

private theorem commonSquareThreeNilpotentMul_triple_zero
    (a b c : Fin 4) :
    commonSquareThreeNilpotentFourMul
        (commonSquareThreeNilpotentFourMul a b) c = 0 := by
  decide +revert

private theorem commonSquareThreeNilpotentMul_zero_left
    (a : Fin 4) :
    commonSquareThreeNilpotentFourMul 0 a = 0 := by
  decide +revert

private theorem commonSquareThreeNilpotentFold_zero
    (xs : List Nat) (valuation : Nat → Fin 4) :
    xs.foldl
        (fun current x =>
          commonSquareThreeNilpotentFourMul current (valuation x))
        0 = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons,
        commonSquareThreeNilpotentMul_zero_left]
      exact ih

theorem commonSquareThreeNilpotentEval_long
    (valuation : Nat → Fin 4) (x y z : Nat) (zs : List Nat) :
    commonSquareThreeNilpotentFour.semigroup.eval valuation
      (wordOfCons x (y :: z :: zs)) = (0 : Fin 4) := by
  change
    zs.foldl
      (fun current t =>
        commonSquareThreeNilpotentFourMul current (valuation t))
      (commonSquareThreeNilpotentFourMul
        (commonSquareThreeNilpotentFourMul
          (valuation x) (valuation y))
        (valuation z)) = 0
  rw [commonSquareThreeNilpotentMul_triple_zero]
  exact commonSquareThreeNilpotentFold_zero zs valuation

def commonSquareThreeNilpotentFiniteSquareLaw :
    Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨1, [1]⟩⟩

def commonSquareThreeNilpotentFiniteLongLaw :
    Identity (Fin 3) :=
  ⟨⟨0, [0]⟩, ⟨0, [1, 2]⟩⟩

theorem commonSquareThreeNilpotentFiniteSquareLaw_map :
    commonSquareThreeNilpotentFiniteSquareLaw.map Fin.val =
      commonSquareThreeNilpotentSquareLaw := rfl

theorem commonSquareThreeNilpotentFiniteLongLaw_map :
    commonSquareThreeNilpotentFiniteLongLaw.map Fin.val =
      commonSquareThreeNilpotentLongLaw := rfl

theorem commonSquareThreeNilpotentFourBasis_models :
    Models commonSquareThreeNilpotentFour.semigroup
      commonSquareThreeNilpotentBasis := by
  intro e he
  simp only [commonSquareThreeNilpotentBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · rw [← commonSquareThreeNilpotentFiniteSquareLaw_map]
    exact commonSquareThreeNilpotentFour.checkIdentityNat_sound
      commonSquareThreeNilpotentFiniteSquareLaw (by decide)
  · rw [← commonSquareThreeNilpotentFiniteLongLaw_map]
    exact commonSquareThreeNilpotentFour.checkIdentityNat_sound
      commonSquareThreeNilpotentFiniteLongLaw (by decide)

private def singletonSeparator (x : Nat) : Nat → Fin 4 :=
  fun y => if y = x then 3 else 0

private theorem validSingleton_eq {x y : Nat}
    (valid :
      (Identity.mk (Word.singleton x) (Word.singleton y)).SatisfiedBy
        commonSquareThreeNilpotentFour.semigroup) :
    x = y := by
  have evaluated := valid (singletonSeparator x)
  change singletonSeparator x x = singletonSeparator x y at evaluated
  apply Decidable.byContradiction
  intro hne
  simp [singletonSeparator, Ne.symm hne] at evaluated

private def orderedPairSeparator
    (a b : Nat) : Nat → Fin 4 :=
  fun x => if x = a then 3 else if x = b then 2 else 0

private theorem orderedPairSeparator_eq_three_iff
    (a b c : Nat) (_hab : a ≠ b) :
    orderedPairSeparator a b c = (3 : Fin 4) ↔ c = a := by
  by_cases hca : c = a
  · subst c
    simp [orderedPairSeparator]
  · by_cases hcb : c = b
    · subst c
      simp [orderedPairSeparator]
    · simp [orderedPairSeparator, hca, hcb]

private theorem orderedPairSeparator_eq_two_iff
    (a b c : Nat) (hab : a ≠ b) :
    orderedPairSeparator a b c = (2 : Fin 4) ↔ c = b := by
  by_cases hca : c = a
  · subst c
    simp [orderedPairSeparator, hab]
  · by_cases hcb : c = b
    · subst c
      simp [orderedPairSeparator, hca]
    · simp [orderedPairSeparator, hca, hcb]

private theorem orderedPairSeparator_eval
    (a b c d : Nat) (hab : a ≠ b) :
    commonSquareThreeNilpotentFour.semigroup.eval
        (orderedPairSeparator a b) (wordOfCons c [d]) =
      if c = a ∧ d = b then (1 : Fin 4) else (0 : Fin 4) := by
  change
    commonSquareThreeNilpotentFourMul
      (orderedPairSeparator a b c)
      (orderedPairSeparator a b d) =
        if c = a ∧ d = b then 1 else 0
  rw [commonSquareThreeNilpotentMul_spec]
  simp only [orderedPairSeparator_eq_three_iff a b c hab,
    orderedPairSeparator_eq_two_iff a b d hab]

private theorem validOffDiagonalPair_eq {a b c d : Nat}
    (valid :
      (Identity.mk (wordOfCons a [b]) (wordOfCons c [d])).SatisfiedBy
        commonSquareThreeNilpotentFour.semigroup)
    (hab : a ≠ b) :
    a = c ∧ b = d := by
  have evaluated := valid (orderedPairSeparator a b)
  rw [orderedPairSeparator_eval a b a b hab,
    orderedPairSeparator_eval a b c d hab] at evaluated
  have exactPair : c = a ∧ d = b := by
    apply Decidable.byContradiction
    intro hne
    simp [hne] at evaluated
  exact ⟨exactPair.1.symm, exactPair.2.symm⟩

private theorem allThree_pair (a b : Nat) :
    commonSquareThreeNilpotentFour.semigroup.eval
      (fun _ => (3 : Fin 4)) (wordOfCons a [b]) = (0 : Fin 4) := by
  change commonSquareThreeNilpotentFourMul 3 3 = 0
  exact commonSquareThreeNilpotentMul_square_zero 3

private theorem allThree_long
    (x y z : Nat) (zs : List Nat) :
    commonSquareThreeNilpotentFour.semigroup.eval
      (fun _ => (3 : Fin 4)) (wordOfCons x (y :: z :: zs)) =
        (0 : Fin 4) :=
  commonSquareThreeNilpotentEval_long _ _ _ _ _

private theorem offDiagonal_pair_one
    (a b : Nat) (hab : a ≠ b) :
    commonSquareThreeNilpotentFour.semigroup.eval
      (orderedPairSeparator a b) (wordOfCons a [b]) = (1 : Fin 4) := by
  rw [orderedPairSeparator_eval a b a b hab]
  simp

private theorem diagonal_pair_zero
    (valuation : Nat → Fin 4) (a : Nat) :
    commonSquareThreeNilpotentFour.semigroup.eval valuation
      (wordOfCons a [a]) = (0 : Fin 4) := by
  change commonSquareThreeNilpotentFourMul (valuation a) (valuation a) = 0
  exact commonSquareThreeNilpotentMul_square_zero _

/-- Unrestricted completeness over `Nat` variables. The table separates
singleton projections and ordered off-diagonal quadratic words. The two
basis identities identify all squares and every word of length at least
three. -/
theorem commonSquareThreeNilpotentFourBasis_complete :
    BasisFor commonSquareThreeNilpotentFour.semigroup
      commonSquareThreeNilpotentBasis := by
  refine ⟨commonSquareThreeNilpotentFourBasis_models, ?_⟩
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
                              commonSquareThreeNilpotentFour.semigroup.eval
                                (fun _ => (3 : Fin 4))
                                (wordOfCons rx [ry]) at evaluated
                          rw [allThree_pair] at evaluated
                          simp at evaluated
                      | cons rz rzs =>
                          have evaluated := valid (fun _ => (3 : Fin 4))
                          change
                            (3 : Fin 4) =
                              commonSquareThreeNilpotentFour.semigroup.eval
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
                            commonSquareThreeNilpotentFour.semigroup.eval
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
                                    commonSquareThreeNilpotentDerivesSquares
                                      (Word.singleton lx)
                                      (Word.singleton rx)
                                · have evaluated :=
                                    valid (orderedPairSeparator rx ry)
                                  change
                                    commonSquareThreeNilpotentFour.semigroup.eval
                                        (orderedPairSeparator rx ry)
                                        (wordOfCons lx [ly]) =
                                      commonSquareThreeNilpotentFour.semigroup.eval
                                        (orderedPairSeparator rx ry)
                                        (wordOfCons rx [ry]) at evaluated
                                  rw [hl, diagonal_pair_zero,
                                    offDiagonal_pair_one rx ry hr] at evaluated
                                  simp at evaluated
                              · by_cases hr : rx = ry
                                · have evaluated :=
                                    valid (orderedPairSeparator lx ly)
                                  change
                                    commonSquareThreeNilpotentFour.semigroup.eval
                                        (orderedPairSeparator lx ly)
                                        (wordOfCons lx [ly]) =
                                      commonSquareThreeNilpotentFour.semigroup.eval
                                        (orderedPairSeparator lx ly)
                                        (wordOfCons rx [ry]) at evaluated
                                  rw [offDiagonal_pair_one lx ly hl, hr,
                                    diagonal_pair_zero] at evaluated
                                  simp at evaluated
                                · have same : lx = rx ∧ ly = ry := by
                                    apply validOffDiagonalPair_eq valid hl
                                  rcases same with ⟨rfl, rfl⟩
                                  exact Derives.refl _
                          | cons rz rzs =>
                              by_cases hl : lx = ly
                              · subst ly
                                have lhsToMarker :=
                                  commonSquareThreeNilpotentDerivesSquares
                                    (Word.singleton lx) (Word.singleton 0)
                                have rhsToMarker :=
                                  commonSquareThreeNilpotentDerivesCommonLongProduct
                                    (Word.singleton rx) (Word.singleton ry)
                                    (wordOfCons rz rzs) (Word.singleton 0)
                                exact Derives.trans
                                  (by simpa [wordOfCons, Word.singleton,
                                      Word.append] using lhsToMarker)
                                  (Derives.symm <| by
                                    simpa [wordOfCons, Word.singleton,
                                      Word.append] using rhsToMarker)
                              · have evaluated :=
                                  valid (orderedPairSeparator lx ly)
                                change
                                  commonSquareThreeNilpotentFour.semigroup.eval
                                      (orderedPairSeparator lx ly)
                                      (wordOfCons lx [ly]) =
                                    commonSquareThreeNilpotentFour.semigroup.eval
                                      (orderedPairSeparator lx ly)
                                      (wordOfCons rx (ry :: rz :: rzs))
                                      at evaluated
                                rw [offDiagonal_pair_one lx ly hl,
                                  commonSquareThreeNilpotentEval_long]
                                  at evaluated
                                simp at evaluated
                  | cons lz lzs =>
                      cases rtail with
                      | nil =>
                          have evaluated := valid (fun _ => (3 : Fin 4))
                          change
                            commonSquareThreeNilpotentFour.semigroup.eval
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
                                  commonSquareThreeNilpotentDerivesCommonLongProduct
                                    (Word.singleton lx) (Word.singleton ly)
                                    (wordOfCons lz lzs) (Word.singleton 0)
                                have rhsToMarker :=
                                  commonSquareThreeNilpotentDerivesSquares
                                    (Word.singleton rx) (Word.singleton 0)
                                exact Derives.trans
                                  (by simpa [wordOfCons, Word.singleton,
                                      Word.append] using lhsToMarker)
                                  (Derives.symm <| by
                                    simpa [wordOfCons, Word.singleton,
                                      Word.append] using rhsToMarker)
                              · have evaluated :=
                                  valid (orderedPairSeparator rx ry)
                                change
                                  commonSquareThreeNilpotentFour.semigroup.eval
                                      (orderedPairSeparator rx ry)
                                      (wordOfCons lx (ly :: lz :: lzs)) =
                                    commonSquareThreeNilpotentFour.semigroup.eval
                                      (orderedPairSeparator rx ry)
                                      (wordOfCons rx [ry]) at evaluated
                                rw [commonSquareThreeNilpotentEval_long,
                                  offDiagonal_pair_one rx ry hr] at evaluated
                                simp at evaluated
                          | cons rz rzs =>
                              have lhsToMarker :=
                                commonSquareThreeNilpotentDerivesCommonLongProduct
                                  (Word.singleton lx) (Word.singleton ly)
                                  (wordOfCons lz lzs) (Word.singleton 0)
                              have rhsToMarker :=
                                commonSquareThreeNilpotentDerivesCommonLongProduct
                                  (Word.singleton rx) (Word.singleton ry)
                                  (wordOfCons rz rzs) (Word.singleton 0)
                              exact Derives.trans
                                (by simpa [wordOfCons, Word.singleton,
                                    Word.append] using lhsToMarker)
                                (Derives.symm <| by
                                  simpa [wordOfCons, Word.singleton,
                                    Word.append] using rhsToMarker)

theorem commonSquareThreeNilpotentFourOppositeBasis_complete :
    BasisFor commonSquareThreeNilpotentFour.semigroup.opposite
      (reversedBasis commonSquareThreeNilpotentBasis) :=
  commonSquareThreeNilpotentFourBasis_complete.oppositeReversed

end SemigroupBasis.Examples
