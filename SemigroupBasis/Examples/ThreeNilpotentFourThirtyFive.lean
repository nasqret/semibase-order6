import SemigroupBasis.Examples.ThreeNilpotentFour

namespace SemigroupBasis.Examples

open SemigroupBasis

/-- The exact zero-based form of the catalogue table
`[[1,1,1,1],[1,1,1,1],[1,1,2,1],[1,1,2,2]]`. -/
def threeNilpotentFourThirtyFiveMul (a b : Fin 4) : Fin 4 :=
  if a = 0 then
    if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else 0
  else if a = 1 then
    if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else 0
  else if a = 2 then
    if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 1 else 0
  else
    if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 1 else 1

/-- The four-element three-nilpotent semigroup representing `S4_35`. -/
def threeNilpotentFourThirtyFive : FiniteTable where
  order := 4
  mul := threeNilpotentFourThirtyFiveMul
  assoc := by decide

private def wordOfCons (x : Nat) (xs : List Nat) : Word Nat :=
  ⟨x, xs⟩

private theorem threeNilpotentFourThirtyFiveMul_triple_zero
    (a b c : Fin 4) :
    threeNilpotentFourThirtyFiveMul
      (threeNilpotentFourThirtyFiveMul a b) c = 0 := by
  decide +revert

theorem threeNilpotentFourThirtyFiveBasis_models :
    Models threeNilpotentFourThirtyFive.semigroup
      threeNilpotentFourBasis := by
  intro e he
  simp only [threeNilpotentFourBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl
  all_goals
    intro valuation
    change
      threeNilpotentFourThirtyFiveMul
          (threeNilpotentFourThirtyFiveMul _ _) _ =
        threeNilpotentFourThirtyFiveMul
          (threeNilpotentFourThirtyFiveMul _ _) _
    rw [threeNilpotentFourThirtyFiveMul_triple_zero,
      threeNilpotentFourThirtyFiveMul_triple_zero]

private theorem threeNilpotentFourThirtyFiveMul_zero_left (a : Fin 4) :
    threeNilpotentFourThirtyFiveMul 0 a = 0 := by
  decide +revert

private theorem threeNilpotentFourThirtyFiveFold_zero (xs : List Nat)
    (valuation : Nat → Fin 4) :
    xs.foldl
        (fun current x =>
          threeNilpotentFourThirtyFiveMul current (valuation x)) 0 = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons,
        threeNilpotentFourThirtyFiveMul_zero_left]
      exact ih

private theorem threeNilpotentFourThirtyFiveEval_long
    (valuation : Nat → Fin 4) (x y z : Nat) (zs : List Nat) :
    threeNilpotentFourThirtyFive.semigroup.eval valuation
      (wordOfCons x (y :: z :: zs)) = (0 : Fin 4) := by
  change
    zs.foldl
      (fun current t =>
        threeNilpotentFourThirtyFiveMul current (valuation t))
      (threeNilpotentFourThirtyFiveMul
        (threeNilpotentFourThirtyFiveMul (valuation x) (valuation y))
        (valuation z)) = 0
  rw [threeNilpotentFourThirtyFiveMul_triple_zero]
  exact threeNilpotentFourThirtyFiveFold_zero zs valuation

private def singletonSeparator (x : Nat) : Nat → Fin 4 :=
  fun y => if y = x then 3 else 0

private theorem validSingleton_eq {x y : Nat}
    (valid :
      (Identity.mk (Word.singleton x) (Word.singleton y)).SatisfiedBy
        threeNilpotentFourThirtyFive.semigroup) :
    x = y := by
  have evaluated := valid (singletonSeparator x)
  change singletonSeparator x x = singletonSeparator x y at evaluated
  apply Decidable.byContradiction
  intro hne
  simp [singletonSeparator, Ne.symm hne] at evaluated

/-- This valuation makes a quadratic word evaluate to zero exactly when its
first variable is `z` and its second variable is not `z`. -/
private def firstOnlySeparator (z : Nat) : Nat → Fin 4 :=
  fun x => if x = z then 2 else 3

private theorem firstOnlySeparator_eval (z a b : Nat) :
    threeNilpotentFourThirtyFive.semigroup.eval (firstOnlySeparator z)
        (wordOfCons a [b]) =
      if a = z ∧ b ≠ z then (0 : Fin 4) else (1 : Fin 4) := by
  change
    threeNilpotentFourThirtyFiveMul
      (firstOnlySeparator z a) (firstOnlySeparator z b) =
        if a = z ∧ b ≠ z then (0 : Fin 4) else (1 : Fin 4)
  by_cases ha : a = z <;> by_cases hb : b = z <;>
    simp [firstOnlySeparator, ha, hb, threeNilpotentFourThirtyFiveMul]

/-- This valuation makes a quadratic word evaluate to zero exactly when its
second variable is `z` and its first variable is not `z`. -/
private def secondOnlySeparator (z : Nat) : Nat → Fin 4 :=
  fun x => if x = z then 3 else 2

private theorem secondOnlySeparator_eval (z a b : Nat) :
    threeNilpotentFourThirtyFive.semigroup.eval (secondOnlySeparator z)
        (wordOfCons a [b]) =
      if a ≠ z ∧ b = z then (0 : Fin 4) else (1 : Fin 4) := by
  change
    threeNilpotentFourThirtyFiveMul
      (secondOnlySeparator z a) (secondOnlySeparator z b) =
        if a ≠ z ∧ b = z then (0 : Fin 4) else (1 : Fin 4)
  by_cases ha : a = z <;> by_cases hb : b = z <;>
    simp [secondOnlySeparator, ha, hb, threeNilpotentFourThirtyFiveMul]

/-- This valuation makes a quadratic word evaluate to one exactly when both
variables are `z`. -/
private def diagonalSeparator (z : Nat) : Nat → Fin 4 :=
  fun x => if x = z then 2 else 0

private theorem diagonalSeparator_eval (z a b : Nat) :
    threeNilpotentFourThirtyFive.semigroup.eval (diagonalSeparator z)
        (wordOfCons a [b]) =
      if a = z ∧ b = z then (1 : Fin 4) else (0 : Fin 4) := by
  change
    threeNilpotentFourThirtyFiveMul
      (diagonalSeparator z a) (diagonalSeparator z b) =
        if a = z ∧ b = z then (1 : Fin 4) else (0 : Fin 4)
  by_cases ha : a = z <;> by_cases hb : b = z <;>
    simp [diagonalSeparator, ha, hb, threeNilpotentFourThirtyFiveMul]

/-- The `S4_35` table separates ordered quadratic words coordinate by
coordinate. -/
private theorem validPair_eq {a b c d : Nat}
    (valid :
      (Identity.mk (wordOfCons a [b]) (wordOfCons c [d])).SatisfiedBy
        threeNilpotentFourThirtyFive.semigroup) :
    a = c ∧ b = d := by
  by_cases hab : a = b
  · subst b
    have evaluated := valid (diagonalSeparator a)
    rw [diagonalSeparator_eval, diagonalSeparator_eval] at evaluated
    have hc : c = a := by
      apply Decidable.byContradiction
      intro hca
      simp [hca] at evaluated
    have hd : d = a := by
      apply Decidable.byContradiction
      intro hda
      simp [hc, hda] at evaluated
    exact ⟨hc.symm, hd.symm⟩
  · have firstEvaluated := valid (firstOnlySeparator a)
    rw [firstOnlySeparator_eval, firstOnlySeparator_eval] at firstEvaluated
    have hc : a = c := by
      apply Decidable.byContradiction
      intro hac
      have hba : b ≠ a := Ne.symm hab
      have hca : c ≠ a := Ne.symm hac
      simp [hba, hca] at firstEvaluated
    have secondEvaluated := valid (secondOnlySeparator b)
    rw [secondOnlySeparator_eval,
      secondOnlySeparator_eval] at secondEvaluated
    have hd : b = d := by
      apply Decidable.byContradiction
      intro hbd
      have hdb : d ≠ b := Ne.symm hbd
      simp [hab, hdb] at secondEvaluated
    exact ⟨hc, hd⟩

private theorem allThree_pair (a b : Nat) :
    threeNilpotentFourThirtyFive.semigroup.eval (fun _ => (3 : Fin 4))
      (wordOfCons a [b]) = (1 : Fin 4) := by
  change threeNilpotentFourThirtyFiveMul 3 3 = 1
  decide

private theorem allThree_long (x y z : Nat) (zs : List Nat) :
    threeNilpotentFourThirtyFive.semigroup.eval (fun _ => (3 : Fin 4))
      (wordOfCons x (y :: z :: zs)) = (0 : Fin 4) :=
  threeNilpotentFourThirtyFiveEval_long _ _ _ _ _

/-- Unrestricted completeness over `Nat` variables for the exact `S4_35`
catalogue representative. -/
theorem threeNilpotentFourThirtyFiveBasis_complete :
    BasisFor threeNilpotentFourThirtyFive.semigroup
      threeNilpotentFourBasis := by
  refine ⟨threeNilpotentFourThirtyFiveBasis_models, ?_⟩
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
                      have same : lx = rx := validSingleton_eq valid
                      subst rx
                      exact Derives.refl _
                  | cons ry rrest =>
                      cases rrest with
                      | nil =>
                          have evaluated := valid (fun _ => (3 : Fin 4))
                          change
                            (3 : Fin 4) =
                              threeNilpotentFourThirtyFive.semigroup.eval
                                (fun _ => (3 : Fin 4))
                                (wordOfCons rx [ry]) at evaluated
                          rw [allThree_pair] at evaluated
                          simp at evaluated
                      | cons rz rzs =>
                          have evaluated := valid (fun _ => (3 : Fin 4))
                          change
                            (3 : Fin 4) =
                              threeNilpotentFourThirtyFive.semigroup.eval
                                (fun _ => (3 : Fin 4))
                                (wordOfCons rx (ry :: rz :: rzs)) at evaluated
                          rw [allThree_long] at evaluated
                          simp at evaluated
              | cons ly lrest =>
                  cases lrest with
                  | nil =>
                      cases rtail with
                      | nil =>
                          have evaluated := valid (fun _ => (3 : Fin 4))
                          change
                            threeNilpotentFourThirtyFive.semigroup.eval
                                (fun _ => (3 : Fin 4))
                                (wordOfCons lx [ly]) =
                              (3 : Fin 4) at evaluated
                          rw [allThree_pair] at evaluated
                          simp at evaluated
                      | cons ry rrest =>
                          cases rrest with
                          | nil =>
                              have same : lx = rx ∧ ly = ry :=
                                validPair_eq valid
                              rcases same with ⟨rfl, rfl⟩
                              exact Derives.refl _
                          | cons rz rzs =>
                              have evaluated := valid (fun _ => (3 : Fin 4))
                              change
                                threeNilpotentFourThirtyFive.semigroup.eval
                                    (fun _ => (3 : Fin 4))
                                    (wordOfCons lx [ly]) =
                                  threeNilpotentFourThirtyFive.semigroup.eval
                                    (fun _ => (3 : Fin 4))
                                    (wordOfCons rx (ry :: rz :: rzs))
                                    at evaluated
                              rw [allThree_pair, allThree_long] at evaluated
                              simp at evaluated
                  | cons lz lzs =>
                      cases rtail with
                      | nil =>
                          have evaluated := valid (fun _ => (3 : Fin 4))
                          change
                            threeNilpotentFourThirtyFive.semigroup.eval
                                (fun _ => (3 : Fin 4))
                                (wordOfCons lx (ly :: lz :: lzs)) =
                              (3 : Fin 4) at evaluated
                          rw [allThree_long] at evaluated
                          simp at evaluated
                      | cons ry rrest =>
                          cases rrest with
                          | nil =>
                              have evaluated := valid (fun _ => (3 : Fin 4))
                              change
                                threeNilpotentFourThirtyFive.semigroup.eval
                                    (fun _ => (3 : Fin 4))
                                    (wordOfCons lx (ly :: lz :: lzs)) =
                                  threeNilpotentFourThirtyFive.semigroup.eval
                                    (fun _ => (3 : Fin 4))
                                    (wordOfCons rx [ry]) at evaluated
                              rw [allThree_long, allThree_pair] at evaluated
                              simp at evaluated
                          | cons rz rzs =>
                              exact threeNilpotentDerivesLongWords
                                (wordOfCons lx (ly :: lz :: lzs))
                                (wordOfCons rx (ry :: rz :: rzs))
                                (by simp [wordOfCons, Word.toList])
                                (by simp [wordOfCons, Word.toList])

theorem threeNilpotentFourThirtyFiveOppositeBasis_complete :
    BasisFor threeNilpotentFourThirtyFive.semigroup.opposite
      (reversedBasis threeNilpotentFourBasis) :=
  threeNilpotentFourThirtyFiveBasis_complete.oppositeReversed

end SemigroupBasis.Examples
