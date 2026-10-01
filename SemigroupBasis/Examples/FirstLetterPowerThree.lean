import SemigroupBasis.Opposite
import SemigroupBasis.FiniteTable

namespace SemigroupBasis.Examples

open SemigroupBasis

def firstPowerMul (a _ : Fin 3) : Fin 3 :=
  if a = 2 then 2 else 0

def firstLetterPowerThree : FiniteTable where
  order := 3
  mul := firstPowerMul
  assoc := by decide

def firstPowerXX : Word Nat := ⟨0, [0]⟩
def firstPowerXY : Word Nat := ⟨0, [1]⟩
def firstPowerBasisLaw : Identity Nat := ⟨firstPowerXX, firstPowerXY⟩
def firstPowerBasis : List (Identity Nat) := [firstPowerBasisLaw]

theorem firstPowerBasisModels :
    Models firstLetterPowerThree.semigroup firstPowerBasis := by
  intro e he
  simp only [firstPowerBasis, List.mem_singleton] at he
  subst e
  intro valuation
  change
    firstPowerMul (valuation 0) (valuation 0) =
      firstPowerMul (valuation 0) (valuation 1)
  rfl

private def instantiateTwo (head suffix : Word Nat) : Nat → Word Nat
  | 0 => head
  | 1 => suffix
  | n + 2 => Word.singleton (n + 2)

theorem firstPowerDerivesNormal (w : Word Nat) :
    match w.tail with
    | [] => Derives firstPowerBasis w w
    | _ :: _ =>
        Derives firstPowerBasis w ⟨w.head, [w.head]⟩ := by
  cases w with
  | mk head tail =>
      cases tail with
      | nil => exact Derives.refl _
      | cons next rest =>
          let suffix : Word Nat := ⟨next, rest⟩
          have hbase : Derives firstPowerBasis firstPowerXX firstPowerXY :=
            Derives.fromBasis (e := firstPowerBasisLaw) (List.Mem.head [])
          have h := Derives.subst hbase <|
            instantiateTwo (Word.singleton head) suffix
          exact Derives.symm <| by
            simpa [firstPowerBasisLaw, firstPowerXX, firstPowerXY,
              instantiateTwo, Word.bind, Word.append, Word.singleton,
              suffix] using h

theorem firstPower_eval_product (valuation : Nat → Fin 3) (head next : Nat)
    (rest : List Nat) :
    firstLetterPowerThree.semigroup.eval valuation ⟨head, next :: rest⟩ =
      firstPowerMul (valuation head) (valuation next) := by
  have stable (a b c : Fin 3) :
      firstPowerMul (firstPowerMul a b) c = firstPowerMul a b := by
    simp [firstPowerMul]
  unfold Semigroup.eval
  simp only [List.foldl_cons, FiniteTable.semigroup, firstLetterPowerThree]
  induction rest with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons, stable]
      exact ih

theorem firstPowerBasisComplete :
    BasisFor firstLetterPowerThree.semigroup firstPowerBasis := by
  refine ⟨firstPowerBasisModels, ?_⟩
  intro e valid
  cases e with
  | mk lhs rhs =>
      cases lhs with
      | mk lhsHead lhsTail =>
          cases lhsTail with
          | nil =>
              cases rhs with
              | mk rhsHead rhsTail =>
                  cases rhsTail with
                  | nil =>
                      have heads : lhsHead = rhsHead := by
                        apply Decidable.byContradiction
                        intro hne
                        let valuation : Nat → Fin 3 := fun z =>
                          if z = lhsHead then 1 else 0
                        have evaluated := valid valuation
                        simp [Semigroup.eval, valuation,
                          Ne.symm hne] at evaluated
                      cases heads
                      exact Derives.refl _
                  | cons rhsNext rhsRest =>
                      let valuation : Nat → Fin 3 := fun z =>
                        if z = lhsHead then 1 else 0
                      have evaluated := valid valuation
                      rw [firstPower_eval_product] at evaluated
                      simp only [Semigroup.eval, List.foldl_nil] at evaluated
                      simp only [valuation, if_pos] at evaluated
                      split at evaluated <;> simp [firstPowerMul] at evaluated
          | cons lhsNext lhsRest =>
              cases rhs with
              | mk rhsHead rhsTail =>
                  cases rhsTail with
                  | nil =>
                      let valuation : Nat → Fin 3 := fun z =>
                        if z = rhsHead then 1 else 0
                      have evaluated := valid valuation
                      rw [firstPower_eval_product] at evaluated
                      simp only [Semigroup.eval, List.foldl_nil] at evaluated
                      simp only [valuation, if_pos] at evaluated
                      split at evaluated <;> simp [firstPowerMul] at evaluated
                  | cons rhsNext rhsRest =>
                      have heads : lhsHead = rhsHead := by
                        apply Decidable.byContradiction
                        intro hne
                        let valuation : Nat → Fin 3 := fun z =>
                          if z = lhsHead then 2 else 0
                        have evaluated := valid valuation
                        rw [firstPower_eval_product,
                          firstPower_eval_product] at evaluated
                        simp [valuation, firstPowerMul,
                          Ne.symm hne] at evaluated
                      have lhsNormal := firstPowerDerivesNormal
                        ⟨lhsHead, lhsNext :: lhsRest⟩
                      have rhsNormal := firstPowerDerivesNormal
                        ⟨rhsHead, rhsNext :: rhsRest⟩
                      exact Derives.trans lhsNormal <| by
                        rw [heads]
                        exact Derives.symm rhsNormal

def firstPowerOppositeBasis : List (Identity Nat) :=
  reversedBasis firstPowerBasis

theorem firstPowerOppositeBasisComplete :
    BasisFor firstLetterPowerThree.semigroup.opposite
      firstPowerOppositeBasis :=
  firstPowerBasisComplete.oppositeReversed

end SemigroupBasis.Examples
