import SemigroupBasis.FiniteTable

namespace SemigroupBasis.Examples

open SemigroupBasis

def nullTwo : FiniteTable where
  order := 2
  mul := fun _ _ => 0
  assoc := by intros; rfl

def nullXY : Word Nat := ⟨0, [1]⟩
def nullZT : Word Nat := ⟨2, [3]⟩
def nullBasisLaw : Identity Nat := ⟨nullXY, nullZT⟩
def nullBasis : List (Identity Nat) := [nullBasisLaw]

theorem nullBasis_models : Models nullTwo.semigroup nullBasis := by
  intro e he
  simp only [nullBasis, List.mem_singleton] at he
  subst e
  intro valuation
  rfl

private def instantiateFour (a b c d : Word Nat) : Nat → Word Nat
  | 0 => a
  | 1 => b
  | 2 => c
  | 3 => d
  | n + 4 => Word.singleton (n + 4)

theorem nullDerivesProducts (u v : Word Nat)
    (hu : u.tail ≠ []) (hv : v.tail ≠ []) :
    Derives nullBasis u v := by
  cases u with
  | mk uHead uTail =>
      cases uTail with
      | nil => contradiction
      | cons uNext uRest =>
          cases v with
          | mk vHead vTail =>
              cases vTail with
              | nil => contradiction
              | cons vNext vRest =>
                  let uSuffix : Word Nat := ⟨uNext, uRest⟩
                  let vSuffix : Word Nat := ⟨vNext, vRest⟩
                  have hbase : Derives nullBasis nullXY nullZT :=
                    Derives.fromBasis (e := nullBasisLaw) (List.Mem.head [])
                  have h := Derives.subst hbase <|
                    instantiateFour (Word.singleton uHead) uSuffix
                      (Word.singleton vHead) vSuffix
                  simpa [nullBasisLaw, nullXY, nullZT, instantiateFour,
                    Word.bind, Word.append, Word.singleton, uSuffix,
                    vSuffix] using h

theorem nullTwo_eval_product (valuation : Nat → Fin 2) (head next : Nat)
    (rest : List Nat) :
    nullTwo.semigroup.eval valuation ⟨head, next :: rest⟩ = (0 : Fin 2) := by
  induction rest with
  | nil => rfl
  | cons x xs ih =>
      simp only [Semigroup.eval, List.foldl_cons]
      exact ih

theorem nullBasis_complete : BasisFor nullTwo.semigroup nullBasis := by
  refine ⟨nullBasis_models, ?_⟩
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
                        let valuation : Nat → Fin 2 := fun z =>
                          if z = lhsHead then 1 else 0
                        have evaluated := valid valuation
                        simp [Semigroup.eval, valuation,
                          Ne.symm hne] at evaluated
                      cases heads
                      exact Derives.refl _
                  | cons rhsNext rhsRest =>
                      let valuation : Nat → Fin 2 := fun _ => 1
                      have evaluated := valid valuation
                      rw [nullTwo_eval_product] at evaluated
                      simp [Semigroup.eval, valuation] at evaluated
          | cons lhsNext lhsRest =>
              cases rhs with
              | mk rhsHead rhsTail =>
                  cases rhsTail with
                  | nil =>
                      let valuation : Nat → Fin 2 := fun _ => 1
                      have evaluated := valid valuation
                      rw [nullTwo_eval_product] at evaluated
                      simp [Semigroup.eval, valuation] at evaluated
                  | cons rhsNext rhsRest =>
                      exact nullDerivesProducts
                        ⟨lhsHead, lhsNext :: lhsRest⟩
                        ⟨rhsHead, rhsNext :: rhsRest⟩
                        (by simp) (by simp)

end SemigroupBasis.Examples
