import SemigroupBasis.Equational

namespace SemigroupBasis

/-- A concrete finite Cayley table together with its associativity proof. -/
structure FiniteTable where
  order : Nat
  mul : Fin order → Fin order → Fin order
  assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)

namespace FiniteTable

def semigroup (T : FiniteTable) : Semigroup (Fin T.order) :=
  ⟨T.mul, T.assoc⟩

def assignments : (variables carrier : Nat) →
    List (Fin variables → Fin carrier)
  | 0, _ => [fun i => Fin.elim0 i]
  | variables + 1, carrier =>
      (List.finRange carrier).flatMap fun head =>
        (assignments variables carrier).map fun tail =>
          Fin.cases head tail

theorem assignment_mem (valuation : Fin variables → Fin carrier) :
    valuation ∈ assignments variables carrier := by
  induction variables with
  | zero =>
      have h : valuation = fun i => Fin.elim0 i := by
        funext i
        exact Fin.elim0 i
      simp [assignments, h]
  | succ variables ih =>
      let head : Fin carrier := valuation 0
      let tail : Fin variables → Fin carrier := fun i => valuation i.succ
      have htail : tail ∈ assignments variables carrier := ih tail
      have hfun : Fin.cases head tail = valuation := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · rfl
        · rfl
      simp only [assignments, List.mem_flatMap, List.mem_map]
      exact ⟨head, List.mem_finRange head, tail, htail, hfun⟩

def checkIdentity (T : FiniteTable) (e : Identity (Fin variables)) : Bool :=
  (assignments variables T.order).all fun valuation =>
    decide (T.semigroup.eval valuation e.lhs = T.semigroup.eval valuation e.rhs)

/-- Exhaustively check finite functions without first flattening their full
cartesian product into one linearly traversed list. -/
def checkAssignmentsFused : (variables carrier : Nat) →
    ((Fin variables → Fin carrier) → Bool) → Bool
  | 0, _, predicate => predicate (fun index => Fin.elim0 index)
  | variables + 1, carrier, predicate =>
      (List.finRange carrier).all fun head =>
        checkAssignmentsFused variables carrier fun tail =>
          predicate (Fin.cases head tail)

theorem checkAssignmentsFused_sound
    (predicate : (Fin variables → Fin carrier) → Bool)
    (checked : checkAssignmentsFused variables carrier predicate = true) :
    ∀ valuation, predicate valuation = true := by
  induction variables with
  | zero =>
      intro valuation
      have valuation_eq :
          valuation = (fun index => Fin.elim0 index) := by
        funext index
        exact Fin.elim0 index
      rw [valuation_eq]
      simpa [checkAssignmentsFused] using checked
  | succ variables ih =>
      intro valuation
      let head : Fin carrier := valuation 0
      let tail : Fin variables → Fin carrier := fun index => valuation index.succ
      change
        (List.finRange carrier).all (fun value =>
          checkAssignmentsFused variables carrier fun candidate =>
            predicate (Fin.cases value candidate)) = true at checked
      have tailChecked :=
        ih (fun candidate => predicate (Fin.cases head candidate))
          ((List.all_eq_true.mp checked) head (List.mem_finRange head)) tail
      have rebuild : Fin.cases head tail = valuation := by
        funext index
        refine Fin.cases ?_ (fun rest => ?_) index
        · rfl
        · rfl
      rw [rebuild] at tailChecked
      exact tailChecked

/-- Fused exhaustive identity checker with bounded semantic recursion depth. -/
def checkIdentityFused (T : FiniteTable)
    (e : Identity (Fin variables)) : Bool :=
  checkAssignmentsFused variables T.order fun valuation =>
    decide (T.semigroup.eval valuation e.lhs = T.semigroup.eval valuation e.rhs)

theorem checkIdentity_sound (T : FiniteTable) (e : Identity (Fin variables))
    (h : T.checkIdentity e = true) : e.SatisfiedBy T.semigroup := by
  intro valuation
  have hall := List.all_eq_true.mp h
  exact of_decide_eq_true (hall valuation (assignment_mem valuation))

theorem checkIdentityFused_sound (T : FiniteTable)
    (e : Identity (Fin variables))
    (checked : T.checkIdentityFused e = true) :
    e.SatisfiedBy T.semigroup := by
  intro valuation
  exact of_decide_eq_true
    (checkAssignmentsFused_sound
      (fun candidate =>
        decide (T.semigroup.eval candidate e.lhs =
          T.semigroup.eval candidate e.rhs)) checked valuation)

/-- An explicit finite-table valuation with unequal evaluations refutes an identity. -/
theorem counterexample_sound (T : FiniteTable)
    (e : Identity (Fin variables))
    (valuation : Fin variables → Fin T.order)
    {lhsValue rhsValue : Fin T.order}
    (lhs_eval : T.semigroup.eval valuation e.lhs = lhsValue)
    (rhs_eval : T.semigroup.eval valuation e.rhs = rhsValue)
    (values_ne : lhsValue ≠ rhsValue) :
    ¬ e.SatisfiedBy T.semigroup := by
  exact Identity.not_satisfiedBy_of_failsAt (valuation := valuation) (by
    intro same
    exact values_ne (lhs_eval.symm.trans (same.trans rhs_eval)))

end FiniteTable
end SemigroupBasis
