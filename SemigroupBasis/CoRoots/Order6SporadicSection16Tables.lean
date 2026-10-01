import SemigroupBasis.FiniteReflection

/-! Exact direct Section16 tables from Lee-Zhang2015 pp49-50.
Closed finite proofs, no assumed Models or completeness. -/

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace SemigroupBasis.CoRoots.Order6SporadicSection16

open SemigroupBasis

def fssExclusionIdentity : Identity Nat :=
  ⟨⟨0, [0, 1, 0, 0, 2, 0, 0]⟩, ⟨0, [0, 1, 2, 0, 0]⟩⟩


namespace S6_3813

def tableMul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6)) else if a = 1 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6)) else if a = 2 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6)) else if a = 3 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6)) else if a = 4 then (if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6)) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := tableMul
  assoc := by decide


theorem squares_idempotent (a : Fin 6) :
    table.mul (table.mul a a) (table.mul a a) = table.mul a a := by
  revert a; decide

def fssValuation (x : Nat) : Fin 6 :=
  if x = 0 then 5 else if x = 1 then 3 else 2

theorem fssExclusion_values :
    table.semigroup.eval fssValuation fssExclusionIdentity.lhs ≠
      table.semigroup.eval fssValuation fssExclusionIdentity.rhs := by decide

theorem not_fssExclusion : ¬ fssExclusionIdentity.SatisfiedBy table.semigroup := by
  intro valid
  exact fssExclusion_values (valid fssValuation)

#print axioms squares_idempotent
#print axioms not_fssExclusion
end S6_3813


namespace S6_3815

def tableMul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6)) else if a = 1 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6)) else if a = 2 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6)) else if a = 3 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6)) else if a = 4 then (if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6)) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := tableMul
  assoc := by decide


theorem squares_idempotent (a : Fin 6) :
    table.mul (table.mul a a) (table.mul a a) = table.mul a a := by
  revert a; decide

def fssValuation (x : Nat) : Fin 6 :=
  if x = 0 then 5 else if x = 1 then 3 else 2

theorem fssExclusion_values :
    table.semigroup.eval fssValuation fssExclusionIdentity.lhs ≠
      table.semigroup.eval fssValuation fssExclusionIdentity.rhs := by decide

theorem not_fssExclusion : ¬ fssExclusionIdentity.SatisfiedBy table.semigroup := by
  intro valid
  exact fssExclusion_values (valid fssValuation)

#print axioms squares_idempotent
#print axioms not_fssExclusion
end S6_3815


namespace S6_3826

def tableMul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6)) else if a = 1 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6)) else if a = 2 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6)) else if a = 3 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6)) else if a = 4 then (if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6)) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := tableMul
  assoc := by decide


theorem squares_idempotent (a : Fin 6) :
    table.mul (table.mul a a) (table.mul a a) = table.mul a a := by
  revert a; decide

def fssValuation (x : Nat) : Fin 6 :=
  if x = 0 then 5 else if x = 1 then 3 else 2

theorem fssExclusion_values :
    table.semigroup.eval fssValuation fssExclusionIdentity.lhs ≠
      table.semigroup.eval fssValuation fssExclusionIdentity.rhs := by decide

theorem not_fssExclusion : ¬ fssExclusionIdentity.SatisfiedBy table.semigroup := by
  intro valid
  exact fssExclusion_values (valid fssValuation)

#print axioms squares_idempotent
#print axioms not_fssExclusion
end S6_3826


namespace S6_3828

def tableMul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6)) else if a = 1 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6)) else if a = 2 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6)) else if a = 3 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6)) else if a = 4 then (if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6)) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := tableMul
  assoc := by decide


theorem squares_idempotent (a : Fin 6) :
    table.mul (table.mul a a) (table.mul a a) = table.mul a a := by
  revert a; decide

def fssValuation (x : Nat) : Fin 6 :=
  if x = 0 then 5 else if x = 1 then 3 else 2

theorem fssExclusion_values :
    table.semigroup.eval fssValuation fssExclusionIdentity.lhs ≠
      table.semigroup.eval fssValuation fssExclusionIdentity.rhs := by decide

theorem not_fssExclusion : ¬ fssExclusionIdentity.SatisfiedBy table.semigroup := by
  intro valid
  exact fssExclusion_values (valid fssValuation)

#print axioms squares_idempotent
#print axioms not_fssExclusion
end S6_3828


namespace S6_6437

def tableMul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6)) else if a = 1 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6)) else if a = 2 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (0 : Fin 6)) else if a = 3 then (if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6)) else if a = 4 then (if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (4 : Fin 6)) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := tableMul
  assoc := by decide


theorem squares_idempotent (a : Fin 6) :
    table.mul (table.mul a a) (table.mul a a) = table.mul a a := by
  revert a; decide

def fssValuation (x : Nat) : Fin 6 :=
  if x = 0 then 5 else if x = 1 then 2 else 4

theorem fssExclusion_values :
    table.semigroup.eval fssValuation fssExclusionIdentity.lhs ≠
      table.semigroup.eval fssValuation fssExclusionIdentity.rhs := by decide

theorem not_fssExclusion : ¬ fssExclusionIdentity.SatisfiedBy table.semigroup := by
  intro valid
  exact fssExclusion_values (valid fssValuation)

#print axioms squares_idempotent
#print axioms not_fssExclusion
end S6_6437


namespace S6_6444

def tableMul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6)) else if a = 1 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6)) else if a = 2 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6)) else if a = 3 then (if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6)) else if a = 4 then (if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (4 : Fin 6)) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := tableMul
  assoc := by decide


theorem squares_idempotent (a : Fin 6) :
    table.mul (table.mul a a) (table.mul a a) = table.mul a a := by
  revert a; decide

def fssValuation (x : Nat) : Fin 6 :=
  if x = 0 then 5 else if x = 1 then 2 else 4

theorem fssExclusion_values :
    table.semigroup.eval fssValuation fssExclusionIdentity.lhs ≠
      table.semigroup.eval fssValuation fssExclusionIdentity.rhs := by decide

theorem not_fssExclusion : ¬ fssExclusionIdentity.SatisfiedBy table.semigroup := by
  intro valid
  exact fssExclusion_values (valid fssValuation)

#print axioms squares_idempotent
#print axioms not_fssExclusion
end S6_6444


end SemigroupBasis.CoRoots.Order6SporadicSection16
