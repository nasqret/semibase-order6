import SemigroupBasis.CoRoots.Order6Day15.B33.B33Opposite

namespace SemigroupBasis.CoRoots.Order6Day15.B33.Catalogue

private theorem semigroup_eq_of_mul {G H : Semigroup S} (same : G.mul = H.mul) : G = H := by
  cases G; cases H; cases same; rfl

namespace S6_6225

def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6))
  else if a = 1 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6))
  else if a = 2 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (0 : Fin 6))
  else if a = 3 then (if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6))
  else if a = 4 then (if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6))
  else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

end S6_6225

theorem semigroup6225_eq : S6_6225.table.semigroup = table6225.semigroup := by
  apply semigroup_eq_of_mul
  funext a b
  exact (by decide : ∀ x y : Fin 6, S6_6225.mul x y = mul6225 x y) a b

theorem basisFor6225 : BasisFor S6_6225.table.semigroup basis := by
  rw [semigroup6225_eq]
  exact SemigroupBasis.CoRoots.Order6Day15.B33.basisFor6225

theorem basisFor6225_opposite : BasisFor S6_6225.table.semigroup.opposite (reversedBasis basis) :=
  basisFor6225.oppositeReversed

namespace S6_9878

def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6))
  else if a = 1 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6))
  else if a = 2 then (if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6))
  else if a = 3 then (if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6))
  else if a = 4 then (if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6))
  else if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

end S6_9878

theorem semigroup9878_eq : S6_9878.table.semigroup = table9878.semigroup := by
  apply semigroup_eq_of_mul
  funext a b
  exact (by decide : ∀ x y : Fin 6, S6_9878.mul x y = mul9878 x y) a b

theorem basisFor9878 : BasisFor S6_9878.table.semigroup basis := by
  rw [semigroup9878_eq]
  exact SemigroupBasis.CoRoots.Order6Day15.B33.basisFor9878

theorem basisFor9878_opposite : BasisFor S6_9878.table.semigroup.opposite (reversedBasis basis) :=
  basisFor9878.oppositeReversed

end SemigroupBasis.CoRoots.Order6Day15.B33.Catalogue
