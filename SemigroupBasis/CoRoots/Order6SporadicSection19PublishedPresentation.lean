import SemigroupBasis.CoRoots.Order6SporadicSection19Presentation

/-! Literal Proposition19.1. The old presentation supplies only its verified
table; its withdrawn nine-law completeness claim is not used. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6SporadicSection19.Published

abbrev table : FiniteTable := SemigroupBasis.CoRoots.Order6SporadicSection19.table

def a_cube : Identity Nat := ⟨⟨0, [0,0]⟩, ⟨0, [0]⟩⟩

def a_left : Identity Nat := ⟨⟨0, [0,1,0]⟩, ⟨0, [1,0]⟩⟩

def a_right : Identity Nat := ⟨⟨0, [1,0,0]⟩, ⟨0, [1,0]⟩⟩

def b_exchange : Identity Nat := ⟨⟨0, [1,0,2,0]⟩, ⟨0, [2,0,1,0]⟩⟩

def c_000 : Identity Nat := ⟨⟨0, [1,0,1]⟩, ⟨0, [0,0,1,1,0]⟩⟩

def c_001 : Identity Nat := ⟨⟨0, [2,1,0,1]⟩, ⟨0, [2,0,0,1,1,0]⟩⟩

def c_010 : Identity Nat := ⟨⟨0, [1,3,0,1]⟩, ⟨0, [0,3,0,1,1,0]⟩⟩

def c_011 : Identity Nat := ⟨⟨0, [2,1,3,0,1]⟩, ⟨0, [2,0,3,0,1,1,0]⟩⟩

def c_100 : Identity Nat := ⟨⟨0, [1,0,4,1]⟩, ⟨0, [0,0,4,1,1,0]⟩⟩

def c_101 : Identity Nat := ⟨⟨0, [2,1,0,4,1]⟩, ⟨0, [2,0,0,4,1,1,0]⟩⟩

def c_110 : Identity Nat := ⟨⟨0, [1,3,0,4,1]⟩, ⟨0, [0,3,0,4,1,1,0]⟩⟩

def c_111 : Identity Nat := ⟨⟨0, [2,1,3,0,4,1]⟩, ⟨0, [2,0,3,0,4,1,1,0]⟩⟩

def d_left_0 : Identity Nat := ⟨⟨0, [1,1,0]⟩, ⟨1, [1,0,1,1,0]⟩⟩

def d_left_1 : Identity Nat := ⟨⟨0, [2,1,1,0]⟩, ⟨1, [1,0,2,1,1,0]⟩⟩

def d_right_00 : Identity Nat := ⟨⟨0, [1,1,0,0]⟩, ⟨0, [1,1,0,1,1,0]⟩⟩

def d_right_01 : Identity Nat := ⟨⟨0, [2,1,1,0,0]⟩, ⟨0, [2,1,1,0,1,1,0]⟩⟩

def d_right_10 : Identity Nat := ⟨⟨0, [1,1,0,3,0]⟩, ⟨0, [1,1,0,3,1,1,0]⟩⟩

def d_right_11 : Identity Nat := ⟨⟨0, [2,1,1,0,3,0]⟩, ⟨0, [2,1,1,0,3,1,1,0]⟩⟩

def e_back_00 : Identity Nat := ⟨⟨0, [1,0,1]⟩, ⟨0, [1,1,0]⟩⟩

def e_back_01 : Identity Nat := ⟨⟨0, [2,1,0,1]⟩, ⟨0, [2,1,1,0]⟩⟩

def e_back_10 : Identity Nat := ⟨⟨0, [1,3,0,1]⟩, ⟨0, [1,3,1,0]⟩⟩

def e_back_11 : Identity Nat := ⟨⟨0, [2,1,3,0,1]⟩, ⟨0, [2,1,3,1,0]⟩⟩

def e_front_00 : Identity Nat := ⟨⟨0, [1,0,1]⟩, ⟨1, [0,0,1]⟩⟩

def e_front_01 : Identity Nat := ⟨⟨0, [2,1,0,1]⟩, ⟨1, [2,0,0,1]⟩⟩

def e_front_10 : Identity Nat := ⟨⟨0, [1,3,0,1]⟩, ⟨1, [0,3,0,1]⟩⟩

def e_front_11 : Identity Nat := ⟨⟨0, [2,1,3,0,1]⟩, ⟨1, [2,0,3,0,1]⟩⟩

def f_right_00 : Identity Nat := ⟨⟨0, [1,1,0,1]⟩, ⟨0, [1,1,0,0]⟩⟩

def f_right_01 : Identity Nat := ⟨⟨0, [2,1,1,0,1]⟩, ⟨0, [2,1,1,0,0]⟩⟩

def f_right_10 : Identity Nat := ⟨⟨0, [1,1,0,3,1]⟩, ⟨0, [1,1,0,3,0]⟩⟩

def f_right_11 : Identity Nat := ⟨⟨0, [2,1,1,0,3,1]⟩, ⟨0, [2,1,1,0,3,0]⟩⟩

def f_left_00 : Identity Nat := ⟨⟨1, [0,1,1,0]⟩, ⟨0, [0,1,1,0]⟩⟩

def f_left_01 : Identity Nat := ⟨⟨1, [2,0,1,1,0]⟩, ⟨0, [2,0,1,1,0]⟩⟩

def f_left_10 : Identity Nat := ⟨⟨1, [0,3,1,1,0]⟩, ⟨0, [0,3,1,1,0]⟩⟩

def f_left_11 : Identity Nat := ⟨⟨1, [2,0,3,1,1,0]⟩, ⟨0, [2,0,3,1,1,0]⟩⟩

def f_middle_00 : Identity Nat := ⟨⟨0, [1,1,1,0]⟩, ⟨0, [0,1,1,0]⟩⟩

def f_middle_01 : Identity Nat := ⟨⟨0, [2,1,1,1,0]⟩, ⟨0, [2,0,1,1,0]⟩⟩

def f_middle_10 : Identity Nat := ⟨⟨0, [1,3,1,1,0]⟩, ⟨0, [0,3,1,1,0]⟩⟩

def f_middle_11 : Identity Nat := ⟨⟨0, [2,1,3,1,1,0]⟩, ⟨0, [2,0,3,1,1,0]⟩⟩

def basis : List (Identity Nat) :=
  [a_cube, a_left, a_right, b_exchange, c_000, c_001, c_010, c_011, c_100, c_101, c_110, c_111, d_left_0, d_left_1, d_right_00, d_right_01, d_right_10, d_right_11, e_back_00, e_back_01, e_back_10, e_back_11, e_front_00, e_front_01, e_front_10, e_front_11, f_right_00, f_right_01, f_right_10, f_right_11, f_left_00, f_left_01, f_left_10, f_left_11, f_middle_00, f_middle_01, f_middle_10, f_middle_11]

theorem basis_length : basis.length = 38 := rfl

theorem basis_exact : basis.map (fun law => (law.lhs.toList, law.rhs.toList)) =
    [([0, 0, 0], [0, 0]), ([0, 0, 1, 0], [0, 1, 0]), ([0, 1, 0, 0], [0, 1, 0]), ([0, 1, 0, 2, 0], [0, 2, 0, 1, 0]), ([0, 1, 0, 1], [0, 0, 0, 1, 1, 0]), ([0, 2, 1, 0, 1], [0, 2, 0, 0, 1, 1, 0]), ([0, 1, 3, 0, 1], [0, 0, 3, 0, 1, 1, 0]), ([0, 2, 1, 3, 0, 1], [0, 2, 0, 3, 0, 1, 1, 0]), ([0, 1, 0, 4, 1], [0, 0, 0, 4, 1, 1, 0]), ([0, 2, 1, 0, 4, 1], [0, 2, 0, 0, 4, 1, 1, 0]), ([0, 1, 3, 0, 4, 1], [0, 0, 3, 0, 4, 1, 1, 0]), ([0, 2, 1, 3, 0, 4, 1], [0, 2, 0, 3, 0, 4, 1, 1, 0]), ([0, 1, 1, 0], [1, 1, 0, 1, 1, 0]), ([0, 2, 1, 1, 0], [1, 1, 0, 2, 1, 1, 0]), ([0, 1, 1, 0, 0], [0, 1, 1, 0, 1, 1, 0]), ([0, 2, 1, 1, 0, 0], [0, 2, 1, 1, 0, 1, 1, 0]), ([0, 1, 1, 0, 3, 0], [0, 1, 1, 0, 3, 1, 1, 0]), ([0, 2, 1, 1, 0, 3, 0], [0, 2, 1, 1, 0, 3, 1, 1, 0]), ([0, 1, 0, 1], [0, 1, 1, 0]), ([0, 2, 1, 0, 1], [0, 2, 1, 1, 0]), ([0, 1, 3, 0, 1], [0, 1, 3, 1, 0]), ([0, 2, 1, 3, 0, 1], [0, 2, 1, 3, 1, 0]), ([0, 1, 0, 1], [1, 0, 0, 1]), ([0, 2, 1, 0, 1], [1, 2, 0, 0, 1]), ([0, 1, 3, 0, 1], [1, 0, 3, 0, 1]), ([0, 2, 1, 3, 0, 1], [1, 2, 0, 3, 0, 1]), ([0, 1, 1, 0, 1], [0, 1, 1, 0, 0]), ([0, 2, 1, 1, 0, 1], [0, 2, 1, 1, 0, 0]), ([0, 1, 1, 0, 3, 1], [0, 1, 1, 0, 3, 0]), ([0, 2, 1, 1, 0, 3, 1], [0, 2, 1, 1, 0, 3, 0]), ([1, 0, 1, 1, 0], [0, 0, 1, 1, 0]), ([1, 2, 0, 1, 1, 0], [0, 2, 0, 1, 1, 0]), ([1, 0, 3, 1, 1, 0], [0, 0, 3, 1, 1, 0]), ([1, 2, 0, 3, 1, 1, 0], [0, 2, 0, 3, 1, 1, 0]), ([0, 1, 1, 1, 0], [0, 0, 1, 1, 0]), ([0, 2, 1, 1, 1, 0], [0, 2, 0, 1, 1, 0]), ([0, 1, 3, 1, 1, 0], [0, 0, 3, 1, 1, 0]), ([0, 2, 1, 3, 1, 1, 0], [0, 2, 0, 3, 1, 1, 0])] := rfl

private theorem cases6 (a : Fin 6) :
    a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 := by decide +revert +kernel

theorem pointwise_a_cube (a0 : Fin 6) :
    (table.mul (table.mul a0 a0) a0) = (table.mul a0 a0) := by
  rcases cases6 a0 with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide +revert +kernel

theorem valid_a_cube : a_cube.SatisfiedBy table.semigroup := by
  intro valuation
  exact pointwise_a_cube (valuation 0)

theorem derives_a_cube : Derives basis a_cube.lhs a_cube.rhs :=
  Derives.fromBasis (by decide : a_cube ∈ basis)

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.pointwise_a_cube
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.valid_a_cube
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.derives_a_cube

theorem pointwise_a_left (a0 a1 : Fin 6) :
    (table.mul (table.mul (table.mul a0 a0) a1) a0) = (table.mul (table.mul a0 a1) a0) := by
  rcases cases6 a0 with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide +revert +kernel

theorem valid_a_left : a_left.SatisfiedBy table.semigroup := by
  intro valuation
  exact pointwise_a_left (valuation 0) (valuation 1)

theorem derives_a_left : Derives basis a_left.lhs a_left.rhs :=
  Derives.fromBasis (by decide : a_left ∈ basis)

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.pointwise_a_left
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.valid_a_left
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.derives_a_left

theorem pointwise_a_right (a0 a1 : Fin 6) :
    (table.mul (table.mul (table.mul a0 a1) a0) a0) = (table.mul (table.mul a0 a1) a0) := by
  rcases cases6 a0 with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide +revert +kernel

theorem valid_a_right : a_right.SatisfiedBy table.semigroup := by
  intro valuation
  exact pointwise_a_right (valuation 0) (valuation 1)

theorem derives_a_right : Derives basis a_right.lhs a_right.rhs :=
  Derives.fromBasis (by decide : a_right ∈ basis)

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.pointwise_a_right
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.valid_a_right
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.derives_a_right

theorem pointwise_b_exchange (a0 a1 a2 : Fin 6) :
    (table.mul (table.mul (table.mul (table.mul a0 a1) a0) a2) a0) = (table.mul (table.mul (table.mul (table.mul a0 a2) a0) a1) a0) := by
  rcases cases6 a0 with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide +revert +kernel

theorem valid_b_exchange : b_exchange.SatisfiedBy table.semigroup := by
  intro valuation
  exact pointwise_b_exchange (valuation 0) (valuation 1) (valuation 2)

theorem derives_b_exchange : Derives basis b_exchange.lhs b_exchange.rhs :=
  Derives.fromBasis (by decide : b_exchange ∈ basis)

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.pointwise_b_exchange
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.valid_b_exchange
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.derives_b_exchange

theorem pointwise_c_000 (a0 a1 : Fin 6) :
    (table.mul (table.mul (table.mul a0 a1) a0) a1) = (table.mul (table.mul (table.mul (table.mul (table.mul a0 a0) a0) a1) a1) a0) := by
  rcases cases6 a0 with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide +revert +kernel

theorem valid_c_000 : c_000.SatisfiedBy table.semigroup := by
  intro valuation
  exact pointwise_c_000 (valuation 0) (valuation 1)

theorem derives_c_000 : Derives basis c_000.lhs c_000.rhs :=
  Derives.fromBasis (by decide : c_000 ∈ basis)

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.pointwise_c_000
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.valid_c_000
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.derives_c_000

theorem pointwise_c_001 (a0 a1 a2 : Fin 6) :
    (table.mul (table.mul (table.mul (table.mul a0 a2) a1) a0) a1) = (table.mul (table.mul (table.mul (table.mul (table.mul (table.mul a0 a2) a0) a0) a1) a1) a0) := by
  rcases cases6 a0 with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide +revert +kernel

theorem valid_c_001 : c_001.SatisfiedBy table.semigroup := by
  intro valuation
  exact pointwise_c_001 (valuation 0) (valuation 1) (valuation 2)

theorem derives_c_001 : Derives basis c_001.lhs c_001.rhs :=
  Derives.fromBasis (by decide : c_001 ∈ basis)

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.pointwise_c_001
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.valid_c_001
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.derives_c_001

theorem pointwise_c_010 (a0 a1 a3 : Fin 6) :
    (table.mul (table.mul (table.mul (table.mul a0 a1) a3) a0) a1) = (table.mul (table.mul (table.mul (table.mul (table.mul (table.mul a0 a0) a3) a0) a1) a1) a0) := by
  rcases cases6 a0 with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide +revert +kernel

theorem valid_c_010 : c_010.SatisfiedBy table.semigroup := by
  intro valuation
  exact pointwise_c_010 (valuation 0) (valuation 1) (valuation 3)

theorem derives_c_010 : Derives basis c_010.lhs c_010.rhs :=
  Derives.fromBasis (by decide : c_010 ∈ basis)

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.pointwise_c_010
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.valid_c_010
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.derives_c_010

theorem pointwise_c_011 (a0 a1 a2 a3 : Fin 6) :
    (table.mul (table.mul (table.mul (table.mul (table.mul a0 a2) a1) a3) a0) a1) = (table.mul (table.mul (table.mul (table.mul (table.mul (table.mul (table.mul a0 a2) a0) a3) a0) a1) a1) a0) := by
  rcases cases6 a0 with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rcases cases6 a1 with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide +revert +kernel

theorem valid_c_011 : c_011.SatisfiedBy table.semigroup := by
  intro valuation
  exact pointwise_c_011 (valuation 0) (valuation 1) (valuation 2) (valuation 3)

theorem derives_c_011 : Derives basis c_011.lhs c_011.rhs :=
  Derives.fromBasis (by decide : c_011 ∈ basis)

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.pointwise_c_011
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.valid_c_011
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.derives_c_011

theorem pointwise_c_100 (a0 a1 a4 : Fin 6) :
    (table.mul (table.mul (table.mul (table.mul a0 a1) a0) a4) a1) = (table.mul (table.mul (table.mul (table.mul (table.mul (table.mul a0 a0) a0) a4) a1) a1) a0) := by
  rcases cases6 a0 with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide +revert +kernel

theorem valid_c_100 : c_100.SatisfiedBy table.semigroup := by
  intro valuation
  exact pointwise_c_100 (valuation 0) (valuation 1) (valuation 4)

theorem derives_c_100 : Derives basis c_100.lhs c_100.rhs :=
  Derives.fromBasis (by decide : c_100 ∈ basis)

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.pointwise_c_100
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.valid_c_100
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.derives_c_100

theorem pointwise_c_101 (a0 a1 a2 a4 : Fin 6) :
    (table.mul (table.mul (table.mul (table.mul (table.mul a0 a2) a1) a0) a4) a1) = (table.mul (table.mul (table.mul (table.mul (table.mul (table.mul (table.mul a0 a2) a0) a0) a4) a1) a1) a0) := by
  rcases cases6 a0 with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rcases cases6 a1 with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide +revert +kernel

theorem valid_c_101 : c_101.SatisfiedBy table.semigroup := by
  intro valuation
  exact pointwise_c_101 (valuation 0) (valuation 1) (valuation 2) (valuation 4)

theorem derives_c_101 : Derives basis c_101.lhs c_101.rhs :=
  Derives.fromBasis (by decide : c_101 ∈ basis)

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.pointwise_c_101
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.valid_c_101
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.derives_c_101

theorem pointwise_c_110 (a0 a1 a3 a4 : Fin 6) :
    (table.mul (table.mul (table.mul (table.mul (table.mul a0 a1) a3) a0) a4) a1) = (table.mul (table.mul (table.mul (table.mul (table.mul (table.mul (table.mul a0 a0) a3) a0) a4) a1) a1) a0) := by
  rcases cases6 a0 with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rcases cases6 a1 with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide +revert +kernel

theorem valid_c_110 : c_110.SatisfiedBy table.semigroup := by
  intro valuation
  exact pointwise_c_110 (valuation 0) (valuation 1) (valuation 3) (valuation 4)

theorem derives_c_110 : Derives basis c_110.lhs c_110.rhs :=
  Derives.fromBasis (by decide : c_110 ∈ basis)

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.pointwise_c_110
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.valid_c_110
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.derives_c_110

theorem pointwise_c_111 (a0 a1 a2 a3 a4 : Fin 6) :
    (table.mul (table.mul (table.mul (table.mul (table.mul (table.mul a0 a2) a1) a3) a0) a4) a1) = (table.mul (table.mul (table.mul (table.mul (table.mul (table.mul (table.mul (table.mul a0 a2) a0) a3) a0) a4) a1) a1) a0) := by
  rcases cases6 a0 with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rcases cases6 a1 with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide +revert +kernel

theorem valid_c_111 : c_111.SatisfiedBy table.semigroup := by
  intro valuation
  exact pointwise_c_111 (valuation 0) (valuation 1) (valuation 2) (valuation 3) (valuation 4)

theorem derives_c_111 : Derives basis c_111.lhs c_111.rhs :=
  Derives.fromBasis (by decide : c_111 ∈ basis)

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.pointwise_c_111
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.valid_c_111
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.derives_c_111

theorem pointwise_d_left_0 (a0 a1 : Fin 6) :
    (table.mul (table.mul (table.mul a0 a1) a1) a0) = (table.mul (table.mul (table.mul (table.mul (table.mul a1 a1) a0) a1) a1) a0) := by
  rcases cases6 a0 with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide +revert +kernel

theorem valid_d_left_0 : d_left_0.SatisfiedBy table.semigroup := by
  intro valuation
  exact pointwise_d_left_0 (valuation 0) (valuation 1)

theorem derives_d_left_0 : Derives basis d_left_0.lhs d_left_0.rhs :=
  Derives.fromBasis (by decide : d_left_0 ∈ basis)

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.pointwise_d_left_0
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.valid_d_left_0
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.derives_d_left_0

theorem pointwise_d_left_1 (a0 a1 a2 : Fin 6) :
    (table.mul (table.mul (table.mul (table.mul a0 a2) a1) a1) a0) = (table.mul (table.mul (table.mul (table.mul (table.mul (table.mul a1 a1) a0) a2) a1) a1) a0) := by
  rcases cases6 a0 with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide +revert +kernel

theorem valid_d_left_1 : d_left_1.SatisfiedBy table.semigroup := by
  intro valuation
  exact pointwise_d_left_1 (valuation 0) (valuation 1) (valuation 2)

theorem derives_d_left_1 : Derives basis d_left_1.lhs d_left_1.rhs :=
  Derives.fromBasis (by decide : d_left_1 ∈ basis)

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.pointwise_d_left_1
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.valid_d_left_1
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.derives_d_left_1

theorem pointwise_d_right_00 (a0 a1 : Fin 6) :
    (table.mul (table.mul (table.mul (table.mul a0 a1) a1) a0) a0) = (table.mul (table.mul (table.mul (table.mul (table.mul (table.mul a0 a1) a1) a0) a1) a1) a0) := by
  rcases cases6 a0 with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide +revert +kernel

theorem valid_d_right_00 : d_right_00.SatisfiedBy table.semigroup := by
  intro valuation
  exact pointwise_d_right_00 (valuation 0) (valuation 1)

theorem derives_d_right_00 : Derives basis d_right_00.lhs d_right_00.rhs :=
  Derives.fromBasis (by decide : d_right_00 ∈ basis)

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.pointwise_d_right_00
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.valid_d_right_00
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.derives_d_right_00

theorem pointwise_d_right_01 (a0 a1 a2 : Fin 6) :
    (table.mul (table.mul (table.mul (table.mul (table.mul a0 a2) a1) a1) a0) a0) = (table.mul (table.mul (table.mul (table.mul (table.mul (table.mul (table.mul a0 a2) a1) a1) a0) a1) a1) a0) := by
  rcases cases6 a0 with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide +revert +kernel

theorem valid_d_right_01 : d_right_01.SatisfiedBy table.semigroup := by
  intro valuation
  exact pointwise_d_right_01 (valuation 0) (valuation 1) (valuation 2)

theorem derives_d_right_01 : Derives basis d_right_01.lhs d_right_01.rhs :=
  Derives.fromBasis (by decide : d_right_01 ∈ basis)

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.pointwise_d_right_01
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.valid_d_right_01
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.derives_d_right_01

theorem pointwise_d_right_10 (a0 a1 a3 : Fin 6) :
    (table.mul (table.mul (table.mul (table.mul (table.mul a0 a1) a1) a0) a3) a0) = (table.mul (table.mul (table.mul (table.mul (table.mul (table.mul (table.mul a0 a1) a1) a0) a3) a1) a1) a0) := by
  rcases cases6 a0 with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide +revert +kernel

theorem valid_d_right_10 : d_right_10.SatisfiedBy table.semigroup := by
  intro valuation
  exact pointwise_d_right_10 (valuation 0) (valuation 1) (valuation 3)

theorem derives_d_right_10 : Derives basis d_right_10.lhs d_right_10.rhs :=
  Derives.fromBasis (by decide : d_right_10 ∈ basis)

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.pointwise_d_right_10
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.valid_d_right_10
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.derives_d_right_10

theorem pointwise_d_right_11 (a0 a1 a2 a3 : Fin 6) :
    (table.mul (table.mul (table.mul (table.mul (table.mul (table.mul a0 a2) a1) a1) a0) a3) a0) = (table.mul (table.mul (table.mul (table.mul (table.mul (table.mul (table.mul (table.mul a0 a2) a1) a1) a0) a3) a1) a1) a0) := by
  rcases cases6 a0 with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rcases cases6 a1 with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide +revert +kernel

theorem valid_d_right_11 : d_right_11.SatisfiedBy table.semigroup := by
  intro valuation
  exact pointwise_d_right_11 (valuation 0) (valuation 1) (valuation 2) (valuation 3)

theorem derives_d_right_11 : Derives basis d_right_11.lhs d_right_11.rhs :=
  Derives.fromBasis (by decide : d_right_11 ∈ basis)

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.pointwise_d_right_11
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.valid_d_right_11
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.derives_d_right_11

theorem pointwise_e_back_00 (a0 a1 : Fin 6) :
    (table.mul (table.mul (table.mul a0 a1) a0) a1) = (table.mul (table.mul (table.mul a0 a1) a1) a0) := by
  rcases cases6 a0 with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide +revert +kernel

theorem valid_e_back_00 : e_back_00.SatisfiedBy table.semigroup := by
  intro valuation
  exact pointwise_e_back_00 (valuation 0) (valuation 1)

theorem derives_e_back_00 : Derives basis e_back_00.lhs e_back_00.rhs :=
  Derives.fromBasis (by decide : e_back_00 ∈ basis)

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.pointwise_e_back_00
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.valid_e_back_00
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.derives_e_back_00

theorem pointwise_e_back_01 (a0 a1 a2 : Fin 6) :
    (table.mul (table.mul (table.mul (table.mul a0 a2) a1) a0) a1) = (table.mul (table.mul (table.mul (table.mul a0 a2) a1) a1) a0) := by
  rcases cases6 a0 with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide +revert +kernel

theorem valid_e_back_01 : e_back_01.SatisfiedBy table.semigroup := by
  intro valuation
  exact pointwise_e_back_01 (valuation 0) (valuation 1) (valuation 2)

theorem derives_e_back_01 : Derives basis e_back_01.lhs e_back_01.rhs :=
  Derives.fromBasis (by decide : e_back_01 ∈ basis)

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.pointwise_e_back_01
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.valid_e_back_01
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.derives_e_back_01

theorem pointwise_e_back_10 (a0 a1 a3 : Fin 6) :
    (table.mul (table.mul (table.mul (table.mul a0 a1) a3) a0) a1) = (table.mul (table.mul (table.mul (table.mul a0 a1) a3) a1) a0) := by
  rcases cases6 a0 with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide +revert +kernel

theorem valid_e_back_10 : e_back_10.SatisfiedBy table.semigroup := by
  intro valuation
  exact pointwise_e_back_10 (valuation 0) (valuation 1) (valuation 3)

theorem derives_e_back_10 : Derives basis e_back_10.lhs e_back_10.rhs :=
  Derives.fromBasis (by decide : e_back_10 ∈ basis)

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.pointwise_e_back_10
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.valid_e_back_10
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.derives_e_back_10

theorem pointwise_e_back_11 (a0 a1 a2 a3 : Fin 6) :
    (table.mul (table.mul (table.mul (table.mul (table.mul a0 a2) a1) a3) a0) a1) = (table.mul (table.mul (table.mul (table.mul (table.mul a0 a2) a1) a3) a1) a0) := by
  rcases cases6 a0 with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rcases cases6 a1 with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide +revert +kernel

theorem valid_e_back_11 : e_back_11.SatisfiedBy table.semigroup := by
  intro valuation
  exact pointwise_e_back_11 (valuation 0) (valuation 1) (valuation 2) (valuation 3)

theorem derives_e_back_11 : Derives basis e_back_11.lhs e_back_11.rhs :=
  Derives.fromBasis (by decide : e_back_11 ∈ basis)

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.pointwise_e_back_11
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.valid_e_back_11
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.derives_e_back_11

theorem pointwise_e_front_00 (a0 a1 : Fin 6) :
    (table.mul (table.mul (table.mul a0 a1) a0) a1) = (table.mul (table.mul (table.mul a1 a0) a0) a1) := by
  rcases cases6 a0 with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide +revert +kernel

theorem valid_e_front_00 : e_front_00.SatisfiedBy table.semigroup := by
  intro valuation
  exact pointwise_e_front_00 (valuation 0) (valuation 1)

theorem derives_e_front_00 : Derives basis e_front_00.lhs e_front_00.rhs :=
  Derives.fromBasis (by decide : e_front_00 ∈ basis)

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.pointwise_e_front_00
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.valid_e_front_00
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.derives_e_front_00

theorem pointwise_e_front_01 (a0 a1 a2 : Fin 6) :
    (table.mul (table.mul (table.mul (table.mul a0 a2) a1) a0) a1) = (table.mul (table.mul (table.mul (table.mul a1 a2) a0) a0) a1) := by
  rcases cases6 a0 with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide +revert +kernel

theorem valid_e_front_01 : e_front_01.SatisfiedBy table.semigroup := by
  intro valuation
  exact pointwise_e_front_01 (valuation 0) (valuation 1) (valuation 2)

theorem derives_e_front_01 : Derives basis e_front_01.lhs e_front_01.rhs :=
  Derives.fromBasis (by decide : e_front_01 ∈ basis)

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.pointwise_e_front_01
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.valid_e_front_01
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.derives_e_front_01

theorem pointwise_e_front_10 (a0 a1 a3 : Fin 6) :
    (table.mul (table.mul (table.mul (table.mul a0 a1) a3) a0) a1) = (table.mul (table.mul (table.mul (table.mul a1 a0) a3) a0) a1) := by
  rcases cases6 a0 with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide +revert +kernel

theorem valid_e_front_10 : e_front_10.SatisfiedBy table.semigroup := by
  intro valuation
  exact pointwise_e_front_10 (valuation 0) (valuation 1) (valuation 3)

theorem derives_e_front_10 : Derives basis e_front_10.lhs e_front_10.rhs :=
  Derives.fromBasis (by decide : e_front_10 ∈ basis)

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.pointwise_e_front_10
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.valid_e_front_10
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.derives_e_front_10

theorem pointwise_e_front_11 (a0 a1 a2 a3 : Fin 6) :
    (table.mul (table.mul (table.mul (table.mul (table.mul a0 a2) a1) a3) a0) a1) = (table.mul (table.mul (table.mul (table.mul (table.mul a1 a2) a0) a3) a0) a1) := by
  rcases cases6 a0 with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rcases cases6 a1 with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide +revert +kernel

theorem valid_e_front_11 : e_front_11.SatisfiedBy table.semigroup := by
  intro valuation
  exact pointwise_e_front_11 (valuation 0) (valuation 1) (valuation 2) (valuation 3)

theorem derives_e_front_11 : Derives basis e_front_11.lhs e_front_11.rhs :=
  Derives.fromBasis (by decide : e_front_11 ∈ basis)

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.pointwise_e_front_11
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.valid_e_front_11
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.derives_e_front_11

theorem pointwise_f_right_00 (a0 a1 : Fin 6) :
    (table.mul (table.mul (table.mul (table.mul a0 a1) a1) a0) a1) = (table.mul (table.mul (table.mul (table.mul a0 a1) a1) a0) a0) := by
  rcases cases6 a0 with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide +revert +kernel

theorem valid_f_right_00 : f_right_00.SatisfiedBy table.semigroup := by
  intro valuation
  exact pointwise_f_right_00 (valuation 0) (valuation 1)

theorem derives_f_right_00 : Derives basis f_right_00.lhs f_right_00.rhs :=
  Derives.fromBasis (by decide : f_right_00 ∈ basis)

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.pointwise_f_right_00
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.valid_f_right_00
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.derives_f_right_00

theorem pointwise_f_right_01 (a0 a1 a2 : Fin 6) :
    (table.mul (table.mul (table.mul (table.mul (table.mul a0 a2) a1) a1) a0) a1) = (table.mul (table.mul (table.mul (table.mul (table.mul a0 a2) a1) a1) a0) a0) := by
  rcases cases6 a0 with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide +revert +kernel

theorem valid_f_right_01 : f_right_01.SatisfiedBy table.semigroup := by
  intro valuation
  exact pointwise_f_right_01 (valuation 0) (valuation 1) (valuation 2)

theorem derives_f_right_01 : Derives basis f_right_01.lhs f_right_01.rhs :=
  Derives.fromBasis (by decide : f_right_01 ∈ basis)

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.pointwise_f_right_01
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.valid_f_right_01
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.derives_f_right_01

theorem pointwise_f_right_10 (a0 a1 a3 : Fin 6) :
    (table.mul (table.mul (table.mul (table.mul (table.mul a0 a1) a1) a0) a3) a1) = (table.mul (table.mul (table.mul (table.mul (table.mul a0 a1) a1) a0) a3) a0) := by
  rcases cases6 a0 with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide +revert +kernel

theorem valid_f_right_10 : f_right_10.SatisfiedBy table.semigroup := by
  intro valuation
  exact pointwise_f_right_10 (valuation 0) (valuation 1) (valuation 3)

theorem derives_f_right_10 : Derives basis f_right_10.lhs f_right_10.rhs :=
  Derives.fromBasis (by decide : f_right_10 ∈ basis)

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.pointwise_f_right_10
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.valid_f_right_10
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.derives_f_right_10

theorem pointwise_f_right_11 (a0 a1 a2 a3 : Fin 6) :
    (table.mul (table.mul (table.mul (table.mul (table.mul (table.mul a0 a2) a1) a1) a0) a3) a1) = (table.mul (table.mul (table.mul (table.mul (table.mul (table.mul a0 a2) a1) a1) a0) a3) a0) := by
  rcases cases6 a0 with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rcases cases6 a1 with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide +revert +kernel

theorem valid_f_right_11 : f_right_11.SatisfiedBy table.semigroup := by
  intro valuation
  exact pointwise_f_right_11 (valuation 0) (valuation 1) (valuation 2) (valuation 3)

theorem derives_f_right_11 : Derives basis f_right_11.lhs f_right_11.rhs :=
  Derives.fromBasis (by decide : f_right_11 ∈ basis)

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.pointwise_f_right_11
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.valid_f_right_11
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.derives_f_right_11

theorem pointwise_f_left_00 (a0 a1 : Fin 6) :
    (table.mul (table.mul (table.mul (table.mul a1 a0) a1) a1) a0) = (table.mul (table.mul (table.mul (table.mul a0 a0) a1) a1) a0) := by
  rcases cases6 a0 with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide +revert +kernel

theorem valid_f_left_00 : f_left_00.SatisfiedBy table.semigroup := by
  intro valuation
  exact pointwise_f_left_00 (valuation 0) (valuation 1)

theorem derives_f_left_00 : Derives basis f_left_00.lhs f_left_00.rhs :=
  Derives.fromBasis (by decide : f_left_00 ∈ basis)

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.pointwise_f_left_00
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.valid_f_left_00
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.derives_f_left_00

theorem pointwise_f_left_01 (a0 a1 a2 : Fin 6) :
    (table.mul (table.mul (table.mul (table.mul (table.mul a1 a2) a0) a1) a1) a0) = (table.mul (table.mul (table.mul (table.mul (table.mul a0 a2) a0) a1) a1) a0) := by
  rcases cases6 a0 with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide +revert +kernel

theorem valid_f_left_01 : f_left_01.SatisfiedBy table.semigroup := by
  intro valuation
  exact pointwise_f_left_01 (valuation 0) (valuation 1) (valuation 2)

theorem derives_f_left_01 : Derives basis f_left_01.lhs f_left_01.rhs :=
  Derives.fromBasis (by decide : f_left_01 ∈ basis)

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.pointwise_f_left_01
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.valid_f_left_01
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.derives_f_left_01

theorem pointwise_f_left_10 (a0 a1 a3 : Fin 6) :
    (table.mul (table.mul (table.mul (table.mul (table.mul a1 a0) a3) a1) a1) a0) = (table.mul (table.mul (table.mul (table.mul (table.mul a0 a0) a3) a1) a1) a0) := by
  rcases cases6 a0 with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide +revert +kernel

theorem valid_f_left_10 : f_left_10.SatisfiedBy table.semigroup := by
  intro valuation
  exact pointwise_f_left_10 (valuation 0) (valuation 1) (valuation 3)

theorem derives_f_left_10 : Derives basis f_left_10.lhs f_left_10.rhs :=
  Derives.fromBasis (by decide : f_left_10 ∈ basis)

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.pointwise_f_left_10
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.valid_f_left_10
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.derives_f_left_10

theorem pointwise_f_left_11 (a0 a1 a2 a3 : Fin 6) :
    (table.mul (table.mul (table.mul (table.mul (table.mul (table.mul a1 a2) a0) a3) a1) a1) a0) = (table.mul (table.mul (table.mul (table.mul (table.mul (table.mul a0 a2) a0) a3) a1) a1) a0) := by
  rcases cases6 a0 with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rcases cases6 a1 with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide +revert +kernel

theorem valid_f_left_11 : f_left_11.SatisfiedBy table.semigroup := by
  intro valuation
  exact pointwise_f_left_11 (valuation 0) (valuation 1) (valuation 2) (valuation 3)

theorem derives_f_left_11 : Derives basis f_left_11.lhs f_left_11.rhs :=
  Derives.fromBasis (by decide : f_left_11 ∈ basis)

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.pointwise_f_left_11
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.valid_f_left_11
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.derives_f_left_11

theorem pointwise_f_middle_00 (a0 a1 : Fin 6) :
    (table.mul (table.mul (table.mul (table.mul a0 a1) a1) a1) a0) = (table.mul (table.mul (table.mul (table.mul a0 a0) a1) a1) a0) := by
  rcases cases6 a0 with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide +revert +kernel

theorem valid_f_middle_00 : f_middle_00.SatisfiedBy table.semigroup := by
  intro valuation
  exact pointwise_f_middle_00 (valuation 0) (valuation 1)

theorem derives_f_middle_00 : Derives basis f_middle_00.lhs f_middle_00.rhs :=
  Derives.fromBasis (by decide : f_middle_00 ∈ basis)

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.pointwise_f_middle_00
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.valid_f_middle_00
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.derives_f_middle_00

theorem pointwise_f_middle_01 (a0 a1 a2 : Fin 6) :
    (table.mul (table.mul (table.mul (table.mul (table.mul a0 a2) a1) a1) a1) a0) = (table.mul (table.mul (table.mul (table.mul (table.mul a0 a2) a0) a1) a1) a0) := by
  rcases cases6 a0 with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide +revert +kernel

theorem valid_f_middle_01 : f_middle_01.SatisfiedBy table.semigroup := by
  intro valuation
  exact pointwise_f_middle_01 (valuation 0) (valuation 1) (valuation 2)

theorem derives_f_middle_01 : Derives basis f_middle_01.lhs f_middle_01.rhs :=
  Derives.fromBasis (by decide : f_middle_01 ∈ basis)

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.pointwise_f_middle_01
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.valid_f_middle_01
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.derives_f_middle_01

theorem pointwise_f_middle_10 (a0 a1 a3 : Fin 6) :
    (table.mul (table.mul (table.mul (table.mul (table.mul a0 a1) a3) a1) a1) a0) = (table.mul (table.mul (table.mul (table.mul (table.mul a0 a0) a3) a1) a1) a0) := by
  rcases cases6 a0 with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide +revert +kernel

theorem valid_f_middle_10 : f_middle_10.SatisfiedBy table.semigroup := by
  intro valuation
  exact pointwise_f_middle_10 (valuation 0) (valuation 1) (valuation 3)

theorem derives_f_middle_10 : Derives basis f_middle_10.lhs f_middle_10.rhs :=
  Derives.fromBasis (by decide : f_middle_10 ∈ basis)

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.pointwise_f_middle_10
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.valid_f_middle_10
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.derives_f_middle_10

theorem pointwise_f_middle_11 (a0 a1 a2 a3 : Fin 6) :
    (table.mul (table.mul (table.mul (table.mul (table.mul (table.mul a0 a2) a1) a3) a1) a1) a0) = (table.mul (table.mul (table.mul (table.mul (table.mul (table.mul a0 a2) a0) a3) a1) a1) a0) := by
  rcases cases6 a0 with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rcases cases6 a1 with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide +revert +kernel

theorem valid_f_middle_11 : f_middle_11.SatisfiedBy table.semigroup := by
  intro valuation
  exact pointwise_f_middle_11 (valuation 0) (valuation 1) (valuation 2) (valuation 3)

theorem derives_f_middle_11 : Derives basis f_middle_11.lhs f_middle_11.rhs :=
  Derives.fromBasis (by decide : f_middle_11 ∈ basis)

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.pointwise_f_middle_11
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.valid_f_middle_11
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.derives_f_middle_11

theorem models : Models table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact valid_a_cube
  · exact valid_a_left
  · exact valid_a_right
  · exact valid_b_exchange
  · exact valid_c_000
  · exact valid_c_001
  · exact valid_c_010
  · exact valid_c_011
  · exact valid_c_100
  · exact valid_c_101
  · exact valid_c_110
  · exact valid_c_111
  · exact valid_d_left_0
  · exact valid_d_left_1
  · exact valid_d_right_00
  · exact valid_d_right_01
  · exact valid_d_right_10
  · exact valid_d_right_11
  · exact valid_e_back_00
  · exact valid_e_back_01
  · exact valid_e_back_10
  · exact valid_e_back_11
  · exact valid_e_front_00
  · exact valid_e_front_01
  · exact valid_e_front_10
  · exact valid_e_front_11
  · exact valid_f_right_00
  · exact valid_f_right_01
  · exact valid_f_right_10
  · exact valid_f_right_11
  · exact valid_f_left_00
  · exact valid_f_left_01
  · exact valid_f_left_10
  · exact valid_f_left_11
  · exact valid_f_middle_00
  · exact valid_f_middle_01
  · exact valid_f_middle_10
  · exact valid_f_middle_11

end SemigroupBasis.CoRoots.Order6SporadicSection19.Published

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.basis_length
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.basis_exact
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.models
