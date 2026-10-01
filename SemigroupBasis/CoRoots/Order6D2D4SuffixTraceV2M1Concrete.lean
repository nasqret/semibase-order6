import SemigroupBasis.CoRoots.Order6D2D4SuffixTraceTargets

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6D2D4SuffixTrace.V2

open SemigroupBasis
open SemigroupBasis.CoRoots.Order6D2D4SuffixTrace

/-!
# Step-2 v2 M1: closed D2/D4 detector transitions

The paper valuation uses the zero-based states `2`, `4`, and `5`.  These
lemmas are the only representation boundary used by the later fold proof.
Every computation below is closed before `decide` is invoked; no generated
table helper or equation theorem is exposed to downstream modules.
-/

abbrev d2G : Semigroup (Fin 6) := d2Table.semigroup

abbrev d4G : Semigroup (Fin 6) := d4Table.semigroup

abbrev d2op (left right : Fin 6) : Fin 6 :=
  d2G.mul left right

abbrev d4op (left right : Fin 6) : Fin 6 :=
  d4G.mul left right

theorem d2_mul_0_2 : d2G.mul (0 : Fin 6) (2 : Fin 6) = (0 : Fin 6) := by decide
theorem d2_mul_0_4 : d2G.mul (0 : Fin 6) (4 : Fin 6) = (0 : Fin 6) := by decide
theorem d2_mul_0_5 : d2G.mul (0 : Fin 6) (5 : Fin 6) = (0 : Fin 6) := by decide
theorem d2_mul_1_2 : d2G.mul (1 : Fin 6) (2 : Fin 6) = (0 : Fin 6) := by decide
theorem d2_mul_1_4 : d2G.mul (1 : Fin 6) (4 : Fin 6) = (0 : Fin 6) := by decide
theorem d2_mul_1_5 : d2G.mul (1 : Fin 6) (5 : Fin 6) = (1 : Fin 6) := by decide
theorem d2_mul_2_2 : d2G.mul (2 : Fin 6) (2 : Fin 6) = (0 : Fin 6) := by decide
theorem d2_mul_2_4 : d2G.mul (2 : Fin 6) (4 : Fin 6) = (1 : Fin 6) := by decide
theorem d2_mul_2_5 : d2G.mul (2 : Fin 6) (5 : Fin 6) = (0 : Fin 6) := by decide
theorem d2_mul_3_2 : d2G.mul (3 : Fin 6) (2 : Fin 6) = (2 : Fin 6) := by decide
theorem d2_mul_3_4 : d2G.mul (3 : Fin 6) (4 : Fin 6) = (3 : Fin 6) := by decide
theorem d2_mul_3_5 : d2G.mul (3 : Fin 6) (5 : Fin 6) = (3 : Fin 6) := by decide
theorem d2_mul_4_2 : d2G.mul (4 : Fin 6) (2 : Fin 6) = (2 : Fin 6) := by decide
theorem d2_mul_4_4 : d2G.mul (4 : Fin 6) (4 : Fin 6) = (3 : Fin 6) := by decide
theorem d2_mul_4_5 : d2G.mul (4 : Fin 6) (5 : Fin 6) = (4 : Fin 6) := by decide
theorem d2_mul_5_2 : d2G.mul (5 : Fin 6) (2 : Fin 6) = (2 : Fin 6) := by decide
theorem d2_mul_5_4 : d2G.mul (5 : Fin 6) (4 : Fin 6) = (3 : Fin 6) := by decide
theorem d2_mul_5_5 : d2G.mul (5 : Fin 6) (5 : Fin 6) = (5 : Fin 6) := by decide

theorem d4_mul_0_2 : d4G.mul (0 : Fin 6) (2 : Fin 6) = (0 : Fin 6) := by decide
theorem d4_mul_0_4 : d4G.mul (0 : Fin 6) (4 : Fin 6) = (0 : Fin 6) := by decide
theorem d4_mul_0_5 : d4G.mul (0 : Fin 6) (5 : Fin 6) = (0 : Fin 6) := by decide
theorem d4_mul_1_2 : d4G.mul (1 : Fin 6) (2 : Fin 6) = (0 : Fin 6) := by decide
theorem d4_mul_1_4 : d4G.mul (1 : Fin 6) (4 : Fin 6) = (0 : Fin 6) := by decide
theorem d4_mul_1_5 : d4G.mul (1 : Fin 6) (5 : Fin 6) = (1 : Fin 6) := by decide
theorem d4_mul_2_2 : d4G.mul (2 : Fin 6) (2 : Fin 6) = (0 : Fin 6) := by decide
theorem d4_mul_2_4 : d4G.mul (2 : Fin 6) (4 : Fin 6) = (1 : Fin 6) := by decide
theorem d4_mul_2_5 : d4G.mul (2 : Fin 6) (5 : Fin 6) = (1 : Fin 6) := by decide
theorem d4_mul_3_2 : d4G.mul (3 : Fin 6) (2 : Fin 6) = (2 : Fin 6) := by decide
theorem d4_mul_3_4 : d4G.mul (3 : Fin 6) (4 : Fin 6) = (3 : Fin 6) := by decide
theorem d4_mul_3_5 : d4G.mul (3 : Fin 6) (5 : Fin 6) = (3 : Fin 6) := by decide
theorem d4_mul_4_2 : d4G.mul (4 : Fin 6) (2 : Fin 6) = (2 : Fin 6) := by decide
theorem d4_mul_4_4 : d4G.mul (4 : Fin 6) (4 : Fin 6) = (3 : Fin 6) := by decide
theorem d4_mul_4_5 : d4G.mul (4 : Fin 6) (5 : Fin 6) = (4 : Fin 6) := by decide
theorem d4_mul_5_2 : d4G.mul (5 : Fin 6) (2 : Fin 6) = (2 : Fin 6) := by decide
theorem d4_mul_5_4 : d4G.mul (5 : Fin 6) (4 : Fin 6) = (3 : Fin 6) := by decide
theorem d4_mul_5_5 : d4G.mul (5 : Fin 6) (5 : Fin 6) = (5 : Fin 6) := by decide

end SemigroupBasis.CoRoots.Order6D2D4SuffixTrace.V2
