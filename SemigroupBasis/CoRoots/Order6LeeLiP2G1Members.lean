import SemigroupBasis.CoRoots.Order6LeeLiP2G1Injection

/-!
# G1 order-six member endpoints

The tables are the orientation-frozen records from Fable message 0052.  Every
member endpoint uses the shared all-variable G1 bridge; the only per-member
obligations are associativity, the two basis laws, and the executable
four-variable canonical-separation sweep.
-/

namespace SemigroupBasis.CoRoots.Order6LeeLiP2G1.Members

open SemigroupBasis
open SemigroupBasis.CoRoots.Order6LeeLiP2G1

private def finiteMul (rows : List (List Nat)) (a b : Fin 6) : Fin 6 :=
  ⟨((rows.getD a.val []).getD b.val 0) % 6, Nat.mod_lt _ (by decide)⟩

namespace S6_3393

def rows : List (List Nat) :=
  [[0, 0, 0, 0, 4, 5],
   [0, 0, 0, 0, 4, 5],
   [0, 0, 0, 1, 4, 5],
   [0, 0, 0, 0, 4, 5],
   [0, 0, 0, 0, 4, 5],
   [0, 0, 0, 4, 4, 5]]

def table : FiniteTable where
  order := 6
  mul := finiteMul rows
  assoc := by decide

def semigroup : Semigroup (Fin 6) := table.semigroup

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem basisFor : BasisFor semigroup basis :=
  Injection.basisFor_of_checks table (by decide) (by decide)

end S6_3393

namespace S6_3557

def rows : List (List Nat) :=
  [[0, 0, 0, 0, 4, 5],
   [0, 0, 0, 0, 4, 5],
   [0, 0, 0, 1, 4, 5],
   [0, 0, 0, 0, 4, 5],
   [0, 0, 0, 0, 4, 5],
   [0, 0, 4, 0, 4, 5]]

def table : FiniteTable where
  order := 6
  mul := finiteMul rows
  assoc := by decide

def semigroup : Semigroup (Fin 6) := table.semigroup

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem basisFor : BasisFor semigroup basis :=
  Injection.basisFor_of_checks table (by decide) (by decide)

end S6_3557

namespace S6_3558

def rows : List (List Nat) :=
  [[0, 0, 0, 0, 4, 5],
   [0, 0, 0, 0, 4, 5],
   [0, 0, 0, 1, 4, 5],
   [0, 0, 0, 0, 4, 5],
   [0, 0, 0, 0, 4, 5],
   [0, 0, 4, 4, 4, 5]]

def table : FiniteTable where
  order := 6
  mul := finiteMul rows
  assoc := by decide

def semigroup : Semigroup (Fin 6) := table.semigroup

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem basisFor : BasisFor semigroup basis :=
  Injection.basisFor_of_checks table (by decide) (by decide)

end S6_3558

namespace S6_3625

def rows : List (List Nat) :=
  [[0, 0, 0, 0, 4, 5],
   [0, 0, 0, 0, 4, 5],
   [0, 0, 0, 1, 4, 5],
   [0, 0, 1, 0, 4, 5],
   [0, 0, 0, 0, 4, 5],
   [0, 0, 0, 4, 4, 5]]

def table : FiniteTable where
  order := 6
  mul := finiteMul rows
  assoc := by decide

def semigroup : Semigroup (Fin 6) := table.semigroup

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem basisFor : BasisFor semigroup basis :=
  Injection.basisFor_of_checks table (by decide) (by decide)

end S6_3625

namespace S6_3626

def rows : List (List Nat) :=
  [[0, 0, 0, 0, 4, 5],
   [0, 0, 0, 0, 4, 5],
   [0, 0, 0, 1, 4, 5],
   [0, 0, 1, 0, 4, 5],
   [0, 0, 0, 0, 4, 5],
   [0, 0, 4, 4, 4, 5]]

def table : FiniteTable where
  order := 6
  mul := finiteMul rows
  assoc := by decide

def semigroup : Semigroup (Fin 6) := table.semigroup

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem basisFor : BasisFor semigroup basis :=
  Injection.basisFor_of_checks table (by decide) (by decide)

end S6_3626

namespace S6_6172

def rows : List (List Nat) :=
  [[0, 0, 0, 3, 3, 5],
   [0, 0, 0, 3, 3, 5],
   [0, 0, 0, 3, 3, 5],
   [0, 0, 0, 3, 3, 5],
   [0, 0, 1, 3, 3, 5],
   [0, 0, 0, 3, 0, 5]]

def table : FiniteTable where
  order := 6
  mul := finiteMul rows
  assoc := by decide

def semigroup : Semigroup (Fin 6) := table.semigroup

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem basisFor : BasisFor semigroup basis :=
  Injection.basisFor_of_checks table (by decide) (by decide)

end S6_6172

namespace S6_6180

def rows : List (List Nat) :=
  [[0, 0, 0, 3, 5, 5],
   [0, 0, 0, 3, 5, 5],
   [0, 0, 0, 3, 5, 5],
   [0, 0, 0, 3, 3, 5],
   [0, 0, 1, 3, 3, 5],
   [0, 0, 0, 3, 3, 5]]

def table : FiniteTable where
  order := 6
  mul := finiteMul rows
  assoc := by decide

def semigroup : Semigroup (Fin 6) := table.semigroup

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem basisFor : BasisFor semigroup basis :=
  Injection.basisFor_of_checks table (by decide) (by decide)

end S6_6180

namespace S6_6187

def rows : List (List Nat) :=
  [[0, 0, 0, 3, 3, 5],
   [0, 0, 0, 3, 3, 5],
   [0, 0, 0, 3, 3, 5],
   [0, 0, 0, 3, 3, 5],
   [0, 0, 1, 3, 3, 5],
   [0, 0, 3, 3, 0, 5]]

def table : FiniteTable where
  order := 6
  mul := finiteMul rows
  assoc := by decide

def semigroup : Semigroup (Fin 6) := table.semigroup

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem basisFor : BasisFor semigroup basis :=
  Injection.basisFor_of_checks table (by decide) (by decide)

end S6_6187

namespace S6_6188

def rows : List (List Nat) :=
  [[0, 0, 0, 3, 3, 5],
   [0, 0, 0, 3, 3, 5],
   [0, 0, 0, 3, 3, 5],
   [0, 0, 0, 3, 3, 5],
   [0, 0, 1, 3, 3, 5],
   [0, 0, 3, 3, 3, 5]]

def table : FiniteTable where
  order := 6
  mul := finiteMul rows
  assoc := by decide

def semigroup : Semigroup (Fin 6) := table.semigroup

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem basisFor : BasisFor semigroup basis :=
  Injection.basisFor_of_checks table (by decide) (by decide)

end S6_6188

namespace S6_9884

def rows : List (List Nat) :=
  [[0, 0, 2, 2, 4, 4],
   [0, 0, 2, 2, 4, 4],
   [0, 0, 2, 2, 4, 4],
   [0, 0, 2, 2, 4, 4],
   [0, 0, 2, 0, 4, 4],
   [0, 0, 2, 1, 4, 4]]

def table : FiniteTable where
  order := 6
  mul := finiteMul rows
  assoc := by decide

def semigroup : Semigroup (Fin 6) := table.semigroup

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem basisFor : BasisFor semigroup basis :=
  Injection.basisFor_of_checks table (by decide) (by decide)

end S6_9884

end SemigroupBasis.CoRoots.Order6LeeLiP2G1.Members
