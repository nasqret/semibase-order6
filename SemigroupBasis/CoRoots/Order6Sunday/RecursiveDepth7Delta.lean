import SemigroupBasis.CoRoots.Order6Sunday.RecursivePublishedFinite

/-! Only new fixed msg0458 table obligations. The recorded parent is reused.
No unrestricted completeness, recursive-key or separation field is supplied. -/

namespace SemigroupBasis.CoRoots.Order6Sunday.RecursiveDepth7Delta

open SemigroupBasis

namespace S6_9726

private abbrev mul := SemigroupBasis.CoRoots.Order6Sunday.RecursivePublishedFinite.S6_9726.mul

def addedLaw0 : Identity Nat := ⟨⟨0, [1, 2, 3, 0, 2]⟩, ⟨0, [1, 2, 3, 2, 0]⟩⟩

def added : List (Identity Nat) :=
  [addedLaw0]

def basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6Sunday.RecursivePublishedFinite.S6_9726.basis ++ added

private theorem law0At0 (b c d : Fin 6) :
    mul (mul (mul (mul (mul (0) (b)) (c)) (d)) (0)) (c) = mul (mul (mul (mul (mul (0) (b)) (c)) (d)) (c)) (0) := by
  decide +revert

private theorem law0At1 (b c d : Fin 6) :
    mul (mul (mul (mul (mul (1) (b)) (c)) (d)) (1)) (c) = mul (mul (mul (mul (mul (1) (b)) (c)) (d)) (c)) (1) := by
  decide +revert

private theorem law0At2 (b c d : Fin 6) :
    mul (mul (mul (mul (mul (2) (b)) (c)) (d)) (2)) (c) = mul (mul (mul (mul (mul (2) (b)) (c)) (d)) (c)) (2) := by
  decide +revert

private theorem law0At3 (b c d : Fin 6) :
    mul (mul (mul (mul (mul (3) (b)) (c)) (d)) (3)) (c) = mul (mul (mul (mul (mul (3) (b)) (c)) (d)) (c)) (3) := by
  decide +revert

private theorem law0At4 (b c d : Fin 6) :
    mul (mul (mul (mul (mul (4) (b)) (c)) (d)) (4)) (c) = mul (mul (mul (mul (mul (4) (b)) (c)) (d)) (c)) (4) := by
  decide +revert

private theorem law0At5 (b c d : Fin 6) :
    mul (mul (mul (mul (mul (5) (b)) (c)) (d)) (5)) (c) = mul (mul (mul (mul (mul (5) (b)) (c)) (d)) (c)) (5) := by
  decide +revert

private theorem law0Values (a b c d : Fin 6) :
    mul (mul (mul (mul (mul (a) (b)) (c)) (d)) (a)) (c) = mul (mul (mul (mul (mul (a) (b)) (c)) (d)) (c)) (a) := by
  exact Fin.cases (law0At0 b c d) (fun a => Fin.cases (law0At1 b c d) (fun a => Fin.cases (law0At2 b c d) (fun a => Fin.cases (law0At3 b c d) (fun a => Fin.cases (law0At4 b c d) (fun a => Fin.cases (law0At5 b c d) (fun a => Fin.elim0 a) a) a) a) a) a) a

theorem addedLaw0Valid : addedLaw0.SatisfiedBy SemigroupBasis.CoRoots.Order6Sunday.RecursivePublishedFinite.S6_9726.table.semigroup := by
  intro valuation
  change mul (mul (mul (mul (mul (valuation 0) (valuation 1)) (valuation 2)) (valuation 3)) (valuation 0)) (valuation 2) = mul (mul (mul (mul (mul (valuation 0) (valuation 1)) (valuation 2)) (valuation 3)) (valuation 2)) (valuation 0)
  exact law0Values (valuation 0) (valuation 1) (valuation 2) (valuation 3)

theorem addedLaw0OppositeValid :
    addedLaw0.reversed.SatisfiedBy SemigroupBasis.CoRoots.Order6Sunday.RecursivePublishedFinite.S6_9726.table.semigroup.opposite := by
  rw [Identity.satisfiedBy_opposite_iff_reversed, Identity.reversed_reversed]
  exact addedLaw0Valid

/-- Extend the recorded finite list by just the newly approved fixed laws. -/
theorem tableModels : Models SemigroupBasis.CoRoots.Order6Sunday.RecursivePublishedFinite.S6_9726.table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_append] at member
  rcases member with old | extra
  · exact SemigroupBasis.CoRoots.Order6Sunday.RecursivePublishedFinite.S6_9726.tableModels identity old
  · simp only [added, List.mem_cons, List.not_mem_nil, or_false] at extra
    subst identity
    exact addedLaw0Valid

theorem oppositeModels : Models SemigroupBasis.CoRoots.Order6Sunday.RecursivePublishedFinite.S6_9726.table.semigroup.opposite (reversedBasis basis) :=
  tableModels.oppositeReversed

def rejectedInnerLaw0 : Identity Nat := ⟨⟨0, [1, 0, 2, 3, 2]⟩, ⟨0, [1, 2, 0, 3, 2]⟩⟩
def rejectedInnerLaw1 : Identity Nat := ⟨⟨2, [1, 0, 2, 3, 0]⟩, ⟨2, [1, 2, 0, 3, 0]⟩⟩

def rejectedInner : List (Identity Nat) :=
  [rejectedInnerLaw0, rejectedInnerLaw1]

private def rejectedValuation0 : Nat → Fin 6
  | 0 => 2
  | 1 => 5
  | 2 => 4
  | 3 => 0
  | _ => 0

/-- Fixed countervaluation for the already reported incompatible inner swap. -/
theorem rejectedInner0NotValid : ¬ rejectedInnerLaw0.SatisfiedBy SemigroupBasis.CoRoots.Order6Sunday.RecursivePublishedFinite.S6_9726.table.semigroup := by
  intro valid
  have ne : SemigroupBasis.CoRoots.Order6Sunday.RecursivePublishedFinite.S6_9726.table.semigroup.eval rejectedValuation0 rejectedInnerLaw0.lhs ≠
      SemigroupBasis.CoRoots.Order6Sunday.RecursivePublishedFinite.S6_9726.table.semigroup.eval rejectedValuation0 rejectedInnerLaw0.rhs := by decide
  exact ne (valid rejectedValuation0)

theorem rejectedInner0OppositeNotValid :
    ¬ rejectedInnerLaw0.reversed.SatisfiedBy SemigroupBasis.CoRoots.Order6Sunday.RecursivePublishedFinite.S6_9726.table.semigroup.opposite := by
  intro valid
  rw [Identity.satisfiedBy_opposite_iff_reversed, Identity.reversed_reversed] at valid
  exact rejectedInner0NotValid valid

private def rejectedValuation1 : Nat → Fin 6
  | 0 => 4
  | 1 => 5
  | 2 => 2
  | 3 => 0
  | _ => 0

/-- Fixed countervaluation for the already reported incompatible inner swap. -/
theorem rejectedInner1NotValid : ¬ rejectedInnerLaw1.SatisfiedBy SemigroupBasis.CoRoots.Order6Sunday.RecursivePublishedFinite.S6_9726.table.semigroup := by
  intro valid
  have ne : SemigroupBasis.CoRoots.Order6Sunday.RecursivePublishedFinite.S6_9726.table.semigroup.eval rejectedValuation1 rejectedInnerLaw1.lhs ≠
      SemigroupBasis.CoRoots.Order6Sunday.RecursivePublishedFinite.S6_9726.table.semigroup.eval rejectedValuation1 rejectedInnerLaw1.rhs := by decide
  exact ne (valid rejectedValuation1)

theorem rejectedInner1OppositeNotValid :
    ¬ rejectedInnerLaw1.reversed.SatisfiedBy SemigroupBasis.CoRoots.Order6Sunday.RecursivePublishedFinite.S6_9726.table.semigroup.opposite := by
  intro valid
  rw [Identity.satisfiedBy_opposite_iff_reversed, Identity.reversed_reversed] at valid
  exact rejectedInner1NotValid valid

end S6_9726

namespace S6_6447

private abbrev mul := SemigroupBasis.CoRoots.Order6Sunday.RecursivePublishedFinite.S6_6447.mul

def addedLaw0 : Identity Nat := ⟨⟨0, [1, 0, 2, 3, 2]⟩, ⟨0, [1, 2, 0, 3, 2]⟩⟩
def addedLaw1 : Identity Nat := ⟨⟨2, [1, 0, 2, 3, 0]⟩, ⟨2, [1, 2, 0, 3, 0]⟩⟩
def addedLaw2 : Identity Nat := ⟨⟨0, [1, 2, 3, 0, 2]⟩, ⟨0, [1, 2, 3, 2, 0]⟩⟩

def added : List (Identity Nat) :=
  [addedLaw0, addedLaw1, addedLaw2]

def basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6Sunday.RecursivePublishedFinite.S6_6447.basis ++ added

private theorem law0At0 (b c d : Fin 6) :
    mul (mul (mul (mul (mul (0) (b)) (0)) (c)) (d)) (c) = mul (mul (mul (mul (mul (0) (b)) (c)) (0)) (d)) (c) := by
  decide +revert

private theorem law0At1 (b c d : Fin 6) :
    mul (mul (mul (mul (mul (1) (b)) (1)) (c)) (d)) (c) = mul (mul (mul (mul (mul (1) (b)) (c)) (1)) (d)) (c) := by
  decide +revert

private theorem law0At2 (b c d : Fin 6) :
    mul (mul (mul (mul (mul (2) (b)) (2)) (c)) (d)) (c) = mul (mul (mul (mul (mul (2) (b)) (c)) (2)) (d)) (c) := by
  decide +revert

private theorem law0At3 (b c d : Fin 6) :
    mul (mul (mul (mul (mul (3) (b)) (3)) (c)) (d)) (c) = mul (mul (mul (mul (mul (3) (b)) (c)) (3)) (d)) (c) := by
  decide +revert

private theorem law0At4 (b c d : Fin 6) :
    mul (mul (mul (mul (mul (4) (b)) (4)) (c)) (d)) (c) = mul (mul (mul (mul (mul (4) (b)) (c)) (4)) (d)) (c) := by
  decide +revert

private theorem law0At5 (b c d : Fin 6) :
    mul (mul (mul (mul (mul (5) (b)) (5)) (c)) (d)) (c) = mul (mul (mul (mul (mul (5) (b)) (c)) (5)) (d)) (c) := by
  decide +revert

private theorem law0Values (a b c d : Fin 6) :
    mul (mul (mul (mul (mul (a) (b)) (a)) (c)) (d)) (c) = mul (mul (mul (mul (mul (a) (b)) (c)) (a)) (d)) (c) := by
  exact Fin.cases (law0At0 b c d) (fun a => Fin.cases (law0At1 b c d) (fun a => Fin.cases (law0At2 b c d) (fun a => Fin.cases (law0At3 b c d) (fun a => Fin.cases (law0At4 b c d) (fun a => Fin.cases (law0At5 b c d) (fun a => Fin.elim0 a) a) a) a) a) a) a

theorem addedLaw0Valid : addedLaw0.SatisfiedBy SemigroupBasis.CoRoots.Order6Sunday.RecursivePublishedFinite.S6_6447.table.semigroup := by
  intro valuation
  change mul (mul (mul (mul (mul (valuation 0) (valuation 1)) (valuation 0)) (valuation 2)) (valuation 3)) (valuation 2) = mul (mul (mul (mul (mul (valuation 0) (valuation 1)) (valuation 2)) (valuation 0)) (valuation 3)) (valuation 2)
  exact law0Values (valuation 0) (valuation 1) (valuation 2) (valuation 3)

theorem addedLaw0OppositeValid :
    addedLaw0.reversed.SatisfiedBy SemigroupBasis.CoRoots.Order6Sunday.RecursivePublishedFinite.S6_6447.table.semigroup.opposite := by
  rw [Identity.satisfiedBy_opposite_iff_reversed, Identity.reversed_reversed]
  exact addedLaw0Valid

private theorem law1At0 (b c d : Fin 6) :
    mul (mul (mul (mul (mul (c) (b)) (0)) (c)) (d)) (0) = mul (mul (mul (mul (mul (c) (b)) (c)) (0)) (d)) (0) := by
  decide +revert

private theorem law1At1 (b c d : Fin 6) :
    mul (mul (mul (mul (mul (c) (b)) (1)) (c)) (d)) (1) = mul (mul (mul (mul (mul (c) (b)) (c)) (1)) (d)) (1) := by
  decide +revert

private theorem law1At2 (b c d : Fin 6) :
    mul (mul (mul (mul (mul (c) (b)) (2)) (c)) (d)) (2) = mul (mul (mul (mul (mul (c) (b)) (c)) (2)) (d)) (2) := by
  decide +revert

private theorem law1At3 (b c d : Fin 6) :
    mul (mul (mul (mul (mul (c) (b)) (3)) (c)) (d)) (3) = mul (mul (mul (mul (mul (c) (b)) (c)) (3)) (d)) (3) := by
  decide +revert

private theorem law1At4 (b c d : Fin 6) :
    mul (mul (mul (mul (mul (c) (b)) (4)) (c)) (d)) (4) = mul (mul (mul (mul (mul (c) (b)) (c)) (4)) (d)) (4) := by
  decide +revert

private theorem law1At5 (b c d : Fin 6) :
    mul (mul (mul (mul (mul (c) (b)) (5)) (c)) (d)) (5) = mul (mul (mul (mul (mul (c) (b)) (c)) (5)) (d)) (5) := by
  decide +revert

private theorem law1Values (a b c d : Fin 6) :
    mul (mul (mul (mul (mul (c) (b)) (a)) (c)) (d)) (a) = mul (mul (mul (mul (mul (c) (b)) (c)) (a)) (d)) (a) := by
  exact Fin.cases (law1At0 b c d) (fun a => Fin.cases (law1At1 b c d) (fun a => Fin.cases (law1At2 b c d) (fun a => Fin.cases (law1At3 b c d) (fun a => Fin.cases (law1At4 b c d) (fun a => Fin.cases (law1At5 b c d) (fun a => Fin.elim0 a) a) a) a) a) a) a

theorem addedLaw1Valid : addedLaw1.SatisfiedBy SemigroupBasis.CoRoots.Order6Sunday.RecursivePublishedFinite.S6_6447.table.semigroup := by
  intro valuation
  change mul (mul (mul (mul (mul (valuation 2) (valuation 1)) (valuation 0)) (valuation 2)) (valuation 3)) (valuation 0) = mul (mul (mul (mul (mul (valuation 2) (valuation 1)) (valuation 2)) (valuation 0)) (valuation 3)) (valuation 0)
  exact law1Values (valuation 0) (valuation 1) (valuation 2) (valuation 3)

theorem addedLaw1OppositeValid :
    addedLaw1.reversed.SatisfiedBy SemigroupBasis.CoRoots.Order6Sunday.RecursivePublishedFinite.S6_6447.table.semigroup.opposite := by
  rw [Identity.satisfiedBy_opposite_iff_reversed, Identity.reversed_reversed]
  exact addedLaw1Valid

private theorem law2At0 (b c d : Fin 6) :
    mul (mul (mul (mul (mul (0) (b)) (c)) (d)) (0)) (c) = mul (mul (mul (mul (mul (0) (b)) (c)) (d)) (c)) (0) := by
  decide +revert

private theorem law2At1 (b c d : Fin 6) :
    mul (mul (mul (mul (mul (1) (b)) (c)) (d)) (1)) (c) = mul (mul (mul (mul (mul (1) (b)) (c)) (d)) (c)) (1) := by
  decide +revert

private theorem law2At2 (b c d : Fin 6) :
    mul (mul (mul (mul (mul (2) (b)) (c)) (d)) (2)) (c) = mul (mul (mul (mul (mul (2) (b)) (c)) (d)) (c)) (2) := by
  decide +revert

private theorem law2At3 (b c d : Fin 6) :
    mul (mul (mul (mul (mul (3) (b)) (c)) (d)) (3)) (c) = mul (mul (mul (mul (mul (3) (b)) (c)) (d)) (c)) (3) := by
  decide +revert

private theorem law2At4 (b c d : Fin 6) :
    mul (mul (mul (mul (mul (4) (b)) (c)) (d)) (4)) (c) = mul (mul (mul (mul (mul (4) (b)) (c)) (d)) (c)) (4) := by
  decide +revert

private theorem law2At5 (b c d : Fin 6) :
    mul (mul (mul (mul (mul (5) (b)) (c)) (d)) (5)) (c) = mul (mul (mul (mul (mul (5) (b)) (c)) (d)) (c)) (5) := by
  decide +revert

private theorem law2Values (a b c d : Fin 6) :
    mul (mul (mul (mul (mul (a) (b)) (c)) (d)) (a)) (c) = mul (mul (mul (mul (mul (a) (b)) (c)) (d)) (c)) (a) := by
  exact Fin.cases (law2At0 b c d) (fun a => Fin.cases (law2At1 b c d) (fun a => Fin.cases (law2At2 b c d) (fun a => Fin.cases (law2At3 b c d) (fun a => Fin.cases (law2At4 b c d) (fun a => Fin.cases (law2At5 b c d) (fun a => Fin.elim0 a) a) a) a) a) a) a

theorem addedLaw2Valid : addedLaw2.SatisfiedBy SemigroupBasis.CoRoots.Order6Sunday.RecursivePublishedFinite.S6_6447.table.semigroup := by
  intro valuation
  change mul (mul (mul (mul (mul (valuation 0) (valuation 1)) (valuation 2)) (valuation 3)) (valuation 0)) (valuation 2) = mul (mul (mul (mul (mul (valuation 0) (valuation 1)) (valuation 2)) (valuation 3)) (valuation 2)) (valuation 0)
  exact law2Values (valuation 0) (valuation 1) (valuation 2) (valuation 3)

theorem addedLaw2OppositeValid :
    addedLaw2.reversed.SatisfiedBy SemigroupBasis.CoRoots.Order6Sunday.RecursivePublishedFinite.S6_6447.table.semigroup.opposite := by
  rw [Identity.satisfiedBy_opposite_iff_reversed, Identity.reversed_reversed]
  exact addedLaw2Valid

/-- Extend the recorded finite list by just the newly approved fixed laws. -/
theorem tableModels : Models SemigroupBasis.CoRoots.Order6Sunday.RecursivePublishedFinite.S6_6447.table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_append] at member
  rcases member with old | extra
  · exact SemigroupBasis.CoRoots.Order6Sunday.RecursivePublishedFinite.S6_6447.tableModels identity old
  · simp only [added, List.mem_cons, List.not_mem_nil, or_false] at extra
    rcases extra with rfl | rfl | rfl
    · exact addedLaw0Valid
    · exact addedLaw1Valid
    · exact addedLaw2Valid

theorem oppositeModels : Models SemigroupBasis.CoRoots.Order6Sunday.RecursivePublishedFinite.S6_6447.table.semigroup.opposite (reversedBasis basis) :=
  tableModels.oppositeReversed

end S6_6447

end SemigroupBasis.CoRoots.Order6Sunday.RecursiveDepth7Delta
