import SemigroupBasis.Generated.CatalogueOrder5Part04
import SemigroupBasis.Order6Subdirect.Common

/-!
# A bounded six-variable table-check shard for `S2_4 × S5_402op`

The staged rank-021 checker attempts all 15,625 right-factor valuations in
one kernel reduction.  This pilot fixes two coordinates, leaving only 625
closed finite valuations for the existing fused checker.
-/

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6Day7.S2_4.Rank021SixVariableFiniteShard

open SemigroupBasis

abbrev rightTable : FiniteTable :=
  SemigroupBasis.Order6Subdirect.oppositeTable
    SemigroupBasis.Generated.Catalogue.S5_402.table

def longIdentity : Identity (Fin 6) :=
  ⟨⟨0, [1, 1, 2, 3, 3, 4, 5, 5]⟩,
    ⟨0, [3, 3, 4, 1, 1, 2, 5, 5]⟩⟩

def tailCheck (first second : Fin 5) : Bool :=
  FiniteTable.checkAssignmentsFused 4 5 fun remaining =>
    decide
      (rightTable.semigroup.eval
        (Fin.cases first (Fin.cases second remaining)) longIdentity.lhs =
       rightTable.semigroup.eval
        (Fin.cases first (Fin.cases second remaining)) longIdentity.rhs)

theorem shard00 : tailCheck 0 0 = true := by
  decide

theorem shard01 : tailCheck 0 1 = true := by
  decide

theorem shard02 : tailCheck 0 2 = true := by
  decide

theorem shard03 : tailCheck 0 3 = true := by
  decide

theorem shard04 : tailCheck 0 4 = true := by
  decide

theorem shard10 : tailCheck 1 0 = true := by
  decide

theorem shard11 : tailCheck 1 1 = true := by
  decide

theorem shard12 : tailCheck 1 2 = true := by
  decide

theorem shard13 : tailCheck 1 3 = true := by
  decide

theorem shard14 : tailCheck 1 4 = true := by
  decide

theorem shard20 : tailCheck 2 0 = true := by
  decide

theorem shard21 : tailCheck 2 1 = true := by
  decide

theorem shard22 : tailCheck 2 2 = true := by
  decide

theorem shard23 : tailCheck 2 3 = true := by
  decide

theorem shard24 : tailCheck 2 4 = true := by
  decide

theorem shard30 : tailCheck 3 0 = true := by
  decide

theorem shard31 : tailCheck 3 1 = true := by
  decide

theorem shard32 : tailCheck 3 2 = true := by
  decide

theorem shard33 : tailCheck 3 3 = true := by
  decide

theorem shard34 : tailCheck 3 4 = true := by
  decide

theorem shard40 : tailCheck 4 0 = true := by
  decide

theorem shard41 : tailCheck 4 1 = true := by
  decide

theorem shard42 : tailCheck 4 2 = true := by
  decide

theorem shard43 : tailCheck 4 3 = true := by
  decide

theorem shard44 : tailCheck 4 4 = true := by
  decide

private theorem row0 (second : Fin 5) : tailCheck 0 second = true :=
  Fin.cases shard00
    (Fin.cases shard01
      (Fin.cases shard02
        (Fin.cases shard03
          (Fin.cases shard04 (fun index => Fin.elim0 index))))) second

private theorem row1 (second : Fin 5) : tailCheck 1 second = true :=
  Fin.cases shard10
    (Fin.cases shard11
      (Fin.cases shard12
        (Fin.cases shard13
          (Fin.cases shard14 (fun index => Fin.elim0 index))))) second

private theorem row2 (second : Fin 5) : tailCheck 2 second = true :=
  Fin.cases shard20
    (Fin.cases shard21
      (Fin.cases shard22
        (Fin.cases shard23
          (Fin.cases shard24 (fun index => Fin.elim0 index))))) second

private theorem row3 (second : Fin 5) : tailCheck 3 second = true :=
  Fin.cases shard30
    (Fin.cases shard31
      (Fin.cases shard32
        (Fin.cases shard33
          (Fin.cases shard34 (fun index => Fin.elim0 index))))) second

private theorem row4 (second : Fin 5) : tailCheck 4 second = true :=
  Fin.cases shard40
    (Fin.cases shard41
      (Fin.cases shard42
        (Fin.cases shard43
          (Fin.cases shard44 (fun index => Fin.elim0 index))))) second

theorem allShards (first second : Fin 5) : tailCheck first second = true :=
  Fin.cases (row0 second)
    (Fin.cases (row1 second)
      (Fin.cases (row2 second)
        (Fin.cases (row3 second)
          (Fin.cases (row4 second) (fun index => Fin.elim0 index))))) first

theorem longIdentity_valid : longIdentity.SatisfiedBy rightTable.semigroup := by
  intro valuation
  have checked :=
    FiniteTable.checkAssignmentsFused_sound
      (fun remaining : Fin 4 → Fin 5 =>
        decide
          (rightTable.semigroup.eval
            (Fin.cases (valuation 0) (Fin.cases (valuation 1) remaining))
            longIdentity.lhs =
           rightTable.semigroup.eval
            (Fin.cases (valuation 0) (Fin.cases (valuation 1) remaining))
            longIdentity.rhs))
      (allShards (valuation 0) (valuation 1))
      (fun index => valuation index.succ.succ)
  have rebuild :
      Fin.cases (valuation 0)
        (Fin.cases (valuation 1) (fun index => valuation index.succ.succ)) =
        valuation := by
    funext index
    refine Fin.cases ?_ (fun rest => ?_) index
    · rfl
    · refine Fin.cases ?_ (fun rest => ?_) rest
      · rfl
      · rfl
  rw [rebuild] at checked
  exact of_decide_eq_true checked

end SemigroupBasis.CoRoots.Order6Day7.S2_4.Rank021SixVariableFiniteShard
