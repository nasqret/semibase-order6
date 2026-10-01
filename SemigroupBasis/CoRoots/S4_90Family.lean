import SemigroupBasis.CoRoots.S4_90

namespace SemigroupBasis.CoRoots.S4_90Family

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.S4_90

def parityZeroEmbedding :
    Embedding parityZeroThree.semigroup
      Generated.Catalogue.S4_93.table.semigroup where
  toFun := fun a => ⟨a.val, Nat.lt_trans a.isLt (by decide)⟩
  map_mul := by decide
  injective := by
    intro a b h
    have values : a.val = b.val := by
      simpa using congrArg Fin.val h
    exact Fin.ext values

theorem valid_support (e : Identity Nat)
    (valid : e.SatisfiedBy Generated.Catalogue.S4_93.table.semigroup) :
    ∀ z, z ∈ e.lhs.toList ↔ z ∈ e.rhs.toList :=
  parityZeroValid_support e
    (parityZeroEmbedding.pullback_identity e valid)

theorem valid_parity (e : Identity Nat)
    (valid : e.SatisfiedBy Generated.Catalogue.S4_93.table.semigroup) :
    ∀ z, e.lhs.toList.count z % 2 =
      e.rhs.toList.count z % 2 :=
  parityZeroValid_parity e
    (parityZeroEmbedding.pullback_identity e valid)

private def headSeparator (z : Nat) : Nat → Fin 4 :=
  fun x => if x = z then 3 else 2

private theorem fold_from_two
    (valuation : Nat → Fin 4) (xs : List Nat) :
    xs.foldl
        (fun current x =>
          Generated.Catalogue.S4_93.mul current (valuation x))
        (2 : Fin 4) = 2 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simpa [List.foldl_cons, Generated.Catalogue.S4_93.mul] using ih

private theorem fold_from_three
    (valuation : Nat → Fin 4) (xs : List Nat) :
    xs.foldl
        (fun current x =>
          Generated.Catalogue.S4_93.mul current (valuation x))
        (3 : Fin 4) = 3 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simpa [List.foldl_cons, Generated.Catalogue.S4_93.mul] using ih

theorem eval_headSeparator (z : Nat) (w : Word Nat) :
    Generated.Catalogue.S4_93.table.semigroup.eval
        (headSeparator z) w =
      if w.head = z then (3 : Fin 4) else (2 : Fin 4) := by
  cases w with
  | mk head tail =>
      by_cases hz : head = z
      · subst head
        simp only [if_pos]
        change
          tail.foldl
              (fun current x =>
                Generated.Catalogue.S4_93.mul current
                  (headSeparator z x))
              (headSeparator z z) = 3
        rw [show headSeparator z z = (3 : Fin 4) by
          simp [headSeparator]]
        exact fold_from_three _ _
      · simp only [if_neg hz]
        change
          tail.foldl
              (fun current x =>
                Generated.Catalogue.S4_93.mul current
                  (headSeparator z x))
              (headSeparator z head) = 2
        rw [show headSeparator z head = (2 : Fin 4) by
          simp [headSeparator, hz]]
        exact fold_from_two _ _

theorem valid_head_eq (e : Identity Nat)
    (valid : e.SatisfiedBy Generated.Catalogue.S4_93.table.semigroup) :
    e.lhs.head = e.rhs.head := by
  apply Decidable.byContradiction
  intro headsNe
  have evaluated := valid (headSeparator e.lhs.head)
  rw [eval_headSeparator, eval_headSeparator] at evaluated
  simp [Ne.symm headsNe] at evaluated

private theorem mul_power (a : Fin 4) :
    a =
      Generated.Catalogue.S4_93.mul
        (Generated.Catalogue.S4_93.mul a a) a := by
  decide +revert

private theorem mul_suffix_commutative (a b c : Fin 4) :
    Generated.Catalogue.S4_93.mul
        (Generated.Catalogue.S4_93.mul a b) c =
      Generated.Catalogue.S4_93.mul
        (Generated.Catalogue.S4_93.mul a c) b := by
  decide +revert

theorem models :
    Models Generated.Catalogue.S4_93.table.semigroup basis := by
  intro e he
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · intro valuation
    change
      Generated.Catalogue.S4_93.mul
          (Generated.Catalogue.S4_93.mul
            (valuation 0) (valuation 1))
          (valuation 2) =
        Generated.Catalogue.S4_93.mul
          (Generated.Catalogue.S4_93.mul
            (valuation 0) (valuation 2))
          (valuation 1)
    exact mul_suffix_commutative
      (valuation 0) (valuation 1) (valuation 2)
  · intro valuation
    change
      valuation 0 =
        Generated.Catalogue.S4_93.mul
          (Generated.Catalogue.S4_93.mul
            (valuation 0) (valuation 0))
          (valuation 0)
    exact mul_power (valuation 0)

theorem basis_complete :
    BasisFor Generated.Catalogue.S4_93.table.semigroup basis :=
  basis_complete_of_separates Generated.Catalogue.S4_93.table
    models valid_head_eq valid_support valid_parity

theorem opposite_basis_complete :
    BasisFor Generated.Catalogue.S4_93.table.semigroup.opposite
      (reversedBasis basis) :=
  basis_complete.oppositeReversed

end SemigroupBasis.CoRoots.S4_90Family
