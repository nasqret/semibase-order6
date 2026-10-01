import SemigroupBasis.CoRoots.S5_97
import SemigroupBasis.Examples.SemilatticeTwo
import SemigroupBasis.Generated.CatalogueOrder5Part01
import SemigroupBasis.Transfer

namespace SemigroupBasis.CoRoots.S5_97Family

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.S5_97

private def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

private def finiteBasis : List (Identity (Fin 3)) :=
  basis.map fun e => e.map toFinThree

private theorem basis_roundTrip_checked :
    basis.all (fun e =>
      decide ((e.map toFinThree).map Fin.val = e)) = true := by
  decide

private theorem basis_roundTrip
    (e : Identity Nat) (member : e ∈ basis) :
    (e.map toFinThree).map Fin.val = e := by
  exact of_decide_eq_true <|
    (List.all_eq_true.mp basis_roundTrip_checked) e member

private theorem models_of_finite_checks
    (T : FiniteTable)
    (checked : finiteBasis.all T.checkIdentity = true) :
    Models T.semigroup basis := by
  intro e member
  have finiteMember : e.map toFinThree ∈ finiteBasis :=
    List.mem_map.mpr ⟨e, member, rfl⟩
  have finiteValid :=
    T.checkIdentityNat_sound (e.map toFinThree)
      ((List.all_eq_true.mp checked) _ finiteMember)
  rw [basis_roundTrip e member] at finiteValid
  exact finiteValid

private theorem fold_sink
    (mul : Fin 5 → Fin 5 → Fin 5)
    (marker sink : Fin 5)
    (sinkStep : mul sink marker = sink)
    (xs : List Nat) :
    xs.foldl (fun current _ => mul current marker) sink = sink := by
  induction xs with
  | nil =>
      rfl
  | cons next rest ih =>
      simp only [List.foldl_cons, sinkStep]
      exact ih

private theorem eval_constant_eq_marker_iff_length_one
    (G : Semigroup (Fin 5))
    (marker sink : Fin 5)
    (markerNeSink : marker ≠ sink)
    (markerSquare : G.mul marker marker = sink)
    (sinkStep : G.mul sink marker = sink)
    (w : Word Nat) :
    G.eval (fun _ => marker) w = marker ↔
      w.toList.length = 1 := by
  cases w with
  | mk head tail =>
      cases tail with
      | nil =>
          simp [Semigroup.eval, Word.toList]
      | cons next rest =>
          change
            rest.foldl
                (fun current _ => G.mul current marker)
                (G.mul marker marker) = marker ↔
              (head :: next :: rest).length = 1
          rw [markerSquare, fold_sink G.mul marker sink sinkStep rest]
          simp [Ne.symm markerNeSink]

private theorem valid_length_one_of_constant
    (G : Semigroup (Fin 5))
    (marker sink : Fin 5)
    (markerNeSink : marker ≠ sink)
    (markerSquare : G.mul marker marker = sink)
    (sinkStep : G.mul sink marker = sink)
    (e : Identity Nat) (valid : e.SatisfiedBy G) :
    e.lhs.toList.length = 1 ↔ e.rhs.toList.length = 1 := by
  have evaluated := valid (fun _ => marker)
  have lhsIff :=
    eval_constant_eq_marker_iff_length_one
      G marker sink markerNeSink markerSquare sinkStep e.lhs
  have rhsIff :=
    eval_constant_eq_marker_iff_length_one
      G marker sink markerNeSink markerSquare sinkStep e.rhs
  constructor
  · intro lhsOne
    apply rhsIff.mp
    rw [← evaluated]
    exact lhsIff.mpr lhsOne
  · intro rhsOne
    apply lhsIff.mp
    rw [evaluated]
    exact rhsIff.mpr rhsOne

namespace S5_97

private def supportEmbedding :
    Embedding semilatticeTwo.semigroup
      Generated.Catalogue.S5_97.table.semigroup where
  toFun := fun a =>
    if a.val = 0 then ⟨0, by decide⟩ else ⟨4, by decide⟩
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  injective := by
    intro a b
    revert a b
    decide

set_option maxRecDepth 100000 in
theorem models :
    Models Generated.Catalogue.S5_97.table.semigroup basis :=
  models_of_finite_checks Generated.Catalogue.S5_97.table (by decide)

theorem valid_support (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_97.table.semigroup) :
    ∀ z, z ∈ e.lhs.toList ↔ z ∈ e.rhs.toList :=
  semilatticeValid_support_eq e
    (supportEmbedding.pullback_identity e valid)

theorem valid_length_one (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_97.table.semigroup) :
    e.lhs.toList.length = 1 ↔ e.rhs.toList.length = 1 :=
  valid_length_one_of_constant
    Generated.Catalogue.S5_97.table.semigroup
    2 0 (by decide) (by decide) (by decide) e valid

theorem basis_complete :
    BasisFor Generated.Catalogue.S5_97.table.semigroup basis :=
  basis_complete_of_separates Generated.Catalogue.S5_97.table
    models valid_support valid_length_one
    (⟨2, by decide⟩ : Fin Generated.Catalogue.S5_97.table.order)
    (⟨3, by decide⟩ : Fin Generated.Catalogue.S5_97.table.order)
    (by decide)

theorem opposite_basis_complete :
    BasisFor Generated.Catalogue.S5_97.table.semigroup.opposite
      (reversedBasis basis) :=
  basis_complete.oppositeReversed

def selfDualEmbedding :
    Embedding Generated.Catalogue.S5_97.table.semigroup.opposite
      Generated.Catalogue.S5_97.table.semigroup where
  toFun := id
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  injective := Function.injective_id

theorem selfDualInvolution (a : Fin 5) :
    selfDualEmbedding.toFun (selfDualEmbedding.toFun a) = a := rfl

end S5_97

end SemigroupBasis.CoRoots.S5_97Family
