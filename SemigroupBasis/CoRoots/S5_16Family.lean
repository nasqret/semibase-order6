import SemigroupBasis.CoRoots.S5_16
import SemigroupBasis.Generated.CatalogueOrder5Part01
import SemigroupBasis.Transfer

namespace SemigroupBasis.CoRoots.S5_16Family

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.S5_16

private def finiteCommonSquareLaw : Identity (Fin 2) :=
  Identity.mk (Word.mk 0 [0]) (Word.mk 1 [1])

private def finiteSquareMiddleLaw : Identity (Fin 2) :=
  Identity.mk (Word.mk 0 [0, 0]) (Word.mk 1 [0, 1])

private def finiteSuffixCommutationLaw : Identity (Fin 3) :=
  Identity.mk (Word.mk 0 [1, 2]) (Word.mk 0 [2, 1])

private def finitePrefixCommutationLaw : Identity (Fin 3) :=
  Identity.mk (Word.mk 0 [1, 2]) (Word.mk 1 [0, 2])

private def finiteLongInsertionLaw : Identity (Fin 3) :=
  Identity.mk (Word.mk 0 [1, 2]) (Word.mk 0 [0, 0, 1, 2])

private theorem finiteCommonSquareLaw_map :
    finiteCommonSquareLaw.map Fin.val = commonSquareLaw := rfl

private theorem finiteSquareMiddleLaw_map :
    finiteSquareMiddleLaw.map Fin.val =
      SemigroupBasis.CoRoots.S5_58.squareMiddleLaw := rfl

private theorem finiteSuffixCommutationLaw_map :
    finiteSuffixCommutationLaw.map Fin.val =
      SemigroupBasis.CoRoots.S5_58.suffixCommutationLaw := rfl

private theorem finitePrefixCommutationLaw_map :
    finitePrefixCommutationLaw.map Fin.val =
      SemigroupBasis.CoRoots.S5_58.prefixCommutationLaw := rfl

private theorem finiteLongInsertionLaw_map :
    finiteLongInsertionLaw.map Fin.val =
      SemigroupBasis.CoRoots.S5_58.longInsertionLaw := rfl

private theorem models_of_checks
    (T : FiniteTable)
    (commonSquare : T.checkIdentity finiteCommonSquareLaw = true)
    (squareMiddle : T.checkIdentity finiteSquareMiddleLaw = true)
    (suffixCommutation :
      T.checkIdentity finiteSuffixCommutationLaw = true)
    (prefixCommutation :
      T.checkIdentity finitePrefixCommutationLaw = true)
    (longInsertion :
      T.checkIdentity finiteLongInsertionLaw = true) :
    Models T.semigroup basis := by
  intro e member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · rw [finiteCommonSquareLaw_map.symm]
    exact T.checkIdentityNat_sound finiteCommonSquareLaw commonSquare
  · rw [finiteSquareMiddleLaw_map.symm]
    exact T.checkIdentityNat_sound finiteSquareMiddleLaw squareMiddle
  · rw [finiteSuffixCommutationLaw_map.symm]
    exact T.checkIdentityNat_sound
      finiteSuffixCommutationLaw suffixCommutation
  · rw [finitePrefixCommutationLaw_map.symm]
    exact T.checkIdentityNat_sound
      finitePrefixCommutationLaw prefixCommutation
  · rw [finiteLongInsertionLaw_map.symm]
    exact T.checkIdentityNat_sound finiteLongInsertionLaw longInsertion

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

namespace S5_16

private def cyclicEmbedding :
    Embedding cyclicTwo.semigroup
      Generated.Catalogue.S5_16.table.semigroup where
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
    Models Generated.Catalogue.S5_16.table.semigroup basis :=
  models_of_checks Generated.Catalogue.S5_16.table
    (by decide) (by decide) (by decide) (by decide) (by decide)

theorem valid_parity (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_16.table.semigroup) :
    SemigroupBasis.CoRoots.S5_58.SameParity e.lhs e.rhs :=
  cyclicValid_parity_eq e
    (cyclicEmbedding.pullback_identity e valid)

theorem valid_length_one (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_16.table.semigroup) :
    e.lhs.toList.length = 1 ↔ e.rhs.toList.length = 1 :=
  valid_length_one_of_constant
    Generated.Catalogue.S5_16.table.semigroup
    1 0 (by decide) (by decide) (by decide) e valid

theorem basis_complete :
    BasisFor Generated.Catalogue.S5_16.table.semigroup basis :=
  basis_complete_of_separates Generated.Catalogue.S5_16.table
    models valid_parity valid_length_one
    (⟨3, by decide⟩ : Fin Generated.Catalogue.S5_16.table.order)
    (⟨2, by decide⟩ : Fin Generated.Catalogue.S5_16.table.order)
    (by decide) (by decide)

end S5_16

namespace S5_20

private def cyclicEmbedding :
    Embedding cyclicTwo.semigroup
      Generated.Catalogue.S5_20.table.semigroup where
  toFun := fun a =>
    if a.val = 0 then ⟨0, by decide⟩ else ⟨2, by decide⟩
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
    Models Generated.Catalogue.S5_20.table.semigroup basis :=
  models_of_checks Generated.Catalogue.S5_20.table
    (by decide) (by decide) (by decide) (by decide) (by decide)

theorem valid_parity (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_20.table.semigroup) :
    SemigroupBasis.CoRoots.S5_58.SameParity e.lhs e.rhs :=
  cyclicValid_parity_eq e
    (cyclicEmbedding.pullback_identity e valid)

theorem valid_length_one (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_20.table.semigroup) :
    e.lhs.toList.length = 1 ↔ e.rhs.toList.length = 1 :=
  valid_length_one_of_constant
    Generated.Catalogue.S5_20.table.semigroup
    1 0 (by decide) (by decide) (by decide) e valid

theorem basis_complete :
    BasisFor Generated.Catalogue.S5_20.table.semigroup basis :=
  basis_complete_of_separates Generated.Catalogue.S5_20.table
    models valid_parity valid_length_one
    (⟨4, by decide⟩ : Fin Generated.Catalogue.S5_20.table.order)
    (⟨3, by decide⟩ : Fin Generated.Catalogue.S5_20.table.order)
    (by decide) (by decide)

end S5_20

namespace S5_21

private def cyclicEmbedding :
    Embedding cyclicTwo.semigroup
      Generated.Catalogue.S5_21.table.semigroup where
  toFun := fun a =>
    if a.val = 0 then ⟨0, by decide⟩ else ⟨2, by decide⟩
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
    Models Generated.Catalogue.S5_21.table.semigroup basis :=
  models_of_checks Generated.Catalogue.S5_21.table
    (by decide) (by decide) (by decide) (by decide) (by decide)

theorem valid_parity (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_21.table.semigroup) :
    SemigroupBasis.CoRoots.S5_58.SameParity e.lhs e.rhs :=
  cyclicValid_parity_eq e
    (cyclicEmbedding.pullback_identity e valid)

theorem valid_length_one (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_21.table.semigroup) :
    e.lhs.toList.length = 1 ↔ e.rhs.toList.length = 1 :=
  valid_length_one_of_constant
    Generated.Catalogue.S5_21.table.semigroup
    1 0 (by decide) (by decide) (by decide) e valid

theorem basis_complete :
    BasisFor Generated.Catalogue.S5_21.table.semigroup basis :=
  basis_complete_of_separates Generated.Catalogue.S5_21.table
    models valid_parity valid_length_one
    (⟨4, by decide⟩ : Fin Generated.Catalogue.S5_21.table.order)
    (⟨1, by decide⟩ : Fin Generated.Catalogue.S5_21.table.order)
    (by decide) (by decide)

theorem opposite_basis_complete :
    BasisFor Generated.Catalogue.S5_21.table.semigroup.opposite
      (reversedBasis basis) :=
  basis_complete.oppositeReversed

end S5_21

end SemigroupBasis.CoRoots.S5_16Family
