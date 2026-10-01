import SemigroupBasis.CoRoots.S5_58
import SemigroupBasis.Generated.CatalogueOrder5Part01
import SemigroupBasis.Generated.CatalogueOrder5Part02
import SemigroupBasis.Transfer

namespace SemigroupBasis.CoRoots.S5_58Family

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.S5_58

private def finiteSquareRightLaw : Identity (Fin 2) :=
  Identity.mk (Word.mk 0 [0, 0]) (Word.mk 0 [1, 1])

private def finiteSquareMiddleLaw : Identity (Fin 2) :=
  Identity.mk (Word.mk 0 [0, 0]) (Word.mk 1 [0, 1])

private def finiteSquareLeftLaw : Identity (Fin 2) :=
  Identity.mk (Word.mk 0 [0, 0]) (Word.mk 1 [1, 0])

private def finiteSuffixCommutationLaw : Identity (Fin 3) :=
  Identity.mk (Word.mk 0 [1, 2]) (Word.mk 0 [2, 1])

private def finitePrefixCommutationLaw : Identity (Fin 3) :=
  Identity.mk (Word.mk 0 [1, 2]) (Word.mk 1 [0, 2])

private def finiteLongInsertionLaw : Identity (Fin 3) :=
  Identity.mk (Word.mk 0 [1, 2]) (Word.mk 0 [0, 0, 1, 2])

private theorem finiteSquareRightLaw_map :
    finiteSquareRightLaw.map Fin.val = squareRightLaw := rfl

private theorem finiteSquareMiddleLaw_map :
    finiteSquareMiddleLaw.map Fin.val = squareMiddleLaw := rfl

private theorem finiteSquareLeftLaw_map :
    finiteSquareLeftLaw.map Fin.val = squareLeftLaw := rfl

private theorem finiteSuffixCommutationLaw_map :
    finiteSuffixCommutationLaw.map Fin.val =
      suffixCommutationLaw := rfl

private theorem finitePrefixCommutationLaw_map :
    finitePrefixCommutationLaw.map Fin.val =
      prefixCommutationLaw := rfl

private theorem finiteLongInsertionLaw_map :
    finiteLongInsertionLaw.map Fin.val =
      longInsertionLaw := rfl

private theorem models_of_checks
    (T : FiniteTable)
    (squareRight : T.checkIdentity finiteSquareRightLaw = true)
    (squareMiddle : T.checkIdentity finiteSquareMiddleLaw = true)
    (squareLeft : T.checkIdentity finiteSquareLeftLaw = true)
    (suffixCommutation :
      T.checkIdentity finiteSuffixCommutationLaw = true)
    (prefixCommutation :
      T.checkIdentity finitePrefixCommutationLaw = true)
    (longInsertion :
      T.checkIdentity finiteLongInsertionLaw = true) :
    Models T.semigroup basis := by
  intro e he
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [finiteSquareRightLaw_map.symm]
    exact T.checkIdentityNat_sound finiteSquareRightLaw squareRight
  · rw [finiteSquareMiddleLaw_map.symm]
    exact T.checkIdentityNat_sound finiteSquareMiddleLaw squareMiddle
  · rw [finiteSquareLeftLaw_map.symm]
    exact T.checkIdentityNat_sound finiteSquareLeftLaw squareLeft
  · rw [finiteSuffixCommutationLaw_map.symm]
    exact T.checkIdentityNat_sound
      finiteSuffixCommutationLaw suffixCommutation
  · rw [finitePrefixCommutationLaw_map.symm]
    exact T.checkIdentityNat_sound
      finitePrefixCommutationLaw prefixCommutation
  · rw [finiteLongInsertionLaw_map.symm]
    exact T.checkIdentityNat_sound finiteLongInsertionLaw longInsertion

private theorem fold_ne
    (mul : Fin 5 → Fin 5 → Fin 5)
    (marker forbidden : Fin 5)
    (step : ∀ current, mul current marker ≠ forbidden)
    (xs : List Nat) (initial : Fin 5)
    (initialNe : initial ≠ forbidden) :
    xs.foldl (fun current _ => mul current marker) initial ≠ forbidden := by
  induction xs generalizing initial with
  | nil =>
      exact initialNe
  | cons x xs ih =>
      simp only [List.foldl_cons]
      exact ih _ (step initial)

private theorem fold_ne_marker_square
    (mul : Fin 5 → Fin 5 → Fin 5)
    (marker square : Fin 5)
    (stepNeMarker : ∀ current, mul current marker ≠ marker)
    (stepNeSquare :
      ∀ current, current ≠ marker →
        mul current marker ≠ square)
    (xs : List Nat) (initial : Fin 5)
    (initialNeMarker : initial ≠ marker)
    (initialNeSquare : initial ≠ square) :
    xs.foldl (fun current _ => mul current marker) initial ≠ marker ∧
      xs.foldl (fun current _ => mul current marker) initial ≠ square := by
  induction xs generalizing initial with
  | nil =>
      exact ⟨initialNeMarker, initialNeSquare⟩
  | cons x xs ih =>
      simp only [List.foldl_cons]
      exact ih _ (stepNeMarker initial)
        (stepNeSquare initial initialNeMarker)

private theorem eval_constant_eq_marker_iff_length_one
    (G : Semigroup (Fin 5)) (marker square : Fin 5)
    (markerNeSquare : marker ≠ square)
    (markerSquare : G.mul marker marker = square)
    (stepNeMarker : ∀ current, G.mul current marker ≠ marker)
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
          rw [markerSquare]
          have notMarker :=
            fold_ne G.mul marker marker stepNeMarker
              rest square markerNeSquare.symm
          constructor
          · intro equal
            exact False.elim (notMarker equal)
          · intro impossible
            simp at impossible

private theorem eval_constant_eq_square_iff_length_two
    (G : Semigroup (Fin 5)) (marker square : Fin 5)
    (markerNeSquare : marker ≠ square)
    (markerSquare : G.mul marker marker = square)
    (stepNeMarker : ∀ current, G.mul current marker ≠ marker)
    (stepNeSquare :
      ∀ current, current ≠ marker →
        G.mul current marker ≠ square)
    (w : Word Nat) :
    G.eval (fun _ => marker) w = square ↔
      w.toList.length = 2 := by
  cases w with
  | mk head tail =>
      cases tail with
      | nil =>
          change marker = square ↔ (head :: []).length = 2
          simp [markerNeSquare]
      | cons next rest =>
          cases rest with
          | nil =>
              change G.mul marker marker = square ↔
                (head :: next :: []).length = 2
              simp [markerSquare]
          | cons third more =>
              change
                more.foldl
                    (fun current _ => G.mul current marker)
                    (G.mul (G.mul marker marker) marker) = square ↔
                  (head :: next :: third :: more).length = 2
              rw [markerSquare]
              have secondNeMarker := stepNeMarker square
              have secondNeSquare :=
                stepNeSquare square markerNeSquare.symm
              have notSquare :=
                (fold_ne_marker_square G.mul marker square
                  stepNeMarker stepNeSquare more
                  (G.mul square marker)
                  secondNeMarker secondNeSquare).2
              constructor
              · intro equal
                exact False.elim (notSquare equal)
              · intro impossible
                simp at impossible

private theorem valid_length_one_of_constant
    (G : Semigroup (Fin 5)) (marker square : Fin 5)
    (markerNeSquare : marker ≠ square)
    (markerSquare : G.mul marker marker = square)
    (stepNeMarker : ∀ current, G.mul current marker ≠ marker)
    (e : Identity Nat) (valid : e.SatisfiedBy G) :
    e.lhs.toList.length = 1 ↔ e.rhs.toList.length = 1 := by
  have evaluated := valid (fun _ => marker)
  have lhsIff :=
    eval_constant_eq_marker_iff_length_one
      G marker square markerNeSquare markerSquare stepNeMarker e.lhs
  have rhsIff :=
    eval_constant_eq_marker_iff_length_one
      G marker square markerNeSquare markerSquare stepNeMarker e.rhs
  constructor
  · intro lhsOne
    apply rhsIff.mp
    rw [← evaluated]
    exact lhsIff.mpr lhsOne
  · intro rhsOne
    apply lhsIff.mp
    rw [evaluated]
    exact rhsIff.mpr rhsOne

private theorem valid_length_two_of_constant
    (G : Semigroup (Fin 5)) (marker square : Fin 5)
    (markerNeSquare : marker ≠ square)
    (markerSquare : G.mul marker marker = square)
    (stepNeMarker : ∀ current, G.mul current marker ≠ marker)
    (stepNeSquare :
      ∀ current, current ≠ marker →
        G.mul current marker ≠ square)
    (e : Identity Nat) (valid : e.SatisfiedBy G) :
    e.lhs.toList.length = 2 ↔ e.rhs.toList.length = 2 := by
  have evaluated := valid (fun _ => marker)
  have lhsIff :=
    eval_constant_eq_square_iff_length_two
      G marker square markerNeSquare markerSquare
      stepNeMarker stepNeSquare e.lhs
  have rhsIff :=
    eval_constant_eq_square_iff_length_two
      G marker square markerNeSquare markerSquare
      stepNeMarker stepNeSquare e.rhs
  constructor
  · intro lhsTwo
    apply rhsIff.mp
    rw [← evaluated]
    exact lhsIff.mpr lhsTwo
  · intro rhsTwo
    apply lhsIff.mp
    rw [evaluated]
    exact rhsIff.mpr rhsTwo

namespace S5_58

private def cyclicEmbedding :
    Embedding cyclicTwo.semigroup
      Generated.Catalogue.S5_58.table.semigroup where
  toFun := fun a =>
    if a.val = 0 then ⟨0, by decide⟩ else ⟨3, by decide⟩
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
    Models Generated.Catalogue.S5_58.table.semigroup basis :=
  models_of_checks Generated.Catalogue.S5_58.table
    (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

theorem valid_parity (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_58.table.semigroup) :
    SameParity e.lhs e.rhs :=
  cyclicValid_parity_eq e
    (cyclicEmbedding.pullback_identity e valid)

private theorem marker_ne_square : (4 : Fin 5) ≠ 1 := by decide

private theorem marker_square :
    Generated.Catalogue.S5_58.mul 4 4 = 1 := by decide

private theorem step_ne_marker (current : Fin 5) :
    Generated.Catalogue.S5_58.mul current 4 ≠ 4 := by
  decide +revert

private theorem step_ne_square (current : Fin 5)
    (currentNe : current ≠ 4) :
    Generated.Catalogue.S5_58.mul current 4 ≠ 1 := by
  revert current
  decide

theorem valid_length_one (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_58.table.semigroup) :
    e.lhs.toList.length = 1 ↔ e.rhs.toList.length = 1 :=
  valid_length_one_of_constant Generated.Catalogue.S5_58.table.semigroup
    4 1 marker_ne_square marker_square step_ne_marker e valid

theorem valid_length_two (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_58.table.semigroup) :
    e.lhs.toList.length = 2 ↔ e.rhs.toList.length = 2 :=
  valid_length_two_of_constant Generated.Catalogue.S5_58.table.semigroup
    4 1 marker_ne_square marker_square
    step_ne_marker step_ne_square e valid

theorem basis_complete :
    BasisFor Generated.Catalogue.S5_58.table.semigroup basis :=
  basis_complete_of_separates Generated.Catalogue.S5_58.table
    models valid_parity valid_length_one valid_length_two
      (⟨2, by decide⟩ :
        Fin Generated.Catalogue.S5_58.table.order)
      (⟨4, by decide⟩ :
        Fin Generated.Catalogue.S5_58.table.order)
      (⟨0, by decide⟩ :
        Fin Generated.Catalogue.S5_58.table.order)
      (⟨4, by decide⟩ :
        Fin Generated.Catalogue.S5_58.table.order)
      (by decide) (by decide)

theorem opposite_basis_complete :
    BasisFor Generated.Catalogue.S5_58.table.semigroup.opposite
      (reversedBasis basis) :=
  basis_complete.oppositeReversed

end S5_58

namespace S5_64

private def cyclicEmbedding :
    Embedding cyclicTwo.semigroup
      Generated.Catalogue.S5_64.table.semigroup where
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
    Models Generated.Catalogue.S5_64.table.semigroup basis :=
  models_of_checks Generated.Catalogue.S5_64.table
    (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

theorem valid_parity (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_64.table.semigroup) :
    SameParity e.lhs e.rhs :=
  cyclicValid_parity_eq e
    (cyclicEmbedding.pullback_identity e valid)

private theorem marker_ne_square : (4 : Fin 5) ≠ 1 := by decide

private theorem marker_square :
    Generated.Catalogue.S5_64.mul 4 4 = 1 := by decide

private theorem step_ne_marker (current : Fin 5) :
    Generated.Catalogue.S5_64.mul current 4 ≠ 4 := by
  decide +revert

private theorem step_ne_square (current : Fin 5)
    (currentNe : current ≠ 4) :
    Generated.Catalogue.S5_64.mul current 4 ≠ 1 := by
  revert current
  decide

theorem valid_length_one (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_64.table.semigroup) :
    e.lhs.toList.length = 1 ↔ e.rhs.toList.length = 1 :=
  valid_length_one_of_constant Generated.Catalogue.S5_64.table.semigroup
    4 1 marker_ne_square marker_square step_ne_marker e valid

theorem valid_length_two (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_64.table.semigroup) :
    e.lhs.toList.length = 2 ↔ e.rhs.toList.length = 2 :=
  valid_length_two_of_constant Generated.Catalogue.S5_64.table.semigroup
    4 1 marker_ne_square marker_square
    step_ne_marker step_ne_square e valid

theorem basis_complete :
    BasisFor Generated.Catalogue.S5_64.table.semigroup basis :=
  basis_complete_of_separates Generated.Catalogue.S5_64.table
    models valid_parity valid_length_one valid_length_two
      (⟨3, by decide⟩ :
        Fin Generated.Catalogue.S5_64.table.order)
      (⟨4, by decide⟩ :
        Fin Generated.Catalogue.S5_64.table.order)
      (⟨0, by decide⟩ :
        Fin Generated.Catalogue.S5_64.table.order)
      (⟨4, by decide⟩ :
        Fin Generated.Catalogue.S5_64.table.order)
      (by decide) (by decide)

theorem opposite_basis_complete :
    BasisFor Generated.Catalogue.S5_64.table.semigroup.opposite
      (reversedBasis basis) :=
  basis_complete.oppositeReversed

end S5_64

namespace S5_179

private def cyclicEmbedding :
    Embedding cyclicTwo.semigroup
      Generated.Catalogue.S5_179.table.semigroup where
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
    Models Generated.Catalogue.S5_179.table.semigroup basis :=
  models_of_checks Generated.Catalogue.S5_179.table
    (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

theorem valid_parity (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_179.table.semigroup) :
    SameParity e.lhs e.rhs :=
  cyclicValid_parity_eq e
    (cyclicEmbedding.pullback_identity e valid)

private theorem marker_ne_square : (4 : Fin 5) ≠ 1 := by decide

private theorem marker_square :
    Generated.Catalogue.S5_179.mul 4 4 = 1 := by decide

private theorem step_ne_marker (current : Fin 5) :
    Generated.Catalogue.S5_179.mul current 4 ≠ 4 := by
  decide +revert

private theorem step_ne_square (current : Fin 5)
    (currentNe : current ≠ 4) :
    Generated.Catalogue.S5_179.mul current 4 ≠ 1 := by
  revert current
  decide

theorem valid_length_one (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_179.table.semigroup) :
    e.lhs.toList.length = 1 ↔ e.rhs.toList.length = 1 :=
  valid_length_one_of_constant Generated.Catalogue.S5_179.table.semigroup
    4 1 marker_ne_square marker_square step_ne_marker e valid

theorem valid_length_two (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_179.table.semigroup) :
    e.lhs.toList.length = 2 ↔ e.rhs.toList.length = 2 :=
  valid_length_two_of_constant Generated.Catalogue.S5_179.table.semigroup
    4 1 marker_ne_square marker_square
    step_ne_marker step_ne_square e valid

theorem basis_complete :
    BasisFor Generated.Catalogue.S5_179.table.semigroup basis :=
  basis_complete_of_separates Generated.Catalogue.S5_179.table
    models valid_parity valid_length_one valid_length_two
      (⟨3, by decide⟩ :
        Fin Generated.Catalogue.S5_179.table.order)
      (⟨4, by decide⟩ :
        Fin Generated.Catalogue.S5_179.table.order)
      (⟨0, by decide⟩ :
        Fin Generated.Catalogue.S5_179.table.order)
      (⟨3, by decide⟩ :
        Fin Generated.Catalogue.S5_179.table.order)
      (by decide) (by decide)

end S5_179

namespace S5_183

private def cyclicEmbedding :
    Embedding cyclicTwo.semigroup
      Generated.Catalogue.S5_183.table.semigroup where
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
    Models Generated.Catalogue.S5_183.table.semigroup basis :=
  models_of_checks Generated.Catalogue.S5_183.table
    (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

theorem valid_parity (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_183.table.semigroup) :
    SameParity e.lhs e.rhs :=
  cyclicValid_parity_eq e
    (cyclicEmbedding.pullback_identity e valid)

private theorem marker_ne_square : (4 : Fin 5) ≠ 1 := by decide

private theorem marker_square :
    Generated.Catalogue.S5_183.mul 4 4 = 1 := by decide

private theorem step_ne_marker (current : Fin 5) :
    Generated.Catalogue.S5_183.mul current 4 ≠ 4 := by
  decide +revert

private theorem step_ne_square (current : Fin 5)
    (currentNe : current ≠ 4) :
    Generated.Catalogue.S5_183.mul current 4 ≠ 1 := by
  revert current
  decide

theorem valid_length_one (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_183.table.semigroup) :
    e.lhs.toList.length = 1 ↔ e.rhs.toList.length = 1 :=
  valid_length_one_of_constant Generated.Catalogue.S5_183.table.semigroup
    4 1 marker_ne_square marker_square step_ne_marker e valid

theorem valid_length_two (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_183.table.semigroup) :
    e.lhs.toList.length = 2 ↔ e.rhs.toList.length = 2 :=
  valid_length_two_of_constant Generated.Catalogue.S5_183.table.semigroup
    4 1 marker_ne_square marker_square
    step_ne_marker step_ne_square e valid

theorem basis_complete :
    BasisFor Generated.Catalogue.S5_183.table.semigroup basis :=
  basis_complete_of_separates Generated.Catalogue.S5_183.table
    models valid_parity valid_length_one valid_length_two
      (⟨3, by decide⟩ :
        Fin Generated.Catalogue.S5_183.table.order)
      (⟨4, by decide⟩ :
        Fin Generated.Catalogue.S5_183.table.order)
      (⟨0, by decide⟩ :
        Fin Generated.Catalogue.S5_183.table.order)
      (⟨3, by decide⟩ :
        Fin Generated.Catalogue.S5_183.table.order)
      (by decide) (by decide)

end S5_183

end SemigroupBasis.CoRoots.S5_58Family
