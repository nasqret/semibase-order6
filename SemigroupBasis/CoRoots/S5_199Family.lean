import SemigroupBasis.CoRoots.S5_199
import SemigroupBasis.Generated.CatalogueOrder5Part02
import SemigroupBasis.Generated.CatalogueOrder5Part04

namespace SemigroupBasis.CoRoots.S5_199Family

open SemigroupBasis
open SemigroupBasis.CoRoots.S5_199

private def finitePowerLaw : Identity (Fin 1) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [0, 0, 0]⟩⟩

private def finiteFirstSwapLaw : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1, 0]⟩⟩

private def finiteTransferLaw : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1, 1]⟩⟩

private def finitePrefixSwapLaw : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨1, [0, 0]⟩⟩

private def finiteHeavyInsertionLaw : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [0, 0, 1]⟩⟩

private def finiteSuffixCommutationLaw : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

private def finitePrefixCommutationLaw : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩

private def finiteLongInsertionLaw : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [0, 1, 2]⟩⟩

private theorem finitePowerLaw_map :
    finitePowerLaw.map Fin.val = powerLaw := rfl

private theorem finiteFirstSwapLaw_map :
    finiteFirstSwapLaw.map Fin.val = firstSwapLaw := rfl

private theorem finiteTransferLaw_map :
    finiteTransferLaw.map Fin.val = transferLaw := rfl

private theorem finitePrefixSwapLaw_map :
    finitePrefixSwapLaw.map Fin.val = prefixSwapLaw := rfl

private theorem finiteHeavyInsertionLaw_map :
    finiteHeavyInsertionLaw.map Fin.val = heavyInsertionLaw := rfl

private theorem finiteSuffixCommutationLaw_map :
    finiteSuffixCommutationLaw.map Fin.val =
      suffixCommutationLaw := rfl

private theorem finitePrefixCommutationLaw_map :
    finitePrefixCommutationLaw.map Fin.val =
      prefixCommutationLaw := rfl

private theorem finiteLongInsertionLaw_map :
    finiteLongInsertionLaw.map Fin.val = longInsertionLaw := rfl

private theorem models_of_checks
    (T : FiniteTable)
    (power : T.checkIdentity finitePowerLaw = true)
    (firstSwap : T.checkIdentity finiteFirstSwapLaw = true)
    (transfer : T.checkIdentity finiteTransferLaw = true)
    (prefixSwap : T.checkIdentity finitePrefixSwapLaw = true)
    (heavyInsertion :
      T.checkIdentity finiteHeavyInsertionLaw = true)
    (suffixCommutation :
      T.checkIdentity finiteSuffixCommutationLaw = true)
    (prefixCommutation :
      T.checkIdentity finitePrefixCommutationLaw = true)
    (longInsertion :
      T.checkIdentity finiteLongInsertionLaw = true) :
    Models T.semigroup basis := by
  intro e he
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [← finitePowerLaw_map]
    exact T.checkIdentityNat_sound finitePowerLaw power
  · rw [← finiteFirstSwapLaw_map]
    exact T.checkIdentityNat_sound finiteFirstSwapLaw firstSwap
  · rw [← finiteTransferLaw_map]
    exact T.checkIdentityNat_sound finiteTransferLaw transfer
  · rw [← finitePrefixSwapLaw_map]
    exact T.checkIdentityNat_sound finitePrefixSwapLaw prefixSwap
  · rw [← finiteHeavyInsertionLaw_map]
    exact
      T.checkIdentityNat_sound finiteHeavyInsertionLaw heavyInsertion
  · rw [← finiteSuffixCommutationLaw_map]
    exact
      T.checkIdentityNat_sound
        finiteSuffixCommutationLaw suffixCommutation
  · rw [← finitePrefixCommutationLaw_map]
    exact
      T.checkIdentityNat_sound
        finitePrefixCommutationLaw prefixCommutation
  · rw [← finiteLongInsertionLaw_map]
    exact
      T.checkIdentityNat_sound finiteLongInsertionLaw longInsertion

private def supportMarker
    (target other : Fin 5) (z : Nat) : Nat → Fin 5 :=
  fun x => if x = z then target else other

private theorem fold_absent_iff
    (mul : Fin 5 → Fin 5 → Fin 5)
    (target other output : Fin 5)
    (z : Nat)
    (step :
      ∀ current x,
        mul current (supportMarker target other z x) = output ↔
          current = output ∧ x ≠ z)
    (xs : List Nat) (initial : Fin 5) :
    xs.foldl
        (fun current x =>
          mul current (supportMarker target other z x))
        initial = output ↔
      initial = output ∧ z ∉ xs := by
  induction xs generalizing initial with
  | nil =>
      simp
  | cons x xs ih =>
      rw [List.foldl_cons, ih, step]
      simp only [List.mem_cons, not_or]
      constructor
      · rintro ⟨⟨currentOutput, xNe⟩, restAbsent⟩
        exact
          ⟨currentOutput, fun zx => xNe zx.symm, restAbsent⟩
      · rintro ⟨currentOutput, zNe, restAbsent⟩
        exact
          ⟨⟨currentOutput, fun xz => zNe xz.symm⟩, restAbsent⟩

private theorem fold_present_iff
    (mul : Fin 5 → Fin 5 → Fin 5)
    (target other output : Fin 5)
    (z : Nat)
    (step :
      ∀ current x,
        mul current (supportMarker target other z x) = output ↔
          current = output ∨ x = z)
    (xs : List Nat) (initial : Fin 5) :
    xs.foldl
        (fun current x =>
          mul current (supportMarker target other z x))
        initial = output ↔
      initial = output ∨ z ∈ xs := by
  induction xs generalizing initial with
  | nil =>
      simp
  | cons x xs ih =>
      rw [List.foldl_cons, ih, step]
      simp only [List.mem_cons]
      constructor
      · intro h
        rcases h with (currentOutput | xEq) | restPresent
        · exact Or.inl currentOutput
        · exact Or.inr (Or.inl xEq.symm)
        · exact Or.inr (Or.inr restPresent)
      · intro h
        rcases h with currentOutput | xEq | restPresent
        · exact Or.inl (Or.inl currentOutput)
        · exact Or.inl (Or.inr xEq.symm)
        · exact Or.inr restPresent

private theorem fold_absent_iff_of_invariant
    (mul : Fin 5 → Fin 5 → Fin 5)
    (target other output : Fin 5)
    (invariant : Fin 5 → Prop)
    (z : Nat)
    (closed :
      ∀ current x, invariant current →
        invariant
          (mul current (supportMarker target other z x)))
    (step :
      ∀ current x, invariant current →
        (mul current (supportMarker target other z x) = output ↔
          current = output ∧ x ≠ z))
    (xs : List Nat) (initial : Fin 5)
    (initialInvariant : invariant initial) :
    xs.foldl
        (fun current x =>
          mul current (supportMarker target other z x))
        initial = output ↔
      initial = output ∧ z ∉ xs := by
  induction xs generalizing initial with
  | nil =>
      simp
  | cons x xs ih =>
      rw [List.foldl_cons,
        ih _ (closed initial x initialInvariant),
        step initial x initialInvariant]
      simp only [List.mem_cons, not_or]
      constructor
      · rintro ⟨⟨currentOutput, xNe⟩, restAbsent⟩
        exact
          ⟨currentOutput, fun zx => xNe zx.symm, restAbsent⟩
      · rintro ⟨currentOutput, zNe, restAbsent⟩
        exact
          ⟨⟨currentOutput, fun xz => zNe xz.symm⟩, restAbsent⟩

private theorem support_of_absence_separation
    (G : Semigroup (Fin 5))
    (target other output : Fin 5)
    (evalOutput :
      ∀ z (w : Word Nat),
        G.eval (supportMarker target other z) w = output ↔
          z ∉ w.toList)
    (e : Identity Nat) (valid : e.SatisfiedBy G) :
    ∀ z, z ∈ e.lhs.toList ↔ z ∈ e.rhs.toList := by
  intro z
  have evaluated := valid (supportMarker target other z)
  have absent :
      z ∉ e.lhs.toList ↔ z ∉ e.rhs.toList := by
    calc
      z ∉ e.lhs.toList ↔
          G.eval
              (supportMarker target other z) e.lhs = output :=
        (evalOutput z e.lhs).symm
      _ ↔
          G.eval
              (supportMarker target other z) e.rhs = output := by
        rw [evaluated]
      _ ↔ z ∉ e.rhs.toList := evalOutput z e.rhs
  constructor
  · intro lhsMember
    apply Decidable.byContradiction
    intro rhsAbsent
    exact (absent.mpr rhsAbsent) lhsMember
  · intro rhsMember
    apply Decidable.byContradiction
    intro lhsAbsent
    exact (absent.mp lhsAbsent) rhsMember

private theorem support_of_presence_separation
    (G : Semigroup (Fin 5))
    (target other output : Fin 5)
    (evalOutput :
      ∀ z (w : Word Nat),
        G.eval (supportMarker target other z) w = output ↔
          z ∈ w.toList)
    (e : Identity Nat) (valid : e.SatisfiedBy G) :
    ∀ z, z ∈ e.lhs.toList ↔ z ∈ e.rhs.toList := by
  intro z
  have evaluated := valid (supportMarker target other z)
  calc
    z ∈ e.lhs.toList ↔
        G.eval
            (supportMarker target other z) e.lhs = output :=
      (evalOutput z e.lhs).symm
    _ ↔
        G.eval
            (supportMarker target other z) e.rhs = output := by
      rw [evaluated]
    _ ↔ z ∈ e.rhs.toList := evalOutput z e.rhs

private def lengthState (marker : Fin 5) (n : Nat) : Fin 5 :=
  if n = 1 then marker else if n = 2 then 1 else 0

private theorem lengthFold
    (mul : Fin 5 → Fin 5 → Fin 5)
    (marker : Fin 5)
    (step :
      ∀ n, 0 < n →
        mul (lengthState marker n) marker =
          lengthState marker (n + 1))
    (xs : List Nat) (acc : Nat) (accPos : 0 < acc) :
    xs.foldl (fun current _ => mul current marker)
        (lengthState marker acc) =
      lengthState marker (acc + xs.length) := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [List.foldl_cons, List.length_cons]
      rw [step acc accPos, ih (acc + 1) (by omega)]
      congr 1
      omega

private theorem lengthState_capped_injective
    (marker : Fin 5)
    (markerNeZero : marker ≠ 0)
    (markerNeOne : marker ≠ 1)
    {m n : Nat} (mPos : 0 < m) (nPos : 0 < n)
    (equal : lengthState marker m = lengthState marker n) :
    min m 3 = min n 3 := by
  by_cases hm1 : m = 1
  · subst m
    by_cases hn1 : n = 1
    · subst n
      rfl
    · by_cases hn2 : n = 2
      · subst n
        have markerEq : marker = 1 := by
          simpa [lengthState] using equal
        exact (markerNeOne markerEq).elim
      · have hn3 : 3 ≤ n := by omega
        have markerEq : marker = 0 := by
          simpa [lengthState, hn1, hn2] using equal
        exact (markerNeZero markerEq).elim
  · by_cases hm2 : m = 2
    · subst m
      by_cases hn1 : n = 1
      · subst n
        have markerEq : marker = 1 := by
          simpa [lengthState] using equal.symm
        exact (markerNeOne markerEq).elim
      · by_cases hn2 : n = 2
        · subst n
          rfl
        · have hn3 : 3 ≤ n := by omega
          have values := congrArg Fin.val equal
          simp [lengthState, hn1, hn2] at values
    · have hm3 : 3 ≤ m := by omega
      by_cases hn1 : n = 1
      · subst n
        have markerEq : marker = 0 := by
          simpa [lengthState, hm1, hm2] using equal.symm
        exact (markerNeZero markerEq).elim
      · by_cases hn2 : n = 2
        · subst n
          have values := congrArg Fin.val equal
          simp [lengthState, hm1, hm2] at values
        · have hn3 : 3 ≤ n := by omega
          simp [Nat.min_eq_right hm3, Nat.min_eq_right hn3]

private theorem capped_length_of_eval
    (G : Semigroup (Fin 5))
    (marker : Fin 5)
    (markerNeZero : marker ≠ 0)
    (markerNeOne : marker ≠ 1)
    (evalLength :
      ∀ w : Word Nat,
        G.eval (fun _ => marker) w =
          lengthState marker w.toList.length)
    (e : Identity Nat) (valid : e.SatisfiedBy G) :
    min e.lhs.toList.length 3 =
      min e.rhs.toList.length 3 := by
  have evaluated := valid (fun _ => marker)
  rw [evalLength, evalLength] at evaluated
  exact lengthState_capped_injective marker
    markerNeZero markerNeOne
    (by simp [Word.toList]) (by simp [Word.toList]) evaluated

namespace S5_199

private theorem supportStep (z : Nat) (current : Fin 5) (x : Nat) :
    Generated.Catalogue.S5_199.mul current
        (supportMarker 3 4 z x) = 4 ↔
      current = 4 ∧ x ≠ z := by
  by_cases hx : x = z
  · subst x
    simp [supportMarker]
    decide +revert
  · simp [supportMarker, hx]
    decide +revert

private theorem evalSupport (z : Nat) (w : Word Nat) :
    Generated.Catalogue.S5_199.table.semigroup.eval
        (supportMarker 3 4 z) w = (4 : Fin 5) ↔
      z ∉ w.toList := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current x =>
              Generated.Catalogue.S5_199.mul current
                (supportMarker 3 4 z x))
            (supportMarker 3 4 z head) = 4 ↔
          z ∉ head :: tail
      rw [fold_absent_iff
        Generated.Catalogue.S5_199.mul 3 4 4 z (supportStep z)]
      simp [supportMarker, eq_comm]

private theorem lengthStep (n : Nat) (nPos : 0 < n) :
    Generated.Catalogue.S5_199.mul
        (lengthState 3 n) 3 =
      lengthState 3 (n + 1) := by
  by_cases hn1 : n = 1
  · subst n
    rfl
  · by_cases hn2 : n = 2
    · subst n
      rfl
    · have hn3 : 3 ≤ n := by omega
      simp [lengthState, hn1, hn2,
        show n ≠ 0 by omega, show n + 1 ≠ 2 by omega,
        Generated.Catalogue.S5_199.mul]

private theorem evalLength (w : Word Nat) :
    Generated.Catalogue.S5_199.table.semigroup.eval
        (fun _ => (3 : Fin 5)) w =
      lengthState 3 w.toList.length := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current _ =>
              Generated.Catalogue.S5_199.mul current 3)
            3 =
          lengthState 3 (head :: tail).length
      simpa [lengthState, Nat.add_comm] using
        lengthFold Generated.Catalogue.S5_199.mul 3
          lengthStep tail 1 (by omega)

set_option maxRecDepth 100000 in
theorem models :
    Models Generated.Catalogue.S5_199.table.semigroup basis :=
  models_of_checks Generated.Catalogue.S5_199.table
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

theorem valid_support (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_199.table.semigroup) :
    ∀ z, z ∈ e.lhs.toList ↔ z ∈ e.rhs.toList :=
  support_of_absence_separation
    Generated.Catalogue.S5_199.table.semigroup
      3 4 4 evalSupport e valid

theorem valid_capped_length (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_199.table.semigroup) :
    min e.lhs.toList.length 3 =
      min e.rhs.toList.length 3 :=
  capped_length_of_eval Generated.Catalogue.S5_199.table.semigroup
    3 (by decide) (by decide) evalLength e valid

theorem basis_complete :
    BasisFor Generated.Catalogue.S5_199.table.semigroup basis :=
  basis_complete_of_separates Generated.Catalogue.S5_199.table
    models valid_support valid_capped_length
      (⟨2, by decide⟩ :
        Fin Generated.Catalogue.S5_199.table.order)
      (⟨3, by decide⟩ :
        Fin Generated.Catalogue.S5_199.table.order)
      (by decide)

theorem opposite_basis_complete :
    BasisFor Generated.Catalogue.S5_199.table.semigroup.opposite
      (reversedBasis basis) :=
  basis_complete.oppositeReversed

end S5_199

namespace S5_219

private theorem supportStep (z : Nat) (current : Fin 5) (x : Nat) :
    Generated.Catalogue.S5_219.mul current
        (supportMarker 4 3 z x) = 4 ↔
      current = 4 ∨ x = z := by
  by_cases hx : x = z
  · subst x
    simp [supportMarker]
    decide +revert
  · simp [supportMarker, hx]
    decide +revert

private theorem evalSupport (z : Nat) (w : Word Nat) :
    Generated.Catalogue.S5_219.table.semigroup.eval
        (supportMarker 4 3 z) w = (4 : Fin 5) ↔
      z ∈ w.toList := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current x =>
              Generated.Catalogue.S5_219.mul current
                (supportMarker 4 3 z x))
            (supportMarker 4 3 z head) = 4 ↔
          z ∈ head :: tail
      rw [fold_present_iff
        Generated.Catalogue.S5_219.mul 4 3 4 z (supportStep z)]
      simp [supportMarker, eq_comm]

private theorem lengthStep (n : Nat) (nPos : 0 < n) :
    Generated.Catalogue.S5_219.mul
        (lengthState 3 n) 3 =
      lengthState 3 (n + 1) := by
  by_cases hn1 : n = 1
  · subst n
    rfl
  · by_cases hn2 : n = 2
    · subst n
      rfl
    · have hn3 : 3 ≤ n := by omega
      simp [lengthState, hn1, hn2,
        show n ≠ 0 by omega, show n + 1 ≠ 2 by omega,
        Generated.Catalogue.S5_219.mul]

private theorem evalLength (w : Word Nat) :
    Generated.Catalogue.S5_219.table.semigroup.eval
        (fun _ => (3 : Fin 5)) w =
      lengthState 3 w.toList.length := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current _ =>
              Generated.Catalogue.S5_219.mul current 3)
            3 =
          lengthState 3 (head :: tail).length
      simpa [lengthState, Nat.add_comm] using
        lengthFold Generated.Catalogue.S5_219.mul 3
          lengthStep tail 1 (by omega)

set_option maxRecDepth 100000 in
theorem models :
    Models Generated.Catalogue.S5_219.table.semigroup basis :=
  models_of_checks Generated.Catalogue.S5_219.table
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

theorem valid_support (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_219.table.semigroup) :
    ∀ z, z ∈ e.lhs.toList ↔ z ∈ e.rhs.toList :=
  support_of_presence_separation
    Generated.Catalogue.S5_219.table.semigroup
      4 3 4 evalSupport e valid

theorem valid_capped_length (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_219.table.semigroup) :
    min e.lhs.toList.length 3 =
      min e.rhs.toList.length 3 :=
  capped_length_of_eval Generated.Catalogue.S5_219.table.semigroup
    3 (by decide) (by decide) evalLength e valid

theorem basis_complete :
    BasisFor Generated.Catalogue.S5_219.table.semigroup basis :=
  basis_complete_of_separates Generated.Catalogue.S5_219.table
    models valid_support valid_capped_length
      (⟨2, by decide⟩ :
        Fin Generated.Catalogue.S5_219.table.order)
      (⟨3, by decide⟩ :
        Fin Generated.Catalogue.S5_219.table.order)
      (by decide)

theorem opposite_basis_complete :
    BasisFor Generated.Catalogue.S5_219.table.semigroup.opposite
      (reversedBasis basis) :=
  basis_complete.oppositeReversed

end S5_219

namespace S5_493

private theorem supportStep (z : Nat) (current : Fin 5) (x : Nat) :
    Generated.Catalogue.S5_493.mul current
        (supportMarker 2 4 z x) = 4 ↔
      current = 4 ∧ x ≠ z := by
  by_cases hx : x = z
  · subst x
    simp [supportMarker]
    decide +revert
  · simp [supportMarker, hx]
    decide +revert

private theorem evalSupport (z : Nat) (w : Word Nat) :
    Generated.Catalogue.S5_493.table.semigroup.eval
        (supportMarker 2 4 z) w = (4 : Fin 5) ↔
      z ∉ w.toList := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current x =>
              Generated.Catalogue.S5_493.mul current
                (supportMarker 2 4 z x))
            (supportMarker 2 4 z head) = 4 ↔
          z ∉ head :: tail
      rw [fold_absent_iff
        Generated.Catalogue.S5_493.mul 2 4 4 z (supportStep z)]
      simp [supportMarker, eq_comm]

private theorem lengthStep (n : Nat) (nPos : 0 < n) :
    Generated.Catalogue.S5_493.mul
        (lengthState 2 n) 2 =
      lengthState 2 (n + 1) := by
  by_cases hn1 : n = 1
  · subst n
    rfl
  · by_cases hn2 : n = 2
    · subst n
      rfl
    · have hn3 : 3 ≤ n := by omega
      simp [lengthState, hn1, hn2,
        show n ≠ 0 by omega, show n + 1 ≠ 2 by omega,
        Generated.Catalogue.S5_493.mul]

private theorem evalLength (w : Word Nat) :
    Generated.Catalogue.S5_493.table.semigroup.eval
        (fun _ => (2 : Fin 5)) w =
      lengthState 2 w.toList.length := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current _ =>
              Generated.Catalogue.S5_493.mul current 2)
            2 =
          lengthState 2 (head :: tail).length
      simpa [lengthState, Nat.add_comm] using
        lengthFold Generated.Catalogue.S5_493.mul 2
          lengthStep tail 1 (by omega)

set_option maxRecDepth 100000 in
theorem models :
    Models Generated.Catalogue.S5_493.table.semigroup basis :=
  models_of_checks Generated.Catalogue.S5_493.table
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

theorem valid_support (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_493.table.semigroup) :
    ∀ z, z ∈ e.lhs.toList ↔ z ∈ e.rhs.toList :=
  support_of_absence_separation
    Generated.Catalogue.S5_493.table.semigroup
      2 4 4 evalSupport e valid

theorem valid_capped_length (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_493.table.semigroup) :
    min e.lhs.toList.length 3 =
      min e.rhs.toList.length 3 :=
  capped_length_of_eval Generated.Catalogue.S5_493.table.semigroup
    2 (by decide) (by decide) evalLength e valid

theorem basis_complete :
    BasisFor Generated.Catalogue.S5_493.table.semigroup basis :=
  basis_complete_of_separates Generated.Catalogue.S5_493.table
    models valid_support valid_capped_length
      (⟨2, by decide⟩ :
        Fin Generated.Catalogue.S5_493.table.order)
      (⟨3, by decide⟩ :
        Fin Generated.Catalogue.S5_493.table.order)
      (by decide)

end S5_493

namespace S5_503

private theorem supportStep (z : Nat) (current : Fin 5) (x : Nat) :
    Generated.Catalogue.S5_503.mul current
        (supportMarker 4 2 z x) = 4 ↔
      current = 4 ∨ x = z := by
  by_cases hx : x = z
  · subst x
    simp [supportMarker]
    decide +revert
  · simp [supportMarker, hx]
    decide +revert

private theorem evalSupport (z : Nat) (w : Word Nat) :
    Generated.Catalogue.S5_503.table.semigroup.eval
        (supportMarker 4 2 z) w = (4 : Fin 5) ↔
      z ∈ w.toList := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current x =>
              Generated.Catalogue.S5_503.mul current
                (supportMarker 4 2 z x))
            (supportMarker 4 2 z head) = 4 ↔
          z ∈ head :: tail
      rw [fold_present_iff
        Generated.Catalogue.S5_503.mul 4 2 4 z (supportStep z)]
      simp [supportMarker, eq_comm]

private theorem lengthStep (n : Nat) (nPos : 0 < n) :
    Generated.Catalogue.S5_503.mul
        (lengthState 2 n) 2 =
      lengthState 2 (n + 1) := by
  by_cases hn1 : n = 1
  · subst n
    rfl
  · by_cases hn2 : n = 2
    · subst n
      rfl
    · have hn3 : 3 ≤ n := by omega
      simp [lengthState, hn1, hn2,
        show n ≠ 0 by omega, show n + 1 ≠ 2 by omega,
        Generated.Catalogue.S5_503.mul]

private theorem evalLength (w : Word Nat) :
    Generated.Catalogue.S5_503.table.semigroup.eval
        (fun _ => (2 : Fin 5)) w =
      lengthState 2 w.toList.length := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current _ =>
              Generated.Catalogue.S5_503.mul current 2)
            2 =
          lengthState 2 (head :: tail).length
      simpa [lengthState, Nat.add_comm] using
        lengthFold Generated.Catalogue.S5_503.mul 2
          lengthStep tail 1 (by omega)

set_option maxRecDepth 100000 in
theorem models :
    Models Generated.Catalogue.S5_503.table.semigroup basis :=
  models_of_checks Generated.Catalogue.S5_503.table
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

theorem valid_support (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_503.table.semigroup) :
    ∀ z, z ∈ e.lhs.toList ↔ z ∈ e.rhs.toList :=
  support_of_presence_separation
    Generated.Catalogue.S5_503.table.semigroup
      4 2 4 evalSupport e valid

theorem valid_capped_length (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_503.table.semigroup) :
    min e.lhs.toList.length 3 =
      min e.rhs.toList.length 3 :=
  capped_length_of_eval Generated.Catalogue.S5_503.table.semigroup
    2 (by decide) (by decide) evalLength e valid

theorem basis_complete :
    BasisFor Generated.Catalogue.S5_503.table.semigroup basis :=
  basis_complete_of_separates Generated.Catalogue.S5_503.table
    models valid_support valid_capped_length
      (⟨2, by decide⟩ :
        Fin Generated.Catalogue.S5_503.table.order)
      (⟨3, by decide⟩ :
        Fin Generated.Catalogue.S5_503.table.order)
      (by decide)

end S5_503

namespace S5_508

private theorem supportClosed
    (z : Nat) (current : Fin 5) (x : Nat)
    (_ : current ≠ 4) :
    Generated.Catalogue.S5_508.mul current
        (supportMarker 2 3 z x) ≠ 4 := by
  by_cases hx : x = z
  · subst x
    simp [supportMarker]
    decide +revert
  · simp [supportMarker, hx]
    decide +revert

private theorem supportStep
    (z : Nat) (current : Fin 5) (x : Nat)
    (currentReachable : current ≠ 4) :
    Generated.Catalogue.S5_508.mul current
        (supportMarker 2 3 z x) = 3 ↔
      current = 3 ∧ x ≠ z := by
  by_cases hx : x = z
  · subst x
    simp [supportMarker]
    decide +revert
  · simp [supportMarker, hx]
    exact by
      revert current
      decide

private theorem evalSupport (z : Nat) (w : Word Nat) :
    Generated.Catalogue.S5_508.table.semigroup.eval
        (supportMarker 2 3 z) w = (3 : Fin 5) ↔
      z ∉ w.toList := by
  cases w with
  | mk head tail =>
      have headReachable :
          supportMarker 2 3 z head ≠ (4 : Fin 5) := by
        by_cases hhead : head = z
        · simp [supportMarker, hhead]
        · simp [supportMarker, hhead]
      change
        tail.foldl
            (fun current x =>
              Generated.Catalogue.S5_508.mul current
                (supportMarker 2 3 z x))
            (supportMarker 2 3 z head) = 3 ↔
          z ∉ head :: tail
      rw [fold_absent_iff_of_invariant
        Generated.Catalogue.S5_508.mul 2 3 3
        (fun current => current ≠ 4) z
        (supportClosed z) (supportStep z) tail
        (supportMarker 2 3 z head) headReachable]
      simp [supportMarker, eq_comm]

private theorem lengthStep (n : Nat) (nPos : 0 < n) :
    Generated.Catalogue.S5_508.mul
        (lengthState 2 n) 2 =
      lengthState 2 (n + 1) := by
  by_cases hn1 : n = 1
  · subst n
    rfl
  · by_cases hn2 : n = 2
    · subst n
      rfl
    · have hn3 : 3 ≤ n := by omega
      simp [lengthState, hn1, hn2,
        show n ≠ 0 by omega, show n + 1 ≠ 2 by omega,
        Generated.Catalogue.S5_508.mul]

private theorem evalLength (w : Word Nat) :
    Generated.Catalogue.S5_508.table.semigroup.eval
        (fun _ => (2 : Fin 5)) w =
      lengthState 2 w.toList.length := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current _ =>
              Generated.Catalogue.S5_508.mul current 2)
            2 =
          lengthState 2 (head :: tail).length
      simpa [lengthState, Nat.add_comm] using
        lengthFold Generated.Catalogue.S5_508.mul 2
          lengthStep tail 1 (by omega)

set_option maxRecDepth 100000 in
theorem models :
    Models Generated.Catalogue.S5_508.table.semigroup basis :=
  models_of_checks Generated.Catalogue.S5_508.table
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

theorem valid_support (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_508.table.semigroup) :
    ∀ z, z ∈ e.lhs.toList ↔ z ∈ e.rhs.toList :=
  support_of_absence_separation
    Generated.Catalogue.S5_508.table.semigroup
      2 3 3 evalSupport e valid

theorem valid_capped_length (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_508.table.semigroup) :
    min e.lhs.toList.length 3 =
      min e.rhs.toList.length 3 :=
  capped_length_of_eval Generated.Catalogue.S5_508.table.semigroup
    2 (by decide) (by decide) evalLength e valid

theorem basis_complete :
    BasisFor Generated.Catalogue.S5_508.table.semigroup basis :=
  basis_complete_of_separates Generated.Catalogue.S5_508.table
    models valid_support valid_capped_length
      (⟨2, by decide⟩ :
        Fin Generated.Catalogue.S5_508.table.order)
      (⟨4, by decide⟩ :
        Fin Generated.Catalogue.S5_508.table.order)
      (by decide)

theorem opposite_basis_complete :
    BasisFor Generated.Catalogue.S5_508.table.semigroup.opposite
      (reversedBasis basis) :=
  basis_complete.oppositeReversed

end S5_508

end SemigroupBasis.CoRoots.S5_199Family
