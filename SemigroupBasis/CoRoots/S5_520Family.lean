import SemigroupBasis.CoRoots.S5_520
import SemigroupBasis.Generated.CatalogueOrder5Part05

namespace SemigroupBasis.CoRoots.S5_520Family

open SemigroupBasis
open SemigroupBasis.CoRoots.S5_520

private def finitePowerLaw : Identity (Fin 1) :=
  Identity.mk (Word.mk 0 [0, 0]) (Word.mk 0 [0, 0, 0])

private def finiteFirstSwapLaw : Identity (Fin 2) :=
  Identity.mk (Word.mk 0 [0, 1]) (Word.mk 0 [1, 0])

private def finiteTransferLaw : Identity (Fin 2) :=
  Identity.mk (Word.mk 0 [0, 1]) (Word.mk 0 [1, 1])

private def finiteHeavyInsertionLaw : Identity (Fin 2) :=
  Identity.mk (Word.mk 0 [0, 1]) (Word.mk 0 [0, 0, 1])

private def finiteSuffixCommutationLaw : Identity (Fin 3) :=
  Identity.mk (Word.mk 0 [1, 2]) (Word.mk 0 [2, 1])

private def finiteLongInsertionLaw : Identity (Fin 3) :=
  Identity.mk (Word.mk 0 [1, 2]) (Word.mk 0 [0, 1, 2])

private theorem finitePowerLaw_map :
    finitePowerLaw.map Fin.val = powerLaw := rfl

private theorem finiteFirstSwapLaw_map :
    finiteFirstSwapLaw.map Fin.val = firstSwapLaw := rfl

private theorem finiteTransferLaw_map :
    finiteTransferLaw.map Fin.val = transferLaw := rfl

private theorem finiteHeavyInsertionLaw_map :
    finiteHeavyInsertionLaw.map Fin.val = heavyInsertionLaw := rfl

private theorem finiteSuffixCommutationLaw_map :
    finiteSuffixCommutationLaw.map Fin.val =
      suffixCommutationLaw := rfl

private theorem finiteLongInsertionLaw_map :
    finiteLongInsertionLaw.map Fin.val = longInsertionLaw := rfl

private theorem models_of_checks
    (T : FiniteTable)
    (power : T.checkIdentity finitePowerLaw = true)
    (firstSwap : T.checkIdentity finiteFirstSwapLaw = true)
    (transfer : T.checkIdentity finiteTransferLaw = true)
    (heavyInsertion :
      T.checkIdentity finiteHeavyInsertionLaw = true)
    (suffixCommutation :
      T.checkIdentity finiteSuffixCommutationLaw = true)
    (longInsertion :
      T.checkIdentity finiteLongInsertionLaw = true) :
    Models T.semigroup basis := by
  intro e he
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [finitePowerLaw_map.symm]
    exact T.checkIdentityNat_sound finitePowerLaw power
  · rw [finiteFirstSwapLaw_map.symm]
    exact T.checkIdentityNat_sound finiteFirstSwapLaw firstSwap
  · rw [finiteTransferLaw_map.symm]
    exact T.checkIdentityNat_sound finiteTransferLaw transfer
  · rw [finiteHeavyInsertionLaw_map.symm]
    exact
      T.checkIdentityNat_sound finiteHeavyInsertionLaw heavyInsertion
  · rw [finiteSuffixCommutationLaw_map.symm]
    exact
      T.checkIdentityNat_sound
        finiteSuffixCommutationLaw suffixCommutation
  · rw [finiteLongInsertionLaw_map.symm]
    exact
      T.checkIdentityNat_sound finiteLongInsertionLaw longInsertion

private def marker
    (target other : Fin 5) (z : Nat) : Nat -> Fin 5 :=
  fun x => if x = z then target else other

private theorem fold_target_iff
    (mul : Fin 5 -> Fin 5 -> Fin 5)
    (target other : Fin 5)
    (z : Nat)
    (step :
      forall current x,
        mul current (marker target other z x) = target <->
          current = target)
    (xs : List Nat) (initial : Fin 5) :
    xs.foldl
        (fun current x =>
          mul current (marker target other z x))
        initial = target <->
      initial = target := by
  induction xs generalizing initial with
  | nil =>
      simp
  | cons x xs ih =>
      rw [List.foldl_cons, ih, step]

private theorem fold_target_iff_of_invariant
    (mul : Fin 5 -> Fin 5 -> Fin 5)
    (target other : Fin 5)
    (invariant : Fin 5 -> Prop)
    (z : Nat)
    (closed :
      forall current x, invariant current ->
        invariant (mul current (marker target other z x)))
    (step :
      forall current x, invariant current ->
        (mul current (marker target other z x) = target <->
          current = target))
    (xs : List Nat) (initial : Fin 5)
    (initialInvariant : invariant initial) :
    xs.foldl
        (fun current x =>
          mul current (marker target other z x))
        initial = target <->
      initial = target := by
  induction xs generalizing initial with
  | nil =>
      simp
  | cons x xs ih =>
      rw [List.foldl_cons,
        ih _ (closed initial x initialInvariant),
        step initial x initialInvariant]

private theorem fold_absent_iff
    (mul : Fin 5 → Fin 5 → Fin 5)
    (target other output : Fin 5)
    (z : Nat)
    (step :
      ∀ current x,
        mul current (marker target other z x) = output ↔
          current = output ∧ x ≠ z)
    (xs : List Nat) (initial : Fin 5) :
    xs.foldl
        (fun current x =>
          mul current (marker target other z x))
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

private theorem fold_present_iff_of_invariant
    (mul : Fin 5 → Fin 5 → Fin 5)
    (target other output : Fin 5)
    (invariant : Fin 5 → Prop)
    (z : Nat)
    (closed :
      ∀ current x, invariant current →
        invariant (mul current (marker target other z x)))
    (step :
      ∀ current x, invariant current →
        (mul current (marker target other z x) = output ↔
          current = output ∨ x = z))
    (xs : List Nat) (initial : Fin 5)
    (initialInvariant : invariant initial) :
    xs.foldl
        (fun current x =>
          mul current (marker target other z x))
        initial = output ↔
      initial = output ∨ z ∈ xs := by
  induction xs generalizing initial with
  | nil =>
      simp
  | cons x xs ih =>
      rw [List.foldl_cons,
        ih _ (closed initial x initialInvariant),
        step initial x initialInvariant]
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

private theorem head_of_separation
    (G : Semigroup (Fin 5))
    (target other : Fin 5)
    (evalTarget :
      ∀ z (w : Word Nat),
        G.eval (marker target other z) w = target ↔
          w.head = z)
    (e : Identity Nat) (valid : e.SatisfiedBy G) :
    e.lhs.head = e.rhs.head := by
  have evaluated := valid (marker target other e.lhs.head)
  have rhsHead : e.rhs.head = e.lhs.head := by
    apply (evalTarget e.lhs.head e.rhs).mp
    rw [← evaluated]
    exact (evalTarget e.lhs.head e.lhs).mpr rfl
  exact rhsHead.symm

private theorem support_of_absence_separation
    (G : Semigroup (Fin 5))
    (target other output : Fin 5)
    (evalOutput :
      ∀ z (w : Word Nat),
        G.eval (marker target other z) w = output ↔
          z ∉ w.toList)
    (e : Identity Nat) (valid : e.SatisfiedBy G) :
    ∀ z, z ∈ e.lhs.toList ↔ z ∈ e.rhs.toList := by
  intro z
  have evaluated := valid (marker target other z)
  have absent :
      z ∉ e.lhs.toList ↔ z ∉ e.rhs.toList := by
    calc
      z ∉ e.lhs.toList ↔
          G.eval (marker target other z) e.lhs = output :=
        (evalOutput z e.lhs).symm
      _ ↔ G.eval (marker target other z) e.rhs = output := by
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
        G.eval (marker target other z) w = output ↔
          z ∈ w.toList)
    (e : Identity Nat) (valid : e.SatisfiedBy G) :
    ∀ z, z ∈ e.lhs.toList ↔ z ∈ e.rhs.toList := by
  intro z
  have evaluated := valid (marker target other z)
  calc
    z ∈ e.lhs.toList ↔
        G.eval (marker target other z) e.lhs = output :=
      (evalOutput z e.lhs).symm
    _ ↔ G.eval (marker target other z) e.rhs = output := by
      rw [evaluated]
    _ ↔ z ∈ e.rhs.toList := evalOutput z e.rhs

private def lengthState (markerValue : Fin 5) (n : Nat) : Fin 5 :=
  if n = 1 then markerValue else if n = 2 then 1 else 0

private theorem lengthFold
    (mul : Fin 5 -> Fin 5 -> Fin 5)
    (markerValue : Fin 5)
    (step :
      forall n, 0 < n ->
        mul (lengthState markerValue n) markerValue =
          lengthState markerValue (n + 1))
    (xs : List Nat) (acc : Nat) (accPos : 0 < acc) :
    xs.foldl (fun current _ => mul current markerValue)
        (lengthState markerValue acc) =
      lengthState markerValue (acc + xs.length) := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [List.foldl_cons, List.length_cons]
      rw [step acc accPos, ih (acc + 1) (by omega)]
      congr 1
      omega

private theorem lengthState_capped_injective
    (markerValue : Fin 5)
    (markerNeZero : Ne markerValue 0)
    (markerNeOne : Ne markerValue 1)
    {m n : Nat} (mPos : 0 < m) (nPos : 0 < n)
    (equal :
      lengthState markerValue m = lengthState markerValue n) :
    min m 3 = min n 3 := by
  by_cases hm1 : m = 1
  · subst m
    by_cases hn1 : n = 1
    · subst n
      rfl
    · by_cases hn2 : n = 2
      · subst n
        have markerEq : markerValue = 1 := by
          simpa [lengthState] using equal
        exact (markerNeOne markerEq).elim
      · have hn3 : 3 <= n := by omega
        have markerEq : markerValue = 0 := by
          simpa [lengthState, hn1, hn2] using equal
        exact (markerNeZero markerEq).elim
  · by_cases hm2 : m = 2
    · subst m
      by_cases hn1 : n = 1
      · subst n
        have markerEq : markerValue = 1 := by
          simpa [lengthState] using equal.symm
        exact (markerNeOne markerEq).elim
      · by_cases hn2 : n = 2
        · subst n
          rfl
        · have hn3 : 3 <= n := by omega
          have values := congrArg Fin.val equal
          simp [lengthState, hn1, hn2] at values
    · have hm3 : 3 <= m := by omega
      by_cases hn1 : n = 1
      · subst n
        have markerEq : markerValue = 0 := by
          simpa [lengthState, hm1, hm2] using equal.symm
        exact (markerNeZero markerEq).elim
      · by_cases hn2 : n = 2
        · subst n
          have values := congrArg Fin.val equal
          simp [lengthState, hm1, hm2] at values
        · have hn3 : 3 <= n := by omega
          simp [Nat.min_eq_right hm3, Nat.min_eq_right hn3]

private theorem capped_length_of_eval
    (G : Semigroup (Fin 5))
    (markerValue : Fin 5)
    (markerNeZero : Ne markerValue 0)
    (markerNeOne : Ne markerValue 1)
    (evalLength :
      forall w : Word Nat,
        G.eval (fun _ => markerValue) w =
          lengthState markerValue w.toList.length)
    (e : Identity Nat) (valid : e.SatisfiedBy G) :
    min e.lhs.toList.length 3 =
      min e.rhs.toList.length 3 := by
  have evaluated := valid (fun _ => markerValue)
  rw [evalLength, evalLength] at evaluated
  exact lengthState_capped_injective markerValue
    markerNeZero markerNeOne
    (by simp [Word.toList]) (by simp [Word.toList]) evaluated

namespace S5_520

private theorem headStep (z : Nat) (current : Fin 5) (x : Nat) :
    Generated.Catalogue.S5_520.mul current
        (marker 4 3 z x) = 4 <->
      current = 4 := by
  by_cases hx : x = z
  · subst x
    simp [marker]
    decide +revert
  · simp [marker, hx]
    decide +revert

private theorem evalHead (z : Nat) (w : Word Nat) :
    Generated.Catalogue.S5_520.table.semigroup.eval
        (marker 4 3 z) w = (4 : Fin 5) <->
      w.head = z := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current x =>
              Generated.Catalogue.S5_520.mul current
                (marker 4 3 z x))
            (marker 4 3 z head) = 4 <->
          head = z
      rw [fold_target_iff
        Generated.Catalogue.S5_520.mul 4 3 z (headStep z)]
      simp [marker]

private theorem supportStep
    (z : Nat) (current : Fin 5) (x : Nat) :
    Generated.Catalogue.S5_520.mul current
        (marker 2 3 z x) = 3 <->
      And (current = 3) (Ne x z) := by
  by_cases hx : x = z
  · subst x
    simp [marker]
    decide +revert
  · simp [marker, hx]
    decide +revert

private theorem evalSupport (z : Nat) (w : Word Nat) :
    Generated.Catalogue.S5_520.table.semigroup.eval
        (marker 2 3 z) w = (3 : Fin 5) ↔
      z ∉ w.toList := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current x =>
              Generated.Catalogue.S5_520.mul current
                (marker 2 3 z x))
            (marker 2 3 z head) = 3 ↔
          z ∉ head :: tail
      rw [fold_absent_iff
        Generated.Catalogue.S5_520.mul 2 3 3 z (supportStep z)]
      simp [marker, eq_comm]

private theorem lengthStep (n : Nat) (nPos : 0 < n) :
    Generated.Catalogue.S5_520.mul
        (lengthState 2 n) 2 =
      lengthState 2 (n + 1) := by
  by_cases hn1 : n = 1
  · subst n
    rfl
  · by_cases hn2 : n = 2
    · subst n
      rfl
    · have hn3 : 3 <= n := by omega
      simp [lengthState, hn1, hn2,
        show Ne n 0 by omega, show Ne (n + 1) 2 by omega,
        Generated.Catalogue.S5_520.mul]

private theorem evalLength (w : Word Nat) :
    Generated.Catalogue.S5_520.table.semigroup.eval
        (fun _ => (2 : Fin 5)) w =
      lengthState 2 w.toList.length := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current _ =>
              Generated.Catalogue.S5_520.mul current 2)
            2 =
          lengthState 2 (head :: tail).length
      simpa [lengthState, Nat.add_comm] using
        lengthFold Generated.Catalogue.S5_520.mul 2
          lengthStep tail 1 (by omega)

set_option maxRecDepth 100000 in
theorem models :
    Models Generated.Catalogue.S5_520.table.semigroup basis :=
  models_of_checks Generated.Catalogue.S5_520.table
    (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

theorem valid_head (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_520.table.semigroup) :
    e.lhs.head = e.rhs.head :=
  head_of_separation
    Generated.Catalogue.S5_520.table.semigroup
      4 3 evalHead e valid

theorem valid_support (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_520.table.semigroup) :
    forall z,
      List.Mem z e.lhs.toList <-> List.Mem z e.rhs.toList :=
  support_of_absence_separation
    Generated.Catalogue.S5_520.table.semigroup
      2 3 3 evalSupport e valid

theorem valid_capped_length (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_520.table.semigroup) :
    min e.lhs.toList.length 3 =
      min e.rhs.toList.length 3 :=
  capped_length_of_eval Generated.Catalogue.S5_520.table.semigroup
    2 (by decide) (by decide) evalLength e valid

theorem basis_complete :
    BasisFor Generated.Catalogue.S5_520.table.semigroup basis :=
  basis_complete_of_separates Generated.Catalogue.S5_520.table
    models valid_head valid_support valid_capped_length

theorem opposite_basis_complete :
    BasisFor Generated.Catalogue.S5_520.table.semigroup.opposite
      (reversedBasis basis) :=
  basis_complete.oppositeReversed

end S5_520

namespace S5_522

private theorem headStep (z : Nat) (current : Fin 5) (x : Nat) :
    Generated.Catalogue.S5_522.mul current
        (marker 3 4 z x) = 3 <->
      current = 3 := by
  by_cases hx : x = z
  · subst x
    simp [marker]
    decide +revert
  · simp [marker, hx]
    decide +revert

private theorem evalHead (z : Nat) (w : Word Nat) :
    Generated.Catalogue.S5_522.table.semigroup.eval
        (marker 3 4 z) w = (3 : Fin 5) <->
      w.head = z := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current x =>
              Generated.Catalogue.S5_522.mul current
                (marker 3 4 z x))
            (marker 3 4 z head) = 3 <->
          head = z
      rw [fold_target_iff
        Generated.Catalogue.S5_522.mul 3 4 z (headStep z)]
      simp [marker]

private theorem supportStep
    (z : Nat) (current : Fin 5) (x : Nat) :
    Generated.Catalogue.S5_522.mul current
        (marker 2 3 z x) = 3 <->
      And (current = 3) (Ne x z) := by
  by_cases hx : x = z
  · subst x
    simp [marker]
    decide +revert
  · simp [marker, hx]
    decide +revert

private theorem evalSupport (z : Nat) (w : Word Nat) :
    Generated.Catalogue.S5_522.table.semigroup.eval
        (marker 2 3 z) w = (3 : Fin 5) ↔
      z ∉ w.toList := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current x =>
              Generated.Catalogue.S5_522.mul current
                (marker 2 3 z x))
            (marker 2 3 z head) = 3 ↔
          z ∉ head :: tail
      rw [fold_absent_iff
        Generated.Catalogue.S5_522.mul 2 3 3 z (supportStep z)]
      simp [marker, eq_comm]

private theorem lengthStep (n : Nat) (nPos : 0 < n) :
    Generated.Catalogue.S5_522.mul
        (lengthState 2 n) 2 =
      lengthState 2 (n + 1) := by
  by_cases hn1 : n = 1
  · subst n
    rfl
  · by_cases hn2 : n = 2
    · subst n
      rfl
    · have hn3 : 3 <= n := by omega
      simp [lengthState, hn1, hn2,
        show Ne n 0 by omega, show Ne (n + 1) 2 by omega,
        Generated.Catalogue.S5_522.mul]

private theorem evalLength (w : Word Nat) :
    Generated.Catalogue.S5_522.table.semigroup.eval
        (fun _ => (2 : Fin 5)) w =
      lengthState 2 w.toList.length := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current _ =>
              Generated.Catalogue.S5_522.mul current 2)
            2 =
          lengthState 2 (head :: tail).length
      simpa [lengthState, Nat.add_comm] using
        lengthFold Generated.Catalogue.S5_522.mul 2
          lengthStep tail 1 (by omega)

set_option maxRecDepth 100000 in
theorem models :
    Models Generated.Catalogue.S5_522.table.semigroup basis :=
  models_of_checks Generated.Catalogue.S5_522.table
    (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

theorem valid_head (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_522.table.semigroup) :
    e.lhs.head = e.rhs.head :=
  head_of_separation
    Generated.Catalogue.S5_522.table.semigroup
      3 4 evalHead e valid

theorem valid_support (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_522.table.semigroup) :
    forall z,
      List.Mem z e.lhs.toList <-> List.Mem z e.rhs.toList :=
  support_of_absence_separation
    Generated.Catalogue.S5_522.table.semigroup
      2 3 3 evalSupport e valid

theorem valid_capped_length (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_522.table.semigroup) :
    min e.lhs.toList.length 3 =
      min e.rhs.toList.length 3 :=
  capped_length_of_eval Generated.Catalogue.S5_522.table.semigroup
    2 (by decide) (by decide) evalLength e valid

theorem basis_complete :
    BasisFor Generated.Catalogue.S5_522.table.semigroup basis :=
  basis_complete_of_separates Generated.Catalogue.S5_522.table
    models valid_head valid_support valid_capped_length

theorem opposite_basis_complete :
    BasisFor Generated.Catalogue.S5_522.table.semigroup.opposite
      (reversedBasis basis) :=
  basis_complete.oppositeReversed

end S5_522

namespace S5_524

private theorem headClosed
    (z : Nat) (current : Fin 5) (x : Nat)
    (_ : Ne current 4) :
    Ne (Generated.Catalogue.S5_524.mul current
        (marker 3 2 z x)) 4 := by
  by_cases hx : x = z
  · subst x
    simp [marker]
    decide +revert
  · simp [marker, hx]
    decide +revert

private theorem headStep
    (z : Nat) (current : Fin 5) (x : Nat)
    (currentReachable : Ne current 4) :
    Generated.Catalogue.S5_524.mul current
        (marker 3 2 z x) = 3 <->
      current = 3 := by
  by_cases hx : x = z
  · subst x
    simp [marker]
    exact by
      revert current
      decide
  · simp [marker, hx]
    exact by
      revert current
      decide

private theorem evalHead (z : Nat) (w : Word Nat) :
    Generated.Catalogue.S5_524.table.semigroup.eval
        (marker 3 2 z) w = (3 : Fin 5) <->
      w.head = z := by
  cases w with
  | mk head tail =>
      have headReachable :
          Ne (marker 3 2 z head) (4 : Fin 5) := by
        by_cases hhead : head = z
        · simp [marker, hhead]
        · simp [marker, hhead]
      change
        tail.foldl
            (fun current x =>
              Generated.Catalogue.S5_524.mul current
                (marker 3 2 z x))
            (marker 3 2 z head) = 3 <->
          head = z
      rw [fold_target_iff_of_invariant
        Generated.Catalogue.S5_524.mul 3 2
        (fun current => Ne current 4) z
        (headClosed z) (headStep z) tail
        (marker 3 2 z head) headReachable]
      simp [marker]

private theorem supportStep
    (z : Nat) (current : Fin 5) (x : Nat) :
    Generated.Catalogue.S5_524.mul current
        (marker 2 4 z x) = 4 <->
      And (current = 4) (Ne x z) := by
  by_cases hx : x = z
  · subst x
    simp [marker]
    decide +revert
  · simp [marker, hx]
    decide +revert

private theorem evalSupport (z : Nat) (w : Word Nat) :
    Generated.Catalogue.S5_524.table.semigroup.eval
        (marker 2 4 z) w = (4 : Fin 5) ↔
      z ∉ w.toList := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current x =>
              Generated.Catalogue.S5_524.mul current
                (marker 2 4 z x))
            (marker 2 4 z head) = 4 ↔
          z ∉ head :: tail
      rw [fold_absent_iff
        Generated.Catalogue.S5_524.mul 2 4 4 z (supportStep z)]
      simp [marker, eq_comm]

private theorem lengthStep (n : Nat) (nPos : 0 < n) :
    Generated.Catalogue.S5_524.mul
        (lengthState 2 n) 2 =
      lengthState 2 (n + 1) := by
  by_cases hn1 : n = 1
  · subst n
    rfl
  · by_cases hn2 : n = 2
    · subst n
      rfl
    · have hn3 : 3 <= n := by omega
      simp [lengthState, hn1, hn2,
        show Ne n 0 by omega, show Ne (n + 1) 2 by omega,
        Generated.Catalogue.S5_524.mul]

private theorem evalLength (w : Word Nat) :
    Generated.Catalogue.S5_524.table.semigroup.eval
        (fun _ => (2 : Fin 5)) w =
      lengthState 2 w.toList.length := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current _ =>
              Generated.Catalogue.S5_524.mul current 2)
            2 =
          lengthState 2 (head :: tail).length
      simpa [lengthState, Nat.add_comm] using
        lengthFold Generated.Catalogue.S5_524.mul 2
          lengthStep tail 1 (by omega)

set_option maxRecDepth 100000 in
theorem models :
    Models Generated.Catalogue.S5_524.table.semigroup basis :=
  models_of_checks Generated.Catalogue.S5_524.table
    (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

theorem valid_head (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_524.table.semigroup) :
    e.lhs.head = e.rhs.head :=
  head_of_separation
    Generated.Catalogue.S5_524.table.semigroup
      3 2 evalHead e valid

theorem valid_support (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_524.table.semigroup) :
    forall z,
      List.Mem z e.lhs.toList <-> List.Mem z e.rhs.toList :=
  support_of_absence_separation
    Generated.Catalogue.S5_524.table.semigroup
      2 4 4 evalSupport e valid

theorem valid_capped_length (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_524.table.semigroup) :
    min e.lhs.toList.length 3 =
      min e.rhs.toList.length 3 :=
  capped_length_of_eval Generated.Catalogue.S5_524.table.semigroup
    2 (by decide) (by decide) evalLength e valid

theorem basis_complete :
    BasisFor Generated.Catalogue.S5_524.table.semigroup basis :=
  basis_complete_of_separates Generated.Catalogue.S5_524.table
    models valid_head valid_support valid_capped_length

theorem opposite_basis_complete :
    BasisFor Generated.Catalogue.S5_524.table.semigroup.opposite
      (reversedBasis basis) :=
  basis_complete.oppositeReversed

end S5_524

namespace S5_534

private theorem headStep (z : Nat) (current : Fin 5) (x : Nat) :
    Generated.Catalogue.S5_534.mul current
        (marker 3 2 z x) = 3 <->
      current = 3 := by
  by_cases hx : x = z
  · subst x
    simp [marker]
    decide +revert
  · simp [marker, hx]
    decide +revert

private theorem evalHead (z : Nat) (w : Word Nat) :
    Generated.Catalogue.S5_534.table.semigroup.eval
        (marker 3 2 z) w = (3 : Fin 5) <->
      w.head = z := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current x =>
              Generated.Catalogue.S5_534.mul current
                (marker 3 2 z x))
            (marker 3 2 z head) = 3 <->
          head = z
      rw [fold_target_iff
        Generated.Catalogue.S5_534.mul 3 2 z (headStep z)]
      simp [marker]

private theorem supportStep
    (z : Nat) (current : Fin 5) (x : Nat) :
    Generated.Catalogue.S5_534.mul current
        (marker 4 3 z x) = 3 <->
      And (current = 3) (Ne x z) := by
  by_cases hx : x = z
  · subst x
    simp [marker]
    decide +revert
  · simp [marker, hx]
    decide +revert

private theorem evalSupport (z : Nat) (w : Word Nat) :
    Generated.Catalogue.S5_534.table.semigroup.eval
        (marker 4 3 z) w = (3 : Fin 5) ↔
      z ∉ w.toList := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current x =>
              Generated.Catalogue.S5_534.mul current
                (marker 4 3 z x))
            (marker 4 3 z head) = 3 ↔
          z ∉ head :: tail
      rw [fold_absent_iff
        Generated.Catalogue.S5_534.mul 4 3 3 z (supportStep z)]
      simp [marker, eq_comm]

private theorem lengthStep (n : Nat) (nPos : 0 < n) :
    Generated.Catalogue.S5_534.mul
        (lengthState 2 n) 2 =
      lengthState 2 (n + 1) := by
  by_cases hn1 : n = 1
  · subst n
    rfl
  · by_cases hn2 : n = 2
    · subst n
      rfl
    · have hn3 : 3 <= n := by omega
      simp [lengthState, hn1, hn2,
        show Ne n 0 by omega, show Ne (n + 1) 2 by omega,
        Generated.Catalogue.S5_534.mul]

private theorem evalLength (w : Word Nat) :
    Generated.Catalogue.S5_534.table.semigroup.eval
        (fun _ => (2 : Fin 5)) w =
      lengthState 2 w.toList.length := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current _ =>
              Generated.Catalogue.S5_534.mul current 2)
            2 =
          lengthState 2 (head :: tail).length
      simpa [lengthState, Nat.add_comm] using
        lengthFold Generated.Catalogue.S5_534.mul 2
          lengthStep tail 1 (by omega)

set_option maxRecDepth 100000 in
theorem models :
    Models Generated.Catalogue.S5_534.table.semigroup basis :=
  models_of_checks Generated.Catalogue.S5_534.table
    (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

theorem valid_head (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_534.table.semigroup) :
    e.lhs.head = e.rhs.head :=
  head_of_separation
    Generated.Catalogue.S5_534.table.semigroup
      3 2 evalHead e valid

theorem valid_support (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_534.table.semigroup) :
    forall z,
      List.Mem z e.lhs.toList <-> List.Mem z e.rhs.toList :=
  support_of_absence_separation
    Generated.Catalogue.S5_534.table.semigroup
      4 3 3 evalSupport e valid

theorem valid_capped_length (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_534.table.semigroup) :
    min e.lhs.toList.length 3 =
      min e.rhs.toList.length 3 :=
  capped_length_of_eval Generated.Catalogue.S5_534.table.semigroup
    2 (by decide) (by decide) evalLength e valid

theorem basis_complete :
    BasisFor Generated.Catalogue.S5_534.table.semigroup basis :=
  basis_complete_of_separates Generated.Catalogue.S5_534.table
    models valid_head valid_support valid_capped_length

theorem opposite_basis_complete :
    BasisFor Generated.Catalogue.S5_534.table.semigroup.opposite
      (reversedBasis basis) :=
  basis_complete.oppositeReversed

end S5_534

namespace S5_537

private theorem headStep (z : Nat) (current : Fin 5) (x : Nat) :
    Generated.Catalogue.S5_537.mul current
        (marker 4 3 z x) = 4 <->
      current = 4 := by
  by_cases hx : x = z
  · subst x
    simp [marker]
    decide +revert
  · simp [marker, hx]
    decide +revert

private theorem evalHead (z : Nat) (w : Word Nat) :
    Generated.Catalogue.S5_537.table.semigroup.eval
        (marker 4 3 z) w = (4 : Fin 5) <->
      w.head = z := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current x =>
              Generated.Catalogue.S5_537.mul current
                (marker 4 3 z x))
            (marker 4 3 z head) = 4 <->
          head = z
      rw [fold_target_iff
        Generated.Catalogue.S5_537.mul 4 3 z (headStep z)]
      simp [marker]

private theorem supportClosed
    (z : Nat) (current : Fin 5) (x : Nat)
    (_ : Ne current 4) :
    Ne (Generated.Catalogue.S5_537.mul current
        (marker 3 2 z x)) 4 := by
  by_cases hx : x = z
  · subst x
    simp [marker]
    decide +revert
  · simp [marker, hx]
    decide +revert

private theorem supportStep
    (z : Nat) (current : Fin 5) (x : Nat)
    (currentReachable : Ne current 4) :
    Generated.Catalogue.S5_537.mul current
        (marker 3 2 z x) = 3 <->
      Or (current = 3) (x = z) := by
  by_cases hx : x = z
  · subst x
    simp [marker]
    exact by
      revert current
      decide
  · simp [marker, hx]
    exact by
      revert current
      decide

private theorem evalSupport (z : Nat) (w : Word Nat) :
    Generated.Catalogue.S5_537.table.semigroup.eval
        (marker 3 2 z) w = (3 : Fin 5) ↔
      z ∈ w.toList := by
  cases w with
  | mk head tail =>
      have headReachable :
          Ne (marker 3 2 z head) (4 : Fin 5) := by
        by_cases hhead : head = z
        · simp [marker, hhead]
        · simp [marker, hhead]
      change
        tail.foldl
            (fun current x =>
              Generated.Catalogue.S5_537.mul current
                (marker 3 2 z x))
            (marker 3 2 z head) = 3 ↔
          z ∈ head :: tail
      rw [fold_present_iff_of_invariant
        Generated.Catalogue.S5_537.mul 3 2 3
        (fun current => Ne current 4) z
        (supportClosed z) (supportStep z) tail
        (marker 3 2 z head) headReachable]
      simp [marker, eq_comm]

private theorem lengthStep (n : Nat) (nPos : 0 < n) :
    Generated.Catalogue.S5_537.mul
        (lengthState 2 n) 2 =
      lengthState 2 (n + 1) := by
  by_cases hn1 : n = 1
  · subst n
    rfl
  · by_cases hn2 : n = 2
    · subst n
      rfl
    · have hn3 : 3 <= n := by omega
      simp [lengthState, hn1, hn2,
        show Ne n 0 by omega, show Ne (n + 1) 2 by omega,
        Generated.Catalogue.S5_537.mul]

private theorem evalLength (w : Word Nat) :
    Generated.Catalogue.S5_537.table.semigroup.eval
        (fun _ => (2 : Fin 5)) w =
      lengthState 2 w.toList.length := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current _ =>
              Generated.Catalogue.S5_537.mul current 2)
            2 =
          lengthState 2 (head :: tail).length
      simpa [lengthState, Nat.add_comm] using
        lengthFold Generated.Catalogue.S5_537.mul 2
          lengthStep tail 1 (by omega)

set_option maxRecDepth 100000 in
theorem models :
    Models Generated.Catalogue.S5_537.table.semigroup basis :=
  models_of_checks Generated.Catalogue.S5_537.table
    (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

theorem valid_head (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_537.table.semigroup) :
    e.lhs.head = e.rhs.head :=
  head_of_separation
    Generated.Catalogue.S5_537.table.semigroup
      4 3 evalHead e valid

theorem valid_support (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_537.table.semigroup) :
    forall z,
      List.Mem z e.lhs.toList <-> List.Mem z e.rhs.toList :=
  support_of_presence_separation
    Generated.Catalogue.S5_537.table.semigroup
      3 2 3 evalSupport e valid

theorem valid_capped_length (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_537.table.semigroup) :
    min e.lhs.toList.length 3 =
      min e.rhs.toList.length 3 :=
  capped_length_of_eval Generated.Catalogue.S5_537.table.semigroup
    2 (by decide) (by decide) evalLength e valid

theorem basis_complete :
    BasisFor Generated.Catalogue.S5_537.table.semigroup basis :=
  basis_complete_of_separates Generated.Catalogue.S5_537.table
    models valid_head valid_support valid_capped_length

theorem opposite_basis_complete :
    BasisFor Generated.Catalogue.S5_537.table.semigroup.opposite
      (reversedBasis basis) :=
  basis_complete.oppositeReversed

end S5_537

end SemigroupBasis.CoRoots.S5_520Family
