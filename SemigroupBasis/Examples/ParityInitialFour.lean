import SemigroupBasis.Examples.ParityInitialFourSyntax
import SemigroupBasis.Opposite

namespace SemigroupBasis.Examples

open SemigroupBasis

/-- Exact zero-based multiplication for the catalogue table
`[[1,2,3,4],[2,1,3,4],[3,3,3,3],[4,4,4,4]]`. The first two elements form
`C₂`; the last two are left zeros. -/
def parityInitialFourMul (a b : Fin 4) : Fin 4 :=
  if a = 0 then b else
    if a = 1 then
      if b = 0 then 1 else if b = 1 then 0 else b
    else a

/-- The root catalogue representative `S4_95`. -/
def parityInitialFour : FiniteTable where
  order := 4
  mul := parityInitialFourMul
  assoc := by decide

private theorem parityInitialMul_power (a : Fin 4) :
    a =
      parityInitialFourMul
        (parityInitialFourMul a a) a := by
  decide +revert

private theorem parityInitialMul_gather (a b : Fin 4) :
    parityInitialFourMul
        (parityInitialFourMul a b) a =
      parityInitialFourMul
        (parityInitialFourMul a a) b := by
  decide +revert

theorem parityInitialBasis_models :
    Models parityInitialFour.semigroup parityInitialBasis := by
  intro e he
  simp only [parityInitialBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · intro valuation
    change
      valuation 0 =
        parityInitialFourMul
          (parityInitialFourMul (valuation 0) (valuation 0))
          (valuation 0)
    exact parityInitialMul_power (valuation 0)
  · intro valuation
    change
      parityInitialFourMul
          (parityInitialFourMul (valuation 0) (valuation 1))
          (valuation 0) =
        parityInitialFourMul
          (parityInitialFourMul (valuation 0) (valuation 0))
          (valuation 1)
    exact parityInitialMul_gather (valuation 0) (valuation 1)

/-- Evaluation of a possibly empty list, using the identity element `0`. -/
private def parityInitialListEval
    (valuation : Nat → Fin 4) (xs : List Nat) : Fin 4 :=
  xs.foldl
    (fun current x => parityInitialFourMul current (valuation x)) 0

private theorem parityInitialMul_left_identity (b : Fin 4) :
    parityInitialFourMul 0 b = b := by
  simp [parityInitialFourMul]

private theorem parityInitialMul_right_identity (a : Fin 4) :
    parityInitialFourMul a 0 = a := by
  decide +revert

private theorem parityInitialMul_left_two (b : Fin 4) :
    parityInitialFourMul 2 b = 2 := by
  simp [parityInitialFourMul]

private theorem parityInitialMul_left_three (b : Fin 4) :
    parityInitialFourMul 3 b = 3 := by
  simp [parityInitialFourMul]

private theorem parityInitialFold_left_two
    (valuation : Nat → Fin 4) (xs : List Nat) :
    xs.foldl
        (fun current x =>
          parityInitialFourMul current (valuation x)) 2 = 2 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simpa [List.foldl_cons, parityInitialMul_left_two] using ih

private theorem parityInitialFold_left_three
    (valuation : Nat → Fin 4) (xs : List Nat) :
    xs.foldl
        (fun current x =>
          parityInitialFourMul current (valuation x)) 3 = 3 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simpa [List.foldl_cons, parityInitialMul_left_three] using ih

private theorem parityInitialFold_all_zero
    (valuation : Nat → Fin 4) :
    ∀ (xs : List Nat) (acc : Fin 4),
      (∀ z, z ∈ xs → valuation z = 0) →
      xs.foldl
          (fun current z =>
            parityInitialFourMul current (valuation z)) acc = acc
  | [], _, _ => rfl
  | z :: zs, acc, hall => by
      simp only [List.foldl_cons]
      rw [hall z (List.Mem.head zs), parityInitialMul_right_identity]
      exact parityInitialFold_all_zero valuation zs acc
        (fun y hy => hall y (List.Mem.tail z hy))

private theorem parityInitialListEval_cons_two
    (valuation : Nat → Fin 4) (x : Nat) (xs : List Nat)
    (hx : valuation x = 2) :
    parityInitialListEval valuation (x :: xs) = 2 := by
  unfold parityInitialListEval
  simp only [List.foldl_cons]
  rw [parityInitialMul_left_identity, hx]
  exact parityInitialFold_left_two valuation xs

private theorem parityInitialListEval_cons_three
    (valuation : Nat → Fin 4) (x : Nat) (xs : List Nat)
    (hx : valuation x = 3) :
    parityInitialListEval valuation (x :: xs) = 3 := by
  unfold parityInitialListEval
  simp only [List.foldl_cons]
  rw [parityInitialMul_left_identity, hx]
  exact parityInitialFold_left_three valuation xs

private theorem parityInitialListEval_cons_zero
    (valuation : Nat → Fin 4) (x : Nat) (xs : List Nat)
    (hx : valuation x = 0) :
    parityInitialListEval valuation (x :: xs) =
      parityInitialListEval valuation xs := by
  simp [parityInitialListEval, hx, parityInitialMul_left_identity]

private theorem parityInitialListEval_single_one
    (valuation : Nat → Fin 4) (x : Nat) (xs : List Nat)
    (hx : valuation x = 1)
    (hrest : ∀ z, z ∈ xs → valuation z = 0) :
    parityInitialListEval valuation (x :: xs) = 1 := by
  unfold parityInitialListEval
  simp only [List.foldl_cons]
  rw [parityInitialMul_left_identity, hx]
  exact parityInitialFold_all_zero valuation xs 1 hrest

private theorem parityInitialListEval_double_one
    (valuation : Nat → Fin 4) (x : Nat) (xs : List Nat)
    (hx : valuation x = 1)
    (hrest : ∀ z, z ∈ xs → valuation z = 0) :
    parityInitialListEval valuation (x :: x :: xs) = 0 := by
  unfold parityInitialListEval
  simp only [List.foldl_cons]
  rw [parityInitialMul_left_identity, hx]
  change
    xs.foldl
        (fun current z =>
          parityInitialFourMul current (valuation z))
        (parityInitialFourMul 1 1) = 0
  have oneSquare :
      parityInitialFourMul 1 1 = (0 : Fin 4) := by decide
  rw [oneSquare]
  exact parityInitialFold_all_zero valuation xs 0 hrest

private theorem parityInitialFold_congr
    (v₁ v₂ : Nat → Fin 4) :
    ∀ (xs : List Nat) (acc : Fin 4),
      (∀ x, x ∈ xs → v₁ x = v₂ x) →
      xs.foldl
          (fun current x =>
            parityInitialFourMul current (v₁ x)) acc =
        xs.foldl
          (fun current x =>
            parityInitialFourMul current (v₂ x)) acc
  | [], _, _ => rfl
  | x :: xs, acc, agree => by
      simp only [List.foldl_cons]
      rw [agree x (List.Mem.head xs)]
      exact parityInitialFold_congr v₁ v₂ xs
        (parityInitialFourMul acc (v₂ x))
        (fun y hy => agree y (List.Mem.tail x hy))

private theorem parityInitialListEval_congr
    (v₁ v₂ : Nat → Fin 4) (xs : List Nat)
    (agree : ∀ x, x ∈ xs → v₁ x = v₂ x) :
    parityInitialListEval v₁ xs =
      parityInitialListEval v₂ xs :=
  parityInitialFold_congr v₁ v₂ xs 0 agree

private theorem parityInitialEval_eq_listEval
    (valuation : Nat → Fin 4) (w : Word Nat) :
    parityInitialFour.semigroup.eval valuation w =
      parityInitialListEval valuation w.toList := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current x =>
              parityInitialFourMul current (valuation x))
            (valuation head) =
          tail.foldl
            (fun current x =>
              parityInitialFourMul current (valuation x))
            (parityInitialFourMul 0 (valuation head))
      rw [parityInitialMul_left_identity]

private theorem parityInitialNormal_heads_eq
    (x y : Nat) (xs ys : List Nat)
    (equalEval :
      ∀ valuation : Nat → Fin 4,
        parityInitialListEval valuation (x :: xs) =
          parityInitialListEval valuation (y :: ys)) :
    x = y := by
  apply Decidable.byContradiction
  intro hxy
  let valuation : Nat → Fin 4 :=
    fun z => if z = x then 2 else if z = y then 3 else 0
  have h := equalEval valuation
  have leftValue :
      parityInitialListEval valuation (x :: xs) = 2 :=
    parityInitialListEval_cons_two valuation x xs (by
      simp [valuation])
  have rightValue :
      parityInitialListEval valuation (y :: ys) = 3 :=
    parityInitialListEval_cons_three valuation y ys (by
      simp [valuation, Ne.symm hxy])
  rw [leftValue, rightValue] at h
  exact (by decide : (2 : Fin 4) ≠ 3) h

/-- Exact-table separators distinguish all first-occurrence/parity block
normal forms. -/
private theorem parityInitialNormal_eq_of_eval_eq
    {xs ys : List Nat}
    (normalX : ParityInitialNormal xs)
    (normalY : ParityInitialNormal ys)
    (equalEval :
      ∀ valuation : Nat → Fin 4,
        parityInitialListEval valuation xs =
          parityInitialListEval valuation ys) :
    xs = ys := by
  induction normalX generalizing ys with
  | nil =>
      cases normalY with
      | nil => rfl
      | single y ys hy _ =>
          let valuation : Nat → Fin 4 :=
            fun z => if z = y then 2 else 0
          have h := equalEval valuation
          have rightValue :
              parityInitialListEval valuation (y :: ys) = 2 :=
            parityInitialListEval_cons_two valuation y ys (by
              simp [valuation])
          change (0 : Fin 4) =
            parityInitialListEval valuation (y :: ys) at h
          rw [rightValue] at h
          exact False.elim ((by decide : (0 : Fin 4) ≠ 2) h)
      | double y ys hy _ =>
          let valuation : Nat → Fin 4 :=
            fun z => if z = y then 2 else 0
          have h := equalEval valuation
          have rightValue :
              parityInitialListEval valuation (y :: y :: ys) = 2 :=
            parityInitialListEval_cons_two valuation y (y :: ys) (by
              simp [valuation])
          change (0 : Fin 4) =
            parityInitialListEval valuation (y :: y :: ys) at h
          rw [rightValue] at h
          exact False.elim ((by decide : (0 : Fin 4) ≠ 2) h)
  | single x xs normalTail xNotMem ih =>
      cases normalY with
      | nil =>
          let valuation : Nat → Fin 4 :=
            fun z => if z = x then 2 else 0
          have h := equalEval valuation
          have leftValue :
              parityInitialListEval valuation (x :: xs) = 2 :=
            parityInitialListEval_cons_two valuation x xs (by
              simp [valuation])
          change
            parityInitialListEval valuation (x :: xs) =
              (0 : Fin 4) at h
          rw [leftValue] at h
          exact False.elim ((by decide : (2 : Fin 4) ≠ 0) h)
      | single y ys normalRight yNotMem =>
          have heads : x = y :=
            parityInitialNormal_heads_eq x y xs ys equalEval
          subst y
          have tailsEqual :
              ∀ valuation : Nat → Fin 4,
                parityInitialListEval valuation xs =
                  parityInitialListEval valuation ys := by
            intro valuation
            let masked : Nat → Fin 4 :=
              fun z => if z = x then 0 else valuation z
            have fullEqual := equalEval masked
            have maskedX : masked x = 0 := by simp [masked]
            rw [parityInitialListEval_cons_zero masked x xs maskedX,
              parityInitialListEval_cons_zero
                masked x ys maskedX] at fullEqual
            calc
              parityInitialListEval valuation xs =
                  parityInitialListEval masked xs := by
                    apply parityInitialListEval_congr
                    intro z hz
                    have hzx : z ≠ x := by
                      intro h
                      apply xNotMem
                      simpa [h] using hz
                    simp [masked, hzx]
              _ = parityInitialListEval masked ys := fullEqual
              _ = parityInitialListEval valuation ys := by
                    apply parityInitialListEval_congr
                    intro z hz
                    have hzx : z ≠ x := by
                      intro h
                      apply yNotMem
                      simpa [h] using hz
                    simp [masked, hzx]
          congr 1
          exact ih normalRight tailsEqual
      | double y ys normalRight yNotMem =>
          have heads : x = y :=
            parityInitialNormal_heads_eq x y xs (y :: ys) equalEval
          subst y
          let valuation : Nat → Fin 4 :=
            fun z => if z = x then 1 else 0
          have h := equalEval valuation
          have leftValue :
              parityInitialListEval valuation (x :: xs) = 1 :=
            parityInitialListEval_single_one valuation x xs (by
              simp [valuation]) (by
                intro z hz
                have hzx : z ≠ x := by
                  intro h
                  apply xNotMem
                  simpa [h] using hz
                simp [valuation, hzx])
          have rightValue :
              parityInitialListEval valuation (x :: x :: ys) = 0 :=
            parityInitialListEval_double_one valuation x ys (by
              simp [valuation]) (by
                intro z hz
                have hzx : z ≠ x := by
                  intro h
                  apply yNotMem
                  simpa [h] using hz
                simp [valuation, hzx])
          rw [leftValue, rightValue] at h
          exact False.elim ((by decide : (1 : Fin 4) ≠ 0) h)
  | double x xs normalTail xNotMem ih =>
      cases normalY with
      | nil =>
          let valuation : Nat → Fin 4 :=
            fun z => if z = x then 2 else 0
          have h := equalEval valuation
          have leftValue :
              parityInitialListEval valuation (x :: x :: xs) = 2 :=
            parityInitialListEval_cons_two valuation x (x :: xs) (by
              simp [valuation])
          change
            parityInitialListEval valuation (x :: x :: xs) =
              (0 : Fin 4) at h
          rw [leftValue] at h
          exact False.elim ((by decide : (2 : Fin 4) ≠ 0) h)
      | single y ys normalRight yNotMem =>
          have heads : x = y :=
            parityInitialNormal_heads_eq x y (x :: xs) ys equalEval
          subst y
          let valuation : Nat → Fin 4 :=
            fun z => if z = x then 1 else 0
          have h := equalEval valuation
          have leftValue :
              parityInitialListEval valuation (x :: x :: xs) = 0 :=
            parityInitialListEval_double_one valuation x xs (by
              simp [valuation]) (by
                intro z hz
                have hzx : z ≠ x := by
                  intro h
                  apply xNotMem
                  simpa [h] using hz
                simp [valuation, hzx])
          have rightValue :
              parityInitialListEval valuation (x :: ys) = 1 :=
            parityInitialListEval_single_one valuation x ys (by
              simp [valuation]) (by
                intro z hz
                have hzx : z ≠ x := by
                  intro h
                  apply yNotMem
                  simpa [h] using hz
                simp [valuation, hzx])
          rw [leftValue, rightValue] at h
          exact False.elim ((by decide : (0 : Fin 4) ≠ 1) h)
      | double y ys normalRight yNotMem =>
          have heads : x = y :=
            parityInitialNormal_heads_eq
              x y (x :: xs) (y :: ys) equalEval
          subst y
          have tailsEqual :
              ∀ valuation : Nat → Fin 4,
                parityInitialListEval valuation xs =
                  parityInitialListEval valuation ys := by
            intro valuation
            let masked : Nat → Fin 4 :=
              fun z => if z = x then 0 else valuation z
            have fullEqual := equalEval masked
            have maskedX : masked x = 0 := by simp [masked]
            rw [parityInitialListEval_cons_zero
                masked x (x :: xs) maskedX,
              parityInitialListEval_cons_zero masked x xs maskedX,
              parityInitialListEval_cons_zero
                masked x (x :: ys) maskedX,
              parityInitialListEval_cons_zero
                masked x ys maskedX] at fullEqual
            calc
              parityInitialListEval valuation xs =
                  parityInitialListEval masked xs := by
                    apply parityInitialListEval_congr
                    intro z hz
                    have hzx : z ≠ x := by
                      intro h
                      apply xNotMem
                      simpa [h] using hz
                    simp [masked, hzx]
              _ = parityInitialListEval masked ys := fullEqual
              _ = parityInitialListEval valuation ys := by
                    apply parityInitialListEval_congr
                    intro z hz
                    have hzx : z ≠ x := by
                      intro h
                      apply yNotMem
                      simpa [h] using hz
                    simp [masked, hzx]
          congr 2
          exact ih normalRight tailsEqual

/-- Unrestricted completeness over `Nat` variables. Every word derives to a
first-occurrence block form with parity-sized blocks, and the exact
four-element table separates all distinct canonical forms. -/
theorem parityInitialBasis_complete :
    BasisFor parityInitialFour.semigroup parityInitialBasis := by
  refine ⟨parityInitialBasis_models, ?_⟩
  intro e valid
  have lhsNormal := parityInitialDerivesNormal e.lhs
  have rhsNormal := parityInitialDerivesNormal e.rhs
  cases hl : parityInitialNormalList e.lhs.toList with
  | nil =>
      exact False.elim <|
        parityInitialNormalList_cons_ne_nil
          e.lhs.head e.lhs.tail (by
            simpa [Word.toList] using hl)
  | cons x xs =>
      cases hr : parityInitialNormalList e.rhs.toList with
      | nil =>
          exact False.elim <|
            parityInitialNormalList_cons_ne_nil
              e.rhs.head e.rhs.tail (by
                simpa [Word.toList] using hr)
      | cons y ys =>
          rw [hl] at lhsNormal
          rw [hr] at rhsNormal
          have reducedEvalEqual :
              ∀ valuation : Nat → Fin 4,
                parityInitialListEval valuation (x :: xs) =
                  parityInitialListEval valuation (y :: ys) := by
            intro valuation
            have lhsSound :=
              lhsNormal.sound parityInitialBasis_models valuation
            have rhsSound :=
              rhsNormal.sound parityInitialBasis_models valuation
            rw [parityInitialEval_eq_listEval] at lhsSound rhsSound
            exact lhsSound.symm.trans ((valid valuation).trans rhsSound)
          have leftForm :
              ParityInitialNormal (x :: xs) := by
            rw [← hl]
            exact parityInitialNormalList_normal e.lhs.toList
          have rightForm :
              ParityInitialNormal (y :: ys) := by
            rw [← hr]
            exact parityInitialNormalList_normal e.rhs.toList
          have reducedEqual : x :: xs = y :: ys :=
            parityInitialNormal_eq_of_eval_eq
              leftForm rightForm reducedEvalEqual
          cases reducedEqual
          exact Derives.trans lhsNormal (Derives.symm rhsNormal)

def parityInitialOppositeBasis : List (Identity Nat) :=
  reversedBasis parityInitialBasis

theorem parityInitialOppositeBasis_complete :
    BasisFor parityInitialFour.semigroup.opposite
      parityInitialOppositeBasis := by
  simpa [parityInitialOppositeBasis] using
    parityInitialBasis_complete.oppositeReversed

end SemigroupBasis.Examples
