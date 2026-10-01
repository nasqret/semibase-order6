import SemigroupBasis.Examples.CommutativeParitySupportFour
import SemigroupBasis.Generated.CatalogueOrder4

namespace SemigroupBasis.Generated.S4_30FamilyProposal

open SemigroupBasis
open SemigroupBasis.Examples

private theorem complete_of_paritySupport_invariants
    (T : FiniteTable)
    (models : Models T.semigroup commutativeParitySupportBasis)
    (support :
      ∀ (e : Identity Nat), e.SatisfiedBy T.semigroup →
        ∀ z, z ∈ e.lhs.toList ↔ z ∈ e.rhs.toList)
    (parity :
      ∀ (e : Identity Nat), e.SatisfiedBy T.semigroup →
        ∀ z, e.lhs.toList.count z % 2 =
          e.rhs.toList.count z % 2)
    (singleton :
      ∀ (e : Identity Nat), e.SatisfiedBy T.semigroup →
        (e.lhs.toList.length = 1 ↔ e.rhs.toList.length = 1)) :
    BasisFor T.semigroup commutativeParitySupportBasis := by
  refine ⟨models, ?_⟩
  intro e valid
  have reducedPerm :=
    paritySupportReduce_perm
      (by simp [Word.toList]) (by simp [Word.toList])
      (support e valid) (parity e valid) (singleton e valid)
  have lhsNormal := paritySupportDerivesNormal e.lhs
  have rhsNormal := paritySupportDerivesNormal e.rhs
  cases hl : paritySupportReduce e.lhs.toList with
  | nil =>
      have notEmpty : paritySupportReduce e.lhs.toList ≠ [] := by
        intro hempty
        unfold paritySupportReduce at hempty
        cases hp : positiveParityReduce e.lhs.toList with
        | nil =>
            have present :
                e.lhs.head ∈ positiveParityReduce e.lhs.toList :=
              (mem_positiveParityReduce_iff _ _).mpr
                (by simp [Word.toList])
            simpa [hp] using present
        | cons x xs =>
            cases xs with
            | nil =>
                split at hempty <;> simp_all
            | cons y ys =>
                simp [hp] at hempty
      exact False.elim (notEmpty hl)
  | cons x xs =>
      cases hr : paritySupportReduce e.rhs.toList with
      | nil =>
          rw [hl, hr] at reducedPerm
          exact False.elim (List.not_perm_cons_nil reducedPerm)
      | cons y ys =>
          rw [hl] at lhsNormal
          rw [hr] at rhsNormal
          rw [hl, hr] at reducedPerm
          exact Derives.trans lhsNormal <|
            Derives.trans
              (paritySupportDerivesPermutation _ _ (by
                simpa using reducedPerm))
              (Derives.symm rhsNormal)

private def parityState (n : Nat) : Fin 4 :=
  if n % 2 = 0 then 0 else 1

private def singletonState (n : Nat) : Fin 4 :=
  if n = 1 then 2 else parityState n

namespace S4_30

/-- Zero-based form of the stored `S4_30` table. -/
def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then
    if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 1 else 0
  else if a = 1 then
    if b = 0 then 1 else if b = 1 then 0 else if b = 2 then 0 else 1
  else if a = 2 then
    if b = 0 then 1 else if b = 1 then 0 else if b = 2 then 0 else 1
  else
    if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 1 else 3

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

theorem table_eq_canonical_catalogue :
    table = SemigroupBasis.Generated.Catalogue.S4_30.table := rfl

private theorem mul_commutative (a b : Fin 4) :
    mul a b = mul b a := by
  decide +revert

private theorem mul_power (a : Fin 4) :
    mul a a = mul (mul (mul a a) a) a := by
  decide +revert

private theorem mul_insertion (a b : Fin 4) :
    mul a b = mul (mul (mul a a) a) b := by
  decide +revert

theorem basis_models :
    Models table.semigroup commutativeParitySupportBasis := by
  intro e he
  simp only [commutativeParitySupportBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl
  · intro valuation
    exact mul_power (valuation 0)
  · intro valuation
    exact mul_commutative (valuation 0) (valuation 1)
  · intro valuation
    exact mul_insertion (valuation 0) (valuation 1)

private def supportSeparator (z : Nat) : Nat → Fin 4 :=
  fun x => if x = z then 0 else 3

private def supportState (n : Nat) : Fin 4 :=
  if n = 0 then 3 else 0

private theorem supportMul_target (n : Nat) :
    mul (supportState n) 0 = supportState (n + 1) := by
  by_cases hn : n = 0
  · subst n
    rfl
  · simp [supportState, mul, hn]

private theorem supportMul_other (n : Nat) :
    mul (supportState n) 3 = supportState n := by
  by_cases hn : n = 0
  · subst n
    rfl
  · simp [supportState, mul, hn]

private theorem supportFold
    (z : Nat) (xs : List Nat) (acc : Nat) :
    xs.foldl
        (fun current x => mul current (supportSeparator z x))
        (supportState acc) =
      supportState (acc + xs.count z) := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      by_cases hx : x = z
      · subst x
        rw [List.count_cons_self]
        rw [show supportSeparator z z = (0 : Fin 4) by
          simp [supportSeparator]]
        rw [supportMul_target, ih]
        congr 1
        omega
      · rw [List.count_cons_of_ne hx]
        rw [show supportSeparator z x = (3 : Fin 4) by
          simp [supportSeparator, hx]]
        rw [supportMul_other, ih]

private theorem eval_supportSeparator
    (z : Nat) (w : Word Nat) :
    table.semigroup.eval (supportSeparator z) w =
      supportState (w.toList.count z) := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current x => mul current (supportSeparator z x))
            (supportSeparator z head) =
          supportState ((head :: tail).count z)
      by_cases hhead : head = z
      · subst head
        rw [List.count_cons_self]
        rw [show supportSeparator z z = supportState 1 by
          apply Fin.ext
          simp [supportSeparator, supportState]]
        rw [supportFold]
        congr 1
        omega
      · rw [List.count_cons_of_ne hhead]
        rw [show supportSeparator z head = supportState 0 by
          apply Fin.ext
          simp [supportSeparator, supportState, hhead]]
        rw [supportFold]
        congr 1
        omega

theorem valid_support
    (e : Identity Nat) (valid : e.SatisfiedBy table.semigroup) :
    ∀ z, z ∈ e.lhs.toList ↔ z ∈ e.rhs.toList := by
  intro z
  have evaluated := valid (supportSeparator z)
  rw [eval_supportSeparator, eval_supportSeparator] at evaluated
  constructor
  · intro hl
    apply Decidable.byContradiction
    intro hr
    have hlne : e.lhs.toList.count z ≠ 0 :=
      Nat.ne_of_gt (List.count_pos_iff.mpr hl)
    have hrzero : e.rhs.toList.count z = 0 :=
      List.count_eq_zero.mpr hr
    simp [supportState, hlne, hrzero] at evaluated
  · intro hr
    apply Decidable.byContradiction
    intro hl
    have hrne : e.rhs.toList.count z ≠ 0 :=
      Nat.ne_of_gt (List.count_pos_iff.mpr hr)
    have hlzero : e.lhs.toList.count z = 0 :=
      List.count_eq_zero.mpr hl
    simp [supportState, hlzero, hrne] at evaluated

private def paritySeparator (z : Nat) : Nat → Fin 4 :=
  fun x => if x = z then 1 else 0

private theorem parityMul_target (n : Nat) :
    mul (parityState n) 1 = parityState (n + 1) := by
  by_cases hp : n % 2 = 0
  · have hnext : (n + 1) % 2 = 1 := by omega
    simp [parityState, mul, hp, hnext]
  · have hmod : n % 2 = 1 := by omega
    have hnext : (n + 1) % 2 = 0 := by omega
    simp [parityState, mul, hmod, hnext]

private theorem parityMul_other (n : Nat) :
    mul (parityState n) 0 = parityState n := by
  by_cases hp : n % 2 = 0
  · simp [parityState, mul, hp]
  · have hmod : n % 2 = 1 := by omega
    simp [parityState, mul, hmod]

private theorem parityFold
    (z : Nat) (xs : List Nat) (acc : Nat) :
    xs.foldl
        (fun current x => mul current (paritySeparator z x))
        (parityState acc) =
      parityState (acc + xs.count z) := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      by_cases hx : x = z
      · subst x
        rw [List.count_cons_self]
        rw [show paritySeparator z z = (1 : Fin 4) by
          simp [paritySeparator]]
        rw [parityMul_target, ih]
        congr 1
        omega
      · rw [List.count_cons_of_ne hx]
        rw [show paritySeparator z x = (0 : Fin 4) by
          simp [paritySeparator, hx]]
        rw [parityMul_other, ih]

private theorem eval_paritySeparator
    (z : Nat) (w : Word Nat) :
    table.semigroup.eval (paritySeparator z) w =
      parityState (w.toList.count z) := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current x => mul current (paritySeparator z x))
            (paritySeparator z head) =
          parityState ((head :: tail).count z)
      by_cases hhead : head = z
      · subst head
        rw [List.count_cons_self]
        rw [show paritySeparator z z = parityState 1 by
          apply Fin.ext
          simp [paritySeparator, parityState]]
        rw [parityFold]
        congr 1
        omega
      · rw [List.count_cons_of_ne hhead]
        rw [show paritySeparator z head = parityState 0 by
          apply Fin.ext
          simp [paritySeparator, parityState, hhead]]
        rw [parityFold]
        congr 1
        omega

theorem valid_parity
    (e : Identity Nat) (valid : e.SatisfiedBy table.semigroup) :
    ∀ z, e.lhs.toList.count z % 2 =
      e.rhs.toList.count z % 2 := by
  intro z
  have evaluated := valid (paritySeparator z)
  rw [eval_paritySeparator, eval_paritySeparator] at evaluated
  have lhsBound : e.lhs.toList.count z % 2 < 2 :=
    Nat.mod_lt _ (by omega)
  have rhsBound : e.rhs.toList.count z % 2 < 2 :=
    Nat.mod_lt _ (by omega)
  have lhsCases :
      e.lhs.toList.count z % 2 = 0 ∨
        e.lhs.toList.count z % 2 = 1 := by
    omega
  have rhsCases :
      e.rhs.toList.count z % 2 = 0 ∨
        e.rhs.toList.count z % 2 = 1 := by
    omega
  rcases lhsCases with hl | hl <;>
    rcases rhsCases with hr | hr <;>
    simp [parityState, hl, hr] at evaluated ⊢

private def singletonSeparator : Nat → Fin 4 := fun _ => 2

private theorem singletonMul (n : Nat) (hpos : 0 < n) :
    mul (singletonState n) 2 = singletonState (n + 1) := by
  by_cases hn : n = 1
  · subst n
    rfl
  · by_cases hp : n % 2 = 0
    · have hn0 : n ≠ 0 := by omega
      have hn1 : n + 1 ≠ 1 := by omega
      have hnext : (n + 1) % 2 = 1 := by omega
      simp [singletonState, parityState, mul, hn, hn0, hn1, hp, hnext]
    · have hmod : n % 2 = 1 := by omega
      have hn0 : n ≠ 0 := by omega
      have hn1 : n + 1 ≠ 1 := by omega
      have hnext : (n + 1) % 2 = 0 := by omega
      simp [singletonState, parityState, mul, hn, hn0, hn1, hmod, hnext]

private theorem singletonFold
    (xs : List Nat) (acc : Nat) (hacc : 0 < acc) :
    xs.foldl
        (fun current _ => mul current 2)
        (singletonState acc) =
      singletonState (acc + xs.length) := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons, List.length_cons]
      rw [singletonMul acc hacc, ih (acc + 1) (by omega)]
      congr 1
      omega

private theorem eval_singletonSeparator (w : Word Nat) :
    table.semigroup.eval singletonSeparator w =
      singletonState w.toList.length := by
  cases w with
  | mk head tail =>
      change
        tail.foldl (fun current _ => mul current 2) 2 =
          singletonState (tail.length + 1)
      have folded := singletonFold tail 1 (by omega)
      simpa [singletonState, Nat.add_comm] using folded

theorem valid_singleton
    (e : Identity Nat) (valid : e.SatisfiedBy table.semigroup) :
    e.lhs.toList.length = 1 ↔ e.rhs.toList.length = 1 := by
  have evaluated := valid singletonSeparator
  rw [eval_singletonSeparator, eval_singletonSeparator] at evaluated
  constructor
  · intro hl
    apply Decidable.byContradiction
    intro hr
    have hnot :
        singletonState e.rhs.toList.length ≠ (2 : Fin 4) := by
      unfold singletonState
      rw [if_neg hr]
      unfold parityState
      split <;> decide
    apply hnot
    rw [← evaluated]
    simp [hl, singletonState]
  · intro hr
    apply Decidable.byContradiction
    intro hl
    have hnot :
        singletonState e.lhs.toList.length ≠ (2 : Fin 4) := by
      unfold singletonState
      rw [if_neg hl]
      unfold parityState
      split <;> decide
    apply hnot
    rw [evaluated]
    simp [hr, singletonState]

theorem representative_basis :
    BasisFor table.semigroup commutativeParitySupportBasis :=
  complete_of_paritySupport_invariants table basis_models
    valid_support valid_parity valid_singleton

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis commutativeParitySupportBasis) :=
  representative_basis.oppositeReversed

end S4_30

namespace S4_33

/-- Zero-based form of the stored `S4_33` table. -/
def mul (a b : Fin 4) : Fin 4 :=
  if a = 0 then
    if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 1 else 3
  else if a = 1 then
    if b = 0 then 1 else if b = 1 then 0 else if b = 2 then 0 else 3
  else if a = 2 then
    if b = 0 then 1 else if b = 1 then 0 else if b = 2 then 0 else 3
  else
    3

def table : FiniteTable where
  order := 4
  mul := mul
  assoc := by decide

theorem table_eq_canonical_catalogue :
    table = SemigroupBasis.Generated.Catalogue.S4_33.table := by
  unfold table SemigroupBasis.Generated.Catalogue.S4_33.table
  rw [FiniteTable.mk.injEq]
  refine ⟨rfl, heq_of_eq ?_⟩
  funext a b
  decide +revert

private theorem mul_commutative (a b : Fin 4) :
    mul a b = mul b a := by
  decide +revert

private theorem mul_power (a : Fin 4) :
    mul a a = mul (mul (mul a a) a) a := by
  decide +revert

private theorem mul_insertion (a b : Fin 4) :
    mul a b = mul (mul (mul a a) a) b := by
  decide +revert

theorem basis_models :
    Models table.semigroup commutativeParitySupportBasis := by
  intro e he
  simp only [commutativeParitySupportBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl
  · intro valuation
    exact mul_power (valuation 0)
  · intro valuation
    exact mul_commutative (valuation 0) (valuation 1)
  · intro valuation
    exact mul_insertion (valuation 0) (valuation 1)

private def supportSeparator (z : Nat) : Nat → Fin 4 :=
  fun x => if x = z then 3 else 0

private def supportState (n : Nat) : Fin 4 :=
  if n = 0 then 0 else 3

private theorem supportMul_target (n : Nat) :
    mul (supportState n) 3 = supportState (n + 1) := by
  by_cases hn : n = 0
  · subst n
    rfl
  · simp [supportState, mul, hn]

private theorem supportMul_other (n : Nat) :
    mul (supportState n) 0 = supportState n := by
  by_cases hn : n = 0
  · subst n
    rfl
  · simp [supportState, mul, hn]

private theorem supportFold
    (z : Nat) (xs : List Nat) (acc : Nat) :
    xs.foldl
        (fun current x => mul current (supportSeparator z x))
        (supportState acc) =
      supportState (acc + xs.count z) := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      by_cases hx : x = z
      · subst x
        rw [List.count_cons_self]
        rw [show supportSeparator z z = (3 : Fin 4) by
          simp [supportSeparator]]
        rw [supportMul_target, ih]
        congr 1
        omega
      · rw [List.count_cons_of_ne hx]
        rw [show supportSeparator z x = (0 : Fin 4) by
          simp [supportSeparator, hx]]
        rw [supportMul_other, ih]

private theorem eval_supportSeparator
    (z : Nat) (w : Word Nat) :
    table.semigroup.eval (supportSeparator z) w =
      supportState (w.toList.count z) := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current x => mul current (supportSeparator z x))
            (supportSeparator z head) =
          supportState ((head :: tail).count z)
      by_cases hhead : head = z
      · subst head
        rw [List.count_cons_self]
        rw [show supportSeparator z z = supportState 1 by
          apply Fin.ext
          simp [supportSeparator, supportState]]
        rw [supportFold]
        congr 1
        omega
      · rw [List.count_cons_of_ne hhead]
        rw [show supportSeparator z head = supportState 0 by
          apply Fin.ext
          simp [supportSeparator, supportState, hhead]]
        rw [supportFold]
        congr 1
        omega

theorem valid_support
    (e : Identity Nat) (valid : e.SatisfiedBy table.semigroup) :
    ∀ z, z ∈ e.lhs.toList ↔ z ∈ e.rhs.toList := by
  intro z
  have evaluated := valid (supportSeparator z)
  rw [eval_supportSeparator, eval_supportSeparator] at evaluated
  constructor
  · intro hl
    apply Decidable.byContradiction
    intro hr
    have hlne : e.lhs.toList.count z ≠ 0 :=
      Nat.ne_of_gt (List.count_pos_iff.mpr hl)
    have hrzero : e.rhs.toList.count z = 0 :=
      List.count_eq_zero.mpr hr
    simp [supportState, hlne, hrzero] at evaluated
  · intro hr
    apply Decidable.byContradiction
    intro hl
    have hrne : e.rhs.toList.count z ≠ 0 :=
      Nat.ne_of_gt (List.count_pos_iff.mpr hr)
    have hlzero : e.lhs.toList.count z = 0 :=
      List.count_eq_zero.mpr hl
    simp [supportState, hlzero, hrne] at evaluated

private def paritySeparator (z : Nat) : Nat → Fin 4 :=
  fun x => if x = z then 1 else 0

private theorem parityMul_target (n : Nat) :
    mul (parityState n) 1 = parityState (n + 1) := by
  by_cases hp : n % 2 = 0
  · have hnext : (n + 1) % 2 = 1 := by omega
    simp [parityState, mul, hp, hnext]
  · have hmod : n % 2 = 1 := by omega
    have hnext : (n + 1) % 2 = 0 := by omega
    simp [parityState, mul, hmod, hnext]

private theorem parityMul_other (n : Nat) :
    mul (parityState n) 0 = parityState n := by
  by_cases hp : n % 2 = 0
  · simp [parityState, mul, hp]
  · have hmod : n % 2 = 1 := by omega
    simp [parityState, mul, hmod]

private theorem parityFold
    (z : Nat) (xs : List Nat) (acc : Nat) :
    xs.foldl
        (fun current x => mul current (paritySeparator z x))
        (parityState acc) =
      parityState (acc + xs.count z) := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      by_cases hx : x = z
      · subst x
        rw [List.count_cons_self]
        rw [show paritySeparator z z = (1 : Fin 4) by
          simp [paritySeparator]]
        rw [parityMul_target, ih]
        congr 1
        omega
      · rw [List.count_cons_of_ne hx]
        rw [show paritySeparator z x = (0 : Fin 4) by
          simp [paritySeparator, hx]]
        rw [parityMul_other, ih]

private theorem eval_paritySeparator
    (z : Nat) (w : Word Nat) :
    table.semigroup.eval (paritySeparator z) w =
      parityState (w.toList.count z) := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current x => mul current (paritySeparator z x))
            (paritySeparator z head) =
          parityState ((head :: tail).count z)
      by_cases hhead : head = z
      · subst head
        rw [List.count_cons_self]
        rw [show paritySeparator z z = parityState 1 by
          apply Fin.ext
          simp [paritySeparator, parityState]]
        rw [parityFold]
        congr 1
        omega
      · rw [List.count_cons_of_ne hhead]
        rw [show paritySeparator z head = parityState 0 by
          apply Fin.ext
          simp [paritySeparator, parityState, hhead]]
        rw [parityFold]
        congr 1
        omega

theorem valid_parity
    (e : Identity Nat) (valid : e.SatisfiedBy table.semigroup) :
    ∀ z, e.lhs.toList.count z % 2 =
      e.rhs.toList.count z % 2 := by
  intro z
  have evaluated := valid (paritySeparator z)
  rw [eval_paritySeparator, eval_paritySeparator] at evaluated
  have lhsBound : e.lhs.toList.count z % 2 < 2 :=
    Nat.mod_lt _ (by omega)
  have rhsBound : e.rhs.toList.count z % 2 < 2 :=
    Nat.mod_lt _ (by omega)
  have lhsCases :
      e.lhs.toList.count z % 2 = 0 ∨
        e.lhs.toList.count z % 2 = 1 := by
    omega
  have rhsCases :
      e.rhs.toList.count z % 2 = 0 ∨
        e.rhs.toList.count z % 2 = 1 := by
    omega
  rcases lhsCases with hl | hl <;>
    rcases rhsCases with hr | hr <;>
    simp [parityState, hl, hr] at evaluated ⊢

private def singletonSeparator : Nat → Fin 4 := fun _ => 2

private theorem singletonMul (n : Nat) (hpos : 0 < n) :
    mul (singletonState n) 2 = singletonState (n + 1) := by
  by_cases hn : n = 1
  · subst n
    rfl
  · by_cases hp : n % 2 = 0
    · have hn0 : n ≠ 0 := by omega
      have hn1 : n + 1 ≠ 1 := by omega
      have hnext : (n + 1) % 2 = 1 := by omega
      simp [singletonState, parityState, mul, hn, hn0, hn1, hp, hnext]
    · have hmod : n % 2 = 1 := by omega
      have hn0 : n ≠ 0 := by omega
      have hn1 : n + 1 ≠ 1 := by omega
      have hnext : (n + 1) % 2 = 0 := by omega
      simp [singletonState, parityState, mul, hn, hn0, hn1, hmod, hnext]

private theorem singletonFold
    (xs : List Nat) (acc : Nat) (hacc : 0 < acc) :
    xs.foldl
        (fun current _ => mul current 2)
        (singletonState acc) =
      singletonState (acc + xs.length) := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons, List.length_cons]
      rw [singletonMul acc hacc, ih (acc + 1) (by omega)]
      congr 1
      omega

private theorem eval_singletonSeparator (w : Word Nat) :
    table.semigroup.eval singletonSeparator w =
      singletonState w.toList.length := by
  cases w with
  | mk head tail =>
      change
        tail.foldl (fun current _ => mul current 2) 2 =
          singletonState (tail.length + 1)
      have folded := singletonFold tail 1 (by omega)
      simpa [singletonState, Nat.add_comm] using folded

theorem valid_singleton
    (e : Identity Nat) (valid : e.SatisfiedBy table.semigroup) :
    e.lhs.toList.length = 1 ↔ e.rhs.toList.length = 1 := by
  have evaluated := valid singletonSeparator
  rw [eval_singletonSeparator, eval_singletonSeparator] at evaluated
  constructor
  · intro hl
    apply Decidable.byContradiction
    intro hr
    have hnot :
        singletonState e.rhs.toList.length ≠ (2 : Fin 4) := by
      unfold singletonState
      rw [if_neg hr]
      unfold parityState
      split <;> decide
    apply hnot
    rw [← evaluated]
    simp [hl, singletonState]
  · intro hr
    apply Decidable.byContradiction
    intro hl
    have hnot :
        singletonState e.lhs.toList.length ≠ (2 : Fin 4) := by
      unfold singletonState
      rw [if_neg hl]
      unfold parityState
      split <;> decide
    apply hnot
    rw [evaluated]
    simp [hr, singletonState]

theorem representative_basis :
    BasisFor table.semigroup commutativeParitySupportBasis :=
  complete_of_paritySupport_invariants table basis_models
    valid_support valid_parity valid_singleton

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis commutativeParitySupportBasis) :=
  representative_basis.oppositeReversed

end S4_33

end SemigroupBasis.Generated.S4_30FamilyProposal
