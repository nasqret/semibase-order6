import SemigroupBasis.Examples.HeadPositiveParitySuffix
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Generated.CatalogueOrder5Part05
import SemigroupBasis.Opposite

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.S5_624

open SemigroupBasis
open SemigroupBasis.Examples

/-- The exact `S5_624` basis
`xx = xxxx`, `xy = xyyy`, `xxy = xyx`, and `xyz = xzy`. -/
def basis : List (Identity Nat) :=
  headPositiveParitySuffixBasis

abbrev table : FiniteTable :=
  Generated.Catalogue.S5_624.table

def finiteHeadPowerLaw : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteContextPowerLaw : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 1, 1]⟩⟩

def finiteGatherLaw : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1, 0]⟩⟩

def finiteSuffixSwapLaw : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem finiteHeadPowerLaw_map :
    finiteHeadPowerLaw.map Fin.val =
      headPositiveParitySuffixHeadPowerLaw := rfl

theorem finiteContextPowerLaw_map :
    finiteContextPowerLaw.map Fin.val =
      headPositiveParitySuffixContextPowerLaw := rfl

theorem finiteGatherLaw_map :
    finiteGatherLaw.map Fin.val =
      headPositiveParitySuffixGatherLaw := rfl

theorem finiteSuffixSwapLaw_map :
    finiteSuffixSwapLaw.map Fin.val =
      headPositiveParitySuffixSwapLaw := rfl

/-- One-based table element `3`, a right identity. -/
def rightIdentity : Fin 5 := 2

/-- One-based table elements `1` and `5`, two distinct left-zero head
markers. -/
def headOrderFirst : Fin 5 := 0
def headOrderSecond : Fin 5 := 4

/-- One-based table element `5`, separating absence, head occurrence, and
suffix occurrence. -/
def supportWitness : Fin 5 := 4

/-- One-based table element `4`, separating odd and even total parity. -/
def parityWitness : Fin 5 := 3

/-- One-based table elements `2` and `4`, whose paired power profiles
separate absence, one occurrence, positive even multiplicity, and odd
multiplicity at least three. -/
def headPowerWitness (index : Fin 2) : Fin 5 :=
  if index = 0 then 1 else 3

theorem rightIdentity_certificate (a : Fin 5) :
    Generated.Catalogue.S5_624.mul a rightIdentity = a := by
  decide +revert

def headOrderWitnessesOneBased : List Nat :=
  [headOrderFirst.val + 1, headOrderSecond.val + 1]

theorem headOrderWitnessesOneBased_certificate :
    headOrderWitnessesOneBased = [1, 5] := by
  decide

theorem headOrder_certificate (a : Fin 5) :
    Generated.Catalogue.S5_624.mul headOrderFirst a =
        headOrderFirst ∧
      Generated.Catalogue.S5_624.mul headOrderSecond a =
        headOrderSecond := by
  decide +revert

def supportProfileOneBased : List Nat :=
  [rightIdentity.val + 1, supportWitness.val + 1,
    (Generated.Catalogue.S5_624.mul
      rightIdentity supportWitness).val + 1]

theorem supportProfileOneBased_certificate :
    supportProfileOneBased = [3, 5, 1] := by
  decide

def parityProfileOneBased : List Nat :=
  [rightIdentity.val + 1, parityWitness.val + 1]

theorem parityProfileOneBased_certificate :
    parityProfileOneBased = [3, 4] := by
  decide

def headPowerWitnessesOneBased : List Nat :=
  [(headPowerWitness 0).val + 1,
    (headPowerWitness 1).val + 1]

theorem headPowerWitnessesOneBased_certificate :
    headPowerWitnessesOneBased = [2, 4] := by
  decide

private theorem headExponent_le_three (n : Nat) :
    periodTwoFromTwoExponent n ≤ 3 := by
  unfold periodTwoFromTwoExponent
  split <;> omega

private theorem headExponent_lt_four (n : Nat) :
    periodTwoFromTwoExponent n < 4 := by
  have bound := headExponent_le_three n
  omega

private def headExponentState (n : Nat) : Fin 4 :=
  ⟨periodTwoFromTwoExponent n, headExponent_lt_four n⟩

private def headExponentNext (state : Fin 4) : Fin 4 :=
  if h : state.val < 3 then
    ⟨state.val + 1, by omega⟩
  else
    ⟨state.val - 1, by omega⟩

private theorem headExponentState_succ (n : Nat) :
    headExponentState (n + 1) =
      headExponentNext (headExponentState n) := by
  apply Fin.ext
  by_cases h : periodTwoFromTwoExponent n < 3
  · simp [headExponentState, headExponentNext, h,
      periodTwoFromTwoExponent_succ]
  · simp [headExponentState, headExponentNext, h,
      periodTwoFromTwoExponent_succ]

def headPowerCode (state : Fin 4) : Fin 5 × Fin 5 :=
  if state = 0 then
    (rightIdentity, rightIdentity)
  else if state = 1 then
    (1, 3)
  else if state = 2 then
    (0, rightIdentity)
  else
    (0, 3)

def headPowerProfilesOneBased : List (List Nat) :=
  [[(headPowerCode 1).1.val + 1,
      (headPowerCode 1).2.val + 1],
    [(headPowerCode 2).1.val + 1,
      (headPowerCode 2).2.val + 1],
    [(headPowerCode 3).1.val + 1,
      (headPowerCode 3).2.val + 1]]

theorem headPowerProfilesOneBased_certificate :
    headPowerProfilesOneBased =
      [[2, 4], [1, 3], [1, 4]] := by
  decide

theorem headPowerCode_injective :
    Function.Injective headPowerCode := by
  intro a b
  revert a b
  decide

private def headPowerCoordinate
    (profile : Fin 5 × Fin 5) (index : Fin 2) : Fin 5 :=
  if index = 0 then profile.1 else profile.2

private theorem headPowerCode_step
    (state : Fin 4) (index : Fin 2)
    (positive : 0 < state.val) :
    Generated.Catalogue.S5_624.mul
        (headPowerCoordinate (headPowerCode state) index)
        (headPowerWitness index) =
      headPowerCoordinate
        (headPowerCode (headExponentNext state)) index := by
  revert state index
  decide

private def headPowerState (index : Fin 2) (n : Nat) : Fin 5 :=
  headPowerCoordinate
    (headPowerCode (headExponentState n)) index

private theorem headPowerState_step
    (index : Fin 2) (n : Nat) (positive : 0 < n) :
    Generated.Catalogue.S5_624.mul
        (headPowerState index n) (headPowerWitness index) =
      headPowerState index (n + 1) := by
  have statePositive : 0 < (headExponentState n).val :=
    periodTwoFromTwoExponent_pos positive
  calc
    Generated.Catalogue.S5_624.mul
        (headPowerState index n) (headPowerWitness index) =
        headPowerCoordinate
          (headPowerCode
            (headExponentNext (headExponentState n))) index := by
      simpa [headPowerState] using
        headPowerCode_step (headExponentState n) index statePositive
    _ = headPowerState index (n + 1) := by
      rw [headPowerState, headExponentState_succ]

private theorem headPowerState_other
    (index : Fin 2) (n : Nat) :
    Generated.Catalogue.S5_624.mul
        (headPowerState index n) rightIdentity =
      headPowerState index n :=
  rightIdentity_certificate _

def headPowerValuation
    (index : Fin 2) (z : Nat) : Nat → Fin 5 :=
  fun x => if x = z then headPowerWitness index else rightIdentity

private theorem headPowerValuation_self
    (index : Fin 2) (z : Nat) :
    headPowerValuation index z z = headPowerState index 1 := by
  by_cases hi : index = 0
  · subst index
    simp [headPowerValuation, headPowerState, headPowerCoordinate,
      headPowerCode, headExponentState, periodTwoFromTwoExponent,
      headPowerWitness, rightIdentity]
  · simp [headPowerValuation, headPowerState, headPowerCoordinate,
      headPowerCode, headExponentState, periodTwoFromTwoExponent,
      headPowerWitness, rightIdentity, hi]

private theorem headPowerValuation_other
    (index : Fin 2) {z x : Nat} (different : x ≠ z) :
    headPowerValuation index z x = headPowerState index 0 := by
  by_cases hi : index = 0
  · subst index
    simp [headPowerValuation, different, headPowerState,
      headPowerCoordinate, headPowerCode, headExponentState,
      periodTwoFromTwoExponent, rightIdentity]
  · simp [headPowerValuation, different, headPowerState,
      headPowerCoordinate, headPowerCode, headExponentState,
      periodTwoFromTwoExponent, rightIdentity, hi]

private theorem headPowerFold (index : Fin 2) (z : Nat) :
    ∀ (xs : List Nat) (n : Nat), 0 < n →
      xs.foldl
          (fun current x =>
            Generated.Catalogue.S5_624.mul current
              (headPowerValuation index z x))
          (headPowerState index n) =
        headPowerState index (n + xs.count z)
  | [], _, _ => by
      simp
  | x :: xs, n, positive => by
      simp only [List.foldl_cons]
      by_cases hx : x = z
      · subst x
        rw [show
          headPowerValuation index z z =
              headPowerWitness index by
            simp [headPowerValuation]]
        rw [headPowerState_step index n positive,
          headPowerFold index z xs (n + 1) (by omega)]
        rw [List.count_cons_self]
        congr 1
        omega
      · rw [show
          headPowerValuation index z x = rightIdentity by
            simp [headPowerValuation, hx]]
        rw [headPowerState_other,
          headPowerFold index z xs n positive,
          List.count_cons_of_ne hx]

theorem eval_headPower
    (index : Fin 2) (z : Nat) (w : Word Nat)
    (headEq : w.head = z) :
    table.semigroup.eval (headPowerValuation index z) w =
      headPowerState index (w.toList.count z) := by
  cases w with
  | mk head tail =>
      simp only at headEq
      subst head
      change
        tail.foldl
            (fun current x =>
              Generated.Catalogue.S5_624.mul current
                (headPowerValuation index z x))
            (headPowerValuation index z z) =
          headPowerState index ((z :: tail).count z)
      rw [headPowerValuation_self,
        headPowerFold index z tail 1 (by omega),
        List.count_cons_self]
      congr 1
      omega

def headValuation (z : Nat) : Nat → Fin 5 :=
  fun x => if x = z then headOrderFirst else headOrderSecond

private theorem headFold_first (z : Nat) :
    ∀ xs : List Nat,
      xs.foldl
          (fun current x =>
            Generated.Catalogue.S5_624.mul current
              (headValuation z x))
          headOrderFirst =
        headOrderFirst
  | [] => rfl
  | x :: xs => by
      simp only [List.foldl_cons]
      rw [(headOrder_certificate (headValuation z x)).1]
      exact headFold_first z xs

private theorem headFold_second (z : Nat) :
    ∀ xs : List Nat,
      xs.foldl
          (fun current x =>
            Generated.Catalogue.S5_624.mul current
              (headValuation z x))
          headOrderSecond =
        headOrderSecond
  | [] => rfl
  | x :: xs => by
      simp only [List.foldl_cons]
      rw [(headOrder_certificate (headValuation z x)).2]
      exact headFold_second z xs

theorem eval_head (z : Nat) (w : Word Nat) :
    table.semigroup.eval (headValuation z) w =
      if w.head = z then headOrderFirst else headOrderSecond := by
  cases w with
  | mk head tail =>
      by_cases hhead : head = z
      · subst head
        simp only [if_pos]
        change
          tail.foldl
              (fun current x =>
                Generated.Catalogue.S5_624.mul current
                  (headValuation z x))
              (headValuation z z) =
            headOrderFirst
        rw [show headValuation z z = headOrderFirst by
          simp [headValuation]]
        exact headFold_first z tail
      · simp only [if_neg hhead]
        change
          tail.foldl
              (fun current x =>
                Generated.Catalogue.S5_624.mul current
                  (headValuation z x))
              (headValuation z head) =
            headOrderSecond
        rw [show headValuation z head = headOrderSecond by
          simp [headValuation, hhead]]
        exact headFold_second z tail

inductive HeadSupportState where
  | absent
  | head
  | suffix
deriving DecidableEq, Repr

def headSupportState (w : Word Nat) (z : Nat) : HeadSupportState :=
  if w.toList.count z = 0 then .absent
  else if w.head = z then .head
  else .suffix

def HeadSupportState.value : HeadSupportState → Fin 5
  | .absent => rightIdentity
  | .head => supportWitness
  | .suffix => 0

private theorem HeadSupportState.value_injective :
    Function.Injective HeadSupportState.value := by
  intro left right
  cases left <;> cases right <;>
    simp_all [HeadSupportState.value, rightIdentity, supportWitness]

def supportValuation (z : Nat) : Nat → Fin 5 :=
  fun x => if x = z then supportWitness else rightIdentity

private theorem supportWitness_leftZero (a : Fin 5) :
    Generated.Catalogue.S5_624.mul supportWitness a =
      supportWitness := by
  decide +revert

private theorem supportHeadFold (z : Nat) :
    ∀ xs : List Nat,
      xs.foldl
          (fun current x =>
            Generated.Catalogue.S5_624.mul current
              (supportValuation z x))
          supportWitness =
        supportWitness
  | [] => rfl
  | x :: xs => by
      simp only [List.foldl_cons]
      rw [supportWitness_leftZero]
      exact supportHeadFold z xs

private def supportSuffixState (n : Nat) : Fin 5 :=
  if n = 0 then rightIdentity else 0

private theorem supportSuffixState_target (n : Nat) :
    Generated.Catalogue.S5_624.mul
        (supportSuffixState n) supportWitness =
      supportSuffixState (n + 1) := by
  by_cases hn : n = 0
  · subst n
    rfl
  · simp [supportSuffixState, hn,
      Generated.Catalogue.S5_624.mul]

private theorem supportSuffixState_other (n : Nat) :
    Generated.Catalogue.S5_624.mul
        (supportSuffixState n) rightIdentity =
      supportSuffixState n :=
  rightIdentity_certificate _

private theorem supportSuffixFold (z : Nat) :
    ∀ (xs : List Nat) (n : Nat),
      xs.foldl
          (fun current x =>
            Generated.Catalogue.S5_624.mul current
              (supportValuation z x))
          (supportSuffixState n) =
        supportSuffixState (n + xs.count z)
  | [], _ => by
      simp
  | x :: xs, n => by
      simp only [List.foldl_cons]
      by_cases hx : x = z
      · subst x
        rw [show supportValuation z z = supportWitness by
          simp [supportValuation]]
        rw [supportSuffixState_target, supportSuffixFold]
        rw [List.count_cons_self]
        congr 1
        omega
      · rw [show supportValuation z x = rightIdentity by
          simp [supportValuation, hx]]
        rw [supportSuffixState_other, supportSuffixFold,
          List.count_cons_of_ne hx]

theorem eval_support (z : Nat) (w : Word Nat) :
    table.semigroup.eval (supportValuation z) w =
      (headSupportState w z).value := by
  cases w with
  | mk head tail =>
      by_cases hhead : head = z
      · subst head
        change
          tail.foldl
              (fun current x =>
                Generated.Catalogue.S5_624.mul current
                  (supportValuation z x))
              (supportValuation z z) =
            (headSupportState ⟨z, tail⟩ z).value
        rw [show supportValuation z z = supportWitness by
          simp [supportValuation]]
        rw [supportHeadFold]
        simp [headSupportState, HeadSupportState.value, Word.toList]
      · change
          tail.foldl
              (fun current x =>
                Generated.Catalogue.S5_624.mul current
                  (supportValuation z x))
              (supportValuation z head) =
            (headSupportState ⟨head, tail⟩ z).value
        rw [show supportValuation z head = supportSuffixState 0 by
          simp [supportValuation, supportSuffixState, hhead]]
        rw [supportSuffixFold]
        by_cases hzero : tail.count z = 0
        · simp [headSupportState, HeadSupportState.value,
            supportSuffixState, Word.toList, hhead, hzero]
        · simp [headSupportState, HeadSupportState.value,
            supportSuffixState, Word.toList, hhead, hzero]

theorem valid_supportState_eq
    (e : Identity Nat)
    (valid : e.SatisfiedBy table.semigroup)
    (z : Nat) :
    headSupportState e.lhs z =
      headSupportState e.rhs z := by
  apply HeadSupportState.value_injective
  have evaluated := valid (supportValuation z)
  simpa [eval_support] using evaluated

private theorem headSupportState_eq_absent_iff
    (w : Word Nat) (z : Nat) :
    headSupportState w z = .absent ↔ z ∉ w.toList := by
  by_cases hzero : w.toList.count z = 0
  · have hnot : z ∉ w.toList :=
      List.count_eq_zero.mp hzero
    simp [headSupportState, hzero, hnot]
  · have hmem : z ∈ w.toList :=
      List.count_pos_iff.mp (by omega)
    by_cases hhead : w.head = z
    · simp [headSupportState, hzero, hhead, hmem]
    · simp [headSupportState, hzero, hhead, hmem]

theorem valid_support
    (e : Identity Nat)
    (valid : e.SatisfiedBy table.semigroup) :
    ∀ z, z ∈ e.lhs.toList ↔ z ∈ e.rhs.toList := by
  intro z
  have states := valid_supportState_eq e valid z
  constructor
  · intro leftMem
    by_cases rightMem : z ∈ e.rhs.toList
    · exact rightMem
    have rightAbsent :
        headSupportState e.rhs z = .absent :=
      (headSupportState_eq_absent_iff e.rhs z).2 rightMem
    have leftAbsent :
        headSupportState e.lhs z = .absent :=
      states.trans rightAbsent
    exact False.elim <|
      (headSupportState_eq_absent_iff e.lhs z).1 leftAbsent
        leftMem
  · intro rightMem
    by_cases leftMem : z ∈ e.lhs.toList
    · exact leftMem
    have leftAbsent :
        headSupportState e.lhs z = .absent :=
      (headSupportState_eq_absent_iff e.lhs z).2 leftMem
    have rightAbsent :
        headSupportState e.rhs z = .absent :=
      states.symm.trans leftAbsent
    exact False.elim <|
      (headSupportState_eq_absent_iff e.rhs z).1 rightAbsent
        rightMem

private def parityResidue (n : Nat) : Fin 2 :=
  ⟨n % 2, Nat.mod_lt n (by decide)⟩

private def parityCode (state : Fin 2) : Fin 5 :=
  if state = 0 then rightIdentity else parityWitness

private theorem parityCode_injective :
    Function.Injective parityCode := by
  intro a b
  revert a b
  decide

private def parityState (n : Nat) : Fin 5 :=
  parityCode (parityResidue n)

private theorem parityState_step (n : Nat) :
    Generated.Catalogue.S5_624.mul
        (parityState n) parityWitness =
      parityState (n + 1) := by
  by_cases hp : n % 2 = 0
  · have hnext : (n + 1) % 2 = 1 := by
      omega
    simp [parityState, parityCode, parityResidue, hp, hnext,
      rightIdentity, parityWitness,
      Generated.Catalogue.S5_624.mul]
  · have hmod : n % 2 = 1 := by
      omega
    have hnext : (n + 1) % 2 = 0 := by
      omega
    simp [parityState, parityCode, parityResidue, hmod, hnext,
      rightIdentity, parityWitness,
      Generated.Catalogue.S5_624.mul]

private theorem parityState_other (n : Nat) :
    Generated.Catalogue.S5_624.mul
        (parityState n) rightIdentity =
      parityState n :=
  rightIdentity_certificate _

def parityValuation (z : Nat) : Nat → Fin 5 :=
  fun x => if x = z then parityWitness else rightIdentity

private theorem parityFold (z : Nat) :
    ∀ (xs : List Nat) (n : Nat),
      xs.foldl
          (fun current x =>
            Generated.Catalogue.S5_624.mul current
              (parityValuation z x))
          (parityState n) =
        parityState (n + xs.count z)
  | [], _ => by
      simp
  | x :: xs, n => by
      simp only [List.foldl_cons]
      by_cases hx : x = z
      · subst x
        rw [show parityValuation z z = parityWitness by
          simp [parityValuation]]
        rw [parityState_step, parityFold,
          List.count_cons_self]
        congr 1
        omega
      · rw [show parityValuation z x = rightIdentity by
          simp [parityValuation, hx]]
        rw [parityState_other, parityFold,
          List.count_cons_of_ne hx]

theorem eval_parity (z : Nat) (w : Word Nat) :
    table.semigroup.eval (parityValuation z) w =
      parityState (w.toList.count z) := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current x =>
              Generated.Catalogue.S5_624.mul current
                (parityValuation z x))
            (parityValuation z head) =
          parityState ((head :: tail).count z)
      by_cases hhead : head = z
      · subst head
        rw [show parityValuation z z = parityState 1 by
          simp [parityValuation, parityState, parityCode,
            parityResidue, parityWitness]]
        rw [parityFold, List.count_cons_self]
        congr 1
        omega
      · rw [show parityValuation z head = parityState 0 by
          simp [parityValuation, hhead, parityState, parityCode,
            parityResidue, rightIdentity]]
        rw [parityFold, List.count_cons_of_ne hhead]
        congr 1
        omega

theorem valid_head
    (e : Identity Nat)
    (valid : e.SatisfiedBy table.semigroup) :
    e.lhs.head = e.rhs.head := by
  apply Decidable.byContradiction
  intro headsNe
  have evaluated := valid (headValuation e.lhs.head)
  rw [eval_head, eval_head] at evaluated
  simp [Ne.symm headsNe] at evaluated
  exact (by decide : headOrderFirst ≠ headOrderSecond) evaluated

theorem valid_parity
    (e : Identity Nat)
    (valid : e.SatisfiedBy table.semigroup) :
    ∀ z,
      e.lhs.toList.count z % 2 =
        e.rhs.toList.count z % 2 := by
  intro z
  have evaluated := valid (parityValuation z)
  rw [eval_parity, eval_parity] at evaluated
  have states :
      parityResidue (e.lhs.toList.count z) =
        parityResidue (e.rhs.toList.count z) := by
    apply parityCode_injective
    simpa [parityState] using evaluated
  exact congrArg Fin.val states

theorem valid_headExponent
    (e : Identity Nat)
    (valid : e.SatisfiedBy table.semigroup) :
    periodTwoFromTwoExponent
        (e.lhs.toList.count e.lhs.head) =
      periodTwoFromTwoExponent
        (e.rhs.toList.count e.rhs.head) := by
  have heads := valid_head e valid
  have first := valid (headPowerValuation 0 e.lhs.head)
  have second := valid (headPowerValuation 1 e.lhs.head)
  rw [eval_headPower 0 e.lhs.head e.lhs rfl,
    eval_headPower 0 e.lhs.head e.rhs heads.symm] at first
  rw [eval_headPower 1 e.lhs.head e.lhs rfl,
    eval_headPower 1 e.lhs.head e.rhs heads.symm] at second
  have profiles :
      headPowerCode
          (headExponentState
            (e.lhs.toList.count e.lhs.head)) =
        headPowerCode
          (headExponentState
            (e.rhs.toList.count e.lhs.head)) := by
    apply Prod.ext
    · simpa [headPowerState, headPowerCoordinate] using first
    · simpa [headPowerState, headPowerCoordinate] using second
  have states := headPowerCode_injective profiles
  have values := congrArg Fin.val states
  simpa [heads] using values

theorem models :
    Models table.semigroup basis := by
  intro identity member
  simp only [basis, headPositiveParitySuffixBasis,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · rw [← finiteHeadPowerLaw_map]
    exact table.checkIdentityNat_sound finiteHeadPowerLaw (by decide)
  · rw [← finiteContextPowerLaw_map]
    exact table.checkIdentityNat_sound finiteContextPowerLaw (by decide)
  · rw [← finiteGatherLaw_map]
    exact table.checkIdentityNat_sound finiteGatherLaw (by decide)
  · rw [← finiteSuffixSwapLaw_map]
    exact table.checkIdentityNat_sound finiteSuffixSwapLaw (by decide)

theorem representative_basis :
    BasisFor table.semigroup basis := by
  simpa only [basis] using
    headPositiveParitySuffixBasis_complete_of_separates
      table models valid_head valid_support valid_parity
      valid_headExponent

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

/-- Lifecycle-compatible alias for the representative completeness theorem. -/
theorem basis_complete :
    BasisFor table.semigroup basis :=
  representative_basis

/-- Lifecycle-compatible alias for the opposite completeness theorem. -/
theorem opposite_basis_complete :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  opposite_basis

end SemigroupBasis.CoRoots.S5_624
