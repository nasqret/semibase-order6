import SemigroupBasis.Examples.HeadSortedCappedThree
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Generated.CatalogueOrder5Part05
import SemigroupBasis.Opposite

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.S5_529

open SemigroupBasis
open SemigroupBasis.Examples

/-- The exact `S5_529` basis
`xxx = xxxx`, `xxy = xyx`, and `xyz = xzy`. -/
def basis : List (Identity Nat) :=
  headSortedCappedThreeBasis

abbrev table : FiniteTable :=
  Generated.Catalogue.S5_529.table

def finitePowerLaw : Identity (Fin 1) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteGatherLaw : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1, 0]⟩⟩

def finiteSuffixSwapLaw : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem finitePowerLaw_map :
    finitePowerLaw.map Fin.val =
      headSortedCappedThreePowerLaw := rfl

theorem finiteGatherLaw_map :
    finiteGatherLaw.map Fin.val =
      headSortedCappedThreeGatherLaw := rfl

theorem finiteSuffixSwapLaw_map :
    finiteSuffixSwapLaw.map Fin.val =
      headSortedCappedThreeSuffixSwapLaw := rfl

/-- One-based table element `5`, recorded as the neutral suffix value. -/
def rightIdentity : Fin 5 := 4

/-- One-based table element `3`, whose powers are `3,2,1` for capped
multiplicities `1,2,3+`. -/
def powerWitness : Fin 5 := 2

/-- One-based table element `4`, used against the neutral value `5` to
separate absent, head, and suffix occurrences. -/
def supportWitness : Fin 5 := 3

theorem rightIdentity_certificate (a : Fin 5) :
    Generated.Catalogue.S5_529.mul a rightIdentity = a := by
  decide +revert

def powerProfileOneBased : List Nat :=
  [powerWitness.val + 1,
    (Generated.Catalogue.S5_529.mul
      powerWitness powerWitness).val + 1,
    (Generated.Catalogue.S5_529.mul
      (Generated.Catalogue.S5_529.mul
        powerWitness powerWitness)
      powerWitness).val + 1]

theorem powerProfileOneBased_certificate :
    powerProfileOneBased = [3, 2, 1] := by
  decide

def headOrderWitnessesOneBased : List Nat :=
  [supportWitness.val + 1, rightIdentity.val + 1]

theorem headOrderWitnessesOneBased_certificate :
    headOrderWitnessesOneBased = [4, 5] := by
  decide

theorem headOrder_certificate :
    Generated.Catalogue.S5_529.mul supportWitness rightIdentity =
        supportWitness ∧
      Generated.Catalogue.S5_529.mul rightIdentity supportWitness =
        (0 : Fin 5) := by
  decide

theorem models :
    Models table.semigroup basis := by
  intro identity member
  simp only [basis, headSortedCappedThreeBasis, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · rw [← finitePowerLaw_map]
    exact table.checkIdentityNat_sound finitePowerLaw (by decide)
  · rw [← finiteGatherLaw_map]
    exact table.checkIdentityNat_sound finiteGatherLaw (by decide)
  · rw [← finiteSuffixSwapLaw_map]
    exact table.checkIdentityNat_sound finiteSuffixSwapLaw (by decide)

def powerValuation (z : Nat) : Nat → Fin 5 :=
  fun x => if x = z then powerWitness else rightIdentity

private def cappedState (n : Nat) : Fin 4 :=
  ⟨headSortedCappedThreeExponent n, by
    have bound := headSortedCappedThreeExponent_le_three n
    omega⟩

def powerCode (state : Fin 4) : Fin 5 :=
  if state.val = 0 then 4
  else if state.val = 1 then 2
  else if state.val = 2 then 1
  else 0

def powerState (n : Nat) : Fin 5 :=
  powerCode (cappedState n)

theorem powerCode_injective :
    Function.Injective powerCode := by
  intro a b
  revert a b
  decide

private theorem powerCode_three :
    powerCode (⟨3, by decide⟩ : Fin 4) = (0 : Fin 5) := by
  decide

theorem powerState_step (n : Nat) :
    Generated.Catalogue.S5_529.mul
        (powerState n) powerWitness =
      powerState (n + 1) := by
  by_cases hn0 : n = 0
  · subst n
    rfl
  · by_cases hn1 : n = 1
    · subst n
      rfl
    · by_cases hn2 : n = 2
      · subst n
        rfl
      · have hn3 : ¬n < 3 := by omega
        have hnext3 : ¬(n + 1 < 3) := by omega
        have hstate :
            cappedState n = (⟨3, by decide⟩ : Fin 4) := by
          apply Fin.ext
          change headSortedCappedThreeExponent n = 3
          simp [cappedState, headSortedCappedThreeExponent, hn3]
        have hnextState :
            cappedState (n + 1) = (⟨3, by decide⟩ : Fin 4) := by
          apply Fin.ext
          change headSortedCappedThreeExponent (n + 1) = 3
          simp [cappedState, headSortedCappedThreeExponent, hnext3]
        have hleft : powerState n = (0 : Fin 5) := by
          calc
            powerState n =
                powerCode (⟨3, by decide⟩ : Fin 4) := by
              simp [powerState, hstate]
            _ = (0 : Fin 5) := powerCode_three
        have hright : powerState (n + 1) = (0 : Fin 5) := by
          calc
            powerState (n + 1) =
                powerCode (⟨3, by decide⟩ : Fin 4) := by
              simp [powerState, hnextState]
            _ = (0 : Fin 5) := powerCode_three
        rw [hleft, hright]
        decide

private theorem powerState_other (n : Nat) :
    Generated.Catalogue.S5_529.mul
        (powerState n) rightIdentity =
      powerState n :=
  rightIdentity_certificate _

private theorem powerFold (z : Nat) :
    ∀ (xs : List Nat) (n : Nat),
      xs.foldl
          (fun current x =>
            Generated.Catalogue.S5_529.mul current
              (powerValuation z x))
          (powerState n) =
        powerState (n + xs.count z)
  | [], _ => by simp
  | x :: xs, n => by
      simp only [List.foldl_cons]
      by_cases hx : x = z
      · subst x
        rw [show powerValuation z z = powerWitness by
          simp [powerValuation]]
        rw [powerState_step, powerFold]
        rw [List.count_cons_self]
        congr 1
        omega
      · rw [show powerValuation z x = rightIdentity by
          simp [powerValuation, hx]]
        rw [powerState_other, powerFold,
          List.count_cons_of_ne hx]

theorem eval_power (z : Nat) (w : Word Nat) :
    table.semigroup.eval (powerValuation z) w =
      powerState (w.toList.count z) := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current x =>
              Generated.Catalogue.S5_529.mul current
                (powerValuation z x))
            (powerValuation z head) =
          powerState ((head :: tail).count z)
      by_cases hhead : head = z
      · subst head
        rw [show powerValuation z z = powerState 1 by
          simp [powerValuation, powerState, powerCode, cappedState,
            headSortedCappedThreeExponent, powerWitness]]
        rw [powerFold, List.count_cons_self]
        congr 1
        omega
      · rw [show powerValuation z head = powerState 0 by
          simp [powerValuation, hhead, powerState, powerCode,
            cappedState, headSortedCappedThreeExponent,
            rightIdentity]]
        rw [powerFold, List.count_cons_of_ne hhead]
        congr 1
        omega

inductive HeadSupportState where
  | absent
  | head
  | suffix
deriving DecidableEq, Repr

def headSupportState
    (w : Word Nat) (z : Nat) : HeadSupportState :=
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
    Generated.Catalogue.S5_529.mul supportWitness a =
      supportWitness := by
  decide +revert

private theorem supportHeadFold (z : Nat) :
    ∀ xs : List Nat,
      xs.foldl
          (fun current x =>
            Generated.Catalogue.S5_529.mul current
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
    Generated.Catalogue.S5_529.mul
        (supportSuffixState n) supportWitness =
      supportSuffixState (n + 1) := by
  by_cases hn : n = 0
  · subst n
    rfl
  · simp [supportSuffixState, hn,
      Generated.Catalogue.S5_529.mul]

private theorem supportSuffixState_other (n : Nat) :
    Generated.Catalogue.S5_529.mul
        (supportSuffixState n) rightIdentity =
      supportSuffixState n :=
  rightIdentity_certificate _

private theorem supportSuffixFold (z : Nat) :
    ∀ (xs : List Nat) (n : Nat),
      xs.foldl
          (fun current x =>
            Generated.Catalogue.S5_529.mul current
              (supportValuation z x))
          (supportSuffixState n) =
        supportSuffixState (n + xs.count z)
  | [], _ => by simp
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
                Generated.Catalogue.S5_529.mul current
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
                Generated.Catalogue.S5_529.mul current
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

private theorem headSupportState_eq_head_iff
    (w : Word Nat) (z : Nat) :
    headSupportState w z = .head ↔ w.head = z := by
  by_cases hzero : w.toList.count z = 0
  · have hnot : z ∉ w.toList :=
      List.count_eq_zero.mp hzero
    have hhead : w.head ≠ z := by
      intro hz
      apply hnot
      rw [← hz]
      simp [Word.toList]
    simp [headSupportState, hzero, hhead]
  · by_cases hhead : w.head = z
    · simp [headSupportState, hzero, hhead]
    · simp [headSupportState, hzero, hhead]

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

theorem valid_head
    (e : Identity Nat)
    (valid : e.SatisfiedBy table.semigroup) :
    e.lhs.head = e.rhs.head := by
  have states :=
    valid_supportState_eq e valid e.lhs.head
  have leftHead :
      headSupportState e.lhs e.lhs.head = .head :=
    (headSupportState_eq_head_iff e.lhs e.lhs.head).2 rfl
  have rightHead :
      headSupportState e.rhs e.lhs.head = .head :=
    states.symm.trans leftHead
  exact
    ((headSupportState_eq_head_iff e.rhs e.lhs.head).1
      rightHead).symm

theorem valid_exponent
    (e : Identity Nat)
    (valid : e.SatisfiedBy table.semigroup) :
    ∀ z,
      headSortedCappedThreeExponent (e.lhs.toList.count z) =
        headSortedCappedThreeExponent (e.rhs.toList.count z) := by
  intro z
  have evaluated := valid (powerValuation z)
  rw [eval_power, eval_power] at evaluated
  have states :
      cappedState (e.lhs.toList.count z) =
        cappedState (e.rhs.toList.count z) := by
    apply powerCode_injective
    simpa [powerState] using evaluated
  exact congrArg Fin.val states

theorem representative_basis :
    BasisFor table.semigroup basis := by
  simpa only [basis] using
    headSortedCappedThreeBasis_complete_of_separates
      table models valid_head valid_exponent

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis basis) :=
  representative_basis.oppositeReversed

theorem basis_complete :
    BasisFor table.semigroup basis :=
  representative_basis

theorem opposite_basis_complete :
    BasisFor table.semigroup.opposite
      (reversedBasis basis) :=
  opposite_basis

end SemigroupBasis.CoRoots.S5_529
