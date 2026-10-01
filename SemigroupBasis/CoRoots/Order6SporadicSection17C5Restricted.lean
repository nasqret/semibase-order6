import SemigroupBasis.CoRoots.Order6SporadicSection17C5Evaluation

/-! Unrestricted proof of the restricted-square detector in Lemma17.2(iv).
The five-state recognizer is proved equivalent to one adjacent square with
no other occurrence. Its finite probe is checked in BOTH literal tables.
The C6 single-letter-gap collision is discharged using the count invariant. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6
open SemigroupBasis

def Restricted (x : Nat) (letters : List Nat) : Prop :=
  ∃ before after, letters = before ++ x :: x :: after ∧ x ∉ before ∧ x ∉ after

theorem restricted_nil (x : Nat) : ¬ Restricted x [] := by
  rintro ⟨before,after,shape,_,_⟩
  have length := congrArg List.length shape
  simp at length
  omega

theorem restricted_cons_same (x : Nat) (letters : List Nat) :
    Restricted x (x :: letters) ↔ ∃ after, letters = x :: after ∧ x ∉ after := by
  constructor
  · rintro ⟨before,after,shape,absent,absentAfter⟩
    cases before with
    | nil => exact ⟨after,(List.cons.inj shape).2,absentAfter⟩
    | cons y ys =>
        have equal : x = y := (List.cons.inj shape).1
        subst y
        exact False.elim (absent (List.mem_cons_self))
  · rintro ⟨after,shape,absent⟩
    exact ⟨[],after,by simp [shape],by simp,absent⟩

theorem restricted_cons_ne (x y : Nat) (letters : List Nat) (different : y ≠ x) :
    Restricted x (y :: letters) ↔ Restricted x letters := by
  constructor
  · rintro ⟨before,after,shape,absent,absentAfter⟩
    cases before with
    | nil => exact False.elim (different (List.cons.inj shape).1)
    | cons z zs =>
        exact ⟨zs,after,(List.cons.inj shape).2,
          fun member => absent (List.mem_cons.mpr (Or.inr member)),absentAfter⟩
  · rintro ⟨before,after,shape,absent,absentAfter⟩
    refine ⟨y :: before,after,?_,?_,absentAfter⟩
    · simpa using congrArg (List.cons y) shape
    · intro member
      rcases List.mem_cons.mp member with equal | member
      · exact different equal.symm
      · exact absent member

inductive RestrictedState where
  | fresh | first | gap | square | dead
  deriving DecidableEq, Repr

def restrictedStep (hit : Bool) : RestrictedState → RestrictedState
  | .fresh => if hit then .first else .fresh
  | .first => if hit then .square else .gap
  | .gap => if hit then .dead else .gap
  | .square => if hit then .dead else .square
  | .dead => .dead

def restrictedScan (x : Nat) (state : RestrictedState) : List Nat → RestrictedState
  | [] => state
  | y :: ys => restrictedScan x (restrictedStep (decide (y = x)) state) ys

theorem restrictedScan_append (x : Nat) (state : RestrictedState) (left right : List Nat) :
    restrictedScan x state (left ++ right) = restrictedScan x (restrictedScan x state left) right := by
  induction left generalizing state with
  | nil => rfl
  | cons y ys ih => exact ih _

theorem restrictedScan_dead (x : Nat) (letters : List Nat) :
    restrictedScan x .dead letters = .dead := by
  induction letters with
  | nil => rfl
  | cons y ys ih => exact ih

theorem restrictedScan_gap (x : Nat) (letters : List Nat) :
    restrictedScan x .gap letters = if x ∈ letters then .dead else .gap := by
  induction letters with
  | nil => rfl
  | cons y ys ih =>
      by_cases equal : y = x
      · subst y
        simp [restrictedScan,restrictedStep,restrictedScan_dead]
      · simp [restrictedScan,restrictedStep,equal,Ne.symm equal,ih]

theorem restrictedScan_square (x : Nat) (letters : List Nat) :
    restrictedScan x .square letters = if x ∈ letters then .dead else .square := by
  induction letters with
  | nil => rfl
  | cons y ys ih =>
      by_cases equal : y = x
      · subst y
        simp [restrictedScan,restrictedStep,restrictedScan_dead]
      · simp [restrictedScan,restrictedStep,equal,Ne.symm equal,ih]

theorem restrictedScan_fresh_square (x : Nat) (letters : List Nat) :
    restrictedScan x .fresh letters = .square ↔ Restricted x letters := by
  induction letters with
  | nil =>
      constructor
      · intro impossible; cases impossible
      · intro impossible; exact False.elim (restricted_nil x impossible)
  | cons y ys ih =>
      by_cases equal : y = x
      · subst y
        rw [restricted_cons_same]
        cases ys with
        | nil => simp [restrictedScan,restrictedStep]
        | cons z zs =>
            by_cases next : z = x
            · subst z
              by_cases found : x ∈ zs
              · simp [restrictedScan,restrictedStep,restrictedScan_square,found]
              · simp [restrictedScan,restrictedStep,restrictedScan_square,found]
            · by_cases found : x ∈ zs
              · simp [restrictedScan,restrictedStep,restrictedScan_gap,next,found]
              · simp [restrictedScan,restrictedStep,restrictedScan_gap,next,found]
      · rw [restricted_cons_ne x y ys equal]
        simpa [restrictedScan,restrictedStep,equal] using ih

def RestrictedCount (n : Nat) : RestrictedState → Prop
  | .fresh => n = 0
  | .first => n = 1
  | .gap => n = 1
  | .square => n = 2
  | .dead => 2 ≤ n

theorem restrictedStep_count (hit : Bool) (state : RestrictedState) (n : Nat)
    (invariant : RestrictedCount n state) :
    RestrictedCount (n + if hit then 1 else 0) (restrictedStep hit state) := by
  cases state <;> cases hit <;> simp_all [RestrictedCount,restrictedStep] <;> omega

theorem restrictedScan_count (x : Nat) (letters : List Nat) (state : RestrictedState) (n : Nat)
    (invariant : RestrictedCount n state) :
    RestrictedCount (n + letters.count x) (restrictedScan x state letters) := by
  induction letters generalizing state n with
  | nil => simpa [restrictedScan] using invariant
  | cons y ys ih =>
      have next := restrictedStep_count (decide (y = x)) state n invariant
      have rest := ih (restrictedStep (decide (y = x)) state) (n + if decide (y = x) then 1 else 0) next
      by_cases equal : y = x
      · subst y
        simpa [restrictedScan,List.count_cons_self,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using rest
      · simpa [restrictedScan,equal,List.count_cons_of_ne equal] using rest

theorem restricted_count_two (x : Nat) (letters : List Nat) (restricted : Restricted x letters) :
    letters.count x = 2 := by
  have invariant := restrictedScan_count x letters .fresh 0 (by rfl)
  rw [(restrictedScan_fresh_square x letters).mpr restricted] at invariant
  simpa [RestrictedCount] using invariant

def Unrestricted (x : Nat) (letters : List Nat) : Prop :=
  x ∈ letters ∧ letters.count x ≠ 1 ∧ ¬ Restricted x letters

namespace Semantics

def restrictedVal (marker x : Nat) : Fin 6 := if x = marker then 4 else 5

def restrictedValue (which : Bool) : RestrictedState → Fin 6
  | .fresh => 5
  | .first => 3
  | .gap => if which then 1 else 0
  | .square => 1
  | .dead => 0

theorem restrictedValue_step (which : Bool) (state : RestrictedState) (hit : Bool) :
    mul which (restrictedValue which state) (if hit then 4 else 5) =
      restrictedValue which (restrictedStep hit state) := by
  cases which <;> cases state <;> cases hit <;> decide

theorem restrictedVal_step (which : Bool) (state : RestrictedState) (marker x : Nat) :
    mul which (restrictedValue which state) (restrictedVal marker x) =
      restrictedValue which (restrictedStep (decide (x = marker)) state) := by
  by_cases equal : x = marker
  · simpa [restrictedVal,equal] using restrictedValue_step which state true
  · simpa [restrictedVal,equal] using restrictedValue_step which state false

theorem restrictedVal_run (which : Bool) (marker : Nat) (letters : List Nat) (state : RestrictedState) :
    run which (restrictedVal marker) (restrictedValue which state) letters =
      restrictedValue which (restrictedScan marker state letters) := by
  induction letters generalizing state with
  | nil => rfl
  | cons x xs ih =>
      rw [run_cons,restrictedVal_step,ih]
      rfl

theorem restricted_probe (which : Bool) (marker : Nat) (letters : List Nat)
    (notSimple : letters.count marker ≠ 1) :
    run which (restrictedVal marker) 5 letters = 1 ↔ Restricted marker letters := by
  have probe := restrictedVal_run which marker letters .fresh
  change run which (restrictedVal marker) 5 letters = _ at probe
  rw [probe,← restrictedScan_fresh_square]
  have invariant := restrictedScan_count marker letters .fresh 0 (by rfl)
  cases result : restrictedScan marker .fresh letters with
  | fresh => cases which <;> decide
  | first => cases which <;> decide
  | square => cases which <;> decide
  | dead => cases which <;> decide
  | gap =>
      rw [result] at invariant
      have one : letters.count marker = 1 := by simpa [RestrictedCount] using invariant
      exact False.elim (notSimple one)

theorem SameEval.restricted_forward {which : Bool} {left right : List Nat}
    (same : SameEval which left right) (marker : Nat) (restricted : Restricted marker left) :
    Restricted marker right := by
  have leftNotSimple : left.count marker ≠ 1 := by
    have two := restricted_count_two marker left restricted
    omega
  have rightNotSimple : right.count marker ≠ 1 :=
    fun one => leftNotSimple ((same.countOne marker).mpr one)
  apply (restricted_probe which marker right rightNotSimple).mp
  rw [← same.runEq (restrictedVal marker) 5]
  exact (restricted_probe which marker left leftNotSimple).mpr restricted

theorem SameEval.restricted {which : Bool} {left right : List Nat}
    (same : SameEval which left right) (marker : Nat) :
    Restricted marker left ↔ Restricted marker right :=
  ⟨same.restricted_forward marker,same.symm.restricted_forward marker⟩

theorem SameEval.unrestricted {which : Bool} {left right : List Nat}
    (same : SameEval which left right) (marker : Nat) :
    Unrestricted marker left ↔ Unrestricted marker right := by
  simp only [Unrestricted,ne_eq,same.mem marker,same.countOne marker,same.restricted marker]

end Semantics

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.restricted_cons_same
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.restricted_cons_ne
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.restrictedScan_fresh_square
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.restrictedScan_count
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.restricted_count_two
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.Semantics.restrictedValue_step
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.Semantics.restrictedVal_run
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.Semantics.restricted_probe
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.Semantics.SameEval.restricted
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.Semantics.SameEval.unrestricted

end SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6
