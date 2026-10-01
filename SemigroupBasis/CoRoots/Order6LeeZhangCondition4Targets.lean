import SemigroupBasis.CoRoots.Order6LeeZhangCondition4Canonical
import SemigroupBasis.Examples.FirstCappedMultiplicityFour
import SemigroupBasis.TransferPower

/-!
# Lee--Zhang Condition 4: exact order-six targets

The two direct Condition-4 roots are `S6_3930` and `S6_3932`.  Besides
checking the three displayed laws, this module records a two-coordinate power
embedding of `S4_74` into each target.  Consequently every target-valid
identity inherits the already formalized first-letter and cap-two
multiplicity invariants of `S4_74`.
-/

namespace SemigroupBasis.CoRoots.Order6LeeZhangCondition4

open SemigroupBasis
open SemigroupBasis.Examples

/-! ## Exact catalogue tables -/

def s6_3930Mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then 0 else
    if left = 1 then (if right = 4 ∨ right = 5 then 1 else 0) else
      if left = 2 then
        (if right = 4 then 1 else if right = 5 then 3 else 0)
      else if left = 3 then
        (if right = 4 ∨ right = 5 then 3 else 0)
      else if left = 4 then
        (if right = 0 then 0 else
          if right = 4 ∨ right = 5 then 4 else 1)
      else
        (if right = 0 then 0 else
          if right = 4 ∨ right = 5 then 5 else 3)

/-- The zero-based catalogue table `S6_3930`. -/
def s6_3930 : FiniteTable where
  order := 6
  mul := s6_3930Mul
  assoc := by decide

def s6_3932Mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then 0 else
    if left = 1 then (if right = 4 ∨ right = 5 then 1 else 0) else
      if left = 2 then
        (if right = 4 then 1 else if right = 5 then 3 else 0)
      else if left = 3 then
        (if right = 4 ∨ right = 5 then 3 else 0)
      else if left = 4 then
        (if right = 0 then 0 else
          if right = 4 ∨ right = 5 then 4 else 3)
      else
        (if right = 0 then 0 else
          if right = 4 ∨ right = 5 then 5 else 1)

/-- The zero-based catalogue table `S6_3932`. -/
def s6_3932 : FiniteTable where
  order := 6
  mul := s6_3932Mul
  assoc := by decide

private theorem s6_3930_power (value : Fin 6) :
    s6_3930Mul value value =
      s6_3930Mul (s6_3930Mul value value) value := by
  decide +revert

private theorem s6_3930_repeatedFirst (left right : Fin 6) :
    s6_3930Mul (s6_3930Mul left left) right =
      s6_3930Mul (s6_3930Mul left right) left := by
  decide +revert

private theorem s6_3930_tailSwap
    (first second left right : Fin 6) :
    s6_3930Mul
        (s6_3930Mul (s6_3930Mul first second) left) right =
      s6_3930Mul
        (s6_3930Mul (s6_3930Mul first second) right) left := by
  decide +revert

theorem s6_3930_models : Models s6_3930.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · intro valuation
    exact s6_3930_power (valuation 0)
  · intro valuation
    exact s6_3930_repeatedFirst (valuation 0) (valuation 1)
  · intro valuation
    exact s6_3930_tailSwap
      (valuation 0) (valuation 1) (valuation 2) (valuation 3)

private theorem s6_3932_power (value : Fin 6) :
    s6_3932Mul value value =
      s6_3932Mul (s6_3932Mul value value) value := by
  decide +revert

private theorem s6_3932_repeatedFirst (left right : Fin 6) :
    s6_3932Mul (s6_3932Mul left left) right =
      s6_3932Mul (s6_3932Mul left right) left := by
  decide +revert

private theorem s6_3932_tailSwap
    (first second left right : Fin 6) :
    s6_3932Mul
        (s6_3932Mul (s6_3932Mul first second) left) right =
      s6_3932Mul
        (s6_3932Mul (s6_3932Mul first second) right) left := by
  decide +revert

theorem s6_3932_models : Models s6_3932.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · intro valuation
    exact s6_3932_power (valuation 0)
  · intro valuation
    exact s6_3932_repeatedFirst (valuation 0) (valuation 1)
  · intro valuation
    exact s6_3932_tailSwap
      (valuation 0) (valuation 1) (valuation 2) (valuation 3)

/-! ## The protected-second probe -/

def secondProbe (first distinguished : Nat) : Nat → Fin 6 :=
  fun letter =>
    if letter = first then 2 else
      if letter = distinguished then 4 else 5

private theorem foldSecondProbeStable
    (mul : Fin 6 → Fin 6 → Fin 6)
    (stable : ∀ state right,
      (state = 1 ∨ state = 3) →
      (right = 4 ∨ right = 5) →
      mul state right = state)
    (first distinguished : Nat) :
    ∀ (letters : List Nat) (state : Fin 6),
      first ∉ letters →
      (state = 1 ∨ state = 3) →
      letters.foldl
          (fun current letter =>
            mul current (secondProbe first distinguished letter))
          state = state
  | [], state, _, _ => rfl
  | letter :: rest, state, firstAbsent, stateCase => by
      have letterNe : letter ≠ first := by
        intro equal
        apply firstAbsent
        simp [equal]
      have restAbsent : first ∉ rest := by
        intro member
        exact firstAbsent (List.Mem.tail letter member)
      have probeCase :
          secondProbe first distinguished letter = 4 ∨
            secondProbe first distinguished letter = 5 := by
        by_cases selected : letter = distinguished
        · left
          simp only [secondProbe]
          rw [if_neg letterNe, if_pos selected]
        · right
          simp only [secondProbe]
          rw [if_neg letterNe, if_neg selected]
      have step := stable state
        (secondProbe first distinguished letter) stateCase probeCase
      simp only [List.foldl_cons]
      rw [step]
      exact foldSecondProbeStable mul stable first distinguished
        rest state restAbsent stateCase

private theorem s6_3930_highStable
    (state right : Fin 6)
    (stateCase : state = 1 ∨ state = 3)
    (rightCase : right = 4 ∨ right = 5) :
    s6_3930Mul state right = state := by
  rcases stateCase with rfl | rfl <;>
    rcases rightCase with rfl | rfl <;> decide

private theorem s6_3932_highStable
    (state right : Fin 6)
    (stateCase : state = 1 ∨ state = 3)
    (rightCase : right = 4 ∨ right = 5) :
    s6_3932Mul state right = state := by
  rcases stateCase with rfl | rfl <;>
    rcases rightCase with rfl | rfl <;> decide

private theorem evalSecondProbeGeneric
    (mul : Fin 6 → Fin 6 → Fin 6)
    (stable : ∀ state right,
      (state = 1 ∨ state = 3) →
      (right = 4 ∨ right = 5) →
      mul state right = state)
    (stepFour : mul 2 4 = 1)
    (stepFive : mul 2 5 = 3)
    (first distinguished actual : Nat) (tail : List Nat)
    (different : first ≠ distinguished)
    (firstCount : (first :: actual :: tail).count first = 1) :
    (actual :: tail).foldl
        (fun current letter =>
          mul current (secondProbe first distinguished letter))
        (secondProbe first distinguished first) =
      if actual = distinguished then (1 : Fin 6) else 3 := by
  have suffixCount : (actual :: tail).count first = 0 := by
    simpa using firstCount
  have suffixAbsent : first ∉ actual :: tail :=
    List.count_eq_zero.mp suffixCount
  have actualNe : actual ≠ first := by
    intro equal
    apply suffixAbsent
    simp [equal]
  have tailAbsent : first ∉ tail := by
    intro member
    exact suffixAbsent (List.Mem.tail actual member)
  by_cases selected : actual = distinguished
  · have firstStep :
        mul (secondProbe first distinguished first)
            (secondProbe first distinguished actual) = 1 := by
      have flipped : ¬ distinguished = first := fun h => different h.symm
      simpa [secondProbe, different, flipped, actualNe, selected]
        using stepFour
    simp only [List.foldl_cons]
    rw [firstStep, if_pos selected]
    exact foldSecondProbeStable mul stable first distinguished
      tail 1 tailAbsent (Or.inl rfl)
  · have firstStep :
        mul (secondProbe first distinguished first)
            (secondProbe first distinguished actual) = 3 := by
      simpa [secondProbe, actualNe, selected] using stepFive
    simp only [List.foldl_cons]
    rw [firstStep, if_neg selected]
    exact foldSecondProbeStable mul stable first distinguished
      tail 3 tailAbsent (Or.inr rfl)

theorem s6_3930_eval_secondProbe
    (first distinguished actual : Nat) (tail : List Nat)
    (different : first ≠ distinguished)
    (firstCount : (first :: actual :: tail).count first = 1) :
    s6_3930.semigroup.eval (secondProbe first distinguished)
        ⟨first, actual :: tail⟩ =
      if actual = distinguished then (1 : Fin 6) else 3 := by
  exact evalSecondProbeGeneric s6_3930Mul s6_3930_highStable
    (by decide) (by decide) first distinguished actual tail
      different firstCount

theorem s6_3932_eval_secondProbe
    (first distinguished actual : Nat) (tail : List Nat)
    (different : first ≠ distinguished)
    (firstCount : (first :: actual :: tail).count first = 1) :
    s6_3932.semigroup.eval (secondProbe first distinguished)
        ⟨first, actual :: tail⟩ =
      if actual = distinguished then (1 : Fin 6) else 3 := by
  exact evalSecondProbeGeneric s6_3932Mul s6_3932_highStable
    (by decide) (by decide) first distinguished actual tail
      different firstCount

/-! ## Reuse of the `S4_74` semantic separators -/

/-- The two separating homomorphisms have coordinate rows
`[0,1,0,4]` and `[4,4,5,4]`. -/
def s4_74IntoS6_3930Power :
    Embedding firstCappedMultiplicityFour.semigroup
      (s6_3930.semigroup.pi (Fin 2)) where
  toFun := fun (value : Fin 4) (coordinate : Fin 2) =>
    if coordinate = 0 then
      if value = 0 then (0 : Fin 6) else
        if value = 1 then (1 : Fin 6) else
          if value = 2 then (0 : Fin 6) else (4 : Fin 6)
    else
      if value = 0 then (4 : Fin 6) else
        if value = 1 then (4 : Fin 6) else
          if value = 2 then (5 : Fin 6) else (4 : Fin 6)
  map_mul := by
    intro left right
    funext coordinate
    exact by decide +revert
  injective := by
    intro left right equalImages
    have first := congrFun equalImages (0 : Fin 2)
    have second := congrFun equalImages (1 : Fin 2)
    clear equalImages
    exact by decide +revert

/-- The first coordinate changes only at source element `3`, giving rows
`[0,1,0,5]` and `[4,4,5,4]` for `S6_3932`. -/
def s4_74IntoS6_3932Power :
    Embedding firstCappedMultiplicityFour.semigroup
      (s6_3932.semigroup.pi (Fin 2)) where
  toFun := fun (value : Fin 4) (coordinate : Fin 2) =>
    if coordinate = 0 then
      if value = 0 then (0 : Fin 6) else
        if value = 1 then (1 : Fin 6) else
          if value = 2 then (0 : Fin 6) else (5 : Fin 6)
    else
      if value = 0 then (4 : Fin 6) else
        if value = 1 then (4 : Fin 6) else
          if value = 2 then (5 : Fin 6) else (4 : Fin 6)
  map_mul := by
    intro left right
    funext coordinate
    exact by decide +revert
  injective := by
    intro left right equalImages
    have first := congrFun equalImages (0 : Fin 2)
    have second := congrFun equalImages (1 : Fin 2)
    clear equalImages
    exact by decide +revert

theorem validInFirstCappedOfS6_3930
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy s6_3930.semigroup) :
    identity.SatisfiedBy firstCappedMultiplicityFour.semigroup := by
  have powerValid :=
    identity.satisfiedByPi s6_3930.semigroup (Fin 2) valid
  exact
    s4_74IntoS6_3930Power.pullback_identity identity powerValid

theorem validInFirstCappedOfS6_3932
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy s6_3932.semigroup) :
    identity.SatisfiedBy firstCappedMultiplicityFour.semigroup := by
  have powerValid :=
    identity.satisfiedByPi s6_3932.semigroup (Fin 2) valid
  exact
    s4_74IntoS6_3932Power.pullback_identity identity powerValid

theorem s6_3930Valid_head_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy s6_3930.semigroup) :
    identity.lhs.head = identity.rhs.head :=
  firstCappedValid_head_eq identity
    (validInFirstCappedOfS6_3930 identity valid)

theorem s6_3932Valid_head_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy s6_3932.semigroup) :
    identity.lhs.head = identity.rhs.head :=
  firstCappedValid_head_eq identity
    (validInFirstCappedOfS6_3932 identity valid)

theorem s6_3930Valid_capped_count_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy s6_3930.semigroup) :
    ∀ letter,
      min (identity.lhs.toList.count letter) 2 =
        min (identity.rhs.toList.count letter) 2 :=
  firstCappedValid_capped_count_eq identity
    (validInFirstCappedOfS6_3930 identity valid)

theorem s6_3932Valid_capped_count_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy s6_3932.semigroup) :
    ∀ letter,
      min (identity.lhs.toList.count letter) 2 =
        min (identity.rhs.toList.count letter) 2 :=
  firstCappedValid_capped_count_eq identity
    (validInFirstCappedOfS6_3932 identity valid)

private theorem simpleSecondEqOfValid
    (G : Semigroup (Fin 6))
    (evalProbe :
      ∀ (first distinguished actual : Nat) (tail : List Nat),
        first ≠ distinguished →
        (first :: actual :: tail).count first = 1 →
        G.eval (secondProbe first distinguished)
            ⟨first, actual :: tail⟩ =
          if actual = distinguished then 1 else 3)
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy G)
    (headEq : identity.lhs.head = identity.rhs.head)
    (capped : ∀ letter,
      min (identity.lhs.toList.count letter) 2 =
        min (identity.rhs.toList.count letter) 2) :
    simpleSecond identity.lhs = simpleSecond identity.rhs := by
  cases identity with
  | mk left right =>
      cases left with
      | mk head leftTail =>
          cases right with
          | mk rightHead rightTail =>
              change head = rightHead at headEq
              subst rightHead
              have simpleIff :
                  (head :: leftTail).count head = 1 ↔
                    (head :: rightTail).count head = 1 := by
                have cappedHead := capped head
                simp only [Word.toList] at cappedHead
                have leftPositive :
                    0 < (head :: leftTail).count head := by simp
                have rightPositive :
                    0 < (head :: rightTail).count head := by simp
                constructor <;> intro simple <;> omega
              by_cases leftSimple :
                  (head :: leftTail).count head = 1
              · have rightSimple := simpleIff.mp leftSimple
                cases leftTail with
                | nil =>
                    cases rightTail with
                    | nil =>
                        simp [simpleSecond, Word.toList,
                          leftSimple, rightSimple]
                    | cons rightSecond rightRest =>
                        exfalso
                        have secondNe : rightSecond ≠ head := by
                          intro equal
                          subst rightSecond
                          simp [Word.toList] at rightSimple
                        have cappedSecond := capped rightSecond
                        simp [Word.toList, secondNe,
                          Ne.symm secondNe] at cappedSecond
                        omega
                | cons leftSecond leftRest =>
                    cases rightTail with
                    | nil =>
                        exfalso
                        have secondNe : leftSecond ≠ head := by
                          intro equal
                          subst leftSecond
                          simp [Word.toList] at leftSimple
                        have cappedSecond := capped leftSecond
                        simp [Word.toList, secondNe,
                          Ne.symm secondNe] at cappedSecond
                    | cons rightSecond rightRest =>
                        have headNeSecond : head ≠ leftSecond := by
                          intro equal
                          subst leftSecond
                          simp [Word.toList] at leftSimple
                        have semanticEquality :=
                          valid (secondProbe head leftSecond)
                        have leftValue :=
                          evalProbe head leftSecond leftSecond leftRest
                            headNeSecond leftSimple
                        have rightValue :=
                          evalProbe head leftSecond rightSecond rightRest
                            headNeSecond rightSimple
                        rw [leftValue, rightValue] at semanticEquality
                        have secondEq : leftSecond = rightSecond := by
                          apply Classical.byContradiction
                          intro different
                          have reverseDifferent :
                              rightSecond ≠ leftSecond := by
                            intro equal
                            exact different equal.symm
                          simp [reverseDifferent] at semanticEquality
                        subst rightSecond
                        change
                          (if (head :: leftSecond :: leftRest).count head = 1
                            then some leftSecond else none) =
                          (if (head :: leftSecond :: rightRest).count head = 1
                            then some leftSecond else none)
                        simp [leftSimple, rightSimple]
              · have rightNotSimple :
                    (head :: rightTail).count head ≠ 1 := by
                  intro rightSimple
                  exact leftSimple (simpleIff.mpr rightSimple)
                change
                  (if (head :: leftTail).count head = 1
                    then leftTail.head? else none) =
                  (if (head :: rightTail).count head = 1
                    then rightTail.head? else none)
                have leftZero : ¬ List.count head leftTail = 0 := by
                  intro zero
                  exact leftSimple (by simp [List.count_cons, zero])
                have rightZero : ¬ List.count head rightTail = 0 := by
                  intro zero
                  exact rightNotSimple (by simp [List.count_cons, zero])
                simp [leftZero, rightZero]

theorem s6_3930Valid_sameSignature
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy s6_3930.semigroup) :
    SameSignature identity.lhs identity.rhs where
  headEq := s6_3930Valid_head_eq identity valid
  cappedCounts := s6_3930Valid_capped_count_eq identity valid
  simpleSecondEq := simpleSecondEqOfValid
    s6_3930.semigroup s6_3930_eval_secondProbe identity valid
      (s6_3930Valid_head_eq identity valid)
      (s6_3930Valid_capped_count_eq identity valid)

theorem s6_3932Valid_sameSignature
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy s6_3932.semigroup) :
    SameSignature identity.lhs identity.rhs where
  headEq := s6_3932Valid_head_eq identity valid
  cappedCounts := s6_3932Valid_capped_count_eq identity valid
  simpleSecondEq := simpleSecondEqOfValid
    s6_3932.semigroup s6_3932_eval_secondProbe identity valid
      (s6_3932Valid_head_eq identity valid)
      (s6_3932Valid_capped_count_eq identity valid)

theorem s6_3930_basis_complete : BasisFor s6_3930.semigroup basis := by
  refine ⟨s6_3930_models, ?_⟩
  intro identity valid
  exact derivesOfCanonicalListEq identity.lhs identity.rhs
    (canonicalList_eq_of_signature
      (s6_3930Valid_sameSignature identity valid))

theorem s6_3932_basis_complete : BasisFor s6_3932.semigroup basis := by
  refine ⟨s6_3932_models, ?_⟩
  intro identity valid
  exact derivesOfCanonicalListEq identity.lhs identity.rhs
    (canonicalList_eq_of_signature
      (s6_3932Valid_sameSignature identity valid))

/-! ## Release-facing aliases -/

namespace S6_3930

theorem representative_basis : BasisFor s6_3930.semigroup basis :=
  s6_3930_basis_complete

theorem opposite_basis :
    BasisFor s6_3930.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_3930

namespace S6_3932

theorem representative_basis : BasisFor s6_3932.semigroup basis :=
  s6_3932_basis_complete

theorem opposite_basis :
    BasisFor s6_3932.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_3932

end SemigroupBasis.CoRoots.Order6LeeZhangCondition4
