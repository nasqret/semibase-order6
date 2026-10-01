import SemigroupBasis.CoRoots.S5_107ListDerives
import SemigroupBasis.Examples.CommutativeIndexFourFive
import SemigroupBasis.Examples.CommutativePeriodThreeFromTwo
import SemigroupBasis.Examples.CommutativePeriodTwoFromThree
import SemigroupBasis.Examples.CommutativePeriodTwoFromTwo
import SemigroupBasis.Examples.CommutativeThresholdSupportFour

namespace SemigroupBasis.RetainedStateFour

open SemigroupBasis
open SemigroupBasis.CoRoots.S5_107
open SemigroupBasis.Examples

/-! ## Threshold-period states -/

/-- The three positive exponent profiles occurring in the order-six
commutative/monoid roots whose canonical states reach four. -/
inductive Profile where
  | thresholdFour
  | periodTwoFromThree
  | periodThreeFromTwo
deriving DecidableEq, Repr

namespace Profile

/-- Canonical positive exponent data. The three cases are respectively
threshold four/period one, threshold three/period two, and threshold
two/period three. -/
def exponent : Profile → Nat → Nat
  | .thresholdFour, n => min n 4
  | .periodTwoFromThree, n => periodTwoFromThreeExponent n
  | .periodThreeFromTwo, n => periodThreeFromTwoExponent n

/-- The state reached when a fifth copy is reduced by the unary law. -/
def resetExponent : Profile → Nat
  | .thresholdFour => 4
  | .periodTwoFromThree => 3
  | .periodThreeFromTwo => 2

@[simp]
theorem exponent_zero (profile : Profile) :
    profile.exponent 0 = 0 := by
  cases profile <;> rfl

@[simp]
theorem exponent_one (profile : Profile) :
    profile.exponent 1 = 1 := by
  cases profile <;> rfl

theorem exponent_pos {profile : Profile} {n : Nat}
    (positive : 0 < n) :
    0 < profile.exponent n := by
  cases profile with
  | thresholdFour =>
      simp only [exponent]
      omega
  | periodTwoFromThree =>
      simpa [exponent] using
        periodTwoFromThreeExponent_pos positive
  | periodThreeFromTwo =>
      simpa [exponent] using
        periodThreeFromTwoExponent_pos positive

theorem exponent_le_four (profile : Profile) (n : Nat) :
    profile.exponent n ≤ 4 := by
  cases profile with
  | thresholdFour =>
      exact Nat.min_le_right n 4
  | periodTwoFromThree =>
      simp only [exponent]
      unfold periodTwoFromThreeExponent
      split <;> omega
  | periodThreeFromTwo =>
      simp only [exponent]
      unfold periodThreeFromTwoExponent
      split <;> omega

/-- Every state below four advances by one; state four wraps to the profile's
threshold-period reset. -/
theorem exponent_succ (profile : Profile) (n : Nat) :
    profile.exponent (n + 1) =
      if profile.exponent n < 4 then
        profile.exponent n + 1
      else
        profile.resetExponent := by
  cases profile with
  | thresholdFour =>
      simp only [exponent, resetExponent]
      by_cases below : min n 4 < 4
      · rw [if_pos below]
        omega
      · rw [if_neg below]
        omega
  | periodTwoFromThree =>
      simp only [exponent, resetExponent]
      rw [periodTwoFromThreeExponent_succ]
      by_cases below : periodTwoFromThreeExponent n < 4
      · simp [exponent, resetExponent, below]
      · have bound : periodTwoFromThreeExponent n ≤ 4 := by
          unfold periodTwoFromThreeExponent
          split <;> omega
        simp [exponent, resetExponent, below]
        omega
  | periodThreeFromTwo =>
      simp only [exponent, resetExponent]
      rw [periodThreeFromTwoExponent_succ]
      by_cases below : periodThreeFromTwoExponent n < 4
      · simp [exponent, resetExponent, below]
      · have bound : periodThreeFromTwoExponent n ≤ 4 := by
          unfold periodThreeFromTwoExponent
          split <;> omega
        simp [exponent, resetExponent, below]
        omega

end Profile

/-- One, two, three, or four retained copies of a block label. -/
inductive State where
  | one
  | two
  | three
  | four
deriving DecidableEq, Repr

namespace State

def exponent : State → Nat
  | .one => 1
  | .two => 2
  | .three => 3
  | .four => 4

/-- Total conversion used only after a profile exponent has been proved
positive and at most four. -/
def ofExponent : Nat → State
  | 2 => .two
  | 3 => .three
  | 4 => .four
  | _ => .one

theorem exponent_ofExponent {n : Nat}
    (positive : 0 < n) (bound : n ≤ 4) :
    (ofExponent n).exponent = n := by
  have cases : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 := by
    omega
  rcases cases with h | h | h | h <;> subst n <;> rfl

def render (state : State) (label : Nat) : List Nat :=
  List.replicate state.exponent label

end State

def Profile.state (profile : Profile) (n : Nat) : State :=
  State.ofExponent (profile.exponent n)

theorem Profile.state_exponent
    {profile : Profile} {n : Nat} (positive : 0 < n) :
    (profile.state n).exponent = profile.exponent n := by
  exact State.exponent_ofExponent
    (profile.exponent_pos positive)
    (profile.exponent_le_four n)

/-! ## Unique labelled block normal forms -/

structure Block where
  label : Nat
  state : State
deriving DecidableEq, Repr

namespace Block

def render (block : Block) : List Nat :=
  block.state.render block.label

end Block

def renderBlocks (blocks : List Block) : List Nat :=
  blocks.flatMap Block.render

def LabelsNodup (blocks : List Block) : Prop :=
  (blocks.map Block.label).Nodup

private theorem filter_ne_length_lt_cons (x : Nat) (xs : List Nat) :
    (xs.filter (fun y => decide (y ≠ x))).length <
      (x :: xs).length := by
  have filteredLength :
      (xs.filter (fun y => decide (y ≠ x))).length ≤ xs.length :=
    List.filter_sublist.length_le
  simpa only [List.length_cons] using Nat.lt_succ_of_le filteredLength

/-- Remove every copy of the current head label, then continue. This exposes
the first-occurrence order directly and stores the exact canonical exponent
state in the unique block for each label. -/
def normalizeBlocks (profile : Profile) : List Nat → List Block
  | [] => []
  | x :: xs =>
      { label := x
        state := profile.state ((x :: xs).count x) } ::
        normalizeBlocks profile
          (xs.filter (fun y => decide (y ≠ x)))
termination_by letters => letters.length
decreasing_by
  have filteredLength :
      (xs.attach.filter (fun y => decide (y.val ≠ x))).length ≤
        xs.attach.length :=
    List.filter_sublist.length_le
  simpa using Nat.lt_succ_of_le filteredLength

private theorem count_replicate_of_ne
    {x z : Nat} (different : z ≠ x) :
    ∀ n : Nat, (List.replicate n x).count z = 0
  | 0 => rfl
  | n + 1 => by
      rw [List.replicate_succ,
        List.count_cons_of_ne (Ne.symm different),
        count_replicate_of_ne different n]

private theorem count_filter_ne_self (x : Nat) (xs : List Nat) :
    (xs.filter (fun y => decide (y ≠ x))).count x = 0 := by
  apply List.count_eq_zero.mpr
  simp

private theorem count_filter_ne_of_ne
    {x z : Nat} (different : z ≠ x) (xs : List Nat) :
    (xs.filter (fun y => decide (y ≠ x))).count z = xs.count z := by
  induction xs with
  | nil => rfl
  | cons y ys inductionHypothesis =>
      by_cases yEq : y = x
      · subst y
        rw [List.filter_cons_of_neg (by simp),
          List.count_cons_of_ne (Ne.symm different)]
        exact inductionHypothesis
      · rw [List.filter_cons_of_pos (by simpa)]
        simp only [List.count_cons]
        rw [inductionHypothesis]

/-- Every block label produced by normalization occurred in the source. -/
theorem label_mem_of_mem_normalizeBlocks
    (profile : Profile) :
    ∀ {letters : List Nat} {block : Block},
      block ∈ normalizeBlocks profile letters →
        block.label ∈ letters
  | [], _, member => by
      simp [normalizeBlocks] at member
  | x :: xs, block, member => by
      simp only [normalizeBlocks, List.mem_cons] at member
      rcases member with rfl | member
      · exact List.Mem.head _
      · have inFiltered :=
          label_mem_of_mem_normalizeBlocks profile member
        exact List.Mem.tail x (List.mem_filter.mp inFiltered).1
termination_by letters => letters.length
decreasing_by
  exact filter_ne_length_lt_cons x xs

/-- The canonical normalizer emits at most one block for each label. -/
theorem normalizeBlocks_labelsNodup (profile : Profile) :
    ∀ letters : List Nat,
      LabelsNodup (normalizeBlocks profile letters)
  | [] => by
      simp [LabelsNodup, normalizeBlocks]
  | x :: xs => by
      have tailNodup :=
        normalizeBlocks_labelsNodup profile
          (xs.filter (fun y => decide (y ≠ x)))
      simp only [normalizeBlocks, LabelsNodup, List.map_cons]
      apply List.nodup_cons.mpr
      constructor
      · intro member
        rcases List.mem_map.mp member with
          ⟨block, blockMember, labelEq⟩
        have inFiltered :=
          label_mem_of_mem_normalizeBlocks profile blockMember
        have different : block.label ≠ x := by
          simpa using (List.mem_filter.mp inFiltered).2
        exact different labelEq
      · simpa [LabelsNodup] using tailNodup
termination_by letters => letters.length
decreasing_by
  exact filter_ne_length_lt_cons x xs

/-- Rendering the canonical blocks preserves exactly the profile-normalized
multiplicity of every label. -/
theorem count_renderBlocks_normalizeBlocks
    (profile : Profile) (z : Nat) :
    ∀ letters : List Nat,
      (renderBlocks (normalizeBlocks profile letters)).count z =
        profile.exponent (letters.count z)
  | [] => by
      simp [renderBlocks, normalizeBlocks]
  | x :: xs => by
      have inductionHypothesis :=
        count_renderBlocks_normalizeBlocks profile z
          (xs.filter (fun y => decide (y ≠ x)))
      unfold renderBlocks at inductionHypothesis
      simp only [normalizeBlocks, renderBlocks, List.flatMap_cons,
        Block.render, State.render, List.count_append]
      by_cases zEq : z = x
      · subst z
        rw [List.count_replicate_self,
          Profile.state_exponent (profile := profile) (by simp),
          inductionHypothesis, count_filter_ne_self,
          Profile.exponent_zero, Nat.add_zero]
      · rw [count_replicate_of_ne zEq,
          inductionHypothesis,
          count_filter_ne_of_ne zEq,
          List.count_cons_of_ne (Ne.symm zEq), Nat.zero_add]
termination_by letters => letters.length
decreasing_by
  exact filter_ne_length_lt_cons x xs

/-! ## Basis-parameterized gathering -/

/-- One occurrence can be gathered across an arbitrary middle and under an
arbitrary suffix. -/
def GatherOneDerivable
    (basis : List (Identity Nat)) : Prop :=
  ∀ (x : Nat) (middle suffix : List Nat),
    ListDerives basis
      (x :: middle ++ x :: suffix)
      (x :: x :: middle ++ suffix)

/-- The unary law contracts five adjacent copies to the profile's reset
state. Context is supplied later through `ListDerives.append`. -/
def FiveReductionDerivable
    (basis : List (Identity Nat)) (profile : Profile) : Prop :=
  ∀ x : Nat,
    ListDerives basis
      (List.replicate 5 x)
      (List.replicate profile.resetExponent x)

/-- A single later occurrence advances any positive normalized block by one
threshold-period transition. -/
def GatherStepDerivable
    (basis : List (Identity Nat)) (profile : Profile) : Prop :=
  ∀ (seen : Nat), 0 < seen →
    ∀ (x : Nat) (middle suffix : List Nat),
      ListDerives basis
        (List.replicate (profile.exponent seen) x ++
          middle ++ x :: suffix)
        (List.replicate (profile.exponent (seen + 1)) x ++
          middle ++ suffix)

/-- The common gather law plus the profile's unary five-reduction supplies
all four local state transitions. -/
theorem gatherStepDerivable_of_laws
    {basis : List (Identity Nat)} {profile : Profile}
    (gatherOne : GatherOneDerivable basis)
    (reduceFive : FiveReductionDerivable basis profile) :
    GatherStepDerivable basis profile := by
  intro seen positive x middle suffix
  let retained := profile.exponent seen
  have retainedPositive : 0 < retained :=
    profile.exponent_pos positive
  have retainedBound : retained ≤ 4 :=
    profile.exponent_le_four seen
  have retainedCases :
      retained = 1 ∨ retained = 2 ∨
        retained = 3 ∨ retained = 4 := by
    omega
  have moved :
      ListDerives basis
        (List.replicate retained x ++ middle ++ x :: suffix)
        (List.replicate (retained + 1) x ++ middle ++ suffix) := by
    rcases retainedCases with h | h | h | h
    · rw [h]
      simpa [List.append_assoc] using gatherOne x middle suffix
    · rw [h]
      simpa [List.append_assoc] using
        (gatherOne x middle suffix).prepend [x]
    · rw [h]
      simpa [List.append_assoc] using
        (gatherOne x middle suffix).prepend [x, x]
    · rw [h]
      simpa [List.append_assoc] using
        (gatherOne x middle suffix).prepend [x, x, x]
  rw [profile.exponent_succ seen]
  by_cases below : retained < 4
  · rw [if_pos below]
    exact moved
  · rw [if_neg below]
    have retainedEq : retained = 4 := by omega
    have reduced :=
      (reduceFive x).append (middle ++ suffix)
    rw [retainedEq] at moved
    have movedReduced := moved.trans <| by
      simpa [List.append_assoc] using reduced
    simpa [retained, retainedEq, List.append_assoc] using movedReduced

/-- Scan a suffix and gather every later occurrence of `x` into its retained
front block. Non-`x` letters keep their relative order. -/
theorem gatherAll
    {basis : List (Identity Nat)} {profile : Profile}
    (step : GatherStepDerivable basis profile) :
    ∀ (seen : Nat), 0 < seen →
      ∀ (x : Nat) (middle rest : List Nat),
        ListDerives basis
          (List.replicate (profile.exponent seen) x ++ middle ++ rest)
          (List.replicate
              (profile.exponent (seen + rest.count x)) x ++
            middle ++ rest.filter (fun y => decide (y ≠ x)))
  | seen, _, x, middle, [] => by
      simp
      exact ListDerives.refl _
  | seen, positive, x, middle, y :: ys => by
      by_cases yEq : y = x
      · subst y
        have first := step seen positive x middle ys
        have remaining :=
          gatherAll step (seen + 1) (by omega) x middle ys
        have countEq :
            seen + (x :: ys).count x =
              (seen + 1) + ys.count x := by
          simp
          omega
        apply first.trans
        rw [countEq]
        simpa using remaining
      · have remaining :=
          gatherAll step seen positive x (middle ++ [y]) ys
        simpa [yEq, List.count_cons_of_ne yEq,
          List.append_assoc] using remaining
termination_by
  _ _ _ _ rest => rest.length

/-- Every list derives to its first-occurrence-ordered, uniquely labelled
state-four block normal form. -/
theorem derivesNormalize
    {basis : List (Identity Nat)} {profile : Profile}
    (step : GatherStepDerivable basis profile) :
    ∀ letters : List Nat,
      ListDerives basis letters
        (renderBlocks (normalizeBlocks profile letters))
  | [] => by
      rw [normalizeBlocks]
      exact ListDerives.refl []
  | x :: xs => by
      have gathered := gatherAll step 1 (by omega) x [] xs
      have countEq :
          1 + xs.count x = (x :: xs).count x := by
        simp
        omega
      have gathered' :
          ListDerives basis (x :: xs)
            (List.replicate
                (profile.exponent ((x :: xs).count x)) x ++
              xs.filter (fun y => decide (y ≠ x))) := by
        simpa [countEq] using gathered
      have tailNormal :=
        derivesNormalize step (xs.filter (fun y => decide (y ≠ x)))
      have prefixed :=
        tailNormal.prepend
          (List.replicate
            (profile.exponent ((x :: xs).count x)) x)
      have stateExponent :
          (profile.state ((x :: xs).count x)).exponent =
            profile.exponent ((x :: xs).count x) :=
        profile.state_exponent (by simp)
      exact gathered'.trans <| by
        rw [normalizeBlocks]
        simpa only [renderBlocks, List.flatMap_cons,
          Block.render, State.render, stateExponent] using prefixed
termination_by letters => letters.length
decreasing_by
  exact filter_ne_length_lt_cons x xs

theorem derivesNormalize_of_laws
    {basis : List (Identity Nat)} {profile : Profile}
    (gatherOne : GatherOneDerivable basis)
    (reduceFive : FiveReductionDerivable basis profile)
    (letters : List Nat) :
    ListDerives basis letters
      (renderBlocks (normalizeBlocks profile letters)) :=
  derivesNormalize
    (gatherStepDerivable_of_laws gatherOne reduceFive) letters

/-! ## State-four block traces -/

/-- `Precedes left right blocks` records that `left` occurs strictly before
`right`. Normalized block lists are label-noduplicated, so this is the exact
dependent-pair order used by the trace interface. -/
def Precedes (left right : Block) (blocks : List Block) : Prop :=
  ∃ before after,
    blocks = before ++ left :: after ∧ right ∈ after

def SameStateMap (source target : List Block) : Prop :=
  ∀ block, block ∈ source ↔ block ∈ target

def BlocksIndependent
    (commutes : Nat → Nat → Prop) (left right : Block) : Prop :=
  commutes left.state.exponent right.state.exponent

def SameDependentOrder
    (commutes : Nat → Nat → Prop)
    (source target : List Block) : Prop :=
  ∀ left right,
    left ∈ source →
    right ∈ source →
    ¬ BlocksIndependent commutes left right →
    (Precedes left right source ↔ Precedes left right target)

def AdjacentSwapDerivable
    (basis : List (Identity Nat))
    (commutes : Nat → Nat → Prop) : Prop :=
  ∀ left right,
    BlocksIndependent commutes left right →
    ListDerives basis
      (left.render ++ right.render)
      (right.render ++ left.render)

/-- Reflexive-transitive closure of adjacent state commutations. Prefix
context is represented by `cons`; `swap` carries arbitrary suffix context. -/
inductive SwapClosure (independent : Block → Block → Prop) :
    List Block → List Block → Prop
  | refl (blocks : List Block) :
      SwapClosure independent blocks blocks
  | trans {source middle target : List Block} :
      SwapClosure independent source middle →
      SwapClosure independent middle target →
      SwapClosure independent source target
  | cons (head : Block) {source target : List Block} :
      SwapClosure independent source target →
      SwapClosure independent (head :: source) (head :: target)
  | swap (left right : Block) (suffix : List Block) :
      independent left right →
      SwapClosure independent
        (left :: right :: suffix) (right :: left :: suffix)

/-- Exact interface to the generic dependent-order combinatorics. The first
shared block-trace theorem can discharge this premise; the state-four lane
only needs the resulting adjacent-swap closure. -/
def TraceOrderComplete (commutes : Nat → Nat → Prop) : Prop :=
  ∀ {source target : List Block},
    LabelsNodup source →
    LabelsNodup target →
    SameStateMap source target →
    SameDependentOrder commutes source target →
    SwapClosure (BlocksIndependent commutes) source target

theorem renderSwapClosure
    {basis : List (Identity Nat)}
    {commutes : Nat → Nat → Prop}
    (adjacentSwap : AdjacentSwapDerivable basis commutes)
    {source target : List Block}
    (derivation :
      SwapClosure (BlocksIndependent commutes) source target) :
    ListDerives basis (renderBlocks source) (renderBlocks target) := by
  induction derivation with
  | refl blocks =>
      exact ListDerives.refl (renderBlocks blocks)
  | @trans source middle target first second ihFirst ihSecond =>
      exact ihFirst.trans ihSecond
  | @cons head source target tailDerivation inductionHypothesis =>
      simpa [renderBlocks] using
        inductionHypothesis.prepend head.render
  | swap left right suffix allowed =>
      simpa [renderBlocks, List.append_assoc] using
        (adjacentSwap left right allowed).append (renderBlocks suffix)

/-- Matching state maps and every dependent pair order make two state-four
block traces derivationally equivalent. -/
theorem blockTraceDerives
    {basis : List (Identity Nat)}
    {commutes : Nat → Nat → Prop}
    {source target : List Block}
    (traceOrderComplete : TraceOrderComplete commutes)
    (sourceLabelsNodup : LabelsNodup source)
    (targetLabelsNodup : LabelsNodup target)
    (sameStateMap : SameStateMap source target)
    (dependentOrder : SameDependentOrder commutes source target)
    (adjacentSwap : AdjacentSwapDerivable basis commutes) :
    ListDerives basis (renderBlocks source) (renderBlocks target) := by
  have swaps :
      SwapClosure (BlocksIndependent commutes) source target :=
    traceOrderComplete sourceLabelsNodup targetLabelsNodup
      sameStateMap dependentOrder
  exact renderSwapClosure adjacentSwap swaps

/-- End-to-end derivation interface for two words once their canonical
state maps and dependent block orders have been identified. -/
theorem derivesOfTrace
    {basis : List (Identity Nat)} {profile : Profile}
    {commutes : Nat → Nat → Prop}
    {left right : List Nat}
    (step : GatherStepDerivable basis profile)
    (traceOrderComplete : TraceOrderComplete commutes)
    (sameStateMap :
      SameStateMap
        (normalizeBlocks profile left)
        (normalizeBlocks profile right))
    (dependentOrder :
      SameDependentOrder commutes
        (normalizeBlocks profile left)
        (normalizeBlocks profile right))
    (adjacentSwap : AdjacentSwapDerivable basis commutes) :
    ListDerives basis left right := by
  have leftNormal := derivesNormalize step left
  have rightNormal := derivesNormalize step right
  have trace :=
    blockTraceDerives
      traceOrderComplete
      (normalizeBlocks_labelsNodup profile left)
      (normalizeBlocks_labelsNodup profile right)
      sameStateMap dependentOrder adjacentSwap
  exact leftNormal.trans <| trace.trans rightNormal.symm

theorem derivesOfTrace_of_laws
    {basis : List (Identity Nat)} {profile : Profile}
    {commutes : Nat → Nat → Prop}
    {left right : List Nat}
    (gatherOne : GatherOneDerivable basis)
    (reduceFive : FiveReductionDerivable basis profile)
    (traceOrderComplete : TraceOrderComplete commutes)
    (sameStateMap :
      SameStateMap
        (normalizeBlocks profile left)
        (normalizeBlocks profile right))
    (dependentOrder :
      SameDependentOrder commutes
        (normalizeBlocks profile left)
        (normalizeBlocks profile right))
    (adjacentSwap : AdjacentSwapDerivable basis commutes) :
    ListDerives basis left right :=
  derivesOfTrace
    (gatherStepDerivable_of_laws gatherOne reduceFive)
    traceOrderComplete sameStateMap dependentOrder adjacentSwap

end SemigroupBasis.RetainedStateFour
