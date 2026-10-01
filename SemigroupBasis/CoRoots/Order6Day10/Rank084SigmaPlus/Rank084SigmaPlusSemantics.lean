import SemigroupBasis.CoRoots.Order6Day10.Rank084SigmaPlus.Rank084SigmaPlusMacros

/-! Actual S4_11 length/support separators and actual S4_77 ordered-prefix
separators. Long tails are handled by fold induction or the existing proved
two-letter evaluation theorem. No bounded semantic-key test is assumed. -/

namespace SemigroupBasis.CoRoots.Order6Day10.Rank084SigmaPlus.Rank084SigmaPlusSemantics

open SemigroupBasis
open SemigroupBasis.CoRoots.Order6Day10.Rank084SigmaPlus.Rank084SigmaPlusMacros

abbrev leftTable := Rank084SigmaPlusMacros.leftTable
abbrev rightTable := Rank084SigmaPlusMacros.rightTable

inductive LengthClass where
  | singleton
  | pair
  | triple
  | long
deriving DecidableEq, Repr

def lengthClass (word : Word Nat) : LengthClass :=
  match word.tail with
  | [] => .singleton
  | [_] => .pair
  | [_, _] => .triple
  | _ :: _ :: _ :: _ => .long

def lengthCode : LengthClass → Fin 4
  | .singleton => 3
  | .pair => 1
  | .triple => 2
  | .long => 0

theorem lengthCode_injective : Function.Injective lengthCode := by
  intro left right equal
  cases left <;> cases right <;> simp [lengthCode] at equal ⊢

theorem cyclic_zero_left (value : Fin 4) : leftTable.mul (0 : Fin 4) value = (0 : Fin 4) := by decide +revert

theorem cyclic_four_zero (a b c d : Fin 4) :
    leftTable.mul (leftTable.mul (leftTable.mul a b) c) d = (0 : Fin 4) := by decide +revert

theorem cyclicFoldZero (valuation : Nat → Fin 4) (letters : List Nat) :
    letters.foldl (fun current letter => leftTable.mul current (valuation letter)) (0 : Fin 4) = (0 : Fin 4) := by
  induction letters with
  | nil => rfl
  | cons letter rest ih =>
      rw [List.foldl_cons, cyclic_zero_left]
      exact ih

theorem cyclicLongEval (valuation : Nat → Fin 4) (a b c d : Nat) (rest : List Nat) :
    leftTable.semigroup.eval valuation (Word.mk a (b :: c :: d :: rest)) = (0 : Fin 4) := by
  change rest.foldl (fun current letter => leftTable.mul current (valuation letter))
    (leftTable.mul (leftTable.mul (leftTable.mul (valuation a) (valuation b)) (valuation c)) (valuation d)) = (0 : Fin 4)
  rw [cyclic_four_zero]
  exact cyclicFoldZero valuation rest

theorem cyclicLength_eval (word : Word Nat) :
    leftTable.semigroup.eval (fun _ => (3 : Fin 4)) word = lengthCode (lengthClass word) := by
  rcases word with ⟨a, tail⟩
  cases tail with
  | nil => rfl
  | cons b rest =>
      cases rest with
      | nil => rfl
      | cons c more =>
          cases more with
          | nil => rfl
          | cons d final => exact cyclicLongEval (fun _ => (3 : Fin 4)) a b c d final

theorem cyclicValid_lengthClass (identity : Identity Nat)
    (valid : identity.SatisfiedBy leftTable.semigroup) :
    lengthClass identity.lhs = lengthClass identity.rhs := by
  have evaluated := valid (fun _ => (3 : Fin 4))
  rw [cyclicLength_eval, cyclicLength_eval] at evaluated
  exact lengthCode_injective evaluated

def cyclicMarker (selected letter : Nat) : Fin 4 := if letter = selected then 0 else 3

theorem cyclicMarker_pair (selected a b : Nat) :
    leftTable.mul (cyclicMarker selected a) (cyclicMarker selected b) =
      if selected ∈ [a, b] then (0 : Fin 4) else (1 : Fin 4) := by
  change Examples.cyclicFourOneMul (cyclicMarker selected a) (cyclicMarker selected b) =
    if selected ∈ [a, b] then (0 : Fin 4) else 1
  by_cases ha : a = selected
  · subst a
    simp [cyclicMarker, Examples.cyclicFourOneMul]
  · by_cases hb : b = selected
    · subst b
      simp [cyclicMarker, Examples.cyclicFourOneMul, ha, Ne.symm ha]
    · simp [cyclicMarker, Examples.cyclicFourOneMul, ha, hb, Ne.symm ha, Ne.symm hb]

theorem cyclicMarker_triple (selected a b c : Nat) :
    leftTable.mul (leftTable.mul (cyclicMarker selected a) (cyclicMarker selected b)) (cyclicMarker selected c) =
      if selected ∈ [a, b, c] then (0 : Fin 4) else (2 : Fin 4) := by
  change Examples.cyclicFourOneMul
    (Examples.cyclicFourOneMul (cyclicMarker selected a) (cyclicMarker selected b)) (cyclicMarker selected c) =
    if selected ∈ [a, b, c] then (0 : Fin 4) else 2
  by_cases ha : a = selected
  · subst a
    simp [cyclicMarker, Examples.cyclicFourOneMul]
  · by_cases hb : b = selected
    · subst b
      simp [cyclicMarker, Examples.cyclicFourOneMul, ha, Ne.symm ha]
    · by_cases hc : c = selected
      · subst c
        simp [cyclicMarker, Examples.cyclicFourOneMul, ha, hb, Ne.symm ha, Ne.symm hb]
      · simp [cyclicMarker, Examples.cyclicFourOneMul, ha, hb, hc, Ne.symm ha, Ne.symm hb, Ne.symm hc]

theorem cyclicMarker_eval (selected : Nat) (word : Word Nat) :
    leftTable.semigroup.eval (cyclicMarker selected) word =
      if selected ∈ word.toList then (0 : Fin 4) else lengthCode (lengthClass word) := by
  rcases word with ⟨a, tail⟩
  cases tail with
  | nil =>
      change cyclicMarker selected a = if selected ∈ [a] then 0 else 3
      simp [cyclicMarker, eq_comm]
  | cons b rest =>
      cases rest with
      | nil => exact cyclicMarker_pair selected a b
      | cons c more =>
          cases more with
          | nil => exact cyclicMarker_triple selected a b c
          | cons d final =>
              simpa [lengthClass, lengthCode] using cyclicLongEval (cyclicMarker selected) a b c d final

theorem shortLengthCode_ne_zero (kind : LengthClass) (short : kind ≠ .long) : lengthCode kind ≠ 0 := by
  cases kind <;> simp_all [lengthCode]

def SameSupport (left right : Word Nat) : Prop :=
  ∀ letter, letter ∈ left.toList ↔ letter ∈ right.toList

theorem cyclicShort_support (identity : Identity Nat)
    (valid : identity.SatisfiedBy leftTable.semigroup) (short : lengthClass identity.lhs ≠ .long) :
    SameSupport identity.lhs identity.rhs := by
  have lengths := cyclicValid_lengthClass identity valid
  have nonzero := shortLengthCode_ne_zero _ short
  intro letter
  have evaluated := valid (cyclicMarker letter)
  rw [cyclicMarker_eval, cyclicMarker_eval, ← lengths] at evaluated
  constructor
  · intro leftMember
    apply Decidable.byContradiction
    intro rightAbsent
    rw [if_pos leftMember, if_neg rightAbsent] at evaluated
    exact nonzero evaluated.symm
  · intro rightMember
    apply Decidable.byContradiction
    intro leftAbsent
    rw [if_neg leftAbsent, if_pos rightMember] at evaluated
    exact nonzero evaluated

def FirstTwo (word : Word Nat) : List Nat := word.toList.take 2

theorem rightPairEval (valuation : Nat → Fin 4) (a b : Nat) (rest : List Nat) :
    rightTable.semigroup.eval valuation (Word.mk a (b :: rest)) =
      Examples.twoLetterPrefixFourMul (valuation a) (valuation b) :=
  Examples.twoLetterPrefixEval_pair valuation a b rest

def headValuation (selected letter : Nat) : Fin 4 := if letter = selected then 3 else 2

theorem rightHead_eval (selected : Nat) (word : Word Nat) :
    rightTable.semigroup.eval (headValuation selected) word =
      if word.head = selected then (3 : Fin 4) else (2 : Fin 4) := by
  rcases word with ⟨a, tail⟩
  cases tail with
  | nil => rfl
  | cons b rest =>
      rw [rightPairEval]
      by_cases equal : a = selected <;> simp [headValuation, equal, Examples.twoLetterPrefixFourMul]

theorem rightHead_eq (identity : Identity Nat) (valid : identity.SatisfiedBy rightTable.semigroup) :
    identity.lhs.head = identity.rhs.head := by
  have evaluated := valid (headValuation identity.lhs.head)
  rw [rightHead_eval, rightHead_eval] at evaluated
  apply Decidable.byContradiction
  intro different
  simp [Ne.symm different] at evaluated

theorem rightSingleton_eval (word : Word Nat) :
    rightTable.semigroup.eval (fun _ => (1 : Fin 4)) word = (1 : Fin 4) ↔ word.tail = [] := by
  rcases word with ⟨a, tail⟩
  cases tail with
  | nil => simp [Semigroup.eval]
  | cons b rest =>
      rw [rightPairEval]
      simp [Examples.twoLetterPrefixFourMul]

theorem rightSingleton_iff (identity : Identity Nat) (valid : identity.SatisfiedBy rightTable.semigroup) :
    identity.lhs.tail = [] ↔ identity.rhs.tail = [] := by
  have evaluated := valid (fun _ => (1 : Fin 4))
  calc
    identity.lhs.tail = [] ↔ rightTable.semigroup.eval (fun _ => (1 : Fin 4)) identity.lhs = (1 : Fin 4) := (rightSingleton_eval _).symm
    _ ↔ rightTable.semigroup.eval (fun _ => (1 : Fin 4)) identity.rhs = (1 : Fin 4) := by rw [evaluated]
    _ ↔ identity.rhs.tail = [] := rightSingleton_eval _

theorem rightSecond_eq (first leftSecond rightSecond : Nat) (leftRest rightRest : List Nat)
    (valid : (Identity.mk (Word.mk first (leftSecond :: leftRest))
      (Word.mk first (rightSecond :: rightRest))).SatisfiedBy rightTable.semigroup) :
    leftSecond = rightSecond := by
  by_cases leftFirst : leftSecond = first
  · subst leftSecond
    let valuation : Nat → Fin 4 := fun letter => if letter = first then 1 else 3
    have evaluated := valid valuation
    rw [rightPairEval, rightPairEval] at evaluated
    apply Decidable.byContradiction
    intro different
    simp [valuation, Ne.symm different, Examples.twoLetterPrefixFourMul] at evaluated
  · let valuation : Nat → Fin 4 := fun letter => if letter = first then 1 else if letter = leftSecond then 3 else 0
    have evaluated := valid valuation
    rw [rightPairEval, rightPairEval] at evaluated
    apply Decidable.byContradiction
    intro different
    by_cases rightFirst : rightSecond = first
    · simp [valuation, leftFirst, rightFirst, Examples.twoLetterPrefixFourMul] at evaluated
    · simp [valuation, leftFirst, rightFirst, Ne.symm different, Examples.twoLetterPrefixFourMul] at evaluated

theorem rightFirstTwo (identity : Identity Nat) (valid : identity.SatisfiedBy rightTable.semigroup) :
    FirstTwo identity.lhs = FirstTwo identity.rhs := by
  rcases identity with ⟨⟨a, leftTail⟩, ⟨b, rightTail⟩⟩
  have heads : a = b := rightHead_eq ⟨⟨a, leftTail⟩, ⟨b, rightTail⟩⟩ valid
  have singletons := rightSingleton_iff ⟨⟨a, leftTail⟩, ⟨b, rightTail⟩⟩ valid
  subst b
  cases leftTail with
  | nil =>
      have rightNil : rightTail = [] := singletons.mp rfl
      subst rightTail
      rfl
  | cons leftSecond leftRest =>
      cases rightTail with
      | nil => simp at singletons
      | cons rightSecond rightRest =>
          have seconds := rightSecond_eq a leftSecond rightSecond leftRest rightRest valid
          subst rightSecond
          rfl

end SemigroupBasis.CoRoots.Order6Day10.Rank084SigmaPlus.Rank084SigmaPlusSemantics
