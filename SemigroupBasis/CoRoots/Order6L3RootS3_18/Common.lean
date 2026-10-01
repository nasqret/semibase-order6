import SemigroupBasis.CoRoots.Order6L3Root3.Common
import SemigroupBasis.CoRoots.Order6L3RootS3_18.PrimitivesS4_2
import SemigroupBasis.CoRoots.Order6L3RootS3_18.PrimitivesS4_9

/-!
# Shared rank-9 guarded-bridge infrastructure

The short factors have one protected stratum each.  For `S4_9`, every word
of length at least three is bulk.  For `S4_2`, bulk means either an arbitrary
nonempty square or a word of length at least three.  These predicates are
closed under every `Derives` constructor, including nonempty substitution.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace SemigroupBasis.CoRoots.Order6L3RootS3_18

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.Order6L3Root3

def cube (value : Word Nat) : Word Nat :=
  (value ++ value) ++ value

theorem threeBlockDecomposition
    (value : Word Nat) (long : 3 ≤ value.toList.length) :
    ∃ first second third : Word Nat,
      value = (first ++ second) ++ third := by
  cases value with
  | mk head tail =>
      cases tail with
      | nil => simp [Word.toList] at long
      | cons second rest =>
          cases rest with
          | nil => simp [Word.toList] at long
          | cons third remaining =>
              refine ⟨Word.singleton head, Word.singleton second,
                Word.mk third remaining, ?_⟩
              rfl

private theorem listLength_le_flatMapWords
    (letters : List Nat) (substitution : Nat → Word Nat) :
    letters.length ≤
      (letters.flatMap fun letter =>
        (substitution letter).toList).length := by
  induction letters with
  | nil => simp
  | cons letter rest induction =>
      simp only [List.length_cons, List.flatMap_cons,
        List.length_append]
      have positive : 1 ≤ (substitution letter).toList.length := by
        exact wordLengthPositive (substitution letter)
      omega

theorem bindLong
    (value : Word Nat) (substitution : Nat → Word Nat)
    (long : 3 ≤ value.toList.length) :
    3 ≤ (value.bind substitution).toList.length := by
  rw [Word.toList_bind]
  exact Nat.le_trans long
    (listLength_le_flatMapWords value.toList substitution)

def EligibleS4_9 (value : Word Nat) : Prop :=
  3 ≤ value.toList.length

def EligibleS4_2 (value : Word Nat) : Prop :=
  (∃ block : Word Nat, value = block ++ block) ∨
    3 ≤ value.toList.length

def SameS4_9Class (left right : Word Nat) : Prop :=
  left = right ∨ EligibleS4_9 left ∧ EligibleS4_9 right

def SameS4_2Class (left right : Word Nat) : Prop :=
  left = right ∨ EligibleS4_2 left ∧ EligibleS4_2 right

theorem eligibleS4_9_prepend
    (pre value : Word Nat) (eligible : EligibleS4_9 value) :
    EligibleS4_9 (pre ++ value) := by
  rw [EligibleS4_9, Word.toList_append, List.length_append]
  change 3 ≤ value.toList.length at eligible
  omega

theorem eligibleS4_9_append
    (value suffix : Word Nat) (eligible : EligibleS4_9 value) :
    EligibleS4_9 (value ++ suffix) := by
  rw [EligibleS4_9, Word.toList_append, List.length_append]
  change 3 ≤ value.toList.length at eligible
  omega

theorem eligibleS4_9_bind
    (value : Word Nat) (substitution : Nat → Word Nat)
    (eligible : EligibleS4_9 value) :
    EligibleS4_9 (value.bind substitution) :=
  bindLong value substitution eligible

theorem eligibleS4_2_prepend
    (pre value : Word Nat) (eligible : EligibleS4_2 value) :
    EligibleS4_2 (pre ++ value) := by
  right
  rw [Word.toList_append, List.length_append]
  have prePositive := wordLengthPositive pre
  rcases eligible with ⟨block, rfl⟩ | long
  · rw [Word.toList_append, List.length_append]
    have blockPositive := wordLengthPositive block
    omega
  · omega

theorem eligibleS4_2_append
    (value suffix : Word Nat) (eligible : EligibleS4_2 value) :
    EligibleS4_2 (value ++ suffix) := by
  right
  rw [Word.toList_append, List.length_append]
  have suffixPositive := wordLengthPositive suffix
  rcases eligible with ⟨block, rfl⟩ | long
  · rw [Word.toList_append, List.length_append]
    have blockPositive := wordLengthPositive block
    omega
  · omega

theorem eligibleS4_2_bind
    (value : Word Nat) (substitution : Nat → Word Nat)
    (eligible : EligibleS4_2 value) :
    EligibleS4_2 (value.bind substitution) := by
  rcases eligible with ⟨block, rfl⟩ | long
  · left
    refine ⟨block.bind substitution, ?_⟩
    exact bind_append block block substitution
  · right
    exact bindLong value substitution long

private theorem sameS4_9Class_symm
    {left right : Word Nat} (same : SameS4_9Class left right) :
    SameS4_9Class right left := by
  rcases same with equal | ⟨leftEligible, rightEligible⟩
  · exact Or.inl equal.symm
  · exact Or.inr ⟨rightEligible, leftEligible⟩

private theorem sameS4_9Class_trans
    {first second third : Word Nat}
    (left : SameS4_9Class first second)
    (right : SameS4_9Class second third) :
    SameS4_9Class first third := by
  rcases left with equal | ⟨firstEligible, secondEligible⟩
  · subst second
    exact right
  · rcases right with equal | ⟨_, thirdEligible⟩
    · subst third
      exact Or.inr ⟨firstEligible, secondEligible⟩
    · exact Or.inr ⟨firstEligible, thirdEligible⟩

private theorem sameS4_2Class_symm
    {left right : Word Nat} (same : SameS4_2Class left right) :
    SameS4_2Class right left := by
  rcases same with equal | ⟨leftEligible, rightEligible⟩
  · exact Or.inl equal.symm
  · exact Or.inr ⟨rightEligible, leftEligible⟩

private theorem sameS4_2Class_trans
    {first second third : Word Nat}
    (left : SameS4_2Class first second)
    (right : SameS4_2Class second third) :
    SameS4_2Class first third := by
  rcases left with equal | ⟨firstEligible, secondEligible⟩
  · subst second
    exact right
  · rcases right with equal | ⟨_, thirdEligible⟩
    · subst third
      exact Or.inr ⟨firstEligible, secondEligible⟩
    · exact Or.inr ⟨firstEligible, thirdEligible⟩

theorem threeNilpotentDerivationClass
    {left right : Word Nat}
    (derivation : Derives threeNilpotentFourBasis left right) :
    SameS4_9Class left right := by
  induction derivation with
  | fromBasis member =>
      simp only [threeNilpotentFourBasis, List.mem_cons,
        List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl <;>
        simp [SameS4_9Class, EligibleS4_9,
          threeNilpotentXXXLawXXY, threeNilpotentXXXLawXYX,
          threeNilpotentXXXLawXYY, threeNilpotentXXXLawXYZ,
          threeNilpotentXXXLawYXX, threeNilpotentXXX,
          threeNilpotentXXY, threeNilpotentXYX, threeNilpotentXYY,
          threeNilpotentXYZ, threeNilpotentYXX, Word.toList]
  | refl => exact Or.inl rfl
  | symm _ induction => exact sameS4_9Class_symm induction
  | trans _ _ first second =>
      exact sameS4_9Class_trans first second
  | prepend pre _ induction =>
      rcases induction with equal | ⟨leftEligible, rightEligible⟩
      · exact Or.inl (congrArg (fun value => pre ++ value) equal)
      · exact Or.inr
          ⟨eligibleS4_9_prepend pre _ leftEligible,
            eligibleS4_9_prepend pre _ rightEligible⟩
  | appendRight _ suffix induction =>
      rcases induction with equal | ⟨leftEligible, rightEligible⟩
      · exact Or.inl (congrArg (fun value => value ++ suffix) equal)
      · exact Or.inr
          ⟨eligibleS4_9_append _ suffix leftEligible,
            eligibleS4_9_append _ suffix rightEligible⟩
  | subst _ substitution induction =>
      rcases induction with equal | ⟨leftEligible, rightEligible⟩
      · exact Or.inl (congrArg (fun value => value.bind substitution) equal)
      · exact Or.inr
          ⟨eligibleS4_9_bind _ substitution leftEligible,
            eligibleS4_9_bind _ substitution rightEligible⟩

theorem commonSquareDerivationClass
    {left right : Word Nat}
    (derivation :
      Derives commonSquareThreeNilpotentBasis left right) :
    SameS4_2Class left right := by
  induction derivation with
  | fromBasis member =>
      simp only [commonSquareThreeNilpotentBasis, List.mem_cons,
        List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · right
        constructor
        · left
          exact ⟨Word.singleton 0, rfl⟩
        · left
          exact ⟨Word.singleton 1, rfl⟩
      · right
        constructor
        · left
          exact ⟨Word.singleton 0, rfl⟩
        · right
          decide
  | refl => exact Or.inl rfl
  | symm _ induction => exact sameS4_2Class_symm induction
  | trans _ _ first second =>
      exact sameS4_2Class_trans first second
  | prepend pre _ induction =>
      rcases induction with equal | ⟨leftEligible, rightEligible⟩
      · exact Or.inl (congrArg (fun value => pre ++ value) equal)
      · exact Or.inr
          ⟨eligibleS4_2_prepend pre _ leftEligible,
            eligibleS4_2_prepend pre _ rightEligible⟩
  | appendRight _ suffix induction =>
      rcases induction with equal | ⟨leftEligible, rightEligible⟩
      · exact Or.inl (congrArg (fun value => value ++ suffix) equal)
      · exact Or.inr
          ⟨eligibleS4_2_append _ suffix leftEligible,
            eligibleS4_2_append _ suffix rightEligible⟩
  | subst _ substitution induction =>
      rcases induction with equal | ⟨leftEligible, rightEligible⟩
      · exact Or.inl (congrArg (fun value => value.bind substitution) equal)
      · exact Or.inr
          ⟨eligibleS4_2_bind _ substitution leftEligible,
            eligibleS4_2_bind _ substitution rightEligible⟩

theorem prependGuardOfEligibleS4_2
    (guard value : Word Nat) (eligible : EligibleS4_2 value) :
    Derives basisS4_2 value (cube guard ++ value) := by
  rcases eligible with ⟨block, rfl⟩ | long
  · simpa [cube, Word.append_assoc] using
      derives2PrimitivePrependGuardSquare block block guard
  · rcases threeBlockDecomposition value long with
      ⟨first, second, third, rfl⟩
    simpa [cube, Word.append_assoc] using
      derives2PrimitivePrependGuardLong
        first second guard third

theorem appendGuardOfEligibleS4_9
    (guard value : Word Nat) (eligible : EligibleS4_9 value) :
    Derives basisS4_9 value (value ++ cube guard) := by
  rcases threeBlockDecomposition value eligible with
    ⟨first, second, third, rfl⟩
  simpa [cube, Word.append_assoc] using
    derives9PrimitiveAppendGuardLong first second third guard

end SemigroupBasis.CoRoots.Order6L3RootS3_18
