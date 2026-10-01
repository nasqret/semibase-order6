import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_2708Raw11Presentation
import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.CappedListNormalization
import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S4_71SuffixReplay
import SemigroupBasis.CoRoots.S5_107ListDerives

/-! Exact contextual rewrites for the approved Sigma12. The internal eight-law
subset is not a different proposal. Every fixed-window obligation is derived. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_2708.Sigma12

open SemigroupBasis
open S4_71Suffix (put put_toList)

def coreBasis : List (Identity Nat) :=
  [law00, law01, law03, law04, law05, law07, law08, missingPrefixSwap]

theorem core_subset_sigma12 (identity : Identity Nat) (member : identity ∈ coreBasis) :
    identity ∈ sigma12 := by
  simp only [coreBasis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [sigma12, basis]

theorem core_models : Models table.semigroup coreBasis :=
  fun identity member => models_sigma12 identity (core_subset_sigma12 identity member)

abbrev Rel := SemigroupBasis.CoRoots.S5_107.ListDerives coreBasis

private def sub4 (a b c d : Word Nat) : Nat → Word Nat
  | 0 => a
  | 1 => b
  | 2 => c
  | 3 => d
  | letter + 4 => Word.singleton (letter + 4)

theorem derivesCubeExpansion (x : Word Nat) :
    Derives coreBasis ((x ++ x) ++ x) (((x ++ x) ++ x) ++ x) := by
  have primitive : Derives coreBasis law00.lhs law00.rhs := Derives.fromBasis (by simp [coreBasis])
  simpa [law00, sub4, Word.bind, Word.append, Word.append_assoc] using primitive.subst (sub4 x x x x)

theorem derivesPrefixPower (x suffix : Word Nat) :
    Derives coreBasis (((x ++ x) ++ x) ++ suffix) ((x ++ x) ++ suffix) := by
  have primitive : Derives coreBasis law01.lhs law01.rhs := Derives.fromBasis (by simp [coreBasis])
  simpa [law01, sub4, Word.bind, Word.append, Word.append_assoc] using primitive.subst (sub4 x suffix suffix suffix)

theorem derivesPrefixGather (x middle suffix : Word Nat) :
    Derives coreBasis (((x ++ middle) ++ x) ++ suffix) (((middle ++ x) ++ x) ++ suffix) := by
  have primitive : Derives coreBasis law07.lhs law07.rhs := Derives.fromBasis (by simp [coreBasis])
  simpa [law07, sub4, Word.bind, Word.append, Word.append_assoc] using primitive.subst (sub4 x middle suffix suffix)

theorem derivesHeavyGather (x middle : Word Nat) :
    Derives coreBasis (((x ++ x) ++ middle) ++ x) (middle ++ ((x ++ x) ++ x)) := by
  have primitive : Derives coreBasis law03.lhs law03.rhs := Derives.fromBasis (by simp [coreBasis])
  simpa [law03, sub4, Word.bind, Word.append, Word.append_assoc] using primitive.subst (sub4 x middle middle middle)

theorem derivesHeavySwitch (x y : Word Nat) :
    Derives coreBasis (((x ++ x) ++ (y ++ y)) ++ x) ((x ++ x) ++ ((y ++ y) ++ y)) := by
  have primitive : Derives coreBasis law04.lhs law04.rhs := Derives.fromBasis (by simp [coreBasis])
  simpa [law04, sub4, Word.bind, Word.append, Word.append_assoc] using primitive.subst (sub4 x y y y)

theorem derivesSquareCommute (x y suffix : Word Nat) :
    Derives coreBasis (((x ++ x) ++ (y ++ y)) ++ suffix) (((y ++ y) ++ (x ++ x)) ++ suffix) := by
  have primitive : Derives coreBasis law05.lhs law05.rhs := Derives.fromBasis (by simp [coreBasis])
  have first : Derives coreBasis (((x ++ x) ++ (y ++ y)) ++ suffix)
      (((x ++ (y ++ y)) ++ x) ++ suffix) := by
    simpa [law05, sub4, Word.bind, Word.append, Word.append_assoc] using primitive.subst (sub4 x y suffix suffix)
  exact first.trans (by simpa only [Word.append_assoc] using derivesPrefixGather x (y ++ y) suffix)

theorem derivesMiddleSwap (x left right : Word Nat) :
    Derives coreBasis (((x ++ left) ++ right) ++ x) (((x ++ right) ++ left) ++ x) := by
  have primitive : Derives coreBasis law08.lhs law08.rhs := Derives.fromBasis (by simp [coreBasis])
  simpa [law08, sub4, Word.bind, Word.append, Word.append_assoc] using primitive.subst (sub4 x left right right)

theorem derivesPrefixSwap (left right firstTail secondTail : Word Nat) :
    Derives coreBasis (((left ++ right) ++ firstTail) ++ secondTail)
      (((right ++ left) ++ firstTail) ++ secondTail) := by
  have primitive : Derives coreBasis missingPrefixSwap.lhs missingPrefixSwap.rhs := Derives.fromBasis (by simp [coreBasis])
  change Derives coreBasis (Word.mk 1 [2, 3, 0]) (Word.mk 2 [1, 3, 0]) at primitive
  simpa [sub4, Word.bind, Word.append, Word.append_assoc] using
    primitive.subst (sub4 secondTail left right firstTail)

theorem relPrefixSwap (front : List Nat) (left right : Nat) (rest : List Nat)
    (penultimate last : Nat) :
    Rel (front ++ left :: right :: (rest ++ [penultimate, last]))
      (front ++ right :: left :: (rest ++ [penultimate, last])) := by
  have step := SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
    (derivesPrefixSwap (Word.singleton left) (Word.singleton right)
      (put rest (Word.singleton penultimate)) (Word.singleton last))
  simpa only [Word.toList_append, Word.toList_singleton, put_toList,
    List.cons_append, List.nil_append, List.append_assoc] using step.prepend front

theorem relTriple (front : List Nat) (letter : Nat) (rest : List Nat) (suffix : Word Nat) :
    Rel (front ++ [letter, letter, letter] ++ rest ++ suffix.toList)
      (front ++ [letter, letter] ++ rest ++ suffix.toList) := by
  have step := SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
    (derivesPrefixPower (Word.singleton letter) (put rest suffix))
  simpa only [Word.toList_append, Word.toList_singleton, put_toList,
    List.cons_append, List.nil_append, List.append_assoc] using step.prepend front

def windowSystem (before after : List Nat) : Normalization.System (List Nat) where
  rel left right := Rel (before ++ left ++ after) (before ++ right ++ after)
  refl := fun _ => .refl _
  symm := fun proof => proof.symm
  trans := fun first second => first.trans second

def capTwo : Nat → Nat := fun _ => 2
def exceptPivot (pivot : Nat) : Nat → Nat := fun letter => if letter = pivot then 0 else 2

def prefixRules (penultimate last : Nat) : CappedList.Rules (windowSystem [] [penultimate, last]) capTwo where
  swap := by
    intro front left right rest
    simpa only [windowSystem, List.nil_append, List.append_assoc, List.cons_append] using
      relPrefixSwap front left right rest penultimate last
  contract := by
    intro front letter rest
    simpa only [windowSystem, capTwo, List.nil_append, List.replicate_succ, List.replicate_zero,
      Word.toList, List.append_assoc, List.cons_append] using
      relTriple front letter rest (Word.mk penultimate [last])

theorem relPrefixPermutation {left right : List Nat} (permutation : left.Perm right)
    (penultimate last : Nat) : Rel (left ++ [penultimate, last]) (right ++ [penultimate, last]) := by
  have result := (prefixRules penultimate last).permute permutation [] []
  simpa only [windowSystem, List.nil_append, List.append_nil] using result

theorem relPrefixNormal (front : List Nat) (penultimate last : Nat) :
    Rel (front ++ [penultimate, last]) (CappedList.normal capTwo front ++ [penultimate, last]) :=
  (prefixRules penultimate last).normal_sound front

theorem relMiddleAdjacentSwap (pivot : Nat) (front : List Nat) (left right : Nat) (rest : List Nat) :
    Rel ([pivot] ++ front ++ left :: right :: rest ++ [pivot])
      ([pivot] ++ front ++ right :: left :: rest ++ [pivot]) := by
  cases rest with
  | nil =>
      have exposePermutation : ([pivot] ++ front ++ [left]).Perm (front ++ [pivot, left]) := by
        simpa only [List.append_assoc] using
          (List.perm_append_comm (l₁ := [pivot]) (l₂ := front)).append_right [left]
      have expose := relPrefixPermutation exposePermutation right pivot
      have step := (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
        (derivesMiddleSwap (Word.singleton pivot) (Word.singleton left) (Word.singleton right))).prepend front
      have restorePermutation : (front ++ [pivot, right]).Perm ([pivot] ++ front ++ [right]) := by
        simpa only [List.append_assoc] using
          (List.perm_append_comm (l₁ := front) (l₂ := [pivot])).append_right [right]
      have restore := relPrefixPermutation restorePermutation left pivot
      simp only [Word.toList_append, Word.toList_singleton, List.append_assoc, List.cons_append, List.nil_append] at expose step restore ⊢
      exact expose.trans (step.trans restore)
  | cons next tail =>
      have step := SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
        (derivesPrefixSwap (Word.singleton left) (Word.singleton right)
          (Word.mk next tail) (Word.singleton pivot))
      simpa only [Word.toList_append, Word.toList_singleton, Word.toList,
        List.append_assoc, List.cons_append, List.nil_append] using step.prepend ([pivot] ++ front)

def middleRules (pivot : Nat) : CappedList.Rules (windowSystem [pivot] [pivot]) capTwo where
  swap := by
    intro front left right rest
    simpa only [windowSystem, List.append_assoc] using relMiddleAdjacentSwap pivot front left right rest
  contract := by
    intro front letter rest
    simpa only [windowSystem, capTwo, List.replicate_succ, List.replicate_zero,
      Word.toList_singleton, List.append_assoc, List.cons_append, List.nil_append] using
      relTriple ([pivot] ++ front) letter rest (Word.singleton pivot)

theorem relMiddleNormal (pivot : Nat) (middle : List Nat) :
    Rel ([pivot] ++ middle ++ [pivot]) ([pivot] ++ CappedList.normal capTwo middle ++ [pivot]) :=
  (middleRules pivot).normal_sound middle

theorem relDeleteBeforeSquare (front rest : List Nat) (pivot last : Nat) :
    Rel (front ++ pivot :: rest ++ [pivot, pivot, last]) (front ++ rest ++ [pivot, pivot, last]) := by
  have permutation : (pivot :: (rest ++ [pivot])).Perm (rest ++ [pivot, pivot]) := by
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using
      (List.perm_append_comm (l₁ := [pivot]) (l₂ := rest)).append_right [pivot]
  have expose := (relPrefixPermutation permutation pivot last).prepend front
  have step := relTriple (front ++ rest) pivot [] (Word.singleton last)
  simp only [List.append_assoc, List.cons_append, List.nil_append, List.append_nil, Word.toList_singleton] at expose step ⊢
  exact expose.trans step

theorem relDeleteBeforeCube (front rest : List Nat) (pivot : Nat) :
    Rel (front ++ pivot :: rest ++ [pivot, pivot, pivot]) (front ++ rest ++ [pivot, pivot, pivot]) := by
  have permutation : (pivot :: (rest ++ [pivot])).Perm (rest ++ [pivot, pivot]) := by
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using
      (List.perm_append_comm (l₁ := [pivot]) (l₂ := rest)).append_right [pivot]
  have expose := (relPrefixPermutation permutation pivot pivot).prepend front
  have step := (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
    (derivesCubeExpansion (Word.singleton pivot)).symm).prepend (front ++ rest)
  simp only [Word.toList_append, Word.toList_singleton, List.append_assoc,
    List.cons_append, List.nil_append] at expose step ⊢
  exact expose.trans step

def squareRules (pivot last : Nat) : CappedList.Rules (windowSystem [] [pivot, pivot, last]) (exceptPivot pivot) where
  swap := by
    intro front left right rest
    simpa only [windowSystem, List.nil_append, List.append_assoc, List.cons_append] using
      relPrefixSwap front left right (rest ++ [pivot]) pivot last
  contract := by
    intro front letter rest
    by_cases equal : letter = pivot
    · subst letter
      simpa only [windowSystem, exceptPivot, if_pos rfl, List.replicate_succ, List.replicate_zero,
        List.nil_append, List.append_assoc, List.cons_append] using relDeleteBeforeSquare front rest pivot last
    · simpa only [windowSystem, exceptPivot, if_neg equal, List.replicate_succ, List.replicate_zero,
        List.nil_append, List.append_assoc, List.cons_append, Word.toList] using
        relTriple front letter rest (Word.mk pivot [pivot, last])

def cubeRules (pivot : Nat) : CappedList.Rules (windowSystem [] [pivot, pivot, pivot]) (exceptPivot pivot) where
  swap := by
    intro front left right rest
    simpa only [windowSystem, List.nil_append, List.append_assoc, List.cons_append] using
      relPrefixSwap front left right (rest ++ [pivot]) pivot pivot
  contract := by
    intro front letter rest
    by_cases equal : letter = pivot
    · subst letter
      simpa only [windowSystem, exceptPivot, if_pos rfl, List.replicate_succ, List.replicate_zero,
        List.nil_append, List.append_assoc, List.cons_append] using relDeleteBeforeCube front rest pivot
    · simpa only [windowSystem, exceptPivot, if_neg equal, List.replicate_succ, List.replicate_zero,
        List.nil_append, List.append_assoc, List.cons_append, Word.toList] using
        relTriple front letter rest (Word.mk pivot [pivot, pivot])

theorem relSquareNormal (front : List Nat) (pivot last : Nat) :
    Rel (front ++ [pivot, pivot, last])
      (CappedList.normal (exceptPivot pivot) front ++ [pivot, pivot, last]) :=
  (squareRules pivot last).normal_sound front

theorem relCubeNormal (front : List Nat) (pivot : Nat) :
    Rel (front ++ [pivot, pivot, pivot])
      (CappedList.normal (exceptPivot pivot) front ++ [pivot, pivot, pivot]) :=
  (cubeRules pivot).normal_sound front

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_2708.Sigma12
