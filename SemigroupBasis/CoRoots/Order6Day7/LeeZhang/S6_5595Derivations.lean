import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_5595Presentation
import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S4_71SuffixReplay

/-! Six unchanged raw laws discharge the suffix replay and terminal-cube moves.
The internal subset is not an amendment or an extra completed system. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_5595

open SemigroupBasis

def coreBasis : List (Identity Nat) := [law00, law01, law03, law04, law05, law07]

theorem coreBasis_length : coreBasis.length = 6 := rfl

theorem core_subset_raw (identity : Identity Nat) (member : identity ∈ coreBasis) : identity ∈ basis := by
  simp only [coreBasis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [basis]

theorem core_models : Models table.semigroup coreBasis :=
  fun identity member => models_raw identity (core_subset_raw identity member)

private def substituteThree (first second third : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | letter + 3 => Word.singleton (letter + 3)

theorem derivesCubeExpansion (x : Word Nat) :
    Derives coreBasis ((x ++ x) ++ x) (((x ++ x) ++ x) ++ x) := by
  have primitive : Derives coreBasis law00.lhs law00.rhs := Derives.fromBasis (by simp [coreBasis])
  simpa [law00, substituteThree, Word.bind, Word.append, Word.append_assoc] using
    primitive.subst (substituteThree x x x)

theorem derivesPrefixPower (x suffix : Word Nat) :
    Derives coreBasis ((x ++ x) ++ suffix) (((x ++ x) ++ x) ++ suffix) := by
  have primitive : Derives coreBasis law01.lhs law01.rhs := Derives.fromBasis (by simp [coreBasis])
  simpa [law01, substituteThree, Word.bind, Word.append, Word.append_assoc] using
    (primitive.subst (substituteThree x suffix suffix)).symm

theorem derivesPrefixGather (x y suffix : Word Nat) :
    Derives coreBasis (((x ++ y) ++ x) ++ suffix) (((y ++ x) ++ x) ++ suffix) := by
  have primitive : Derives coreBasis law07.lhs law07.rhs := Derives.fromBasis (by simp [coreBasis])
  simpa [law07, substituteThree, Word.bind, Word.append, Word.append_assoc] using
    primitive.subst (substituteThree x y suffix)

theorem derivesPrefixSquareCommutation (x y suffix : Word Nat) :
    Derives coreBasis (((x ++ x) ++ (y ++ y)) ++ suffix)
      (((y ++ y) ++ (x ++ x)) ++ suffix) := by
  have primitive : Derives coreBasis law05.lhs law05.rhs := Derives.fromBasis (by simp [coreBasis])
  have first : Derives coreBasis (((x ++ x) ++ (y ++ y)) ++ suffix)
      (((x ++ (y ++ y)) ++ x) ++ suffix) := by
    simpa [law05, substituteThree, Word.bind, Word.append, Word.append_assoc] using
      primitive.subst (substituteThree x y suffix)
  exact first.trans (by
    simpa only [Word.append_assoc] using derivesPrefixGather x (y ++ y) suffix)

theorem derivesHeavyGather (x middle : Word Nat) :
    Derives coreBasis (((x ++ x) ++ middle) ++ x) (middle ++ ((x ++ x) ++ x)) := by
  have primitive : Derives coreBasis law03.lhs law03.rhs := Derives.fromBasis (by simp [coreBasis])
  simpa [law03, substituteThree, Word.bind, Word.append, Word.append_assoc] using
    primitive.subst (substituteThree x middle middle)

theorem derivesHeavySwitch (x y : Word Nat) :
    Derives coreBasis (((x ++ x) ++ (y ++ y)) ++ x) ((x ++ x) ++ ((y ++ y) ++ y)) := by
  have primitive : Derives coreBasis law04.lhs law04.rhs := Derives.fromBasis (by simp [coreBasis])
  simpa [law04, substituteThree, Word.bind, Word.append, Word.append_assoc] using
    primitive.subst (substituteThree x y y)

def coreSuffixRules : S4_71Suffix.Rules coreBasis where
  power := derivesPrefixPower
  gather := derivesPrefixGather
  squareCommute := derivesPrefixSquareCommutation

structure TerminalRules (system : List (Identity Nat)) : Prop where
  prefixRules : S4_71Suffix.Rules system
  cubeExpand : ∀ x : Word Nat,
    Derives system ((x ++ x) ++ x) (((x ++ x) ++ x) ++ x)
  heavyGather : ∀ x middle : Word Nat,
    Derives system (((x ++ x) ++ middle) ++ x) (middle ++ ((x ++ x) ++ x))
  heavySwitch : ∀ x y : Word Nat,
    Derives system (((x ++ x) ++ (y ++ y)) ++ x) ((x ++ x) ++ ((y ++ y) ++ y))

def coreRules : TerminalRules coreBasis where
  prefixRules := coreSuffixRules
  cubeExpand := derivesCubeExpansion
  heavyGather := derivesHeavyGather
  heavySwitch := derivesHeavySwitch

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_5595
