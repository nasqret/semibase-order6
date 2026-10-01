import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_6183Presentation
import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S4_71SuffixReplay

/-! Arbitrary nonempty-word instances of the unchanged raw7. These discharge
the existing S4_71 prefix replay and the new marked-terminal square move.
The five first examples across both original screen windows derive without
adding any law: the screen only instantiates letters, not arbitrary words. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_6183

open SemigroupBasis

private def substituteThree (first second third : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | letter + 3 => Word.singleton (letter + 3)

theorem derivesPower (x : Word Nat) : Derives basis (x ++ x) ((x ++ x) ++ x) := by
  have primitive : Derives basis law00.lhs law00.rhs := Derives.fromBasis (by simp [basis])
  simpa [law00, substituteThree, Word.bind, Word.append, Word.append_assoc] using
    primitive.subst (substituteThree x x x)

theorem derivesRepeatContraction (x middle : Word Nat) :
    Derives basis (((x ++ x) ++ middle) ++ x) ((x ++ middle) ++ x) := by
  have primitive : Derives basis law01.lhs law01.rhs := Derives.fromBasis (by simp [basis])
  simpa [law01, substituteThree, Word.bind, Word.append, Word.append_assoc] using
    primitive.subst (substituteThree x middle middle)

theorem derivesSquareInterleave (x y : Word Nat) :
    Derives basis ((x ++ x) ++ (y ++ y)) (((x ++ y) ++ x) ++ y) := by
  have primitive : Derives basis law02.lhs law02.rhs := Derives.fromBasis (by simp [basis])
  simpa [law02, substituteThree, Word.bind, Word.append, Word.append_assoc] using
    primitive.subst (substituteThree x y y)

theorem derivesSquareSandwich (x y : Word Nat) :
    Derives basis ((x ++ x) ++ (y ++ y)) ((x ++ (y ++ y)) ++ x) := by
  have primitive : Derives basis law03.lhs law03.rhs := Derives.fromBasis (by simp [basis])
  simpa [law03, substituteThree, Word.bind, Word.append, Word.append_assoc] using
    primitive.subst (substituteThree x y y)

theorem derivesMarkedSquareSplit (x marked middle : Word Nat) :
    Derives basis ((((x ++ x) ++ marked) ++ middle) ++ marked)
      ((((x ++ marked) ++ x) ++ middle) ++ marked) := by
  have primitive : Derives basis law04.lhs law04.rhs := Derives.fromBasis (by simp [basis])
  simpa [law04, substituteThree, Word.bind, Word.append, Word.append_assoc] using
    primitive.subst (substituteThree x marked middle)

theorem derivesPrefixGather (x middle suffix : Word Nat) :
    Derives basis (((x ++ middle) ++ x) ++ suffix) (((middle ++ x) ++ x) ++ suffix) := by
  have primitive : Derives basis law05.lhs law05.rhs := Derives.fromBasis (by simp [basis])
  simpa [law05, substituteThree, Word.bind, Word.append, Word.append_assoc] using
    primitive.subst (substituteThree x middle suffix)

theorem derivesDeleteBeforeSquare (x middle : Word Nat) :
    Derives basis ((x ++ middle) ++ (x ++ x)) (middle ++ (x ++ x)) := by
  have primitive : Derives basis law06.lhs law06.rhs := Derives.fromBasis (by simp [basis])
  simpa [law06, substituteThree, Word.bind, Word.append, Word.append_assoc] using
    (primitive.subst (substituteThree middle x x)).symm

theorem derivesSquareCommutation (x y : Word Nat) :
    Derives basis ((x ++ x) ++ (y ++ y)) ((y ++ y) ++ (x ++ x)) := by
  have first := (derivesSquareInterleave x y).trans (derivesPrefixGather x y y)
  exact first.trans (by simpa only [Word.append_assoc] using (derivesSquareSandwich y x).symm)

theorem derivesMarkedSquareSwap (x marked middle : Word Nat) :
    Derives basis ((((x ++ x) ++ marked) ++ middle) ++ marked)
      ((((marked ++ x) ++ x) ++ middle) ++ marked) := by
  exact (derivesMarkedSquareSplit x marked middle).trans (by
    simpa only [Word.append_assoc] using derivesPrefixGather x marked (middle ++ marked))

def prefixRules : S4_71Suffix.Rules basis where
  power := fun x suffix => Derives.appendRight (derivesPower x) suffix
  gather := derivesPrefixGather
  squareCommute := fun x y suffix => Derives.appendRight (derivesSquareCommutation x y) suffix

theorem prefix_lower_replay (left right : List Nat) (suffix : Word Nat)
    (same : ∀ valuation, S4_71Suffix.listEval valuation left = S4_71Suffix.listEval valuation right) :
    Derives basis (S4_71Suffix.put left suffix) (S4_71Suffix.put right suffix) :=
  prefixRules.derivesLists left right suffix same

theorem derivesTripleSandwichExpansion (x middle : Word Nat) :
    Derives basis ((x ++ middle) ++ x) ((((x ++ x) ++ x) ++ middle) ++ x) := by
  exact (derivesRepeatContraction x middle).symm.trans (by
    simpa only [Word.append_assoc] using Derives.appendRight (derivesPower x) (middle ++ x))

theorem derivesFourthSandwichExpansion (x middle : Word Nat) :
    Derives basis ((x ++ middle) ++ x) (((((x ++ x) ++ x) ++ x) ++ middle) ++ x) := by
  exact (derivesTripleSandwichExpansion x middle).trans (by
    simpa only [Word.append_assoc] using
      Derives.appendRight (Derives.appendRight (derivesPower x) x) (middle ++ x))

theorem screenGap_xyzx_xxyzx : Derives basis (Word.mk 0 [1,2,0]) (Word.mk 0 [0,1,2,0]) := by
  simpa [Word.append] using (derivesRepeatContraction (Word.singleton 0) (Word.mk 1 [2])).symm

theorem screenGap_xyzx_xxxyzx : Derives basis (Word.mk 0 [1,2,0]) (Word.mk 0 [0,0,1,2,0]) := by
  simpa [Word.append] using derivesTripleSandwichExpansion (Word.singleton 0) (Word.mk 1 [2])

theorem screenGap_xyzx_xxxxyzx : Derives basis (Word.mk 0 [1,2,0]) (Word.mk 0 [0,0,0,1,2,0]) := by
  simpa [Word.append] using derivesFourthSandwichExpansion (Word.singleton 0) (Word.mk 1 [2])

theorem screenGap_xzyx_xxzyx : Derives basis (Word.mk 0 [2,1,0]) (Word.mk 0 [0,2,1,0]) := by
  simpa [Word.append] using (derivesRepeatContraction (Word.singleton 0) (Word.mk 2 [1])).symm

theorem screenGap_xzyx_xxxzyx : Derives basis (Word.mk 0 [2,1,0]) (Word.mk 0 [0,0,2,1,0]) := by
  simpa [Word.append] using derivesTripleSandwichExpansion (Word.singleton 0) (Word.mk 2 [1])

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_6183
