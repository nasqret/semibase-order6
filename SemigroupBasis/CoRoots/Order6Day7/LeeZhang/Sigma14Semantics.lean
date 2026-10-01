import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Sigma14PairProbe

/-! Unrestricted semantic necessity of the two concrete Word normal forms.
All cases range over arbitrary words and arbitrary valuations; finite screens
and historical raw-presentation completeness claims are not premises. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Sigma14

open SemigroupBasis
open S6_2708.Sigma12
open S4_71Suffix (put)

instance (swapping : Bool) (front : List Nat) (penultimate last : Nat) :
    Decidable (GoodDouble swapping front penultimate last) :=
  inferInstanceAs (Decidable ((front ++ [penultimate, last]).count last = 2 ∧
    (swapping = true ∨ penultimate = last)))

def modeFrame (swapping : Bool) (front : List Nat) (penultimate last : Nat) : Word Nat :=
  let whole := front ++ [penultimate, last]
  if whole.count last = 1 then
    if whole.count penultimate = 1 then
      put (bulk [penultimate, last] whole) (Word.mk penultimate [last])
    else
      let selected := pivot whole
      put (bulk [selected, last] whole) (Word.mk selected [selected, last])
  else if GoodDouble swapping front penultimate last then
    put (bulk [last] whole) (Word.mk last [last])
  else
    heavyWord whole

theorem modeFrame_swap (front : List Nat) (penultimate last : Nat) :
    modeFrame true front penultimate last = swapFrame front penultimate last := by
  by_cases simple : (front ++ [penultimate, last]).count last = 1
  · have notDouble : (front ++ [penultimate, last]).count last ≠ 2 := by omega
    simp only [modeFrame, swapFrame, normalFrame, if_pos simple, if_neg notDouble]
  · by_cases double : (front ++ [penultimate, last]).count last = 2
    · have good : GoodDouble true front penultimate last := ⟨double, Or.inl rfl⟩
      simp only [modeFrame, swapFrame, if_neg simple, if_pos good, if_pos double]
    · have notGood : ¬GoodDouble true front penultimate last := fun good => double good.1
      simp only [modeFrame, swapFrame, normalFrame, if_neg simple, if_neg notGood, if_neg double, heavyWord]

theorem modeFrame_absorb (front : List Nat) (penultimate last : Nat) :
    modeFrame false front penultimate last = absorbFrame front penultimate last := by
  by_cases simple : (front ++ [penultimate, last]).count last = 1
  · have notDouble : (front ++ [penultimate, last]).count last ≠ 2 := by omega
    have notSeparated : ¬((front ++ [penultimate, last]).count last = 2 ∧ penultimate ≠ last) :=
      fun separated => notDouble separated.1
    simp only [modeFrame, absorbFrame, normalFrame, if_pos simple, if_neg notSeparated]
  · by_cases double : (front ++ [penultimate, last]).count last = 2
    · by_cases adjacent : penultimate = last
      · have good : GoodDouble false front penultimate last := ⟨double, Or.inr adjacent⟩
        have notSeparated : ¬((front ++ [penultimate, last]).count last = 2 ∧ penultimate ≠ last) :=
          fun separated => separated.2 adjacent
        simp only [modeFrame, absorbFrame, normalFrame, if_neg simple, if_pos good,
          if_neg notSeparated, if_pos double, if_pos adjacent]
      · have notGood : ¬GoodDouble false front penultimate last := by
          intro good
          rcases good.2 with impossible | equal
          · cases impossible
          · exact adjacent equal
        have separated : (front ++ [penultimate, last]).count last = 2 ∧ penultimate ≠ last :=
          ⟨double, adjacent⟩
        simp only [modeFrame, absorbFrame, if_neg simple, if_neg notGood, if_pos separated]
    · have notGood : ¬GoodDouble false front penultimate last := fun good => double good.1
      have notSeparated : ¬((front ++ [penultimate, last]).count last = 2 ∧ penultimate ≠ last) :=
        fun separated => double separated.1
      simp only [modeFrame, absorbFrame, normalFrame, if_neg simple, if_neg notGood,
        if_neg notSeparated, if_neg double, heavyWord]

def modeNormal (swapping : Bool) (word : Word Nat) : Word Nat :=
  if swapping then swapNormal word else absorbNormal word

theorem modeNormal_frame (swapping : Bool) (front : List Nat) (penultimate last : Nat) :
    modeNormal swapping (framed front penultimate last) = modeFrame swapping front penultimate last := by
  cases swapping <;>
    simp only [modeNormal, Bool.false_eq_true, if_false, if_true, swapNormal_frame,
      absorbNormal_frame, modeFrame_swap, modeFrame_absorb]

variable {G : Semigroup (Fin 6)} {swapping : Bool}

theorem modeFrame_eq_of_equivalent (model : ProbeModel G swapping) (leftFront rightFront : List Nat)
    (leftPenultimate rightPenultimate leftLast rightLast : Nat)
    (same : Equivalent G (framed leftFront leftPenultimate leftLast) (framed rightFront rightPenultimate rightLast)) :
    modeFrame swapping leftFront leftPenultimate leftLast =
      modeFrame swapping rightFront rightPenultimate rightLast := by
  have caps : SameCaps (leftFront ++ [leftPenultimate, leftLast]) (rightFront ++ [rightPenultimate, rightLast]) := by
    simpa only [framed_toList] using caps_of_equivalent model _ _ same
  by_cases leftSimple : (leftFront ++ [leftPenultimate, leftLast]).count leftLast = 1
  · obtain ⟨lastEqual, rightSimple⟩ := simpleLast_preserved model leftFront rightFront
      leftPenultimate rightPenultimate leftLast rightLast same leftSimple
    subst rightLast
    by_cases leftPenultimateSimple : (leftFront ++ [leftPenultimate, leftLast]).count leftPenultimate = 1
    · have penultimateEqual := simplePenultimate_preserved model leftFront rightFront
        leftPenultimate rightPenultimate leftLast same leftSimple leftPenultimateSimple
      subst rightPenultimate
      have rightPenultimateSimple := (caps.simple leftPenultimate).mp leftPenultimateSimple
      simp only [modeFrame, if_pos leftSimple, if_pos rightSimple,
        if_pos leftPenultimateSimple, if_pos rightPenultimateSimple]
      rw [bulk_eq_of_caps [leftPenultimate, leftLast] caps]
    · have rightPenultimateNotSimple : (rightFront ++ [rightPenultimate, leftLast]).count rightPenultimate ≠ 1 := by
        intro rightPenultimateSimple
        have penultimateEqual := simplePenultimate_preserved model rightFront leftFront
          rightPenultimate leftPenultimate leftLast same.symm rightSimple rightPenultimateSimple
        have leftCount := (caps.simple rightPenultimate).mpr rightPenultimateSimple
        exact leftPenultimateSimple (by simpa only [penultimateEqual] using leftCount)
      have pivotEqual := pivot_eq_of_caps caps
      simp only [modeFrame, if_pos leftSimple, if_pos rightSimple,
        if_neg leftPenultimateSimple, if_neg rightPenultimateNotSimple, pivotEqual]
      rw [bulk_eq_of_caps [pivot (rightFront ++ [rightPenultimate, leftLast]), leftLast] caps]
  · have rightNotSimple : (rightFront ++ [rightPenultimate, rightLast]).count rightLast ≠ 1 := by
      intro rightSimple
      exact leftSimple (simpleLast_preserved model rightFront leftFront rightPenultimate leftPenultimate
        rightLast leftLast same.symm rightSimple).2
    by_cases leftGood : GoodDouble swapping leftFront leftPenultimate leftLast
    · obtain ⟨lastEqual, rightGood⟩ := goodDouble_preserved model leftFront rightFront
        leftPenultimate rightPenultimate leftLast rightLast same leftGood
      subst rightLast
      simp only [modeFrame, if_neg leftSimple, if_neg rightNotSimple, if_pos leftGood, if_pos rightGood]
      rw [bulk_eq_of_caps [leftLast] caps]
    · have rightNotGood : ¬GoodDouble swapping rightFront rightPenultimate rightLast := by
        intro rightGood
        exact leftGood (goodDouble_preserved model rightFront leftFront rightPenultimate leftPenultimate
          rightLast leftLast same.symm rightGood).2
      have pivotEqual := pivot_eq_of_caps caps
      simp only [modeFrame, if_neg leftSimple, if_neg rightNotSimple,
        if_neg leftGood, if_neg rightNotGood, heavyWord, pivotEqual]
      rw [bulk_eq_of_caps [pivot (rightFront ++ [rightPenultimate, rightLast])] caps]

theorem modeNormal_eq_of_equivalent (model : ProbeModel G swapping) (left right : Word Nat)
    (same : Equivalent G left right) : modeNormal swapping left = modeNormal swapping right := by
  rcases existsSingleOrFrame left with ⟨letter, rfl⟩ | ⟨leftFront, leftPenultimate, leftLast, rfl⟩
  · have caps : SameCaps [letter] right.toList := caps_of_equivalent model _ _ same
    rw [singleton_of_caps right letter caps]
  · rcases existsSingleOrFrame right with ⟨letter, rfl⟩ | ⟨rightFront, rightPenultimate, rightLast, rfl⟩
    · have caps : SameCaps [letter] (framed leftFront leftPenultimate leftLast).toList :=
        caps_of_equivalent model _ _ same.symm
      rw [singleton_of_caps _ letter caps]
    · rw [modeNormal_frame, modeNormal_frame]
      exact modeFrame_eq_of_equivalent model leftFront rightFront
        leftPenultimate rightPenultimate leftLast rightLast same

theorem swapNormal_eq_of_equivalent (model : ProbeModel G true) (left right : Word Nat)
    (same : Equivalent G left right) : swapNormal left = swapNormal right :=
  modeNormal_eq_of_equivalent model left right same

theorem absorbNormal_eq_of_equivalent (model : ProbeModel G false) (left right : Word Nat)
    (same : Equivalent G left right) : absorbNormal left = absorbNormal right :=
  modeNormal_eq_of_equivalent model left right same

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Sigma14
