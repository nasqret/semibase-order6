import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Sigma14ForwardDerivations
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon

/-! Sound arbitrary-word candidate stages for the two Sigma14 review packets.
Equal computed candidates imply derivability. The converse from each class's
semantics is deliberately NOT asserted before exact statement approval.
The C1 reachable interface contains only the proved forward obligation.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Sigma14

open SemigroupBasis
open S6_2708.Sigma12
open S4_71Suffix (put)

def swapFrame (front : List Nat) (penultimate last : Nat) : Word Nat :=
  let whole := front ++ [penultimate, last]
  if whole.count last = 2 then
    put (bulk [last] whole) (Word.mk last [last])
  else
    normalFrame front penultimate last

def absorbFrame (front : List Nat) (penultimate last : Nat) : Word Nat :=
  let whole := front ++ [penultimate, last]
  if whole.count last = 2 ∧ penultimate ≠ last then
    heavyWord whole
  else
    normalFrame front penultimate last

def swapNormal (word : Word Nat) : Word Nat :=
  match decompose word with
  | .single letter => Word.singleton letter
  | .frame front penultimate last => swapFrame front penultimate last

def absorbNormal (word : Word Nat) : Word Nat :=
  match decompose word with
  | .single letter => Word.singleton letter
  | .frame front penultimate last => absorbFrame front penultimate last

theorem swapNormal_single (letter : Nat) : swapNormal (Word.singleton letter) = Word.singleton letter := rfl
theorem absorbNormal_single (letter : Nat) : absorbNormal (Word.singleton letter) = Word.singleton letter := rfl

theorem swapNormal_frame (front : List Nat) (penultimate last : Nat) :
    swapNormal (framed front penultimate last) = swapFrame front penultimate last := by
  simp only [swapNormal, decompose_frame]
theorem absorbNormal_frame (front : List Nat) (penultimate last : Nat) :
    absorbNormal (framed front penultimate last) = absorbFrame front penultimate last := by
  simp only [absorbNormal, decompose_frame]

theorem derives_swapFrame (front : List Nat) (penultimate last : Nat) :
    Derives swapBasis (framed front penultimate last) (swapFrame front penultimate last) := by
  have first := derives_base_normal_swap (framed front penultimate last)
  rw [normalForm_frame] at first
  by_cases double : (front ++ [penultimate, last]).count last = 2
  · simp only [swapFrame, if_pos double]
    have notSimple : (front ++ [penultimate, last]).count last ≠ 1 := by omega
    by_cases adjacent : penultimate = last
    · simpa only [normalFrame, if_neg notSimple, if_pos double, if_pos adjacent] using first
    · simp only [normalFrame, if_neg notSimple, if_pos double, if_neg adjacent] at first
      exact first.trans (swap_separated_square _ last)
  · simpa only [swapFrame, if_neg double] using first

theorem derives_absorbFrame (front : List Nat) (penultimate last : Nat) :
    Derives absorbBasis (framed front penultimate last) (absorbFrame front penultimate last) := by
  have first := derives_base_normal_absorb (framed front penultimate last)
  rw [normalForm_frame] at first
  by_cases separatedDouble : (front ++ [penultimate, last]).count last = 2 ∧ penultimate ≠ last
  · simp only [absorbFrame, if_pos separatedDouble]
    have notSimple : (front ++ [penultimate, last]).count last ≠ 1 := by omega
    simp only [normalFrame, if_neg notSimple, if_pos separatedDouble.1, if_neg separatedDouble.2] at first
    have nonempty : bulk [last] (front ++ [penultimate, last]) ≠ [] :=
      bulk_nonempty_of_other separatedDouble.2 (by simp)
    exact first.trans (absorb_separated_heavy _ last (by omega) nonempty)
  · simpa only [absorbFrame, if_neg separatedDouble] using first

theorem derives_swapNormal (word : Word Nat) : Derives swapBasis word (swapNormal word) := by
  rcases existsSingleOrFrame word with ⟨letter, rfl⟩ | ⟨front, penultimate, last, rfl⟩
  · rw [swapNormal_single]
    exact Derives.refl _
  · rw [swapNormal_frame]
    exact derives_swapFrame front penultimate last

theorem derives_absorbNormal (word : Word Nat) : Derives absorbBasis word (absorbNormal word) := by
  rcases existsSingleOrFrame word with ⟨letter, rfl⟩ | ⟨front, penultimate, last, rfl⟩
  · rw [absorbNormal_single]
    exact Derives.refl _
  · rw [absorbNormal_frame]
    exact derives_absorbFrame front penultimate last

def swapStage : Normalization.Stage (Normalization.derivesSystem swapBasis) (Word Nat) id where
  run := swapNormal
  sound := derives_swapNormal
def absorbStage : Normalization.Stage (Normalization.derivesSystem absorbBasis) (Word Nat) id where
  run := absorbNormal
  sound := derives_absorbNormal

theorem swap_derives_of_key_eq (left right : Word Nat) (same : swapNormal left = swapNormal right) :
    Derives swapBasis left right :=
  Normalization.derives_of_key [swapStage] swapNormal id (fun _ => rfl) same

theorem absorb_derives_of_key_eq (left right : Word Nat) (same : absorbNormal left = absorbNormal right) :
    Derives absorbBasis left right :=
  Normalization.derives_of_key [absorbStage] absorbNormal id (fun _ => rfl) same

def swapReachable :
    SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.ReachableNormalForm swapBasis where
  normal := swapNormal
  derives_normal := derives_swapNormal

def absorbReachable :
    SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.ReachableNormalForm absorbBasis where
  normal := absorbNormal
  derives_normal := derives_absorbNormal

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Sigma14
