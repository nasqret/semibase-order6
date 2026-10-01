import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0455NilZ2Presentation

/-! Unrestricted semantic boundary for the missing power-absorption step.
Appending a square at the end preserves S6_9386 evaluation exactly when its
letter already occurs at least three times. This is a semantic theorem, not
a derivation from the refuted B11 or a self-approved enlarged basis. -/

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0455NilZ2

open SemigroupBasis

def appendPair (word : Word Nat) (letter : Nat) : Word Nat := word ++ ⟨letter, [letter]⟩

theorem appendPair_toList (word : Word Nat) (letter : Nat) :
    (appendPair word letter).toList = word.toList ++ [letter, letter] := rfl

theorem appendPair_count (word : Word Nat) (letter tested : Nat) :
    (appendPair word letter).toList.count tested =
      word.toList.count tested + if tested = letter then 2 else 0 := by
  rw [appendPair_toList, List.count_append]
  by_cases equal : tested = letter
  · subst tested
    simp
  · have reverse : letter ≠ tested := Ne.symm equal
    simp [equal, reverse]

theorem appendPair_count_self (word : Word Nat) (letter : Nat) :
    (appendPair word letter).toList.count letter = word.toList.count letter + 2 := by
  simpa using appendPair_count word letter letter

theorem sameSignature_appendPair (word : Word Nat) (letter : Nat)
    (triple : 3 ≤ word.toList.count letter) :
    Msg0446NilZ2.SameSignature word (appendPair word letter) := by
  constructor
  · intro tested
    apply (Msg0446TailBudget.cap_eq_iff 3 _ _).2
    by_cases equal : tested = letter
    · subst tested
      rw [appendPair_count_self]
      constructor <;> omega
    · have counts : (appendPair word letter).toList.count tested = word.toList.count tested := by
        simpa [equal] using appendPair_count word letter tested
      rw [counts]
      exact ⟨rfl, rfl⟩
  · intro separator leftSimple rightSimple tested parity
    have member : separator ∈ word.toList :=
      List.count_pos_iff.mp (by change 0 < word.toList.count separator; rw [leftSimple]; decide)
    obtain ⟨before, after, shape⟩ := List.mem_iff_append.mp member
    have extendedShape : (appendPair word letter).toList =
        before ++ separator :: (after ++ [letter, letter]) := by
      rw [appendPair_toList, shape]
      simp [List.append_assoc]
    rw [S5_254.prefixParityBefore_iff_prefixValue leftSimple,
      S5_254.prefixParityBefore_iff_prefixValue rightSimple,
      S5_254.simplePrefixBefore_eq_of_split leftSimple before after shape,
      S5_254.simplePrefixBefore_eq_of_split rightSimple before
        (after ++ [letter, letter]) extendedShape]

theorem appendPair_valid_of_count_ge_three (word : Word Nat) (letter : Nat)
    (triple : 3 ≤ word.toList.count letter) :
    (⟨word, appendPair word letter⟩ : Identity Nat).SatisfiedBy target.semigroup :=
  Msg0446NilZ2.valid9386_of_sameSignature _ (sameSignature_appendPair word letter triple)

/-- The threshold is exact, with arbitrary word length and alphabet. -/
theorem appendPair_valid_iff_count_ge_three (word : Word Nat) (letter : Nat) :
    (⟨word, appendPair word letter⟩ : Identity Nat).SatisfiedBy target.semigroup ↔
      3 ≤ word.toList.count letter := by
  constructor
  · intro valid
    have counts :=
      (Msg0446NilZ2.sameSignature_of_valid9386 ⟨word, appendPair word letter⟩ valid).cappedCounts letter
    change min (word.toList.count letter) 3 =
      min ((appendPair word letter).toList.count letter) 3 at counts
    rw [appendPair_count_self] at counts
    omega
  · exact appendPair_valid_of_count_ge_three word letter

theorem separatedCube_is_appendPair : appendPair separatedCube.lhs 0 = separatedCube.rhs := rfl

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0455NilZ2
