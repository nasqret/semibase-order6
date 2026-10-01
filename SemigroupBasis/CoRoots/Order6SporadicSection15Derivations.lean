import SemigroupBasis.CoRoots.Order6SporadicSection15
import SemigroupBasis.CoRoots.S5_107ListDerives

namespace SemigroupBasis.CoRoots.Order6SporadicSection15

open SemigroupBasis

/-- List-level derivability for the Section 15 basis. -/
abbrev ListDerives : List Nat → List Nat → Prop :=
  S5_107.ListDerives basis

/-- Put any word-level Section 15 derivation under arbitrary list context. -/
theorem listDerivesContextOfWord
    (before after : List Nat) {left right : Word Nat}
    (derivation : Derives basis left right) :
    ListDerives
      (before ++ left.toList ++ after)
      (before ++ right.toList ++ after) :=
  S5_107.ListDerives.context before after
    (S5_107.ListDerives.ofWord derivation)

private def instantiateSevenWords
    (x y h k optionalH optionalK optionalT : Word Nat) : Nat → Word Nat
  | 0 => x
  | 1 => y
  | 2 => h
  | 3 => k
  | 4 => optionalH
  | 5 => optionalK
  | 6 => optionalT
  | n + 7 => Word.singleton (n + 7)

/-- Append a paper context when that context is present.  The expanded
Section 15 basis supplies a separate semigroup identity for the absent case. -/
def appendOptional (stem : Word Nat) : Option (Word Nat) → Word Nat
  | none => stem
  | some context => stem ++ context

private theorem substituteBasisLaw
    (identity : Identity Nat) (member : identity ∈ basis)
    (replacement : Nat → Word Nat) :
    Derives basis
      (identity.lhs.bind replacement)
      (identity.rhs.bind replacement) :=
  Derives.subst (Derives.fromBasis (e := identity) member) replacement

def pattern15_1aCore
    (x : Word Nat) (optionalH optionalK : Option (Word Nat)) : Word Nat :=
  appendOptional (appendOptional x optionalH ++ x) optionalK ++ x

def pattern15_1aLeft
    (x : Word Nat) (optionalH optionalK : Option (Word Nat)) : Word Nat :=
  x ++ pattern15_1aCore x optionalH optionalK

def pattern15_1aMiddle
    (x : Word Nat) (optionalH optionalK : Option (Word Nat)) : Word Nat :=
  appendOptional
      ((appendOptional x optionalH ++ x) ++ x) optionalK ++ x

def pattern15_1aRight
    (x : Word Nat) (optionalH optionalK : Option (Word Nat)) : Word Nat :=
  pattern15_1aCore x optionalH optionalK ++ x

def pattern15_1bSource
    (x y : Word Nat)
    (optionalH optionalK optionalT : Option (Word Nat)) : Word Nat :=
  appendOptional
      (appendOptional
        (appendOptional x optionalH ++ y) optionalK ++ x)
      optionalT ++ y

def pattern15_1bLeftTarget
    (x y : Word Nat)
    (optionalH optionalK optionalT : Option (Word Nat)) : Word Nat :=
  appendOptional
      (appendOptional
        (appendOptional y optionalH ++ x) optionalK ++ x)
      optionalT ++ y

def pattern15_1bMiddleTarget
    (x y : Word Nat)
    (optionalH optionalK optionalT : Option (Word Nat)) : Word Nat :=
  appendOptional
      (appendOptional
        (appendOptional x optionalH ++ x) optionalK ++ y)
      optionalT ++ y

def pattern15_1bRightTarget
    (x y : Word Nat)
    (optionalH optionalK optionalT : Option (Word Nat)) : Word Nat :=
  appendOptional
      (appendOptional
        (appendOptional x optionalH ++ y) optionalK ++ y)
      optionalT ++ x

def pattern15_1cLeftSource
    (x y h : Word Nat) (optionalK : Option (Word Nat)) : Word Nat :=
  appendOptional (((x ++ x) ++ h) ++ y) optionalK ++ y

def pattern15_1cLeftTarget
    (x y h : Word Nat) (optionalK : Option (Word Nat)) : Word Nat :=
  appendOptional (((x ++ h) ++ x) ++ y) optionalK ++ y

def pattern15_1cMiddleSource
    (x y : Word Nat) (optionalH optionalK : Option (Word Nat)) : Word Nat :=
  appendOptional
      (appendOptional (x ++ x) optionalH ++ y) optionalK ++ y

def pattern15_1cMiddleTarget
    (x y : Word Nat) (optionalH optionalK : Option (Word Nat)) : Word Nat :=
  (appendOptional
      (appendOptional x optionalH ++ y) optionalK ++ x) ++ y

def pattern15_1cRightSource
    (x y k : Word Nat) (optionalH : Option (Word Nat)) : Word Nat :=
  (((appendOptional y optionalH ++ x) ++ x) ++ k) ++ y

def pattern15_1cRightTarget
    (x y k : Word Nat) (optionalH : Option (Word Nat)) : Word Nat :=
  (((appendOptional y optionalH ++ x) ++ k) ++ x) ++ y

def pattern15_1dLeftSource
    (x y k : Word Nat) (optionalH : Option (Word Nat)) : Word Nat :=
  (((appendOptional x optionalH ++ x) ++ k) ++ y) ++ y

def pattern15_1dLeftTarget
    (x y k : Word Nat) (optionalH : Option (Word Nat)) : Word Nat :=
  (((appendOptional x optionalH ++ x) ++ y) ++ k) ++ y

def pattern15_1dMiddleSource
    (x y : Word Nat) (optionalH optionalK : Option (Word Nat)) : Word Nat :=
  (appendOptional
      (appendOptional x optionalH ++ x) optionalK ++ y) ++ y

def pattern15_1dMiddleTarget
    (x y : Word Nat) (optionalH optionalK : Option (Word Nat)) : Word Nat :=
  appendOptional
      (appendOptional (x ++ y) optionalH ++ x) optionalK ++ y

def pattern15_1dRightSource
    (x y h : Word Nat) (optionalK : Option (Word Nat)) : Word Nat :=
  appendOptional (((x ++ h) ++ y) ++ y) optionalK ++ x

def pattern15_1dRightTarget
    (x y h : Word Nat) (optionalK : Option (Word Nat)) : Word Nat :=
  appendOptional (((x ++ y) ++ h) ++ y) optionalK ++ x

def pattern15_1eForwardSource
    (x y h k : Word Nat) (optionalT : Option (Word Nat)) : Word Nat :=
  appendOptional ((((h ++ x) ++ h) ++ y) ++ k) optionalT ++ k

def pattern15_1eForwardTarget
    (x y h k : Word Nat) (optionalT : Option (Word Nat)) : Word Nat :=
  appendOptional ((((h ++ y) ++ h) ++ x) ++ k) optionalT ++ k

def pattern15_1eReverseSource
    (x y h k : Word Nat) (optionalT : Option (Word Nat)) : Word Nat :=
  ((((appendOptional k optionalT ++ k) ++ x) ++ h) ++ y) ++ h

def pattern15_1eReverseTarget
    (x y h k : Word Nat) (optionalT : Option (Word Nat)) : Word Nat :=
  ((((appendOptional k optionalT ++ k) ++ y) ++ h) ++ x) ++ h

def pattern15_1fLeft (x y h : Word Nat) : Word Nat :=
  (((h ++ x) ++ h) ++ y) ++ h

def pattern15_1fRight (x y h : Word Nat) : Word Nat :=
  (((h ++ y) ++ h) ++ x) ++ h

/-- Substitution form of the left placement in (15.1a), selecting one of the
four generated laws according to the two optional contexts. -/
theorem derives15_1aLeft
    (x : Word Nat) (optionalH optionalK : Option (Word Nat)) :
    Derives basis
      (pattern15_1aLeft x optionalH optionalK)
      (pattern15_1aCore x optionalH optionalK) := by
  cases optionalH with
  | none =>
      cases optionalK with
      | none =>
          simpa [pattern15_1aLeft, pattern15_1aCore, appendOptional,
            law_15_1a_left_empty, word_15_1a_left_empty_left,
            word_15_1a_left_empty_right, instantiateSevenWords,
            Word.bind, Word.append, Word.singleton, Word.append_assoc] using
            (substituteBasisLaw law_15_1a_left_empty (by simp [basis])
              (instantiateSevenWords x x x x x x x))
      | some kContext =>
          simpa [pattern15_1aLeft, pattern15_1aCore, appendOptional,
            law_15_1a_left_K, word_15_1a_left_K_left,
            word_15_1a_left_K_right, instantiateSevenWords,
            Word.bind, Word.append, Word.singleton, Word.append_assoc] using
            (substituteBasisLaw law_15_1a_left_K (by simp [basis])
              (instantiateSevenWords x x x x x kContext x))
  | some hContext =>
      cases optionalK with
      | none =>
          simpa [pattern15_1aLeft, pattern15_1aCore, appendOptional,
            law_15_1a_left_H, word_15_1a_left_H_left,
            word_15_1a_left_H_right, instantiateSevenWords,
            Word.bind, Word.append, Word.singleton, Word.append_assoc] using
            (substituteBasisLaw law_15_1a_left_H (by simp [basis])
              (instantiateSevenWords x x x x hContext x x))
      | some kContext =>
          simpa [pattern15_1aLeft, pattern15_1aCore, appendOptional,
            law_15_1a_left_HK, word_15_1a_left_HK_left,
            word_15_1a_left_HK_right, instantiateSevenWords,
            Word.bind, Word.append, Word.singleton, Word.append_assoc] using
            (substituteBasisLaw law_15_1a_left_HK (by simp [basis])
              (instantiateSevenWords x x x x hContext kContext x))

/-- Substitution form of the middle placement in (15.1a). -/
theorem derives15_1aMiddle
    (x : Word Nat) (optionalH optionalK : Option (Word Nat)) :
    Derives basis
      (pattern15_1aMiddle x optionalH optionalK)
      (pattern15_1aCore x optionalH optionalK) := by
  cases optionalH with
  | none =>
      cases optionalK with
      | none =>
          simpa [pattern15_1aMiddle, pattern15_1aCore, appendOptional,
            law_15_1a_middle_empty, word_15_1a_middle_empty_left,
            word_15_1a_middle_empty_right, instantiateSevenWords,
            Word.bind, Word.append, Word.singleton, Word.append_assoc] using
            (substituteBasisLaw law_15_1a_middle_empty (by simp [basis])
              (instantiateSevenWords x x x x x x x))
      | some kContext =>
          simpa [pattern15_1aMiddle, pattern15_1aCore, appendOptional,
            law_15_1a_middle_K, word_15_1a_middle_K_left,
            word_15_1a_middle_K_right, instantiateSevenWords,
            Word.bind, Word.append, Word.singleton, Word.append_assoc] using
            (substituteBasisLaw law_15_1a_middle_K (by simp [basis])
              (instantiateSevenWords x x x x x kContext x))
  | some hContext =>
      cases optionalK with
      | none =>
          simpa [pattern15_1aMiddle, pattern15_1aCore, appendOptional,
            law_15_1a_middle_H, word_15_1a_middle_H_left,
            word_15_1a_middle_H_right, instantiateSevenWords,
            Word.bind, Word.append, Word.singleton, Word.append_assoc] using
            (substituteBasisLaw law_15_1a_middle_H (by simp [basis])
              (instantiateSevenWords x x x x hContext x x))
      | some kContext =>
          simpa [pattern15_1aMiddle, pattern15_1aCore, appendOptional,
            law_15_1a_middle_HK, word_15_1a_middle_HK_left,
            word_15_1a_middle_HK_right, instantiateSevenWords,
            Word.bind, Word.append, Word.singleton, Word.append_assoc] using
            (substituteBasisLaw law_15_1a_middle_HK (by simp [basis])
              (instantiateSevenWords x x x x hContext kContext x))

/-- Substitution form of the right placement in (15.1a). -/
theorem derives15_1aRight
    (x : Word Nat) (optionalH optionalK : Option (Word Nat)) :
    Derives basis
      (pattern15_1aRight x optionalH optionalK)
      (pattern15_1aCore x optionalH optionalK) := by
  cases optionalH with
  | none =>
      cases optionalK with
      | none =>
          simpa [pattern15_1aRight, pattern15_1aCore, appendOptional,
            law_15_1a_right_empty, word_15_1a_right_empty_left,
            word_15_1a_right_empty_right, instantiateSevenWords,
            Word.bind, Word.append, Word.singleton, Word.append_assoc] using
            (substituteBasisLaw law_15_1a_right_empty (by simp [basis])
              (instantiateSevenWords x x x x x x x))
      | some kContext =>
          simpa [pattern15_1aRight, pattern15_1aCore, appendOptional,
            law_15_1a_right_K, word_15_1a_right_K_left,
            word_15_1a_right_K_right, instantiateSevenWords,
            Word.bind, Word.append, Word.singleton, Word.append_assoc] using
            (substituteBasisLaw law_15_1a_right_K (by simp [basis])
              (instantiateSevenWords x x x x x kContext x))
  | some hContext =>
      cases optionalK with
      | none =>
          simpa [pattern15_1aRight, pattern15_1aCore, appendOptional,
            law_15_1a_right_H, word_15_1a_right_H_left,
            word_15_1a_right_H_right, instantiateSevenWords,
            Word.bind, Word.append, Word.singleton, Word.append_assoc] using
            (substituteBasisLaw law_15_1a_right_H (by simp [basis])
              (instantiateSevenWords x x x x hContext x x))
      | some kContext =>
          simpa [pattern15_1aRight, pattern15_1aCore, appendOptional,
            law_15_1a_right_HK, word_15_1a_right_HK_left,
            word_15_1a_right_HK_right, instantiateSevenWords,
            Word.bind, Word.append, Word.singleton, Word.append_assoc] using
            (substituteBasisLaw law_15_1a_right_HK (by simp [basis])
              (instantiateSevenWords x x x x hContext kContext x))

/-- Substitution form of the left placement in (15.1b). -/
theorem derives15_1bLeft
    (x y : Word Nat)
    (optionalH optionalK optionalT : Option (Word Nat)) :
    Derives basis
      (pattern15_1bSource x y optionalH optionalK optionalT)
      (pattern15_1bLeftTarget x y optionalH optionalK optionalT) := by
  cases optionalH with
  | none =>
      cases optionalK with
      | none =>
          cases optionalT with
          | none =>
              simpa [pattern15_1bSource, pattern15_1bLeftTarget,
                appendOptional, law_15_1b_left_empty,
                word_15_1b_left_empty_left, word_15_1b_left_empty_right,
                instantiateSevenWords, Word.bind, Word.append,
                Word.singleton, Word.append_assoc] using
                (substituteBasisLaw law_15_1b_left_empty (by simp [basis])
                  (instantiateSevenWords x y x x x x x))
          | some tContext =>
              simpa [pattern15_1bSource, pattern15_1bLeftTarget,
                appendOptional, law_15_1b_left_T,
                word_15_1b_left_T_left, word_15_1b_left_T_right,
                instantiateSevenWords, Word.bind, Word.append,
                Word.singleton, Word.append_assoc] using
                (substituteBasisLaw law_15_1b_left_T (by simp [basis])
                  (instantiateSevenWords x y x x x x tContext))
      | some kContext =>
          cases optionalT with
          | none =>
              simpa [pattern15_1bSource, pattern15_1bLeftTarget,
                appendOptional, law_15_1b_left_K,
                word_15_1b_left_K_left, word_15_1b_left_K_right,
                instantiateSevenWords, Word.bind, Word.append,
                Word.singleton, Word.append_assoc] using
                (substituteBasisLaw law_15_1b_left_K (by simp [basis])
                  (instantiateSevenWords x y x x x kContext x))
          | some tContext =>
              simpa [pattern15_1bSource, pattern15_1bLeftTarget,
                appendOptional, law_15_1b_left_KT,
                word_15_1b_left_KT_left, word_15_1b_left_KT_right,
                instantiateSevenWords, Word.bind, Word.append,
                Word.singleton, Word.append_assoc] using
                (substituteBasisLaw law_15_1b_left_KT (by simp [basis])
                  (instantiateSevenWords x y x x x kContext tContext))
  | some hContext =>
      cases optionalK with
      | none =>
          cases optionalT with
          | none =>
              simpa [pattern15_1bSource, pattern15_1bLeftTarget,
                appendOptional, law_15_1b_left_H,
                word_15_1b_left_H_left, word_15_1b_left_H_right,
                instantiateSevenWords, Word.bind, Word.append,
                Word.singleton, Word.append_assoc] using
                (substituteBasisLaw law_15_1b_left_H (by simp [basis])
                  (instantiateSevenWords x y x x hContext x x))
          | some tContext =>
              simpa [pattern15_1bSource, pattern15_1bLeftTarget,
                appendOptional, law_15_1b_left_HT,
                word_15_1b_left_HT_left, word_15_1b_left_HT_right,
                instantiateSevenWords, Word.bind, Word.append,
                Word.singleton, Word.append_assoc] using
                (substituteBasisLaw law_15_1b_left_HT (by simp [basis])
                  (instantiateSevenWords x y x x hContext x tContext))
      | some kContext =>
          cases optionalT with
          | none =>
              simpa [pattern15_1bSource, pattern15_1bLeftTarget,
                appendOptional, law_15_1b_left_HK,
                word_15_1b_left_HK_left, word_15_1b_left_HK_right,
                instantiateSevenWords, Word.bind, Word.append,
                Word.singleton, Word.append_assoc] using
                (substituteBasisLaw law_15_1b_left_HK (by simp [basis])
                  (instantiateSevenWords x y x x hContext kContext x))
          | some tContext =>
              simpa [pattern15_1bSource, pattern15_1bLeftTarget,
                appendOptional, law_15_1b_left_HKT,
                word_15_1b_left_HKT_left, word_15_1b_left_HKT_right,
                instantiateSevenWords, Word.bind, Word.append,
                Word.singleton, Word.append_assoc] using
                (substituteBasisLaw law_15_1b_left_HKT (by simp [basis])
                  (instantiateSevenWords x y x x hContext kContext tContext))

/-- Substitution form of the middle placement in (15.1b). -/
theorem derives15_1bMiddle
    (x y : Word Nat)
    (optionalH optionalK optionalT : Option (Word Nat)) :
    Derives basis
      (pattern15_1bSource x y optionalH optionalK optionalT)
      (pattern15_1bMiddleTarget x y optionalH optionalK optionalT) := by
  cases optionalH with
  | none =>
      cases optionalK with
      | none =>
          cases optionalT with
          | none =>
              simpa [pattern15_1bSource, pattern15_1bMiddleTarget,
                appendOptional, law_15_1b_middle_empty,
                word_15_1b_middle_empty_left,
                word_15_1b_middle_empty_right, instantiateSevenWords,
                Word.bind, Word.append, Word.singleton,
                Word.append_assoc] using
                (substituteBasisLaw law_15_1b_middle_empty (by simp [basis])
                  (instantiateSevenWords x y x x x x x))
          | some tContext =>
              simpa [pattern15_1bSource, pattern15_1bMiddleTarget,
                appendOptional, law_15_1b_middle_T,
                word_15_1b_middle_T_left, word_15_1b_middle_T_right,
                instantiateSevenWords, Word.bind, Word.append,
                Word.singleton, Word.append_assoc] using
                (substituteBasisLaw law_15_1b_middle_T (by simp [basis])
                  (instantiateSevenWords x y x x x x tContext))
      | some kContext =>
          cases optionalT with
          | none =>
              simpa [pattern15_1bSource, pattern15_1bMiddleTarget,
                appendOptional, law_15_1b_middle_K,
                word_15_1b_middle_K_left, word_15_1b_middle_K_right,
                instantiateSevenWords, Word.bind, Word.append,
                Word.singleton, Word.append_assoc] using
                (substituteBasisLaw law_15_1b_middle_K (by simp [basis])
                  (instantiateSevenWords x y x x x kContext x))
          | some tContext =>
              simpa [pattern15_1bSource, pattern15_1bMiddleTarget,
                appendOptional, law_15_1b_middle_KT,
                word_15_1b_middle_KT_left, word_15_1b_middle_KT_right,
                instantiateSevenWords, Word.bind, Word.append,
                Word.singleton, Word.append_assoc] using
                (substituteBasisLaw law_15_1b_middle_KT (by simp [basis])
                  (instantiateSevenWords x y x x x kContext tContext))
  | some hContext =>
      cases optionalK with
      | none =>
          cases optionalT with
          | none =>
              simpa [pattern15_1bSource, pattern15_1bMiddleTarget,
                appendOptional, law_15_1b_middle_H,
                word_15_1b_middle_H_left, word_15_1b_middle_H_right,
                instantiateSevenWords, Word.bind, Word.append,
                Word.singleton, Word.append_assoc] using
                (substituteBasisLaw law_15_1b_middle_H (by simp [basis])
                  (instantiateSevenWords x y x x hContext x x))
          | some tContext =>
              simpa [pattern15_1bSource, pattern15_1bMiddleTarget,
                appendOptional, law_15_1b_middle_HT,
                word_15_1b_middle_HT_left, word_15_1b_middle_HT_right,
                instantiateSevenWords, Word.bind, Word.append,
                Word.singleton, Word.append_assoc] using
                (substituteBasisLaw law_15_1b_middle_HT (by simp [basis])
                  (instantiateSevenWords x y x x hContext x tContext))
      | some kContext =>
          cases optionalT with
          | none =>
              simpa [pattern15_1bSource, pattern15_1bMiddleTarget,
                appendOptional, law_15_1b_middle_HK,
                word_15_1b_middle_HK_left, word_15_1b_middle_HK_right,
                instantiateSevenWords, Word.bind, Word.append,
                Word.singleton, Word.append_assoc] using
                (substituteBasisLaw law_15_1b_middle_HK (by simp [basis])
                  (instantiateSevenWords x y x x hContext kContext x))
          | some tContext =>
              simpa [pattern15_1bSource, pattern15_1bMiddleTarget,
                appendOptional, law_15_1b_middle_HKT,
                word_15_1b_middle_HKT_left,
                word_15_1b_middle_HKT_right, instantiateSevenWords,
                Word.bind, Word.append, Word.singleton,
                Word.append_assoc] using
                (substituteBasisLaw law_15_1b_middle_HKT (by simp [basis])
                  (instantiateSevenWords x y x x hContext kContext tContext))

/-- Substitution form of the right placement in (15.1b). -/
theorem derives15_1bRight
    (x y : Word Nat)
    (optionalH optionalK optionalT : Option (Word Nat)) :
    Derives basis
      (pattern15_1bSource x y optionalH optionalK optionalT)
      (pattern15_1bRightTarget x y optionalH optionalK optionalT) := by
  cases optionalH with
  | none =>
      cases optionalK with
      | none =>
          cases optionalT with
          | none =>
              simpa [pattern15_1bSource, pattern15_1bRightTarget,
                appendOptional, law_15_1b_right_empty,
                word_15_1b_right_empty_left,
                word_15_1b_right_empty_right, instantiateSevenWords,
                Word.bind, Word.append, Word.singleton,
                Word.append_assoc] using
                (substituteBasisLaw law_15_1b_right_empty (by simp [basis])
                  (instantiateSevenWords x y x x x x x))
          | some tContext =>
              simpa [pattern15_1bSource, pattern15_1bRightTarget,
                appendOptional, law_15_1b_right_T,
                word_15_1b_right_T_left, word_15_1b_right_T_right,
                instantiateSevenWords, Word.bind, Word.append,
                Word.singleton, Word.append_assoc] using
                (substituteBasisLaw law_15_1b_right_T (by simp [basis])
                  (instantiateSevenWords x y x x x x tContext))
      | some kContext =>
          cases optionalT with
          | none =>
              simpa [pattern15_1bSource, pattern15_1bRightTarget,
                appendOptional, law_15_1b_right_K,
                word_15_1b_right_K_left, word_15_1b_right_K_right,
                instantiateSevenWords, Word.bind, Word.append,
                Word.singleton, Word.append_assoc] using
                (substituteBasisLaw law_15_1b_right_K (by simp [basis])
                  (instantiateSevenWords x y x x x kContext x))
          | some tContext =>
              simpa [pattern15_1bSource, pattern15_1bRightTarget,
                appendOptional, law_15_1b_right_KT,
                word_15_1b_right_KT_left, word_15_1b_right_KT_right,
                instantiateSevenWords, Word.bind, Word.append,
                Word.singleton, Word.append_assoc] using
                (substituteBasisLaw law_15_1b_right_KT (by simp [basis])
                  (instantiateSevenWords x y x x x kContext tContext))
  | some hContext =>
      cases optionalK with
      | none =>
          cases optionalT with
          | none =>
              simpa [pattern15_1bSource, pattern15_1bRightTarget,
                appendOptional, law_15_1b_right_H,
                word_15_1b_right_H_left, word_15_1b_right_H_right,
                instantiateSevenWords, Word.bind, Word.append,
                Word.singleton, Word.append_assoc] using
                (substituteBasisLaw law_15_1b_right_H (by simp [basis])
                  (instantiateSevenWords x y x x hContext x x))
          | some tContext =>
              simpa [pattern15_1bSource, pattern15_1bRightTarget,
                appendOptional, law_15_1b_right_HT,
                word_15_1b_right_HT_left, word_15_1b_right_HT_right,
                instantiateSevenWords, Word.bind, Word.append,
                Word.singleton, Word.append_assoc] using
                (substituteBasisLaw law_15_1b_right_HT (by simp [basis])
                  (instantiateSevenWords x y x x hContext x tContext))
      | some kContext =>
          cases optionalT with
          | none =>
              simpa [pattern15_1bSource, pattern15_1bRightTarget,
                appendOptional, law_15_1b_right_HK,
                word_15_1b_right_HK_left, word_15_1b_right_HK_right,
                instantiateSevenWords, Word.bind, Word.append,
                Word.singleton, Word.append_assoc] using
                (substituteBasisLaw law_15_1b_right_HK (by simp [basis])
                  (instantiateSevenWords x y x x hContext kContext x))
          | some tContext =>
              simpa [pattern15_1bSource, pattern15_1bRightTarget,
                appendOptional, law_15_1b_right_HKT,
                word_15_1b_right_HKT_left, word_15_1b_right_HKT_right,
                instantiateSevenWords, Word.bind, Word.append,
                Word.singleton, Word.append_assoc] using
                (substituteBasisLaw law_15_1b_right_HKT (by simp [basis])
                  (instantiateSevenWords x y x x hContext kContext tContext))

/-- Substitution form of the left placement in (15.1c).  Paper `h` is an
ordinary word; only paper `K` is optional here. -/
theorem derives15_1cLeft
    (x y h : Word Nat) (optionalK : Option (Word Nat)) :
    Derives basis
      (pattern15_1cLeftSource x y h optionalK)
      (pattern15_1cLeftTarget x y h optionalK) := by
  cases optionalK with
  | none =>
      simpa [pattern15_1cLeftSource, pattern15_1cLeftTarget,
        appendOptional, law_15_1c_left_empty,
        word_15_1c_left_empty_left, word_15_1c_left_empty_right,
        instantiateSevenWords, Word.bind, Word.append, Word.singleton,
        Word.append_assoc] using
        (substituteBasisLaw law_15_1c_left_empty (by simp [basis])
          (instantiateSevenWords x y h x x x x))
  | some kContext =>
      simpa [pattern15_1cLeftSource, pattern15_1cLeftTarget,
        appendOptional, law_15_1c_left_K,
        word_15_1c_left_K_left, word_15_1c_left_K_right,
        instantiateSevenWords, Word.bind, Word.append, Word.singleton,
        Word.append_assoc] using
        (substituteBasisLaw law_15_1c_left_K (by simp [basis])
          (instantiateSevenWords x y h x x kContext x))

/-- Substitution form of the middle placement in (15.1c). -/
theorem derives15_1cMiddle
    (x y : Word Nat) (optionalH optionalK : Option (Word Nat)) :
    Derives basis
      (pattern15_1cMiddleSource x y optionalH optionalK)
      (pattern15_1cMiddleTarget x y optionalH optionalK) := by
  cases optionalH with
  | none =>
      cases optionalK with
      | none =>
          simpa [pattern15_1cMiddleSource, pattern15_1cMiddleTarget,
            appendOptional, law_15_1c_middle_empty,
            word_15_1c_middle_empty_left, word_15_1c_middle_empty_right,
            instantiateSevenWords, Word.bind, Word.append,
            Word.singleton, Word.append_assoc] using
            (substituteBasisLaw law_15_1c_middle_empty (by simp [basis])
              (instantiateSevenWords x y x x x x x))
      | some kContext =>
          simpa [pattern15_1cMiddleSource, pattern15_1cMiddleTarget,
            appendOptional, law_15_1c_middle_K,
            word_15_1c_middle_K_left, word_15_1c_middle_K_right,
            instantiateSevenWords, Word.bind, Word.append,
            Word.singleton, Word.append_assoc] using
            (substituteBasisLaw law_15_1c_middle_K (by simp [basis])
              (instantiateSevenWords x y x x x kContext x))
  | some hContext =>
      cases optionalK with
      | none =>
          simpa [pattern15_1cMiddleSource, pattern15_1cMiddleTarget,
            appendOptional, law_15_1c_middle_H,
            word_15_1c_middle_H_left, word_15_1c_middle_H_right,
            instantiateSevenWords, Word.bind, Word.append,
            Word.singleton, Word.append_assoc] using
            (substituteBasisLaw law_15_1c_middle_H (by simp [basis])
              (instantiateSevenWords x y x x hContext x x))
      | some kContext =>
          simpa [pattern15_1cMiddleSource, pattern15_1cMiddleTarget,
            appendOptional, law_15_1c_middle_HK,
            word_15_1c_middle_HK_left, word_15_1c_middle_HK_right,
            instantiateSevenWords, Word.bind, Word.append,
            Word.singleton, Word.append_assoc] using
            (substituteBasisLaw law_15_1c_middle_HK (by simp [basis])
              (instantiateSevenWords x y x x hContext kContext x))

/-- Substitution form of the right placement in (15.1c).  Paper `k` is an
ordinary word; only paper `H` is optional here. -/
theorem derives15_1cRight
    (x y k : Word Nat) (optionalH : Option (Word Nat)) :
    Derives basis
      (pattern15_1cRightSource x y k optionalH)
      (pattern15_1cRightTarget x y k optionalH) := by
  cases optionalH with
  | none =>
      simpa [pattern15_1cRightSource, pattern15_1cRightTarget,
        appendOptional, law_15_1c_right_empty,
        word_15_1c_right_empty_left, word_15_1c_right_empty_right,
        instantiateSevenWords, Word.bind, Word.append, Word.singleton,
        Word.append_assoc] using
        (substituteBasisLaw law_15_1c_right_empty (by simp [basis])
          (instantiateSevenWords x y x k x x x))
  | some hContext =>
      simpa [pattern15_1cRightSource, pattern15_1cRightTarget,
        appendOptional, law_15_1c_right_H,
        word_15_1c_right_H_left, word_15_1c_right_H_right,
        instantiateSevenWords, Word.bind, Word.append, Word.singleton,
        Word.append_assoc] using
        (substituteBasisLaw law_15_1c_right_H (by simp [basis])
          (instantiateSevenWords x y x k hContext x x))

/-- Substitution form of the left placement in (15.1d). -/
theorem derives15_1dLeft
    (x y k : Word Nat) (optionalH : Option (Word Nat)) :
    Derives basis
      (pattern15_1dLeftSource x y k optionalH)
      (pattern15_1dLeftTarget x y k optionalH) := by
  cases optionalH with
  | none =>
      simpa [pattern15_1dLeftSource, pattern15_1dLeftTarget,
        appendOptional, law_15_1d_left_empty,
        word_15_1d_left_empty_left, word_15_1d_left_empty_right,
        instantiateSevenWords, Word.bind, Word.append, Word.singleton,
        Word.append_assoc] using
        (substituteBasisLaw law_15_1d_left_empty (by simp [basis])
          (instantiateSevenWords x y x k x x x))
  | some hContext =>
      simpa [pattern15_1dLeftSource, pattern15_1dLeftTarget,
        appendOptional, law_15_1d_left_H,
        word_15_1d_left_H_left, word_15_1d_left_H_right,
        instantiateSevenWords, Word.bind, Word.append, Word.singleton,
        Word.append_assoc] using
        (substituteBasisLaw law_15_1d_left_H (by simp [basis])
          (instantiateSevenWords x y x k hContext x x))

/-- Substitution form of the middle placement in (15.1d). -/
theorem derives15_1dMiddle
    (x y : Word Nat) (optionalH optionalK : Option (Word Nat)) :
    Derives basis
      (pattern15_1dMiddleSource x y optionalH optionalK)
      (pattern15_1dMiddleTarget x y optionalH optionalK) := by
  cases optionalH with
  | none =>
      cases optionalK with
      | none =>
          simpa [pattern15_1dMiddleSource, pattern15_1dMiddleTarget,
            appendOptional, law_15_1d_middle_empty,
            word_15_1d_middle_empty_left, word_15_1d_middle_empty_right,
            instantiateSevenWords, Word.bind, Word.append,
            Word.singleton, Word.append_assoc] using
            (substituteBasisLaw law_15_1d_middle_empty (by simp [basis])
              (instantiateSevenWords x y x x x x x))
      | some kContext =>
          simpa [pattern15_1dMiddleSource, pattern15_1dMiddleTarget,
            appendOptional, law_15_1d_middle_K,
            word_15_1d_middle_K_left, word_15_1d_middle_K_right,
            instantiateSevenWords, Word.bind, Word.append,
            Word.singleton, Word.append_assoc] using
            (substituteBasisLaw law_15_1d_middle_K (by simp [basis])
              (instantiateSevenWords x y x x x kContext x))
  | some hContext =>
      cases optionalK with
      | none =>
          simpa [pattern15_1dMiddleSource, pattern15_1dMiddleTarget,
            appendOptional, law_15_1d_middle_H,
            word_15_1d_middle_H_left, word_15_1d_middle_H_right,
            instantiateSevenWords, Word.bind, Word.append,
            Word.singleton, Word.append_assoc] using
            (substituteBasisLaw law_15_1d_middle_H (by simp [basis])
              (instantiateSevenWords x y x x hContext x x))
      | some kContext =>
          simpa [pattern15_1dMiddleSource, pattern15_1dMiddleTarget,
            appendOptional, law_15_1d_middle_HK,
            word_15_1d_middle_HK_left, word_15_1d_middle_HK_right,
            instantiateSevenWords, Word.bind, Word.append,
            Word.singleton, Word.append_assoc] using
            (substituteBasisLaw law_15_1d_middle_HK (by simp [basis])
              (instantiateSevenWords x y x x hContext kContext x))

/-- Substitution form of the right placement in (15.1d). -/
theorem derives15_1dRight
    (x y h : Word Nat) (optionalK : Option (Word Nat)) :
    Derives basis
      (pattern15_1dRightSource x y h optionalK)
      (pattern15_1dRightTarget x y h optionalK) := by
  cases optionalK with
  | none =>
      simpa [pattern15_1dRightSource, pattern15_1dRightTarget,
        appendOptional, law_15_1d_right_empty,
        word_15_1d_right_empty_left, word_15_1d_right_empty_right,
        instantiateSevenWords, Word.bind, Word.append, Word.singleton,
        Word.append_assoc] using
        (substituteBasisLaw law_15_1d_right_empty (by simp [basis])
          (instantiateSevenWords x y h x x x x))
  | some kContext =>
      simpa [pattern15_1dRightSource, pattern15_1dRightTarget,
        appendOptional, law_15_1d_right_K,
        word_15_1d_right_K_left, word_15_1d_right_K_right,
        instantiateSevenWords, Word.bind, Word.append, Word.singleton,
        Word.append_assoc] using
        (substituteBasisLaw law_15_1d_right_K (by simp [basis])
          (instantiateSevenWords x y h x x kContext x))

/-- Substitution form of the forward placement in (15.1e). -/
theorem derives15_1eForward
    (x y h k : Word Nat) (optionalT : Option (Word Nat)) :
    Derives basis
      (pattern15_1eForwardSource x y h k optionalT)
      (pattern15_1eForwardTarget x y h k optionalT) := by
  cases optionalT with
  | none =>
      simpa [pattern15_1eForwardSource, pattern15_1eForwardTarget,
        appendOptional, law_15_1e_forward_empty,
        word_15_1e_forward_empty_left, word_15_1e_forward_empty_right,
        instantiateSevenWords, Word.bind, Word.append, Word.singleton,
        Word.append_assoc] using
        (substituteBasisLaw law_15_1e_forward_empty (by simp [basis])
          (instantiateSevenWords x y h k x x x))
  | some tContext =>
      simpa [pattern15_1eForwardSource, pattern15_1eForwardTarget,
        appendOptional, law_15_1e_forward_T,
        word_15_1e_forward_T_left, word_15_1e_forward_T_right,
        instantiateSevenWords, Word.bind, Word.append, Word.singleton,
        Word.append_assoc] using
        (substituteBasisLaw law_15_1e_forward_T (by simp [basis])
          (instantiateSevenWords x y h k x x tContext))

/-- Substitution form of the reverse placement in (15.1e). -/
theorem derives15_1eReverse
    (x y h k : Word Nat) (optionalT : Option (Word Nat)) :
    Derives basis
      (pattern15_1eReverseSource x y h k optionalT)
      (pattern15_1eReverseTarget x y h k optionalT) := by
  cases optionalT with
  | none =>
      simpa [pattern15_1eReverseSource, pattern15_1eReverseTarget,
        appendOptional, law_15_1e_reverse_empty,
        word_15_1e_reverse_empty_left, word_15_1e_reverse_empty_right,
        instantiateSevenWords, Word.bind, Word.append, Word.singleton,
        Word.append_assoc] using
        (substituteBasisLaw law_15_1e_reverse_empty (by simp [basis])
          (instantiateSevenWords x y h k x x x))
  | some tContext =>
      simpa [pattern15_1eReverseSource, pattern15_1eReverseTarget,
        appendOptional, law_15_1e_reverse_T,
        word_15_1e_reverse_T_left, word_15_1e_reverse_T_right,
        instantiateSevenWords, Word.bind, Word.append, Word.singleton,
        Word.append_assoc] using
        (substituteBasisLaw law_15_1e_reverse_T (by simp [basis])
          (instantiateSevenWords x y h k x x tContext))

/-- Substitution form of (15.1f). -/
theorem derives15_1f (x y h : Word Nat) :
    Derives basis (pattern15_1fLeft x y h) (pattern15_1fRight x y h) := by
  simpa [pattern15_1fLeft, pattern15_1fRight, law_15_1f,
    word_15_1f_left, word_15_1f_right, instantiateSevenWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
    (substituteBasisLaw law_15_1f (by simp [basis])
      (instantiateSevenWords x y h h h h h))

/-- All three placements of paper family (15.1a). -/
theorem derives15_1a
    (x : Word Nat) (optionalH optionalK : Option (Word Nat)) :
    Derives basis
        (pattern15_1aLeft x optionalH optionalK)
        (pattern15_1aCore x optionalH optionalK) ∧
      Derives basis
        (pattern15_1aMiddle x optionalH optionalK)
        (pattern15_1aCore x optionalH optionalK) ∧
      Derives basis
        (pattern15_1aRight x optionalH optionalK)
        (pattern15_1aCore x optionalH optionalK) :=
  ⟨derives15_1aLeft x optionalH optionalK,
    derives15_1aMiddle x optionalH optionalK,
    derives15_1aRight x optionalH optionalK⟩

/-- All three placements of paper family (15.1b). -/
theorem derives15_1b
    (x y : Word Nat)
    (optionalH optionalK optionalT : Option (Word Nat)) :
    Derives basis
        (pattern15_1bSource x y optionalH optionalK optionalT)
        (pattern15_1bLeftTarget x y optionalH optionalK optionalT) ∧
      Derives basis
        (pattern15_1bSource x y optionalH optionalK optionalT)
        (pattern15_1bMiddleTarget x y optionalH optionalK optionalT) ∧
      Derives basis
        (pattern15_1bSource x y optionalH optionalK optionalT)
        (pattern15_1bRightTarget x y optionalH optionalK optionalT) :=
  ⟨derives15_1bLeft x y optionalH optionalK optionalT,
    derives15_1bMiddle x y optionalH optionalK optionalT,
    derives15_1bRight x y optionalH optionalK optionalT⟩

/-- All three placements of paper family (15.1c). -/
theorem derives15_1c
    (x y h k : Word Nat) (optionalH optionalK : Option (Word Nat)) :
    Derives basis
        (pattern15_1cLeftSource x y h optionalK)
        (pattern15_1cLeftTarget x y h optionalK) ∧
      Derives basis
        (pattern15_1cMiddleSource x y optionalH optionalK)
        (pattern15_1cMiddleTarget x y optionalH optionalK) ∧
      Derives basis
        (pattern15_1cRightSource x y k optionalH)
        (pattern15_1cRightTarget x y k optionalH) :=
  ⟨derives15_1cLeft x y h optionalK,
    derives15_1cMiddle x y optionalH optionalK,
    derives15_1cRight x y k optionalH⟩

/-- All three placements of paper family (15.1d). -/
theorem derives15_1d
    (x y h k : Word Nat) (optionalH optionalK : Option (Word Nat)) :
    Derives basis
        (pattern15_1dLeftSource x y k optionalH)
        (pattern15_1dLeftTarget x y k optionalH) ∧
      Derives basis
        (pattern15_1dMiddleSource x y optionalH optionalK)
        (pattern15_1dMiddleTarget x y optionalH optionalK) ∧
      Derives basis
        (pattern15_1dRightSource x y h optionalK)
        (pattern15_1dRightTarget x y h optionalK) :=
  ⟨derives15_1dLeft x y k optionalH,
    derives15_1dMiddle x y optionalH optionalK,
    derives15_1dRight x y h optionalK⟩

/-- Both placements of paper family (15.1e). -/
theorem derives15_1e
    (x y h k : Word Nat) (optionalT : Option (Word Nat)) :
    Derives basis
        (pattern15_1eForwardSource x y h k optionalT)
        (pattern15_1eForwardTarget x y h k optionalT) ∧
      Derives basis
        (pattern15_1eReverseSource x y h k optionalT)
        (pattern15_1eReverseTarget x y h k optionalT) :=
  ⟨derives15_1eForward x y h k optionalT,
    derives15_1eReverse x y h k optionalT⟩

end SemigroupBasis.CoRoots.Order6SporadicSection15
