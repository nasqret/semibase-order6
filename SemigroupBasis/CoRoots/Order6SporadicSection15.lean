import SemigroupBasis.FiniteReflection
import SemigroupBasis.Generated.S3_6
import SemigroupBasis.Generated.S4_40
import SemigroupBasis.Opposite

/-! Lightweight laws, basis, and generic completeness interface for Section 15. -/

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6SporadicSection15

open SemigroupBasis

@[simp]
private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def word_15_1a_left_empty_left : Word Nat := w 0 [0, 0, 0]
def word_15_1a_left_empty_right : Word Nat := w 0 [0, 0]
def law_15_1a_left_empty : Identity Nat := ⟨word_15_1a_left_empty_left, word_15_1a_left_empty_right⟩
def word_15_1a_left_H_left : Word Nat := w 0 [0, 4, 0, 0]
def word_15_1a_left_H_right : Word Nat := w 0 [4, 0, 0]
def law_15_1a_left_H : Identity Nat := ⟨word_15_1a_left_H_left, word_15_1a_left_H_right⟩
def word_15_1a_left_K_left : Word Nat := w 0 [0, 0, 5, 0]
def word_15_1a_left_K_right : Word Nat := w 0 [0, 5, 0]
def law_15_1a_left_K : Identity Nat := ⟨word_15_1a_left_K_left, word_15_1a_left_K_right⟩
def word_15_1a_left_HK_left : Word Nat := w 0 [0, 4, 0, 5, 0]
def word_15_1a_left_HK_right : Word Nat := w 0 [4, 0, 5, 0]
def law_15_1a_left_HK : Identity Nat := ⟨word_15_1a_left_HK_left, word_15_1a_left_HK_right⟩
def word_15_1a_middle_empty_left : Word Nat := w 0 [0, 0, 0]
def word_15_1a_middle_empty_right : Word Nat := w 0 [0, 0]
def law_15_1a_middle_empty : Identity Nat := ⟨word_15_1a_middle_empty_left, word_15_1a_middle_empty_right⟩
def word_15_1a_middle_H_left : Word Nat := w 0 [4, 0, 0, 0]
def word_15_1a_middle_H_right : Word Nat := w 0 [4, 0, 0]
def law_15_1a_middle_H : Identity Nat := ⟨word_15_1a_middle_H_left, word_15_1a_middle_H_right⟩
def word_15_1a_middle_K_left : Word Nat := w 0 [0, 0, 5, 0]
def word_15_1a_middle_K_right : Word Nat := w 0 [0, 5, 0]
def law_15_1a_middle_K : Identity Nat := ⟨word_15_1a_middle_K_left, word_15_1a_middle_K_right⟩
def word_15_1a_middle_HK_left : Word Nat := w 0 [4, 0, 0, 5, 0]
def word_15_1a_middle_HK_right : Word Nat := w 0 [4, 0, 5, 0]
def law_15_1a_middle_HK : Identity Nat := ⟨word_15_1a_middle_HK_left, word_15_1a_middle_HK_right⟩
def word_15_1a_right_empty_left : Word Nat := w 0 [0, 0, 0]
def word_15_1a_right_empty_right : Word Nat := w 0 [0, 0]
def law_15_1a_right_empty : Identity Nat := ⟨word_15_1a_right_empty_left, word_15_1a_right_empty_right⟩
def word_15_1a_right_H_left : Word Nat := w 0 [4, 0, 0, 0]
def word_15_1a_right_H_right : Word Nat := w 0 [4, 0, 0]
def law_15_1a_right_H : Identity Nat := ⟨word_15_1a_right_H_left, word_15_1a_right_H_right⟩
def word_15_1a_right_K_left : Word Nat := w 0 [0, 5, 0, 0]
def word_15_1a_right_K_right : Word Nat := w 0 [0, 5, 0]
def law_15_1a_right_K : Identity Nat := ⟨word_15_1a_right_K_left, word_15_1a_right_K_right⟩
def word_15_1a_right_HK_left : Word Nat := w 0 [4, 0, 5, 0, 0]
def word_15_1a_right_HK_right : Word Nat := w 0 [4, 0, 5, 0]
def law_15_1a_right_HK : Identity Nat := ⟨word_15_1a_right_HK_left, word_15_1a_right_HK_right⟩
def word_15_1b_left_empty_left : Word Nat := w 0 [1, 0, 1]
def word_15_1b_left_empty_right : Word Nat := w 1 [0, 0, 1]
def law_15_1b_left_empty : Identity Nat := ⟨word_15_1b_left_empty_left, word_15_1b_left_empty_right⟩
def word_15_1b_left_H_left : Word Nat := w 0 [4, 1, 0, 1]
def word_15_1b_left_H_right : Word Nat := w 1 [4, 0, 0, 1]
def law_15_1b_left_H : Identity Nat := ⟨word_15_1b_left_H_left, word_15_1b_left_H_right⟩
def word_15_1b_left_K_left : Word Nat := w 0 [1, 5, 0, 1]
def word_15_1b_left_K_right : Word Nat := w 1 [0, 5, 0, 1]
def law_15_1b_left_K : Identity Nat := ⟨word_15_1b_left_K_left, word_15_1b_left_K_right⟩
def word_15_1b_left_HK_left : Word Nat := w 0 [4, 1, 5, 0, 1]
def word_15_1b_left_HK_right : Word Nat := w 1 [4, 0, 5, 0, 1]
def law_15_1b_left_HK : Identity Nat := ⟨word_15_1b_left_HK_left, word_15_1b_left_HK_right⟩
def word_15_1b_left_T_left : Word Nat := w 0 [1, 0, 6, 1]
def word_15_1b_left_T_right : Word Nat := w 1 [0, 0, 6, 1]
def law_15_1b_left_T : Identity Nat := ⟨word_15_1b_left_T_left, word_15_1b_left_T_right⟩
def word_15_1b_left_HT_left : Word Nat := w 0 [4, 1, 0, 6, 1]
def word_15_1b_left_HT_right : Word Nat := w 1 [4, 0, 0, 6, 1]
def law_15_1b_left_HT : Identity Nat := ⟨word_15_1b_left_HT_left, word_15_1b_left_HT_right⟩
def word_15_1b_left_KT_left : Word Nat := w 0 [1, 5, 0, 6, 1]
def word_15_1b_left_KT_right : Word Nat := w 1 [0, 5, 0, 6, 1]
def law_15_1b_left_KT : Identity Nat := ⟨word_15_1b_left_KT_left, word_15_1b_left_KT_right⟩
def word_15_1b_left_HKT_left : Word Nat := w 0 [4, 1, 5, 0, 6, 1]
def word_15_1b_left_HKT_right : Word Nat := w 1 [4, 0, 5, 0, 6, 1]
def law_15_1b_left_HKT : Identity Nat := ⟨word_15_1b_left_HKT_left, word_15_1b_left_HKT_right⟩
def word_15_1b_middle_empty_left : Word Nat := w 0 [1, 0, 1]
def word_15_1b_middle_empty_right : Word Nat := w 0 [0, 1, 1]
def law_15_1b_middle_empty : Identity Nat := ⟨word_15_1b_middle_empty_left, word_15_1b_middle_empty_right⟩
def word_15_1b_middle_H_left : Word Nat := w 0 [4, 1, 0, 1]
def word_15_1b_middle_H_right : Word Nat := w 0 [4, 0, 1, 1]
def law_15_1b_middle_H : Identity Nat := ⟨word_15_1b_middle_H_left, word_15_1b_middle_H_right⟩
def word_15_1b_middle_K_left : Word Nat := w 0 [1, 5, 0, 1]
def word_15_1b_middle_K_right : Word Nat := w 0 [0, 5, 1, 1]
def law_15_1b_middle_K : Identity Nat := ⟨word_15_1b_middle_K_left, word_15_1b_middle_K_right⟩
def word_15_1b_middle_HK_left : Word Nat := w 0 [4, 1, 5, 0, 1]
def word_15_1b_middle_HK_right : Word Nat := w 0 [4, 0, 5, 1, 1]
def law_15_1b_middle_HK : Identity Nat := ⟨word_15_1b_middle_HK_left, word_15_1b_middle_HK_right⟩
def word_15_1b_middle_T_left : Word Nat := w 0 [1, 0, 6, 1]
def word_15_1b_middle_T_right : Word Nat := w 0 [0, 1, 6, 1]
def law_15_1b_middle_T : Identity Nat := ⟨word_15_1b_middle_T_left, word_15_1b_middle_T_right⟩
def word_15_1b_middle_HT_left : Word Nat := w 0 [4, 1, 0, 6, 1]
def word_15_1b_middle_HT_right : Word Nat := w 0 [4, 0, 1, 6, 1]
def law_15_1b_middle_HT : Identity Nat := ⟨word_15_1b_middle_HT_left, word_15_1b_middle_HT_right⟩
def word_15_1b_middle_KT_left : Word Nat := w 0 [1, 5, 0, 6, 1]
def word_15_1b_middle_KT_right : Word Nat := w 0 [0, 5, 1, 6, 1]
def law_15_1b_middle_KT : Identity Nat := ⟨word_15_1b_middle_KT_left, word_15_1b_middle_KT_right⟩
def word_15_1b_middle_HKT_left : Word Nat := w 0 [4, 1, 5, 0, 6, 1]
def word_15_1b_middle_HKT_right : Word Nat := w 0 [4, 0, 5, 1, 6, 1]
def law_15_1b_middle_HKT : Identity Nat := ⟨word_15_1b_middle_HKT_left, word_15_1b_middle_HKT_right⟩
def word_15_1b_right_empty_left : Word Nat := w 0 [1, 0, 1]
def word_15_1b_right_empty_right : Word Nat := w 0 [1, 1, 0]
def law_15_1b_right_empty : Identity Nat := ⟨word_15_1b_right_empty_left, word_15_1b_right_empty_right⟩
def word_15_1b_right_H_left : Word Nat := w 0 [4, 1, 0, 1]
def word_15_1b_right_H_right : Word Nat := w 0 [4, 1, 1, 0]
def law_15_1b_right_H : Identity Nat := ⟨word_15_1b_right_H_left, word_15_1b_right_H_right⟩
def word_15_1b_right_K_left : Word Nat := w 0 [1, 5, 0, 1]
def word_15_1b_right_K_right : Word Nat := w 0 [1, 5, 1, 0]
def law_15_1b_right_K : Identity Nat := ⟨word_15_1b_right_K_left, word_15_1b_right_K_right⟩
def word_15_1b_right_HK_left : Word Nat := w 0 [4, 1, 5, 0, 1]
def word_15_1b_right_HK_right : Word Nat := w 0 [4, 1, 5, 1, 0]
def law_15_1b_right_HK : Identity Nat := ⟨word_15_1b_right_HK_left, word_15_1b_right_HK_right⟩
def word_15_1b_right_T_left : Word Nat := w 0 [1, 0, 6, 1]
def word_15_1b_right_T_right : Word Nat := w 0 [1, 1, 6, 0]
def law_15_1b_right_T : Identity Nat := ⟨word_15_1b_right_T_left, word_15_1b_right_T_right⟩
def word_15_1b_right_HT_left : Word Nat := w 0 [4, 1, 0, 6, 1]
def word_15_1b_right_HT_right : Word Nat := w 0 [4, 1, 1, 6, 0]
def law_15_1b_right_HT : Identity Nat := ⟨word_15_1b_right_HT_left, word_15_1b_right_HT_right⟩
def word_15_1b_right_KT_left : Word Nat := w 0 [1, 5, 0, 6, 1]
def word_15_1b_right_KT_right : Word Nat := w 0 [1, 5, 1, 6, 0]
def law_15_1b_right_KT : Identity Nat := ⟨word_15_1b_right_KT_left, word_15_1b_right_KT_right⟩
def word_15_1b_right_HKT_left : Word Nat := w 0 [4, 1, 5, 0, 6, 1]
def word_15_1b_right_HKT_right : Word Nat := w 0 [4, 1, 5, 1, 6, 0]
def law_15_1b_right_HKT : Identity Nat := ⟨word_15_1b_right_HKT_left, word_15_1b_right_HKT_right⟩
def word_15_1c_left_empty_left : Word Nat := w 0 [0, 2, 1, 1]
def word_15_1c_left_empty_right : Word Nat := w 0 [2, 0, 1, 1]
def law_15_1c_left_empty : Identity Nat := ⟨word_15_1c_left_empty_left, word_15_1c_left_empty_right⟩
def word_15_1c_left_K_left : Word Nat := w 0 [0, 2, 1, 5, 1]
def word_15_1c_left_K_right : Word Nat := w 0 [2, 0, 1, 5, 1]
def law_15_1c_left_K : Identity Nat := ⟨word_15_1c_left_K_left, word_15_1c_left_K_right⟩
def word_15_1c_middle_empty_left : Word Nat := w 0 [0, 1, 1]
def word_15_1c_middle_empty_right : Word Nat := w 0 [1, 0, 1]
def law_15_1c_middle_empty : Identity Nat := ⟨word_15_1c_middle_empty_left, word_15_1c_middle_empty_right⟩
def word_15_1c_middle_H_left : Word Nat := w 0 [0, 4, 1, 1]
def word_15_1c_middle_H_right : Word Nat := w 0 [4, 1, 0, 1]
def law_15_1c_middle_H : Identity Nat := ⟨word_15_1c_middle_H_left, word_15_1c_middle_H_right⟩
def word_15_1c_middle_K_left : Word Nat := w 0 [0, 1, 5, 1]
def word_15_1c_middle_K_right : Word Nat := w 0 [1, 5, 0, 1]
def law_15_1c_middle_K : Identity Nat := ⟨word_15_1c_middle_K_left, word_15_1c_middle_K_right⟩
def word_15_1c_middle_HK_left : Word Nat := w 0 [0, 4, 1, 5, 1]
def word_15_1c_middle_HK_right : Word Nat := w 0 [4, 1, 5, 0, 1]
def law_15_1c_middle_HK : Identity Nat := ⟨word_15_1c_middle_HK_left, word_15_1c_middle_HK_right⟩
def word_15_1c_right_empty_left : Word Nat := w 1 [0, 0, 3, 1]
def word_15_1c_right_empty_right : Word Nat := w 1 [0, 3, 0, 1]
def law_15_1c_right_empty : Identity Nat := ⟨word_15_1c_right_empty_left, word_15_1c_right_empty_right⟩
def word_15_1c_right_H_left : Word Nat := w 1 [4, 0, 0, 3, 1]
def word_15_1c_right_H_right : Word Nat := w 1 [4, 0, 3, 0, 1]
def law_15_1c_right_H : Identity Nat := ⟨word_15_1c_right_H_left, word_15_1c_right_H_right⟩
def word_15_1d_left_empty_left : Word Nat := w 0 [0, 3, 1, 1]
def word_15_1d_left_empty_right : Word Nat := w 0 [0, 1, 3, 1]
def law_15_1d_left_empty : Identity Nat := ⟨word_15_1d_left_empty_left, word_15_1d_left_empty_right⟩
def word_15_1d_left_H_left : Word Nat := w 0 [4, 0, 3, 1, 1]
def word_15_1d_left_H_right : Word Nat := w 0 [4, 0, 1, 3, 1]
def law_15_1d_left_H : Identity Nat := ⟨word_15_1d_left_H_left, word_15_1d_left_H_right⟩
def word_15_1d_middle_empty_left : Word Nat := w 0 [0, 1, 1]
def word_15_1d_middle_empty_right : Word Nat := w 0 [1, 0, 1]
def law_15_1d_middle_empty : Identity Nat := ⟨word_15_1d_middle_empty_left, word_15_1d_middle_empty_right⟩
def word_15_1d_middle_H_left : Word Nat := w 0 [4, 0, 1, 1]
def word_15_1d_middle_H_right : Word Nat := w 0 [1, 4, 0, 1]
def law_15_1d_middle_H : Identity Nat := ⟨word_15_1d_middle_H_left, word_15_1d_middle_H_right⟩
def word_15_1d_middle_K_left : Word Nat := w 0 [0, 5, 1, 1]
def word_15_1d_middle_K_right : Word Nat := w 0 [1, 0, 5, 1]
def law_15_1d_middle_K : Identity Nat := ⟨word_15_1d_middle_K_left, word_15_1d_middle_K_right⟩
def word_15_1d_middle_HK_left : Word Nat := w 0 [4, 0, 5, 1, 1]
def word_15_1d_middle_HK_right : Word Nat := w 0 [1, 4, 0, 5, 1]
def law_15_1d_middle_HK : Identity Nat := ⟨word_15_1d_middle_HK_left, word_15_1d_middle_HK_right⟩
def word_15_1d_right_empty_left : Word Nat := w 0 [2, 1, 1, 0]
def word_15_1d_right_empty_right : Word Nat := w 0 [1, 2, 1, 0]
def law_15_1d_right_empty : Identity Nat := ⟨word_15_1d_right_empty_left, word_15_1d_right_empty_right⟩
def word_15_1d_right_K_left : Word Nat := w 0 [2, 1, 1, 5, 0]
def word_15_1d_right_K_right : Word Nat := w 0 [1, 2, 1, 5, 0]
def law_15_1d_right_K : Identity Nat := ⟨word_15_1d_right_K_left, word_15_1d_right_K_right⟩
def word_15_1e_forward_empty_left : Word Nat := w 2 [0, 2, 1, 3, 3]
def word_15_1e_forward_empty_right : Word Nat := w 2 [1, 2, 0, 3, 3]
def law_15_1e_forward_empty : Identity Nat := ⟨word_15_1e_forward_empty_left, word_15_1e_forward_empty_right⟩
def word_15_1e_forward_T_left : Word Nat := w 2 [0, 2, 1, 3, 6, 3]
def word_15_1e_forward_T_right : Word Nat := w 2 [1, 2, 0, 3, 6, 3]
def law_15_1e_forward_T : Identity Nat := ⟨word_15_1e_forward_T_left, word_15_1e_forward_T_right⟩
def word_15_1e_reverse_empty_left : Word Nat := w 3 [3, 0, 2, 1, 2]
def word_15_1e_reverse_empty_right : Word Nat := w 3 [3, 1, 2, 0, 2]
def law_15_1e_reverse_empty : Identity Nat := ⟨word_15_1e_reverse_empty_left, word_15_1e_reverse_empty_right⟩
def word_15_1e_reverse_T_left : Word Nat := w 3 [6, 3, 0, 2, 1, 2]
def word_15_1e_reverse_T_right : Word Nat := w 3 [6, 3, 1, 2, 0, 2]
def law_15_1e_reverse_T : Identity Nat := ⟨word_15_1e_reverse_T_left, word_15_1e_reverse_T_right⟩
def word_15_1f_left : Word Nat := w 2 [0, 2, 1, 2]
def word_15_1f_right : Word Nat := w 2 [1, 2, 0, 2]
def law_15_1f : Identity Nat := ⟨word_15_1f_left, word_15_1f_right⟩

/-- The 57 ordinary instances of the optional-context systems (15.1). -/
def basis : List (Identity Nat) :=
  [law_15_1a_left_empty, law_15_1a_left_H, law_15_1a_left_K, law_15_1a_left_HK, law_15_1a_middle_empty, law_15_1a_middle_H, law_15_1a_middle_K, law_15_1a_middle_HK, law_15_1a_right_empty, law_15_1a_right_H, law_15_1a_right_K, law_15_1a_right_HK, law_15_1b_left_empty, law_15_1b_left_H, law_15_1b_left_K, law_15_1b_left_HK, law_15_1b_left_T, law_15_1b_left_HT, law_15_1b_left_KT, law_15_1b_left_HKT, law_15_1b_middle_empty, law_15_1b_middle_H, law_15_1b_middle_K, law_15_1b_middle_HK, law_15_1b_middle_T, law_15_1b_middle_HT, law_15_1b_middle_KT, law_15_1b_middle_HKT, law_15_1b_right_empty, law_15_1b_right_H, law_15_1b_right_K, law_15_1b_right_HK, law_15_1b_right_T, law_15_1b_right_HT, law_15_1b_right_KT, law_15_1b_right_HKT, law_15_1c_left_empty, law_15_1c_left_K, law_15_1c_middle_empty, law_15_1c_middle_H, law_15_1c_middle_K, law_15_1c_middle_HK, law_15_1c_right_empty, law_15_1c_right_H, law_15_1d_left_empty, law_15_1d_left_H, law_15_1d_middle_empty, law_15_1d_middle_H, law_15_1d_middle_K, law_15_1d_middle_HK, law_15_1d_right_empty, law_15_1d_right_K, law_15_1e_forward_empty, law_15_1e_forward_T, law_15_1e_reverse_empty, law_15_1e_reverse_T, law_15_1f]

def oppositeBasis : List (Identity Nat) :=
  reversedBasis basis

/-- The identity excluded in Lemma 15.2(iv), with variables x=0,y=1,z=2. -/
def fssExclusionIdentity : Identity Nat :=
  ⟨w 0 [0, 0, 1, 0, 0, 0, 2, 0, 0, 0],
    w 0 [0, 0, 1, 2, 0, 0, 0]⟩

/-- The finite multiplication equations used by the generic directed-simple-
adjacency detector. The argument order follows the states 0,1,target,source,
other from the certificate replay. -/
structure DirectedSimpleAdjacencyLaws {S : Type u}
    (candidate : Semigroup S)
    (zero one target source other : S) : Prop where
  zero_ne_one : zero ≠ one
  other_other : candidate.mul other other = other
  other_source : candidate.mul other source = source
  source_target : candidate.mul source target = one
  one_other : candidate.mul one other = one
  zero_other : candidate.mul zero other = zero
  target_other : candidate.mul target other = target
  target_source : candidate.mul target source = zero
  source_other_other :
    candidate.mul (candidate.mul source other) other =
      candidate.mul source other
  source_other_target :
    candidate.mul (candidate.mul source other) target = zero
  other_target_other :
    candidate.mul (candidate.mul other target) other =
      candidate.mul other target
  other_target_source :
    candidate.mul (candidate.mul other target) source = zero

private def toFinSeven : Nat → Fin 7
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | _ => 6

def finiteBasis : List (Identity (Fin 7)) :=
  basis.map fun identity => identity.map toFinSeven

def finiteOppositeBasis : List (Identity (Fin 7)) :=
  oppositeBasis.map fun identity => identity.map toFinSeven

private theorem basis_roundTrip_checked :
    basis.all (fun identity =>
      decide ((identity.map toFinSeven).map Fin.val = identity)) = true := by
  decide

private theorem oppositeBasis_roundTrip_checked :
    oppositeBasis.all (fun identity =>
      decide ((identity.map toFinSeven).map Fin.val = identity)) = true := by
  decide

private theorem basis_roundTrip
    (identity : Identity Nat) (member : identity ∈ basis) :
    (identity.map toFinSeven).map Fin.val = identity := by
  exact of_decide_eq_true <|
    (List.all_eq_true.mp basis_roundTrip_checked) identity member

private theorem oppositeBasis_roundTrip
    (identity : Identity Nat) (member : identity ∈ oppositeBasis) :
    (identity.map toFinSeven).map Fin.val = identity := by
  exact of_decide_eq_true <|
    (List.all_eq_true.mp oppositeBasis_roundTrip_checked) identity member

/-- Exhaustive finite checks establish soundness of the displayed system. -/
theorem models_of_finite_checks
    (candidate : FiniteTable)
    (checked : finiteBasis.all candidate.checkIdentity = true) :
    Models candidate.semigroup basis := by
  intro identity member
  have finiteMember : identity.map toFinSeven ∈ finiteBasis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    candidate.checkIdentityNat_sound (identity.map toFinSeven)
      ((List.all_eq_true.mp checked) _ finiteMember)
  rw [basis_roundTrip identity member] at finiteValid
  exact finiteValid

theorem modelsOpposite_of_finite_checks
    (candidate : FiniteTable)
    (checked : finiteOppositeBasis.all candidate.checkIdentity = true) :
    Models candidate.semigroup oppositeBasis := by
  intro identity member
  have finiteMember : identity.map toFinSeven ∈ finiteOppositeBasis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    candidate.checkIdentityNat_sound (identity.map toFinSeven)
      ((List.all_eq_true.mp checked) _ finiteMember)
  rw [oppositeBasis_roundTrip identity member] at finiteValid
  exact finiteValid

/-- The unrestricted canonical-form content of Proposition 15.1.  Candidate
validity remains explicit because Lemma 15.2(iv) uses the target-specific FSS
exclusion in addition to the three divisor consequences. -/
structure Completeness {S : Type u} (candidate : Semigroup S) : Prop where
  derives :
    ∀ identity : Identity Nat,
      identity.SatisfiedBy candidate →
      identity.SatisfiedBy Generated.S4_40.table.semigroup →
      identity.SatisfiedBy Generated.S3_6.table.semigroup →
      identity.SatisfiedBy Generated.S3_6.table.semigroup.opposite →
      Derives basis identity.lhs identity.rhs

theorem basisFor_of_completeness
    {S : Type u} (candidate : Semigroup S)
    (models : Models candidate basis)
    (validCount :
      ∀ identity : Identity Nat,
        identity.SatisfiedBy candidate →
        identity.SatisfiedBy Generated.S4_40.table.semigroup)
    (validFinal :
      ∀ identity : Identity Nat,
        identity.SatisfiedBy candidate →
        identity.SatisfiedBy Generated.S3_6.table.semigroup)
    (validInitial :
      ∀ identity : Identity Nat,
        identity.SatisfiedBy candidate →
        identity.SatisfiedBy Generated.S3_6.table.semigroup.opposite)
    (completion : Completeness candidate) :
    BasisFor candidate basis := by
  refine ⟨models, ?_⟩
  intro identity valid
  exact completion.derives identity valid
    (validCount identity valid)
    (validFinal identity valid)
    (validInitial identity valid)

end SemigroupBasis.CoRoots.Order6SporadicSection15
