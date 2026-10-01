import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0468PrefixComparison
import SemigroupBasis.Opposite

/-! Exact simple-separator prefix data and globally repeated-letter swaps.
All lists, alphabets and contexts are unrestricted. A concrete basis must
prove the GlobalSwaps capability; it is not supplied by this definition. -/

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.SimplePrefix

open SemigroupBasis PrefixCount

structure ExactSignature (left right : List Nat) : Prop where
  counts : ∀ tested, left.count tested = right.count tested
  prefixes : ∀ separator, left.count separator = 1 → ∀ tested,
    (before separator left).count tested = (before separator right).count tested

theorem ExactSignature.refl (letters : List Nat) : ExactSignature letters letters :=
  ⟨fun _ => rfl, fun _ _ _ => rfl⟩

theorem ExactSignature.symm {left right : List Nat} (same : ExactSignature left right) :
    ExactSignature right left := by
  refine ⟨fun tested => (same.counts tested).symm, ?_⟩
  intro separator one tested
  exact (same.prefixes separator ((same.counts separator).trans one) tested).symm

theorem ExactSignature.trans {left middle right : List Nat}
    (first : ExactSignature left middle) (second : ExactSignature middle right) :
    ExactSignature left right := by
  refine ⟨fun tested => (first.counts tested).trans (second.counts tested), ?_⟩
  intro separator one tested
  exact (first.prefixes separator one tested).trans
    (second.prefixes separator ((first.counts separator).symm.trans one) tested)

theorem before_count_le (separator tested : Nat) (letters : List Nat) :
    (before separator letters).count tested ≤ letters.count tested := by
  induction letters with
  | nil => simp [before]
  | cons head tail induction =>
      by_cases equal : head = separator
      · simp [before, equal]
      · simp only [before_cons_of_ne separator head tail equal, List.count_cons]
        omega

def GlobalSwaps (basis : List (Identity Nat)) : Prop :=
  ∀ (prefixWords : List Nat) (left right : Nat) (suffix : List Nat),
    2 ≤ (prefixWords ++ left :: right :: suffix).count left →
    2 ≤ (prefixWords ++ left :: right :: suffix).count right →
      S5_107.ListDerives basis (prefixWords ++ left :: right :: suffix)
        (prefixWords ++ right :: left :: suffix)

theorem swap_signature (prefixWords : List Nat) (left right : Nat) (suffix : List Nat)
    (leftHeavy : 2 ≤ (prefixWords ++ left :: right :: suffix).count left)
    (rightHeavy : 2 ≤ (prefixWords ++ left :: right :: suffix).count right) :
    ExactSignature (prefixWords ++ left :: right :: suffix)
      (prefixWords ++ right :: left :: suffix) := by
  refine ⟨?_, ?_⟩
  · intro tested
    simp only [List.count_append, List.count_cons]
    omega
  · intro separator one tested
    have leftNe : left ≠ separator := by
      intro equal
      subst separator
      omega
    have rightNe : right ≠ separator := by
      intro equal
      subst separator
      omega
    by_cases seen : separator ∈ prefixWords
    · rw [before_append_of_mem separator prefixWords _ seen,
        before_append_of_mem separator prefixWords _ seen]
    · simp only [before_append_of_not_mem separator prefixWords _ seen,
        before_cons_of_ne separator left _ leftNe, before_cons_of_ne separator right _ rightNe,
        List.count_append, List.count_cons]
      omega

theorem reverse_listDerives {basis : List (Identity Nat)} {left right : List Nat}
    (derivation : S5_107.ListDerives basis left right) :
    S5_107.ListDerives (reversedBasis basis) left.reverse right.reverse := by
  cases derivation with
  | empty => exact S5_107.ListDerives.empty
  | words wordDerivation =>
      have reversed := S5_107.ListDerives.ofWord wordDerivation.reverse
      simpa only [Word.toList_reverse] using reversed

theorem GlobalSwaps.reversed {basis : List (Identity Nat)} (swaps : GlobalSwaps basis) :
    GlobalSwaps (reversedBasis basis) := by
  intro prefixWords left right suffix leftHeavy rightHeavy
  have rightHeavy' : 2 ≤ (suffix.reverse ++ right :: left :: prefixWords.reverse).count right := by
    simp only [List.count_append, List.count_cons, List.count_reverse] at rightHeavy ⊢
    omega
  have leftHeavy' : 2 ≤ (suffix.reverse ++ right :: left :: prefixWords.reverse).count left := by
    simp only [List.count_append, List.count_cons, List.count_reverse] at leftHeavy ⊢
    omega
  have reversed := reverse_listDerives (swaps suffix.reverse right left prefixWords.reverse rightHeavy' leftHeavy')
  simpa [List.reverse_append, List.reverse_cons, List.append_assoc] using reversed

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.SimplePrefix
