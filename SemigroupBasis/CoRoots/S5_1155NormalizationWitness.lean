import SemigroupBasis.CoRoots.S5_1155Invariant
import SemigroupBasis.CoRoots.S5_1155Normalization

namespace SemigroupBasis.CoRoots.S5_1155

open SemigroupBasis
open SemigroupBasis.Examples

private theorem selected_mem_repeatedHeadRetargetTail
    (word : Word Nat) (selected : Nat)
    (headRepeated : 2 ≤ word.toList.count word.head) :
    selected ∈ repeatedHeadRetargetTail word selected := by
  by_cases same : word.head = selected
  · rw [repeatedHeadRetargetTail, if_pos same]
    subst selected
    cases word with
    | mk head tail =>
        simp only [Word.toList, Word.head, Word.tail] at headRepeated ⊢
        rw [List.count_cons_self] at headRepeated
        exact List.count_pos_iff.mp (by omega)
  · simp [repeatedHeadRetargetTail, same, retargetedTail]

/-- The explicit retarget normal form contains the selected head at least
twice. Tail reduction preserves the selected letter's support. -/
theorem repeatedHeadRetargetNormal_selected_count
    (word : Word Nat) (selected : Nat)
    (headRepeated : 2 ≤ word.toList.count word.head) :
    2 ≤
      (repeatedHeadRetargetNormal word selected).toList.count selected := by
  have selectedInReduced :
      selected ∈
        positiveModThreeReduce
          (repeatedHeadRetargetTail word selected) :=
    (mem_positiveModThreeReduce_iff selected _).2 <|
      selected_mem_repeatedHeadRetargetTail
        word selected headRepeated
  have reducedCountPositive :
      0 <
        (positiveModThreeReduce
          (repeatedHeadRetargetTail word selected)).count selected :=
    List.count_pos_iff.mpr selectedInReduced
  simp only [repeatedHeadRetargetNormal, toList_wordOfCons,
    List.count_cons_self]
  omega

/-- The explicit retarget normal form has the same exact semantic signature
as its source word. -/
theorem repeatedHeadRetargetNormal_sameSemanticSignature
    (word : Word Nat) (selected : Nat)
    (headRepeated : 2 ≤ word.toList.count word.head)
    (selectedSupported : selected ∈ word.toList) :
    SameSemanticSignature word
      (repeatedHeadRetargetNormal word selected) :=
  derives_sameSemanticSignature <|
    derivesRepeatedHeadRetarget
      word selected headRepeated selectedSupported

/-- All four fields required from the explicit repeated-head retarget normal
form, packaged with their exact target. -/
theorem repeatedHeadRetargetNormal_spec
    (word : Word Nat) (selected : Nat)
    (headRepeated : 2 ≤ word.toList.count word.head)
    (selectedSupported : selected ∈ word.toList) :
    (repeatedHeadRetargetNormal word selected).head = selected ∧
      2 ≤
        (repeatedHeadRetargetNormal word selected).toList.count selected ∧
      SameSemanticSignature word
        (repeatedHeadRetargetNormal word selected) ∧
      Derives basis word
        (repeatedHeadRetargetNormal word selected) := by
  exact
    ⟨repeatedHeadRetargetNormal_head word selected,
      repeatedHeadRetargetNormal_selected_count
        word selected headRepeated,
      repeatedHeadRetargetNormal_sameSemanticSignature
        word selected headRepeated selectedSupported,
      derivesRepeatedHeadRetarget
        word selected headRepeated selectedSupported⟩

/-- The explicit retarget normal form discharges the declared repeated-head
normalization obligation. -/
theorem repeatedHeadNormalization :
    RepeatedHeadNormalizationObligation where
  retarget word selected headRepeated selectedSupported :=
    ⟨repeatedHeadRetargetNormal word selected,
      repeatedHeadRetargetNormal_spec
        word selected headRepeated selectedSupported⟩

end SemigroupBasis.CoRoots.S5_1155
