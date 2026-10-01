import SemigroupBasis.CoRoots.Order6D2D4SuffixTraceV2M2FSL
import SemigroupBasis.CoRoots.S5_107BlockCombinatorics

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6D2D4SuffixTrace.V2

open SemigroupBasis
open SemigroupBasis.CoRoots

abbrev SameFSS (left right : Word Nat) : Prop :=
  ∀ x y,
    S5_107.SimpleAdjacent left x y ↔
      S5_107.SimpleAdjacent right x y

def prependLetter (letter : Nat) (word : Word Nat) : Word Nat :=
  Word.singleton letter ++ word

@[simp] theorem prependLetter_toList (letter : Nat) (word : Word Nat) :
    (prependLetter letter word).toList = letter :: word.toList := by
  cases word
  rfl

/-- The paper prefix reduction, with the inherited simplicity of `y` stated
at the exact boundary where an FSL factor becomes an FSS factor. -/
theorem simpleAdjacent_iff_fsl_prepend
    (word : Word Nat) (x y : Nat)
    (ySimple : S5_107.SimpleIn word y) :
    S5_107.SimpleAdjacent word x y ↔
      SimpleLastFactor (prependLetter y word) x y := by
  constructor
  · rintro ⟨xSimple, _, adjacent⟩
    obtain ⟨before, after, split⟩ :=
      (S5_107.mem_adjacentPairs_iff_exists_split x y word).mp adjacent
    have different : x ≠ y := by
      intro equal
      subst y
      unfold S5_107.SimpleIn at xSimple
      rw [split] at xSimple
      simp only [List.count_append, List.count_cons] at xSimple
      simp at xSimple
      omega
    have yAfterZero : after.count y = 0 := by
      have equation := ySimple
      unfold S5_107.SimpleIn at equation
      rw [split] at equation
      simp only [List.count_append, List.count_cons] at equation
      simp [different] at equation
      omega
    have yFree : y ∉ after := List.count_eq_zero.mp yAfterZero
    refine ⟨?_, ?_, y :: before, after, ?_, yFree⟩
    · unfold S5_107.SimpleIn at xSimple ⊢
      rw [prependLetter_toList]
      simp [Ne.symm different, xSimple]
    · unfold S5_107.SimpleIn at ySimple
      rw [prependLetter_toList]
      simp [ySimple]
    · rw [prependLetter_toList, split]
      simp
  · rintro ⟨prefixedXSimple, _, before, after, split, _⟩
    have different : x ≠ y := by
      intro equal
      subst x
      unfold S5_107.SimpleIn at prefixedXSimple ySimple
      rw [prependLetter_toList] at prefixedXSimple
      simp [ySimple] at prefixedXSimple
    have xSimple : S5_107.SimpleIn word x := by
      unfold S5_107.SimpleIn at prefixedXSimple ⊢
      rw [prependLetter_toList] at prefixedXSimple
      simpa [Ne.symm different] using prefixedXSimple
    rw [prependLetter_toList] at split
    cases before with
    | nil =>
        simp only [List.nil_append] at split
        injection split with headEq _
        exact False.elim (different headEq.symm)
    | cons first rest =>
        simp only [List.cons_append] at split
        injection split with _ tailEq
        refine ⟨xSimple, ySimple, ?_⟩
        exact
          (S5_107.mem_adjacentPairs_iff_exists_split x y word).mpr
            ⟨rest, after, tailEq⟩

/-- If every common one-letter prefix preserves FSL, the original pair
preserves FSS.  M5 supplies these prefix FSL hypotheses from target validity. -/
theorem sameFSS_of_prefixFSL
    {left right : Word Nat}
    (base :
      S5_381Invariant.SameSimpleSequenceLastGapInitialSignature left right)
    (prefixFSL : ∀ letter,
      SameFSL (prependLetter letter left) (prependLetter letter right)) :
    SameFSS left right := by
  intro x y
  constructor
  · intro leftAdjacent
    have leftYSimple : S5_107.SimpleIn left y := leftAdjacent.2.1
    have rightYSimple : S5_107.SimpleIn right y :=
      (base.simple y).mp leftYSimple
    have leftFSL : SimpleLastFactor (prependLetter y left) x y :=
      (simpleAdjacent_iff_fsl_prepend left x y leftYSimple).mp
        leftAdjacent
    have rightFSL : SimpleLastFactor (prependLetter y right) x y :=
      (prefixFSL y x y).mp leftFSL
    exact
      (simpleAdjacent_iff_fsl_prepend right x y rightYSimple).mpr
        rightFSL
  · intro rightAdjacent
    have rightYSimple : S5_107.SimpleIn right y := rightAdjacent.2.1
    have leftYSimple : S5_107.SimpleIn left y :=
      (base.simple y).mpr rightYSimple
    have rightFSL : SimpleLastFactor (prependLetter y right) x y :=
      (simpleAdjacent_iff_fsl_prepend right x y rightYSimple).mp
        rightAdjacent
    have leftFSL : SimpleLastFactor (prependLetter y left) x y :=
      (prefixFSL y x y).mpr rightFSL
    exact
      (simpleAdjacent_iff_fsl_prepend left x y leftYSimple).mpr
        leftFSL

end SemigroupBasis.CoRoots.Order6D2D4SuffixTrace.V2
