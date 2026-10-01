import SemigroupBasis.Word

namespace SemigroupBasis.CoRoots.S5_415

open SemigroupBasis

/-- Proof-relevant evidence that a chosen occurrence of `tested` lies in a
contiguous cell `y p y` of `word`.  The lists `prefix` and `suffix` retain the
ambient context, while `p` retains the inside of the cell. -/
structure CellContains {alpha : Type} (word : Word alpha)
    (tested : alpha) : Type where
  y : alpha
  leadingContext : List alpha
  p : List alpha
  suffix : List alpha
  factorization :
    word.toList = leadingContext ++ y :: (p ++ y :: suffix)
  tested_mem : tested ∈ y :: (p ++ [y])

/-- A word is repeated when every letter in its support lies in a displayed
cell.  Support is represented directly by membership in `word.toList`. -/
def RepeatedWord {alpha : Type} (word : Word alpha) : Prop :=
  Nonempty
    (∀ tested, tested ∈ word.toList → CellContains word tested)

noncomputable instance {alpha : Type} {word : Word alpha} :
    CoeFun (RepeatedWord word)
      (fun _ => ∀ tested, tested ∈ word.toList →
        CellContains word tested) where
  coe repeated := Classical.choice repeated

/-- Every cell has at least its two displayed boundary occurrences. -/
theorem CellContains.two_le_length
    {alpha : Type} {word : Word alpha} {tested : alpha}
    (cell : CellContains word tested) :
    2 ≤ word.toList.length := by
  rw [cell.factorization]
  simp only [List.length_append, List.length_cons]
  omega

/-- Failure of repeatedness exposes a supported letter with no containing
cell.  This form keeps the failed cell obligation available to later proofs. -/
theorem exists_supported_not_cell_of_not_repeated
    {alpha : Type} {word : Word alpha}
    (notRepeated : ¬ RepeatedWord word) :
    ∃ tested, tested ∈ word.toList ∧
      ¬ Nonempty (CellContains word tested) := by
  classical
  apply Decidable.byContradiction
  intro noTested
  apply notRepeated
  refine ⟨fun tested testedMem => Classical.choice ?_⟩
  apply Decidable.byContradiction
  intro noCell
  exact noTested ⟨tested, testedMem, noCell⟩

/-- Volkov's repeated-word split.  A word which is not repeated has a unique
occurrence of some supported letter, and no letter crosses that occurrence.
The prefix and suffix may be empty. -/
theorem exists_isolated_split_of_not_repeated
    {alpha : Type} {word : Word alpha}
    (notRepeated : ¬ RepeatedWord word) :
    ∃ tested beforeMarker suffix,
      word.toList = beforeMarker ++ [tested] ++ suffix ∧
        tested ∉ beforeMarker ∧
        tested ∉ suffix ∧
        ∀ letter, letter ∈ beforeMarker → letter ∉ suffix := by
  classical
  obtain ⟨tested, testedMem, noCell⟩ :=
    exists_supported_not_cell_of_not_repeated notRepeated
  obtain ⟨beforeMarker, suffix, split⟩ :=
    List.mem_iff_append.mp testedMem
  have singletonSplit :
      word.toList = beforeMarker ++ [tested] ++ suffix := by
    simpa [List.append_assoc] using split
  refine ⟨tested, beforeMarker, suffix, singletonSplit, ?_, ?_, ?_⟩
  · intro testedInPrefix
    obtain ⟨before, middle, prefixSplit⟩ :=
      List.mem_iff_append.mp testedInPrefix
    apply noCell
    refine
      ⟨{ y := tested
         leadingContext := before
         p := middle
         suffix := suffix
         factorization := ?_
         tested_mem := ?_ }⟩
    · rw [split, prefixSplit]
      simp [List.append_assoc]
    · simp
  · intro testedInSuffix
    obtain ⟨middle, after, suffixSplit⟩ :=
      List.mem_iff_append.mp testedInSuffix
    apply noCell
    refine
      ⟨{ y := tested
         leadingContext := beforeMarker
         p := middle
         suffix := after
         factorization := ?_
         tested_mem := ?_ }⟩
    · rw [split, suffixSplit]
    · simp
  · intro letter letterInPrefix letterInSuffix
    obtain ⟨before, leftMiddle, prefixSplit⟩ :=
      List.mem_iff_append.mp letterInPrefix
    obtain ⟨rightMiddle, after, suffixSplit⟩ :=
      List.mem_iff_append.mp letterInSuffix
    apply noCell
    refine
      ⟨{ y := letter
         leadingContext := before
         p := leftMiddle ++ tested :: rightMiddle
         suffix := after
         factorization := ?_
         tested_mem := ?_ }⟩
    · rw [split, prefixSplit, suffixSplit]
      simp [List.append_assoc]
    · simp [List.append_assoc]

end SemigroupBasis.CoRoots.S5_415
