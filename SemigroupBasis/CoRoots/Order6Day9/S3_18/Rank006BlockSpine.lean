import SemigroupBasis.CoRoots.Order6Day9.S3_18.Rank006SquaredReplay

/-!
# Rank006: arbitrary-word derivation to a support-disjoint block spine

Appending a letter already present in an earlier block closes the whole
intervening return into a genuine square. Fresh letters are left single.
The construction is an induction on the input list, with no length, rank
or multiplicity bound. It preserves an actual Sigma+ derivation, not just
a lower-factor signature. Adjacent square blocks are not yet merged, and
canonical separator uniqueness is a subsequent, separate layer.
-/

namespace SemigroupBasis.CoRoots.Order6Day9.S3_18.Rank006BlockSpine

open SemigroupBasis
open SemigroupBasis.CoRoots.S5_107
open SemigroupBasis.CoRoots.Order6Day9.S3_18.Rank006SigmaPlus
open SemigroupBasis.CoRoots.Order6Day9.S3_18.Rank006PeriodMacros
open SemigroupBasis.CoRoots.Order6Day9.S3_18.Rank006SquaredReplay

inductive Block where
  | single : Nat → Block
  | squared : Word Nat → Block
deriving DecidableEq

def Block.labels : Block → List Nat
  | .single letter => [letter]
  | .squared root => root.toList

def Block.render : Block → List Nat
  | .single letter => [letter]
  | .squared root => (square root).toList

def labels (blocks : List Block) : List Nat := blocks.flatMap Block.labels
def render (blocks : List Block) : List Nat := blocks.flatMap Block.render

/-- Every block's support is disjoint from every later block's support. -/
def Separated : List Block → Prop
  | [] => True
  | block :: rest =>
      (∀ letter, letter ∈ block.labels → letter ∉ labels rest) ∧ Separated rest

theorem block_render_support (block : Block) (letter : Nat) :
    letter ∈ block.render ↔ letter ∈ block.labels := by
  cases block with
  | single value => rfl
  | squared root =>
      simp only [Block.render, Block.labels, square, Word.toList_append,
        List.mem_append, or_self]

theorem render_support (blocks : List Block) (letter : Nat) :
    letter ∈ render blocks ↔ letter ∈ labels blocks := by
  simp only [render, labels, List.mem_flatMap, block_render_support]

theorem block_render_ne_nil (block : Block) : block.render ≠ [] := by
  cases block with
  | single value => simp [Block.render]
  | squared root => simp [Block.render, Word.toList]

theorem single_return (letter : Nat) (gap : List Nat) :
    ∃ root : Word Nat,
      ListDerives sigmaPlus ([letter] ++ gap ++ [letter]) (square root).toList := by
  cases gap with
  | nil =>
      refine ⟨Word.singleton letter, ?_⟩
      exact ListDerives.refl _
  | cons head tail =>
      refine ⟨Word.singleton letter ++ square (Word.mk head tail), ?_⟩
      simpa only [Word.toList_append, Word.toList_singleton, Word.toList] using
        ListDerives.ofWord
          (derivesReturnToSquare (Word.singleton letter) (Word.mk head tail))

theorem double_return (letter : Nat) (gap : List Nat) :
    ∃ root : Word Nat,
      ListDerives sigmaPlus
        ((square (Word.singleton letter)).toList ++ gap ++ [letter]) (square root).toList := by
  cases gap with
  | nil =>
      refine ⟨cube (Word.singleton letter), ?_⟩
      simpa [square, cube, Word.singleton, Word.append, Word.toList] using
        ListDerives.ofWord (derivesCubeToSquare (Word.singleton letter))
  | cons head tail =>
      refine ⟨cube (Word.singleton letter) ++ square (Word.mk head tail), ?_⟩
      simpa only [Word.toList_append, Word.toList_singleton, Word.toList] using
        ListDerives.ofWord
          (derivesDoubleReturnToSquare (Word.singleton letter) (Word.mk head tail))

/-- A return to ANY letter of a square block collapses the intervening gap
as well. The square's root is never replaced by its first letter alone. -/
theorem square_absorbs_member (word : Word Nat) (gap : List Nat) (letter : Nat)
    (member : letter ∈ word.toList) :
    ∃ root : Word Nat,
      ListDerives sigmaPlus ((square word).toList ++ gap ++ [letter]) (square root).toList := by
  have permutation := List.perm_cons_erase member
  cases erased : word.toList.erase letter with
  | nil =>
      rw [erased] at permutation
      have arrange : Derives sigmaPlus (square word) (square (Word.singleton letter)) :=
        derivesSquaredPermutation word (Word.singleton letter) permutation
      obtain ⟨root, collapse⟩ := double_return letter gap
      refine ⟨root, ?_⟩
      have first : ListDerives sigmaPlus ((square word).toList ++ gap ++ [letter])
          ((square (Word.singleton letter)).toList ++ gap ++ [letter]) := by
        simpa only [List.append_assoc] using
          (ListDerives.ofWord arrange).append (gap ++ [letter])
      exact first.trans collapse
  | cons head tail =>
      rw [erased] at permutation
      have arrange : Derives sigmaPlus (square word) (square (Word.mk letter (head :: tail))) :=
        derivesSquaredPermutation word (Word.mk letter (head :: tail)) permutation
      have collect : Derives sigmaPlus (square word)
          (square (Word.singleton letter) ++ square (Word.mk head tail)) :=
        arrange.trans (derivesSquareAppend (Word.singleton letter) (Word.mk head tail))
      obtain ⟨root, collapse⟩ :=
        double_return letter ((square (Word.mk head tail)).toList ++ gap)
      refine ⟨root, ?_⟩
      have first : ListDerives sigmaPlus ((square word).toList ++ gap ++ [letter])
          ((square (Word.singleton letter)).toList ++
            ((square (Word.mk head tail)).toList ++ gap) ++ [letter]) := by
        simpa only [Word.toList_append, List.append_assoc] using
          (ListDerives.ofWord collect).append (gap ++ [letter])
      exact first.trans collapse

theorem block_absorbs_member (block : Block) (gap : List Nat) (letter : Nat)
    (member : letter ∈ block.labels) :
    ∃ root : Word Nat,
      ListDerives sigmaPlus (block.render ++ gap ++ [letter]) (square root).toList := by
  cases block with
  | single value =>
      have same : letter = value := by simpa only [Block.labels, List.mem_singleton] using member
      subst letter
      exact single_return value gap
  | squared word =>
      exact square_absorbs_member word gap letter member

/-- Append one input letter and retain support separation plus a derivation. -/
theorem append_letter (blocks : List Block) (separated : Separated blocks) (letter : Nat) :
    ∃ output : List Block, Separated output ∧
      ListDerives sigmaPlus (render blocks ++ [letter]) (render output) := by
  induction blocks with
  | nil =>
      refine ⟨[Block.single letter], ?_, ?_⟩
      · simp [Separated, labels]
      · exact ListDerives.refl _
  | cons block rest induction =>
      by_cases member : letter ∈ block.labels
      · obtain ⟨root, collapse⟩ := block_absorbs_member block (render rest) letter member
        refine ⟨[Block.squared root], ?_, ?_⟩
        · simp [Separated, labels]
        · simpa only [render, List.flatMap_cons, List.flatMap_nil, List.append_nil,
            Block.render] using collapse
      · obtain ⟨output, outputSeparated, derivation⟩ := induction separated.2
        refine ⟨block :: output, ?_, ?_⟩
        · refine ⟨?_, outputSeparated⟩
          intro tested inBlock inOutput
          have inRender := (render_support output tested).mpr inOutput
          have inSource := (listDerives_support derivation tested).mpr inRender
          have cases : tested ∈ render rest ∨ tested = letter := by
            simpa only [List.mem_append, List.mem_singleton] using inSource
          rcases cases with inRest | same
          · exact separated.1 tested inBlock ((render_support rest tested).mp inRest)
          · subst tested
            exact member inBlock
        · simpa only [render, List.flatMap_cons, List.append_assoc] using
            derivation.prepend block.render

theorem append_letters (letters : List Nat) (blocks : List Block) (separated : Separated blocks) :
    ∃ output : List Block, Separated output ∧
      ListDerives sigmaPlus (render blocks ++ letters) (render output) := by
  induction letters generalizing blocks with
  | nil =>
      exact ⟨blocks, separated, by simpa using ListDerives.refl (basis := sigmaPlus) (render blocks)⟩
  | cons letter tail induction =>
      obtain ⟨next, nextSeparated, first⟩ := append_letter blocks separated letter
      obtain ⟨output, outputSeparated, second⟩ := induction next nextSeparated
      refine ⟨output, outputSeparated, ?_⟩
      have contextual : ListDerives sigmaPlus (render blocks ++ letter :: tail)
          (render next ++ tail) := by
        simpa only [List.append_assoc, List.singleton_append] using first.append tail
      exact contextual.trans second

/-- Every finite list admits an actual, support-disjoint Sigma+ block spine. -/
theorem separated_normal_list (letters : List Nat) :
    ∃ blocks : List Block, Separated blocks ∧ ListDerives sigmaPlus letters (render blocks) := by
  simpa only [render, List.flatMap_nil, List.nil_append] using
    append_letters letters [] (by trivial)

/-- Unrestricted nonempty-word version, retaining a nonempty target spine. -/
theorem separated_normal_word (word : Word Nat) :
    ∃ blocks : List Block, blocks ≠ [] ∧ Separated blocks ∧
      ListDerives sigmaPlus word.toList (render blocks) := by
  obtain ⟨blocks, separated, derivation⟩ := separated_normal_list word.toList
  refine ⟨blocks, ?_, separated, derivation⟩
  intro empty
  have nonempty := ListDerives.target_ne_nil derivation
  exact nonempty (by simp [empty, render])

theorem separated_normal_support (letters : List Nat) (blocks : List Block)
    (derivation : ListDerives sigmaPlus letters (render blocks)) (letter : Nat) :
    letter ∈ letters ↔ letter ∈ labels blocks :=
  (listDerives_support derivation letter).trans (render_support blocks letter)

end SemigroupBasis.CoRoots.Order6Day9.S3_18.Rank006BlockSpine
