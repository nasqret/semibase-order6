import SemigroupBasis.CoRoots.S5_107ListDerives
import SemigroupBasis.CoRoots.S5_213Syntax

namespace SemigroupBasis.CoRoots.S5_213Normalization

open SemigroupBasis
open SemigroupBasis.CoRoots
open SemigroupBasis.Examples

private abbrev ListDerives :=
  S5_107.ListDerives S5_213.basis

/-- The cap used by the gathered first-occurrence block normalizer. -/
def cappedExponent (count : Nat) : Nat :=
  if count < 3 then count else 3

theorem cappedExponent_eq_min (count : Nat) :
    cappedExponent count = Nat.min 3 count := by
  unfold cappedExponent
  simp only [Nat.min_def]
  split <;> split <;> omega

private theorem min_three_min_add (left right : Nat) :
    Nat.min 3 (Nat.min 3 left + right) =
      Nat.min 3 (left + right) := by
  by_cases capped : 3 ≤ left
  · have inner : Nat.min 3 left = 3 :=
      Nat.min_eq_left capped
    calc
      Nat.min 3 (Nat.min 3 left + right) =
          Nat.min 3 (3 + right) := by rw [inner]
      _ = 3 := Nat.min_eq_left (by omega)
      _ = Nat.min 3 (left + right) :=
        (Nat.min_eq_left (by omega)).symm
  · have below : left ≤ 3 := by omega
    have inner : Nat.min 3 left = left :=
      Nat.min_eq_right below
    rw [inner]

private theorem cappedExponent_pos
    {count : Nat} (positive : 0 < count) :
    0 < cappedExponent count := by
  unfold cappedExponent
  split <;> omega

private theorem cappedExponent_le_three (count : Nat) :
    cappedExponent count ≤ 3 := by
  unfold cappedExponent
  split <;> omega

private theorem cappedExponent_succ_normalized (count : Nat) :
    cappedExponent (cappedExponent count + 1) =
      cappedExponent (count + 1) := by
  simp only [cappedExponent_eq_min]
  exact min_three_min_add count 1

private def wordOfCons (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

/-- Move the second occurrence of the initial variable next to the first. -/
private theorem derivesFirstRepeat
    (x : Nat) (middle suffix : List Nat) :
    Derives S5_213.basis
      (wordOfCons x (middle ++ x :: suffix))
      (wordOfCons x (x :: middle ++ suffix)) := by
  cases middle with
  | nil =>
      exact Derives.refl _
  | cons y ys =>
      let middleWord := wordOfCons y ys
      cases suffix with
      | nil =>
          simpa [wordOfCons, middleWord, Word.append, Word.singleton,
            Word.append_assoc] using
              S5_213.derivesLeftGather
                (Word.singleton x) middleWord
      | cons z zs =>
          have moved :=
            Derives.appendRight
              (S5_213.derivesLeftGather
                (Word.singleton x) middleWord)
              (wordOfCons z zs)
          simpa [wordOfCons, middleWord, Word.append, Word.singleton,
            Word.append_assoc] using moved

/-- Move the third occurrence next to the gathered square. -/
private theorem derivesThird
    (x : Nat) (middle suffix : List Nat) :
    Derives S5_213.basis
      (wordOfCons x (x :: middle ++ x :: suffix))
      (wordOfCons x (x :: x :: middle ++ suffix)) := by
  cases middle with
  | nil =>
      exact Derives.refl _
  | cons y ys =>
      let middleWord := wordOfCons y ys
      have moved :=
        Derives.prepend (Word.singleton x) <|
          S5_213.derivesLeftGather
            (Word.singleton x) middleWord
      cases suffix with
      | nil =>
          simpa [wordOfCons, middleWord, Word.append, Word.singleton,
            Word.append_assoc] using moved
      | cons z zs =>
          have movedWithSuffix :=
            Derives.appendRight moved (wordOfCons z zs)
          simpa [wordOfCons, middleWord, Word.append, Word.singleton,
            Word.append_assoc] using movedWithSuffix

/-- Gather a fourth occurrence and contract the leading fourth power to a
triple. Further occurrences repeat this same transition. -/
private theorem derivesFourthToTriple
    (x : Nat) (middle suffix : List Nat) :
    Derives S5_213.basis
      (wordOfCons x (x :: x :: middle ++ x :: suffix))
      (wordOfCons x (x :: x :: middle ++ suffix)) := by
  cases middle with
  | nil =>
      cases suffix with
      | nil =>
          simpa [wordOfCons, Word.append, Word.singleton,
            Word.append_assoc] using
              S5_213.derivesPowerContraction
                (Word.singleton x)
      | cons z zs =>
          have contracted :=
            Derives.appendRight
              (S5_213.derivesPowerContraction
                (Word.singleton x))
              (wordOfCons z zs)
          simpa [wordOfCons, Word.append, Word.singleton,
            Word.append_assoc] using contracted
  | cons y ys =>
      let middleWord := wordOfCons y ys
      have moved :=
        Derives.prepend
          ((Word.singleton x) ++ (Word.singleton x)) <|
            S5_213.derivesLeftGather
              (Word.singleton x) middleWord
      have contracted :=
        Derives.appendRight
          (S5_213.derivesPowerContraction
            (Word.singleton x))
          middleWord
      cases suffix with
      | nil =>
          apply Derives.trans
          · simpa [wordOfCons, middleWord, Word.append,
              Word.singleton, Word.append_assoc] using moved
          · simpa [wordOfCons, middleWord, Word.append,
              Word.singleton, Word.append_assoc] using contracted
      | cons z zs =>
          have movedWithSuffix :=
            Derives.appendRight moved (wordOfCons z zs)
          have contractedWithSuffix :=
            Derives.appendRight contracted (wordOfCons z zs)
          apply Derives.trans
          · simpa [wordOfCons, middleWord, Word.append,
              Word.singleton, Word.append_assoc] using movedWithSuffix
          · simpa [wordOfCons, middleWord, Word.append,
              Word.singleton, Word.append_assoc] using
                contractedWithSuffix

private inductive GatherState where
  | one
  | two
  | three
deriving DecidableEq, Repr

private def GatherState.exponent : GatherState → Nat
  | .one => 1
  | .two => 2
  | .three => 3

private def GatherState.next : GatherState → GatherState
  | .one => .two
  | .two => .three
  | .three => .three

private def GatherState.advance :
    GatherState → Nat → GatherState
  | state, 0 => state
  | state, count + 1 => advance state.next count

private def gatheredTail
    (state : GatherState)
    (x : Nat) (middle suffix : List Nat) : List Nat :=
  List.replicate (state.exponent - 1) x ++ middle ++ suffix

private theorem advance_exponent
    (state : GatherState) (count : Nat) :
    (state.advance count).exponent =
      cappedExponent (state.exponent + count) := by
  induction count generalizing state with
  | zero =>
      cases state <;> decide
  | succ count induction =>
      rw [GatherState.advance, induction]
      cases state <;>
        simp only [GatherState.next, GatherState.exponent] <;>
        unfold cappedExponent <;>
        split <;> split <;> omega

/-- Scan a suffix and gather every later copy of the initial variable into
one leading block of length `1`, `2`, or `3`. -/
private theorem derivesGatherCap :
    ∀ (state : GatherState)
        (x : Nat) (middle rest : List Nat),
      Derives S5_213.basis
        (wordOfCons x (gatheredTail state x middle rest))
        (wordOfCons x
          (gatheredTail
            (state.advance (rest.count x)) x middle
            (rest.filter (fun y => decide (y ≠ x)))))
  | state, x, middle, [] => by
      simp [gatheredTail, GatherState.advance]
      exact Derives.refl _
  | state, x, middle, y :: ys => by
      by_cases equal : y = x
      · subst y
        cases state with
        | one =>
            have first := derivesFirstRepeat x middle ys
            have remaining :=
              derivesGatherCap .two x middle ys
            exact first.trans <| by
              simpa [gatheredTail, GatherState.advance] using remaining
        | two =>
            have first := derivesThird x middle ys
            have remaining :=
              derivesGatherCap .three x middle ys
            exact first.trans <| by
              simpa [gatheredTail, GatherState.advance] using remaining
        | three =>
            have first := derivesFourthToTriple x middle ys
            have remaining :=
              derivesGatherCap .three x middle ys
            exact first.trans <| by
              simpa [gatheredTail, GatherState.advance] using remaining
      · have remaining :=
          derivesGatherCap state x (middle ++ [y]) ys
        simpa [gatheredTail, equal, List.count_cons_of_ne equal,
          List.append_assoc] using remaining

private theorem count_replicate_of_ne
    {x z : Nat} (different : z ≠ x) :
    ∀ count : Nat, (List.replicate count x).count z = 0
  | 0 => rfl
  | count + 1 => by
      rw [List.replicate_succ,
        List.count_cons_of_ne (Ne.symm different),
        count_replicate_of_ne different count]

private theorem count_filter_ne_self
    (x : Nat) (letters : List Nat) :
    (letters.filter (fun z => decide (z ≠ x))).count x = 0 := by
  apply List.count_eq_zero.mpr
  simp

private theorem count_filter_ne_of_ne
    {x z : Nat} (different : z ≠ x) (letters : List Nat) :
    (letters.filter (fun value => decide (value ≠ x))).count z =
      letters.count z := by
  induction letters with
  | nil => rfl
  | cons value rest induction =>
      by_cases equal : value = x
      · subst value
        rw [List.filter_cons_of_neg (by simp),
          List.count_cons_of_ne (Ne.symm different)]
        exact induction
      · rw [List.filter_cons_of_pos (by simpa)]
        simp only [List.count_cons]
        rw [induction]

/-- First-occurrence blocks with every exponent capped to `1`, `2`, or `3`. -/
def gatheredNormalList : List Nat → List Nat
  | [] => []
  | x :: xs =>
      let rest := gatheredNormalList xs
      List.replicate
          (cappedExponent ((x :: xs).count x)) x ++
        rest.filter (fun y => decide (y ≠ x))

theorem gatheredNormalList_count
    (z : Nat) :
    ∀ letters : List Nat,
      (gatheredNormalList letters).count z =
        cappedExponent (letters.count z)
  | [] => by
      simp [gatheredNormalList, cappedExponent]
  | x :: xs => by
      simp only [gatheredNormalList, List.count_append]
      by_cases equal : z = x
      · subst z
        rw [List.count_replicate_self,
          count_filter_ne_self]
        omega
      · rw [count_replicate_of_ne equal,
          count_filter_ne_of_ne equal,
          Nat.zero_add, gatheredNormalList_count]
        rw [List.count_cons_of_ne (Ne.symm equal)]

theorem gatheredNormalList_cons_ne_nil
    (x : Nat) (xs : List Nat) :
    gatheredNormalList (x :: xs) ≠ [] := by
  intro empty
  have countEquation :=
    gatheredNormalList_count x (x :: xs)
  rw [empty, List.count_nil, List.count_cons_self] at countEquation
  exact
    (Nat.ne_of_gt <|
      cappedExponent_pos (by omega)) countEquation.symm

private theorem derivesNormalizeList :
    ∀ x xs,
      match gatheredNormalList (x :: xs) with
      | [] => False
      | y :: ys =>
          Derives S5_213.basis
            (wordOfCons x xs) (wordOfCons y ys)
  | x, [] => by
      have normal :
          gatheredNormalList [x] = [x] := by
        simp [gatheredNormalList, cappedExponent]
      rw [normal]
      exact Derives.refl _
  | x, y :: ys => by
      have suffixNormal := derivesNormalizeList y ys
      cases normalSuffix : gatheredNormalList (y :: ys) with
      | nil =>
          exact False.elim <|
            gatheredNormalList_cons_ne_nil y ys normalSuffix
      | cons z zs =>
          rw [normalSuffix] at suffixNormal
          have prefixed :=
            Derives.prepend (Word.singleton x) suffixNormal
          have gathered :=
            derivesGatherCap .one x [] (z :: zs)
          have restCount :
              (z :: zs).count x =
                cappedExponent ((y :: ys).count x) := by
            simpa [normalSuffix] using
              gatheredNormalList_count x (y :: ys)
          have exponentEqual :
              (GatherState.one.advance
                  ((z :: zs).count x)).exponent =
                cappedExponent ((x :: y :: ys).count x) := by
            rw [advance_exponent]
            simp only [GatherState.exponent]
            rw [restCount, List.count_cons_self]
            simpa [Nat.add_comm] using
              cappedExponent_succ_normalized
                ((y :: ys).count x)
          have positive :
              0 < cappedExponent ((x :: y :: ys).count x) :=
            cappedExponent_pos (by simp)
          have normalEqual :
              gatheredNormalList (x :: y :: ys) =
                x ::
                  List.replicate
                    (cappedExponent
                      ((x :: y :: ys).count x) - 1) x ++
                    (z :: zs).filter
                      (fun value => decide (value ≠ x)) := by
            change
              List.replicate
                  (cappedExponent ((x :: y :: ys).count x)) x ++
                  (gatheredNormalList (y :: ys)).filter
                    (fun value => decide (value ≠ x)) =
                x ::
                  List.replicate
                    (cappedExponent
                      ((x :: y :: ys).count x) - 1) x ++
                    (z :: zs).filter
                      (fun value => decide (value ≠ x))
            rw [normalSuffix]
            cases exponent :
                cappedExponent ((x :: y :: ys).count x) with
            | zero => omega
            | succ count =>
                simp [List.replicate_succ]
          rw [normalEqual]
          apply Derives.trans
          · simpa [wordOfCons, Word.append, Word.singleton,
              Word.append_assoc] using prefixed
          · simpa [gatheredTail, exponentEqual] using gathered
termination_by
  _ xs => xs.length

/-- Every word derives to its capped first-occurrence block list. -/
theorem derivesGatheredNormal (word : Word Nat) :
    match gatheredNormalList word.toList with
    | [] => False
    | head :: tail =>
        Derives S5_213.basis word (wordOfCons head tail) := by
  cases word with
  | mk head tail =>
      exact derivesNormalizeList head tail

/-- A repeated block carries its cap-two or cap-three tag explicitly. -/
inductive RepeatedBlock where
  | double : Nat → RepeatedBlock
  | triple : Nat → RepeatedBlock
deriving DecidableEq, Repr

namespace RepeatedBlock

def label : RepeatedBlock → Nat
  | .double x => x
  | .triple x => x

def render : RepeatedBlock → List Nat
  | .double x => [x, x]
  | .triple x => [x, x, x]

end RepeatedBlock

def renderRepeatedBlocks (blocks : List RepeatedBlock) : List Nat :=
  blocks.flatMap RepeatedBlock.render

/-- A double or triple block moves across an arbitrary list. This is the
stable-partition step that never swaps two singleton variables. -/
theorem listDerivesRepeatedBlockAcross
    (block : RepeatedBlock) (letters : List Nat) :
    ListDerives
      (block.render ++ letters)
      (letters ++ block.render) := by
  cases letters with
  | nil =>
      simpa using
        S5_107.ListDerives.refl
          (basis := S5_213.basis) block.render
  | cons head tail =>
      cases block with
      | double x =>
          exact S5_107.ListDerives.words <| by
            simpa [RepeatedBlock.render, wordOfCons,
              S5_107.listWordOfCons, Word.append, Word.singleton,
              Word.append_assoc] using
                S5_213.derivesSquareAcross
                  (Word.singleton x) (wordOfCons head tail)
      | triple x =>
          exact S5_107.ListDerives.words <| by
            simpa [RepeatedBlock.render, wordOfCons,
              S5_107.listWordOfCons, Word.append, Word.singleton,
              Word.append_assoc] using
                S5_213.derivesCubeAcross
                  (Word.singleton x) (wordOfCons head tail)

/-- Any two repeated blocks commute after rendering. -/
theorem listDerivesRepeatedBlockCommutation
    (left right : RepeatedBlock) :
    ListDerives
      (left.render ++ right.render)
      (right.render ++ left.render) :=
  listDerivesRepeatedBlockAcross left right.render

/-- Every permutation of repeated blocks is derivable. -/
theorem listDerivesRepeatedBlockPermutation
    {source target : List RepeatedBlock}
    (permutation : source.Perm target) :
    ListDerives
      (renderRepeatedBlocks source)
      (renderRepeatedBlocks target) := by
  induction permutation with
  | nil =>
      exact S5_107.ListDerives.empty
  | cons block _ induction =>
      simpa [renderRepeatedBlocks] using
        induction.prepend block.render
  | swap left right rest =>
      have swapped :=
        listDerivesRepeatedBlockCommutation left right
      simpa [renderRepeatedBlocks] using
        (swapped.append
          (renderRepeatedBlocks rest)).symm
  | trans _ _ first second =>
      exact first.trans second

def sortedRepeatedBlocks
    (blocks : List RepeatedBlock) : List RepeatedBlock :=
  blocks.mergeSort
    (fun left right =>
      decide (left.label ≤ right.label))

/-- Sorting repeated blocks by their variable is derivable. -/
theorem listDerivesSortRepeatedBlocks
    (blocks : List RepeatedBlock) :
    ListDerives
      (renderRepeatedBlocks blocks)
      (renderRepeatedBlocks (sortedRepeatedBlocks blocks)) := by
  apply listDerivesRepeatedBlockPermutation
  exact (List.mergeSort_perm _ _).symm

private def cappedBlock
    (letters : List Nat) (letter : Nat) : List Nat :=
  List.replicate (cappedExponent (letters.count letter)) letter

private def firstOccurrenceBlockList
    (letters : List Nat) : List Nat :=
  (firstOccurrenceSequence letters).flatMap
    (cappedBlock letters)

private theorem filter_replicate_self
    (selected : Nat) :
    ∀ count : Nat,
      (List.replicate count selected).filter
          (fun letter => decide (letter ≠ selected)) = []
  | 0 => rfl
  | count + 1 => by
      rw [List.replicate_succ]
      simp [filter_replicate_self selected count]

private theorem filter_replicate_of_ne
    {letter selected : Nat} (different : letter ≠ selected) :
    ∀ count : Nat,
      (List.replicate count letter).filter
          (fun value => decide (value ≠ selected)) =
        List.replicate count letter
  | 0 => rfl
  | count + 1 => by
      rw [List.replicate_succ]
      simp [different, filter_replicate_of_ne different count]

private theorem filter_capped_blocks
    (source target : List Nat) (selected : Nat)
    (sameCounts :
      ∀ letter, letter ≠ selected →
        source.count letter = target.count letter) :
    ∀ labels : List Nat,
      (labels.flatMap (cappedBlock source)).filter
          (fun letter => decide (letter ≠ selected)) =
        (labels.filter
            (fun letter => decide (letter ≠ selected))).flatMap
          (cappedBlock target)
  | [] => rfl
  | letter :: rest => by
      have recursive :=
        filter_capped_blocks
          source target selected sameCounts rest
      rw [List.flatMap_cons, List.filter_append]
      by_cases equal : letter = selected
      · subst letter
        have blockFilter :
            (cappedBlock source selected).filter
                (fun letter => decide (letter ≠ selected)) = [] := by
          exact
            filter_replicate_self selected
              (cappedExponent (source.count selected))
        rw [blockFilter, List.nil_append, recursive]
        simp
      · have countEq := sameCounts letter equal
        have blockEq :
            cappedBlock source letter =
              cappedBlock target letter := by
          unfold cappedBlock
          rw [countEq]
        have blockFilter :
            (cappedBlock target letter).filter
                (fun value => decide (value ≠ selected)) =
              cappedBlock target letter := by
          exact
            filter_replicate_of_ne equal
              (cappedExponent (target.count letter))
        rw [blockEq, blockFilter, recursive]
        simp [equal]

private theorem gatheredNormalList_eq_firstOccurrenceBlockList :
    ∀ letters : List Nat,
      gatheredNormalList letters =
        firstOccurrenceBlockList letters
  | [] => rfl
  | letter :: rest => by
      have induction :=
        gatheredNormalList_eq_firstOccurrenceBlockList rest
      have filtered :=
        filter_capped_blocks rest (letter :: rest) letter
          (fun next different => by
            simp [List.count_cons_of_ne (Ne.symm different)])
          (firstOccurrenceSequence rest)
      unfold firstOccurrenceBlockList
      simp only [gatheredNormalList]
      rw [firstOccurrenceSequence, List.flatMap_cons]
      have headBlock :
          cappedBlock (letter :: rest) letter =
            List.replicate
              (cappedExponent ((letter :: rest).count letter))
              letter := rfl
      rw [headBlock, induction]
      unfold firstOccurrenceBlockList
      rw [filtered]

private def singletonLabel
    (word : Word Nat) (letter : Nat) : Bool :=
  decide (word.toList.count letter = 1)

private def repeatedLabel
    (word : Word Nat) (letter : Nat) : Bool :=
  decide (2 ≤ word.toList.count letter)

private def repeatedBlockOf
    (word : Word Nat) (letter : Nat) : RepeatedBlock :=
  if word.toList.count letter = 2 then
    .double letter
  else
    .triple letter

private def repeatedBlocksInput
    (word : Word Nat) : List RepeatedBlock :=
  (S5_213Syntax.repeatedLetterInput word).map
    (repeatedBlockOf word)

private def canonicalRepeatedBlocks
    (word : Word Nat) : List RepeatedBlock :=
  (S5_213Syntax.sortedRepeatedLetters word).map
    (repeatedBlockOf word)

private theorem cappedBlock_eq_singleton
    (word : Word Nat) {letter : Nat}
    (simple : word.toList.count letter = 1) :
    cappedBlock word.toList letter = [letter] := by
  simp [cappedBlock, cappedExponent, simple]

private theorem cappedBlock_eq_repeatedBlock_render
    (word : Word Nat) {letter : Nat}
    (multiple : 2 ≤ word.toList.count letter) :
    cappedBlock word.toList letter =
      (repeatedBlockOf word letter).render := by
  by_cases double : word.toList.count letter = 2
  · simp [cappedBlock, cappedExponent, repeatedBlockOf,
      RepeatedBlock.render, double]
  · have notSmall : ¬ word.toList.count letter < 3 := by
      omega
    simp [cappedBlock, cappedExponent, repeatedBlockOf,
      RepeatedBlock.render, double, notSmall]

private theorem repeatedBlockOf_render
    (word : Word Nat) (letter : Nat) :
    (repeatedBlockOf word letter).render =
      S5_213Syntax.renderRepeatedBlock word letter := by
  unfold repeatedBlockOf S5_213Syntax.renderRepeatedBlock
  split <;> rfl

private theorem renderRepeatedBlocks_map
    (word : Word Nat) :
    ∀ labels : List Nat,
      renderRepeatedBlocks
          (labels.map (repeatedBlockOf word)) =
        labels.flatMap
          (S5_213Syntax.renderRepeatedBlock word)
  | [] => rfl
  | letter :: rest => by
      change
        (repeatedBlockOf word letter).render ++
            renderRepeatedBlocks (rest.map (repeatedBlockOf word)) =
          S5_213Syntax.renderRepeatedBlock word letter ++
            rest.flatMap (S5_213Syntax.renderRepeatedBlock word)
      rw [repeatedBlockOf_render, renderRepeatedBlocks_map word rest]

private theorem listDerivesBlocksToPartition
    (word : Word Nat) :
    ∀ labels : List Nat,
      (∀ letter, letter ∈ labels →
        0 < word.toList.count letter) →
      ListDerives
        (labels.flatMap (cappedBlock word.toList))
        (labels.filter (singletonLabel word) ++
          renderRepeatedBlocks
            ((labels.filter (repeatedLabel word)).map
              (repeatedBlockOf word)))
  | [], _ => by
      simpa [renderRepeatedBlocks] using
        S5_107.ListDerives.empty
          (basis := S5_213.basis)
  | letter :: rest, positive => by
      have headPositive :
          0 < word.toList.count letter :=
        positive letter (by simp)
      have restPositive :
          ∀ selected, selected ∈ rest →
            0 < word.toList.count selected := by
        intro selected member
        exact positive selected (by simp [member])
      have tailDerivation :=
        listDerivesBlocksToPartition word rest restPositive
      by_cases simple : word.toList.count letter = 1
      · have notRepeated :
            ¬ 2 ≤ word.toList.count letter := by
          omega
        have prefixed := tailDerivation.prepend [letter]
        simpa [List.flatMap_cons,
          cappedBlock_eq_singleton word simple,
          singletonLabel, repeatedLabel, simple, notRepeated] using
            prefixed
      · have multiple :
            2 ≤ word.toList.count letter := by
          omega
        have blockEq :=
          cappedBlock_eq_repeatedBlock_render word multiple
        have prefixed :=
          tailDerivation.prepend
            (repeatedBlockOf word letter).render
        have movedWithSuffix :=
          (listDerivesRepeatedBlockAcross
              (repeatedBlockOf word letter)
              (rest.filter (singletonLabel word))).append
            (renderRepeatedBlocks
              ((rest.filter (repeatedLabel word)).map
                (repeatedBlockOf word)))
        have movedFromTailTarget :
            ListDerives
              ((repeatedBlockOf word letter).render ++
                (rest.filter (singletonLabel word) ++
                  renderRepeatedBlocks
                    ((rest.filter (repeatedLabel word)).map
                      (repeatedBlockOf word))))
              (rest.filter (singletonLabel word) ++
                ((repeatedBlockOf word letter).render ++
                  renderRepeatedBlocks
                    ((rest.filter (repeatedLabel word)).map
                      (repeatedBlockOf word)))) := by
          simpa [List.append_assoc] using movedWithSuffix
        have combined :=
          prefixed.trans movedFromTailTarget
        simpa [List.flatMap_cons, blockEq,
          singletonLabel, repeatedLabel, simple, multiple,
          renderRepeatedBlocks, List.append_assoc] using combined

private theorem listDerivesGatheredNormalToPartition
    (word : Word Nat) :
    ListDerives
      (gatheredNormalList word.toList)
      (S5_213Syntax.singletonSequence word ++
        renderRepeatedBlocks (repeatedBlocksInput word)) := by
  have partition :=
    listDerivesBlocksToPartition word
      (firstOccurrenceSequence word.toList) <| by
        intro letter member
        exact List.count_pos_iff.mpr <|
          (S5_213Syntax.mem_firstOccurrenceSequence_iff
            letter word.toList).1 member
  rw [gatheredNormalList_eq_firstOccurrenceBlockList]
  simpa [firstOccurrenceBlockList, singletonLabel, repeatedLabel,
    repeatedBlocksInput, S5_213Syntax.repeatedLetterInput,
    S5_213Syntax.singletonSequence_eq_firstOccurrence_filter] using
      partition

private theorem repeatedBlocksInput_perm_canonical
    (word : Word Nat) :
    (repeatedBlocksInput word).Perm
      (canonicalRepeatedBlocks word) := by
  unfold repeatedBlocksInput canonicalRepeatedBlocks
    S5_213Syntax.sortedRepeatedLetters
  exact
    ((List.mergeSort_perm
      (S5_213Syntax.repeatedLetterInput word)
      (fun left right : Nat => decide (left ≤ right))).map
        (repeatedBlockOf word)).symm

private theorem sortedRepeatedBlocks_perm_canonical
    (word : Word Nat) :
    (sortedRepeatedBlocks (repeatedBlocksInput word)).Perm
      (canonicalRepeatedBlocks word) := by
  have sortedPerm :
      (sortedRepeatedBlocks (repeatedBlocksInput word)).Perm
        (repeatedBlocksInput word) := by
    unfold sortedRepeatedBlocks
    exact List.mergeSort_perm _ _
  exact sortedPerm.trans
    (repeatedBlocksInput_perm_canonical word)

private theorem listDerivesPartitionToCanonical
    (word : Word Nat) :
    ListDerives
      (S5_213Syntax.singletonSequence word ++
        renderRepeatedBlocks (repeatedBlocksInput word))
      (S5_213Syntax.canonicalList word) := by
  have sorted :=
    listDerivesSortRepeatedBlocks (repeatedBlocksInput word)
  have reordered :=
    listDerivesRepeatedBlockPermutation
      (sortedRepeatedBlocks_perm_canonical word)
  have repeatedDerivation := sorted.trans reordered
  have prefixed :=
    repeatedDerivation.prepend
      (S5_213Syntax.singletonSequence word)
  simpa [S5_213Syntax.canonicalList, canonicalRepeatedBlocks,
    renderRepeatedBlocks_map] using prefixed

/-- The gathered capped blocks derive to the deterministic canonical list. -/
theorem listDerivesGatheredNormalToCanonical
    (word : Word Nat) :
    ListDerives
      (gatheredNormalList word.toList)
      (S5_213Syntax.canonicalList word) :=
  (listDerivesGatheredNormalToPartition word).trans
    (listDerivesPartitionToCanonical word)

private theorem derivesGatheredNormalToCanonicalWord
    (word : Word Nat) {head : Nat} {tail : List Nat}
    (normal :
      gatheredNormalList word.toList = head :: tail) :
    Derives S5_213.basis
      (wordOfCons head tail)
      (S5_213Syntax.canonicalWord word) := by
  have listDerivation :=
    listDerivesGatheredNormalToCanonical word
  rw [normal] at listDerivation
  obtain
      ⟨canonicalHead, canonicalTail,
        targetEq, wordDerivation⟩ :=
    S5_107.ListDerives.from_cons listDerivation
  have targetWordEq :
      S5_107.listWordOfCons canonicalHead canonicalTail =
        S5_213Syntax.canonicalWord word := by
    apply Word.toList_injective
    rw [S5_213Syntax.toList_canonicalWord]
    simpa [S5_107.listWordOfCons, Word.toList] using
      targetEq.symm
  rw [targetWordEq] at wordDerivation
  simpa [wordOfCons, S5_107.listWordOfCons] using
    wordDerivation

/-- Every word derives unconditionally to its canonical representative. -/
theorem derivesCanonical (word : Word Nat) :
    Derives S5_213.basis word
      (S5_213Syntax.canonicalWord word) := by
  have gathered := derivesGatheredNormal word
  cases normal : gatheredNormalList word.toList with
  | nil =>
      exact False.elim <| by
        rw [normal] at gathered
        exact gathered
  | cons head tail =>
      rw [normal] at gathered
      exact gathered.trans <|
        derivesGatheredNormalToCanonicalWord word normal

/-- Equal capped multiplicities and singleton order imply derivability. -/
theorem derives_of_sameSignature
    {left right : Word Nat}
    (same :
      S5_213Syntax.SameCappedSingletonSignature left right) :
    Derives S5_213.basis left right := by
  have leftCanonical := derivesCanonical left
  have rightCanonical := derivesCanonical right
  rw [same.canonicalWord_eq] at leftCanonical
  exact leftCanonical.trans rightCanonical.symm

end SemigroupBasis.CoRoots.S5_213Normalization
