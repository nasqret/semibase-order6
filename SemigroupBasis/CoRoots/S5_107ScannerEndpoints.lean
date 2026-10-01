import SemigroupBasis.CoRoots.S5_107Extraction

namespace SemigroupBasis.CoRoots.S5_107

private theorem terminatedBlockScan_first_block_ne_nil
    (whole current remaining : List Nat)
    (currentNe : current ≠ [])
    (first : List Nat × Nat)
    (rest : List (List Nat × Nat))
    (shape :
      (terminatedBlockScan whole current remaining).1 =
        first :: rest) :
    first.1 ≠ [] := by
  induction remaining generalizing current first rest with
  | nil =>
      simp [terminatedBlockScan] at shape
  | cons letter remaining ih =>
      by_cases simple : whole.count letter = 1
      · exact
          ih (letter :: current) (by simp)
            first rest <| by
            simpa [terminatedBlockScan, simple] using shape
      · simp only [terminatedBlockScan, if_neg simple] at shape
        have firstEq :
            (current.reverse, letter) = first :=
          (List.cons.inj shape).1
        rw [← firstEq]
        simpa using currentNe

private theorem terminatedBlockScan_final_ne_nil_of_last_simple
    (whole current before : List Nat)
    (last : Nat)
    (lastSimple : whole.count last = 1) :
    (terminatedBlockScan whole current (before ++ [last])).2 ≠ [] := by
  induction before generalizing current with
  | nil =>
      simp [terminatedBlockScan, lastSimple]
  | cons letter before ih =>
      by_cases simple : whole.count letter = 1
      · simpa [terminatedBlockScan, simple] using
          ih (letter :: current)
      · simpa [terminatedBlockScan, simple] using
          ih ([] : List Nat)

private theorem terminatedBlockScan_final_eq_nil_of_last_not_simple
    (whole current before : List Nat)
    (last : Nat)
    (lastNotSimple : whole.count last ≠ 1) :
    (terminatedBlockScan whole current (before ++ [last])).2 = [] := by
  induction before generalizing current with
  | nil =>
      simp [terminatedBlockScan, lastNotSimple]
  | cons letter before ih =>
      by_cases simple : whole.count letter = 1
      · simpa [terminatedBlockScan, simple] using
          ih (letter :: current)
      · simpa [terminatedBlockScan, simple] using
          ih ([] : List Nat)

private theorem terminatedBlockScan_final_eq_simpleBlockScan_getLastD
    (whole current before : List Nat)
    (last : Nat)
    (lastSimple : whole.count last = 1) :
    (terminatedBlockScan whole current (before ++ [last])).2 =
      (simpleBlockScan whole current
        (before ++ [last])).getLastD [] := by
  have finalNe :=
    terminatedBlockScan_final_ne_nil_of_last_simple
      whole current before last lastSimple
  have bridge :=
    simpleBlockScan_eq_terminatedBlockScan
      whole current (before ++ [last])
  have lastEq :=
    congrArg
      (fun blocks : List (List Nat) => blocks.getLastD [])
      bridge
  simpa [simpleBlocksFromTerminated, finalNe] using lastEq.symm

/-- The trailing block produced by the terminated scanner is exactly the
final maximal simple block. -/
theorem terminatedFinalBlock_eq_finalSimpleBlock
    (letters : List Nat) :
    terminatedFinalBlock letters = finalSimpleBlock letters := by
  cases letters with
  | nil =>
      rfl
  | cons head tail =>
      have wordShape :
          head :: tail =
            (head :: tail).dropLast ++ [tail.getLastD head] := by
        have reconstruct :=
          (List.dropLast_concat_getLast
            (l := head :: tail) (by simp)).symm
        rw [List.getLast_eq_getLastD] at reconstruct
        simpa only [List.getLastD_cons] using reconstruct
      change
        (terminatedBlockScan
          (head :: tail) [] (head :: tail)).2 =
            if decide
                ((head :: tail).count (tail.getLastD head) = 1)
            then
              (simpleBlockScan
                (head :: tail) [] (head :: tail)).getLastD []
            else
              []
      by_cases finalSimple :
          (head :: tail).count (tail.getLastD head) = 1
      · have endpoint :=
          terminatedBlockScan_final_eq_simpleBlockScan_getLastD
            (head :: tail) []
            (head :: tail).dropLast
            (tail.getLastD head) finalSimple
        rw [← wordShape] at endpoint
        have finalDecision :
            decide
                ((head :: tail).count
                  (tail.getLastD head) = 1) =
              true := by
          exact decide_eq_true finalSimple
        rw [finalDecision]
        exact endpoint
      · have endpoint :=
          terminatedBlockScan_final_eq_nil_of_last_not_simple
            (head :: tail) []
            (head :: tail).dropLast
            (tail.getLastD head) finalSimple
        rw [← wordShape] at endpoint
        have finalDecision :
            decide
                ((head :: tail).count
                  (tail.getLastD head) = 1) =
              false := by
          exact decide_eq_false finalSimple
        rw [finalDecision]
        exact endpoint

/-- When the terminated scanner emits at least one factor, its first block
is the initial simple block and the remaining nonempty blocks are precisely
the interior simple blocks. -/
theorem terminatedBlocks_cons_endpoint_blocks
    (letters : List Nat)
    (first : List Nat × Nat)
    (rest : List (List Nat × Nat))
    (shape : terminatedBlocks letters = first :: rest) :
    first.1 = initialSimpleBlock letters ∧
      nonemptyTerminatedBlocks rest =
        interiorSimpleBlocks letters := by
  have firstEq : first.1 = initialSimpleBlock letters := by
    cases letters with
    | nil =>
        simp [terminatedBlocks, terminatedBlockScan] at shape
    | cons head tail =>
        change
          first.1 =
            if decide ((head :: tail).count head = 1)
            then
              (simpleBlocks (head :: tail)).headD []
            else
              []
        by_cases initialSimple :
            (head :: tail).count head = 1
        · have initialDecision :
              decide ((head :: tail).count head = 1) =
                true := by
            exact decide_eq_true initialSimple
          rw [initialDecision]
          have scanShape :
              (terminatedBlockScan
                (head :: tail) [head] tail).1 =
                  first :: rest := by
            simpa [terminatedBlocks, terminatedBlockScan,
              initialSimple] using shape
          have firstNe :
              first.1 ≠ [] :=
            terminatedBlockScan_first_block_ne_nil
              (head :: tail) [head] tail (by simp)
              first rest scanShape
          have blocksShape :=
            simpleBlocks_eq_simpleBlocksFromTerminated
              (head :: tail)
          rw [shape] at blocksShape
          simp only [simpleBlocksFromTerminated,
            nonemptyTerminatedBlocks, if_neg firstNe] at blocksShape
          rw [blocksShape]
          simp
        · have firstIsEmpty : first.1 = [] := by
            change
              (terminatedBlockScan
                (head :: tail) [] (head :: tail)).1 =
                  first :: rest at shape
            simp only [terminatedBlockScan,
              if_neg initialSimple] at shape
            exact congrArg Prod.fst (List.cons.inj shape).1.symm
          have initialDecision :
              decide ((head :: tail).count head = 1) =
                false := by
            exact decide_eq_false initialSimple
          rw [initialDecision]
          exact firstIsEmpty
  refine ⟨firstEq, ?_⟩
  cases letters with
  | nil =>
      simp [terminatedBlocks, terminatedBlockScan] at shape
  | cons head tail =>
      have wordShape :
          head :: tail =
            (head :: tail).dropLast ++ [tail.getLastD head] := by
        have reconstruct :=
          (List.dropLast_concat_getLast
            (l := head :: tail) (by simp)).symm
        rw [List.getLast_eq_getLastD] at reconstruct
        simpa only [List.getLastD_cons] using reconstruct
      have blocksShape :=
        simpleBlocks_eq_simpleBlocksFromTerminated
          (head :: tail)
      rw [shape] at blocksShape
      change
        nonemptyTerminatedBlocks rest =
          let withoutInitial :=
            if decide ((head :: tail).count head = 1)
            then
              (simpleBlocks (head :: tail)).drop 1
            else
              simpleBlocks (head :: tail)
          if decide
              ((head :: tail).count (tail.getLastD head) = 1)
          then
            withoutInitial.dropLast
          else
            withoutInitial
      by_cases initialSimple :
          (head :: tail).count head = 1
      · have initialDecision :
            decide ((head :: tail).count head = 1) =
              true := by
          exact decide_eq_true initialSimple
        rw [initialDecision]
        have firstNe :
            first.1 ≠ [] := by
          have scanShape :
              (terminatedBlockScan
                (head :: tail) [head] tail).1 =
                  first :: rest := by
            simpa [terminatedBlocks, terminatedBlockScan,
              initialSimple] using shape
          exact
            terminatedBlockScan_first_block_ne_nil
              (head :: tail) [head] tail (by simp)
              first rest scanShape
        by_cases finalSimple :
            (head :: tail).count (tail.getLastD head) = 1
        · have finalDecision :
              decide
                  ((head :: tail).count
                    (tail.getLastD head) = 1) =
                true := by
            exact decide_eq_true finalSimple
          rw [finalDecision]
          have finalNe :
              terminatedFinalBlock (head :: tail) ≠ [] := by
            have endpoint :=
              terminatedBlockScan_final_ne_nil_of_last_simple
                (head :: tail) []
                (head :: tail).dropLast
                (tail.getLastD head) finalSimple
            rw [← wordShape] at endpoint
            exact endpoint
          rw [blocksShape]
          simp [simpleBlocksFromTerminated,
            nonemptyTerminatedBlocks, firstNe, finalNe]
        · have finalDecision :
              decide
                  ((head :: tail).count
                    (tail.getLastD head) = 1) =
                false := by
            exact decide_eq_false finalSimple
          rw [finalDecision]
          have finalIsEmpty :
              terminatedFinalBlock (head :: tail) = [] := by
            have endpoint :=
              terminatedBlockScan_final_eq_nil_of_last_not_simple
                (head :: tail) []
                (head :: tail).dropLast
                (tail.getLastD head) finalSimple
            rw [← wordShape] at endpoint
            exact endpoint
          rw [blocksShape]
          simp [simpleBlocksFromTerminated,
            nonemptyTerminatedBlocks, firstNe,
            finalIsEmpty]
      · have initialDecision :
            decide ((head :: tail).count head = 1) =
              false := by
          exact decide_eq_false initialSimple
        rw [initialDecision]
        have firstIsEmpty : first.1 = [] := by
          change
            (terminatedBlockScan
              (head :: tail) [] (head :: tail)).1 =
                first :: rest at shape
          simp only [terminatedBlockScan,
            if_neg initialSimple] at shape
          exact congrArg Prod.fst (List.cons.inj shape).1.symm
        by_cases finalSimple :
            (head :: tail).count (tail.getLastD head) = 1
        · have finalDecision :
              decide
                  ((head :: tail).count
                    (tail.getLastD head) = 1) =
                true := by
            exact decide_eq_true finalSimple
          rw [finalDecision]
          have finalNe :
              terminatedFinalBlock (head :: tail) ≠ [] := by
            have endpoint :=
              terminatedBlockScan_final_ne_nil_of_last_simple
                (head :: tail) []
                (head :: tail).dropLast
                (tail.getLastD head) finalSimple
            rw [← wordShape] at endpoint
            exact endpoint
          rw [blocksShape]
          simp [simpleBlocksFromTerminated,
            nonemptyTerminatedBlocks, firstIsEmpty, finalNe]
        · have finalDecision :
              decide
                  ((head :: tail).count
                    (tail.getLastD head) = 1) =
                false := by
            exact decide_eq_false finalSimple
          rw [finalDecision]
          have finalIsEmpty :
              terminatedFinalBlock (head :: tail) = [] := by
            have endpoint :=
              terminatedBlockScan_final_eq_nil_of_last_not_simple
                (head :: tail) []
                (head :: tail).dropLast
                (tail.getLastD head) finalSimple
            rw [← wordShape] at endpoint
            exact endpoint
          rw [blocksShape]
          simp [simpleBlocksFromTerminated,
            nonemptyTerminatedBlocks, firstIsEmpty,
            finalIsEmpty]

end SemigroupBasis.CoRoots.S5_107
