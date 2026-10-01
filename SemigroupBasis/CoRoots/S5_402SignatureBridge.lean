import SemigroupBasis.CoRoots.S5_402Canonical
import SemigroupBasis.CoRoots.S5_107ScannerEndpoints

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.S5_402

open SemigroupBasis

/-! ## Translating the exact S5_402 signature -/

private theorem getLastD_append_cons
    (before : List Nat) (head fallback : Nat)
    (after : List Nat) :
    (before ++ head :: after).getLastD fallback =
      after.getLastD head := by
  induction before generalizing fallback with
  | nil =>
      simp only [List.nil_append, List.getLastD_cons]
  | cons letter rest ih =>
      simp only [List.cons_append, List.getLastD_cons]
      exact ih letter

private theorem final_eq_getLastD_of_split
    (word : Word Nat) (before after : List Nat)
    (source : Nat)
    (split : word.toList = before ++ source :: after) :
    word.final = after.getLastD source := by
  cases word with
  | mk head tail =>
      have last :=
        congrArg
          (fun letters : List Nat => letters.getLastD head)
          split
      simpa only [Word.toList, Word.final,
        List.getLastD_cons, getLastD_append_cons] using last

private theorem suffix_free_of_simple_split
    (word : Word Nat) (before after : List Nat)
    (source : Nat)
    (split : word.toList = before ++ source :: after)
    (simple : GloballySimple word source) :
    source ∉ after := by
  intro member
  change word.toList.count source = 1 at simple
  have positive : 0 < after.count source :=
    List.count_pos_iff.mpr member
  rw [split, List.count_append, List.count_cons_self] at simple
  omega

/-- A globally simple variable is final exactly when it has no immediate
successor. This is the endpoint information implicit in the S5_402
successor signature. -/
theorem simpleFinal_iff_noImmediateSuccessor
    (word : Word Nat) (source : Nat) :
    S5_107.SimpleFinal word source ↔
      GloballySimple word source ∧
        ∀ target, ¬ImmediateSuccessor word source target := by
  constructor
  · rintro ⟨simple, finalEqual⟩
    refine ⟨simple, ?_⟩
    intro target successor
    obtain ⟨before, after, split⟩ :=
      (S5_107.mem_adjacentPairs_iff_exists_split
        source target word).mp successor.2.2
    have suffixFree :=
      suffix_free_of_simple_split
        word before (target :: after) source split simple
    have finalAtSuffix :=
      final_eq_getLastD_of_split
        word before (target :: after) source split
    have finalMember :
        (target :: after).getLastD source ∈ target :: after := by
      simpa only [List.getLastD_cons] using
        (List.getLastD_mem_cons (l := after) (a := target))
    apply suffixFree
    rw [← finalEqual, finalAtSuffix]
    exact finalMember
  · rintro ⟨simple, noSuccessor⟩
    refine ⟨simple, ?_⟩
    have sourceCount : word.toList.count source = 1 := by
      simpa only [GloballySimple] using simple
    have sourceMember : source ∈ word.toList :=
      List.count_pos_iff.mp (by omega)
    obtain ⟨before, after, split⟩ :=
      List.mem_iff_append.mp sourceMember
    have suffixFree :=
      suffix_free_of_simple_split
        word before after source split simple
    cases after with
    | nil =>
        simpa using
          final_eq_getLastD_of_split
            word before [] source split
    | cons target rest =>
        have different : source ≠ target := by
          intro equal
          apply suffixFree
          simp [equal]
        exfalso
        exact noSuccessor target
          ⟨different, simple,
            (S5_107.mem_adjacentPairs_iff_exists_split
              source target word).mpr
                ⟨before, rest, split⟩⟩

private theorem simple_source_ne_adjacent_target
    (word : Word Nat) (source target : Nat)
    (sourceSimple : GloballySimple word source)
    (adjacent : (source, target) ∈ word.adjacentPairs) :
    source ≠ target := by
  intro equal
  subst target
  change word.toList.count source = 1 at sourceSimple
  obtain ⟨before, after, split⟩ :=
    (S5_107.mem_adjacentPairs_iff_exists_split
      source source word).mp adjacent
  have repeated :
      2 ≤ (before ++ source :: source :: after).count source := by
    simp [List.count_append]
    omega
  rw [split] at sourceSimple
  omega

/-- The S5_402 capped/head/simple-successor signature contains the complete
S5_107 simple-adjacency signature. -/
theorem SameSimpleSuccessorSignature.toSimpleAdjacencySignature
    {left right : Word Nat}
    (same : SameSimpleSuccessorSignature left right) :
    S5_107.SameSimpleAdjacencySignature left right := by
  refine
    { capped := same.capped
      initial := ?_
      final := ?_
      adjacent := ?_ }
  · intro letter
    constructor
    · rintro ⟨simple, initial⟩
      exact
        ⟨(same.globallySimple letter).mp simple,
          same.head.symm.trans initial⟩
    · rintro ⟨simple, initial⟩
      exact
        ⟨(same.globallySimple letter).mpr simple,
          same.head.trans initial⟩
  · intro letter
    simp only [simpleFinal_iff_noImmediateSuccessor]
    constructor
    · rintro ⟨simple, noSuccessor⟩
      refine ⟨(same.globallySimple letter).mp simple, ?_⟩
      intro target rightSuccessor
      exact noSuccessor target <|
        (same.successor letter target).mpr rightSuccessor
    · rintro ⟨simple, noSuccessor⟩
      refine ⟨(same.globallySimple letter).mpr simple, ?_⟩
      intro target leftSuccessor
      exact noSuccessor target <|
        (same.successor letter target).mp leftSuccessor
  · intro source target
    constructor
    · rintro ⟨sourceSimple, targetSimple, adjacent⟩
      have different :=
        simple_source_ne_adjacent_target
          left source target sourceSimple adjacent
      have successor :=
        (same.successor source target).mp
          ⟨different, sourceSimple, adjacent⟩
      exact
        ⟨(same.globallySimple source).mp sourceSimple,
          (same.globallySimple target).mp targetSimple,
          successor.2.2⟩
    · rintro ⟨sourceSimple, targetSimple, adjacent⟩
      have different :=
        simple_source_ne_adjacent_target
          right source target sourceSimple adjacent
      have successor :=
        (same.successor source target).mpr
          ⟨different, sourceSimple, adjacent⟩
      exact
        ⟨(same.globallySimple source).mpr sourceSimple,
          (same.globallySimple target).mpr targetSimple,
          successor.2.2⟩

/-! ## Aligning the local scanner with established combinatorics -/

/-- The local S5_402 terminated scanner is definitionally parallel to the
established S5_107 scanner. -/
theorem terminatedBlockScan_eq_s5_107
    (whole current remaining : List Nat) :
    terminatedBlockScan whole current remaining =
      S5_107.terminatedBlockScan whole current remaining := by
  induction remaining generalizing current with
  | nil =>
      rfl
  | cons letter rest ih =>
      by_cases simple : whole.count letter = 1
      · simpa [terminatedBlockScan,
          S5_107.terminatedBlockScan, simple] using
            ih (letter :: current)
      · simp only [terminatedBlockScan,
          S5_107.terminatedBlockScan, simple, if_false]
        rw [ih ([] : List Nat)]

theorem terminatedBlocks_eq_s5_107 (letters : List Nat) :
    terminatedBlocks letters = S5_107.terminatedBlocks letters := by
  simpa [terminatedBlocks, S5_107.terminatedBlocks] using
    congrArg Prod.fst
      (terminatedBlockScan_eq_s5_107 letters [] letters)

theorem terminatedFinalBlock_eq_s5_107 (letters : List Nat) :
    terminatedFinalBlock letters =
      S5_107.terminatedFinalBlock letters := by
  simpa [terminatedFinalBlock, S5_107.terminatedFinalBlock] using
    congrArg Prod.snd
      (terminatedBlockScan_eq_s5_107 letters [] letters)

private theorem listAdjacent_target_unique_of_count_one
    (source : Nat) :
    ∀ (letters : List Nat) (leftTarget rightTarget : Nat),
      letters.count source = 1 →
      (source, leftTarget) ∈ S5_107.listAdjacentPairs letters →
      (source, rightTarget) ∈ S5_107.listAdjacentPairs letters →
      leftTarget = rightTarget
  | [], leftTarget, rightTarget, _, leftEdge, _ => by
      simp at leftEdge
  | [letter], leftTarget, rightTarget, _, leftEdge, _ => by
      simp at leftEdge
  | first :: second :: rest,
      leftTarget, rightTarget, countOne, leftEdge, rightEdge => by
      simp only [S5_107.listAdjacentPairs_cons_cons,
        List.mem_cons, Prod.mk.injEq] at leftEdge rightEdge
      by_cases firstSource : first = source
      · subst first
        have tailAbsent : source ∉ second :: rest := by
          apply List.count_eq_zero.mp
          simp only [List.count_cons_self] at countOne
          omega
        have noTail :
            ∀ target,
              (source, target) ∉
                S5_107.listAdjacentPairs (second :: rest) := by
          intro target edge
          obtain ⟨before, after, split⟩ :=
            (S5_107.mem_listAdjacentPairs_iff_exists_split
              source target (second :: rest)).mp edge
          apply tailAbsent
          rw [split]
          simp
        rcases leftEdge with leftFirst | leftTail
        · rcases rightEdge with rightFirst | rightTail
          · exact leftFirst.2.trans rightFirst.2.symm
          · exact False.elim (noTail rightTarget rightTail)
        · exact False.elim (noTail leftTarget leftTail)
      · have tailCount : (second :: rest).count source = 1 := by
          simpa [firstSource] using countOne
        have leftTail :
            (source, leftTarget) ∈
              S5_107.listAdjacentPairs (second :: rest) := by
          rcases leftEdge with leftFirst | leftTail
          · exact False.elim (firstSource leftFirst.1.symm)
          · exact leftTail
        have rightTail :
            (source, rightTarget) ∈
              S5_107.listAdjacentPairs (second :: rest) := by
          rcases rightEdge with rightFirst | rightTail
          · exact False.elim (firstSource rightFirst.1.symm)
          · exact rightTail
        exact listAdjacent_target_unique_of_count_one source
          (second :: rest) leftTarget rightTarget
          tailCount leftTail rightTail

private theorem immediateSuccessor_target_unique
    (word : Word Nat) (source leftTarget rightTarget : Nat)
    (leftSuccessor : ImmediateSuccessor word source leftTarget)
    (rightSuccessor : ImmediateSuccessor word source rightTarget) :
    leftTarget = rightTarget := by
  apply listAdjacent_target_unique_of_count_one
    source word.toList leftTarget rightTarget leftSuccessor.2.1
  · rw [S5_107.listAdjacentPairs_toList]
    exact leftSuccessor.2.2
  · rw [S5_107.listAdjacentPairs_toList]
    exact rightSuccessor.2.2

private theorem sortedTerminatedBlocks_cons_raw
    (letters : List Nat) (first : List Nat × Nat)
    (rest : List (List Nat × Nat))
    (shape : sortedTerminatedBlocks letters = first :: rest) :
    ∃ rawRest,
      terminatedBlocks letters = first :: rawRest ∧
        rest.Perm rawRest := by
  cases rawShape : terminatedBlocks letters with
  | nil =>
      simp [sortedTerminatedBlocks, rawShape] at shape
  | cons rawFirst rawRest =>
      have expanded :
          rawFirst :: sortedTerminatedTail rawRest = first :: rest := by
        simpa [sortedTerminatedBlocks, rawShape] using shape
      have firstEqual := (List.cons.inj expanded).1
      have restEqual := (List.cons.inj expanded).2
      refine ⟨rawRest, ?_, ?_⟩
      · simpa [firstEqual] using rawShape
      · rw [← restEqual]
        exact sortedTerminatedTail_perm rawRest

private theorem sortedTerminatedBlocks_cons_raw_exact
    (letters : List Nat) (first : List Nat × Nat)
    (rest : List (List Nat × Nat))
    (shape : sortedTerminatedBlocks letters = first :: rest) :
    ∃ rawRest,
      terminatedBlocks letters = first :: rawRest ∧
        rest = sortedTerminatedTail rawRest := by
  cases rawShape : terminatedBlocks letters with
  | nil =>
      simp [sortedTerminatedBlocks, rawShape] at shape
  | cons rawFirst rawRest =>
      have expanded :
          rawFirst :: sortedTerminatedTail rawRest = first :: rest := by
        simpa [sortedTerminatedBlocks, rawShape] using shape
      have firstEqual := (List.cons.inj expanded).1
      have restEqual := (List.cons.inj expanded).2
      exact ⟨rawRest, by simpa [firstEqual] using rawShape,
        restEqual.symm⟩

private theorem blockLast_mem
    (block : List Nat) (nonempty : block ≠ []) :
    block.getLastD 0 ∈ block := by
  obtain ⟨head, tail, rfl⟩ :=
    List.exists_cons_of_ne_nil nonempty
  simpa only [List.getLastD_cons] using
    (List.getLastD_mem_cons (l := tail) (a := head))

private theorem terminatedFactor_immediateSuccessor
    (word : Word Nat) (block : List Nat) (marker : Nat)
    (member : (block, marker) ∈ terminatedBlocks word.toList)
    (nonempty : block ≠ []) :
    ImmediateSuccessor word (block.getLastD 0) marker := by
  let source := block.getLastD 0
  have sourceMember : source ∈ block := blockLast_mem block nonempty
  have sourceSimple : word.toList.count source = 1 :=
    terminatedBlocks_block_simple word.toList (block, marker)
      member source sourceMember
  have markerMultiple : 2 ≤ word.toList.count marker :=
    terminatedBlocks_marker_multiple word.toList (block, marker) member
  have different : source ≠ marker := by
    intro equal
    subst marker
    omega
  obtain ⟨before, after, factorSplit⟩ :=
    List.mem_iff_append.mp member
  have reconstruction :
      block.dropLast ++ [source] = block := by
    have rebuilt :
        block.dropLast ++ [block.getLastD 0] = block := by
      obtain ⟨head, tail, rfl⟩ :=
        List.exists_cons_of_ne_nil nonempty
      have last :=
        List.dropLast_concat_getLast
          (l := head :: tail) (by simp)
      rw [List.getLast_eq_getLastD] at last
      simpa only [List.getLastD_cons] using last
    simpa [source] using rebuilt
  have literal := terminatedBlocks_render word.toList
  rw [factorSplit] at literal
  have split :
      word.toList =
        (renderTerminatedBlocks before ++ block.dropLast) ++
          source :: marker ::
            (renderTerminatedBlocks after ++
              terminatedFinalBlock word.toList) := by
    calc
      word.toList =
          renderTerminatedBlocks
              (before ++ (block, marker) :: after) ++
            terminatedFinalBlock word.toList := literal.symm
      _ =
          (renderTerminatedBlocks before ++ block.dropLast) ++
            source :: marker ::
              (renderTerminatedBlocks after ++
                terminatedFinalBlock word.toList) := by
        have expanded :=
          congrArg
            (fun middle =>
              (renderTerminatedBlocks before ++ middle) ++
                marker ::
                  (renderTerminatedBlocks after ++
                    terminatedFinalBlock word.toList))
            reconstruction.symm
        simpa [renderTerminatedBlocks_append, renderTerminatedBlocks,
          List.append_assoc] using expanded
  exact
    ⟨different, sourceSimple,
      (S5_107.mem_adjacentPairs_iff_exists_split
        source marker word).mpr
          ⟨renderTerminatedBlocks before ++ block.dropLast,
            renderTerminatedBlocks after ++
              terminatedFinalBlock word.toList,
            split⟩⟩

private theorem sortedTail_blockBearingBlocks_perm_interior
    (word : Word Nat) (first : List Nat × Nat)
    (rest : List (List Nat × Nat))
    (shape : sortedTerminatedBlocks word.toList = first :: rest) :
    ((blockBearingFactors rest).map fun factor => factor.1).Perm
      (S5_107.interiorSimpleBlocks word.toList) := by
  obtain ⟨rawRest, rawShape, tailPermutation⟩ :=
    sortedTerminatedBlocks_cons_raw word.toList first rest shape
  have rawShape107 :
      S5_107.terminatedBlocks word.toList = first :: rawRest := by
    rw [← terminatedBlocks_eq_s5_107]
    exact rawShape
  have endpoint :=
    S5_107.terminatedBlocks_cons_endpoint_blocks
      word.toList first rawRest rawShape107
  have rawBlocks :
      (blockBearingFactors rawRest).map (fun factor => factor.1) =
        S5_107.interiorSimpleBlocks word.toList := by
    calc
      (blockBearingFactors rawRest).map (fun factor => factor.1) =
          S5_107.terminatedFactorBlocks
            (S5_107.blockBearingFactors rawRest) := by rfl
      _ = S5_107.nonemptyTerminatedBlocks rawRest :=
        S5_107.terminatedFactorBlocks_blockBearingFactors rawRest
      _ = S5_107.interiorSimpleBlocks word.toList := endpoint.2
  have filtered :=
    tailPermutation.filter
      (fun factor : List Nat × Nat => decide (factor.1 ≠ []))
  have mapped := filtered.map (fun factor => factor.1)
  change
    ((blockBearingFactors rest).map (fun factor => factor.1)).Perm
      ((blockBearingFactors rawRest).map (fun factor => factor.1)) at mapped
  rw [rawBlocks] at mapped
  exact mapped

private theorem mem_blockBearing_sortedTail_iff
    (word : Word Nat) (first : List Nat × Nat)
    (rest : List (List Nat × Nat))
    (shape : sortedTerminatedBlocks word.toList = first :: rest)
    (block : List Nat) (marker : Nat) (nonempty : block ≠ []) :
    (block, marker) ∈ blockBearingFactors rest ↔
      block ∈ S5_107.interiorSimpleBlocks word.toList ∧
        ImmediateSuccessor word (block.getLastD 0) marker := by
  obtain ⟨rawRest, rawShape, tailPermutation⟩ :=
    sortedTerminatedBlocks_cons_raw word.toList first rest shape
  have blocksPermutation :=
    sortedTail_blockBearingBlocks_perm_interior
      word first rest shape
  constructor
  · intro member
    have restMember : (block, marker) ∈ rest :=
      (List.mem_filter.mp member).1
    have rawMember : (block, marker) ∈ rawRest :=
      tailPermutation.mem_iff.mp restMember
    have completeMember :
        (block, marker) ∈ terminatedBlocks word.toList := by
      rw [rawShape]
      simp [rawMember]
    exact
      ⟨blocksPermutation.mem_iff.mp
          (List.mem_map_of_mem member),
        terminatedFactor_immediateSuccessor
          word block marker completeMember nonempty⟩
  · rintro ⟨interiorMember, successor⟩
    have mappedMember :
        block ∈ (blockBearingFactors rest).map
          (fun factor => factor.1) :=
      blocksPermutation.mem_iff.mpr interiorMember
    rcases List.mem_map.mp mappedMember with
      ⟨factor, factorMember, factorBlock⟩
    rcases factor with ⟨witnessBlock, witnessMarker⟩
    simp only at factorBlock
    subst witnessBlock
    have restMember : (block, witnessMarker) ∈ rest :=
      (List.mem_filter.mp factorMember).1
    have rawMember : (block, witnessMarker) ∈ rawRest :=
      tailPermutation.mem_iff.mp restMember
    have completeMember :
        (block, witnessMarker) ∈ terminatedBlocks word.toList := by
      rw [rawShape]
      simp [rawMember]
    have witnessSuccessor :=
      terminatedFactor_immediateSuccessor
        word block witnessMarker completeMember nonempty
    have markerEqual :=
      immediateSuccessor_target_unique
        word (block.getLastD 0) witnessMarker marker
        witnessSuccessor successor
    subst witnessMarker
    exact factorMember

private theorem nodup_of_map_nodup
    {alpha beta : Type} (project : alpha → beta) :
    ∀ {items : List alpha},
      (items.map project).Nodup → items.Nodup
  | [], _ => by simp
  | item :: rest, mappedNodup => by
      simp only [List.map_cons, List.nodup_cons] at mappedNodup ⊢
      exact
        ⟨fun member => mappedNodup.1 <|
            List.mem_map_of_mem member,
          nodup_of_map_nodup project mappedNodup.2⟩

private theorem blockBearing_sortedTail_nodup
    (word : Word Nat) (first : List Nat × Nat)
    (rest : List (List Nat × Nat))
    (shape : sortedTerminatedBlocks word.toList = first :: rest) :
    (blockBearingFactors rest).Nodup := by
  apply nodup_of_map_nodup (fun factor : List Nat × Nat => factor.1)
  exact
    (sortedTail_blockBearingBlocks_perm_interior
      word first rest shape).nodup_iff.mpr
        (S5_107.interiorSimpleBlocks_nodup word.toList)

private theorem firstMarker_eq_head_of_block_empty
    (word : Word Nat) (marker : Nat)
    (rest : List (List Nat × Nat))
    (shape : terminatedBlocks word.toList = ([], marker) :: rest) :
    marker = word.head := by
  have literal := terminatedBlocks_render word.toList
  rw [shape] at literal
  have heads := congrArg List.head? literal
  simpa [renderTerminatedBlocks, Word.toList] using heads

private theorem sortedFirstFactor_eq_of_sameSignature
    {left right : Word Nat}
    (same : SameSimpleSuccessorSignature left right)
    (leftFirst rightFirst : List Nat × Nat)
    (leftRest rightRest : List (List Nat × Nat))
    (leftShape :
      sortedTerminatedBlocks left.toList = leftFirst :: leftRest)
    (rightShape :
      sortedTerminatedBlocks right.toList = rightFirst :: rightRest) :
    leftFirst = rightFirst := by
  obtain ⟨leftRaw, leftRawShape, _⟩ :=
    sortedTerminatedBlocks_cons_raw
      left.toList leftFirst leftRest leftShape
  obtain ⟨rightRaw, rightRawShape, _⟩ :=
    sortedTerminatedBlocks_cons_raw
      right.toList rightFirst rightRest rightShape
  have leftRawShape107 :
      S5_107.terminatedBlocks left.toList = leftFirst :: leftRaw := by
    rw [← terminatedBlocks_eq_s5_107]
    exact leftRawShape
  have rightRawShape107 :
      S5_107.terminatedBlocks right.toList = rightFirst :: rightRaw := by
    rw [← terminatedBlocks_eq_s5_107]
    exact rightRawShape
  have leftEndpoint :=
    S5_107.terminatedBlocks_cons_endpoint_blocks
      left.toList leftFirst leftRaw leftRawShape107
  have rightEndpoint :=
    S5_107.terminatedBlocks_cons_endpoint_blocks
      right.toList rightFirst rightRaw rightRawShape107
  have blockEqual : leftFirst.1 = rightFirst.1 :=
    leftEndpoint.1.trans <|
      (S5_107.SameSimpleAdjacencySignature.initialSimpleBlock_eq
        (SameSimpleSuccessorSignature.toSimpleAdjacencySignature same)).trans
        rightEndpoint.1.symm
  rcases leftFirst with ⟨leftBlock, leftMarker⟩
  rcases rightFirst with ⟨rightBlock, rightMarker⟩
  simp only at blockEqual
  subst rightBlock
  by_cases blockEmpty : leftBlock = []
  · subst leftBlock
    have leftHead :=
      firstMarker_eq_head_of_block_empty
        left leftMarker leftRaw leftRawShape
    have rightHead :=
      firstMarker_eq_head_of_block_empty
        right rightMarker rightRaw rightRawShape
    have markerEqual : leftMarker = rightMarker :=
      leftHead.trans <| same.head.trans rightHead.symm
    exact congrArg (fun marker => ([], marker)) markerEqual
  · have leftSuccessor :=
      terminatedFactor_immediateSuccessor
        left leftBlock leftMarker (by rw [leftRawShape]; simp) blockEmpty
    have rightSuccessor :=
      terminatedFactor_immediateSuccessor
        right leftBlock rightMarker (by rw [rightRawShape]; simp) blockEmpty
    have transported :=
      (same.successor (leftBlock.getLastD 0) leftMarker).mp
        leftSuccessor
    have markerEqual :=
      immediateSuccessor_target_unique
        right (leftBlock.getLastD 0) leftMarker rightMarker
        transported rightSuccessor
    subst rightMarker
    rfl

private theorem blockBearing_sortedTails_perm_of_sameSignature
    {left right : Word Nat}
    (same : SameSimpleSuccessorSignature left right)
    (leftFirst rightFirst : List Nat × Nat)
    (leftRest rightRest : List (List Nat × Nat))
    (leftShape :
      sortedTerminatedBlocks left.toList = leftFirst :: leftRest)
    (rightShape :
      sortedTerminatedBlocks right.toList = rightFirst :: rightRest) :
    (blockBearingFactors leftRest).Perm
      (blockBearingFactors rightRest) := by
  have adjacencySame :=
    SameSimpleSuccessorSignature.toSimpleAdjacencySignature same
  have sameMembership :
      ∀ factor,
        factor ∈ blockBearingFactors leftRest ↔
          factor ∈ blockBearingFactors rightRest := by
    intro factor
    rcases factor with ⟨block, marker⟩
    constructor
    · intro member
      have nonempty :=
        blockBearingFactors_blocks_nonempty
          leftRest (block, marker) member
      have data :=
        (mem_blockBearing_sortedTail_iff
          left leftFirst leftRest leftShape
          block marker nonempty).mp member
      apply (mem_blockBearing_sortedTail_iff
        right rightFirst rightRest rightShape
        block marker nonempty).mpr
      exact
        ⟨adjacencySame.interiorSimpleBlocks_perm.mem_iff.mp data.1,
          (same.successor (block.getLastD 0) marker).mp data.2⟩
    · intro member
      have nonempty :=
        blockBearingFactors_blocks_nonempty
          rightRest (block, marker) member
      have data :=
        (mem_blockBearing_sortedTail_iff
          right rightFirst rightRest rightShape
          block marker nonempty).mp member
      apply (mem_blockBearing_sortedTail_iff
        left leftFirst leftRest leftShape
        block marker nonempty).mpr
      exact
        ⟨adjacencySame.interiorSimpleBlocks_perm.mem_iff.mpr data.1,
          (same.successor (block.getLastD 0) marker).mpr data.2⟩
  have leftNodup :=
    blockBearing_sortedTail_nodup left leftFirst leftRest leftShape
  have rightNodup :=
    blockBearing_sortedTail_nodup right rightFirst rightRest rightShape
  rw [List.perm_iff_count]
  intro factor
  rw [leftNodup.count, rightNodup.count]
  simpa only [sameMembership factor]

/-- Equal S5_402 signatures determine the trailing simple block exactly. -/
theorem terminatedFinalBlock_eq_of_sameSignature
    {left right : Word Nat}
    (same : SameSimpleSuccessorSignature left right) :
    terminatedFinalBlock left.toList =
      terminatedFinalBlock right.toList := by
  rw [terminatedFinalBlock_eq_s5_107,
    terminatedFinalBlock_eq_s5_107,
    S5_107.terminatedFinalBlock_eq_finalSimpleBlock,
    S5_107.terminatedFinalBlock_eq_finalSimpleBlock]
  exact S5_107.SameSimpleAdjacencySignature.finalSimpleBlock_eq
    (SameSimpleSuccessorSignature.toSimpleAdjacencySignature same)

/-- Equal S5_402 signatures determine the multiset of maximal simple blocks. -/
theorem simpleBlocks_perm_of_sameSignature
    {left right : Word Nat}
    (same : SameSimpleSuccessorSignature left right) :
    (S5_107.simpleBlocks left.toList).Perm
      (S5_107.simpleBlocks right.toList) :=
  S5_107.SameSimpleAdjacencySignature.simpleBlocks_perm
    (SameSimpleSuccessorSignature.toSimpleAdjacencySignature same)

/-- Equal S5_402 signatures determine the initial maximal simple block. -/
theorem initialSimpleBlock_eq_of_sameSignature
    {left right : Word Nat}
    (same : SameSimpleSuccessorSignature left right) :
    S5_107.initialSimpleBlock left.toList =
      S5_107.initialSimpleBlock right.toList :=
  S5_107.SameSimpleAdjacencySignature.initialSimpleBlock_eq
    (SameSimpleSuccessorSignature.toSimpleAdjacencySignature same)

/-- Equal S5_402 signatures determine the sorted multiple-letter support. -/
theorem sortedMultipleLetters_eq_of_sameSignature
    {left right : Word Nat}
    (same : SameSimpleSuccessorSignature left right) :
    S5_107.sortedMultipleLetters left.toList =
      S5_107.sortedMultipleLetters right.toList :=
  S5_107.SameSimpleAdjacencySignature.sortedMultipleLetters_eq
    (SameSimpleSuccessorSignature.toSimpleAdjacencySignature same)

private theorem sortedTerminatedBlocks_ne_nil_of_multiple
    (letters : List Nat) (marker : Nat)
    (multiple : 2 ≤ letters.count marker) :
    sortedTerminatedBlocks letters ≠ [] := by
  have markerMember :
      marker ∈ S5_107.terminatedFactorMarkers
        (S5_107.terminatedBlocks letters) :=
    (S5_107.mem_terminatedFactorMarkers_iff marker letters).mpr multiple
  have rawNonempty : terminatedBlocks letters ≠ [] := by
    intro empty
    rw [← terminatedBlocks_eq_s5_107, empty] at markerMember
    simp [S5_107.terminatedFactorMarkers] at markerMember
  cases rawShape : terminatedBlocks letters with
  | nil => exact False.elim (rawNonempty rawShape)
  | cons first rest =>
      simp [sortedTerminatedBlocks, rawShape]

/-- The fixed first factor and every sorted noninitial block-bearing
simple-successor factor are determined literally by the exact table
signature. -/
theorem retainedSortedFactors_eq_of_sameSignature
    {left right : Word Nat}
    (same : SameSimpleSuccessorSignature left right) :
    retainedSortedFactors left.toList =
      retainedSortedFactors right.toList := by
  have adjacencySame :=
    SameSimpleSuccessorSignature.toSimpleAdjacencySignature same
  cases leftShape : sortedTerminatedBlocks left.toList with
  | nil =>
      cases rightShape : sortedTerminatedBlocks right.toList with
      | nil =>
          simp [retainedSortedFactors, leftShape, rightShape]
      | cons rightFirst rightRest =>
          obtain ⟨rightRaw, rightRawShape, _⟩ :=
            sortedTerminatedBlocks_cons_raw
              right.toList rightFirst rightRest rightShape
          have rightMultiple :
              2 ≤ right.toList.count rightFirst.2 :=
            terminatedBlocks_marker_multiple
              right.toList rightFirst (by rw [rightRawShape]; simp)
          have leftMultiple :
              2 ≤ left.toList.count rightFirst.2 :=
            (adjacencySame.multiple rightFirst.2).mpr rightMultiple
          exact False.elim <|
            (sortedTerminatedBlocks_ne_nil_of_multiple
              left.toList rightFirst.2 leftMultiple) leftShape
  | cons leftFirst leftRest =>
      cases rightShape : sortedTerminatedBlocks right.toList with
      | nil =>
          obtain ⟨leftRaw, leftRawShape, _⟩ :=
            sortedTerminatedBlocks_cons_raw
              left.toList leftFirst leftRest leftShape
          have leftMultiple :
              2 ≤ left.toList.count leftFirst.2 :=
            terminatedBlocks_marker_multiple
              left.toList leftFirst (by rw [leftRawShape]; simp)
          have rightMultiple :
              2 ≤ right.toList.count leftFirst.2 :=
            (adjacencySame.multiple leftFirst.2).mp leftMultiple
          exact False.elim <|
            (sortedTerminatedBlocks_ne_nil_of_multiple
              right.toList leftFirst.2 rightMultiple) rightShape
      | cons rightFirst rightRest =>
          have firstEqual :=
            sortedFirstFactor_eq_of_sameSignature
              same leftFirst rightFirst leftRest rightRest
              leftShape rightShape
          obtain ⟨leftRaw, _, leftRestShape⟩ :=
            sortedTerminatedBlocks_cons_raw_exact
              left.toList leftFirst leftRest leftShape
          obtain ⟨rightRaw, _, rightRestShape⟩ :=
            sortedTerminatedBlocks_cons_raw_exact
              right.toList rightFirst rightRest rightShape
          have tailPermutation :=
            blockBearing_sortedTails_perm_of_sameSignature
              same leftFirst rightFirst leftRest rightRest
              leftShape rightShape
          have sortedEqual :=
            sortedTerminatedFactors_eq_of_perm tailPermutation
          have leftProjection :
              blockBearingFactors leftRest =
                sortedTerminatedFactors
                  (blockBearingFactors leftRaw) := by
            rw [leftRestShape,
              blockBearingFactors_sortedTerminatedTail]
          have rightProjection :
              blockBearingFactors rightRest =
                sortedTerminatedFactors
                  (blockBearingFactors rightRaw) := by
            rw [rightRestShape,
              blockBearingFactors_sortedTerminatedTail]
          have leftFixed :
              sortedTerminatedFactors
                  (blockBearingFactors leftRest) =
                blockBearingFactors leftRest := by
            calc
              sortedTerminatedFactors (blockBearingFactors leftRest) =
                  sortedTerminatedFactors
                    (sortedTerminatedFactors
                      (blockBearingFactors leftRaw)) :=
                congrArg sortedTerminatedFactors leftProjection
              _ = sortedTerminatedFactors
                    (blockBearingFactors leftRaw) :=
                sortedTerminatedFactors_idempotent _
              _ = blockBearingFactors leftRest := leftProjection.symm
          have rightFixed :
              sortedTerminatedFactors
                  (blockBearingFactors rightRest) =
                blockBearingFactors rightRest := by
            calc
              sortedTerminatedFactors (blockBearingFactors rightRest) =
                  sortedTerminatedFactors
                    (sortedTerminatedFactors
                      (blockBearingFactors rightRaw)) :=
                congrArg sortedTerminatedFactors rightProjection
              _ = sortedTerminatedFactors
                    (blockBearingFactors rightRaw) :=
                sortedTerminatedFactors_idempotent _
              _ = blockBearingFactors rightRest := rightProjection.symm
          have tailsEqual :
              blockBearingFactors leftRest =
                blockBearingFactors rightRest :=
            leftFixed.symm.trans (sortedEqual.trans rightFixed)
          unfold retainedSortedFactors
          rw [leftShape, rightShape, firstEqual]
          change
            rightFirst :: blockBearingFactors leftRest =
              rightFirst :: blockBearingFactors rightRest
          rw [tailsEqual]

private theorem markerOnlyLabel_iff_multiple_of_not_retained
    (word : Word Nat) (first : List Nat × Nat)
    (rest : List (List Nat × Nat))
    (shape : sortedTerminatedBlocks word.toList = first :: rest)
    (marker : Nat)
    (notRetained :
      marker ∉ terminatedFactorMarkers
        (first :: blockBearingFactors rest)) :
    marker ∈ terminatedFactorMarkers (markerOnlyFactors rest) ↔
      2 ≤ word.toList.count marker := by
  obtain ⟨rawRest, rawShape, tailPermutation⟩ :=
    sortedTerminatedBlocks_cons_raw word.toList first rest shape
  have rawShape107 :
      S5_107.terminatedBlocks word.toList = first :: rawRest := by
    rw [← terminatedBlocks_eq_s5_107]
    exact rawShape
  constructor
  · intro labelMember
    change marker ∈
      (markerOnlyFactors rest).map
        (fun factor : List Nat × Nat => factor.2) at labelMember
    rcases List.mem_map.mp labelMember with
      ⟨factor, factorMember, factorMarker⟩
    rcases factor with ⟨block, witnessMarker⟩
    simp only at factorMarker
    subst witnessMarker
    have restMember : (block, marker) ∈ rest :=
      (List.mem_filter.mp factorMember).1
    have rawMember : (block, marker) ∈ rawRest :=
      tailPermutation.mem_iff.mp restMember
    exact terminatedBlocks_marker_multiple
      word.toList (block, marker) (by rw [rawShape]; simp [rawMember])
  · intro multiple
    obtain ⟨factor, rawMember, factorMarker⟩ :=
      S5_107.exists_tail_factor_with_marker_of_multiple
        word.toList first rawRest marker rawShape107 multiple
    rcases factor with ⟨block, witnessMarker⟩
    simp only at factorMarker
    subst witnessMarker
    have restMember : (block, marker) ∈ rest :=
      tailPermutation.mem_iff.mpr rawMember
    by_cases blockEmpty : block = []
    · subst block
      have markerOnlyMember :
          ([], marker) ∈ markerOnlyFactors rest := by
        simp [markerOnlyFactors, restMember]
      change marker ∈
        (markerOnlyFactors rest).map
          (fun factor : List Nat × Nat => factor.2)
      exact
        List.mem_map_of_mem markerOnlyMember
    · have blockBearingMember :
          (block, marker) ∈ blockBearingFactors rest := by
        simp [blockBearingFactors, restMember, blockEmpty]
      apply False.elim
      apply notRetained
      simp only [terminatedFactorMarkers, List.map_cons,
        List.mem_cons]
      exact Or.inr <|
        List.mem_map_of_mem blockBearingMember

/-- Exact combinatorial boundary for the canonical factor inventory. The
concrete scanner proof below supplies this record unconditionally. -/
structure CanonicalFactorInventorySignatureObligation : Prop where
  inventoryEqual :
    ∀ {left right : Word Nat},
      SameSimpleSuccessorSignature left right →
        canonicalSquaredFactorInventory left.toList =
          canonicalSquaredFactorInventory right.toList

/-- Equal exact table signatures give literal equality of the raw canonical
factor inventories, including the filtered marker-only square bank. -/
theorem canonicalSquaredFactorInventory_eq_of_sameSignature
    {left right : Word Nat}
    (same : SameSimpleSuccessorSignature left right) :
    canonicalSquaredFactorInventory left.toList =
      canonicalSquaredFactorInventory right.toList := by
  have retainedEqual := retainedSortedFactors_eq_of_sameSignature same
  have adjacencySame :=
    SameSimpleSuccessorSignature.toSimpleAdjacencySignature same
  cases leftShape : sortedTerminatedBlocks left.toList with
  | nil =>
      cases rightShape : sortedTerminatedBlocks right.toList with
      | nil =>
          simp [canonicalSquaredFactorInventory, leftShape, rightShape]
      | cons rightFirst rightRest =>
          have impossible :
              ([] : List (List Nat × Nat)) =
                rightFirst :: blockBearingFactors rightRest := by
            simpa [retainedSortedFactors, leftShape, rightShape] using
              retainedEqual
          simp at impossible
  | cons leftFirst leftRest =>
      cases rightShape : sortedTerminatedBlocks right.toList with
      | nil =>
          have impossible :
              leftFirst :: blockBearingFactors leftRest =
                ([] : List (List Nat × Nat)) := by
            simpa [retainedSortedFactors, leftShape, rightShape] using
              retainedEqual
          simp at impossible
      | cons rightFirst rightRest =>
          have retainedEqual' :
              leftFirst :: blockBearingFactors leftRest =
                rightFirst :: blockBearingFactors rightRest := by
            simpa [retainedSortedFactors, leftShape, rightShape] using
              retainedEqual
          have protectedEqual :=
            congrArg terminatedFactorMarkers retainedEqual'
          let leftLabels :=
            terminatedFactorMarkers (markerOnlyFactors leftRest)
          let rightLabels :=
            terminatedFactorMarkers (markerOnlyFactors rightRest)
          have bankEqual :
              canonicalMarkerBank
                  (terminatedFactorMarkers
                    (leftFirst :: blockBearingFactors leftRest))
                  leftLabels =
                canonicalMarkerBank
                  (terminatedFactorMarkers
                    (rightFirst :: blockBearingFactors rightRest))
                  rightLabels := by
            rw [← protectedEqual]
            apply canonicalMarkerBank_eq_of_residual_mem_iff
            intro marker notRetained
            have leftCharacterization :=
              markerOnlyLabel_iff_multiple_of_not_retained
                left leftFirst leftRest leftShape marker notRetained
            have notRightRetained :
                marker ∉ terminatedFactorMarkers
                  (rightFirst :: blockBearingFactors rightRest) := by
              rwa [← protectedEqual]
            have rightCharacterization :=
              markerOnlyLabel_iff_multiple_of_not_retained
                right rightFirst rightRest rightShape marker
                notRightRetained
            exact leftCharacterization.trans <|
              (adjacencySame.multiple marker).trans
                rightCharacterization.symm
          unfold canonicalSquaredFactorInventory
          rw [leftShape, rightShape]
          change
            (leftFirst :: blockBearingFactors leftRest) ++
                markerOnlyFactorList
                  (canonicalMarkerBank
                    (terminatedFactorMarkers
                      (leftFirst :: blockBearingFactors leftRest))
                    leftLabels) =
              (rightFirst :: blockBearingFactors rightRest) ++
                markerOnlyFactorList
                  (canonicalMarkerBank
                    (terminatedFactorMarkers
                      (rightFirst :: blockBearingFactors rightRest))
                    rightLabels)
          rw [bankEqual, retainedEqual']

theorem canonicalFactorInventorySignatureObligation :
    CanonicalFactorInventorySignatureObligation where
  inventoryEqual := fun same =>
    canonicalSquaredFactorInventory_eq_of_sameSignature same

/-- The exact factor-inventory obligation is sufficient for equality of the
complete canonical lists; the final-block equality is already proved. -/
theorem squareInventoryCanonicalList_eq_of_obligation
    (obligation : CanonicalFactorInventorySignatureObligation)
    {left right : Word Nat}
    (same : SameSimpleSuccessorSignature left right) :
    squareInventoryCanonicalList left.toList =
      squareInventoryCanonicalList right.toList := by
  unfold squareInventoryCanonicalList
  rw [obligation.inventoryEqual same,
    terminatedFinalBlock_eq_of_sameSignature same]

theorem squareInventoryCanonicalWord_eq_of_obligation
    (obligation : CanonicalFactorInventorySignatureObligation)
    {left right : Word Nat}
    (same : SameSimpleSuccessorSignature left right) :
    squareInventoryCanonicalWord left =
      squareInventoryCanonicalWord right := by
  apply Word.toList_injective
  rw [toList_squareInventoryCanonicalWord,
    toList_squareInventoryCanonicalWord,
    squareInventoryCanonicalList_eq_of_obligation obligation same]

/-- Parametric completeness theorem exposing the factor-inventory interface.
The concrete witness below turns this into unconditional completeness. -/
theorem derivesOfSameSimpleSuccessorSignature_of_obligation
    (obligation : CanonicalFactorInventorySignatureObligation)
    {left right : Word Nat}
    (same : SameSimpleSuccessorSignature left right) :
    Derives basis left right := by
  have leftNormal := derivesSquareInventoryCanonical left
  have rightNormal := derivesSquareInventoryCanonical right
  have middle :
      Derives basis
        (squareInventoryCanonicalWord left)
        (squareInventoryCanonicalWord right) := by
    rw [squareInventoryCanonicalWord_eq_of_obligation obligation same]
    exact Derives.refl _
  exact leftNormal.trans (middle.trans rightNormal.symm)

/-- Equal exact table signatures have identical unrestricted canonical lists. -/
theorem squareInventoryCanonicalList_eq_of_sameSignature
    {left right : Word Nat}
    (same : SameSimpleSuccessorSignature left right) :
    squareInventoryCanonicalList left.toList =
      squareInventoryCanonicalList right.toList :=
  squareInventoryCanonicalList_eq_of_obligation
    canonicalFactorInventorySignatureObligation same

/-- Equal exact table signatures have identical unrestricted canonical words. -/
theorem squareInventoryCanonicalWord_eq_of_sameSignature
    {left right : Word Nat}
    (same : SameSimpleSuccessorSignature left right) :
    squareInventoryCanonicalWord left =
      squareInventoryCanonicalWord right :=
  squareInventoryCanonicalWord_eq_of_obligation
    canonicalFactorInventorySignatureObligation same

/-- The concrete scanner inventory proof closes unrestricted signature
sufficiency for arbitrary nonempty words. -/
theorem derivesOfSameSimpleSuccessorSignature
    {left right : Word Nat}
    (same : SameSimpleSuccessorSignature left right) :
    Derives basis left right :=
  derivesOfSameSimpleSuccessorSignature_of_obligation
    canonicalFactorInventorySignatureObligation same

/-- Unconditional direct basis endpoint for the exact S5_402 catalogue table. -/
theorem basisFor : BasisFor table.semigroup basis := by
  refine ⟨models, ?_⟩
  intro identity valid
  exact derivesOfSameSimpleSuccessorSignature
    (sameSignature_of_valid identity valid)

/-- Unconditional endpoint for the opposite table and literal reversed
thirteen-law basis. -/
theorem oppositeBasisFor :
    BasisFor table.semigroup.opposite oppositeBasis := by
  simpa [oppositeBasis] using basisFor.oppositeReversed

end SemigroupBasis.CoRoots.S5_402
